-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards #-}

module Cryptol.Eval (
    moduleEnv
  , EvalEnv()
  , emptyEnv
  , evalExpr
  , evalDecls
  , EvalError(..)
  , WithBase(..)
  , evalExprGeneric
  , evalDeclsGeneric
  , concretely
  , ExprOperations(..)
  ) where

import Cryptol.Eval.Error
import Cryptol.Eval.Env
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.TypeCheck.AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP
import Cryptol.Prims.Syntax (ECon)
import Cryptol.Prims.Eval

import Control.Monad (foldM)
import Data.List (transpose)
import Data.Monoid (Monoid(..),mconcat)
import qualified Data.Map as Map

data ExprOperations e b w = ExprOperations
  { eoECon       :: ECon -> GenValue b w
  , eoBindTerm   :: QName -> GenValue b w -> e -> e
  , eoBindType   :: TVar  -> TValue       -> e -> e
  , eoLookupTerm :: QName -> e -> GenValue b w
  -- TODO: should this be eoLookupType :: TVar -> e -> TValue?
  , eoEvalType   :: e -> Type -> TValue
  , eoListSel    :: Int -> GenValue b w -> GenValue b w
  , eoIf         :: b -> GenValue b w -> GenValue b w -> GenValue b w
  , eoPP         :: GenValue b w -> Doc
  }

concretely :: ExprOperations EvalEnv Bool BV
concretely = ExprOperations
  { eoECon       = evalECon
  , eoBindTerm   = bindVar
  , eoBindType   = bindType
  , eoLookupTerm = \n env -> case lookupVar n env of
      Just val -> val
      Nothing  -> evalPanic "evalExpr"
        [ "var `" ++ show (pp n) ++ "` is not defined"
        , pretty (WithBase defaultPPOpts env)
        ]
  , eoEvalType   = evalType
  , eoListSel    = \n v -> fromSeq v !! n
  , eoIf         = \b t f -> if b then t else f
  , eoPP         = ppValue defaultPPOpts
  }

-- Expression Evaluation -------------------------------------------------------

moduleEnv :: Module -> EvalEnv -> EvalEnv
moduleEnv m env = evalDecls (mDecls m) (evalNewtypes (mNewtypes m) env)

evalExpr :: EvalEnv -> Expr -> Value
evalExpr = evalExprGeneric concretely

evalExprGeneric
  :: (Monoid e, BitWord b w) => ExprOperations e b w
  -> e -> Expr -> GenValue b w
evalExprGeneric ops = eval where
  eval env expr = let eval' = eval env in case expr of
    ECon con      -> eoECon ops con
    EList es ty   -> VSeq (isTBit (eoEvalType ops env ty)) (map eval' es)
    ETuple es     -> VTuple (map eval' es)
    ERec fields   -> VRecord [ (f, eval' e) | (f, e) <- fields ]
    ESel e sel    -> evalSel ops sel (eval' e)
    EIf c t f     -> eoIf ops (fromVBit (eval' c)) (eval' t) (eval' f)
    EComp l h gs  -> evalComp ops env (eoEvalType ops env l) h gs
    EVar n        -> eoLookupTerm ops n env
    ETAbs tv b    -> VPoly $ \ty -> eval (eoBindType ops (tpVar tv) ty env) b
    ETApp e ty    -> case eval' e of
      VPoly f -> f (eoEvalType ops env ty)
      val     -> evalPanic "evalExpr"
                      ["expected a polymorphic value"
                      , show (eoPP ops val), show e, show ty
                      ]
    EApp f x      -> case eval' f of
      VFun f' -> f' (eval' x)
      val     -> evalPanic "evalExpr" ["expected a function", show (eoPP ops val) ]
    EAbs n _ b    -> VFun $ \val -> eval (eoBindTerm ops n val env) b

    -- XXX these will likely change once there is an evidence value
    EProofAbs _ e -> eval' e
    EProofApp e   -> eval' e

    ECast e _     -> eval' e
    EWhere e ds   -> eval (evalDeclsGeneric ops env ds) e


-- Newtypes --------------------------------------------------------------------

evalNewtypes :: Map.Map QName Newtype -> EvalEnv -> EvalEnv
evalNewtypes nts env = Map.foldl (flip evalNewtype) env nts

-- | Introduce the constructor function for a newtype.
evalNewtype :: Newtype -> EvalEnv -> EvalEnv
evalNewtype nt = bindVar (ntName nt) (foldr tabs con (ntParams nt))
  where
  tabs _tp body = tlam (\ _ -> body)
  con           = VFun id


-- Declarations ----------------------------------------------------------------

evalDecls :: [DeclGroup] -> EvalEnv -> EvalEnv
evalDecls dgs env = evalDeclsGeneric concretely env dgs

evalDeclsGeneric
  :: (Monoid e, BitWord b w) => ExprOperations e b w
  -> e -> [DeclGroup] -> e
evalDeclsGeneric ops = foldl (evalDeclGroup ops)

evalDeclGroup
  :: (Monoid e, BitWord b w) => ExprOperations e b w
  -> e -> DeclGroup -> e
evalDeclGroup ops env dg = env'
  where
  -- the final environment is passed in for each declaration, to permit
  -- recursive values.
  env' = case dg of
    Recursive ds   -> foldr (evalDecl ops env') env ds
    NonRecursive d -> evalDecl ops env d env

evalDecl
  :: (Monoid e, BitWord b w) => ExprOperations e b w
  -> e -- ^ the environment to evaluate declaration bodies in
  -> Decl
  -> e -- ^ the environment to add bindings to
  -> e
evalDecl ops renv d = eoBindTerm ops (dName d) (evalExprGeneric ops renv (dDefinition d))


-- Selectors -------------------------------------------------------------------

evalSel :: ExprOperations e b w -> Selector -> GenValue b w -> GenValue b w
evalSel ops sel = case sel of
  TupleSel  n _ -> tupleSel  n
  RecordSel n _ -> recordSel n
  ListSel   n _ -> listSel   n
  where

  atLeaf f = go where
    go (VSeq False vs) = VSeq False (fmap go vs)
    go (VStream    vs) = VStream    (fmap go vs)
    go (VFun       vf) = VFun       (fmap go vf)
    go v = f v

  tupleSel n = atLeaf $ \v -> case v of
    VTuple vs -> vs !! n
    _         -> evalPanic "evalSel"
      [ "Tuple selector applied to incompatible type"
      , show (eoPP ops v) ]

  recordSel n = atLeaf $ \v -> case v of
    VRecord {} -> lookupRecord n v
    _          -> evalPanic "evalSel"
      [ "Record selector applied to incompatible type"
      , show (eoPP ops v) ]

  listSel = eoListSel ops


-- List Comprehensions ---------------------------------------------------------

-- | Evaluate a comprehension.
evalComp
  :: (Monoid e, BitWord b w) => ExprOperations e b w
  -> e -> TValue -> Expr -> [[Match]] -> GenValue b w
evalComp ops env seqty body ms
  | Just (len,el) <- isTSeq seqty = toSeq len el [ evalExprGeneric ops e body | e <- envs ]
  | otherwise = evalPanic "Cryptol.Eval.evalComp"
    [ "not a sequence type", show seqty ]
  -- XXX we could potentially print this as a number if the type was available.
  where
  -- generate a new environment for each iteration of each parallel branch
  benvs = map (branchEnvs ops env) ms

  -- take parallel slices of each environment.  when the length of the list
  -- drops below the number of branches, one branch has terminated.
  allBranches es = length es == length ms
  slices         = takeWhile allBranches (transpose benvs)

  -- join environments to produce environments at each step through the process.
  envs = map mconcat slices

-- | Turn a list of matches into the final environments for each iteration of
-- the branch.
branchEnvs :: (Monoid e, BitWord b w) => ExprOperations e b w -> e -> [Match] -> [e]
branchEnvs ops = foldM (evalMatch ops)

-- | Turn a match into the list of environments it represents.
evalMatch :: (Monoid e, BitWord b w) => ExprOperations e b w -> e -> Match -> [e]
evalMatch ops env m = case m of

  -- many envs
  From n _ty expr -> [eoBindTerm ops n v env | v <- fromSeq (evalExprGeneric ops env expr)]

  -- XXX we don't currently evaluate these as though they could be recursive, as
  -- they are typechecked that way; the read environment to evalDecl is the same
  -- as the environment to bind a new name in.
  Let d           -> [evalDecl ops env d env]
