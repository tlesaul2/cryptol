-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Cryptol.Symbolic where

import Control.Applicative
import Control.Monad (replicateM, when, zipWithM)
import Control.Monad.IO.Class
import Data.List (transpose, intercalate)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid (Monoid(..))
import Data.Traversable (traverse)
import qualified Control.Exception as X

import qualified Data.SBV as SBV

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M

import Cryptol.Symbolic.BitVector
import Cryptol.Symbolic.Prims
import Cryptol.Symbolic.Value

import Cryptol.Eval (ExprOperations(..))
import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Value as Eval
import qualified Cryptol.Eval.Type (evalType)
import qualified Cryptol.Eval.Env (EvalEnv(..))
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

-- External interface ----------------------------------------------------------

proverConfigs :: [(String, SBV.SMTConfig)]
proverConfigs =
  [ ("cvc4"     , SBV.cvc4     )
  , ("yices"    , SBV.yices    )
  , ("z3"       , SBV.z3       )
  , ("boolector", SBV.boolector)
  , ("mathsat"  , SBV.mathSAT  )
  , ("offline"  , SBV.defaultSMTCfg )
  , ("any"      , SBV.defaultSMTCfg )
  ]

proverNames :: [String]
proverNames = map fst proverConfigs

lookupProver :: String -> SBV.SMTConfig
lookupProver s =
  case lookup s proverConfigs of
    Just cfg -> cfg
    -- should be caught by UI for setting prover user variable
    Nothing  -> panic "Cryptol.Symbolic" [ "invalid prover: " ++ s ]

type SatResult = [(Type, Expr, Eval.Value)]

-- | A prover result is either an error message, an empty result (eg
-- for the offline prover), a counterexample or a lazy list of
-- satisfying assignments.
data ProverResult = AllSatResult [SatResult] -- LAZY
                  | ThmResult    [Type]
                  | EmptyResult
                  | ProverError  String

allSatSMTResults :: SBV.AllSatResult -> [SBV.SMTResult]
allSatSMTResults (SBV.AllSatResult (_, rs)) = rs

thmSMTResults :: SBV.ThmResult -> [SBV.SMTResult]
thmSMTResults (SBV.ThmResult r) = [r]

satProve :: Bool
         -> Maybe Int -- ^ satNum
         -> (String, Bool, Bool)
         -> [DeclGroup]
         -> Maybe FilePath
         -> (Expr, Schema)
         -> M.ModuleCmd ProverResult
satProve isSat mSatNum (proverName, useSolverIte, verbose) edecls mfile (expr, schema) = protectStack useSolverIte $ \modEnv -> do
  let extDgs = allDeclGroups modEnv ++ edecls
  provers <-
    case proverName of
      "any" -> SBV.sbvAvailableSolvers
      _ -> return [(lookupProver proverName) { SBV.smtFile = mfile }]
  let provers' = [ p { SBV.timing = verbose, SBV.verbose = verbose } | p <- provers ]
  let tyFn = if isSat then existsFinType else forallFinType
  let runProver fn tag e = do
        when verbose $ liftIO $
          putStrLn $ "Trying proof with " ++
                     intercalate ", " (map show provers)
        (firstProver, res) <- fn provers' e
        when verbose $ liftIO $
          putStrLn $ "Got result from " ++ show firstProver
        return (tag res)
  let runFn | isSat     = runProver SBV.allSatWithAny allSatSMTResults
            | otherwise = runProver SBV.proveWithAny  thmSMTResults
  case predArgTypes schema of
    Left msg -> return (Right (ProverError msg, modEnv), [])
    Right ts -> do when verbose $ putStrLn "Simulating..."
                   let env = evalDecls (emptyEnv useSolverIte) extDgs
                   let v = evalExpr env expr
                   results' <- runFn $ do
                                 args <- mapM tyFn ts
                                 b <- return $! fromVBit (foldl fromVFun v args)
                                 return b
                   let results = maybe results' (\n -> take n results') mSatNum
                   esatexprs <- case results of
                     -- allSat can return more than one as long as
                     -- they're satisfiable
                     (SBV.Satisfiable {} : _) -> do
                       tevss <- mapM mkTevs results
                       return $ AllSatResult tevss
                       where
                         mkTevs result =
                           let Right (_, cws) = SBV.getModel result
                               (vs, _) = parseValues ts cws
                               sattys = unFinType <$> ts
                               satexprs = zipWithM Eval.toExpr sattys vs
                           in case zip3 sattys <$> satexprs <*> pure vs of
                             Nothing ->
                               panic "Cryptol.Symbolic.sat"
                                 [ "unable to make assignment into expression" ]
                             Just tevs -> return $ tevs
                     -- prove returns only one
                     [SBV.Unsatisfiable {}] ->
                       return $ ThmResult (unFinType <$> ts)
                     -- unsat returns empty
                     [] -> return $ ThmResult (unFinType <$> ts)
                     -- otherwise something is wrong
                     _ -> return $ ProverError (rshow results)
                            where rshow | isSat = show . SBV.AllSatResult . (boom,)
                                        | otherwise = show . SBV.ThmResult . head
                                  boom = panic "Cryptol.Symbolic.sat"
                                           [ "attempted to evaluate bogus boolean for pretty-printing" ]
                   return (Right (esatexprs, modEnv), [])

satProveOffline :: Bool
                -> Bool
                -> Bool
                -> [DeclGroup]
                -> Maybe FilePath
                -> (Expr, Schema)
                -> M.ModuleCmd ProverResult
satProveOffline isSat useIte vrb edecls mfile (expr, schema) =
  protectStack useIte $ \modEnv -> do
    let extDgs = allDeclGroups modEnv ++ edecls
    let tyFn = if isSat then existsFinType else forallFinType
    let filename = fromMaybe "standard output" mfile
    case predArgTypes schema of
      Left msg -> return (Right (ProverError msg, modEnv), [])
      Right ts ->
        do when vrb $ putStrLn "Simulating..."
           let env = evalDecls (emptyEnv useIte) extDgs
           let v = evalExpr env expr
           let satWord | isSat = "satisfiability"
                       | otherwise = "validity"
           txt <- SBV.compileToSMTLib True isSat $ do
                    args <- mapM tyFn ts
                    b <- return $! fromVBit (foldl fromVFun v args)
                    liftIO $ putStrLn $
                      "Writing to SMT-Lib file " ++ filename ++ "..."
                    return b
           liftIO $ putStrLn $
             "To determine the " ++ satWord ++
             " of the expression, use an external SMT solver."
           case mfile of
             Just path -> writeFile path txt
             Nothing -> putStr txt
           return (Right (EmptyResult, modEnv), [])

protectStack :: Bool
             -> M.ModuleCmd ProverResult
             -> M.ModuleCmd ProverResult
protectStack usingITE cmd modEnv = X.catchJust isOverflow (cmd modEnv) handler
  where isOverflow X.StackOverflow = Just ()
        isOverflow _               = Nothing
        msg | usingITE  = msgBase
            | otherwise = msgBase ++ "\n" ++
                          "Using ':set iteSolver=on' might help."
        msgBase = "Symbolic evaluation failed to terminate."
        handler () = return (Right (ProverError msg, modEnv), [])

parseValues :: [FinType] -> [SBV.CW] -> ([Eval.Value], [SBV.CW])
parseValues [] cws = ([], cws)
parseValues (t : ts) cws = (v : vs, cws'')
  where (v, cws') = parseValue t cws
        (vs, cws'') = parseValues ts cws'

parseValue :: FinType -> [SBV.CW] -> (Eval.Value, [SBV.CW])
parseValue FTBit [] = panic "Cryptol.Symbolic.parseValue" [ "empty FTBit" ]
parseValue FTBit (cw : cws) = (Eval.VBit (SBV.fromCW cw), cws)
parseValue (FTSeq 0 FTBit) cws = (Eval.VWord (Eval.BV 0 0), cws)
parseValue (FTSeq n FTBit) (cw : cws)
  | SBV.isBounded cw = (Eval.VWord (Eval.BV (toInteger n) (SBV.fromCW cw)), cws)
  | otherwise = panic "Cryptol.Symbolic.parseValue" [ "unbounded concrete word" ]
parseValue (FTSeq n FTBit) cws = (Eval.VSeq True vs, cws')
  where (vs, cws') = parseValues (replicate n FTBit) cws
parseValue (FTSeq n t) cws = (Eval.VSeq False vs, cws')
  where (vs, cws') = parseValues (replicate n t) cws
parseValue (FTTuple ts) cws = (Eval.VTuple vs, cws')
  where (vs, cws') = parseValues ts cws
parseValue (FTRecord fs) cws = (Eval.VRecord (zip ns vs), cws')
  where (ns, ts) = unzip fs
        (vs, cws') = parseValues ts cws

allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups = concatMap mDecls . M.loadedModules

data FinType
    = FTBit
    | FTSeq Int FinType
    | FTTuple [FinType]
    | FTRecord [(Name, FinType)]

numType :: Type -> Maybe Int
numType (TCon (TC (TCNum n)) [])
  | 0 <= n && n <= toInteger (maxBound :: Int) = Just (fromInteger n)
numType (TUser _ _ t) = numType t
numType _ = Nothing

finType :: Type -> Maybe FinType
finType ty =
  case ty of
    TCon (TC TCBit) []       -> Just FTBit
    TCon (TC TCSeq) [n, t]   -> FTSeq <$> numType n <*> finType t
    TCon (TC (TCTuple _)) ts -> FTTuple <$> traverse finType ts
    TRec fields              -> FTRecord <$> traverse (traverseSnd finType) fields
    TUser _ _ t              -> finType t
    _                        -> Nothing

unFinType :: FinType -> Type
unFinType fty =
  case fty of
    FTBit        -> tBit
    FTSeq l ety  -> tSeq (tNum l) (unFinType ety)
    FTTuple ftys -> tTuple (unFinType <$> ftys)
    FTRecord fs  -> tRec (zip fns tys)
      where
        fns = fst <$> fs
        tys = unFinType . snd <$> fs

predArgTypes :: Schema -> Either String [FinType]
predArgTypes schema@(Forall ts ps ty)
  | null ts && null ps =
      case go ty of
        Just fts -> Right fts
        Nothing  -> Left $ "Not a valid predicate type:\n" ++ show (pp schema)
  | otherwise = Left $ "Not a monomorphic type:\n" ++ show (pp schema)
  where
    go (TCon (TC TCBit) []) = Just []
    go (TCon (TC TCFun) [ty1, ty2]) = (:) <$> finType ty1 <*> go ty2
    go (TUser _ _ t) = go t
    go _ = Nothing

forallFinType :: FinType -> SBV.Symbolic Value
forallFinType ty =
  case ty of
    FTBit         -> VBit <$> SBV.forall_
    FTSeq 0 FTBit -> return $ VWord (SBV.literal (bv 0 0))
    FTSeq n FTBit -> VWord <$> (forallBV_ n)
    FTSeq n t     -> VSeq False <$> replicateM n (forallFinType t)
    FTTuple ts    -> VTuple <$> mapM forallFinType ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd forallFinType) fs

existsFinType :: FinType -> SBV.Symbolic Value
existsFinType ty =
  case ty of
    FTBit         -> VBit <$> SBV.exists_
    FTSeq 0 FTBit -> return $ VWord (SBV.literal (bv 0 0))
    FTSeq n FTBit -> VWord <$> existsBV_ n
    FTSeq n t     -> VSeq False <$> replicateM n (existsFinType t)
    FTTuple ts    -> VTuple <$> mapM existsFinType ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd existsFinType) fs

-- Simulation environment ------------------------------------------------------

data Env = Env
  { envVars :: Map.Map QName Value
  , envTypes :: Map.Map TVar TValue
  , envIteSolver :: Bool -- ^ Should we pay more (in terms of number of external SMT solver calls) to avoid more instances of non-terminating symbolic computations?
  }

instance Monoid Env where
  mempty = Env
    { envVars  = Map.empty
    , envTypes = Map.empty
    , envIteSolver = False
    }

  mappend l r = Env
    { envVars  = Map.union (envVars  l) (envVars  r)
    , envTypes = Map.union (envTypes l) (envTypes r)
    , envIteSolver = envIteSolver l || envIteSolver r
    }

emptyEnv :: Bool -> Env
emptyEnv useIteSolver = Env Map.empty Map.empty useIteSolver

-- | Bind a variable in the evaluation environment.
bindVar :: QName -> Value -> Env -> Env
bindVar n thunk env = env { envVars = Map.insert n thunk (envVars env) }

-- | Lookup a variable in the environment.
lookupVar :: QName -> Env -> Maybe Value
lookupVar n env = Map.lookup n (envVars env)

-- | Look up a variable and throw an error if it isn't there.
unsafeLookupVar n env = case lookupVar n env of
  Just x -> x
  _ -> panic "Cryptol.Symbolic.lookupVar"
    [ "Variable " ++ show n ++ " not found" ]
  -- TODO: how to deal with uninterpreted functions?

-- | Bind a type variable of kind *.
bindType :: TVar -> TValue -> Env -> Env
bindType p ty env = env { envTypes = Map.insert p ty (envTypes env) }

-- | Lookup a type variable.
lookupType :: TVar -> Env -> Maybe TValue
lookupType p env = Map.lookup p (envTypes env)

-- | Select the value at a given index of a sequence.
index :: Int -> Value -> Value
index n (VWord s) = VBit (SBV.sbvTestBit s n)
index n v         = fromSeq v !! n

-- Expressions -----------------------------------------------------------------

symbolically :: Env -> ExprOperations Env SBV.SBool SWord
symbolically env = ExprOperations
  { eoECon       = evalECon
  , eoBindTerm   = bindVar
  , eoBindType   = bindType
  , eoLookupTerm = unsafeLookupVar
  , eoEvalType   = evalType
  , eoListSel    = index
  , eoIf         = if envIteSolver env then SBV.sBranch else SBV.ite
  , eoPP         = \_ -> text "(can't pretty-print symbolic values)" -- TODO
  }

evalExpr :: Env -> Expr -> Value
evalExpr env expr = Eval.evalExprGeneric (symbolically env) env expr

evalType :: Env -> Type -> TValue
evalType env ty = Cryptol.Eval.Type.evalType env' ty
  where env' = Cryptol.Eval.Env.EvalEnv Map.empty (envTypes env)


-- Declarations ----------------------------------------------------------------

evalDecls :: Env -> [DeclGroup] -> Env
evalDecls env = Eval.evalDeclsGeneric (symbolically env) env
