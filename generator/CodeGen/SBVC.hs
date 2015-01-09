{-# LANGUAGE DataKinds, EmptyDataDecls, GADTs, LambdaCase, PatternSynonyms, RankNTypes, TypeFamilies #-}
-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

-- TODO: inspect every case statement for semantic exhaustiveness
module CodeGen.SBVC where

import Control.Applicative
import Data.List
import Data.Map (Map)
import Data.Maybe
import Data.SBV
import System.Exit
import System.IO
import qualified Data.Map as M

import Cryptol.Eval.Value
import Cryptol.ModuleSystem (ModuleEnv(..))
import Cryptol.Parser
import Cryptol.Prims.Syntax
import Cryptol.Utils.PP
import Cryptol.Parser.AST (QName(..), Name(..), mkUnqual, mkQual, unqual) -- T.QName == P.QName
import Cryptol.Parser.Position
import Cryptol.TypeCheck.Defaulting
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))
import qualified Cryptol.Parser.AST     as P
import qualified Cryptol.Symbolic       as S
import qualified Cryptol.Symbolic.Value as S
import qualified Cryptol.TypeCheck.AST  as T

import CodeGen.Types

-- | Find a declaration in a module.
lookupDecl :: QName -> T.Module -> [(T.Expr, T.Schema)]
lookupDecl qn mod =
  [(T.dDefinition decl, T.dSignature decl)
    | group <- T.mDecls mod
    , decl  <- T.groupDecls group
    , T.dName decl `moreSpecificThan` qn
  ]

-- | Check that two names are equal, but also call them equal if the first one
-- has a qualification and the second one doesn't.
moreSpecificThan :: QName -> QName -> Bool
QName mod name `moreSpecificThan` QName mod' name' =
  name == name' && (mod == mod' || isNothing mod')

-- | Strip top-level location information from an expression.
dislocate :: P.Expr -> P.Expr
dislocate (P.ELocated e _) = dislocate e
dislocate e = e

-- TODO: What should we really do here?
-- | Pick a C identifier that corresponds to a given qualified name.
cName :: QName -> String
cName qn = case unqual qn of Name s -> s

-- | Print a diagnostic message and quit.
die :: String -> IO ()
die s = hPutStrLn stderr s >> exitFailure

codeGen :: Maybe FilePath -> GenerationRoot -> (T.Module, ModuleEnv) -> IO ()
codeGen dir (Identifier id) (mod, _) =
  case parseExpr id of
    Right e -> case dislocate e of
      P.EVar qn -> case lookupDecl qn mod of
        [(e, t)] -> case defaultExpr emptyRange {- TODO -} e t of
          Just (subst, e) -> compileToC dir (cName qn) (codeGenImpl subst e t)
          _ -> die $ "can't generate code for polymorphic expression " ++ id ++ " (and couldn't find a good way to monomorph it, either)"
        [] -> die $   "unknown identifier " ++ id
        _  -> die $ "ambiguous identifier " ++ id
      e -> die $ "looking for a variable name, got something more complicated instead\n" ++ show e
    Left err -> die $ id ++ " is not a valid variable name\n" ++ pretty err

pattern TConC h t = T.TCon (T.TC h) t
pattern Word n = TConC T.TCSeq [TConC (T.TCNum n) [], TConC T.TCBit []]
pattern Word8  = Word 8
pattern Word16 = Word 16
pattern Word32 = Word 32
pattern tyIn :-> tyOut = TConC T.TCFun [tyIn, tyOut]

data CodeGenValue
  = CGBit    SBool          -- ^ Bit
  | CGSeq    [CodeGenValue] -- ^ [n]a
  | CGWord8  SWord8         -- ^ [8]
  | CGWord16 SWord16        -- ^ [16]
  | CGWord32 SWord32        -- ^ [32]
  | CGFun (CodeGenValue -> CodeGenValue)  -- ^ functions
  | CGPoly (TValue -> CodeGenValue)       -- ^ polymorphic values
  | CGUninterpreted String [CodeGenValue] -- ^ function calls: function name and arguments
  -- TODO: records, tuples, streams

unBit :: CodeGenValue -> Maybe SBool
unBit (CGBit s) = Just s
unBit _ = Nothing

-- TODO: could try to do something smarter when the sequence contains just
-- literals
cgSeq xs = case mapM unBit xs of
  Just bits -> case length bits of
    8  -> CGWord8  (fromBitsBE bits)
    16 -> CGWord16 (fromBitsBE bits)
    32 -> CGWord32 (fromBitsBE bits)
    _ -> CGSeq xs
  _ -> CGSeq xs

data Env = Env
  { envVal  :: Map QName  CodeGenValue
  , envType :: Map T.TVar TValue
  }

emptyEnv = Env M.empty M.empty

bindVal   qn val env = env { envVal = M.insert qn val (envVal env) }
lookupVal qn     env = M.lookup qn (envVal env)
bindType n ty env = env -- TODO
evalType env ty = TValue ty  -- TODO

evalExpr :: Env -> T.Expr -> CodeGenValue
evalExpr env = \case
  T.ECon econ         -> evalECon econ
  T.EVar n            -> case lookupVal n env of
    Just x  -> x
    Nothing -> CGUninterpreted (cName n) []
  T.ETAbs tv e        -> CGPoly $ \ty -> evalExpr (bindType (T.tpVar tv) ty env) e
  T.ETApp e ty        -> case eval e of CGPoly f -> f (evalType env ty)
  T.EApp e e'         -> case eval e of
    CGUninterpreted f vs -> CGUninterpreted f (vs ++ [eval e'])
    CGFun f              -> f (eval e')
  T.EAbs qn _ty e     -> CGFun $ \x -> evalExpr (bindVal qn x env) e
  T.EProofAbs _prop e -> eval e
  T.EProofApp e       -> eval e
  where eval = evalExpr env

evalECon :: ECon -> CodeGenValue
evalECon = \case
  ECPlus   -> binArith (+)
  ECDemote -> CGPoly $ \value ->
              CGPoly $ \width ->
              case (numTValue value, numTValue width) of
                (Nat val, Nat  8) -> CGWord8  (fromInteger val)
                (Nat val, Nat 16) -> CGWord16 (fromInteger val)
                (Nat val, Nat 32) -> CGWord32 (fromInteger val)
                (Nat val, Nat  w) -> CGSeq [CGBit (fromBool (testBit val i)) | i <- [0..fromInteger w-1]]

binArith :: (forall a. Num a => a -> a -> a) -> CodeGenValue
binArith f = CGPoly $ \_ -> CGFun (CGFun . go) where
  go (CGSeq   xs) (CGSeq   ys) = CGSeq (zipWith go xs ys)
  go (CGWord8  x) (CGWord8  y) = CGWord8  (f x y)
  go (CGWord16 x) (CGWord16 y) = CGWord16 (f x y)
  go (CGWord32 x) (CGWord32 y) = CGWord32 (f x y)
  -- TODO: CGUninterpreted

codeGenImpl :: [(T.TParam, T.Type)] -> T.Expr -> T.Schema -> SBVCodeGen ()
codeGenImpl tyEnv expr (T.Forall [] [] ty) =
  supplyArgs v initTy >>= genOutput
  where
  initTy  = tValTy (evalType initEnv ty)
  initEnv = foldr (\(tp, ty) -> bindType (tparamToTVar tp) (TValue ty))
                  emptyEnv
                  tyEnv
  tparamToTVar tp = T.TVBound (T.tpUnique tp) (T.tpKind tp)
  v = evalExpr initEnv expr

  supplyArgs :: CodeGenValue -> T.Type -> SBVCodeGen CodeGenValue
  supplyArgs (CGFun f) (tyIn :-> tyOut) = case tyIn of
    Word8 -> cgInputWord8 >>= \v -> supplyArgs (f v) tyOut
    _ -> error "dunno how to make something of that type"
  supplyArgs v ty = return v

  genOutput (CGWord8 w) = cgOutput "out" w

cgInputWord8 :: SBVCodeGen CodeGenValue
cgInputWord8 = CGWord8 <$> cgInput "in"

--show' (CGRecord fields) = "{" ++ intercalate ", " [show n ++ "=" ++ show' v | (n, v) <- fields] ++ "}"
--show' (CGTuple vs) = "(" ++ intercalate ", " (map show' vs) ++ ")"
show' (CGBit b) = "bit"
show' (CGSeq vs) = "[" ++ intercalate ", " (map show' vs) ++ "]"
show' (CGWord8  w) = "word8"
show' (CGWord16 w) = "word16"
show' (CGWord32 w) = "word32"
--show' (CGStream vs) = "stream" ++ show' (VSeq undefined vs)
show' (CGFun f) = "function"
show' (CGPoly f) = "type function"
show' (CGUninterpreted f vs) = f ++ "(" ++ intercalate ", " (map show' vs) ++ ")"
