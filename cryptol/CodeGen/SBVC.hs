{-# LANGUAGE DataKinds, EmptyDataDecls, GADTs, LambdaCase, PatternSynonyms #-}
-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module CodeGen.SBVC where

import Control.Applicative
import Data.Map (Map)
import Data.Maybe
import Data.SBV
import System.Exit
import System.IO
import qualified Data.Map as M

import Cryptol.Eval.Value
import Cryptol.ModuleSystem
import Cryptol.Parser
import Cryptol.Prims.Syntax
import Cryptol.Utils.PP
import Cryptol.Parser.AST (QName(..), Name(..), mkUnqual, mkQual, unqual) -- T.QName == P.QName
import Cryptol.Parser.Position
import Cryptol.TypeCheck.Defaulting
import qualified Cryptol.Parser.AST    as P
import qualified Cryptol.TypeCheck.AST as T

import CodeGen.Types

-- | Find a declaration in a module.
lookupVar :: QName -> T.Module -> [(T.Expr, T.Schema)]
lookupVar qn mod =
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
      P.EVar qn -> case lookupVar qn mod of
        [(e, t)] -> case defaultExpr emptyRange {- TODO -} e t of
          Just (subst, e) -> compileToC dir (cName qn) (codeGenImpl subst e)
          _ -> die $ "can't generate code for polymorphic expression " ++ id ++ " (and couldn't find a good way to monomorph it, either)"
        [] -> die $   "unknown identifier " ++ id
        _  -> die $ "ambiguous identifier " ++ id
      e -> die $ "looking for a variable name, got something more complicated instead\n" ++ show e
    Left err -> die $ id ++ " is not a valid variable name\n" ++ pretty err

data MExpr a where
  MCon :: MCon a -> MExpr a
  MVar :: MName a -> MExpr a
  MApp :: MExpr (a -> b) -> MExpr a -> MExpr b
  MAbs :: MName a -> MExpr b -> MExpr (a -> b)

data MName a
data Array i e
data MCon a

data Expr where
  ExprBox :: MExpr a -> Expr

data CType a where
  CBit   :: CType Bool
  CSeq8  :: CType Word8
  CSeq16 :: CType Word16
  CSeq32 :: CType Word32

lookupType :: [(T.TParam, T.Type)] -> T.TVar -> Maybe T.Type
lookupType env (T.TVBound unique kind) = listToMaybe
  [ t
  | (T.TParam { T.tpUnique = unique', T.tpKind = kind' }, t) <- env
  , unique == unique'
  , kind   == kind'
  ]
-- we can't hope for free type variables to be available in the binding
-- environment
lookupType _ _ = Nothing

closeType :: [(T.TParam, T.Type)] -> T.Type -> Maybe T.Type
closeType env (T.TCon tcon ts)  = T.TCon tcon <$> mapM (closeType env) ts
closeType env (T.TVar t)        = lookupType env t
closeType env (T.TUser qn ts t) = T.TUser qn ts <$> closeType env t
closeType env (T.TRec fields)   = T.TRec <$> mapM closeField fields where
  closeField (n, t) = do
    t' <- closeType env t
    return (n, t')

data SBVDynamic where
  SBVDynamic :: CType a -> SBV a -> SBVDynamic

data TEq a b where Refl :: TEq a a

class Eq1 f where eq :: f a -> f b -> Maybe (TEq a b)
instance Eq1 CType where
  eq CBit   CBit   = Just Refl
  eq CSeq8  CSeq8  = Just Refl
  eq CSeq16 CSeq16 = Just Refl
  eq CSeq32 CSeq32 = Just Refl
  eq _ _ = Nothing

flattenExpr :: T.Expr -> T.Expr
flattenExpr = \case
  e@(T.ETApp (T.ETApp (T.ECon ECDemote) _) _) -> e
  T.EProofApp   e    -> flattenExpr e
  T.ETApp       e _  -> flattenExpr e
  T.ETAbs     _ e    -> flattenExpr e
  T.EProofAbs _ e    -> flattenExpr e
  T.EProofApp   e    -> flattenExpr e
  T.EAbs    n t e    -> T.EAbs n t (flattenExpr e)
  T.EApp        e e' -> T.EApp (flattenExpr e) (flattenExpr e')
  e@(T.EVar{})       -> e
  e@(T.ECon{})       -> e
  e                  -> error ("unimplemented expression flattening: " ++ show e)

pattern TConC h t = T.TCon (T.TC h) t
pattern Word n = TConC T.TCSeq [TConC (T.TCNum n) [], TConC T.TCBit []]
pattern Word8  = Word 8
pattern Word16 = Word 16
pattern Word32 = Word 32

-- TODO
codeGenImpl :: [(T.TParam, T.Type)] -> T.Expr -> SBVCodeGen ()
codeGenImpl tyEnv = go M.empty . flattenExpr where
  go tmEnv (T.EAbs n t e) = case closeType tyEnv t of
    Just Word8 -> do
      -- TODO: probably need to be careful about name clashes when calling
      -- cName here
      var <- cgInput (cName n)
      go (M.insert n (SBVDynamic CSeq8 var) tmEnv) e
    _ -> error ("don't know how to represent type: " ++ show t)
  go tmEnv e@(T.EApp{}) = case genBody tmEnv e of
    -- TODO: "result" seems like a good way to cause name clashes
    SBVDynamic CSeq8 v -> cgOutput "result" v
    _ -> error "couldn't work out how to represent computation result type"
  go _ e = error ("code gen unimplemented for term: " ++ show e)

genBody = undefined
