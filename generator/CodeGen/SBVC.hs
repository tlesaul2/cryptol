{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module CodeGen.SBVC where

import Control.Applicative
import Data.List (intercalate)
import Data.Foldable (foldrM)
import Data.Map (Map)
import Data.Monoid
import Data.SBV
import qualified Data.SBV.Internals as SBV
import qualified Data.Map as M

import Cryptol.Eval (ExprOperations(..), evalDeclsGeneric, evalNewtypesGeneric)
import Cryptol.Eval.Value (BitWord(..), GenValue(..), PPOpts(..), TValue(..), WithBase(..), defaultPPOpts)
import Cryptol.ModuleSystem (ModuleEnv(..), checkExpr, focusedEnv, initialModuleEnv)
import Cryptol.ModuleSystem.Env (moduleDeps)
import Cryptol.ModuleSystem.Monad (runModuleM, ModuleM, getModuleEnv, io)
import qualified Cryptol.ModuleSystem.Base as Base
import Cryptol.ModuleSystem.Renamer (namingEnv, rename, runRenamer)
import Cryptol.Parser (parseExpr)
import Cryptol.Parser.Position (Range, emptyRange)
import Cryptol.Prims.Eval (BinOp, UnOp)
import Cryptol.Prims.Syntax
import Cryptol.Symbolic.Value () -- for its instance Mergeable (GenValue b w)
import Cryptol.TypeCheck.AST
           (ModName(..), QName(..), Name(..), TVar, Expr, Type(..), Schema(..),
            TCon(..), TC(..), Expr(..), Module(..), Decl(..), DeclGroup(),
            groupDecls)
import Cryptol.TypeCheck.Defaulting (defaultExpr)
import Cryptol.TypeCheck.Subst (apSubst)
import Cryptol.Utils.Compare
import Cryptol.Utils.Panic
import Cryptol.Utils.PP (PP(..), Doc, braces, brackets, char, comma, fsep, parens, pp, pretty, punctuate, sep, text)

import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Prims.Eval as Eval
import qualified Cryptol.Eval       as Eval
import qualified Cryptol.Eval.Type  as Eval
import qualified Cryptol.Eval.Env   as Eval
import qualified Cryptol.Utils.PP   as PP

import qualified CodeGen.Types as T


-- CWord -----------------------------------------------------------------------

-- A type of words with statically-known bit sizes.
data CWord
  = CWord8  SWord8
  | CWord16 SWord16
  | CWord32 SWord32
  | CWord64 SWord64
  | UnsupportedSize Int

instance BitWord SBool CWord where
  packWord bs = case length bs of
    8  -> CWord8  $ fromBitsBE bs
    16 -> CWord16 $ fromBitsBE bs
    32 -> CWord32 $ fromBitsBE bs
    64 -> CWord64 $ fromBitsBE bs
    n  -> UnsupportedSize n
  unpackWord cw = case cw of
    CWord8  w -> blastBE w
    CWord16 w -> blastBE w
    CWord32 w -> blastBE w
    CWord64 w -> blastBE w
    UnsupportedSize n -> panic "CodeGen.SBVC.unpackWord @SBool @CWord"
      [ "Words of width " ++ show n ++ " are not supported." ]

instance Comparable CWord OrderingSymbolic where
  cmp (CWord8  l) (CWord8  r) = cmp l r
  cmp (CWord16 l) (CWord16 r) = cmp l r
  cmp (CWord32 l) (CWord32 r) = cmp l r
  cmp (CWord64 l) (CWord64 r) = cmp l r
  cmp l r
    | cWidth l == cWidth r = panic "CodeGen.SBVC.cmp @CWord"
      [ "Can't compare words of unsupported size " ++ show (cWidth l) ]
    | otherwise = panic "CodeGen.SBVC.cmp @CWord"
      [ "Can't compare words of differing sizes:"
      , show (cWidth l)
      , show (cWidth r)
      ]

mkCWord :: Integer -> Integer -> CWord
mkCWord width value = case width of
  8  -> CWord8  $ fromInteger value
  16 -> CWord16 $ fromInteger value
  32 -> CWord32 $ fromInteger value
  64 -> CWord64 $ fromInteger value
  _  -> UnsupportedSize $ fromInteger width

cWidth :: CWord -> Int
cWidth CWord8 {} = 8
cWidth CWord16{} = 16
cWidth CWord32{} = 32
cWidth CWord64{} = 64
cWidth (UnsupportedSize n) = n

liftUnCWord
  :: UnOp SWord8
  -> UnOp SWord16
  -> UnOp SWord32
  -> UnOp SWord64
  -> Integer -> UnOp CWord
liftUnCWord op8 op16 op32 op64 _ cw = case cw of
  CWord8  w -> CWord8  (op8  w)
  CWord16 w -> CWord16 (op16 w)
  CWord32 w -> CWord32 (op32 w)
  CWord64 w -> CWord64 (op64 w)
  _ -> cw

liftBinCWord
  :: BinOp SWord8
  -> BinOp SWord16
  -> BinOp SWord32
  -> BinOp SWord64
  -> Integer -> BinOp CWord
liftBinCWord op8 op16 op32 op64 _ cl cr = case (cl, cr) of
  (CWord8  l, CWord8  r) -> CWord8  (op8  l r)
  (CWord16 l, CWord16 r) -> CWord16 (op16 l r)
  (CWord32 l, CWord32 r) -> CWord32 (op32 l r)
  (CWord64 l, CWord64 r) -> CWord64 (op64 l r)
  (UnsupportedSize l, UnsupportedSize r) | l == r -> UnsupportedSize l
  _ -> panic "CodeGen.SBVC.liftBinCWord"
    [ "size mismatch"
    , show (cWidth cl)
    , show (cWidth cr)
    ]

-- | All the classes supported by the kinds of words contained in a 'CWord'.
-- Commented-out contexts are ones which we could support but don't for now
-- because we aren't using them yet and don't want to spuriously add imports.
type SBVWord a =
  ( SDivisible a
  , FromBits a
  , Polynomial a
  , Bounded a
  , Enum a
  , Eq a
  , Num a
  , Show a
  -- , Arbitrary a
  , Bits a
  -- , NFData a
  -- , Random a
  , SExecutable a
  , Data.SBV.HasKind a
  , PrettyNum a
  , Uninterpreted a
  , Mergeable a
  , OrdSymbolic a
  , EqSymbolic a
  )

liftBinSBVWord :: (forall a. SBVWord a => BinOp a) -> Integer -> BinOp CWord
liftBinSBVWord op = liftBinCWord op op op op

liftUnSBVWord :: (forall a. SBVWord a => UnOp a) -> Integer -> UnOp CWord
liftUnSBVWord op = liftUnCWord op op op op

instance Mergeable CWord where
  symbolicMerge b sb = liftBinSBVWord
    (symbolicMerge b sb)
    (panic "CodeGen.SBVC.symbolicMerge @CWord" ["unused size argument was unexpectedly inspected"])


-- Primitives ------------------------------------------------------------------

type Value = GenValue SBool CWord

-- | Extend an environment with the contents of a module.
extEnv :: Module -> Env -> Env
extEnv m = evalTopDecls (mDecls m)
         . evalNewtypesGeneric withSBVC (mNewtypes m)

evalTopDecls :: [DeclGroup] -> Env -> Env
evalTopDecls ds env = evalDeclsGeneric withSBVC env' ds
  where
  env' = foldl addUninterpreted env (concatMap groupDecls ds)

-- See also Cryptol.Symbolic.Prims.evalECon
--      and Cryptol.Prims.Eval.evalECon
evalECon :: ECon -> Value
evalECon e = case e of
  ECTrue        -> VBit true
  ECFalse       -> VBit false
  ECDemote      -> Eval.ecDemoteGeneric "CodeGen.SBVC.evalECon" mkCWord
  ECPlus        -> binArith "+" (+)
  ECMinus       -> binArith "-" (-)
  ECMul         -> binArith "*" (*)
  ECDiv         -> binArith "div" sDiv
  ECMod         -> binArith "mod" sMod
  {-
  ECExp         ->
  ECLg2         ->
  -}
  ECNeg         -> unArith "neg" negate
  ECLt          -> Eval.binary $ Eval.cmpOrder  lt
  ECGt          -> Eval.binary $ Eval.cmpOrder  gt
  ECLtEq        -> Eval.binary $ Eval.cmpOrder ngt
  ECGtEq        -> Eval.binary $ Eval.cmpOrder nlt
  ECEq          -> Eval.binary $ Eval.cmpOrder  eq
  ECNotEq       -> Eval.binary $ Eval.cmpOrder neq
  ECFunEq       -> Eval.funCmp  eq
  ECFunNotEq    -> Eval.funCmp neq
  ECMin         -> Eval.binary $ Eval.withOrder ngt
  ECMax         -> Eval.binary $ Eval.withOrder nlt
  ECAnd         -> Eval.binary $ Eval.pointwiseBinary (&&&) (liftBinSBVWord (.&.))
  ECOr          -> Eval.binary $ Eval.pointwiseBinary (|||) (liftBinSBVWord (.|.))
  ECXor         -> Eval.binary $ Eval.pointwiseBinary (<+>) (liftBinSBVWord  xor )
  ECCompl       -> Eval.unary  $ Eval.pointwiseUnary  bnot  (liftUnSBVWord complement)
  {-
  ECZero        ->
  ECShiftL      ->
  ECShiftR      ->
  ECRotL        ->
  ECRotR        ->
  ECCat         ->
  ECSplitAt     ->
  ECJoin        ->
  ECSplit       ->
  ECReverse     ->
  ECTranspose   ->
  ECAt          ->
  ECAtRange     ->
  ECAtBack      ->
  ECAtRangeBack ->
  ECFromThen    ->
  ECFromTo      ->
  ECFromThenTo  ->
  ECInfFrom     ->
  ECInfFromThen ->
  ECError       ->
  ECPMul        ->
  ECPDiv        ->
  ECPMod        ->
  ECRandom      ->
  -}
  _ -> panic "CodeGen.SBVC.evalECon" ["operation not supported: " ++ show e]

binArith :: String -> (forall a. SBVWord a => BinOp a) -> Value
binArith opName op = Eval.binary $ Eval.pointwiseBinary
  (panic "CodeGen.SBVC.evalECon"
    ["Bits were a complete surprise when evaluating " ++ opName])
  (liftBinSBVWord op)

unArith :: String -> (forall a. SBVWord a => UnOp a) -> Value
unArith opName op = Eval.unary $ Eval.pointwiseUnary
  (panic "CodeGen.SBVC.evalECon"
    ["Bits were a complete surprise when evaluating " ++ opName])
  (liftUnSBVWord op)


-- Uninterpreted Functions -----------------------------------------------------

addUninterpreted :: Env -> Decl -> Env
addUninterpreted env Decl { .. } = bindUninterpretedTerm dName val env
  where
  val = bindArgs dName dSignature

-- | Generate a value that will apply arguments to an uninterpreted value.
bindArgs :: QName -> Schema -> Value
bindArgs qn sig = go [] args

  where

  (args,res) = flattenSchema sig

  -- TODO: change to panic
  badType ty =
    error ("bindArgs: unsupported type: " ++ pretty qn ++ " : " ++ pretty ty ++ "(" ++ show ty ++ ")")

  kind =
    case res of
      PWord n | n `elem` [8,16,32,64] -> KBounded False (fromInteger n)
      _                               -> badType res

  go vals (PWord n : rest)
    | n `elem` [8, 16, 32, 64] =
      VFun (\ (VWord val) -> go (val:vals) rest )

  go _ (ty:_) = badType ty

  -- TODO: allow results other than CWord8
  go vals [] =
    VWord $ CWord8 $ SBV.SBV kind $ Right $ SBV.cache $ \ st ->
      do words <- mapM (toSW st) (reverse vals)
         SBV.newExpr st kind (SBV.SBVApp (SBV.Uninterpreted (cName qn)) words)

  toSW st (CWord8  sbv) = SBV.sbvToSW st sbv
  toSW st (CWord16 sbv) = SBV.sbvToSW st sbv
  toSW st (CWord32 sbv) = SBV.sbvToSW st sbv
  toSW st (CWord64 sbv) = SBV.sbvToSW st sbv

  toSW _ _ = error "bindArgs: toSW"


-- | Flattens a schema into the arguments, and result type.
--
-- TODO: What should we do if we encounter something other than a monomorphic
-- type?
flattenSchema :: Schema -> ([Type],Type)

flattenSchema (Forall [] [] ty) = go [] ty
  where
  go is (TCon (TC TCFun) [i, o]) = go (i:is) o
  go is res                      = (reverse is, res)

flattenSchema _ = error "flattenSchema: Unexpected polymorphic schema"


pattern PNum n = TCon (TC (TCNum n)) []
pattern PSeq ty len = TCon (TC TCSeq) [PNum len, ty]
pattern PBit = TCon (TC TCBit) []
pattern i :-> o = TCon (TC TCFun) [i, o]
pattern PWord n = PSeq PBit n


-- Environments ----------------------------------------------------------------

-- | Invariant: the uninterpreted names are a subset of the local names.
data Env = Env
  { envLocal         :: Map QName Value -- ^ global declarations which should be inlined + things that are in a local scope
  , envUninterpreted :: Map QName Value -- ^ declarations which should not be inlined
  , envTypes         :: Map TVar TValue
  }

instance Monoid Env where
  mempty = Env mempty mempty mempty
  mappend e e' = Env (mappend (envLocal         e) (envLocal         e'))
                     (mappend (envUninterpreted e) (envUninterpreted e'))
                     (mappend (envTypes         e) (envTypes         e'))

bindLocalTerm :: QName -> Value -> Env -> Env
bindLocalTerm n v e = e { envLocal = M.insert n v (envLocal e) }

-- | Intended for internal use only, as it can violate the invariant that
-- uninterpreted names are a subset of local names.
bindUninterpretedTerm :: QName -> Value -> Env -> Env
bindUninterpretedTerm n v e = e { envUninterpreted = M.insert n v (envUninterpreted e) }

bindGlobalTerm :: QName
               -> Value -- ^ Function implementation
               -> Value -- ^ Uninterpreted variant
               -> Env -> Env
bindGlobalTerm n v uv = bindLocalTerm n v . bindUninterpretedTerm n uv

bindType :: TVar -> TValue -> Env -> Env
bindType n v e = e { envTypes = M.insert n v (envTypes e) }

lookupLocalTerm :: QName -> Env -> Maybe Value
lookupLocalTerm n e = M.lookup n (envLocal e)

-- | Intended for internal use only (but not dangerous).
lookupUninterpretedTerm :: QName -> Env -> Maybe Value
lookupUninterpretedTerm n e = M.lookup n (envUninterpreted e)

lookupGlobalTerm :: QName -> Env -> Maybe Value
lookupGlobalTerm n e = lookupUninterpretedTerm n e <|> lookupLocalTerm n e

lookupTerm :: QName -> Env -> Value
lookupTerm n e = case lookupGlobalTerm n e of
  Just v  -> v
  Nothing -> panic "CodeGen.SBVC.lookupTerm"
    [ "No term named " ++ show n ++ " in scope" ]


-- Evaluation ------------------------------------------------------------------

evalExpr :: Env -> Expr -> Value
evalExpr = Eval.evalExprGeneric withSBVC

withSBVC :: ExprOperations Env SBool CWord
withSBVC = ExprOperations
  { eoECon       = evalECon
  , eoBindTerm   = bindLocalTerm
  , eoBindType   = bindType
  , eoLookupTerm = lookupTerm
  , eoEvalType   = evalType
  , eoListSel    = evalListSel
  , eoIf         = ite
  , eoPP         = pp
  }

evalType :: Env -> Type -> TValue
evalType env = Eval.evalType (mempty { Eval.envTypes = envTypes env })

evalListSel :: Int -> Value -> Value
evalListSel n (VWord cw) = VBit $ case cw of
  CWord8  w -> sbvTestBit w n
  CWord16 w -> sbvTestBit w n
  CWord32 w -> sbvTestBit w n
  CWord64 w -> sbvTestBit w n
  UnsupportedSize w -> panic "CodeGen.SBVC.evalListSel"
    [ "Trying to index into a word of unsupported size " ++ show w ]
evalListSel n (VSeq _  vs) = vs !! n
evalListSel n (VStream vs) = vs !! n
evalListSel _ v = panic "CodeGen.SBVC.evalListSel"
  [ "Trying to index into a non-list value:", pretty v ]


-- Pretty Printing -------------------------------------------------------------

-- TODO: use hex or WithBase instead, and reflect the bit widths visually
instance PP CWord where
  ppPrec _ cw = case cw of
    CWord8  w -> ppw 8  w
    CWord16 w -> ppw 16 w
    CWord32 w -> ppw 32 w
    CWord64 w -> ppw 64 w
    UnsupportedSize n -> size n
    where
    size n = text $ "<[" ++ show (n :: Int) ++ "]>"
    ppw  n = maybe (size n) (text . show) . unliteral

instance PP (WithBase Value) where
  ppPrec _ (WithBase opts val) = go val where
    go v = case v of
      VRecord fs   -> braces   (sep (punctuate comma (map ppField fs)))
      VTuple vals  -> parens   (sep (punctuate comma (map go    vals)))
      VSeq _ vals  -> brackets (sep (punctuate comma (map go    vals)))
      VBit b       -> ppSBVShow "<Bit>" b
      VWord w      -> pp w
      VStream vals -> brackets $ fsep
                               $ punctuate comma
                               ( take (useInfLength opts) (map go vals)
                                 ++ [text "..."]
                               )
      VFun _       -> text "<function>"
      VPoly _      -> text "<polymorphic value>"

    ppField (f,r) = pp f PP.<+> char '=' PP.<+> go r

instance PP Value where
  ppPrec n v = ppPrec n (WithBase defaultPPOpts v)

-- | Pretty-print literals as their values, and non-literals as some default
-- description (typically their type wrapped in angle brackets).
ppSBVLit :: SymWord a => Doc -> (a -> Doc) -> SBV a -> Doc
ppSBVLit sym lit expr = maybe sym lit (unliteral expr)

ppSBVShow :: (Show a, SymWord a) => String -> SBV a -> Doc
ppSBVShow sym = ppSBVLit (text sym) (text . show)


-- Code Generation -------------------------------------------------------------

dislocate :: P.Expr -> P.Expr
dislocate (P.ELocated v _) = dislocate v
dislocate v = v

location :: P.Expr -> Range
location (P.ELocated _ r) = r
location _ = emptyRange

class CName a where cName :: a -> String

instance CName ModName where
  cName (ModName mods) = intercalate "_" mods

instance CName Name where
  cName (Name s) = s
  cName (NewName pass n) = show pass ++ "_" ++ show n

instance CName QName where
  cName (QName (Just (ModName mods)) name) = intercalate "_" mods ++ "_" ++ cName name
  cName (QName Nothing name) = cName name


-- | Interpret a GenerationRoot, producing code that goes into the given output
-- directory.
codeGen :: Maybe FilePath -- ^ The output directory
        -> T.Root         -- ^ Where to start
        -> ModuleM ()

codeGen outDir (T.FromIdent path qn) =
  do (env,mods) <- cgAllModulesFrom path
     let m    = head mods
         name = cName (mName m)
     io (print name)
     io (compileToCLib outDir (cName qn) (moduleToC env m))

codeGen outDir (T.FromFiles files) = undefined


guardHasDecl :: Module -> QName -> ModuleM ()
guardHasDecl m qn =
  case Base.lookupDecl qn m of
    Just _  -> return ()
    Nothing -> fail $ show $ text "Unable to find" PP.<+> PP.quotes (pp (P.unqual qn))
                         PP.<+> text "in module" PP.<+> PP.quotes (pp (mName m))

-- | Given a module path, produce an environment that can be used for code
-- generation.
cgAllModulesFrom :: FilePath -> ModuleM (Env,[Module])
cgAllModulesFrom path =
  do m    <- Base.loadModuleByPath path
     env  <- getModuleEnv
     let deps = moduleDeps env (mName m)

     return (foldr cgModule mempty deps, deps)

-- | Extend the given environment.
cgModule :: Module -> Env -> Env
cgModule m env
    -- skip the prelude
  | mName m == ModName ["Cryptol"] = env
  | otherwise                      = extEnv m env

moduleToC :: Env -> Module -> [(String,SBVCodeGen ())]
moduleToC env Module { .. } = [ mkDecl d | dg <- mDecls, d <- groupDecls dg ]
  where
  mkDecl Decl { .. } =
    case lookupLocalTerm dName env of
      Just val -> (cName dName, valueToC val)
      Nothing  -> error ("value not in scope: " ++ show dName)

valueToC :: Value -> SBVCodeGen ()
valueToC val =
  do cgGenerateMakefile False
     cgGenerateDriver   False
     _ <- genArgs 0 val
     return ()

genArgs :: Int -> Value -> SBVCodeGen ()

genArgs ix (VFun f) =
  do var <- cgInput ("in" ++ show ix)

     -- TODO: have this type the input based on the actual expected type
     genArgs (ix + 1) (f (VWord (CWord8 var)))

genArgs _ (VWord (CWord8  w)) = cgReturn w
genArgs _ (VWord (CWord16 w)) = cgReturn w
genArgs _ (VWord (CWord32 w)) = cgReturn w
genArgs _ (VWord (CWord64 w)) = cgReturn w

genArgs _ _ =
     fail "unexpected value?"


-- TODO:
-- * put module bindings in the environment
-- * handle pattern match failures
-- codeGen :: Maybe FilePath -> GenerationRoot -> (Module, ModuleEnv) -> IO ()
-- codeGen dir (Identifier id) (mod, modEnv) =
--   case parseExpr id of
--     Right e -> checkExpr e modEnv >>= \resT -> case resT of
--       (Right ((e', schema), modEnv'), []) -> case defaultExpr (location e) e' schema of
--         Just (subst, eMono) -> case apSubst subst schema of
--           Forall [] [] t -> case eMono of
--             EVar qn -> compileToC dir (cName qn) (supplyArgs eMono t)

-- -- TODO
-- supplyArgs :: Expr -> Type -> SBVCodeGen ()
-- supplyArgs = go . evalExpr mempty where
--   go (VWord (CWord8 w)) (PWord 8) = cgOutput "out" w
--   go (VFun f) (PWord 8 :-> t) = cgInput "in" >>= \w -> go (f (VWord (CWord8 w))) t
