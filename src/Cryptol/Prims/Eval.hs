-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Cryptol.Prims.Eval where

import Cryptol.Prims.Syntax (ECon(..))
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..),fromNat,genLog, nMul)
import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Error
import Cryptol.Eval.Type(evalTF)
import Cryptol.Eval.Value
import Cryptol.Testing.Random (randomValue)
import Cryptol.Utils.Compare
import Cryptol.Utils.Panic (panic)

import Data.List (transpose,genericTake,genericReplicate,genericSplitAt,genericIndex)
import Data.Bits (Bits(..))

import System.Random.TF (mkTFGen)


-- Utilities -------------------------------------------------------------------

#if __GLASGOW_HASKELL__ < 706
noNum = panic "Cryptol.Prims.Eval"
          [ "Num instance for Bool shouldn't be used." ]
instance Num Bool where
  _ + _         = noNum
  _ * _         = noNum
  _ - _         = noNum
  negate _      = noNum
  abs _         = noNum
  signum _      = noNum
  fromInteger _ = noNum
#endif

#if __GLASGOW_HASKELL__ < 708
instance Bits Bool where
  (.&.) = (&&)

  (.|.) = (||)

  xor = (/=)

  complement = not

  shift a 0 = a
  shift _ _ = False

  rotate a _ = a

  bitSize _ = 1

  isSigned _ = False

  testBit a 1 = a
  testBit _ _ = False

  bit 0 = True
  bit _ = False

  popCount a = if a then 1 else 0
#endif


-- Primitives ------------------------------------------------------------------

evalECon :: ECon -> Value
evalECon ec = case ec of

  ECFalse       -> VBit False
  ECTrue        -> VBit True
  ECPlus        -> binary (arithBinary (liftBinArith (+)))
  ECMinus       -> binary (arithBinary (liftBinArith (-)))
  ECMul         -> binary (arithBinary (liftBinArith (*)))
  ECDiv         -> binary (arithBinary (liftBinArith divWrap))
  ECMod         -> binary (arithBinary (liftBinArith modWrap))
  ECExp         -> binary (arithBinary (liftBinBV    modExp))
  ECLg2         -> unary  (arithUnary  (liftUnArith  lg2))
  ECNeg         -> unary  (arithUnary  (liftUnArith  negate))
  ECLt          -> binary (cmpOrder lt )
  ECGt          -> binary (cmpOrder gt )
  ECLtEq        -> binary (cmpOrder ngt)
  ECGtEq        -> binary (cmpOrder nlt)
  ECEq          -> binary (cmpOrder eq )
  ECNotEq       -> binary (cmpOrder neq)
  ECMin         -> binary (withOrder ngt)
  ECMax         -> binary (withOrder nlt)
  ECAnd         -> binary (logicBinary (.&.))
  ECOr          -> binary (logicBinary (.|.))
  ECXor         -> binary (logicBinary xor)
  ECCompl       -> unary  (logicUnary complement)
  ECShiftL      -> logicShift shiftLW shiftLS
  ECShiftR      -> logicShift shiftRW shiftRS
  ECRotL        -> logicShift rotateLW rotateLS
  ECRotR        -> logicShift rotateRW rotateRS

  ECDemote -> ecDemoteV

  ECCat -> tlam $ \ front ->
           tlam $ \ back  ->
           tlam $ \ elty  ->
            lam  $ \ l     ->
            lam  $ \ r     -> ccatV front back elty l r

  ECAt          -> indexPrimOne  indexFront
  ECAtRange     -> indexPrimMany indexFrontRange
  ECAtBack      -> indexPrimOne  indexBack
  ECAtRangeBack -> indexPrimMany indexBackRange

  ECFunEq    -> funCmp eq
  ECFunNotEq -> funCmp neq

  ECZero        -> tlam zeroV

  ECJoin -> tlam $ \ parts ->
            tlam $ \ each  ->
            tlam $ \ a     -> lam (joinV parts each a)

  ECSplit -> ecSplitV
  ECSplitAt -> tlam $ \ front ->
               tlam $ \ back  ->
               tlam $ \ a     -> lam (splitAtV front back a)

  ECFromThen   -> fromThenV
  ECFromTo     -> fromToV
  ECFromThenTo -> fromThenToV

  ECInfFrom    ->
    tlam $ \(finTValue -> bits)  ->
     lam $ \(fromWord  -> first) ->
    toStream (map (word bits) [ first .. ])

  ECInfFromThen ->
    tlam $ \(finTValue -> bits)  ->
     lam $ \(fromWord  -> first) ->
     lam $ \(fromWord  -> next)  ->
    toStream [ word bits n | n <- [ first, next .. ] ]

  ECError ->
    tlam $ \_              ->
    tlam $ \_              ->
     lam $ \(fromStr -> s) -> cryUserError s

  ECReverse ->
    tlam $ \a ->
    tlam $ \b ->
     lam $ \(fromSeq -> xs) -> toSeq a b (reverse xs)

  ECTranspose ->
    tlam $ \a ->
    tlam $ \b ->
    tlam $ \c ->
     lam $ \((map fromSeq . fromSeq) -> xs) ->
        case numTValue a of
           Nat 0 ->
             let val = toSeq a c []
             in case numTValue b of
                  Nat n -> toSeq b (tvSeq a c) $ genericReplicate n val
                  Inf   -> VStream $ repeat val
           _ -> toSeq b (tvSeq a c) $ map (toSeq a c) $ transpose xs

  ECPMul ->
    tlam $ \(finTValue -> a) ->
    tlam $ \(finTValue -> b) ->
     lam $ \(fromWord  -> x) ->
     lam $ \(fromWord  -> y) -> word (max 1 (a + b) - 1) (mul 0 x y b)
     where
     mul !res !_ !_ 0 = res
     mul  res bs as n = mul (if even as then res else xor res bs)
                            (bs `shiftL` 1) (as `shiftR` 1) (n-1)

  ECPDiv ->
    tlam $ \(fromInteger . finTValue -> a) ->
    tlam $ \(fromInteger . finTValue -> b) ->
     lam $ \(fromWord  -> x) ->
     lam $ \(fromWord  -> y) -> word (toInteger a)
                                     (fst (divModPoly x a y b))

  ECPMod ->
    tlam $ \(fromInteger . finTValue -> a) ->
    tlam $ \(fromInteger . finTValue -> b) ->
     lam $ \(fromWord  -> x) ->
     lam $ \(fromWord  -> y) -> word (toInteger b)
                                     (snd (divModPoly x a y (b+1)))

  ECRandom ->
    tlam $ \a ->
     lam $ \(fromWord -> x) -> randomV a x


-- | Make a numeric constant.
ecDemoteV :: Value
ecDemoteV = tlam $ \valT ->
            tlam $ \bitT ->
            case (numTValue valT, numTValue bitT) of
              (Nat v, Nat bs) -> VWord (mkBv bs v)
              _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
                       ["Unexpected Inf in constant."
                       , show valT
                       , show bitT
                       ]

--------------------------------------------------------------------------------
divModPoly :: Integer -> Int -> Integer -> Int -> (Integer, Integer)
divModPoly xs xsLen ys ysLen
  | ys == 0   = divideByZero
  | otherwise = go 0 initR (xsLen - degree) todoBits

  where
  downIxes n  = [ n - 1, n - 2 .. 0 ]

  degree      = head [ n | n <- downIxes ysLen, testBit ys n ]

  initR       = xs `shiftR` (xsLen - degree)
  nextR r b   = (r `shiftL` 1) .|. (if b then 1 else 0)

  go !res !r !bitN todo =
     let x = xor r ys
         (res',r') | testBit x degree = (res,             r)
                   | otherwise        = (setBit res bitN, x)
     in case todo of
          b : bs -> go res' (nextR r' b) (bitN-1) bs
          []     -> (res',r')

  todoBits  = map (testBit xs) (downIxes (xsLen - degree))


-- | Create a packed word 
modExp :: Integer -- ^ bit size of the resulting word
       -> Integer -- ^ base
       -> Integer -- ^ exponent
       -> Integer
modExp bits base e
  | bits == 0            = 0
  | base < 0 || bits < 0 = evalPanic "modExp"
                             [ "bad args: "
                             , "  base = " ++ show base
                             , "  e    = " ++ show e
                             , "  bits = " ++ show modulus
                             ]
  | otherwise            = doubleAndAdd base e modulus
  where
  modulus = 0 `setBit` fromInteger bits

doubleAndAdd :: Integer -- ^ base
             -> Integer -- ^ exponent mask
             -> Integer -- ^ modulus
             -> Integer
doubleAndAdd base0 expMask modulus = go 1 base0 expMask
  where
  go acc base k
    | k > 0     = acc' `seq` base' `seq` go acc' base' (k `shiftR` 1)
    | otherwise = acc
    where
    acc' | k `testBit` 0 = acc `modMul` base
         | otherwise     = acc

    base' = base `modMul` base

    modMul x y = (x * y) `mod` modulus



-- Operation Lifting -----------------------------------------------------------

type GenBinary b w = TValue -> GenValue b w -> GenValue b w -> GenValue b w
type Binary = GenBinary Bool BV

binary :: GenBinary b w -> GenValue b w
binary f = tlam $ \ ty ->
            lam $ \ a  ->
            lam $ \ b  -> f ty a b

type GenUnary b w = TValue -> GenValue b w -> GenValue b w
type Unary = GenUnary Bool BV

unary :: GenUnary b w -> GenValue b w
unary f = tlam $ \ ty ->
           lam $ \ a  -> f ty a


-- Arith -----------------------------------------------------------------------

-- | Turn a binop on Integers that understands widths into one that can handle
-- bitvectors.
liftBinBV :: (Integer -> BinOp Integer) -> (Integer -> BinOp BV)
liftBinBV op w l r = mkBv w (op w (fromBV l) (fromBV r))

liftUnBV :: (Integer -> UnOp Integer) -> (Integer -> UnOp BV)
liftUnBV op w x = mkBv w (op w (fromBV x))

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
liftBinArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftBinArith op = liftBinBV (\_ -> op)

type BinOp w = w -> w -> w
type BinArith w = Integer -> BinOp w

pointwiseBinary :: BitWord b w => BinOp b -> (Integer -> BinOp w) -> GenBinary b w
pointwiseBinary bop op = loop . toTypeVal
  where
  loop ty l r = case ty of
    TVBit         -> VBit (bop (fromVBit l) (fromVBit r))
    TVSeq w TVBit -> VWord (op w (fromVWord l) (fromVWord r))
    TVSeq _ t     -> VSeq False (zipWith (loop t) (fromSeq l) (fromSeq r))
    TVStream t    -> toStream (zipWith (loop t) (fromSeq l) (fromSeq r))
    TVTuple ts    -> VTuple (zipWith3 loop ts (fromVTuple l) (fromVTuple r))
    TVRecord fs   -> VRecord [ (f, loop fty (lookupRecord f l) (lookupRecord f r))
                             | (f, fty) <- fs ]
    TVFun _ t     -> lam $ \ x -> loop t (fromVFun l x) (fromVFun r x)

arithBinary :: BitWord b w => BinArith w -> GenBinary b w
arithBinary = pointwiseBinary (evalPanic "arithBinary" ["Invalid arguments"])

-- | Turn a normal unop on Integers into one that understands bitvectors.
liftUnArith :: (Integer -> Integer) -> UnArith BV
liftUnArith op w = mkBv w . op . fromBV

type UnOp w = w -> w
type UnArith w = Integer -> w -> w

pointwiseUnary :: BitWord b w => UnOp b -> (Integer -> UnOp w) -> GenUnary b w
pointwiseUnary bop op = loop . toTypeVal
  where
  loop ty x = case ty of
    TVBit         -> VBit (bop (fromVBit x))
    TVSeq w TVBit -> VWord (op w (fromVWord x))
    TVSeq _ t     -> VSeq False (map (loop t) (fromSeq x))
    TVStream t    -> toStream (map (loop t) (fromSeq x))
    TVTuple ts    -> VTuple (zipWith loop ts (fromVTuple x))
    TVRecord fs   -> VRecord [ (f, loop fty (lookupRecord f x))
                             | (f, fty) <- fs ]
    TVFun _ t     -> lam $ \ y -> loop t (fromVFun x y)

arithUnary :: BitWord b w => UnArith w -> GenUnary b w
arithUnary = pointwiseUnary (evalPanic "arithUnary" ["Invalid arguments"])

lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0

divWrap :: Integral a => a -> a -> a
divWrap _ 0 = divideByZero
divWrap x y = x `div` y

modWrap :: Integral a => a -> a -> a
modWrap _ 0 = divideByZero
modWrap x y = x `mod` y

-- Cmp -------------------------------------------------------------------------

cmpOrder :: Comparable (GenValue b w) o
         => (o -> b) -> TValue -> GenValue b w -> GenValue b w -> GenValue b w
cmpOrder op _ty l r = VBit (op (cmp l r))

withOrder :: (Comparable (GenValue b w) o, Conditional b (GenValue b w))
          => (o -> b) -> TValue -> GenValue b w -> GenValue b w -> GenValue b w
withOrder op _ty l r = cond (op (cmp l r)) l r

funCmp :: Comparable (GenValue b w) o => (o -> b) -> GenValue b w
funCmp op =
  tlam $ \ _a ->
  tlam $ \  b ->
   lam $ \  l ->
   lam $ \  r ->
   lam $ \  x -> cmpOrder op b (fromVFun l x) (fromVFun r x)


-- Logic -----------------------------------------------------------------------

zeroV :: TValue -> Value
zeroV ty

  -- bits
  | isTBit ty =
    VBit False

  -- sequences
  | Just (n,ety) <- isTSeq ty =
    toSeq n ety $ case numTValue n of
                    Nat w -> replicate (fromInteger w) (zeroV ety)
                    Inf   -> repeat                    (zeroV ety)

  -- functions
  | Just (_,bty) <- isTFun ty =
    lam (\ _ -> zeroV bty)

  -- tuples
  | Just (_,tys) <- isTTuple ty =
    VTuple (map zeroV tys)

  -- records
  | Just fields <- isTRec ty =
    VRecord [ (f,zeroV fty) | (f,fty) <- fields ]

  | otherwise = evalPanic "zeroV" ["invalid type for zero"]

-- | Join a sequence of sequences into a single sequence.
joinV :: TValue -> TValue -> TValue -> Value -> Value
joinV parts each a val =
  let len = toNumTValue (numTValue parts `nMul` numTValue each)
  in toSeq len a (concatMap fromSeq (fromSeq val))

splitAtV :: TValue -> TValue -> TValue -> Value -> Value
splitAtV front back a val =
  case numTValue back of

    -- remember that words are big-endian in cryptol, so the masked portion
    -- needs to be first, assuming that we're on a little-endian machine.
    Nat rightWidth | aBit ->
      let i          = fromWord val
       in VTuple [ word leftWidth (i `shiftR` fromInteger rightWidth)
                 , word rightWidth i ]

    _ ->
      let (ls,rs) = splitAt (fromInteger leftWidth) (fromSeq val)
       in VTuple [VSeq aBit ls, toSeq back a rs]

  where

  aBit = isTBit a

  leftWidth = case numTValue front of
    Nat n -> n
    _     -> evalPanic "splitAtV" ["invalid `front` len"]


-- | Split implementation.
ecSplitV :: Value
ecSplitV =
  tlam $ \ parts ->
  tlam $ \ each  ->
  tlam $ \ a     ->
  lam  $ \ val ->
  let mkChunks f = map (toFinSeq a) $ f $ fromSeq val
  in case (numTValue parts, numTValue each) of
       (Nat p, Nat e) -> VSeq False $ mkChunks (finChunksOf p e)
       (Inf  , Nat e) -> toStream   $ mkChunks (infChunksOf e)
       _              -> evalPanic "splitV" ["invalid type arguments to split"]

-- | Split into infinitely many chunks
infChunksOf :: Integer -> [a] -> [[a]]
infChunksOf each xs = let (as,bs) = genericSplitAt each xs
                      in as : infChunksOf each bs

-- | Split into finitely many chunks
finChunksOf :: Integer -> Integer -> [a] -> [[a]]
finChunksOf 0 _ _ = []
finChunksOf parts each xs = let (as,bs) = genericSplitAt each xs
                            in as : finChunksOf (parts - 1) each bs


ccatV :: TValue -> TValue -> TValue -> Value -> Value -> Value
ccatV front back elty l r =
  toSeq (evalTF TCAdd [front,back]) elty (fromSeq l ++ fromSeq r)

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: (forall a. Bits a => a -> a -> a) -> Binary
logicBinary op = pointwiseBinary op (liftBinBV (\_ -> op))

logicUnary :: (forall a. Bits a => a -> a) -> Unary
logicUnary op = pointwiseUnary op (liftUnBV (\_ -> op))


logicShift :: (Integer -> Integer -> Int -> Integer)
              -- ^ the Integer value (argument 2) may contain junk bits, but the
              -- Int (argument 3) will always be clean
           -> (TValue -> TValue -> [Value] -> Int -> [Value])
           -> Value
logicShift opW opS
  = tlam $ \ a ->
    tlam $ \ _ ->
    tlam $ \ c ->
     lam  $ \ l ->
     lam  $ \ r ->
        if isTBit c
          then -- words
            let BV w i  = fromVWord l
            in VWord (BV w (opW w i (fromInteger (fromWord r))))

          else toSeq a c (opS a c (fromSeq l) (fromInteger (fromWord r)))

-- Left shift for words.
shiftLW :: Integer -> Integer -> Int -> Integer
shiftLW w ival by
  | toInteger by >= w = 0
  | otherwise         = shiftL ival by

shiftLS :: TValue -> TValue -> [Value] -> Int -> [Value]
shiftLS w ety vs by =
  case numTValue w of
    Nat len
      | toInteger by < len -> genericTake len (drop by vs ++ repeat (zeroV ety))
      | otherwise          -> genericReplicate len (zeroV ety)
    Inf                    -> drop by vs

shiftRW :: Integer -> Integer -> Int -> Integer
shiftRW w i by
  | toInteger by >= w = 0
  | otherwise         = shiftR (mask w i) by

shiftRS :: TValue -> TValue -> [Value] -> Int -> [Value]
shiftRS w ety vs by =
  case numTValue w of
    Nat len
      | toInteger by < len -> genericTake len (replicate by (zeroV ety) ++ vs)
      | otherwise          -> genericReplicate len (zeroV ety)
    Inf                    -> replicate by (zeroV ety) ++ vs

-- XXX integer doesn't implement rotateL, as there's no bit bound
rotateLW :: Integer -> Integer -> Int -> Integer
rotateLW 0 i _  = i
rotateLW w i by = (i `shiftL` b) .|. (mask w i `shiftR` (fromInteger w - b))
  where b = by `mod` fromInteger w


rotateLS :: TValue -> TValue -> [Value] -> Int -> [Value]
rotateLS w _ vs at =
  case numTValue w of
    Nat len -> let at'     = toInteger at `mod` len
                   (ls,rs) = genericSplitAt at' vs
                in rs ++ ls
    _ -> panic "Cryptol.Eval.Prim.rotateLS" [ "unexpected infinite sequence" ]

-- XXX integer doesn't implement rotateR, as there's no bit bound
rotateRW :: Integer -> Integer -> Int -> Integer
rotateRW 0 i _  = i
rotateRW w i by = (mask w i `shiftR` b) .|. (i `shiftL` (fromInteger w - b))
  where b = by `mod` fromInteger w

rotateRS :: TValue -> TValue -> [Value] -> Int -> [Value]
rotateRS w _ vs at =
  case numTValue w of
    Nat len -> let at'     = toInteger at `mod` len
                   (ls,rs) = genericSplitAt (len - at') vs
                in rs ++ ls
    _ -> panic "Cryptol.Eval.Prim.rotateRS" [ "unexpected infinite sequence" ]


-- Sequence Primitives ---------------------------------------------------------

-- | Indexing operations that return one element.
indexPrimOne :: (Maybe Integer -> [Value] -> Integer -> Value) -> Value
indexPrimOne op =
  tlam $ \ n  ->
  tlam $ \ _a ->
  tlam $ \ _i ->
   lam $ \ l  ->
   lam $ \ r  ->
     let vs  = fromSeq l
         ix  = fromWord r
      in op (fromNat (numTValue n)) vs ix

indexFront :: Maybe Integer -> [Value] -> Integer -> Value
indexFront mblen vs ix =
  case mblen of
    Just len | len <= ix -> invalidIndex ix
    _                    -> genericIndex vs ix

indexBack :: Maybe Integer -> [Value] -> Integer -> Value
indexBack mblen vs ix =
  case mblen of
    Just len | len > ix  -> genericIndex vs (len - ix - 1)
             | otherwise -> invalidIndex ix
    Nothing              -> evalPanic "indexBack"
                            ["unexpected infinite sequence"]

-- | Indexing operations that return many elements.
indexPrimMany :: (Maybe Integer -> [Value] -> [Integer] -> [Value]) -> Value
indexPrimMany op =
  tlam $ \ n  ->
  tlam $ \ a  ->
  tlam $ \ m  ->
  tlam $ \ _i ->
   lam $ \ l  ->
   lam $ \ r  ->
     let vs    = fromSeq l
         ixs   = map fromWord (fromSeq r)
     in toSeq m a (op (fromNat (numTValue n)) vs ixs)

indexFrontRange :: Maybe Integer -> [Value] -> [Integer] -> [Value]
indexFrontRange mblen vs = map (indexFront mblen vs)

indexBackRange :: Maybe Integer -> [Value] -> [Integer] -> [Value]
indexBackRange mblen vs = map (indexBack mblen vs)

-- @[ 0, 1 .. ]@
fromThenV :: Value
fromThenV  =
  tlamN $ \ first ->
  tlamN $ \ next  ->
  tlamN $ \ bits  ->
  tlamN $ \ len   ->
    case (first, next, len, bits) of
      (_         , _        , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat next', Nat len', Nat bits') ->
        let nums = enumFromThen first' next'
         in VSeq False (genericTake len' (map (VWord . BV bits') nums))
      _ -> evalPanic "fromThenV" ["invalid arguments"]

-- @[ 0 .. 10 ]@
fromToV :: Value
fromToV  =
  tlamN $ \ first ->
  tlamN $ \ lst   ->
  tlamN $ \ bits  ->
    case (first, lst, bits) of
      (_         , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat lst', Nat bits') ->
        let nums = enumFromThenTo first' (first' + 1) lst'
            len  = 1 + (lst' - first')
         in VSeq False (genericTake len (map (VWord . BV bits') nums))

      _ -> evalPanic "fromThenV" ["invalid arguments"]

-- @[ 0, 1 .. 10 ]@
fromThenToV :: Value
fromThenToV  =
  tlamN $ \ first ->
  tlamN $ \ next  ->
  tlamN $ \ lst   ->
  tlamN $ \ bits  ->
  tlamN $ \ len   ->
    case (first, next, lst, len, bits) of
      (_         , _        , _       , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat next', Nat lst', Nat len', Nat bits') ->
        let nums = enumFromThenTo first' next' lst'
         in VSeq False (genericTake len' (map (VWord . BV bits') nums))

      _ -> evalPanic "fromThenV" ["invalid arguments"]

-- Random Values ---------------------------------------------------------------

-- | Produce a random value with the given seed. If we do not support
-- making values of the given type, return zero of that type.
-- TODO: do better than returning zero
randomV :: TValue -> Integer -> Value
randomV ty seed =
  case randomValue (tValTy ty) of
    Nothing -> zeroV ty
    Just gen -> fst $ gen 100 $ mkTFGen (fromIntegral seed)


-- Miscellaneous ---------------------------------------------------------------

tlamN :: (Nat' -> GenValue b w) -> GenValue b w
tlamN f = VPoly (\x -> f (numTValue x))
