-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Cryptol.Utils.Compare
  ( -- $summary
    Comparable(..)
  , cmpOrd, cmpOrdSymbolic
  , Comparison(..)
  , Conditional(..)
  , OrderingSymbolic
  ) where

-- The class definitions are split into a separate module so that they can be
-- marked with the Safe language extension.
import Cryptol.Utils.Compare.Class
import Data.Monoid
import Data.SBV

-- $summary
-- This is a generalization of the standard 'Ord' typeclass and the
-- SBV-specific 'OrdSymbolic' typeclass. There are some concerns being met by
-- this API design:
--
-- 1. The 'compare' function from the 'Ord' typeclass is nice for efficiency:
--    it enables instances for container types to traverse contained values
--    just once in a given comparison (and not, say, once to check the @(<)@
--    condition and once to check the @(==)@ condition).
-- 2. The interface of 'OrdSymbolic' includes only the boolean-valued
--    comparison operations (like @<@, @<=@, @==@, etc.). This is nice for SMT
--    solvers, which typically understand comparison operations but do not have
--    an analog of 'compare'.
-- 3. To the extent possible, when performing symbolic comparisons, we would
--    like to use the full gamut of comparison operations available to keep the
--    produced formulas small. This reduces load on human and machine readers
--    of the formulas alike.
--
-- To that end, we export separate classes for doing comparison traversals and
-- for turning traversals into boolean-like values.

instance Comparable SBool OrderingSymbolic where
  cmp = cmpOrdSymbolic

-- | A default implementation of 'cmp' for 'OrdSymbolic' instances.
cmpOrdSymbolic :: OrdSymbolic a => a -> a -> OrderingSymbolic
cmpOrdSymbolic x y = OrderingSymbolic (x .< y) (x .<= y) (x .== y) (x ./= y)

instance Comparison OrderingSymbolic SBool where
  lt    = isLT
  eq    = isEQ
  gt    = bnot . isNGT
  nlt   = bnot . isLT
  neq   = isNEQ
  ngt   = isNGT

instance Mergeable a => Conditional SBool a where
  cond = ite

-- TODO: Just go ahead and track all six conditions, so there's no need for the
-- comment about lt/gt and nlt/ngt.
-- | An analog of 'Ordering' for SBV. There is no good way to create a value of
-- type @SBV Ordering@, so we fake it by tracking an @SBV Bool@ for a couple
-- possible queries against 'Ordering's -- just enough such queries to form
-- efficient symbolic computations for each.
--
-- When using the 'Comparison' instance, @lt (cmp y x)@ will produce slightly
-- smaller formulas than @gt (cmp x y)@, and @ngt@ is similarly slightly better
-- than @nlt@.
data OrderingSymbolic = OrderingSymbolic { isLT, isNGT, isEQ, isNEQ :: SBool }
-- | See also the 'Monoid' instance for 'Ordering'.
instance Monoid OrderingSymbolic where
  mempty = OrderingSymbolic false true true false
  mappend x y = OrderingSymbolic (isLT  x ||| (isEQ  x &&& isLT  y))
                                 (isNGT x &&& (isNEQ x ||| isNGT y))
                                 (isEQ  x &&&  isEQ  y)
                                 (isNEQ x |||  isNEQ y)
