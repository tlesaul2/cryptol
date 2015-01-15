-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Safe #-}

module Cryptol.Utils.Compare.Class where

-- $seefulldocs
-- See "Cryptol.Utils.Compare" for full documentation.

class Comparable value order | value -> order where
  -- | A generalization of 'compare'.
  cmp :: value -> value -> order

instance Comparable Bool Ordering where cmp = cmpOrd

-- | A default implementation of 'cmp' for 'Ord' instances.
cmpOrd :: Ord a => a -> a -> Ordering
cmpOrd = compare

class Comparison order bool | order -> bool where
  lt, eq, gt, nlt, neq, ngt :: order -> bool

instance Comparison Ordering Bool where
  lt  = (==LT)
  eq  = (==EQ)
  gt  = (==GT)
  nlt = (/=LT)
  neq = (/=EQ)
  ngt = (/=GT)
