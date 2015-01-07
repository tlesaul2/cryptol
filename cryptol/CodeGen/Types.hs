-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleInstances #-}

module CodeGen.Types where

import Data.Char
import Data.String

data GenerationRoot
  = Identifier String
  | Module     String
  | File       FilePath
  | Directory  FilePath
  deriving (Eq, Ord, Read, Show)

data GenerationTarget = SBVC | SV | BSV | Verilog
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

instance IsString (Maybe GenerationTarget) where
  fromString = flip lookup targetMapping
             . map toLower
             . filter isAlpha

-- | A mapping from public-facing human-readable strings to the internal
-- representation of possible codegen targets. The 'IsString' instance for
-- 'GenerationTarget' assumes that the 'String's here contain characters
-- satisfying @isLower@ and @isAlpha@.
targetMapping :: [(String, GenerationTarget)]
targetMapping = [("sbvc", SBVC), ("sv", SV), ("bsv", BSV), ("verilog", Verilog)]

-- | 'String' versions of the 'GenerationTarget' values.
knownTargets :: [String]
knownTargets = map fst targetMapping
