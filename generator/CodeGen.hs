-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module CodeGen (GenerationRoot(..), GenerationTarget(..), codeGen, knownTargets) where

import Cryptol.ModuleSystem
import Cryptol.TypeCheck.AST

import CodeGen.Types
import qualified CodeGen.SBVC as SBVC

import System.IO
import System.Exit

codeGen :: Maybe FilePath -> GenerationRoot -> GenerationTarget -> (Module, ModuleEnv) -> IO ()
codeGen dir root impl m = case impl of
  SBVC -> SBVC.codeGen dir root m
  _    -> do
    hPutStrLn stderr "This backend is not yet implemented."
    exitFailure
