-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Main where

import CodeGen
import Cryptol.ModuleSystem (loadModuleByPath, initialModuleEnv)
import Cryptol.ModuleSystem.Env (moduleDeps)
import Cryptol.Utils.PP (pp)
import Data.Char (toLower)
import Data.List (intercalate)
import Data.String (fromString)
import Options
import System.Directory (doesFileExist,getDirectoryContents)
import System.FilePath (takeExtension)
import System.IO (hPrint, hPutStrLn, stderr)

data CGOptions = CGOptions
  { optLoad   :: [FilePath]
  , optOutput :: Maybe FilePath
  , optRoot   :: Maybe GenerationRoot
  , optTarget :: GenerationTarget
  } deriving (Show)

argParser :: ArgParser CGOptions
argParser = ArgParser
  { nonOptions  = ReturnInOrder addFile
  , defOptions  = defaultOptions CGOptions
    { optLoad   = []
    , optOutput = Nothing
    , optRoot   = Nothing
    , optTarget = SBVC
    }
  , description = defaultDescription
    [ Option "o" ["output-dir"] (ReqArg setOutput "DIR")
      "output directory for code generation (default stdout)"

    , Option ""  ["root"] (ReqArg setRoot "UNIT")
      "generate code for the specified identifier, module, file, or directory"

    , Option "t" ["target"] (ReqArg setTarget "BACKEND")
      "code generation backend (default SBV-C)"
    ]
  , toolName = "Cryptol Code Generator"
  }

-- | Set a single file to be loaded.  This should be extended in the future, if
-- we ever plan to allow multiple files to be loaded at the same time.
addFile :: String -> OptParser (Options CGOptions)
addFile path = modifyOpt $ \ opts -> opts { optLoad = path : optLoad opts }

-- | Choose a unit for code generation. Heuristic: it's always an identifier.
-- This also signals that code generation should be performed instead of
-- dropping into the REPL.
-- XXX Use a better heuristic.
setRoot :: String -> OptParser (Options CGOptions)
setRoot id = modifyOpt $ \opts -> opts { optRoot = Just (Identifier id) }

-- | Choose an output directory.
setOutput :: FilePath -> OptParser (Options CGOptions)
setOutput path = modifyOpt $ \opts -> opts { optOutput = Just path }

-- | Choose a code generation target.
setTarget :: String -> OptParser (Options CGOptions)
setTarget target = case fromString target of
  Just t  -> modifyOpt $ \opts -> opts { optTarget = t }
  Nothing -> report $ "Unknown backend " ++ target ++
                      ". Choices are " ++ intercalate ", " knownTargets

main :: IO ()
main = getOpts argParser >>= codeGenFromOpts

-- | Precondition: the generation root must be 'Just'.
codeGenFromOpts :: CGOptions -> IO ()
codeGenFromOpts CGOptions
  { optRoot   = Just root
  , optOutput = outDir
  , optTarget = impl
  , optLoad   = inFiles
  } = do
  -- } = case inFiles of
  -- [f] -> do
    codeGen outDir root impl
    -- env <- initialModuleEnv
    -- (modRes, _warnings) <- loadModuleByPath f env
    -- either (hPrint stderr . pp) (codeGen outDir root impl) modRes
  -- _   -> hPutStrLn stderr "Must specify exactly one file to load."
