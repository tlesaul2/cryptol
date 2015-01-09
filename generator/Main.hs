-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Main where

import CodeGen
import Cryptol.ModuleSystem (loadModuleByPath)
import Cryptol.Utils.PP (pp)
import Cryptol.Version (commitHash, commitBranch, commitDirty)
import Data.List (intercalate)
import Data.Monoid (mconcat)
import Data.String (fromString)
import Data.Version (showVersion)
import OptParser
import Paths_cryptol (version)
import System.Environment (getArgs,getProgName)
import System.Exit (exitFailure)
import System.IO (hPrint, hPutStrLn, stderr)
import System.Console.GetOpt
    (OptDescr(..),ArgOrder(..),ArgDescr(..),getOpt,usageInfo)

data Options = Options
  { optLoad    :: [FilePath]
  , optVersion :: Bool
  , optHelp    :: Bool
  , optDirectory      :: Maybe FilePath
  , optGenerationRoot :: Maybe GenerationRoot
  , optTarget  :: GenerationTarget
  } deriving (Show)

defaultOptions :: Options
defaultOptions  = Options
  { optLoad    = []
  , optVersion = False
  , optHelp    = False
  , optDirectory      = Nothing
  , optGenerationRoot = Nothing
  , optTarget         = SBVC
  }

options :: [OptDescr (OptParser Options)]
options  =
  [ Option "v" ["version"] (NoArg setVersion)
    "display version number"

  , Option "h" ["help"] (NoArg setHelp)
    "display this message"

  , Option "o" ["output-dir"] (ReqArg setDirectory "DIR")
    "output directory for code generation (default stdout)"

  , Option ""  ["root"] (ReqArg setGenerationRoot "UNIT")
    "generate code for the specified identifier, module, file, or directory"

  , Option "t" ["target"] (ReqArg setTarget "BACKEND")
    "code generation backend (default SBV-C)"
  ]

-- | Set a single file to be loaded.  This should be extended in the future, if
-- we ever plan to allow multiple files to be loaded at the same time.
addFile :: String -> OptParser Options
addFile path = modify $ \ opts -> opts { optLoad = [ path ] }

-- | Signal that version should be displayed.
setVersion :: OptParser Options
setVersion  = modify $ \ opts -> opts { optVersion = True }

-- | Signal that help should be displayed.
setHelp :: OptParser Options
setHelp  = modify $ \ opts -> opts { optHelp = True }

-- | Choose a unit for code generation. Heuristic: it's always an identifier.
-- This also signals that code generation should be performed instead of
-- dropping into the REPL.
-- XXX Use a better heuristic.
setGenerationRoot :: String -> OptParser Options
setGenerationRoot id = modify $ \opts -> opts { optGenerationRoot = Just (Identifier id) }

-- | Choose an output directory.
setDirectory :: FilePath -> OptParser Options
setDirectory path = modify $ \opts -> opts { optDirectory = Just path }

-- | Choose a code generation target.
setTarget target = case fromString target of
  Just t  -> modify $ \opts -> opts { optTarget = t }
  Nothing -> report $ "Unknown backend " ++ target ++
                      ". Choices are " ++ intercalate ", " knownTargets

-- | Parse arguments.
parseArgs :: [String] -> Either [String] Options
parseArgs args = case getOpt (ReturnInOrder addFile) options args of
  (ps,[],[]) -> runOptParser defaultOptions (mconcat ps)
  (_,_,errs) -> Left errs

displayHelp :: [String] -> IO ()
displayHelp errs = do
  prog <- getProgName
  let banner = "Usage: " ++ prog ++ " [OPTIONS]"
  putStrLn (usageInfo (unlines errs ++ banner) options)

displayVersion :: IO ()
displayVersion = do
    let ver = showVersion version
    putStrLn ("Cryptol code generator " ++ ver)
    putStrLn ("Git commit " ++ commitHash)
    putStrLn ("    branch " ++ commitBranch ++ dirtyLab)
      where
      dirtyLab | commitDirty = " (non-committed files present during build)"
               | otherwise   = ""

main = do
  args <- getArgs
  case parseArgs args of
    Left errs -> do
      displayHelp errs
      exitFailure

    Right opts
      | optHelp opts    -> displayHelp []
      | optVersion opts -> displayVersion
      | otherwise       -> codeGenFromOpts opts

-- | Precondition: the generation root must be 'Just'.
codeGenFromOpts :: Options -> IO ()
codeGenFromOpts Options
  { optGenerationRoot = Just root
  , optDirectory      = outDir
  , optTarget         = impl
  , optLoad           = inFiles
  } = case inFiles of
  [f] -> loadModuleByPath f >>= either (hPrint stderr . pp) (codeGen outDir root impl) . fst
  _   -> hPutStrLn stderr "Must specify exactly one file to load."
