-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import Options

import REPL.Command (loadCmd,loadPrelude)
import REPL.Haskeline
import REPL.Monad (REPL,setREPLTitle,io,DotCryptol(..),
                   prependSearchPath,setSearchPath)
import REPL.Logo
import qualified REPL.Monad as REPL

import Cryptol.Utils.PP(pp)

import System.Environment (lookupEnv)
import System.FilePath (splitSearchPath)

data REPLOptions = REPLOptions
  { optLoad            :: [FilePath]
  , optBatch           :: Maybe FilePath
  , optDotCryptol      :: DotCryptol
  , optCryptolPathOnly :: Bool
  } deriving (Show)

argParser :: ArgParser REPLOptions
argParser = ArgParser
  { nonOptions  = ReturnInOrder addFile
  , defOptions  = defaultOptions REPLOptions
    { optLoad            = []
    , optBatch           = Nothing
    , optDotCryptol      = DotCDefault
    , optCryptolPathOnly = False
    }
  , description = defaultDescription
    [ Option "b" ["batch"] (ReqArg setBatchScript "FILE")
      "run the script provided and exit"

    , Option ""  ["ignore-dot-cryptol"] (NoArg setDotCDisabled)
      "disable reading of .cryptol files"

    , Option ""  ["cryptol-script"] (ReqArg addDotC "FILE")
      "read additional .cryptol files"

    , Option ""  ["cryptolpath-only"] (NoArg setCryptolPathOnly)
      "only look for .cry files in CRYPTOLPATH; don't use built-in locations"
    ]
  , toolName = "Cryptol"
  }

-- | Set a single file to be loaded.  This should be extended in the future, if
-- we ever plan to allow multiple files to be loaded at the same time.
addFile :: String -> OptParser (Options REPLOptions)
addFile path = modifyOpt $ \ opts -> opts { optLoad = [ path ] }

-- | Set a batch script to be run.
setBatchScript :: String -> OptParser (Options REPLOptions)
setBatchScript path = modifyOpt $ \ opts -> opts { optBatch = Just path }

-- | Disable .cryptol files entirely
setDotCDisabled :: OptParser (Options REPLOptions)
setDotCDisabled  = modifyOpt $ \ opts -> opts { optDotCryptol = DotCDisabled }

-- | Add another file to read as a .cryptol file, unless .cryptol
-- files have been disabled
addDotC :: String -> OptParser (Options REPLOptions)
addDotC path = modifyOpt $ \ opts ->
  case optDotCryptol opts of
    DotCDefault  -> opts { optDotCryptol = DotCFiles [path] }
    DotCDisabled -> opts
    DotCFiles xs -> opts { optDotCryptol = DotCFiles (path:xs) }

setCryptolPathOnly :: OptParser (Options REPLOptions)
setCryptolPathOnly  = modifyOpt $ \opts -> opts { optCryptolPathOnly = True }

main :: IO ()
main  = do
  opts <- getOpts argParser
  repl (optDotCryptol opts) (optBatch opts) (setupREPL opts)

setupREPL :: REPLOptions -> REPL ()
setupREPL opts = do
  displayLogo True
  setREPLTitle
  mCryptolPath <- io $ lookupEnv "CRYPTOLPATH"
  case mCryptolPath of
    Nothing -> return ()
    Just path | optCryptolPathOnly opts -> setSearchPath path'
              | otherwise               -> prependSearchPath path'
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
      -- Windows paths search from end to beginning
      where path' = reverse (splitSearchPath path)
#else
      where path' = splitSearchPath path
#endif
  case optLoad opts of
    []  -> loadPrelude `REPL.catch` \x -> io $ print $ pp x
    [l] -> loadCmd l `REPL.catch` \x -> io $ print $ pp x
    _   -> io $ putStrLn "Only one file may be loaded at the command line."
