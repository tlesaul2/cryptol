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

import Cryptol.REPL.Command (loadCmd,loadPrelude)
import Cryptol.REPL.Monad (REPL,updateREPLTitle,setUpdateREPLTitle,
                   io,prependSearchPath,setSearchPath)
import qualified Cryptol.REPL.Monad as REPL

import REPL.Haskeline (Cryptolrc(..),repl,setREPLTitle)
import REPL.Logo

import Cryptol.Utils.PP(pp,vcat,hang,text)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (splitSearchPath,takeDirectory)

data REPLOptions = REPLOptions
  { optLoad            :: [FilePath]
  , optBatch           :: Maybe FilePath
  , optCryptolrc       :: Cryptolrc
  , optCryptolPathOnly :: Bool
  } deriving (Show)

argParser :: ArgParser REPLOptions
argParser = ArgParser
  { nonOptions  = ReturnInOrder addFile
  , defOptions  = defaultOptions REPLOptions
    { optLoad            = []
    , optBatch           = Nothing
    , optCryptolrc       = CryrcDefault
    , optCryptolPathOnly = False
    }
  , description = defaultDescription
    [ Option "b" ["batch"] (ReqArg setBatchScript "FILE")
      "run the script provided and exit"

    , Option ""  ["ignore-cryptolrc"] (NoArg setCryrcDisabled)
      "disable reading of .cryptolrc files"

    , Option ""  ["cryptolrc-script"] (ReqArg addCryrc "FILE")
      "read additional .cryptolrc files"

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

-- | Disable .cryptolrc files entirely
setCryrcDisabled :: OptParser (Options REPLOptions)
setCryrcDisabled  = modifyOpt $ \ opts -> opts { optCryptolrc = CryrcDisabled }

-- | Add another file to read as a @.cryptolrc@ file, unless @.cryptolrc@
-- files have been disabled
addCryrc :: String -> OptParser (Options REPLOptions)
addCryrc path = modifyOpt $ \ opts ->
  case optCryptolrc opts of
    CryrcDefault  -> opts { optCryptolrc = CryrcFiles [path] }
    CryrcDisabled -> opts
    CryrcFiles xs -> opts { optCryptolrc = CryrcFiles (path:xs) }

setCryptolPathOnly :: OptParser (Options REPLOptions)
setCryptolPathOnly  = modifyOpt $ \opts -> opts { optCryptolPathOnly = True }

main :: IO ()
main  = do
  setLocaleEncoding utf8
  opts <- getOpts argParser
  repl (optCryptolrc opts) (optBatch opts) (setupREPL opts)

setupREPL :: REPLOptions -> REPL ()
setupREPL opts = do
  smoke <- REPL.smokeTest
  case smoke of
    [] -> return ()
    _  -> io $ do
      print (hang (text "Errors encountered on startup; exiting:")
                4 (vcat (map pp smoke)))
      exitFailure
  displayLogo True
  setUpdateREPLTitle setREPLTitle
  updateREPLTitle
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
  case optBatch opts of
    Nothing -> return ()
    -- add the directory containing the batch file to the module search path
    Just file -> prependSearchPath [ takeDirectory file ]
  case optLoad opts of
    []  -> loadPrelude `REPL.catch` \x -> io $ print $ pp x
    [l] -> loadCmd l `REPL.catch` \x -> io $ print $ pp x
    _   -> io $ putStrLn "Only one file may be loaded at the command line."
