module Options
  ( module Options
  , module OptParser
  , ArgOrder(..)
  , ArgDescr(..)
  , OptDescr(..)
  ) where

import OptParser
import Paths_cryptol (version)
import Cryptol.Version (commitHash, commitBranch, commitDirty)
import Data.Version (showVersion)
import Data.Monoid (mconcat)
import System.Environment (getArgs,getProgName)
import System.Exit (exitFailure, exitSuccess)
import System.Console.GetOpt
    (OptDescr(..),ArgOrder(..),ArgDescr(..),getOpt,usageInfo)

data Options a = Options
  { optVersion :: Bool
  , optHelp    :: Bool
  , optExtra   :: a
  } deriving (Show)

defaultOptions :: a -> Options a
defaultOptions a = Options
  { optVersion = False
  , optHelp    = False
  , optExtra   = a
  }

type Description a = [OptDescr (OptParser (Options a))]

defaultDescription :: Description a -> Description a
defaultDescription descr = descr ++
  [ Option "v" ["version"] (NoArg setVersion)
    "display version number"

  , Option "h" ["help"] (NoArg setHelp)
    "display this message"
  ]

-- | Hook for users to modify their custom options.
modifyOpt :: (a -> a) -> OptParser (Options a)
modifyOpt f = modify $ \ opts -> opts { optExtra = f (optExtra opts) }

-- | Signal that version should be displayed.
setVersion :: OptParser (Options a)
setVersion  = modify $ \ opts -> opts { optVersion = True }

-- | Signal that help should be displayed.
setHelp :: OptParser (Options a)
setHelp  = modify $ \ opts -> opts { optHelp = True }

-- | All the information needed to parse an executable's arguments and provide
-- versioning and usage information.
data ArgParser a = ArgParser
  { nonOptions  :: ArgOrder (OptParser (Options a))
  , defOptions  :: Options a
  , description :: Description a
  , toolName    :: String
  }

-- | Parse arguments.
parseArgs :: ArgParser a -> [String] -> Either [String] (Options a)
parseArgs parser args = case getOpt (nonOptions parser) (description parser) args of
  (ps,[],[]) -> runOptParser (defOptions parser) (mconcat ps)
  (_,_,errs) -> Left errs

displayVersion :: ArgParser a -> IO ()
displayVersion parser = do
    let ver = showVersion version
    putStrLn (toolName parser ++ " " ++ ver)
    putStrLn ("Git commit " ++ commitHash)
    putStrLn ("    branch " ++ commitBranch ++ dirtyLab)
      where
      dirtyLab | commitDirty = " (non-committed files present during build)"
               | otherwise   = ""

displayHelp :: ArgParser a -> [String] -> IO ()
displayHelp parser errs = do
  prog <- getProgName
  let banner = "Usage: " ++ prog ++ " [OPTIONS]"
  putStrLn (usageInfo (unlines errs ++ banner) (description parser))

-- | Parse the arguments. Provided there are no parse errors and the user has
-- not requested help or versioning information, return the options.
getOpts :: ArgParser a -> IO a
getOpts parser = do
  args <- getArgs
  case parseArgs parser args of

    Left errs -> do
      displayHelp parser errs
      exitFailure

    Right opts
      | optHelp opts    -> displayHelp parser [] >> exitSuccess
      | optVersion opts -> displayVersion parser >> exitSuccess
      | otherwise       -> return (optExtra opts)
