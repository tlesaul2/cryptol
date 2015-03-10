module GitRev.TH where

import Control.Applicative
import Control.Exception
import Control.Monad
import Data.Maybe
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import System.Directory
import System.FilePath
import System.Process

-- | Run git with the given arguments and no stdin, returning the
-- stdout output. If git isn't available or something goes wrong,
-- return the second argument.
runGit :: [String] -> String -> Q String
runGit args def = do
  let oops :: SomeException -> IO String
      oops _e = return def
  gitFound <- runIO $ isJust <$> findExecutable "git"
  if gitFound
    then do
      pwd <- runIO $ getCurrentDirectory
      let index = pwd </> ".git" </> "index"
      indexExists <- runIO $ doesFileExist index
      when indexExists $ addDependentFile index
      runIO $ (takeWhile (/= '\n') <$> readProcess "git" args "") `catch` oops
    else return def

getHash :: ExpQ
getHash =
  stringE =<< runGit ["rev-parse", "HEAD"] "UNKNOWN"

getBranch :: ExpQ
getBranch =
  stringE =<< runGit ["rev-parse", "--abbrev-ref", "HEAD"] "UNKNOWN"

getDirty :: ExpQ
getDirty = do
  output <- runGit ["status", "--porcelain"] ""
  case output of
    "" -> conE $ mkName "Prelude.False"
    _  -> conE $ mkName "Prelude.True"
