-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module CodeGen (GenerationRoot(..), GenerationTarget(..), codeGen, knownTargets) where

import Cryptol.ModuleSystem (initialModuleEnv,ModuleError(..))
import Cryptol.ModuleSystem.Base (findModule)
import Cryptol.ModuleSystem.Monad (runModuleM, ModuleM, io, cantFindFile)
import Cryptol.Parser (parseModName,parseQName,parseExpr)
import qualified Cryptol.Parser.AST as P
import Cryptol.TypeCheck.AST
import Cryptol.Utils.PP (text, (<+>), pp)

import CodeGen.Types as Types
import qualified CodeGen.SBVC as SBVC

import Data.Char (toLower)
import Data.Maybe (fromMaybe)
import System.Directory (doesFileExist,getDirectoryContents)
import System.IO
import System.Exit
import System.FilePath (takeExtension)

codeGen :: Maybe FilePath -> GenerationRoot -> GenerationTarget -> IO ()
codeGen dir root impl = inFreshEnv $
  do root' <- checkRoot root
     case impl of
       SBVC -> SBVC.codeGen dir root'
       _    -> fail "This backend is not yet implemented"

inFreshEnv :: ModuleM () -> IO ()
inFreshEnv body =
  do env         <- initialModuleEnv
     (res,warns) <- runModuleM env body
     mapM_ (print . pp) warns
     case res of
       Right (a,_) ->    return ()
       Left err    -> do print (pp err)
                         exitFailure


-- | Check a generation target, resolving identifiers, module names and
-- directories.
checkRoot :: GenerationRoot -> ModuleM Root

-- The identifier must be fully-qualified, so that we know which module it
-- references
checkRoot (Identifier str) =
  case parseQName str of
    Just qn@(QName (Just mn) _) ->
      do path <- findModule mn
         return (FromIdent path qn)

    Nothing -> fail ("Failed to parse identifier: " ++ str)

-- Translate module names into filenames.
checkRoot (Types.Module name) =
  case parseModName name of
    Just mn -> do path <- findModule mn
                  return (FromFiles [path])

    Nothing -> fail ("Failed to parse identifier:" ++ name)

-- Filenames are OK as they are.
checkRoot (File path) =
  do exists <- io (doesFileExist path)
     if exists
        then return (FromFiles [path])
        else cantFindFile path

-- Traverse the provided directory, generating one File target for each entry.
checkRoot (Directory path) =
  do files <- io (getDirectoryContents path)
     return (FromFiles (filter isCryptol files))
  where
  isCryptol file = map toLower (takeExtension file) == "cry"
