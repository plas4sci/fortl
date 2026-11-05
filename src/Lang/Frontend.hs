{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE BangPatterns #-}
module Lang.Frontend where

import Lang.Options
import Lang.Parser      (parseProgram)
import Lang.PrettyPrint (pprint)
import Lang.Semantics   (interpret, Env, Value)
import Lang.Desugar     (desugar)
import Lang.Syntax
import Lang.Types
import Lang.TypeError

import System.Directory (getCurrentDirectory, doesFileExist)
import System.FilePath ((</>), (<.>), takeExtension)
import GHC.IO.Exception (IOErrorType(..), ioe_type)

import Control.Monad (when)
import Control.Exception (try, IOException)

banner :: String
banner = "cosi v0.4.0 - Code with Scientific Intent"

-- | Resolve a source file name, allowing the @.cosi@ extension to be omitted:
-- if @fname@ does not exist but @fname.cosi@ does, use the latter.
resolveSourceFile :: FilePath -> IO FilePath
resolveSourceFile fname = do
  exists <- doesFileExist fname
  if exists || takeExtension fname == sourceExtension
    then return fname
    else do
      let withExt = fname <.> sourceExtension
      existsWithExt <- doesFileExist withExt
      return $ if existsWithExt then withExt else fname

sourceExtension :: String
sourceExtension = ".cosi"

tryReadFile :: FilePath -> IO (Either IOException String)
tryReadFile path = try $ do
  !contents <- readFile path
  return contents

run :: Bool -> String -> IO (Either String (Program 'Parsed, [Option], Env, Value, Context))
run report fname0 = do
  fname <- resolveSourceFile fname0
  currentDir <- getCurrentDirectory
  let path = currentDir </> fname
  result <- tryReadFile path
  case result of
    Right contents -> do
      when report $ putStrLn $ "Checking " <> fname <> " (Full path:" <> path <> ") ..."
      case parseProgram fname contents of
        Right (parsetree, options) -> do
          case desugar parsetree of
            Left err -> do
              let ?srcFile = fname
              putStrLn $ ansi_bold <> ansi_red
                      <> "Not well-formed.\n" <> errorToString err <> ansi_reset
              return $ Left (errorToString err)
            Right ast -> do
              -- Typing
              case typeCheck options ast of
                Left err -> do
                  let ?srcFile = fname
                  putStrLn $ ansi_bold <> ansi_red
                    <> "Not well-typed.\n" <> errorToString err <> ansi_reset
                  return $ Left (errorToString err)
                Right (ctxt, ty) -> do
                  -- Evaluate
                  let (env, normalForm) = interpret options ast

                  putStrLn $ ansi_bold <> ansi_green
                    <> "Well-typed " <> ansi_reset
                    <> ansi_bold <> "as " <> ansi_reset <> pprint ty

                  return $ Right (parsetree, options, env, normalForm, ctxt)
        Left msg -> do
          putStrLn $ ansi_red ++ "Error: " ++ ansi_reset ++ msg
          return $ Left msg
    Left e -> do
      case ioe_type e of
        NoSuchThing -> do
          let alsoTried
                | takeExtension fname /= sourceExtension
                    = " (also tried `" <> (fname <.> sourceExtension) <> "`)"
                | otherwise = ""
          putStrLn $ "File `" <> fname <> "` (Full path:" <> path <> ") cannot be found" <> alsoTried <> "."
          return $ Left "File not found"
        _ -> do
          let msg = show e
          putStrLn msg
          return $ Left msg

typeCheck :: [Option] -> Program 'Desugared -> Either TypeError (Context, Type 0)
typeCheck options program =
    case typeCheckProgram program of
        Right ty -> Right ty
        Left err -> Left err

ansi_red, ansi_green, ansi_reset, ansi_bold :: String
ansi_red   = "\ESC[31;1m"
ansi_green = "\ESC[32;1m"
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
