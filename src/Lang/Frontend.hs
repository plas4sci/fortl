{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE BangPatterns #-}
module Lang.Frontend where

import Lang.Options
import Lang.Parser      (parseProgram)
import Lang.PrettyPrint (pprint)
import Lang.Semantics   (interpret, Env, Value)
import Lang.Desugar     (desugar)
import Lang.ExtractPy   (extractProgram)
import Lang.Syntax
import Lang.Types
import Lang.TypeError

import System.Directory (getCurrentDirectory)
import System.Environment (getArgs)
import System.Exit
import System.FilePath    ((</>), replaceExtension)
import GHC.IO.Exception   (IOErrorType(..), ioe_type)

import Control.Monad (when)
import Control.Exception (try, IOException)

banner :: String
banner = "fortl v0.3.0 - Programming for science"

helpMessage :: String
helpMessage = unlines
  [ "Usage: fortl <filename>"
  , "       fortl <filename> --extract-py [output.py]"
  , "       fortl --help"
  ]

main :: IO ()
main = do
  putStrLn banner
  args <- getArgs
  -- Get command line args
  case args of
    [] -> putStrLn "Please supply a filename as a command line argument"
    ("--help":_) -> putStr helpMessage
    -- `--extract-py` may appear anywhere among the arguments, e.g.
    -- `fortl --extract-py file.frtl` or `fortl file.frtl --extract-py`
    _ | "--extract-py" `elem` args ->
          case filter (/= "--extract-py") args of
            []           -> do
              putStrLn "Please supply a filename to extract"
              exitFailure
            (fname:rest) -> extractPy fname rest
    -- If we have at least one
    (fname:_) -> do
      result <- run True fname
      case result of
        Left _   -> exitFailure
        Right (_, _, _, result, _)  -> do
          putStrLn $ pprint result
          exitSuccess

-- | Parse, desugar and typecheck a fortl file, and if it is well-typed,
-- write out an equivalent Python program.
extractPy :: String -> [String] -> IO ()
extractPy fname rest = do
  result <- run True fname
  case result of
    Left _ -> exitFailure
    Right (parsetree, _, _, _, _) -> do
      let outPath = case rest of
                      (out:_) -> out
                      []      -> replaceExtension fname ".py"
      writeFile outPath (extractProgram (Just fname) parsetree)
      putStrLn $ "Wrote Python translation to " <> outPath
      exitSuccess

tryReadFile :: FilePath -> IO (Either IOException String)
tryReadFile path = try $ do
  !contents <- readFile path
  return contents

run :: Bool -> String -> IO (Either String (Program 'Parsed, [Option], Env, Value, Context))
run report fname = do
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
          putStrLn $ "File `" <> fname <> "` (Full path:" <> path <> ") cannot be found."
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
