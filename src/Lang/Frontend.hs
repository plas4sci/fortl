{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
module Lang.Frontend where

import Lang.Options
import Lang.Parser      (parseProgram)
import Lang.PrettyPrint (pprint)
import Lang.Semantics   (interpret, Env)
import Lang.Desugar     (desugar)
import Lang.ExtractPy   (extractProgram)
import Lang.Syntax
import Lang.Types
import Lang.TypeError

import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit
import System.FilePath    (replaceExtension)

import Control.Monad (when)

banner :: String
banner = "fortl v0.2.1 - Programming for science"

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
    ["--help"] -> putStr helpMessage
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
      result <- parseAndCheck True fname
      case result of
        Left _   -> exitFailure
        Right (_, _, _, result, _)  -> do
          putStrLn $ pprint result
          exitSuccess

-- | Parse, desugar and typecheck a fortl file, and if it is well-typed,
-- write out an equivalent Python program.
extractPy :: String -> [String] -> IO ()
extractPy fname rest = do
  result <- parseAndCheck True fname
  case result of
    Left _ -> exitFailure
    Right (parsetree, _, _, _, _) -> do
      let outPath = case rest of
                      (out:_) -> out
                      []      -> replaceExtension fname ".py"
      writeFile outPath (extractProgram (Just fname) parsetree)
      putStrLn $ "Wrote Python translation to " <> outPath
      exitSuccess

parseAndCheck :: Bool -> String -> IO (Either String (Program 'Parsed, [Option], Env, Expr, Context))
parseAndCheck report fname = do
  -- Check if this is a file
  exists <- doesPathExist fname
  if not exists
    then do
      putStrLn $ "File `" <> fname <> "` cannot be found."
      return $ Left "File not found"
    else do
      when report $ putStrLn $ "Checking " <> fname <> "..."
      -- Read the file, parse, and do something...
      input <- readFile fname
      case parseProgram fname input of
        Right (parsetree, options) -> do
          let ast = desugar parsetree
          -- Evaluate
          let (env, normalForm) = interpret options ast
          -- Typing
          case typeInference options ast of
              Left err -> do
                let ?srcFile = fname
                putStrLn $ ansi_bold <> ansi_red
                        <> "Not well-typed.\n" <> errorToString err <> ansi_reset
                return $ Left (errorToString err)
              Right (ctxt, ty) -> do
                putStrLn $ ansi_bold <> ansi_green
                        <> "Well-typed " <> ansi_reset
                        <> ansi_bold <> "as " <> ansi_reset <> pprint ty
                return $ Right (parsetree, options, env, normalForm, ctxt)
        Left msg -> do
          putStrLn $ ansi_red ++ "Error: " ++ ansi_reset ++ msg
          return $ Left msg

typeInference :: [Option] -> Program 'Desugared -> Either TypeError (Context, Type 0)
typeInference options program =
    case synthProgram program of
        Right ty -> Right ty
        Left err -> Left err
ansi_red, ansi_green, ansi_reset, ansi_bold :: String
ansi_red   = "\ESC[31;1m"
ansi_green = "\ESC[32;1m"
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"