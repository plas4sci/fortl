module Lang.Frontend where

import Lang.Options
import Lang.Parser      (parseProgram)
import Lang.PrettyPrint (pprint)
import Lang.Semantics   (multiStep)
import Lang.Syntax
import qualified Lang.HindleyMilner as HM
import Lang.Types

import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit

main :: IO ()
main = do
  args <- getArgs
  -- Get command line args
  case args of
    [] -> putStrLn "Please supply a filename as a command line argument"
    -- If we have at least one
    (fname:_) -> do
      result <- run fname
      case result of
        Left _   -> exitFailure
        Right _  -> exitSuccess

run :: String -> IO (Either String (Expr PCF))
run fname = do
  -- Check if this is a file
  exists <- doesPathExist fname
  if not exists
    then do
      putStrLn $ "File `" <> fname <> "` cannot be found."
      return $ Left "File not found."
    else do
      -- Read the file, parse, and do something...
      input <- readFile fname
      case parseProgram fname input of
        Right (ast, options) -> do
          -- Show options
          putStrLn $ "\n " <> ansi_bold <> "Reducer: " <> ansi_reset <> (showReducer options)

          -- Show AST
          putStrLn $ "\n " <> ansi_bold <> "AST: " <> ansi_reset <> show ast

          -- Pretty print
          putStrLn $ "\n " <> ansi_bold <> "Pretty: " <> ansi_reset <> pprint ast

          -- Evaluate
          let (normalForm, count) = multiStep options ast
          putStrLn $ "\n " <> ansi_bold <> "Number of steps: " <> ansi_reset <> show count
          putStrLn $ "\n " <> ansi_bold <> "Normal form: " <> ansi_reset <> pprint normalForm

          -- Typing
          if isTyped options
            then
              (case typeInference options ast of
                  Left err -> do
                    putStrLn $ "\n" <> ansi_bold <> ansi_red
                                              <> "Not well-typed.\n" <> err <> ansi_reset
                    return $ Left err
                  Right ty -> do
                    putStrLn $ "\n" <> ansi_bold <> ansi_green
                                              <> "Well-typed " <> ansi_reset
                                              <> ansi_bold <> "as " <> ansi_reset <> pprint ty
                    return $ Right normalForm)
          else return $ Right normalForm
        Left msg -> do
          putStrLn $ ansi_red ++ "Error: " ++ ansi_reset ++ msg
          return $ Left msg

typeInference :: [Option] -> Expr PCF -> Either String Type
typeInference options e =
  if isML options
    then case HM.inferType [] e of
            Just ty -> Right ty
            Nothing -> Left "Type inference failed."
    else synth [] e

ansi_red, ansi_green, ansi_reset, ansi_bold :: String
ansi_red   = "\ESC[31;1m"
ansi_green = "\ESC[32;1m"
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"