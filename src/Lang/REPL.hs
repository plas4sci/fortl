{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DataKinds #-}
module Lang.REPL where

import Lang.Syntax
import Lang.Frontend    (banner, run, ansi_bold, ansi_reset)
import Lang.Parser      (parseExpr, parseType)
import Lang.PrettyPrint (pprint)
import Lang.Types       (synth, errorToString)
import Lang.Semantics   (bigStep, Env)
import Lang.Kinding     (synthKind)
import Lang.Options     (Option)

import System.FilePath  (takeBaseName)
import System.IO        (hFlush, stdout)
import System.Console.Haskeline

data FileState = 
  FileState {
      filename :: FilePath
    , ast      :: Program 'Parsed
  }

data REPLState = 
  REPLState {
      currentFile :: Maybe FileState
    , prompt      :: String
    , env         :: Env
    , options     :: [Option]
  }

initialState :: REPLState
initialState = REPLState {
     currentFile = Nothing
   , prompt      = "[F]"
   , env         = []
   , options     = []
  }

-- Main REPL
replLoop :: REPLState -> IO REPLState
replLoop state = do
  line <- getInputLine (prompt state ++ "> ")
  case line of
    ':':rest -> 
      -- Command
      case rest of
        'q':_ -> return state
        'h':_ -> do
          printHelp
          replLoop state
        'l':' ':rest -> do
          runResult <- run False rest 
          case runResult of
            Left err -> do
              putStrLn err 
              replLoop state
            Right (ast, options, env, expr) -> do
              displayResult expr
              let fileState = FileState { filename = rest, ast = ast }
              replLoop $ state { currentFile = Just fileState
                                , prompt = takeBaseName rest
                                , env = env
                                , options = options }

        't':' ':rest -> do
          case parseExpr rest of
            Left err   -> 
              case parseType rest of
                Left err -> putStrLn err
                Right ty -> 
                  case synthKind ty of
                    Left err -> let ?srcFile = "<repl>" in putStrLn $ errorToString err
                    Right (ty', kind) -> do
                      if ty /= ty'
                        then putStrLn $ "Elaborated type: " ++ pprint ty'
                        else return ()
                      putStrLn $ pprint kind
            Right expr -> 
              case synth [] expr of
                Left err -> let ?srcFile = "<repl>" in putStrLn $ errorToString err
                Right ty -> putStrLn $ pprint ty
          replLoop state
        rest -> do
          putStrLn $ "Unknown command :" ++ rest
          printHelp
          replLoop state
    -- not a command
    rest -> do
      case parseExpr rest of
        Left err   -> putStrLn err
        Right expr ->
          case bigStep (env state) (options state) expr of
            Left err  -> putStrLn err
            Right var -> putStrLn $ pprint var
      replLoop state

displayResult :: Expr -> IO ()
displayResult e = do
  putStrLn $ pprint e

main :: IO ()
main = do
  putStrLn $ ansi_bold <> banner <> ansi_reset
  putStrLn "Run :h for help"
  _ <- replLoop initialState
  return ()

printHelp :: IO ()
printHelp = do
  putStrLn "Commands:"
  putStrLn "    :h      - This message"
  putStrLn "    :t expr - Infer the type of an expression"
  putStrLn "    :t type - Infer the type of a type"
  putStrLn "    :l path - Load the file"
  putStrLn "    :r      - Reload the currenty loaded file"
  putStrLn "    :q      - Quit"
  putStrLn " Or type an expression to evaluate it"