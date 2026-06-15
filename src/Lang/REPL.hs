{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DataKinds #-}
module Lang.REPL where

import Lang.Syntax
import Lang.Frontend    (banner, run, ansi_bold, ansi_reset)
import Lang.Parser      (parseExpr, parseType)
import Lang.PrettyPrint (pprint)
import Lang.Types       (synth, errorToString, Context)
import Lang.Semantics   (bigStep, Env)
import Lang.Kinding     (synthKind)
import Lang.Options     (Option)

import System.FilePath  (takeBaseName)
import System.Console.Haskeline
import Control.Monad.IO.Class (liftIO)

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
    , typingContext :: Context
  }

initialState :: REPLState
initialState = REPLState {
     currentFile = Nothing
   , prompt      = "[F]"
   , env         = []
   , options     = []
   , typingContext = []
  }

-- Main REPL
replLoop :: REPLState -> InputT IO REPLState
replLoop state = do
  line <- getInputLine (prompt state ++ "> ")
  case line of
    Nothing -> return state
    Just str -> case str of
      ':':rest ->
        -- Command
        case rest of
          'q':_ -> return state
          'h':_ -> do
            liftIO printHelp
            replLoop state
          'l':' ':path -> do
            runResult <- liftIO $ run False path
            case runResult of
              Left err -> do
                liftIO $ putStrLn err
                replLoop state
              Right (ast', opts, env', expr, ctxt) -> do
                liftIO $ displayResult expr
                let fileState = FileState { filename = path, ast = ast' }
                replLoop $ state { currentFile = Just fileState
                                  , prompt = takeBaseName path
                                  , env = env'
                                  , options = opts
                                  , typingContext = ctxt }

          't':' ':rest' -> do
            liftIO $ case parseExpr rest' of
              Left err  -> putStrLn err
              Right expr ->
                case synth (typingContext state) expr of
                  Left err -> let ?srcFile = "<repl>" in putStrLn $ errorToString err
                  Right ty -> putStrLn $ pprint ty
            replLoop state

          'k':' ': rest' -> do
              liftIO $ case parseType rest' of
                  Left err -> putStrLn err
                  Right ty ->
                    case synthKind ty of
                      Left err -> let ?srcFile = "<repl>" in putStrLn $ errorToString err
                      Right (ty', kind) -> do
                        if ty /= ty'
                          then putStrLn $ "Elaborated type: " ++ pprint ty'
                          else return ()
                        putStrLn $ pprint kind
              replLoop state
          rest' -> do
            liftIO $ putStrLn $ "Unknown command :" ++ rest'
            liftIO printHelp
            replLoop state
      -- not a command
      rest -> do
        liftIO $ case parseExpr rest of
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
  _ <- runInputT defaultSettings (replLoop initialState)
  return ()

printHelp :: IO ()
printHelp = do
  putStrLn "Commands:"
  putStrLn "    :h      - This message"
  putStrLn "    :t expr - Infer the type of an expression"
  putStrLn "    :k type - Infer the type of a type (its kind)"
  putStrLn "    :l path - Load the file"
  putStrLn "    :r      - Reload the currenty loaded file"
  putStrLn "    :q      - Quit"
  putStrLn " Or type an expression to evaluate it"