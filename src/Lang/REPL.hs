module Lang.REPL where

import Lang.Frontend    (banner)
import Lang.Parser      (parseExpr, parseType)
import Lang.PrettyPrint (pprint)
import Lang.Types       (synth, errorToString)
import Lang.Semantics   (bigStep)
import Lang.Kinding     (synthKind)

import System.IO        (hFlush, stdout)

-- Main REPL
replLoop :: IO ()
replLoop = do
  putStr "fortl> "
  hFlush stdout
  inp <- getLine
  case inp of
    ':':'q':_ -> return ()
    ':':'t':' ':rest -> do
      case parseExpr rest of
        Left err   -> putStrLn err
        Right expr -> 
          case synth [] expr of
            Left err -> putStrLn $ errorToString err
            Right ty -> putStrLn $ pprint ty
      replLoop
    ':':'k':' ':rest -> do
      case parseType rest of
        Left err -> putStrLn err
        Right ty -> 
          case synthKind ty of
            Left err -> putStrLn $ errorToString err
            Right kind -> putStrLn $ pprint kind
      replLoop
    rest -> do
      case parseExpr rest of
        Left err   -> putStrLn err
        Right expr ->
          case bigStep [] [] expr of
            Left err  -> putStrLn err
            Right var -> putStrLn $ pprint var
      replLoop

main :: IO ()
main = do
  putStrLn banner
  replLoop