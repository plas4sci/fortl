-- {-# OPTIONS_GHC -F -pgmF hspec-discover #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Test.Tasty (defaultMain, TestTree, testGroup)
import qualified Test.Tasty.Golden as G
import Test.Tasty.Golden.Advanced (goldenTest)
import System.Directory (setCurrentDirectory)
import System.Exit (ExitCode)
import System.FilePath (dropExtension)
import qualified System.IO.Strict as Strict (readFile)
--import System.Environment
--import System.Directory (doesFileExist)
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)
import Control.Monad (unless)

import qualified Lang.Frontend as Lang
import Lang.Syntax
import Lang.PrettyPrint (pprint)
import Data.List (sort)
import Control.Exception (catch, throwIO)

import Debug.Trace

type InterpreterError = String
type InterpreterResult = Expr PCF



main :: IO ()
main = do
  setCurrentDirectory "."
  negative  <- goldenTestsNegative
  positive  <- goldenTestsPositive

  catch
    (defaultMain $ testGroup "Golden tests" [negative, positive])
    (\(e :: ExitCode) -> do
      throwIO e
    )

findByExtension :: [FilePath] -> FilePath -> IO [FilePath]
findByExtension exs path = G.findByExtension exs path >>= (return . sort)

goldenTestsNegative :: IO TestTree
goldenTestsNegative = do
  -- get example files, but discard the excluded ones
  files <- findByExtension fortlFileExtensions "tests/cases/negative"

  -- ensure we don't have spurious output files without associated tests
  outfiles <- findByExtension [".output"] "tests/cases/negative"
  failOnOrphanOutfiles files outfiles

  return $ testGroup
    "Negative regressions"
    (map (grGolden formatResult) files)

  where
    formatResult :: Either InterpreterError InterpreterResult -> String
    formatResult = \case
        Left err -> err
        Right x -> error $ "Negative test passed!\n" <> show x

goldenTestsPositive :: IO TestTree
goldenTestsPositive = do
  exampleFiles  <- findByExtension fortlFileExtensions "examples"
  positiveFiles <- findByExtension fortlFileExtensions "tests/cases/positive"
  let files = exampleFiles <> positiveFiles

  -- ensure we don't have spurious output files without associated tests
  exampleOutfiles  <- findByExtension [".output"] "examples"
  positiveOutfiles <- findByExtension [".output"] "tests/cases/positive"
  let outfiles = exampleOutfiles <> positiveOutfiles
  failOnOrphanOutfiles files outfiles

  return $ testGroup
    "Golden examples and positive regressions"
    (map (grGolden formatResult) files)

  where
    formatResult :: Either InterpreterError InterpreterResult -> String
    formatResult = \case
        Right val -> pprint val
        Left err -> error err

grGolden
  :: (Either InterpreterError InterpreterResult -> String)
  -> FilePath
  -> TestTree
grGolden formatResult file = show file `trace` goldenTest
    file
    (Strict.readFile outfile)
    (formatResult <$> runInterp file)
    checkDifference
    (\actual -> unless (null actual) (writeFile outfile actual))
  where
    outfile = file <> ".output"
    checkDifference :: String -> String -> IO (Maybe String)
    checkDifference exp act = if exp == act
      then return Nothing
      else return . Just $ unlines
        [ "Contents of " <> outfile <> " (<) and actual output (>) differ:"
        , ppDiff $ getGroupedDiff (lines exp) (lines act)
        ]

    runInterp :: FilePath -> IO (Either InterpreterError InterpreterResult)
    runInterp fp =
      Lang.run False fp

failOnOrphanOutfiles :: [FilePath] -> [FilePath] -> IO ()
failOnOrphanOutfiles files outfiles
  = case filter (\outfile -> dropExtension outfile `notElem` files) outfiles of
    [] -> return ()
    orphans -> error . red $ "Orphan output files:\n" <> unlines orphans
  where
    red x = "\ESC[31;1m" <> x <> "\ESC[0m"

fortlFileExtensions :: [String]
fortlFileExtensions = [".frtl"]
