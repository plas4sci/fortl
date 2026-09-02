-- {-# OPTIONS_GHC -F -pgmF hspec-discover #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
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
import Lang.Descriptions (normalisationByEvaluation, descriptionEquality)
import Lang.TypeHelpers (Specificational(..))
import Data.List (sort)
import Data.Either (isLeft, isRight)
import Control.Exception (catch, throwIO)
import Test.Tasty.HUnit (testCase, (@?=), assertBool, assertFailure)

import Debug.Trace

type InterpreterError = String
type InterpreterResult = Expr



main :: IO ()
main = do
  setCurrentDirectory "."
  negative  <- goldenTestsNegative
  positive  <- goldenTestsPositive

  catch
    (defaultMain $ testGroup "All tests" [negative, positive, speciesUnitTests])
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
    runInterp fp = do
      res <- Lang.run False fp
      case res of
        Left err -> return $ Left err
        Right (_, _, _, e, _) -> return $ Right e

failOnOrphanOutfiles :: [FilePath] -> [FilePath] -> IO ()
failOnOrphanOutfiles files outfiles
  = case filter (\outfile -> dropExtension outfile `notElem` files) outfiles of
    [] -> return ()
    orphans -> error . red $ "Orphan output files:\n" <> unlines orphans
  where
    red x = "\ESC[31;1m" <> x <> "\ESC[0m"

fortlFileExtensions :: [String]
fortlFileExtensions = [".frtl"]

-- Unit tests for species indexing semantics
speciesUnitTests :: TestTree
speciesUnitTests = testGroup "Species indexing unit tests"
  [ testGroup "normalisation-by-evaluation"
  [ testCase "S * S = S (idempotent)" $
    assertNormalisesTo (ProdTy (sp "Fox") (sp "Fox")) (sp "Fox")
  , testCase "1 * S = S (left identity)" $
    assertNormalisesTo (ProdTy (sp "1") (sp "Fox")) (sp "Fox")
  , testCase "S * 1 = S (right identity)" $
    assertNormalisesTo (ProdTy (sp "Fox") (sp "1")) (sp "Fox")
  , testCase "1 * 1 = 1" $
    assertNormalisesTo (ProdTy (sp "1") (sp "1")) (sp "1")
  , testCase "exponentiation is no-op for species" $
    assertNormalisesTo (ExponentTy (sp "Fox") 2.0) (sp "Fox")
    , testCase "S * T normalises to distinct value (mismatch preserved)" $
    case normalisationByEvaluation (ProdTy (sp "Fox") (sp "Rabbit")) of
      Right t  -> assertBool "Fox * Rabbit should not normalise to Fox" (t /= sp "Fox")
      Left err -> assertFailure ("Unexpected normalisation failure: " <> show err)
    ]
  , testGroup "description-equality"
    [ testCase "Species[S] == Species[S]" $
        assertBool "same species should be equal" $ isRight $
          descriptionEquality (sp "Fox") (IsSpec (sp "Fox"))
    , testCase "Species[1] == Species[1]" $
        assertBool "identity species should equal itself" $ isRight $
          descriptionEquality (sp "1") (IsSpec (sp "1"))
    , testCase "Species[Fox] /= Species[Rabbit]" $
        assertBool "different species should be unequal" $ isLeft $
          descriptionEquality (sp "Fox") (IsSpec (sp "Rabbit"))
    , testCase "Species[1] /= Species[Fox]" $
        assertBool "identity species should not equal a named species" $ isLeft $
          descriptionEquality (sp "1") (IsSpec (sp "Fox"))
    ]
  ]
  where
    sp s = TyApp (tyCon0 "Species") (tyCon0 s)

    assertNormalisesTo :: Type 0 -> Type 0 -> IO ()
    assertNormalisesTo input expected =
      case normalisationByEvaluation input of
        Right actual -> actual @?= expected
        Left err -> assertFailure ("Unexpected normalisation failure: " <> show err)
