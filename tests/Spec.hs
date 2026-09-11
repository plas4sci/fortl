-- {-# OPTIONS_GHC -F -pgmF hspec-discover #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Test.Tasty (defaultMain, TestTree, testGroup)
import qualified Test.Tasty.Golden as G
import Test.Tasty.Golden.Advanced (goldenTest)
import System.Directory (setCurrentDirectory, getTemporaryDirectory, removeFile, findExecutable)
import System.Exit (ExitCode(..))
import System.FilePath (dropExtension, (</>))
import System.Process (readProcessWithExitCode)
import qualified System.IO.Strict as Strict (readFile)
--import System.Environment
--import System.Directory (doesFileExist)
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)
import Control.Monad (unless)

import qualified Lang.Frontend as Lang
import Lang.Syntax
import Lang.PrettyPrint (pprint)
import Lang.ExtractPy (extractProgram)
import Lang.Descriptions (normalisationByEvaluation, descriptionEquality)
import Lang.TypeHelpers (Specificational(..))
import Data.List (sort, dropWhileEnd)
import Data.Maybe (mapMaybe)
import Data.Char (isSpace)
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
  pythonExtraction <- pythonExtractionTests

  catch
    (defaultMain $ testGroup "All tests" [negative, positive, pythonExtraction, speciesUnitTests, basisUnitTests])
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
      res <- Lang.parseAndCheck False fp
      case res of
        Left err -> return $ Left err
        Right (_, _, _, e, _) -> return $ Right e

-- | Sanity-check the Python extraction against the example programs: for
-- each file in "examples", extract it to Python, run the result with
-- python3, and check the printed value against fortl's own interpreted
-- result for the same program. Skipped entirely if python3 isn't on PATH.
--
-- This is deliberately scoped to "examples" (not the full "tests/cases"
-- suite): those are hand-picked realistic programs, whereas tests/cases
-- exercises language corners (e.g. `case`, PCF naturals) that extraction
-- doesn't attempt to support.
pythonExtractionTests :: IO TestTree
pythonExtractionTests = do
  files      <- findByExtension fortlFileExtensions "examples"
  hasPython3 <- findExecutable "python3"
  return $ testGroup "Python extraction (examples)" $
    case hasPython3 of
      Nothing -> [testCase "python3 not found, skipping" (return ())]
      Just _  -> map pythonExtractionTest files

pythonExtractionTest :: FilePath -> TestTree
pythonExtractionTest file = testCase file $ do
  result <- Lang.parseAndCheck False file
  case result of
    Left err -> assertFailure $ "fortl failed to typecheck " <> file <> ": " <> err
    Right (parsetree, _, _, normalForm, _) -> do
      let expected  = pprint normalForm
          pySource  = extractProgram (Just file) parsetree
          tmpName   = map (\c -> if c `elem` ("/\\." :: String) then '_' else c) file <> ".py"
      tmpDir <- getTemporaryDirectory
      let pyPath = tmpDir </> tmpName
      writeFile pyPath pySource
      (exitCode, out, err) <- readProcessWithExitCode "python3" [pyPath] ""
      removeFile pyPath
      case exitCode of
        ExitFailure _ ->
          assertFailure $ "python3 failed to run extraction of " <> file <> ":\n" <> err
        ExitSuccess ->
          assertBool
            (unlines
              [ "fortl and python disagree on the result of " <> file
              , "  fortl:  " <> expected
              , "  python: " <> trim out
              ])
            (valuesMatch expected out)

-- | Compare a fortl-printed value against Python's printed output for
-- (hopefully) the same value. Exact string equality first; failing that,
-- pull out all the numbers each side printed and compare them
-- pointwise with a relative tolerance, since Haskell's `Float` and
-- Python's (64-bit) `float` don't always print identically (e.g.
-- "4.1468305e14" vs "414683070427051.25" for the same underlying value).
valuesMatch :: String -> String -> Bool
valuesMatch expected actual =
  trim expected == trim actual ||
  (not (null expectedNums) &&
   length expectedNums == length actualNums &&
   and (zipWith closeEnough expectedNums actualNums))
  where
    expectedNums = extractNumbers expected
    actualNums   = extractNumbers actual

    closeEnough x y = abs (x - y) <= 1e-3 * max 1 (max (abs x) (abs y))

    extractNumbers :: String -> [Double]
    extractNumbers = mapMaybe readDouble . words . map keepNumeric
      where
        keepNumeric c
          | c `elem` ("0123456789.eE+-" :: String) = c
          | otherwise                               = ' '
        readDouble w = case reads w of
          [(d, "")] -> Just (d :: Double)
          _         -> Nothing

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

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

basisUnitTests :: TestTree
basisUnitTests = testGroup "Basis indexing unit tests"
  [ testCase "Basis[Fox] * Basis[Fox] = Basis[Fox]" $
      assertNormalisesTo (ProdTy (bs "Fox") (bs "Fox")) (bs "Fox")
  , testCase "Basis[Fox] ^ 2 = Basis[Fox]" $
      assertNormalisesTo (ExponentTy (bs "Fox") 2.0) (bs "Fox")
  , testCase "Basis[Fox] == Basis[Fox]" $
      assertBool "same basis should be equal" $ isRight $
        descriptionEquality (bs "Fox") (IsSpec (bs "Fox"))
  , testCase "Basis[Fox] /= Basis[Rabbit]" $
      assertBool "different bases should be unequal" $ isLeft $
        descriptionEquality (bs "Fox") (IsSpec (bs "Rabbit"))
  ]
  where
    bs s = TyApp (tyCon0 "Basis") (tyCon0 s)

    assertNormalisesTo :: Type 0 -> Type 0 -> IO ()
    assertNormalisesTo input expected =
      case normalisationByEvaluation input of
        Right actual -> actual @?= expected
        Left err -> assertFailure ("Unexpected normalisation failure: " <> show err)
