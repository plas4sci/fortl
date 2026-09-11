{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- | Extracts a fortl program into an equivalent Python program.
--
-- This works by pretty printing the AST in much the same shape as
-- Lang.PrettyPrint" but erasing everything that has no run-time meaning
-- once translated to Python: type signatures, casts, lifts, and type
-- abstraction/application. These are all erasable accroding to the Lang.Semantics
-- so dropping them and keeping the underlying term preserves fortl's behaviour.
module Lang.ExtractPy (extractProgram) where

import Lang.Syntax
import Lang.PrettyPrint (isLexicallyAtomic)

import Data.List (intercalate, isInfixOf)

-- | Render a whole (parsed) fortl program as Python source.
--
-- The result always ends by printing `it`, seeded to `None` up front so a
-- program that never binds it still prints something -- this mirrors
-- "Lang.Semantics".`interpretDefs`'s own fallback (@lookup "it" env@,
-- defaulting to @None@), so the printed value matches what @fortl@ itself
-- prints for the same program.
extractProgram :: Maybe String -> Program 'Parsed -> String
extractProgram original defs =
  let body   = concatMap extractDef defs
      whence = case original of
                 Nothing -> "a fortl program"
                 Just filename -> "fortl program " ++ filename
      header = ("# Generated from " ++ whence ++ " by --extract-py")
             : if any ("math.sqrt(" `isInfixOf`) body then ["import math", ""] else [""]
      preamble = ["it = None"]
      trailer  = ["print(it)"]
  in unlines (header ++ preamble ++ body ++ trailer)

extractDef :: Def 'Parsed -> [String]
extractDef (ValDef lhs e)   = [extractLhs lhs ++ " = " ++ pyExpr e]
extractDef (Return e)       = ["it = " ++ pyExpr e]
extractDef (TypeDef _ _ _)  = []
extractDef (DataDef _ _ _)  = []
extractDef (ImportDef spec) = [extractImport spec]

-- | Assignment targets, mirroring the source: a plain variable, or a
-- (possibly nested) pair, which becomes Python's native tuple unpacking.
extractLhs :: Lhs 'Parsed -> String
extractLhs (VarLhs x _)    = x
extractLhs (PairLhs l1 l2) = "(" ++ extractLhs l1 ++ ", " ++ extractLhs l2 ++ ")"

extractImport :: ImportSpec -> String
extractImport (ImportModule m)   = "import " ++ m
extractImport (ImportAll m)      = "from " ++ m ++ " import *"
extractImport (ImportOnly m ids) = "from " ++ m ++ " import " ++ intercalate ", " ids

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

bracketPy :: Expr -> String
bracketPy e | isLexicallyAtomic e = pyExpr e
            | otherwise    = "(" ++ pyExpr e ++ ")"

-- | Pretty print a fortl expression as Python.
pyExpr :: Expr -> String
pyExpr (Abs var _ e)         = "lambda " ++ var ++ ": " ++ pyExpr e
-- Type application/abstraction, signatures, casts and lifts are all
-- run-time identities: erase them and keep the underlying term.
pyExpr (App e1 (TyEmbed _))  = pyExpr e1
pyExpr (App (Var "sqrt") e2) = "math.sqrt(" ++ pyExpr e2 ++ ")"
pyExpr (App e1 e2)           = bracketPy e1 ++ "(" ++ pyExpr e2 ++ ")"
pyExpr (Var var)             = var
pyExpr (Sig e _)             = pyExpr e
pyExpr (Cast e)              = pyExpr e
pyExpr (TyAbs _ e)           = pyExpr e
pyExpr (TyEmbed _)           = ""
-- let becomes an immediately-applied lambda
pyExpr (GenLet x e1 e2)      = "(lambda " ++ x ++ ": " ++ pyExpr e2 ++ ")(" ++ pyExpr e1 ++ ")"
pyExpr Zero                  = "0"
pyExpr Succ                  = "(lambda _n: _n + 1)"
pyExpr (Pair e1 e2)          = "(" ++ pyExpr e1 ++ ", " ++ pyExpr e2 ++ ")"
pyExpr (Fst e)                = bracketPy e ++ "[0]"
pyExpr (Snd e)                = bracketPy e ++ "[1]"
-- Sum types/case are not implemented in Lang.Semantics either, so there is
-- no behaviour to preserve here; fail loudly if it's ever evaluated.
pyExpr (Case _ _ _)           =
  "throw(NotImplementedError(\"case is not supported by --extract-py\"))"
pyExpr (BinOp op e1 e2)       = bracketPy e1 ++ " " ++ pprint op ++ " " ++ bracketPy e2
pyExpr (UnOp op e)            = pprint op ++ bracketPy e
pyExpr (Lift e _)             = pyExpr e
pyExpr (NumFloat f)           = show f
pyExpr (NumInteger n)         = show n
pyExpr (StringConst s)        = pyStringLit s
pyExpr (Cond e1 e2 e3)        = pyExpr e1 ++ " if " ++ pyExpr e2 ++ " else " ++ pyExpr e3
pyExpr (Con c [])             = c
pyExpr (Con c es)             = c ++ "(" ++ intercalate ", " (map pyExpr es) ++ ")"

-- | Python's operators, not fortl's: notably `^` means exponentiation in
-- fortl's surface syntax but bitwise XOR in Python, so `BinOpExp` must map
-- to `**`, not to fortl's own `pprint` for this operator.
pyBinOp :: BinOp -> String
pyBinOp BinOpExp    = "**"
pyBinOp BinOpPlus   = "+"
pyBinOp BinOpMinus  = "-"
pyBinOp BinOpTimes  = "*"
pyBinOp BinOpDivide = "/"
pyBinOp BinOpAnd    = "and"
pyBinOp BinOpOr     = "or"

-- | Render a Haskell string as a Python string literal, escaping only the
-- characters that need it and passing everything else through untouched.
pyStringLit :: String -> String
pyStringLit s = "\"" ++ concatMap escape s ++ "\""
  where
    escape '"'  = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\t' = "\\t"
    escape '\r' = "\\r"
    escape c    = [c]
