{
{-# OPTIONS_GHC -w #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Lang.Lexer (Token(..),scanTokens,symString
                 ,getPos, tyVarString) where

import Data.Text (Text)
import Lang.FirstParameter
import GHC.Generics (Generic)

}

%wrapper "posn"

$digit  = 0-9

-- Unicode letters commonly used in science/maths identifiers, curated
-- rather than opening identifiers to all of Unicode (which would admit
-- confusables, mixed-script homoglyphs, and other look-alike characters).
-- Extend these ranges deliberately as more symbols are needed.
$greekUpper      = [\x0391-\x03A9]                         -- Α-Ω
$greekLower      = [\x03B1-\x03C9\x03D1\x03D5\x03D6\x03F5] -- α-ω, ϑ ϕ ϖ ϵ (common variants)
$letterlikeMath  = [\x2113\x210F\x2135-\x2138]              -- ℓ ℏ ℵ ℶ ℷ ℸ
$unicodeAlpha    = [$greekUpper $greekLower $letterlikeMath]

$alpha  = [a-zA-Z\_\-$unicodeAlpha]
$lower  = [a-z]
$upper  = [A-Z]
$eol    = [\n]
$hwhite = [\ \t]
$alphanum  = [$alpha $digit \_]
@sym    = ($lower | $upper | $unicodeAlpha) ($alphanum | \')*
@tyvar    = \' @sym
@float   = \-? $digit+ \. $digit+ ([eE] \-? $digit+)?
@int    = \-? $digit+ ([eE] \-? $digit+)?
@charLiteral = \' ([\\.]|[^\']| . ) \'
@stringLiteral = \"(\\.|[^\"]|\n)*\"

@langPrag = [a-z]+

tokens :-

  $hwhite*$eol                  { \p s -> TokenNL p }
  $eol+                         { \p s -> TokenNL p }
  $hwhite+                      ;
  "#" .*                        ;
  @tyvar                          { \p s -> TokenTyVar p (tail s) }
  lang\.@langPrag               { \p s -> TokenLang p s }
  forall                        { \p _ -> TokenForall p }
  data                          { \p s -> TokenData p }
  let                           { \p s -> TokenLet p }
  def                           { \p s -> TokenDef p }
  in                            { \p s -> TokenIn p }
  succ                          { \p s -> TokenSucc p }
  zero                          { \p s -> TokenZero p }
  case                          { \p s -> TokenCase p }
  fst                           { \p s -> TokenFst p }
  snd                           { \p s -> TokenSnd p }
  cast                          { \p s -> TokenCast p }
  lift                          { \p s -> TokenLift p }
  label                         { \p s -> TokenLabel p }
  return                        { \p s -> TokenReturn p }
  from                          { \p s -> TokenFrom p }
  import                        { \p s -> TokenImport p }
  lambda                        { \p s -> TokenLambda p }
  if                            { \p s -> TokenIf p }
  else                          { \p s -> TokenElse p }
  and                           { \p s -> TokenAnd p }
  or                            { \p s -> TokenOr p }
  not                           { \p s -> TokenNot p }
  "|"                           { \p s -> TokenSep p }
  @sym				                  { \p s -> TokenSym p s }
  @stringLiteral                { \p s -> TokenString p s }
  @float                        { \p s -> TokenFloat p s }
  @int                          { \p s -> TokenInt p s }
  "->"                          { \p s -> TokenArrow p }
  \/\\                          { \p s -> TokenTyLambda p }
  \=                            { \p s -> TokenEq p }
  \(                            { \p s -> TokenLParen p }
  \)                            { \p s -> TokenRParen p }
  "{"                           { \p s -> TokenLBrace p }
  "}"                           { \p s -> TokenRBrace p }
  \:                            { \p s -> TokenSig p }
  "?"                           { \p _ -> TokenHole p }
  "*"                           { \p s -> TokenProd p }
  "+"                           { \p s -> TokenSum p }
  "-"                           { \p s -> TokenMinus p }
  "/"                           { \p s -> TokenDivide p }
  "&"                           { \p s -> TokenAmpersand p }
  "["                           { \p s -> TokenLBrack p }
  "]"                           { \p s -> TokenRBrack p }
  ","                           { \p s -> TokenMPair p }
  "^"                           { \p s -> TokenExponent p }
  \.                            { \p _ -> TokenDot p }

{

data Token
  = TokenLang     AlexPosn String
  | TokenData     AlexPosn
  | TokenDef      AlexPosn
  | TokenCase     AlexPosn
  | TokenSep      AlexPosn
  | TokenLet      AlexPosn
  | TokenIn       AlexPosn
  | TokenTyLambda  AlexPosn
  | TokenLambda   AlexPosn
  | TokenIf       AlexPosn
  | TokenElse     AlexPosn
  | TokenSym      AlexPosn String
  | TokenTyVar    AlexPosn String
  | TokenZero     AlexPosn
  | TokenSucc     AlexPosn
  | TokenArrow    AlexPosn
  | TokenEq       AlexPosn
  | TokenLParen   AlexPosn
  | TokenRParen   AlexPosn
  | TokenNL       AlexPosn
  | TokenIndent   AlexPosn
  | TokenDedent   AlexPosn
  | TokenSig      AlexPosn
  | TokenEquiv    AlexPosn
  | TokenHole     AlexPosn
  | TokenProd     AlexPosn
  | TokenSum      AlexPosn
  | TokenMinus    AlexPosn
  | TokenDivide   AlexPosn
  | TokenAnd      AlexPosn
  | TokenOr       AlexPosn
  | TokenNot      AlexPosn
  | TokenLPair    AlexPosn
  | TokenRPair    AlexPosn
  | TokenLBrack    AlexPosn
  | TokenRBrack    AlexPosn
  | TokenLBrace    AlexPosn
  | TokenRBrace    AlexPosn
  | TokenMPair    AlexPosn
  | TokenFst      AlexPosn
  | TokenSnd      AlexPosn
  | TokenForall   AlexPosn
  | TokenDot      AlexPosn
  | TokenInt      AlexPosn String
  | TokenFloat    AlexPosn String
  | TokenBool     AlexPosn Bool
  | TokenString   AlexPosn String
  | TokenAmpersand AlexPosn
  | TokenExponent  AlexPosn
  | TokenCast     AlexPosn
  | TokenLift     AlexPosn
  | TokenLabel    AlexPosn
  | TokenReturn   AlexPosn
  | TokenFrom     AlexPosn
  | TokenImport   AlexPosn
  deriving (Eq, Show, Generic)

symString :: Token -> String
symString (TokenSym _ x) = x
symString t = error $ "Not a symbol " ++ show t

tyVarString :: Token -> String
tyVarString (TokenTyVar _ x) = x
tyVarString t = error $ "Not a type variable " ++ show t

scanTokens = alexScanTokens . stripDocstrings >>= (return . trim . layout)

-- Add layout markers for function bodies. Existing multiline expressions use
-- indentation for readability, so layout is activated only after a def header.
-- A stack of block columns supports arbitrarily nested defs.
layout :: [Token] -> [Token]
layout tokens = go [] tokens [] 0
  where
    -- go <tokens of current line so far> <remaining tokens> <block column stack> <paren depth>
    go _ [] stack _ = map (const (TokenDedent (AlexPn 0 0 0))) stack
    go line (t:ts) stack parenDepth =
      case t of
        TokenNL p ->
          let (next, _) = nextNonNL ts
              lineHeader = isDefHeader line
              nextColumn = maybe 0 (snd . getPos) next
              newline = if (not (null stack) && parenDepth == 0)
                           || lineHeader || lineStartsImport line
                        then [t]
                        else []
              (popped, remaining) = span (> nextColumn) stack
              (emitted, stack')
                -- indentation is ignored inside parentheses
                | parenDepth /= 0 = (newline, stack)
                -- block opens after a def header: nl before indent
                | lineHeader && nextColumn > lineColumn line =
                    (newline ++ [TokenIndent p], nextColumn : stack)
                -- blocks close: one dedent per level, before the nl so the
                -- enclosing block still sees a statement separator
                | otherwise =
                    (map (const (TokenDedent p)) popped ++ newline, remaining)
          in emitted ++ go [] ts stack' parenDepth
        _ -> t : go (line ++ [t]) ts stack (parenDepth + parenthesisDepth t)

    nextNonNL [] = (Nothing, [])
    nextNonNL (TokenNL _ : ts) = nextNonNL ts
    nextNonNL (t:ts) = (Just t, ts)

    lineColumn [] = 0
    lineColumn (t:_) = snd (getPos t)

    isDefHeader line = any isDef line && any isColon line
    isDef (TokenDef _) = True
    isDef _ = False
    isColon (TokenSig _) = True
    isColon _ = False

    parenthesisDepth (TokenLParen _) = 1
    parenthesisDepth (TokenRParen _) = -1
    parenthesisDepth _ = 0

    lineStartsImport (TokenLang _ _ : _) = True
    lineStartsImport (TokenImport _ : _) = True
    lineStartsImport (TokenFrom _ : _) = True
    lineStartsImport _ = False

-- Strip Python-style triple-quoted docstrings before lexing.
-- We preserve newlines to keep parser layout/error positions stable.
stripDocstrings :: String -> String
stripDocstrings = go
  where
    go ('"':'"':'"':xs) = "   " ++ goDoc xs
    go (x:xs) = x : go xs
    go [] = []

    goDoc ('"':'"':'"':xs) = "   " ++ go xs
    goDoc (x:xs)
      | x == '\n' = '\n' : goDoc xs
      | otherwise = ' ' : goDoc xs
    goDoc [] = []

trim :: [Token] -> [Token]
trim = reverse . trimNL . reverse . trimNL

trimNL :: [Token] -> [Token]
trimNL [] = []
trimNL (TokenNL _ : ts) = trimNL ts
trimNL ts = ts

instance FirstParameter Token AlexPosn

getPos :: Token -> (Int, Int)
getPos t = (l, c)
  where (AlexPn _ l c) = getFirstParameter t

}
