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
$alpha  = [a-zA-Z\_\-]
$lower  = [a-z]
$upper  = [A-Z]
$eol    = [\n]
$alphanum  = [$alpha $digit \_]
@sym    = ($lower | $upper) ($alphanum | \')*
@tyvar    = \' @sym
@float   = \-? $digit+ \. $digit+ ([eE] \-? $digit+)?
@int    = \-? $digit+ ([eE] \-? $digit+)?
@charLiteral = \' ([\\.]|[^\']| . ) \'
@stringLiteral = \"(\\.|[^\"]|\n)*\"

@langPrag = [a-z]+

tokens :-

  $white*$eol                   { \p s -> TokenNL p }
  $eol+                         { \p s -> TokenNL p }
  $white+                       ;
  "#" .*                        ;
  @tyvar                          { \p s -> TokenTyVar p (tail s) }
  lang\.@langPrag               { \p s -> TokenLang p s }
  forall                        { \p _ -> TokenForall p }
  data                          { \p s -> TokenData p }
  let                           { \p s -> TokenLet p }
  in                            { \p s -> TokenIn p }
  succ                          { \p s -> TokenSucc p }
  zero                          { \p s -> TokenZero p }
  natcase                       { \p s -> TokenNatCase p }
  case                          { \p s -> TokenCase p }
  of                            { \p s -> TokenOf p }
  fix                           { \p s -> TokenFix p }
  fst                           { \p s -> TokenFst p }
  snd                           { \p s -> TokenSnd p }
  inl                           { \p s -> TokenInl p }
  inr                           { \p s -> TokenInr p }
  cast                          { \p s -> TokenCast p }
  return                        { \p s -> TokenReturn p }
  from                          { \p s -> TokenFrom p }
  import                        { \p s -> TokenImport p }
  lambda                        { \p s -> TokenLambda p }
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
  \@                            { \p _ -> TokenAt p }

{

data Token
  = TokenLang     AlexPosn String
  | TokenData     AlexPosn
  | TokenCase     AlexPosn
  | TokenNatCase  AlexPosn
  | TokenOf       AlexPosn
  | TokenSep      AlexPosn
  | TokenFix      AlexPosn
  | TokenLet      AlexPosn
  | TokenIn       AlexPosn
  | TokenTyLambda  AlexPosn
  | TokenLambda   AlexPosn
  | TokenSym      AlexPosn String
  | TokenTyVar    AlexPosn String
  | TokenZero     AlexPosn
  | TokenSucc     AlexPosn
  | TokenArrow    AlexPosn
  | TokenEq       AlexPosn
  | TokenLParen   AlexPosn
  | TokenRParen   AlexPosn
  | TokenNL       AlexPosn
  | TokenSig      AlexPosn
  | TokenEquiv    AlexPosn
  | TokenHole     AlexPosn
  | TokenProd     AlexPosn
  | TokenSum      AlexPosn
  | TokenMinus    AlexPosn
  | TokenDivide   AlexPosn
  | TokenLPair    AlexPosn
  | TokenRPair    AlexPosn
  | TokenLBrack    AlexPosn
  | TokenRBrack    AlexPosn
  | TokenLBrace    AlexPosn
  | TokenRBrace    AlexPosn
  | TokenMPair    AlexPosn
  | TokenFst      AlexPosn
  | TokenSnd      AlexPosn
  | TokenInl      AlexPosn
  | TokenInr      AlexPosn
  | TokenForall   AlexPosn
  | TokenDot      AlexPosn
  | TokenAt       AlexPosn
  | TokenInt      AlexPosn String
  | TokenFloat    AlexPosn String
  | TokenString   AlexPosn String
  | TokenAmpersand AlexPosn
  | TokenExponent  AlexPosn
  | TokenCast     AlexPosn
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

scanTokens = alexScanTokens . stripDocstrings >>= (return . trim)

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
