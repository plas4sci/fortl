{
{-# OPTIONS_GHC -w #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Lang.Lexer (Token(..),scanTokens,symString
                 ,getPos, constrString) where

import Data.Text (Text)
import Lang.FirstParameter
import GHC.Generics (Generic)

}

%wrapper "posn"

$digit  = 0-9
$alpha  = [a-zA-Z\_\-\=]
$lower  = [a-z]
$upper  = [A-Z]
$eol    = [\n]
$alphanum  = [$alpha $digit \_]
@sym    = ($lower | $upper) ($alphanum | \')*
@var    = \' @sym
@float   = \-? $digit+ \. $digit+
@int    = \-? $digit+
@charLiteral = \' ([\\.]|[^\']| . ) \'
@stringLiteral = \"(\\.|[^\"]|\n)*\"

@langPrag = [a-z]+

tokens :-

  $white*$eol                   { \p s -> TokenNL p }
  $eol+                         { \p s -> TokenNL p }
  $white+                       ;
  "--".*                        ;
  @var                          { \p s -> TokenVar p (tail s) }
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
  "|"                           { \p s -> TokenSep p }
  @sym				                  { \p s -> TokenSym p s }
  @float                        { \p s -> TokenFloat p s }
  @int                          { \p s -> TokenInt p s }
  "->"                          { \p s -> TokenArrow p }
  \\                            { \p s -> TokenLambda p }
  \/\\                          { \p s -> TokenTyLambda p }
  \=                            { \p s -> TokenEq p }
  \(                            { \p s -> TokenLParen p }
  \)                            { \p s -> TokenRParen p }
  \:                            { \p s -> TokenSig p }
  "?"                           { \p _ -> TokenHole p }
  "*"                           { \p s -> TokenProd p }
  "+"                           { \p s -> TokenSum p }
  "-"                           { \p s -> TokenMinus p }
  "/"                           { \p s -> TokenDivide p }
  "&"                           { \p s -> TokenAmpersand p }
  "<"                           { \p s -> TokenLPair p }
  ">"                           { \p s -> TokenRPair p }
  "["                           { \p s -> TokenLBrack p }
  "]"                           { \p s -> TokenRBrack p }
  ", "                          { \p s -> TokenMPair p }
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
  | TokenVar      AlexPosn String
  | TokenZero     AlexPosn
  | TokenSucc     AlexPosn
  | TokenArrow    AlexPosn
  | TokenEq       AlexPosn
  | TokenLParen   AlexPosn
  | TokenRParen   AlexPosn
  | TokenNL       AlexPosn
  | TokenConstr   AlexPosn String
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
  | TokenAmpersand AlexPosn
  | TokenExponent  AlexPosn
  | TokenCast     AlexPosn
  deriving (Eq, Show, Generic)

symString :: Token -> String
symString (TokenSym _ x) = x
symString t = error $ "Not a symbol " ++ show t

constrString :: Token -> String
constrString (TokenConstr _ x) = x

scanTokens = alexScanTokens >>= (return . trim)

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
