{
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

module Lang.Parser where

import Numeric
import System.Exit
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)

import Lang.Lexer
import Lang.Syntax
import Lang.Options

}

%name program Program
%name expr Expr
%tokentype { Token }
%error { parseError }
%monad { ReaderT String (Either String) }

%token
    nl      { TokenNL _ }
    let     { TokenLet _ }
    case    { TokenCase _ }
    natcase { TokenNatCase _ }
    of      { TokenOf _ }
    '|'     { TokenSep _ }
    fix     { TokenFix _ }
    fst     { TokenFst _ }
    snd     { TokenSnd _ }
    inl     { TokenInl _ }
    inr     { TokenInr _ }
    in      { TokenIn  _  }
    zero    { TokenZero _ }
    succ    { TokenSucc _ }
    VAR     { TokenSym _ _ }
    LANG    { TokenLang _ _ }
    CONSTR  { TokenConstr _ _ }
    FLOAT   { TokenFloat _ _ }
    INT     { TokenInt _ _ }
    forall  { TokenForall _ }
    '\\'    { TokenLambda _ }
    Lam     { TokenTyLambda _ }
    '->'    { TokenArrow _ }
    '='     { TokenEq _ }
    '('     { TokenLParen _ }
    ')'     { TokenRParen _ }
    ':'     { TokenSig _ }
    '?'     { TokenHole _ }
    '*'     { TokenProd _ }
    '-'     { TokenMinus _ }
    '/'     { TokenDivide _ }
    '+'     { TokenSum _ }
    '^'     { TokenExponent _ }
    '&'     { TokenAmpersand _ }
    '<'     { TokenLPair _ }
    '>'     { TokenRPair _ }
    '['     { TokenLBrack _ }
    ']'     { TokenRBrack _ }
    ', '    { TokenMPair _ }
    '.'     { TokenDot _ }
    '@'     { TokenAt _ }

%right in
%right '->'
%left ':'
%left '+' '-'
%left '*'
%%

Program :: { (Expr PCF, [Option]) }
  : LangOpts Defs  { ($2 $1, $1) }

LangOpts :: { [Option] }
  : LANG NL LangOpts    {% (readOption $1) >>= (\opt -> addOption opt $3) }
  | LANG                {% readOption $1 >>= (return . (:[])) }
  | {- empty -}         { [] }

Defs :: { [Option] -> Expr PCF }
  : Def NL Defs           { \opts -> ($1 opts) ($3 opts) }
  | Expr                  { \opts -> $1 opts }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Def :: { [Option] -> Expr PCF -> Expr PCF }
  : VAR '=' Expr { \opts -> \program -> App (Abs (symString $1) Nothing program) ($3 opts) }
  | VAR ':' Type '=' Expr { \opts -> \program -> App (Abs (symString $1) Nothing program) (Sig ($5 opts) ($3 opts)) }

Expr :: { [Option] -> Expr PCF }
  : let VAR '=' Expr in Expr
    { \opts ->
      GenLet (symString $2) ($4 opts) ($6 opts) }

  | '\\' '(' VAR ':' Type ')' '->' Expr
    { \opts -> Abs (symString $3) (Just ($5 opts)) ($8 opts) }

  | '\\' VAR '->' Expr
    { \opts -> Abs (symString $2) Nothing ($4 opts) }

  | Lam VAR '->' Expr
    { \opts -> TyAbs (symString $2) ($4 opts) }

  | Expr ':' Type  { \opts -> Sig ($1 opts) ($3 opts) }

  | Form
    { $1 }

  | fix '(' Expr ')'
     { \opts -> Ext (Fix ($3 opts)) }

  | natcase Expr of zero '->' Expr '|' succ VAR '->' Expr
     { \opts -> Ext (NatCase ($2 opts) ($6 opts) (symString $9, ($11 opts))) }

  | fst '(' Expr ')'
     { \opts -> Ext (Fst ($3 opts)) }

  | snd '(' Expr ')'
     { \opts -> Ext (Snd ($3 opts)) }

  | inl '(' Expr ')'
     { \opts -> Ext (Inl ($3 opts)) }

  | inr '(' Expr ')'
     { \opts -> Ext (Inr ($3 opts)) }

 | case Expr of inl VAR '->' Expr '|' inr VAR '->' Expr
     { \opts -> Ext (Case ($2 opts) (symString $5, $7 opts) (symString $10, ($12 opts))) }

Form :: { [Option] -> Expr PCF }
  : Form '+' Form  { \opts -> Ext $ BinOp OpPlus ($1 opts) ($3 opts) }
  | Form '-' Form  { \opts -> Ext $ BinOp OpMinus ($1 opts) ($3 opts) }
  | Form '*' Form  { \opts -> Ext $ BinOp OpTimes ($1 opts) ($3 opts) }
  | Form '/' Form  { \opts -> Ext $ BinOp OpDivide ($1 opts) ($3 opts) }
  | Juxt           { $1 }

Type :: { [Option] -> Type 0 }
Type
  : Type '->' Type   { \opts -> FunTy ($1 opts) ($3 opts) }
  | Type '*' Type    { \opts -> ProdTy ($1 opts) ($3 opts) }
  | Type '+' Type    { \opts -> SumTy ($1 opts) ($3 opts) }
  | Type '&' Type    { \opts -> IntersectTy ($1 opts) ($3 opts) }
  | Type '^' NumFloat   { \opts -> ExponentTy ($1 opts) $3 }
  | TyJuxt           { $1 }
  | '[' Type ']'     { \opts -> TyApp (TyCon "Unit") ($2 opts) }
  | forall VAR '.' Type { \opts ->
                            if isPoly opts
                              then Forall (symString $2) ($4 opts)
                              else error "Type quantification not supported in simple types; try lang.poly. " }

TyJuxt :: { [Option] -> Type 0 }
TyJuxt
  : TyJuxt TypeAtom { \opts -> TyApp ($1 opts) ($2 opts) }
  | TypeAtom        { $1 }

NumFloat :: { Float }
NumFloat
  : FLOAT { let (TokenFloat _ x) = $1 in read x }
  | INT   { let (TokenInt _ x) = $1   in let r = (read x) :: Integer in fromIntegral r }

TypeAtom :: { [Option] -> Type 0 }
TypeAtom
  : CONSTR           { \opts -> TyCon $ constrString $1 }
  | VAR              { \opts ->
                          if isPoly opts
                            then TyVar (symString $1)
                            else error "Type variables not supported in simple types; try lang.poly." }
  | '(' Type ')'     { \opts -> $2 opts }
  | INT              { \opts -> TyCon $ let (TokenInt _ x) = $1 in x }

Juxt :: { [Option] -> Expr PCF }
  : Juxt Atom                 { \opts -> App ($1 opts) ($2 opts) }
  | Atom                      { $1 }

Atom :: { [Option] -> Expr PCF }
  : '(' Expr ')'              { $2 }
  | VAR                       { \opts -> Var $ symString $1 }
  | zero
    { \opts -> Ext Zero }
  | succ
    { \opts -> Ext Succ }

  | '@' TypeAtom
    { \opts ->
        if isPoly opts
          then TyEmbed ($2 opts)
          else error "Cannot embed a type as a term; try lang.poly" }

  | '<' Expr ', ' Expr '>'
     { \opts -> Ext (Pair ($2 opts) ($4 opts)) }

  | FLOAT
     { \opts ->
          let (TokenFloat _ x) = $1
          in Ext (NumFloat $ read x) }

  | INT
     { \opts ->
          let (TokenInt _ x) = $1
          in Ext (NumFloat $ fromIntegral $ read x) }

  -- For later
  -- | '?' { Hole }
{

readOption :: Token -> ReaderT String (Either String) Option
readOption (TokenLang _ x) | x == "lang.inference" = return HindleyMilner
readOption (TokenLang _ x) | x == "lang.typed" = return Typed
readOption (TokenLang _ x) | x == "lang.poly"  = return Poly
readOption (TokenLang _ x) = lift . Left $ "Unknown language option: " <> x
readOption _ = lift . Left $ "Wrong token for language"

parseError :: [Token] -> ReaderT String (Either String) a
parseError [] = lift . Left $ "Premature end of file"
parseError t  =  do
    file <- ask
    lift . Left $ file <> ":" <> show l <> ":" <> show c
                        <> ": parse error"
  where (l, c) = getPos (head t)

parseProgram :: FilePath -> String -> Either String (Expr PCF, [Option])
parseProgram file input = runReaderT (program $ scanTokens input) file

}