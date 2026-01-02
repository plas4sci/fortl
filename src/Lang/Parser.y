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
    data    { TokenData _ }
    cast    { TokenCast _ }
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
    return  { TokenReturn _ }
    IDENT   { TokenSym _ _ }
    LANG    { TokenLang _ _ }
    TYVAR   { TokenTyVar _ _ }
    FLOAT   { TokenFloat _ _ }
    INT     { TokenInt _ _ }
    forall  { TokenForall _ }
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
    LAMBDA  { TokenLambda _ }

%right in
%right '->'
%left ':'
%nonassoc LAMBDA
%left '+' '-'
%left '*'
%%

Program :: { (Program, [Option]) }
  : LangOpts Defs  { ($2 $1, $1) }

LangOpts :: { [Option] }
  : LANG NL LangOpts    {% (readOption $1) >>= (\opt -> addOption opt $3) }
  | LANG                {% readOption $1 >>= (return . (:[])) }
  | {- empty -}         { [] }

Defs :: { [Option] -> Program }
  : Def NL Defs           { \opts -> ($1 opts) : ($3 opts) }
  | return Expr           { \opts -> [Return ($2 opts)] }
  | Def                   { \opts -> [$1 opts] }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Def :: { [Option] -> Def }
  : IDENT '=' Expr          { \opts -> VarDef (symString $1) Nothing ($3 opts) }
  | IDENT ':' Type '=' Expr { \opts -> VarDef (symString $1) (Just $ $3 opts) ($5 opts) } 
  | data IDENT ':' Kind '=' ConstructorList { \opts -> DataDef (symString $2) ($6 opts) ($4 opts) }

ConstructorList :: { [Option] -> [(Identifier, [Type 0])] }
ConstructorList
  : IDENT '|' ConstructorList { \opts -> ((symString $1) , []) : ($3 opts) }
  | IDENT                     { \opts -> [(symString $1, [])] }
  | {- empty -}              { \_ -> [] }

Expr :: { [Option] -> Expr }
  : let IDENT '=' Expr in Expr
    { \opts ->
      GenLet (symString $2) ($4 opts) ($6 opts) }

   -- TODO: probably needs reconciling with lambda syntax
  | Lam IDENT '->' Expr
    { \opts -> TyAbs (symString $2) ($4 opts) }

  | Form ':' Type
    { \opts -> Sig ($1 opts) ($3 opts) }

  | Form
    { $1 }

  | fix '(' Expr ')'
     { \opts -> Fix ($3 opts) }

  | natcase Expr of zero '->' Expr '|' succ IDENT '->' Expr
     { \opts -> NatCase ($2 opts) ($6 opts) (symString $9, ($11 opts)) }

  | fst '(' Expr ')'
     { \opts -> Fst ($3 opts) }

  | snd '(' Expr ')'
     { \opts -> Snd ($3 opts) }

  | inl '(' Expr ')'
     { \opts -> Inl ($3 opts) }

  | inr '(' Expr ')'
     { \opts -> Inr ($3 opts) }

 | case Expr of inl IDENT '->' Expr '|' inr IDENT '->' Expr
     { \opts -> Case ($2 opts) (symString $5, $7 opts) (symString $10, ($12 opts)) }

Form :: { [Option] -> Expr }
  : Form '+' Form  { \opts -> BinOp OpPlus ($1 opts) ($3 opts) }
  | Form '-' Form  { \opts -> BinOp OpMinus ($1 opts) ($3 opts) }
  | Form '*' Form  { \opts -> BinOp OpTimes ($1 opts) ($3 opts) }
  | Form '/' Form  { \opts -> BinOp OpDivide ($1 opts) ($3 opts) }
  | Juxt           { $1 }

Kind :: { [Option] -> Type 1 }
Kind
  : Kind '->' Kind   { \opts -> FunTy ($1 opts) ($3 opts) }
  | IDENT            { \opts -> case symString $1 of
                                  "type" -> TyCon "type"
                                  v -> error "TODO" }
  
Type :: { [Option] -> Type 0 }
Type
  : Type '->' Type        { \opts -> FunTy ($1 opts) ($3 opts) }
  | Type '*' Type         { \opts -> ProdTy ($1 opts) ($3 opts) }
  | Type '+' Type         { \opts -> SumTy ($1 opts) ($3 opts) }
  | Type '&' Type         { \opts -> WithTy ($1 opts) ($3 opts) }
  | Type '^' NumFloat     { \opts -> ExponentTy ($1 opts) $3 }
  | TypeAtom '(' Type ')' { \opts -> TyApp ($1 opts) ($3 opts) }
  | TypeAtom              { \opts -> $1 opts }
  | forall IDENT '.' Type { \opts -> Forall (symString $2) ($4 opts) }

NumFloat :: { Float }
NumFloat
  : FLOAT { let (TokenFloat _ x) = $1 in read x }
  | INT   { let (TokenInt _ x) = $1   in let r = (read x) :: Integer in fromIntegral r }

TypeAtom :: { [Option] -> Type 0 }
TypeAtom
  : IDENT            { \opts -> TyCon $ symString $1 }
  | TYVAR            { \opts -> TyVar $ tyVarString $1 }
  | '(' Type ')'     { \opts -> $2 opts }
  | INT              { \opts -> TyCon $ let (TokenInt _ x) = $1 in x }
  | '?'              { \opts -> TyCon "?" }

Juxt :: { [Option] -> Expr }
  : Juxt '(' Atom ')'                 { \opts -> App ($1 opts) ($3 opts) }
  | cast '(' Atom ')'                 { \opts -> Cast ($3 opts) }
  | Atom                      { $1 }

Atom :: { [Option] -> Expr }
  : '(' Expr ')'              { $2 }
  | IDENT                     { \opts -> Var $ symString $1 }
  | LAMBDA IDENT ':' Expr
    { \opts -> Abs (symString $2) Nothing ($4 opts) }
  | zero
    { \opts -> Zero }
  | succ
    { \opts -> Succ }

  | '@' TypeAtom
    { \opts -> TyEmbed ($2 opts) }

  | '<' Expr ', ' Expr '>'
     { \opts -> Pair ($2 opts) ($4 opts) }

  | FLOAT
     { \opts ->
          let (TokenFloat _ x) = $1
          in NumFloat $ read x }

  | INT
     { \opts ->
          let (TokenInt _ x) = $1
          in NumFloat $ fromIntegral $ read x }

  -- For later
  -- | '?' { Hole }
{

readOption :: Token -> ReaderT String (Either String) Option
readOption (TokenLang _ x) = lift . Left $ "Unknown language option: " <> x
readOption _ = lift . Left $ "Wrong token for language"

parseError :: [Token] -> ReaderT String (Either String) a
parseError [] = lift . Left $ "Premature end of file"
parseError t  =  do
    file <- ask
    lift . Left $ file <> ":" <> show l <> ":" <> show c
                        <> ": parse error"
  where (l, c) = getPos (head t)

parseProgram :: FilePath -> String -> Either String (Program, [Option])
parseProgram file input = runReaderT (program $ scanTokens input) file

}