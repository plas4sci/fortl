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
%name typeParser Type
%tokentype { Token }
%error { parseError }
%monad { ReaderT String (Either String) }

%token
    nl      { TokenNL _ }
    data    { TokenData _ }
    from    { TokenFrom _ }
    import  { TokenImport _ }
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
    STRING  { TokenString _ _ }
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
    '['     { TokenLBrack _ }
    ']'     { TokenRBrack _ }
    '{'     { TokenLBrace _ }
    '}'     { TokenRBrace _ }
    ','     { TokenMPair _ }
    '.'     { TokenDot _ }
    '@'     { TokenAt _ }
    LAMBDA  { TokenLambda _ }

%right in
%right '->'
%left ':'
%nonassoc LAMBDA
%left ','
%left '+' '-'
%left '*'
%%

Program :: { (Program 'Parsed, [Option]) }
  : LangOpts Imports Defs  { ($2 ++ ($3 $1), $1) }

LangOpts :: { [Option] }
  : LANG NL LangOpts    {% (readOption $1) >>= (\opt -> addOption opt $3) }
  | LANG                {% readOption $1 >>= (return . (:[])) }
  | {- empty -}         { [] }

Imports :: { [Def 'Parsed] }
  : Import NL Imports   { $1 : $3 }
  | Import              { [$1] }
  | {- empty -}         { [] }

Import :: { Def 'Parsed }
  : import IDENT                 { ImportDef (ImportModule (symString $2)) }
  | from IDENT import '*'        { ImportDef (ImportAll (symString $2)) }
  | from IDENT import ImportList { ImportDef (ImportOnly (symString $2) $4) }

ImportList :: { [Identifier] }
  : IDENT ',' ImportList { (symString $1) : $3 }
  | IDENT                { [symString $1] }

Defs :: { [Option] -> Program 'Parsed }
  : Def NL Defs           { \opts -> ($1 opts) : ($3 opts) }
  | return Expr           { \opts -> [Return ($2 opts)] }
  | Def                   { \opts -> [$1 opts] }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Def :: { [Option] -> Def 'Parsed}
  : Lhs '=' Expr          { \opts -> ValDef ($1 opts) ($3 opts) }
  | data IDENT ':' Kind '=' ConstructorList { \opts -> DataDef (symString $2) ($6 opts) ($4 opts) }

Lhs :: { [Option] -> Lhs 'Parsed }
  : IDENT { \opts -> VarLhs (symString $1) Nothing }
  | IDENT ':' Type { \opts -> VarLhs (symString $1) (Just $ $3 opts) }
  | Lhs ',' Lhs { \opts -> PairLhs ($1 opts) ($3 opts) }
  | '(' Lhs ')' { $2 }

ConstructorList :: { [Option] -> [(Identifier, [Type 0])] }
ConstructorList
  : IDENT '|' ConstructorList { \opts -> ((symString $1) , []) : ($3 opts) }
  | IDENT                     { \opts -> [(symString $1, [])] }
  | {- empty -}              { \_ -> [] }

Expr :: { [Option] -> Expr }
  : let IDENT '=' Expr in Expr
    { \opts ->
      MkGenLet (mkPos $1) (symString $2) ($4 opts) ($6 opts) }

   -- TODO: probably needs reconciling with lambda syntax
  | Lam IDENT '->' Expr
    { \opts -> MkTyAbs (mkPos $1) (symString $2) ($4 opts) }

  | Form ':' Type
    { \opts -> MkSig (mkPos $2) ($1 opts) ($3 opts) }

  | Form
    { $1 }

  | fix '(' Expr ')'
     { \opts -> MkFix (mkPos $1) ($3 opts) }

  | natcase Expr of zero '->' Expr '|' succ IDENT '->' Expr
     { \opts -> MkNatCase (mkPos $1) ($2 opts) ($6 opts) (symString $9, ($11 opts)) }

  | fst '(' Expr ')'
     { \opts -> MkFst (mkPos $1) ($3 opts) }

  | snd '(' Expr ')'
     { \opts -> MkSnd (mkPos $1) ($3 opts) }

  | inl '(' Expr ')'
     { \opts -> MkInl (mkPos $1) ($3 opts) }

  | inr '(' Expr ')'
     { \opts -> MkInr (mkPos $1) ($3 opts) }

 | case Expr of inl IDENT '->' Expr '|' inr IDENT '->' Expr
     { \opts -> MkCase (mkPos $1) ($2 opts) (symString $5, $7 opts) (symString $10, ($12 opts)) }

Form :: { [Option] -> Expr }
  : Form '+' Form  { \opts -> MkBinOp (mkPos $2) OpPlus ($1 opts) ($3 opts) }
  | Form '-' Form  { \opts -> MkBinOp (mkPos $2) OpMinus ($1 opts) ($3 opts) }
  | Form '*' Form  { \opts -> MkBinOp (mkPos $2) OpTimes ($1 opts) ($3 opts) }
  | Form '^' NumFloat  { \opts -> MkBinOp (mkPos $2) OpExp ($1 opts) (MkNumFloat (mkPos $2) $3) }
  | Form '/' Form  { \opts -> MkBinOp (mkPos $2) OpDivide ($1 opts) ($3 opts) }
  | Juxt           { $1 }

Kind :: { [Option] -> Type 1 }
Kind
  : Kind '->' Kind   { \opts -> FunTy ($1 opts) ($3 opts) }
  | IDENT            { \opts -> case symString $1 of
                                  k -> tyCon1 k }
  
Type :: { [Option] -> Type 0 }
Type
  : Type '->' Type        { \opts -> FunTy ($1 opts) ($3 opts) }
  | Type '*' Type         { \opts -> ProdTy ($1 opts) ($3 opts) }
  | Type '+' Type         { \opts -> SumTy ($1 opts) ($3 opts) }
  | Type '&' Type         { \opts -> WithTy ($1 opts) ($3 opts) }
  | Type '^' NumFloat     { \opts -> ExponentTy ($1 opts) $3 }
  | Type '/' Type         { \opts -> ProdTy ($1 opts) (ExponentTy ($3 opts) (-1)) }
  | TypeAtom '[' '{' Kind '}' ']' { \opts -> ImplicitTyApp ($1 opts) ($4 opts) }
  | TypeAtom '[' Type ']' { \opts -> TyApp ($1 opts) ($3 opts) }
  | TypeAtom              { \opts -> $1 opts }
  | forall IDENT '.' Type { \opts -> Forall (symString $2) ($4 opts) }

NumFloat :: { Float }
NumFloat
  : FLOAT { let (TokenFloat _ x) = $1 in read x }
  | INT   { let (TokenInt _ x) = $1   in let r = (read x) :: Integer in fromIntegral r }

TypeAtom :: { [Option] -> Type 0 }
TypeAtom
  : IDENT            { \opts -> tyCon0 $ symString $1 }
  | TYVAR            { \opts -> TyVar $ tyVarString $1 }
  | '(' Type ')'     { \opts -> $2 opts }
  | INT              { \opts -> tyCon0 $ let (TokenInt _ x) = $1 in x }
  | '?'              { \opts -> tyCon0 "?" }

Juxt :: { [Option] -> Expr }
  : Juxt '(' Atom ')'                 { \opts -> App ($1 opts) ($3 opts) }
  | cast '(' Atom ')'                 { \opts -> MkCast (mkPos $1) ($3 opts) }
  | Atom                      { $1 }

Atom :: { [Option] -> Expr }
  : '(' Expr ')'              { $2 }
  | IDENT                     { \opts -> MkVar (mkPos $1) (symString $1) }
  | LAMBDA IDENT ':' Expr
    { \opts -> MkAbs (mkPos $1) (symString $2) Nothing ($4 opts) }
  | zero
    { \opts -> MkZero (mkPos $1) }
  | succ
    { \opts -> MkSucc (mkPos $1) }

  | '@' TypeAtom
    { \opts -> MkTyEmbed (mkPos $1) ($2 opts) }

  | Expr ',' Expr
     { \opts -> Pair ($1 opts) ($3 opts) }

  | FLOAT
     { \opts ->
          let (TokenFloat _ x) = $1
          in MkNumFloat (mkPos $1) (read x) }

  | INT
     { \opts ->
          let (TokenInt _ x) = $1
          in MkNumInteger (mkPos $1) (fromIntegral $ read x) }

    | STRING
       { \opts ->
      let (TokenString _ x) = $1
      in MkStringConst (mkPos $1) (read x) }

  -- For later
  -- | '?' { Hole }
{

mkPos :: Token -> Maybe SrcPos
mkPos t = let (l, c) = getPos t in Just (SrcPos l c)

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

parseExpr :: String -> Either String Expr
parseExpr input = runReaderT (expr $ scanTokens input) ""
 >>= (\f -> return $ f [])

parseType :: String -> Either String (Type 0)
parseType input = runReaderT (typeParser $ scanTokens input) ""
 >>= (\f -> return $ f [])


parseProgram :: FilePath -> String -> Either String (Program 'Parsed, [Option])
parseProgram file input = runReaderT (program $ scanTokens input) file

}