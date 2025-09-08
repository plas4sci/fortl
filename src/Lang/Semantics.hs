{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Semantics where

import Lang.Syntax
import Lang.Options
-- import Debug.Trace

import qualified Data.Set as Set

type Env = [(Identifier, Expr)]

-- Evaluate a program to normal form
interpret :: [Option] -> Program -> Expr
interpret = interpretDefs []

-- Interpret the definitions, including building an environment
-- for the rest of the program
interpretDefs :: Env -> [Option] -> Program -> Expr

interpretDefs env opts ((VarDef id _ e):defs) = 
  case bigStep env opts e of
    Right v -> interpretDefs ((id, v) : env) opts defs
    Left err -> error err

-- Return expression
interpretDefs env opts ((Return e):defs) = 
  case bigStep env opts e of
    Right v -> v
    Left err -> error err

interpretDefs env opts (_:defs ) = interpretDefs env opts defs

interpretDefs env opts [] = error "No return statement"

-- Big step operational model (i.e., expression interpreter)
bigStep :: Env -> [Option] -> Expr -> Either String Expr
bigStep env opts (App e1 e2) =
  case bigStep env opts e1 of
    Left err -> Left err
    Right (Abs x _ body) ->
      case bigStep env opts e2 of
        Left err -> Left err
        Right v2 -> bigStep env opts (substitute body (x, v2))
    Right (TyAbs var body) ->
      case bigStep env opts e2 of
        Left err -> Left err
        Right (TyEmbed t) -> bigStep env opts (substitute body (var, TyEmbed t))
        Right _ -> Left "Type application expects a type"
    Right _ -> Left "Application expects a function"
bigStep env opts (Sig e _) = bigStep env opts e
bigStep env opts (Cast e) = bigStep env opts e
bigStep env opts (Var x) = case lookup x env of
  Just v  -> Right v
  Nothing -> Left $ "Unbound variable: " ++ x
bigStep env opts (GenLet x e1 e2) = do
  v1 <- bigStep env opts e1
  bigStep ((x, v1) : env) opts e2

bigStep env opts (NatCase eg ez (bind, es)) =
  case bigStep env opts eg of
    Left err -> Left err
    Right Zero -> bigStep env opts ez
    Right (App Succ n) -> bigStep ((bind, n):env) opts es
    Right _ -> Left "natcase expects a natural number"
bigStep env opts (Fix e) =
  case bigStep env opts e of
    Left err -> Left err
    Right (Abs x _ body) -> bigStep ((x, Fix (Abs x Nothing body)) : env) opts e
    Right _ -> Left "fix expects a function"
bigStep env opts (Case eg branchl branchr) = do
  v <- bigStep env opts eg
  case v of
    Inl e1 -> bigStep ((fst branchl, e1) : env) opts (snd branchl)
    Inr e2 -> bigStep ((fst branchr, e2) : env) opts (snd branchr)
    _      -> Left "case expects a sum type"
bigStep env opts (Fst e) =
  case bigStep env opts e of
    Right (Pair e1 _) -> bigStep env opts e1
    _         -> Left "fst expects a pair"
bigStep env opts (Snd e) =
  case bigStep env opts e of
    Right (Pair _ e2) -> bigStep env opts e2
    _         -> Left "snd expects a pair"
bigStep env opts (Pair e1 e2) = do
  v1 <- bigStep env opts e1
  v2 <- bigStep env opts e2
  return $ Pair v1 v2
bigStep env opts (Inl e) = Inl <$> bigStep env opts e
bigStep env opts (Inr e) = Inr <$> bigStep env opts e
bigStep env opts (BinOp op e1 e2) = do
  v1 <- bigStep env opts e1
  v2 <- bigStep env opts e2
  case (v1, v2) of
    (NumFloat n1, NumFloat n2) ->
      case op of
        OpPlus   -> return $ NumFloat $ n1 + n2
        OpTimes  -> return $ NumFloat $ n1 * n2
        OpMinus  -> return $ NumFloat $ n1 - n2
        OpDivide -> return $ NumFloat $ n1 / n2
    _ -> Left "Binary operation expects two numbers"

-- Values
bigStep env opts (TyEmbed e) = Right $ TyEmbed e -- TODO: remove this
bigStep env opts (TyAbs x e) = Right $ TyAbs x e
bigStep env opts (NumFloat f) = Right $ NumFloat f
bigStep env opts Succ = Right Succ
bigStep env opts Zero = Right Zero
bigStep env opts (Abs x mt body) = Right $ Abs x mt body

class Substitutable e where
  substitute :: e -> (Identifier, e) -> e

instance Substitutable Expr where
  substitute = substituteExpr

-- Syntactic substitution - `substituteExpr e (x, e')` means e[e'/x]
substituteExpr :: Expr -> (Identifier, Expr) -> Expr
substituteExpr (Var y) (x, e')
  | x == y = e'
  | otherwise = Var y

substituteExpr (App e1 e2) s =
  App (substituteExpr e1 s) (substituteExpr e2 s)

substituteExpr (Abs y mt e) s =
  let (y', e') = substitute_binding y e s in Abs y' mt e'

substituteExpr (Sig e t) s = Sig (substituteExpr e s) t

-- ML

substituteExpr (GenLet x e1 e2) s =
  let (x' , e2') = substitute_binding x e2 s in GenLet x' (substituteExpr e1 s) e2'

-- Casts
substituteExpr (Cast e) s =
  Cast (substituteExpr e s)

-- PCF terms
substituteExpr Zero s = Zero
substituteExpr Succ s = Succ

substituteExpr (Fix e) s = Fix $ substituteExpr e s

substituteExpr (NatCase e e1 (y,e2)) s =
  let e'  = substituteExpr e s
      e1' = substituteExpr e1 s
      (y', e2') = substitute_binding y e2 s
  in NatCase e' e1' (y', e2')

substituteExpr (Pair e1 e2) s =
  Pair (substituteExpr e1 s) (substituteExpr e2 s)

substituteExpr (Fst e) s = Fst $ substituteExpr e s
substituteExpr (Snd e) s = Snd $ substituteExpr e s

substituteExpr (Case e (x,e1) (y,e2)) s =
  let e' = substituteExpr e s
      (x', e1') = substitute_binding x e1 s
      (y', e2') = substitute_binding y e2 s
  in Case e' (x', e1') (y', e2')

substituteExpr (Inl e) s = Inl $ substituteExpr e s
substituteExpr (Inr e) s = Inr $ substituteExpr e s

substituteExpr (NumFloat n) s = NumFloat n

substituteExpr (BinOp op e1 e2) s =
  BinOp op (substituteExpr e1 s) (substituteExpr e2 s)

-- Poly

-- Substitute inside types
substituteExpr (TyEmbed t) (var, TyEmbed t') =
  TyEmbed (substituteType t (var, t'))

substituteExpr (TyEmbed t) (var, _) =
    TyEmbed t

substituteExpr (TyAbs y e) s =
  TyAbs y (substituteExpr e s)


-- substitute_binding x e (y,e') substitutes e' into e for y,
-- but assumes e has just had binder x introduced
substitute_binding :: (Term t, Substitutable t) => Identifier -> t -> (Identifier, t) -> (Identifier, t)
substitute_binding x e (y,e')
  -- Name clash in binding - we are done
  | x == y = (x, e)
  -- If expression to be bound contains already bound variable
  | x `Set.member` freeVars e' =
    let x' = fresh_var x (freeVars e `Set.union` freeVars e')
    in (x', substitute (substitute e (x, mkVar x')) (y, e'))
  | otherwise = (x, substitute e (y,e'))

instance Substitutable (Type 0) where
    substitute = substituteType

substituteType :: Type 0 -> (Identifier, Type 0) -> Type 0
substituteType (FunTy t1 t2) s =
  FunTy (substituteType t1 s) (substituteType t2 s)

substituteType (TyCon c) s = TyCon c

substituteType (ProdTy t1 t2) s =
  ProdTy (substituteType t1 s) (substituteType t2 s)

substituteType (SumTy t1 t2) s =
  SumTy (substituteType t1 s) (substituteType t2 s)

substituteType (TyApp t1 t2) s =
  TyApp (substituteType t1 s) (substituteType t2 s)

-- Actual substitution happening here
substituteType (TyVar var) (varS, t)
  | var == varS  = t
  | otherwise    = TyVar var

substituteType (Forall var t) s =
  let (var', t') = substitute_binding var t s in Forall var' t'

substituteType (IntersectTy t1 t2) s =
  IntersectTy (substituteType t1 s) (substituteType t2 s)

substituteType (ExponentTy t1 f) s =
  ExponentTy (substituteType t1 s) f
