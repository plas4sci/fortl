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

interpretDefs env opts ((VarDef v _ e):defs) = 
  case multiStep env opts e of
    (e', _) -> interpretDefs (env ++ [(v, e')]) opts defs

-- Return expression
interpretDefs env opts ((Return e):defs) = 
  fst $ multiStep env opts e

interpretDefs env opts (_:defs ) = interpretDefs env opts defs

interpretDefs env opts [] = error "No return statement"

-- Keep doing small step reductions until normal form reached
multiStep :: Env -> [Option] -> Expr -> (Expr, Int)
multiStep env opts e = multiStep' env callByValue e 0

type Reducer a = Env -> a -> Maybe a

multiStep' :: Env -> Reducer Expr -> Expr -> Int -> (Expr, Int)
multiStep' env step t n =
  case step env t of
    -- Normal form reached
    Nothing -> (t, n)
    -- Can do more reduction
    Just t' -> multiStep' env step t' (n+1)

callByValue :: Reducer Expr
callByValue env (Var _) = Nothing
callByValue env (App (Abs x _ e) e') | isValue e' = beta e x e'
-- Poly beta
callByValue env (App (TyAbs var e) (TyEmbed t)) = beta e var (TyEmbed t)
callByValue env (App e1 e2) | isValue e1 = zeta2 env callByValue e1 e2
callByValue env (App e1 e2) = zeta1 env callByValue e1 e2
callByValue env (Abs x _ e) = Nothing
callByValue env (Sig e _)   = Just e
callByValue env (Cast e)    = Just e
-- PCF rules (previously in Ext)
callByValue env e@Fix{} = reducePCF env callByValue e
callByValue env e@NatCase{} = reducePCF env callByValue e
callByValue env e@Pair{} = reducePCF env callByValue e
callByValue env e@Fst{} = reducePCF env callByValue e
callByValue env e@Snd{} = reducePCF env callByValue e
callByValue env e@Case{} = reducePCF env callByValue e
callByValue env e@BinOp{} = reducePCF env callByValue e
callByValue env Zero = Nothing
callByValue env Succ = Nothing
callByValue env (NumFloat _) = Nothing
callByValue env e@Inl{} = reducePCF env callByValue e
callByValue env e@Inr{} = reducePCF env callByValue e
-- Poly
callByValue env (TyAbs x e) = Nothing
callByValue env (TyEmbed t) = Nothing
callByValue env (GenLet x e' e)
  | isValue e' = beta e x e'
  | otherwise = (callByValue env e') >>= (\e' -> return $ GenLet x e' e)

-- Base case
beta :: (Substitutable t) => t -> Identifier -> t -> Maybe t
beta e x e' = Just (substitute e (x, e'))

-- Inductive rules
zeta1 :: Env -> Reducer Expr -> Expr -> Expr -> Maybe Expr
zeta1 env step e1 e2 = (\e1' -> App e1' e2) <$> step env e1

zeta2 :: Env -> Reducer Expr  -> Expr -> Expr -> Maybe Expr
zeta2 env step e1 e2 = (\e2' -> App e1 e2') <$> step env e2

zeta3 :: Env -> Reducer Expr  -> Identifier -> Expr -> Maybe Expr
zeta3 env step x e = (\e' -> Abs x Nothing e') <$> step env e

zeta3Ty :: Env -> Reducer Expr  -> Identifier -> Expr -> Maybe Expr
zeta3Ty env step x e = (\e' -> TyAbs x e') <$> step env e


-- Reducer for the PCF syntax
reducePCF :: Env -> Reducer Expr -> Expr -> Maybe Expr

-- Fix point
reducePCF env step (Fix e) = return $ App e (Fix e)

-- Beta-rules for Nat
reducePCF env step (NatCase Zero e1 _) = Just e1

reducePCF env step (NatCase (App Succ n) _ (x,e2)) = Just $ substitute e2 (x,n)

-- Congruence for Nat-eliminator
reducePCF env step (NatCase e e1 (x,e2)) =
  (\e' -> NatCase e' e1 (x,e2)) <$> step env e

-- Congruence for productor constructor
reducePCF env step (Pair e1 e2) =
  case step env e1 of
    Just e1' -> Just $ Pair e1' e2
    Nothing -> (\e2' -> Pair e1 e2') <$> step env e2

-- Beta-rules for products
reducePCF env step (Fst (Pair e1 e2)) = Just e1
reducePCF env step (Snd (Pair e1 e2)) = Just e2

-- Congruence rules for product eliminators
reducePCF env step (Fst e) = (\e' -> Fst e') <$> step env e
reducePCF env step (Snd e) = (\e' -> Snd e') <$> step env e

-- Beta-rules for sum types
reducePCF env step (Case (Inl e) (x,e1) _) = Just $ substitute e1 (x,e)
reducePCF env step (Case (Inr e) _ (y,e2)) = Just $ substitute e2 (y,e)

-- Congruence for sum eliminator
reducePCF env step (Case e (x,e1) (y,e2)) =
  (\e' -> Case e' (x,e1) (y,e2)) <$> step env e

-- Congruence for sum constructor
reducePCF env step (Inl e) = (\e' -> Inl e') <$> step env e
reducePCF env step (Inr e) = (\e' -> Inr e') <$> step env e

-- Binary oeprators
reducePCF env step (BinOp op (NumFloat v1) (NumFloat v2)) =
  case op of
    OpPlus   -> return $ NumFloat $ v1 + v2
    OpTimes  -> return $ NumFloat $ v1 * v2
    OpMinus  -> return $ NumFloat $ v1 - v2
    OpDivide -> return $ NumFloat $ v1 / v2

reducePCF env step (BinOp op e1 e2) =
  case step env e1 of
    Just e1' -> Just $ BinOp op e1' e2
    Nothing -> (\e2' -> BinOp op e1 e2') <$> step env e2

-- other terms
reducePCF env step _ = Nothing

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
