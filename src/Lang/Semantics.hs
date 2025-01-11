{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Semantics where

import Lang.Syntax
import Lang.Options
-- import Debug.Trace

import qualified Data.Set as Set

type Env = [(Identifier, Expr PCF)]

-- Evaluate a program to normal form
interpret :: [Option] -> Program PCF -> Expr PCF
interpret = interpretDefs []

-- Interpret the definitions, including building an environment
-- for the rest of the program
interpretDefs :: Env -> [Option] -> Program PCF -> Expr PCF

interpretDefs env opts ((VarDef v _ e):defs) = 
  case multiStep env opts e of
    (e', _) -> interpretDefs (env ++ [(v, e')]) opts defs

-- Return expression
interpretDefs env opts ((Return e):defs) = 
  fst $ multiStep env opts e

interpretDefs env opts (_:defs ) = interpretDefs env opts defs

interpretDefs env opts [] = error "No return statement"

-- Keep doing small step reductions until normal form reached
multiStep :: Env -> [Option] -> Expr PCF -> (Expr PCF, Int)
multiStep env opts e = multiStep' env callByValue e 0

type Reducer a = Env -> a -> Maybe a

multiStep' :: Env -> Reducer (Expr PCF) -> Expr PCF -> Int -> (Expr PCF, Int)
multiStep' env step t n =
  case step env t of
    -- Normal form reached
    Nothing -> (t, n)
    -- Can do more reduction
    Just t' -> multiStep' env step t' (n+1)

callByValue :: Reducer (Expr PCF)
callByValue env (Var _) = Nothing
callByValue env (App (Abs x _ e) e') | isValue e' = beta e x e'
-- Poly beta
callByValue env (App (TyAbs var e) (TyEmbed t)) = beta e var (TyEmbed t)
callByValue env (App e1 e2) | isValue e1 = zeta2 env callByValue e1 e2
callByValue env (App e1 e2) = zeta1 env callByValue e1 e2
callByValue env (Abs x _ e) = Nothing
callByValue env (Sig e _)   = Just e
callByValue env (Cast e)    = Just e
callByValue env (Ext e)     = reducePCF env callByValue (Ext e)
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
zeta1 :: Env -> Reducer (Expr PCF) -> Expr PCF -> Expr PCF -> Maybe (Expr PCF)
zeta1 env step e1 e2 = (\e1' -> App e1' e2) <$> step env e1

zeta2 :: Env -> Reducer (Expr PCF)  -> Expr PCF -> Expr PCF -> Maybe (Expr PCF)
zeta2 env step e1 e2 = (\e2' -> App e1 e2') <$> step env e2

zeta3 :: Env -> Reducer (Expr PCF)  -> Identifier -> Expr PCF -> Maybe (Expr PCF)
zeta3 env step x e = (\e' -> Abs x Nothing e') <$> step env e

zeta3Ty :: Env -> Reducer (Expr PCF)  -> Identifier -> Expr PCF -> Maybe (Expr PCF)
zeta3Ty env step x e = (\e' -> TyAbs x e') <$> step env e


-- Reducer for the extended PCF syntax
reducePCF :: Env -> Reducer (Expr PCF) -> Expr PCF -> Maybe (Expr PCF)

-- Fix point
reducePCF env step (Ext (Fix e)) = return $ App e (Ext $ Fix e)

-- Beta-rules for Nat
reducePCF env step (Ext (NatCase (Ext Zero) e1 _)) = Just e1

reducePCF env step (Ext (NatCase (App (Ext Succ) n) _ (x,e2))) = Just $ substitute e2 (x,n)

-- Congruence for Nat-eliminator
reducePCF env step (Ext (NatCase e e1 (x,e2))) =
  (\e' -> Ext (NatCase e' e1 (x,e2))) <$> step env e

-- Congruence for productor constructor
reducePCF env step (Ext (Pair e1 e2)) =
  case step env e1 of
    Just e1' -> Just $ Ext $ Pair e1' e2
    Nothing -> (\e2' -> Ext $ Pair e1 e2') <$> step env e2

-- Beta-rules for products
reducePCF env step (Ext (Fst (Ext (Pair e1 e2)))) = Just e1
reducePCF env step (Ext (Snd (Ext (Pair e1 e2)))) = Just e2

-- Congruence rules for product eliminators
reducePCF env step (Ext (Fst e)) = (\e' -> Ext $ Fst e') <$> step env e
reducePCF env step (Ext (Snd e)) = (\e' -> Ext $ Snd e') <$> step env e

-- Beta-rules for sum types
reducePCF env step (Ext (Case (Ext (Inl e)) (x,e1) _)) = Just $ substitute e1 (x,e)
reducePCF env step (Ext (Case (Ext (Inr e)) _ (y,e2))) = Just $ substitute e2 (y,e)

-- Congruence for sum eliminator
reducePCF env step (Ext (Case e (x,e1) (y,e2))) =
  (\e' -> Ext (Case e' (x,e1) (y,e2))) <$> step env e

-- Congruence for sum constructor
reducePCF env step (Ext (Inl e)) = (\e' -> Ext $ Inl e') <$> step env e
reducePCF env step (Ext (Inr e)) = (\e' -> Ext $ Inr e') <$> step env e

-- Binary oeprators
reducePCF env step (Ext (BinOp op (Ext (NumFloat v1)) (Ext (NumFloat v2)))) =
  case op of
    OpPlus   -> return $ Ext (NumFloat $ v1 + v2)
    OpTimes  -> return $ Ext (NumFloat $ v1 * v2)
    OpMinus  -> return $ Ext (NumFloat $ v1 - v2)
    OpDivide -> return $ Ext (NumFloat $ v1 / v2)

reducePCF env step (Ext (BinOp op e1 e2)) =
  case step env e1 of
    Just e1' -> Just $ Ext $ BinOp op e1' e2
    Nothing -> (\e2' -> Ext $ BinOp op e1 e2') <$> step env e2

-- other Ext terms
reducePCF env step (Ext _) = Nothing

-- Non Ext terms
reducePCF _ _ _ = error "invalid term"

class Substitutable e where
  substitute :: e -> (Identifier, e) -> e

instance Substitutable (Expr PCF) where
  substitute = substituteExpr

-- Syntactic substitution - `substituteExpr e (x, e')` means e[e'/x]
substituteExpr :: Expr PCF -> (Identifier, Expr PCF) -> Expr PCF
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
substituteExpr (Ext Zero) s = Ext Zero
substituteExpr (Ext Succ) s = Ext Succ

substituteExpr (Ext (Fix e)) s = Ext $ Fix $ substituteExpr e s

substituteExpr (Ext (NatCase e e1 (y,e2))) s =
  let e'  = substituteExpr e s
      e1' = substituteExpr e1 s
      (y', e2') = substitute_binding y e2 s
  in Ext $ NatCase e' e1' (y', e2')

substituteExpr (Ext (Pair e1 e2)) s =
  Ext $ Pair (substituteExpr e1 s) (substituteExpr e2 s)

substituteExpr (Ext (Fst e)) s = Ext $ Fst $ substituteExpr e s
substituteExpr (Ext (Snd e)) s = Ext $ Snd $ substituteExpr e s

substituteExpr (Ext (Case e (x,e1) (y,e2))) s =
  let e' = substituteExpr e s
      (x', e1') = substitute_binding x e1 s
      (y', e2') = substitute_binding y e2 s
  in Ext $ Case e' (x', e1') (y', e2')

substituteExpr (Ext (Inl e)) s = Ext $ Inl $ substituteExpr e s
substituteExpr (Ext (Inr e)) s = Ext $ Inr $ substituteExpr e s

substituteExpr (Ext (NumFloat n)) s = Ext $ NumFloat n

substituteExpr (Ext (BinOp op e1 e2)) s =
  Ext $ BinOp op (substituteExpr e1 s) (substituteExpr e2 s)

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
