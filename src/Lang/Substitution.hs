{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}


module Lang.Substitution where

import Lang.Syntax

import qualified Data.Set as Set

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
substituteExpr (NumInteger n) s = NumInteger n
substituteExpr (StringConst str) s = StringConst str

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

substituteExpr (Con c es) s =
  Con c (map (`substituteExpr` s) es)

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

instance Substitutable (Type 1) where
    substitute = substituteType

class SubstituteType l where
  substituteType :: Type l -> (Identifier, Type l) -> Type l

instance SubstituteType 0 where
  substituteType (FunTy t1 t2) s =
    FunTy (substituteType t1 s) (substituteType t2 s)

  substituteType (TyCon p c) s = TyCon p c

  substituteType (ProdTy t1 t2) s =
    ProdTy (substituteType t1 s) (substituteType t2 s)

  substituteType (SumTy t1 t2) s =
    SumTy (substituteType t1 s) (substituteType t2 s)

  substituteType (ImplicitTyApp t1 t2) s =
    ImplicitTyApp (substituteType t1 s) t2

  substituteType (TyApp t1 t2) s =
    TyApp (substituteType t1 s) (substituteType t2 s)

  -- Actual substitution happening here
  substituteType (TyVar var) (varS, t)
    | var == varS  = t
    | otherwise    = TyVar var

  substituteType (Forall var t) s =
    let (var', t') = substitute_binding var t s in Forall var' t'

  substituteType (WithTy t1 t2) s =
    WithTy (substituteType t1 s) (substituteType t2 s)

  substituteType (ExponentTy t1 f) s =
    ExponentTy (substituteType t1 s) f


instance SubstituteType 1 where
  substituteType (ImplicitFunTy var t1 t2) s =
    let (var', t2') = substitute_binding var t2 s
    in ImplicitFunTy var' t1 t2'

  substituteType (FunTy t1 t2) s =
    FunTy (substituteType t1 s) (substituteType t2 s)

  substituteType (TyCon p c) s = TyCon p c

  substituteType (TyApp t1 t2) s =
    TyApp (substituteType t1 s) (substituteType t2 s)

  -- Actual substitution happening here
  substituteType (TyVar var) (varS, t)
    | var == varS  = t
    | otherwise    = TyVar var

  substituteType (WithTy t1 t2) s =
    WithTy (substituteType t1 s) (substituteType t2 s)

-- The 'type' (kind) of Float is
-- ImplicitFunTy "d" (FunTy (tyVar "d") type0)
-- therefore the type of the "d" part has to be also in Type 1
-- So then we might come along with Base which is not a Type (Type 0)
-- but a kind (Type 1)