{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Syntax where

import qualified Data.Set as Set
import GHC.TypeLits

type Identifier = String

type Program ex = [Def ex]

data Def ex where
    VarDef  :: Identifier -> Maybe (Type n) -> Expr ex -> Def ex
    TypeDef :: Identifier -> Type n -> Type (1 + n) -> Def ex
    DataDef :: Identifier -> [(Identifier, Type n)] -> Type (1 + n) -> Def ex
    Return  :: Expr ex -> Def ex

-- Abstract-syntax tree for LambdaCore
-- parameterised by an additional type `ex`
-- used to represent the abstract syntax
-- tree of additional commands
data Expr ex where
    Abs :: Identifier -> Maybe (Type 0) -> Expr ex -> Expr ex
                                            -- \x -> e  [λ x . e] (Curry style)
                                            -- or
                                            -- \(x : A) -> e (Church style)
    App :: Expr ex ->  Expr ex   -> Expr ex -- e1 e2
    Var :: Identifier            -> Expr ex -- x

    Sig :: Expr ex -> Type 0     -> Expr ex -- e : A

    -- Poly
    TyAbs   :: Identifier -> Expr ex -> Expr ex -- /\ a -> e
    TyEmbed :: Type 0                -> Expr ex -- @A

    -- ML
    GenLet :: Identifier -> Expr ex -> Expr ex -> Expr ex -- let x = e1 in e2 (ML-style polymorphism)

    -- Casts
    Cast :: Expr ex -> Expr ex

    -- Extend the ast at this point
    Ext :: ex -> Expr ex
  deriving Show

----------------------------
-- Extend the language to PCF (natural number constructors
-- and deconstructor + fixed point)

data PCF =
    NatCase (Expr PCF) (Expr PCF) (Identifier, Expr PCF)
                               -- case e of zero -> e1 | succ x -> e2
  | Fix (Expr PCF)             -- fix(e)
  | Succ                       -- succ (function)
  | Zero                       -- zero
  | Pair (Expr PCF) (Expr PCF) -- <e1, e2>
  | Fst (Expr PCF)             -- fst(e)
  | Snd (Expr PCF)             -- snd(e)
  | Inl (Expr PCF)             -- inl(e)
  | Inr (Expr PCF)             -- inr(e)
  | Case (Expr PCF) (Identifier, Expr PCF) (Identifier, Expr PCF)
                               -- case e of inl x -> e1 | inr y -> e2
  | NumFloat Float
  | BinOp Op (Expr PCF) (Expr PCF)
  deriving Show

-- Operators
data Op = OpPlus | OpTimes | OpMinus | OpDivide
  deriving Show

isValue :: Expr PCF -> Bool
isValue Abs{}   = True
isValue TyAbs{} = True
isValue Var{}   = True
isValue (Ext (NumFloat _)) = True
isValue (Ext p) = isValuePCF p
isValue e       = isNatVal e

isNatVal :: Expr PCF -> Bool
isNatVal (Ext Zero)  = True
isNatVal (Ext Succ)  = True
isNatVal (App e1 e2) = isNatVal e1 && isNatVal e2
isNatVal _           = False

isValuePCF :: PCF -> Bool
isValuePCF (Pair e1 e2) = isValue e1 && isValue e2
isValuePCF (Inl e) = isValue e
isValuePCF (Inr e) = isValue e
isValuePCF Zero = True
isValuePCF Succ = True
isValuePCF (NumFloat f) = True
isValuePCF _ = False


------------------------------
-- Type syntax

data Type (n :: Nat) where
    FunTy :: Type l -> Type l -> Type l  -- A -> B

    TyCon :: Identifier -> Type l        -- K
    TyApp :: Type l -> Type l -> Type l  -- A B

    ProdTy :: Type 0 -> Type 0 -> Type 0 -- A * B
    SumTy  :: Type 0 -> Type 0 -> Type 0  -- A + B

    -- Polymorphic lambda calculus types
    TyVar :: Identifier -> Type 0           -- a
    Forall :: Identifier -> Type 0 -> Type 0 -- forall a . A

    -- Intersection types
    IntersectTy :: Type 0 -> Type 0 -> Type 0

    -- For units
    -- TODO: make just a type constructor
    ExponentTy :: Type 0 -> Float -> Type 0

deriving instance Ord (Type 0)
deriving instance Ord (Type 1)
deriving instance Eq (Type 0)
deriving instance Eq (Type 1)
deriving instance Show (Type 0)
deriving instance Show (Type 1)

----------------------------

class Term t where
  boundVars :: t -> Set.Set Identifier
  freeVars  :: t -> Set.Set Identifier
  mkVar     :: Identifier -> t

instance Term (Expr PCF) where
  boundVars (Abs var _ e)                = var `Set.insert` boundVars e
  boundVars (TyAbs var e)                = var `Set.insert` boundVars e
  boundVars (TyEmbed t)                  = boundVars t
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Var var)                    = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars (GenLet var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars (Cast e)                     = boundVars e
  boundVars (Ext (NatCase e e1 (x,e2)))  =
    x `Set.insert` (boundVars e `Set.union` boundVars e1 `Set.union` boundVars e2)
  boundVars (Ext (Fix e))                = boundVars e
  boundVars (Ext (Pair e1 e2))           = boundVars e1 `Set.union` boundVars e2
  boundVars (Ext (Fst e))                = boundVars e
  boundVars (Ext (Snd e))                = boundVars e
  boundVars (Ext (Inl e))                = boundVars e
  boundVars (Ext (Inr e))                = boundVars e
  boundVars (Ext (Case e (x,e1) (y,e2))) =
    boundVars e `Set.union` (x `Set.insert` boundVars e1) `Set.union` (y `Set.insert` boundVars e2)
  boundVars (Ext (BinOp _ e1 e2))        = boundVars e1 `Set.union` boundVars e2
  boundVars (Ext _)                      = Set.empty

  freeVars (Abs var _ e)                 = Set.delete var (freeVars e)
  freeVars (TyAbs var e)                 = Set.delete var (freeVars e)
  freeVars (TyEmbed t)                   = freeVars t
  freeVars (App e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Var var)                     = Set.singleton var
  freeVars (Sig e _)                     = freeVars e
  freeVars (GenLet var e1 e2)            = Set.delete var (freeVars e1 `Set.union` freeVars e2)
  freeVars (Cast e)                      = freeVars e
  freeVars (Ext (NatCase e e1 (x,e2)))   =
    freeVars e `Set.union` freeVars e1 `Set.union` (Set.delete x (freeVars e2))
  freeVars (Ext (Fix e))                 = freeVars e
  freeVars (Ext (Pair e1 e2))            = freeVars e1 `Set.union` freeVars e2
  freeVars (Ext (Fst e))                 = freeVars e
  freeVars (Ext (Snd e))                 = freeVars e
  freeVars (Ext (Inl e))                 = freeVars e
  freeVars (Ext (Inr e))                 = freeVars e
  freeVars (Ext (Case e (x,e1) (y,e2)))  =
    freeVars e `Set.union` (Set.delete x (freeVars e1)) `Set.union` (Set.delete y (freeVars e2))
  freeVars (Ext (BinOp _ e1 e2))         = freeVars e1 `Set.union` freeVars e2
  freeVars (Ext _)                       = Set.empty

  mkVar = Var

instance Term (Type 0) where
  boundVars (FunTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (ProdTy t1 t2) = boundVars t1 `Set.union` boundVars t2
  boundVars (SumTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyApp t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyCon _)      = Set.empty
  boundVars (TyVar var)    = Set.empty
  boundVars (Forall var t) = var `Set.insert` boundVars t
  boundVars (IntersectTy t1 t2) = boundVars t1 `Set.union` boundVars t2
  boundVars (ExponentTy t1 _) = boundVars t1

  freeVars (FunTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (ProdTy t1 t2) = freeVars t1 `Set.union` freeVars t2
  freeVars (SumTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyApp t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyCon _)      = Set.empty
  freeVars (TyVar var)    = Set.singleton var
  freeVars (Forall var t) = var `Set.delete` freeVars t
  freeVars (IntersectTy t1 t2) = freeVars t1 `Set.union` freeVars t2
  freeVars (ExponentTy t1 _) = freeVars t1

  mkVar = TyVar

  ----------------------------
-- Fresh variable with respect to a set of variables
-- By adding apostrophes to a supplied initial variable

fresh_var :: Identifier -> Set.Set Identifier -> Identifier
fresh_var var vars =
  if var `Set.member` vars then fresh_var (var ++ "'") vars else var