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

type Program = [Def]

data Def where
    VarDef  :: Identifier -> Maybe (Type 0) -> Expr -> Def
    TypeDef :: Identifier -> Type n -> Type (1 + n) -> Def
    DataDef :: Identifier -> [(Identifier, [Type n])] -> Type (1 + n) -> Def
    Return  :: Expr -> Def

-- Abstract-syntax tree for LambdaCore with PCF extensions
data Expr where
    Abs :: Identifier -> Maybe (Type 0) -> Expr -> Expr
                                            -- \x -> e  [λ x . e] (Curry style)
                                            -- or
                                            -- \(x : A) -> e (Church style)
    App :: Expr ->  Expr   -> Expr -- e1 e2
    Var :: Identifier      -> Expr -- x

    Sig :: Expr -> Type 0  -> Expr -- e : A

    -- Poly
    TyAbs   :: Identifier -> Expr -> Expr -- /\ a -> e
    TyEmbed :: Type 0             -> Expr -- @A

    -- ML
    GenLet :: Identifier -> Expr -> Expr -> Expr -- let x = e1 in e2 (ML-style polymorphism)

    -- Casts
    Cast :: Expr -> Expr

    -- PCF extensions (previously in the PCF data type)
    NatCase :: Expr -> Expr -> (Identifier, Expr) -> Expr
                               -- case e of zero -> e1 | succ x -> e2
    Fix :: Expr              -> Expr             -- fix(e)
    Succ                     :: Expr             -- succ (function)
    Zero                     :: Expr             -- zero
    Pair :: Expr -> Expr     -> Expr             -- <e1, e2>
    Fst :: Expr              -> Expr             -- fst(e)
    Snd :: Expr              -> Expr             -- snd(e)
    Inl :: Expr              -> Expr             -- inl(e)
    Inr :: Expr              -> Expr             -- inr(e)
    Case :: Expr -> (Identifier, Expr) -> (Identifier, Expr) -> Expr
                               -- case e of inl x -> e1 | inr y -> e2
    NumFloat   :: Float        -> Expr
    NumInteger :: Integer      -> Expr
    BinOp :: Op -> Expr -> Expr -> Expr

    -- constructors
    Con   :: Identifier -> [Expr]  -> Expr
  deriving Show

-- Operators
data Op = OpPlus | OpTimes | OpMinus | OpDivide
  deriving Show

isValue :: Expr -> Bool
isValue Abs{}   = True
isValue TyAbs{} = True
isValue Var{}   = True
isValue (NumFloat _) = True
isValue (NumInteger _) = True
isValue Zero = True
isValue Succ = True
isValue (Pair e1 e2) = isValue e1 && isValue e2
isValue (Inl e) = isValue e
isValue (Inr e) = isValue e
isValue e       = isNatVal e

isNatVal :: Expr -> Bool
isNatVal Zero = True
isNatVal Succ = True
isNatVal (App e1 e2) = isNatVal e1 && isNatVal e2
isNatVal _           = False


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

    -- With types
    WithTy :: Type 0 -> Type 0 -> Type 0

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

instance Term Expr where
  boundVars (Abs var _ e)                = var `Set.insert` boundVars e
  boundVars (TyAbs var e)                = var `Set.insert` boundVars e
  boundVars (TyEmbed t)                  = boundVars t
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Var var)                    = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars (GenLet var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars (Cast e)                     = boundVars e
  boundVars (NatCase e e1 (x,e2))        =
    x `Set.insert` (boundVars e `Set.union` boundVars e1 `Set.union` boundVars e2)
  boundVars (Fix e)                      = boundVars e
  boundVars (Pair e1 e2)                 = boundVars e1 `Set.union` boundVars e2
  boundVars (Fst e)                      = boundVars e
  boundVars (Snd e)                      = boundVars e
  boundVars (Inl e)                      = boundVars e
  boundVars (Inr e)                      = boundVars e
  boundVars (Case e (x,e1) (y,e2))       =
    boundVars e `Set.union` (x `Set.insert` boundVars e1) `Set.union` (y `Set.insert` boundVars e2)
  boundVars (BinOp _ e1 e2)              = boundVars e1 `Set.union` boundVars e2
  boundVars _                            = Set.empty

  freeVars (Abs var _ e)                 = Set.delete var (freeVars e)
  freeVars (TyAbs var e)                 = Set.delete var (freeVars e)
  freeVars (TyEmbed t)                   = freeVars t
  freeVars (App e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Var var)                     = Set.singleton var
  freeVars (Sig e _)                     = freeVars e
  freeVars (GenLet var e1 e2)            = Set.delete var (freeVars e1 `Set.union` freeVars e2)
  freeVars (Cast e)                      = freeVars e
  freeVars (NatCase e e1 (x,e2))         =
    freeVars e `Set.union` freeVars e1 `Set.union` (Set.delete x (freeVars e2))
  freeVars (Fix e)                       = freeVars e
  freeVars (Pair e1 e2)                  = freeVars e1 `Set.union` freeVars e2
  freeVars (Fst e)                       = freeVars e
  freeVars (Snd e)                       = freeVars e
  freeVars (Inl e)                       = freeVars e
  freeVars (Inr e)                       = freeVars e
  freeVars (Case e (x,e1) (y,e2))        =
    freeVars e `Set.union` (Set.delete x (freeVars e1)) `Set.union` (Set.delete y (freeVars e2))
  freeVars (BinOp _ e1 e2)               = freeVars e1 `Set.union` freeVars e2
  freeVars _                             = Set.empty

  mkVar = Var

instance Term (Type 0) where
  boundVars (FunTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (ProdTy t1 t2) = boundVars t1 `Set.union` boundVars t2
  boundVars (SumTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyApp t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyCon _)      = Set.empty
  boundVars (TyVar var)    = Set.empty
  boundVars (Forall var t) = var `Set.insert` boundVars t
  boundVars (WithTy t1 t2) = boundVars t1 `Set.union` boundVars t2
  boundVars (ExponentTy t1 _) = boundVars t1

  freeVars (FunTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (ProdTy t1 t2) = freeVars t1 `Set.union` freeVars t2
  freeVars (SumTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyApp t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyCon _)      = Set.empty
  freeVars (TyVar var)    = Set.singleton var
  freeVars (Forall var t) = var `Set.delete` freeVars t
  freeVars (WithTy t1 t2) = freeVars t1 `Set.union` freeVars t2
  freeVars (ExponentTy t1 _) = freeVars t1

  mkVar = TyVar

  ----------------------------
-- Fresh variable with respect to a set of variables
-- By adding apostrophes to a supplied initial variable

fresh_var :: Identifier -> Set.Set Identifier -> Identifier
fresh_var var vars =
  if var `Set.member` vars then fresh_var (var ++ "'") vars else var