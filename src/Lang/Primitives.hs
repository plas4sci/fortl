{-# LANGUAGE DataKinds #-}

module Lang.Primitives where

import Lang.Syntax

type0 :: Type 1
type0 = TyCon "Type"

natTy :: Type 0
natTy = TyCon "Nat"

floatTy :: Type 0 -> Type 0
floatTy t = TyApp (TyCon "Float") t

integerTy :: Type 0 -> Type 0
integerTy t = TyApp (TyCon "Integer") t

agroup :: Type 1
agroup = TyCon "AbelianGroup"

desc :: Type 1
desc = TyCon "Descriptor"

typeConstructors :: [(Identifier, Type 1)]
typeConstructors = [
    ("Float", FunTy "" desc type0)   -- Graded float
  , ("Integer", FunTy "" desc type0) -- Graded integer
  , ("Nat"  , type0)
  , ("Unit" , FunTy "" agroup desc)
  , ("Quantity", FunTy "" agroup desc)
  , ("1", agroup)
  , ("Vec", FunTy "n" (TyCon "Nat") type0)
  -- SI Units
  , ("M", agroup)
  , ("S", agroup)
  , ("Kg", agroup)
  , ("J", agroup)
 ]

-- Which type constructors can be promoted to type level
promotable :: [Identifier]
promotable = ["Nat"]

-- | Check if a type constructors a descriptor
isDescConstructor :: Identifier -> Maybe (Type 1)
isDescConstructor conId =
  case lookup conId typeConstructors of
    Just k@(FunTy _ _ t) | t == desc -> Just k
    _                                -> Nothing


valueConstructors :: [(Identifier, Type 0)]
valueConstructors = [
    ("zero", natTy)
  , ("succ", FunTy "" natTy natTy)
  ]