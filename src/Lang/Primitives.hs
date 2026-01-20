{-# LANGUAGE DataKinds #-}

module Lang.Primitives where

import Lang.Syntax

type0 :: Type 1
type0 = TyCon "Type"

natTy :: Type 0
natTy = TyCon "Nat"

boolTy :: Type 0
boolTy = TyCon "Bool"

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
    ("Float", FunTy desc type0)   -- Graded float
  , ("Integer", FunTy desc type0) -- Graded integer
  , ("Bool", FunTy desc type0) -- Graded Boolean
  , ("Nat"  , type0)
  , ("Bool", type0)
  , ("Unit" , FunTy agroup desc)
  , ("Quantity", FunTy agroup desc)
  , ("1", agroup)
 ]

-- | Check if a type constructors a descriptor
isDescConstructor :: Identifier -> Maybe (Type 1)
isDescConstructor conId =
  case lookup conId typeConstructors of
    Just k@(FunTy t _) | t == desc -> Just k
    _                              -> Nothing

