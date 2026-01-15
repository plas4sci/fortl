{-# LANGUAGE DataKinds #-}

module Lang.Primitives where

import Lang.Syntax

type0 :: Type 1
type0 = TyCon "Type"

natTy :: Type 0
natTy = TyCon "Nat"

floatTy :: Type 0 -> Type 0
floatTy t = TyApp (TyCon "Float") t

agroup :: Type 1
agroup = TyCon "AbelianGroup"

desc :: Type 1
desc = TyCon "Descriptor"

typeConstructors :: [(Identifier, Type 1)]
typeConstructors = [
    ("Float", FunTy desc type0) -- Graded float
  , ("Nat"  , type0)
  , ("Unit" , FunTy agroup desc)
  , ("Quantity", FunTy agroup desc)
  , ("1", agroup)
 ]

-- | Check if a type constructors a descriptor
isDescConstructor :: Identifier -> Maybe (Type 1)
isDescConstructor conId =
  case lookup conId typeConstructors of
    Just k@(FunTy _ t) | t == desc -> Just k
    _                              -> Nothing

