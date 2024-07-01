{-# LANGUAGE DataKinds #-}

module Lang.Primitives where

import Lang.Syntax

type0 :: Type 1
type0 = TyCon "Type"

natTy :: Type 0
natTy = TyCon "Nat"

floatTy :: Type 0
floatTy = TyCon "Float"

agroup :: Type 1
agroup = TyCon "AbelianGroup"

desc :: Type 1
desc = TyCon "Descriptor"

-- | Representation of the top of the intersection types
omega :: String
omega = "?"

typeConstructors :: [(Identifier, Type 1)]
typeConstructors = [
    (omega, desc)
  , ("Float", type0)
  , ("Nat"  , type0)
  , ("Unit" , FunTy agroup desc)
  , ("Quantity", FunTy agroup desc)
  , ("1", agroup)
  -- SI Units
  , ("M", agroup)
  , ("S", agroup)
  , ("Kg", agroup)
  , ("J", agroup)
 ]

-- | Check if a type constructors a descriptor
isDescConstructor :: Identifier -> Maybe (Type 1)
isDescConstructor conId =
  case lookup conId typeConstructors of
    Just k@(FunTy _ t) | t == desc -> Just k
    _                              -> Nothing