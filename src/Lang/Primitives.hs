{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Primitives where

import Lang.Syntax

type0 :: Type 1
type0 = tyCon1 "Type"

type1 :: Type 2
type1 = tyCon2 "Type"

natTy :: Type 0
natTy = tyCon0 "Nat"

floatTy :: Type 0 -> Type 0
floatTy t = TyApp (ImplicitTyApp (tyCon0 "Float") (tyCon1 "Base")) t

integerTy :: Type 0 -> Type 0
integerTy t = TyApp (ImplicitTyApp (tyCon0 "Integer") (tyCon1 "Base")) t

desc :: Type 1
desc = tyCon1 "Descriptor"

desc2 :: Type 2
desc2 = tyCon2 "Descriptor"


typeConstructors :: [(Identifier, Type 1)]
typeConstructors = [
     -- Graded float
    ("Float"    , ImplicitFunTy "d" desc2 (FunTy (tyVar "d") type0))
  , ("Integer"  , ImplicitFunTy "d" desc2 (FunTy (tyVar "d") type0)) -- Graded integer
  , ("Nat"      , type0)
  , ("Unit"     , FunTy type0 (tyCon1 "UoM"))
  , ("Quantity" , FunTy type0 (tyCon1 "KoQ"))
  , ("m"        , type0)
  , ("s"        , type0)
 ]

kindConstructors :: [(Identifier, Type 2)]
kindConstructors = [
    ("UoM"      , desc2)
  , ("KoQ"      , desc2)
  , ("Base"     , desc2) -- The base Descriptor (bottom)
  -- Products of descriptors
  , ("&"        , FunTy desc2 (FunTy desc2 desc2))
  ]

base :: Type 1
base = tyCon1 "Base"

agroup :: Type 1
agroup = tyCon1 "AGroup"

-- | Check if a type constructors a descriptor
isDescConstructor :: Identifier -> Maybe (Type 1)
isDescConstructor conId =
  case lookup conId typeConstructors of
    Just k@(FunTy t _) | t == desc -> Just k
    Just k@(ImplicitFunTy _ t _) | t == desc2 -> Just k
    _                              -> Nothing

