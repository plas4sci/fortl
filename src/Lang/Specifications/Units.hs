{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Specifications.Units where

import Lang.Syntax
import Lang.PrettyPrint
import Data.Map.Lazy

------------------------------------
-- # Unit-specific typing
------------------------------------

-- | Predicate on whether a type is a unit description: if so extract
-- the unit
isUnitTy :: Type 0 -> Maybe (Type 0)
isUnitTy (TyApp (TyCon "Unit") t) = Just t
isUnitTy _ = Nothing

-- | Matches on a type that is either a Float or an
-- intersection type containing a float, extracting its unit
floatWithUnit :: Type 0 -> Maybe (Type 0)

-- Dimensionless/unitless float
floatWithUnit (TyCon "Float") =
  Just (TyCon "1")

-- Extract the unit in any position of the intersection
floatWithUnit (IntersectTy (TyCon "Float") t) =
  isUnitTy t

-- Commutativity
floatWithUnit (IntersectTy t (TyCon "Float")) =
  floatWithUnit (IntersectTy (TyCon "Float") t)

-- TODO: Extensibility to other properties would need to come here
floatWithUnit t = Nothing

-- | Given a unit, construct its inverse
reciprocalUnit :: Type 0 -> Type 0
reciprocalUnit t = ExponentTy t (-1.0)

--------------------------------------------

unitEquality :: Type 0 -> Type 0 -> Bool
unitEquality u1 u2 =
    evalUnit u1 == evalUnit u2

type UnitRepr = Map Identifier Float

evalUnit :: Type 0 -> UnitRepr
evalUnit (TyCon "1") = empty
evalUnit (ExponentTy t n) = scale n (evalUnit t)
evalUnit (ProdTy t1 t2) =
  unionWith (+) (evalUnit t1) (evalUnit t2)
evalUnit (TyCon c) = singleton c 1.0
evalUnit t = error $ "Not well kinded unit " <> pprint t

scale :: Float -> UnitRepr -> UnitRepr
scale n = fmap (n *)

reifyUnit :: UnitRepr -> Type 0
reifyUnit =
  foldrWithKey (\k v t -> ExponentTy (TyCon k) v `ProdTy` t) (TyCon "1")

