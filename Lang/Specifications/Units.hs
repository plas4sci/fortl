{-# LANGUAGE ViewPatterns #-}

module Lang.Specifications.Units where

import Lang.Syntax

------------------------------------
-- # Unit-specific typing
------------------------------------

-- | Predicate on whether a type is a unit description: if so extract
-- the unit
isUnitTy :: Type -> Maybe Type
isUnitTy (TyApp (TyCon "Unit") t) = Just t
isUnitTy _ = Nothing

-- | Matches on a type that is either a Float or an
-- intersection type containing a float, extracting its unit
floatWithUnit :: Type -> Maybe Type

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
reciprocalUnit :: Type -> Type
reciprocalUnit t = ExponentTy t (-1.0)