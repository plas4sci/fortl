{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.TypeHelpers where

import Lang.Syntax
import Lang.Primitives

-- Typing and kinding context: maps term/type-constructor names to their types
-- (Type 0). When used for kinding, a Lift is applied to promote to Type 1.
type Context = [(Identifier, Type 0)]

-- # Smart constructors

-- | Given a unit, construct its inverse
reciprocalType :: Type 0 -> Type 0
reciprocalType t = ExponentTy t (-1.0)

-- # Smart destructors

-- | Check if a type is a graded type and extract the grading type and the grade
isGradableNumericType :: Type 0 -> Maybe (Identifier, Type 1, Type 0)
isGradableNumericType ty =
  case ty of
    TyCon _ conId -> 
      case isDescConstructor conId of
        Just _  -> Just (conId, base, tyCon0 "1") -- Default index for base type
        Nothing -> Nothing
    TyApp (ImplicitTyApp (TyCon _ conId) gType) grade ->
      case isDescConstructor conId of
        Just _  -> Just (conId, gType, grade)
        Nothing -> Nothing
    _ -> Nothing

-- # Equality helpers

-- Wrapper to indicate that something is specificational
data Specificational a = IsSpec { unwrapSpec :: a }

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM p []     = return True
allM p (x:xs) = do
    q <- p x
    if q then allM p xs else return False
