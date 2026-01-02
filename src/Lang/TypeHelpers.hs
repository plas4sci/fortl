{-# LANGUAGE DataKinds #-}

module Lang.TypeHelpers where

import Lang.Syntax

-- # Smart constructors

-- | Given a unit, construct its inverse
reciprocalType :: Type 0 -> Type 0
reciprocalType t = ExponentTy t (-1.0)

-- # Smart destructors

-- | Check if a type is an indexed type and extract the index
isGradedType :: Identifier -> Type 0 -> Maybe (Type 0)
isGradedType conId ty =
  case ty of
    TyApp (TyCon c) t | c == conId ->
      Just t
    TyCon "Float" -> Just (TyCon "1") -- TODO generalise so that this isn't a special case
    _ -> Nothing

-- # Equality helpers

-- Wrapper to indicate that something is specificational
data Specificational a = IsSpec { unwrapSpec :: a }

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM p []     = return True
allM p (x:xs) = do
    q <- p x
    if q then allM p xs else return False
