{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Kinding where

-- import Control.Monad
import Lang.Syntax
import Lang.Primitives
import Lang.PrettyPrint

-- Check if a type is well-kinded against the second argument (kind)
checkKind :: Type 0 -> Type 1 -> Either String ()
checkKind (FunTy t1 t2) k = do
  checkKind t1 k
  checkKind t2 k

checkKind t@(TyApp t1 t2) k = do
  k1 <- synthKind t1
  case k1 of
    FunTy k1' k2 ->
      if k == k2
        then checkKind t2 k1'
        else Left $ "For " <> pprint t <> ", expecting kind " <> pprint k <> " but got " <> pprint k2
    _ -> Left $ "Expecting a function kind but got " <> pprint k

checkKind t k = do
  k' <- synthKind t
  if k == k'
    then Right ()
    else Left $ "For type " <> pprint t <> ", expecting kind " <> pprint k <> " but got kind " <> pprint k'

-- Infer a kind for a type
synthKind :: Type 0 -> Either String (Type 1)
synthKind (TyCon c) =
  case lookup c typeConstructors of
    Nothing -> Left $ "Unknown type constructor " <> c
    Just k' -> Right k'

synthKind (TyApp t1 t2) = do
  k <- synthKind t1
  case k of
    FunTy k1 k2 -> do
        checkKind t2 k1
        return k2
    _ -> Left $ "Expecting a function kind but got " <> pprint k

synthKind (FunTy t1 t2) = do
  k <- synthKind t1
  checkKind t2 k
  return k

synthKind (ProdTy t1 t2) = do
  synthCheckPair t1 t2

synthKind (SumTy t1 t2) = do
  synthCheckPair t1 t2

synthKind (ExponentTy t _) = do
  checkKind t agroup
  return agroup

synthKind (IntersectTy t1 t2) = do
  checkKind t1 type0
  checkKind t2 type0
  return type0

synthKind t = Left $ "Cannot infer kind for " <> pprint t

synthCheckPair :: Type 0 -> Type 0 -> Either String (Type 1)
synthCheckPair t1 t2 =
  -- Try to infer the kind of the first type
  case synthKind t1 of
    Left err -> do
      k <- synthKind t2
      checkKind t1 k
      return k

    Right k -> do
      checkKind t2 k
      return k