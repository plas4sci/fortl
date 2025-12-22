{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Kinding where

-- import Control.Monad
import Lang.Syntax
import Lang.Primitives
import Lang.TypeError

-- Check if a type is well-kinded against the second argument (kind)
checkKind :: Type 0 -> Type 1 -> Either TypeError ()
checkKind (FunTy t1 t2) k = do
  checkKind t1 k
  checkKind t2 k

checkKind t@(TyApp t1 t2) k = do
  k1 <- synthKind t1
  case k1 of
    FunTy k1' k2 ->
      if k == k2
        then checkKind t2 k1'
        else Left $ KindMismatch k k2 t
    _ -> Left $ ExpectingFunctionKind k

-- Allow constructors of any abelian group to get checked
-- as we will form a free abelian group over some arbitrary set of generators
checkKind (TyCon c) k | k == agroup =
  return ()

checkKind t k = do
  k' <- synthKind t
  if k == k'
    then Right ()
    else Left $ KindMismatch k k' t

-- Infer a kind for a type
synthKind :: Type 0 -> Either TypeError (Type 1)
synthKind (TyCon c) =
  case lookup c typeConstructors of
    Nothing -> Left $ UnknownTypeConstructor c
    Just k' -> Right k'

synthKind (TyApp t1 t2) = do
  k <- synthKind t1
  case k of
    FunTy k1 k2 -> do
        checkKind t2 k1
        return k2
    _ -> Left $ ExpectingFunctionKind k

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

synthKind (IntersectTy t1 t2) =
  -- Symmetry of intersectTy despite its asymmetry
  (do
    checkKind t1 type0
    checkKind t2 desc
    return type0)
  <|>
   -- Two descriptiors
  (do
    checkKind t1 desc
    checkKind t2 desc
    return desc)
 <|>
  (do
    checkKind t1 desc
    checkKind t2 type0
    return type0)

synthKind (TyVar t) =
  -- TODO: allow generalisation of type variables
  return type0

synthKind (Forall v t) =
  -- TODO: need type variable environment
  synthKind t

-- synthKind t = Left $ "Cannot infer kind for " <> pprint t

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

(<|>) :: Either String (Type 1) -> Either String (Type 1) -> Either String (Type 1)
(Left err) <|> (Left err') =
  -- TODO: generalise using error data type
  -- Filter out certain kinds of error here that are to do with
  -- overloading
  if "expecting kind" `isInfixOf` err
    then Left err'
    else
      if "expecting kind" `isInfixOf` err
        then Left err
        else
          Left ("No resolution. Either: \n" <> indent err <> "\nor\n" <> indent err')

(Right x) <|> _ = Right x
_ <|> (Right x) = Right x

indent :: String -> String
indent = unlines . map ("  " <>) . lines