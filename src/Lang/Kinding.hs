{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.Kinding where

-- import Control.Monad
import Lang.Syntax
import Lang.Primitives
import Lang.TypeError
import Lang.Substitution
import Lang.TypeHelpers

--import Debug.Trace

-- Check if a type is well-kinded against the second argument (kind)
-- and if so, elaborate any implicit arguments in the type
checkKind :: Type 0 -> Type 1 -> Either TypeError (Type 0)
checkKind (FunTy t1 t2) k = do
  t1' <- checkKind t1 k
  t2' <- checkKind t2 k
  return $ FunTy t1' t2'

-- e.g. Float[U[m]]
-- :k Float : {d : Desc} -> d -> Type
-- U[m] : UoM
-- therefore elaborate to Float[{UoM}][U[m]]
checkKind t@(TyApp t1 t2) k = do
  (t1', k1) <- synthKind t1
  case k1 of
    FunTy k1' k2 ->
        case kindEquality k2 (IsSpec k) of
          Left err -> Left err
          Right () -> do
               t2' <- checkKind t2 k1'
               return $ TyApp t1' t2'
    -- Since ImplictTys must come with an ImplicitTyApp
    -- then this means we have an implicit application here
    ImplicitFunTy var k1' (FunTy (TyVar var') k3) | var == var' -> do
      -- We therefore have to synth the kind of t2
      (t2', k2) <- synthKind t2
      -- this is now what we want to specialise k1' at
      return (TyApp (ImplicitTyApp t1 k2) t2')

      -- Now we know what k1 is
    _ -> Left $ ExpectingFunctionKind k1

-- :k Float : {d : Desc} -> d -> Type
-- :k (Float[{Base}]) : Base -> Type
checkKind t@(ImplicitTyApp t1 t2) k = do
  (t1', k1) <- synthKind t1              
  case k1 of
    -- t1 : {var : k1'} -> kres
    ImplicitFunTy var k1' kres -> do
      -- t2 : k1'
      t2' <- checkSort t2 k1'
      -- if so now we want to substitute
      -- i.e., [t2/var]kres
      let k_calc = substituteType kres (var, t2)
      -- now we need to check this matches `k`
--      _ <- checkKind t_calc k
      -- and this should match `k`
      if k == k_calc
        then return (ImplicitTyApp t1' t2')
        else Left $ KindMismatch k k_calc (Just t)
    _ -> Left $ ExpectingFunctionKind k

-- Allow constructors of any abelian group to get checked
-- as we will form a free abelian group over some arbitrary set of generators
checkKind t@(TyCon _ c) k | k == agroup =
  return t

checkKind t k = do
  (t', k') <- synthKind t
  if k == k'
    then Right t'
    else Left $ KindMismatch k k' (Just t)


checkSort :: Type 1 -> Type 2 -> Either TypeError (Type 1)
checkSort (FunTy t1 t2) k = do
  t1' <- checkSort t1 k
  t2' <- checkSort t2 k
  return $ FunTy t1' t2'

checkSort t@(TyApp t1 t2) k = do
  (t1', k1) <- synthSort t1
  case k1 of
    FunTy k1' k2 ->
        if k == k2
            then do
               t2' <- checkSort t2 k1'
               return $ TyApp t1' t2'
            else Left $ SortMismatch k k2 t
    _ -> Left $ ExpectingFunctionSort k

checkSort t k = do
  (t', k') <- synthSort t
  if k == k'
    then Right t'
    else Left $ SortMismatch k k' t

synthSort :: Type 1 -> Either TypeError (Type 1, Type 2)
synthSort t@(TyCon (SuccP ZeroP) c) =
    case lookup c kindConstructors of
      Nothing -> Left $ UnknownTypeConstructor c
      Just k' -> Right (t, k')

synthSort (TyCon (SuccP (SuccP _)) c) =
  error $ "Fortl bug: Should be inaccessible for " ++ c

synthSort (TyApp t1 t2) = do
  (t1', k) <- synthSort t1
  case k of
    FunTy k1 k2 -> do
        t2' <- checkSort t2 k1
        return (TyApp t1' t2', k2)
    _ -> Left $ ExpectingFunctionSort k

synthSort (FunTy t1 t2) = do
  (t1', k) <- synthSort t1
  t2'      <- checkSort t2 k
  return (FunTy t1' t2', k)

synthSort (ImplicitFunTy var t1 t2) = do
  -- TODO: need synthOrder?
--  (t1', _) <- synthSort t1
  (t2', k) <- synthSort t2
  return (ImplicitFunTy var t1 t2', k)

synthSort (WithTy t1 t2) = do
  -- Two descriptiors
  (t1', k) <- synthSort t1
  (t2', k') <- synthSort t2
  if k == k' 
    then return (WithTy t1' t2', k)
    else Left $ SortMismatch k k' (WithTy t1 t2)


-- TODO : no scoping of sort variables
synthSort (TyVar v) = return (TyVar v, TyCon (SuccP (SuccP ZeroP)) "Type")


-- Infer a kind for a type and elaborate the type
-- at the same time
synthKind :: Type 0 -> Either TypeError (Type 0, Type 1)

synthKind t@(TyCon ZeroP c) =
    case lookup c typeConstructors of
      Nothing -> --Left $ UnknownTypeConstructor c
                 Right (t, type0)
      Just k' -> Right (t, k')

synthKind (TyApp t1 t2) = do
  (t1', k) <- synthKind t1
  case k of
    FunTy k1 k2 -> do
        t2' <- checkKind t2 k1
        return (TyApp t1' t2', k2)

    ImplicitFunTy var k1' (FunTy (TyVar var') k3) | var == var' -> do
      -- We therefore have to synth the kind of t2
      (t2', k2) <- synthKind t2
      -- this is now what we want to specialise k1' at
      return (TyApp (ImplicitTyApp t1 k2) t2', k3)

    _ -> Left $ ExpectingFunctionKind k

synthKind (ImplicitTyApp t1 t2) = do
  (t1', k) <- synthKind t1
  case k of
    ImplicitFunTy var k1 k2 -> do
        t2' <- checkSort t2 k1
        let k_calc = substituteType k2 (var, t2)
        return (ImplicitTyApp t1' t2', k_calc)
    _ -> Left $ ExpectingFunctionKind k


synthKind (FunTy t1 t2) = do
  (t1', k) <- synthKind t1
  t2'      <- checkKind t2 k
  return (FunTy t1' t2', k)

synthKind (ProdTy t1 t2) = do
  (t1', t2', k) <- synthCheckPair t1 t2
  return $ (ProdTy t1' t2', k)

synthKind (SumTy t1 t2) = do
  (t1', t2', k) <- synthCheckPair t1 t2
  return $ (SumTy t1' t2', k) 

synthKind (ExponentTy t n) = do
 (t', k) <- synthKind t
 return (ExponentTy t' n, k)

synthKind (WithTy t1 t2) = do
  -- Two descriptiors
  (t1', k) <- synthKind t1
  (t2', k') <- synthKind t2
  return (WithTy t1' t2', WithTy k k')

synthKind t@(TyVar v) =
  -- TODO: allow generalisation of type variables
  return (t, type0)

synthKind (Forall v t) = do
  -- TODO: need type variable environment
  (t', k) <- synthKind t
  return (Forall v t', k)

-- synthKind t = Left $ CannotInferKind t

synthCheckPair :: Type 0 -> Type 0 -> Either TypeError (Type 0, Type 0, Type 1)
synthCheckPair t1 t2 =
  -- Try to infer the kind of the first type
  case synthKind t1 of
    Left err -> do
      (t2', k) <- synthKind t2
      t1' <- checkKind t1 k
      return (t1', t2', k)

    Right (t1', k) -> do
      t2' <- checkKind t2 k
      return (t1', t2', k)

indent :: String -> String
indent = unlines . map ("  " <>) . lines

kindEquality :: Type 1 -> Specificational (Type 1) -> Either TypeError ()
kindEquality (WithTy t1 t2) (IsSpec (WithTy t1' t2')) =
  (kindEquality t1 (IsSpec t1') >> kindEquality t2 (IsSpec t2')) <|>
  (kindEquality t1 (IsSpec t2') >> kindEquality t2 (IsSpec t1'))
kindEquality t1 (IsSpec t2) =
  if t1 == t2
    then Right ()
    else Left $ KindMismatch t2 t1 Nothing
