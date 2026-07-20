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
checkKind :: Context -> Type 0 -> Type 1 -> Either TypeError (Type 0)
checkKind ctx (FunTy t1 t2) k = do
  t1' <- checkKind ctx t1 k
  t2' <- checkKind ctx t2 k
  return $ FunTy t1' t2'

-- e.g. Float[U[m]]
-- :k Float : {d : Desc} -> d -> Type
-- U[m] : UoM
-- therefore elaborate to Float[{UoM}][U[m]]
checkKind ctx t@(TyApp t1 t2) k = do
  (t1', k1) <- synthKind ctx t1
  case k1 of
    FunTy k1' k2 ->
        case kindEquality k2 (IsSpec k) of
          Left err -> Left err
          Right () -> do
               t2' <- checkKind ctx t2 k1'
               return $ TyApp t1' t2'
    -- Since ImplictTys must come with an ImplicitTyApp
    -- then this means we have an implicit application here
    ImplicitFunTy var k1' (FunTy (TyVar var') k3) | var == var' -> do
      -- We therefore have to synth the kind of t2
      (t2', k2) <- synthKind ctx t2
      -- this is now what we want to specialise k1' at
      return (TyApp (ImplicitTyApp t1 k2) t2')

      -- Now we know what k1 is
    _ -> Left $ ExpectingFunctionKind k1

-- :k Float : {d : Desc} -> d -> Type
-- :k (Float[{Base}]) : Base -> Type
checkKind ctx t@(ImplicitTyApp t1 t2) k = do
  (t1', k1) <- synthKind ctx t1
  case k1 of
    -- t1 : {var : k1'} -> kres
    ImplicitFunTy var k1' kres -> do
      -- t2 : k1'
      t2' <- checkSort ctx t2 k1'
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

-- -- Allow constructors of any abelian group to get checked
-- -- as we will form a free abelian group over some arbitrary set of generators
-- checkKind ctx t@(TyCon _ c) k | k == agroup =
--   return t

checkKind ctx t k = do
  (t', k') <- synthKind ctx t
  if k == k'
    then Right t'
    else Left $ KindMismatch k k' (Just t)


checkSort :: Context -> Type 1 -> Type 2 -> Either TypeError (Type 1)
checkSort ctx (FunTy t1 t2) k = do
  t1' <- checkSort ctx t1 k
  t2' <- checkSort ctx t2 k
  return $ FunTy t1' t2'

checkSort ctx t@(TyApp t1 t2) k = do
  (t1', k1) <- synthSort ctx t1
  case k1 of
    FunTy k1' k2 ->
        if k == k2
            then do
               t2' <- checkSort ctx t2 k1'
               return $ TyApp t1' t2'
            else Left $ SortMismatch k k2 t
    _ -> Left $ ExpectingFunctionSort k

checkSort ctx t k = do
  (t', k') <- synthSort ctx t
  if k == k'
    then Right t'
    else Left $ SortMismatch k k' t

synthSort :: Context -> Type 1 -> Either TypeError (Type 1, Type 2)
synthSort ctx t@(TyCon (SuccP ZeroP) c) =
    case lookup c kindConstructors of
      Nothing -> Left $ UnknownTypeConstructor c
      Just k' -> Right (t, k')

synthSort ctx (TyCon (SuccP (SuccP _)) c) =
  error $ "Fortl bug: Should be inaccessible for " ++ c

synthSort ctx (TyApp t1 t2) = do
  (t1', k) <- synthSort ctx t1
  case k of
    FunTy k1 k2 -> do
        t2' <- checkSort ctx t2 k1
        return (TyApp t1' t2', k2)
    _ -> Left $ ExpectingFunctionSort k

synthSort ctx (FunTy t1 t2) = do
  (t1', k) <- synthSort ctx t1
  t2'      <- checkSort ctx t2 k
  return (FunTy t1' t2', k)

synthSort ctx (ImplicitFunTy var t1 t2) = do
  -- TODO: need synthOrder?
--  (t1', _) <- synthSort ctx t1
  (t2', k) <- synthSort ctx t2
  return (ImplicitFunTy var t1 t2', k)

synthSort ctx (WithTy t1 t2) = do
  -- Two descriptiors
  (t1', k) <- synthSort ctx t1
  (t2', k') <- synthSort ctx t2
  if k == k'
    then return (WithTy t1' t2', k)
    else Left $ SortMismatch k k' (WithTy t1 t2)


-- TODO : no scoping of sort variables
synthSort ctx (TyVar v) = return (TyVar v, TyCon (SuccP (SuccP ZeroP)) "Type")

-- A lifted Type 0 value used as a kind always has sort Type
synthSort ctx (Lift t) = do
  (t', _) <- synthKind ctx t
  return (Lift t', type1)


-- Infer a kind for a type and elaborate the type
-- at the same time
synthKind :: Context -> Type 0 -> Either TypeError (Type 0, Type 1)

synthKind ctx t@(TyCon ZeroP c) =
    case lookup c typeConstructors of
      Nothing ->
        -- Perhaps a local definition
        case lookup c ctx of
          Just t' -> return (t, Lift t')
          Nothing -> Left $ UnknownTypeConstructor c 
      Just k' -> Right (t, k')

synthKind ctx (TyApp t1 t2) = do
  (t1', k) <- synthKind ctx t1
  case k of
    FunTy k1 k2 -> do
        t2' <- checkKind ctx t2 k1
        return (TyApp t1' t2', k2)

    ImplicitFunTy var k1' (FunTy (TyVar var') k3) | var == var' -> do
      -- We therefore have to synth the kind of t2
      (t2', k2) <- synthKind ctx t2
      -- this is now what we want to specialise k1' at
      return (TyApp (ImplicitTyApp t1 k2) t2', k3)

    _ -> Left $ ExpectingFunctionKind k

synthKind ctx (ImplicitTyApp t1 t2) = do
  (t1', k) <- synthKind ctx t1
  case k of
    ImplicitFunTy var k1 k2 -> do
        t2' <- checkSort ctx t2 k1
        let k_calc = substituteType k2 (var, t2)
        return (ImplicitTyApp t1' t2', k_calc)
    _ -> Left $ ExpectingFunctionKind k


synthKind ctx (FunTy t1 t2) = do
  (t1', k) <- synthKind ctx t1
  t2'      <- checkKind ctx t2 k
  return (FunTy t1' t2', k)

synthKind ctx (ProdTy t1 t2) = do
  (t1', t2', k) <- synthCheckPair ctx t1 t2
  return $ (ProdTy t1' t2', k)

synthKind ctx (SumTy t1 t2) = do
  (t1', t2', k) <- synthCheckPair ctx t1 t2
  return $ (SumTy t1' t2', k)

synthKind ctx (ExponentTy t n) = do
 (t', k) <- synthKind ctx t
 return (ExponentTy t' n, k)

synthKind ctx (WithTy t1 t2) = do
  -- Two descriptiors
  (t1', k) <- synthKind ctx t1
  (t2', k') <- synthKind ctx t2
  return (WithTy t1' t2', WithTy k k')

synthKind ctx t@(TyVar v) =
  -- TODO: allow generalisation of type variables
  return (t, type0)

synthKind ctx (Forall v t) = do
  -- TODO: need type variable environment
  (t', k) <- synthKind ctx t
  return (Forall v t', k)

-- synthKind ctx t = Left $ CannotInferKind t

synthCheckPair :: Context -> Type 0 -> Type 0 -> Either TypeError (Type 0, Type 0, Type 1)
synthCheckPair ctx t1 t2 =
  -- Try to infer the kind of the first type
  case synthKind ctx t1 of
    Left err -> do
      (t2', k) <- synthKind ctx t2
      t1' <- checkKind ctx t1 k
      return (t1', t2', k)

    Right (t1', k) -> do
      t2' <- checkKind ctx t2 k
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
