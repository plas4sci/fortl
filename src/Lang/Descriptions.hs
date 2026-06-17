{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}

module Lang.Descriptions where

import Lang.Syntax
import Lang.TypeHelpers
import Lang.PrettyPrint
import Data.Map.Lazy
import Lang.TypeError
import Data.List (sort)

unitDescription :: Type 0
unitDescription = tyCon0 "1"

-- | Equality on descriptions
descriptionEquality :: Type 0 -> Specificational (Type 0) -> Either TypeError ()
descriptionEquality t1 (IsSpec t2) =
    case eq of
        Nothing  -> Left $ DescriptionEqualityFailure (normalisationByEvaluation t1) (normalisationByEvaluation t2)
        Just x   -> x
    where
        eq = do
            d1 <- computeRepresentation t1 :: Maybe DescriptionsRepr
            d2 <- computeRepresentation t2 :: Maybe DescriptionsRepr
            return $ d1 `reprEquality` (IsSpec d2)

-- # Representations class

class Representation a where
    computeRepresentation :: Type 0 -> Maybe a
    reifyToTypeTerm       :: a -> Type 0
    reprEquality          :: a -> Specificational a -> Either TypeError ()

-- | Normalize a description type by computing its representation the reifying
normalisationByEvaluation :: Type 0 -> Type 0
normalisationByEvaluation t = 
    case computeRepresentation t :: Maybe DescriptionsRepr of
        Just repr -> reifyToTypeTerm repr
        Nothing   -> t

-- | Internal representation of groups of descriptions
type DescriptionsRepr = Map Identifier DescriptionRepr

-- | Representation of a description
data DescriptionRepr = 
     FreeAGroup AGroupRepr
   | TypeTree (Type 0)
   deriving Show

-- | Internal free representation of abelian groups
type AGroupRepr = Map Identifier Float

-- | Internal representation of groups of descriptions
instance Representation DescriptionsRepr where
    -- | Compute the representation of a description type
    computeRepresentation :: Type 0 -> Maybe DescriptionsRepr
    computeRepresentation (TyApp (TyCon ZeroP "Unit") t)     = do
        d <- computeRepresentation t
        Just $ singleton "Unit" d
    computeRepresentation (TyApp (TyCon ZeroP "Quantity") t) = do
        d <- computeRepresentation t
        Just $ singleton "Quantity" d
    computeRepresentation (WithTy t1 t2) = do
        d1 <- computeRepresentation t1
        d2 <- computeRepresentation t2
        Just $ union d1 d2
    computeRepresentation (ExponentTy t n) = do
        d <- computeRepresentation t
        Just $ fmap (exp n) d
        where
          exp :: Float -> DescriptionRepr -> DescriptionRepr
          exp n (FreeAGroup a) = FreeAGroup $ fmap (n *) a
          exp n (TypeTree t)   = TypeTree $ ExponentTy t n
    computeRepresentation (TyCon ZeroP "1") = Just empty
    computeRepresentation (ProdTy t1 t2) = do
        d1 <- computeRepresentation t1
        d2 <- computeRepresentation t2
        Just $ unionWith combineRepr d1 d2
        where
          combineRepr :: DescriptionRepr -> DescriptionRepr -> DescriptionRepr
          combineRepr (FreeAGroup a1) (FreeAGroup a2) = FreeAGroup $ unionWith (+) a1 a2
          combineRepr (TypeTree t1) (TypeTree t2)     = TypeTree $ ProdTy t1 t2
          combineRepr _ _                             = error "Mismatched description representation types in product"
    computeRepresentation _ = Nothing

    -- | Reify a description representation back to a type term
    reifyToTypeTerm :: DescriptionsRepr -> Type 0
    reifyToTypeTerm ds =
      if length (keys ds) == 0
        then tyCon0 "1"
        else
          Prelude.foldr (\(k, v) t -> WithTy (TyApp (tyCon0 k) (reifyToTypeTerm v)) t) base rest
          where
            base    = TyApp (tyCon0 k) (reifyToTypeTerm v)
            (k, v)  = head (assocs ds)
            rest    = tail (assocs ds)

    -- | Equality on description representations
    reprEquality :: DescriptionsRepr -> Specificational DescriptionsRepr -> Either TypeError ()
    reprEquality d1 (IsSpec d2) =
        if keys d1 == keys d2
            then
                -- Keys have already been checked so the keys are irrelevant here
                mapM_ (\((_k1, u1), (_k2, u2)) -> reprEquality u1 (IsSpec u2)) (zip (assocs d1) (assocs d2))
            else
                Left $ DescriptionKeyMismatch (keys d2) (keys d1)

-- | Representation of a single description
instance Representation DescriptionRepr where
    -- | Compute the representation of a description type
    computeRepresentation :: Type 0 -> Maybe DescriptionRepr
    computeRepresentation t =
            Just $ FreeAGroup $ Data.Map.Lazy.filter (/= 0) (computeFreeAGroupRepr' t)
        where
            computeFreeAGroupRepr' :: Type 0 -> AGroupRepr
            computeFreeAGroupRepr' (TyCon ZeroP "1") = empty
            computeFreeAGroupRepr' (ExponentTy t n) = scale n (computeFreeAGroupRepr' t)
            computeFreeAGroupRepr' (ProdTy t1 t2) =
                unionWith (+) (computeFreeAGroupRepr' t1) (computeFreeAGroupRepr' t2)
            computeFreeAGroupRepr' (TyCon ZeroP c) = singleton c 1.0
            computeFreeAGroupRepr' t = error $ "Not well kinded unit " <> pprint t

            scale :: Float -> AGroupRepr -> AGroupRepr
            scale n = fmap (n *)

    -- | Reify a description representation back to a type term
    reifyToTypeTerm :: DescriptionRepr -> Type 0
    reifyToTypeTerm (FreeAGroup a) =
      if length (assocs a) == 0
        then tyCon0 "1"
        else
          Prelude.foldr (\(k, v) t -> exp k v `ProdTy` t) base rest
          where
            exp k 1 = tyCon0 k
            exp k v = ExponentTy (tyCon0 k) v
            base    = exp k v
            (k, v)  = head (assocs a)
            rest    = tail (assocs a)
    reifyToTypeTerm (TypeTree t) = t

    -- | Equality on description representations
    reprEquality :: DescriptionRepr -> Specificational DescriptionRepr -> Either TypeError ()
    reprEquality (FreeAGroup a1) (IsSpec (FreeAGroup a2)) =
        if a1n == a2n
            then Right ()
            else Left $ AbelianGroupMismatch (reifyToTypeTerm (FreeAGroup a2)) (reifyToTypeTerm (FreeAGroup a1))
      where
        a1n = sort $ nonZeroAssocs a1
        a2n = sort $ nonZeroAssocs a2
        nonZeroAssocs a = Prelude.filter (\(_, v) -> v /= 0) (assocs a)
    reprEquality (TypeTree t1) (IsSpec (TypeTree t2)) =
        if t1 == t2
            then Right ()
            else Left $ TypeTreeMismatch t2 t1
    reprEquality _ _ =
        Left MismatchedDescriptionReprTypes
    

--------

-- coercions :: 

