{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}

module Lang.Descriptions where

import Lang.Syntax
import Lang.TypeHelpers
import Lang.PrettyPrint
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy
import Lang.TypeError
import Data.List (sort, intersect)
import Lang.Primitives (rewriteSI)

unitDescription :: Type 0
unitDescription = tyCon0 "1"

-- | Equality on descriptions
descriptionEquality :: Type 0 -> Specificational (Type 0) -> Either TypeError ()
descriptionEquality t1 (IsSpec t2) = do
    d1 <- computeRepresentation t1 :: Either TypeError DescriptionsRepr
    d2 <- computeRepresentation t2 :: Either TypeError DescriptionsRepr
    d1 `reprEquality` (IsSpec d2)

-- # Representations class

class Representation a where
    computeRepresentation :: Type 0 -> Either TypeError a
    reifyToTypeTerm       :: a -> Type 0
    reprEquality          :: a -> Specificational a -> Either TypeError ()

-- | Normalize a description type by computing its representation the reifying
normalisationByEvaluation :: Type 0 -> Either TypeError (Type 0)
normalisationByEvaluation t = do
        repr <- computeRepresentation t :: Either TypeError DescriptionsRepr
        repr' <- coherenceChecks repr
        return (reifyToTypeTerm repr')

coherenceChecks :: DescriptionsRepr -> Either TypeError DescriptionsRepr
coherenceChecks repr = do
  case Map.lookup "Unit" repr of
    Just (FreeAGroup unitRepr) ->
      case Map.lookup "Dimension" repr of
        Just (FreeAGroup dimRepr) ->
          if checkCoherence unitRepr (assocs dimRepr)
            then Right repr
            else Left (DimensionAndUnitIncoherence
                    (reifyToTypeTerm $ singleton "Dimension" $ FreeAGroup dimRepr)
                    (reifyToTypeTerm $ singleton "Unit" $ FreeAGroup unitRepr))
        _ -> Right repr
    _ -> Right repr

  where
    -- TODO: generalise to the idea that all injective grading algebra morphisms
    -- must have this coherence

    -- We need the there to be no left over units that don't match a dimension
    checkCoherence unitRepr [] = Map.null unitRepr

    -- Check that the unit is SI compliant with the dimension
    checkCoherence unitRepr ((dimName, exponent):dimRepr) =
      case Map.lookup (rewriteSI dimName) unitRepr of
        Just exponent' | exponent == exponent ->
          checkCoherence (delete (rewriteSI dimName) unitRepr) dimRepr

        _ -> False

-- | Internal representation of groups of descriptions
type DescriptionsRepr = Map Identifier DescriptionRepr

-- | Representation of a description
data DescriptionRepr =
     FreeAGroup AGroupRepr
   | TypeTree (Type 0)
   | IndexType (Type 0)   -- ^ Exact-match index (e.g. Species): preserved through all ops, never combined
   | AffineSpace (Type 0) Int
   deriving (Eq, Show)

-- | Internal free representation of abelian groups
type AGroupRepr = Map Identifier Float

-- | Internal representation of groups of descriptions
instance Representation DescriptionsRepr where
    -- | Compute the representation of a description type
    computeRepresentation :: Type 0 -> Either TypeError DescriptionsRepr
    -- Apply desc homomorphisms
    computeRepresentation (TyApp (TyCon ZeroP "SI") t) = do
      d <- computeRepresentation t
      case Map.lookup "Dimension" d of
        Just (FreeAGroup repr) -> do
          return $ insert "Unit" (FreeAGroup (mapKeys rewriteSI repr)) (delete "Dimension" d)
        _ -> return d

    -- Free abelian groups
    computeRepresentation (TyApp (TyCon ZeroP "Unit") t)     = do
        d <- computeRepresentation t
        return $ singleton "Unit" d
    computeRepresentation (TyApp (TyCon ZeroP "Dimension") t) = do
        d <- computeRepresentation t
        return $ singleton "Dimension" d
    computeRepresentation (TyApp (TyCon ZeroP "Quantity") t) = do
        d <- computeRepresentation t
        return $ singleton "Quantity" d

    computeRepresentation (TyApp (TyCon ZeroP "Species") t) =
        return $ singleton "Species" (IndexType t)
    computeRepresentation (TyApp (TyCon ZeroP "Basis") t) =
        return $ singleton "Basis" (IndexType t)

    computeRepresentation (TyApp (TyCon ZeroP "Vector") t) =
        return $ singleton "Affine" (AffineSpace t 0)
    computeRepresentation (TyApp (TyCon ZeroP "Point") t) =
        return $ singleton "Affine" (AffineSpace t 1)
    -- "DVector" is not meant to be written by users -- it only ever arises
    -- as a synthesised result (e.g. Vector - Point) -- but once synthesised
    -- it's stored as a real type and re-used, so it must round-trip back
    -- through computeRepresentation like Vector/Point do.
    computeRepresentation (TyApp (TyCon ZeroP "DVector") t) =
        return $ singleton "Affine" (AffineSpace t (-1))
    computeRepresentation (WithTy t1 t2) = do
        d1 <- computeRepresentation t1
        d2 <- computeRepresentation t2
        -- Check for any overlapping keys
        let overlapping = intersect (keys d1) (keys d2)
        if all (\k -> (d1 ! k) == (d2 ! k)) overlapping
          then return $ union d1 d2
          else case overlapping of
                 (k:_) -> Left $ OverlappingDescriptionConflict k t1 t2
                 []    -> error "unreachable: overlapping is non-empty here since `all` over [] is True"

    computeRepresentation (ExponentTy t n) = do
        d <- computeRepresentation t
        return $ fmap (exp n) d
        where
          exp :: Float -> DescriptionRepr -> DescriptionRepr
          exp n (FreeAGroup a) = FreeAGroup $ fmap (n *) a
          exp n (TypeTree t)   = TypeTree $ ExponentTy t n
          exp _ (IndexType t)  = IndexType t  -- exponentiation is no-op for indexed types
          exp _ (AffineSpace t n) = AffineSpace t n
    computeRepresentation (TyCon ZeroP "1") = return empty
    computeRepresentation (ProdTy t1 t2) = do
        d1 <- computeRepresentation t1
        d2 <- computeRepresentation t2
        return $ unionWith combineRepr d1 d2
        where
          combineRepr :: DescriptionRepr -> DescriptionRepr -> DescriptionRepr
          combineRepr (FreeAGroup a1) (FreeAGroup a2) = FreeAGroup $ unionWith (+) a1 a2
          combineRepr (TypeTree t1) (TypeTree t2)     = TypeTree $ ProdTy t1 t2
          combineRepr (IndexType t1) (IndexType t2)
            | t1 == tyCon0 "1" = IndexType t2        -- 1 * S = S
            | t2 == tyCon0 "1" = IndexType t1        -- S * 1 = S
            | t1 == t2         = IndexType t1        -- S * S = S
            | otherwise        = IndexType (ProdTy t1 t2)  -- mismatch: preserved for later equality check
          combineRepr _ _                             = error "Mismatched description representation types in product"
    computeRepresentation (SumTy t1 t2) = do
        d1 <- computeRepresentation t1
        d2 <- computeRepresentation t2
        combineDescriptionsForAddSub BinOpPlus d1 d2

    computeRepresentation t = Left $ CannotComputeDescriptionRepresentation t

    -- | Reify a description representation back to a type term
    reifyToTypeTerm :: DescriptionsRepr -> Type 0
    reifyToTypeTerm ds =
      case assocs ds of
        []            -> tyCon0 "1"
        ((k, v):rest) ->
          Prelude.foldr (\(k', v') t -> WithTy (wrapKey k' v') t) (wrapKey k v) rest
          where
            -- Most keys ("Unit", "Species", ...) name a real wrapper type
            -- constructor, so re-applying it reconstructs the source
            -- syntax. "Affine" is purely internal bookkeeping: its value
            -- already reifies to the complete type (Point[t]/Vector[t]/
            -- DVector[t]), so it must be spliced in as-is, not re-wrapped
            -- as e.g. "Affine[Point[t]]".
            wrapKey "Affine" v' = reifyToTypeTerm v'
            wrapKey k'        v' = TyApp (tyCon0 k') (reifyToTypeTerm v')

    -- | Equality on description representations
    reprEquality :: DescriptionsRepr -> Specificational DescriptionsRepr -> Either TypeError ()
    reprEquality d1 (IsSpec d2) =
        if keys d1 == keys d2
            then
                -- Keys have already been checked so the keys are irrelevant here
                mapM_ (\((_k1, u1), (_k2, u2)) -> reprEquality u1 (IsSpec u2)) (zip (assocs d1) (assocs d2))
            else
                Left $ DescriptionKeyMismatch (keys d2) (keys d1)

-- | Negate the grade of any affine-space ("Point"/"Vector") component of a
-- description, leaving every other component unchanged. Used to implement
-- subtraction as addition of a negated second operand, e.g.
-- Vector(0) - Point(1) = Vector(0) + Point(-1) = DVector(-1).
negateAffineGrades :: DescriptionsRepr -> DescriptionsRepr
negateAffineGrades = Data.Map.Lazy.map negOne
  where
    negOne (AffineSpace t n) = AffineSpace t (negate n)
    negOne v                 = v

-- | Combine two description representations for `+`/`-` (BinOpPlus negates
-- neither side; BinOpMinus negates the affine grade of the second side
-- first). Every key must either match exactly -- ordinary units,
-- quantities, species, basis descriptions are unaffected by `+`/`-` and
-- must simply agree -- or be the "Affine" key, whose grade combines
-- additively (Vector = 0, Point = 1), rejecting any result outside
-- {DVector = -1, Vector = 0, Point = 1} (e.g. Point + Point).
combineDescriptionsForAddSub :: BinOp -> DescriptionsRepr -> DescriptionsRepr -> Either TypeError DescriptionsRepr
combineDescriptionsForAddSub op d1 d2
    | keys d1 /= keys d2 = Left mismatchErr
    | otherwise           = traverseWithKey combineKey d1
  where
    d2' = if op == BinOpMinus then negateAffineGrades d2 else d2

    -- Report the original (pre-negation) operands so the error reads
    -- naturally for `-` too.
    mismatchErr = BinaryOperatorDescriptionMismatch op (reifyToTypeTerm d1) (reifyToTypeTerm d2)

    combineKey "Affine" v1 =
      case (v1, d2' ! "Affine") of
        (AffineSpace t1 n1, AffineSpace t2 n2)
          | t1 /= t2                  -> Left mismatchErr
          | n1 + n2 `elem` [-1, 0, 1] -> Right $ AffineSpace t1 (n1 + n2)
          | otherwise ->
              Left $ AffineSpaceCombinationUndefined op (reifyToTypeTerm v1) (reifyToTypeTerm (d2 ! "Affine"))
        _ -> Left mismatchErr
    combineKey k v1
      | v1 == d2' ! k = Right v1
      | otherwise      = Left mismatchErr

-- | Whether a (not-yet-normalised) description type has an affine-space
-- ("Point"/"Vector") component. Affine-space values cannot be scaled, so
-- this guards `*`, `/` and `^`.
descriptionHasAffine :: Type 0 -> Bool
descriptionHasAffine t = case computeRepresentation t :: Either TypeError DescriptionsRepr of
  Right repr -> member "Affine" repr
  Left _     -> False

-- | Whether a description is that of a Point in an affine space
descriptionIsPoint :: Type 0 -> Bool
descriptionIsPoint t = case computeRepresentation t :: Either TypeError DescriptionsRepr of
  Right repr | Just (AffineSpace _ 1) <- Map.lookup "Affine" repr -> True
  _ -> False

-- | The component of a description built from the given descriptor
-- constructor, if present, e.g. the "Quantity" component of
-- Unit[m] & Quantity[Length] is Quantity[Length]
descriptionComponent :: Identifier -> Type 0 -> Either TypeError (Maybe (Type 0))
descriptionComponent k t = do
  repr <- computeRepresentation t :: Either TypeError DescriptionsRepr
  return $ (\v -> reifyToTypeTerm (singleton k v)) <$> Map.lookup k repr

-- | Remove the component of a description built from the given descriptor
-- constructor, e.g. dropping "Quantity" from Unit[1] & Quantity[Angle]
-- gives Unit[1]
dropDescriptionComponent :: Identifier -> Type 0 -> Either TypeError (Type 0)
dropDescriptionComponent k t = do
  repr <- computeRepresentation t :: Either TypeError DescriptionsRepr
  return $ reifyToTypeTerm (Map.delete k repr)

-- | Remove any affine-space (Point/Vector) component of a description
dropAffine :: Type 0 -> Either TypeError (Type 0)
dropAffine = dropDescriptionComponent "Affine"

-- | Representation of a single description
instance Representation DescriptionRepr where
    -- | Compute the representation of a description type
    computeRepresentation :: Type 0 -> Either TypeError DescriptionRepr
    computeRepresentation t =
            return $ FreeAGroup $ Data.Map.Lazy.filter (/= 0) (computeFreeAGroupRepr' t)
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
    reifyToTypeTerm (IndexType t) = t
    reifyToTypeTerm (FreeAGroup a) =
      case assocs a of
        []            -> tyCon0 "1"
        ((k, v):rest) ->
          Prelude.foldr (\(k', v') t -> exp k' v' `ProdTy` t) base rest
          where
            exp k' 1 = tyCon0 k'
            exp k' v' = ExponentTy (tyCon0 k') v'
            base = exp k v
    reifyToTypeTerm (TypeTree t) = t
    reifyToTypeTerm (AffineSpace t 0) = TyApp (tyCon0 "Vector") t
    reifyToTypeTerm (AffineSpace t 1) = TyApp (tyCon0 "Point")  t
    reifyToTypeTerm (AffineSpace t (-1)) = TyApp (tyCon0 "DVector") t
    reifyToTypeTerm (AffineSpace t _) = error "Not representable"


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
    reprEquality (IndexType t1) (IsSpec (IndexType t2)) =
        if t1 == t2
            then Right ()
            else Left $ DescriptionEqualityFailure t2 t1  -- reuse error: shows expected vs actual species
    reprEquality (AffineSpace t1 n1) (IsSpec (AffineSpace t2 n2)) =
        if t1 == t2 && n1 == n2
            then Right ()
            else Left $ DescriptionEqualityFailure (reifyToTypeTerm (AffineSpace t2 n2)) (reifyToTypeTerm (AffineSpace t1 n1))
    reprEquality _ _ =
        Left MismatchedDescriptionReprTypes


--------

-- coercions ::

