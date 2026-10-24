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
import Data.Ratio (numerator, denominator)

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
   | AffineSpace AffineRepr
   deriving (Eq, Show)

-- | Representation of an affine-space descriptor
data AffineRepr =
     Affine (Type 0) Rational  -- ^ weighted point over a base space (Point = 1, Vector = 0, NPoint = -1)
   | Scalar                    -- ^ a scalar of unknown value, as in a units library
   deriving (Eq, Show)

-- | Internal free representation of abelian groups
type AGroupRepr = Map Identifier Rational

-- | Internal representation of groups of descriptions
instance Representation DescriptionsRepr where
    -- | Compute the representation of a description type
    computeRepresentation :: Type 0 -> Either TypeError DescriptionsRepr
    -- Apply desc homomorphisms
    computeRepresentation (TyApp (TyCon ZeroP "SI") [t]) = do
      d <- computeRepresentation t
      case Map.lookup "Dimension" d of
        Just (FreeAGroup repr) -> do
          return $ insert "Unit" (FreeAGroup (mapKeys rewriteSI repr)) (delete "Dimension" d)
        _ -> return d

    -- Free abelian groups
    computeRepresentation (TyApp (TyCon ZeroP "Unit") [t])     = do
        d <- computeRepresentation t
        return $ singleton "Unit" d
    computeRepresentation (TyApp (TyCon ZeroP "Dimension") [t]) = do
        d <- computeRepresentation t
        return $ singleton "Dimension" d
    computeRepresentation (TyApp (TyCon ZeroP "Quantity") [t]) = do
        d <- computeRepresentation t
        return $ singleton "Quantity" d

    computeRepresentation (TyApp (TyCon ZeroP "Species") [t]) =
        return $ singleton "Species" (IndexType t)
    computeRepresentation (TyApp (TyCon ZeroP "Basis") [t]) =
        return $ singleton "Basis" (IndexType t)

    computeRepresentation (TyApp (TyCon ZeroP "Vector") [t]) =
        return $ singleton "Affine" (AffineSpace (Affine t 0))
    computeRepresentation (TyApp (TyCon ZeroP "Point") [t]) =
        return $ singleton "Affine" (AffineSpace (Affine t 1))
    computeRepresentation (TyApp (TyCon ZeroP "NPoint") [t]) =
        return $ singleton "Affine" (AffineSpace (Affine t (-1)))
    computeRepresentation t@(TyApp (TyCon ZeroP "Affine") [space, w]) =
        case w of
          TyRat r -> return $ singleton "Affine" (AffineSpace (Affine space r))
          _       -> Left $ CannotComputeDescriptionRepresentation t
    computeRepresentation (TyCon ZeroP "Scalar") =
        return $ singleton "Affine" (AffineSpace Scalar)
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

    computeRepresentation e@(ExponentTy t n) = do
        d <- computeRepresentation t
        traverse (exp n) d
        where
          exp :: Rational -> DescriptionRepr -> Either TypeError DescriptionRepr
          exp n (FreeAGroup a) = Right $ FreeAGroup $ fmap (n *) a
          exp n (TypeTree t)   = Right $ TypeTree $ ExponentTy t n
          exp _ (IndexType t)  = Right $ IndexType t  -- exponentiation is no-op for indexed types
          -- weights multiply under products, so exponentiation raises the weight to the power
          exp _ (AffineSpace Scalar) = Right $ AffineSpace Scalar
          -- a position (over a space other than 1) can only be raised to the power 1,
          -- so it cannot be squared or be a divisor
          exp n (AffineSpace a@(Affine t _))
            | t /= unitDescription = if n == 1 then Right (AffineSpace a)
                                     else Left $ AffineSpacePowerUndefined e
          exp n (AffineSpace (Affine t w)) =
            case weightPower w n of
              Just w' -> Right $ AffineSpace (Affine t w')
              Nothing -> Left $ AffineSpacePowerUndefined e
    computeRepresentation (TyCon ZeroP "1") = return empty
    -- the additive inverse negates an affine weight and, as under `+`, leaves
    -- every other component alone
    computeRepresentation (NegTy t) = negateAffineGrades <$> computeRepresentation t
    computeRepresentation (ProdTy t1 t2) = do
        d1 <- computeRepresentation t1
        d2 <- computeRepresentation t2
        sequenceA $ unionWith (\a b -> do { x <- a; y <- b; combineRepr x y }) (fmap Right d1) (fmap Right d2)
        where
          combineRepr :: DescriptionRepr -> DescriptionRepr -> Either TypeError DescriptionRepr
          combineRepr (FreeAGroup a1) (FreeAGroup a2) = Right $ FreeAGroup $ unionWith (+) a1 a2
          combineRepr (TypeTree t1) (TypeTree t2)     = Right $ TypeTree $ ProdTy t1 t2
          combineRepr (IndexType t1) (IndexType t2) = Right $ IndexType (combineIndex t1 t2)
          -- weights multiply, so a scalar of weight c scales a weight w to c * w,
          -- and base spaces combine like indices
          -- and at least one factor must be a scalar: two positions cannot be multiplied
          combineRepr (AffineSpace (Affine s1 w1)) (AffineSpace (Affine s2 w2))
            | s1 == unitDescription || s2 == unitDescription =
                Right $ AffineSpace (Affine (combineIndex s1 s2) (w1 * w2))
            | otherwise = Left $ AffineSpaceProductUndefined t1 t2
          -- a scalar of unknown value leaves a scalar a scalar, and a weight 0 at weight 0,
          -- but its effect on any other weight is unknown
          combineRepr (AffineSpace Scalar) (AffineSpace Scalar) = Right $ AffineSpace Scalar
          combineRepr (AffineSpace Scalar) (AffineSpace a)      = scaleByUnknown a
          combineRepr (AffineSpace a) (AffineSpace Scalar)      = scaleByUnknown a
          combineRepr _ _                             = error "Mismatched description representation types in product"
          scaleByUnknown a@(Affine s w)
            | s == unitDescription = Right $ AffineSpace Scalar
            | w == 0               = Right $ AffineSpace a
          scaleByUnknown _ = Left $ AffineSpaceProductUndefined t1 t2
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
            -- NPoint[t]), so it must be spliced in as-is, not re-wrapped
            -- as e.g. "Affine[Point[t]]".
            wrapKey "Affine" v' = reifyToTypeTerm v'
            wrapKey k'        v' = TyApp (tyCon0 k') [reifyToTypeTerm v']

    -- | Equality on description representations
    reprEquality :: DescriptionsRepr -> Specificational DescriptionsRepr -> Either TypeError ()
    reprEquality d1 (IsSpec d2) =
        if keys d1 == keys d2
            then
                -- Keys have already been checked so the keys are irrelevant here
                mapM_ (\((_k1, u1), (_k2, u2)) -> reprEquality u1 (IsSpec u2)) (zip (assocs d1) (assocs d2))
            else
                Left $ DescriptionKeyMismatch (keys d2) (keys d1)

-- | Product of two index types, such as the species of a Species descriptor
-- or the base space of an affine space: it is idempotent (S * S = S) with
-- unit 1, and a mismatch is preserved for a later equality check
combineIndex :: Type 0 -> Type 0 -> Type 0
combineIndex t1 t2
  | t1 == tyCon0 "1" = t2
  | t2 == tyCon0 "1" = t1
  | t1 == t2         = t1
  | otherwise        = ProdTy t1 t2

-- | An affine weight raised to a rational power, when that is itself a
-- rational: the weight must be 1, or the power an integer (negative powers
-- of 0 are undefined), or the weight 0 with a positive power
weightPower :: Rational -> Rational -> Maybe Rational
weightPower w n
  | w == 1                  = Just 1
  | denominator n == 1, n >= 0 = Just (w ^ numerator n)
  | denominator n == 1, w /= 0 = Just (w ^^ numerator n)
  | w == 0, n > 0           = Just 0
  | otherwise               = Nothing

-- | The description of a numeric constant c: the scalar of weight c, i.e. the
-- weighted point over the trivial space 1, written Affine[1, c]
scalarDescription :: Rational -> Type 0
scalarDescription c = reifyToTypeTerm (singleton "Affine" (AffineSpace (Affine unitDescription c)))

-- | The description a numeric constant c takes beside an operand of `+` or
-- `-` with the given description: the same description, except that an
-- affine-space component becomes the scalar of weight c, since adding a
-- constant adds its weight
adoptConstant :: Rational -> Type 0 -> Either TypeError (Type 0)
adoptConstant c d = do
  repr <- computeRepresentation d :: Either TypeError DescriptionsRepr
  let adopt (AffineSpace _) = AffineSpace (Affine unitDescription c)
      adopt v               = v
  Right $ reifyToTypeTerm (Data.Map.Lazy.map adopt repr)

-- | The affine-space component of a description
descriptionAffine :: Type 0 -> Maybe AffineRepr
descriptionAffine t = case computeRepresentation t :: Either TypeError DescriptionsRepr of
  Right repr | Just (AffineSpace a) <- Map.lookup "Affine" repr -> Just a
  _ -> Nothing

-- | Whether a description is that of a scalar: either a Scalar of unknown
-- value, or a weighted point over the trivial space 1, such as Affine[1, 1/2]
descriptionIsScalar :: Type 0 -> Bool
descriptionIsScalar t = case descriptionAffine t of
  Just Scalar       -> True
  Just (Affine s _) -> s == unitDescription
  Nothing           -> False

-- | The affine weight of a description, if it has a weighted affine-space component
descriptionAffineWeight :: Type 0 -> Maybe Rational
descriptionAffineWeight t = case descriptionAffine t of
  Just (Affine _ w) -> Just w
  _                 -> Nothing

-- | Negate the grade of any affine-space ("Point"/"Vector") component of a
-- description, leaving every other component unchanged. Used to implement
-- subtraction as addition of a negated second operand, e.g.
-- Vector(0) - Point(1) = Vector(0) + Point(-1) = NPoint(-1).
negateAffineGrades :: DescriptionsRepr -> DescriptionsRepr
negateAffineGrades = Data.Map.Lazy.map negOne
  where
    negOne (AffineSpace (Affine t n)) = AffineSpace (Affine t (negate n))
    negOne v                 = v

-- | Combine two description representations for `+`/`-`
-- (BinOpMinus negates the affine weight of the second side
-- first). Every key must either match exactly -- ordinary units,
-- quantities, species, basis descriptions are unaffected by `+`/`-` and
-- must simply agree -- or be the "Affine" key, whose weight combines
-- additively (Vector = 0, Point = 1).
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
        (AffineSpace (Affine t1 w1), AffineSpace (Affine t2 w2))
          | t1 /= t2  -> Left mismatchErr
          | otherwise -> Right $ AffineSpace (Affine t1 (w1 + w2))
        -- a scalar of unknown value absorbs the weight of a scalar of known weight
        (AffineSpace Scalar, AffineSpace Scalar) -> Right v1
        (AffineSpace Scalar, AffineSpace (Affine t _)) | t == unitDescription -> Right v1
        (AffineSpace (Affine t _), AffineSpace Scalar) | t == unitDescription -> Right (AffineSpace Scalar)
        _ -> Left mismatchErr
    combineKey k v1
      | v1 == d2' ! k = Right v1
      | otherwise      = Left mismatchErr

-- | Whether a (not-yet-normalised) description type has an affine-space
-- ("Point"/"Vector") component. This guards `*`, `/` and `^`, where
-- affine-space values can be scaled only in limited ways.
descriptionHasAffine :: Type 0 -> Bool
descriptionHasAffine t = case computeRepresentation t :: Either TypeError DescriptionsRepr of
  Right repr -> member "Affine" repr
  Left _     -> False

-- | Whether a description is that of a Point in an affine space
descriptionIsPoint :: Type 0 -> Bool
descriptionIsPoint t = case computeRepresentation t :: Either TypeError DescriptionsRepr of
  Right repr | Just (AffineSpace (Affine _ 1)) <- Map.lookup "Affine" repr -> True
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

            scale :: Rational -> AGroupRepr -> AGroupRepr
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
    reifyToTypeTerm (AffineSpace Scalar) = tyCon0 "Scalar"
    -- a scalar of known weight, over the trivial space, is always written out
    reifyToTypeTerm (AffineSpace (Affine t w)) | t == unitDescription = TyApp (tyCon0 "Affine") [t, TyRat w]
    reifyToTypeTerm (AffineSpace (Affine t 0))    = TyApp (tyCon0 "Vector") [t]
    reifyToTypeTerm (AffineSpace (Affine t 1))    = TyApp (tyCon0 "Point")  [t]
    reifyToTypeTerm (AffineSpace (Affine t (-1))) = TyApp (tyCon0 "NPoint") [t]
    -- any other weight is written out, e.g. Affine[t, 2]
    reifyToTypeTerm (AffineSpace (Affine t w)) = TyApp (tyCon0 "Affine") [t, TyRat w]


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
    reprEquality (AffineSpace a1) (IsSpec (AffineSpace a2)) =
        if a1 == a2
            then Right ()
            else Left $ DescriptionEqualityFailure (reifyToTypeTerm (AffineSpace a2)) (reifyToTypeTerm (AffineSpace a1))
    reprEquality _ _ =
        Left MismatchedDescriptionReprTypes


--------

-- coercions ::

