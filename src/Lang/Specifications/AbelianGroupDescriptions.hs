{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- TODO: rename to something about AbelianGroup descriptors
module Lang.Specifications.AbelianGroupDescriptions where

import Lang.Syntax
import Lang.PrettyPrint
import Lang.Primitives
import Data.Map.Lazy hiding (foldr)

------------------------------------
-- # Description-specific typing
------------------------------------

type Descriptions = Map Identifier (Type 0)

-- | Predicate on whether a type is a description: if so extract this part
-- and give its normalised representation
isDescription :: Type 0 -> Maybe Descriptions
isDescription (TyApp (TyCon "Unit") t)     = Just $ singleton "Unit" t
isDescription (TyApp (TyCon "Quantity") t) = Just $ singleton "Quantity" t
isDescription (IntersectTy t1 t2) = do
  d1 <- isDescription t1
  d2 <- isDescription t2
  Just $ union d1 d2
isDescription (ProdTy t1 t2) = do
  k1 <- isDescription t1
  k2 <- isDescription t2
  Just $ union k1 k2
isDescription _ = Nothing

-- | Matches on a type that is either a Float or an
-- intersection type containing a float and something of kind description
floatWithDescription :: Type 0 -> Maybe Descriptions
floatWithDescription t =
  -- First flatten out intersections into a list
  if (TyCon "Float" `elem` floatWithDescription' t) then
    -- Remove the Float and fold up the rest as descriptions
    let descs = Prelude.filter (/= TyCon "Float") (floatWithDescription' t) in
      foldr
      (\d acc -> do
          dDesc <- isDescription d
          accDesc <- acc
          Just $ union dDesc accDesc)
      (Just empty)
      descs
  else
    Nothing
  where
    floatWithDescription' :: Type 0 -> [Type 0]
    floatWithDescription' (IntersectTy t1 t2) = do
      floatWithDescription' t1 ++ floatWithDescription' t2
    floatWithDescription' t = [t]

reifyDescription :: Descriptions -> Type 0
reifyDescription =
  foldrWithKey (\k v t -> TyApp (TyCon k) v `IntersectTy` t) (TyCon omega)

-- | Given a unit, construct its inverse
reciprocalUnit :: Type 0 -> Type 0
reciprocalUnit t = ExponentTy t (-1.0)

--------------------------------------------

descriptionEquality :: Descriptions
                    -> Descriptions
                    -> Bool
descriptionEquality d1 d2 =
  all
  (\((k1, u1), (k2, u2)) -> k1 == k2 && agroupEquality u1 u2)
  (zip (assocs d1) (assocs d2))


agroupEquality :: Type 0 -> Type 0 -> Bool
agroupEquality u1 u2 =
    evalFreeAGroup u1 == evalFreeAGroup u2

type AGroupRepr = Map Identifier Float

evalFreeAGroup :: Type 0 -> AGroupRepr
evalFreeAGroup t =
    Data.Map.Lazy.filter (/= 0) (evalFreeAGroup' t)
  where
    evalFreeAGroup' :: Type 0 -> AGroupRepr
    evalFreeAGroup' (TyCon "1") = empty
    evalFreeAGroup' (ExponentTy t n) = scale n (evalFreeAGroup' t)
    evalFreeAGroup' (ProdTy t1 t2) =
      unionWith (+) (evalFreeAGroup' t1) (evalFreeAGroup' t2)
    evalFreeAGroup' (TyCon c) = singleton c 1.0
    evalFreeAGroup' t = error $ "Not well kinded unit " <> pprint t

scale :: Float -> AGroupRepr -> AGroupRepr
scale n = fmap (n *)

reifyAGroup :: AGroupRepr -> Type 0
reifyAGroup =
  foldrWithKey (\k v t -> ExponentTy (TyCon k) v `ProdTy` t) (TyCon "1")

