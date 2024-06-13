module Lang.Types where

import Lang.Syntax
import Lang.PrettyPrint
import Lang.Semantics (substituteType)

import Data.Maybe (mapMaybe)
import Data.List (intercalate)

{-

**********************************************************************************
Declarative specification of the (relational) graded simply-typed lambda calculus
**********************************************************************************
Recall contexts are like lists of variable-type assumptions


G ::=  G, x : A | .

       (x :_1 A) in G
var ----------------------
       G |- x : A

     G1 |- e1 : A -> B      G2 |- e2 : A
app ---------------------------------------
    G1 + r * G2 |- e1 e2 : B

      G, x :_r A |- e : B
abs ------------------------
      G |- \x -> e : A r -> B

-}

-- Represent contexts as lists
type Context = [(Identifier, Type)]

{-

Bidirectional checking
*********************************
G |- e <= A    check
**********************************
-}

check :: Context -> Expr PCF -> Type -> Either String ()

check gamma (Var x) ty =
  case lookup x gamma of
    Nothing -> Left $ "Variable " <> x <> " not found in context."
    -- contravariant subtyping
    Just t -> if isSubtype ty (IsSpec t) then Right ()
               else Left $ "Expecting " <> pprint t <> " but got " <> pprint ty

{--

G, x : A |- e <= B
--------------------------- abs
G |- (\x -> e) <= A -> B

-}
-- Curry style
check gamma (Abs x Nothing expr) (FunTy tyA tyB) =
  check ([(x, tyA)] ++ gamma) expr tyB

-- Church style
check gamma (Abs x (Just tyA') expr) (FunTy tyA tyB) | isSubtype tyA' (IsSpec tyA) =
  check ([(x, tyA)] ++ gamma) expr tyB

--- PCF rules
check gamma (Ext (Fix e)) t = check gamma e (FunTy t t)

check gamma (Ext (NatCase e e1 (x,e2))) t = do
  check gamma e natTy
  check gamma e1 t
  check ([(x, natTy)] ++ gamma) e2 t

check gamma (Ext (Pair e1 e2)) (ProdTy t1 t2) = do
  check gamma e1 t1
  check gamma e2 t2

check gamma e (IntersectTy t1 t2) = do
  check gamma e t1
  check gamma e t2

check gamma (Ext (Pair _ _)) t = Left $ "Trying to assign non-product type " <> pprint t <> " to pair."

check gamma (Ext (Fst e)) t =
  case synth gamma e of
    Right (ProdTy t1 t2) ->
      if isSubtype t1 (IsSpec t) then Right ()
      else Left $ "Expecting " <> pprint t1 <> " but got " <> pprint t
    _ -> Left $ "Expecting product type but got " <> pprint t

check gamma (Ext (Snd e)) t =
  case synth gamma e of
    Right (ProdTy t1 t2) ->
      if isSubtype t2 (IsSpec t) then Right ()
      else Left $ "Expecting " <> pprint t2 <> " but got " <> pprint t
    _ -> Left $ "Expecting product type but got " <> pprint t

check gamma (Ext (Inl e)) (SumTy t1 t2) = check gamma e t1
check gamma (Ext (Inl e)) t = Left $ "Sum construction cannot have type " <> pprint t

check gamma (Ext (Inr e)) (SumTy t1 t2) = check gamma e t2
check gamma (Ext (Inr e)) t = Left $ "Sum construction cannot have type " <> pprint t

check gamma (Ext (Case e (x,e1) (y,e2))) t =
  case synth gamma e of
    Right (SumTy t1 t2) -> do
      check ([(x,t1)] ++ gamma) e1 t
      check ([(y,t2)] ++ gamma) e2 t
    Right _ -> Left $ "Expecting sum type for " <> pprint e
    Left err -> Left err

-- Polymorphic lambda calculus
check gamma (TyAbs alpha e) (Forall alpha' tau)
  | alpha == alpha' =
    -- find all free variables in gamma which have alpha free inside of their type assumption
    case mapMaybe (\(id, t) -> if alpha `elem` freeVars t then Just id else Nothing) gamma of
      -- side condition is true
      [] -> check gamma e tau
      vars -> Left $ "Free variables " <> intercalate "," vars
                  <> " use bound type variable `" <> alpha <> "`"

  | otherwise =
    Left $ "Term-level type abstraction on `" <> alpha
          <> "` does not match name of type abstraction `" <> alpha' <> "`"

{--

G |- e => A'   A' <: A
--------------------------- synthCheck
G |- e <= A

--}

check gamma expr tyA =
  case synth gamma expr of
    Left err -> Left $ err <> "\nCould not synth type for " ++ pprint expr
    Right tyA' ->
      if isSubtype tyA' (IsSpec tyA) then
        Right ()
      else
        Left $ "Expecting " <> pprint tyA <> " but got " <> pprint tyA'

{-
Bidirectional synthesis
**********************************
 G |- e => A    synth
**********************************
-}

synth :: Context -> Expr PCF -> Either String Type

{-

(x : A) in G
--------------- var
G |- x => A

-}

synth gamma (Var x) =
 case lookup x gamma of
    Just ty -> Right ty
    Nothing -> Left $ "Variable " <> x <> " not found in context."

{-

The following is a special form of (app) which
is useful for doing top-level definitions in our style,
which are of the form (\x -> e) (e' : A).

This is equivalent to combining the synthesis for general
application (below, (app) rule) with the synthesis rule we can have
if we have Church-style syntax

      G, x : A |- e => B
      -------------------------------------- abs-Church
      G |- (\(x : A) -> e) => A -> B

i.e., we know we have a signature for the argument.

-}

-- app (special for form of top-level definitions)
synth gamma (App (Abs x Nothing e1) (Sig e2 tyA)) =
  case check gamma e2 tyA of
    Right () -> synth ((x, tyA) : gamma) e1
    Left err -> Left err
    -- else error $ "Expecting (" ++ pprint e2 ++ ") to have type " ++ pprint tyA


-- abs-Church (actually rule)
synth gamma (Abs x (Just tyA) e) =
  synth ((x, tyA) : gamma) e

-- Type checking a type speciaisation
synth gamma (App e (TyEmbed tau')) =
  case synth gamma e of
    Right (Forall alpha tau) -> Right $ substituteType tau (alpha, tau')
    Right t -> Left $ "Expecting polymorphic type but got `" <> pprint t <> "`"
    Left err -> Left $ err <> "\nExpecting polymorphic type but didn't get anything."

{-

  G |- e1 => A -> B    G |- e2 <= A
  ----------------------------------- app
  G |- e1 e2 => B

-}

synth gamma (App e1 e2) =
  -- Synth the left-hand side
  case synth gamma e1 of
    Right (FunTy tyA tyB) ->
      -- Check the right-hand side
      case check gamma e2 tyA of
        -- Yay!
        Right () -> Right tyB
        Left err -> Left err --  error $ "Expecting (" ++ pprint e2 ++ ") to have type " ++ pprint tyA

    Right t ->
      Left $ "Expecting (" ++ pprint e1 ++ ") to have function type but got " ++ pprint t

    Left err ->
      Left $ err <> "\nExpecting (" ++ pprint e1 ++ ") to have function type."

-- PCF rules
synth gamma (Ext Zero) =
  Right natTy

synth gamma (Ext Succ) =
  Right (FunTy natTy natTy)

synth gamma (Ext (NatCase e e1 (x,e2))) =
  case check gamma e natTy of
    Right () ->
      case synth gamma e1 of
        Right t ->
          case check ([(x, natTy)] ++ gamma) e2 t of
            Right () -> Right t
            Left err -> Left err
        Left err ->
          case synth ([(x, natTy)] ++ gamma) e2 of
            Right t ->
              case check gamma e1 t of
                Right () -> Right t
                Left err -> Left err
            Left err -> Left err
    Left err -> Left err

synth gamma (Ext (Fix e)) =
  case synth gamma e of
    Right (FunTy t1 t2) ->
      if t1 == t2 then Right t1
      else Left $ "Expecting (" ++ pprint e ++ ") to have function type with equal domain/range but got " ++ pprint (FunTy t1 t2)
    Right t -> Left $ "Expecting (" ++ pprint e ++ ") to have function type with equal domain/range but got " ++ pprint t
    Left err -> Left $ err <> "\nExpecting (" ++ pprint e ++ ") to have function type with equal domain/range"

synth gamma (Ext (Pair e1 e2)) =
  case synth gamma e1 of
    Right t1 ->
      case synth gamma e2 of
        Right t2 -> Right (ProdTy t1 t2)
        Left err -> Left err
    Left err -> Left err

synth gamma (Ext (Fst e)) =
  case synth gamma e of
    Right (ProdTy t1 t2) -> Right t1
    Right t -> Left $ "Expecting (" ++ pprint e ++ ") to have product type but got " ++ pprint t
    Left err -> Left err

synth gamma (Ext (Snd e)) =
  case synth gamma e of
    Right (ProdTy t1 t2) -> Right t2
    Right t -> Left $ "Expecting (" ++ pprint e ++ ") to have product type but got " ++ pprint t
    Left err -> Left err

synth gamma (Ext (Case e (x,e1) (y,e2))) =
  case synth gamma e of
    Right (SumTy t1 t2) -> (
      case synth ([(x,t1)] ++ gamma) e1 of
        Right t ->
          case check ([(y,t2)] ++ gamma) e2 t of
            Right () -> Right t
            Left err -> Left err
        Left err -> (
          case synth ([(y,t2)] ++ gamma) e2 of
            Right t ->
              case check ([(x,t1)] ++ gamma) e1 t of
                Right () -> Right t
                Left err -> Left err
            Left err -> Left $ err <> "\nCould not synth types for " ++ pprint e1 ++ ", " ++ pprint e2
          )
        )
    Right t -> Left $ "Expecting (" ++ pprint e ++ ") to have sum type but got " ++ pprint t
    Left err -> Left $ "Could not synth type for " ++ pprint e

synth gamma (Ext (NumFloat n)) =
  Right floatTy

synth gamma (Ext (BinOp op e1 e2)) =
  case check gamma e1 FloatTy of
    Right () ->
      case check gamma e2 FloatTy of
        Right () -> Right FloatTy
        Left err -> Left $ err <> "\nInferring the type of operator use " <> pprint op <> " on the left."
    Left err -> Left $ err <> "\nInferring the type of operator use " <> pprint op <> " on the right."


{-

  G |- e <= A
  ------------------- checkSynth
  G |- (e : A) => A

-}

-- checkSynth
synth gamma (Sig e ty) =
  case check gamma e ty of
    Right () -> Right ty
    Left err -> Left $ "Trying to check explicit signature " ++ pprint ty

-- catch all (cannot synth here)
synth gamma e =
   Left $ "Cannot synth the type for " ++ pprint e

---------------------------------
-- # Type equality
---------------------------------

data Specificational a = IsSpec { unwrapSpec :: a }

isSubtype :: Type -> Specificational Type -> Bool
isSubtype t1 (IsSpec (IntersectTy t1' t2')) =
  isSubtype t1 (IsSpec t1') || isSubtype t1 (IsSpec t2')
-- Fall through case
isSubtype t1 (IsSpec t2) = t1 == t2