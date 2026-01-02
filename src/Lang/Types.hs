{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Types where

import Lang.Syntax
import Lang.PrettyPrint
import Lang.Semantics (substituteType)
import Lang.Kinding
import Lang.Primitives
import Lang.Descriptions
import Lang.TypeHelpers
import Lang.TypeError

import Data.Maybe (mapMaybe)
import Debug.Trace

synthProgram :: Program -> Either TypeError (Type 0)
synthProgram = synthProgram' []
  where
    synthProgram' :: Context -> Program -> Either TypeError (Type 0)
    synthProgram' gamma [] = Right $ TyCon "Unit"  -- Return unit type when no return statement
    synthProgram' gamma ((VarDef v (Just ty) e):defs) =
      case check gamma e ty of
        Right () -> synthProgram' ((v, ty) : gamma) defs
        Left err -> Left err
    synthProgram' gamma ((VarDef v Nothing e):defs) =
      case synth gamma e of
        Right ty -> synthProgram' ((v, ty) : gamma) defs
        Left err -> Left err
    synthProgram' gamma ((Return e):defs) = synth gamma e
    synthProgram' gamma ((DataDef v constrs ty):defs) =
      synthProgram' gamma defs
    synthProgram' gamma (_:defs) = synthProgram' gamma defs
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
type Context = [(Identifier, Type 0)]

{-

Bidirectional checking
*********************************
G |- e <= A    check
**********************************
-}

check :: Context -> Expr -> Type 0 -> Either TypeError ()

check gamma (Var x) ty =
  case lookup x gamma of
    Nothing -> Left $ VariableNotFound x
    Just t -> 
      case typeEquality ty (IsSpec t) of
        Right () -> Right ()
        Left err -> Left $ TypeCheckFailure t ty (errorToString err)

check gamma (NumFloat n) ty =
  case isGradedType "Float" ty of
    Just desc ->
      -- Float type of any grade will do
        Right ()
    Nothing -> Left $ TypeCheckFailure (floatTy unitDescription) ty "Expecting Float type."

{--

G, x : A |- e <= B
--------------------------- abs
G |- (\x -> e) <= A -> B

-}
-- Curry style
check gamma (Abs x Nothing expr) (FunTy tyA tyB) =
  check ([(x, tyA)] ++ gamma) expr tyB

-- Church style
check gamma (Abs x (Just tyA') expr) (FunTy tyA tyB) =
  case typeEquality tyA' (IsSpec tyA) of
    Right () -> check ([(x, tyA)] ++ gamma) expr tyB
    Left err -> Left $ ChainedError (FunctionAbstractionTypeMismatch tyA tyA') err

-- Cast
check gamma (Cast e) t@(WithTy t1 t2) =
  case synthKind t1 of
    Left err -> Left err
    Right k | k == type0 -> check gamma e t1
    Right k1 ->
      case synthKind t2 of
        Left err -> Left err
        Right k | k == type0 -> check gamma e t2
        Right k2 ->
          Left $ CannotProjectFromType t (pprint k1 <> " and " <> pprint k2 <> " and thus no base Type remains.")

check gamma (Fix e) t = check gamma e (FunTy t t)

check gamma (NatCase e e1 (x,e2)) t = do
  check gamma e natTy
  check gamma e1 t
  check ([(x, natTy)] ++ gamma) e2 t

check gamma (Pair e1 e2) (ProdTy t1 t2) = do
  check gamma e1 t1
  check gamma e2 t2

check gamma (BinOp op e1 e2) ty@(isGradedType ("Float") -> Just desc) =
  case op of
    OpPlus ->
      case check gamma e1 ty of
        Right () -> check gamma e2 ty
        Left err -> Left err
    OpMinus ->
      case check gamma e1 ty of
        Right () -> check gamma e2 ty
        Left err -> Left err
    _ ->
      case synth gamma e1 of
        Left err -> Left $ OperatorTypeError op err
        Right (isGradedType ("Float") -> Just d1) ->
          case synth gamma e2 of
            Left err -> Left $ OperatorTypeError op err
            Right (isGradedType ("Float") -> Just d2) ->
              case op of
                OpTimes  -> typeEquality (floatTy $ WithTy d1 d2) (IsSpec $ floatTy desc)
                OpDivide -> typeEquality (floatTy $ WithTy d1 (reciprocalType d2)) (IsSpec $ floatTy desc)
            Right t2  -> Left $ ExpectingFloatType t2
        Right t1  -> Left $ ExpectingFloatType t1

-- check gamma e (WithTy t1 t2) = do
--   check gamma e t1
--   check gamma e t2

check gamma (Pair _ _) t = Left $ NonProductTypeToPair t

check gamma (Fst e) t =
  case synth gamma e of
    Right (ProdTy t1 t2) -> typeEquality t1 (IsSpec t)
    _ -> Left $ ExpectingProductType e t

check gamma (Snd e) t =
  case synth gamma e of
    Right (ProdTy t1 t2) -> typeEquality t2 (IsSpec t)
    _ -> Left $ ExpectingProductType e t

check gamma (Inl e) (SumTy t1 t2) = check gamma e t1
check gamma (Inl e) t = Left $ SumConstructionTypeMismatch t

check gamma (Inr e) (SumTy t1 t2) = check gamma e t2
check gamma (Inr e) t = Left $ SumConstructionTypeMismatch t

check gamma (Case e (x,e1) (y,e2)) t =
  case synth gamma e of
    Right (SumTy t1 t2) -> do
      check ([(x,t1)] ++ gamma) e1 t
      check ([(y,t2)] ++ gamma) e2 t
    Right _ -> Left $ ExpectingSumType e
    Left err -> Left err

-- Polymorphic lambda calculus
check gamma (TyAbs alpha e) (Forall alpha' tau)
  | alpha == alpha' =
    -- find all free variables in gamma which have alpha free inside of their type assumption
    case mapMaybe (\(id, t) -> if alpha `elem` freeVars t then Just id else Nothing) gamma of
      -- side condition is true
      [] -> check gamma e tau
      vars -> Left $ FreeVariablesInAbstraction vars

  | otherwise =
    Left $ TermLevelTypeAbstraction alpha

{--

G |- e => A'   A' <: A
--------------------------- synthCheck
G |- e <= A

--}

check gamma expr tyA =
  case synth gamma expr of
    Left err -> Left $ ChainedError err (CannotSynthType expr)
    Right tyA' ->
      case typeEquality tyA' (IsSpec tyA) of
        Right () -> Right ()
        Left err -> Left $ ChainedError err (TypeMismatch tyA tyA')

{-
Bidirectional synthesis
**********************************
 G |- e => A    synth
**********************************
-}

synth :: Context -> Expr -> Either TypeError (Type 0)

{-

(x : A) in G
--------------- var
G |- x => A

-}

synth gamma (Var x) =
 case lookup x gamma of
    Just ty -> Right ty
    Nothing -> Left $ VariableNotFound x

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
  case checkKind tyA type0 of
    Left err -> Left err
    Right () ->
      case check gamma e2 tyA of
        Right () -> synth ((x, tyA) : gamma) e1
        Left err -> Left err
        -- else error $ "Expecting (" ++ pprint e2 ++ ") to have type " ++ pprint tyA


-- abs-Church (actually rule)
synth gamma (Abs x (Just tyA) e) =
  case checkKind tyA type0 of
    Left err -> Left err
    Right () -> synth ((x, tyA) : gamma) e

-- Type checking a type speciaisation
synth gamma (App e (TyEmbed tau')) =
  case checkKind tau' type0 of
    Left err -> Left err
    Right () ->
      case synth gamma e of
        Right (Forall alpha tau) -> Right $ substituteType tau (alpha, tau')
        Right t -> Left $ ExpectingPolymorphicType t
        Left err -> Left err

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
      Left $ ExpectingFunctionType e1 t

    Left err -> Left err

-- PCF rules
synth gamma Zero =
  Right natTy

synth gamma Succ =
  Right (FunTy natTy natTy)

synth gamma (NatCase e e1 (x,e2)) =
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

synth gamma (Fix e) =
  case synth gamma e of
    Right (FunTy t1 t2) ->
      if t1 == t2 then Right t1
      else Left $ FixpointDomainRangeMismatch e t1 t2
    Right t -> Left $ ExpectingFunctionType e t
    Left err -> Left err

synth gamma (Pair e1 e2) =
  case synth gamma e1 of
    Right t1 ->
      case synth gamma e2 of
        Right t2 -> Right (ProdTy t1 t2)
        Left err -> Left err
    Left err -> Left err

synth gamma (Fst e) =
  case synth gamma e of
    Right (ProdTy t1 t2) -> Right t1
    Right t -> Left $ ExpectingProductType e t
    Left err -> Left err

synth gamma (Snd e) =
  case synth gamma e of
    Right (ProdTy t1 t2) -> Right t2
    Right t -> Left $ ExpectingProductType e t
    Left err -> Left err

synth gamma (Case e (x,e1) (y,e2)) =
  case synth gamma e of
    Right (SumTy t1 t2) -> (
      case synth ([(x,t1)] ++ gamma) e1 of
        Right t ->
          case check ([(y,t2)] ++ gamma) e2 t of
            Right () -> Right t
            Left err -> Left err
        Left err -> do
          t <- synth ([(y,t2)] ++ gamma) e2
          case check ([(x,t1)] ++ gamma) e1 t of
            Right () -> Right t
            Left err -> Left err
      )
    Right t -> Left $ ExpectingSumType e
    Left err -> Left $ err

synth gamma (NumFloat n) =
  Right (floatTy unitDescription)

synth gamma (BinOp op e1 e2) =
  case synth gamma e1 of
    Left err -> Left $ OperatorTypeError op err
    Right t1 ->
      case isGradedType "Float" t1 of
        Nothing -> Left $ ExpectingFloatType t1
        Just d1 ->
          case synth gamma e2 of
            Left err -> Left $ OperatorTypeError op err
            Right t2 ->
              case isGradedType "Float" t2 of
                Nothing -> Left $ ExpectingFloatType t2
                Just d2 ->
                  case op of
                    OpTimes -> Right $ floatTy (normalisationByEvaluation $ ProdTy d1 d2)
                    OpDivide -> Right $ floatTy (normalisationByEvaluation $ ProdTy d1 (reciprocalType d2))
                    _        ->
                      case typeEquality d1 (IsSpec d2) of
                        -- d1 == d2
                        Right () -> Right $ floatTy (normalisationByEvaluation d1)
                        Left err -> Left $ OperatorDescriptionMismatch op (normalisationByEvaluation d1) (normalisationByEvaluation d2)


{-

  G |- e <= A
  ------------------- checkSynth
  G |- (e : A) => A

-}

-- checkSynth
synth gamma (Sig e ty) =
  case checkKind ty type0 of
    Left err -> Left err
    Right () ->
      case check gamma e ty of
        Right () -> Right ty
        Left err -> Left $ ExplicitSignatureCheckFailure ty err

-- catch all (cannot synth here)
synth gamma e =
   Left $ CannotSynthType e

---------------------------------
-- # Type equality
---------------------------------

typeEquality :: Type 0 -> Specificational (Type 0) -> Either TypeError ()
typeEquality (isGradedType "Float" -> Just d1) (IsSpec (isGradedType "Float" -> Just d2)) =
  descriptionEquality d1 (IsSpec d2)
typeEquality t1 (IsSpec t2) =
  if t1 == t2
    then Right ()
    else Left $ TypeMismatch t2 t1

---------------------------------

-- | Convert a TypeError to a human-readable String
errorToString :: TypeError -> String
errorToString (VariableNotFound x) =
  "Variable " <> x <> " not found in context."

errorToString (TypeMismatch expected actual) =
  "Expecting type " <> pprint (normalise expected) <> " but got " <> pprint (normalise actual)

errorToString (TypeCheckFailure inferred checked reason) =
  reason <> "\nTrying to check at " <> pprint (normalise checked) 
  <> " but got type " <> pprint (normalise inferred)

errorToString (CannotSynthType e) =
  "Cannot synth the type for " ++ pprint e

errorToString (ExpectingFloatType t) =
  "Expecting Float type but got " ++ pprint (normalise t)

errorToString (ExpectingFunctionType e t) =
  "Expecting (" ++ pprint e ++ ") to have function type but got " ++ pprint (normalise t)

errorToString (ExpectingProductType e t) =
  "Expecting (" ++ pprint e ++ ") to have product type but got " ++ pprint (normalise t)

errorToString (ExpectingSumType e) =
  "Expecting sum type for " <> pprint e

errorToString (ExpectingPolymorphicType t) =
  "Expecting polymorphic type but got `" <> pprint (normalise t) <> "`"

errorToString (NonProductTypeToPair t) =
  "Trying to assign non-product type " <> pprint (normalise t) <> " to pair."

errorToString (SumConstructionTypeMismatch t) =
  "Sum construction cannot have type " <> pprint (normalise t)

errorToString (FunctionAbstractionTypeMismatch expected actual) =
  "In function abstraction, expecting argument type " <> pprint (normalise expected) 
  <> " but got " <> pprint (normalise actual)

errorToString (FixpointDomainRangeMismatch e t1 t2) =
  "Expecting (" ++ pprint e ++ ") to have function type with equal domain/range but got " 
  ++ pprint (normalise (FunTy t1 t2))

errorToString (ExplicitSignatureCheckFailure ty err) =
  errorToString err <> "\nTrying to check explicit signature " ++ pprint (normalise ty)

errorToString (CannotProjectFromType t reason) =
  "Cannot project out of " <> pprint (normalise t) <> " as the kinds are " <> reason

errorToString (DescriptionEqualityFailure t1 t2) =
  "Description equality failed between " ++ pprint (normalise t1) ++ " and " ++ pprint (normalise t2)

errorToString (DescriptionKeyMismatch expected actual) =
  "Expecting description keys " <> show expected <> " but got " <> show actual

errorToString (AbelianGroupMismatch expected actual) =
  "Expecting abelian group " <> pprint (normalise expected) <> " but got " <> pprint (normalise actual)

errorToString (TypeTreeMismatch expected actual) =
  "Expecting type tree " <> pprint (normalise expected) <> " but got " <> pprint (normalise actual)

errorToString MismatchedDescriptionReprTypes =
  "Mismatched description representation types"

errorToString (KindMismatch expectedK actualK t) =
  "For " <> pprint (normalise t) <> ", expecting kind " <> pprint expectedK 
  <> " but got " <> pprint actualK

errorToString (UnknownTypeConstructor c) =
  "Unknown type constructor " <> c

errorToString (ExpectingFunctionKind k) =
  "Expecting a function kind but got " <> pprint k

errorToString (CannotInferKind t) =
  "Cannot infer kind for " <> pprint (normalise t)

errorToString (OperatorTypeError op err) =
  errorToString err <> "\nError infering type for operator " ++ pprint op

errorToString (OperatorDescriptionMismatch op t1 t2) =
  "Expecting descriptions to be the same but got " <> pprint (normalise t1) 
  <> " and " <> pprint (normalise t2) <> " for operator " ++ pprint op

errorToString (FreeVariablesInAbstraction vars) =
  "Free variables " <> unwords (map show vars)

errorToString (TermLevelTypeAbstraction alpha) =
  "Term-level type abstraction on `" <> alpha 
  <> "` is not yet supported (requires a polymorphic inference algorithm)"

errorToString TypeApplicationExpectsType =
  "Type application expects a type"

errorToString (ContextualError msg) =
  msg

errorToString (ChainedError err1 err2) =
  errorToString err1 <> "\n" <> errorToString err2

-- | Normalize a type (useful for displaying information to the user)
normalise :: Type 0 -> Type 0
normalise t =
  if normalise' t == t
    then t
    else normalise (normalise' t)

normalise' :: Type 0 -> Type 0
normalise' (FunTy t1 t2) = FunTy (normalise' t1) (normalise' t2)
normalise' (isGradedType "Float" -> Just desc) =
    floatTy (normalisationByEvaluation desc)
normalise' (TyApp t1 t2) = TyApp (normalise' t1) (normalise' t2)
normalise' (Forall x t) = Forall x (normalise' t)
normalise' (ProdTy t1 t2) = ProdTy (normalise' t1) (normalise' t2)
normalise' (SumTy t1 t2) = SumTy (normalise' t1) (normalise' t2)
normalise' (WithTy t (TyCon "1")) = normalise' t
normalise' (WithTy (TyCon "1") t) = normalise' t
normalise' (WithTy t1 t2) = WithTy (normalise' t1) (normalise' t2)
normalise' (ExponentTy t n) = ExponentTy (normalise' t) n
normalise' t = t  -- Base case: TyCon, TyVar, etc.
