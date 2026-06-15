{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}

module Lang.Types where

import Lang.Syntax
import Lang.PrettyPrint
import Lang.Substitution
import Lang.Kinding
import Lang.Primitives
import Lang.Descriptions
import Lang.TypeHelpers
import Lang.TypeError

import Data.Maybe (mapMaybe)

synthProgram :: Program 'Desugared -> Either TypeError (Type 0)
synthProgram = synthProgram' []
  where
    synthProgram' :: Context -> Program 'Desugared -> Either TypeError (Type 0)
    synthProgram' gamma [] = 
      case lookup "it" gamma of
        Just ty -> return ty
        Nothing -> Right $ tyCon0 "Unit"  -- Return unit type when no return statement
    synthProgram' gamma ((ValDef (VarLhs v (Just ty)) e):defs) =
      case synthKind ty of
        Left err -> Left err
        Right (ty', kind) ->
          case check gamma e ty' of
            Right () -> synthProgram' ((v, ty') : gamma) defs
            Left err -> Left err
                  
    synthProgram' gamma ((ValDef (VarLhs v Nothing) e):defs) =
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

-- | Annotate a type error with a source position if it isn't already annotated
annotateWith :: Maybe SrcPos -> Either TypeError a -> Either TypeError a
annotateWith (Just p) (Left err) | not (isLocated err) = Left (Located p err)
annotateWith _ r = r

isLocated :: TypeError -> Bool
isLocated (Located _ _) = True
isLocated _ = False

{-

Bidirectional checking
*********************************
G |- e <= A    check
**********************************
-}

check :: Context -> Expr -> Type 0 -> Either TypeError ()
check gamma e ty = annotateWith (exprPos e) (check_ gamma e ty)

check_ :: Context -> Expr -> Type 0 -> Either TypeError ()

check_ gamma (Var x) ty =
  case lookup x gamma of
    Nothing -> Left $ VariableNotFound x
    Just t -> 
      case typeEquality ty (IsSpec t) of
        Right () -> Right ()
        Left err -> Left $ TypeCheckFailure t ty (let ?srcFile = "" in errorToString err)

check_ gamma (NumFloat n) ty =
  case isGradableNumericType ty of
    Just (base, _, _) | base == "Float" ->
        Right ()
    _ -> Left $ TypeCheckFailure (floatTy unitDescription) ty "Expecting Float type."

check_ gamma (NumInteger n) ty =
  case isGradableNumericType ty of
    Just (base, _, _) | base == "Integer" ->
        Right ()
    _ -> Left $ TypeCheckFailure (integerTy unitDescription) ty "Expecting Integer type."

check_ gamma (Sig e tyA) ty =
  case typeEquality ty (IsSpec tyA) of
    Right () -> check gamma e tyA
    Left err -> Left $ TypeCheckFailure tyA ty (let ?srcFile = "" in errorToString err)

{--

G, x : A |- e <= B
--------------------------- abs
G |- (\x -> e) <= A -> B

-}
-- Curry style
check_ gamma (Abs x Nothing expr) (FunTy tyA tyB) =
  check ([(x, tyA)] ++ gamma) expr tyB

-- Church style
check_ gamma (Abs x (Just tyA') expr) (FunTy tyA tyB) =
  case typeEquality tyA' (IsSpec tyA) of
    Right () -> check ([(x, tyA)] ++ gamma) expr tyB
    Left err -> Left $ ChainedError (FunctionAbstractionTypeMismatch tyA tyA') err

check_ gamma (Fix e) t = check gamma e (FunTy t t)

check_ gamma (NatCase e e1 (x,e2)) t = do
  check gamma e natTy
  check gamma e1 t
  check ([(x, natTy)] ++ gamma) e2 t

check_ gamma (Pair e1 e2) (ProdTy t1 t2) = do
  check gamma e1 t1
  check gamma e2 t2

check_ gamma (BinOp op e1 e2) ty@(isGradableNumericType -> Just (baseType, gradeType, desc)) =
  -- We have a gradable numeric type
  case op of
    -- Plus and minus must have the same type
    OpPlus ->
      case check gamma e1 ty of
        Right () -> check gamma e2 ty
        Left err -> Left $ OperatorTypeError op err
    OpMinus ->
      case check gamma e1 ty of
        Right () -> check gamma e2 ty
        Left err -> Left $ OperatorTypeError op err
    _ ->
      -- For other operators, first synth the types of the arguments
      -- whose base type must match
      case synth gamma e1 of
        Left err -> Left $ OperatorTypeError op err
        Right (isGradableNumericType -> Just (baseType', gradeType1, d1)) ->
          if baseType /= baseType'
            then Left $ OperatorTypeError op (BaseTypeMismatch baseType baseType')
            else
              case synth gamma e2 of
                Left err -> Left $ OperatorTypeError op err
                Right (isGradableNumericType -> Just (baseType'', gradeType2, d2)) ->
                  if baseType /= baseType''
                    then Left $ OperatorTypeError op (BaseTypeMismatch baseType baseType'')
                    else do
                      () <- kindEquality gradeType1 (IsSpec gradeType2)
                      case op of
                        OpTimes  -> typeEquality (TyApp (ImplicitTyApp (tyCon0 baseType) gradeType1) $ ProdTy d1 d2) (IsSpec ty)
                        OpDivide -> 
                          typeEquality (TyApp (ImplicitTyApp (tyCon0 baseType) gradeType1) $ ProdTy d1 (reciprocalType d2)) (IsSpec ty)
                Right t2  -> Left $ ExpectingNumericType t2
        Right t1  -> Left $ ExpectingNumericType t1

check_ gamma (Pair _ _) t = Left $ NonProductTypeToPair t

check_ gamma (Fst e) t =
  case synth gamma e of
    Right (ProdTy t1 t2) -> typeEquality t1 (IsSpec t)
    _ -> Left $ ExpectingProductType e t

check_ gamma (Snd e) t =
  case synth gamma e of
    Right (ProdTy t1 t2) -> typeEquality t2 (IsSpec t)
    _ -> Left $ ExpectingProductType e t

check_ gamma (Inl e) (SumTy t1 t2) = check gamma e t1
check_ gamma (Inl e) t = Left $ SumConstructionTypeMismatch t

check_ gamma (Inr e) (SumTy t1 t2) = check gamma e t2
check_ gamma (Inr e) t = Left $ SumConstructionTypeMismatch t

check_ gamma (Case e (x,e1) (y,e2)) t =
  case synth gamma e of
    Right (SumTy t1 t2) -> do
      check ([(x,t1)] ++ gamma) e1 t
      check ([(y,t2)] ++ gamma) e2 t
    Right _ -> Left $ ExpectingSumType e
    Left err -> Left err

-- Polymorphic lambda calculus
check_ gamma (TyAbs alpha e) (Forall alpha' tau)
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

check_ gamma expr tyA =
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
synth gamma e = annotateWith (exprPos e) (synth_ gamma e)

synth_ :: Context -> Expr -> Either TypeError (Type 0)

{-

(x : A) in G
--------------- var
G |- x => A

-}

synth_ gamma (Var x) =
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
synth_ gamma (App (Abs x Nothing e1) (Sig e2 tyA)) =
  case checkKind tyA type0 of
    Left err -> Left err
    Right tyA ->
      case check gamma e2 tyA of
        Right () -> synth ((x, tyA) : gamma) e1
        Left err -> Left err


-- abs-Church (actually rule)
synth_ gamma (Abs x (Just tyA) e) =
  case checkKind tyA type0 of
    Left err -> Left err
    Right tyA' -> synth ((x, tyA') : gamma) e

-- Type checking a type speciaisation
synth_ gamma (App e (TyEmbed tau')) =
  case checkKind tau' type0 of
    Left err -> Left err
    Right tau' ->
      case synth gamma e of
        Right (Forall alpha tau) -> Right $ substituteType tau (alpha, tau')
        Right t -> Left $ ExpectingPolymorphicType t
        Left err -> Left err

{-

  G |- e1 => A -> B    G |- e2 <= A
  ----------------------------------- app
  G |- e1 e2 => B

-}

synth_ gamma (App e1 e2) =
  -- Synth the left-hand side
  case synth gamma e1 of
    Right (FunTy tyA tyB) ->
      -- Check the right-hand side
      case check gamma e2 tyA of
        Right () -> Right tyB
        Left err -> Left err

    Right t ->
      Left $ ExpectingFunctionType e1 t

    Left err -> Left err

-- PCF rules
synth_ gamma Zero =
  Right natTy

synth_ gamma Succ =
  Right (FunTy natTy natTy)

synth_ gamma (NatCase e e1 (x,e2)) =
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

synth_ gamma (Fix e) =
  case synth gamma e of
    Right (FunTy t1 t2) ->
      if t1 == t2 then Right t1
      else Left $ FixpointDomainRangeMismatch e t1 t2
    Right t -> Left $ ExpectingFunctionType e t
    Left err -> Left err

synth_ gamma (Pair e1 e2) =
  case synth gamma e1 of
    Right t1 ->
      case synth gamma e2 of
        Right t2 -> Right (ProdTy t1 t2)
        Left err -> Left err
    Left err -> Left err

synth_ gamma (Fst e) =
  case synth gamma e of
    Right (ProdTy t1 t2) -> Right t1
    Right t -> Left $ ExpectingProductType e t
    Left err -> Left err

synth_ gamma (Snd e) =
  case synth gamma e of
    Right (ProdTy t1 t2) -> Right t2
    Right t -> Left $ ExpectingProductType e t
    Left err -> Left err

synth_ gamma (Case e (x,e1) (y,e2)) =
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

synth_ gamma (NumFloat n) =
  Right (floatTy unitDescription)

synth_ gamma (NumInteger n) =
  Right (integerTy unitDescription)

synth_ gamma (BinOp op e1 e2) =
  case synth gamma e1 of
    Left err -> Left $ OperatorTypeError op err
    Right t1 ->
      case isGradableNumericType t1 of
        Nothing -> Left $ ExpectingNumericType t1
        Just (baseType, gradeType1, d1) ->
          case synth gamma e2 of
            Left err -> Left $ OperatorTypeError op err
            Right t2 ->
              case isGradableNumericType t2 of
                Nothing -> Left $ ExpectingNumericType t2
                Just (baseType', gradeType2, d2) ->
                  if baseType /= baseType'
                    then Left $ OperatorTypeError op (BaseTypeMismatch baseType baseType')
                    else do
                      () <- kindEquality gradeType1 (IsSpec gradeType2)
                      case op of
                          OpTimes -> Right $ TyApp (ImplicitTyApp (tyCon0 baseType) gradeType1) (normalisationByEvaluation $ ProdTy d1 d2)
                          OpDivide -> Right $ TyApp (ImplicitTyApp (tyCon0 baseType) gradeType1) (normalisationByEvaluation $ ProdTy d1 (reciprocalType d2))
                          _        ->
                            case descriptionEquality d1 (IsSpec d2) of
                              Right () -> Right $ TyApp (ImplicitTyApp (tyCon0 baseType) gradeType1) (normalisationByEvaluation d1)
                              Left err -> Left $ OperatorDescriptionMismatch op (normalisationByEvaluation d1) (normalisationByEvaluation d2)


{-

  G |- e <= A
  ------------------- checkSynth
  G |- (e : A) => A

-}

-- checkSynth
synth_ gamma (Sig e ty) =
  case checkKind ty type0 of
    Left err -> Left err
    -- Get elaborated type
    Right ty' ->
      case check gamma e ty' of
        Right () -> Right ty
        Left err -> Left $ ExplicitSignatureCheckFailure ty err

-- catch all (cannot synth here)
synth_ gamma e =
   Left $ CannotSynthType e

---------------------------------
-- # Type equality
---------------------------------

typeEquality :: Type 0 -> Specificational (Type 0) -> Either TypeError ()
typeEquality (isGradableNumericType -> Just (baseType1, gradeType1, d1))
     (IsSpec (isGradableNumericType -> Just (baseType2, gradeType2, d2))) =
  if baseType1 == baseType2
    then do
      () <- kindEquality gradeType1 (IsSpec gradeType2)
      descriptionEquality d1 (IsSpec d2)
      
    else Left $ BaseTypeMismatch baseType1 baseType2
typeEquality (WithTy t1 t2) (IsSpec (WithTy t1' t2')) =
  (typeEquality t1 (IsSpec t1') >> typeEquality t2 (IsSpec t2')) <|>
  (typeEquality t1 (IsSpec t2') >> typeEquality t2 (IsSpec t1'))

typeEquality t1 (IsSpec t2) =
  if t1 == t2
    then Right ()
    else Left $ TypeMismatch t2 t1

---------------------------------

errorToString :: (?srcFile :: FilePath) => TypeError -> String
errorToString (VariableNotFound x) =
  "Variable " <> x <> " not found in context."

errorToString (TypeMismatch expected actual) =
  "Expecting type " <> pprint (normalise expected) <> " but got " <> pprint (normalise actual)

errorToString (TypeCheckFailure inferred checked reason) =
  reason <> "\nTrying to check at " <> pprint (normalise checked) 
  <> " but got type " <> pprint (normalise inferred)

errorToString (CannotSynthType e) =
  "Cannot synth the type for " ++ pprint e

errorToString (ExpectingNumericType t) =
  "Expecting numeric type but got " ++ pprint (normalise t)

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
  "Expecting descriptor `" <> pprint (normalise expected) <> "` but got `" <> pprint (normalise actual) <> "`"

errorToString (TypeTreeMismatch expected actual) =
  "Expecting type tree " <> pprint (normalise expected) <> " but got " <> pprint (normalise actual)

errorToString MismatchedDescriptionReprTypes =
  "Mismatched description representation types"

errorToString (BaseTypeMismatch expected actual) =
  "Mismatch between base type of graded types, expected " <> expected <> " but got " <> actual

errorToString (KindMismatch expectedK actualK (Just t)) =
  "For " <> pprint (normalise t) <> ", expecting kind " <> pprint expectedK 
  <> " but got " <> pprint actualK

errorToString (KindMismatch expectedK actualK Nothing) =
  "Expecting kind " <> pprint expectedK 
  <> " but got " <> pprint actualK

errorToString (SortMismatch expectedK actualK t) =
  "For " <> pprint t <> ", expecting sort " <> pprint expectedK 
  <> " but got " <> pprint actualK


errorToString (UnknownTypeConstructor c) =
  "Unknown type constructor " <> c

errorToString (ExpectingFunctionKind k) =
  "Expecting a function kind but got " <> pprint k

errorToString (ExpectingFunctionSort k) =
  "Expecting a function sort but got " <> pprint k


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

errorToString (Located (SrcPos l c) err) =
  ?srcFile <> ":" <> show l <> ":" <> show c <> ": " <> errorToString err

-- | Normalize a type (useful for displaying information to the user)
normalise :: Type 0 -> Type 0
normalise t =
  if normalise' t == t
    then t
    else normalise (normalise' t)

normalise' :: Type 0 -> Type 0
normalise' (FunTy t1 t2) = FunTy (normalise' t1) (normalise' t2)
normalise' (isGradableNumericType -> Just (baseType, gradeType, desc)) =
  TyApp (ImplicitTyApp (tyCon0 baseType) gradeType) (normalisationByEvaluation desc)
normalise' (TyApp t1 t2) = TyApp (normalise' t1) (normalise' t2)
normalise' (Forall x t) = Forall x (normalise' t)
normalise' (ProdTy t1 t2) = ProdTy (normalise' t1) (normalise' t2)
normalise' (SumTy t1 t2) = SumTy (normalise' t1) (normalise' t2)
normalise' (WithTy t (TyCon ZeroP "1")) = normalise' t
normalise' (WithTy (TyCon ZeroP "1") t) = normalise' t
normalise' (WithTy t1 t2) = WithTy (normalise' t1) (normalise' t2)
normalise' (ExponentTy t n) = ExponentTy (normalise' t) n
normalise' t = t  -- Base case: TyCon, TyVar, etc.

