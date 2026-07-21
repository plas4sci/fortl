{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

module Lang.TypeError where

import Lang.Syntax

-- | Comprehensive type error type for the Fortl language
data TypeError
  -- Variable errors
  = VariableNotFound Identifier
  
  -- Type checking errors
  | TypeMismatch { expected :: Type 0, actual :: Type 0 }
  | TypeCheckFailure { inferredType :: Type 0, checkType :: Type 0, reason :: String }
  | CannotSynthType Expr
  | ExpectingNumericType (Type 0)
  | ExpectingFunctionType Expr (Type 0)
  | ExpectingProductType Expr (Type 0)
  | ExpectingSumType Expr
  | ExpectingPolymorphicType (Type 0)
  | NonProductTypeToPair (Type 0)
  | SumConstructionTypeMismatch (Type 0)
  | FunctionAbstractionTypeMismatch { expectedArg :: Type 0, actualArg :: Type 0 }
  | FixpointDomainRangeMismatch Expr (Type 0) (Type 0)
  | ExplicitSignatureCheckFailure (Type 0) TypeError
  | CannotProjectFromType (Type 0) String
  
  -- Description/grading errors  
  | DescriptionEqualityFailure (Type 0) (Type 0)
  | DescriptionKeyMismatch [Identifier] [Identifier]
  | AbelianGroupMismatch (Type 0) (Type 0)
  | TypeTreeMismatch (Type 0) (Type 0)
  | MismatchedDescriptionReprTypes
  | BaseTypeMismatch Identifier Identifier
  
  -- Kinding errors
  | KindMismatch { expectedKind :: Type 1, actualKind :: Type 1, typeInQuestion :: Maybe (Type 0) }
  | UnknownTypeConstructor Identifier
  | ExpectingFunctionKind (Type 1)
  | ExpectingFunctionSort (Type 2)
  | CannotInferKind (Type 0)
  | SortMismatch { expectedSort :: Type 2, actualSort :: Type 2, kindInQuestion :: Type 1 }
  
  -- Operator errors
  | OperatorTypeError Op TypeError
  | OperatorDescriptionMismatch Op (Type 0) (Type 0)
  
  -- Abstraction and polymorphism errors
  | FreeVariablesInAbstraction [Identifier]
  | TermLevelTypeAbstraction Identifier
  | TypeApplicationExpectsType
  
  -- Generic/contextual errors
  | ContextualError String
  
  -- Nested/chained errors
  | ChainedError TypeError TypeError

  -- Source location annotation
  | Located SrcPos TypeError

  deriving (Show)

class MonadAlt m where
  (<|>) :: m a -> m a -> m a

instance MonadAlt (Either TypeError) where
  Left err <|> Left err' = Left err
  Right x <|> _ = Right x
  _ <|> Right x = Right x

instance MonadAlt Maybe where
  Nothing <|> Nothing = Nothing
  Just x <|> _ = Just x
  _ <|> Just x = Just x