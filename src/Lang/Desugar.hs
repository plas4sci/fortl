{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Desugar where

-- Lowers a program into a desugared state (for simpler interpreter)

import Lang.Syntax
import Lang.TypeError

import Control.Monad.Trans.State
import Control.Monad.Trans.Class     (lift)

import Data.Foldable                 (traverse_)
import qualified Data.Map.Lazy as Map

-- Desugarer state
data ST = ST
    { next_var :: Integer
      -- Stack of type annotations that have been found inline
    , pendingAnnotations :: [Map.Map Identifier (Type 0)]
      -- Stack of desugared defs, one list per nested function body being desugared
    , outputDefs :: [[Def 'Desugared]]
    }

initState :: ST
initState = ST 0 [Map.empty] [[]]

-- Desugarer monad
type Desugar = StateT ST (Either TypeError)

freshVar :: Desugar Identifier
freshVar = do
    st <- get
    let i = next_var st
    put $ st { next_var = i + 1 }
    return $ "_" ++ show i

-- Convert from a parsed program to a desugared one
desugar :: Program 'Parsed -> Either TypeError (Program 'Desugared)
desugar p = fst . popStack . outputDefs <$> execStateT (traverse_ desugarDef p) initState

-- | Pop the top of a stack maintained non-empty by construction (pushes and
-- pops on 'outputDefs'/'pendingAnnotations' are always balanced).
popStack :: [a] -> (a, [a])
popStack (top:rest) = (top, rest)
popStack []         = error "Lang.Desugar: stack invariant violated"

-- | Add desugared definitions to the top of the output stack.
emitDefs :: [Def 'Desugared] -> Desugar ()
emitDefs defs = modify $ \st ->
  let (top, rest) = popStack (outputDefs st)
  in st { outputDefs = (top ++ defs) : rest }

desugarDef :: Def 'Parsed -> Desugar ()
desugarDef (TypeDef id ty1 ty2) = emitDefs [TypeDef id ty1 ty2]
desugarDef (DataDef id cs ty)   = emitDefs [DataDef id cs ty]
desugarDef (ImportDef spec)     = emitDefs [ImportDef spec]
desugarDef (Return e)           = emitDefs [Return e]

desugarDef (AnnDef id ty) =
  -- Add the typing annotation of id (into the head stack)
  modify $ \st ->
    let (top, rest) = popStack (pendingAnnotations st)
    in st { pendingAnnotations = Map.insert id ty top : rest }

desugarDef (FunDef id args returnTy body) = do
  -- Push a new annotation map and defs list onto their stacks
  modify $ \st -> st { pendingAnnotations = Map.empty : pendingAnnotations st
                     , outputDefs = [] : outputDefs st }
  -- Desugar the body
  traverse_ desugarDef body
  -- Pop the body's desugared defs and annotations off their stacks
  st <- get
  let (body', outputRest)          = popStack (outputDefs st)
      (headAnnotations, annotationsRest) = popStack (pendingAnnotations st)
  put (st { outputDefs = outputRest, pendingAnnotations = annotationsRest })
  -- Resolve the types into the parameters
  typedParams <- lift $ resolveFunctionParameterTypes args headAnnotations
  emitDefs [FunDefElaborated id typedParams returnTy body']

desugarDef (ValDef lhs e) = do
    lhs' <- applyPendingAnnotation lhs
    desugarVal lhs' e

-- | Resolve the declared types of a function's parameters before lowering its
-- body to a lambda expression. Parameters can come with their type or have
-- their type given as a standalon annotation in the body
-- There should be exactly one of these, not both
resolveFunctionParameterTypes :: [(Identifier, Maybe (Type 0))] -> Map.Map Identifier (Type 0) -> Either TypeError [(Identifier, Type 0)]
resolveFunctionParameterTypes args annotations = mapM fillIn args
    where
      fillIn (param_var, Nothing) = 
        case Map.lookup param_var annotations of
          Nothing -> Left $ WellFormednessError $ MissingParameterAnnotation param_var
          Just ty -> Right (param_var, ty)
      fillIn (param_var, Just ty) =
        case Map.lookup param_var annotations of
          Nothing  -> Right (param_var, ty)
          Just ty' -> Left $ WellFormednessError $ DuplicateParameterAnnotation param_var

applyPendingAnnotation :: Lhs 'Parsed -> Desugar (Lhs 'Parsed)
applyPendingAnnotation lhs = do
    st <- get
    let (top, rest) = popStack (pendingAnnotations st)
        (lhs', annotations) = applyAnnotation top lhs
    put $ st { pendingAnnotations = annotations : rest }
    return lhs'

-- | Apply and consume a preceding standalone annotation when the binding has
-- no inline annotation. Inline annotations remain authoritative.
applyAnnotation :: Map.Map Identifier (Type 0) -> Lhs 'Parsed -> (Lhs 'Parsed, Map.Map Identifier (Type 0))
applyAnnotation annotations lhs@(VarLhs id Nothing) =
    case Map.lookup id annotations of
        Just ty -> (VarLhs id (Just ty), Map.delete id annotations)
        Nothing -> (lhs, annotations)
applyAnnotation annotations lhs = (lhs, annotations)

-- (a, (b1, b2)) = c
-- _0 = c
-- a = fst _0
-- _1 = snd _0
-- b1 = fst _1
-- b2 = snd _2 

desugarVal :: Lhs p -> Expr -> Desugar ()
desugarVal (VarLhs x ty) e = emitDefs [ValDef (VarLhs x ty) e]

desugarVal (PairLhs l1 l2) e = do
    tmp <- freshVar
    emitDefs [ValDef (VarLhs tmp Nothing) e]
    desugarVal l1 (Fst (Var tmp))
    desugarVal l2 (Snd (Var tmp))