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
    , pendingAnnotations :: Map.Map Identifier (Type 0)
    , outputDefs :: [Def 'Desugared]
    }

initState :: ST
initState = ST 0 Map.empty []

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
desugar p = outputDefs <$> execStateT (traverse_ desugarDef p) initState

-- | Add desugared definitions to the output of the desugaring pass.
emitDefs :: [Def 'Desugared] -> Desugar ()
emitDefs defs = modify $ \st -> st { outputDefs = outputDefs st ++ defs }

desugarDef :: Def 'Parsed -> Desugar ()
desugarDef (TypeDef id ty1 ty2) = emitDefs [TypeDef id ty1 ty2]
desugarDef (DataDef id cs ty)   = emitDefs [DataDef id cs ty]
desugarDef (ImportDef spec)     = emitDefs [ImportDef spec]
desugarDef (Return e)           = emitDefs [Return e]
desugarDef (AnnDef id ty) = do
  -- Add the typing annotation of id
  modify $ \st -> st { pendingAnnotations = Map.insert id ty (pendingAnnotations st) }
desugarDef (FunDef id args body) = do
  annotations <- pendingAnnotations <$> get
  bodyExpr <- desugarBody annotations body
  -- Get the types of arguments
  typedArgs <- lift $ resolveFunctionParameterTypes args body
  -- Build the function input type
  let argType = functionArgType typedArgs
  -- Rewrite the body expression to have the right type annotations
  argVar <- freshVar
  let bindArgs = bindFunctionArgs typedArgs (Var argVar) bodyExpr
  -- Build the lambda
  let functionExpr = Abs argVar (Just argType) bindArgs
  emitDefs [ValDef (VarLhs id Nothing) functionExpr]

desugarDef (ValDef lhs e) = do
    lhs' <- applyPendingAnnotation lhs
    desugarVal lhs' e

-- | Resolve the declared types of a function's parameters before lowering its
-- body to a lambda expression. Parameters can carry an optional legacy header
-- annotation, while standalone annotations in the body support Python-style
-- declarations such as @def f(x): x : T@. A body annotation takes precedence,
-- keeping the parameter name next to its documentation and unit information.
-- Every parameter must resolve to a type because the generated lambda is
-- explicitly typed.
resolveFunctionParameterTypes :: [(Identifier, Maybe (Type 0))] -> [Def 'Parsed] -> Either TypeError [(Identifier, Type 0)]
resolveFunctionParameterTypes args body = traverse argumentType args
    where
        argumentType (arg, headerType) =
            case [ty | AnnDef name ty <- body, name == arg] of
                ty:_ | Just _ <- headerType ->
                    Left $ WellFormednessError $ DuplicateParameterAnnotation arg
                ty:_ -> Right (arg, ty)
                [] -> case headerType of
                    Just ty -> Right (arg, ty)
                    Nothing -> Left $ WellFormednessError $ MissingParameterAnnotation arg

-- From a list of identifiers and types, create a product type
functionArgType :: [(Identifier, Type 0)] -> Type 0
functionArgType [] = tyCon0 "()"
functionArgType args = foldr1 ProdTy (map snd args)

desugarBody :: Map.Map Identifier (Type 0) -> [Def 'Parsed] -> Desugar Expr
desugarBody _ [] = return (Con "None" [])
desugarBody _ (Return e : _) = return e
desugarBody annotations (AnnDef id ty : defs) =
    desugarBody (Map.insert id ty annotations) defs
desugarBody annotations (ValDef lhs e : defs) = do
    let (lhs', annotations') = applyAnnotation annotations lhs
    rest <- desugarBody annotations' defs
    bindLhs lhs' e rest
desugarBody annotations (_ : defs) = desugarBody annotations defs

applyPendingAnnotation :: Lhs 'Parsed -> Desugar (Lhs 'Parsed)
applyPendingAnnotation lhs = do
    st <- get
    let (lhs', annotations) = applyAnnotation (pendingAnnotations st) lhs
    put $ st { pendingAnnotations = annotations }
    return lhs'

-- | Apply and consume a preceding standalone annotation when the binding has
-- no inline annotation. Inline annotations remain authoritative.
applyAnnotation :: Map.Map Identifier (Type 0) -> Lhs 'Parsed -> (Lhs 'Parsed, Map.Map Identifier (Type 0))
applyAnnotation annotations lhs@(VarLhs id Nothing) =
    case Map.lookup id annotations of
        Just ty -> (VarLhs id (Just ty), Map.delete id annotations)
        Nothing -> (lhs, annotations)
applyAnnotation annotations lhs = (lhs, annotations)

bindLhs :: Lhs 'Parsed -> Expr -> Expr -> Desugar Expr
bindLhs (VarLhs x (Just ty)) e rest = return (Let x (Sig e ty) rest)
bindLhs (VarLhs x Nothing) e rest = return (Let x e rest)
bindLhs (PairLhs l1 l2) e rest = do
    tmp <- freshVar
    rest' <- bindLhs l1 (Fst (Var tmp)) rest
    bindLhs l2 (Snd (Var tmp)) (Let tmp e rest')

bindFunctionArgs :: [(Identifier, Type 0)] -> Expr -> Expr -> Expr
bindFunctionArgs [] _ body = body
bindFunctionArgs [(x, _)] arg body = Let x arg body
bindFunctionArgs args arg body =
    foldr bind body (zip args (pairProjections (length args) arg))
  where
    bind ((x, _), projection) rest = Let x projection rest

pairProjections :: Int -> Expr -> [Expr]
pairProjections count arg =
    [ projection index | index <- [0 .. count - 1] ]
  where
    projection 0 = Fst arg
    projection index = Snd (iterate Snd arg !! (index - 1))

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