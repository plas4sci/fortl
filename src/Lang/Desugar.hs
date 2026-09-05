{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Desugar where

import Lang.Syntax

import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Class     (lift)

import Data.Foldable                 (traverse_)

newtype ST = ST { next_var :: Integer }

initState :: ST
initState = ST 0

type Desugar = StateT ST (Writer [Def 'Desugared])

freshVar :: Desugar Identifier
freshVar = do
    st <- get
    let i = next_var st
    put $ st { next_var = i + 1 }
    return $ "_" ++ show i

desugar :: Program 'Parsed -> Program 'Desugared
desugar p = 
    let m = traverse_ desugarDef p
        (_, out) = runWriter (runStateT m initState)
    in out

-- | Add desugared definitions to the output of the desugaring pass.
emitDefs :: [Def 'Desugared] -> Desugar ()
emitDefs = lift . tell

desugarDef :: Def 'Parsed -> Desugar ()
desugarDef (TypeDef id ty1 ty2) = emitDefs [TypeDef id ty1 ty2]
desugarDef (DataDef id cs ty)   = emitDefs [DataDef id cs ty]
desugarDef (ImportDef spec)     = emitDefs [ImportDef spec]
desugarDef (Return e)           = emitDefs [Return e]
desugarDef (AnnDef _ _)         = return ()
desugarDef (FunDef id args body) = do
    bodyExpr <- desugarBody body
    let typedArgs = functionArguments args body
        argType = functionArgType typedArgs
        bindArgs = bindFunctionArgs typedArgs (Var "_args") bodyExpr
        functionExpr = Abs "_args" (Just argType) bindArgs
    emitDefs [ValDef (VarLhs id Nothing) functionExpr]
desugarDef (ValDef lhs e)       = do desugarVal lhs e

-- | Resolve the declared types of a function's parameters before lowering its
-- body to a lambda expression. Parameters can carry an optional legacy header
-- annotation, while standalone annotations in the body support Python-style
-- declarations such as @def f(x): x : T@. A body annotation takes precedence,
-- keeping the parameter name next to its documentation and unit information.
-- Every parameter must resolve to a type because the generated lambda is
-- explicitly typed.
functionArguments :: [(Identifier, Maybe (Type 0))] -> [Def 'Parsed] -> [(Identifier, Type 0)]
functionArguments args body = map argumentType args
    where
        argumentType (arg, headerType) =
            case [ty | AnnDef name ty <- body, name == arg] of
                ty:_ -> (arg, ty)
                [] -> case headerType of
                    Just ty -> (arg, ty)
                    Nothing -> error $ "Missing type annotation for function parameter " ++ arg

functionArgType :: [(Identifier, Type 0)] -> Type 0
functionArgType [( _, ty)] = ty
functionArgType args = foldr1 ProdTy (map snd args)

desugarBody :: [Def 'Parsed] -> Desugar Expr
desugarBody [] = return (Con "None" [])
desugarBody (Return e : _) = return e
desugarBody (AnnDef _ _ : defs) = desugarBody defs
desugarBody (ValDef lhs e : defs) = do
    rest <- desugarBody defs
    bindLhs lhs e rest
desugarBody (_ : defs) = desugarBody defs

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