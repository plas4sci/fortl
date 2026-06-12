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
desugarDef (Return e)           = emitDefs [Return e]
desugarDef (ValDef lhs e)       = do desugarVal lhs e

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