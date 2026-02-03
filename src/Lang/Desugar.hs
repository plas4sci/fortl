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

nextVar :: Desugar Identifier
nextVar = do
    st <- get
    let i = next_var st
    put $ st { next_var = i + 1 }
    return $ "_" ++ show i

desugar :: Program 'Parsed -> Program 'Desugared
desugar p = 
    let m = traverse_ desugarDef p
        (_, out) = runWriter (runStateT m initState)
    in out

emit :: [Def 'Desugared] -> Desugar ()
emit d = lift $ tell d

desugarDef :: Def 'Parsed -> Desugar ()
desugarDef (TypeDef id ty1 ty2) = emit [TypeDef id ty1 ty2]
desugarDef (DataDef id cs ty)   = emit [DataDef id cs ty]
desugarDef (Return e)           = emit [Return e]
desugarDef (ValDef lhs ty e)    = do desugarVal lhs ty e

-- (a, (b1, b2)) = c
-- _0 = c
-- a = fst _0
-- _1 = snd _0
-- b1 = fst _1
-- b2 = snd _2 

desugarVal :: Lhs p -> Maybe (Type 0) -> Expr -> Desugar ()
desugarVal (VarLhs x) ty e = emit [ValDef (VarLhs x) ty e]

desugarVal (PairLhs l1 l2) ty e = do
    tmp <- nextVar
    emit [ValDef (VarLhs tmp) ty e]
    let (t1, t2) = 
            case ty of
                Just (ProdTy t1 t2) -> (Just t1, Just t2)
                _ -> (Nothing, Nothing)
    desugarVal l1 t1 (Fst (Var tmp))
    desugarVal l2 t2 (Snd (Var tmp))