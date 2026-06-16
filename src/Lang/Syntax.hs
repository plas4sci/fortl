{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Syntax where

import qualified Data.Set as Set
import GHC.TypeLits

data Phase = Parsed | Desugared

type Identifier = String

-- | Source position (line, column)
data SrcPos = SrcPos { srcLine :: Int, srcCol :: Int }
  deriving (Eq, Show)

data ImportSpec
  = ImportModule Identifier
  | ImportAll Identifier
  | ImportOnly Identifier [Identifier]
  deriving (Eq, Show)

type Program (p :: Phase) = [Def p]

data Def (p :: Phase) where
    ValDef  :: Lhs p -> Expr -> Def p
    TypeDef :: Identifier -> Type n -> Type (1 + n) -> Def p
    DataDef :: Identifier -> [(Identifier, [Type n])] -> Type (1 + n) -> Def p -- Currently not implemented beyond front end
    ImportDef :: ImportSpec -> Def p
    Return  :: Expr -> Def p

data Lhs (p :: Phase) where
  VarLhs   :: Identifier -> Maybe (Type 0) -> Lhs p
  PairLhs  :: HasPairLhsC p => Lhs p -> Lhs p -> Lhs p

type family HasPairLhs p :: Bool where
  HasPairLhs 'Parsed    = 'True
  HasPairLhs 'Desugared = 'False

type HasPairLhsC p = (HasPairLhs p ~ 'True)

-- Abstract-syntax tree for LambdaCore with PCF extensions
-- The Mk* constructors carry an optional source position as their first argument.
-- Use the pattern synonyms (Abs, App, Var, ...) for position-agnostic matching
-- and construction. Use the Mk* constructors directly when you need to supply or
-- inspect source positions.
data Expr where
    MkAbs :: Maybe SrcPos -> Identifier -> Maybe (Type 0) -> Expr -> Expr
    MkApp :: Maybe SrcPos -> Expr ->  Expr   -> Expr
    MkVar :: Maybe SrcPos -> Identifier      -> Expr
    MkSig :: Maybe SrcPos -> Expr -> Type 0  -> Expr
    MkTyAbs   :: Maybe SrcPos -> Identifier -> Expr -> Expr
    MkTyEmbed :: Maybe SrcPos -> Type 0             -> Expr
    MkGenLet :: Maybe SrcPos -> Identifier -> Expr -> Expr -> Expr
    MkCast :: Maybe SrcPos -> Expr -> Expr
    MkZero :: Maybe SrcPos -> Expr
    MkSucc :: Maybe SrcPos -> Expr
    MkNatCase :: Maybe SrcPos -> Expr -> Expr -> (Identifier, Expr) -> Expr
    MkFix :: Maybe SrcPos -> Expr              -> Expr
    MkPair :: Maybe SrcPos -> Expr -> Expr     -> Expr
    MkFst :: Maybe SrcPos -> Expr              -> Expr
    MkSnd :: Maybe SrcPos -> Expr              -> Expr
    MkInl :: Maybe SrcPos -> Expr              -> Expr
    MkInr :: Maybe SrcPos -> Expr              -> Expr
    MkCase :: Maybe SrcPos -> Expr -> (Identifier, Expr) -> (Identifier, Expr) -> Expr
    MkNumFloat   :: Maybe SrcPos -> Float        -> Expr
    MkNumInteger :: Maybe SrcPos -> Integer      -> Expr
    MkBinOp :: Maybe SrcPos -> Op -> Expr -> Expr -> Expr
    MkCon   :: Maybe SrcPos -> Identifier -> [Expr]  -> Expr
  deriving Show

-- | Extract the source position from any Expr node
exprPos :: Expr -> Maybe SrcPos
exprPos (MkAbs p _ _ _)     = p
exprPos (MkApp p _ _)       = p
exprPos (MkVar p _)         = p
exprPos (MkSig p _ _)       = p
exprPos (MkTyAbs p _ _)     = p
exprPos (MkTyEmbed p _)     = p
exprPos (MkGenLet p _ _ _)  = p
exprPos (MkCast p _)        = p
exprPos (MkZero p)          = p
exprPos (MkSucc p)          = p
exprPos (MkNatCase p _ _ _) = p
exprPos (MkFix p _)         = p
exprPos (MkPair p _ _)      = p
exprPos (MkFst p _)         = p
exprPos (MkSnd p _)         = p
exprPos (MkInl p _)         = p
exprPos (MkInr p _)         = p
exprPos (MkCase p _ _ _)    = p
exprPos (MkNumFloat p _)    = p
exprPos (MkNumInteger p _)  = p
exprPos (MkBinOp p _ _ _)   = p
exprPos (MkCon p _ _)       = p

-- | Position-agnostic pattern synonyms.
-- In a pattern they match regardless of the stored position.
-- As expressions they construct with Nothing as the position.
pattern Abs :: Identifier -> Maybe (Type 0) -> Expr -> Expr
pattern Abs x mt e <- MkAbs _ x mt e
  where Abs x mt e = MkAbs Nothing x mt e

pattern App :: Expr -> Expr -> Expr
pattern App e1 e2 <- MkApp _ e1 e2
  where App e1 e2 = MkApp Nothing e1 e2

pattern Var :: Identifier -> Expr
pattern Var x <- MkVar _ x
  where Var x = MkVar Nothing x

pattern Sig :: Expr -> Type 0 -> Expr
pattern Sig e t <- MkSig _ e t
  where Sig e t = MkSig Nothing e t

pattern TyAbs :: Identifier -> Expr -> Expr
pattern TyAbs x e <- MkTyAbs _ x e
  where TyAbs x e = MkTyAbs Nothing x e

pattern TyEmbed :: Type 0 -> Expr
pattern TyEmbed t <- MkTyEmbed _ t
  where TyEmbed t = MkTyEmbed Nothing t

pattern GenLet :: Identifier -> Expr -> Expr -> Expr
pattern GenLet x e1 e2 <- MkGenLet _ x e1 e2
  where GenLet x e1 e2 = MkGenLet Nothing x e1 e2

pattern Cast :: Expr -> Expr
pattern Cast e <- MkCast _ e
  where Cast e = MkCast Nothing e

pattern Zero :: Expr
pattern Zero <- MkZero _
  where Zero = MkZero Nothing

pattern Succ :: Expr
pattern Succ <- MkSucc _
  where Succ = MkSucc Nothing

pattern NatCase :: Expr -> Expr -> (Identifier, Expr) -> Expr
pattern NatCase e e1 b <- MkNatCase _ e e1 b
  where NatCase e e1 b = MkNatCase Nothing e e1 b

pattern Fix :: Expr -> Expr
pattern Fix e <- MkFix _ e
  where Fix e = MkFix Nothing e

pattern Pair :: Expr -> Expr -> Expr
pattern Pair e1 e2 <- MkPair _ e1 e2
  where Pair e1 e2 = MkPair Nothing e1 e2

pattern Fst :: Expr -> Expr
pattern Fst e <- MkFst _ e
  where Fst e = MkFst Nothing e

pattern Snd :: Expr -> Expr
pattern Snd e <- MkSnd _ e
  where Snd e = MkSnd Nothing e

pattern Inl :: Expr -> Expr
pattern Inl e <- MkInl _ e
  where Inl e = MkInl Nothing e

pattern Inr :: Expr -> Expr
pattern Inr e <- MkInr _ e
  where Inr e = MkInr Nothing e

pattern Case :: Expr -> (Identifier, Expr) -> (Identifier, Expr) -> Expr
pattern Case e bl br <- MkCase _ e bl br
  where Case e bl br = MkCase Nothing e bl br

pattern NumFloat :: Float -> Expr
pattern NumFloat n <- MkNumFloat _ n
  where NumFloat n = MkNumFloat Nothing n

pattern NumInteger :: Integer -> Expr
pattern NumInteger n <- MkNumInteger _ n
  where NumInteger n = MkNumInteger Nothing n

pattern BinOp :: Op -> Expr -> Expr -> Expr
pattern BinOp op e1 e2 <- MkBinOp _ op e1 e2
  where BinOp op e1 e2 = MkBinOp Nothing op e1 e2

pattern Con :: Identifier -> [Expr] -> Expr
pattern Con c es <- MkCon _ c es
  where Con c es = MkCon Nothing c es

{-# COMPLETE MkAbs, MkApp, MkVar, MkSig, MkTyAbs, MkTyEmbed, MkGenLet, MkCast,
             MkZero, MkSucc, MkNatCase, MkFix, MkPair, MkFst, MkSnd,
             MkInl, MkInr, MkCase, MkNumFloat, MkNumInteger, MkBinOp, MkCon #-}
{-# COMPLETE Abs, App, Var, Sig, TyAbs, TyEmbed, GenLet, Cast,
             Zero, Succ, NatCase, Fix, Pair, Fst, Snd,
             Inl, Inr, Case, NumFloat, NumInteger, BinOp, Con #-}

-- Operators
data Op = OpPlus | OpTimes | OpMinus | OpDivide | OpExp
  deriving Show

isValue :: Expr -> Bool
isValue Abs{}   = True
isValue TyAbs{} = True
isValue Var{}   = True
isValue (NumFloat _) = True
isValue (NumInteger _) = True
isValue (Pair e1 e2) = isValue e1 && isValue e2
isValue (Inl e) = isValue e
isValue (Inr e) = isValue e
isValue Zero = True
isValue Succ = True
isValue e       = isNatVal e

isNatVal :: Expr -> Bool
isNatVal Zero = True
isNatVal Succ = True
isNatVal (App e1 e2) = isNatVal e1 && isNatVal e2
isNatVal _           = False

------------------------------
-- Type syntax

data ProxyN (n :: Nat) where
  ZeroP :: ProxyN 0
  SuccP :: ProxyN n -> ProxyN (1 + n)

pToInteger :: ProxyN n -> Integer
pToInteger ZeroP = 0
pToInteger (SuccP n) = 1 + pToInteger n

instance Show (ProxyN n) where
  show k = show $ pToInteger k

instance Eq (ProxyN n) where
  n == n' = pToInteger n == pToInteger n'

instance Ord (ProxyN n) where
  compare n n' = compare (pToInteger n) (pToInteger n')

data Type (n :: Nat) where
    -- {id : arg1} -> arg2
    ImplicitFunTy :: Identifier -> Type 2 -> Type 1 -> Type 1
    FunTy :: Type l -> Type l -> Type l  -- A -> B

    TyCon :: ProxyN l -> Identifier -> Type l        -- K

    ImplicitTyApp :: Type 0 -> Type 1 -> Type 0
    TyApp :: Type l -> Type l -> Type l  -- A B

    ProdTy :: Type 0 -> Type 0 -> Type 0 -- A * B
    SumTy  :: Type 0 -> Type 0 -> Type 0  -- A + B

    -- Type variables
    TyVar :: Identifier -> Type l            -- a
    -- Polymorphic lambda calculus types
    Forall :: Identifier -> Type 0 -> Type 0 -- forall a . A

    -- With types
    WithTy :: Type l -> Type l -> Type l

    -- For units
    -- TODO: make just a type constructor
    ExponentTy :: Type 0 -> Float -> Type 0

tyVar :: Identifier -> Type l
tyVar = TyVar

tyCon0 :: Identifier -> Type 0
tyCon0 id = TyCon ZeroP id

tyCon1 :: Identifier -> Type 1
tyCon1 id = TyCon (SuccP ZeroP) id

tyCon2 :: Identifier -> Type 2
tyCon2 id = TyCon (SuccP $ SuccP ZeroP) id

deriving instance Ord (Type 0)
deriving instance Ord (Type 1)
deriving instance Ord (Type 2)
deriving instance Eq (Type 0)
deriving instance Eq (Type 1)
deriving instance Eq (Type 2)
deriving instance Show (Type 0)
deriving instance Show (Type 1)
deriving instance Show (Type 2)

----------------------------

class Term t where
  boundVars :: t -> Set.Set Identifier
  freeVars  :: t -> Set.Set Identifier
  mkVar     :: Identifier -> t

instance Term Expr where
  boundVars (Abs var _ e)                = var `Set.insert` boundVars e
  boundVars (TyAbs var e)                = var `Set.insert` boundVars e
  boundVars (TyEmbed t)                  = boundVars t
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Var var)                    = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars (GenLet var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars (Cast e)                     = boundVars e
  boundVars (NatCase e e1 (x,e2))        =
    x `Set.insert` (boundVars e `Set.union` boundVars e1 `Set.union` boundVars e2)
  boundVars (Fix e)                      = boundVars e
  boundVars (Pair e1 e2)                 = boundVars e1 `Set.union` boundVars e2
  boundVars (Fst e)                      = boundVars e
  boundVars (Snd e)                      = boundVars e
  boundVars (Inl e)                      = boundVars e
  boundVars (Inr e)                      = boundVars e
  boundVars (Case e (x,e1) (y,e2))       =
    boundVars e `Set.union` (x `Set.insert` boundVars e1) `Set.union` (y `Set.insert` boundVars e2)
  boundVars (BinOp _ e1 e2)              = boundVars e1 `Set.union` boundVars e2
  boundVars _                            = Set.empty

  freeVars (Abs var _ e)                 = Set.delete var (freeVars e)
  freeVars (TyAbs var e)                 = Set.delete var (freeVars e)
  freeVars (TyEmbed t)                   = freeVars t
  freeVars (App e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Var var)                     = Set.singleton var
  freeVars (Sig e _)                     = freeVars e
  freeVars (GenLet var e1 e2)            = Set.delete var (freeVars e1 `Set.union` freeVars e2)
  freeVars (Cast e)                      = freeVars e
  freeVars (NatCase e e1 (x,e2))         =
    freeVars e `Set.union` freeVars e1 `Set.union` (Set.delete x (freeVars e2))
  freeVars (Fix e)                       = freeVars e
  freeVars (Pair e1 e2)                  = freeVars e1 `Set.union` freeVars e2
  freeVars (Fst e)                       = freeVars e
  freeVars (Snd e)                       = freeVars e
  freeVars (Inl e)                       = freeVars e
  freeVars (Inr e)                       = freeVars e
  freeVars (Case e (x,e1) (y,e2))        =
    freeVars e `Set.union` (Set.delete x (freeVars e1)) `Set.union` (Set.delete y (freeVars e2))
  freeVars (BinOp _ e1 e2)               = freeVars e1 `Set.union` freeVars e2
  freeVars _                             = Set.empty

  mkVar = Var

instance {-# OVERLAPS #-} Term (Type 0) where
  boundVars (FunTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (ProdTy t1 t2) = boundVars t1 `Set.union` boundVars t2
  boundVars (SumTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (ImplicitTyApp t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyApp t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyCon _ _)      = Set.empty
  boundVars (TyVar var)    = Set.empty
  boundVars (Forall var t) = var `Set.insert` boundVars t
  boundVars (WithTy t1 t2) = boundVars t1 `Set.union` boundVars t2
  boundVars (ExponentTy t1 _) = boundVars t1

  freeVars (FunTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (ProdTy t1 t2) = freeVars t1 `Set.union` freeVars t2
  freeVars (SumTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (ImplicitTyApp t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyApp t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyCon _ _)      = Set.empty
  freeVars (TyVar var)    = Set.singleton var
  freeVars (Forall var t) = var `Set.delete` freeVars t
  freeVars (WithTy t1 t2) = freeVars t1 `Set.union` freeVars t2
  freeVars (ExponentTy t1 _) = freeVars t1

  mkVar = TyVar

instance Term (Type 1) where
  boundVars (ImplicitFunTy i t1 t2) = i `Set.insert` (boundVars t1 `Set.union` boundVars t2)
  boundVars (FunTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyApp t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyCon _ _)      = Set.empty
  boundVars (TyVar var)    = Set.empty
  boundVars (WithTy t1 t2) = boundVars t1 `Set.union` boundVars t2

  freeVars (ImplicitFunTy i t1 t2) = freeVars t1 `Set.union` (Set.delete i (freeVars t2))
  freeVars (FunTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyApp t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyCon _ _)      = Set.empty
  freeVars (TyVar var)    = Set.singleton var
  freeVars (WithTy t1 t2) = freeVars t1 `Set.union` freeVars t2

  mkVar = TyVar

instance Term (Type 2) where
  boundVars (FunTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyApp t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (TyCon _ _)      = Set.empty
  boundVars (TyVar var)    = Set.empty
  boundVars (WithTy t1 t2) = boundVars t1 `Set.union` boundVars t2

  freeVars (FunTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyApp t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (TyCon _ _)      = Set.empty
  freeVars (TyVar var)    = Set.singleton var
  freeVars (WithTy t1 t2) = freeVars t1 `Set.union` freeVars t2

  mkVar = TyVar



  ----------------------------
-- Fresh variable with respect to a set of variables
-- By adding apostrophes to a supplied initial variable

fresh_var :: Identifier -> Set.Set Identifier -> Identifier
fresh_var var vars =
  if var `Set.member` vars then fresh_var (var ++ "'") vars else var