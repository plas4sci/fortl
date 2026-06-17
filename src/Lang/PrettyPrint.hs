{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Lang.PrettyPrint where

import Lang.Syntax

-- Pretty print terms
class PrettyPrint t where
    isLexicallyAtomic :: t -> Bool
    isLexicallyAtomic _ = False

    pprint :: t -> String

bracket_pprint :: PrettyPrint t => t -> String
bracket_pprint t | isLexicallyAtomic t = pprint t
                 | otherwise           = "(" ++ pprint t ++ ")"

-- Untyped lambda calculus
instance PrettyPrint Expr where
    isLexicallyAtomic (Var _) = True
    isLexicallyAtomic (NumFloat _) = True
    isLexicallyAtomic _       = False

    pprint (Abs var Nothing e)  = "lambda " ++ var ++ ": " ++ pprint e
    pprint (Abs var (Just t) e) = "lambda (" ++ var ++ " : " ++ pprint t ++ "): " ++ pprint e
    pprint (App (Abs var mt e1) e2) =
      bracket_pprint (Abs var mt e1) ++ " " ++ bracket_pprint e2
    pprint (App (Sig e1 t) e2) =
      bracket_pprint (Sig e1 t) ++ " " ++ bracket_pprint e2
    pprint (App e1 e2) = pprint e1 ++ " " ++ bracket_pprint e2
    pprint (Var var) = var
    pprint (Sig e t) = bracket_pprint e ++ " : " ++ pprint t
    pprint (Cast t)  = "cast " ++ pprint t
    -- Poly
    pprint (TyAbs var e) = "/\\" ++ var ++ " -> " ++ pprint e
    pprint (TyEmbed t) = "@" ++ bracket_pprint t
    -- ML
    pprint (GenLet x e1 e2) = "let " ++ x ++ " = " ++ pprint e1 ++ " in " ++ pprint e2
    -- PCF expressions
    pprint Zero                   = "zero"
    pprint Succ                   = "succ"
    pprint (Fix e)                = "fix " ++ bracket_pprint e
    pprint (NatCase e e1 (x,e2))  =
      "natcase " ++ bracket_pprint e ++ " of zero => " ++
      bracket_pprint e1 ++ " | succ " ++ x ++ " => " ++ bracket_pprint e2
    pprint (Pair e1 e2)           = "(" ++ pprint e1 ++ ", " ++ pprint e2 ++ ")"
    pprint (Fst e)                = "fst " ++ bracket_pprint e
    pprint (Snd e)                = "snd " ++ bracket_pprint e
    pprint (Inl e)                = "inl " ++ bracket_pprint e
    pprint (Inr e)                = "inr " ++ bracket_pprint e
    pprint (Case e (x,e1) (y,e2)) =
      "case " ++ bracket_pprint e ++ " of inl " ++ x ++ " => " ++
      bracket_pprint e1 ++ " | inr " ++ y ++ " => " ++ bracket_pprint e2
    pprint (BinOp op e1 e2) =
      let arg1 = bracket_pprint e1
          arg2 = bracket_pprint e2
          operator = pprint op
      in
        arg1 <> operator <> arg2
    pprint (NumFloat f) = show f
    pprint (NumInteger n) = show n
    pprint (Con c []) = c
    pprint (Con c es) =
      c ++ "(" ++ concat (map (\e -> pprint e ++ ", ") es) ++ ")"

instance PrettyPrint Op where
  pprint op =
    case op of
      OpExp -> "^"
      OpPlus -> "+"
      OpMinus -> "-"
      OpTimes -> "*"
      OpDivide -> "/"

instance PrettyPrint () where
    pprint () = "()"

instance PrettyPrint (Type i) where
    isLexicallyAtomic (TyCon _ _) = True
    isLexicallyAtomic (TyVar _) = True
    isLexicallyAtomic (TyApp _ _) = True
    isLexicallyAtomic (ExponentTy _ _) = True
    isLexicallyAtomic _     = False

    pprint (TyCon _ c) = c
    pprint (ImplicitFunTy var tyA tyB) =
      "{" ++ var ++ " : " ++ pprint tyA ++ "} -> " ++ pprint tyB
    pprint (FunTy tyA tyB) =
      bracket_pprint tyA ++ " -> " ++ pprint tyB
    pprint (ProdTy tyA tyB) =
      bracket_pprint tyA ++ " * " ++ bracket_pprint tyB
    pprint (SumTy tyA tyB) =
      bracket_pprint tyA ++ " + " ++ bracket_pprint tyB
    pprint (TyApp tyA tyB) =
      pprint tyA ++ "[" ++ bracket_pprint tyB ++ "]"
    pprint (ImplicitTyApp tyA tyB) =
      bracket_pprint tyA ++ "[{" ++ bracket_pprint tyB ++ "}]"
    pprint (TyVar var) = var
    pprint (Forall var t) = "forall " ++ var ++ " . " ++ pprint t
    pprint (WithTy t1 t2) =
      bracket_pprint t1 ++ " & " ++ bracket_pprint t2
    pprint (ExponentTy t1 1) =
      bracket_pprint t1
    pprint (ExponentTy t1 q) =
      bracket_pprint t1 ++ "^" ++ show q