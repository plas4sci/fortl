{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Semantics where

import Lang.Syntax
import Lang.Options
import Lang.Substitution
import Lang.Primitives (dataConstructors)
-- import Debug.Trace

type Env = [(Identifier, Expr)]

-- Evaluate a program to normal form
interpret :: [Option] -> Program 'Desugared -> (Env, Expr)
interpret = interpretDefs []

-- Interpret the definitions, including building an environment
-- for the rest of the program
interpretDefs :: Env -> [Option] -> Program 'Desugared -> (Env, Expr)

interpretDefs env opts ((ValDef (VarLhs id _) e):defs) = 
  case bigStep env opts e of
    Right v -> interpretDefs ((id, v) : env) opts defs
    Left err -> error err

-- Return expression
interpretDefs env opts ((Return e):defs) = 
  case bigStep env opts e of
    Right v -> (env, v)
    Left err -> error err

interpretDefs env opts (_:defs ) = interpretDefs env opts defs

interpretDefs env opts [] = 
  -- No definition
  -- return the expression fro the last binder if there is one
  case lookup "it" env of
    Just v  -> (env, v)
    Nothing -> (env, Con "None" [])

-- Big step operational model (i.e., expression interpreter)
bigStep :: Env -> [Option] -> Expr -> Either String Expr
bigStep env opts (App e1 e2) =
  case bigStep env opts e1 of
    Left err -> Left err
    Right (Abs x _ body) ->
      case bigStep env opts e2 of
        Left err -> Left err
        Right v2 -> bigStep env opts (substitute body (x, v2))
    Right (TyAbs var body) ->
      case bigStep env opts e2 of
        Left err -> Left err
        Right (TyEmbed t) -> bigStep env opts (substitute body (var, TyEmbed t))
        Right _ -> Left "Type application expects a type"
    Right _ -> Left "Application expects a function"
bigStep env opts (Sig e _) = bigStep env opts e
bigStep env opts (Cast e) = bigStep env opts e
bigStep env opts (Var x) = case lookup x env of
  Just v  -> Right v
  Nothing ->
    case lookup x dataConstructors of
      Just _  -> Right (Con x [])
      Nothing -> Left $ "Unbound variable: " ++ x
bigStep env opts (GenLet x e1 e2) = do
  v1 <- bigStep env opts e1
  bigStep ((x, v1) : env) opts e2

bigStep env opts (NatCase eg ez (bind, es)) =
  case bigStep env opts eg of
    Left err -> Left err
    Right Zero -> bigStep env opts ez
    Right (App Succ n) -> bigStep ((bind, n):env) opts es
    Right _ -> Left "natcase expects a natural number"
bigStep env opts (Fix e) =
  case bigStep env opts e of
    Left err -> Left err
    Right (Abs x _ body) -> bigStep ((x, Fix (Abs x Nothing body)) : env) opts e
    Right _ -> Left "fix expects a function"
bigStep env opts (Case eg branchl branchr) = do
  v <- bigStep env opts eg
  case v of
    Inl e1 -> bigStep ((fst branchl, e1) : env) opts (snd branchl)
    Inr e2 -> bigStep ((fst branchr, e2) : env) opts (snd branchr)
    _      -> Left "case expects a sum type"
bigStep env opts (Fst e) =
  case bigStep env opts e of
    Right (Pair e1 _) -> bigStep env opts e1
    _         -> Left "fst expects a pair"
bigStep env opts (Snd e) =
  case bigStep env opts e of
    Right (Pair _ e2) -> bigStep env opts e2
    _         -> Left "snd expects a pair"
bigStep env opts (Pair e1 e2) = do
  v1 <- bigStep env opts e1
  v2 <- bigStep env opts e2
  return $ Pair v1 v2
bigStep env opts (Inl e) = Inl <$> bigStep env opts e
bigStep env opts (Inr e) = Inr <$> bigStep env opts e
bigStep env opts (Lift e _) = bigStep env opts e
bigStep env opts (BinOp op e1 e2) = do
  v1 <- bigStep env opts e1
  v2 <- bigStep env opts e2
  case (v1, v2) of
    (NumFloat n1, NumFloat n2) ->
      case op of
        BinOpExp    -> return $ NumFloat $ n1 ** n2
        BinOpPlus   -> return $ NumFloat $ n1 + n2
        BinOpTimes  -> return $ NumFloat $ n1 * n2
        BinOpMinus  -> return $ NumFloat $ n1 - n2
        BinOpDivide -> if n2 /= 0
                      then return $ NumFloat $ n1 / n2
                      else Left "Division by zero"
        BinOpAnd    -> Left "Logical AND is not defined for floats"
        BinOpOr     -> Left "Logical OR is not defined for floats"
    (NumInteger n1, NumInteger n2) ->
      case op of
        BinOpExp    -> return $ NumInteger $ floor $ ((fromInteger n1 ** fromInteger n2) :: Float)
        BinOpPlus   -> return $ NumInteger $ n1 + n2
        BinOpTimes  -> return $ NumInteger $ n1 * n2
        BinOpMinus  -> return $ NumInteger $ n1 - n2
        BinOpDivide -> if n2 /= 0
                      then return $ NumInteger $ n1 `div` n2
                      else Left "Division by zero"
        BinOpAnd    -> Left "Logical AND is not defined for integers"
        BinOpOr     -> Left "Logical OR is not defined for integers"
    (BoolConst b1, BoolConst b2) ->
      case op of
        BinOpAnd -> return $ BoolConst $ b1 && b2
        BinOpOr  -> return $ BoolConst $ b1 || b2
        _        -> Left "Binary operation expects two booleans"
    _ -> Left "Binary operation expects two numbers"
bigStep env opts (UnOp op e) = do
  v <- bigStep env opts e
  case v of
    (NumFloat n) ->
      case op of
        UnOpNegate -> return $ NumFloat $ -n
        UnOpNot    -> Left "Logical NOT is not defined for floats"
    (NumInteger n) ->
      case op of
        UnOpNegate -> return $ NumInteger $ -n
        UnOpNot    -> Left "Logical NOT is not defined for integers"
    (BoolConst b) ->
      case op of
        UnOpNot -> return $ BoolConst $ not b
        UnOpNegate -> Left "Negation is not defined for booleans"
    _ -> Left "Unary operation expects a number"
bigStep env opts (Cond e1 e2 e3) = do
  v2 <- bigStep env opts e2
  case v2 of
    BoolConst True  -> bigStep env opts e1
    BoolConst False -> bigStep env opts e3
    _               -> Left "Condition expects a boolean"

-- Values
bigStep env opts (TyEmbed e) = Right $ TyEmbed e -- TODO: remove this
bigStep env opts (TyAbs x e) = Right $ TyAbs x e
bigStep env opts (NumFloat f) = Right $ NumFloat f
bigStep env opts (NumInteger n) = Right $ NumInteger n
bigStep env opts (StringConst s) = Right $ StringConst s
bigStep env opts (BoolConst b) = Right $ BoolConst b
bigStep env opts Succ = Right Succ
bigStep env opts Zero = Right Zero
bigStep env opts (Abs x mt body) = Right $ Abs x mt body
bigStep env opts (Con c es) = do
  vs <- mapM (bigStep env opts) es
  return $ Con c vs
