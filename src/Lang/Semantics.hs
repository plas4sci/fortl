{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Semantics where

import Lang.Syntax
import Lang.Options
import Lang.Substitution
import Lang.Primitives (dataConstructors)
import qualified Data.Map.Lazy as Map
-- import Debug.Trace

data Env = Env
    { vars :: Map.Map Identifier Expr
    , funs :: Map.Map Identifier (Def 'Desugared)
    }

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty

-- Evaluate a program to normal form
interpret :: [Option] -> Program 'Desugared -> (Env, Expr)
interpret = interpretDefs emptyEnv

-- Interpret the definitions, including building an environment
-- for the rest of the program
interpretDefs :: Env -> [Option] -> Program 'Desugared -> (Env, Expr)

interpretDefs env opts ((ValDef (VarLhs id _) e):defs) = 
  case bigStep env opts e of
    Right v -> interpretDefs (env { vars = Map.insert id v (vars env) }) opts defs
    Left err -> error err

interpretDefs env opts ((FunDefElaborated id params body):defs) =
  interpretDefs (env { funs = Map.insert id (FunDefElaborated id params body) (funs env) }) opts defs

-- Return expression
interpretDefs env opts ((Return e):defs) = 
  case bigStep env opts e of
    Right v -> (env, v)
    Left err -> error err

interpretDefs env opts (_:defs ) = interpretDefs env opts defs

interpretDefs env opts [] = 
  -- No definition
  -- return the expression fro the last binder if there is one
  case Map.lookup "it" (vars env) of
    Just v  -> (env, v)
    Nothing -> (env, Con "None" [])

-- Big step operational model (i.e., expression interpreter)
bigStep :: Env -> [Option] -> Expr -> Either String Expr
-- Special-cased primitive: sqrt
bigStep env opts (App (Var "sqrt") [e2]) =
  case bigStep env opts e2 of
    Right (NumFloat n) -> return $ NumFloat $ sqrt n
    Right _            -> Left "sqrt expects a number"
    Left err           -> Left err
bigStep env opts (App (Var f) es)
  | Just (FunDefElaborated _ params body) <- Map.lookup f (funs env) =
      if length params /= length es
        then Left "Function application has the wrong number of arguments"
        else do
          vs <- mapM (bigStep env opts) es
          let callVars = foldr (\(x, v) m -> Map.insert x v m) (vars env) (zip (map fst params) vs)
          Right (snd (interpretDefs (env { vars = callVars }) opts body))
bigStep env opts (App e1 es) =
  case bigStep env opts e1 of
    Left err -> Left err
    Right (Abs params body)
      -- full or partial (curried) application
      | length es <= length params -> do
          let (paramsHere, paramsRest) = splitAt (length es) params
          vs <- mapM (bigStep env opts) es
          let body' = foldl (\current (x, v) -> substitute current (x, v)) body (zip (map fst paramsHere) vs)
          if null paramsRest
            then bigStep env opts body'
            else Right (Abs paramsRest body')
      -- over-application: apply the arguments this function takes, then
      -- continue applying the rest to the resulting value
      | otherwise -> do
          let (esHere, esRest) = splitAt (length params) es
          vs <- mapM (bigStep env opts) esHere
          v <- bigStep env opts (foldl (\current (x, v) -> substitute current (x, v)) body (zip (map fst params) vs))
          bigStep env opts (App v esRest)
    Right (TyAbs var body) ->
      case es of
        [e2] ->
          case bigStep env opts e2 of
            Left err -> Left err
            Right (TyEmbed t) -> bigStep env opts (substitute body (var, TyEmbed t))
            Right _ -> Left "Type application expects a type"
        _ -> Left "Type application expects one type"
    Right _ -> Left "Application expects a function"
bigStep env opts (Sig e _) = bigStep env opts e
bigStep env opts (Cast e) = bigStep env opts e
bigStep env opts (Var x) = case Map.lookup x (vars env) of
  Just v  -> Right v
  Nothing ->
    case lookup x dataConstructors of
      Just _  -> Right (Con x [])
      Nothing -> Left $ "Unbound variable: " ++ x
bigStep env opts (Let x e1 e2) = do
  v1 <- bigStep env opts e1
  bigStep (env { vars = Map.insert x v1 (vars env) }) opts e2

bigStep env opts (Case eg branchl branchr) = do
  error "Not implemented yet"
--   v <- bigStep env opts eg
--   case v of
--     Inl e1 -> bigStep ((fst branchl, e1) : env) opts (snd branchl)
--     Inr e2 -> bigStep ((fst branchr, e2) : env) opts (snd branchr)
--     _      -> Left "case expects a sum type"

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
    (Con b1 [], Con b2 []) ->
      case op of
        BinOpAnd -> 
          case (b1, b2) of
            ("True", "True")   -> return $ Con "True" []
            ("True", "False")  -> return $ Con "False" []
            ("False", "True")  -> return $ Con "False" []
            ("False", "False") -> return $ Con "False" []
            _ -> Left "Logical AND operation expects two booleans"
        BinOpOr  -> 
          case (b1, b2) of
            ("True", "True")   -> return $ Con "True" []
            ("True", "False")  -> return $ Con "True" []
            ("False", "True")  -> return $ Con "True" []
            ("False", "False") -> return $ Con "False" []
            _ -> Left "Logical OR operation expects two booleans"
        _ -> Left "Binary operation undefined for given inputs"
    _ -> Left "Error in binary operation evaluation"
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
    (Con b []) ->
      case op of
        UnOpNot -> 
          case b of
            "True" -> return $ Con "False" []
            "False" -> return $ Con "True" []
            _ -> Left "Logical NOT operation expects a boolean"
        UnOpNegate -> Left "Negation is not defined for booleans"
    _ -> Left "Error in unary operation evaluation"
bigStep env opts (Cond e1 e2 e3) = do
  v2 <- bigStep env opts e2
  case v2 of
    Con "True" []  -> bigStep env opts e1
    Con "False" [] -> bigStep env opts e3
    _              -> Left "Condition expects a boolean"

-- Values
bigStep env opts (TyEmbed e) = Right $ TyEmbed e -- TODO: remove this
bigStep env opts (TyAbs x e) = Right $ TyAbs x e
bigStep env opts (NumFloat f) = Right $ NumFloat f
bigStep env opts (NumInteger n) = Right $ NumInteger n
bigStep env opts (StringConst s) = Right $ StringConst s
bigStep env opts Succ = Right Succ
bigStep env opts Zero = Right Zero
bigStep env opts (Abs params body) = Right $ Abs params body
bigStep env opts (Con c es) = do
  vs <- mapM (bigStep env opts) es
  return $ Con c vs
