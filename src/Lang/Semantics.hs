{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Lang.Semantics where

import Lang.Syntax
import Lang.Options
import Lang.Substitution
import Lang.PrettyPrint
import Lang.Primitives (dataConstructors)
import qualified Data.Map.Lazy as Map
-- import Debug.Trace

-- **************************************
-- ** Evaluation context and values
-- ***************************************

-- Result of evaluating is a value which is either a (normal form) expression
-- or a function closure
data Value =
    VClosure { closureParams :: [Identifier], closureBody :: [Def 'Desugared], closureEnv :: Env }
  | ValExpr Expr

instance PrettyPrint Value where
  pprint (ValExpr e) = pprint e
  pprint (VClosure params _ _) = "<function/" ++ show (length params) ++ ">"

-- | Project a normal-form expression out of a value
-- (closures have no expression form)
valueToExpr :: Value -> Either String Expr
valueToExpr (ValExpr e) = Right e
valueToExpr VClosure{}  = Left "Cannot use a function value here"

-- Environment
data Env = Env
    { bindings :: Map.Map Identifier Value
    , parent   :: Maybe Env
    }

-- Empty env (at top of lexical scope)
emptyEnv :: Env
emptyEnv = Env Map.empty Nothing

-- Add binding in the current frame
bindHere :: Identifier -> Value -> Env -> Env
bindHere id val (Env bindings parent) =
  Env (Map.insert id val bindings) parent

lookupBinding :: Identifier -> Env -> Either String Value
lookupBinding name env =
  case Map.lookup name (bindings env) of
    Just value -> Right value
    Nothing ->
      case parent env of
        Just outer -> lookupBinding name outer
        Nothing    -> Left $ "Unbound variable: " ++ name

-- **************************************
-- ** Interpreter for definitions
-- ***************************************

-- Evaluate a program to normal form
interpret :: [Option] -> Program 'Desugared -> (Env, Value)
interpret = interpretDefs emptyEnv

-- Interpret the definitions, including building an environment
-- for the rest of the program
interpretDefs :: Env -> [Option] -> Program 'Desugared -> (Env, Value)

interpretDefs env opts ((ValDef (VarLhs id _) e):defs) =
  case bigStep env opts e of
    Right v -> interpretDefs (bindHere id v env) opts defs
    Left err -> error err

interpretDefs env opts ((FunDefElaborated id params body):defs) =
  -- Make a closure capturing the environment and proceed
  let env' = bindHere id (VClosure (map fst params) body env) env
  in interpretDefs env' opts defs

-- Return expression
interpretDefs env opts ((Return e):defs) =
  case bigStep env opts e of
    Right v -> (env, v)
    Left err -> error err

-- TODO: work out what handling we need here
interpretDefs env opts (TypeDef{}:defs)   = interpretDefs env opts defs
interpretDefs env opts (DataDef{}:defs)   = interpretDefs env opts defs
interpretDefs env opts (ImportDef{}:defs) = interpretDefs env opts defs

interpretDefs env opts [] =
  -- No definition
  -- return the expression for the last binder if there is one
  case lookupBinding "it" env of
    Right v  -> (env, v)
    Left _   -> (env, ValExpr (Con "None" []))

-- **************************************
-- ** Interpreter for expressions
-- ***************************************

bigStep :: Env -> [Option] -> Expr -> Either String Value

-- Special-cased primitive: sqrt
bigStep env opts (App (Var "sqrt") [e2]) =
  case bigStep env opts e2 of
    Right (ValExpr (NumFloat n)) ->
      return $ ValExpr $ NumFloat $ sqrt n
    Right _            -> Left "sqrt expects a number"
    Left err           -> Left err

bigStep env opts (App e1 es) = do
  v1 <- bigStep env opts e1
  apply v1 es
  where
    -- local loop: a Value cannot be wrapped back into an App node, and
    -- over-application must re-apply the resulting value to the leftover args
    apply (VClosure params body capturedEnv) es
      -- full or partial (curried) application
      | length es <= length params = do
          let (paramsHere, paramsRest) = splitAt (length es) params
          -- Evaluate the arguments
          vs <- mapM (bigStep env opts) es
          let env' = Env { bindings = Map.fromList (zip paramsHere vs), parent = Just capturedEnv }
          if null paramsRest
            then Right $ snd $ interpretDefs env' opts body
            else Right $ VClosure paramsRest body env'
      -- over-application: apply the arguments this closure takes, then apply
      -- the resulting value to the rest
      | otherwise = do
          let (esHere, esRest) = splitAt (length params) es
          vs <- mapM (bigStep env opts) esHere
          let env' = Env { bindings = Map.fromList (zip params vs), parent = Just capturedEnv }
          apply (snd (interpretDefs env' opts body)) esRest

    -- Type abstraction: uses a substitution (rather than environment) to avoid
    -- having to carry around type environments
    apply (ValExpr (TyAbs var body)) es =
      case es of
        [e2] -> do
          v2 <- bigStep env opts e2
          case v2 of
            ValExpr (TyEmbed t) -> bigStep env opts (substitute body (var, TyEmbed t))
            _ -> Left "Type application expects a type"
        _ -> Left "Type application expects one type"

    apply _ _ = Left "Application expects a function"

bigStep env opts (Sig e _) = bigStep env opts e
bigStep env opts (Cast e) = bigStep env opts e
bigStep env opts (Var x) =
  case lookupBinding x env of
    Right v  -> Right v
    Left _   ->
      -- If the variable is not bound, check if it is a data constructor
      -- If so, return the constructor with no arguments
      case lookup x dataConstructors of
        Just _  -> Right (ValExpr (Con x []))
        Nothing -> Left $ "Unbound variable: " ++ x


bigStep env opts (Let x e1 e2) = do
  v1 <- bigStep env opts e1
  bigStep (bindHere x v1 env) opts e2

bigStep env opts (Case eg branchl branchr) = do
  error "Not implemented yet"
--   v <- bigStep env opts eg
--   case v of
--     Inl e1 -> bigStep ((fst branchl, e1) : env) opts (snd branchl)
--     Inr e2 -> bigStep ((fst branchr, e2) : env) opts (snd branchr)
--     _      -> Left "case expects a sum type"

bigStep env opts (Fst e) = do
  v <- bigStep env opts e
  case v of
    -- pair components are already in normal form
    ValExpr (Pair e1 _) -> Right $ ValExpr e1
    _         -> Left "fst expects a pair"
bigStep env opts (Snd e) = do
  v <- bigStep env opts e
  case v of
    ValExpr (Pair _ e2) -> Right $ ValExpr e2
    _         -> Left "snd expects a pair"
bigStep env opts (Pair e1 e2) = do
  v1 <- bigStep env opts e1 >>= valueToExpr
  v2 <- bigStep env opts e2 >>= valueToExpr
  return $ ValExpr $ Pair v1 v2
bigStep env opts (Lift e _) = bigStep env opts e
bigStep env opts (BinOp op e1 e2) = do
  v1 <- bigStep env opts e1 >>= valueToExpr
  v2 <- bigStep env opts e2 >>= valueToExpr
  ValExpr <$> case (v1, v2) of
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
  v <- bigStep env opts e >>= valueToExpr
  ValExpr <$> case v of
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
    ValExpr (Con "True" [])  -> bigStep env opts e1
    ValExpr (Con "False" []) -> bigStep env opts e3
    _              -> Left "Condition expects a boolean"

-- Values
bigStep env opts (TyEmbed e) = Right $ ValExpr $ TyEmbed e -- TODO: remove this
bigStep env opts (TyAbs x e) = Right $ ValExpr $ TyAbs x e
bigStep env opts (NumFloat f) = Right $ ValExpr $ NumFloat f
bigStep env opts (NumInteger n) = Right $ ValExpr $ NumInteger n
bigStep env opts (StringConst s) = Right $ ValExpr $ StringConst s
bigStep env opts Succ = Right $ ValExpr Succ
bigStep env opts Zero = Right $ ValExpr Zero
-- A lambda closes over its environment; its body becomes a single-return block
bigStep env opts (Abs params body) = Right $ VClosure (map fst params) [Return body] env
bigStep env opts (Con c es) = do
  vs <- mapM (\e -> bigStep env opts e >>= valueToExpr) es
  return $ ValExpr $ Con c vs
