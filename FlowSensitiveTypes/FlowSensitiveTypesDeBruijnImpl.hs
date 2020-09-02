module FlowSensitiveTypesDeBruijnImpl where
import FlowSensitiveTypesDeBruijnBase
import FlowSensitiveTypesDeBruijnShow

import qualified Data.Map


eval :: Term -> Either String Term
eval (TmApply func arg) = case eval func of -- E-AppAbs E-App1 E-App2
  Right (TmAbstraction f) -> case eval arg of
    Right aa -> eval (termTermSubstitute aa Z f)
    Left s -> Left s
  Right other -> Left ("Applying to something that is not an abstraction: func=" ++ show other ++ ", arg=" ++ show arg)
  Left s -> Left s
eval (TmTypeApply tm typ) = case eval tm of -- E-TappTabs E-Tapp
  Right (TmTypeAbstraction t superTyp) -> eval (termTypeSubstitute typ Z t)
  Right other -> Left ("Type applying to something that is not a type abstraction: tm=" ++ show tm ++ ", typ=" ++ show typ)
  Left s -> Left s
eval (TmIf cond thn els) = case eval cond of -- E-If E-IfTrue E-IfFalse
  Right TmTrue -> eval thn
  Right TmFalse -> eval els
  Right other -> Left ("If statement with non-boolean condition: cond=" ++ show cond)
  Left s -> Left s
eval (TmIsEq l r) = case eval l of -- E-EqL E-EqR E-EqTrue E-EqFalse
  Right ll -> case eval r of
    Right rr -> if ll == rr then Right TmTrue else Right TmFalse
    Left s -> Left s
  Left s -> Left s
eval (TmAnd a b) = case eval a of -- E-AndL E-AndR E-AndFalseL E-AndFalseR E-AndTrue
  Right TmFalse -> Right TmFalse
  Right TmTrue -> case eval b of
    Right TmFalse -> Right TmFalse
    Right TmTrue -> Right TmTrue
    Right other -> Left ("right-hand side of && is non-bool: " ++ show other)
    Left s -> Left s
  Right other -> Left ("left-hand side of && is non-bool: " ++ show other)
  Left s -> Left s
eval (TmOr a b) = case eval a of
  Right TmTrue -> Right TmTrue
  Right TmFalse -> case eval b of
    Right TmTrue -> Right TmTrue
    Right TmFalse -> Right TmFalse
    Right other -> Left ("right-hand side of || is non-bool: " ++ show other)
    Left s -> Left s
  Right other -> Left ("left-hand side of || is non-bool: " ++ show other)
  Left s -> Left s


-- by variable index we index the variables, new variables are pushed to the front
data EnvItem = EnvVarValue Type | EnvVarType Type deriving (Eq, Show)
type TypingEnv = [EnvItem]

-- the pair denotes the possibility of cases (False, True)
type InformationEnv = Data.Map.Map Variable (Bool, Bool)

data Env = Env TypingEnv InformationEnv

emptyEnv :: Env
emptyEnv = Env [] Data.Map.empty

getItemFromEnv :: Variable -> TypingEnv -> Either String EnvItem
getItemFromEnv Z (item:_) = Right item
getItemFromEnv (SVarValue v) (EnvVarValue _:rest) = getItemFromEnv v rest
getItemFromEnv (SVarType v) (EnvVarType _:rest) = getItemFromEnv v rest
getItemFromEnv _ _ = Left "wrong or no binding for var, or DeBruijn index structure does not match path in term"

getVarValueFromEnv :: Variable -> Env -> Either String Type
getVarValueFromEnv v (Env typEnv _) = case getItemFromEnv v typEnv of
  Right (EnvVarValue v) -> Right v
  Left s -> Left s
  otherwise -> Left "requested EnvVarValue but found something else"

getVarTypeFromEnv :: Variable -> Env -> Either String Type
getVarTypeFromEnv v (Env typEnv _) = case getItemFromEnv v typEnv of
  Right (EnvVarType v) -> Right v
  Left s -> Left s
  otherwise -> Left "requested EnvVarType but found something else"

containsVarInEnv :: Variable -> TypingEnv -> Either String Bool
containsVarInEnv Z (item:_) = Right True
containsVarInEnv _ [] = Right False
containsVarInEnv (SVarValue v) (EnvVarValue _:rest) = containsVarInEnv v rest
containsVarInEnv (SVarType v) (EnvVarType _:rest) = containsVarInEnv v rest
containsVarInEnv _ _ = Left "containsVar given var and env paths do not match"

containsVar :: Variable -> Env -> Either String Bool
containsVar v (Env typEnv infoEnv) = containsVarInEnv v typEnv

shiftEnvItem :: Variable -> EnvItem -> EnvItem
shiftEnvItem v (EnvVarValue t) = EnvVarValue (typeshiftplus v t)
shiftEnvItem v (EnvVarType superType) = EnvVarType (typeshiftplus v superType)

shiftOverVarType :: Type -> Env -> Env
shiftOverVarType superType (Env typEnv infoEnv) = Env (map (shiftEnvItem (SVarType Z)) ((EnvVarType superType:) typEnv)) infoEnv

shiftOverVarValue :: Type -> Env -> Env
shiftOverVarValue t (Env typEnv infoEnv) = Env (map (shiftEnvItem (SVarValue Z)) ((EnvVarValue t:) typEnv)) infoEnv

shiftFuncReturn :: Type -> Type
shiftFuncReturn t = typeshiftminus (SVarValue Z) t

typesAreEqual :: Env -> Type -> Type -> Either String Bool
typesAreEqual env t1 t2 = do
  case isSubType env t1 t2 of
    Right True -> isSubType env t2 t1
    Right False -> Right False
    Left s -> Left s

errorSafeAnd :: Either String Bool -> Either String Bool -> Either String Bool
errorSafeAnd (Right a) (Right b) = Right (a && b)
errorSafeAnd (Right a) (Left s) = Left s
errorSafeAnd (Left s) _ = Left s

errorSafeOr :: Either String Bool -> Either String Bool -> Either String Bool
errorSafeOr (Right a) (Right b) = Right (a || b)
errorSafeOr (Right a) (Left s) = Left s
errorSafeOr (Left s) _ = Left s

-- Returns true if the first argument is a subtype of the second
isSubType :: Env -> Type -> Type -> Either String Bool
isSubType env sub Top = Right True -- SA-Top
isSubType env TypTrue TypTrue = Right True -- SA-RelfTrue
isSubType env TypFalse TypFalse = Right True -- SA-ReflFalse
isSubType env (TypVariable v1) (TypVariable v2) = -- SA-ReflTVar
  case containsVar v1 env of
    Right b -> Right (v1 == v2 && b)
    Left s -> Left s
isSubType env a@(TypRecord tru1 fls1 select1) b@(TypRecord tru2 fls2 select2) = -- SA-ReflMap
  if (tru1 == tru2 && fls1 == fls2 && select1 == select2)
  then Right True
  else -- Default to SA-TEvalRead
    case typeEval a EvalRead env of
      Right teA -> isSubType env teA b
      Left s -> Left s
isSubType env a@(TypRecord tru fls select) b = -- SA-TEvalRead
  case typeEval a EvalRead env of
    Right teA -> isSubType env teA b
    Left s -> Left s
isSubType env a b@(TypRecord tru fls select) = -- SA-TEvalWrite
  case typeEval b EvalWrite env of
    Right teB -> isSubType env a teB
    Left s -> Left s
isSubType env (TypVariable v) superType = -- SA-TransTVar
  case getVarTypeFromEnv v env of
    Right vType -> isSubType env vType superType
    Left s -> Left s
isSubType env (TypFunction s1 s2) (TypFunction t1 t2) = -- SA-Arrow
  errorSafeAnd (isSubType env t1 s1) (isSubType env s2 t2)
isSubType env (TypUniversal s ua) (TypUniversal t ub) = -- SA-All
  errorSafeAnd (typesAreEqual env ua ub) (isSubType (shiftOverVarType ua env) s t)
    -- For S-ALL, if the supertypes of the Universals are not equal, then one cannot be a subtype of the other
isSubType env (TypUnion l r) t = -- SA-UnionN
  errorSafeAnd (isSubType env l t) (isSubType env r t)
isSubType env t (TypUnion l r) = -- SA-UnionLR
  errorSafeOr (isSubType env t l) (isSubType env t r)

 -- Custom rules for testing
isSubType env (Typ "TestSubTyp") (Typ "TestSuperTyp") = Right True
isSubType env (Typ a) (Typ b) =
  Right (a == b)

isSubType env a b = Right False


-- TODO add new context, the learned information context
-- 


typBool :: Type
typBool = TypUnion TypTrue TypFalse

infersToBool :: Env -> Term -> Either String Bool
infersToBool env t = case inferType env t of
  Right typ -> isSubType env typ typBool
  Left s -> Left s

data EvalMode = EvalRead | EvalWrite deriving(Eq, Show)
typeEval :: Type -> EvalMode -> Env -> Either String Type
typeEval (TypRecord tru fls select) m env = 
  case (typeEval select m env) of -- TE-Map
    Right TypTrue -> typeEval tru m env -- TE-MapTrue
    Right TypFalse -> typeEval fls m env -- TE-MapFalse
    Right (TypUnion l r) -> -- TE-MapUnion
      if m == EvalRead 
      then typeEval (TypUnion (TypRecord tru fls l) (TypRecord tru fls r)) EvalRead env
      else Right (TypRecord tru fls select)
    Right other -> Right other
    Left s -> Left s
typeEval (TypUnion l r) m env = -- TE-Union
  case typeEval l m env of
    Right ll -> case typeEval r m env of
      Right rr -> Right (TypUnion ll rr)
      Left s -> Left s
    Left s -> Left s
typeEval (TypVariable v) EvalRead env = getVarTypeFromEnv v env
typeEval (TypVariable v) EvalWrite env = undefined
typeEval t m env = Right t -- transitive closure, allow applying 0 rules

-- TODO variables?

-- onder env+X is typeTerm type T2, 
-- Dan is TypeAbstraction typeTerm onder env type TypUniversal T2

inferType :: Env -> Term -> Either String Type
inferType env TmTrue = Right TypTrue -- BT-True
inferType env TmFalse = Right TypFalse -- BT-False
inferType env (TmVariable v) = getVarValueFromEnv v env -- BT-Var
--inferType env (TmAbstraction subTerm inputType) =    -- No BT-Abs?
--  let outputType = inferType (shiftOverVarValue inputType env) subTerm in
--    TypFunction inputType (shiftFuncReturn outputType)
inferType env (TmAnnotation term typ) = -- BT-Ann
  case isOfType env term typ of
    Right True -> Right typ
    Right False -> Left ("term: " ++ show term ++ " is not of type " ++ show typ)
    Left s -> Left s
inferType env (TmTypeAbstraction typeTerm superType) = -- BT-TAbs
  case inferType (shiftOverVarType superType env) typeTerm of
    Right typeTermType -> Right (TypUniversal typeTermType superType)
    Left s -> Left s
inferType env (TmApply func arg) = -- BT-App
  case inferType env func of
    Right (TypFunction funcInputType funcOutputType) -> 
      case isOfType env arg funcInputType of
        Right True -> Right funcOutputType
        Right False -> Left ("func and arg type mismatch: func=" ++ show (TypFunction funcInputType funcOutputType) ++ ", arg=" ++ show arg)
        Left s -> Left s
    Right other -> Left ("Apply expects TypFunction as first arg (was " ++ show other ++ ")")
    Left s -> Left s

inferType env (TmTypeApply universalFunc typeToSubstitute) = -- BT-TApp
  case inferType env universalFunc of
    Right (TypUniversal typTerm superType) -> 
      case isSubType env typeToSubstitute superType of
        Right True -> Right (typeTypeSubstitute typeToSubstitute Z typTerm)
        Right False -> Left ("AtRightting to apply a type to a universal type that does not accept it: universalFunc=" ++ show universalFunc ++ ", typeToSubstitute=" ++ show typeToSubstitute)
        Left s -> Left s
    Right other -> Left "type should be universal, since we are doing a type application"
    Left s -> Left s

inferType env (TmIsEq t1 t2) = -- BT-Eq
  case inferType env t1 of
    Right r1 -> case inferType env t2 of
      Right r2 -> Right typBool
      Left s -> Left s
    Left s -> Left s

inferType env (TmAnd t1 t2) = -- BT-And
  case errorSafeAnd (infersToBool env t1) (infersToBool env t2) of
    Right True -> Right typBool
    Right False -> Left ("Non-Bool args to &&: (" ++ show t1 ++ ") && (" ++ show t2 ++ ")")
    Left s -> Left s

inferType env (TmOr t1 t2) = -- BT-Or
  case errorSafeAnd (infersToBool env t1) (infersToBool env t2) of
    Right True -> Right typBool
    Right False -> Left ("Non-Bool args to ||: (" ++ show t1 ++ ") || (" ++ show t2 ++ ")")
    Left s -> Left s

inferType env (TmIf cond thn els) = -- BT-If
  case isOfType env cond typBool of
    Right True -> let infoOfCond = informationOf env cond in
      case inferType (addInfoToEnv env infoOfCond) thn of
        Right thnTyp -> case inferType (addInfoToEnv env (invert infoOfCond)) els of
          Right elsTyp -> Right (TypUnion thnTyp elsTyp)
          Left s -> Left s
        Left s -> Left s
    Right False -> Left "Condition is not of type Bool!"
    Left s -> Left s

inferType env (TmAbstraction _) = 
  Left "inferType of Abstractions is not supported"

-- others not defined


typeof :: Term -> Either String Type
typeof = inferType emptyEnv


isOfType :: Env -> Term -> Type -> Either String Bool
isOfType env (TmAbstraction tm) funcTyp = -- BT-Abs
  case funcTyp of
    TypFunction from to -> 
      let envInAbstraction = shiftOverVarValue from env in
        isOfType envInAbstraction tm to
    otherwise -> Left ("isOfType of an abstraction must atRightt to check with a function type! Actual type: " ++ show funcTyp)

isOfType env term typ = -- BT-Sub
  case inferType env term of
    Right typOfTerm -> isSubType env typOfTerm typ
    Left s -> Left s


informationOf :: Env -> Term -> InformationEnv
informationOf env TmTrue = Data.Map.empty -- CI-True
informationOf env TmFalse = Data.Map.empty -- CI-False
informationOf env (TmIsEq (TmVariable v) TmTrue) = Data.Map.insert v (False, True) Data.Map.empty -- CI-EqTrueR
informationOf env (TmIsEq TmTrue (TmVariable v)) = Data.Map.insert v (False, True) Data.Map.empty -- CI-EqTrueL
informationOf env (TmIsEq (TmVariable v) TmFalse) = Data.Map.insert v (True, False) Data.Map.empty -- CI-EqFalseR
informationOf env (TmIsEq TmFalse (TmVariable v)) = Data.Map.insert v (True, False) Data.Map.empty -- CI-EqFalseL
informationOf env (TmAnd t1 t2) = intersect (informationOf env t1) (informationOf env t2) -- CI-EqAnd
informationOf env _ = Data.Map.empty -- CI-EqOtherwise


intersect :: InformationEnv -> InformationEnv -> InformationEnv
intersect = Data.Map.unionWith combine where -- CO-Intersect
  combine :: (Bool, Bool) -> (Bool, Bool) -> (Bool, Bool)
  combine (f1, t1) (f2, t2) = (f1 && f2, t1 && t2)

addInfoToEnv :: Env -> InformationEnv -> Env
addInfoToEnv (Env typEnv infoEnv) newInfo = Env typEnv (intersect infoEnv newInfo)

invert :: InformationEnv -> InformationEnv
invert = Data.Map.map inv where -- CO-Union?
  inv :: (Bool, Bool) -> (Bool, Bool)
  inv (f, t) = (not f, not t)

