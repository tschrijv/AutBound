module SystemFSubtypingDeBruijnImpl where
import SystemFSubtypingDeBruijnBase
import SystemFSubtypingDeBruijnShow

import Debug.Trace

eval :: Term -> Maybe Value
eval (TmVariable v) = Nothing -- runtime error, bare variable
eval (TmApply f a) = 
  do
    fval <- eval f;
    case fval of
      Abstraction fContent typ -> 
        do {
          val <- eval a; -- eager evaluation
          eval (termTermSubstitute fContent Z (TmValue val))
        }
      TypeAbstraction _ _ -> Nothing -- error, unexpected type expression
eval (TmTypeApply ftrm atyp) = 
  do
    fval <- eval ftrm;
    case fval of
      Abstraction fContent typ -> Nothing -- error, unexpected term expression
      TypeAbstraction absterm superType -> eval (termTypeSubstitute atyp Z absterm)

eval (TmValue v) = Just v



-- by variable index we index the variables, new variables are pushed to the front
data EnvItem = EnvVarValue Type | EnvVarType Type deriving (Eq, Show)
type Env = [EnvItem]

emptyEnv :: Env
emptyEnv = []

getItemFromEnv :: Variable -> Env -> EnvItem
getItemFromEnv Z (item:_) = item
getItemFromEnv (SVarValue v) (EnvVarValue _:rest) = getItemFromEnv v rest
getItemFromEnv (SVarType v) (EnvVarType _:rest) = getItemFromEnv v rest
getItemFromEnv _ _ = error "wrong or no binding for var, or DeBruijn index structure does not match path in term"

getVarValueFromEnv :: Variable -> Env -> Maybe Type
getVarValueFromEnv v env = case getItemFromEnv v env of
  EnvVarValue v -> Just v
  otherwise -> error "requested EnvVarValue but found something else"

getVarTypeFromEnv :: Variable -> Env -> Maybe Type
getVarTypeFromEnv v env = case getItemFromEnv v env of
  EnvVarType v -> Just v
  otherwise -> error "requested EnvVarType but found something else"


shiftEnvItem :: Variable -> EnvItem -> EnvItem
shiftEnvItem v (EnvVarValue t) = EnvVarValue (typeshiftplus v t)
shiftEnvItem v (EnvVarType superType) = EnvVarType (typeshiftplus v superType)

shiftOverVarType :: Type -> Env -> Env
shiftOverVarType superType = map (shiftEnvItem (SVarType Z)) . (EnvVarType superType:)

shiftOverVarValue :: Type -> Env -> Env
shiftOverVarValue t = map (shiftEnvItem (SVarValue Z)) . (EnvVarValue t:)




shiftFuncReturn :: Type -> Type
shiftFuncReturn t = typeshiftminus (SVarValue Z) t

-- onder env+X is typeTerm type T2, 
-- Dan is TypeAbstraction typeTerm onder env type TypUniversal T2

typeofHelper :: Env -> Term -> Maybe Type
typeofHelper env (TmVariable v) = getVarValueFromEnv v env
typeofHelper env (TmValue (Abstraction subTerm inputType)) = 
  do
    outputType <- typeofHelper (shiftOverVarValue inputType env) subTerm;
    Just (TypFunction inputType (shiftFuncReturn outputType))
typeofHelper env (TmValue (TypeAbstraction typeTerm superType)) =
  do
    typeTermType <- typeofHelper (shiftOverVarType superType env) typeTerm;
    Just (TypUniversal typeTermType superType)
typeofHelper env (TmApply func arg) = 
  do
    funcType <- typeofHelper env func;
    argType <- typeofHelper env arg;
    case funcType of
      TypFunction funcInputType funcOutputType -> 
        if funcInputType == argType
          then Just funcOutputType
          else error ("func and arg type mismatch: func=" ++ show funcType ++ ", arg=" ++ show argType)
      otherwise -> error ("Apply expects TypFunction as first arg (was " ++ show funcType ++ ")")

typeofHelper env (TmTypeApply universalFunc typeToSubstitute) = 
  do
    typeOfT1 <- typeofHelper env universalFunc;
    case typeOfT1 of
      TypUniversal typTerm superType -> 
        do
          typIsSubType <- isSubType typeToSubstitute superType env;
          if typIsSubType
          then Just (typeTypeSubstitute typeToSubstitute Z typTerm)
          else error ("Attempting to apply a type to a universal type that does not accept it: universalFunc=" ++ show universalFunc ++ ", typeToSubstitute=" ++ show typeToSubstitute)
      otherwise -> error "type should be universal, since we are doing a type application"

typeof :: Term -> Maybe Type
typeof = typeofHelper []


-- Returns true if the first argument is a subtype of the second
isSubType :: Type -> Type -> Env -> Maybe Bool
isSubType (TypFunction s1 s2) (TypFunction t1 t2) env = -- S-ARROW
  do
    input <- isSubType t1 s1 env;
    output <- isSubType s2 t2 env;
    Just (input && output)
isSubType (TypVariable v) superType env = -- S-TVAR + S-TRANS   v <: vType <: superType => v <: superType
  do
    vType <- getVarTypeFromEnv v env;
    isSubType vType superType env
isSubType (TypUniversal s ua) (TypUniversal t ub) env = -- S-ALL
  if ua == ub
  then isSubType s t (shiftOverVarType ua env)
  else Just False -- For S-ALL, if the supertypes of the Universals are not equal, then one cannot be a subtype of the other
isSubType sub Top env = Just True -- S-TOP
isSubType (Typ "TestSubTyp") (Typ "TestSuperTyp") env = Just True
isSubType sub super env = 
  if sub == super -- S-REFL
  then Just True
  else Just False

