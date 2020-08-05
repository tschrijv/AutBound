module SystemFDeBruijnImpl where
import SystemFDeBruijnBase
import SystemFDeBruijnShow

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
      TypeAbstraction _ -> Nothing -- error, unexpected type expression
eval (TmTypeApply ftrm atyp) = 
  do
    fval <- eval ftrm;
    case fval of
      Abstraction fContent typ -> Nothing -- error, unexpected term expression
      TypeAbstraction absterm -> eval (termTypeSubstitute atyp Z absterm)

eval (TmValue v) = Just v



-- by variable index we index the variables, new variables are pushed to the front
data EnvItem = EnvVarValue Type | EnvVarType deriving (Eq, Show)
type Env = [EnvItem]

getVarFromEnv :: Variable -> Env -> Maybe Type
getVarFromEnv Z (EnvVarValue typ:_) = Just typ
getVarFromEnv (SVarValue v) (EnvVarValue _:rest) = getVarFromEnv v rest
getVarFromEnv (SVarType v) (EnvVarType:rest) = getVarFromEnv v rest
getVarFromEnv _ _ = error "wrong or no binding for var"

shiftEnvItem :: Variable -> EnvItem -> EnvItem
shiftEnvItem v (EnvVarValue t) = EnvVarValue (typeshiftplus v t)
shiftEnvItem v (EnvVarType) = EnvVarType

shiftEnvOverTypeAbs :: Env -> Env
shiftEnvOverTypeAbs = map (shiftEnvItem (SVarType Z)) . (EnvVarType:)

shiftEnvOverAbs :: Type -> Env -> Env
shiftEnvOverAbs t = map (shiftEnvItem (SVarValue Z)) . (EnvVarValue t:)

shiftFuncReturn :: Type -> Type
shiftFuncReturn t = typeshiftminus (SVarValue Z) t

-- onder env+X is typeTerm type T2, 
-- Dan is TypeAbstraction typeTerm onder env type TypUniversal T2

typeofHelper :: Env -> Term -> Maybe Type
typeofHelper env (TmVariable v) = getVarFromEnv v env
typeofHelper env (TmValue (Abstraction subTerm inputType)) = 
  do
    outputType <- typeofHelper (shiftEnvOverAbs inputType env) subTerm;
    Just (TypFunction inputType (shiftFuncReturn outputType))
typeofHelper env (TmValue (TypeAbstraction typeTerm)) =
  do
    typeTermType <- typeofHelper (shiftEnvOverTypeAbs env) typeTerm;
    Just (TypUniversal typeTermType)
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

typeofHelper env (TmTypeApply templateFunc templateArg) = 
  do
    typeOfT1 <- typeofHelper env templateFunc;
    case typeOfT1 of
      TypUniversal typTerm -> Just (typeTypeSubstitute templateArg Z typTerm)
      otherwise -> error "type should be universal, since we are doing a type application"

typeof :: Term -> Maybe Type
typeof = typeofHelper []
