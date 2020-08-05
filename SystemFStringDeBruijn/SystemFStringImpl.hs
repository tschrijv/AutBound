module SystemFStringImpl where
import SystemFStringBase
import SystemFStringShow

import Debug.Trace
import qualified Data.Map as Map

eval :: Term -> Maybe Value
eval (TmVariable v) = Nothing -- runtime error, bare variable
eval (TmApply f a) = 
  do {
    fval <- eval f;
    case fval of
      Abstraction var fContent typ -> 
        do {
          val <- eval a; -- eager evaluation
          eval (termTermSubstitute var fContent (TmValue val))
        }
      TypeAbstraction tvar _ -> Nothing -- error, unexpected type expression
  }
eval (TmTypeApply ftrm atyp) = 
  do {
    fval <- eval ftrm;
    case fval of
      Abstraction var fContent typ -> Nothing -- error, unexpected term expression
      TypeAbstraction var absterm -> eval (termTypeSubstitute var atyp absterm)
  }
eval (TmValue v) = Just v



-- by variable index we index the variables, new variables are pushed to the front
type Env = Map.Map String Type

getVarFromEnv :: Variable -> Env -> Maybe Type
getVarFromEnv (SVarValue svv) = Map.lookup svv
getVarFromEnv (SVarType svt) = error "looking up typevar"

addVarToEnv :: Variable -> Type -> Env -> Env
addVarToEnv (SVarValue svv) typ = Map.insert svv typ -- replacement ensures that inner variables hide outer variables with the same name
addVarToEnv (SVarType svt) typ = error "inserting typevar"

-- onder env+X is typeTerm type T2, 
-- Dan is TypeAbstraction typeTerm onder env type TypUniversal T2

typeofHelper :: Env -> Term -> Maybe Type
typeofHelper env (TmVariable v) = getVarFromEnv v env
typeofHelper env (TmValue (Abstraction var subTerm inputType)) = 
  do
    outputType <- typeofHelper (addVarToEnv var inputType env) subTerm;
    Just (TypFunction inputType outputType)
  
typeofHelper env (TmValue (TypeAbstraction var typeTerm)) = 
  do
    typeTermType <- typeofHelper env typeTerm; -- env is kept, nothing needs to be done as there is no extra information for the typevars
    Just (TypUniversal var typeTermType)
  
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
      TypUniversal varName typTerm -> Just (typeTypeSubstitute varName templateArg typTerm)
      otherwise -> error "type should be universal, since we are doing a type application"

typeof :: Term -> Maybe Type
typeof = typeofHelper Map.empty
