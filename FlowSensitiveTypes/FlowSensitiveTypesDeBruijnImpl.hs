module FlowSensitiveTypesDeBruijnImpl where
import FlowSensitiveTypesDeBruijnBase
import FlowSensitiveTypesDeBruijnShow

import qualified Data.Map
import Debug.Trace

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

emptyTypEnv :: TypingEnv
emptyTypEnv = []
emptyInfoEnv :: InformationEnv
emptyInfoEnv = Data.Map.empty

emptyEnv :: Env
emptyEnv = Env emptyTypEnv emptyInfoEnv

getItemFromEnv :: Variable -> TypingEnv -> Either String EnvItem
getItemFromEnv Z (item:_) = Right item
getItemFromEnv (SVarValue v) (EnvVarValue _:rest) = getItemFromEnv v rest
getItemFromEnv (SVarType v) (EnvVarType _:rest) = getItemFromEnv v rest
getItemFromEnv _ _ = Left "wrong or no binding for var, or DeBruijn index structure does not match path in term"

getVarValueFromEnv :: Variable -> Env -> Either String Type
getVarValueFromEnv v (Env typEnv _) = do
  foundItem <- getItemFromEnv v typEnv;
  case foundItem of
    EnvVarValue v -> Right v
    other -> Left ("requested EnvVarValue but found: " ++ show other)

getVarTypeFromEnv :: Variable -> Env -> Either String Type
getVarTypeFromEnv v (Env typEnv _) = do
  foundItem <- getItemFromEnv v typEnv;
  case foundItem of
    EnvVarType v -> Right v
    other -> Left ("requested EnvVarType but found: " ++ show other)

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
  isSubT <- isSubType env t1 t2
  if isSubT
  then isSubType env t2 t1
  else Right False

-- Returns true if the first argument is a subtype of the second
isSubType :: Env -> Type -> Type -> Either String Bool
isSubType env sub Top = Right True -- SA-Top
isSubType env TypTrue TypTrue = Right True -- SA-RelfTrue
isSubType env TypFalse TypFalse = Right True -- SA-ReflFalse
isSubType env (TypVariable v1) (TypVariable v2) = do -- SA-ReflTVar
  envContainsV <- containsVar v1 env;
  Right (v1 == v2 && envContainsV)
isSubType env a@(TypRecord tru1 fls1 select1) b@(TypRecord tru2 fls2 select2) = -- SA-ReflMap
  if (tru1 == tru2 && fls1 == fls2 && select1 == select2)
  then Right True
  else do -- Default to SA-TEvalRead
    (hasSimplified, teA) <- typeEval a EvalRead env;
    if hasSimplified
    then isSubType env teA b
    else Right False
isSubType env (TypFunction s1 s2) (TypFunction t1 t2) = do -- SA-Arrow
  t1Subs1 <- isSubType env t1 s1;
  t2Subs2 <- isSubType env t2 s2;
  Right (t1Subs1 && t2Subs2)
isSubType env (TypUniversal s ua) (TypUniversal t ub) = do -- SA-All
  abEqual <- typesAreEqual env ua ub;
  sSubT <- isSubType (shiftOverVarType ua env) s t;
  Right (abEqual && sSubT)-- For S-ALL, if the supertypes of the Universals are not equal, then one cannot be a subtype of the other
isSubType env (TypUnion l r) t = do -- SA-UnionM
  lSubT <- isSubType env l t;
  rSubT <- isSubType env r t;
  Right (lSubT && rSubT)
isSubType env t (TypUnion l r) = do -- SA-UnionLR
  tSubL <- isSubType env t l;
  tSubR <- isSubType env t r;
  Right (tSubL || tSubR)
 -- Custom rules for testing
isSubType env a@(TypRecord tru fls select) b = do -- SA-TEvalRead
  (hasSimplified, teA) <- typeEval a EvalRead env;
  if hasSimplified
  then isSubType env teA b
  else Right False
isSubType env a b@(TypRecord tru fls select) = do -- SA-TEvalWrite
  (hasSimplified, teB) <- typeEval b EvalWrite env
  if hasSimplified
  then isSubType env a teB
  else Right False
isSubType env (TypVariable v) superType = do -- SA-TransTVar
  vType <- getVarTypeFromEnv v env; -- moved to back because early unpacking was interfering with UnionLR and UnionM
  isSubType env vType superType
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

eitherOR :: Bool -> Either String (Bool, Type) -> Either String (Bool, Type)
eitherOR b (Right (b2, typ)) = Right (b || b2, typ)
eitherOR b (Left s) = Left s

typeEval :: Type -> EvalMode -> Env -> Either String (Bool, Type)
typeEval (TypRecord tru fls select) m env = do
  evalOfSelect <- typeEval select m env;
  case evalOfSelect of -- TE-Map
    (b, TypTrue) -> eitherOR True (typeEval tru m env) -- TE-MapTrue
    (b, TypFalse) -> eitherOR True (typeEval fls m env) -- TE-MapFalse
    (b, TypUnion l r) -> -- TE-MapUnion
      if m == EvalRead 
      then eitherOR True (typeEval (TypUnion (TypRecord tru fls l) (TypRecord tru fls r)) EvalRead env)
      else Right (b, TypRecord tru fls (TypUnion l r))
    (b, other) -> Right (b, other)

typeEval (TypUnion l r) m env = do -- TE-Union
  (bl, ll) <- typeEval l m env;
  (br, rr) <- typeEval r m env;
  Right (bl || br, TypUnion ll rr)

typeEval (TypVariable v) EvalRead env = do -- TE-TVarRead
  var <- getVarTypeFromEnv v env;
  Right (True, var)
typeEval (TypVariable v) EvalWrite env@(Env typEnv infoEnv) =  -- TE-TVarWrite
  case getSinglyDefinedVarFromEnv infoEnv v of
    Nothing -> Right (False, TypVariable v)
    Just result -> do
      (b, evalledResult) <- typeEval result EvalWrite env;
      Right (True, evalledResult)
typeEval t m env = Right (False, t) -- typeEval on non evaluatable type, returns that it has not changed it's input

getSinglyDefinedVarFromEnv :: InformationEnv -> Variable -> Maybe Type
getSinglyDefinedVarFromEnv infoEnv v = case Data.Map.lookup v infoEnv of
  Nothing -> Nothing
  Just info -> case info of
    (True, False) -> Just TypFalse
    (False, True) -> Just TypTrue
    (True, True) -> Nothing
    (False, False) -> Nothing
    

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
inferType env (TmAnnotation term typ) = do -- BT-Ann
  typIsCorrect <- isOfType env term typ;
  if typIsCorrect
  then Right typ
  else Left ("term: " ++ show term ++ " is not of type " ++ show typ)

inferType env (TmTypeAbstraction typeTerm superType) = do -- BT-TAbs
  typeTermType <- inferType (shiftOverVarType superType env) typeTerm;
  Right (TypUniversal typeTermType superType)

inferType env (TmApply func arg) = do -- BT-App
  funcType <- inferType env func;
  case funcType of
    (TypFunction funcInputType funcOutputType) -> do
      argTypIsCorrect <- isOfType env arg funcInputType;
      if argTypIsCorrect
      then Right funcOutputType
      else Left ("func and arg type mismatch: func=" ++ show (TypFunction funcInputType funcOutputType) ++ ", arg=" ++ show arg)
    other -> Left ("Apply expects TypFunction as first arg (was " ++ show other ++ ")")

inferType env (TmTypeApply universalFunc typeToSubstitute) = do -- BT-TApp
  universalFuncType <- inferType env universalFunc;
  case universalFuncType of
    (TypUniversal typTerm superType) -> do
      subsTypeIsCorrect <- isSubType env typeToSubstitute superType;
      if subsTypeIsCorrect
      then Right (typeTypeSubstitute typeToSubstitute Z typTerm)
      else Left ("AtRightting to apply a type to a universal type that does not accept it: universalFunc=" ++ show universalFunc ++ ", typeToSubstitute=" ++ show typeToSubstitute)
    other -> Left "type should be universal, since we are doing a type application"

inferType env (TmIsEq t1 t2) = do -- BT-Eq
  t1Typ <- inferType env t1;
  t2Typ <- inferType env t2;
  Right typBool

inferType env (TmAnd t1 t2) = do -- BT-And
  t1IsBool <- infersToBool env t1;
  t2IsBool <- infersToBool env t2;
  if t1IsBool && t2IsBool
  then Right typBool
  else Left ("Non-Bool args to &&: (" ++ show t1 ++ ") && (" ++ show t2 ++ ")")
  
inferType env (TmOr t1 t2) = do -- BT-Or
  t1IsBool <- infersToBool env t1;
  t2IsBool <- infersToBool env t2;
  if t1IsBool && t2IsBool
  then Right typBool
  else Left ("Non-Bool args to ||: (" ++ show t1 ++ ") || (" ++ show t2 ++ ")")

inferType env (TmIf cond thn els) = do -- BT-If
  condIsBool <- isOfType env cond typBool
  if condIsBool
  then let infoOfCond = informationOf env cond in do
    thnTyp <- inferType (addInfoToEnv env infoOfCond) thn;
    elsTyp <- inferType (addInfoToEnv env (invert infoOfCond)) els;
    Right (TypUnion thnTyp elsTyp)
  else Left "Condition is not of type Bool!"

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

isOfType env term typ = do -- BT-Sub
  typOfTerm <- inferType env term;
  isSubType env typOfTerm typ


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

