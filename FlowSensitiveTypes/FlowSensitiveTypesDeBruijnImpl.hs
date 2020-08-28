module FlowSensitiveTypesDeBruijnImpl where
import FlowSensitiveTypesDeBruijnBase
import FlowSensitiveTypesDeBruijnShow

import qualified Data.Map

-- by variable index we index the variables, new variables are pushed to the front
data EnvItem = EnvVarValue Type | EnvVarType Type deriving (Eq, Show)
type TypingEnv = [EnvItem]

-- the pair denotes the possibility of cases (False, True)
type InformationEnv = Data.Map.Map Variable (Bool, Bool)

data Env = Env TypingEnv InformationEnv

emptyEnv :: Env
emptyEnv = Env [] Data.Map.empty

getItemFromEnv :: Variable -> TypingEnv -> EnvItem
getItemFromEnv Z (item:_) = item
getItemFromEnv (SVarValue v) (EnvVarValue _:rest) = getItemFromEnv v rest
getItemFromEnv (SVarType v) (EnvVarType _:rest) = getItemFromEnv v rest
getItemFromEnv _ _ = error "wrong or no binding for var, or DeBruijn index structure does not match path in term"

getVarValueFromEnv :: Variable -> Env -> Type
getVarValueFromEnv v (Env typEnv _) = case getItemFromEnv v typEnv of
  EnvVarValue v -> v
  otherwise -> error "requested EnvVarValue but found something else"

getVarTypeFromEnv :: Variable -> Env -> Type
getVarTypeFromEnv v (Env typEnv _) = case getItemFromEnv v typEnv of
  EnvVarType v -> v
  otherwise -> error "requested EnvVarType but found something else"

containsVarInEnv :: Variable -> TypingEnv -> Bool
containsVarInEnv Z (item:_) = True
containsVarInEnv _ [] = False
containsVarInEnv (SVarValue v) (EnvVarValue _:rest) = containsVarInEnv v rest
containsVarInEnv (SVarType v) (EnvVarType _:rest) = containsVarInEnv v rest
containsVarInEnv _ _ = error "containsVar given var and env paths do not match"

containsVar :: Variable -> Env -> Bool
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



-- turns a tree of top-level unions into a list of Types, all of which together form the full union
flattenUnion :: Type -> [Type]
flattenUnion (TypUnion a b) = flattenUnion a ++ flattenUnion b
flattenUnion anythingElse = [anythingElse]

-- removes duplicates in a union list (X U Y -> Y iff X <: Y)
eliminateSubTypesFromUnionList :: Env -> [Type] -> [Type]
eliminateSubTypesFromUnionList env [] = []
eliminateSubTypesFromUnionList env (item:rest) = 
  let filteredRest = filter (\i -> not (isSubType env i item)) rest in
    let eliminatedRest = eliminateSubTypesFromUnionList env filteredRest in
      -- we can just check on eliminatedRest instead of filteredRest, 
      -- because if there was an element v for which item <: v, and v was removed by an element v <: w, 
      -- then item will still be removed by w since item <: v <: w -> item <: w
      if any (\i -> isSubType env item i) eliminatedRest then
        eliminatedRest
      else
        (item : eliminatedRest)

normalizeUnion :: Env -> Type -> [Type]
normalizeUnion env = eliminateSubTypesFromUnionList env . flattenUnion

-- finds and removes the first element for which the condition holds
findAndRemove :: (a -> Bool) -> [a] -> Maybe [a] 
findAndRemove c [] = Nothing -- item was not found
findAndRemove c (item:rest) = 
  if c item
  then Just rest
  else case findAndRemove c rest of
    Nothing -> Nothing
    Just removedRest -> Just (item : removedRest)

areListsEqual :: (a -> a -> Bool) -> [a] -> [a] -> Bool
areListsEqual eq [] [] = True
areListsEqual eq [] (x:xs) = False -- second list contains an item not in the first list
areListsEqual eq (item1:rest1) list2 = case findAndRemove (eq item1) list2 of
  Nothing -> False -- one of the types was not found
  Just rest2 -> areListsEqual eq rest1 rest2

typesAreEqual :: Env -> Type -> Type -> Bool
typesAreEqual env t1 t2 = isSubType env t1 t2 && isSubType env t2 t1
  --let nt1 = normalizeUnion env t1 in
  --  let nt2 = normalizeUnion env t2 in
  --    areListsEqual (\x y -> isSubType env x y && isSubType env y x) nt1 nt2

-- Returns true if the first argument is a subtype of the second
isSubType :: Env -> Type -> Type -> Bool
isSubType env sub Top = True -- SA-Top
isSubType env TypTrue TypTrue = True -- SA-RelfTrue
isSubType env TypFalse TypFalse = True -- SA-ReflFalse
isSubType env (TypVariable v1) (TypVariable v2) = -- SA-ReflTVar
  v1 == v2 && containsVar v1 env
isSubType env (TypRecord tru1 fls1 select1) (TypRecord tru2 fls2 select2) = -- SA-ReflMap
  tru1 == tru2 && fls1 == fls2 && select1 == select2
isSubType env r@(TypRecord tru fls select) a = -- SA-TEvalRead
  typesAreEqual env (typeEval r EvalRead env) (typeEval a EvalRead env)
isSubType env a r@(TypRecord tru fls select) = -- SA-TEvalWrite
  typesAreEqual env (typeEval r EvalWrite env) (typeEval a EvalWrite env)
isSubType env (TypVariable v) superType = -- SA-TransTVar
  let vType = getVarTypeFromEnv v env in
    isSubType env vType superType
isSubType env (TypFunction s1 s2) (TypFunction t1 t2) = -- SA-Arrow
    isSubType env t1 s1 && isSubType env s2 t2
isSubType env (TypUniversal s ua) (TypUniversal t ub) = -- SA-All
  if typesAreEqual env ua ub
  then isSubType (shiftOverVarType ua env) s t
  else False -- For S-ALL, if the supertypes of the Universals are not equal, then one cannot be a subtype of the other
isSubType env (TypUnion l r) t = -- SA-UnionN
  isSubType env l t && isSubType env r t
isSubType env t (TypUnion l r) = -- SA-UnionLR
  isSubType env t l || isSubType env t r

 -- Custom rules for testing
isSubType env (Typ "TestSubTyp") (Typ "TestSuperTyp") = True
isSubType env (Typ a) (Typ b) =
  a == b




-- TODO add new context, the learned information context
-- 


typBool :: Type
typBool = TypUnion TypTrue TypFalse

data EvalMode = EvalRead | EvalWrite deriving(Eq, Show)
typeEval :: Type -> EvalMode -> Env -> Type
typeEval (TypRecord tru fls select) m env = 
  case (typeEval select m env) of -- TE-Map
    TypTrue -> typeEval tru m env -- TE-MapTrue
    TypFalse -> typeEval fls m env -- TE-MapFalse
    TypUnion l r -> -- TE-MapUnion
      if m == EvalRead 
      then typeEval (TypUnion (TypRecord tru fls l) (TypRecord tru fls r)) EvalRead env
      else (TypRecord tru fls select)
typeEval (TypUnion l r) m env = -- TE-Union
  let ll = typeEval l m env in
    let rr = typeEval r m env in
      TypUnion ll rr
typeEval t m env = t -- transitive closure, allow applying 0 rules

-- TODO variables?

-- onder env+X is typeTerm type T2, 
-- Dan is TypeAbstraction typeTerm onder env type TypUniversal T2

inferType :: Env -> Term -> Type
inferType env TmTrue = TypTrue -- BT-True
inferType env TmFalse = TypFalse -- BT-False
inferType env (TmVariable v) = getVarValueFromEnv v env -- BT-Var
--inferType env (TmAbstraction subTerm inputType) =    -- No BT-Abs?
--  let outputType = inferType (shiftOverVarValue inputType env) subTerm in
--    TypFunction inputType (shiftFuncReturn outputType)
inferType env (TmAnnotation term typ) = -- BT-Ann
  if isOfType env term typ
  then typ
  else error ("term: " ++ show term ++ " is not of type " ++ show typ)
inferType env (TmTypeAbstraction typeTerm superType) = -- BT-TAbs
  let typeTermType = inferType (shiftOverVarType superType env) typeTerm in
    TypUniversal typeTermType superType
inferType env (TmApply func arg) = -- BT-App
  let funcType = inferType env func in
    case funcType of
      TypFunction funcInputType funcOutputType -> 
        if isOfType env arg funcInputType
          then funcOutputType
          else error ("func and arg type mismatch: func=" ++ show funcType ++ ", arg=" ++ show arg)
      otherwise -> error ("Apply expects TypFunction as first arg (was " ++ show funcType ++ ")")

inferType env (TmTypeApply universalFunc typeToSubstitute) = -- BT-TApp
  case inferType env universalFunc of
    TypUniversal typTerm superType -> 
      if isSubType env typeToSubstitute superType
      then typeTypeSubstitute typeToSubstitute Z typTerm
      else error ("Attempting to apply a type to a universal type that does not accept it: universalFunc=" ++ show universalFunc ++ ", typeToSubstitute=" ++ show typeToSubstitute)
    otherwise -> error "type should be universal, since we are doing a type application"

inferType env (TmIsEq t1 t2) = -- BT-Eq
  let typ1 = inferType env t1 in -- unused, but can throw error if invalid
    let typ2 = inferType env t2 in -- unused, but can throw error if invalid
      typBool

inferType env (TmAnd t1 t2) = -- BT-And
  if isSubType env (inferType env t1) typBool && isSubType env (inferType env t2) typBool
  then typBool
  else error ("Non-Bool args to &&: (" ++ show t1 ++ ") && (" ++ show t2 ++ ")")

inferType env (TmOr t1 t2) = -- BT-Or
  if isSubType env (inferType env t1) typBool && isSubType env (inferType env t2) typBool
  then typBool
  else error ("Non-Bool args to ||: (" ++ show t1 ++ ") || (" ++ show t2 ++ ")")

inferType env (TmIf cond thn els) = -- BT-If
  if isOfType env cond typBool
  then let infoOfCond = informationOf env cond in
    TypUnion (inferType (addInfoToEnv env infoOfCond) thn) (inferType (addInfoToEnv env (invert infoOfCond)) els)
  else error "Condition is not of type Bool!"

inferType env (TmAbstraction _) = 
  error "inferType of Abstractions is not supported"

-- others not defined


typeof :: Term -> Type
typeof = inferType emptyEnv


isOfType :: Env -> Term -> Type -> Bool
isOfType env (TmAbstraction tm) funcTyp = -- BT-Abs
  case funcTyp of
    TypFunction from to -> 
      let envInAbstraction = shiftOverVarValue from env in
        isOfType envInAbstraction tm to
    otherwise -> error ("isOfType of an abstraction must attempt to check with a function type! Actual type: " ++ show funcTyp)

isOfType env term typ = -- BT-Sub
  let typOfTerm = inferType env term in
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

