module FlowSensitiveTypesDeBruijnQuickCheck where
import FlowSensitiveTypesDeBruijnBase
import FlowSensitiveTypesDeBruijnImpl
import FlowSensitiveTypesDeBruijnShow
import Test.QuickCheck

import Debug.Trace

isValidTypedTerm :: Env -> Term -> Bool
isValidTypedTerm env t = case inferType env t of
  Right r -> True
  Left s -> False

isSubTypeErrable :: Env -> Type -> Type -> Bool
isSubTypeErrable env t1 t2 = case isSubType env t1 t2 of
  Right v -> v
  Left s -> error s -- convert to an error, as this should only be called on valid types


-- Type generation
genFunction :: Env -> Gen Type
genFunction env = do
  t1 <- genType env;
  t2 <- genType env;
  return $ TypFunction t1 t2

genUniversal :: Env -> Gen Type
genUniversal env = do
  super <- genType env;
  expr <- genType (shiftOverVarType super env);
  return $ TypUniversal expr super

genUnion :: Env -> Gen Type
genUnion env = do
  a <- genType env;
  b <- genType env;
  return $ TypUnion a b

genBoolType :: Env -> Gen Type
genBoolType env = suchThat (genType env) (isBool) where
  isBool :: Type -> Bool
  isBool t = case isSubType env t typBool of
    Right b -> b
    Left s -> error (s ++ " occured when calling isSubType .. typBool with " ++ show t)

genRecord :: Env -> Gen Type
genRecord env = do
  tru <- genType env;
  fls <- genType env;
  sel <- genBoolType env;
  return $ TypRecord tru fls sel

getVarAtIndex :: TypingEnv -> Int -> Variable
getVarAtIndex t 0 = Z
getVarAtIndex (EnvVarType t : typEnv) i = SVarType (getVarAtIndex typEnv (i-1))
getVarAtIndex (EnvVarValue t : typEnv) i = SVarValue (getVarAtIndex typEnv (i-1))
getVarAtIndex [] i = error "getVarAtIndex: Index out of range"

genTypeVarFromEnv :: TypingEnv -> Gen Variable
genTypeVarFromEnv typEnv = do
  index <- chooseInt (0, length typEnv - 1);
  return (getVarAtIndex typEnv index)

genVariable :: Env -> Gen Type
genVariable (Env typEnv infoEnv) = 
  if typEnv == []
  then genType (Env [] infoEnv) -- generate something else
  else do
    v <- genTypeVarFromEnv typEnv;
    return (TypVariable v)


genBool :: Gen Type
genBool = elements [TypTrue, TypFalse]

genTop :: Gen Type
genTop = return Top

--genTypeVarFromEnv :: TypingEnv -> Gen Variable
--genTypeVarFromEnv env 

--genVariable :: Env -> Gen Type
--genVariable (Env [] infoEnv) = Nothing
--genVariable (Env (EnvVarType t:r) infoEnv) = choose []

genOperator :: Env -> Gen Type
genOperator env = oneof [genFunction env, genUniversal env, genUnion env, genRecord env]

genType :: Env -> Gen Type
genType env = oneof [genOperator env, genBool, genTop, genVariable env]

--genEnv :: Env -> Gen Env
--genEnv parentEnv = 

instance Arbitrary Type
  where
    arbitrary = genType emptyEnv

-- >>> sample (genType emptyEnv)
-- Top
-- {true:Top, false:(Top --> {true:{true:Top, false:ttrue}[tfalse], false:tfalse}[{true:Top, false:ttrue}[tfalse]])}[ttrue]
-- {true:Top, false:{true:(Top U Top), false:Top}[tfalse]}[ttrue]
-- Top
-- ttrue
-- Top
-- tfalse
-- Top
-- tfalse
-- {true:{true:(ttrue U ((Top U ttrue) <:-> (Top U Top))), false:{true:Top, false:ttrue}[tfalse]}[ttrue], false:tfalse}[{true:tfalse, false:tfalse}[ttrue]]
-- tfalse
--

-- >>> sample (genBoolType emptyEnv)
-- tfalse
-- tfalse
-- ttrue
-- tfalse
-- ttrue
-- tfalse
-- ttrue
-- tfalse
-- {true:ttrue, false:Top}[ttrue]
-- ttrue
-- tfalse
--

quickCheckAllTypesSubTypeTop :: Type -> Bool
quickCheckAllTypesSubTypeTop t = isSubTypeErrable emptyEnv t Top
-- >>> quickCheck quickCheckAllTypesSubTypeTop
-- +++ OK, passed 100 tests.
--

checkTransitiveTypeYes :: (Type, Type, Type) -> Property
checkTransitiveTypeYes (t1, t2, t3) = 
  isSubTypeErrable emptyEnv t1 t2 && 
  isSubTypeErrable emptyEnv t2 t3 ==>
  isSubTypeErrable emptyEnv t1 t3

checkReflexiveType :: Type -> Bool
checkReflexiveType t = isSubTypeErrable emptyEnv t t

-- >>> quickCheckWith stdArgs { maxSuccess = 5000 } checkReflexiveType
-- *** Failed! (after 672 tests):
-- Exception:
--   Prelude.undefined
--   CallStack (from HasCallStack):
--     error, called at libraries/base/GHC/Err.hs:79:14 in base:GHC.Err
--     undefined, called at /home/lennart/Desktop/AutBound/FlowSensitiveTypes/FlowSensitiveTypesDeBruijnImpl.hs:207:42 in main:FlowSensitiveTypesDeBruijnImpl
-- (∀ t_ <: Top . (Top U {true:t_, false:t_}[ttrue]))
--

typeHitsUndefined = TypUniversal (TypUnion Top (TypRecord t_ t_ TypTrue)) Top

-- >>> typeHitsUndefined
-- (∀ t_ <: Top . (Top U {true:t_, false:t_}[ttrue]))
--

-- >>> TypUniversal (TypFunction t_ t_) Top
-- (∀ t_ <: Top . (t_ --> t_))
--


-- >>> isSubType emptyEnv typeHitsUndefined typeHitsUndefined
-- Right True
--

-- >>> quickCheckWith stdArgs { maxSuccess = 5000 } checkReflexiveType
-- *** Failed! Falsified (after 20 tests):
-- (∀ t_ <: (tfalse --> Top) . ({true:t_, false:t_}[(tfalse U tfalse)] U tfalse))

badTerm = TypUniversal (TypUnion (TypVariable Z) TypTrue) Top

badTerm2 = TypUnion (TypVariable Z) TypTrue

badTerm3 = TypVariable Z

isBad = TypUnion TypTrue TypFalse

-- >>> badTerm
-- (∀ t_ <: Top . (t_ U ttrue))
--

-- >>> isSubType emptyEnv badTerm badTerm
-- Right True
--

-- >>> badTerm2
-- (t_ U ttrue)
--

oneTypeEnv = Env [EnvVarType Top] emptyInfoEnv

-- >>> isSubType oneTypeEnv t_ (TypUnion t_ TypTrue)
-- t_
-- t_
-- ttrue
-- True
-- Right True
--

-- >>> isSubType oneTypeEnv t_ TypTrue
-- Right False
--

-- >>> False || True
-- True
--

-- >>> isSubType oneTypeEnv t_ t_
-- Right True
--

-- >>> isSubType oneTypeEnv badTerm2 badTerm2
-- Right False
--

-- >>> isSubType oneTypeEnv badTerm3 badTerm3
-- Right True
--

-- >>> isSubType emptyEnv isBad isBad
-- Right True
--


-- (Top <:-> (t_ U ttrue))
--


-- >>> quickCheckWith stdArgs { maxSuccess = 5000 } checkReflexiveType
-- *** Failed! Falsified (after 451 tests):
-- (∀ t_ <: Top . (t_ U {true:t_, false:(∀ t_ <: tfalse . t_t)}[ttrue]))
--

-- (∀ t_ <: Top . (t_ U {true:t_, false:(∀ t_ <: tfalse . t_t)}[ttrue]))
failingRefl = TypUniversal failingRefl2 Top

failingRefl2 = TypUnion t_ failingRefl3

failingRefl3 = TypRecord t_ (TypUniversal t_t TypFalse) TypTrue

failingReflHypot = TypUniversal failingReflHypotSmaller Top

failingReflHypotSmaller = TypUnion t_ (TypRecord t_ Top TypTrue)

--failingReflHypot2 = TypUniversal ((TypRecord t_ Top TypTrue)) Top

--failingReflHypot3 = TypUniversal (TypUnion t_ t_) Top

-- >>> failingRefl
-- (∀ t_ <: Top . (t_ U {true:t_, false:(∀ t_ <: tfalse . t_t)}[ttrue]))
--

-- >>> failingRefl3
-- {true:t_, false:(∀ t_ <: tfalse . t_t)}[ttrue]
--

-- >>> isSubType emptyEnv failingRefl failingRefl
-- Right True
--

-- >>> isSubType emptyEnv failingReflHypot failingReflHypot
-- Right False
--

-- >>> isSubType emptyEnv failingReflHypot2 failingReflHypot2
-- Right True
--

-- >>> isSubType emptyEnv failingReflHypot3 failingReflHypot3
-- Right True
--

-- >>> isSubType oneTypeEnv failingReflHypotSmaller failingReflHypotSmaller
-- Right True
--

-- >>> isSubType oneTypeEnv t_ (TypUnion t_ (TypRecord t_ Top TypTrue))
-- Right True
--
-- >>> isSubType oneTypeEnv (TypRecord t_ Top TypTrue) (TypUnion t_ (TypRecord t_ Top TypTrue))
-- Right True
--

-- >>> isSubType oneTypeEnv (TypRecord t_ Top TypTrue) (TypRecord t_ Top TypTrue)
-- Right True
--

-- >>> isSubType oneTypeEnv failingRefl2 failingRefl2
-- Right False
--

-- >>> isSubType oneTypeEnv failingRefl3 failingRefl3
-- Right True
--

-- >>> quickCheckWith stdArgs { maxSuccess = 5000 } checkReflexiveType
-- +++ OK, passed 5000 tests.
--


-- >>> quickCheck checkTransitiveTypeYes
-- *** Failed! Falsified (after 14 tests):
-- (ttrue,Top,{true:ttrue, false:Top}[tfalse])
--
-- This error has been fixed

-- >>> quickCheck checkTransitiveTypeYes
-- *** Failed! Falsified (after 26 tests):
-- ({true:ttrue, false:ttrue}[ttrue],Top,{true:{true:Top, false:ttrue}[ttrue], false:Top}[tfalse])
--
-- This error has been fixed

-- >>> quickCheck checkTransitiveTypeYes
-- *** Failed! (after 49 tests):                            
-- Exception:
--   invalid result from TypeEval? Input:{true:(ttrue U tfalse), false:tfalse}[{true:tfalse, false:ttrue}[(ttrue U ttrue)]]
--   CallStack (from HasCallStack):
--     error, called at FlowSensitiveTypesDeBruijnQuickCheck.hs:16:13 in main:FlowSensitiveTypesDeBruijnQuickCheck
-- (ttrue,{true:(ttrue U tfalse), false:tfalse}[{true:tfalse, false:ttrue}[(ttrue U ttrue)]],Top)


-- >>> quickCheckWith stdArgs { maxSuccess = 5000 } checkTransitiveTypeYes
-- +++ OK, passed 5000 tests; 16979 discarded.
--

testTyp :: Type
testTyp = TypRecord (TypUnion TypTrue TypFalse) TypFalse (TypRecord TypFalse TypTrue (TypUnion TypTrue TypTrue))


bad_t1p :: Type
bad_t1p = TypFalse

bad_t1 :: Type
bad_t1 = TypUnion TypTrue (TypFunction TypFalse TypFalse)

-- {true:({true:Top, false:((Top <:-> tfalse) --> (Top U Top))}[tfalse] <:-> Top), false:Top}[{true:ttrue, false:tfalse}[(tfalse U ttrue)]]
bad_t2 :: Type
bad_t2 = TypRecord (TypUniversal Top (TypRecord Top (TypFunction (TypUniversal TypFalse Top) (TypUnion Top Top)) TypFalse)) Top (TypRecord TypTrue TypFalse (TypUnion TypFalse TypTrue))

bad_t2p :: Type
bad_t2p = TypRecord TypFalse TypFalse (TypUnion TypFalse TypFalse)


--bad_t2 :: Type
--bad_t2 = TypRecord (TypUniversal Top (TypRecord Top (TypFunction (TypUniversal TypFalse Top) (TypUnion Top Top)) TypFalse)) Top (TypRecord TypTrue TypFalse (TypUnion TypFalse TypTrue))


-- CRASH
-- bad_t1 = ttrue U (tfalse --> tfalse)
-- bad_t2 = {true:({true:Top, false:((Top <:-> tfalse) --> (Top U Top))}[tfalse] <:-> Top), false:Top}[{true:ttrue, false:tfalse}[(tfalse U ttrue)]]
-- isSubType emptyEnv bad_t1 bad_t2

-- Minimal crash:
-- isSubType emptyEnv tfalse {true:tfalse, false:tfalse}[tfalse U tfalse]


-- >>> typeEval testTyp EvalWrite emptyEnv
-- Right {true:tfalse, false:ttrue}[(ttrue U ttrue)]
--

