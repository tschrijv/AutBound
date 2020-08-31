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
genFunction :: Gen Type
genFunction = do
  t1 <- genType;
  t2 <- genType;
  return $ TypFunction t1 t2

genUniversal :: Gen Type
genUniversal = do
  super <- genType;
  expr <- genType;
  return $ TypUniversal expr super

genUnion :: Gen Type
genUnion = do
  a <- genType;
  b <- genType;
  return $ TypUnion a b

genBoolType :: Gen Type
genBoolType = suchThat genType (isBool) where
  isBool :: Type -> Bool
  isBool t = case isSubType emptyEnv t typBool of
    Right b -> b
    Left s -> error s

genRecord :: Gen Type
genRecord = do
  tru <- genType;
  fls <- genType;
  sel <- genBoolType;
  return $ TypRecord tru fls sel

genBool :: Gen Type
genBool = elements [TypTrue, TypFalse]

genTop :: Gen Type
genTop = return Top

genOperator :: Gen Type
genOperator = oneof [genFunction, genUniversal, genUnion, genRecord]

genType :: Gen Type
genType = oneof [genOperator, genBool, genTop]

instance Arbitrary Type
  where
    arbitrary = genType

-- >>> sample genType
-- Top
-- Top
-- ttrue
-- (ttrue U (Top U ttrue))
-- Top
-- {true:{true:ttrue, false:({true:{true:Top, false:{true:(Top <:-> Top), false:ttrue}[tfalse]}[tfalse], false:(ttrue --> Top)}[ttrue] U ttrue)}[tfalse], false:ttrue}[tfalse]
-- ttrue
-- tfalse
-- tfalse
-- tfalse
-- {true:tfalse, false:Top}[ttrue]
--


quickCheckAllTypesSubTypeTop :: Type -> Bool
quickCheckAllTypesSubTypeTop t = isSubTypeErrable emptyEnv t Top
-- >>> quickCheck quickCheckAllTypesSubTypeTop
-- +++ OK, passed 100 tests.
--

checkTransitiveTypeYes :: (Type, Type, Type) -> Property
checkTransitiveTypeYes (t1, t2, t3) = 
  isSubTypeErrable emptyEnv (traceShowId t1) (traceShowId t2) && isSubTypeErrable emptyEnv t2 (traceShowId t3) ==>
  isSubTypeErrable emptyEnv t1 t3

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


-- >>> quickCheck checkTransitiveTypeYes

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

