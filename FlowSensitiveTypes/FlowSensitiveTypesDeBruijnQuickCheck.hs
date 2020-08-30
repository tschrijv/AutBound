module FlowSensitiveTypesDeBruijnQuickCheck where
import FlowSensitiveTypesDeBruijnBase
import FlowSensitiveTypesDeBruijnImpl
import FlowSensitiveTypesDeBruijnShow
import Test.QuickCheck


isValidTypedTerm :: Env -> Term -> Bool
isValidTypedTerm env t = case inferType env t of
  Right r -> True
  Left s -> False

isSubTypeErrable :: Env -> Type -> Type -> Bool
isSubTypeErrable env t1 t2 = case isSubType env t1 t2 of
  Right v -> v
  Left s -> error s -- convert to an error, as this should only be called on valid types

checkTransitiveTypeYes :: (Type, Type, Type) -> Property
checkTransitiveTypeYes (t1, t2, t3) = 
  isSubTypeErrable emptyEnv t1 t2 && isSubTypeErrable emptyEnv t2 t3 ==>
  isSubTypeErrable emptyEnv t1 t3

quickCheckTest :: Int -> Property
quickCheckTest i = i < 500 ==> i < 500

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

-- >>> quickCheck quickCheckTest
-- +++ OK, passed 100 tests.
--

-- >>> quickCheck checkTransitiveTypeYes
-- *** Failed! Falsified (after 14 tests):
-- (ttrue,Top,{true:ttrue, false:Top}[tfalse])
--

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
