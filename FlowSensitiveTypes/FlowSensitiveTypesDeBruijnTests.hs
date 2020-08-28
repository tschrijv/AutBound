module FlowSensitiveTypesDeBruijnTests where
import FlowSensitiveTypesDeBruijnBase
import FlowSensitiveTypesDeBruijnImpl
import FlowSensitiveTypesDeBruijnShow

idFunc :: Term
idFunc = Top /<:-> (lambda v_)

idType :: Type
idType = typeof idFunc

-- apply takes two arguments, a function, and an argument to the function, and then runs the function on the argument
apply :: Term
apply = Top /<:-> (lambda (lambda (v_v <+ v_)))

-- double takes two arguments, a function, and an argument to the function, and then runs the function twice on the argument
double :: Term
double = Top /<:-> (lambda (lambda (v_v <+ (v_v <+ v_))))

tru :: Term
tru = TmTrue

fls :: Term
fls = TmFalse

superType :: Type
superType = Typ "TestSuperTyp"
subType :: Type
subType = Typ "TestSubTyp"

a :: Type
a = Typ "a"

b :: Type
b = Typ "b"

c :: Type
c = Typ "c"

d :: Type
d = Typ "d"

u :: Type -> Type -> Type
u t1 t2 = TypUnion t1 t2

-- commutativity
-- >>> isSubType emptyEnv (TypUnion a b) (TypUnion b a)
-- True
--

-- associativity
-- >>> isSubType emptyEnv (TypUnion (TypUnion a b) c) (TypUnion a (TypUnion b c))
-- True
--

-- associativity 2
-- >>> isSubType emptyEnv (TypUnion (TypUnion a b) (TypUnion c d)) (TypUnion (TypUnion (TypUnion a b) c) d)
-- True
--



-- old tests


-- >>> isSubType emptyEnv Top Top
-- True
--

-- >>> True
-- True
--

-- >>> isSubType emptyEnv superType subType
-- False
--

-- >>> isSubType emptyEnv (superType --> subType) (subType --> superType)
-- True
--

--typeOfTestTerm :: Term
--typeOfTestTerm = (subType --> superType) /-> (v_)


-- >>> typeof (((subType --> superType) /<:-> (lambda v_)) <++ (superType --> subType))
-- *** Exception: inferType of Abstractions is not supported
-- CallStack (from HasCallStack):
--   error, called at /home/lennart/Desktop/AutBound/FlowSensitiveTypes/FlowSensitiveTypesDeBruijnImpl.hs:221:3 in main:FlowSensitiveTypesDeBruijnImpl
--

-- >>> Top /<:-> v_
-- (Top /<:-> v_)
--

-- >>> (double <++ Typ "Int")
-- ((Top /<:-> (lambda (lambda (v_v <+ (v_v <+ v_))))) <++ Int)
--

annot :: Type
annot = ((Typ "Int" --> Typ "Int") --> Typ "Int" --> Typ "Int")

annotTermNoType :: Term
annotTermNoType = (double <++ Typ "Int")

annotTerm :: Term
annotTerm = TmAnnotation annotTermNoType annot

-- >>> annotTerm
-- (((Top /<:-> (lambda (lambda (v_v <+ (v_v <+ v_))))) <++ Int):(((Int --> Int) --> Int) --> Int))
--

-- >>> isOfType emptyEnv annotTerm annot
-- *** Exception: inferType of Abstractions is not supported
-- CallStack (from HasCallStack):
--   error, called at /home/lennart/Desktop/AutBound/FlowSensitiveTypes/FlowSensitiveTypesDeBruijnImpl.hs:221:3 in main:FlowSensitiveTypesDeBruijnImpl
--



-- >>> apply <++ Typ "Double"
-- ((Top /<:-> ((t_ --> t_) /-> (t_v /-> (v_v <+ v_)))) <++ {Double})
--

-- >>> typeof (apply <++ Typ "Int")
-- Just (({Int} --> {Int}) --> ({Int} --> {Int}))
--

-- >>> apply
-- (Top /<:-> ((t_ --> t_) /-> (t_v /-> (v_v <+ v_))))
--

-- >>> typeof apply
-- Just (Top <:-> ((t_ --> t_) --> (t_ --> t_)))
--

-- >>> typeof double
-- Just (Top <:-> ((t_ --> t_) --> (t_ --> t_)))
--


-- >>> typeof (double <++ idType)
-- Just (((Top <:-> (t_ --> t_)) --> (Top <:-> (t_ --> t_))) --> ((Top <:-> (t_ --> t_)) --> (Top <:-> (t_ --> t_))))
--

-- >>> eval idFunc
-- Just (Top /<:-> (t_ /-> v_))
--

-- >>> eval ((idFunc <++ idType) <+ idFunc)
-- Just (Top /<:-> (t_ /-> v_))
--

-- >>> eval (idFunc <++ idType)
-- Just ((Top <:-> (t_ --> t_)) /-> v_)
--

-- >>> typeof idFunc
-- Just (Top <:-> (t_ --> t_))
--

-- >>> typeof (idFunc <++ idType)
-- Just ((Top <:-> (t_ --> t_)) --> (Top <:-> (t_ --> t_)))
--


