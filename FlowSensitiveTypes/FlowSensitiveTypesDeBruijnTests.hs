module FlowSensitiveTypesDeBruijnTests where
import FlowSensitiveTypesDeBruijnBase
import FlowSensitiveTypesDeBruijnImpl
import FlowSensitiveTypesDeBruijnShow

idFunc :: Term
idFunc = Top /<:-> (t_ /-> v_)

idType :: Type
idType = typeof idFunc

-- apply takes two arguments, a function, and an argument to the function, and then runs the function on the argument
apply :: Term
apply = Top /<:-> ((t_ --> t_) /-> (t_v /-> (v_v <+ v_)))

-- double takes two arguments, a function, and an argument to the function, and then runs the function twice on the argument
double :: Term
double = Top /<:-> ((t_ --> t_) /-> (t_v /-> (v_v <+ (v_v <+ v_))))


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
-- >>> isSubType (TypUnion a b) (TypUnion b a) emptyEnv
-- True
--

-- associativity
-- >>> isSubType (TypUnion (TypUnion a b) c) (TypUnion a (TypUnion b c)) emptyEnv
-- True
--

-- associativity 2
-- >>> isSubType (TypUnion (TypUnion a b) (TypUnion c d)) (TypUnion (TypUnion (TypUnion a b) c) d) emptyEnv
-- True
--



-- old tests


-- >>> isSubType Top Top emptyEnv
-- True
--

-- >>> True
-- True
--

-- >>> isSubType superType subType emptyEnv
-- Just False
--

-- >>> isSubType (superType --> subType) (subType --> superType) emptyEnv
-- Just True
--

--typeOfTestTerm :: Term
--typeOfTestTerm = (subType --> superType) /-> (v_)


-- >>> typeof (((subType --> superType) /<:-> (t_ /-> v_)) <++ (superType --> subType))
-- Just (({TestSuperTyp} --> {TestSubTyp}) --> ({TestSuperTyp} --> {TestSubTyp}))
--

-- >>> typeof (double <++ Typ "Int")
-- Just (({Int} --> {Int}) --> ({Int} --> {Int}))
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


