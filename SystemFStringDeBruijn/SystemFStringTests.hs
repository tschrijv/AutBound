module SystemFStringTests where
import SystemFStringBase
import SystemFStringImpl
import SystemFStringShow

var :: String -> Term
var s = TmVariable (SVarValue s)

typ :: String -> Type
typ s = TypVariable (SVarType s)

idFunc :: Term
idFunc = template "T" (("x" =: typ "T") /-> var "x")

-- apply takes two arguments, a function, and an argument to the function, and then runs the function on the argument
apply :: Term
apply = template "T" ("f" =: (typ "T" --> typ "T") /-> ("a" =: typ "T" /-> (var "f" <: var "a")))

-- double takes two arguments, a function, and an argument to the function, and then runs the function twice on the argument
double :: Term
double = template "T" ("f" =: (typ "T" --> typ "T") /-> ("a" =: typ "T" /-> (var "f" <: (var "f" <: var "a"))))

--fls :: Term
--fls = template (t_ /-> (t_ /-> ))

-- >>> typeof (double)
-- Just ∀.T ((T --> T) --> (T --> T))
--

-- >>> apply <:: Typ "Int"
-- ((template<T> (\f: (T --> T) -> (\a: T -> (f a)))) [{Int}])
--

-- >>> typeof (apply <:: Typ "Int")
-- Just (({Int} --> {Int}) --> ({Int} --> {Int}))
--

-- >>> double
-- template T (\f: (T --> T) -> (\a: T -> (f <: (f <: a))))
--

-- >>> typeof (double <:: idType)
-- <interactive>:12965:21: error:
--     Variable not in scope: idType :: SystemFStringBase.Type
--

-- >>> eval idFunc
-- Just template (t_ /-> v_)
--

-- >>> eval ((idFunc <:: getType idFunc) <: idFunc)
-- Just template (t_ /-> v_)
--

-- >>> eval (idFunc <:: getType idFunc)
-- Just (A.X (t_ --> t_) /-> v_)
--

-- >>> typeof idFunc
-- Just A.X (t_ --> t_)
--

-- >>> typeof (idFunc <:: getType idFunc)
-- Just A.X (t_ --> t_)
--


