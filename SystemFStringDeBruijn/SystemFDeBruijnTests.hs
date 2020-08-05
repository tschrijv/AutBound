module SystemFDeBruijnTests where
import SystemFDeBruijnBase
import SystemFDeBruijnImpl
import SystemFDeBruijnShow

idFunc :: Term
idFunc = template (t_ /-> v_)

-- apply takes two arguments, a function, and an argument to the function, and then runs the function on the argument
apply :: Term
apply = template ((t_ --> t_) /-> (t_v /-> (v_v <: v_)))

-- double takes two arguments, a function, and an argument to the function, and then runs the function twice on the argument
double :: Term
double = template ((t_ --> t_) /-> (t_v /-> (v_v <: (v_v <: v_))))

--fls :: Term
--fls = template (t_ /-> (t_ /-> ))

-- >>> typeof (double <:: Typ "Int")
-- Just (({Int} --> {Int}) --> ({Int} --> {Int}))
--

-- >>> apply <:: Typ "Double"
-- (template ((t_ --> t_) /-> (t_v /-> (v_v <: v_))) <:: {Double})
--

-- >>> typeof (apply <:: Typ "Int")
-- Just (({Int} --> {Int}) --> ({Int} --> {Int}))
--

-- >>> apply
-- template ((t_ --> t_) /-> (t_v /-> (v_v <: v_)))
--

-- >>> typeof apply
-- Just A.X ((t_ --> t_) --> (t_ --> t_))
--

applyAtStep1 :: Term
applyAtStep1 = (t_ --> t_) /-> (t_v /-> (v_v <: v_))

envAtStep1 :: Env
envAtStep1 = [(EnvVarType)]

-- >>> typeofHelper envAtStep1 applyAtStep1
-- Just ((t_ --> t_) --> (t_ --> t_))
--

applyAtStep2 :: Term
applyAtStep2 = (t_v /-> (v_v <: v_))

envAtStep2 :: Env
envAtStep2 = [EnvVarValue (t_v --> t_v), EnvVarType]

-- >>> typeofHelper envAtStep2 applyAtStep2
-- Just (t_v --> t_v)
--

applyAtStep3 :: Term
applyAtStep3 = (v_v <: v_)

envAtStep3 :: Env
envAtStep3 = [EnvVarValue t_vv, EnvVarValue (t_vv --> t_vv), EnvVarType]

-- >>> typeofHelper envAtStep3 applyAtStep3
-- Just t_vv
--


-- >>> typeof double
-- Just A.X ((t_ --> t_) --> (t_v --> t_v))
--


-- >>> typeof (double <:: idType)
-- Just ((A.X (t_ --> t_) --> A.X (t_ --> t_)) --> (t_v --> t_v))
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


