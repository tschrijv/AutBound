module SystemFSubtypingDeBruijnTests where
import SystemFSubtypingDeBruijnBase
import SystemFSubtypingDeBruijnImpl
import SystemFSubtypingDeBruijnShow

idFunc :: Term
idFunc = Top /<:-> (t_ /-> v_)

idType :: Type
idType = removeMaybe (typeof idFunc) where 
  removeMaybe :: Maybe Type -> Type
  removeMaybe Nothing = error ""
  removeMaybe (Just t) = t

-- apply takes two arguments, a function, and an argument to the function, and then runs the function on the argument
apply :: Term
apply = Top /<:-> ((t_ --> t_) /-> (t_v /-> (v_v <+ v_)))

-- double takes two arguments, a function, and an argument to the function, and then runs the function twice on the argument
double :: Term
double = Top /<:-> ((t_ --> t_) /-> (t_v /-> (v_v <+ (v_v <+ v_))))


superType :: Type
superType = Typ "TestSuperTyp"
subType :: Type
subType = Typ "TestSubTyp"


-- >>> isSubType Top Top emptyEnv
-- Just True
--

-- >>> isSubType superType subType emptyEnv
-- Just False
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


