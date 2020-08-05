module LambdaImpl where
import LambdaBase

eval :: Term -> Maybe Value
eval (TmVariable v) = Nothing
eval (TmValue v) = Just v
eval (TmApply t1 t2) = 
  do {
    (Abstraction t) <- eval t1;
    let subsV = termTermSubstitute t2 Z t in
      eval subsV
  }

idFunc :: Term
idFunc = TmValue (Abstraction (TmVariable Z))

func :: Term -> Term
func t = TmValue (Abstraction t)

zero :: Term
zero = TmVariable Z

one :: Term
one = TmVariable (SVarValue Z)

apply :: Term
apply = func (func (TmApply one zero))

-- >>> eval apply
-- (Error while loading modules for evaluation)
-- <BLANKLINE>
-- <no location info>: error:
--     module ‘main@main:Main’ is defined in multiple files: /home/lennart/Desktop/AutBound/BasicLambda/LambdaImpl.hs
--                                                           /home/lennart/Desktop/AutBound/newSysF/SystemFImpl.hs
-- Failed, modules loaded: none.
--

-- >>> eval (TmApply (TmApply apply idFunc) idFunc)
-- (Error while loading modules for evaluation)
-- <BLANKLINE>
-- <no location info>: error:
--     module ‘main@main:Main’ is defined in multiple files: /home/lennart/Desktop/AutBound/BasicLambda/LambdaImpl.hs
--                                                           /home/lennart/Desktop/AutBound/newSysF/SystemFImpl.hs
-- Failed, modules loaded: none.
--


-- >>> func
-- <interactive>:47:2: error:
--     • No instance for (Show (Term -> Term))
--         arising from a use of ‘print’
--         (maybe you haven't applied a function to enough arguments?)
--     • In a stmt of an interactive GHCi command: print it
--

