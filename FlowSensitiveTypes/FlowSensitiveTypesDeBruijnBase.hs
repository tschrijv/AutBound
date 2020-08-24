module FlowSensitiveTypesDeBruijnBase where
import Data.List 

data Variable = Z | SVarValue Variable | SVarType Variable deriving(Eq)

data Term = TmVariable Variable | TmApply Term Term | TmTypeApply Term Type | TmIf Term Term Term | TmIsEq Term Term | TmAnd Term Term | TmOr Term Term | TmAbstraction Term Type | TmTypeAbstraction Term Type | TmTrue | TmFalse deriving(Eq)

data Type = TypVariable Variable | TypFunction Type Type | TypUniversal Type Type | TypUnion Type Type | TypRecord Type Type Type | TypTrue | TypFalse | TypBool | Top | Typ String deriving(Eq)


-- Add two Variables.
plus :: Variable -> Variable -> Variable
plus (Z) h = h
plus h (Z) = h
plus (SVarValue x1) x2 = (SVarValue (plus x1 x2))
plus (SVarType x1) x2 = (SVarType (plus x1 x2))

-- Substract the second Variable from the first. The first Variable has to
-- be greater than the second one.
minus :: Variable -> Variable -> Variable
minus (Z) (Z) = (Z)
minus (Z) _ = (error "You cannot substract zero with a positive number")
minus result (Z) = result
minus (SVarValue h1) (SVarValue h2) = (minus h1 h2)
minus (SVarValue h1) (SVarType h2) = (SVarValue (minus h1 (SVarType h2)))
minus (SVarType h1) (SVarValue h2) = (SVarType (minus h1 (SVarValue h2)))
minus (SVarType h1) (SVarType h2) = (minus h1 h2)

-- Apply SVarValue n times to the second argument c.
generateHnatVarValue :: Int -> Variable -> Variable
generateHnatVarValue 0 c = c
generateHnatVarValue n c = (SVarValue (generateHnatVarValue (n - 1) c))

-- Apply SVarType n times to the second argument c.
generateHnatVarType :: Int -> Variable -> Variable
generateHnatVarType 0 c = c
generateHnatVarType n c = (SVarType (generateHnatVarType (n - 1) c))

-- Perform the shift operation on one Term with the TmVariable constructor.
termshiftHelpplus :: Variable -> Variable -> Term -> Term
termshiftHelpplus d c (TmVariable var) = if (var >= c) then (TmVariable (plus c (plus d (minus var c)))) else (TmVariable var)

-- Perform the shift operation on one Type with the TypVariable constructor.
typeshiftHelpplus :: Variable -> Variable -> Type -> Type
typeshiftHelpplus d c (TypVariable var) = if (var >= c) then (TypVariable (plus c (plus d (minus var c)))) else (TypVariable var)

-- Perform the shift operation on a Term.
termshiftplus :: Variable -> Term -> Term
termshiftplus d t = (termmap (termshiftHelpplus d) (typeshiftHelpplus d) (Z) t)

-- Perform the shift operation on a Type.
typeshiftplus :: Variable -> Type -> Type
typeshiftplus d t = (typemap (typeshiftHelpplus d) (Z) t)

-- Perform the shift operation on one Term with the TmVariable constructor.
termshiftHelpminus :: Variable -> Variable -> Term -> Term
termshiftHelpminus d c (TmVariable var) = if (var >= c) then (TmVariable (minus var d)) else (TmVariable var)

-- Perform the shift operation on one Type with the TypVariable constructor.
typeshiftHelpminus :: Variable -> Variable -> Type -> Type
typeshiftHelpminus d c (TypVariable var) = if (var >= c) then (TypVariable (minus var d)) else (TypVariable var)

-- Perform the shift operation on a Term.
termshiftminus :: Variable -> Term -> Term
termshiftminus d t = (termmap (termshiftHelpminus d) (typeshiftHelpminus d) (Z) t)

-- Perform the shift operation on a Type.
typeshiftminus :: Variable -> Type -> Type
typeshiftminus d t = (typemap (typeshiftHelpminus d) (Z) t)

-- Return the Term where onVarValue, onVarType are applied to each
-- Term, Type in the given Term respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
termmap :: (Variable -> Term -> Term) -> (Variable -> Type -> Type) -> Variable -> Term -> Term
termmap onVarValue onVarType c (TmVariable var) = (onVarValue c (TmVariable var))
termmap onVarValue onVarType c (TmApply t1 t2) = (TmApply (termmap onVarValue onVarType c t1) (termmap onVarValue onVarType c t2))
termmap onVarValue onVarType c (TmTypeApply t1 t2) = (TmTypeApply (termmap onVarValue onVarType c t1) (typemap onVarType c t2))
termmap onVarValue onVarType c (TmIf cond thn els) = (TmIf (termmap onVarValue onVarType c cond) (termmap onVarValue onVarType c thn) (termmap onVarValue onVarType c els))
termmap onVarValue onVarType c (TmIsEq a b) = (TmIsEq (termmap onVarValue onVarType c a) (termmap onVarValue onVarType c b))
termmap onVarValue onVarType c (TmAnd a b) = (TmAnd (termmap onVarValue onVarType c a) (termmap onVarValue onVarType c b))
termmap onVarValue onVarType c (TmOr a b) = (TmOr (termmap onVarValue onVarType c a) (termmap onVarValue onVarType c b))
termmap onVarValue onVarType c (TmAbstraction t typ) = (TmAbstraction (termmap onVarValue onVarType (SVarValue c) t) (typemap onVarType c typ))
termmap onVarValue onVarType c (TmTypeAbstraction typeTerm superType) = (TmTypeAbstraction (termmap onVarValue onVarType (SVarType c) typeTerm) (typemap onVarType c superType))
termmap onVarValue onVarType c (TmTrue) = (TmTrue)
termmap onVarValue onVarType c (TmFalse) = (TmFalse)

-- Return the Type where onVarType is applied to each
-- Type in the given Type respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied function.
typemap :: (Variable -> Type -> Type) -> Variable -> Type -> Type
typemap onVarType c (TypVariable var) = (onVarType c (TypVariable var))
typemap onVarType c (TypFunction from to) = (TypFunction (typemap onVarType c from) (typemap onVarType c to))
typemap onVarType c (TypUniversal on superType) = (TypUniversal (typemap onVarType (SVarType c) on) (typemap onVarType c superType))
typemap onVarType c (TypUnion a b) = (TypUnion (typemap onVarType c a) (typemap onVarType c b))
typemap onVarType c (TypRecord tru fls selector) = (TypRecord (typemap onVarType c tru) (typemap onVarType c fls) (typemap onVarType c selector))
typemap onVarType c (TypTrue) = (TypTrue)
typemap onVarType c (TypFalse) = (TypFalse)
typemap onVarType c (TypBool) = (TypBool)
typemap onVarType c (Top) = (Top)
typemap onVarType c (Typ string1) = (Typ string1)

-- Perform one substitution step on a Term with the TmVariable constructor.
termSubstituteHelp :: Term -> Variable -> Term -> Term
termSubstituteHelp sub c (TmVariable var) = if (var == c) then (termshiftplus c sub) else (TmVariable var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Term in the given Term.
termTermSubstitute :: Term -> Variable -> Term -> Term
termTermSubstitute sub orig t = (termmap (termSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Type in the given Term.
termTypeSubstitute :: Type -> Variable -> Term -> Term
termTypeSubstitute sub orig t = (termmap (\c x -> x) (typeSubstituteHelp sub) orig t)

-- Perform one substitution step on a Type with the TypVariable constructor.
typeSubstituteHelp :: Type -> Variable -> Type -> Type
typeSubstituteHelp sub c (TypVariable var) = if (var == c) then (typeshiftplus c sub) else (TypVariable var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Type in the given Type.
typeTypeSubstitute :: Type -> Variable -> Type -> Type
typeTypeSubstitute sub orig t = (typemap (typeSubstituteHelp sub) orig t)

-- Return a list of the free variables of the given Term.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesTerm :: Variable -> Term -> [Variable]
freeVariablesTerm c (TmVariable var) = if (var >= c) then [(minus var c)] else []
freeVariablesTerm c (TmApply t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesTerm c t2)]))
freeVariablesTerm c (TmTypeApply t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesType c t2)]))
freeVariablesTerm c (TmIf cond thn els) = (nub (concat [(freeVariablesTerm c cond),(freeVariablesTerm c thn),(freeVariablesTerm c els)]))
freeVariablesTerm c (TmIsEq a b) = (nub (concat [(freeVariablesTerm c a),(freeVariablesTerm c b)]))
freeVariablesTerm c (TmAnd a b) = (nub (concat [(freeVariablesTerm c a),(freeVariablesTerm c b)]))
freeVariablesTerm c (TmOr a b) = (nub (concat [(freeVariablesTerm c a),(freeVariablesTerm c b)]))
freeVariablesTerm c (TmAbstraction t typ) = (nub (concat [(freeVariablesTerm (SVarValue c) t),(freeVariablesType c typ)]))
freeVariablesTerm c (TmTypeAbstraction typeTerm superType) = (nub (concat [(freeVariablesTerm (SVarType c) typeTerm),(freeVariablesType c superType)]))
freeVariablesTerm c (TmTrue) = (nub (concat [[]]))
freeVariablesTerm c (TmFalse) = (nub (concat [[]]))

-- Return a list of the free variables of the given Type.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesType :: Variable -> Type -> [Variable]
freeVariablesType c (TypVariable var) = if (var >= c) then [(minus var c)] else []
freeVariablesType c (TypFunction from to) = (nub (concat [(freeVariablesType c from),(freeVariablesType c to)]))
freeVariablesType c (TypUniversal on superType) = (nub (concat [(freeVariablesType (SVarType c) on),(freeVariablesType c superType)]))
freeVariablesType c (TypUnion a b) = (nub (concat [(freeVariablesType c a),(freeVariablesType c b)]))
freeVariablesType c (TypRecord tru fls selector) = (nub (concat [(freeVariablesType c tru),(freeVariablesType c fls),(freeVariablesType c selector)]))
freeVariablesType c (TypTrue) = (nub (concat [[]]))
freeVariablesType c (TypFalse) = (nub (concat [[]]))
freeVariablesType c (TypBool) = (nub (concat [[]]))
freeVariablesType c (Top) = (nub (concat [[]]))
freeVariablesType c (Typ string1) = (nub (concat [[]]))
instance Ord Variable where
  compare (Z) (Z) = (EQ)
  compare (Z) _ = (LT)
  compare _ (Z) = (GT)
  compare (SVarValue h1) (SVarValue h2) = (compare h1 h2)
  compare (SVarValue h1) (SVarType h2) = (error "differing namespace found in compare")
  compare (SVarType h1) (SVarValue h2) = (error "differing namespace found in compare")
  compare (SVarType h1) (SVarType h2) = (compare h1 h2)
