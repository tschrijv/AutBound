module SystemFBase where
import Data.List 

data Variable = Z | STermVar Variable | STypeVar Variable deriving(Show, Eq)

data Term = TmVar Variable | TmAbs Term Type | TmApp Term Term | TmTApp Term Type | TmTAbs Term deriving(Show, Eq)

data Type = TyVar Variable | TyArr Type Type | TyAll Type | TyBase deriving(Show, Eq)


-- Add two Variables.
plus :: Variable -> Variable -> Variable
plus (Z) h = h
plus h (Z) = h
plus (STermVar x1) x2 = (STermVar (plus x1 x2))
plus (STypeVar x1) x2 = (STypeVar (plus x1 x2))

-- Substract the second Variable from the first. The first Variable has to
-- be greater than the second one.
minus :: Variable -> Variable -> Variable
minus (Z) (Z) = (Z)
minus (Z) _ = (error "You cannot substract zero with a positive number")
minus result (Z) = result
minus (STermVar h1) (STermVar h2) = (minus h1 h2)
minus (STermVar h1) (STypeVar h2) = (STermVar (minus h1 (STypeVar h2)))
minus (STypeVar h1) (STermVar h2) = (STypeVar (minus h1 (STermVar h2)))
minus (STypeVar h1) (STypeVar h2) = (minus h1 h2)

-- Apply STermVar n times to the second argument c.
generateHnatTermVar :: Int -> Variable -> Variable
generateHnatTermVar 0 c = c
generateHnatTermVar n c = (STermVar (generateHnatTermVar (n - 1) c))

-- Apply STypeVar n times to the second argument c.
generateHnatTypeVar :: Int -> Variable -> Variable
generateHnatTypeVar 0 c = c
generateHnatTypeVar n c = (STypeVar (generateHnatTypeVar (n - 1) c))

-- Perform the shift operation on one Term with the TmVar constructor.
termshiftHelpplus :: Variable -> Variable -> Term -> Term
termshiftHelpplus d c (TmVar var) = if (var >= c) then (TmVar (plus c (plus d (minus var c)))) else (TmVar var)

-- Perform the shift operation on one Type with the TyVar constructor.
typeshiftHelpplus :: Variable -> Variable -> Type -> Type
typeshiftHelpplus d c (TyVar var) = if (var >= c) then (TyVar (plus c (plus d (minus var c)))) else (TyVar var)

-- Perform the shift operation on a Term.
termshiftplus :: Variable -> Term -> Term
termshiftplus d t = (termmap (termshiftHelpplus d) (typeshiftHelpplus d) (Z) t)

-- Perform the shift operation on a Type.
typeshiftplus :: Variable -> Type -> Type
typeshiftplus d t = (typemap (typeshiftHelpplus d) (Z) t)

-- Perform the shift operation on one Term with the TmVar constructor.
termshiftHelpminus :: Variable -> Variable -> Term -> Term
termshiftHelpminus d c (TmVar var) = if (var >= c) then (TmVar (minus var d)) else (TmVar var)

-- Perform the shift operation on one Type with the TyVar constructor.
typeshiftHelpminus :: Variable -> Variable -> Type -> Type
typeshiftHelpminus d c (TyVar var) = if (var >= c) then (TyVar (minus var d)) else (TyVar var)

-- Perform the shift operation on a Term.
termshiftminus :: Variable -> Term -> Term
termshiftminus d t = (termmap (termshiftHelpminus d) (typeshiftHelpminus d) (Z) t)

-- Perform the shift operation on a Type.
typeshiftminus :: Variable -> Type -> Type
typeshiftminus d t = (typemap (typeshiftHelpminus d) (Z) t)

-- Return the Term where onTermVar, onTypeVar are applied to each
-- Term, Type in the given Term respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
termmap :: (Variable -> Term -> Term) -> (Variable -> Type -> Type) -> Variable -> Term -> Term
termmap onTermVar onTypeVar c (TmVar var) = (onTermVar c (TmVar var))
termmap onTermVar onTypeVar c (TmAbs x t) = (TmAbs (termmap onTermVar onTypeVar (STermVar c) x) (typemap onTypeVar c t))
termmap onTermVar onTypeVar c (TmApp t1 t2) = (TmApp (termmap onTermVar onTypeVar c t1) (termmap onTermVar onTypeVar c t2))
termmap onTermVar onTypeVar c (TmTApp t1 t) = (TmTApp (termmap onTermVar onTypeVar c t1) (typemap onTypeVar c t))
termmap onTermVar onTypeVar c (TmTAbs t1) = (TmTAbs (termmap onTermVar onTypeVar (STypeVar c) t1))

-- Return the Type where onTypeVar is applied to each
-- Type in the given Type respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied function.
typemap :: (Variable -> Type -> Type) -> Variable -> Type -> Type
typemap onTypeVar c (TyVar var) = (onTypeVar c (TyVar var))
typemap onTypeVar c (TyArr t1 t2) = (TyArr (typemap onTypeVar c t1) (typemap onTypeVar c t2))
typemap onTypeVar c (TyAll t1) = (TyAll (typemap onTypeVar (STypeVar c) t1))
typemap onTypeVar c (TyBase) = (TyBase)

-- Perform one substitution step on a Term with the TmVar constructor.
termSubstituteHelp :: Term -> Variable -> Term -> Term
termSubstituteHelp sub c (TmVar var) = if (var == c) then (termshiftplus c sub) else (TmVar var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Term in the given Term.
termTermSubstitute :: Term -> Variable -> Term -> Term
termTermSubstitute sub orig t = (termmap (termSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Type in the given Term.
termTypeSubstitute :: Type -> Variable -> Term -> Term
termTypeSubstitute sub orig t = (termmap (\c x -> x) (typeSubstituteHelp sub) orig t)

-- Perform one substitution step on a Type with the TyVar constructor.
typeSubstituteHelp :: Type -> Variable -> Type -> Type
typeSubstituteHelp sub c (TyVar var) = if (var == c) then (typeshiftplus c sub) else (TyVar var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Type in the given Type.
typeTypeSubstitute :: Type -> Variable -> Type -> Type
typeTypeSubstitute sub orig t = (typemap (typeSubstituteHelp sub) orig t)

-- Return a list of the free variables of the given Term.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesTerm :: Variable -> Term -> [Variable]
freeVariablesTerm c (TmVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesTerm c (TmAbs x t) = (nub (concat [(freeVariablesTerm (STermVar c) x),(freeVariablesType c t)]))
freeVariablesTerm c (TmApp t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesTerm c t2)]))
freeVariablesTerm c (TmTApp t1 t) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesType c t)]))
freeVariablesTerm c (TmTAbs t1) = (nub (concat [(freeVariablesTerm (STypeVar c) t1)]))

-- Return a list of the free variables of the given Type.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesType :: Variable -> Type -> [Variable]
freeVariablesType c (TyVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesType c (TyArr t1 t2) = (nub (concat [(freeVariablesType c t1),(freeVariablesType c t2)]))
freeVariablesType c (TyAll t1) = (nub (concat [(freeVariablesType (STypeVar c) t1)]))
freeVariablesType c (TyBase) = (nub (concat [[]]))
instance Ord Variable where
  compare (Z) (Z) = (EQ)
  compare (Z) _ = (LT)
  compare _ (Z) = (GT)
  compare (STermVar h1) (STermVar h2) = (compare h1 h2)
  compare (STermVar h1) (STypeVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (STermVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (STypeVar h2) = (compare h1 h2)
