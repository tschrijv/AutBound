module SystemFBase where
import Data.List

data Variable = Z | STermVar Variable | STypeVar Variable deriving(Show, Eq)

data Term = TmVar Variable | TmAbs Term Type | TmApp Term Term | TmTApp Term Type | TmTAbs Term deriving(Show, Eq)

data Type = TyVar Variable | TyArr Type Type | TyAll Type | TyBase deriving(Show, Eq)


plus (Z) h = h
plus h (Z) = h
plus (STermVar x1) x2 = (STermVar (plus x1 x2))
plus (STypeVar x1) x2 = (STypeVar (plus x1 x2))

minus (Z) (Z) = (Z)
minus (Z) _ = (error "You cannot substract zero with a positive number")
minus result (Z) = result
minus (STermVar h1) (STermVar h2) = (minus h1 h2)
minus (STermVar h1) (STypeVar h2) = (STermVar (minus h1 (STypeVar h2)))
minus (STypeVar h1) (STermVar h2) = (STypeVar (minus h1 (STermVar h2)))
minus (STypeVar h1) (STypeVar h2) = (minus h1 h2)

generateHnatTermVar 0 c = c
generateHnatTermVar n c = (STermVar (generateHnatTermVar (n - 1) c))

generateHnatTypeVar 0 c = c
generateHnatTypeVar n c = (STypeVar (generateHnatTypeVar (n - 1) c))

termshiftHelpplus d c (TmVar var) = if (var >= c) then (TmVar (plus c (plus d (minus var c)))) else (TmVar var)

typeshiftHelpplus d c (TyVar var) = if (var >= c) then (TyVar (plus c (plus d (minus var c)))) else (TyVar var)

termshiftplus d t = (termmap (termshiftHelpplus d) (typeshiftHelpplus d) (Z) t)

typeshiftplus d t = (typemap (typeshiftHelpplus d) (Z) t)

termshiftHelpminus d c (TmVar var) = if (var >= c) then (TmVar (minus var d)) else (TmVar var)

typeshiftHelpminus d c (TyVar var) = if (var >= c) then (TyVar (minus var d)) else (TyVar var)

termshiftminus d t = (termmap (termshiftHelpminus d) (typeshiftHelpminus d) (Z) t)

typeshiftminus d t = (typemap (typeshiftHelpminus d) (Z) t)

termmap onTermVar onTypeVar c (TmVar var) = (onTermVar c (TmVar var))
termmap onTermVar onTypeVar c (TmAbs x t) = (TmAbs (termmap onTermVar onTypeVar (STermVar c) x) (typemap onTypeVar c t))
termmap onTermVar onTypeVar c (TmApp t1 t2) = (TmApp (termmap onTermVar onTypeVar c t1) (termmap onTermVar onTypeVar c t2))
termmap onTermVar onTypeVar c (TmTApp t1 t) = (TmTApp (termmap onTermVar onTypeVar c t1) (typemap onTypeVar c t))
termmap onTermVar onTypeVar c (TmTAbs t1) = (TmTAbs (termmap onTermVar onTypeVar (STypeVar c) t1))

typemap onTypeVar c (TyVar var) = (onTypeVar c (TyVar var))
typemap onTypeVar c (TyArr t1 t2) = (TyArr (typemap onTypeVar c t1) (typemap onTypeVar c t2))
typemap onTypeVar c (TyAll t1) = (TyAll (typemap onTypeVar (STypeVar c) t1))
typemap onTypeVar c (TyBase) = (TyBase)

termSubstituteHelp sub c (TmVar var) = if (var == c) then (termshiftplus c sub) else (TmVar var)

termTermSubstitute sub orig t = (termmap (termSubstituteHelp sub) (\c x -> x) orig t)

termTypeSubstitute sub orig t = (termmap (\c x -> x) (typeSubstituteHelp sub) orig t)

typeSubstituteHelp sub c (TyVar var) = if (var == c) then (typeshiftplus c sub) else (TyVar var)

typeTypeSubstitute sub orig t = (typemap (typeSubstituteHelp sub) orig t)

freeVariablesTerm c (TmVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesTerm c (TmAbs x t) = (nub (concat [(freeVariablesTerm (STermVar c) x),(freeVariablesType c t)]))
freeVariablesTerm c (TmApp t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesTerm c t2)]))
freeVariablesTerm c (TmTApp t1 t) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesType c t)]))
freeVariablesTerm c (TmTAbs t1) = (nub (concat [(freeVariablesTerm (STypeVar c) t1)]))

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
