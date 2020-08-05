module SystemFDeBruijnBase where
import Data.List 

data Variable = Z | SVarValue Variable | SVarType Variable deriving(Eq)

data Value = Abstraction Term Type | TypeAbstraction Term deriving(Eq)

data Term = TmVariable Variable | TmApply Term Term | TmTypeApply Term Type | TmValue Value deriving(Eq)

data Type = TypVariable Variable | TypFunction Type Type | TypUniversal Type | Typ String deriving(Eq)


plus (Z) h = h
plus h (Z) = h
plus (SVarValue x1) x2 = (SVarValue (plus x1 x2))
plus (SVarType x1) x2 = (SVarType (plus x1 x2))

minus (Z) (Z) = (Z)
minus (Z) _ = (error "You cannot substract zero with a positive number")
minus result (Z) = result
minus (SVarValue h1) (SVarValue h2) = (minus h1 h2)
minus (SVarValue h1) (SVarType h2) = (SVarValue (minus h1 (SVarType h2)))
minus (SVarType h1) (SVarValue h2) = (SVarType (minus h1 (SVarValue h2)))
minus (SVarType h1) (SVarType h2) = (minus h1 h2)

generateHnatVarValue 0 c = c
generateHnatVarValue n c = (SVarValue (generateHnatVarValue (n - 1) c))

generateHnatVarType 0 c = c
generateHnatVarType n c = (SVarType (generateHnatVarType (n - 1) c))

termshiftHelpplus d c (TmVariable var) = if (var >= c) then (TmVariable (plus c (plus d (minus var c)))) else (TmVariable var)

typeshiftHelpplus d c (TypVariable var) = if (var >= c) then (TypVariable (plus c (plus d (minus var c)))) else (TypVariable var)

valueshiftplus d t = (valuemap (termshiftHelpplus d) (typeshiftHelpplus d) (Z) t)

termshiftplus d t = (termmap (termshiftHelpplus d) (typeshiftHelpplus d) (Z) t)

typeshiftplus d t = (typemap (typeshiftHelpplus d) (Z) t)

termshiftHelpminus d c (TmVariable var) = if (var >= c) then (TmVariable (minus var d)) else (TmVariable var)

typeshiftHelpminus d c (TypVariable var) = if (var >= c) then (TypVariable (minus var d)) else (TypVariable var)

valueshiftminus d t = (valuemap (termshiftHelpminus d) (typeshiftHelpminus d) (Z) t)

termshiftminus d t = (termmap (termshiftHelpminus d) (typeshiftHelpminus d) (Z) t)

typeshiftminus d t = (typemap (typeshiftHelpminus d) (Z) t)

valuemap onVarValue onVarType c (Abstraction t typ) = (Abstraction (termmap onVarValue onVarType (SVarValue c) t) (typemap onVarType c typ))
valuemap onVarValue onVarType c (TypeAbstraction typeTerm) = (TypeAbstraction (termmap onVarValue onVarType (SVarType c) typeTerm))

termmap onVarValue onVarType c (TmVariable var) = (onVarValue c (TmVariable var))
termmap onVarValue onVarType c (TmApply t1 t2) = (TmApply (termmap onVarValue onVarType c t1) (termmap onVarValue onVarType c t2))
termmap onVarValue onVarType c (TmTypeApply t1 t2) = (TmTypeApply (termmap onVarValue onVarType c t1) (typemap onVarType c t2))
termmap onVarValue onVarType c (TmValue v) = (TmValue (valuemap onVarValue onVarType c v))

typemap onVarType c (TypVariable var) = (onVarType c (TypVariable var))
typemap onVarType c (TypFunction from to) = (TypFunction (typemap onVarType c from) (typemap onVarType c to))
typemap onVarType c (TypUniversal on) = (TypUniversal (typemap onVarType (SVarType c) on))
typemap onVarType c (Typ string1) = (Typ string1)

valueTermSubstitute sub orig t = (valuemap (termSubstituteHelp sub) (\c x -> x) orig t)

valueTypeSubstitute sub orig t = (valuemap (\c x -> x) (typeSubstituteHelp sub) orig t)

termSubstituteHelp sub c (TmVariable var) = if (var == c) then (termshiftplus c sub) else (TmVariable var)

termTermSubstitute sub orig t = (termmap (termSubstituteHelp sub) (\c x -> x) orig t)

termTypeSubstitute sub orig t = (termmap (\c x -> x) (typeSubstituteHelp sub) orig t)

typeSubstituteHelp sub c (TypVariable var) = if (var == c) then (typeshiftplus c sub) else (TypVariable var)

typeTypeSubstitute sub orig t = (typemap (typeSubstituteHelp sub) orig t)

freeVariablesValue c (Abstraction t typ) = (nub (concat [(freeVariablesTerm (SVarValue c) t),(freeVariablesType c typ)]))
freeVariablesValue c (TypeAbstraction typeTerm) = (nub (concat [(freeVariablesTerm (SVarType c) typeTerm)]))

freeVariablesTerm c (TmVariable var) = if (var >= c) then [(minus var c)] else []
freeVariablesTerm c (TmApply t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesTerm c t2)]))
freeVariablesTerm c (TmTypeApply t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesType c t2)]))
freeVariablesTerm c (TmValue v) = (nub (concat [(freeVariablesValue c v)]))

freeVariablesType c (TypVariable var) = if (var >= c) then [(minus var c)] else []
freeVariablesType c (TypFunction from to) = (nub (concat [(freeVariablesType c from),(freeVariablesType c to)]))
freeVariablesType c (TypUniversal on) = (nub (concat [(freeVariablesType (SVarType c) on)]))
freeVariablesType c (Typ string1) = (nub (concat [[]]))
instance Ord Variable where
  compare (Z) (Z) = (EQ)
  compare (Z) _ = (LT)
  compare _ (Z) = (GT)
  compare (SVarValue h1) (SVarValue h2) = (compare h1 h2)
  compare (SVarValue h1) (SVarType h2) = (error "differing namespace found in compare")
  compare (SVarType h1) (SVarValue h2) = (error "differing namespace found in compare")
  compare (SVarType h1) (SVarType h2) = (compare h1 h2)
