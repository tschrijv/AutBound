module LambdaBase where
import Data.List 

data Variable = Z | SVarValue Variable deriving(Show, Eq)

data Value = Abstraction Term deriving(Show, Eq)

data Term = TmVariable Variable | TmValue Value | TmApply Term Term deriving(Show, Eq)


plus (Z) h = h
plus h (Z) = h
plus (SVarValue x1) x2 = (SVarValue (plus x1 x2))

minus (Z) (Z) = (Z)
minus (Z) _ = (error "You cannot substract zero with a positive number")
minus result (Z) = result
minus (SVarValue h1) (SVarValue h2) = (minus h1 h2)

generateHnatVarValue 0 c = c
generateHnatVarValue n c = (SVarValue (generateHnatVarValue (n - 1) c))

termshiftHelpplus d c (TmVariable var) = if (var >= c) then (TmVariable (plus c (plus d (minus var c)))) else (TmVariable var)

valueshiftplus d t = (valuemap (termshiftHelpplus d) (Z) t)

termshiftplus d t = (termmap (termshiftHelpplus d) (Z) t)

termshiftHelpminus d c (TmVariable var) = if (var >= c) then (TmVariable (minus var d)) else (TmVariable var)

valueshiftminus d t = (valuemap (termshiftHelpminus d) (Z) t)

termshiftminus d t = (termmap (termshiftHelpminus d) (Z) t)

valuemap onVarValue c (Abstraction x) = (Abstraction (termmap onVarValue (SVarValue c) x))

termmap onVarValue c (TmVariable var) = (onVarValue c (TmVariable var))
termmap onVarValue c (TmValue v) = (TmValue (valuemap onVarValue c v))
termmap onVarValue c (TmApply f a) = (TmApply (termmap onVarValue c f) (termmap onVarValue c a))

valueTermSubstitute sub orig t = (valuemap (termSubstituteHelp sub) orig t)

termSubstituteHelp sub c (TmVariable var) = if (var == c) then (termshiftplus c sub) else (TmVariable var)

termTermSubstitute sub orig t = (termmap (termSubstituteHelp sub) orig t)

freeVariablesValue c (Abstraction x) = (nub (concat [(freeVariablesTerm (SVarValue c) x)]))

freeVariablesTerm c (TmVariable var) = if (var >= c) then [(minus var c)] else []
freeVariablesTerm c (TmValue v) = (nub (concat [(freeVariablesValue c v)]))
freeVariablesTerm c (TmApply f a) = (nub (concat [(freeVariablesTerm c f),(freeVariablesTerm c a)]))
instance Ord Variable where
  compare (Z) (Z) = (EQ)
  compare (Z) _ = (LT)
  compare _ (Z) = (GT)
  compare (SVarValue h1) (SVarValue h2) = (compare h1 h2)
