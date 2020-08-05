module SystemFStringBase where
import Data.List 

data Variable = SVarValue String | SVarType String deriving(Eq)

data Value = Abstraction Variable Term Type | TypeAbstraction Variable Term deriving(Eq)

data Term = TmVariable Variable | TmApply Term Term | TmTypeApply Term Type | TmValue Value deriving(Eq)

data Type = TypVariable Variable | TypFunction Type Type | TypUniversal Variable Type | Typ String deriving(Eq)


valuemap onVarValue onVarType c (Abstraction b t typ) = (Abstraction b (termmap onVarValue onVarType (concat [[b],c]) t) (typemap onVarType c typ))
valuemap onVarValue onVarType c (TypeAbstraction b typeTerm) = (TypeAbstraction b (termmap onVarValue onVarType (concat [[b],c]) typeTerm))

termmap onVarValue onVarType c (TmVariable var) = (onVarValue c (TmVariable var))
termmap onVarValue onVarType c (TmApply t1 t2) = (TmApply (termmap onVarValue onVarType c t1) (termmap onVarValue onVarType c t2))
termmap onVarValue onVarType c (TmTypeApply t1 t2) = (TmTypeApply (termmap onVarValue onVarType c t1) (typemap onVarType c t2))
termmap onVarValue onVarType c (TmValue v) = (TmValue (valuemap onVarValue onVarType c v))

typemap onVarType c (TypVariable var) = (onVarType c (TypVariable var))
typemap onVarType c (TypFunction from to) = (TypFunction (typemap onVarType c from) (typemap onVarType c to))
typemap onVarType c (TypUniversal b on) = (TypUniversal b (typemap onVarType (concat [[b],c]) on))
typemap onVarType c (Typ string1) = (Typ string1)

freeVariablesValue c (Abstraction b t typ) = (nub (concat [(freeVariablesTerm (concat [[b],c]) t),(freeVariablesType c typ)]))
freeVariablesValue c (TypeAbstraction b typeTerm) = (nub (concat [(freeVariablesTerm (concat [[b],c]) typeTerm)]))

freeVariablesTerm c (TmVariable var) = if (elem var c) then [] else [var]
freeVariablesTerm c (TmApply t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesTerm c t2)]))
freeVariablesTerm c (TmTypeApply t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesType c t2)]))
freeVariablesTerm c (TmValue v) = (nub (concat [(freeVariablesValue c v)]))

freeVariablesType c (TypVariable var) = if (elem var c) then [] else [var]
freeVariablesType c (TypFunction from to) = (nub (concat [(freeVariablesType c from),(freeVariablesType c to)]))
freeVariablesType c (TypUniversal b on) = (nub (concat [(freeVariablesType (concat [[b],c]) on)]))
freeVariablesType c (Typ string1) = (nub (concat [[]]))

valueVarReplace orig sub (Abstraction b t typ) = (Abstraction (freshVarValue b (concat [[sub],(freeVariablesTerm [] t),(freeVariablesType [] typ)])) (termVarReplace orig sub (termVarReplace b (freshVarValue b (concat [[sub],(freeVariablesTerm [] t),(freeVariablesType [] typ)])) t)) (typeVarReplace orig sub (typeVarReplace b (freshVarValue b (concat [[sub],(freeVariablesTerm [] t),(freeVariablesType [] typ)])) typ)))
valueVarReplace orig sub (TypeAbstraction b typeTerm) = (TypeAbstraction (freshVarType b (concat [[sub],(freeVariablesTerm [] typeTerm)])) (termVarReplace orig sub (termVarReplace b (freshVarType b (concat [[sub],(freeVariablesTerm [] typeTerm)])) typeTerm)))

valueTermSubstitute orig sub (Abstraction b t typ) = (Abstraction (freshVarValue b (concat [(freeVariablesTerm [] sub),(freeVariablesTerm [] t),(freeVariablesType [] typ)])) (termTermSubstitute orig sub (termVarReplace b (freshVarValue b (concat [(freeVariablesTerm [] sub),(freeVariablesTerm [] t),(freeVariablesType [] typ)])) t)) typ)
valueTermSubstitute orig sub (TypeAbstraction b typeTerm) = (TypeAbstraction (freshVarType b (concat [(freeVariablesTerm [] sub),(freeVariablesTerm [] typeTerm)])) (termTermSubstitute orig sub (termVarReplace b (freshVarType b (concat [(freeVariablesTerm [] sub),(freeVariablesTerm [] typeTerm)])) typeTerm)))

valueTypeSubstitute orig sub (Abstraction b t typ) = (Abstraction (freshVarValue b (concat [(freeVariablesType [] sub),(freeVariablesTerm [] t),(freeVariablesType [] typ)])) (termTypeSubstitute orig sub (termVarReplace b (freshVarValue b (concat [(freeVariablesType [] sub),(freeVariablesTerm [] t),(freeVariablesType [] typ)])) t)) (typeTypeSubstitute orig sub (typeVarReplace b (freshVarValue b (concat [(freeVariablesType [] sub),(freeVariablesTerm [] t),(freeVariablesType [] typ)])) typ)))
valueTypeSubstitute orig sub (TypeAbstraction b typeTerm) = (TypeAbstraction (freshVarType b (concat [(freeVariablesType [] sub),(freeVariablesTerm [] typeTerm)])) (termTypeSubstitute orig sub (termVarReplace b (freshVarType b (concat [(freeVariablesType [] sub),(freeVariablesTerm [] typeTerm)])) typeTerm)))

termVarReplace orig sub (TmVariable var) = if (var == orig) then (TmVariable sub) else (TmVariable var)
termVarReplace orig sub (TmApply t1 t2) = (TmApply (termVarReplace orig sub t1) (termVarReplace orig sub t2))
termVarReplace orig sub (TmTypeApply t1 t2) = (TmTypeApply (termVarReplace orig sub t1) (typeVarReplace orig sub t2))
termVarReplace orig sub (TmValue v) = (TmValue (valueVarReplace orig sub v))

termTermSubstitute orig sub (TmVariable var) = if (var == orig) then sub else (TmVariable var)
termTermSubstitute orig sub (TmApply t1 t2) = (TmApply (termTermSubstitute orig sub t1) (termTermSubstitute orig sub t2))
termTermSubstitute orig sub (TmTypeApply t1 t2) = (TmTypeApply (termTermSubstitute orig sub t1) t2)
termTermSubstitute orig sub (TmValue v) = (TmValue (valueTermSubstitute orig sub v))

termTypeSubstitute orig sub (TmVariable var) = (TmVariable var)
termTypeSubstitute orig sub (TmApply t1 t2) = (TmApply (termTypeSubstitute orig sub t1) (termTypeSubstitute orig sub t2))
termTypeSubstitute orig sub (TmTypeApply t1 t2) = (TmTypeApply (termTypeSubstitute orig sub t1) (typeTypeSubstitute orig sub t2))
termTypeSubstitute orig sub (TmValue v) = (TmValue (valueTypeSubstitute orig sub v))

typeVarReplace orig sub (TypVariable var) = if (var == orig) then (TypVariable sub) else (TypVariable var)
typeVarReplace orig sub (TypFunction from to) = (TypFunction (typeVarReplace orig sub from) (typeVarReplace orig sub to))
typeVarReplace orig sub (TypUniversal b on) = (TypUniversal (freshVarType b (concat [[sub],(freeVariablesType [] on)])) (typeVarReplace orig sub (typeVarReplace b (freshVarType b (concat [[sub],(freeVariablesType [] on)])) on)))
typeVarReplace orig sub (Typ string1) = (Typ string1)

typeTypeSubstitute orig sub (TypVariable var) = if (var == orig) then sub else (TypVariable var)
typeTypeSubstitute orig sub (TypFunction from to) = (TypFunction (typeTypeSubstitute orig sub from) (typeTypeSubstitute orig sub to))
typeTypeSubstitute orig sub (TypUniversal b on) = (TypUniversal (freshVarType b (concat [(freeVariablesType [] sub),(freeVariablesType [] on)])) (typeTypeSubstitute orig sub (typeVarReplace b (freshVarType b (concat [(freeVariablesType [] sub),(freeVariablesType [] on)])) on)))
typeTypeSubstitute orig sub (Typ string1) = (Typ string1)

boundVariablesValue c (Abstraction b t typ) = (nub (concat [c,[b],[]]))
boundVariablesValue c (TypeAbstraction b typeTerm) = (nub (concat [c,[b],[]]))

boundVariablesTerm c (TmVariable var) = []
boundVariablesTerm c (TmApply t1 t2) = (nub (concat [c,[]]))
boundVariablesTerm c (TmTypeApply t1 t2) = (nub (concat [c,[]]))
boundVariablesTerm c (TmValue v) = (nub (concat [c,[]]))

boundVariablesType c (TypVariable var) = []
boundVariablesType c (TypFunction from to) = (nub (concat [c,[]]))
boundVariablesType c (TypUniversal b on) = (nub (concat [c,[b],[]]))
boundVariablesType c (Typ string1) = (nub (concat [c,[]]))

freshVarValue x b = if not (x `elem` b) then x else head [SVarValue ('v' : show n) | n <- [0..], not (SVarValue ('v' : show n) `elem` b)]
freshVarType x b = if not (x `elem` b) then x else head [SVarType ('v' : show n) | n <- [0..], not (SVarType ('v' : show n) `elem` b)]