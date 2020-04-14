module FCoBase where
import Data.List 

data Variable = Z | STermVar Variable | STypeVar Variable deriving(Show, Eq)

data Term = TmVar Variable | TmAbs Term Type | TmApp Term Term | TmTApp Term Type | TmTAbs Term | TmTop | TmTuple Term Term | TmInt Int | TmCast Coercion Term deriving(Show, Eq)

data Type = TyVar Variable | TyArr Type Type | TyAll Type | TyInt | TyTop | TyProd Type Type deriving(Show, Eq)

data Coercion = CoId | CoTrans Coercion Coercion | CoTop Type | CoBot Type | CoArrow Coercion Coercion | CoTuple Coercion Coercion | CoProj1 Type | CoProj2 Type | CoAll Coercion | CoDistArrow | CoTopArrow | CoTopAll | CoDistAll deriving(Show, Eq)


plus (Z) h = h
plus h (Z) = h
plus x1 (STermVar x2) = (STermVar (plus x1 x2))
plus x1 (STypeVar x2) = (STypeVar (plus x1 x2))

minus (Z) (Z) = (Z)
minus (Z) _ = (error "You cannot substract zero with a positive number")
minus result (Z) = result
minus (STermVar h1) (STermVar h2) = (minus h1 h2)
minus (STermVar h1) (STypeVar h2) = (error "differing namespace found in minus")
minus (STypeVar h1) (STermVar h2) = (error "differing namespace found in minus")
minus (STypeVar h1) (STypeVar h2) = (minus h1 h2)

generateHnatTermVar 0 c = c
generateHnatTermVar n c = (STermVar (generateHnatTermVar (n - 1) c))

generateHnatTypeVar 0 c = c
generateHnatTypeVar n c = (STypeVar (generateHnatTypeVar (n - 1) c))

termshiftHelpplus d c (TmVar var) = if (var >= c) then (TmVar (plus var d)) else (TmVar var)

typeshiftHelpplus d c (TyVar var) = if (var >= c) then (TyVar (plus var d)) else (TyVar var)

termshiftplus d t = (termmap (termshiftHelpplus d) (typeshiftHelpplus d) (Z) t)

typeshiftplus d t = (typemap (typeshiftHelpplus d) (Z) t)

coercionshiftplus d t = (coercionmap (typeshiftHelpplus d) (Z) t)

termshiftHelpminus d c (TmVar var) = if (var >= c) then (TmVar (minus var d)) else (TmVar var)

typeshiftHelpminus d c (TyVar var) = if (var >= c) then (TyVar (minus var d)) else (TyVar var)

termshiftminus d t = (termmap (termshiftHelpminus d) (typeshiftHelpminus d) (Z) t)

typeshiftminus d t = (typemap (typeshiftHelpminus d) (Z) t)

coercionshiftminus d t = (coercionmap (typeshiftHelpminus d) (Z) t)

termmap onTermVar onTypeVar c (TmVar var) = (onTermVar c (TmVar var))
termmap onTermVar onTypeVar c (TmAbs x t) = (TmAbs (termmap onTermVar onTypeVar (STermVar c) x) (typemap onTypeVar c t))
termmap onTermVar onTypeVar c (TmApp t1 t2) = (TmApp (termmap onTermVar onTypeVar c t1) (termmap onTermVar onTypeVar c t2))
termmap onTermVar onTypeVar c (TmTApp t1 t) = (TmTApp (termmap onTermVar onTypeVar c t1) (typemap onTypeVar c t))
termmap onTermVar onTypeVar c (TmTAbs t1) = (TmTAbs (termmap onTermVar onTypeVar (STypeVar c) t1))
termmap onTermVar onTypeVar c (TmTop) = (TmTop)
termmap onTermVar onTypeVar c (TmTuple e1 e2) = (TmTuple (termmap onTermVar onTypeVar c e1) (termmap onTermVar onTypeVar c e2))
termmap onTermVar onTypeVar c (TmInt int1) = (TmInt int1)
termmap onTermVar onTypeVar c (TmCast co e) = (TmCast (coercionmap onTypeVar c co) (termmap onTermVar onTypeVar c e))

typemap onTypeVar c (TyVar var) = (onTypeVar c (TyVar var))
typemap onTypeVar c (TyArr t1 t2) = (TyArr (typemap onTypeVar c t1) (typemap onTypeVar c t2))
typemap onTypeVar c (TyAll t1) = (TyAll (typemap onTypeVar (STypeVar c) t1))
typemap onTypeVar c (TyInt) = (TyInt)
typemap onTypeVar c (TyTop) = (TyTop)
typemap onTypeVar c (TyProd t1 t2) = (TyProd (typemap onTypeVar c t1) (typemap onTypeVar c t2))

coercionmap onTypeVar c (CoId) = (CoId)
coercionmap onTypeVar c (CoTrans co1 co2) = (CoTrans (coercionmap onTypeVar c co1) (coercionmap onTypeVar c co2))
coercionmap onTypeVar c (CoTop ty) = (CoTop (typemap onTypeVar c ty))
coercionmap onTypeVar c (CoBot ty) = (CoBot (typemap onTypeVar c ty))
coercionmap onTypeVar c (CoArrow co1 co2) = (CoArrow (coercionmap onTypeVar c co1) (coercionmap onTypeVar c co2))
coercionmap onTypeVar c (CoTuple co1 co2) = (CoTuple (coercionmap onTypeVar c co1) (coercionmap onTypeVar c co2))
coercionmap onTypeVar c (CoProj1 ty2) = (CoProj1 (typemap onTypeVar c ty2))
coercionmap onTypeVar c (CoProj2 ty1) = (CoProj2 (typemap onTypeVar c ty1))
coercionmap onTypeVar c (CoAll co1) = (CoAll (coercionmap onTypeVar c co1))
coercionmap onTypeVar c (CoDistArrow) = (CoDistArrow)
coercionmap onTypeVar c (CoTopArrow) = (CoTopArrow)
coercionmap onTypeVar c (CoTopAll) = (CoTopAll)
coercionmap onTypeVar c (CoDistAll) = (CoDistAll)

termSubstituteHelp sub c (TmVar var) = if (var == c) then (termshiftplus c sub) else (TmVar var)

termTermSubstitute sub orig t = (termmap (termSubstituteHelp sub) (\c x -> x) orig t)

termTypeSubstitute sub orig t = (termmap (\c x -> x) (typeSubstituteHelp sub) orig t)

typeSubstituteHelp sub c (TyVar var) = if (var == c) then (typeshiftplus c sub) else (TyVar var)

typeTypeSubstitute sub orig t = (typemap (typeSubstituteHelp sub) orig t)

coercionTypeSubstitute sub orig t = (coercionmap (typeSubstituteHelp sub) orig t)

freeVariablesTerm c (TmVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesTerm c (TmAbs x t) = (nub (concat [(freeVariablesTerm (STermVar c) x),(freeVariablesType c t)]))
freeVariablesTerm c (TmApp t1 t2) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesTerm c t2)]))
freeVariablesTerm c (TmTApp t1 t) = (nub (concat [(freeVariablesTerm c t1),(freeVariablesType c t)]))
freeVariablesTerm c (TmTAbs t1) = (nub (concat [(freeVariablesTerm (STypeVar c) t1)]))
freeVariablesTerm c (TmTop) = (nub (concat [[]]))
freeVariablesTerm c (TmTuple e1 e2) = (nub (concat [(freeVariablesTerm c e1),(freeVariablesTerm c e2)]))
freeVariablesTerm c (TmInt int1) = (nub (concat [[]]))
freeVariablesTerm c (TmCast co e) = (nub (concat [(freeVariablesCoercion c co),(freeVariablesTerm c e)]))

freeVariablesType c (TyVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesType c (TyArr t1 t2) = (nub (concat [(freeVariablesType c t1),(freeVariablesType c t2)]))
freeVariablesType c (TyAll t1) = (nub (concat [(freeVariablesType (STypeVar c) t1)]))
freeVariablesType c (TyInt) = (nub (concat [[]]))
freeVariablesType c (TyTop) = (nub (concat [[]]))
freeVariablesType c (TyProd t1 t2) = (nub (concat [(freeVariablesType c t1),(freeVariablesType c t2)]))

freeVariablesCoercion c (CoId) = (nub (concat [[]]))
freeVariablesCoercion c (CoTrans co1 co2) = (nub (concat [(freeVariablesCoercion c co1),(freeVariablesCoercion c co2)]))
freeVariablesCoercion c (CoTop ty) = (nub (concat [(freeVariablesType c ty)]))
freeVariablesCoercion c (CoBot ty) = (nub (concat [(freeVariablesType c ty)]))
freeVariablesCoercion c (CoArrow co1 co2) = (nub (concat [(freeVariablesCoercion c co1),(freeVariablesCoercion c co2)]))
freeVariablesCoercion c (CoTuple co1 co2) = (nub (concat [(freeVariablesCoercion c co1),(freeVariablesCoercion c co2)]))
freeVariablesCoercion c (CoProj1 ty2) = (nub (concat [(freeVariablesType c ty2)]))
freeVariablesCoercion c (CoProj2 ty1) = (nub (concat [(freeVariablesType c ty1)]))
freeVariablesCoercion c (CoAll co1) = (nub (concat [(freeVariablesCoercion c co1)]))
freeVariablesCoercion c (CoDistArrow) = (nub (concat [[]]))
freeVariablesCoercion c (CoTopArrow) = (nub (concat [[]]))
freeVariablesCoercion c (CoTopAll) = (nub (concat [[]]))
freeVariablesCoercion c (CoDistAll) = (nub (concat [[]]))
instance Ord Variable where
  compare (Z) (Z) = (EQ)
  compare (Z) _ = (LT)
  compare _ (Z) = (GT)
  compare (STermVar h1) (STermVar h2) = (compare h1 h2)
  compare (STermVar h1) (STypeVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (STermVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (STypeVar h2) = (compare h1 h2)
