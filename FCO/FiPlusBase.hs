module FiPlusBase where
import Data.List 

data Variable = Z | STermVar Variable | STypeVar Variable deriving(Show, Eq)

data FiTerm = TmVar Variable | TmInt Int | TmTop | TmAbs FiTerm FiType | TmApp FiTerm FiTerm | TmMerge FiTerm FiTerm | TmAnn FiTerm FiType | TmRecord FiTerm String | TmProj FiTerm String | TmAll FiType FiTerm | TypeApp FiTerm FiType deriving(Show, Eq)

data FiType = TyTop | TyBot | TyInt | TyArr FiType FiType | TyAnd FiType FiType | TyRecord FiType String | TyVar Variable | TyAll FiType FiType deriving(Show, Eq)


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

fiTermshiftHelpplus d c (TmVar var) = if (var >= c) then (TmVar (plus var d)) else (TmVar var)

fiTypeshiftHelpplus d c (TyVar var) = if (var >= c) then (TyVar (plus var d)) else (TyVar var)

fiTermshiftplus d t = (fiTermmap (fiTermshiftHelpplus d) (fiTypeshiftHelpplus d) (Z) t)

fiTypeshiftplus d t = (fiTypemap (fiTypeshiftHelpplus d) (Z) t)

fiTermshiftHelpminus d c (TmVar var) = if (var >= c) then (TmVar (minus var d)) else (TmVar var)

fiTypeshiftHelpminus d c (TyVar var) = if (var >= c) then (TyVar (minus var d)) else (TyVar var)

fiTermshiftminus d t = (fiTermmap (fiTermshiftHelpminus d) (fiTypeshiftHelpminus d) (Z) t)

fiTypeshiftminus d t = (fiTypemap (fiTypeshiftHelpminus d) (Z) t)

fiTermmap onTermVar onTypeVar c (TmVar var) = (onTermVar c (TmVar var))
fiTermmap onTermVar onTypeVar c (TmInt int1) = (TmInt int1)
fiTermmap onTermVar onTypeVar c (TmTop) = (TmTop)
fiTermmap onTermVar onTypeVar c (TmAbs t ty) = (TmAbs (fiTermmap onTermVar onTypeVar (STermVar c) t) (fiTypemap onTypeVar c ty))
fiTermmap onTermVar onTypeVar c (TmApp t1 t2) = (TmApp (fiTermmap onTermVar onTypeVar c t1) (fiTermmap onTermVar onTypeVar c t2))
fiTermmap onTermVar onTypeVar c (TmMerge t1 t2) = (TmMerge (fiTermmap onTermVar onTypeVar c t1) (fiTermmap onTermVar onTypeVar c t2))
fiTermmap onTermVar onTypeVar c (TmAnn t ty) = (TmAnn (fiTermmap onTermVar onTypeVar c t) (fiTypemap onTypeVar c ty))
fiTermmap onTermVar onTypeVar c (TmRecord t string1) = (TmRecord (fiTermmap onTermVar onTypeVar c t) string1)
fiTermmap onTermVar onTypeVar c (TmProj t string1) = (TmProj (fiTermmap onTermVar onTypeVar c t) string1)
fiTermmap onTermVar onTypeVar c (TmAll ty t) = (TmAll (fiTypemap onTypeVar c ty) (fiTermmap onTermVar onTypeVar (STypeVar c) t))
fiTermmap onTermVar onTypeVar c (TypeApp t ty) = (TypeApp (fiTermmap onTermVar onTypeVar c t) (fiTypemap onTypeVar c ty))

fiTypemap onTypeVar c (TyTop) = (TyTop)
fiTypemap onTypeVar c (TyBot) = (TyBot)
fiTypemap onTypeVar c (TyInt) = (TyInt)
fiTypemap onTypeVar c (TyArr ty1 ty2) = (TyArr (fiTypemap onTypeVar c ty1) (fiTypemap onTypeVar c ty2))
fiTypemap onTypeVar c (TyAnd ty1 ty2) = (TyAnd (fiTypemap onTypeVar c ty1) (fiTypemap onTypeVar c ty2))
fiTypemap onTypeVar c (TyRecord ty string1) = (TyRecord (fiTypemap onTypeVar c ty) string1)
fiTypemap onTypeVar c (TyVar var) = (onTypeVar c (TyVar var))
fiTypemap onTypeVar c (TyAll tyStar ty) = (TyAll (fiTypemap onTypeVar c tyStar) (fiTypemap onTypeVar (STypeVar c) ty))

fiTermSubstituteHelp sub c (TmVar var) = if (var == c) then (fiTermshiftplus c sub) else (TmVar var)

fiTermFiTermSubstitute sub orig t = (fiTermmap (fiTermSubstituteHelp sub) (\c x -> x) orig t)

fiTermFiTypeSubstitute sub orig t = (fiTermmap (\c x -> x) (fiTypeSubstituteHelp sub) orig t)

fiTypeSubstituteHelp sub c (TyVar var) = if (var == c) then (fiTypeshiftplus c sub) else (TyVar var)

fiTypeFiTypeSubstitute sub orig t = (fiTypemap (fiTypeSubstituteHelp sub) orig t)

freeVariablesFiTerm c (TmVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesFiTerm c (TmInt int1) = (nub (concat [[]]))
freeVariablesFiTerm c (TmTop) = (nub (concat [[]]))
freeVariablesFiTerm c (TmAbs t ty) = (nub (concat [(freeVariablesFiTerm (STermVar c) t),(freeVariablesFiType c ty)]))
freeVariablesFiTerm c (TmApp t1 t2) = (nub (concat [(freeVariablesFiTerm c t1),(freeVariablesFiTerm c t2)]))
freeVariablesFiTerm c (TmMerge t1 t2) = (nub (concat [(freeVariablesFiTerm c t1),(freeVariablesFiTerm c t2)]))
freeVariablesFiTerm c (TmAnn t ty) = (nub (concat [(freeVariablesFiTerm c t),(freeVariablesFiType c ty)]))
freeVariablesFiTerm c (TmRecord t string1) = (nub (concat [(freeVariablesFiTerm c t)]))
freeVariablesFiTerm c (TmProj t string1) = (nub (concat [(freeVariablesFiTerm c t)]))
freeVariablesFiTerm c (TmAll ty t) = (nub (concat [(freeVariablesFiType c ty),(freeVariablesFiTerm (STypeVar c) t)]))
freeVariablesFiTerm c (TypeApp t ty) = (nub (concat [(freeVariablesFiTerm c t),(freeVariablesFiType c ty)]))

freeVariablesFiType c (TyTop) = (nub (concat [[]]))
freeVariablesFiType c (TyBot) = (nub (concat [[]]))
freeVariablesFiType c (TyInt) = (nub (concat [[]]))
freeVariablesFiType c (TyArr ty1 ty2) = (nub (concat [(freeVariablesFiType c ty1),(freeVariablesFiType c ty2)]))
freeVariablesFiType c (TyAnd ty1 ty2) = (nub (concat [(freeVariablesFiType c ty1),(freeVariablesFiType c ty2)]))
freeVariablesFiType c (TyRecord ty string1) = (nub (concat [(freeVariablesFiType c ty)]))
freeVariablesFiType c (TyVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesFiType c (TyAll tyStar ty) = (nub (concat [(freeVariablesFiType c tyStar),(freeVariablesFiType (STypeVar c) ty)]))
instance Ord Variable where
  compare (Z) (Z) = (EQ)
  compare (Z) _ = (LT)
  compare _ (Z) = (GT)
  compare (STermVar h1) (STermVar h2) = (compare h1 h2)
  compare (STermVar h1) (STypeVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (STermVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (STypeVar h2) = (compare h1 h2)
