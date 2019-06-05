module Fi
  ( Env(..)
  , HNat(..)
  , FiType(..)
  , fiTypefiTypeSubstitute
  , freeVariablesFiType
  , fiTypeshiftplus
  , fiTypeshiftminus
  , FiTerm(..)
  , fiTermfiTermSubstitute
  , fiTermfiTypeSubstitute
  , freeVariablesFiTerm
  , fiTermshiftplus
  , fiTermshiftminus
  , generateHnatTypeVar
  , generateHnatTermVar
  ) where

import           Data.List

data FiType
  = TyTop
  | TyBot
  | TyInt
  | TyArr FiType
          FiType
  | TyAnd FiType
          FiType
  | TyRecord FiType
             String
  | TyVar HNat
  | TyAll FiType
          FiType
  deriving (Show, Eq)

data FiTerm
  = TmVar HNat
  | TmInt Int
  | TmTop
  | TmAbs FiTerm
          FiType
  | TmApp FiTerm
          FiTerm
  | TmMerge FiTerm
            FiTerm
  | TmAnn FiTerm
          FiType
  | TmRecord FiTerm
             String
  | TmProj FiTerm
           String
  | TmAll FiType
          FiTerm
  | TypeApp FiTerm
            FiType
  deriving (Show, Eq)

data HNat
  = Z
  | STypeVar HNat
  | STermVar HNat
  deriving (Show, Eq)

plus x1 (STypeVar x2) = STypeVar (plus x1 x2)
plus x1 (STermVar x2) = STermVar (plus x1 x2)
plus Z h              = h
plus h Z              = h

instance Ord HNat where
  compare (STypeVar h1) (STypeVar h2) = compare h1 h2
  compare (STypeVar h1) (STermVar h2) =
    error "differing namespace found in compare "
  compare (STermVar h1) (STypeVar h2) =
    error "differing namespace found in compare "
  compare (STermVar h1) (STermVar h2) = compare h1 h2
  compare Z Z = EQ
  compare Z _ = LT
  compare _ Z = GT

minus (STypeVar h1) (STypeVar h2) = minus h1 h2
minus (STypeVar h1) (STermVar h2) = error "differing namespace found in minus "
minus (STermVar h1) (STypeVar h2) = error "differing namespace found in minus "
minus (STermVar h1) (STermVar h2) = minus h1 h2
minus Z Z = Z
minus Z _ = error " You cannot substract zero with a positive number "
minus result Z = result

data Env
  = Nil
  | ETypeVar FiType
             Env
  | ETermVar FiType
             Env
  deriving (Show, Eq)

generateHnatTypeVar 0 c = c
generateHnatTypeVar n c = STypeVar (generateHnatTypeVar (n - 1) c)

generateHnatTermVar 0 c = c
generateHnatTermVar n c = STermVar (generateHnatTermVar (n - 1) c)

fiTypemap :: (HNat -> FiType -> FiType) -> HNat -> FiType -> FiType
fiTypemap onTypeVar c (TyTop) = TyTop
fiTypemap onTypeVar c (TyBot) = TyBot
fiTypemap onTypeVar c (TyInt) = TyInt
fiTypemap onTypeVar c (TyArr ty1 ty2) =
  TyArr (fiTypemap onTypeVar c ty1) (fiTypemap onTypeVar c ty2)
fiTypemap onTypeVar c (TyAnd ty1 ty2) =
  TyAnd (fiTypemap onTypeVar c ty1) (fiTypemap onTypeVar c ty2)
fiTypemap onTypeVar c (TyRecord ty string0) =
  TyRecord (fiTypemap onTypeVar c ty) string0
fiTypemap onTypeVar c (TyVar hnat) = onTypeVar c (TyVar hnat)
fiTypemap onTypeVar c (TyAll tyStar ty) =
  TyAll (fiTypemap onTypeVar c tyStar) (fiTypemap onTypeVar (STypeVar c) ty)

fiTermmap ::
     (HNat -> FiTerm -> FiTerm)
  -> (HNat -> FiType -> FiType)
  -> HNat
  -> FiTerm
  -> FiTerm
fiTermmap onTermVar onTypeVar c (TmVar hnat) = onTermVar c (TmVar hnat)
fiTermmap onTermVar onTypeVar c (TmInt int0) = TmInt int0
fiTermmap onTermVar onTypeVar c (TmTop) = TmTop
fiTermmap onTermVar onTypeVar c (TmAbs t ty) =
  TmAbs
    (fiTermmap onTermVar onTypeVar (STermVar c) t)
    (fiTypemap onTypeVar c ty)
fiTermmap onTermVar onTypeVar c (TmApp t1 t2) =
  TmApp
    (fiTermmap onTermVar onTypeVar c t1)
    (fiTermmap onTermVar onTypeVar c t2)
fiTermmap onTermVar onTypeVar c (TmMerge t1 t2) =
  TmMerge
    (fiTermmap onTermVar onTypeVar c t1)
    (fiTermmap onTermVar onTypeVar c t2)
fiTermmap onTermVar onTypeVar c (TmAnn t ty) =
  TmAnn (fiTermmap onTermVar onTypeVar c t) (fiTypemap onTypeVar c ty)
fiTermmap onTermVar onTypeVar c (TmRecord t string0) =
  TmRecord (fiTermmap onTermVar onTypeVar c t) string0
fiTermmap onTermVar onTypeVar c (TmProj t string0) =
  TmProj (fiTermmap onTermVar onTypeVar c t) string0
fiTermmap onTermVar onTypeVar c (TmAll ty t) =
  TmAll
    (fiTypemap onTypeVar c ty)
    (fiTermmap onTermVar onTypeVar (STypeVar c) t)
fiTermmap onTermVar onTypeVar c (TypeApp t ty) =
  TypeApp (fiTermmap onTermVar onTypeVar c t) (fiTypemap onTypeVar c ty)

fiTypeshiftHelpplus d c (TyVar hnat)
  | hnat >= c = TyVar (plus hnat d)
  | otherwise = TyVar hnat

fiTermshiftHelpplus d c (TmVar hnat)
  | hnat >= c = TmVar (plus hnat d)
  | otherwise = TmVar hnat

fiTypeshiftplus :: HNat -> FiType -> FiType
fiTypeshiftplus d t = fiTypemap (fiTypeshiftHelpplus d) Z t

fiTermshiftplus :: HNat -> FiTerm -> FiTerm
fiTermshiftplus d t =
  fiTermmap (fiTermshiftHelpplus d) (fiTypeshiftHelpplus d) Z t

fiTypeshiftHelpminus d c (TyVar hnat)
  | hnat >= c = TyVar (minus hnat d)
  | otherwise = TyVar hnat

fiTermshiftHelpminus d c (TmVar hnat)
  | hnat >= c = TmVar (minus hnat d)
  | otherwise = TmVar hnat

fiTypeshiftminus :: HNat -> FiType -> FiType
fiTypeshiftminus d t = fiTypemap (fiTypeshiftHelpminus d) Z t

fiTermshiftminus :: HNat -> FiTerm -> FiTerm
fiTermshiftminus d t =
  fiTermmap (fiTermshiftHelpminus d) (fiTypeshiftHelpminus d) Z t

fiTypeSubstituteHelp sub orig c (TyVar hnat)
  | hnat == plus orig c = fiTypeshiftplus c sub
  | otherwise = TyVar hnat

fiTermSubstituteHelp sub orig c (TmVar hnat)
  | hnat == plus orig c = fiTermshiftplus c sub
  | otherwise = TmVar hnat

fiTypefiTypeSubstitute :: FiType -> HNat -> FiType -> FiType
fiTypefiTypeSubstitute sub orig t =
  fiTypemap (fiTypeSubstituteHelp sub orig) Z t

fiTermfiTermSubstitute :: FiTerm -> HNat -> FiTerm -> FiTerm
fiTermfiTermSubstitute sub orig t =
  fiTermmap (fiTermSubstituteHelp sub orig) (\c x -> x) Z t

fiTermfiTypeSubstitute :: FiType -> HNat -> FiTerm -> FiTerm
fiTermfiTypeSubstitute sub orig t =
  fiTermmap (\c x -> x) (fiTypeSubstituteHelp sub orig) Z t

freeVariablesFiType :: HNat -> FiType -> [HNat]
freeVariablesFiType c (TyTop) = nub ([])
freeVariablesFiType c (TyBot) = nub ([])
freeVariablesFiType c (TyInt) = nub ([])
freeVariablesFiType c (TyArr ty1 ty2) =
  nub ((freeVariablesFiType c ty1) ++ (freeVariablesFiType c ty2))
freeVariablesFiType c (TyAnd ty1 ty2) =
  nub ((freeVariablesFiType c ty1) ++ (freeVariablesFiType c ty2))
freeVariablesFiType c (TyRecord ty _) = nub ((freeVariablesFiType c ty))
freeVariablesFiType c (TyVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesFiType c (TyAll tyStar ty) =
  nub ((freeVariablesFiType c tyStar) ++ (freeVariablesFiType (STypeVar c) ty))

freeVariablesFiTerm :: HNat -> FiTerm -> [HNat]
freeVariablesFiTerm c (TmVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesFiTerm c (TmInt _) = nub ([])
freeVariablesFiTerm c (TmTop) = nub ([])
freeVariablesFiTerm c (TmAbs t ty) =
  nub ((freeVariablesFiTerm (STermVar c) t) ++ (freeVariablesFiType c ty))
freeVariablesFiTerm c (TmApp t1 t2) =
  nub ((freeVariablesFiTerm c t1) ++ (freeVariablesFiTerm c t2))
freeVariablesFiTerm c (TmMerge t1 t2) =
  nub ((freeVariablesFiTerm c t1) ++ (freeVariablesFiTerm c t2))
freeVariablesFiTerm c (TmAnn t ty) =
  nub ((freeVariablesFiTerm c t) ++ (freeVariablesFiType c ty))
freeVariablesFiTerm c (TmRecord t _) = nub ((freeVariablesFiTerm c t))
freeVariablesFiTerm c (TmProj t _) = nub ((freeVariablesFiTerm c t))
freeVariablesFiTerm c (TmAll ty t) =
  nub ((freeVariablesFiType c ty) ++ (freeVariablesFiTerm (STypeVar c) t))
freeVariablesFiTerm c (TypeApp t ty) =
  nub ((freeVariablesFiTerm c t) ++ (freeVariablesFiType c ty))
