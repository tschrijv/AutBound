module FCO
  ( Env(..)
  , HNat(..)
  , Coercion(..)
  , coerciontypeSubstitute
  , freeVariablesCoercion
  , coercionshiftplus
  , coercionshiftminus
  , Type(..)
  , typetypeSubstitute
  , freeVariablesType
  , typeshiftplus
  , typeshiftminus
  , Term(..)
  , termtermSubstitute
  , termtypeSubstitute
  , freeVariablesTerm
  , termshiftplus
  , termshiftminus
  , generateHnatTypeVar
  , generateHnatTermVar
  ) where

import           Data.List

data Coercion
  = CoId
  | CoTrans Coercion
            Coercion
  | CoTop Type
  | CoBot Type
  | CoArrow Coercion
            Coercion
  | CoTuple Coercion
            Coercion
  | CoProj1 Type
  | CoProj2 Type
  | CoAll Coercion
  | CoDistArrow
  | CoTopArrow
  | CoTopAll
  | CoDistAll
  deriving (Show, Eq)

data Type
  = TyVar HNat
  | TyArr Type
          Type
  | TyAll Type
  | TyInt
  | TyTop
  | TyProd Type
           Type
  deriving (Show, Eq)

data Term
  = TmVar HNat
  | TmAbs Term
          Type
  | TmApp Term
          Term
  | TmTApp Term
           Type
  | TmTAbs Term
  | TmTop
  | TmTuple Term
            Term
  | TmInt Int
  | TmCast Coercion
           Term
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
  | ETypeVar Env
  | ETermVar Type
             Env
  deriving (Show, Eq)

generateHnatTypeVar 0 c = c
generateHnatTypeVar n c = STypeVar (generateHnatTypeVar (n - 1) c)

generateHnatTermVar 0 c = c
generateHnatTermVar n c = STermVar (generateHnatTermVar (n - 1) c)

coercionmap :: (HNat -> Type -> Type) -> HNat -> Coercion -> Coercion
coercionmap onTypeVar c (CoId) = CoId
coercionmap onTypeVar c (CoTrans co1 co2) =
  CoTrans (coercionmap onTypeVar c co1) (coercionmap onTypeVar c co2)
coercionmap onTypeVar c (CoTop ty) = CoTop (typemap onTypeVar c ty)
coercionmap onTypeVar c (CoBot ty) = CoBot (typemap onTypeVar c ty)
coercionmap onTypeVar c (CoArrow co1 co2) =
  CoArrow (coercionmap onTypeVar c co1) (coercionmap onTypeVar c co2)
coercionmap onTypeVar c (CoTuple co1 co2) =
  CoTuple (coercionmap onTypeVar c co1) (coercionmap onTypeVar c co2)
coercionmap onTypeVar c (CoProj1 ty2) = CoProj1 (typemap onTypeVar c ty2)
coercionmap onTypeVar c (CoProj2 ty1) = CoProj2 (typemap onTypeVar c ty1)
coercionmap onTypeVar c (CoAll co1) = CoAll (coercionmap onTypeVar c co1)
coercionmap onTypeVar c (CoDistArrow) = CoDistArrow
coercionmap onTypeVar c (CoTopArrow) = CoTopArrow
coercionmap onTypeVar c (CoTopAll) = CoTopAll
coercionmap onTypeVar c (CoDistAll) = CoDistAll

typemap :: (HNat -> Type -> Type) -> HNat -> Type -> Type
typemap onTypeVar c (TyVar hnat) = onTypeVar c (TyVar hnat)
typemap onTypeVar c (TyArr t1 t2) =
  TyArr (typemap onTypeVar c t1) (typemap onTypeVar c t2)
typemap onTypeVar c (TyAll t1) = TyAll (typemap onTypeVar (STypeVar c) t1)
typemap onTypeVar c (TyInt) = TyInt
typemap onTypeVar c (TyTop) = TyTop
typemap onTypeVar c (TyProd t1 t2) =
  TyProd (typemap onTypeVar c t1) (typemap onTypeVar c t2)

termmap ::
     (HNat -> Term -> Term) -> (HNat -> Type -> Type) -> HNat -> Term -> Term
termmap onTermVar onTypeVar c (TmVar hnat) = onTermVar c (TmVar hnat)
termmap onTermVar onTypeVar c (TmAbs x t) =
  TmAbs (termmap onTermVar onTypeVar (STermVar c) x) (typemap onTypeVar c t)
termmap onTermVar onTypeVar c (TmApp t1 t2) =
  TmApp (termmap onTermVar onTypeVar c t1) (termmap onTermVar onTypeVar c t2)
termmap onTermVar onTypeVar c (TmTApp t1 t) =
  TmTApp (termmap onTermVar onTypeVar c t1) (typemap onTypeVar c t)
termmap onTermVar onTypeVar c (TmTAbs t1) =
  TmTAbs (termmap onTermVar onTypeVar (STypeVar c) t1)
termmap onTermVar onTypeVar c (TmTop) = TmTop
termmap onTermVar onTypeVar c (TmTuple e1 e2) =
  TmTuple (termmap onTermVar onTypeVar c e1) (termmap onTermVar onTypeVar c e2)
termmap onTermVar onTypeVar c (TmInt int0) = TmInt int0
termmap onTermVar onTypeVar c (TmCast co e) =
  TmCast (coercionmap onTypeVar c co) (termmap onTermVar onTypeVar c e)

typeshiftHelpplus d c (TyVar hnat)
  | hnat >= c = TyVar (plus hnat d)
  | otherwise = TyVar hnat

termshiftHelpplus d c (TmVar hnat)
  | hnat >= c = TmVar (plus hnat d)
  | otherwise = TmVar hnat

coercionshiftplus :: HNat -> Coercion -> Coercion
coercionshiftplus d t = coercionmap (typeshiftHelpplus d) Z t

typeshiftplus :: HNat -> Type -> Type
typeshiftplus d t = typemap (typeshiftHelpplus d) Z t

termshiftplus :: HNat -> Term -> Term
termshiftplus d t = termmap (termshiftHelpplus d) (typeshiftHelpplus d) Z t

typeshiftHelpminus d c (TyVar hnat)
  | hnat >= c = TyVar (minus hnat d)
  | otherwise = TyVar hnat

termshiftHelpminus d c (TmVar hnat)
  | hnat >= c = TmVar (minus hnat d)
  | otherwise = TmVar hnat

coercionshiftminus :: HNat -> Coercion -> Coercion
coercionshiftminus d t = coercionmap (typeshiftHelpminus d) Z t

typeshiftminus :: HNat -> Type -> Type
typeshiftminus d t = typemap (typeshiftHelpminus d) Z t

termshiftminus :: HNat -> Term -> Term
termshiftminus d t = termmap (termshiftHelpminus d) (typeshiftHelpminus d) Z t

typeSubstituteHelp sub orig c (TyVar hnat)
  | hnat == plus orig c = typeshiftplus orig sub
  | otherwise = TyVar hnat

termSubstituteHelp sub orig c (TmVar hnat)
  | hnat == plus orig c = termshiftplus orig sub
  | otherwise = TmVar hnat

coerciontypeSubstitute :: Type -> HNat -> Coercion -> Coercion
coerciontypeSubstitute sub orig t =
  coercionmap (typeSubstituteHelp sub orig) Z t

typetypeSubstitute :: Type -> HNat -> Type -> Type
typetypeSubstitute sub orig t = typemap (typeSubstituteHelp sub orig) Z t

termtermSubstitute :: Term -> HNat -> Term -> Term
termtermSubstitute sub orig t =
  termmap (termSubstituteHelp sub orig) (\c x -> x) Z t

termtypeSubstitute :: Type -> HNat -> Term -> Term
termtypeSubstitute sub orig t =
  termmap (\c x -> x) (typeSubstituteHelp sub orig) Z t

freeVariablesCoercion :: HNat -> Coercion -> [HNat]
freeVariablesCoercion c (CoId) = nub ([])
freeVariablesCoercion c (CoTrans co1 co2) =
  nub ((freeVariablesCoercion c co1) ++ (freeVariablesCoercion c co2))
freeVariablesCoercion c (CoTop ty) = nub ((freeVariablesType c ty))
freeVariablesCoercion c (CoBot ty) = nub ((freeVariablesType c ty))
freeVariablesCoercion c (CoArrow co1 co2) =
  nub ((freeVariablesCoercion c co1) ++ (freeVariablesCoercion c co2))
freeVariablesCoercion c (CoTuple co1 co2) =
  nub ((freeVariablesCoercion c co1) ++ (freeVariablesCoercion c co2))
freeVariablesCoercion c (CoProj1 ty2) = nub ((freeVariablesType c ty2))
freeVariablesCoercion c (CoProj2 ty1) = nub ((freeVariablesType c ty1))
freeVariablesCoercion c (CoAll co1) = nub ((freeVariablesCoercion c co1))
freeVariablesCoercion c (CoDistArrow) = nub ([])
freeVariablesCoercion c (CoTopArrow) = nub ([])
freeVariablesCoercion c (CoTopAll) = nub ([])
freeVariablesCoercion c (CoDistAll) = nub ([])

freeVariablesType :: HNat -> Type -> [HNat]
freeVariablesType c (TyVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesType c (TyArr t1 t2) =
  nub ((freeVariablesType c t1) ++ (freeVariablesType c t2))
freeVariablesType c (TyAll t1) = nub ((freeVariablesType (STypeVar c) t1))
freeVariablesType c (TyInt) = nub ([])
freeVariablesType c (TyTop) = nub ([])
freeVariablesType c (TyProd t1 t2) =
  nub ((freeVariablesType c t1) ++ (freeVariablesType c t2))

freeVariablesTerm :: HNat -> Term -> [HNat]
freeVariablesTerm c (TmVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesTerm c (TmAbs x t) =
  nub ((freeVariablesTerm (STermVar c) x) ++ (freeVariablesType c t))
freeVariablesTerm c (TmApp t1 t2) =
  nub ((freeVariablesTerm c t1) ++ (freeVariablesTerm c t2))
freeVariablesTerm c (TmTApp t1 t) =
  nub ((freeVariablesTerm c t1) ++ (freeVariablesType c t))
freeVariablesTerm c (TmTAbs t1) = nub ((freeVariablesTerm (STypeVar c) t1))
freeVariablesTerm c (TmTop) = nub ([])
freeVariablesTerm c (TmTuple e1 e2) =
  nub ((freeVariablesTerm c e1) ++ (freeVariablesTerm c e2))
freeVariablesTerm c (TmInt _) = nub ([])
freeVariablesTerm c (TmCast co e) =
  nub ((freeVariablesCoercion c co) ++ (freeVariablesTerm c e))
