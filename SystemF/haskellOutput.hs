module HaskellOutput
  ( Env(..)
  , HNat(..)
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

data Type
  = TyVar HNat
  | TyArr Type
          Type
  | TyAll Type
  | TyBase
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

typemap :: (HNat -> Type -> Type) -> HNat -> Type -> Type
typemap onTypeVar c (TyVar hnat) = onTypeVar c (TyVar hnat)
typemap onTypeVar c (TyArr t1 t2) =
  TyArr (typemap onTypeVar c t1) (typemap onTypeVar c t2)
typemap onTypeVar c (TyAll t1) = TyAll (typemap onTypeVar (STypeVar c) t1)
typemap onTypeVar c (TyBase) = TyBase

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

typeshiftHelpplus d c (TyVar hnat)
  | hnat >= c = TyVar (plus hnat d)
  | otherwise = TyVar hnat

termshiftHelpplus d c (TmVar hnat)
  | hnat >= c = TmVar (plus hnat d)
  | otherwise = TmVar hnat

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

typeshiftminus :: HNat -> Type -> Type
typeshiftminus d t = typemap (typeshiftHelpminus d) Z t

termshiftminus :: HNat -> Term -> Term
termshiftminus d t = termmap (termshiftHelpminus d) (typeshiftHelpminus d) Z t

typeSubstituteHelp sub orig c (TyVar hnat)
  | hnat == plus orig c = typeshiftplus c sub
  | otherwise = TyVar hnat

termSubstituteHelp sub orig c (TmVar hnat)
  | hnat == plus orig c = termshiftplus c sub
  | otherwise = TmVar hnat

typetypeSubstitute :: Type -> HNat -> Type -> Type
typetypeSubstitute sub orig t = typemap (typeSubstituteHelp sub orig) Z t

termtermSubstitute :: Term -> HNat -> Term -> Term
termtermSubstitute sub orig t =
  termmap (termSubstituteHelp sub orig) (\c x -> x) Z t

termtypeSubstitute :: Type -> HNat -> Term -> Term
termtypeSubstitute sub orig t =
  termmap (\c x -> x) (typeSubstituteHelp sub orig) Z t

freeVariablesType :: HNat -> Type -> [HNat]
freeVariablesType c (TyVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesType c (TyArr t1 t2) =
  nub ((freeVariablesType c t1) ++ (freeVariablesType c t2))
freeVariablesType c (TyAll t1) = nub ((freeVariablesType (STypeVar c) t1))
freeVariablesType c (TyBase) = nub ([])

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
