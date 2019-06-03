module HaskellOutputFCo
  ( Term(..)
  , Type(..)
  , Coercion(..)
  , typeOf
  , fullEval
  , HNat(..)
  , Env(..)
  ) where

import           Data.List

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

data Type
  = TyVar HNat
  | TyArr Type
          Type
  | TyAll Type
  | TyInt
  | TyTop
  | TyProd Type
           Type
  | PolyType
  deriving (Show, Eq)

data Coercion
  = CoId
  | CoTrans Coercion
            Coercion
  | CoTop
  | CoBot
  | CoArrow Coercion
            Coercion
  | CoTuple Coercion
            Coercion
  | CoProj1
  | CoProj2
  | CoAll Coercion
  | CoDistArrow
  | CoTopArrow
  | CoTopAll
  | CoDistAll
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
  compare (STypeVar h1) (STermVar h2) = compare h1 h2
  compare (STermVar h1) (STypeVar h2) = compare h1 h2
  compare (STermVar h1) (STermVar h2) = compare h1 h2
  compare Z Z                         = EQ
  compare Z _                         = LT
  compare _ Z                         = GT

minus (STypeVar h1) (STypeVar h2) = minus h1 h2
minus (STypeVar h1) (STermVar h2) = error "differing namespace found "
minus (STermVar h1) (STypeVar h2) = error "differing namespace found "
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
typemap onTypeVar c (TyInt) = TyInt
typemap onTypeVar c (TyTop) = TyTop
typemap onTypeVar c (TyProd t1 t2) =
  TyProd (typemap onTypeVar c t1) (typemap onTypeVar c t2)
typemap onTypeVar c (PolyType) = PolyType

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
  TmCast co (termmap onTermVar onTypeVar c e)

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
  | hnat == plus orig c = typeshiftplus orig sub
  | otherwise = TyVar hnat

termSubstituteHelp sub orig c (TmVar hnat)
  | hnat == plus orig c = termshiftplus orig sub
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
freeVariablesType c (TyInt) = nub ([])
freeVariablesType c (TyTop) = nub ([])
freeVariablesType c (TyProd t1 t2) =
  nub ((freeVariablesType c t1) ++ (freeVariablesType c t2))
freeVariablesType c (PolyType) = nub ([])

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
freeVariablesTerm c (TmCast co e) = nub ((freeVariablesTerm c e))

--end of generated code
isVal :: Term -> Bool
isVal (TmAbs x t)              = True
isVal (TmTAbs t1)              = True
isVal (TmTop)                  = True
isVal (TmTuple e1 e2)          = isVal e1 && isVal e2
isVal (TmInt int0)             = True
isVal (TmCast (CoArrow _ _) e) = isVal e
isVal (TmCast (CoAll _) e)     = isVal e
isVal (TmCast (CoDistArrow) e) = isVal e
isVal (TmCast (CoTopArrow) e)  = isVal e
isVal (TmCast (CoDistAll) e)   = isVal e
isVal _                        = False

getTypeFromEnv :: Env -> HNat -> Either String Type
getTypeFromEnv (ETermVar ty _) Z = return ty
getTypeFromEnv _ Z = Left "wrong or no binding for term"
getTypeFromEnv (ETermVar _ rest) (STermVar h) = getTypeFromEnv rest h
getTypeFromEnv _ (STermVar h) = Left "wrong term binding"
getTypeFromEnv (ETypeVar rest) (STypeVar h) = getTypeFromEnv rest h
getTypeFromEnv _ (STypeVar h) = Left "No variable type"

--evaluation
stepEval :: Term -> Maybe Term
--function application
stepEval (TmApp (TmAbs t ty) t2)
  | isVal t2 =
    Just
      (termshiftminus
         (STermVar Z)
         (termtermSubstitute (termshiftplus (STermVar Z) t2) Z t))
--type application
stepEval (TmTApp (TmTAbs t) ty) =
  Just
    (termshiftminus
       (STypeVar Z)
       (termtypeSubstitute (typeshiftplus (STypeVar Z) ty) Z t))
--R-proj1
stepEval (TmCast CoProj1 (TmTuple e1 e2))
  | not (isVal e1) = do
    newe1 <- stepEval e1
    return (TmCast CoProj1 (TmTuple newe1 e2))
  | not (isVal e2) = do
    newe2 <- stepEval e2
    return (TmCast CoProj1 (TmTuple e1 newe2))
  | otherwise = do return e1
--R-proj2
stepEval (TmCast CoProj2 (TmTuple e1 e2))
  | not (isVal e1) = do
    newe1 <- stepEval e1
    return (TmCast CoProj2 (TmTuple newe1 e2))
  | not (isVal e2) = do
    newe2 <- stepEval e2
    return (TmCast CoProj2 (TmTuple e1 newe2))
  | otherwise = do return e2
--R-ID
stepEval (TmCast CoId t) = return t
--R-Top
stepEval (TmCast CoTop e)
  | not (isVal e) = do
    newe <- stepEval e
    return (TmCast CoTop newe)
  | otherwise = return TmTop
--R-Trans
stepEval (TmCast (CoTrans co1 co2) e)
  | not (isVal e) = do
    newe <- stepEval e
    return (TmCast (CoTrans co1 co2) newe)
  | otherwise = do return (TmCast co1 (TmCast co2 e))
--R-ARR
stepEval (TmApp (TmCast (CoArrow co1 co2) e1) e2)
  | not (isVal e1) = do
    newe1 <- stepEval e1
    return (TmApp (TmCast (CoArrow co1 co2) newe1) e2)
  | not (isVal e2) = do
    newe2 <- stepEval e2
    return (TmApp (TmCast (CoArrow co1 co2) e1) newe2)
  | otherwise = return (TmCast co1 (TmApp e1 (TmCast co2 e2)))
--R-Pair
stepEval (TmCast (CoTuple co1 co2) e1)
  | isVal e1 = return (TmTuple (TmCast co1 e1) (TmCast co2 e1))
  | otherwise = do
    newe <- stepEval e1
    return (TmCast (CoTuple co1 co2) newe)
--R-Forall
stepEval (TmTApp (TmCast (CoAll co) e) ty)
  | isVal e = return (TmCast co (TmTApp e ty))
--R-TopArr
stepEval (TmApp (TmCast CoTopArrow TmTop) TmTop) = return (TmTop)
--R-TopAll
stepEval (TmTApp (TmCast CoTopAll TmTop) ty) = return (TmTop)
--R-DistArr
stepEval (TmApp (TmCast CoDistArrow (TmTuple t1 t2)) t3)
  | not (isVal t1) = do
    newe <- stepEval t1
    return (TmApp (TmCast CoDistArrow (TmTuple newe t2)) t3)
  | not (isVal t2) = do
    newe <- stepEval t2
    return (TmApp (TmCast CoDistArrow (TmTuple t1 newe)) t3)
  | not (isVal t3) = do
    newe <- stepEval t3
    return (TmApp (TmCast CoDistArrow (TmTuple t1 t2)) newe)
  | otherwise = return (TmTuple (TmApp t1 t3) (TmApp t2 t3))
--R-DistAll
stepEval (TmTApp (TmCast CoDistAll (TmTuple t1 t2)) ty)
  | not (isVal t1) = do
    newe <- stepEval t1
    return (TmTApp (TmCast CoDistAll (TmTuple newe t2)) ty)
  | not (isVal t2) = do
    newe <- stepEval t2
    return (TmTApp (TmCast CoDistAll (TmTuple t1 newe)) ty)
  | otherwise = return (TmTuple (TmTApp t1 ty) (TmTApp t2 ty))
--R-CTXT
stepEval (TmApp t1 t2)
  | isVal t1 = do
    newt2 <- stepEval t2
    return (TmApp t1 newt2)
  | otherwise = do
    newt1 <- stepEval t1
    return (TmApp newt1 t2)
stepEval (TmTApp t ty)
  | not (isVal t) = do
    newt <- stepEval t
    return (TmTApp newt ty)
stepEval (TmCast co t)
  | not (isVal t) = do
    newe <- stepEval t
    return (TmCast co t)
stepEval (TmTuple t1 t2)
  | not (isVal t1) = do
    newe <- stepEval t1
    return (TmTuple newe t2)
  | not (isVal t2) = do
    newe <- stepEval t2
    return (TmTuple t1 newe)
stepEval _ = Nothing

--evaluates a term
fullEval :: Term -> Term
fullEval t = maybe t (fullEval) t2
  where
    t2 = stepEval t

typeOfCo :: Coercion -> Type -> Either String Type
typeOfCo CoId ty = return ty
typeOfCo CoTop _ = return TyTop
typeOfCo (CoTrans co1 co2) ty = do
  ty2 <- typeOfCo co2 ty
  ty3 <- typeOfCo co1 ty2
  return ty3
typeOfCo CoBot ty
  | ty == PolyType = return PolyType
  | ty == TyAll (TyVar Z) = return PolyType
  | otherwise = Left "wrong type"
typeOfCo (CoArrow co1 co2) (TyArr ty1 ty2) = do
  ty3 <- typeOfCo co2 ty2
  ty4 <- typeOfCoReverse co1 ty1
  return (TyArr ty4 ty3)
typeOfCo (CoArrow co1 co2) PolyType = do
  ty3 <- typeOfCo co2 PolyType
  ty4 <- typeOfCoReverse co1 PolyType
  return (TyArr ty4 ty3)
typeOfCo CoTopArrow ty
  | ty == TyTop = return (TyArr TyTop TyTop)
  | ty == PolyType = return (TyArr TyTop TyTop)
  | otherwise = Left "not a TyTop"
typeOfCo (CoTuple co1 co2) ty = do
  ty2 <- typeOfCo co1 ty
  ty3 <- typeOfCo co2 ty
  return (TyProd ty2 ty3)
typeOfCo CoProj1 (TyProd ty1 _) = return ty1
typeOfCo CoProj1 PolyType = return PolyType
typeOfCo CoProj2 (TyProd _ ty2) = return ty2
typeOfCo CoProj2 PolyType = return PolyType
typeOfCo (CoAll co) ty = do
  ty2 <- typeOfCo co ty
  return (TyAll ty2)
typeOfCo (CoTopAll) ty
  | ty == TyTop = return (TyAll TyTop)
  | ty == PolyType = return (TyAll TyTop)
  | otherwise = Left "type is not Top"
typeOfCo CoDistArrow (TyProd (TyArr ty1 ty2) (TyArr ty3 ty4))
  | ty1 == ty3 = return (TyArr ty1 (TyProd ty2 ty4))
  | ty1 == PolyType = return (TyArr ty3 (TyProd ty2 ty4))
  | ty3 == PolyType = return (TyArr ty1 (TyProd ty2 ty4))
  | otherwise = Left "type 1 does not equal type 2 of function in Coercion"
typeOfCo CoDistArrow (TyProd PolyType (TyArr ty3 ty4)) =
  return (TyArr ty3 (TyProd PolyType ty4))
typeOfCo CoDistArrow (TyProd (TyArr ty1 ty2) PolyType) =
  return (TyArr ty1 (TyProd ty2 PolyType))
typeOfCo CoDistArrow PolyType =
  return (TyArr PolyType (TyProd PolyType PolyType))
typeOfCo CoDistAll (TyProd (TyAll ty1) (TyAll ty2)) =
  return (TyAll (TyProd ty1 ty2))
typeOfCo CoDistAll PolyType = return (TyAll (TyProd PolyType PolyType))
typeOfCo CoDistAll (TyProd (TyAll ty1) PolyType) =
  return (TyAll (TyProd ty1 PolyType))
typeOfCo CoDistAll (TyProd PolyType (TyAll ty2)) =
  return (TyAll (TyProd PolyType ty2))
typeOfCo _ _ = Left "type mismatch in coercion use"

typeOfCoReverse :: Coercion -> Type -> Either String Type
typeOfCoReverse CoId ty = return ty
typeOfCoReverse CoTop ty
  | TyTop == ty = return PolyType
  | ty == PolyType = return PolyType
  | otherwise = Left "wrong Reverse coercion for Top "
typeOfCoReverse (CoTrans co1 co2) ty = do
  ty2 <- typeOfCoReverse co1 ty
  ty3 <- typeOfCoReverse co2 ty2
  return ty3
typeOfCoReverse (CoArrow co1 co2) (TyArr ty1 ty2) = do
  ty3 <- typeOfCoReverse co2 ty2
  ty4 <- typeOfCo co1 ty1
  return (TyArr ty4 ty3)
typeOfCoReverse (CoArrow co1 co2) PolyType = do
  ty3 <- typeOfCoReverse co2 PolyType
  ty4 <- typeOfCo co1 PolyType
  return (TyArr ty4 ty3)
typeOfCoReverse CoBot _ = return (TyAll (TyVar Z))
typeOfCoReverse CoTopArrow ty
  | ty == (TyArr TyTop TyTop) = return TyTop
  | ty == PolyType = return TyTop
  | otherwise = Left "not a (TyArr TyTop TyTop)"
typeOfCoReverse (CoTuple co1 co2) (TyProd ty1 ty2) = do
  ty3 <- typeOfCoReverse co1 ty1
  ty4 <- typeOfCoReverse co2 ty2
  if ty3 == ty4
    then return ty4
    else Left "type mismatch in tuple coercion"
typeOfCoReverse CoProj1 ty = return (TyProd ty PolyType)
typeOfCoReverse CoProj2 ty = return (TyProd PolyType ty)
typeOfCoReverse (CoAll co) ty = do
  ty2 <- typeOfCoReverse co ty
  return (TyAll ty2)
typeOfCoReverse (CoTopAll) ty
  | ty == (TyAll TyTop) = return TyTop
  | ty == (TyAll PolyType) = return TyTop
  | ty == PolyType = return TyTop
  | otherwise = Left "type is not Top"
typeOfCoReverse CoDistArrow (TyArr ty1 (TyProd ty2 ty3)) =
  return (TyProd (TyArr ty1 ty2) (TyArr ty1 ty3))
typeOfCoReverse CoDistArrow PolyType =
  return (TyProd (TyArr PolyType PolyType) (TyArr PolyType PolyType))
typeOfCoReverse CoDistArrow (TyArr ty1 PolyType) =
  return (TyProd (TyArr ty1 PolyType) (TyArr ty1 PolyType))
typeOfCoReverse CoDistAll (TyAll (TyProd ty1 ty2)) =
  return (TyProd (TyAll ty1) (TyAll ty2))
typeOfCoReverse CoDistAll PolyType =
  return (TyProd (TyAll PolyType) (TyAll PolyType))
typeOfCoReverse CoDistAll (TyAll PolyType) =
  return (TyProd (TyAll PolyType) (TyAll PolyType))
typeOfCoReverse _ _ = Left "Wrongful coercion use"

typeOf :: Term -> Env -> Either String Type
typeOf (TmVar nat) ctx = getTypeFromEnv ctx nat
typeOf (TmAbs t ty) ctx = do
  ty2 <- typeOf t (ETermVar ty ctx)
  return (TyArr ty ty2)
typeOf (TmApp t1 t2) ctx =
  case (typeOf t1 ctx) of
    Right (TyArr ty1 ty2) ->
      if (typeOf t2 ctx) == Right ty1
        then Right ty2
        else Left "parameter mismatch"
    Left a -> Left a
    _ -> Left "arrow type expected"
typeOf (TmTApp t ty) ctx =
  case (typeOf t ctx) of
    Right (TyAll ty2) ->
      return
        (typeshiftminus
           (STypeVar Z)
           (typetypeSubstitute (typeshiftplus (STypeVar Z) ty) Z ty2))
    Left a -> Left a
    _ -> Left "not a type abstraction"
typeOf (TmTAbs t) ctx = do
  ty <- typeOf t (ETypeVar ctx)
  return (TyAll ty)
typeOf TmTop ctx = return TyTop
typeOf (TmTuple t1 t2) ctx = do
  ty1 <- typeOf t1 ctx
  ty2 <- typeOf t2 ctx
  return (TyProd ty1 ty2)
typeOf (TmCast co e) ctx = do
  tye <- typeOf e ctx
  (typeOfCo co tye)
typeOf (TmInt _) ctx = return TyInt
--Deprecated
-- isTyProd :: Type->Bool
-- isTyProd (TyProd _ _) = True
-- isTyProd _ = False
-- isTyAll :: Type->Bool
-- isTyAll (TyAll _) = True
-- isTyAll _ = False
-- typeOfCo2:: Coercion ->   (Type->Either String Type)
-- typeOfCo2 CoId =  (\x->return x)
-- typeOfCo2 CoTop =  (\x-> return TyTop)
-- typeOfCo2 (CoTrans co1 co2) =  (\x-> do
                                    -- first<- f2 x
                                    -- second <- f1 first
                                    -- return second )
                                       -- where  f1 = typeOfCo2 co1
                                              -- f2 = typeOfCo2 co2
-- typeOfCo2 CoTopArrow = (\x-> if x== TyTop then return TyTop else Left "function x is not a ")
-- typeOfCo2 (CoTuple co1 co2)  =  (\x -> do
                                          -- first <- f1 x
                                          -- second <- f2 x
                                          -- return (TyProd first second) )
                                    -- where f1= typeOfCo2 co1
                                          -- f2= typeOfCo2 co2
-- typeOfCo2 CoProj1 = (\(x)-> if isTyProd x  then f x else Left "is not Product type")
                                            -- where f = (\(TyProd x y) -> return x)
-- typeOfCo2 CoProj2 = (\(x)-> if isTyProd x  then f x else Left "is not Product type")
                                            -- where f = (\(TyProd x y) -> return y)
-- typeOfCo2 (CoAll co )  = (\x -> do
                            -- result<- f x
                            -- return (TyAll result) )
                             -- where f = typeOfCo2 co
-- typeOfCo2 (CoTopAll) = (\x-> if x == TyTop then return (TyAll TyTop) else Left "type is not TyTop")
-- typeOfCo2 CoDistAll = (\x-> if isTyProd x  then (if  correctAllType x  then f x  else Left "in CoDistAll not TyAll in both parts") else Left "not Product type in codistall")
                            -- where correctAllType= (\(TyProd x y)-> isTyAll x && isTyAll y)
                                  -- f = (\(TyProd (TyAll ty1) (TyAll ty2) )-> return (TyAll (TyProd ty1 ty2)))
-- typeOfCo2 CoDistArrow = (\x-> f x )
                -- where f ( TyProd   (TyArr ty1 ty2)  (TyArr ty3 ty4) )
                                -- | ty1 == ty2 = return (TyArr ty1  (TyProd ty2 ty4) )
                                -- | otherwise = Left "type 1 does not equal type 2 of function in Coercion"
                      -- f _ = Left "wrong types for CoDistArrow "
-- typeOfCo2 CoBot = (\x-> )
-- typeOfCo2 (CoArrow co1 co2) =
                                -- where f1 =  typeOfCo2 co1
                                      -- f2 =  typeOfCo2 co2
                                      -- coerce (TyArr ty1 ty2 )=
                                      -- coerce _ =  Left "not arrow type"
