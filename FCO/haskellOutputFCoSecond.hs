module HaskellOutputFCoSecond
  ( Term(..)
  , Type(..)
  , Coercion(..)
  , typeOf
  , fullEval
  , HNat(..)
  , Env(..)
  ) where

import           FCO

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
stepEval (TmCast (CoProj1 ty) (TmTuple e1 e2))
  | not (isVal e1) = do
    newe1 <- stepEval e1
    return (TmCast (CoProj1 ty) (TmTuple newe1 e2))
  | not (isVal e2) = do
    newe2 <- stepEval e2
    return (TmCast (CoProj1 ty) (TmTuple e1 newe2))
  | otherwise = do return e1
--R-proj2
stepEval (TmCast (CoProj2 ty) (TmTuple e1 e2))
  | not (isVal e1) = do
    newe1 <- stepEval e1
    return (TmCast (CoProj2 ty) (TmTuple newe1 e2))
  | not (isVal e2) = do
    newe2 <- stepEval e2
    return (TmCast (CoProj2 ty) (TmTuple e1 newe2))
  | otherwise = do return e2
--R-ID
stepEval (TmCast CoId t) = return t
--R-Top
stepEval (TmCast (CoTop ty) e)
  | not (isVal e) = do
    newe <- stepEval e
    return (TmCast (CoTop ty) newe)
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
typeOfCo (CoTop _) _ = return TyTop
typeOfCo (CoTrans co1 co2) ty = do
  ty2 <- typeOfCo co2 ty
  ty3 <- typeOfCo co1 ty2
  return ty3
typeOfCo (CoBot ty1) ty
  | ty == TyAll (TyVar Z) = return ty1
  | otherwise = Left "wrong type"
typeOfCo (CoArrow co1 co2) (TyArr ty1 ty2) = do
  ty3 <- typeOfCo co2 ty2
  ty4 <- typeOfCoReverse co1 ty1
  return (TyArr ty4 ty3)
typeOfCo CoTopArrow ty
  | ty == TyTop = return (TyArr TyTop TyTop)
  | otherwise = Left "not a TyTop"
typeOfCo (CoTuple co1 co2) ty = do
  ty2 <- typeOfCo co1 ty
  ty3 <- typeOfCo co2 ty
  return (TyProd ty2 ty3)
typeOfCo (CoProj1 _) (TyProd ty1 _) = return ty1
typeOfCo (CoProj2 _) (TyProd _ ty2) = return ty2
typeOfCo (CoAll co) ty = do
  ty2 <- typeOfCo co ty
  return (TyAll ty2)
typeOfCo (CoTopAll) ty
  | ty == TyTop = return (TyAll TyTop)
  | otherwise = Left "type is not Top"
typeOfCo CoDistArrow (TyProd (TyArr ty1 ty2) (TyArr ty3 ty4))
  | ty1 == ty3 = return (TyArr ty1 (TyProd ty2 ty4))
  | otherwise = Left "type 1 does not equal type 2 of function in Coercion"
typeOfCo CoDistAll (TyProd (TyAll ty1) (TyAll ty2)) =
  return (TyAll (TyProd ty1 ty2))
typeOfCo _ _ = Left "type mismatch in coercion use"

typeOfCoReverse :: Coercion -> Type -> Either String Type
typeOfCoReverse CoId ty = return ty
typeOfCoReverse (CoTop ty2) ty
  | TyTop == ty = return ty2
  | otherwise = Left "wrong Reverse coercion for Top "
typeOfCoReverse (CoTrans co1 co2) ty = do
  ty2 <- typeOfCoReverse co1 ty
  ty3 <- typeOfCoReverse co2 ty2
  return ty3
typeOfCoReverse (CoArrow co1 co2) (TyArr ty1 ty2) = do
  ty3 <- typeOfCoReverse co2 ty2
  ty4 <- typeOfCo co1 ty1
  return (TyArr ty4 ty3)
typeOfCoReverse (CoBot _) _ = return (TyAll (TyVar Z))
typeOfCoReverse CoTopArrow ty
  | ty == (TyArr TyTop TyTop) = return TyTop
  | otherwise = Left "not a (TyArr TyTop TyTop)"
typeOfCoReverse (CoTuple co1 co2) (TyProd ty1 ty2) = do
  ty3 <- typeOfCoReverse co1 ty1
  ty4 <- typeOfCoReverse co2 ty2
  if ty3 == ty4
    then return ty4
    else Left "type mismatch in tuple coercion"
typeOfCoReverse (CoProj1 ty2) ty = return (TyProd ty ty2)
typeOfCoReverse (CoProj2 ty1) ty = return (TyProd ty1 ty)
typeOfCoReverse (CoAll co) ty = do
  ty2 <- typeOfCoReverse co ty
  return (TyAll ty2)
typeOfCoReverse (CoTopAll) ty
  | ty == (TyAll TyTop) = return TyTop
  | otherwise = Left "type is not Top"
typeOfCoReverse CoDistArrow (TyArr ty1 (TyProd ty2 ty3)) =
  return (TyProd (TyArr ty1 ty2) (TyArr ty1 ty3))
typeOfCoReverse CoDistAll (TyAll (TyProd ty1 ty2)) =
  return (TyProd (TyAll ty1) (TyAll ty2))
typeOfCoReverse _ _ = Left "Wrongful coercion use"

typeOf :: Term -> Env -> Either String Type
typeOf (TmVar nat) ctx = getTypeFromEnv ctx nat
typeOf (TmAbs t ty) ctx = do
  ty2 <- typeOf t (ETermVar ty ctx)
  return (TyArr ty ty2)
typeOf (TmApp t1 t2) ctx =
  case (typeOf t1 ctx) of
    Right (TyArr ty1 ty2) ->
      case (typeOf t2 ctx) of
        Right ty ->
          if ty == ty1
            then Right ty2
            else Left "different parameter expected"
        Left a -> Left a
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
