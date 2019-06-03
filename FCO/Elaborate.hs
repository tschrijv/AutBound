module Elaborate
  ( Term(..)
  , Type(..)
  , Coercion(..)
  , elaborate
  , goodelaborate
  ) where

import           Fi
import           FiImpl

data Term
  = TmVarCo HNat
  | TmAbsCo Term
            Type
  | TmAppCo Term
            Term
  | TmTAppCo Term
             Type
  | TmTAbsCo Term
  | TmTopCo
  | TmTupleCo Term
              Term
  | TmIntCo Int
  | TmCast Coercion
           Term
  deriving (Show, Eq)

data Type
  = TyVarCo HNat
  | TyArrCo Type
            Type
  | TyAllCo Type
  | TyIntCo
  | TyTopCo
  | TyProdCo Type
             Type
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

getTypeFromEnv :: Env -> HNat -> Either String FiType
getTypeFromEnv (ETermVar ty _) Z = return ty
getTypeFromEnv _ Z = Left "wrong or no binding for FiTerm"
getTypeFromEnv (ETermVar _ rest) (STermVar h) = getTypeFromEnv rest h
getTypeFromEnv _ (STermVar h) = Left "wrong FiTerm binding"
getTypeFromEnv (ETypeVar _ rest) (STypeVar h) = getTypeFromEnv rest h
getTypeFromEnv _ (STypeVar h) = Left "No variable FiType"

elaborate :: FiTerm -> Env -> Either String Term
elaborate TmTop ctx = return TmTopCo
elaborate (TmInt i) ctx = return (TmIntCo i)
elaborate (TmVar hnat) ctx = return (TmVarCo hnat)
elaborate (TmAbs t ty) ctx = do
  term <- elaborate t (ETermVar ty ctx)
  return (TmAbsCo term (convertType ty))
elaborate (TmApp t1 t2) ctx = do
  term1 <- elaborate t1 ctx
  term2 <- elaborate t2 ctx
  ty2 <- typeOf t2 ctx
  case typeOf t1 ctx of
    Right (TyArr ty3 ty4) -> do
      a <- (algoSubtypingCo EmptyQueue ty2 ty3)
      return (TmAppCo term1 (TmCast a term2))
    _ -> Left "Wrong use of elaborate"
elaborate (TmMerge t1 t2) ctx = do
  term1 <- elaborate t1 ctx
  term2 <- elaborate t2 ctx
  return (TmTupleCo term1 term2)
elaborate (TmRecord t str) ctx = do
  term <- elaborate t ctx
  return term
elaborate (TmProj t str) ctx = do
  term <- elaborate t ctx
  return term
elaborate (TmAnn t ty) ctx = do
  tyt <- typeOf t ctx
  term <- elaborate t ctx
  sub <- (algoSubtypingCo EmptyQueue tyt ty)
  return (TmCast sub term)
elaborate (TypeApp t ty) ctx = do
  term <- elaborate t ctx
  return (TmTAppCo term (convertType ty))
elaborate (TmAll ty t) ctx = do
  term <- elaborate t (ETypeVar ty ctx)
  return (TmTAbsCo term)

convertType :: FiType -> Type
convertType TyInt           = TyIntCo
convertType (TyAnd ty1 ty2) = TyProdCo (convertType ty1) (convertType ty2)
convertType TyBot           = TyAllCo (TyVarCo Z)
convertType TyTop           = TyTopCo
convertType (TyRecord ty _) = convertType ty
convertType (TyVar hnat)    = TyVarCo hnat
convertType (TyArr ty1 ty2) = TyArrCo (convertType ty1) (convertType ty2)
convertType (TyAll ty tyB)  = TyAllCo (convertType tyB)

pushQueue :: Queue -> Queue -> Queue
pushQueue EmptyQueue q              = q
pushQueue (LabelQueue str q) newq   = LabelQueue str (pushQueue q newq)
pushQueue (TypeQueue ty q) newq     = TypeQueue ty (pushQueue q newq)
pushQueue (TypeStarQueue ty q) newq = TypeStarQueue ty (pushQueue q newq)

isTypeConstant :: FiType -> Bool
isTypeConstant TyInt     = True
isTypeConstant TyBot     = True
isTypeConstant (TyVar _) = True
isTypeConstant _         = False

algoSubtypingCo :: Queue -> FiType -> FiType -> Either String Coercion
algoSubtypingCo q tyA TyTop = do
  a <- (calcQueueTop q)
  return (CoTrans a (CoTop))
algoSubtypingCo q tyA (TyAnd ty1 ty2) = do
  a <- (algoSubtypingCo q tyA ty1)
  b <- (algoSubtypingCo q tyA ty2)
  c <- (calcQueueAnd q)
  return (CoTrans c (CoTuple a b))
algoSubtypingCo q tyA (TyArr ty1 ty2) =
  algoSubtypingCo (pushQueue q (TypeQueue ty1 EmptyQueue)) tyA ty2
algoSubtypingCo EmptyQueue tyA tyB
  | tyA == tyB && isTypeConstant tyA = return CoId
algoSubtypingCo q TyBot c
  | isTypeConstant c = return CoBot
algoSubtypingCo q tyA (TyRecord tyB str) =
  algoSubtypingCo (pushQueue q (LabelQueue str EmptyQueue)) tyA tyB
algoSubtypingCo q tyA (TyAll ty1 ty2) =
  algoSubtypingCo (pushQueue q (TypeStarQueue ty1 EmptyQueue)) tyA ty2
algoSubtypingCo (TypeQueue ty q) (TyArr ty1 ty2) tyB
  | isTypeConstant tyB = do
    a <- (algoSubtypingCo EmptyQueue ty ty1)
    b <- (algoSubtypingCo q ty2 tyB)
    return (CoArrow a b)
algoSubtypingCo (LabelQueue str1 q) (TyRecord ty2 str2) tyB
  | isTypeConstant tyB && str1 == str2 = algoSubtypingCo q ty2 tyB
algoSubtypingCo q (TyAnd ty1 ty2) tyB
  | isTypeConstant tyB && algoSubtyping q ty1 tyB = do
    a <- (algoSubtypingCo q ty1 tyB)
    return (CoTrans a (CoProj1))
  | isTypeConstant tyB && algoSubtyping q ty2 tyB = do
    a <- (algoSubtypingCo q ty2 tyB)
    return (CoTrans a (CoProj2))
algoSubtypingCo (TypeStarQueue ty q) (TyAll ty1 ty2) tyB
  | isTypeConstant tyB = do
    a <- (algoSubtypingCo q ty2 tyB)
    return (CoAll a)
algoSubtypingCo _ _ _ = Left "no subtype"

calcQueueTop :: Queue -> Either String Coercion
calcQueueTop EmptyQueue = return CoTop
calcQueueTop (LabelQueue _ q) = do
  a <- (calcQueueTop q)
  return (CoTrans a CoId)
calcQueueTop (TypeQueue _ q) = do
  a <- (calcQueueTop q)
  return (CoTrans (CoArrow CoTop a) CoTopArrow)
calcQueueTop (TypeStarQueue _ q) = do
  a <- (calcQueueTop q)
  return (CoTrans (CoAll a) CoTopAll)

calcQueueAnd :: Queue -> Either String Coercion
calcQueueAnd EmptyQueue = return CoTop
calcQueueAnd (LabelQueue _ q) = do
  a <- (calcQueueAnd q)
  return (CoTrans a CoId)
calcQueueAnd (TypeQueue _ q) = do
  a <- (calcQueueAnd q)
  return (CoTrans (CoArrow CoId a) CoDistArrow)
calcQueueAnd (TypeStarQueue _ q) = do
  a <- (calcQueueAnd q)
  return (CoTrans (CoAll a) CoDistAll)

goodelaborate term = do
  ty <- typeOf term Nil
  elaborate term Nil
