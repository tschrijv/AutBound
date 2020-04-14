module Elaborate where

import           FCoBase
import qualified FiPlusBase as FP
import qualified FiImpl as FIm

varTranslate :: FP.Variable -> Variable
varTranslate FP.Z              = Z
varTranslate (FP.STermVar var) = STermVar (varTranslate var)
varTranslate (FP.STypeVar var) = STypeVar (varTranslate var)

getTypeFromEnv :: FIm.Env -> FP.Variable -> Either String FP.FiType
getTypeFromEnv (FIm.ETermVar ty _) FP.Z = return ty
getTypeFromEnv _ FP.Z = Left "wrong or no binding for FiTerm"
getTypeFromEnv (FIm.ETermVar _ rest) (FP.STermVar h) = getTypeFromEnv rest h
getTypeFromEnv _ (FP.STermVar h) = Left "wrong FiTerm binding"
getTypeFromEnv (FIm.ETypeVar _ rest) (FP.STypeVar h) = getTypeFromEnv rest h
getTypeFromEnv _ (FP.STypeVar h) = Left "No variable FP.FiType"

elaborate :: FP.FiTerm -> FIm.Env -> Either String Term
elaborate FP.TmTop ctx = return TmTop
elaborate (FP.TmInt i) ctx = return (TmInt i)
elaborate (FP.TmVar hnat) ctx = return (TmVar (varTranslate hnat))
elaborate (FP.TmAbs t ty) ctx = do
  term <- elaborate t (FIm.ETermVar ty ctx)
  return (TmAbs term (convertType ty))
elaborate (FP.TmApp t1 t2) ctx = do
  term1 <- elaborate t1 ctx
  term2 <- elaborate t2 ctx
  ty2 <- FIm.typeOf t2 ctx
  case FIm.typeOf t1 ctx of
    Right (FP.TyArr ty3 ty4) -> do
      a <- (algoSubtypingCo FIm.EmptyQueue ty2 ty3)
      return (TmApp term1 (TmCast a term2))
    _ -> Left "Wrong use of elaborate"
elaborate (FP.TmMerge t1 t2) ctx = do
  term1 <- elaborate t1 ctx
  term2 <- elaborate t2 ctx
  return (TmTuple term1 term2)
elaborate (FP.TmRecord t str) ctx = do
  term <- elaborate t ctx
  return term
elaborate (FP.TmProj t str) ctx = do
  term <- elaborate t ctx
  return term
elaborate (FP.TmAnn t ty) ctx = do
  tyt <- FIm.typeOf t ctx
  term <- elaborate t ctx
  sub <- (algoSubtypingCo FIm.EmptyQueue tyt ty)
  return (TmCast sub term)
elaborate (FP.TypeApp t ty) ctx = do
  term <- elaborate t ctx
  return (TmTApp term (convertType ty))
elaborate (FP.TmAll ty t) ctx = do
  term <- elaborate t (FIm.ETypeVar ty ctx)
  return (TmTAbs term)

convertType :: FP.FiType -> Type
convertType FP.TyInt           = TyInt
convertType (FP.TyAnd ty1 ty2) = TyProd (convertType ty1) (convertType ty2)
convertType FP.TyBot           = TyAll (TyVar Z)
convertType FP.TyTop           = TyTop
convertType (FP.TyRecord ty _) = convertType ty
convertType (FP.TyVar hnat)    = TyVar (varTranslate hnat)
convertType (FP.TyArr ty1 ty2) = TyArr (convertType ty1) (convertType ty2)
convertType (FP.TyAll ty tyB)  = TyAll (convertType tyB)

pushQueue :: FIm.Queue -> FIm.Queue -> FIm.Queue
pushQueue FIm.EmptyQueue q              = q
pushQueue (FIm.LabelQueue str q) newq   = FIm.LabelQueue str (pushQueue q newq)
pushQueue (FIm.TypeQueue ty q) newq     = FIm.TypeQueue ty (pushQueue q newq)
pushQueue (FIm.TypeStarQueue ty q) newq = FIm.TypeStarQueue ty (pushQueue q newq)

isTypeConstant :: FP.FiType -> Bool
isTypeConstant FP.TyInt     = True
isTypeConstant FP.TyBot     = True
isTypeConstant (FP.TyVar _) = True
isTypeConstant _            = False

algoSubtypingCo :: FIm.Queue -> FP.FiType -> FP.FiType -> Either String Coercion
algoSubtypingCo q tyA FP.TyTop = do
  a <- (calcQueueTop q)
  return (CoTrans a (CoTopAll))
algoSubtypingCo q tyA (FP.TyAnd ty1 ty2) = do
  a <- (algoSubtypingCo q tyA ty1)
  b <- (algoSubtypingCo q tyA ty2)
  c <- (calcQueueAnd q)
  return (CoTrans c (CoTuple a b))
algoSubtypingCo q tyA (FP.TyArr ty1 ty2) =
  algoSubtypingCo (pushQueue q (FIm.TypeQueue ty1 FIm.EmptyQueue)) tyA ty2
algoSubtypingCo FIm.EmptyQueue tyA tyB
  | tyA == tyB && isTypeConstant tyA = return CoId
algoSubtypingCo q FP.TyBot c
  | isTypeConstant c = return $ CoBot (convertType c)
algoSubtypingCo q tyA (FP.TyRecord tyB str) =
  algoSubtypingCo (pushQueue q (FIm.LabelQueue str FIm.EmptyQueue)) tyA tyB
algoSubtypingCo q tyA (FP.TyAll ty1 ty2) =
  algoSubtypingCo (pushQueue q (FIm.TypeStarQueue ty1 FIm.EmptyQueue)) tyA ty2
algoSubtypingCo (FIm.TypeQueue ty q) (FP.TyArr ty1 ty2) tyB
  | isTypeConstant tyB = do
    a <- (algoSubtypingCo FIm.EmptyQueue ty ty1)
    b <- (algoSubtypingCo q ty2 tyB)
    return (CoArrow a b)
algoSubtypingCo (FIm.LabelQueue str1 q) (FP.TyRecord ty2 str2) tyB
  | isTypeConstant tyB && str1 == str2 = algoSubtypingCo q ty2 tyB
algoSubtypingCo q (FP.TyAnd ty1 ty2) tyB
  | isTypeConstant tyB && FIm.algoSubtyping q ty1 tyB = do
    a <- (algoSubtypingCo q ty1 tyB)
    return (CoTrans a (CoProj1 (convertType ty1)))
  | isTypeConstant tyB && FIm.algoSubtyping q ty2 tyB = do
    a <- (algoSubtypingCo q ty2 tyB)
    return (CoTrans a (CoProj2 (convertType ty2)))
algoSubtypingCo (FIm.TypeStarQueue ty q) (FP.TyAll ty1 ty2) tyB
  | isTypeConstant tyB = do
    a <- (algoSubtypingCo q ty2 tyB)
    return (CoAll a)
algoSubtypingCo _ _ _ = Left "no subtype"

calcQueueTop :: FIm.Queue -> Either String Coercion
calcQueueTop FIm.EmptyQueue = return CoTopAll
calcQueueTop (FIm.LabelQueue _ q) = do
  a <- (calcQueueTop q)
  return (CoTrans a CoId)
calcQueueTop (FIm.TypeQueue _ q) = do
  a <- (calcQueueTop q)
  return (CoTrans (CoArrow CoTopAll a) CoTopArrow)
calcQueueTop (FIm.TypeStarQueue _ q) = do
  a <- (calcQueueTop q)
  return (CoTrans (CoAll a) CoTopAll)

calcQueueAnd :: FIm.Queue -> Either String Coercion
calcQueueAnd FIm.EmptyQueue = return CoTopAll
calcQueueAnd (FIm.LabelQueue _ q) = do
  a <- (calcQueueAnd q)
  return (CoTrans a CoId)
calcQueueAnd (FIm.TypeQueue _ q) = do
  a <- (calcQueueAnd q)
  return (CoTrans (CoArrow CoId a) CoDistArrow)
calcQueueAnd (FIm.TypeStarQueue _ q) = do
  a <- (calcQueueAnd q)
  return (CoTrans (CoAll a) CoDistAll)

goodelaborate term = do
  ty <- FIm.typeOf term FIm.Nil
  elaborate term FIm.Nil
