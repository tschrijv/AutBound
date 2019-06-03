module FiImpl
  ( FiTerm(..)
  , FiType(..)
  , Queue(..)
  , typeOf
  , HNat(..)
  , Env(..)
  , fiTermshiftplus
  , fiTermshiftminus
  , fiTypeshiftminus
  , fiTypeshiftplus
  , algoSubtyping
  , disjointness
  ) where

import           Fi

--end generated code
getTypeFromEnv :: Env -> HNat -> Either String FiType
getTypeFromEnv (ETermVar ty _) Z = return ty
getTypeFromEnv _ Z = Left "wrong or no binding for FiTerm"
getTypeFromEnv (ETermVar _ rest) (STermVar h) = getTypeFromEnv rest h
getTypeFromEnv _ (STermVar h) = Left "wrong FiTerm binding"
getTypeFromEnv (ETypeVar _ rest) (STypeVar h) = getTypeFromEnv rest h
getTypeFromEnv _ (STypeVar h) = Left "No variable FiType"

--end generated code
getTypeFromEnvDis :: Env -> HNat -> Either String FiType
getTypeFromEnvDis (ETypeVar ty _) Z = return ty
getTypeFromEnvDis _ Z = error "wrong or no binding for typevar"
getTypeFromEnvDis (ETermVar _ rest) (STermVar h) = getTypeFromEnvDis rest h
getTypeFromEnvDis _ (STermVar h) = error "wrong FiTerm binding"
getTypeFromEnvDis (ETypeVar _ rest) (STypeVar h) = getTypeFromEnvDis rest h
getTypeFromEnvDis _ (STypeVar h) = error "No variable FiType"

typeOf :: FiTerm -> Env -> Either String FiType
typeOf TmTop ctx = return TyTop
typeOf (TmInt i) ctx = return TyInt
typeOf (TmVar hnat) ctx = getTypeFromEnv ctx hnat
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
            else if algoSubtyping EmptyQueue ty ty1
                   then Right ty2
                   else Left "No subtyping relation found"
        Left a -> Left a
    Left a -> Left a
    _ -> Left "arrow FiType expected"
typeOf (TmMerge t1 t2) ctx = do
  ty1 <- typeOf t1 ctx
  ty2 <- typeOf t2 ctx
  isdis <- disjointness ctx ty1 ty2
  if isdis
    then return (TyAnd ty1 ty2)
    else Left "not disjoinnt"
typeOf (TmRecord t str) ctx = do
  ty <- typeOf t ctx
  return (TyRecord ty str)
typeOf (TmProj t str) ctx =
  case typeOf t ctx of
    Right (TyRecord tyR str2) ->
      if str == str2
        then return tyR
        else Left "Wrong label of record"
    Left a -> Left a
    _ -> Left "didn't receive record FiType"
typeOf (TmAnn t ty) ctx = do
  tyInfer <- typeOf t ctx
  if tyInfer == ty
    then return ty
    else if algoSubtyping EmptyQueue tyInfer ty
           then return ty
           else Left "No derivation found"
typeOf (TypeApp t ty) ctx =
  case (typeOf t ctx) of
    Right (TyAll anyty ty2) -> do
      a <- disjointness ctx ty anyty
      if a
        then return
               (fiTypeshiftminus
                  (STypeVar Z)
                  (fiTypefiTypeSubstitute
                     (fiTypeshiftplus (STypeVar Z) ty)
                     Z
                     ty2))
        else Left "not disjoint"
    Left a -> Left a
    _ -> Left "not a FiType abstraction"
typeOf (TmAll ty t) ctx = do
  ty2 <- typeOf t (ETypeVar ty ctx)
  return (TyAll ty ty2)

data Queue
  = EmptyQueue
  | LabelQueue String
               Queue
  | TypeQueue FiType
              Queue
  | TypeStarQueue FiType
                  Queue
  deriving (Show, Eq)

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

algoSubtyping :: Queue -> FiType -> FiType -> Bool
algoSubtyping q tyA TyTop = True
algoSubtyping q tyA (TyAnd ty1 ty2) =
  algoSubtyping q tyA ty1 && algoSubtyping q tyA ty2
algoSubtyping q tyA (TyArr ty1 ty2) =
  algoSubtyping (pushQueue q (TypeQueue ty1 EmptyQueue)) tyA ty2
algoSubtyping EmptyQueue tyA tyB
  | tyA == tyB && isTypeConstant tyA = True
algoSubtyping q TyBot c
  | isTypeConstant c = True
algoSubtyping q tyA (TyRecord tyB str) =
  algoSubtyping (pushQueue q (LabelQueue str EmptyQueue)) tyA tyB
algoSubtyping q tyA (TyAll ty1 ty2) =
  algoSubtyping (pushQueue q (TypeStarQueue ty1 EmptyQueue)) tyA ty2
algoSubtyping (TypeQueue ty q) (TyArr ty1 ty2) tyB
  | isTypeConstant tyB =
    algoSubtyping EmptyQueue ty ty1 && algoSubtyping q ty2 tyB
algoSubtyping (LabelQueue str1 q) (TyRecord ty2 str2) tyB
  | isTypeConstant tyB && str1 == str2 = algoSubtyping q ty2 tyB
algoSubtyping q (TyAnd ty1 ty2) tyB
  | isTypeConstant tyB = algoSubtyping q ty1 tyB || algoSubtyping q ty2 tyB
algoSubtyping (TypeStarQueue ty q) (TyAll ty1 ty2) tyB
  | isTypeConstant tyB =
    algoSubtyping EmptyQueue ty ty1 && algoSubtyping q ty2 tyB
algoSubtyping _ _ _ = False

toplike :: FiType -> Bool
toplike TyTop           = True
toplike (TyAnd t1 t2)   = toplike t1 && toplike t2
toplike (TyArr t1 t2)   = toplike t2
toplike (TyRecord ty _) = toplike ty
toplike (TyAll ty1 ty2) = toplike ty2
toplike _               = False

disjointness :: Env -> FiType -> FiType -> Either String Bool
disjointness ctx (TyArr ty1 ty2) (TyArr ty3 ty4) = disjointness ctx ty2 ty4
disjointness ctx (TyAnd ty1 ty2) ty3 = do
  a <- disjointness ctx ty1 ty3
  b <- disjointness ctx ty2 ty3
  return (a && b)
disjointness ctx ty3 (TyAnd ty1 ty2) = do
  a <- disjointness ctx ty3 ty1
  b <- disjointness ctx ty3 ty2
  return (a && b)
disjointness ctx (TyRecord ty1 label1) (TyRecord ty2 label2) = do
  a <- disjointness ctx ty1 ty2
  return
    (if label1 == label2
       then a
       else True)
disjointness ctx (TyVar hnat) ty2 = do
  a <- (getTypeFromEnvDis ctx hnat)
  return (algoSubtyping EmptyQueue a ty2)
disjointness ctx ty1 (TyVar hnat) = do
  a <- (getTypeFromEnvDis ctx hnat)
  return (algoSubtyping EmptyQueue a ty1)
disjointness ctx (TyAll ty1 ty2) (TyAll ty3 ty4) =
  disjointness (ETypeVar (TyAnd ty1 ty2) ctx) ty2 ty4
disjointness _ ty1 ty2
  | toplike ty1 || toplike ty2 = return True
  | otherwise = dAx ty1 ty2

dAx :: FiType -> FiType -> Either String Bool
dAx TyInt (TyArr ty1 ty2)           = return True
dAx TyInt (TyRecord ty _)           = return True
dAx TyInt (TyAll _ _)               = return True
dAx (TyArr ty1 ty2) (TyAll ty3 ty4) = return True
dAx (TyArr ty1 ty2) (TyRecord _ _)  = return True
dAx (TyAll _ _) (TyRecord _ _)      = return True
dAx _ _                             = return False
