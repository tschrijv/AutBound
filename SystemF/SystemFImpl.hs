import SystemFBase

data Env
  = Nil
  | ETypeVar Env
  | ETermVar Type
             Env
  deriving (Show, Eq)

nth :: Env -> Variable -> Maybe Env
nth env Z = Just env
nth (ETypeVar env) (STypeVar x) = nth env x
nth (ETermVar _ env) (STermVar x) = nth env x
nth _ _ = Nothing

isVal :: Term -> Bool
isVal (TmAbs x t)              = True
isVal (TmTAbs t1)              = True
isVal _ = False

getTypeFromEnv :: Env -> Variable -> Either String Type
getTypeFromEnv e v = go e v Z where
  go :: Env -> Variable -> Variable -> Either String Type
  go (ETermVar ty _)   Z            shift = return $ typeshiftplus (plus shift (STermVar Z)) ty
  go _                 Z            _     = Left "wrong or no binding for term"
  go (ETermVar _ rest) (STermVar h) shift = go rest h (plus shift (STermVar Z))
  go (ETypeVar rest)   (STypeVar h) shift = go rest h (plus shift (STypeVar Z))
  go _                 (STermVar h) _     = Left "wrong term binding"
  go _                 (STypeVar h) _     = Left "No variable type"

--evaluation
stepEval :: Term -> Maybe Term
--function application
stepEval (TmApp (TmAbs t ty) t2)
  | isVal t2 =
    Just
      (termshiftminus
         (STermVar Z)
         (termTermSubstitute (termshiftplus (STermVar Z) t2) Z t))
--type application
stepEval (TmTApp (TmTAbs t) ty) =
  Just
    (termshiftminus
       (STypeVar Z)
       (termTypeSubstitute (typeshiftplus (STypeVar Z) ty) Z t))
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
stepEval _ = Nothing

--evaluates a term
fullEval :: Term -> Term
fullEval t = maybe t (fullEval) t2
  where
    t2 = stepEval t

wellFormed :: Type -> Env -> Bool
wellFormed (TyVar i) env       = case (nth env i) of
  Nothing -> False
  Just (ETermVar _ _) -> False
  Just (ETypeVar _) -> True
  Just Nil -> False
wellFormed (TyArr ty1 ty2) env = wellFormed ty1 env && wellFormed ty2 env
wellFormed (TyAll ty) env      = wellFormed ty (ETypeVar env)
wellFormed (TyBase) env        = True

typeOf :: Term -> Env -> Either String Type
typeOf (TmVar nat) ctx = getTypeFromEnv ctx nat
typeOf (TmAbs t ty) ctx =
  if (wellFormed ty ctx) then do
    ty2 <- typeOf t (ETermVar ty ctx)
    return $ TyArr ty (typeshiftminus (STermVar Z) ty2)
  else Left (show ty ++ " is not well-formed")
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
  if (wellFormed ty ctx) then
    case (typeOf t ctx) of
      Right (TyAll ty2) -> return
        (typeshiftminus
           (STypeVar Z)
           (typeTypeSubstitute (typeshiftplus (STypeVar Z) ty) Z ty2))
      Left a -> Left a
      Right _ -> Left "not a type abstraction"
  else Left (show ty ++ " is not well-formed")
typeOf (TmTAbs t) ctx = do
  ty <- typeOf t (ETypeVar ctx)
  return (TyAll ty)
