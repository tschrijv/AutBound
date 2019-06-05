import HaskellOutput

isVal :: Term -> Bool
isVal (TmAbs x t)              = True
isVal (TmTAbs t1)              = True
isVal _ = False

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
