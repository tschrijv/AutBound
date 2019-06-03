module ExEffImpl
  ( Value(..)
  , OperationCompTuple(..)
  , Handler(..)
  , Computation(..)
  , ValueType(..)
  , SkeletonType(..)
  , Coercion(..)
  , SimpleCoercionType(..)
  , CoercionType(..)
  , Dirt(..)
  , ComputationType(..)
  , HNat(..)
  , Env(..)
  , fullEval
  , fullEvalComputation
  , Op(..)
  ) where

import           Data.List
import           Data.Maybe
import           ExEff
import           Operations

--end of generated code
isTerminalVal :: Value -> Bool
isTerminalVal TmUnit               = True
isTerminalVal (TmFun _ _)          = True
isTerminalVal (TmHandler _)        = True
isTerminalVal (TmCoAbs _ _)        = True
isTerminalVal (TmDirtAbs _)        = True
isTerminalVal (TmTSkellAbs _)      = True
isTerminalVal (TmValueTypeAbs _ _) = True
isTerminalVal _                    = False

isResultVal :: Value -> Bool
isResultVal (TmCast val (CoArrow co1 co2))   = isResultVal val
isResultVal (TmCast val (CoHandler co1 co2)) = isResultVal val
isResultVal (TmCast val (CoskeletonAll co))  = isResultVal val
isResultVal (TmCast val (CoTypeAll co1 ty))  = isResultVal val
isResultVal (TmCast val (CoDirt co))         = isResultVal val
isResultVal (TmCast val (CoCoArrow pi co))   = isResultVal val
isResultVal v                                = isTerminalVal v

isTerminalComp :: Computation -> Bool
isTerminalComp (ReturnComp val)                     = isResultVal val
isTerminalComp (CastComp c (CoComputation co1 co2)) = isTerminalComp c
isTerminalComp _                                    = False

isResultComp :: Computation -> Bool
isResultComp (OpComp val ty comp op) = isResultVal val
isResultComp c                       = isTerminalComp c

stepEval :: Value -> Maybe Value
stepEval (TmCast val co)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (TmCast newval co)
  | co == CoUnit = return val
stepEval (TmCoApp val co)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (TmCoApp newval co)
stepEval (TmDirtApp val ty)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (TmDirtApp newval ty)
stepEval (TmTSkelApp val ty)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (TmTSkelApp newval ty)
stepEval (TmValueTypeApp val co)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (TmValueTypeApp newval co)
stepEval (TmTSkelApp (TmCast val (CoskeletonAll co)) skel) =
  return (TmCast (TmTSkelApp val skel) newco)
  where
    newco =
      coercionshiftminus
        (SSkelTypeVar Z)
        (coercionskeletonTypeSubstitute
           (skeletonTypeshiftplus (SSkelTypeVar Z) skel)
           Z
           co)
stepEval (TmValueTypeApp (TmCast val (CoTypeAll co skel)) ty) =
  return (TmCast (TmValueTypeApp val ty) newco)
  where
    newco =
      coercionshiftminus
        (STypeVar Z)
        (coercionvalueTypeSubstitute (valueTypeshiftplus (STypeVar Z) ty) Z co)
stepEval (TmDirtApp (TmCast val (CodirtAll co)) dirt) =
  return (TmCast (TmDirtApp val dirt) newco)
  where
    newco =
      coercionshiftminus
        (SDirtVar Z)
        (coerciondirtSubstitute (dirtshiftplus (SDirtVar Z) dirt) Z co)
stepEval (TmCoApp (TmCast val (CoCoArrow pi co1)) co2) =
  return (TmCast (TmCoApp val co2) co1)
stepEval (TmCoApp (TmCoAbs val pi) co) =
  return
    (valueshiftminus
       (SCoVar Z)
       (valuecoercionSubstitute (coercionshiftplus (SCoVar Z) co) Z val))
stepEval (TmDirtApp (TmDirtAbs val) dirt) =
  return
    (valueshiftminus
       (SDirtVar Z)
       (valuedirtSubstitute (dirtshiftplus (SDirtVar Z) dirt) Z val))
stepEval (TmTSkelApp (TmTSkellAbs val) skel) =
  return
    (valueshiftminus
       (SSkelTypeVar Z)
       (valueskeletonTypeSubstitute
          (skeletonTypeshiftplus (SSkelTypeVar Z) skel)
          Z
          val))
stepEval (TmValueTypeApp (TmValueTypeAbs val skel) ty) =
  return
    (valueshiftminus
       (STypeVar Z)
       (valuevalueTypeSubstitute (valueTypeshiftplus (STypeVar Z) ty) Z val))
stepEval _ = Nothing

isReturnCast :: Computation -> Bool
isReturnCast (CastComp val (CoComputation co1 co2)) = isReturnCast val
isReturnCast (ReturnComp val)                       = True
isReturnCast _                                      = False

eraseComputationsCoercions :: Computation -> Value
eraseComputationsCoercions (CastComp val (CoComputation co1 co2)) =
  (TmCast (eraseComputationsCoercions val) co1)
eraseComputationsCoercions (ReturnComp val) = val

isOpInHandler :: Op -> [OperationCompTuple] -> Bool
isOpInHandler _ [] = False
isOpInHandler op1 ((OpAndComp c op2):rest) =
  if op1 == op2
    then True
    else isOpInHandler op1 rest

getCompHandler :: Op -> [OperationCompTuple] -> Maybe Computation
getCompHandler _ [] = Nothing
getCompHandler op1 ((OpAndComp c op2):rest) =
  if op1 == op2
    then return c
    else getCompHandler op1 rest

--evaluates a term
fullEval :: Value -> Value
fullEval t = maybe t (fullEval) t2
  where
    t2 = stepEval t

stepEvalComp :: Computation -> Maybe Computation
stepEvalComp (ComputationApp v1 v2)
  | not (isResultVal v1) = do
    newval <- stepEval v1
    return (ComputationApp newval v2)
  | not (isResultVal v2) = do
    newval <- stepEval v2
    return (ComputationApp v1 newval)
stepEvalComp (ComputationApp (TmFun c ty) val) =
  return
    (computationshiftminus
       (STermVar Z)
       (computationvalueSubstitute (valueshiftplus (STermVar Z) val) Z c))
stepEvalComp (ComputationApp (TmCast val1 (CoArrow co1 co2)) val2) =
  return (CastComp (ComputationApp val1 (TmCast val2 co1)) co2)
stepEvalComp (LetComp val c)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (LetComp newval c)
  | otherwise =
    return
      (computationshiftminus
         (STermVar Z)
         (computationvalueSubstitute (valueshiftplus (STermVar Z) val) Z c))
stepEvalComp (ReturnComp val)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (ReturnComp newval)
stepEvalComp (DoComp c1 c2)
  | not (isResultComp c1) = do
    result <- stepEvalComp c1
    return (DoComp result c2)
stepEvalComp (HandleComp c val)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (HandleComp c newval)
  | not (isResultComp c) = do
    newcomp <- stepEvalComp c
    return (HandleComp newcomp val)
stepEvalComp (HandleComp c (TmCast val (CoHandler co1 co2))) =
  return (CastComp (HandleComp (CastComp c co1) val) co2)
stepEvalComp (CastComp c co)
  | not (isResultComp c) = do
    newc <- stepEvalComp c
    return (CastComp c co)
stepEvalComp (OpComp val ty comp op)
  | not (isResultVal val) = do
    newval <- stepEval val
    return (OpComp newval ty comp op)
stepEvalComp (CastComp (OpComp val ty comp op) co) =
  return (OpComp val ty (CastComp comp co) op)
stepEvalComp (DoComp (OpComp val ty comp op) c2) =
  return (OpComp val ty (DoComp comp c2) op)
stepEvalComp (DoComp c c2)
  | isReturnCast c =
    return
      (computationshiftminus
         (STermVar Z)
         (computationvalueSubstitute
            (valueshiftplus (STermVar Z) (eraseComputationsCoercions c))
            Z
            c2))
stepEvalComp (HandleComp c (TmHandler (ReturnHandler ops ty cr)))
  | isReturnCast c =
    return
      (computationshiftminus
         (STermVar Z)
         (computationvalueSubstitute
            (valueshiftplus (STermVar Z) (eraseComputationsCoercions c))
            Z
            cr))
stepEvalComp (HandleComp (OpComp val1 ty1 comp op) (TmHandler (ReturnHandler ops ty2 cr)))
  | not (isOpInHandler op ops) =
    return
      (OpComp
         val1
         ty1
         (HandleComp comp (TmHandler (ReturnHandler ops ty2 cr)))
         op)
  | isOpInHandler op ops = return final
  where
    cop = fromJust (getCompHandler op ops)
    intermediate =
      (computationshiftminus
         (STermVar Z)
         (computationvalueSubstitute
            (valueshiftplus
               (STermVar Z)
               (TmFun
                  (HandleComp comp (TmHandler (ReturnHandler ops ty2 cr)))
                  ty1))
            Z
            cop))
    final =
      (computationshiftminus
         (STermVar Z)
         (computationvalueSubstitute
            (valueshiftplus (STermVar Z) val1)
            Z
            intermediate))
stepEvalComp _ = Nothing

fullEvalComputation :: Computation -> Computation
fullEvalComputation c = maybe c (fullEvalComputation) c2
  where
    c2 = stepEvalComp c

rewriteTypeToCoercion :: ValueType -> Coercion
rewriteTypeToCoercion (ValTyVar hnat) = CoTypeVar (ValTyVar hnat)
rewriteTypeToCoercion (ValTUnit) = CoUnit
rewriteTypeToCoercion (ValTyArr ty1 (ComputationTy ty2 dirt)) =
  CoArrow
    (rewriteTypeToCoercion ty1)
    (CoComputation (rewriteTypeToCoercion ty2) (CoDirt dirt))
rewriteTypeToCoercion (ValTyHandler (ComputationTy ty1 dirt1) (ComputationTy ty2 dirt2)) =
  CoHandler
    (CoComputation (rewriteTypeToCoercion ty1) (CoDirt dirt1))
    (CoComputation (rewriteTypeToCoercion ty2) (CoDirt dirt2))
rewriteTypeToCoercion (ValTyAllSkel ty) =
  CoskeletonAll (rewriteTypeToCoercion ty)
rewriteTypeToCoercion (ValTyAll valty skel) =
  CoTypeAll (rewriteTypeToCoercion valty) skel
rewriteTypeToCoercion (ValTyAllDirt valty) =
  CodirtAll (rewriteTypeToCoercion valty)
rewriteTypeToCoercion (ValTyCoArr pi ty) =
  CoCoArrow pi (rewriteTypeToCoercion ty)

rewriteCoercion :: Coercion -> Coercion
rewriteCoercion (CoTypeVar ty) = rewriteTypeToCoercion ty
rewriteCoercion (CoArrow co1 co2) =
  CoArrow (rewriteCoercion co1) (rewriteCoercion co2)
rewriteCoercion (CoHandler co1 co2) =
  CoHandler (rewriteCoercion co1) (rewriteCoercion co2)
rewriteCoercion (UnionOp co1 op) = UnionOp (rewriteCoercion co1) op
rewriteCoercion (CoskeletonAll co) = CoskeletonAll (rewriteCoercion co)
rewriteCoercion (CoTypeAll co skel) = CoTypeAll (rewriteCoercion co) skel
rewriteCoercion (CoCoArrow pi co) = CoCoArrow pi (rewriteCoercion co)
rewriteCoercion (CoComputation co1 co2) =
  CoComputation (rewriteCoercion co1) (rewriteCoercion co2)
rewriteCoercion co = co

test4 =
  freeVariablesComputation
    Z
    (ComputationApp
       (TmFun (ReturnComp (TmVar (STermVar (STypeVar Z)))) ValTUnit)
       TmUnit)
