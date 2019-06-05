module ExEff
  ( Env(..)
  , HNat(..)
  , Coercion(..)
  , coercioncoercionSubstitute
  , coercionvalueTypeSubstitute
  , coercionskeletonTypeSubstitute
  , coerciondirtSubstitute
  , freeVariablesCoercion
  , coercionshiftplus
  , coercionshiftminus
  , ComputationType(..)
  , computationTypevalueTypeSubstitute
  , computationTypeskeletonTypeSubstitute
  , computationTypedirtSubstitute
  , freeVariablesComputationType
  , computationTypeshiftplus
  , computationTypeshiftminus
  , Dirt(..)
  , dirtdirtSubstitute
  , freeVariablesDirt
  , dirtshiftplus
  , dirtshiftminus
  , SkeletonType(..)
  , skeletonTypeskeletonTypeSubstitute
  , freeVariablesSkeletonType
  , skeletonTypeshiftplus
  , skeletonTypeshiftminus
  , SimpleCoercionType(..)
  , simpleCoercionTypevalueTypeSubstitute
  , simpleCoercionTypeskeletonTypeSubstitute
  , simpleCoercionTypedirtSubstitute
  , freeVariablesSimpleCoercionType
  , simpleCoercionTypeshiftplus
  , simpleCoercionTypeshiftminus
  , CoercionType(..)
  , coercionTypevalueTypeSubstitute
  , coercionTypeskeletonTypeSubstitute
  , coercionTypedirtSubstitute
  , freeVariablesCoercionType
  , coercionTypeshiftplus
  , coercionTypeshiftminus
  , ValueType(..)
  , valueTypevalueTypeSubstitute
  , valueTypeskeletonTypeSubstitute
  , valueTypedirtSubstitute
  , freeVariablesValueType
  , valueTypeshiftplus
  , valueTypeshiftminus
  , Computation(..)
  , computationvalueSubstitute
  , computationvalueTypeSubstitute
  , computationskeletonTypeSubstitute
  , computationdirtSubstitute
  , computationcoercionSubstitute
  , freeVariablesComputation
  , computationshiftplus
  , computationshiftminus
  , Handler(..)
  , handlervalueSubstitute
  , handlervalueTypeSubstitute
  , handlerskeletonTypeSubstitute
  , handlerdirtSubstitute
  , handlercoercionSubstitute
  , freeVariablesHandler
  , handlershiftplus
  , handlershiftminus
  , OperationCompTuple(..)
  , operationCompTuplevalueSubstitute
  , operationCompTuplevalueTypeSubstitute
  , operationCompTupleskeletonTypeSubstitute
  , operationCompTupledirtSubstitute
  , operationCompTuplecoercionSubstitute
  , freeVariablesOperationCompTuple
  , operationCompTupleshiftplus
  , operationCompTupleshiftminus
  , Value(..)
  , valuevalueSubstitute
  , valuevalueTypeSubstitute
  , valueskeletonTypeSubstitute
  , valuedirtSubstitute
  , valuecoercionSubstitute
  , freeVariablesValue
  , valueshiftplus
  , valueshiftminus
  , generateHnatCoVar
  , generateHnatTypeVar
  , generateHnatDirtVar
  , generateHnatSkelTypeVar
  , generateHnatTermVar
  ) where

import           Data.List
import           Operations

data Coercion
  = CoercionVar HNat
  | CoUnit
  | CoTypeVar ValueType
  | CoDirt Dirt
  | CoArrow Coercion
            Coercion
  | CoHandler Coercion
              Coercion
  | CoEmptyDirt
  | UnionOp Coercion
            Op
  | CoskeletonAll Coercion
  | CoTypeAll Coercion
              SkeletonType
  | CodirtAll Coercion
  | CoCoArrow SimpleCoercionType
              Coercion
  | CoComputation Coercion
                  Coercion
  deriving (Show, Eq)

data ComputationType =
  ComputationTy ValueType
                Dirt
  deriving (Show, Eq)

data Dirt
  = DirtVariable HNat
  | EmptyDirt
  | UnionDirt Dirt
              Op
  deriving (Show, Eq)

data SkeletonType
  = SkelTUnit
  | SkellAllType SkeletonType
  | SkelVar HNat
  | SkelArr SkeletonType
            SkeletonType
  deriving (Show, Eq)

data SimpleCoercionType
  = DirtCoTypes Dirt
                Dirt
  | ValTypes ValueType
             ValueType
  deriving (Show, Eq)

data CoercionType
  = CoSimple SimpleCoercionType
  | CoComp ComputationType
           ComputationType
  deriving (Show, Eq)

data ValueType
  = ValTyVar HNat
  | ValTUnit
  | ValTyArr ValueType
             ComputationType
  | ValTyHandler ComputationType
                 ComputationType
  | ValTyAllSkel ValueType
  | ValTyAll ValueType
             SkeletonType
  | ValTyAllDirt ValueType
  | ValTyCoArr SimpleCoercionType
               ValueType
  deriving (Show, Eq)

data Computation
  = ReturnComp Value
  | HandleComp Computation
               Value
  | ComputationApp Value
                   Value
  | LetComp Value
            Computation
  | DoComp Computation
           Computation
  | CastComp Computation
             Coercion
  | OpComp Value
           ValueType
           Computation
           Op
  deriving (Show, Eq)

data Handler =
  ReturnHandler [OperationCompTuple]
                ValueType
                Computation
  deriving (Show, Eq)

data OperationCompTuple =
  OpAndComp Computation
            Op
  deriving (Show, Eq)

data Value
  = TmVar HNat
  | TmFun Computation
          ValueType
  | TmTSkellAbs Value
  | TmTSkelApp Value
               SkeletonType
  | TmValueTypeAbs Value
                   SkeletonType
  | TmValueTypeApp Value
                   ValueType
  | TmDirtAbs Value
  | TmDirtApp Value
              Dirt
  | TmCoAbs Value
            SimpleCoercionType
  | TmCoApp Value
            Coercion
  | TmCast Value
           Coercion
  | TmUnit
  | TmHandler Handler
  deriving (Show, Eq)

data HNat
  = Z
  | SCoVar HNat
  | STypeVar HNat
  | SDirtVar HNat
  | SSkelTypeVar HNat
  | STermVar HNat
  deriving (Show, Eq)

plus x1 (SCoVar x2)       = SCoVar (plus x1 x2)
plus x1 (STypeVar x2)     = STypeVar (plus x1 x2)
plus x1 (SDirtVar x2)     = SDirtVar (plus x1 x2)
plus x1 (SSkelTypeVar x2) = SSkelTypeVar (plus x1 x2)
plus x1 (STermVar x2)     = STermVar (plus x1 x2)
plus Z h                  = h
plus h Z                  = h

instance Ord HNat where
  compare (SCoVar h1) (SCoVar h2) = compare h1 h2
  compare (SCoVar h1) (STypeVar h2) =
    error "differing namespace found in compare "
  compare (SCoVar h1) (SDirtVar h2) =
    error "differing namespace found in compare "
  compare (SCoVar h1) (SSkelTypeVar h2) =
    error "differing namespace found in compare "
  compare (SCoVar h1) (STermVar h2) =
    error "differing namespace found in compare "
  compare (STypeVar h1) (SCoVar h2) =
    error "differing namespace found in compare "
  compare (STypeVar h1) (STypeVar h2) = compare h1 h2
  compare (STypeVar h1) (SDirtVar h2) =
    error "differing namespace found in compare "
  compare (STypeVar h1) (SSkelTypeVar h2) =
    error "differing namespace found in compare "
  compare (STypeVar h1) (STermVar h2) =
    error "differing namespace found in compare "
  compare (SDirtVar h1) (SCoVar h2) =
    error "differing namespace found in compare "
  compare (SDirtVar h1) (STypeVar h2) =
    error "differing namespace found in compare "
  compare (SDirtVar h1) (SDirtVar h2) = compare h1 h2
  compare (SDirtVar h1) (SSkelTypeVar h2) =
    error "differing namespace found in compare "
  compare (SDirtVar h1) (STermVar h2) =
    error "differing namespace found in compare "
  compare (SSkelTypeVar h1) (SCoVar h2) =
    error "differing namespace found in compare "
  compare (SSkelTypeVar h1) (STypeVar h2) =
    error "differing namespace found in compare "
  compare (SSkelTypeVar h1) (SDirtVar h2) =
    error "differing namespace found in compare "
  compare (SSkelTypeVar h1) (SSkelTypeVar h2) = compare h1 h2
  compare (SSkelTypeVar h1) (STermVar h2) =
    error "differing namespace found in compare "
  compare (STermVar h1) (SCoVar h2) =
    error "differing namespace found in compare "
  compare (STermVar h1) (STypeVar h2) =
    error "differing namespace found in compare "
  compare (STermVar h1) (SDirtVar h2) =
    error "differing namespace found in compare "
  compare (STermVar h1) (SSkelTypeVar h2) =
    error "differing namespace found in compare "
  compare (STermVar h1) (STermVar h2) = compare h1 h2
  compare Z Z = EQ
  compare Z _ = LT
  compare _ Z = GT

minus (SCoVar h1) (SCoVar h2) = minus h1 h2
minus (SCoVar h1) (STypeVar h2) = error "differing namespace found in minus "
minus (SCoVar h1) (SDirtVar h2) = error "differing namespace found in minus "
minus (SCoVar h1) (SSkelTypeVar h2) =
  error "differing namespace found in minus "
minus (SCoVar h1) (STermVar h2) = error "differing namespace found in minus "
minus (STypeVar h1) (SCoVar h2) = error "differing namespace found in minus "
minus (STypeVar h1) (STypeVar h2) = minus h1 h2
minus (STypeVar h1) (SDirtVar h2) = error "differing namespace found in minus "
minus (STypeVar h1) (SSkelTypeVar h2) =
  error "differing namespace found in minus "
minus (STypeVar h1) (STermVar h2) = error "differing namespace found in minus "
minus (SDirtVar h1) (SCoVar h2) = error "differing namespace found in minus "
minus (SDirtVar h1) (STypeVar h2) = error "differing namespace found in minus "
minus (SDirtVar h1) (SDirtVar h2) = minus h1 h2
minus (SDirtVar h1) (SSkelTypeVar h2) =
  error "differing namespace found in minus "
minus (SDirtVar h1) (STermVar h2) = error "differing namespace found in minus "
minus (SSkelTypeVar h1) (SCoVar h2) =
  error "differing namespace found in minus "
minus (SSkelTypeVar h1) (STypeVar h2) =
  error "differing namespace found in minus "
minus (SSkelTypeVar h1) (SDirtVar h2) =
  error "differing namespace found in minus "
minus (SSkelTypeVar h1) (SSkelTypeVar h2) = minus h1 h2
minus (SSkelTypeVar h1) (STermVar h2) =
  error "differing namespace found in minus "
minus (STermVar h1) (SCoVar h2) = error "differing namespace found in minus "
minus (STermVar h1) (STypeVar h2) = error "differing namespace found in minus "
minus (STermVar h1) (SDirtVar h2) = error "differing namespace found in minus "
minus (STermVar h1) (SSkelTypeVar h2) =
  error "differing namespace found in minus "
minus (STermVar h1) (STermVar h2) = minus h1 h2
minus Z Z = Z
minus Z _ = error " You cannot substract zero with a positive number "
minus result Z = result

data Env
  = Nil
  | ECoVar SimpleCoercionType
           Env
  | ETypeVar SkeletonType
             Env
  | EDirtVar Env
  | ESkelTypeVar Env
  | ETermVar ValueType
             Env
  deriving (Show, Eq)

generateHnatCoVar 0 c = c
generateHnatCoVar n c = SCoVar (generateHnatCoVar (n - 1) c)

generateHnatTypeVar 0 c = c
generateHnatTypeVar n c = STypeVar (generateHnatTypeVar (n - 1) c)

generateHnatDirtVar 0 c = c
generateHnatDirtVar n c = SDirtVar (generateHnatDirtVar (n - 1) c)

generateHnatSkelTypeVar 0 c = c
generateHnatSkelTypeVar n c = SSkelTypeVar (generateHnatSkelTypeVar (n - 1) c)

generateHnatTermVar 0 c = c
generateHnatTermVar n c = STermVar (generateHnatTermVar (n - 1) c)

coercionmap ::
     (HNat -> Coercion -> Coercion)
  -> (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> HNat
  -> Coercion
  -> Coercion
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoercionVar hnat) =
  onCoVar c (CoercionVar hnat)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoUnit) = CoUnit
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoTypeVar valty) =
  CoTypeVar (valueTypemap onTypeVar onSkelTypeVar onDirtVar c valty)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoDirt d) =
  CoDirt (dirtmap onDirtVar c d)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoArrow co1 co2) =
  CoArrow
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co1)
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co2)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoHandler co1 co2) =
  CoHandler
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co1)
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co2)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoEmptyDirt) =
  CoEmptyDirt
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (UnionOp co op0) =
  UnionOp (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co) op0
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoskeletonAll co) =
  CoskeletonAll
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar (SSkelTypeVar c) co)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoTypeAll co t) =
  CoTypeAll
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar (STypeVar c) co)
    (skeletonTypemap onSkelTypeVar c t)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CodirtAll co) =
  CodirtAll
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar (SDirtVar c) co)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoCoArrow pi co) =
  CoCoArrow
    (simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c pi)
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoComputation co1 co2) =
  CoComputation
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co1)
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co2)

computationTypemap ::
     (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> HNat
  -> ComputationType
  -> ComputationType
computationTypemap onTypeVar onSkelTypeVar onDirtVar c (ComputationTy t d) =
  ComputationTy
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c t)
    (dirtmap onDirtVar c d)

dirtmap :: (HNat -> Dirt -> Dirt) -> HNat -> Dirt -> Dirt
dirtmap onDirtVar c (DirtVariable hnat) = onDirtVar c (DirtVariable hnat)
dirtmap onDirtVar c (EmptyDirt) = EmptyDirt
dirtmap onDirtVar c (UnionDirt d op0) = UnionDirt (dirtmap onDirtVar c d) op0

skeletonTypemap ::
     (HNat -> SkeletonType -> SkeletonType)
  -> HNat
  -> SkeletonType
  -> SkeletonType
skeletonTypemap onSkelTypeVar c (SkelTUnit) = SkelTUnit
skeletonTypemap onSkelTypeVar c (SkellAllType t) =
  SkellAllType (skeletonTypemap onSkelTypeVar (SSkelTypeVar c) t)
skeletonTypemap onSkelTypeVar c (SkelVar hnat) = onSkelTypeVar c (SkelVar hnat)
skeletonTypemap onSkelTypeVar c (SkelArr t1 t2) =
  SkelArr
    (skeletonTypemap onSkelTypeVar c t1)
    (skeletonTypemap onSkelTypeVar c t2)

simpleCoercionTypemap ::
     (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> HNat
  -> SimpleCoercionType
  -> SimpleCoercionType
simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c (DirtCoTypes d1 d2) =
  DirtCoTypes (dirtmap onDirtVar c d1) (dirtmap onDirtVar c d2)
simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTypes d1 d2) =
  ValTypes
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c d1)
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c d2)

coercionTypemap ::
     (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> HNat
  -> CoercionType
  -> CoercionType
coercionTypemap onTypeVar onSkelTypeVar onDirtVar c (CoSimple co) =
  CoSimple (simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c co)
coercionTypemap onTypeVar onSkelTypeVar onDirtVar c (CoComp v1 v2) =
  CoComp
    (computationTypemap onTypeVar onSkelTypeVar onDirtVar c v1)
    (computationTypemap onTypeVar onSkelTypeVar onDirtVar c v2)

valueTypemap ::
     (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> HNat
  -> ValueType
  -> ValueType
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyVar hnat) =
  onTypeVar c (ValTyVar hnat)
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTUnit) = ValTUnit
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyArr ty comp) =
  ValTyArr
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c ty)
    (computationTypemap onTypeVar onSkelTypeVar onDirtVar c comp)
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyHandler c1 c2) =
  ValTyHandler
    (computationTypemap onTypeVar onSkelTypeVar onDirtVar c c1)
    (computationTypemap onTypeVar onSkelTypeVar onDirtVar c c2)
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyAllSkel t) =
  ValTyAllSkel
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar (SSkelTypeVar c) t)
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyAll t ty) =
  ValTyAll
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar (STypeVar c) t)
    (skeletonTypemap onSkelTypeVar c ty)
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyAllDirt t) =
  ValTyAllDirt (valueTypemap onTypeVar onSkelTypeVar onDirtVar (SDirtVar c) t)
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyCoArr pi t) =
  ValTyCoArr
    (simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c pi)
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c t)

computationmap ::
     (HNat -> Value -> Value)
  -> (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> (HNat -> Coercion -> Coercion)
  -> HNat
  -> Computation
  -> Computation
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (ReturnComp v) =
  ReturnComp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c v)
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (HandleComp comp v) =
  HandleComp
    (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c comp)
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c v)
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (ComputationApp t1 t2) =
  ComputationApp
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t1)
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t2)
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (LetComp v comp) =
  LetComp
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c v)
    (computationmap
       onTermVar
       onTypeVar
       onSkelTypeVar
       onDirtVar
       onCoVar
       (STermVar c)
       comp)
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (DoComp c1 c2) =
  DoComp
    (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c c1)
    (computationmap
       onTermVar
       onTypeVar
       onSkelTypeVar
       onDirtVar
       onCoVar
       (STermVar c)
       c2)
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (CastComp comp gamma) =
  CastComp
    (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c comp)
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c gamma)
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (OpComp v ty co op0) =
  OpComp
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c v)
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c ty)
    (computationmap
       onTermVar
       onTypeVar
       onSkelTypeVar
       onDirtVar
       onCoVar
       (STermVar c)
       co)
    op0

handlermap ::
     (HNat -> Value -> Value)
  -> (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> (HNat -> Coercion -> Coercion)
  -> HNat
  -> Handler
  -> Handler
handlermap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (ReturnHandler opsc ty cr) =
  ReturnHandler
    (map
       (operationCompTuplemap
          onTermVar
          onTypeVar
          onSkelTypeVar
          onDirtVar
          onCoVar
          (STermVar c))
       opsc)
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c ty)
    (computationmap
       onTermVar
       onTypeVar
       onSkelTypeVar
       onDirtVar
       onCoVar
       (STermVar c)
       cr)

operationCompTuplemap ::
     (HNat -> Value -> Value)
  -> (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> (HNat -> Coercion -> Coercion)
  -> HNat
  -> OperationCompTuple
  -> OperationCompTuple
operationCompTuplemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (OpAndComp comp op0) =
  OpAndComp
    (computationmap
       onTermVar
       onTypeVar
       onSkelTypeVar
       onDirtVar
       onCoVar
       (STermVar c)
       comp)
    op0

valuemap ::
     (HNat -> Value -> Value)
  -> (HNat -> ValueType -> ValueType)
  -> (HNat -> SkeletonType -> SkeletonType)
  -> (HNat -> Dirt -> Dirt)
  -> (HNat -> Coercion -> Coercion)
  -> HNat
  -> Value
  -> Value
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmVar hnat) =
  onTermVar c (TmVar hnat)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmFun x t) =
  TmFun
    (computationmap
       onTermVar
       onTypeVar
       onSkelTypeVar
       onDirtVar
       onCoVar
       (STermVar c)
       x)
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c t)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmTSkellAbs t1) =
  TmTSkellAbs
    (valuemap
       onTermVar
       onTypeVar
       onSkelTypeVar
       onDirtVar
       onCoVar
       (SSkelTypeVar c)
       t1)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmTSkelApp t1 ty) =
  TmTSkelApp
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t1)
    (skeletonTypemap onSkelTypeVar c ty)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmValueTypeAbs t ty) =
  TmValueTypeAbs
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STypeVar c) t)
    (skeletonTypemap onSkelTypeVar c ty)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmValueTypeApp t ty) =
  TmValueTypeApp
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t)
    (valueTypemap onTypeVar onSkelTypeVar onDirtVar c ty)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmDirtAbs t) =
  TmDirtAbs
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (SDirtVar c) t)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmDirtApp t ty) =
  TmDirtApp
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t)
    (dirtmap onDirtVar c ty)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmCoAbs t coty) =
  TmCoAbs
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (SCoVar c) t)
    (simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c coty)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmCoApp t co) =
  TmCoApp
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t)
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmCast val co) =
  TmCast
    (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c val)
    (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmUnit) = TmUnit
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmHandler h) =
  TmHandler (handlermap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c h)

coercionshiftHelpplus d c (CoercionVar hnat)
  | hnat >= c = CoercionVar (plus hnat d)
  | otherwise = CoercionVar hnat

dirtshiftHelpplus d c (DirtVariable hnat)
  | hnat >= c = DirtVariable (plus hnat d)
  | otherwise = DirtVariable hnat

skeletonTypeshiftHelpplus d c (SkelVar hnat)
  | hnat >= c = SkelVar (plus hnat d)
  | otherwise = SkelVar hnat

valueTypeshiftHelpplus d c (ValTyVar hnat)
  | hnat >= c = ValTyVar (plus hnat d)
  | otherwise = ValTyVar hnat

valueshiftHelpplus d c (TmVar hnat)
  | hnat >= c = TmVar (plus hnat d)
  | otherwise = TmVar hnat

coercionshiftplus :: HNat -> Coercion -> Coercion
coercionshiftplus d t =
  coercionmap
    (coercionshiftHelpplus d)
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    Z
    t

computationTypeshiftplus :: HNat -> ComputationType -> ComputationType
computationTypeshiftplus d t =
  computationTypemap
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    Z
    t

dirtshiftplus :: HNat -> Dirt -> Dirt
dirtshiftplus d t = dirtmap (dirtshiftHelpplus d) Z t

skeletonTypeshiftplus :: HNat -> SkeletonType -> SkeletonType
skeletonTypeshiftplus d t = skeletonTypemap (skeletonTypeshiftHelpplus d) Z t

simpleCoercionTypeshiftplus :: HNat -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypeshiftplus d t =
  simpleCoercionTypemap
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    Z
    t

coercionTypeshiftplus :: HNat -> CoercionType -> CoercionType
coercionTypeshiftplus d t =
  coercionTypemap
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    Z
    t

valueTypeshiftplus :: HNat -> ValueType -> ValueType
valueTypeshiftplus d t =
  valueTypemap
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    Z
    t

computationshiftplus :: HNat -> Computation -> Computation
computationshiftplus d t =
  computationmap
    (valueshiftHelpplus d)
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    (coercionshiftHelpplus d)
    Z
    t

handlershiftplus :: HNat -> Handler -> Handler
handlershiftplus d t =
  handlermap
    (valueshiftHelpplus d)
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    (coercionshiftHelpplus d)
    Z
    t

operationCompTupleshiftplus :: HNat -> OperationCompTuple -> OperationCompTuple
operationCompTupleshiftplus d t =
  operationCompTuplemap
    (valueshiftHelpplus d)
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    (coercionshiftHelpplus d)
    Z
    t

valueshiftplus :: HNat -> Value -> Value
valueshiftplus d t =
  valuemap
    (valueshiftHelpplus d)
    (valueTypeshiftHelpplus d)
    (skeletonTypeshiftHelpplus d)
    (dirtshiftHelpplus d)
    (coercionshiftHelpplus d)
    Z
    t

coercionshiftHelpminus d c (CoercionVar hnat)
  | hnat >= c = CoercionVar (minus hnat d)
  | otherwise = CoercionVar hnat

dirtshiftHelpminus d c (DirtVariable hnat)
  | hnat >= c = DirtVariable (minus hnat d)
  | otherwise = DirtVariable hnat

skeletonTypeshiftHelpminus d c (SkelVar hnat)
  | hnat >= c = SkelVar (minus hnat d)
  | otherwise = SkelVar hnat

valueTypeshiftHelpminus d c (ValTyVar hnat)
  | hnat >= c = ValTyVar (minus hnat d)
  | otherwise = ValTyVar hnat

valueshiftHelpminus d c (TmVar hnat)
  | hnat >= c = TmVar (minus hnat d)
  | otherwise = TmVar hnat

coercionshiftminus :: HNat -> Coercion -> Coercion
coercionshiftminus d t =
  coercionmap
    (coercionshiftHelpminus d)
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    Z
    t

computationTypeshiftminus :: HNat -> ComputationType -> ComputationType
computationTypeshiftminus d t =
  computationTypemap
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    Z
    t

dirtshiftminus :: HNat -> Dirt -> Dirt
dirtshiftminus d t = dirtmap (dirtshiftHelpminus d) Z t

skeletonTypeshiftminus :: HNat -> SkeletonType -> SkeletonType
skeletonTypeshiftminus d t = skeletonTypemap (skeletonTypeshiftHelpminus d) Z t

simpleCoercionTypeshiftminus :: HNat -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypeshiftminus d t =
  simpleCoercionTypemap
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    Z
    t

coercionTypeshiftminus :: HNat -> CoercionType -> CoercionType
coercionTypeshiftminus d t =
  coercionTypemap
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    Z
    t

valueTypeshiftminus :: HNat -> ValueType -> ValueType
valueTypeshiftminus d t =
  valueTypemap
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    Z
    t

computationshiftminus :: HNat -> Computation -> Computation
computationshiftminus d t =
  computationmap
    (valueshiftHelpminus d)
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    (coercionshiftHelpminus d)
    Z
    t

handlershiftminus :: HNat -> Handler -> Handler
handlershiftminus d t =
  handlermap
    (valueshiftHelpminus d)
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    (coercionshiftHelpminus d)
    Z
    t

operationCompTupleshiftminus :: HNat -> OperationCompTuple -> OperationCompTuple
operationCompTupleshiftminus d t =
  operationCompTuplemap
    (valueshiftHelpminus d)
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    (coercionshiftHelpminus d)
    Z
    t

valueshiftminus :: HNat -> Value -> Value
valueshiftminus d t =
  valuemap
    (valueshiftHelpminus d)
    (valueTypeshiftHelpminus d)
    (skeletonTypeshiftHelpminus d)
    (dirtshiftHelpminus d)
    (coercionshiftHelpminus d)
    Z
    t

coercionSubstituteHelp sub orig c (CoercionVar hnat)
  | hnat == plus orig c = coercionshiftplus c sub
  | otherwise = CoercionVar hnat

dirtSubstituteHelp sub orig c (DirtVariable hnat)
  | hnat == plus orig c = dirtshiftplus c sub
  | otherwise = DirtVariable hnat

skeletonTypeSubstituteHelp sub orig c (SkelVar hnat)
  | hnat == plus orig c = skeletonTypeshiftplus c sub
  | otherwise = SkelVar hnat

valueTypeSubstituteHelp sub orig c (ValTyVar hnat)
  | hnat == plus orig c = valueTypeshiftplus c sub
  | otherwise = ValTyVar hnat

valueSubstituteHelp sub orig c (TmVar hnat)
  | hnat == plus orig c = valueshiftplus c sub
  | otherwise = TmVar hnat

coercioncoercionSubstitute :: Coercion -> HNat -> Coercion -> Coercion
coercioncoercionSubstitute sub orig t =
  rewriteCoercion $
  coercionmap
    (coercionSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

coercionvalueTypeSubstitute :: ValueType -> HNat -> Coercion -> Coercion
coercionvalueTypeSubstitute sub orig t =
  rewriteCoercion $
  coercionmap
    (\c x -> x)
    (valueTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    Z
    t

coercionskeletonTypeSubstitute :: SkeletonType -> HNat -> Coercion -> Coercion
coercionskeletonTypeSubstitute sub orig t =
  rewriteCoercion $
  coercionmap
    (\c x -> x)
    (\c x -> x)
    (skeletonTypeSubstituteHelp sub orig)
    (\c x -> x)
    Z
    t

coerciondirtSubstitute :: Dirt -> HNat -> Coercion -> Coercion
coerciondirtSubstitute sub orig t =
  rewriteCoercion $
  coercionmap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (dirtSubstituteHelp sub orig)
    Z
    t

computationTypevalueTypeSubstitute ::
     ValueType -> HNat -> ComputationType -> ComputationType
computationTypevalueTypeSubstitute sub orig t =
  computationTypemap
    (valueTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    Z
    t

computationTypeskeletonTypeSubstitute ::
     SkeletonType -> HNat -> ComputationType -> ComputationType
computationTypeskeletonTypeSubstitute sub orig t =
  computationTypemap
    (\c x -> x)
    (skeletonTypeSubstituteHelp sub orig)
    (\c x -> x)
    Z
    t

computationTypedirtSubstitute ::
     Dirt -> HNat -> ComputationType -> ComputationType
computationTypedirtSubstitute sub orig t =
  computationTypemap (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub orig) Z t

dirtdirtSubstitute :: Dirt -> HNat -> Dirt -> Dirt
dirtdirtSubstitute sub orig t = dirtmap (dirtSubstituteHelp sub orig) Z t

skeletonTypeskeletonTypeSubstitute ::
     SkeletonType -> HNat -> SkeletonType -> SkeletonType
skeletonTypeskeletonTypeSubstitute sub orig t =
  skeletonTypemap (skeletonTypeSubstituteHelp sub orig) Z t

simpleCoercionTypevalueTypeSubstitute ::
     ValueType -> HNat -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypevalueTypeSubstitute sub orig t =
  simpleCoercionTypemap
    (valueTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    Z
    t

simpleCoercionTypeskeletonTypeSubstitute ::
     SkeletonType -> HNat -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypeskeletonTypeSubstitute sub orig t =
  simpleCoercionTypemap
    (\c x -> x)
    (skeletonTypeSubstituteHelp sub orig)
    (\c x -> x)
    Z
    t

simpleCoercionTypedirtSubstitute ::
     Dirt -> HNat -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypedirtSubstitute sub orig t =
  simpleCoercionTypemap
    (\c x -> x)
    (\c x -> x)
    (dirtSubstituteHelp sub orig)
    Z
    t

coercionTypevalueTypeSubstitute ::
     ValueType -> HNat -> CoercionType -> CoercionType
coercionTypevalueTypeSubstitute sub orig t =
  coercionTypemap (valueTypeSubstituteHelp sub orig) (\c x -> x) (\c x -> x) Z t

coercionTypeskeletonTypeSubstitute ::
     SkeletonType -> HNat -> CoercionType -> CoercionType
coercionTypeskeletonTypeSubstitute sub orig t =
  coercionTypemap
    (\c x -> x)
    (skeletonTypeSubstituteHelp sub orig)
    (\c x -> x)
    Z
    t

coercionTypedirtSubstitute :: Dirt -> HNat -> CoercionType -> CoercionType
coercionTypedirtSubstitute sub orig t =
  coercionTypemap (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub orig) Z t

valueTypevalueTypeSubstitute :: ValueType -> HNat -> ValueType -> ValueType
valueTypevalueTypeSubstitute sub orig t =
  valueTypemap (valueTypeSubstituteHelp sub orig) (\c x -> x) (\c x -> x) Z t

valueTypeskeletonTypeSubstitute ::
     SkeletonType -> HNat -> ValueType -> ValueType
valueTypeskeletonTypeSubstitute sub orig t =
  valueTypemap (\c x -> x) (skeletonTypeSubstituteHelp sub orig) (\c x -> x) Z t

valueTypedirtSubstitute :: Dirt -> HNat -> ValueType -> ValueType
valueTypedirtSubstitute sub orig t =
  valueTypemap (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub orig) Z t

computationvalueSubstitute :: Value -> HNat -> Computation -> Computation
computationvalueSubstitute sub orig t =
  computationmap
    (valueSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

computationvalueTypeSubstitute ::
     ValueType -> HNat -> Computation -> Computation
computationvalueTypeSubstitute sub orig t =
  computationmap
    (\c x -> x)
    (valueTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

computationskeletonTypeSubstitute ::
     SkeletonType -> HNat -> Computation -> Computation
computationskeletonTypeSubstitute sub orig t =
  computationmap
    (\c x -> x)
    (\c x -> x)
    (skeletonTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    Z
    t

computationdirtSubstitute :: Dirt -> HNat -> Computation -> Computation
computationdirtSubstitute sub orig t =
  computationmap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (dirtSubstituteHelp sub orig)
    (\c x -> x)
    Z
    t

computationcoercionSubstitute :: Coercion -> HNat -> Computation -> Computation
computationcoercionSubstitute sub orig t =
  computationmap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (coercionSubstituteHelp sub orig)
    Z
    t

handlervalueSubstitute :: Value -> HNat -> Handler -> Handler
handlervalueSubstitute sub orig t =
  handlermap
    (valueSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

handlervalueTypeSubstitute :: ValueType -> HNat -> Handler -> Handler
handlervalueTypeSubstitute sub orig t =
  handlermap
    (\c x -> x)
    (valueTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

handlerskeletonTypeSubstitute :: SkeletonType -> HNat -> Handler -> Handler
handlerskeletonTypeSubstitute sub orig t =
  handlermap
    (\c x -> x)
    (\c x -> x)
    (skeletonTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    Z
    t

handlerdirtSubstitute :: Dirt -> HNat -> Handler -> Handler
handlerdirtSubstitute sub orig t =
  handlermap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (dirtSubstituteHelp sub orig)
    (\c x -> x)
    Z
    t

handlercoercionSubstitute :: Coercion -> HNat -> Handler -> Handler
handlercoercionSubstitute sub orig t =
  handlermap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (coercionSubstituteHelp sub orig)
    Z
    t

operationCompTuplevalueSubstitute ::
     Value -> HNat -> OperationCompTuple -> OperationCompTuple
operationCompTuplevalueSubstitute sub orig t =
  operationCompTuplemap
    (valueSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

operationCompTuplevalueTypeSubstitute ::
     ValueType -> HNat -> OperationCompTuple -> OperationCompTuple
operationCompTuplevalueTypeSubstitute sub orig t =
  operationCompTuplemap
    (\c x -> x)
    (valueTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

operationCompTupleskeletonTypeSubstitute ::
     SkeletonType -> HNat -> OperationCompTuple -> OperationCompTuple
operationCompTupleskeletonTypeSubstitute sub orig t =
  operationCompTuplemap
    (\c x -> x)
    (\c x -> x)
    (skeletonTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    Z
    t

operationCompTupledirtSubstitute ::
     Dirt -> HNat -> OperationCompTuple -> OperationCompTuple
operationCompTupledirtSubstitute sub orig t =
  operationCompTuplemap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (dirtSubstituteHelp sub orig)
    (\c x -> x)
    Z
    t

operationCompTuplecoercionSubstitute ::
     Coercion -> HNat -> OperationCompTuple -> OperationCompTuple
operationCompTuplecoercionSubstitute sub orig t =
  operationCompTuplemap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (coercionSubstituteHelp sub orig)
    Z
    t

valuevalueSubstitute :: Value -> HNat -> Value -> Value
valuevalueSubstitute sub orig t =
  valuemap
    (valueSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

valuevalueTypeSubstitute :: ValueType -> HNat -> Value -> Value
valuevalueTypeSubstitute sub orig t =
  valuemap
    (\c x -> x)
    (valueTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    Z
    t

valueskeletonTypeSubstitute :: SkeletonType -> HNat -> Value -> Value
valueskeletonTypeSubstitute sub orig t =
  valuemap
    (\c x -> x)
    (\c x -> x)
    (skeletonTypeSubstituteHelp sub orig)
    (\c x -> x)
    (\c x -> x)
    Z
    t

valuedirtSubstitute :: Dirt -> HNat -> Value -> Value
valuedirtSubstitute sub orig t =
  valuemap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (dirtSubstituteHelp sub orig)
    (\c x -> x)
    Z
    t

valuecoercionSubstitute :: Coercion -> HNat -> Value -> Value
valuecoercionSubstitute sub orig t =
  valuemap
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (\c x -> x)
    (coercionSubstituteHelp sub orig)
    Z
    t

freeVariablesCoercion :: HNat -> Coercion -> [HNat]
freeVariablesCoercion c (CoercionVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesCoercion c (CoUnit) = nub ([])
freeVariablesCoercion c (CoTypeVar valty) =
  nub ((freeVariablesValueType c valty))
freeVariablesCoercion c (CoDirt d) = nub ((freeVariablesDirt c d))
freeVariablesCoercion c (CoArrow co1 co2) =
  nub ((freeVariablesCoercion c co1) ++ (freeVariablesCoercion c co2))
freeVariablesCoercion c (CoHandler co1 co2) =
  nub ((freeVariablesCoercion c co1) ++ (freeVariablesCoercion c co2))
freeVariablesCoercion c (CoEmptyDirt) = nub ([])
freeVariablesCoercion c (UnionOp co _) = nub ((freeVariablesCoercion c co))
freeVariablesCoercion c (CoskeletonAll co) =
  nub ((freeVariablesCoercion (SSkelTypeVar c) co))
freeVariablesCoercion c (CoTypeAll co t) =
  nub
    ((freeVariablesCoercion (STypeVar c) co) ++ (freeVariablesSkeletonType c t))
freeVariablesCoercion c (CodirtAll co) =
  nub ((freeVariablesCoercion (SDirtVar c) co))
freeVariablesCoercion c (CoCoArrow pi co) =
  nub ((freeVariablesSimpleCoercionType c pi) ++ (freeVariablesCoercion c co))
freeVariablesCoercion c (CoComputation co1 co2) =
  nub ((freeVariablesCoercion c co1) ++ (freeVariablesCoercion c co2))

freeVariablesComputationType :: HNat -> ComputationType -> [HNat]
freeVariablesComputationType c (ComputationTy t d) =
  nub ((freeVariablesValueType c t) ++ (freeVariablesDirt c d))

freeVariablesDirt :: HNat -> Dirt -> [HNat]
freeVariablesDirt c (DirtVariable hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesDirt c (EmptyDirt) = nub ([])
freeVariablesDirt c (UnionDirt d _) = nub ((freeVariablesDirt c d))

freeVariablesSkeletonType :: HNat -> SkeletonType -> [HNat]
freeVariablesSkeletonType c (SkelTUnit) = nub ([])
freeVariablesSkeletonType c (SkellAllType t) =
  nub ((freeVariablesSkeletonType (SSkelTypeVar c) t))
freeVariablesSkeletonType c (SkelVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesSkeletonType c (SkelArr t1 t2) =
  nub ((freeVariablesSkeletonType c t1) ++ (freeVariablesSkeletonType c t2))

freeVariablesSimpleCoercionType :: HNat -> SimpleCoercionType -> [HNat]
freeVariablesSimpleCoercionType c (DirtCoTypes d1 d2) =
  nub ((freeVariablesDirt c d1) ++ (freeVariablesDirt c d2))
freeVariablesSimpleCoercionType c (ValTypes d1 d2) =
  nub ((freeVariablesValueType c d1) ++ (freeVariablesValueType c d2))

freeVariablesCoercionType :: HNat -> CoercionType -> [HNat]
freeVariablesCoercionType c (CoSimple co) =
  nub ((freeVariablesSimpleCoercionType c co))
freeVariablesCoercionType c (CoComp v1 v2) =
  nub
    ((freeVariablesComputationType c v1) ++ (freeVariablesComputationType c v2))

freeVariablesValueType :: HNat -> ValueType -> [HNat]
freeVariablesValueType c (ValTyVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesValueType c (ValTUnit) = nub ([])
freeVariablesValueType c (ValTyArr ty comp) =
  nub ((freeVariablesValueType c ty) ++ (freeVariablesComputationType c comp))
freeVariablesValueType c (ValTyHandler c1 c2) =
  nub
    ((freeVariablesComputationType c c1) ++ (freeVariablesComputationType c c2))
freeVariablesValueType c (ValTyAllSkel t) =
  nub ((freeVariablesValueType (SSkelTypeVar c) t))
freeVariablesValueType c (ValTyAll t ty) =
  nub
    ((freeVariablesValueType (STypeVar c) t) ++ (freeVariablesSkeletonType c ty))
freeVariablesValueType c (ValTyAllDirt t) =
  nub ((freeVariablesValueType (SDirtVar c) t))
freeVariablesValueType c (ValTyCoArr pi t) =
  nub ((freeVariablesSimpleCoercionType c pi) ++ (freeVariablesValueType c t))

freeVariablesComputation :: HNat -> Computation -> [HNat]
freeVariablesComputation c (ReturnComp v) = nub ((freeVariablesValue c v))
freeVariablesComputation c (HandleComp comp v) =
  nub ((freeVariablesComputation c comp) ++ (freeVariablesValue c v))
freeVariablesComputation c (ComputationApp t1 t2) =
  nub ((freeVariablesValue c t1) ++ (freeVariablesValue c t2))
freeVariablesComputation c (LetComp v comp) =
  nub ((freeVariablesValue c v) ++ (freeVariablesComputation (STermVar c) comp))
freeVariablesComputation c (DoComp c1 c2) =
  nub
    ((freeVariablesComputation c c1) ++
     (freeVariablesComputation (STermVar c) c2))
freeVariablesComputation c (CastComp comp gamma) =
  nub ((freeVariablesComputation c comp) ++ (freeVariablesCoercion c gamma))
freeVariablesComputation c (OpComp v ty co _) =
  nub
    ((freeVariablesValue c v) ++
     (freeVariablesValueType c ty) ++ (freeVariablesComputation (STermVar c) co))

freeVariablesHandler :: HNat -> Handler -> [HNat]
freeVariablesHandler c (ReturnHandler opsc ty cr) =
  nub
    ((concatMap (freeVariablesOperationCompTuple (STermVar c)) opsc) ++
     (freeVariablesValueType c ty) ++ (freeVariablesComputation (STermVar c) cr))

freeVariablesOperationCompTuple :: HNat -> OperationCompTuple -> [HNat]
freeVariablesOperationCompTuple c (OpAndComp comp _) =
  nub ((freeVariablesComputation (STermVar c) comp))

freeVariablesValue :: HNat -> Value -> [HNat]
freeVariablesValue c (TmVar hnat)
  | hnat >= c = [minus hnat c]
  | otherwise = []
freeVariablesValue c (TmFun x t) =
  nub
    ((freeVariablesComputation (STermVar c) x) ++ (freeVariablesValueType c t))
freeVariablesValue c (TmTSkellAbs t1) =
  nub ((freeVariablesValue (SSkelTypeVar c) t1))
freeVariablesValue c (TmTSkelApp t1 ty) =
  nub ((freeVariablesValue c t1) ++ (freeVariablesSkeletonType c ty))
freeVariablesValue c (TmValueTypeAbs t ty) =
  nub ((freeVariablesValue (STypeVar c) t) ++ (freeVariablesSkeletonType c ty))
freeVariablesValue c (TmValueTypeApp t ty) =
  nub ((freeVariablesValue c t) ++ (freeVariablesValueType c ty))
freeVariablesValue c (TmDirtAbs t) = nub ((freeVariablesValue (SDirtVar c) t))
freeVariablesValue c (TmDirtApp t ty) =
  nub ((freeVariablesValue c t) ++ (freeVariablesDirt c ty))
freeVariablesValue c (TmCoAbs t coty) =
  nub
    ((freeVariablesValue (SCoVar c) t) ++
     (freeVariablesSimpleCoercionType c coty))
freeVariablesValue c (TmCoApp t co) =
  nub ((freeVariablesValue c t) ++ (freeVariablesCoercion c co))
freeVariablesValue c (TmCast val co) =
  nub ((freeVariablesValue c val) ++ (freeVariablesCoercion c co))
freeVariablesValue c (TmUnit) = nub ([])
freeVariablesValue c (TmHandler h) = nub ((freeVariablesHandler c h))

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
