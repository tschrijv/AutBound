module ExEff where
import Data.List 
import Operations 

data Variable = Z | STermVar Variable | SSkelTypeVar Variable | SDirtVar Variable | STypeVar Variable | SCoVar Variable deriving(Show, Eq)

data Value = TmVar Variable | TmFun Computation ValueType | TmTSkellAbs Value | TmTSkelApp Value SkeletonType | TmValueTypeAbs Value SkeletonType | TmValueTypeApp Value ValueType | TmDirtAbs Value | TmDirtApp Value Dirt | TmCoAbs Value SimpleCoercionType | TmCoApp Value Coercion | TmCast Value Coercion | TmUnit | TmHandler Handler deriving(Show, Eq)

data OperationCompTuple = OpAndComp Computation Op deriving(Show, Eq)

data Handler = ReturnHandler [OperationCompTuple] ValueType Computation deriving(Show, Eq)

data Computation = ReturnComp Value | HandleComp Computation Value | ComputationApp Value Value | LetComp Value Computation | DoComp Computation Computation | CastComp Computation Coercion | OpComp Value ValueType Computation Op deriving(Show, Eq)

data ValueType = ValTyVar Variable | ValTUnit | ValTyArr ValueType ComputationType | ValTyHandler ComputationType ComputationType | ValTyAllSkel ValueType | ValTyAll ValueType SkeletonType | ValTyAllDirt ValueType | ValTyCoArr SimpleCoercionType ValueType deriving(Show, Eq)

data CoercionType = CoSimple SimpleCoercionType | CoComp ComputationType ComputationType deriving(Show, Eq)

data SimpleCoercionType = DirtCoTypes Dirt Dirt | ValTypes ValueType ValueType deriving(Show, Eq)

data SkeletonType = SkelTUnit | SkellAllType SkeletonType | SkelVar Variable | SkelArr SkeletonType SkeletonType deriving(Show, Eq)

data Dirt = DirtVariable Variable | EmptyDirt | UnionDirt Dirt Op deriving(Show, Eq)

data ComputationType = ComputationTy ValueType Dirt deriving(Show, Eq)

data Coercion = CoercionVar Variable | CoUnit | CoTypeVar ValueType | CoDirt Dirt | CoArrow Coercion Coercion | CoHandler Coercion Coercion | CoEmptyDirt | UnionOp Coercion Op | CoskeletonAll Coercion | CoTypeAll Coercion SkeletonType | CodirtAll Coercion | CoCoArrow SimpleCoercionType Coercion | CoComputation Coercion Coercion deriving(Show, Eq)


-- Add two Variables.
plus :: Variable -> Variable -> Variable
plus (Z) h = h
plus h (Z) = h
plus (STermVar x1) x2 = (STermVar (plus x1 x2))
plus (SSkelTypeVar x1) x2 = (SSkelTypeVar (plus x1 x2))
plus (SDirtVar x1) x2 = (SDirtVar (plus x1 x2))
plus (STypeVar x1) x2 = (STypeVar (plus x1 x2))
plus (SCoVar x1) x2 = (SCoVar (plus x1 x2))

-- Substract the second Variable from the first. The first Variable has to
-- be greater than the second one.
minus :: Variable -> Variable -> Variable
minus (Z) (Z) = (Z)
minus (Z) _ = (error "You cannot substract zero with a positive number")
minus result (Z) = result
minus (STermVar h1) (STermVar h2) = (minus h1 h2)
minus (STermVar h1) (SSkelTypeVar h2) = (STermVar (minus h1 (SSkelTypeVar h2)))
minus (STermVar h1) (SDirtVar h2) = (STermVar (minus h1 (SDirtVar h2)))
minus (STermVar h1) (STypeVar h2) = (STermVar (minus h1 (STypeVar h2)))
minus (STermVar h1) (SCoVar h2) = (STermVar (minus h1 (SCoVar h2)))
minus (SSkelTypeVar h1) (STermVar h2) = (SSkelTypeVar (minus h1 (STermVar h2)))
minus (SSkelTypeVar h1) (SSkelTypeVar h2) = (minus h1 h2)
minus (SSkelTypeVar h1) (SDirtVar h2) = (SSkelTypeVar (minus h1 (SDirtVar h2)))
minus (SSkelTypeVar h1) (STypeVar h2) = (SSkelTypeVar (minus h1 (STypeVar h2)))
minus (SSkelTypeVar h1) (SCoVar h2) = (SSkelTypeVar (minus h1 (SCoVar h2)))
minus (SDirtVar h1) (STermVar h2) = (SDirtVar (minus h1 (STermVar h2)))
minus (SDirtVar h1) (SSkelTypeVar h2) = (SDirtVar (minus h1 (SSkelTypeVar h2)))
minus (SDirtVar h1) (SDirtVar h2) = (minus h1 h2)
minus (SDirtVar h1) (STypeVar h2) = (SDirtVar (minus h1 (STypeVar h2)))
minus (SDirtVar h1) (SCoVar h2) = (SDirtVar (minus h1 (SCoVar h2)))
minus (STypeVar h1) (STermVar h2) = (STypeVar (minus h1 (STermVar h2)))
minus (STypeVar h1) (SSkelTypeVar h2) = (STypeVar (minus h1 (SSkelTypeVar h2)))
minus (STypeVar h1) (SDirtVar h2) = (STypeVar (minus h1 (SDirtVar h2)))
minus (STypeVar h1) (STypeVar h2) = (minus h1 h2)
minus (STypeVar h1) (SCoVar h2) = (STypeVar (minus h1 (SCoVar h2)))
minus (SCoVar h1) (STermVar h2) = (SCoVar (minus h1 (STermVar h2)))
minus (SCoVar h1) (SSkelTypeVar h2) = (SCoVar (minus h1 (SSkelTypeVar h2)))
minus (SCoVar h1) (SDirtVar h2) = (SCoVar (minus h1 (SDirtVar h2)))
minus (SCoVar h1) (STypeVar h2) = (SCoVar (minus h1 (STypeVar h2)))
minus (SCoVar h1) (SCoVar h2) = (minus h1 h2)

-- Apply STermVar n times to the second argument c.
generateHnatTermVar :: Int -> Variable -> Variable
generateHnatTermVar 0 c = c
generateHnatTermVar n c = (STermVar (generateHnatTermVar (n - 1) c))

-- Apply SSkelTypeVar n times to the second argument c.
generateHnatSkelTypeVar :: Int -> Variable -> Variable
generateHnatSkelTypeVar 0 c = c
generateHnatSkelTypeVar n c = (SSkelTypeVar (generateHnatSkelTypeVar (n - 1) c))

-- Apply SDirtVar n times to the second argument c.
generateHnatDirtVar :: Int -> Variable -> Variable
generateHnatDirtVar 0 c = c
generateHnatDirtVar n c = (SDirtVar (generateHnatDirtVar (n - 1) c))

-- Apply STypeVar n times to the second argument c.
generateHnatTypeVar :: Int -> Variable -> Variable
generateHnatTypeVar 0 c = c
generateHnatTypeVar n c = (STypeVar (generateHnatTypeVar (n - 1) c))

-- Apply SCoVar n times to the second argument c.
generateHnatCoVar :: Int -> Variable -> Variable
generateHnatCoVar 0 c = c
generateHnatCoVar n c = (SCoVar (generateHnatCoVar (n - 1) c))

-- Perform the shift operation on one Value with the TmVar constructor.
valueshiftHelpplus :: Variable -> Variable -> Value -> Value
valueshiftHelpplus d c (TmVar var) = if (var >= c) then (TmVar (plus c (plus d (minus var c)))) else (TmVar var)

-- Perform the shift operation on one ValueType with the ValTyVar constructor.
valueTypeshiftHelpplus :: Variable -> Variable -> ValueType -> ValueType
valueTypeshiftHelpplus d c (ValTyVar var) = if (var >= c) then (ValTyVar (plus c (plus d (minus var c)))) else (ValTyVar var)

-- Perform the shift operation on one SkeletonType with the SkelVar constructor.
skeletonTypeshiftHelpplus :: Variable -> Variable -> SkeletonType -> SkeletonType
skeletonTypeshiftHelpplus d c (SkelVar var) = if (var >= c) then (SkelVar (plus c (plus d (minus var c)))) else (SkelVar var)

-- Perform the shift operation on one Dirt with the DirtVariable constructor.
dirtshiftHelpplus :: Variable -> Variable -> Dirt -> Dirt
dirtshiftHelpplus d c (DirtVariable var) = if (var >= c) then (DirtVariable (plus c (plus d (minus var c)))) else (DirtVariable var)

-- Perform the shift operation on one Coercion with the CoercionVar constructor.
coercionshiftHelpplus :: Variable -> Variable -> Coercion -> Coercion
coercionshiftHelpplus d c (CoercionVar var) = if (var >= c) then (CoercionVar (plus c (plus d (minus var c)))) else (CoercionVar var)

-- Perform the shift operation on a Value.
valueshiftplus :: Variable -> Value -> Value
valueshiftplus d t = (valuemap (valueshiftHelpplus d) (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (coercionshiftHelpplus d) (Z) t)

-- Perform the shift operation on a OperationCompTuple.
operationCompTupleshiftplus :: Variable -> OperationCompTuple -> OperationCompTuple
operationCompTupleshiftplus d t = (operationCompTuplemap (valueshiftHelpplus d) (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (coercionshiftHelpplus d) (Z) t)

-- Perform the shift operation on a Handler.
handlershiftplus :: Variable -> Handler -> Handler
handlershiftplus d t = (handlermap (valueshiftHelpplus d) (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (coercionshiftHelpplus d) (Z) t)

-- Perform the shift operation on a Computation.
computationshiftplus :: Variable -> Computation -> Computation
computationshiftplus d t = (computationmap (valueshiftHelpplus d) (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (coercionshiftHelpplus d) (Z) t)

-- Perform the shift operation on a ValueType.
valueTypeshiftplus :: Variable -> ValueType -> ValueType
valueTypeshiftplus d t = (valueTypemap (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (Z) t)

-- Perform the shift operation on a CoercionType.
coercionTypeshiftplus :: Variable -> CoercionType -> CoercionType
coercionTypeshiftplus d t = (coercionTypemap (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (Z) t)

-- Perform the shift operation on a SimpleCoercionType.
simpleCoercionTypeshiftplus :: Variable -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypeshiftplus d t = (simpleCoercionTypemap (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (Z) t)

-- Perform the shift operation on a SkeletonType.
skeletonTypeshiftplus :: Variable -> SkeletonType -> SkeletonType
skeletonTypeshiftplus d t = (skeletonTypemap (skeletonTypeshiftHelpplus d) (Z) t)

-- Perform the shift operation on a Dirt.
dirtshiftplus :: Variable -> Dirt -> Dirt
dirtshiftplus d t = (dirtmap (dirtshiftHelpplus d) (Z) t)

-- Perform the shift operation on a ComputationType.
computationTypeshiftplus :: Variable -> ComputationType -> ComputationType
computationTypeshiftplus d t = (computationTypemap (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (Z) t)

-- Perform the shift operation on a Coercion.
coercionshiftplus :: Variable -> Coercion -> Coercion
coercionshiftplus d t = (coercionmap (coercionshiftHelpplus d) (valueTypeshiftHelpplus d) (skeletonTypeshiftHelpplus d) (dirtshiftHelpplus d) (Z) t)

-- Perform the shift operation on one Value with the TmVar constructor.
valueshiftHelpminus :: Variable -> Variable -> Value -> Value
valueshiftHelpminus d c (TmVar var) = if (var >= c) then (TmVar (minus var d)) else (TmVar var)

-- Perform the shift operation on one ValueType with the ValTyVar constructor.
valueTypeshiftHelpminus :: Variable -> Variable -> ValueType -> ValueType
valueTypeshiftHelpminus d c (ValTyVar var) = if (var >= c) then (ValTyVar (minus var d)) else (ValTyVar var)

-- Perform the shift operation on one SkeletonType with the SkelVar constructor.
skeletonTypeshiftHelpminus :: Variable -> Variable -> SkeletonType -> SkeletonType
skeletonTypeshiftHelpminus d c (SkelVar var) = if (var >= c) then (SkelVar (minus var d)) else (SkelVar var)

-- Perform the shift operation on one Dirt with the DirtVariable constructor.
dirtshiftHelpminus :: Variable -> Variable -> Dirt -> Dirt
dirtshiftHelpminus d c (DirtVariable var) = if (var >= c) then (DirtVariable (minus var d)) else (DirtVariable var)

-- Perform the shift operation on one Coercion with the CoercionVar constructor.
coercionshiftHelpminus :: Variable -> Variable -> Coercion -> Coercion
coercionshiftHelpminus d c (CoercionVar var) = if (var >= c) then (CoercionVar (minus var d)) else (CoercionVar var)

-- Perform the shift operation on a Value.
valueshiftminus :: Variable -> Value -> Value
valueshiftminus d t = (valuemap (valueshiftHelpminus d) (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (coercionshiftHelpminus d) (Z) t)

-- Perform the shift operation on a OperationCompTuple.
operationCompTupleshiftminus :: Variable -> OperationCompTuple -> OperationCompTuple
operationCompTupleshiftminus d t = (operationCompTuplemap (valueshiftHelpminus d) (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (coercionshiftHelpminus d) (Z) t)

-- Perform the shift operation on a Handler.
handlershiftminus :: Variable -> Handler -> Handler
handlershiftminus d t = (handlermap (valueshiftHelpminus d) (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (coercionshiftHelpminus d) (Z) t)

-- Perform the shift operation on a Computation.
computationshiftminus :: Variable -> Computation -> Computation
computationshiftminus d t = (computationmap (valueshiftHelpminus d) (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (coercionshiftHelpminus d) (Z) t)

-- Perform the shift operation on a ValueType.
valueTypeshiftminus :: Variable -> ValueType -> ValueType
valueTypeshiftminus d t = (valueTypemap (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (Z) t)

-- Perform the shift operation on a CoercionType.
coercionTypeshiftminus :: Variable -> CoercionType -> CoercionType
coercionTypeshiftminus d t = (coercionTypemap (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (Z) t)

-- Perform the shift operation on a SimpleCoercionType.
simpleCoercionTypeshiftminus :: Variable -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypeshiftminus d t = (simpleCoercionTypemap (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (Z) t)

-- Perform the shift operation on a SkeletonType.
skeletonTypeshiftminus :: Variable -> SkeletonType -> SkeletonType
skeletonTypeshiftminus d t = (skeletonTypemap (skeletonTypeshiftHelpminus d) (Z) t)

-- Perform the shift operation on a Dirt.
dirtshiftminus :: Variable -> Dirt -> Dirt
dirtshiftminus d t = (dirtmap (dirtshiftHelpminus d) (Z) t)

-- Perform the shift operation on a ComputationType.
computationTypeshiftminus :: Variable -> ComputationType -> ComputationType
computationTypeshiftminus d t = (computationTypemap (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (Z) t)

-- Perform the shift operation on a Coercion.
coercionshiftminus :: Variable -> Coercion -> Coercion
coercionshiftminus d t = (coercionmap (coercionshiftHelpminus d) (valueTypeshiftHelpminus d) (skeletonTypeshiftHelpminus d) (dirtshiftHelpminus d) (Z) t)

-- Return the Value where onTermVar, onSkelTypeVar, onDirtVar, onTypeVar, onCoVar are applied to each
-- Value, SkeletonType, Dirt, ValueType, Coercion in the given Value respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
valuemap :: (Variable -> Value -> Value) -> (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> (Variable -> Coercion -> Coercion) -> Variable -> Value -> Value
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmVar var) = (onTermVar c (TmVar var))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmFun x t) = (TmFun (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STermVar c) x) (valueTypemap onTypeVar onSkelTypeVar onDirtVar c t))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmTSkellAbs t1) = (TmTSkellAbs (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (SSkelTypeVar c) t1))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmTSkelApp t1 ty) = (TmTSkelApp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t1) (skeletonTypemap onSkelTypeVar c ty))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmValueTypeAbs t ty) = (TmValueTypeAbs (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STypeVar c) t) (skeletonTypemap onSkelTypeVar c ty))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmValueTypeApp t ty) = (TmValueTypeApp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t) (valueTypemap onTypeVar onSkelTypeVar onDirtVar c ty))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmDirtAbs t) = (TmDirtAbs (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (SDirtVar c) t))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmDirtApp t ty) = (TmDirtApp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t) (dirtmap onDirtVar c ty))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmCoAbs t coty) = (TmCoAbs (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (SCoVar c) t) (simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c coty))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmCoApp t co) = (TmCoApp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t) (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmCast val co) = (TmCast (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c val) (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co))
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmUnit) = (TmUnit)
valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (TmHandler h) = (TmHandler (handlermap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c h))

-- Return the OperationCompTuple where onTermVar, onSkelTypeVar, onDirtVar, onTypeVar, onCoVar are applied to each
-- Value, SkeletonType, Dirt, ValueType, Coercion in the given OperationCompTuple respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
operationCompTuplemap :: (Variable -> Value -> Value) -> (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> (Variable -> Coercion -> Coercion) -> Variable -> OperationCompTuple -> OperationCompTuple
operationCompTuplemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (OpAndComp comp op1) = (OpAndComp (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STermVar c) comp) op1)

-- Return the Handler where onTermVar, onSkelTypeVar, onDirtVar, onTypeVar, onCoVar are applied to each
-- Value, SkeletonType, Dirt, ValueType, Coercion in the given Handler respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
handlermap :: (Variable -> Value -> Value) -> (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> (Variable -> Coercion -> Coercion) -> Variable -> Handler -> Handler
handlermap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (ReturnHandler opsc ty cr) = (ReturnHandler (map (operationCompTuplemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STermVar c)) opsc) (valueTypemap onTypeVar onSkelTypeVar onDirtVar c ty) (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STermVar c) cr))

-- Return the Computation where onTermVar, onSkelTypeVar, onDirtVar, onTypeVar, onCoVar are applied to each
-- Value, SkeletonType, Dirt, ValueType, Coercion in the given Computation respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
computationmap :: (Variable -> Value -> Value) -> (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> (Variable -> Coercion -> Coercion) -> Variable -> Computation -> Computation
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (ReturnComp v) = (ReturnComp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c v))
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (HandleComp comp v) = (HandleComp (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c comp) (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c v))
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (ComputationApp t1 t2) = (ComputationApp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t1) (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c t2))
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (LetComp v comp) = (LetComp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c v) (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STermVar c) comp))
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (DoComp c1 c2) = (DoComp (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c c1) (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STermVar c) c2))
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (CastComp comp gamma) = (CastComp (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c comp) (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c gamma))
computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c (OpComp v ty co op1) = (OpComp (valuemap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar c v) (valueTypemap onTypeVar onSkelTypeVar onDirtVar c ty) (computationmap onTermVar onTypeVar onSkelTypeVar onDirtVar onCoVar (STermVar c) co) op1)

-- Return the ValueType where onSkelTypeVar, onDirtVar, onTypeVar are applied to each
-- SkeletonType, Dirt, ValueType in the given ValueType respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
valueTypemap :: (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> Variable -> ValueType -> ValueType
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyVar var) = (onTypeVar c (ValTyVar var))
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTUnit) = (ValTUnit)
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyArr ty comp) = (ValTyArr (valueTypemap onTypeVar onSkelTypeVar onDirtVar c ty) (computationTypemap onTypeVar onSkelTypeVar onDirtVar c comp))
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyHandler c1 c2) = (ValTyHandler (computationTypemap onTypeVar onSkelTypeVar onDirtVar c c1) (computationTypemap onTypeVar onSkelTypeVar onDirtVar c c2))
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyAllSkel t) = (ValTyAllSkel (valueTypemap onTypeVar onSkelTypeVar onDirtVar (SSkelTypeVar c) t))
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyAll t ty) = (ValTyAll (valueTypemap onTypeVar onSkelTypeVar onDirtVar (STypeVar c) t) (skeletonTypemap onSkelTypeVar c ty))
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyAllDirt t) = (ValTyAllDirt (valueTypemap onTypeVar onSkelTypeVar onDirtVar (SDirtVar c) t))
valueTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTyCoArr pi t) = (ValTyCoArr (simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c pi) (valueTypemap onTypeVar onSkelTypeVar onDirtVar c t))

-- Return the CoercionType where onSkelTypeVar, onDirtVar, onTypeVar are applied to each
-- SkeletonType, Dirt, ValueType in the given CoercionType respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
coercionTypemap :: (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> Variable -> CoercionType -> CoercionType
coercionTypemap onTypeVar onSkelTypeVar onDirtVar c (CoSimple co) = (CoSimple (simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c co))
coercionTypemap onTypeVar onSkelTypeVar onDirtVar c (CoComp v1 v2) = (CoComp (computationTypemap onTypeVar onSkelTypeVar onDirtVar c v1) (computationTypemap onTypeVar onSkelTypeVar onDirtVar c v2))

-- Return the SimpleCoercionType where onSkelTypeVar, onDirtVar, onTypeVar are applied to each
-- SkeletonType, Dirt, ValueType in the given SimpleCoercionType respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
simpleCoercionTypemap :: (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> Variable -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c (DirtCoTypes d1 d2) = (DirtCoTypes (dirtmap onDirtVar c d1) (dirtmap onDirtVar c d2))
simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c (ValTypes d1 d2) = (ValTypes (valueTypemap onTypeVar onSkelTypeVar onDirtVar c d1) (valueTypemap onTypeVar onSkelTypeVar onDirtVar c d2))

-- Return the SkeletonType where onSkelTypeVar is applied to each
-- SkeletonType in the given SkeletonType respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied function.
skeletonTypemap :: (Variable -> SkeletonType -> SkeletonType) -> Variable -> SkeletonType -> SkeletonType
skeletonTypemap onSkelTypeVar c (SkelTUnit) = (SkelTUnit)
skeletonTypemap onSkelTypeVar c (SkellAllType t) = (SkellAllType (skeletonTypemap onSkelTypeVar (SSkelTypeVar c) t))
skeletonTypemap onSkelTypeVar c (SkelVar var) = (onSkelTypeVar c (SkelVar var))
skeletonTypemap onSkelTypeVar c (SkelArr t1 t2) = (SkelArr (skeletonTypemap onSkelTypeVar c t1) (skeletonTypemap onSkelTypeVar c t2))

-- Return the Dirt where onDirtVar is applied to each
-- Dirt in the given Dirt respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied function.
dirtmap :: (Variable -> Dirt -> Dirt) -> Variable -> Dirt -> Dirt
dirtmap onDirtVar c (DirtVariable var) = (onDirtVar c (DirtVariable var))
dirtmap onDirtVar c (EmptyDirt) = (EmptyDirt)
dirtmap onDirtVar c (UnionDirt d op1) = (UnionDirt (dirtmap onDirtVar c d) op1)

-- Return the ComputationType where onSkelTypeVar, onDirtVar, onTypeVar are applied to each
-- SkeletonType, Dirt, ValueType in the given ComputationType respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
computationTypemap :: (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> Variable -> ComputationType -> ComputationType
computationTypemap onTypeVar onSkelTypeVar onDirtVar c (ComputationTy t d) = (ComputationTy (valueTypemap onTypeVar onSkelTypeVar onDirtVar c t) (dirtmap onDirtVar c d))

-- Return the Coercion where onSkelTypeVar, onDirtVar, onTypeVar, onCoVar are applied to each
-- SkeletonType, Dirt, ValueType, Coercion in the given Coercion respectively.
-- The second argument represents the number of bound variables with respect to the top
-- level scope. It is also passed as an argument to the supplied functions.
coercionmap :: (Variable -> Coercion -> Coercion) -> (Variable -> ValueType -> ValueType) -> (Variable -> SkeletonType -> SkeletonType) -> (Variable -> Dirt -> Dirt) -> Variable -> Coercion -> Coercion
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoercionVar var) = (onCoVar c (CoercionVar var))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoUnit) = (CoUnit)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoTypeVar valty) = (CoTypeVar (valueTypemap onTypeVar onSkelTypeVar onDirtVar c valty))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoDirt d) = (CoDirt (dirtmap onDirtVar c d))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoArrow co1 co2) = (CoArrow (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co1) (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co2))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoHandler co1 co2) = (CoHandler (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co1) (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co2))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoEmptyDirt) = (CoEmptyDirt)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (UnionOp co op1) = (UnionOp (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co) op1)
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoskeletonAll co) = (CoskeletonAll (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar (SSkelTypeVar c) co))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoTypeAll co t) = (CoTypeAll (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar (STypeVar c) co) (skeletonTypemap onSkelTypeVar c t))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CodirtAll co) = (CodirtAll (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar (SDirtVar c) co))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoCoArrow pi co) = (CoCoArrow (simpleCoercionTypemap onTypeVar onSkelTypeVar onDirtVar c pi) (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co))
coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c (CoComputation co1 co2) = (CoComputation (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co1) (coercionmap onCoVar onTypeVar onSkelTypeVar onDirtVar c co2))

-- Perform one substitution step on a Value with the TmVar constructor.
valueSubstituteHelp :: Value -> Variable -> Value -> Value
valueSubstituteHelp sub c (TmVar var) = if (var == c) then (valueshiftplus c sub) else (TmVar var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Value in the given Value.
valueValueSubstitute :: Value -> Variable -> Value -> Value
valueValueSubstitute sub orig t = (valuemap (valueSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given Value.
valueValueTypeSubstitute :: ValueType -> Variable -> Value -> Value
valueValueTypeSubstitute sub orig t = (valuemap (\c x -> x) (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given Value.
valueSkeletonTypeSubstitute :: SkeletonType -> Variable -> Value -> Value
valueSkeletonTypeSubstitute sub orig t = (valuemap (\c x -> x) (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given Value.
valueDirtSubstitute :: Dirt -> Variable -> Value -> Value
valueDirtSubstitute sub orig t = (valuemap (\c x -> x) (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Coercion in the given Value.
valueCoercionSubstitute :: Coercion -> Variable -> Value -> Value
valueCoercionSubstitute sub orig t = (valuemap (\c x -> x) (\c x -> x) (\c x -> x) (\c x -> x) (coercionSubstituteHelp sub) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Value in the given OperationCompTuple.
operationCompTupleValueSubstitute :: Value -> Variable -> OperationCompTuple -> OperationCompTuple
operationCompTupleValueSubstitute sub orig t = (operationCompTuplemap (valueSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given OperationCompTuple.
operationCompTupleValueTypeSubstitute :: ValueType -> Variable -> OperationCompTuple -> OperationCompTuple
operationCompTupleValueTypeSubstitute sub orig t = (operationCompTuplemap (\c x -> x) (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given OperationCompTuple.
operationCompTupleSkeletonTypeSubstitute :: SkeletonType -> Variable -> OperationCompTuple -> OperationCompTuple
operationCompTupleSkeletonTypeSubstitute sub orig t = (operationCompTuplemap (\c x -> x) (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given OperationCompTuple.
operationCompTupleDirtSubstitute :: Dirt -> Variable -> OperationCompTuple -> OperationCompTuple
operationCompTupleDirtSubstitute sub orig t = (operationCompTuplemap (\c x -> x) (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Coercion in the given OperationCompTuple.
operationCompTupleCoercionSubstitute :: Coercion -> Variable -> OperationCompTuple -> OperationCompTuple
operationCompTupleCoercionSubstitute sub orig t = (operationCompTuplemap (\c x -> x) (\c x -> x) (\c x -> x) (\c x -> x) (coercionSubstituteHelp sub) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Value in the given Handler.
handlerValueSubstitute :: Value -> Variable -> Handler -> Handler
handlerValueSubstitute sub orig t = (handlermap (valueSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given Handler.
handlerValueTypeSubstitute :: ValueType -> Variable -> Handler -> Handler
handlerValueTypeSubstitute sub orig t = (handlermap (\c x -> x) (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given Handler.
handlerSkeletonTypeSubstitute :: SkeletonType -> Variable -> Handler -> Handler
handlerSkeletonTypeSubstitute sub orig t = (handlermap (\c x -> x) (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given Handler.
handlerDirtSubstitute :: Dirt -> Variable -> Handler -> Handler
handlerDirtSubstitute sub orig t = (handlermap (\c x -> x) (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Coercion in the given Handler.
handlerCoercionSubstitute :: Coercion -> Variable -> Handler -> Handler
handlerCoercionSubstitute sub orig t = (handlermap (\c x -> x) (\c x -> x) (\c x -> x) (\c x -> x) (coercionSubstituteHelp sub) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Value in the given Computation.
computationValueSubstitute :: Value -> Variable -> Computation -> Computation
computationValueSubstitute sub orig t = (computationmap (valueSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given Computation.
computationValueTypeSubstitute :: ValueType -> Variable -> Computation -> Computation
computationValueTypeSubstitute sub orig t = (computationmap (\c x -> x) (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given Computation.
computationSkeletonTypeSubstitute :: SkeletonType -> Variable -> Computation -> Computation
computationSkeletonTypeSubstitute sub orig t = (computationmap (\c x -> x) (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given Computation.
computationDirtSubstitute :: Dirt -> Variable -> Computation -> Computation
computationDirtSubstitute sub orig t = (computationmap (\c x -> x) (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Coercion in the given Computation.
computationCoercionSubstitute :: Coercion -> Variable -> Computation -> Computation
computationCoercionSubstitute sub orig t = (computationmap (\c x -> x) (\c x -> x) (\c x -> x) (\c x -> x) (coercionSubstituteHelp sub) orig t)

-- Perform one substitution step on a ValueType with the ValTyVar constructor.
valueTypeSubstituteHelp :: ValueType -> Variable -> ValueType -> ValueType
valueTypeSubstituteHelp sub c (ValTyVar var) = if (var == c) then (valueTypeshiftplus c sub) else (ValTyVar var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given ValueType.
valueTypeValueTypeSubstitute :: ValueType -> Variable -> ValueType -> ValueType
valueTypeValueTypeSubstitute sub orig t = (valueTypemap (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given ValueType.
valueTypeSkeletonTypeSubstitute :: SkeletonType -> Variable -> ValueType -> ValueType
valueTypeSkeletonTypeSubstitute sub orig t = (valueTypemap (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given ValueType.
valueTypeDirtSubstitute :: Dirt -> Variable -> ValueType -> ValueType
valueTypeDirtSubstitute sub orig t = (valueTypemap (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given CoercionType.
coercionTypeValueTypeSubstitute :: ValueType -> Variable -> CoercionType -> CoercionType
coercionTypeValueTypeSubstitute sub orig t = (coercionTypemap (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given CoercionType.
coercionTypeSkeletonTypeSubstitute :: SkeletonType -> Variable -> CoercionType -> CoercionType
coercionTypeSkeletonTypeSubstitute sub orig t = (coercionTypemap (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given CoercionType.
coercionTypeDirtSubstitute :: Dirt -> Variable -> CoercionType -> CoercionType
coercionTypeDirtSubstitute sub orig t = (coercionTypemap (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given SimpleCoercionType.
simpleCoercionTypeValueTypeSubstitute :: ValueType -> Variable -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypeValueTypeSubstitute sub orig t = (simpleCoercionTypemap (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given SimpleCoercionType.
simpleCoercionTypeSkeletonTypeSubstitute :: SkeletonType -> Variable -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypeSkeletonTypeSubstitute sub orig t = (simpleCoercionTypemap (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given SimpleCoercionType.
simpleCoercionTypeDirtSubstitute :: Dirt -> Variable -> SimpleCoercionType -> SimpleCoercionType
simpleCoercionTypeDirtSubstitute sub orig t = (simpleCoercionTypemap (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) orig t)

-- Perform one substitution step on a SkeletonType with the SkelVar constructor.
skeletonTypeSubstituteHelp :: SkeletonType -> Variable -> SkeletonType -> SkeletonType
skeletonTypeSubstituteHelp sub c (SkelVar var) = if (var == c) then (skeletonTypeshiftplus c sub) else (SkelVar var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given SkeletonType.
skeletonTypeSkeletonTypeSubstitute :: SkeletonType -> Variable -> SkeletonType -> SkeletonType
skeletonTypeSkeletonTypeSubstitute sub orig t = (skeletonTypemap (skeletonTypeSubstituteHelp sub) orig t)

-- Perform one substitution step on a Dirt with the DirtVariable constructor.
dirtSubstituteHelp :: Dirt -> Variable -> Dirt -> Dirt
dirtSubstituteHelp sub c (DirtVariable var) = if (var == c) then (dirtshiftplus c sub) else (DirtVariable var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given Dirt.
dirtDirtSubstitute :: Dirt -> Variable -> Dirt -> Dirt
dirtDirtSubstitute sub orig t = (dirtmap (dirtSubstituteHelp sub) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given ComputationType.
computationTypeValueTypeSubstitute :: ValueType -> Variable -> ComputationType -> ComputationType
computationTypeValueTypeSubstitute sub orig t = (computationTypemap (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given ComputationType.
computationTypeSkeletonTypeSubstitute :: SkeletonType -> Variable -> ComputationType -> ComputationType
computationTypeSkeletonTypeSubstitute sub orig t = (computationTypemap (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) orig t)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given ComputationType.
computationTypeDirtSubstitute :: Dirt -> Variable -> ComputationType -> ComputationType
computationTypeDirtSubstitute sub orig t = (computationTypemap (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) orig t)

-- Perform one substitution step on a Coercion with the CoercionVar constructor.
coercionSubstituteHelp :: Coercion -> Variable -> Coercion -> Coercion
coercionSubstituteHelp sub c (CoercionVar var) = if (var == c) then (coercionshiftplus c sub) else (CoercionVar var)

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Coercion in the given Coercion.
coercionCoercionSubstitute :: Coercion -> Variable -> Coercion -> Coercion
coercionCoercionSubstitute sub orig t = (rewriteCoercion (coercionmap (coercionSubstituteHelp sub) (\c x -> x) (\c x -> x) (\c x -> x) orig t))

-- Substitute every occurence of the variable orig with the first
-- argument sub with type ValueType in the given Coercion.
coercionValueTypeSubstitute :: ValueType -> Variable -> Coercion -> Coercion
coercionValueTypeSubstitute sub orig t = (rewriteCoercion (coercionmap (\c x -> x) (valueTypeSubstituteHelp sub) (\c x -> x) (\c x -> x) orig t))

-- Substitute every occurence of the variable orig with the first
-- argument sub with type SkeletonType in the given Coercion.
coercionSkeletonTypeSubstitute :: SkeletonType -> Variable -> Coercion -> Coercion
coercionSkeletonTypeSubstitute sub orig t = (rewriteCoercion (coercionmap (\c x -> x) (\c x -> x) (skeletonTypeSubstituteHelp sub) (\c x -> x) orig t))

-- Substitute every occurence of the variable orig with the first
-- argument sub with type Dirt in the given Coercion.
coercionDirtSubstitute :: Dirt -> Variable -> Coercion -> Coercion
coercionDirtSubstitute sub orig t = (rewriteCoercion (coercionmap (\c x -> x) (\c x -> x) (\c x -> x) (dirtSubstituteHelp sub) orig t))

-- Return a list of the free variables of the given Value.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesValue :: Variable -> Value -> [Variable]
freeVariablesValue c (TmVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesValue c (TmFun x t) = (nub (concat [(freeVariablesComputation (STermVar c) x),(freeVariablesValueType c t)]))
freeVariablesValue c (TmTSkellAbs t1) = (nub (concat [(freeVariablesValue (SSkelTypeVar c) t1)]))
freeVariablesValue c (TmTSkelApp t1 ty) = (nub (concat [(freeVariablesValue c t1),(freeVariablesSkeletonType c ty)]))
freeVariablesValue c (TmValueTypeAbs t ty) = (nub (concat [(freeVariablesValue (STypeVar c) t),(freeVariablesSkeletonType c ty)]))
freeVariablesValue c (TmValueTypeApp t ty) = (nub (concat [(freeVariablesValue c t),(freeVariablesValueType c ty)]))
freeVariablesValue c (TmDirtAbs t) = (nub (concat [(freeVariablesValue (SDirtVar c) t)]))
freeVariablesValue c (TmDirtApp t ty) = (nub (concat [(freeVariablesValue c t),(freeVariablesDirt c ty)]))
freeVariablesValue c (TmCoAbs t coty) = (nub (concat [(freeVariablesValue (SCoVar c) t),(freeVariablesSimpleCoercionType c coty)]))
freeVariablesValue c (TmCoApp t co) = (nub (concat [(freeVariablesValue c t),(freeVariablesCoercion c co)]))
freeVariablesValue c (TmCast val co) = (nub (concat [(freeVariablesValue c val),(freeVariablesCoercion c co)]))
freeVariablesValue c (TmUnit) = (nub (concat [[]]))
freeVariablesValue c (TmHandler h) = (nub (concat [(freeVariablesHandler c h)]))

-- Return a list of the free variables of the given OperationCompTuple.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesOperationCompTuple :: Variable -> OperationCompTuple -> [Variable]
freeVariablesOperationCompTuple c (OpAndComp comp op1) = (nub (concat [(freeVariablesComputation (STermVar c) comp)]))

-- Return a list of the free variables of the given Handler.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesHandler :: Variable -> Handler -> [Variable]
freeVariablesHandler c (ReturnHandler opsc ty cr) = (nub (concat [(concat (map (freeVariablesOperationCompTuple (STermVar c)) opsc)),(freeVariablesValueType c ty),(freeVariablesComputation (STermVar c) cr)]))

-- Return a list of the free variables of the given Computation.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesComputation :: Variable -> Computation -> [Variable]
freeVariablesComputation c (ReturnComp v) = (nub (concat [(freeVariablesValue c v)]))
freeVariablesComputation c (HandleComp comp v) = (nub (concat [(freeVariablesComputation c comp),(freeVariablesValue c v)]))
freeVariablesComputation c (ComputationApp t1 t2) = (nub (concat [(freeVariablesValue c t1),(freeVariablesValue c t2)]))
freeVariablesComputation c (LetComp v comp) = (nub (concat [(freeVariablesValue c v),(freeVariablesComputation (STermVar c) comp)]))
freeVariablesComputation c (DoComp c1 c2) = (nub (concat [(freeVariablesComputation c c1),(freeVariablesComputation (STermVar c) c2)]))
freeVariablesComputation c (CastComp comp gamma) = (nub (concat [(freeVariablesComputation c comp),(freeVariablesCoercion c gamma)]))
freeVariablesComputation c (OpComp v ty co op1) = (nub (concat [(freeVariablesValue c v),(freeVariablesValueType c ty),(freeVariablesComputation (STermVar c) co)]))

-- Return a list of the free variables of the given ValueType.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesValueType :: Variable -> ValueType -> [Variable]
freeVariablesValueType c (ValTyVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesValueType c (ValTUnit) = (nub (concat [[]]))
freeVariablesValueType c (ValTyArr ty comp) = (nub (concat [(freeVariablesValueType c ty),(freeVariablesComputationType c comp)]))
freeVariablesValueType c (ValTyHandler c1 c2) = (nub (concat [(freeVariablesComputationType c c1),(freeVariablesComputationType c c2)]))
freeVariablesValueType c (ValTyAllSkel t) = (nub (concat [(freeVariablesValueType (SSkelTypeVar c) t)]))
freeVariablesValueType c (ValTyAll t ty) = (nub (concat [(freeVariablesValueType (STypeVar c) t),(freeVariablesSkeletonType c ty)]))
freeVariablesValueType c (ValTyAllDirt t) = (nub (concat [(freeVariablesValueType (SDirtVar c) t)]))
freeVariablesValueType c (ValTyCoArr pi t) = (nub (concat [(freeVariablesSimpleCoercionType c pi),(freeVariablesValueType c t)]))

-- Return a list of the free variables of the given CoercionType.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesCoercionType :: Variable -> CoercionType -> [Variable]
freeVariablesCoercionType c (CoSimple co) = (nub (concat [(freeVariablesSimpleCoercionType c co)]))
freeVariablesCoercionType c (CoComp v1 v2) = (nub (concat [(freeVariablesComputationType c v1),(freeVariablesComputationType c v2)]))

-- Return a list of the free variables of the given SimpleCoercionType.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesSimpleCoercionType :: Variable -> SimpleCoercionType -> [Variable]
freeVariablesSimpleCoercionType c (DirtCoTypes d1 d2) = (nub (concat [(freeVariablesDirt c d1),(freeVariablesDirt c d2)]))
freeVariablesSimpleCoercionType c (ValTypes d1 d2) = (nub (concat [(freeVariablesValueType c d1),(freeVariablesValueType c d2)]))

-- Return a list of the free variables of the given SkeletonType.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesSkeletonType :: Variable -> SkeletonType -> [Variable]
freeVariablesSkeletonType c (SkelTUnit) = (nub (concat [[]]))
freeVariablesSkeletonType c (SkellAllType t) = (nub (concat [(freeVariablesSkeletonType (SSkelTypeVar c) t)]))
freeVariablesSkeletonType c (SkelVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesSkeletonType c (SkelArr t1 t2) = (nub (concat [(freeVariablesSkeletonType c t1),(freeVariablesSkeletonType c t2)]))

-- Return a list of the free variables of the given Dirt.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesDirt :: Variable -> Dirt -> [Variable]
freeVariablesDirt c (DirtVariable var) = if (var >= c) then [(minus var c)] else []
freeVariablesDirt c (EmptyDirt) = (nub (concat [[]]))
freeVariablesDirt c (UnionDirt d op1) = (nub (concat [(freeVariablesDirt c d)]))

-- Return a list of the free variables of the given ComputationType.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesComputationType :: Variable -> ComputationType -> [Variable]
freeVariablesComputationType c (ComputationTy t d) = (nub (concat [(freeVariablesValueType c t),(freeVariablesDirt c d)]))

-- Return a list of the free variables of the given Coercion.
-- The first argument represents the number of bound variables with respect to the top
-- level scope.
freeVariablesCoercion :: Variable -> Coercion -> [Variable]
freeVariablesCoercion c (CoercionVar var) = if (var >= c) then [(minus var c)] else []
freeVariablesCoercion c (CoUnit) = (nub (concat [[]]))
freeVariablesCoercion c (CoTypeVar valty) = (nub (concat [(freeVariablesValueType c valty)]))
freeVariablesCoercion c (CoDirt d) = (nub (concat [(freeVariablesDirt c d)]))
freeVariablesCoercion c (CoArrow co1 co2) = (nub (concat [(freeVariablesCoercion c co1),(freeVariablesCoercion c co2)]))
freeVariablesCoercion c (CoHandler co1 co2) = (nub (concat [(freeVariablesCoercion c co1),(freeVariablesCoercion c co2)]))
freeVariablesCoercion c (CoEmptyDirt) = (nub (concat [[]]))
freeVariablesCoercion c (UnionOp co op1) = (nub (concat [(freeVariablesCoercion c co)]))
freeVariablesCoercion c (CoskeletonAll co) = (nub (concat [(freeVariablesCoercion (SSkelTypeVar c) co)]))
freeVariablesCoercion c (CoTypeAll co t) = (nub (concat [(freeVariablesCoercion (STypeVar c) co),(freeVariablesSkeletonType c t)]))
freeVariablesCoercion c (CodirtAll co) = (nub (concat [(freeVariablesCoercion (SDirtVar c) co)]))
freeVariablesCoercion c (CoCoArrow pi co) = (nub (concat [(freeVariablesSimpleCoercionType c pi),(freeVariablesCoercion c co)]))
freeVariablesCoercion c (CoComputation co1 co2) = (nub (concat [(freeVariablesCoercion c co1),(freeVariablesCoercion c co2)]))
instance Ord Variable where
  compare (Z) (Z) = (EQ)
  compare (Z) _ = (LT)
  compare _ (Z) = (GT)
  compare (STermVar h1) (STermVar h2) = (compare h1 h2)
  compare (STermVar h1) (SSkelTypeVar h2) = (error "differing namespace found in compare")
  compare (STermVar h1) (SDirtVar h2) = (error "differing namespace found in compare")
  compare (STermVar h1) (STypeVar h2) = (error "differing namespace found in compare")
  compare (STermVar h1) (SCoVar h2) = (error "differing namespace found in compare")
  compare (SSkelTypeVar h1) (STermVar h2) = (error "differing namespace found in compare")
  compare (SSkelTypeVar h1) (SSkelTypeVar h2) = (compare h1 h2)
  compare (SSkelTypeVar h1) (SDirtVar h2) = (error "differing namespace found in compare")
  compare (SSkelTypeVar h1) (STypeVar h2) = (error "differing namespace found in compare")
  compare (SSkelTypeVar h1) (SCoVar h2) = (error "differing namespace found in compare")
  compare (SDirtVar h1) (STermVar h2) = (error "differing namespace found in compare")
  compare (SDirtVar h1) (SSkelTypeVar h2) = (error "differing namespace found in compare")
  compare (SDirtVar h1) (SDirtVar h2) = (compare h1 h2)
  compare (SDirtVar h1) (STypeVar h2) = (error "differing namespace found in compare")
  compare (SDirtVar h1) (SCoVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (STermVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (SSkelTypeVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (SDirtVar h2) = (error "differing namespace found in compare")
  compare (STypeVar h1) (STypeVar h2) = (compare h1 h2)
  compare (STypeVar h1) (SCoVar h2) = (error "differing namespace found in compare")
  compare (SCoVar h1) (STermVar h2) = (error "differing namespace found in compare")
  compare (SCoVar h1) (SSkelTypeVar h2) = (error "differing namespace found in compare")
  compare (SCoVar h1) (SDirtVar h2) = (error "differing namespace found in compare")
  compare (SCoVar h1) (STypeVar h2) = (error "differing namespace found in compare")
  compare (SCoVar h1) (SCoVar h2) = (compare h1 h2)
rewriteTypeToCoercion :: ValueType -> Coercion
rewriteTypeToCoercion (ValTyVar hnat) = CoTypeVar (ValTyVar hnat)
rewriteTypeToCoercion (ValTUnit) = CoUnit
rewriteTypeToCoercion (ValTyArr ty1 (ComputationTy ty2 dirt)) = CoArrow (rewriteTypeToCoercion ty1) (CoComputation (rewriteTypeToCoercion ty2) (CoDirt dirt))
rewriteTypeToCoercion (ValTyHandler (ComputationTy ty1 dirt1) (ComputationTy ty2 dirt2)) = CoHandler (CoComputation (rewriteTypeToCoercion ty1) (CoDirt dirt1)) (CoComputation (rewriteTypeToCoercion ty2) (CoDirt dirt2))
rewriteTypeToCoercion (ValTyAllSkel ty) = CoskeletonAll (rewriteTypeToCoercion ty)
rewriteTypeToCoercion (ValTyAll valty skel) = CoTypeAll (rewriteTypeToCoercion valty) skel
rewriteTypeToCoercion (ValTyAllDirt valty) = CodirtAll (rewriteTypeToCoercion valty)
rewriteTypeToCoercion (ValTyCoArr pi ty) = CoCoArrow pi (rewriteTypeToCoercion ty)

rewriteCoercion :: Coercion -> Coercion
rewriteCoercion (CoTypeVar ty) = rewriteTypeToCoercion ty
rewriteCoercion (CoArrow co1 co2) = CoArrow (rewriteCoercion co1) (rewriteCoercion co2)
rewriteCoercion (CoHandler co1 co2) = CoHandler (rewriteCoercion co1) (rewriteCoercion co2)
rewriteCoercion (UnionOp co1 op) = UnionOp (rewriteCoercion co1) op
rewriteCoercion (CoskeletonAll co) = CoskeletonAll (rewriteCoercion co)
rewriteCoercion (CoTypeAll co skel) = CoTypeAll (rewriteCoercion co) skel
rewriteCoercion (CoCoArrow pi co) = CoCoArrow pi (rewriteCoercion co)
rewriteCoercion (CoComputation co1 co2) = CoComputation (rewriteCoercion co1) (rewriteCoercion co2)
rewriteCoercion co = co
