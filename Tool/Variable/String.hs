module Variable.String where

import GeneralTerms
import Program

getVariableType :: [NamespaceDef] -> (Type, [Constructor])
getVariableType nsd = ("Variable", map (\ns -> Constr ('S' : getName ns) ["String"]) nsd)

getVariableInstances :: (Type, [Constructor]) -> [(Type, Type, [Function])]
getVariableInstances _ = []

getVariableFunctions :: Language -> (Type, [Constructor]) -> [Function]
getVariableFunctions _ _ = []
