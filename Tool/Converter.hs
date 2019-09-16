module Converter where

import Program
import GeneralTerms
import Converter.Environments
import Converter.FreeVariables
import Converter.Mappings
import Converter.Shifts
import Converter.Substitutions
import Converter.Types

data VariableFunctions = VF {
  variableType :: [NameSpaceDef] -> (Type, [Constructor]),
  variableInstances :: (Type, [Constructor]) -> [(Type, Type, [Function])],
  variableFunctions :: Language -> (Type, [Constructor]) -> [Function]
}

convert :: Language -> VariableFunctions -> Program
convert lan@(nsd, sd, imp, cd) vf =
  let var = (variableType vf) nsd
      env  = getEnvType nsd
  in P {
    imports = imp,
    types = var : env : getTypes lan,
    instances = (variableInstances vf) var,
    functions = (variableFunctions vf) lan var ++
                getMappings lan ++
                getShift lan ++
                getSubst lan ++
                getEnvFunctions lan ++
                getFreeVar lan,
    code = cd
  }
