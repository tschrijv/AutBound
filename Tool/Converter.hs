module Converter where

import Program
import GeneralTerms
import Converter.Environments
import Converter.FreeVariables
import Converter.Mappings
import Converter.Substitutions
import Converter.Types

-- | Data type for storing the functions that depend on the
-- variable representation
data VariableFunctions = VF {
  variableType :: [NamespaceDef] -> (Type, [Constructor]),
  variableInstances :: (Type, [Constructor]) -> [(Type, Type, [Function])],
  variableFunctions :: Language -> (Type, [Constructor]) -> [Function]
}

-- | Convert a language into a program using the specified variable functions
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
                getSubst lan ++
                getEnvFunctions lan ++
                getFreeVar lan,
    code = cd
  }
