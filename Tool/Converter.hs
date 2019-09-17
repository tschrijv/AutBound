module Converter where

import Program
import GeneralTerms

-- | Data type for storing the functions that depend on the
-- variable representation
data ConvertFunctions = VF {
  variableType :: Language -> (Type, [Constructor]),
  envType :: Language -> (Type, [Constructor]),
  userTypes :: Language -> [(Type, [Constructor])],
  variableInstances :: (Type, [Constructor]) -> [(Type, Type, [Function])],
  variableFunctions :: Language -> (Type, [Constructor]) -> [Function],
  envFunctions :: Language -> [Function]
}

-- | Convert a language into a program using the specified variable functions
convert :: Language -> ConvertFunctions -> Program
convert lan@(nsd, sd, imp, cd) vf =
  let var = (variableType vf) lan
      env = (envType vf) lan
  in P {
    imports = imp,
    types = var : env : (userTypes vf) lan,
    instances = (variableInstances vf) var,
    functions = (variableFunctions vf) lan var ++
                (envFunctions vf) lan,
    code = cd
  }
