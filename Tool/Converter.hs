module Converter where

import Program
import GeneralTerms

-- | Data type for storing the functions that depend on the
-- variable representation
data ConvertFunctions = VF {
  variableType :: Language -> (Type, [Constructor]),
  userTypes :: Language -> [(Type, [Constructor])],
  variableInstances :: (Type, [Constructor]) -> [(Type, Type, [Function])],
  variableFunctions :: Language -> (Type, [Constructor]) -> [Function],
  nativeCode :: Language -> (Type, [Constructor])-> [String]
}

-- | Convert a language into a program using the specified variable functions
convert :: Language -> ConvertFunctions -> Program
convert lan@(nsd, sd, _, imp, cd) vf =
  let var = (variableType vf) lan
  in P {
    imports = imp,
    types = var : (userTypes vf) lan,
    instances = (variableInstances vf) var,
    functions = (variableFunctions vf) lan var,
    code = (nativeCode vf) lan var ++ cd
  }
