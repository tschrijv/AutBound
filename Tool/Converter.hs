module Converter where

import Program
import GeneralTerms
import Converter.Environments
import Converter.FreeVariables
import Converter.Mappings
import Converter.Shifts
import Converter.Substitutions
import Converter.Types

convert :: Language -> Program
convert lan@(nsd, sd, imp, cd) =
  let var = getHNatType nsd
      env  = getEnvType nsd
  in P {
    imports = imp,
    types = var : env : getTypes lan,
    instances = [getHNatOrd var],
    functions = getHNatModifiers var ++
                getGenerators nsd ++
                getMappings lan ++
                getShift lan ++
                getSubst lan ++
                getEnvFunctions lan ++
                getFreeVar lan,
    code = cd
  }
