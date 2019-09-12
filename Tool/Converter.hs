module Converter where

import Abstract
import GeneralTerms
import Converter.Environments
import Converter.FreeVariables
import Converter.Mappings
import Converter.Shifts
import Converter.Substitutions
import Converter.Types

convert :: Language -> Program
convert lan@(nsd, sd, imp, cd) =
  let hnat = getHNatType nsd
      env  = getEnvType nsd
  in P {
    imports = imp,
    types = hnat : env : getTypes lan,
    instances = [getHNatOrd nsd hnat],
    functions = getHNatModifiers hnat ++
                getGenerators nsd ++
                getMappings lan ++
                getShift lan ++
                getSubst lan ++
                getEnvFunctions lan ++
                getFreeVar lan,
    code = cd
  }
