{-# OPTIONS_GHC -Wall #-}

module Abstract where

import GeneralTerms

-- | Variable, function and constructor names
type Name = String
-- | Data types (including built-in and classes)
type Type = String
-- | Constructors are made up of a name and 0 or more type parameters
type Constructor = (Name, [Type])
-- | Function parameters can be pure variables and pattern matches for constructors
data Parameter = VarParam Name | ConstrParam Name [Parameter]
-- | Expressions in function bodies can be
-- function calls (function name + parameters)
-- or constructor calls (constructor name + parameters)
data Expression = FnCall Name [Parameter] | ConstrInst Name [Parameter]
-- | Functions are made up of a name and multiple head (parameter list)
-- and body (expression) pairs
type Function = (Name, [([Parameter], Expression)])

-- | A complete program consists of type declarations, type class instances,
-- and functions
data Program = P {
  imports :: [(String, [String])],
  types :: [(Type, [Constructor])],
  instances :: [(Type, Type, [Function])],
  functions :: [Function],
  code :: [String]
}

convert :: Language -> Program
convert (nsd, sd, imp, cd) =
  P {
    imports = imp,
    types = [],
    instances = [],
    functions = [],
    code = cd
  }
