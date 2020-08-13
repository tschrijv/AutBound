{-# OPTIONS_GHC -Wall #-}

module Program where

-- | Variable, function and constructor names
type Name = String

-- | Data types (including built-in and classes)
type Type = String

-- | A data type to represent the possible types in a type signature
-- | TyType represents the basic types like Bool, Int and String
-- | TyFunc represents the function type that maps TsType(s) to a TsType
-- | TyList represents a list of TsType
-- | TyVar represents the Variable type
-- | TyGeneric represents a generic type like in a -> a
-- | TyPrecondition represents preconditions in the type signature. There can only be one precondition type
-- | which contains all preconditions
data TsType 
  = TyBasic Type 
  | TyFunc [TsType] 
  | TyList TsType 
  | TyVar
  | TyGeneric String
  | TyPrecondition [(Type, Type)]

-- | Type signatures represented as a list of TsType ([Int, Bool, String] represents the Haskell signature Int -> Bool -> String)
type TypeSignature = [TsType]

-- | Description of functions
type Description = String

-- | Constructors are made up of a name and 0 or more type parameters
data Constructor = Constr Name [Type] deriving Eq

-- | Function parameters can be pure variables and pattern matches
-- for constructors
data Parameter
  = VarParam Name
  | ConstrParam Name [Parameter]
  | StringParam String
  | IntParam Int

-- | Expressions in function bodies can be
-- function calls (function name + parameters)
-- or constructor calls (constructor name + parameters)
data Expression
  = FnCall Name [Expression]
  | ConstrInst Name [Expression]
  | VarExpr Name
  | Minus Expression Expression
  | IntExpr Int
  | StringExpr String
  | IfExpr Expression Expression Expression
  | GTEExpr Expression Expression
  | EQExpr Expression Expression
  | ListExpr [Expression]
  | LambdaExpr [Parameter] Expression

-- | Functions are made up of a name, type signature and multiple head (parameter list)
-- and body (expression) pairs
data Function = Fn Name TypeSignature Description [([Parameter], Expression)]

-- | A complete program consists of type declarations, type class instances,
-- and functions
data Program = P {
  imports :: [(String, [String])],
  types :: [(Type, [Constructor])],
  instances :: [(Type, Type, [Function])],
  functions :: [Function],
  code :: [String]
}
