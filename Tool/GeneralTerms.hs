{-# OPTIONS_GHC -Wall #-}

module GeneralTerms where

import Data.Maybe

type FoldName         = String
type ConstructorName  = String
type SortName         = String
type NameSpaceName    = String
type IdName           = String
type HaskellTypeName  = String
type Language         = ([NameSpaceDef], [SortDef], [[String]], [String])
type InstanceName     = String

--the inherited or synthesised contexts
data NamespaceInstance
  = INH InstanceName NameSpaceName
  | SYN InstanceName NameSpaceName
  deriving (Show, Eq)

--the left part of an expression like t1.ctx=lhs.ctx
data LeftExpr
  = LHS InstanceName
  | Sub IdName InstanceName
  deriving (Show, Eq)

--the right part of an expression like t1.ctx=lhs.ctx
data RightExpr
  = ExprLHS InstanceName
  | ExprSub IdName InstanceName
  | ExprAdd RightExpr IdName
  deriving (Show, Eq)

--the complete expression of like t1.ctx=lhs.ctx
type NameSpaceRule = (LeftExpr, RightExpr)

--the definition of a namespace declaration
data NameSpaceDef =
  MkNameSpace NameSpaceName SortName [String]
  deriving (Show, Eq)

--definition of a sort
data SortDef =
  MkDefSort SortName [NamespaceInstance] [ConstructorDef] Bool
  deriving (Show, Eq)

--definition of a constructor
data ConstructorDef
  = MkDefConstructor ConstructorName
                     [(IdName, SortName)] --list where all is inherited
                     [(IdName, SortName)] -- just this
                     [(IdName, SortName, FoldName)] -- for Foldables
                     [NameSpaceRule]
                     [HaskellTypeName]
  | MkBindConstructor ConstructorName
                      [(IdName, SortName)] --list where all is inherited
                      [(IdName, SortName)]
                      [(IdName, SortName, FoldName)] -- for Foldables
                      (String, NameSpaceName)
                      [NameSpaceRule]
                      [HaskellTypeName]
  | MkVarConstructor ConstructorName
                     InstanceName
  deriving (Show, Eq)

class Named a where
  getName :: a -> String

instance Named SortDef where
  getName (MkDefSort sname _ _ _) = sname

instance Named NameSpaceDef where
  getName (MkNameSpace name _ _) = name

instance Named ConstructorDef
    -- get the name of definition of a constructor
                                                   where
  getName (MkDefConstructor cname _ _ _ _ _)    = cname
  getName (MkVarConstructor cname _)            = cname
  getName (MkBindConstructor cname _ _ _ _ _ _) = cname

instance Named NamespaceInstance where
  getName (INH name _) = name
  getName (SYN name _) = name

--get the defs of constructors in the sort
getConstructorDefsSort :: SortDef -> [ConstructorDef]
getConstructorDefsSort (MkDefSort _ _ cdefs _) = cdefs

-- get the name on the left expression
getLeftExprId :: LeftExpr -> [IdName]
getLeftExprId (LHS _)    = []
getLeftExprId (Sub id _) = [id]

getLeftIdSub :: LeftExpr -> IdName
getLeftIdSub (LHS _)    = ""
getLeftIdSub (Sub id _) = id

--gets the idName of the rightexpr
getRightExprId :: RightExpr -> [IdName]
getRightExprId (ExprLHS _)      = []
getRightExprId (ExprSub name _) = [name]
getRightExprId (ExprAdd expr _) = getRightExprId expr

-- get the namespaceName where the instance is referring to
getNamespaceNameInstance :: NamespaceInstance -> NameSpaceName
getNamespaceNameInstance (INH _ name) = name
getNamespaceNameInstance (SYN _ name) = name

--get the name of the context of a left expr
getInstanceNamesOfRuleLeft :: LeftExpr -> InstanceName
getInstanceNamesOfRuleLeft (LHS name)   = name
getInstanceNamesOfRuleLeft (Sub _ name) = name

--get the name of the context of a right expr
getInstanceNamesOfRuleRight :: RightExpr -> InstanceName
getInstanceNamesOfRuleRight (ExprAdd expr _) = getInstanceNamesOfRuleRight expr
getInstanceNamesOfRuleRight (ExprLHS name) = name
getInstanceNamesOfRuleRight (ExprSub _ name) = name

-- get the instances by the sorts in the
getInstanceSorts :: SortDef -> [NamespaceInstance]
getInstanceSorts (MkDefSort _ instances _ _) = instances

--get the names   contexts and the namespaces it refers to for a sorts in a tuple
sortNameAndNSI :: SortDef -> (SortName, [NamespaceInstance])
sortNameAndNSI s = (getName s, getInstanceSorts s)

--collects all the rules of the identifiers used in the constructor and groups them in a list with each identifier getting a list of rules
collectRulesAllField ::
     [NameSpaceRule]
  -> [(IdName, SortName)]
  -> [(IdName, [NameSpaceRule])]
  -> [(IdName, [NameSpaceRule])]
collectRulesAllField rules [] acc = acc
collectRulesAllField rules ((id, _):rest) acc =
  collectRulesAllField rules rest (acc ++ [collectRulesOfId rules id []])
  where
    -- group the rules of one  identifier together
    collectRulesOfId ::
        [NameSpaceRule] -> IdName -> [NameSpaceRule] -> (IdName, [NameSpaceRule])
    collectRulesOfId [] id acc = (id, acc)
    collectRulesOfId ((Sub fieldname ctxname, r):rest) id acc
      | fieldname == id =
        collectRulesOfId rest id ((Sub fieldname ctxname, r) : acc)
      | otherwise = collectRulesOfId rest id acc
    collectRulesOfId (_:rest) id acc = collectRulesOfId rest id acc

collectRulesOfIdSyn ::
     [NameSpaceRule] -> IdName -> [NameSpaceRule] -> (IdName, [NameSpaceRule])
collectRulesOfIdSyn [] id acc = (id, acc)
collectRulesOfIdSyn ((Sub fieldname ctxname, ExprSub fieldname2 ctxName2):rest) id acc
  | fieldname == id =
    collectRulesOfIdSyn
      rest
      id
      ((Sub fieldname ctxname, ExprSub fieldname2 ctxName2) : acc)
  | otherwise = collectRulesOfIdSyn rest id acc
collectRulesOfIdSyn (_:rest) id acc = collectRulesOfIdSyn rest id acc

collectRuleLHS :: [NameSpaceRule] -> [NameSpaceRule] -> [NameSpaceRule]
collectRuleLHS ((LHS ctxname, r):rest) acc =
  collectRuleLHS rest ((LHS ctxname, r) : acc)
collectRuleLHS (_:rest) acc = collectRuleLHS rest acc
collectRuleLHS [] acc = acc

collectRulesSyn ::
     [NameSpaceRule]
  -> [(IdName, SortName)]
  -> [(IdName, [NameSpaceRule])]
  -> [(IdName, [NameSpaceRule])]
collectRulesSyn rules [] acc = (("lhs", collectRuleLHS rules []) : acc)
collectRulesSyn rules ((id, _):rest) acc =
  collectRulesSyn rules rest (acc ++ [collectRulesOfIdSyn rules id []])
