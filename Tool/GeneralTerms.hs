{-# OPTIONS_GHC -Wall #-}

module GeneralTerms where

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
  = LeftLHS InstanceName
  | LeftSub IdName InstanceName
  deriving (Show, Eq)

--the right part of an expression like t1.ctx=lhs.ctx
data RightExpr
  = RightLHS InstanceName
  | RightSub IdName InstanceName
  | RightAdd RightExpr IdName
  deriving (Show, Eq)

--the complete expression of like t1.ctx=lhs.ctx
type NameSpaceRule = (LeftExpr, RightExpr)

--the definition of a namespace declaration
data NameSpaceDef
  = MkNameSpace NameSpaceName SortName [String]
  deriving (Show, Eq)

--definition of a sort
data SortDef
  = MkDefSort SortName [NamespaceInstance] [ConstructorDef] Bool
  deriving (Show, Eq)

--definition of a constructor
data ConstructorDef
  = MkDefConstructor
      ConstructorName
      [(IdName, SortName)] --list where all is inherited
      [(IdName, SortName)] -- just this
      [(IdName, SortName, FoldName)] -- for Foldables
      [NameSpaceRule]
      [HaskellTypeName]
  | MkBindConstructor
      ConstructorName
      [(IdName, SortName)] --list where all is inherited
      [(IdName, SortName)]
      [(IdName, SortName, FoldName)] -- for Foldables
      (String, NameSpaceName)
      [NameSpaceRule]
      [HaskellTypeName]
  | MkVarConstructor
      ConstructorName
      InstanceName
  deriving (Show, Eq)

class Named a where
  getName :: a -> String

instance Named SortDef where
  getName (MkDefSort sname _ _ _) = sname

instance Named NameSpaceDef where
  getName (MkNameSpace name _ _) = name

-- get the name of definition of a constructor
instance Named ConstructorDef where
  getName (MkDefConstructor cname _ _ _ _ _)    = cname
  getName (MkVarConstructor cname _)            = cname
  getName (MkBindConstructor cname _ _ _ _ _ _) = cname

instance Named NamespaceInstance where
  getName (INH name _) = name
  getName (SYN name _) = name

--get the defs of constructors in the sort
getConstrDefs :: SortDef -> [ConstructorDef]
getConstrDefs (MkDefSort _ _ cdefs _) = cdefs

-- get the instances by the sorts in the
getNSI :: SortDef -> [NamespaceInstance]
getNSI (MkDefSort _ instances _ _) = instances

--get the names   contexts and the namespaces it refers to for a sorts in a tuple
getNameAndNSI :: SortDef -> (SortName, [NamespaceInstance])
getNameAndNSI s = (getName s, getNSI s)

-- get the name on the left expression
getLeftExprId :: LeftExpr -> [IdName]
getLeftExprId (LeftLHS _)    = []
getLeftExprId (LeftSub iden _) = [iden]

getLeftIdSub :: LeftExpr -> IdName
getLeftIdSub (LeftLHS _)    = ""
getLeftIdSub (LeftSub iden _) = iden

--gets the idName of the rightexpr
getRightExprId :: RightExpr -> [IdName]
getRightExprId (RightLHS _)      = []
getRightExprId (RightSub name _) = [name]
getRightExprId (RightAdd expr _) = getRightExprId expr

-- get the namespaceName where the instance is referring to
getNamespaceNameInstance :: NamespaceInstance -> NameSpaceName
getNamespaceNameInstance (INH _ name) = name
getNamespaceNameInstance (SYN _ name) = name

--get the name of the context of a left expr
getInstanceNamesOfRuleLeft :: LeftExpr -> InstanceName
getInstanceNamesOfRuleLeft (LeftLHS name)   = name
getInstanceNamesOfRuleLeft (LeftSub _ name) = name

--get the name of the context of a right expr
getInstanceNamesOfRuleRight :: RightExpr -> InstanceName
getInstanceNamesOfRuleRight (RightAdd expr _) = getInstanceNamesOfRuleRight expr
getInstanceNamesOfRuleRight (RightLHS name) = name
getInstanceNamesOfRuleRight (RightSub _ name) = name

--collects all the rules of the identifiers used in the constructor and groups them in a list with each identifier getting a list of rules
collectRulesAllField :: [NameSpaceRule] -> [(IdName, SortName)] -> [(IdName, [NameSpaceRule])]
collectRulesAllField rules = map (\(i, _) -> collectRulesOfId rules i)
  where
    -- group the rules of one  identifier together
    collectRulesOfId :: [NameSpaceRule] -> IdName -> (IdName, [NameSpaceRule])
    collectRulesOfId nsr i = (i, filter (\(LeftSub fieldname ctxname, r) -> fieldname == i) nsr)

collectRulesSyn :: [NameSpaceRule] -> [(IdName, SortName)] -> [(IdName, [NameSpaceRule])] -> [(IdName, [NameSpaceRule])]
collectRulesSyn rules [] acc = ("lhs", collectRuleLHS rules []) : acc where
  collectRuleLHS :: [NameSpaceRule] -> [NameSpaceRule] -> [NameSpaceRule]
  collectRuleLHS ((LeftLHS ctxname, r):rest) acc =
    collectRuleLHS rest ((LeftLHS ctxname, r) : acc)
  collectRuleLHS (_:rest) acc = collectRuleLHS rest acc
  collectRuleLHS [] acc = acc
collectRulesSyn rules ((iden, _):rest) acc =
  collectRulesSyn rules rest (acc ++ [collectRulesOfIdSyn rules iden])
  where
    collectRulesOfIdSyn :: [NameSpaceRule] -> IdName -> (IdName, [NameSpaceRule])
    collectRulesOfIdSyn nsr iden = (iden, filter (\(LeftSub fieldname ctxname, RightSub fieldname2 ctxName2) -> fieldname == iden) nsr)
