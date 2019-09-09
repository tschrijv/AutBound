{-# OPTIONS_GHC -Wall #-}

module GeneralTerms where

import Data.Char
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
  getname :: a -> String

instance Named SortDef where
  getname (MkDefSort sname _ _ _) = sname

instance Named NameSpaceDef where
  getname (MkNameSpace name _ _) = name

instance Named ConstructorDef
    -- get the name of definition of a constructor
                                                   where
  getname (MkDefConstructor cname _ _ _ _ _)    = cname
  getname (MkVarConstructor cname _)            = cname
  getname (MkBindConstructor cname _ _ _ _ _ _) = cname

instance Named NamespaceInstance where
  getname (INH name _) = name
  getname (SYN name _) = name

toLowerCaseFirst :: String -> String
toLowerCaseFirst (first:rest) = ((toLower first) : rest)

capitalize :: String -> String
capitalize (first:rest) = ((toUpper first) : rest)

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

isInh :: NamespaceInstance -> Bool
isInh (INH _ _) = True
isInh _         = False

isSyn :: NamespaceInstance -> Bool
isSyn (SYN _ _) = True
isSyn _         = False

--get the names   contexts and the namespaces it refers to for a sorts in a tuple
getTableOfInstancesToNamespacesSortWithSortName ::
     SortDef -> (SortName, [NamespaceInstance])
getTableOfInstancesToNamespacesSortWithSortName s =
  (getname s, getInstanceSorts s)

-- group the rules of one  identifier together
collectRulesOfId ::
     [NameSpaceRule] -> IdName -> [NameSpaceRule] -> (IdName, [NameSpaceRule])
collectRulesOfId [] id acc = (id, acc)
collectRulesOfId ((Sub fieldname ctxname, r):rest) id acc
  | fieldname == id =
    collectRulesOfId rest id ((Sub fieldname ctxname, r) : acc)
  | otherwise = collectRulesOfId rest id acc
collectRulesOfId (_:rest) id acc = collectRulesOfId rest id acc

--collects all the rules of the identifiers used in the constructor and groups them in a list with each identifier getting a list of rules
collectRulesAllField ::
     [NameSpaceRule]
  -> [(IdName, SortName)]
  -> [(IdName, [NameSpaceRule])]
  -> [(IdName, [NameSpaceRule])]
collectRulesAllField rules [] acc = acc
collectRulesAllField rules ((id, _):rest) acc =
  collectRulesAllField rules rest (acc ++ [collectRulesOfId rules id []])

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

-- filters all the synthesised namespaces
findContextToNamespaceInstanceSyn ::
     InstanceName
  -> SortName
  -> [(SortName, [NamespaceInstance])]
  -> [NamespaceInstance]
findContextToNamespaceInstanceSyn ctxName sname table =
  filter
    (\x -> getname x == ctxName)
    [ SYN ctxNamesyn namespacename
    | SYN ctxNamesyn namespacename <- fromJust (lookup sname table)
    ]

-- filters all the inherited namespaces
findContextToNamespaceInstanceInh ::
     InstanceName
  -> SortName
  -> [(SortName, [NamespaceInstance])]
  -> [NamespaceInstance]
findContextToNamespaceInstanceInh ctxName sname table =
  filter
    (\x -> getname x == ctxName)
    [ INH ctxNameinh namespacename
    | INH ctxNameinh namespacename <- fromJust (lookup sname table)
    ]

filterTableBySameNamespace ::
     NamespaceInstance
  -> [(SortName, [NamespaceInstance])]
  -> [(SortName, [NamespaceInstance])]
filterTableBySameNamespace inst table =
  map (filterTableBySameNamespaceSort (getNamespaceNameInstance inst)) table

filterTableBySameNamespaceSort ::
     NameSpaceName
  -> (SortName, [NamespaceInstance])
  -> (SortName, [NamespaceInstance])
filterTableBySameNamespaceSort namespacename (sname, list) = (sname, newlist)
  where
    newlist = filter (\x -> getNamespaceNameInstance x == namespacename) list

-- function generating for each Sort, if it has access to some variable
isVariable :: ConstructorDef -> Bool
isVariable (MkVarConstructor _ _) = True
isVariable _                      = False

hasVariables :: SortDef -> Bool
hasVariables s = or (map isVariable (getConstructorDefsSort s))

getTableOfHasVariable :: [SortDef] -> [(SortName, Bool)]
getTableOfHasVariable [] = []
getTableOfHasVariable (s:srest) =
  ((getname s, hasVariables s) : getTableOfHasVariable srest)

hasAccessSortName :: [(SortName, SortDef)] -> [SortName] -> SortName -> Bool
hasAccessSortName table visited nextSort
  | any (\x -> x == nextSort) visited = False
  | otherwise =
    snd
      (sortCanAccessVariables
         (map snd table)
         (nextSort : visited)
         (fromJust (lookup nextSort table)))

constructorCanAccessVariables ::
     [(SortName, SortDef)] -> [SortName] -> ConstructorDef -> Bool
constructorCanAccessVariables table visited (MkVarConstructor _ _) = True
constructorCanAccessVariables table visited (MkBindConstructor _ listSorts sorts folds _ _ _) =
  or
    (map
       (hasAccessSortName table visited)
       ((map snd sorts) ++ (map snd listSorts) ++ map (\(a, b, c) -> b) folds))
constructorCanAccessVariables table visited (MkDefConstructor _ listSorts sorts folds _ _) =
  or
    (map
       (hasAccessSortName table visited)
       ((map snd sorts) ++ (map snd listSorts) ++ map (\(a, b, c) -> b) folds))

sortCanAccessVariables :: [SortDef] -> [SortName] -> SortDef -> (SortName, Bool)
sortCanAccessVariables allSorts listVisited s
  | hasAccess = (sname, hasAccess)
  | otherwise = (sname, findPathToVariable)
  where
    sname = getname s
    hasAccess = fromJust (lookup sname (getTableOfHasVariable allSorts))
    sortDefTable = map (\x -> (getname x, x)) allSorts
    findPathToVariable =
      or
        (map
           (constructorCanAccessVariables sortDefTable listVisited)
           (getConstructorDefsSort s))

getTableOfHasAccessVariable :: [SortDef] -> [(SortName, Bool)]
getTableOfHasAccessVariable [] = []
getTableOfHasAccessVariable sList = map (sortCanAccessVariables sList []) sList
