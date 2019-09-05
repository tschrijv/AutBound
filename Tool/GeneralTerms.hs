{-# OPTIONS_GHC -Wall #-}

module GeneralTerms
  ( collectRulesAllField
  , IdName
  , getTableOfInstancesToNamespacesSortWithSortName
  , NamespaceInstance(..)
  , InstanceName
  , LeftExpr(..)
  , RightExpr(..)
  , NameSpaceRule
  , ConstructorDef(..)
  , getname
  , SortDef(..)
  , wellFormed
  , Language
  , SortName
  , ConstructorName
  , NameSpaceName
  , NameSpaceDef(..)
  , getConstructorDefsSort
  , collectRulesSyn
  , isInh
  , isSyn
  , filterTableBySameNamespace
  , getInstanceNamesOfRuleLeft
  , getLeftIdSub
  , getInstanceSorts
  , capitalize
  , HaskellTypeName
  , getTableOfHasAccessVariable
  , FoldName
  ) where

import Data.Char
import Data.Maybe

type FoldName = String

type ConstructorName = String

type SortName = String

type NameSpaceName = String

type IdName = String

type HaskellTypeName = String

type Language = ([NameSpaceDef], [SortDef], [[String]], [String])

type InstanceName = String

--the inherited or synthesised contexts
data NamespaceInstance
  = INH InstanceName
        NameSpaceName
  | SYN InstanceName
        NameSpaceName
  deriving (Show, Eq)

--the left part of an expression like t1.ctx=lhs.ctx
data LeftExpr
  = LHS InstanceName
  | Sub IdName
        InstanceName
  deriving (Show, Eq)

--the right part of an expression like t1.ctx=lhs.ctx
data RightExpr
  = ExprLHS InstanceName
  | ExprSub IdName
            InstanceName
  | ExprAdd RightExpr
            IdName
  deriving (Show, Eq)

--the complete expression of like t1.ctx=lhs.ctx
type NameSpaceRule = (LeftExpr, RightExpr)

--the definition of a namespace declaration
data NameSpaceDef =
  MkNameSpace NameSpaceName
              SortName
              [String]
  deriving (Show, Eq)

--definition of a sort
data SortDef =
  MkDefSort SortName
            [NamespaceInstance]
            [ConstructorDef]
            Bool
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

--when is this syntax wellFormed : 1. when there are no duplicate constructors in the language i.e. there are no duplicate names among constructors or sorts and every sort has at the least one constructor
wellFormed :: Language -> Either String Bool
wellFormed ([], [], _, _) = Left "Empty Language"
wellFormed (namespaces, sorts, imps, _) = do
  o <- helpWellFormedVariablesNamespace sorts namespaces
  helpWellFormed (namespaces, sorts, imps) [] [] [] [] [] [] []

--accumulates the sortnames, constructornames, and the sortnames contained in the constructors,
--then looks up if all sortnames,namespacenames and contructornames are unique, if all sorts in the constructors exist,
--and whether sorts and constructors and namespaces have distinct names. Also namespacenames used in sorts should exist and constructors can only use variablebindings of namespaces they can access in the sort
helpWellFormed ::
     ([NameSpaceDef], [SortDef], [[String]])
  -> [SortName]
  -> [ConstructorName]
  -> [SortName]
  -> [NameSpaceName]
  -> [SortName]
  -> [(SortName, [NamespaceInstance])]
  -> [SortDef]
  -> Either String Bool
helpWellFormed (namespacedef:lanrest, sorts, imp) sortnames consnames sortconsnames namespacenames sortnamespaces instTable sortdefs =
  helpWellFormed
    (lanrest, sorts, imp)
    sortnames
    consnames
    sortconsnames
    ((getname namespacedef) : namespacenames)
    ((getSortNameSpace namespacedef) : sortnamespaces)
    instTable
    sortdefs
helpWellFormed ([], s:lanrest, imp) sortnames consnames sortconsnames namespacenames sortnamespaces instTable sortdefs = do
  a <- isEmptySort s
  b <-
    helpWellFormedNameSpaceNameInConstructors
      (getNamespaceNamesUsedInSort s)
      namespacenames
  c <-
    wellFormedConstructors
      (getConstructorDefsSort s)
      (map getname (getInstanceSorts s))
  d <- helpWellFormedInstances (getInstanceSortsNameSpaceNames s) namespacenames
  e <- helpWellFormedVariables (getConstructorDefsSort s) (getInstanceSorts s)
  f <- helpWellFormedInstanceNames (map getname (getInstanceSorts s))
  helpWellFormed
    ([], lanrest, imp)
    ((getname s) : sortnames)
    ((getConstructorNames s) ++ consnames)
    ((getSortsUsedByConstructors s) ++ sortconsnames)
    namespacenames
    sortnamespaces
    (getTableOfInstancesToNamespacesSortWithSortName s : instTable)
    (s : sortdefs)
helpWellFormed ([], [], imp) sortnames consnames sortconsnames namespacenames sortnamespaces instTable sortdefs = do
  a <- helpWellFormedSortName sortnames
  b <- helpWellFormedConstructorName consnames
  c <- helpWellFormedNameSpaceName namespacenames
  d <- helpWellFormedConstructorAndSort consnames sortnames
  e <- helpWellFormedNameSpaceAndSort namespacenames sortnames
  f <- helpWellFormedNameSpaceAndConstructor namespacenames consnames
  g <- helpWellFormedSortNameInConstructors sortconsnames sortnames
  h <- helpWellFormedSortNameInNamespaces sortnamespaces sortnames
  k <- helpWellFormedRulesInstances sortdefs instTable
  l <- isWellFormedBindToContext sortdefs instTable
  m <- helpWellFormedRulesLHSExpressions sortdefs instTable
  return True

wellFormedConstructors ::
     [ConstructorDef] -> [InstanceName] -> Either String Bool
wellFormedConstructors [] _ = return True
wellFormedConstructors (c:crest) inst = do
  a <- wellFormedConstructor c inst
  wellFormedConstructors crest inst

wellFormedConstructor :: ConstructorDef -> [InstanceName] -> Either String Bool
wellFormedConstructor cons inst = do
  a <- helpWellFormedIdentifiers (getIdentifiersConstructor cons)
  b <-
    helpWellFormedRulesIdentifiers
      (getAllIds cons)
      (getIdentifiersConstructor cons)
  c <-
    helpWellFormedIdentifierBindingInRightExpr
      (getRightExprIdsConstructorBinding cons)
      (getBinding cons)
  d <-
    helpWellFormedIdentifierInLeftExpr
      (getLeftExprIdsConstructor cons)
      (getIdentifiersWithoutBinding cons)
  e <-
    helpWellFormedIdentifierInRightExpr
      (getRightExprIdsConstructor cons)
      (getIdentifiersWithoutBinding cons)
  g <-
    helpWellFormedIdentifiers
      (map toLowerCaseFirst (getIdentifiersWithoutBinding cons))
  return True

isEmptySort :: SortDef -> Either String Bool
isEmptySort (MkDefSort name _ [] _) = Left (show name ++ " has no constructor")
isEmptySort _ = return True

-- variables in a sort can only access the inherited namespaces
helpWellFormedVariables ::
     [ConstructorDef] -> [NamespaceInstance] -> Either String Bool
helpWellFormedVariables [] _ = return True
helpWellFormedVariables ((MkVarConstructor _ contextName):rest) instances = do
  a <-
    shouldBeInSecondList
      [contextName]
      ([name | INH name _ <- instances])
      "Namespace is not an inherited namespace "
  helpWellFormedVariables rest instances
helpWellFormedVariables (_:rest) instances =
  helpWellFormedVariables rest instances

-- --function to detect if all namespaceinstances used in rules exist
-- helpWellFormedInstanceNamesExist ::
--      [InstanceName] -> [InstanceName] -> Either String Bool
-- helpWellFormedInstanceNamesExist l l2 =
--   shouldBeInSecondList l l2 "rule does not reference an existing instance"

--function to detect if all namespaces used in instances in sorts exist
helpWellFormedInstances ::
     [NameSpaceName] -> [NameSpaceName] -> Either String Bool
helpWellFormedInstances l l2 =
  shouldBeInSecondList l l2 "Instance does not reference an existing namespace"

--all instancenames across sorts should be unique
helpWellFormedInstanceNames :: [InstanceName] -> Either String Bool
helpWellFormedInstanceNames l =
  isUniqueInList l "Instance is not a unique name in the declaration "

--variables should only refer to namespace they are part of
helpWellFormedVariablesNamespace ::
     [SortDef] -> [NameSpaceDef] -> Either String Bool
helpWellFormedVariablesNamespace [] _ = return True
helpWellFormedVariablesNamespace ((MkDefSort sname inst cons _):rest) namespaces = do
  helpWellFormedVariablesCons sname cons inst namespaces
  helpWellFormedVariablesNamespace rest namespaces

helpWellFormedVariablesCons ::
     SortName
  -> [ConstructorDef]
  -> [NamespaceInstance]
  -> [NameSpaceDef]
  -> Either String Bool
helpWellFormedVariablesCons sname [] _ _ = Right True
helpWellFormedVariablesCons sname (MkVarConstructor name instanceName:rest) inst namespaces = do
  a <- helpWellFormedVarInst sname instanceName inst namespaces
  helpWellFormedVariablesCons sname rest inst namespaces
helpWellFormedVariablesCons sname (_:rest) inst namespace =
  helpWellFormedVariablesCons sname rest inst namespace

helpWellFormedVarInst ::
     SortName
  -> InstanceName
  -> [NamespaceInstance]
  -> [NameSpaceDef]
  -> Either String Bool
helpWellFormedVarInst sname name [] namespaces =
  Left ("No instance found with that name in " ++ name)
helpWellFormedVarInst sname name (inst:rest) namespaces =
  if getname inst == name
    then helpVarnamespace sname (getNamespaceNameInstance inst) namespaces
    else helpWellFormedVarInst sname name rest namespaces

helpVarnamespace :: SortName -> String -> [NameSpaceDef] -> Either String Bool
helpVarnamespace sname name [] =
  Left "Instance and namespace in variable do not coincide"
helpVarnamespace sname name (MkNameSpace namespacename sortname _:rest) =
  if namespacename == name
    then (if sname == sortname
            then return True
            else Left ("sort cannot use this namespace in " ++ sname))
    else helpVarnamespace sname name rest

--function to detect if all identifiers used in the rules exist as fields
helpWellFormedRulesIdentifiers :: [IdName] -> [IdName] -> Either String Bool
helpWellFormedRulesIdentifiers l l2 =
  shouldBeInSecondList l l2 "identifier not used in constructor"

--function to detect if all identifiers are unique in the fields of a constructor
helpWellFormedIdentifiers :: [IdName] -> Either String Bool
helpWellFormedIdentifiers l = isUniqueInList l "not unique identifier"

--function to detect if all sortnames are unique
helpWellFormedSortName :: [SortName] -> Either String Bool
helpWellFormedSortName l = isUniqueInList l "not unique sortname"

--function to detect if all constructors are unique
helpWellFormedConstructorName :: [ConstructorName] -> Either String Bool
helpWellFormedConstructorName l = isUniqueInList l "not unique constructor"

--function to detect if all NameSpaceNames are unique
helpWellFormedNameSpaceName :: [NameSpaceName] -> Either String Bool
helpWellFormedNameSpaceName l = isUniqueInList l "not unique namespace"

--function to detect if all ConstructorName and Sortnames are unique
helpWellFormedConstructorAndSort ::
     [ConstructorName] -> [SortName] -> Either String Bool
helpWellFormedConstructorAndSort l l2 =
  shouldNotBeInSecondList l l2 "constructor and sort have same name"

--function to detect if all NameSpaceNames and Sortnames are unique
helpWellFormedNameSpaceAndSort ::
     [NameSpaceName] -> [SortName] -> Either String Bool
helpWellFormedNameSpaceAndSort l l2 =
  shouldNotBeInSecondList l l2 "namespace and sort have same name"

--function to detect if all constructornames and namespacenames are unique
helpWellFormedNameSpaceAndConstructor ::
     [NameSpaceName] -> [ConstructorName] -> Either String Bool
helpWellFormedNameSpaceAndConstructor l l2 =
  shouldNotBeInSecondList l l2 "constructor and namespace have same name"

--function to detect if all sortnames in constructors are valid
helpWellFormedSortNameInConstructors ::
     [SortName] -> [SortName] -> Either String Bool
helpWellFormedSortNameInConstructors l l2 =
  shouldBeInSecondList l l2 "sortname in constructor does not appear"

--function to detect if all sortnames in constructors are valid
helpWellFormedSortNameInNamespaces ::
     [SortName] -> [SortName] -> Either String Bool
helpWellFormedSortNameInNamespaces l l2 =
  shouldBeInSecondList l l2 "sortname in namespace does not appear"

--function to detect if all namespacenames in constructors are valid (or in other words: are declared )
helpWellFormedNameSpaceNameInConstructors ::
     [NameSpaceName] -> [NameSpaceName] -> Either String Bool
helpWellFormedNameSpaceNameInConstructors l l2 =
  shouldBeInSecondList
    l
    l2
    "Namespace in constructor is not a declared namespace"

--detects if an identifier in the right expression does not appear as a binder
helpWellFormedIdentifierBindingInRightExpr ::
     [IdName] -> [IdName] -> Either String Bool
helpWellFormedIdentifierBindingInRightExpr l l2 =
  shouldBeInSecondList
    l
    l2
    "Identifier in right expression does not appear as binder"

--detects if an identifier in the right expression does not appear as constructorfield
helpWellFormedIdentifierInLeftExpr :: [IdName] -> [IdName] -> Either String Bool
helpWellFormedIdentifierInLeftExpr l l2 =
  shouldBeInSecondList
    l
    l2
    "Identifier in left expression does not appear as constructorfield"

--detects if an identifier in the right expression does not appear as constructorfield
helpWellFormedIdentifierInRightExpr ::
     [IdName] -> [IdName] -> Either String Bool
helpWellFormedIdentifierInRightExpr l l2 =
  shouldBeInSecondList
    l
    l2
    "Identifier in right expression does not appear as constructorfield"

--get the constructornames of a sortDef
getConstructorNames :: SortDef -> [ConstructorName]
getConstructorNames (MkDefSort _ _ cnames _) = map (getname) cnames

--get the defs of constructors in the sort
getConstructorDefsSort :: SortDef -> [ConstructorDef]
getConstructorDefsSort (MkDefSort _ _ cdefs _) = cdefs

--get the sort of the namespace
getSortNameSpace :: NameSpaceDef -> SortName
getSortNameSpace (MkNameSpace _ name _) = name

--get the sorts used in the constructor
getSortsConstructor :: ConstructorDef -> [SortName]
getSortsConstructor (MkDefConstructor _ lists sorts folds _ _) =
  map snd sorts ++ map snd lists ++ map (\(x, y, z) -> y) folds
getSortsConstructor (MkBindConstructor _ lists sorts folds _ _ _) =
  map snd sorts ++ map snd lists ++ map (\(x, y, z) -> y) folds
getSortsConstructor _ = []

--get the Identifiers of the arguments of a constructor (including the binder)
getIdentifiersConstructor :: ConstructorDef -> [String]
getIdentifiersConstructor (MkDefConstructor _ lists sorts folds _ _) =
  map fst lists ++ (map fst sorts) ++ map (\(x, y, z) -> x) folds
getIdentifiersConstructor (MkBindConstructor _ lists sorts folds namespace _ _) =
  map fst lists ++
  map fst sorts ++ map (\(x, y, z) -> x) folds ++ [fst namespace]
getIdentifiersConstructor _ = []

-- get all the identifiers without the binder included
getIdentifiersWithoutBinding :: ConstructorDef -> [String]
getIdentifiersWithoutBinding (MkDefConstructor _ lists sorts folds _ _) =
  (map fst sorts) ++ (map fst lists) ++ map (\(x, y, z) -> x) folds
getIdentifiersWithoutBinding (MkBindConstructor _ lists sorts folds _ _ _) =
  (map fst sorts) ++ (map fst lists) ++ map (\(x, y, z) -> x) folds
getIdentifiersWithoutBinding _ = []

-- get the name on the left expression
getLeftExprId :: LeftExpr -> [IdName]
getLeftExprId (LHS _)    = []
getLeftExprId (Sub id _) = [id]

getLeftIdSub :: LeftExpr -> IdName
getLeftIdSub (LHS _)    = ""
getLeftIdSub (Sub id _) = id

-- get the name on the right expression
getRightExprIdBinding :: RightExpr -> [IdName]
getRightExprIdBinding (ExprLHS _)       = []
getRightExprIdBinding (ExprSub _ _)     = []
getRightExprIdBinding (ExprAdd expr id) = (id : (getRightExprIdBinding expr))

--gets the idName of the rightexpr
getRightExprId :: RightExpr -> [IdName]
getRightExprId (ExprLHS _)      = []
getRightExprId (ExprSub name _) = [name]
getRightExprId (ExprAdd expr _) = getRightExprId expr

--get identifiers of the rule, left expression+the rightexpr
getRuleIdentifiers :: NameSpaceRule -> [IdName]
getRuleIdentifiers (l, r) =
  getLeftExprId l ++ getRightExprIdBinding r ++ getRightExprId r

--get the identifiers used in the rules defined in the constructor
getAllIds :: ConstructorDef -> [IdName]
getAllIds (MkDefConstructor _ _ sorts _ rules _) =
  concatMap getRuleIdentifiers rules
getAllIds (MkBindConstructor _ _ sorts _ namespace rules _) =
  concatMap getRuleIdentifiers rules
getAllIds _ = []

--get the binding of a constructor
getBinding :: ConstructorDef -> [IdName]
getBinding (MkBindConstructor _ _ _ _ name _ _) = [fst name]
getBinding _                                    = []

--get the ids of the RightExpr that bind, including the binder added
getRightExprIdsConstructorBinding :: ConstructorDef -> [IdName]
getRightExprIdsConstructorBinding (MkDefConstructor _ _ sorts _ rules _) =
  concatMap getRightExprIdBinding (map snd rules)
getRightExprIdsConstructorBinding (MkBindConstructor _ _ sorts _ namespace rules _) =
  concatMap getRightExprIdBinding (map snd rules)
getRightExprIdsConstructorBinding _ = []

-- --getListIds
-- getListIds :: ConstructorDef -> [SortName]
-- getListIds (MkDefConstructor _ lists sorts _ rules _) = (map fst lists)
-- getListIds (MkBindConstructor _ lists sorts _ namespace rules _) =
--   (map fst lists)
-- getListIds _ = []

-- --get ids of the folds
-- getFoldIds :: ConstructorDef -> [SortName]
-- getFoldIds (MkDefConstructor _ lists sorts folds rules _) =
--   map (\(x, y, z) -> x) folds
-- getFoldIds (MkBindConstructor _ lists sorts folds namespace rules _) =
--   map (\(x, y, z) -> x) folds
-- getFoldIds _ = []

-- get the ids of the RightExpr without any binders included
getRightExprIdsConstructor :: ConstructorDef -> [IdName]
getRightExprIdsConstructor (MkDefConstructor _ _ sorts _ rules _) =
  concatMap getRightExprId (map snd rules)
getRightExprIdsConstructor (MkBindConstructor _ _ sorts _ namespace rules _) =
  concatMap getRightExprId (map snd rules)
getRightExprIdsConstructor _ = []

--get the ids of the LeftExpr
getLeftExprIdsConstructor :: ConstructorDef -> [IdName]
getLeftExprIdsConstructor (MkDefConstructor _ _ sorts _ rules _) =
  concatMap getLeftExprId (map fst rules)
getLeftExprIdsConstructor (MkBindConstructor _ _ sorts _ namespace rules _) =
  concatMap getLeftExprId (map fst rules)
getLeftExprIdsConstructor _ = []

-- get the sorts used by constructors in a list of constructors
getSortsOfConstructors :: [ConstructorDef] -> [SortName]
getSortsOfConstructors constrs = concatMap (getSortsConstructor) constrs

--get the sorts used in all constructors of the sort
getSortsUsedByConstructors :: SortDef -> [SortName]
getSortsUsedByConstructors s =
  (getSortsOfConstructors (getConstructorDefsSort s))

--getNamespaceName of a ConstructorDef
getNamespaceNameConstructor :: ConstructorDef -> Maybe NameSpaceName
getNamespaceNameConstructor (MkBindConstructor _ _ _ _ name _ _) =
  Just (snd name)
getNamespaceNameConstructor _ = Nothing

--get the namespaces used by the constructors
getNamespaceNamesUsedInSort :: SortDef -> [NameSpaceName]
getNamespaceNamesUsedInSort s =
  map
    fromJust
    (filter
       isJust
       (map (getNamespaceNameConstructor) (getConstructorDefsSort s)))

-- get the namespaceName where the instance is referring to
getNamespaceNameInstance :: NamespaceInstance -> NameSpaceName
getNamespaceNameInstance (INH _ name) = name
getNamespaceNameInstance (SYN _ name) = name

--get the instances used by sorts
getInstanceSortsNameSpaceNames :: SortDef -> [NameSpaceName]
getInstanceSortsNameSpaceNames (MkDefSort _ instances _ _) =
  map getNamespaceNameInstance instances

--get the name of the context of a left expr
getInstanceNamesOfRuleLeft :: LeftExpr -> InstanceName
getInstanceNamesOfRuleLeft (LHS name)   = name
getInstanceNamesOfRuleLeft (Sub _ name) = name

--get the name of the context of a right expr
getInstanceNamesOfRuleRight :: RightExpr -> InstanceName
getInstanceNamesOfRuleRight (ExprAdd expr _) = getInstanceNamesOfRuleRight expr
getInstanceNamesOfRuleRight (ExprLHS name) = name
getInstanceNamesOfRuleRight (ExprSub _ name) = name

-- --get the name of the contexts an expr
-- getInstanceNamesOfRule :: NameSpaceRule -> [InstanceName]
-- getInstanceNamesOfRule (l, r) =
--   [getInstanceNamesOfRuleLeft l] ++ [getInstanceNamesOfRuleRight r]

-- -- get the instance names used by the rules in the constructor
-- getInstanceNamesOfConstructor :: ConstructorDef -> [InstanceName]
-- getInstanceNamesOfConstructor (MkDefConstructor _ _ _ _ rules _) =
--   concatMap getInstanceNamesOfRule rules
-- getInstanceNamesOfConstructor (MkBindConstructor _ _ _ _ _ rules _) =
--   concatMap getInstanceNamesOfRule rules
-- getInstanceNamesOfConstructor _ = []

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

-- --get a list of tuples with sortnames and their respective namespaceinstances
-- getTableOfInstancesToNamespacesSortsWithSortName ::
--      [SortDef] -> [(SortName, [NamespaceInstance])]
-- getTableOfInstancesToNamespacesSortsWithSortName sorts =
--   map getTableOfInstancesToNamespacesSortWithSortName sorts

  -- checking if the binding to a constructorrule is ok by looking if the right expression is of the right type
isWellFormedBindToContextConstructorRule ::
     SortName
  -> NameSpaceName
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> NameSpaceRule
  -> Either String Bool
isWellFormedBindToContextConstructorRule sname namespacebind tableIdentifiers tableInstances (_, ExprAdd expr id)
  | getRightExprId expr == [] &&
      any
        (\x ->
           getInstanceNamesOfRuleRight expr == getname x &&
           getNamespaceNameInstance x == namespacebind)
        (fromJust (lookup sname tableInstances)) = return True
  | getRightExprId expr /= [] &&
      any
        (\x ->
           getInstanceNamesOfRuleRight expr == getname x &&
           getNamespaceNameInstance x == namespacebind)
        (fromJust
           (lookup
              (fromJust (lookup (head (getRightExprId expr)) tableIdentifiers))
              tableInstances)) = return True
  | otherwise = Left "incorrect binding"
isWellFormedBindToContextConstructorRule _ _ _ _ _ = return True
  -- checking if the binding to a constructor is ok by looking if the right expression is of the right type for all the rules of its constructor (only checks bindingConstructors)

isWellFormedBindToContextConstructor ::
     SortName
  -> [(SortName, [NamespaceInstance])]
  -> ConstructorDef
  -> [Either String Bool]
isWellFormedBindToContextConstructor sname table (MkBindConstructor _ _ sortids _ (id, namespacename) rules _) =
  map
    (isWellFormedBindToContextConstructorRule sname namespacename sortids table)
    rules
isWellFormedBindToContextConstructor _ _ _ = [return True]

--helper for the binding check when
isWellFormedBindToContextSort ::
     [(SortName, [NamespaceInstance])] -> SortDef -> [Either String Bool]
isWellFormedBindToContextSort table s =
  concatMap
    (isWellFormedBindToContextConstructor (getname s) table)
    (getConstructorDefsSort s)

--binders should only be added to contexts that correspond to the same namespace (not necessarily the same context)
isWellFormedBindToContext ::
     [SortDef] -> [(SortName, [NamespaceInstance])] -> Either String Bool
isWellFormedBindToContext sdefs table
  | (length errors) > 0 = head errors
  | otherwise = return True
  where
    errors =
      [Left x | Left x <- concatMap (isWellFormedBindToContextSort table) sdefs]

--checks whether both the lefthandside and the right hand side abide by the check of whether they refer to the same namespace
helpWellFormedRulesInstancesRule ::
     SortName
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(IdName, SortName, FoldName)]
  -> [(SortName, [NamespaceInstance])]
  -> NameSpaceRule
  -> Either String Bool
helpWellFormedRulesInstancesRule sname lists tableIdentifiers folds tableInstances (leftexpr, rightexpr)
  | getRightExprId rightexpr /= [] &&
      elem
        (head (getRightExprId rightexpr))
        (map fst lists ++ map (\(x, y, z) -> x) folds) = return True
  | getLeftExprId leftexpr /= [] &&
      elem
        (head (getLeftExprId leftexpr))
        (map fst lists ++ map (\(a, b, c) -> a) folds) = return True
  | getRightExprId rightexpr == [] &&
      length rightInstanceLHS > 0 &&
      getLeftExprId leftexpr == [] &&
      length leftInstanceLHS > 0 &&
      getNamespaceNameInstance (head rightInstanceLHS) ==
      getNamespaceNameInstance (head leftInstanceLHS) = return True
  | getRightExprId rightexpr /= [] &&
      length rightInstanceNoLHS > 0 &&
      getLeftExprId leftexpr == [] &&
      length leftInstanceLHS > 0 &&
      getNamespaceNameInstance (head rightInstanceNoLHS) ==
      getNamespaceNameInstance (head leftInstanceLHS) = return True
  | getRightExprId rightexpr /= [] &&
      length rightInstanceNoLHS > 0 &&
      getLeftExprId leftexpr /= [] &&
      length leftInstanceNoLHS > 0 &&
      getNamespaceNameInstance (head rightInstanceNoLHS) ==
      getNamespaceNameInstance (head leftInstanceNoLHS) = return True
  | getRightExprId rightexpr == [] &&
      length rightInstanceLHS > 0 &&
      getLeftExprId leftexpr /= [] &&
      length leftInstanceNoLHS > 0 &&
      getNamespaceNameInstance (head rightInstanceLHS) ==
      getNamespaceNameInstance (head leftInstanceNoLHS) = return True
  | otherwise = Left ("incorrect context for this sort " ++ sname)
  where
    rightInstanceLHS =
      (filter
         (\x -> getInstanceNamesOfRuleRight rightexpr == getname x)
         (fromJust (lookup sname tableInstances)))
    rightInstanceNoLHS =
      (filter
         (\x -> getInstanceNamesOfRuleRight rightexpr == getname x)
         (fromJust
            (lookup
               (fromJust
                  (lookup (head (getRightExprId rightexpr)) tableIdentifiers))
               tableInstances)))
    leftInstanceLHS =
      (filter
         (\x -> getInstanceNamesOfRuleLeft leftexpr == getname x)
         (fromJust (lookup sname tableInstances)))
    leftInstanceNoLHS =
      (filter
         (\x -> getInstanceNamesOfRuleLeft leftexpr == getname x)
         (fromJust
            (lookup
               (fromJust
                  (lookup (head (getLeftExprId leftexpr)) tableIdentifiers))
               tableInstances)))

--checks if all the rules are welldefined for the normal constructors and the binding constructors
helpWellFormedRulesInstancesConstructor ::
     SortName
  -> [(SortName, [NamespaceInstance])]
  -> ConstructorDef
  -> [Either String Bool]
helpWellFormedRulesInstancesConstructor sname table (MkDefConstructor _ listids sortids folds rules _) =
  map (helpWellFormedRulesInstancesRule sname listids sortids folds table) rules
helpWellFormedRulesInstancesConstructor sname table (MkBindConstructor _ listids sortids folds (id, namespacename) rules _) =
  map (helpWellFormedRulesInstancesRule sname listids sortids folds table) rules
helpWellFormedRulesInstancesConstructor _ _ _ = [return True]

--checks if all the constructors have welltyped rules
helpWellFormedRulesInstancesSort ::
     [(SortName, [NamespaceInstance])] -> SortDef -> [Either String Bool]
helpWellFormedRulesInstancesSort table s =
  concatMap
    (helpWellFormedRulesInstancesConstructor (getname s) table)
    (getConstructorDefsSort s)

-- identifiers in Rules can only use contexts they are allowed to use
helpWellFormedRulesInstances ::
     [SortDef] -> [(SortName, [NamespaceInstance])] -> Either String Bool
helpWellFormedRulesInstances sdefs table
  | (length errors) > 0 = head errors
  | otherwise = return True
  where
    errors =
      [ Left x
      | Left x <- concatMap (helpWellFormedRulesInstancesSort table) sdefs
      ]

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

--LeftExpressions that are LHS should be SYN contexts
helpWellFormedRulesLHSExpressions ::
     [SortDef] -> [(SortName, [NamespaceInstance])] -> Either String Bool
helpWellFormedRulesLHSExpressions sdefs table
  | (length errors) > 0 = head errors
  | otherwise = return True
  where
    errors =
      [ Left x
      | Left x <- concatMap (helpWellFormedRulesLHSExpressionsSort table) sdefs
      ]

--checks if the left hand side is a synthesised namespace if an identifier appears on the left hand side of a rule expression
helpWellFormedRulesLHSExpressionsSort ::
     [(SortName, [NamespaceInstance])] -> SortDef -> [Either String Bool]
helpWellFormedRulesLHSExpressionsSort table s =
  concatMap
    (helpWellFormedRulesLHSExpressionsConstructor (getname s) table)
    (getConstructorDefsSort s)

helpWellFormedRulesLHSExpressionsConstructor ::
     SortName
  -> [(SortName, [NamespaceInstance])]
  -> ConstructorDef
  -> [Either String Bool]
helpWellFormedRulesLHSExpressionsConstructor sname table (MkDefConstructor _ _ sortids _ rules _) =
  map (helpWellFormedRulesInstancesRuleLHSLeft sname sortids table) rules
helpWellFormedRulesLHSExpressionsConstructor sname table (MkBindConstructor _ _ sortids _ (id, namespacename) rules _) =
  map (helpWellFormedRulesInstancesRuleLHSLeft sname sortids table) rules
helpWellFormedRulesLHSExpressionsConstructor _ _ _ = [Right True]

--checks if the left hand side and right hand side are wellformed in the sense that inherited contexts and synthesised contexts cannot be used in every position
helpWellFormedRulesInstancesRuleLHSLeft ::
     SortName
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> NameSpaceRule
  -> Either String Bool
helpWellFormedRulesInstancesRuleLHSLeft sname tableIdentifiers tableInstances (LHS contextName, ExprLHS contextName2)
  | length (findContextToNamespaceInstanceSyn contextName sname tableInstances) >
      0 &&
      length
        (findContextToNamespaceInstanceInh contextName2 sname tableInstances) >
      0 = return True
  | otherwise =
    Left
      (contextName ++
       contextName2 ++
       "not a good combination of synthesised and inherited namespaces")
helpWellFormedRulesInstancesRuleLHSLeft sname tableIdentifiers tableInstances (LHS contextName, ExprSub fieldname2 contextName2)
  | (lookup fieldname2 tableIdentifiers) == Nothing = return True
  | length (findContextToNamespaceInstanceSyn contextName sname tableInstances) >
      0 &&
      length
        (findContextToNamespaceInstanceSyn
           contextName2
           (fromJust (lookup fieldname2 tableIdentifiers))
           tableInstances) >
      0 = return True
  | otherwise = Left (contextName ++ "is not a synthesised namespace")
helpWellFormedRulesInstancesRuleLHSLeft sname tableIdentifiers tableInstances (leftexpr, ExprAdd expr _) =
  helpWellFormedRulesInstancesRuleLHSLeft
    sname
    tableIdentifiers
    tableInstances
    (leftexpr, expr)
helpWellFormedRulesInstancesRuleLHSLeft sname tableIdentifiers tableInstances (Sub fieldname contextName, ExprSub fieldname2 contextName2)
  | sname2 == Nothing || sname1 == Nothing = return True
  | fieldname == fieldname2 =
    Left
      (fieldname ++
       "appears on both sides of a rule, which would cause infinite recursion")
  | length
     (findContextToNamespaceInstanceInh
        contextName
        (fromJust sname1)
        tableInstances) >
      0 &&
      length
        (findContextToNamespaceInstanceSyn
           contextName2
           (fromJust sname2)
           tableInstances) >
      0 = return True
  | otherwise = Left (contextName ++ "is not a synthesised namespace")
  where
    sname2 = (lookup fieldname2 tableIdentifiers)
    sname1 = (lookup fieldname tableIdentifiers)
helpWellFormedRulesInstancesRuleLHSLeft sname tableIdentifiers tableInstances (Sub fieldname contextName, ExprLHS contextName2)
  | (lookup fieldname tableIdentifiers) == Nothing = return True
  | length
     (findContextToNamespaceInstanceInh
        contextName
        (fromJust (lookup fieldname tableIdentifiers))
        tableInstances) >
      0 &&
      length
        (findContextToNamespaceInstanceInh contextName2 sname tableInstances) >
      0 = return True
  | otherwise = Left (contextName ++ "is not a synthesised namespace")

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

--function to detect if all names are unique
isUniqueInList :: [String] -> String -> Either String Bool
isUniqueInList [] _ = return True
isUniqueInList (str:strs) err =
  if any (\x -> x == str) strs
    then Left (show (str) ++ err)
    else isUniqueInList strs err

--helper to detect if different lists have unique names
shouldNotBeInSecondList :: [String] -> [String] -> String -> Either String Bool
shouldNotBeInSecondList [] _ _ = return True
shouldNotBeInSecondList (str:crest) sorts err =
  if any (\x -> x == str) sorts
    then Left (show (str) ++ err)
    else (shouldNotBeInSecondList crest sorts err)

--helper to detect if names in the first list  exist in the available second list
shouldBeInSecondList :: [String] -> [String] -> String -> Either String Bool
shouldBeInSecondList [] _ _ = return True
shouldBeInSecondList (str:strs) sorts err =
  if any (\x -> x == str) sorts
    then (shouldBeInSecondList strs sorts err)
    else Left (show (str) ++ err)
