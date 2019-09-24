{-# OPTIONS_GHC -Wall #-}

module WellFormed (wellFormed) where

import GeneralTerms
import Utility
import Data.Maybe

--when is this syntax wellFormed : 1. when there are no duplicate constructors in the language i.e. there are no duplicate names among constructors or sorts and every sort has at the least one constructor
wellFormed :: Language -> Either String Bool
wellFormed ([], [], _, _) = Left "Empty Language"
wellFormed (namespaces, sorts, _, _) = do
  _ <- helpWellFormedVariablesNamespace sorts namespaces
  helpWellFormed (namespaces, sorts) [] [] [] [] [] [] []

--accumulates the sortnames, constructornames, and the sortnames contained in the constructors,
--then looks up if all sortnames,namespacenames and contructornames are unique, if all sorts in the constructors exist,
--and whether sorts and constructors and namespaces have distinct names. Also namespacenames used in sorts should exist and constructors can only use variablebindings of namespaces they can access in the sort
helpWellFormed :: ([NamespaceDef], [SortDef]) -> [SortName] -> [ConstructorName] -> [SortName] -> [NamespaceName] -> [SortName] -> [(SortName, [Context])] -> [SortDef] -> Either String Bool
helpWellFormed (namespacedef:lanrest, sorts) sortnames consnames sortconsnames namespacenames sortnamespaces instTable sortdefs =
  helpWellFormed
    (lanrest, sorts)
    sortnames
    consnames
    sortconsnames
    (nname namespacedef : namespacenames)
    (nsort namespacedef : sortnamespaces)
    instTable
    sortdefs
helpWellFormed ([], s:lanrest) sortnames consnames sortconsnames namespacenames sortnamespaces instTable sortdefs = do
  _ <- isEmptySort s
  _ <- helpWellFormedNameSpaceNameInConstructors getNamespaceNamesUsedInSort namespacenames
  _ <- wellFormedConstructors (sctors s)
  _ <- helpWellFormedInstances (getInstanceSortsNameSpaceNames s) namespacenames
  _ <- helpWellFormedVariables (sctors s) (sctxs s)
  _ <- helpWellFormedInstanceNames (map xinst (sctxs s))
  helpWellFormed
    ([], lanrest)
    (sname s : sortnames)
    (getConstructorNames s ++ consnames)
    (getSortsUsedByConstructors ++ sortconsnames)
    namespacenames
    sortnamespaces
    (snameAndCtxs s : instTable)
    (s : sortdefs)
    where
      --get the namespaces used by the constructors
      getNamespaceNamesUsedInSort :: [NamespaceName]
      getNamespaceNamesUsedInSort = map fromJust (filter isJust (map getNamespaceNameConstructor (sctors s)))
        where
          --getNamespaceName of a ConstructorDef
          getNamespaceNameConstructor :: ConstructorDef -> Maybe NamespaceName
          getNamespaceNameConstructor (MkBindConstructor _ _ _ _ name _ _) =
            Just (snd name)
          getNamespaceNameConstructor _ = Nothing

      --get the instances used by sorts
      getInstanceSortsNameSpaceNames :: SortDef -> [NamespaceName]
      getInstanceSortsNameSpaceNames (MkDefSort _ ctxs _ _) =
        map xnamespace ctxs

      --get the constructornames of a sortDef
      getConstructorNames :: SortDef -> [ConstructorName]
      getConstructorNames (MkDefSort _ _ cnames _) = map cname cnames

      --get the sorts used in all constructors of the sort
      getSortsUsedByConstructors :: [SortName]
      getSortsUsedByConstructors = getSortsOfConstructors (sctors s)
        where
          -- get the sorts used by constructors in a list of constructors
          getSortsOfConstructors :: [ConstructorDef] -> [SortName]
          getSortsOfConstructors = concatMap getSortsConstructor where
            --get the sorts used in the constructor
            getSortsConstructor :: ConstructorDef -> [SortName]
            getSortsConstructor (MkDefConstructor _ lists sorts folds _ _) = map snd sorts ++ map snd lists ++ map (\(_, y, _) -> y) folds
            getSortsConstructor (MkBindConstructor _ lists sorts folds _ _ _) = map snd sorts ++ map snd lists ++ map (\(_, y, _) -> y) folds
            getSortsConstructor _ = []
helpWellFormed ([], []) sortnames consnames sortconsnames namespacenames sortnamespaces instTable sortdefs = do
  _ <- helpWellFormedSortName sortnames
  _ <- helpWellFormedConstructorName consnames
  _ <- helpWellFormedNameSpaceName namespacenames
  _ <- helpWellFormedConstructorAndSort consnames sortnames
  _ <- helpWellFormedNameSpaceAndSort namespacenames sortnames
  _ <- helpWellFormedNameSpaceAndConstructor namespacenames consnames
  _ <- helpWellFormedSortNameInConstructors sortconsnames sortnames
  _ <- helpWellFormedSortNameInNamespaces sortnamespaces sortnames
  _ <- helpWellFormedRulesInstances sortdefs instTable
  _ <- isWellFormedBindToContext sortdefs instTable
  _ <- helpWellFormedRulesLHSExpressions sortdefs instTable
  return True

wellFormedConstructors :: [ConstructorDef] -> Either String Bool
wellFormedConstructors [] = return True
wellFormedConstructors (c:crest) = do
  _ <- wellFormedConstructor c
  wellFormedConstructors crest

wellFormedConstructor :: ConstructorDef -> Either String Bool
wellFormedConstructor cons = do
  _ <- helpWellFormedIdentifiers (getIdentifiersConstructor cons)
  _ <- helpWellFormedRulesIdentifiers (getAllIds cons) (getIdentifiersConstructor cons)
  _ <- helpWellFormedIdentifierBindingInRightExpr (getRightExprIdsConstructorBinding cons) (getBinding cons)
  _ <- helpWellFormedIdentifierInLeftExpr (getLeftExprIdsConstructor cons) (getIdentifiersWithoutBinding cons)
  _ <- helpWellFormedIdentifierInRightExpr (getRightExprIdsConstructor cons) (getIdentifiersWithoutBinding cons)
  _ <- helpWellFormedIdentifiers (getIdentifiersWithoutBinding cons)
  return True
  where
    --get the Identifiers of the arguments of a constructor (including the binder)
    getIdentifiersConstructor :: ConstructorDef -> [String]
    getIdentifiersConstructor (MkDefConstructor _ lists sorts folds _ _) = map fst lists ++ map fst sorts ++ map (\(x, _, _) -> x) folds
    getIdentifiersConstructor (MkBindConstructor _ lists sorts folds namespace _ _) = map fst lists ++ map fst sorts ++ map (\(x, _, _) -> x) folds ++ [fst namespace]
    getIdentifiersConstructor _ = []

    --get the ids of the RightExpr that bind, including the binder added
    getRightExprIdsConstructorBinding :: ConstructorDef -> [IdenName]
    getRightExprIdsConstructorBinding (MkDefConstructor _ _ _ _ rules _) = concatMap (getRightExprIdBinding . snd) rules
    getRightExprIdsConstructorBinding (MkBindConstructor _ _ _ _ _ rules _) = concatMap (getRightExprIdBinding . snd) rules
    getRightExprIdsConstructorBinding _ = []

    -- get the name on the right expression
    getRightExprIdBinding :: RightExpr -> [IdenName]
    getRightExprIdBinding (RightLHS _)       = []
    getRightExprIdBinding (RightSub _ _)     = []
    getRightExprIdBinding (RightAdd expr iden) = iden : getRightExprIdBinding expr

    -- get all the identifiers without the binder included
    getIdentifiersWithoutBinding :: ConstructorDef -> [String]
    getIdentifiersWithoutBinding (MkDefConstructor _ lists sorts folds _ _) = map fst sorts ++ map fst lists ++ map (\(x, _, _) -> x) folds
    getIdentifiersWithoutBinding (MkBindConstructor _ lists sorts folds _ _ _) = map fst sorts ++ map fst lists ++ map (\(x, _, _) -> x) folds
    getIdentifiersWithoutBinding _ = []

    --get the identifiers used in the rules defined in the constructor
    getAllIds :: ConstructorDef -> [IdenName]
    getAllIds (MkDefConstructor _ _ _ _ rules _) = concatMap getRuleIdentifiers rules
    getAllIds (MkBindConstructor _ _ _ _ _ rules _) = concatMap getRuleIdentifiers rules
    getAllIds _ = []

    --get identifiers of the rule, left expression+the rightexpr
    getRuleIdentifiers :: AttributeDef -> [IdenName]
    getRuleIdentifiers (l, r) = getLeftExprId l ++ getRightExprIdBinding r ++ getRightExprId r

    --get the binding of a constructor
    getBinding :: ConstructorDef -> [IdenName]
    getBinding (MkBindConstructor _ _ _ _ name _ _) = [fst name]
    getBinding _                                    = []

    -- get the ids of the RightExpr without any binders included
    getRightExprIdsConstructor :: ConstructorDef -> [IdenName]
    getRightExprIdsConstructor (MkDefConstructor _ _ _ _ rules _) = concatMap (getRightExprId . snd) rules
    getRightExprIdsConstructor (MkBindConstructor _ _ _ _ _ rules _) = concatMap (getRightExprId . snd) rules
    getRightExprIdsConstructor _ = []

    --get the ids of the LeftExpr
    getLeftExprIdsConstructor :: ConstructorDef -> [IdenName]
    getLeftExprIdsConstructor (MkDefConstructor _ _ _ _ rules _) = concatMap (getLeftExprId . fst) rules
    getLeftExprIdsConstructor (MkBindConstructor _ _ _ _ _ rules _) = concatMap (getLeftExprId . fst) rules
    getLeftExprIdsConstructor _ = []

isEmptySort :: SortDef -> Either String Bool
isEmptySort (MkDefSort name _ [] _) = Left (show name ++ " has no constructor")
isEmptySort _ = return True

-- variables in a sort can only access the inherited namespaces
helpWellFormedVariables :: [ConstructorDef] -> [Context] -> Either String Bool
helpWellFormedVariables [] _ = return True
helpWellFormedVariables (MkVarConstructor _ contextName:rest) instances = do
  _ <- shouldBeInSecondList [contextName] [name | INH name _ <- instances] "Namespace is not an inherited namespace "
  helpWellFormedVariables rest instances
helpWellFormedVariables (_:rest) instances =
  helpWellFormedVariables rest instances

--function to detect if all namespaces used in instances in sorts exist
helpWellFormedInstances :: [NamespaceName] -> [NamespaceName] -> Either String Bool
helpWellFormedInstances l l2 = shouldBeInSecondList l l2 "Instance does not reference an existing namespace"

--all instancenames across sorts should be unique
helpWellFormedInstanceNames :: [InstanceName] -> Either String Bool
helpWellFormedInstanceNames l = isUniqueInList l "Instance is not a unique name in the declaration "

--variables should only refer to namespace they are part of
helpWellFormedVariablesNamespace :: [SortDef] -> [NamespaceDef] -> Either String Bool
helpWellFormedVariablesNamespace [] _ = return True
helpWellFormedVariablesNamespace (MkDefSort sortName ctxs cons _:rest) namespaces = do
  _ <- helpWellFormedVariablesCons sortName cons ctxs namespaces
  helpWellFormedVariablesNamespace rest namespaces

helpWellFormedVariablesCons :: SortName -> [ConstructorDef] -> [Context] -> [NamespaceDef] -> Either String Bool
helpWellFormedVariablesCons _ [] _ _ = Right True
helpWellFormedVariablesCons sortName (MkVarConstructor _ instanceName:rest) ctxs namespaces = do
  _ <- helpWellFormedVarInst sortName instanceName ctxs namespaces
  helpWellFormedVariablesCons sortName rest ctxs namespaces
helpWellFormedVariablesCons sortName (_:rest) ctxs namespace =
  helpWellFormedVariablesCons sortName rest ctxs namespace

helpWellFormedVarInst :: SortName -> InstanceName -> [Context] -> [NamespaceDef] -> Either String Bool
helpWellFormedVarInst _ name [] _ =
  Left ("No instance found with that name in " ++ name)
helpWellFormedVarInst sortName name (ctx:rest) namespaces =
  if xinst ctx == name
    then helpVarnamespace sortName (xnamespace ctx) namespaces
    else helpWellFormedVarInst sortName name rest namespaces

helpVarnamespace :: SortName -> String -> [NamespaceDef] -> Either String Bool
helpVarnamespace _ _ [] =
  Left "Instance and namespace in variable do not coincide"
helpVarnamespace sortName name (MkNameSpace namespacename sortname _:rest) =
  if namespacename == name
    then (if sortName == sortname
            then return True
            else Left ("sort cannot use this namespace in " ++ sortName))
    else helpVarnamespace sortName name rest

--function to detect if all identifiers used in the rules exist as fields
helpWellFormedRulesIdentifiers :: [IdenName] -> [IdenName] -> Either String Bool
helpWellFormedRulesIdentifiers l l2 = shouldBeInSecondList l l2 "identifier not used in constructor"

--function to detect if all identifiers are unique in the fields of a constructor
helpWellFormedIdentifiers :: [IdenName] -> Either String Bool
helpWellFormedIdentifiers l = isUniqueInList l "not unique identifier"

--function to detect if all sortnames are unique
helpWellFormedSortName :: [SortName] -> Either String Bool
helpWellFormedSortName l = isUniqueInList l "not unique sortname"

--function to detect if all constructors are unique
helpWellFormedConstructorName :: [ConstructorName] -> Either String Bool
helpWellFormedConstructorName l = isUniqueInList l "not unique constructor"

--function to detect if all NameSpaceNames are unique
helpWellFormedNameSpaceName :: [NamespaceName] -> Either String Bool
helpWellFormedNameSpaceName l = isUniqueInList l "not unique namespace"

--function to detect if all ConstructorName and Sortnames are unique
helpWellFormedConstructorAndSort :: [ConstructorName] -> [SortName] -> Either String Bool
helpWellFormedConstructorAndSort l l2 = shouldNotBeInSecondList l l2 "constructor and sort have same name"

--function to detect if all NameSpaceNames and Sortnames are unique
helpWellFormedNameSpaceAndSort :: [NamespaceName] -> [SortName] -> Either String Bool
helpWellFormedNameSpaceAndSort l l2 = shouldNotBeInSecondList l l2 "namespace and sort have same name"

--function to detect if all constructornames and namespacenames are unique
helpWellFormedNameSpaceAndConstructor :: [NamespaceName] -> [ConstructorName] -> Either String Bool
helpWellFormedNameSpaceAndConstructor l l2 = shouldNotBeInSecondList l l2 "constructor and namespace have same name"

--function to detect if all sortnames in constructors are valid
helpWellFormedSortNameInConstructors :: [SortName] -> [SortName] -> Either String Bool
helpWellFormedSortNameInConstructors l l2 = shouldBeInSecondList l l2 "sortname in constructor does not appear"

--function to detect if all sortnames in constructors are valid
helpWellFormedSortNameInNamespaces :: [SortName] -> [SortName] -> Either String Bool
helpWellFormedSortNameInNamespaces l l2 = shouldBeInSecondList l l2 "sortname in namespace does not appear"

--function to detect if all namespacenames in constructors are valid (or in other words: are declared )
helpWellFormedNameSpaceNameInConstructors :: [NamespaceName] -> [NamespaceName] -> Either String Bool
helpWellFormedNameSpaceNameInConstructors l l2 =
  shouldBeInSecondList l l2 "Namespace in constructor is not a declared namespace"

--detects if an identifier in the right expression does not appear as a binder
helpWellFormedIdentifierBindingInRightExpr :: [IdenName] -> [IdenName] -> Either String Bool
helpWellFormedIdentifierBindingInRightExpr l l2 =
  shouldBeInSecondList l l2 "Identifier in right expression does not appear as binder"

--detects if an identifier in the right expression does not appear as constructorfield
helpWellFormedIdentifierInLeftExpr :: [IdenName] -> [IdenName] -> Either String Bool
helpWellFormedIdentifierInLeftExpr l l2 =
  shouldBeInSecondList l l2 "Identifier in left expression does not appear as constructorfield"

--detects if an identifier in the right expression does not appear as constructorfield
helpWellFormedIdentifierInRightExpr :: [IdenName] -> [IdenName] -> Either String Bool
helpWellFormedIdentifierInRightExpr l l2 =
  shouldBeInSecondList l l2 "Identifier in right expression does not appear as constructorfield"

--LeftExpressions that are LeftLHS should be SYN contexts
helpWellFormedRulesLHSExpressions :: [SortDef] -> [(SortName, [Context])] -> Either String Bool
helpWellFormedRulesLHSExpressions sdefs table
  | not (null errors) = head errors
  | otherwise = return True
  where
    errors =
      [ Left x
      | Left x <- concatMap (helpWellFormedRulesLHSExpressionsSort table) sdefs
      ]

--checks if the left hand side is a synthesised namespace if an identifier appears on the left hand side of a rule expression
helpWellFormedRulesLHSExpressionsSort :: [(SortName, [Context])] -> SortDef -> [Either String Bool]
helpWellFormedRulesLHSExpressionsSort table s =
  concatMap (helpWellFormedRulesLHSExpressionsConstructor (sname s) table) (sctors s)

helpWellFormedRulesLHSExpressionsConstructor :: SortName -> [(SortName, [Context])] -> ConstructorDef -> [Either String Bool]
helpWellFormedRulesLHSExpressionsConstructor sortName table (MkDefConstructor _ _ sortids _ rules _) =
  map (helpWellFormedRulesInstancesRuleLHSLeft sortName sortids table) rules
helpWellFormedRulesLHSExpressionsConstructor sortName table (MkBindConstructor _ _ sortids _ (_, _) rules _) =
  map (helpWellFormedRulesInstancesRuleLHSLeft sortName sortids table) rules
helpWellFormedRulesLHSExpressionsConstructor _ _ _ = [Right True]

--checks if the left hand side and right hand side are wellformed in the sense that inherited contexts and synthesised contexts cannot be used in every position
helpWellFormedRulesInstancesRuleLHSLeft :: SortName -> [(IdenName, SortName)] -> [(SortName, [Context])] -> AttributeDef -> Either String Bool
helpWellFormedRulesInstancesRuleLHSLeft sortName _ tableInstances (LeftLHS contextName, RightLHS contextName2)
  | not (null (findContextToNamespaceInstanceSyn contextName sortName tableInstances)) && not (null (findContextToNamespaceInstanceInh contextName2 sortName tableInstances)) = return True
  | otherwise = Left (contextName ++ contextName2 ++ "not a good combination of synthesised and inherited namespaces")
helpWellFormedRulesInstancesRuleLHSLeft sortName tableIdentifiers tableInstances (LeftLHS contextName, RightSub fieldname2 contextName2)
  | isNothing (lookup fieldname2 tableIdentifiers) = return True
  | not (null (findContextToNamespaceInstanceSyn contextName sortName tableInstances)) && not (null (findContextToNamespaceInstanceSyn contextName2 (fromJust (lookup fieldname2 tableIdentifiers)) tableInstances)) = return True
  | otherwise = Left (contextName ++ "is not a synthesised namespace")
helpWellFormedRulesInstancesRuleLHSLeft sortName tableIdentifiers tableInstances (leftexpr, RightAdd expr _) =
  helpWellFormedRulesInstancesRuleLHSLeft sortName tableIdentifiers tableInstances (leftexpr, expr)
helpWellFormedRulesInstancesRuleLHSLeft _ tableIdentifiers tableInstances (LeftSub fieldname contextName, RightSub fieldname2 contextName2)
  | isNothing sname2 || isNothing sname1 = return True
  | fieldname == fieldname2 = Left (fieldname ++ "appears on both sides of a rule, which would cause infinite recursion")
  | not (null (findContextToNamespaceInstanceInh contextName (fromJust sname1) tableInstances)) && not (null (findContextToNamespaceInstanceSyn contextName2 (fromJust sname2) tableInstances)) = return True
  | otherwise = Left (contextName ++ "is not a synthesised namespace")
  where
    sname2 = lookup fieldname2 tableIdentifiers
    sname1 = lookup fieldname tableIdentifiers
helpWellFormedRulesInstancesRuleLHSLeft sortName tableIdentifiers tableInstances (LeftSub fieldname contextName, RightLHS contextName2)
  | isNothing (lookup fieldname tableIdentifiers) = return True
  | not (null (findContextToNamespaceInstanceInh contextName (fromJust (lookup fieldname tableIdentifiers)) tableInstances)) && not (null (findContextToNamespaceInstanceInh contextName2 sortName tableInstances)) = return True
  | otherwise = Left (contextName ++ "is not a synthesised namespace")

-- filters all the synthesised namespaces
findContextToNamespaceInstanceSyn :: InstanceName -> SortName -> [(SortName, [Context])] -> [Context]
findContextToNamespaceInstanceSyn instName sortName table =
  filter
    (\ctx -> xinst ctx == instName)
    [ SYN ctxNamesyn namespacename
    | SYN ctxNamesyn namespacename <- fromJust (lookup sortName table)
    ]

-- filters all the inherited namespaces
findContextToNamespaceInstanceInh :: InstanceName -> SortName -> [(SortName, [Context])] -> [Context]
findContextToNamespaceInstanceInh instName sortName table =
  filter
    (\ctx -> xinst ctx == instName)
    [ INH ctxNameinh namespacename
    | INH ctxNameinh namespacename <- fromJust (lookup sortName table)
    ]

  -- checking if the binding to a constructorrule is ok by looking if the right expression is of the right type
isWellFormedBindToContextConstructorRule :: SortName -> NamespaceName -> [(IdenName, SortName)] -> [(SortName, [Context])] -> AttributeDef -> Either String Bool
isWellFormedBindToContextConstructorRule sortName namespacebind tableIdentifiers tableInstances (_, RightAdd expr _)
 | null (getRightExprId expr) && any (\ctx -> getInstanceNamesOfRuleRight expr == xinst ctx && xnamespace ctx == namespacebind) (fromJust (lookup sortName tableInstances)) = return True
 | not (null (getRightExprId expr)) && any (\ctx -> getInstanceNamesOfRuleRight expr == xinst ctx && xnamespace ctx == namespacebind) (fromJust (lookup (fromJust (lookup (head (getRightExprId expr)) tableIdentifiers)) tableInstances)) = return True
 | otherwise = Left "incorrect binding"
isWellFormedBindToContextConstructorRule _ _ _ _ _ = return True
 -- checking if the binding to a constructor is ok by looking if the right expression is of the right type for all the rules of its constructor (only checks bindingConstructors)

isWellFormedBindToContextConstructor :: SortName -> [(SortName, [Context])] -> ConstructorDef -> [Either String Bool]
isWellFormedBindToContextConstructor sortName table (MkBindConstructor _ _ sortids _ (_, namespacename) rules _) =
 map (isWellFormedBindToContextConstructorRule sortName namespacename sortids table) rules
isWellFormedBindToContextConstructor _ _ _ = [return True]

--helper for the binding check when
isWellFormedBindToContextSort :: [(SortName, [Context])] -> SortDef -> [Either String Bool]
isWellFormedBindToContextSort table s =
 concatMap (isWellFormedBindToContextConstructor (sname s) table) (sctors s)

--binders should only be added to contexts that correspond to the same namespace (not necessarily the same context)
isWellFormedBindToContext :: [SortDef] -> [(SortName, [Context])] -> Either String Bool
isWellFormedBindToContext sdefs table
 | not (null errors) = head errors
 | otherwise = return True
 where
   errors = [Left x | Left x <- concatMap (isWellFormedBindToContextSort table) sdefs]

--checks whether both the lefthandside and the right hand side abide by the check of whether they refer to the same namespace
helpWellFormedRulesInstancesRule :: SortName -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName, FoldName)] -> [(SortName, [Context])] -> AttributeDef -> Either String Bool
helpWellFormedRulesInstancesRule sortName lists tableIdentifiers folds tableInstances (leftexpr, rightexpr)
 | not (null (getRightExprId rightexpr)) && elem (head (getRightExprId rightexpr)) (map fst lists ++ map (\(x, _, _) -> x) folds) = return True
 | not (null (getLeftExprId leftexpr)) && elem (head (getLeftExprId leftexpr)) (map fst lists ++ map (\(a, _, _) -> a) folds) = return True
 | null (getRightExprId rightexpr) && not (null rightInstanceLHS) && null (getLeftExprId leftexpr) && not (null leftInstanceLHS) && xnamespace (head rightInstanceLHS) == xnamespace (head leftInstanceLHS) = return True
 | not (null (getRightExprId rightexpr)) && not (null rightInstanceNoLHS) && null (getLeftExprId leftexpr) && not (null leftInstanceLHS) && xnamespace (head rightInstanceNoLHS) == xnamespace (head leftInstanceLHS) = return True
 | not (null (getRightExprId rightexpr)) && not (null rightInstanceNoLHS) && not (null (getLeftExprId leftexpr)) && not (null leftInstanceNoLHS) && xnamespace (head rightInstanceNoLHS) == xnamespace (head leftInstanceNoLHS) = return True
 | null (getRightExprId rightexpr) && not (null rightInstanceLHS) && not (null (getLeftExprId leftexpr)) && not (null leftInstanceNoLHS) && xnamespace (head rightInstanceLHS) == xnamespace (head leftInstanceNoLHS) = return True
 | otherwise = Left ("incorrect context for this sort " ++ sortName)
 where
   rightInstanceLHS = filter (\ctx -> getInstanceNamesOfRuleRight rightexpr == xinst ctx) (fromJust (lookup sortName tableInstances))
   rightInstanceNoLHS = filter (\ctx -> getInstanceNamesOfRuleRight rightexpr == xinst ctx) (fromJust (lookup (fromJust (lookup (head (getRightExprId rightexpr)) tableIdentifiers)) tableInstances))
   leftInstanceLHS = filter (\ctx -> linst leftexpr == xinst ctx) (fromJust (lookup sortName tableInstances))
   leftInstanceNoLHS = filter (\ctx -> linst leftexpr == xinst ctx) (fromJust (lookup (fromJust (lookup (head (getLeftExprId leftexpr)) tableIdentifiers)) tableInstances))

--checks if all the rules are welldefined for the normal constructors and the binding constructors
helpWellFormedRulesInstancesConstructor :: SortName -> [(SortName, [Context])] -> ConstructorDef -> [Either String Bool]
helpWellFormedRulesInstancesConstructor sortName table (MkDefConstructor _ listids sortids folds rules _) =
 map (helpWellFormedRulesInstancesRule sortName listids sortids folds table) rules
helpWellFormedRulesInstancesConstructor sortName table (MkBindConstructor _ listids sortids folds (_, _) rules _) =
 map (helpWellFormedRulesInstancesRule sortName listids sortids folds table) rules
helpWellFormedRulesInstancesConstructor _ _ _ = [return True]

--checks if all the constructors have welltyped rules
helpWellFormedRulesInstancesSort :: [(SortName, [Context])] -> SortDef -> [Either String Bool]
helpWellFormedRulesInstancesSort table s =
 concatMap (helpWellFormedRulesInstancesConstructor (sname s) table) (sctors s)

-- identifiers in Rules can only use contexts they are allowed to use
helpWellFormedRulesInstances :: [SortDef] -> [(SortName, [Context])] -> Either String Bool
helpWellFormedRulesInstances sdefs table
 | not (null errors) = head errors
 | otherwise = return True
 where
   errors =
     [ Left x
     | Left x <- concatMap (helpWellFormedRulesInstancesSort table) sdefs
     ]

-- get the name on the left expression
getLeftExprId :: LeftExpr -> [IdenName]
getLeftExprId (LeftLHS _)    = []
getLeftExprId (LeftSub iden _) = [iden]

--gets the idName of the rightexpr
getRightExprId :: RightExpr -> [IdenName]
getRightExprId (RightLHS _)      = []
getRightExprId (RightSub name _) = [name]
getRightExprId (RightAdd expr _) = getRightExprId expr

--get the name of the context of a right expr
getInstanceNamesOfRuleRight :: RightExpr -> InstanceName
getInstanceNamesOfRuleRight (RightAdd expr _) = getInstanceNamesOfRuleRight expr
getInstanceNamesOfRuleRight (RightLHS name) = name
getInstanceNamesOfRuleRight (RightSub _ name) = name

--function to detect if all names are unique
isUniqueInList :: [String] -> String -> Either String Bool
isUniqueInList [] _ = return True
isUniqueInList (str:strs) err =
  if str `elem` strs
    then Left (show str ++ err)
    else isUniqueInList strs err

--helper to detect if different lists have unique names
shouldNotBeInSecondList :: [String] -> [String] -> String -> Either String Bool
shouldNotBeInSecondList [] _ _ = return True
shouldNotBeInSecondList (str:crest) sorts err =
  if str `elem` sorts
    then Left (show str ++ err)
    else shouldNotBeInSecondList crest sorts err

--helper to detect if names in the first list  exist in the available second list
shouldBeInSecondList :: [String] -> [String] -> String -> Either String Bool
shouldBeInSecondList [] _ _ = return True
shouldBeInSecondList (str:strs) sorts err =
  if str `elem` sorts
    then shouldBeInSecondList strs sorts err
    else Left (show str ++ err)
