{-# OPTIONS_GHC -Wall #-}

module WellFormed (wellFormed) where

import GeneralTerms
import Utility
import Data.Maybe
import Data.List

--when is this syntax wellFormed : 1. when there are no duplicate constructors in the language i.e. there are no duplicate names among constructors or sorts and every sort has at the least one constructor
wellFormed :: Language -> Either String ()
wellFormed ([], [], _, _) = Left "Empty Language"
wellFormed (namespaces, sorts, _, _) = do
  mapM_ checkVarCtors sorts
  helpWellFormed sorts [] [] [] (map nname namespaces) (map nsort namespaces) [] []
  where
    checkVarCtors :: SortDef -> Either String ()
    checkVarCtors (MkDefSort name ctxs ctors _) = mapM_ (
        \ctor -> checkInst name (cinst ctor) ctxs
      ) [MkVarConstructor n i | MkVarConstructor n i <- ctors]

    checkInst :: SortName -> InstanceName -> [Context] -> Either String ()
    checkInst sortName name ctxs
      = let match = find (\ctx -> xinst ctx == name) ctxs
        in case match of
          Nothing  -> Left ("No instance found with that name in " ++ name)
          Just ctx -> checkNsSort sortName (xnamespace ctx) namespaces

    checkNsSort :: SortName -> NamespaceName -> [NamespaceDef] -> Either String ()
    checkNsSort sortName namespaceName nsd
      = let match = find (\ns -> nname ns == namespaceName) nsd
        in case match of
          Nothing -> Left "Instance and namespace in variable do not coincide"
          Just ns -> if nsort ns == sortName
                       then return ()
                       else Left ("sort cannot use this namespace in " ++ sortName)

--accumulates the sortnames, constructornames, and the sortnames contained in the constructors,
--then looks up if all sortnames,namespacenames and contructornames are unique, if all sorts in the constructors exist,
--and whether sorts and constructors and namespaces have distinct names. Also namespacenames used in sorts should exist and constructors can only use variablebindings of namespaces they can access in the sort
helpWellFormed :: [SortDef] -> [SortName] -> [ConstructorName] -> [SortName] -> [NamespaceName] -> [SortName] -> [(SortName, [Context])] -> [SortDef] -> Either String ()
helpWellFormed (s:lanrest) sortnames consnames sortconsnames namespacenames sortnamespaces instTable sortdefs = do
  notEmpty s
  checkBinderNamespaces [snd (fromJust (cbinder ctor)) | ctor <- sctors s, isBind ctor] namespacenames
  wellFormedConstructors (sctors s)
  helpWellFormedInstances (getInstanceSortsNameSpaceNames s) namespacenames
  helpWellFormedVariables (sctors s) (sctxs s)
  helpWellFormedInstanceNames (map xinst (sctxs s))
  helpWellFormed lanrest (sname s : sortnames) (getConstructorNames s ++ consnames) (getSortsUsedByConstructors ++ sortconsnames) namespacenames sortnamespaces (snameAndCtxs s : instTable) (s : sortdefs)
    where
      notEmpty :: SortDef -> Either String ()
      notEmpty (MkDefSort name _ [] _) = Left (show name ++ " has no constructor")
      notEmpty _ = return ()

      --function to detect if all namespacenames in constructors are valid (or in other words: are declared )
      checkBinderNamespaces :: [NamespaceName] -> [NamespaceName] -> Either String ()
      checkBinderNamespaces l l2 = shouldBeInSecondList l l2 "Namespace in constructor is not a declared namespace"

      wellFormedConstructors :: [ConstructorDef] -> Either String ()
      wellFormedConstructors ctors = mapM_ wellFormedConstructor ctors
        where
          wellFormedConstructor :: ConstructorDef -> Either String ()
          wellFormedConstructor cons = do
            helpWellFormedIdentifiers (getIdentifiersConstructor cons)
            helpWellFormedRulesIdentifiers (getAllIds cons) (getIdentifiersConstructor cons)
            helpWellFormedIdentifierBindingInRightExpr (getRightExprIdsConstructorBinding cons) (getBinding cons)
            helpWellFormedIdentifierInLeftExpr (getLeftExprIdsConstructor cons) (getIdentifiersWithoutBinding cons)
            helpWellFormedIdentifierInRightExpr (getRightExprIdsConstructor cons) (getIdentifiersWithoutBinding cons)
            helpWellFormedIdentifiers (getIdentifiersWithoutBinding cons)
            where
              --function to detect if all identifiers are unique in the fields of a constructor
              helpWellFormedIdentifiers :: [IdenName] -> Either String ()
              helpWellFormedIdentifiers l = isUniqueInList l "not unique identifier"

              --function to detect if all identifiers used in the rules exist as fields
              helpWellFormedRulesIdentifiers :: [IdenName] -> [IdenName] -> Either String ()
              helpWellFormedRulesIdentifiers l l2 = shouldBeInSecondList l l2 "identifier not used in constructor"

              --detects if an identifier in the right expression does not appear as a binder
              helpWellFormedIdentifierBindingInRightExpr :: [IdenName] -> [IdenName] -> Either String ()
              helpWellFormedIdentifierBindingInRightExpr l l2 = shouldBeInSecondList l l2 "Identifier in right expression does not appear as binder"

              --detects if an identifier in the right expression does not appear as constructorfield
              helpWellFormedIdentifierInLeftExpr :: [IdenName] -> [IdenName] -> Either String ()
              helpWellFormedIdentifierInLeftExpr l l2 = shouldBeInSecondList l l2 "Identifier in left expression does not appear as constructorfield"

              --detects if an identifier in the right expression does not appear as constructorfield
              helpWellFormedIdentifierInRightExpr :: [IdenName] -> [IdenName] -> Either String ()
              helpWellFormedIdentifierInRightExpr l l2 = shouldBeInSecondList l l2 "Identifier in right expression does not appear as constructorfield"

              --get the Identifiers of the arguments of a constructor (including the binder)
              getIdentifiersConstructor :: ConstructorDef -> [String]
              getIdentifiersConstructor (MkVarConstructor _ _) = []
              getIdentifiersConstructor ctor = map fst (clists ctor) ++ map fst (csorts ctor) ++ map (\(x, _, _) -> x) (cfolds ctor) ++ maybe [] (\b -> [fst b]) (cbinder ctor)

              --get the ids of the RightExpr that bind, including the binder added
              getRightExprIdsConstructorBinding :: ConstructorDef -> [IdenName]
              getRightExprIdsConstructorBinding (MkVarConstructor _ _) = []
              getRightExprIdsConstructorBinding ctor = concatMap (getRightExprIdBinding . snd) (cattrs ctor)

              -- get the name on the right expression
              getRightExprIdBinding :: RightExpr -> [IdenName]
              getRightExprIdBinding (RightLHS _)       = []
              getRightExprIdBinding (RightSub _ _)     = []
              getRightExprIdBinding (RightAdd expr iden) = iden : getRightExprIdBinding expr

              -- get all the identifiers without the binder included
              getIdentifiersWithoutBinding :: ConstructorDef -> [String]
              getIdentifiersWithoutBinding (MkVarConstructor _ _) = []
              getIdentifiersWithoutBinding ctor = map fst (csorts ctor) ++ map fst (clists ctor) ++ map (\(x, _, _) -> x) (cfolds ctor)

              --get the identifiers used in the rules defined in the constructor
              getAllIds :: ConstructorDef -> [IdenName]
              getAllIds (MkVarConstructor _ _) = []
              getAllIds ctor = concatMap getRuleIdentifiers (cattrs ctor)

              --get identifiers of the rule, left expression+the rightexpr
              getRuleIdentifiers :: AttributeDef -> [IdenName]
              getRuleIdentifiers (l, r) = getLeftExprId l ++ getRightExprIdBinding r ++ getRightExprId r

              --get the binding of a constructor
              getBinding :: ConstructorDef -> [IdenName]
              getBinding (MkBindConstructor _ _ _ _ name _ _) = [fst name]
              getBinding _                                    = []

              -- get the ids of the RightExpr without any binders included
              getRightExprIdsConstructor :: ConstructorDef -> [IdenName]
              getRightExprIdsConstructor (MkVarConstructor _ _) = []
              getRightExprIdsConstructor ctor = concatMap (getRightExprId . snd) (cattrs ctor)

              --get the ids of the LeftExpr
              getLeftExprIdsConstructor :: ConstructorDef -> [IdenName]
              getLeftExprIdsConstructor (MkVarConstructor _ _) = []
              getLeftExprIdsConstructor ctor = concatMap (getLeftExprId . fst) (cattrs ctor)

      --function to detect if all namespaces used in instances in sorts exist
      helpWellFormedInstances :: [NamespaceName] -> [NamespaceName] -> Either String ()
      helpWellFormedInstances l l2 = shouldBeInSecondList l l2 "Instance does not reference an existing namespace"

      -- variables in a sort can only access the inherited namespaces
      helpWellFormedVariables :: [ConstructorDef] -> [Context] -> Either String ()
      helpWellFormedVariables [] _ = return ()
      helpWellFormedVariables (MkVarConstructor _ contextName:rest) instances = do
        _ <- shouldBeInSecondList [contextName] [name | INH name _ <- instances] "Namespace is not an inherited namespace "
        helpWellFormedVariables rest instances
      helpWellFormedVariables (_:rest) instances =
        helpWellFormedVariables rest instances

      --all instancenames across sorts should be unique
      helpWellFormedInstanceNames :: [InstanceName] -> Either String ()
      helpWellFormedInstanceNames l = isUniqueInList l "Instance is not a unique name in the declaration "

      --get the instances used by sorts
      getInstanceSortsNameSpaceNames :: SortDef -> [NamespaceName]
      getInstanceSortsNameSpaceNames (MkDefSort _ ctxs _ _) = map xnamespace ctxs

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
            getSortsConstructor (MkVarConstructor _ _) = []
            getSortsConstructor ctor =  map snd (csorts ctor) ++ map snd (clists ctor) ++ map (\(_, y, _) -> y) (cfolds ctor)
helpWellFormed [] sortnames consnames sortconsnames namespacenames sortnamespaces instTable sortdefs = do
  helpWellFormedSortName sortnames
  helpWellFormedConstructorName consnames
  helpWellFormedNameSpaceName namespacenames
  helpWellFormedConstructorAndSort consnames sortnames
  helpWellFormedNameSpaceAndSort namespacenames sortnames
  helpWellFormedNameSpaceAndConstructor namespacenames consnames
  helpWellFormedSortNameInConstructors sortconsnames sortnames
  helpWellFormedSortNameInNamespaces sortnamespaces sortnames
  helpWellFormedRulesInstances sortdefs instTable
  isWellFormedBindToContext sortdefs instTable
  helpWellFormedRulesLHSExpressions sortdefs instTable
  where
    --function to detect if all sortnames are unique
    helpWellFormedSortName :: [SortName] -> Either String ()
    helpWellFormedSortName l = isUniqueInList l "not unique sortname"

    --function to detect if all constructors are unique
    helpWellFormedConstructorName :: [ConstructorName] -> Either String ()
    helpWellFormedConstructorName l = isUniqueInList l "not unique constructor"

    --function to detect if all NameSpaceNames are unique
    helpWellFormedNameSpaceName :: [NamespaceName] -> Either String ()
    helpWellFormedNameSpaceName l = isUniqueInList l "not unique namespace"

    --function to detect if all ConstructorName and Sortnames are unique
    helpWellFormedConstructorAndSort :: [ConstructorName] -> [SortName] -> Either String ()
    helpWellFormedConstructorAndSort l l2 = shouldNotBeInSecondList l l2 "constructor and sort have same name"

    --function to detect if all NameSpaceNames and Sortnames are unique
    helpWellFormedNameSpaceAndSort :: [NamespaceName] -> [SortName] -> Either String ()
    helpWellFormedNameSpaceAndSort l l2 = shouldNotBeInSecondList l l2 "namespace and sort have same name"

    --function to detect if all constructornames and namespacenames are unique
    helpWellFormedNameSpaceAndConstructor :: [NamespaceName] -> [ConstructorName] -> Either String ()
    helpWellFormedNameSpaceAndConstructor l l2 = shouldNotBeInSecondList l l2 "constructor and namespace have same name"

    --function to detect if all sortnames in constructors are valid
    helpWellFormedSortNameInConstructors :: [SortName] -> [SortName] -> Either String ()
    helpWellFormedSortNameInConstructors l l2 = shouldBeInSecondList l l2 "sortname in constructor does not appear"

    --function to detect if all sortnames in constructors are valid
    helpWellFormedSortNameInNamespaces :: [SortName] -> [SortName] -> Either String ()
    helpWellFormedSortNameInNamespaces l l2 = shouldBeInSecondList l l2 "sortname in namespace does not appear"

    -- identifiers in Rules can only use contexts they are allowed to use
    helpWellFormedRulesInstances :: [SortDef] -> [(SortName, [Context])] -> Either String ()
    helpWellFormedRulesInstances sdefs table
      | not (null errors) = head errors
      | otherwise = return ()
      where
        errors = [Left x | Left x <- concatMap (helpWellFormedRulesInstancesSort table) sdefs]

        --checks if all the constructors have welltyped rules
        helpWellFormedRulesInstancesSort :: [(SortName, [Context])] -> SortDef -> [Either String ()]
        helpWellFormedRulesInstancesSort table s = concatMap (helpWellFormedRulesInstancesConstructor (sname s) table) (sctors s)

        --checks if all the rules are welldefined for the normal constructors and the binding constructors
        helpWellFormedRulesInstancesConstructor :: SortName -> [(SortName, [Context])] -> ConstructorDef -> [Either String ()]
        helpWellFormedRulesInstancesConstructor _ _ (MkVarConstructor _ _) = [return ()]
        helpWellFormedRulesInstancesConstructor sortName table ctor =
          map (helpWellFormedRulesInstancesRule sortName (clists ctor) (csorts ctor) (cfolds ctor) table) (cattrs ctor)

        --checks whether both the lefthandside and the right hand side abide by the check of whether they refer to the same namespace
        helpWellFormedRulesInstancesRule :: SortName -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName, FoldName)] -> [(SortName, [Context])] -> AttributeDef -> Either String ()
        helpWellFormedRulesInstancesRule sortName lists tableIdentifiers folds tableInstances (leftexpr, rightexpr)
          | not (null (getRightExprId rightexpr)) && elem (head (getRightExprId rightexpr)) (map fst lists ++ map (\(x, _, _) -> x) folds) = return ()
          | not (null (getLeftExprId leftexpr)) && elem (head (getLeftExprId leftexpr)) (map fst lists ++ map (\(a, _, _) -> a) folds) = return ()
          | null (getRightExprId rightexpr) && not (null rightInstanceLHS) && null (getLeftExprId leftexpr) && not (null leftInstanceLHS) && xnamespace (head rightInstanceLHS) == xnamespace (head leftInstanceLHS) = return ()
          | not (null (getRightExprId rightexpr)) && not (null rightInstanceNoLHS) && null (getLeftExprId leftexpr) && not (null leftInstanceLHS) && xnamespace (head rightInstanceNoLHS) == xnamespace (head leftInstanceLHS) = return ()
          | not (null (getRightExprId rightexpr)) && not (null rightInstanceNoLHS) && not (null (getLeftExprId leftexpr)) && not (null leftInstanceNoLHS) && xnamespace (head rightInstanceNoLHS) == xnamespace (head leftInstanceNoLHS) = return ()
          | null (getRightExprId rightexpr) && not (null rightInstanceLHS) && not (null (getLeftExprId leftexpr)) && not (null leftInstanceNoLHS) && xnamespace (head rightInstanceLHS) == xnamespace (head leftInstanceNoLHS) = return ()
          | otherwise = Left ("incorrect context for this sort " ++ sortName)
          where
            rightInstanceLHS = filter (\ctx -> getInstanceNamesOfRuleRight rightexpr == xinst ctx) (fromJust (lookup sortName tableInstances))
            rightInstanceNoLHS = filter (\ctx -> getInstanceNamesOfRuleRight rightexpr == xinst ctx) (fromJust (lookup (fromJust (lookup (head (getRightExprId rightexpr)) tableIdentifiers)) tableInstances))
            leftInstanceLHS = filter (\ctx -> linst leftexpr == xinst ctx) (fromJust (lookup sortName tableInstances))
            leftInstanceNoLHS = filter (\ctx -> linst leftexpr == xinst ctx) (fromJust (lookup (fromJust (lookup (head (getLeftExprId leftexpr)) tableIdentifiers)) tableInstances))

    --binders should only be added to contexts that correspond to the same namespace (not necessarily the same context)
    isWellFormedBindToContext :: [SortDef] -> [(SortName, [Context])] -> Either String ()
    isWellFormedBindToContext sdefs table
      | not (null errors) = head errors
      | otherwise = return ()
      where
        errors = [Left x | Left x <- concatMap (isWellFormedBindToContextSort table) sdefs]

        --helper for the binding check when
        isWellFormedBindToContextSort :: [(SortName, [Context])] -> SortDef -> [Either String ()]
        isWellFormedBindToContextSort table s =
          concatMap (isWellFormedBindToContextConstructor (sname s) table) (sctors s)

         -- checking if the binding to a constructor is ok by looking if the right expression is of the right type for all the rules of its constructor (only checks bindingConstructors)
        isWellFormedBindToContextConstructor :: SortName -> [(SortName, [Context])] -> ConstructorDef -> [Either String ()]
        isWellFormedBindToContextConstructor sortName table (MkBindConstructor _ _ sortids _ (_, namespacename) rules _) =
          map (isWellFormedBindToContextConstructorRule sortName namespacename sortids table) rules
        isWellFormedBindToContextConstructor _ _ _ = [return ()]

        -- checking if the binding to a constructorrule is ok by looking if the right expression is of the right type
        isWellFormedBindToContextConstructorRule :: SortName -> NamespaceName -> [(IdenName, SortName)] -> [(SortName, [Context])] -> AttributeDef -> Either String ()
        isWellFormedBindToContextConstructorRule sortName namespacebind tableIdentifiers tableInstances (_, RightAdd expr _)
          | null (getRightExprId expr) && any (\ctx -> getInstanceNamesOfRuleRight expr == xinst ctx && xnamespace ctx == namespacebind) (fromJust (lookup sortName tableInstances)) = return ()
          | not (null (getRightExprId expr)) && any (\ctx -> getInstanceNamesOfRuleRight expr == xinst ctx && xnamespace ctx == namespacebind) (fromJust (lookup (fromJust (lookup (head (getRightExprId expr)) tableIdentifiers)) tableInstances)) = return ()
          | otherwise = Left "incorrect binding"
        isWellFormedBindToContextConstructorRule _ _ _ _ _ = return ()

    --LeftExpressions that are LeftLHS should be SYN contexts
    helpWellFormedRulesLHSExpressions :: [SortDef] -> [(SortName, [Context])] -> Either String ()
    helpWellFormedRulesLHSExpressions sdefs table
      | not (null errors) = head errors
      | otherwise = return ()
      where
        errors = [Left x | Left x <- concatMap (helpWellFormedRulesLHSExpressionsSort table) sdefs]

        --checks if the left hand side is a synthesised namespace if an identifier appears on the left hand side of a rule expression
        helpWellFormedRulesLHSExpressionsSort :: [(SortName, [Context])] -> SortDef -> [Either String ()]
        helpWellFormedRulesLHSExpressionsSort table s =
          concatMap (helpWellFormedRulesLHSExpressionsConstructor (sname s) table) (sctors s)

        helpWellFormedRulesLHSExpressionsConstructor :: SortName -> [(SortName, [Context])] -> ConstructorDef -> [Either String ()]
        helpWellFormedRulesLHSExpressionsConstructor _ _ (MkVarConstructor _ _) = [Right ()]
        helpWellFormedRulesLHSExpressionsConstructor sortName table ctor =
          map (helpWellFormedRulesInstancesRuleLHSLeft sortName (csorts ctor) table) (cattrs ctor)

        --checks if the left hand side and right hand side are wellformed in the sense that inherited contexts and synthesised contexts cannot be used in every position
        helpWellFormedRulesInstancesRuleLHSLeft :: SortName -> [(IdenName, SortName)] -> [(SortName, [Context])] -> AttributeDef -> Either String ()
        helpWellFormedRulesInstancesRuleLHSLeft sortName _ tableInstances (LeftLHS contextName, RightLHS contextName2)
          | not (null (findContextToNamespaceInstanceSyn contextName sortName tableInstances)) && not (null (findContextToNamespaceInstanceInh contextName2 sortName tableInstances)) = return ()
          | otherwise = Left (contextName ++ contextName2 ++ "not a good combination of synthesised and inherited namespaces")
        helpWellFormedRulesInstancesRuleLHSLeft sortName tableIdentifiers tableInstances (LeftLHS contextName, RightSub fieldname2 contextName2)
          | isNothing (lookup fieldname2 tableIdentifiers) = return ()
          | not (null (findContextToNamespaceInstanceSyn contextName sortName tableInstances)) && not (null (findContextToNamespaceInstanceSyn contextName2 (fromJust (lookup fieldname2 tableIdentifiers)) tableInstances)) = return ()
          | otherwise = Left (contextName ++ "is not a synthesised namespace")
        helpWellFormedRulesInstancesRuleLHSLeft sortName tableIdentifiers tableInstances (leftexpr, RightAdd expr _) =
          helpWellFormedRulesInstancesRuleLHSLeft sortName tableIdentifiers tableInstances (leftexpr, expr)
        helpWellFormedRulesInstancesRuleLHSLeft _ tableIdentifiers tableInstances (LeftSub fieldname contextName, RightSub fieldname2 contextName2)
          | isNothing sname2 || isNothing sname1 = return ()
          | fieldname == fieldname2 = Left (fieldname ++ "appears on both sides of a rule, which would cause infinite recursion")
          | not (null (findContextToNamespaceInstanceInh contextName (fromJust sname1) tableInstances)) && not (null (findContextToNamespaceInstanceSyn contextName2 (fromJust sname2) tableInstances)) = return ()
          | otherwise = Left (contextName ++ "is not a synthesised namespace")
          where
            sname2 = lookup fieldname2 tableIdentifiers
            sname1 = lookup fieldname tableIdentifiers
        helpWellFormedRulesInstancesRuleLHSLeft sortName tableIdentifiers tableInstances (LeftSub fieldname contextName, RightLHS contextName2)
          | isNothing (lookup fieldname tableIdentifiers) = return ()
          | not (null (findContextToNamespaceInstanceInh contextName (fromJust (lookup fieldname tableIdentifiers)) tableInstances)) && not (null (findContextToNamespaceInstanceInh contextName2 sortName tableInstances)) = return ()
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
isUniqueInList :: [String] -> String -> Either String ()
isUniqueInList [] _ = return ()
isUniqueInList (str:strs) err =
  if str `elem` strs
    then Left (show str ++ err)
    else isUniqueInList strs err

--helper to detect if different lists have unique names
shouldNotBeInSecondList :: [String] -> [String] -> String -> Either String ()
shouldNotBeInSecondList [] _ _ = return ()
shouldNotBeInSecondList (str:crest) sorts err =
  if str `elem` sorts
    then Left (show str ++ err)
    else shouldNotBeInSecondList crest sorts err

--helper to detect if names in the first list  exist in the available second list
shouldBeInSecondList :: [String] -> [String] -> String -> Either String ()
shouldBeInSecondList [] _ _ = return ()
shouldBeInSecondList (str:strs) sorts err =
  if str `elem` sorts
    then shouldBeInSecondList strs sorts err
    else Left (show str ++ err)
