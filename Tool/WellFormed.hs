{-# OPTIONS_GHC -Wall #-}

module WellFormed (wellFormed) where

import GeneralTerms
import Utility
import Data.Maybe
import Data.List

--when is this syntax wellFormed : 1. when there are no duplicate constructors in the language i.e. there are no duplicate names among constructors or sorts and every sort has at the least one constructor
--accumulates the sortnames, constructornames, and the sortnames contained in the constructors,
--then looks up if all sortnames,namespacenames and contructornames are unique, if all sorts in the constructors exist,
--and whether sorts and constructors and namespaces have distinct names. Also namespacenames used in sorts should exist and constructors can only use variablebindings of namespaces they can access in the sort
wellFormed :: Language -> Either String ()
wellFormed (namespaces, sorts, rel, _, _)
  = let sortnames = map sname sorts
        consnames = concatMap (\sort -> map cname (sctors sort)) sorts
        sortconsnames = concatMap getSortsUsedByConstructors sorts
        namespaceNames = map nname namespaces
        sortnamespaces = map nsort namespaces
        instTable = map snameAndCtxs sorts
    in do
      noDuplicatesOrError sortnames "not unique sortname"
      noDuplicatesOrError consnames "not unique constructor"
      noDuplicatesOrError namespaceNames "not unique namespace"
      disjointOrError consnames sortnames "constructor and sort have same name"
      disjointOrError namespaceNames sortnames "namespace and sort have same name"
      disjointOrError namespaceNames consnames "constructor and namespace have same name"
      subsetOfOrError sortconsnames sortnames "sortname in constructor does not appear"
      subsetOfOrError sortnamespaces sortnames "sortname in namespace does not appear"
      mapM_ (
        \sort ->
          let ctors = sctors sort
              ctxs = sctxs sort
          in do
            noDuplicatesOrError (map xinst ctxs) "Instance is not a unique name in the declaration "
            subsetOfOrError [snd (fromJust (cbinder ctor)) | ctor <- ctors, isBind ctor] namespaceNames "Namespace in constructor is not a declared namespace"
            subsetOfOrError (map xnamespace ctxs) namespaceNames "Instance does not reference an existing namespace"
            notEmpty sort
            checkVarCtors sort
            wellFormedConstructors ctors
            helpWellFormedVariables ctors ctxs
        ) sorts
      helpWellFormedRulesInstances sorts instTable
      isWellFormedBindToContext sorts instTable
      helpWellFormedRulesLHSExpressions sorts instTable
      mapM_ (\r -> wfRelation r sorts rel) rel
  where
    checkVarCtors :: SortDef -> Either String ()
    checkVarCtors (MkDefSort name ctxs ctors _) = mapM_ (
        \ctor -> checkInst name (cinst ctor) ctxs
      ) [MkVarConstructor n i | MkVarConstructor n i <- ctors]
      where
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

    notEmpty :: SortDef -> Either String ()
    notEmpty (MkDefSort name _ [] _) = Left (show name ++ " has no constructor")
    notEmpty _ = return ()

    wellFormedConstructors :: [ConstructorDef] -> Either String ()
    wellFormedConstructors ctors = mapM_ wellFormedConstructor ctors
      where
        wellFormedConstructor :: ConstructorDef -> Either String ()
        wellFormedConstructor cons = do
          noDuplicatesOrError (getIdentifiersConstructor cons) "not unique identifier"
          subsetOfOrError (getAllIds cons) (getIdentifiersConstructor cons) "identifier not used in constructor"
          subsetOfOrError (getRightExprIdsConstructorBinding cons) (maybe [] (\b -> [fst b]) (cbinder cons)) "Identifier in right expression does not appear as binder"
          subsetOfOrError (getLeftExprIdsConstructor cons) (getIdentifiersWithoutBinding cons) "Identifier in left expression does not appear as constructorfield"
          subsetOfOrError (getRightExprIdsConstructor cons) (getIdentifiersWithoutBinding cons) "Identifier in right expression does not appear as constructorfield"
          where
            --get the Identifiers of the arguments of a constructor (including the binder)
            getIdentifiersConstructor :: ConstructorDef -> [String]
            getIdentifiersConstructor (MkVarConstructor _ _) = []
            getIdentifiersConstructor ctor = cidens ctor ++ maybe [] (\b -> [fst b]) (cbinder ctor)

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
            getIdentifiersWithoutBinding ctor = cidens ctor

            --get the identifiers used in the rules defined in the constructor
            getAllIds :: ConstructorDef -> [IdenName]
            getAllIds (MkVarConstructor _ _) = []
            getAllIds ctor = concatMap getRuleIdentifiers (cattrs ctor)

            --get identifiers of the rule, left expression+the rightexpr
            getRuleIdentifiers :: AttributeDef -> [IdenName]
            getRuleIdentifiers (l, r) = getLeftExprId l ++ getRightExprIdBinding r ++ getRightExprId r

            -- get the ids of the RightExpr without any binders included
            getRightExprIdsConstructor :: ConstructorDef -> [IdenName]
            getRightExprIdsConstructor (MkVarConstructor _ _) = []
            getRightExprIdsConstructor ctor = concatMap (getRightExprId . snd) (cattrs ctor)

            --get the ids of the LeftExpr
            getLeftExprIdsConstructor :: ConstructorDef -> [IdenName]
            getLeftExprIdsConstructor (MkVarConstructor _ _) = []
            getLeftExprIdsConstructor ctor = concatMap (getLeftExprId . fst) (cattrs ctor)

    -- variables in a sort can only access the inherited namespaces
    helpWellFormedVariables :: [ConstructorDef] -> [Context] -> Either String ()
    helpWellFormedVariables ctors instances
      = let inhNames = [name | INH name _ <- instances]
        in mapM_
          (\ctor -> subsetOfOrError [cinst ctor] inhNames "Namespace is not an inherited namespace")
          [MkVarConstructor n i | MkVarConstructor n i <- ctors]

    --get the sorts used in all constructors of the sort
    getSortsUsedByConstructors :: SortDef -> [SortName]
    getSortsUsedByConstructors s = getSortsOfConstructors (sctors s)
      where
        -- get the sorts used by constructors in a list of constructors
        getSortsOfConstructors :: [ConstructorDef] -> [SortName]
        getSortsOfConstructors = concatMap getSortsConstructor where
          --get the sorts used in the constructor
          getSortsConstructor :: ConstructorDef -> [SortName]
          getSortsConstructor (MkVarConstructor _ _) = []
          getSortsConstructor ctor =  cidenSorts ctor

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
          | not (null (getLeftExprId leftexpr))   && elem (head (getLeftExprId leftexpr))   (map fst lists ++ map (\(x, _, _) -> x) folds) = return ()
          | null (getRightExprId rightexpr)       && not (null rightInstanceLHS)   && null (getLeftExprId leftexpr)       && not (null leftInstanceLHS)   && xnamespace (head rightInstanceLHS)   == xnamespace (head leftInstanceLHS)    = return ()
          | not (null (getRightExprId rightexpr)) && not (null rightInstanceNoLHS) && null (getLeftExprId leftexpr)       && not (null leftInstanceLHS)   && xnamespace (head rightInstanceNoLHS) == xnamespace (head leftInstanceLHS)    = return ()
          | not (null (getRightExprId rightexpr)) && not (null rightInstanceNoLHS) && not (null (getLeftExprId leftexpr)) && not (null leftInstanceNoLHS) && xnamespace (head rightInstanceNoLHS) == xnamespace (head leftInstanceNoLHS)  = return ()
          | null (getRightExprId rightexpr)       && not (null rightInstanceLHS)   && not (null (getLeftExprId leftexpr)) && not (null leftInstanceNoLHS) && xnamespace (head rightInstanceLHS)   == xnamespace (head leftInstanceNoLHS)  = return ()
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
            [SYN ctxNamesyn namespacename | SYN ctxNamesyn namespacename <- fromJust (lookup sortName table)]

        -- filters all the inherited namespaces
        findContextToNamespaceInstanceInh :: InstanceName -> SortName -> [(SortName, [Context])] -> [Context]
        findContextToNamespaceInstanceInh instName sortName table =
          filter
            (\ctx -> xinst ctx == instName)
            [INH ctxNameinh namespacename | INH ctxNameinh namespacename <- fromJust (lookup sortName table)]

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
noDuplicatesOrError :: [String] -> String -> Either String ()
noDuplicatesOrError [] _ = return ()
noDuplicatesOrError (str:strs) err =
  if str `elem` strs
    then Left (show str ++ err)
    else noDuplicatesOrError strs err

--helper to detect if different lists have unique names
disjointOrError :: [String] -> [String] -> String -> Either String ()
disjointOrError [] _ _ = return ()
disjointOrError (str:crest) sorts err =
  if str `elem` sorts
    then Left (show str ++ err)
    else disjointOrError crest sorts err

--helper to detect if names in the first list  exist in the available second list
subsetOfOrError :: [String] -> [String] -> String -> Either String ()
subsetOfOrError [] _ _ = return ()
subsetOfOrError (str:strs) sorts err =
  if str `elem` sorts
    then subsetOfOrError strs sorts err
    else Left (show str ++ err)

-- Environment for accumulating the types of metavariables
data EnvItem = EnvItemSort { itemname :: SortName }
              | EnvItemNamespace { itemname :: NamespaceName }  
              | EnvItemVar { itemname :: SortName }
              deriving (Show, Eq)
type Env = [(IdenName, EnvItem)]

-- Checks whether a relation is well formed. It is well formed if both the type signature and
-- all the relation bodies are well formed.
wfRelation :: Relation -> [SortDef] -> [Relation] -> Either String ()
wfRelation rel sorts relations 
  = let ts = rtypesignature rel
        tsrelations = map (\r -> (rname r, rtypesignature r)) relations
        name = rname rel
    in do
      wfSig ts sorts tsrelations
      mapM_ (
        \body -> wfRelbody body ts sorts tsrelations
        ) (rbody rel)

-- Checks whether a type signature of a relation is well formed.
-- It is well formed if:
--     1. the given type signature corresponds (and corresponding relation name)
--        with an element of the third argument (relations)
--     2. all the types of the type signature are valid sorts
wfSig :: TypeSignatureDef -> [SortDef] -> [(RelationName, TypeSignatureDef)] -> Either String ()
wfSig ts sorts relations
  = let name = tsname ts in
      case lookup (tsname ts) relations of
        Nothing -> Left (show name ++ "is not parsed correctly")
        Just ts -> wfTypes (tstypes ts) (snameAndCtorsList sorts)
        Just x -> Left (show name ++ " has type signature " ++ show x ++ " while "
                        ++ show ts ++ " was expected")
  where
    -- Check that the types in the type signature are valid sorts
    wfTypes :: [SortName] -> [(SortName, [ConstructorDef])] -> Either String ()
    wfTypes [] _ = return ()
    wfTypes (t:ts) sorts
      = if (isJust (lookup t sorts))
        then wfTypes ts sorts
        else Left (show t ++ "is not a valid type")

-- Checks whether a relation body is well formed.
-- It is well formed if:
--    1. The judgement is well formed
--    2. All judgements in the conditions are well formed
wfRelbody :: RelationBodyDef -> TypeSignatureDef -> [SortDef] -> [(RelationName, TypeSignatureDef)] -> Either String ()
wfRelbody body ts sorts relations
  = case (wfJudgement (rjudg body) ts [] sorts relations) of
          Left s -> Left s
          Right env -> wfConditions (rconditions body) env sorts relations

-- Checks whether the judgements in the conditions are well formed
wfConditions :: [Judgement] -> Env -> [SortDef] -> [(RelationName, TypeSignatureDef)] -> Either String ()
wfConditions [] env _ _ = return ()
wfConditions (j:js) env sorts relations
  = let name = jname j
        ts = fromJust (lookup name relations)
    in case (wfJudgement j ts [] sorts relations) of
          Left s -> Left s
          Right env' -> wfConditions js env' sorts relations

-- Checks whether a judgement is well formed.
-- It is well formed if:
--    1. The relation name of the judgement is the same as the relation name of the type signature
--    2. The number of arguments is correct
--    3. All arguments are well formed
wfJudgement :: Judgement -> TypeSignatureDef -> Env -> [SortDef] -> [(RelationName, TypeSignatureDef)] -> Either String Env
wfJudgement j ts env sorts relations
  = if (jname j) == (tsname ts)
    then checkArguments (jargs j) (tstypes ts) env sorts (tsname ts)
    else Left ("A relation body of " ++ show (tsname ts) ++ " was expected, instead a body of " ++ show (jname j)
          ++ "was given")
  where
    -- Checks whether the number of arguments are correct and whether the arguments are well formed.
    checkArguments :: [ArgumentDef] -> [SortName] -> Env -> [SortDef] -> RelationName -> Either String Env
    checkArguments [] [] env _ _ = Right env
    checkArguments [] (t:ts) _ _ name = Left ("Too few arguments are supplied to " ++ show name)
    checkArguments (x:xs) [] _ _ name = Left ("Too many arguments are supplied to " ++ show name)
    checkArguments (x:xs) (t:ts) env sorts name 
      = case (wfArgument x t env sorts) of
          Left s -> Left s
          Right env' -> checkArguments xs ts env' sorts name

-- Check whether an argument is well formed.
wfArgument :: ArgumentDef -> SortName -> Env -> [SortDef] -> Either String Env
wfArgument (MkMetaVarArgument name) t env sorts 
  = case lookup name env of
      Nothing -> case (lookup t (snameAndCtorsList sorts)) of
                    Nothing -> Right ((name, (EnvItemNamespace t)) : env)
                    Just x -> Right ((name, (EnvItemSort t)) : env)
      Just x -> checkSortAndNamespace t (itemname x)
  where
    -- Check whether actual and expected types match
    checkSortAndNamespace :: String -> String -> Either String Env
    checkSortAndNamespace t x = if x == t
                                then Right env
                                else Left (show name ++ " has conflicting types: " ++ show t ++ " and " ++ show x)
wfArgument (MkSortArgument ctorName args) t env sorts 
  = case (lookup t (snameAndCtorsList sorts)) of
    Nothing -> Left (show t ++ " is not a valid sort")
    Just ctorlist -> case (filter (\ctor -> (cname ctor) == ctorName) ctorlist) of
                        [] -> Left (show ctorName ++ " is not a valid constructor for " ++ show t)
                        [ctor] -> wfSortCtor ctor t args env sorts
                        otherwise -> Left (show ctorName ++ " is not a unique constructor for " ++ show t)
wfArgument (MkSubstArgument a1 name a2) t env sorts = do
  env1 <- wfSubst a1 name a2 t env sorts
  return (removeVarItems env1)
  where 
    -- Remove all EnvItemVar from the environment
    removeVarItems :: Env -> Env
    removeVarItems [] = []
    removeVarItems ((_, EnvItemVar{}) : xs) = removeVarItems xs
    removeVarItems (x : xs) = x : removeVarItems xs

-- Check that the construction of a sort is well formed.
-- It is well formed if:
--      1. The number of arguments is correct
--      2. All the arguments of the constructor of the sort are well formed
wfSortCtor :: ConstructorDef -> SortName -> [ArgumentDef] -> Env -> [SortDef] -> Either String Env
wfSortCtor ctor@(MkDefConstructor{}) _ args env sorts = checkCtorArguments ctor args env sorts wfArgument
wfSortCtor ctor@(MkBindConstructor{}) _ args env sorts
  = let id = head args
        ns = snd (_cbinder ctor) in
      do env1 <- wfArgument id ns env sorts
         env2 <- checkCtorArguments ctor (tail args) env1 sorts wfArgument
         case id of
           MkMetaVarArgument name -> return (delete (name, EnvItemNamespace ns) env2)
           _ -> Left "" -- cannot occur
wfSortCtor ctor@(MkVarConstructor{}) sname args env sorts
  = case args of
      [] -> Left (show (cname ctor) ++ " has no argument while it expects one")
      [x] -> let list = (instanceAndNamespaceList (snameAndCtxsList sorts) sname)
                 ns = fromJust (lookup (cinst ctor) list) in
                   wfArgument x ns env sorts
      _ -> Left (show (cname ctor) ++ " has more than one argument while it expects one")

-- Check the wellformedness of the list, foldable, regular sort and native arguments of the constructor of a sort
checkCtorArguments :: ConstructorDef -> [ArgumentDef] -> Env -> [SortDef] -> 
                      (ArgumentDef -> SortName -> Env -> [SortDef] -> Either String Env) -> 
                      Either String Env
checkCtorArguments ctor args env sorts func
  = let listctor =  clists ctor
        foldctor = cfolds ctor
        sortctor = csorts ctor
        natctor = cnatives ctor
        lenl = length listctor
        lenf = length foldctor
        lens = length sortctor
        lenn = length natctor
        totalLength = lenl + lenf + lens + lenn
        lenArgs = length args
        (listargs, rest1) = splitAt lenl args
        (foldargs, rest2) = splitAt (lenl + lenf) rest1
        (sortargs, natargs) = splitAt (lenl + lenf + lens) rest2
    in if totalLength == lenArgs
        then do
            env1 <- checkLists listctor listargs env sorts
            env2 <- checkFolds foldctor foldargs env1 sorts
            env3 <- checkSorts sortctor sortargs env2 sorts
            checkNatives natctor natargs env3 sorts
        else Left (show (cname ctor) ++ " has " ++ show totalLength ++ " arguments while " ++
                    show lenArgs ++ " arguments were given")
  where
    -- Check the wellformedness of the list arguments of the constructor of a sort
    checkLists :: [(IdenName, SortName)] -> [ArgumentDef] -> Env -> [SortDef] -> Either String Env
    checkLists [] [] env _ = Right env
    checkLists _ _ _ _ = Left ("List arguments are not supported in relations")

    -- Check the wellformedness of the foldable arguments of the constructor of a sort
    checkFolds :: [(IdenName, SortName, FoldName)] -> [ArgumentDef] -> Env -> [SortDef] -> Either String Env
    checkFolds [] [] env _ = Right env
    checkFolds _ _ _ _ = Left ("Foldable arguments are not supported in relations")

    -- Check the wellformedness of the regular sort arguments of the constructor of a sort
    checkSorts :: [(IdenName, SortName)] -> [ArgumentDef] -> Env -> [SortDef] -> Either String Env
    checkSorts [] [] env _ = Right env
    checkSorts ((_,x):xs) (y:ys) env sorts 
      = do env' <- func y x env sorts
           checkSorts xs ys env' sorts
    checkSorts [] _ _ _ = Left "" -- This case cannot occur, but ghc doesn't know that
    
    -- Check the wellformedness of the native arguments of the constructor of a sort
    checkNatives :: [HaskellTypeName] -> [ArgumentDef] -> Env -> [SortDef] -> Either String Env
    checkNatives [] [] env _ = Right env
    checkNatives _ _ _ _ = Left ("Native types in arguments are not supported in relations")

-- Check whether a substitution argument is well formed.
wfSubst :: ArgumentDef -> IdenName -> ArgumentDef -> SortName -> Env -> [SortDef] -> Either String Env
wfSubst a1@(MkMetaVarArgument name) x a2 t env sorts 
  = if name == x
    then wfArgument a2 t env sorts
    else wfArgument a1 t env sorts
wfSubst a1@(MkSortArgument ctorName args) x a2 t env sorts 
  = let ctorlist = fromJust (lookup t (snameAndCtorsList sorts)) in
      case (filter (\ctor -> (cname ctor) == ctorName) ctorlist) of
          [] -> Left (show ctorName ++ " is not a valid constructor for " ++ show t)
          [ctor] -> wfSubstCtor ctor x a2 t args env sorts
          otherwise -> Left (show ctorName ++ " is not a unique constructor for " ++ show t)
wfSubst a1@(MkSubstArgument a11 y a12) x a2 t1 env sorts = do
  env1 <- wfSubst a11 y a12 t1 env sorts
  case lookup y env1 of
    Nothing -> wfSubst a11 x a2 t1 env1 sorts
    Just (EnvItemVar t2) -> do env2 <- wfSubst a12 x a2 t2 env1 sorts
                               wfSubst a11 x a2 t1 env2 sorts
    Just _ -> Left ("Ambiguous occurence of " ++ show y)

-- Check that the construction of a sort is well formed within a substitution
-- It is well formed if:
--      1. The number of arguments is correct
--      2. All the arguments of the constructor of the sort are well formed within the substitution
wfSubstCtor :: ConstructorDef -> IdenName -> ArgumentDef -> SortName -> [ArgumentDef] -> Env -> [SortDef] -> Either String Env
wfSubstCtor ctor@(MkDefConstructor{}) x a2 _ args env sorts = checkCtorArguments ctor args env sorts (\a1 t env' sorts' -> wfSubst a1 x a2 t env' sorts')
wfSubstCtor ctor@(MkBindConstructor{}) x a2 _ args env sorts
  = let id = head args
        ns = snd (_cbinder ctor) in
      do env1 <- wfSubst id x a2 ns env sorts
         checkCtorArguments ctor (tail args) env1 sorts (\a1 t env2 sorts' -> wfSubst a1 x a2 t env2 sorts')
wfSubstCtor ctor@(MkVarConstructor{}) x a2 t args env sorts
  = case args of
      [] -> Left (show (cname ctor) ++ " has no argument while it expects one")
      [(MkMetaVarArgument y)] -> if y == x
                                  then case lookup x env of
                                          Nothing -> do env' <- wfArgument a2 t env sorts
                                                        return ((x, EnvItemVar t) : env')
                                          Just (EnvItemVar t') -> if t == t'
                                                    then do env' <- wfArgument a2 t env sorts
                                                            return ((x, EnvItemVar t) : env')
                                                    else Left ("Variable " ++ show x ++ " has conflicting types: " ++ 
                                                                  show t ++ " and " ++ show t')
                                          Just _ -> Left ("Ambiguous occurence of " ++ show x)
                                  else Right env
      [(MkSortArgument{})] -> Left (show (cname ctor) ++ " cannot have a sort argument")
      [(MkSubstArgument{})] -> Left (show (cname ctor) ++ " cannot have a substitution argument")
      _ -> Left (show (cname ctor) ++ " has more than one argument while it expects one")


        
