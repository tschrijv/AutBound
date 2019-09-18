{-# OPTIONS_GHC -Wall #-}

module Variable.Common (getEnvType, getEnvFunctions, getFreeVar, getMappings, getSubst, getSortForId, firstToVarParams, dropFold, ExternalFunctions(..), getSortInheritedInstances) where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility

data ExternalFunctions = EF {
  getCtorParams :: ConstructorDef -> [Parameter],
  varCtorFreeVar :: String -> Expression,
  oneDeeper :: String -> [Expression] -> Expression,
  substExpr :: String -> String -> Expression,
  includeBinders :: Bool
}

-- * Types
-- ----------------------------------------------------------------------------

getEnvType :: Language -> (Type, [Constructor])
getEnvType (nsd, _, _, _) = ("Env", Constr "Nil" [] : map (
    \(MkNameSpace ns _ inEnv) -> Constr ('E' : ns) (inEnv ++ ["Env"])
  ) nsd)

getEnvFunctions :: Language -> [Function]
getEnvFunctions (nsd, sd, _, _) = let table = map getSortNameAndInstances sd
  in concatMap (\s ->
    let nsi = [SYN x y | SYN x y <- sctxs s]
    in if null nsi then [] else
    map (\c ->
      generateSortSynSystemOneConstructor (sname s) nsd table c (head nsi)
    ) (sctors s)
  ) sd

generateSortSynSystemOneConstructor :: SortName -> [NamespaceDef] -> [(SortName, [Context])] -> ConstructorDef -> Context -> Function
generateSortSynSystemOneConstructor sname _ _ (MkVarConstructor consName _) _ =
  Fn ("addToEnvironment" ++ sname) [([ConstrParam (capitalize consName) [VarParam "var"], VarParam "c"], VarExpr "c")]
generateSortSynSystemOneConstructor sname namespaces table cons ctx =
  Fn ("addToEnvironment" ++ sname ++ xinst ctx) [([ConstrParam (capitalize consName) (firstToVarParams listSorts ++ [VarParam "_" | _ <- hTypes]), VarParam "c"], getEnvFunctionGenerate sname ctx namespaces newtable listSorts rules)]
  where
    newtable = filterContextsForSameNamespace ctx table
    consName = cname cons
    listSorts = csorts cons
    hTypes = cnatives cons
    rules = cattrs cons

getEnvFunctionGenerate :: SortName -> Context -> [NamespaceDef] -> [(SortName, [Context])] -> [(IdenName, SortName)]  -> [AttributeDef] -> Expression
getEnvFunctionGenerate sname ctx namespaces table listSorts rules
  | null $ fromJust (lookup "lhs" allrules) = VarExpr "c"
  | otherwise = navigateRules sname ctx namespaces table listSorts rules start
  where
    allrules = collectRulesSyn rules listSorts
    start = fromJust (
      find
        (\x -> linst (fst x) == xinst ctx)
        (fromJust (lookup "lhs" allrules))
      )

    collectRulesSyn :: [AttributeDef] -> [(IdenName, SortName)] -> [(IdenName, [AttributeDef])]
    collectRulesSyn rules ids =
      foldl
        (++)
        [("lhs", [(LeftLHS c, r) | (LeftLHS c, r) <- rules])]
        (map (\(iden, _) -> [collectRulesOfIdSyn rules iden]) ids)
      where
        collectRulesOfIdSyn :: [AttributeDef] -> IdenName -> (IdenName, [AttributeDef])
        collectRulesOfIdSyn nsr i = (i, filter (\(LeftSub fieldname _, RightSub _ _) -> fieldname == i) nsr)

navigateRules :: SortName -> Context -> [NamespaceDef] -> [(SortName, [Context])] -> [(IdenName, SortName)] -> [AttributeDef] -> AttributeDef -> Expression
navigateRules sname ctx namespaces table listSorts rules (l, RightAdd expr _) =
  FnCall ("S" ++ xnamespace ctx) [navigateRules sname ctx namespaces table listSorts rules (l, expr)]
navigateRules _ _ _ _ _ _ (LeftLHS _, RightLHS _) =
  VarExpr "c"
navigateRules sname ctx namespaces table listSorts rules (LeftLHS _, RightSub iden _)
  | isJust newrule =
    FnCall functionName [VarExpr iden, navigateRules sname ctx namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
  where
    newrule = find (\(l, _) -> liden l == iden) rules
    functionName = "addToEnvironment" ++ fromJust (lookup iden listSorts) ++ xinst ctx -- TODO: iden was included in function name with a space?? included here both, below once + twice!!
navigateRules _ _ _ _ _ _ (LeftSub _ _, RightLHS _) =
  VarExpr "c"
navigateRules sname ctx namespaces table listSorts rules (LeftSub _ _, RightSub iden _)
  | isJust newrule =
    FnCall functionName [VarExpr iden, navigateRules sname ctx namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
  where
    newrule = find (\(l, _) -> liden l == iden) rules
    functionName = "addToEnvironment" ++ fromJust (lookup iden listSorts) ++ xinst ctx

-- * Free variables
-- ----------------------------------------------------------------------------

getFreeVar :: Language -> ExternalFunctions -> [Function]
getFreeVar (_, sd, _, _) ef =
  let table = map getSortNameAndInstances sd
      accessVarTable = getVarAccessTable sd
      filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) accessVarTable)) sd
  in map (\(MkDefSort sname _ cons _) ->
    Fn ("freeVariables" ++ sname)
    (map (\c ->
      (VarParam "c" : getCtorParams ef c,
      case c of
        (MkVarConstructor consName _) -> varCtorFreeVar ef consName
        _ -> let consName = cname c
                 folds = cfolds c
                 lists = clists c
                 sorts = csorts c
                 rules = cattrs c
                 hTypes = cnatives c
          in FnCall "nub" [
            FnCall "concat"
              [ListExpr (
                applyRulesIdentifiersFreeVariables
                  ef
                  sname
                  rules
                  (attrByIden rules (dropFold folds ++ lists ++ sorts))
                  (dropFold folds)
                  lists
                  sorts
                  table
                  accessVarTable
              )]
          ]
      )
    ) cons)
  ) filtered

applyRulesIdentifiersFreeVariables :: ExternalFunctions -> SortName -> [AttributeDef] -> [(IdenName, [AttributeDef])] -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(SortName, [Context])] -> [(SortName, Bool)] -> [Expression]
applyRulesIdentifiersFreeVariables _ _ _ [] _ _ _ _ _ = [ListExpr []]
applyRulesIdentifiersFreeVariables ef sname rules [(iden, idRules)] folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) = [FnCall ("freeVariables" ++ sortnameInUse) (addedBinders : [VarExpr (toLowerCaseFirst iden)])]
  | otherwise = [ListExpr []]
  where
    addedBinders = applyRuleInheritedNamespaces ef sname rules (iden, idRules) folds lists listSorts table (getSortInheritedInstances sortnameInUse table)
    sortnameInUse = getSortForId iden (lists ++ listSorts)
applyRulesIdentifiersFreeVariables ef sname rules ((iden, idRules):rest) folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (iden `elem` map fst folds) =
    FnCall "foldMap" [FnCall ("freeVariables" ++ sortnameInUse) [addedBinders], VarExpr (toLowerCaseFirst iden)]
    :
    applyRulesIdentifiersFreeVariables ef sname rules rest folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (iden `elem` map fst lists) =
    FnCall "concatMap" [FnCall ("freeVariables" ++ sortnameInUse) [addedBinders], VarExpr (toLowerCaseFirst iden)]
    :
    applyRulesIdentifiersFreeVariables ef sname rules rest folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) =
    FnCall ("freeVariables" ++ sortnameInUse) (addedBinders : [VarExpr (toLowerCaseFirst iden)])
    :
    applyRulesIdentifiersFreeVariables ef sname rules rest folds lists listSorts table accessVarTable
  | otherwise =
    applyRulesIdentifiersFreeVariables ef sname rules rest folds lists listSorts table accessVarTable
  where
    addedBinders = applyRuleInheritedNamespaces ef sname rules (iden, idRules) folds lists listSorts table (getSortInheritedInstances sortnameInUse table)
    sortnameInUse = getSortForId iden (folds ++ lists ++ listSorts)

-- * Mapping functions
-- ----------------------------------------------------------------------------

getMappings :: Language -> ExternalFunctions -> [Function]
getMappings (_, sd, _, _) ef =
  let filtered = filter (\(MkDefSort name _ _ _) -> isJust (lookup name (getVarAccessTable sd))) sd
      table = map getSortNameAndInstances sd
      accessVarTable = getVarAccessTable sd
  in map (
    \(MkDefSort name ctx constr _) ->
        Fn (sortMapName name)
        (map (\c ->
          (
            [VarParam ("on" ++ namespace) | INH _ namespace <- ctx] ++
            [VarParam "c"] ++
            getCtorParams ef c
          ,
            getExpr name c table accessVarTable
          )
        ) constr)
  ) filtered
  where
    sortMapName :: SortName -> String
    sortMapName sname = toLowerCaseFirst sname ++ "map"

    getExpr :: SortName -> ConstructorDef -> [(SortName, [Context])] -> [(SortName, Bool)] -> Expression
    getExpr sname (MkVarConstructor consName _) table _ =
      FnCall ("on" ++ xnamespace (head (fromJust (lookup sname table)))) [
        VarExpr "c",
        ConstrInst (capitalize consName) [VarExpr "var"]
      ]
    getExpr sname cons table accessVarTable =
      let binder = if includeBinders ef && isBind cons then [VarExpr "b"] else []
      in ConstrInst (capitalize (cname cons)) (binder ++ map process idRules ++ [VarExpr (toLowerCaseFirst x ++ show n) | (x, n) <- zip (cnatives cons) [1 :: Int ..]])
      where
        rules = cattrs cons
        idRules = attrByIden rules (folds ++ lists ++ sorts)
        folds = dropFold (cfolds cons)
        lists = clists cons
        sorts = csorts cons

        isBind MkBindConstructor{} = True
        isBind _                   = False

        process (iden, idenRules)
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst folds) =
            FnCall "fmap" [FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders), VarExpr (toLowerCaseFirst iden)]
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst lists) =
            FnCall "map" [FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders), VarExpr (toLowerCaseFirst iden)]
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst sorts) =
            FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders ++ [VarExpr (toLowerCaseFirst iden)])
          | otherwise = VarExpr (toLowerCaseFirst iden)
          where
            addedBinders =
              [applyRuleInheritedNamespaces
                ef
                sname
                rules
                (iden, idenRules)
                folds
                lists
                sorts
                table
                (getSortInheritedInstances sortnameInUse table)]
            sortnameInUse = getSortForId iden (folds ++ lists ++ sorts)

            nsiExprs :: [Context] -> [Expression]
            nsiExprs ctx = [VarExpr ("on" ++ namespace) | INH _ namespace <- ctx]

-- * Substitution functions
-- ----------------------------------------------------------------------------

getSubst :: Language -> ExternalFunctions -> [Function]
getSubst (nsd, sd, _, _) ef = let accessVarTable = getVarAccessTable sd
  in getSubstHelpers ef sd accessVarTable ++ getSubstFunctions sd nsd accessVarTable

getSubstHelpers :: ExternalFunctions -> [SortDef] -> [(SortName, Bool)] -> [Function]
getSubstHelpers ef sd varAccessTable =
  let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) varAccessTable)) sd
  in concatMap (\(MkDefSort sname _ cdefs _) ->
    [
      Fn (toLowerCaseFirst sname ++ "SubstituteHelp")
      [
        (
          [VarParam "sub", VarParam "c", ConstrParam (capitalize consName) [VarParam "var"]],
          substExpr ef sname consName
        )
      ]
    | MkVarConstructor consName _ <- cdefs]
  ) filtered

getSubstFunctions :: [SortDef] -> [NamespaceDef] -> [(SortName, Bool)] -> [Function]
getSubstFunctions sd nsd varAccessTable =
  let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) varAccessTable)) sd
  in concatMap (\(MkDefSort sname namespaceDecl _ bool) ->
    let filteredNs = [INH x y | INH x y <- namespaceDecl]
    in map (\ctx -> namespaceInstanceSubstFunction sname ctx namespaceDecl nsd bool) filteredNs
  ) filtered
  where
    namespaceInstanceSubstFunction :: SortName -> Context -> [Context] -> [NamespaceDef] -> Bool -> Function
    namespaceInstanceSubstFunction sname (INH instname namespaceName) namespaceDecl defs bool =
      Fn
        (toLowerCaseFirst sname ++ secondSort ++ "Substitute")
        [
          (
            [VarParam "sub", VarParam "orig", VarParam "t"],
            if bool then FnCall ("rewrite" ++ sname) [mapCall] else mapCall
          )
        ]
      where
        secondSort = lookForSortName namespaceName defs
        mapCall = FnCall (toLowerCaseFirst sname ++ "map") (declarationsToFunctionsSubst (INH instname namespaceName) namespaceDecl defs ++ [VarExpr "orig", VarExpr "t"])

    declarationsToFunctionsSubst :: Context -> [Context] -> [NamespaceDef] -> [Expression]
    declarationsToFunctionsSubst (INH instname1 namespaceName) nsi nsd =
      [
        if instname1 == instname2
          then FnCall (lookForSortName namespaceName nsd ++ "SubstituteHelp") [VarExpr "sub"]
          else LambdaExpr [VarParam "c", VarParam "x"] (VarExpr "x")
      | INH instname2 _ <- nsi]

-- * Helper functions
-- ----------------------------------------------------------------------------

getSortInheritedInstances :: SortName -> [(SortName, [Context])] -> [Context]
getSortInheritedInstances sname table = [INH x y | INH x y <- ctx]
  where
    ctx = fromJust (lookup sname table)

getSortForId :: IdenName -> [(IdenName, SortName)] -> SortName
getSortForId iden table = fromJust (lookup iden table)

firstToVarParams :: [(String, String)] -> [Parameter]
firstToVarParams = map (VarParam . toLowerCaseFirst . fst)

dropFold :: [(String, String, String)] -> [(String, String)]
dropFold = map (\(a, b, _) -> (a, b))

applyRuleInheritedNamespaces :: ExternalFunctions -> SortName -> [AttributeDef] -> (IdenName, [AttributeDef]) -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(SortName, [Context])] -> [Context] -> Expression
applyRuleInheritedNamespaces ef sname rules (iden, rulesOfId) folds lists listSorts table = recurse
  where
    newString =
      applyTheRuleOneInheritedNamespace
        ef
        sname
        rules
        (iden, rulesOfId)
        folds
        lists
        listSorts
        table
    recurse :: [Context] -> Expression
    recurse [] = VarExpr "c"
    recurse (x:xs) = case newString x (recurse xs) of
      Just ex -> ex
      Nothing -> recurse xs

    applyTheRuleOneInheritedNamespace :: ExternalFunctions -> SortName -> [AttributeDef] -> (IdenName, [AttributeDef]) -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(SortName, [Context])] -> Context -> Expression -> Maybe Expression
    applyTheRuleOneInheritedNamespace ef sname rules (_, rulesOfId) folds lists listSorts table currentCtx param
      | isJust foundrule = applyOneRuleLogic ef sname currentCtx newrules (fromJust foundrule) folds lists listSorts newtable [param]
      | otherwise = Nothing
      where
        foundrule = find (\x -> linst (fst x) == xinst currentCtx) rulesOfId
        newtable = filterContextsForSameNamespace currentCtx table
        newrules = filter (\(l, r) ->
            let sortnameId = liden l
                snameLookup = fromJust (lookup (capitalize sname) table)
                sortnameIdlookup = fromJust (lookup (getSortForId sortnameId (folds ++ lists ++ listSorts)) table)
            in (sortnameId == "" && any (\ctx -> linst l == xinst ctx) snameLookup) || any (\ctx -> linst l == xinst ctx) sortnameIdlookup
          ) rules

    applyOneRuleLogic :: ExternalFunctions -> SortName -> Context -> [AttributeDef] -> AttributeDef -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(SortName, [Context])] -> [Expression] -> Maybe Expression
    applyOneRuleLogic _ _ _ _ (_, RightLHS _) _ _ _ _ _ = Nothing
    applyOneRuleLogic ef sname ctx rules (l, RightAdd expr _) folds lists listSorts table params =
      return (oneDeeper ef (xnamespace ctx) (emptyOrToList (applyOneRuleLogic ef sname ctx rules (l, expr) folds lists listSorts table []) ++ params))
    applyOneRuleLogic ef sname ctx rules (_, RightSub iden context) folds lists listSorts table params
      | (elem iden (map fst lists) || elem iden (map fst folds)) && isJust newrule =
        return (FnCall ("generateHnat" ++ xnamespace ctx) (FnCall "length" (VarExpr iden : nextStep) : params))
      | elem iden (map fst lists) || elem iden (map fst folds) =
        return (FnCall ("generateHnat" ++ xnamespace ctx) (FnCall "length" [VarExpr iden] : params))
      | isJust newrule =
        return (FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) ((VarExpr iden : nextStep) ++ params))
      | otherwise =
        return (FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) (VarExpr iden : params))
      where
        newrule = find (\(l, _) -> liden l == iden) rules
        nextStep = emptyOrToList (applyOneRuleLogic ef sname ctx rules (fromJust newrule) folds lists listSorts table [])
