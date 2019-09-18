{-# OPTIONS_GHC -Wall #-}

module Variable.Common (getEnvType, getEnvFunctions, getFreeVar, getMappings, getSubst, getSortForId, firstToVarParams, dropFold, applyRuleInheritedNamespaces, ExternalFunctions(..)) where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility

data ExternalFunctions = EF {
  getCtorParams :: ConstructorDef -> [Parameter],
  varCtorFreeVar :: String -> Expression,
  oneDeeper :: String -> [Expression] -> Expression
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
    let nsi = [SYN x y | SYN x y <- getSortInstances s]
    in if null nsi then [] else
    map (\c ->
      generateSortSynSystemOneConstructor (getName s) nsd table c (head nsi)
    ) (getSortCtors s)
  ) sd

generateSortSynSystemOneConstructor :: SortName -> [NamespaceDef] -> [(SortName, [NamespaceInstance])] -> ConstructorDef -> NamespaceInstance -> Function
generateSortSynSystemOneConstructor sname _ _ (MkVarConstructor consName _) _ =
  Fn ("addToEnvironment" ++ sname) [([ConstrParam (capitalize consName) [VarParam "var"], VarParam "c"], VarExpr "c")]
generateSortSynSystemOneConstructor sname namespaces table cons inst =
  Fn ("addToEnvironment" ++ sname ++ getName inst) [([ConstrParam (capitalize consName) (firstToVarParams listSorts ++ [VarParam "_" | _ <- hTypes]), VarParam "c"], getEnvFunctionGenerate sname inst namespaces newtable listSorts rules)]
  where
    newtable = filterTableBySameNamespace inst table
    consName = getName cons
    listSorts = getCtorSorts cons
    hTypes = getCtorHTypes cons
    rules = getCtorRules cons

getEnvFunctionGenerate :: SortName -> NamespaceInstance -> [NamespaceDef] -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)]  -> [NamespaceRule] -> Expression
getEnvFunctionGenerate sname inst namespaces table listSorts rules
  | null $ fromJust (lookup "lhs" allrules) = VarExpr "c"
  | otherwise = navigateRules sname inst namespaces table listSorts rules start
  where
    allrules = collectRulesSyn rules listSorts
    start = fromJust (
      find
        (\x -> getLeftSubInstanceName (fst x) == getName inst)
        (fromJust (lookup "lhs" allrules))
      )

    collectRulesSyn :: [NamespaceRule] -> [(IdName, SortName)] -> [(IdName, [NamespaceRule])]
    collectRulesSyn rules ids =
      foldl
        (++)
        [("lhs", [(LeftLHS c, r) | (LeftLHS c, r) <- rules])]
        (map (\(iden, _) -> [collectRulesOfIdSyn rules iden]) ids)
      where
        collectRulesOfIdSyn :: [NamespaceRule] -> IdName -> (IdName, [NamespaceRule])
        collectRulesOfIdSyn nsr i = (i, filter (\(LeftSub fieldname _, RightSub _ _) -> fieldname == i) nsr)

navigateRules :: SortName -> NamespaceInstance -> [NamespaceDef] -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)] -> [NamespaceRule] -> NamespaceRule -> Expression
navigateRules sname inst namespaces table listSorts rules (l, RightAdd expr _) =
  FnCall ("S" ++ getInstanceNameSpace inst) [navigateRules sname inst namespaces table listSorts rules (l, expr)]
navigateRules _ _ _ _ _ _ (LeftLHS _, RightLHS _) =
  VarExpr "c"
navigateRules sname inst namespaces table listSorts rules (LeftLHS _, RightSub iden _)
  | isJust newrule =
    FnCall functionName [VarExpr iden, navigateRules sname inst namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
  where
    newrule = find (\(l, _) -> getLeftSubIden l == iden) rules
    functionName = "addToEnvironment" ++ fromJust (lookup iden listSorts) ++ getName inst -- TODO: iden was included in function name with a space?? included here both, below once + twice!!
navigateRules _ _ _ _ _ _ (LeftSub _ _, RightLHS _) =
  VarExpr "c"
navigateRules sname inst namespaces table listSorts rules (LeftSub _ _, RightSub iden _)
  | isJust newrule =
    FnCall functionName [VarExpr iden, navigateRules sname inst namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
  where
    newrule = find (\(l, _) -> getLeftSubIden l == iden) rules
    functionName = "addToEnvironment" ++ fromJust (lookup iden listSorts) ++ getName inst

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
        _ -> let consName = getName c
                 folds = getCtorFolds c
                 lists = getCtorLists c
                 sorts = getCtorSorts c
                 rules = getCtorRules c
                 hTypes = getCtorHTypes c
          in FnCall "nub" [
            FnCall "concat"
              [ListExpr (
                applyRulesIdentifiersFreeVariables
                  ef
                  sname
                  rules
                  (groupRulesByIden rules (dropFold folds ++ lists ++ sorts))
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

applyRulesIdentifiersFreeVariables :: ExternalFunctions -> SortName -> [NamespaceRule] -> [(IdName, [NamespaceRule])] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> [Expression]
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
    \(MkDefSort name inst constr _) ->
        Fn (sortMapName name)
        (map (\c ->
          (
            [VarParam ("on" ++ namespace) | INH _ namespace <- inst] ++
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

    getExpr :: SortName -> ConstructorDef -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> Expression
    getExpr sname (MkVarConstructor consName _) table _ =
      FnCall ("on" ++ getInstanceNameSpace (head (fromJust (lookup sname table)))) [
        VarExpr "c",
        ConstrInst (capitalize consName) [VarExpr "var"]
      ]
    getExpr sname cons table accessVarTable =
      ConstrInst (capitalize (getName cons)) (map process idRules ++ [VarExpr (toLowerCaseFirst x ++ show n) | (x, n) <- zip (getCtorHTypes cons) [1 :: Int ..]])
      where
        rules = getCtorRules cons
        idRules = groupRulesByIden rules (folds ++ lists ++ sorts)
        folds = dropFold (getCtorFolds cons)
        lists = getCtorLists cons
        sorts = getCtorSorts cons

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

            nsiExprs :: [NamespaceInstance] -> [Expression]
            nsiExprs inst = [VarExpr ("on" ++ namespace) | INH _ namespace <- inst]

-- * Substitution functions
-- ----------------------------------------------------------------------------

getSubst :: Language -> [Function]
getSubst (nsd, sd, _, _) = let accessVarTable = getVarAccessTable sd
  in getSubstHelpers sd accessVarTable ++ getSubstFunctions sd nsd accessVarTable

getSubstHelpers :: [SortDef] -> [(SortName, Bool)] -> [Function]
getSubstHelpers sd varAccessTable =
  let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) varAccessTable)) sd
  in concatMap (\(MkDefSort sname _ cdefs _) ->
    [
      Fn (toLowerCaseFirst sname ++ "SubstituteHelp")
      [
        (
          [VarParam "sub", VarParam "c", ConstrParam (capitalize consName) [VarParam "var"]],
          IfExpr
            (EQExpr (VarExpr "var") (VarExpr "c"))
            (FnCall (toLowerCaseFirst sname ++ "shiftplus") [VarExpr "c", VarExpr "sub"])
            (ConstrInst (capitalize consName) [VarExpr "var"])
        )
      ]
    | MkVarConstructor consName _ <- cdefs]
  ) filtered

getSubstFunctions :: [SortDef] -> [NamespaceDef] -> [(SortName, Bool)] -> [Function]
getSubstFunctions sd nsd varAccessTable =
  let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) varAccessTable)) sd
  in concatMap (\(MkDefSort sname namespaceDecl _ bool) ->
    let filteredNs = [INH x y | INH x y <- namespaceDecl]
    in map (\inst -> namespaceInstanceSubstFunction sname inst namespaceDecl nsd bool) filteredNs
  ) filtered
  where
    namespaceInstanceSubstFunction :: SortName -> NamespaceInstance -> [NamespaceInstance] -> [NamespaceDef] -> Bool -> Function
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

    declarationsToFunctionsSubst :: NamespaceInstance -> [NamespaceInstance] -> [NamespaceDef] -> [Expression]
    declarationsToFunctionsSubst (INH instname1 namespaceName) nsi nsd =
      [
        if instname1 == instname2
          then FnCall (lookForSortName namespaceName nsd ++ "SubstituteHelp") [VarExpr "sub"]
          else LambdaExpr [VarParam "c", VarParam "x"] (VarExpr "x")
      | INH instname2 _ <- nsi]

-- * Helper functions
-- ----------------------------------------------------------------------------

getSortInheritedInstances :: SortName -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance]
getSortInheritedInstances sname table = [INH x y | INH x y <- inst]
  where
    inst = fromJust (lookup sname table)

getSortForId :: IdName -> [(IdName, SortName)] -> SortName
getSortForId iden table = fromJust (lookup iden table)

firstToVarParams :: [(String, String)] -> [Parameter]
firstToVarParams = map (VarParam . toLowerCaseFirst . fst)

dropFold :: [(String, String, String)] -> [(String, String)]
dropFold = map (\(a, b, _) -> (a, b))

applyRuleInheritedNamespaces :: ExternalFunctions -> SortName -> [NamespaceRule] -> (IdName, [NamespaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance] -> Expression
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
    recurse :: [NamespaceInstance] -> Expression
    recurse [] = VarExpr "c"
    recurse (x:xs) = case newString x (recurse xs) of
      Just ex -> ex
      Nothing -> recurse xs

    applyTheRuleOneInheritedNamespace :: ExternalFunctions -> SortName -> [NamespaceRule] -> (IdName, [NamespaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> NamespaceInstance -> Expression -> Maybe Expression
    applyTheRuleOneInheritedNamespace ef sname rules (_, rulesOfId) folds lists listSorts table currentinst param
      | isJust foundrule = applyOneRuleLogic ef sname currentinst newrules (fromJust foundrule) folds lists listSorts newtable [param]
      | otherwise = Nothing
      where
        foundrule = find (\x -> getLeftSubInstanceName (fst x) == getName currentinst) rulesOfId
        newtable = filterTableBySameNamespace currentinst table
        newrules = filter (\(l, r) ->
            let sortnameId = getLeftSubIden l
                snameLookup = fromJust (lookup (capitalize sname) table)
                sortnameIdlookup = fromJust (lookup (getSortForId sortnameId (folds ++ lists ++ listSorts)) table)
            in (sortnameId == "" && any (\x -> getLeftSubInstanceName l == getName x) snameLookup)
            || any (\x -> getLeftSubInstanceName l == getName x) sortnameIdlookup
          ) rules

    applyOneRuleLogic :: ExternalFunctions -> SortName -> NamespaceInstance -> [NamespaceRule] -> NamespaceRule -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [Expression] -> Maybe Expression
    applyOneRuleLogic _ _ _ _ (_, RightLHS _) _ _ _ _ _ = Nothing
    applyOneRuleLogic ef sname inst rules (l, RightAdd expr _) folds lists listSorts table params =
      return (oneDeeper ef (getInstanceNameSpace inst) (emptyOrToList (applyOneRuleLogic ef sname inst rules (l, expr) folds lists listSorts table []) ++ params))
    applyOneRuleLogic ef sname inst rules (_, RightSub iden context) folds lists listSorts table params
      | (elem iden (map fst lists) || elem iden (map fst folds)) && isJust newrule =
        return (FnCall ("generateHnat" ++ getInstanceNameSpace inst) (FnCall "length" (VarExpr iden : nextStep) : params))
      | elem iden (map fst lists) || elem iden (map fst folds) =
        return (FnCall ("generateHnat" ++ getInstanceNameSpace inst) (FnCall "length" [VarExpr iden] : params))
      | isJust newrule =
        return (FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) ((VarExpr iden : nextStep) ++ params))
      | otherwise =
        return (FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) (VarExpr iden : params))
      where
        newrule = find (\(l, _) -> getLeftSubIden l == iden) rules
        nextStep = emptyOrToList (applyOneRuleLogic ef sname inst rules (fromJust newrule) folds lists listSorts table [])
