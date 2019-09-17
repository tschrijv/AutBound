{-# OPTIONS_GHC -Wall #-}

module Variable.Common (getTypes, getEnvType, getEnvFunctions, getFreeVar, getMappings, getSubst, getSortForId, firstToVarParams, dropFold, applyRuleInheritedNamespaces) where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility

getTypes :: Language -> [(Type, [Constructor])]
getTypes (_, sd, _, _) = map (
    \(MkDefSort name _ cds _) -> (name, map getConstr cds)
  ) sd where
    getConstr :: ConstructorDef -> Constructor
    getConstr (MkDefConstructor n lists listSorts folds _ hTypes) =
      Constr n (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes)
    getConstr (MkBindConstructor n lists listSorts folds (var, ns) _ hTypes) =
      Constr n (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes)
      -- Constr n ("Variable" : (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes))
    getConstr (MkVarConstructor n _) =
      Constr n ["Variable"]

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


getFreeVar :: Language -> [Function]
getFreeVar (_, sd, _, _) =
  let table = map getSortNameAndInstances sd
      accessVarTable = getVarAccessTable sd
      filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) accessVarTable)) sd
  in map (\(MkDefSort sname _ cons _) ->
    Fn ("freeVariables" ++ sname)
    (concatMap (\c ->
      generateFreeVariableFunction sname c table accessVarTable
    ) cons)
  ) filtered

generateFreeVariableFunction :: SortName -> ConstructorDef -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> [([Parameter], Expression)]
generateFreeVariableFunction _ cons@(MkVarConstructor _ _) _ _ =
  [([VarParam "c", generateFreeVariableConstructor cons], IfExpr (GTEExpr (VarExpr "var") (VarExpr "c")) (ListExpr [FnCall "minus" [VarExpr "var", VarExpr "c"]]) (ListExpr []))]
  -- [([VarParam "c", generateFreeVariableConstructor cons], IfExpr (FnCall "elem" [VarExpr "var", VarExpr "c"]) (ListExpr []) (ListExpr [ConstrInst (getName cons) [VarExpr "var"]]))]
generateFreeVariableFunction sname cons table accessVarTable =
  [([VarParam "c", generateFreeVariableConstructor cons],
    FnCall "nub" [
      FnCall "concat"
        [ListExpr (
          applyRulesIdentifiersFreeVariables
            sname
            rules
            (groupRulesByIden rules (dropFold folds ++ lists ++ listSorts))
            (dropFold folds)
            lists
            listSorts
            table
            accessVarTable
        )]
    ]
  )]
  where
    folds = getCtorFolds cons
    lists = getCtorLists cons
    listSorts = getCtorSorts cons
    rules = getCtorRules cons

generateFreeVariableConstructor :: ConstructorDef -> Parameter
generateFreeVariableConstructor (MkVarConstructor consName _) =
  ConstrParam (capitalize consName) [VarParam "var"]
generateFreeVariableConstructor cons =
  ConstrParam (capitalize consName) (firstToVarParams (dropFold folds ++ lists ++ listSorts) ++ [VarParam "_" | _ <- hTypes])
  -- ConstrParam (capitalize consName) ((map (\_ -> VarParam "b") (emptyOrToList (getCtorBindVarName cons))) ++ firstToVarParams (dropFold folds ++ lists ++ listSorts) ++ [VarParam "_" | _ <- hTypes])
  where
    consName = getName cons
    folds = getCtorFolds cons
    lists = getCtorLists cons
    listSorts = getCtorSorts cons
    hTypes = getCtorHTypes cons

applyRulesIdentifiersFreeVariables :: SortName -> [NamespaceRule] -> [(IdName, [NamespaceRule])] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> [Expression]
applyRulesIdentifiersFreeVariables _ _ [] _ _ _ _ _ = [ListExpr []]
applyRulesIdentifiersFreeVariables sname rules [(iden, idRules)] folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) = [FnCall ("freeVariables" ++ sortnameInUse) (addedBinders : [VarExpr (toLowerCaseFirst iden)])]
  | otherwise = [ListExpr []]
  where
    addedBinders = applyRuleInheritedNamespaces sname rules (iden, idRules) folds lists listSorts table (getSortInheritedInstances sortnameInUse table)
    sortnameInUse = getSortForId iden (lists ++ listSorts)
applyRulesIdentifiersFreeVariables sname rules ((iden, idRules):rest) folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (iden `elem` map fst folds) =
    FnCall "foldMap" [FnCall ("freeVariables" ++ sortnameInUse) [addedBinders], VarExpr (toLowerCaseFirst iden)]
    :
    applyRulesIdentifiersFreeVariables sname rules rest folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (iden `elem` map fst lists) =
    FnCall "concatMap" [FnCall ("freeVariables" ++ sortnameInUse) [addedBinders], VarExpr (toLowerCaseFirst iden)]
    :
    applyRulesIdentifiersFreeVariables sname rules rest folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) =
    FnCall ("freeVariables" ++ sortnameInUse) (addedBinders : [VarExpr (toLowerCaseFirst iden)])
    :
    applyRulesIdentifiersFreeVariables sname rules rest folds lists listSorts table accessVarTable
  | otherwise =
    applyRulesIdentifiersFreeVariables sname rules rest folds lists listSorts table accessVarTable
  where
    addedBinders = applyRuleInheritedNamespaces sname rules (iden, idRules) folds lists listSorts table (getSortInheritedInstances sortnameInUse table)
    sortnameInUse = getSortForId iden (folds ++ lists ++ listSorts)

getMappings :: Language -> [Function]
getMappings (_, sd, _, _) =
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
            getCtorParams c
          ,
            getExpr name c table accessVarTable
          )
        ) constr)
  ) filtered
  where
    sortMapName :: SortName -> String
    sortMapName sname = toLowerCaseFirst sname ++ "map"

    getCtorParams :: ConstructorDef -> [Parameter]
    getCtorParams (MkVarConstructor consName _) = [ConstrParam (capitalize consName) [VarParam "var"]]
    getCtorParams cons = [ConstrParam (capitalize consName) (firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
    -- getCtorParams cons = [ConstrParam (capitalize consName) ((map (\_ -> VarParam "b") (emptyOrToList (getCtorBindVarName cons))) ++ firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
      where
        consName = getName cons
        folds = getCtorFolds cons
        lists = getCtorLists cons
        sorts = getCtorSorts cons
        hTypes = getCtorHTypes cons

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

applyRuleInheritedNamespaces :: SortName -> [NamespaceRule] -> (IdName, [NamespaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance] -> Expression
applyRuleInheritedNamespaces sname rules (iden, rulesOfId) folds lists listSorts table = recurse
  where
    newString =
      applyTheRuleOneInheritedNamespace
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

    applyTheRuleOneInheritedNamespace :: SortName -> [NamespaceRule] -> (IdName, [NamespaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> NamespaceInstance -> Expression -> Maybe Expression
    applyTheRuleOneInheritedNamespace sname rules (_, rulesOfId) folds lists listSorts table currentinst param
      | isJust foundrule = applyOneRuleLogic sname currentinst newrules (fromJust foundrule) folds lists listSorts newtable [param]
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

    applyOneRuleLogic :: SortName -> NamespaceInstance -> [NamespaceRule] -> NamespaceRule -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [Expression] -> Maybe Expression
    applyOneRuleLogic _ _ _ (_, RightLHS _) _ _ _ _ _ = Nothing
    applyOneRuleLogic sname inst rules (l, RightAdd expr _) folds lists listSorts table params =
      return (ConstrInst ("S" ++ getInstanceNameSpace inst) (emptyOrToList (applyOneRuleLogic sname inst rules (l, expr) folds lists listSorts table []) ++ params))
      -- return (FnCall "insert" (VarExpr "b" : (emptyOrToList (applyOneRuleLogic sname inst rules (l, expr) folds lists listSorts table []) ++ params)))
    applyOneRuleLogic sname inst rules (_, RightSub iden context) folds lists listSorts table params
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
        nextStep = emptyOrToList (applyOneRuleLogic sname inst rules (fromJust newrule) folds lists listSorts table [])
