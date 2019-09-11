{-# OPTIONS_GHC -Wall #-}

module Abstract where

import GeneralTerms
import Data.Maybe
import Data.List
import Utility

-- | Variable, function and constructor names
type Name = String
-- | Data types (including built-in and classes)
type Type = String
-- | Constructors are made up of a name and 0 or more type parameters
data Constructor = Constr Name [Type]
-- | Function parameters can be pure variables and pattern matches for constructors
data Parameter = VarParam Name | ConstrParam Name [Parameter] | StringParam String | IntParam Int
-- | Expressions in function bodies can be
-- function calls (function name + parameters)
-- or constructor calls (constructor name + parameters)
data Expression = FnCall Name [Expression] | ConstrInst Name [Expression] | VarExpr Name | Minus Expression Expression | IntExpr Int | StringExpr String
-- | Functions are made up of a name and multiple head (parameter list)
-- and body (expression) pairs
data Function = Fn Name [([Parameter], Expression)]

-- | A complete program consists of type declarations, type class instances,
-- and functions
data Program = P {
  imports :: [(String, [String])],
  types :: [(Type, [Constructor])],
  instances :: [(Type, Type, [Function])],
  functions :: [Function],
  code :: [String]
}

convert :: Language -> Program
convert lan@(nsd, sd, imp, cd) =
  let hnat = getHNatType nsd
      env  = getEnvType nsd
  in P {
    imports = imp,
    types = hnat : env : getTypes lan,
    instances = [getHNatOrd nsd hnat],
    functions = getHNatModifiers hnat ++ getGenerators nsd ++ getMappings lan,
    code = cd
  }

getTypes :: Language -> [(Type, [Constructor])]
getTypes (nsd, sd, imp, cd) = map (
    \(MkDefSort name _ cds _) -> (name, map getConstr cds)
  ) sd where
    getConstr :: ConstructorDef -> Constructor
    getConstr (MkDefConstructor n lists listSorts folds _ hTypes) =
      Constr n ((map (\(i, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds) ++ (map (\(_, t) -> "[" ++ t ++ "]") lists) ++ (map snd listSorts) ++ hTypes)
    getConstr (MkBindConstructor n lists listSorts folds _ _ hTypes) =
      Constr n ((map (\(i, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds) ++ (map (\(_, t) -> "[" ++ t ++ "]") lists) ++ (map snd listSorts) ++ hTypes)
    getConstr (MkVarConstructor n _) =
      Constr n ["HNat"]

getHNatType :: [NameSpaceDef] -> (Type, [Constructor])
getHNatType nsd = ("HNat", (Constr "Z" []) : map (\ns -> Constr ('S' : getName ns) ["HNat"]) nsd)

getEnvType :: [NameSpaceDef] -> (Type, [Constructor])
getEnvType nsd = ("Env", (Constr "Nil" []) : map (
    \(MkNameSpace ns _ inEnv) -> Constr ('E' : ns) (inEnv ++ ["Env"])
  ) nsd)

-- /////////////////////////////////////////////////////////////////////////////

getHNatOrd :: [NameSpaceDef] -> (Type, [Constructor]) -> (Type, Type, [Function])
getHNatOrd nsd (_, hnatc) = ("Ord", "HNat", [
    Fn "compare" ([
      ([ConstrParam "Z" [], ConstrParam "_" []], ConstrInst "LT" []),
      ([ConstrParam "Z" [], ConstrParam "Z" []], ConstrInst "EQ" []),
      ([ConstrParam "_" [], ConstrParam "Z" []], ConstrInst "GT" [])
    ] ++ (map generateCompare [(left, right) | left <- hnatc, right <- hnatc]))
  ]) where
    generateCompare :: (Constructor, Constructor) -> ([Parameter], Expression)
    generateCompare ((Constr n1 _), (Constr n2 _))
      | n1 == n2 = ([(ConstrParam n1 [(VarParam "h1")]), (ConstrParam n2 [(VarParam "h2")])], FnCall "compare" [(VarExpr "h1"), (VarExpr "h2")])
      | otherwise = ([(ConstrParam n1 [(VarParam "h1")]), (ConstrParam n2 [(VarParam "h2")])], FnCall "error" [StringExpr "differing namespace found in compare"])

-- /////////////////////////////////////////////////////////////////////////////

getHNatModifiers :: (Type, [Constructor]) -> [Function]
getHNatModifiers (_, hnatc) = [
    Fn "plus" ([
      ([ConstrParam "Z" [], VarParam "h"], VarExpr "h"),
      ([VarParam "h", ConstrParam "Z" []], VarExpr "h")
    ] ++ (map generatePlus hnatc))
  ,
    Fn "minus" ([
      ([ConstrParam "Z" [], ConstrParam "Z" []], ConstrInst "Z" []),
      ([ConstrParam "_" [], ConstrParam "Z" []], FnCall "error" [StringExpr "You cannot substract zero with a positive number"]),
      ([VarParam "result", ConstrParam "Z" []], VarExpr "result")
    ] ++ (map generateMinus [(left, right) | left <- hnatc, right <- hnatc]))
  ]
  where
    generatePlus :: Constructor -> ([Parameter], Expression)
    generatePlus (Constr n _) = ([VarParam "x1", ConstrParam n [VarParam "x2"]], ConstrInst n [FnCall "plus" [VarExpr "x1", VarExpr "x2"]])

    generateMinus :: (Constructor, Constructor) -> ([Parameter], Expression)
    generateMinus ((Constr n1 _), (Constr n2 _))
      | n1 == n2 = ([(ConstrParam n1 [(VarParam "h1")]), (ConstrParam n2 [(VarParam "h2")])], FnCall "minus" [(VarExpr "h1"), (VarExpr "h2")])
      | otherwise = ([(ConstrParam n1 [(VarParam "h1")]), (ConstrParam n2 [(VarParam "h2")])], FnCall "error" [StringExpr "differing namespace found in minus"])

getGenerators :: [NameSpaceDef] -> [Function]
getGenerators nsd = map (
    \ns ->
      let name = getName ns
          fnName = "generateHnat" ++ name
          constr = 'S' : name
      in
      Fn fnName [
        ([IntParam 0, VarParam "c"], VarExpr "c"),
        ([VarParam "n", VarParam "c"], ConstrInst constr [FnCall fnName [Minus (VarExpr "n") (IntExpr 1)], VarExpr "c"])
      ]
  ) nsd

-- /////////////////////////////////////////////////////////////////////////////

getMappings :: Language -> [Function]
getMappings (nsd, sd, _, _) =
  let filtered = filter (\(MkDefSort name inst constr _) -> lookup name (getVarAccessTable sd) /= Nothing) sd
      table = map getNameAndNSI sd
      accessVarTable = getVarAccessTable sd
  in map (
    \(MkDefSort name inst constr _) ->
        -- generateTypingmap name inst nsd <>
        Fn (sortMapName name)
        (map (\c ->
          (
            nsiParams inst ++
            [VarParam "c"] ++
            getMapParamConstr c
          ,
            getMapExpr name inst c table nsd accessVarTable
          )
        ) constr)
  ) filtered
  where
    -- generateTypingmap :: SortName -> [NamespaceInstance] -> [NameSpaceDef] -> Doc String
    -- generateTypingmap sname instances namespaces =
    --   pretty (toLowerCaseFirst sname) <> pretty "map" <+>
    --   pretty "::" <+>
    --   generateTypingInstancemap (filter isInh instances) namespaces <+>
    --   pretty "HNat ->" <+> sorttype <+> pretty "->" <+> sorttype <+> pretty "\n"
    --   where
    --     sorttype = pretty (capitalize sname)

    -- generateTypingInstancemap :: [NamespaceInstance] -> [NameSpaceDef] -> Doc String
    -- generateTypingInstancemap [] _ = pretty ""
    -- generateTypingInstancemap (INH _ namespaceName:rest) namespaces =
    --   pretty "(HNat->" <> sortType <+>
    --   pretty "->" <+>
    --   sortType <> pretty ")->" <+> generateTypingInstancemap rest namespaces
    --   where
    --     sortType = pretty (capitalize (lookForSortName namespaceName namespaces))

    getVarAccessTable :: [SortDef] -> [(SortName, Bool)]
    getVarAccessTable sList = map (sortCanAccessVariables sList []) sList

    getMapParamConstr :: ConstructorDef -> [Parameter]
    getMapParamConstr (MkVarConstructor consName _) = [ConstrParam (capitalize consName) [VarParam "hnat"]]
    getMapParamConstr cons = [ConstrParam (capitalize consName) (listToSpaceslower (foldToNormalList folds) ++ listToSpaceslower lists ++ listToSpaceslower listSorts ++ [VarParam (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1..]])]
      where
        consName = getName cons
        folds = getConstrFolds cons
        lists = getConstrLists cons
        listSorts = getConstrListSorts cons
        hTypes = getConstrHTypes cons

    getMapExpr :: SortName -> [NamespaceInstance] -> ConstructorDef -> [(SortName, [NamespaceInstance])] -> [NameSpaceDef] -> [(SortName, Bool)] -> Expression
    getMapExpr sname inst (MkVarConstructor consName contextName) table namespaces accessVarTable =
      FnCall ("on" ++ getNameInstancenamespace (head (fromJust (lookup (capitalize sname) table)))) [
        VarExpr "c",
        ConstrInst (capitalize consName) [VarExpr "hnat"]
      ]
    getMapExpr sname inst cons table namespaces accessVarTable =
      ConstrInst (capitalize consName) ((applyRulesIdentifiers
        sname
        inst
        rules
        (collectRulesAllField rules (foldToNormalList folds ++ lists ++ listSorts))
        (foldToNormalList folds)
        lists
        listSorts
        table
        accessVarTable) ++
        [VarExpr (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1..]])
      where
        consName = getName cons
        folds = getConstrFolds cons
        lists = getConstrLists cons
        listSorts = getConstrListSorts cons
        hTypes = getConstrHTypes cons
        rules = getConstrRules cons

    sortCanAccessVariables :: [SortDef] -> [SortName] -> SortDef -> (SortName, Bool)
    sortCanAccessVariables allSorts listVisited s
      | hasAccess = (sname, hasAccess)
      | otherwise = (sname, findPathToVariable)
      where
        sname = getName s
        hasAccess = fromJust (lookup sname (getTableOfHasVariable allSorts))
        sortDefTable = map (\x -> (getName x, x)) allSorts
        findPathToVariable =
          or
            (map
              (constructorCanAccessVariables sortDefTable listVisited)
              (getConstrDefs s))

        getTableOfHasVariable :: [SortDef] -> [(SortName, Bool)]
        getTableOfHasVariable sd = [(getName s, hasVariables s) | s <- sd]

        -- function generating for each Sort, if it has access to some variable
        hasVariables :: SortDef -> Bool
        hasVariables s = or [True | (MkVarConstructor _ _) <- getConstrDefs s]

        constructorCanAccessVariables :: [(SortName, SortDef)] -> [SortName] -> ConstructorDef -> Bool
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

        hasAccessSortName :: [(SortName, SortDef)] -> [SortName] -> SortName -> Bool
        hasAccessSortName table visited nextSort
          | any (\x -> x == nextSort) visited = False
          | otherwise =
            snd
              (sortCanAccessVariables
                (map snd table)
                (nextSort : visited)
                (fromJust (lookup nextSort table)))

    sortMapName :: SortName -> String
    sortMapName sname = toLowerCaseFirst sname ++ "map"

    nsiParams :: [NamespaceInstance] -> [Parameter]
    nsiParams inst = [VarParam ("on" ++ namespace) | INH _ namespace <- inst]

    nsiExprs :: [NamespaceInstance] -> [Expression]
    nsiExprs inst = [VarExpr ("on" ++ namespace) | INH _ namespace <- inst]

    listToSpaceslower :: [(String, String)] -> [Parameter]
    listToSpaceslower list = map (VarParam . toLowerCaseFirst . fst) list

    foldToNormalList :: [(String, String, String)] -> [(String, String)]
    foldToNormalList foldsWithFoldName = map (\(a, b, c) -> (a, b)) foldsWithFoldName

    getNameInstancenamespace :: NamespaceInstance -> NameSpaceName
    getNameInstancenamespace (INH _ name) = name
    getNameInstancenamespace (SYN _ name) = name

    --calculate the inherited namespace of an identifier and for every inherited namespace, check what happens
    applyRulesIdentifiers :: SortName -> [NamespaceInstance] -> [NameSpaceRule] -> [(IdName, [NameSpaceRule])] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> [Expression]
    applyRulesIdentifiers sname inst rules idRules folds lists listSorts table accessVarTable = map process idRules where
      process (id, idRules)
        | fromJust (lookup (capitalize sortnameInUse) accessVarTable) && elem id (map fst folds) =
          FnCall "fmap" [(FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders)), VarExpr (toLowerCaseFirst id)]
        | fromJust (lookup (capitalize sortnameInUse) accessVarTable) && elem id (map fst lists) =
          FnCall "map" [(FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders)), VarExpr (toLowerCaseFirst id)]
        | fromJust (lookup (capitalize sortnameInUse) accessVarTable) && elem id (map fst listSorts) =
          FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders ++ [VarExpr (toLowerCaseFirst id)])
        | otherwise = VarExpr (toLowerCaseFirst id)
        where
          addedBinders =
            applyRuleInheritedNamespaces
              sname
              inst
              rules
              (id, idRules)
              folds
              lists
              listSorts
              table
              (calculateInheritedNameSpace sortnameInUse table)
          sortnameInUse = (lookupIdToSort id (folds ++ lists ++ listSorts))

    applyRuleInheritedNamespaces :: SortName -> [NamespaceInstance] -> [NameSpaceRule] -> (IdName, [NameSpaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance] -> [Expression]
    applyRuleInheritedNamespaces sname inst rules (id, rulesOfId) folds lists listSorts table ihns = recurse filtered
      where
        filtered = filter (\x -> isJust (newString x)) ihns
        newString x =
          applyTheRuleOneInheritedNamespace
            sname
            rules
            (id, rulesOfId)
            folds
            lists
            listSorts
            table
            x
        recurse [] = [VarExpr "c"]
        recurse (x:xs) = fromJust (newString x) : recurse xs

    applyTheRuleOneInheritedNamespace :: SortName -> [NameSpaceRule] -> (IdName, [NameSpaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> NamespaceInstance -> Maybe (Expression)
    applyTheRuleOneInheritedNamespace sname rules (id, rulesOfId) folds lists listSorts table currentinst
      | isJust foundrule =
        applyOneRuleLogic sname currentinst newrules (fromJust foundrule) folds lists listSorts newtable
      | otherwise = Nothing
      where
        foundrule = find (\x -> getInstanceNamesOfRuleLeft (fst x) == getName currentinst) rulesOfId
        newtable = filterTableBySameNamespace currentinst table
        newrules = getNewRules rules [] sname table (folds ++ lists ++ listSorts)

    applyOneRuleLogic :: SortName -> NamespaceInstance -> [NameSpaceRule] -> NameSpaceRule -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> Maybe (Expression)
    applyOneRuleLogic sname inst rules (l, RightLHS _) folds lists listSorts table = Nothing
    applyOneRuleLogic sname inst rules (l, RightAdd expr _) folds lists listSorts table =
      return (ConstrInst ("S" ++ (getNameInstancenamespace inst)) (stepLogic sname inst rules (l, expr) folds lists listSorts table))
    applyOneRuleLogic sname inst rules (l, RightSub id context) folds lists listSorts table
      | (elem id (map fst lists) || elem id (map fst folds)) && (isJust newrule) =
        return (FnCall ("generateHnat" ++ (getNameInstancenamespace inst)) [FnCall "length" (VarExpr id : nextStep)]) -- TODO: is removing the $ fine?
      | (elem id (map fst lists) || elem id (map fst folds)) =
        return (FnCall ("generateHnat" ++ (getNameInstancenamespace inst)) [FnCall "length" [VarExpr id]])
      | (isJust newrule) =
        return (FnCall ("addToEnvironment" ++ fromJust (lookup id listSorts) ++ context) (VarExpr id : nextStep)) -- TODO: is removing the $ fine?
      | otherwise =
        return (FnCall ("addToEnvironment" ++ fromJust (lookup id listSorts) ++ context) [VarExpr id])
      where
        newrule = find (\(l, r) -> (getLeftIdSub l) == id) rules
        nextStep = stepLogic sname inst rules (fromJust newrule) folds lists listSorts table

    stepLogic :: SortName -> NamespaceInstance -> [NameSpaceRule] -> NameSpaceRule -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [Expression]
    stepLogic sname inst rules (l, RightLHS _) folds lists listSorts table = []
    stepLogic sname inst rules (l, RightAdd expr _) folds lists listSorts table =
      [(ConstrInst ("S" ++ (getNameInstancenamespace inst)) (stepLogic sname inst rules (l, expr) folds lists listSorts table))]
    stepLogic sname inst rules (l, RightSub id context) folds lists listSorts table
      | (elem id (map fst lists) || elem id (map fst folds)) && (isJust newrule) =
        [(FnCall ("generateHnat" ++ (getNameInstancenamespace inst)) [FnCall "length" ((VarExpr id) : nextStep)])]
      | (elem id (map fst lists) || elem id (map fst folds)) =
        [(FnCall ("generateHnat" ++ (getNameInstancenamespace inst)) [FnCall "length" [VarExpr id]])]
      | (isJust newrule) =
        [(FnCall ("addToEnvironment" ++ fromJust (lookup id listSorts) ++ context) ((VarExpr id) : nextStep))]
      | otherwise =
        [(FnCall ("addToEnvironment" ++ fromJust (lookup id listSorts) ++ context) [VarExpr id])]
      where
        newrule = find (\(l, r) -> (getLeftIdSub l) == id) rules
        nextStep =
          stepLogic sname inst rules (fromJust newrule) folds lists listSorts table

    getNewRules :: [NameSpaceRule] -> [NameSpaceRule] -> SortName -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)] -> [NameSpaceRule]
    getNewRules [] acc _ _ _ = acc
    getNewRules ((l, r):rest) acc sname table listSorts
      | sortnameId == "" && any (\x -> getInstanceNamesOfRuleLeft l == getName x) snameLookup =
        getNewRules rest ((l, r) : acc) sname table listSorts
      | any (\x -> getInstanceNamesOfRuleLeft l == getName x) sortnameIdlookup =
        getNewRules rest ((l, r) : acc) sname table listSorts
      | otherwise = getNewRules rest acc sname table listSorts
      where
        sortnameId = getLeftIdSub l
        snameLookup = fromJust (lookup (capitalize sname) table)
        sortnameIdlookup = fromJust (lookup (lookupIdToSort sortnameId listSorts) table)

    calculateInheritedNameSpace :: SortName -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance]
    calculateInheritedNameSpace sname table = [INH x y | INH x y <- instances]
      where
        instances = fromJust (lookup sname table)

    lookupIdToSort :: IdName -> [(IdName, SortName)] -> SortName
    lookupIdToSort id table = fromJust (lookup id table)

    filterTableBySameNamespace :: NamespaceInstance -> [(SortName, [NamespaceInstance])] -> [(SortName, [NamespaceInstance])]
    filterTableBySameNamespace inst table = map (filterTableBySameNamespaceSort (getNamespaceNameInstance inst)) table
      where
        filterTableBySameNamespaceSort :: NameSpaceName -> (SortName, [NamespaceInstance]) -> (SortName, [NamespaceInstance])
        filterTableBySameNamespaceSort namespacename (sname, list) = (sname, newlist)
          where
            newlist = filter (\x -> getNamespaceNameInstance x == namespacename) list
