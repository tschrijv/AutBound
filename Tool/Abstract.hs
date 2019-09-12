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
data Expression = FnCall Name [Expression] | ConstrInst Name [Expression] | VarExpr Name | Minus Expression Expression | IntExpr Int | StringExpr String | IfExpr Expression Expression Expression | GTEExpr Expression Expression | EQExpr Expression Expression
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
    functions = getHNatModifiers hnat ++
                getGenerators nsd ++
                getMappings lan ++
                getShift lan ++
                getSubst lan,
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

-- /////////////////////////////////////////////////////////////////////////////

getShift :: Language -> [Function]
getShift (nsd, sd, _, _) = let accessVarTable = getVarAccessTable sd
  in concat $ [getShiftHelpers sd op accessVarTable nsd ++ getShiftFunctions sd nsd op accessVarTable | op <- ["plus", "minus"]]

getShiftHelpers :: [SortDef] -> String -> [(SortName, Bool)] -> [NameSpaceDef] -> [Function]
getShiftHelpers sd opName varAccessTable namespaces = let filtered = filter (\(MkDefSort sname inst cdefs _) -> (lookup sname varAccessTable) /= Nothing) sd
  in concat $ map (\(MkDefSort sname inst cdefs _) -> constructorsToCheckShift cdefs sname opName namespaces inst) filtered
  where
    constructorsToCheckShift :: [ConstructorDef] -> SortName -> String -> [NameSpaceDef] -> [NamespaceInstance] -> [Function]
    constructorsToCheckShift cdefs sname opName namespaces inst = let filtered = [MkVarConstructor c i | MkVarConstructor c i <- cdefs]
      in map (\c -> constructorDefineCheckShift c sname opName namespaces inst) filtered

    constructorDefineCheckShift :: ConstructorDef -> SortName -> String -> [NameSpaceDef] -> [NamespaceInstance] -> Function
    constructorDefineCheckShift (MkVarConstructor consName instname) sname opName namespaces inst =
      Fn ((toLowerCaseFirst sname) ++ "shiftHelp" ++ opName)
        [
          ([VarParam "d", VarParam "c", ConstrParam (capitalize consName) [VarParam "hnat"]],
          IfExpr
            (GTEExpr (VarExpr "hnat") (VarExpr "c"))
            (ConstrInst (capitalize consName) [FnCall opName [VarExpr "hnat", VarExpr "d"]])
            (ConstrInst (capitalize consName) [VarExpr "hnat"])
          )
        ]
      where
        instanceNamespace = lookforInstance inst (instname)
        newname = lookForSortName (instanceNamespace) namespaces

    lookforInstance :: [NamespaceInstance] -> String -> String
    lookforInstance ((INH ctxname namespacename):rest) instname
      | ctxname == instname = namespacename
      | otherwise = lookforInstance rest instname
    lookforInstance ((SYN ctxname namespacename):rest) instname =
      lookforInstance rest instname

-- generation of all shift functions
getShiftFunctions :: [SortDef] -> [NameSpaceDef] -> String -> [(SortName, Bool)] -> [Function]
getShiftFunctions sd defs opName varAccessTable = let filtered = filter (\s -> (lookup (getName s) varAccessTable) /= Nothing) sd
  in map (\(MkDefSort sname namespaceDecl _ _) ->
    -- generateTypingshift s defs opName <>
    Fn
      ((toLowerCaseFirst sname) ++ "shift" ++ opName)
      [
        ([VarParam "d", VarParam "t"],
        FnCall
          ((toLowerCaseFirst sname) ++ "map")
          ((declarationsToFunctions namespaceDecl defs opName) ++ ([ConstrInst "Z" [], VarExpr "t"]))
        )
      ]
  ) filtered
  where
    -- generateTypingshift :: SortDef -> [NameSpaceDef] -> String -> Doc String
    -- generateTypingshift (MkDefSort sname _ _ _) namespaces str =
    --   pretty (toLowerCaseFirst sname) <> pretty "shift" <> pretty str <+>
    --   pretty "::" <+>
    --   pretty "HNat ->" <+> sorttype <+> pretty "->" <+> sorttype <+> pretty "\n"
    --   where
    --     sorttype = pretty (capitalize sname)

    declarationsToFunctions :: [NamespaceInstance] -> [NameSpaceDef] -> String -> [Expression]
    declarationsToFunctions nsd defs opName = let filtered = [INH x y | INH x y <- nsd]
      in map (\(INH _ namespaceName) ->
        FnCall ((lookForSortName namespaceName defs) ++ "shiftHelp" ++ opName) [VarExpr "d"]
      ) filtered

-- /////////////////////////////////////////////////////////////////////////////

getSubst :: Language -> [Function]
getSubst (nsd, sd, _, _) = let accessVarTable = getVarAccessTable sd
  in getSubstHelpers sd accessVarTable ++ getSubstFunctions sd nsd accessVarTable

getSubstHelpers :: [SortDef] -> [(SortName, Bool)] -> [Function]
getSubstHelpers sd varAccessTable =
  let filtered = filter (\(MkDefSort sname _ cdefs _) -> (lookup (capitalize sname) varAccessTable) /= Nothing) sd
  in concat $ map (\(MkDefSort sname _ cdefs _) ->
    let filteredCdefs = [MkVarConstructor x y | MkVarConstructor x y <- cdefs]
    in map (\c -> constructorDefineCheckSubst c sname) filteredCdefs
  ) sd
  where
    constructorDefineCheckSubst :: ConstructorDef -> SortName -> Function
    constructorDefineCheckSubst (MkVarConstructor consName _) sname =
      Fn ((toLowerCaseFirst sname) ++ "SubstituteHelp")
        [
          (
            [VarParam "sub", VarParam "c", ConstrParam (capitalize consName) [VarParam "hnat"]],
            IfExpr
              (EQExpr (VarExpr "hnat") (VarExpr "c"))
              (FnCall ((toLowerCaseFirst sname) ++ "shiftplus") [VarExpr "c", VarExpr "sub"])
              (ConstrInst (capitalize consName) [VarExpr "hnat"])
          )
        ]

getSubstFunctions :: [SortDef] -> [NameSpaceDef] -> [(SortName, Bool)] -> [Function]
getSubstFunctions sd defs varAccessTable =
  let filtered = filter (\(MkDefSort sname _ cdefs _) -> (lookup (capitalize sname) varAccessTable) /= Nothing) sd
  in concat $ map (\(MkDefSort sname namespaceDecl _ bool) ->
    let filteredNs = [INH x y | INH x y <- namespaceDecl]
    in map (\inst -> namespaceInstanceSubstFunction sname inst namespaceDecl defs bool) filteredNs
  ) filtered
  where
    namespaceInstanceSubstFunction :: SortName -> NamespaceInstance -> [NamespaceInstance] -> [NameSpaceDef] -> Bool -> Function
    namespaceInstanceSubstFunction sname (INH instname namespaceName) instances defs bool
      | bool =
        -- generateTypingsubst sname secondSort defs <>
        Fn
          (toLowerCaseFirst sname ++ secondSort ++ "Substitute")
          [
            (
              [VarParam "sub", VarParam "orig", VarParam "t"],
              FnCall ("rewrite" ++ sname) [
                FnCall (toLowerCaseFirst sname ++ "map") ((declarationsToFunctionsSubst (INH instname namespaceName) instances defs) ++ [VarExpr "orig", VarExpr "t"])
              ]
            )
          ]
      | otherwise =
        -- generateTypingsubst sname secondSort defs <>
        Fn
        (toLowerCaseFirst sname ++ secondSort ++ "Substitute")
        [
          (
            [VarParam "sub", VarParam "orig", VarParam "t"],
            FnCall (toLowerCaseFirst sname ++ "map") ((declarationsToFunctionsSubst (INH instname namespaceName) instances defs) ++ [VarExpr "orig", VarExpr "t"])
          )
        ]
      where
        secondSort = lookForSortName namespaceName defs

    -- generateTypingsubst :: SortName -> SortName -> [NameSpaceDef] -> Doc String
    -- generateTypingsubst snamefirst snamesecond namespaces =
    --   pretty ((toLowerCaseFirst snamefirst) ++ snamesecond) <> pretty "Substitute" <+>
    --   pretty "::" <+>
    --   pretty (capitalize snamesecond) <+>
    --   pretty "->HNat ->" <+> sorttype <+> pretty "->" <+> sorttype <+> pretty "\n"
    --   where
    --     sorttype = pretty (capitalize snamefirst)

    declarationsToFunctionsSubst :: NamespaceInstance -> [NamespaceInstance] -> [NameSpaceDef] -> [Expression]
    declarationsToFunctionsSubst (INH instname1 namespaceName) nsi defs =
      let filtered = [INH x y | INH x y <- nsi]
      in map (\(INH instname2 _) ->
        case instname1 == instname2 of
          True -> FnCall ((lookForSortName namespaceName defs) ++ "SubstituteHelp") [VarExpr "sub"]
          False -> VarExpr "id" -- TODO: substituted from: \c x->x
      ) filtered

-- /////////////////////////////////////////////////////////////////////////////

-- generation for all syn contexts
getEnvFunctions :: Language -> [Function]
getEnvFunctions (nsd, sd, _, _) = let table = map getNameAndNSI sd
  in concat $ map (\s ->
    -- generateTypingsyn sname (getName x) <>
    map (\c ->
      generateSortSynSystemOneConstructor (getName s) nsd table c (head ([SYN x y | SYN x y <- (getNSI s)]))
    ) (getConstrDefs s)
  ) sd

-- generateTypingsyn :: SortName -> InstanceName -> Doc String
-- generateTypingsyn sname instname =
--   pretty "addToEnvironment" <> pretty sname <> pretty instname <+>
--   pretty "::" <+>
--   pretty (capitalize sname) <+> pretty "->HNat -> HNat" <+> pretty "\n"

generateSortSynSystemOneConstructor :: SortName -> [NameSpaceDef] -> [(SortName, [NamespaceInstance])] -> ConstructorDef -> NamespaceInstance -> Function
generateSortSynSystemOneConstructor sname namespaces table (MkVarConstructor consName _) inst =
  Fn ("addToEnvironment" ++ sname) [([ConstrParam (capitalize consName) [VarParam "hnat"], VarParam "c"], VarExpr "c")]
generateSortSynSystemOneConstructor sname namespaces table cons inst =
  Fn ("addToEnvironment" ++ sname ++ (getName inst)) [([ConstrParam (capitalize consName) (listToSpaceslower listSorts ++ [VarParam "_" | _ <- hTypes]), VarParam "c"], getEnvFunctionGenerate sname inst namespaces newtable listSorts rules)]
  where
    newtable = filterTableBySameNamespace inst table
    consName = getName cons
    folds = getConstrFolds cons
    lists = getConstrLists cons
    listSorts = getConstrListSorts cons
    hTypes = getConstrHTypes cons
    rules = getConstrRules cons

    listToSpaceslower :: [(String, String)] -> [Parameter]
    listToSpaceslower list = map (VarParam . toLowerCaseFirst . fst) list

--after = part logic of the syn functions
getEnvFunctionGenerate :: SortName -> NamespaceInstance -> [NameSpaceDef] -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)]  -> [NameSpaceRule] -> Expression
getEnvFunctionGenerate sname inst namespaces table listSorts rules
  | fromJust (lookup "lhs" allrules) == [] = VarExpr "c"
  | otherwise = navigateRules sname inst namespaces table listSorts rules start
  where
    allrules = (collectRulesSyn rules listSorts)
    start = fromJust (
      find
        (\x -> getInstanceNamesOfRuleLeft (fst x) == getName inst)
        (fromJust (lookup "lhs" allrules))
      )

navigateRules :: SortName -> NamespaceInstance -> [NameSpaceDef] -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)] -> [NameSpaceRule] -> NameSpaceRule -> Expression
navigateRules sname inst namespaces table listSorts rules (l, RightAdd expr _) =
  FnCall ("S" ++ (getNameInstancenamespace inst)) [navigateRules sname inst namespaces table listSorts rules (l, expr)]
navigateRules sname inst namespaces table listSorts rules (LeftLHS _, RightLHS _) =
  VarExpr "c"
navigateRules sname inst namespaces table listSorts rules (LeftLHS _, RightSub id _)
  | isJust newrule =
    FnCall functionName [VarExpr id, navigateRules sname inst namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr id, VarExpr "c"]
  where
    newrule = find (\(l, r) -> (getLeftIdSub l) == id) rules
    functionName = "addToEnvironment" ++ fromJust (lookup id listSorts) ++ (getName inst) -- TODO: id was included in function name with a space?? included here both, below once + twice!!
navigateRules sname inst namespaces table listSorts rules (LeftSub _ _, RightLHS _) =
  VarExpr "c"
navigateRules sname inst namespaces table listSorts rules (LeftSub _ _, RightSub id _)
  | isJust newrule =
    FnCall functionName [VarExpr id, navigateRules sname inst namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr id, VarExpr "c"]
  where
    newrule = find (\(l, r) -> (getLeftIdSub l) == id) rules
    functionName =
      "addToEnvironment" ++ fromJust (lookup id listSorts) ++ (getName inst)
