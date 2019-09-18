module Variable.String (getFunctions) where

import GeneralTerms
import Program
import Converter
import Variable.Common
import Utility

import Data.Maybe
import Data.List

getFunctions :: ConvertFunctions
getFunctions
  = VF {
    variableType = getVariableType,
    envType = getEnvType,
    userTypes = getTypes,
    variableInstances = getVariableInstances,
    variableFunctions = getVariableFunctions,
    envFunctions = getEnvFunctions
  }

getVariableType :: Language -> (Type, [Constructor])
getVariableType (nsd, _, _, _) = ("Variable", map (\ns -> Constr ('S' : nname ns) ["String"]) nsd)

getTypes :: Language -> [(Type, [Constructor])]
getTypes (_, sd, _, _) = map (
    \(MkDefSort name _ cds _) -> (name, map getConstr cds)
  ) sd where
    getConstr :: ConstructorDef -> Constructor
    getConstr (MkDefConstructor n lists listSorts folds _ hTypes) =
      Constr n (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes)
    getConstr (MkBindConstructor n lists listSorts folds (var, ns) _ hTypes) =
      Constr n ("Variable" : (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes))
    getConstr (MkVarConstructor n _) =
      Constr n ["Variable"]

getVariableInstances :: (Type, [Constructor]) -> [(Type, Type, [Function])]
getVariableInstances _ = []

getVariableFunctions :: Language -> (Type, [Constructor]) -> [Function]
getVariableFunctions lan _ = getMappings lan ef ++ getCustSubst lan ++ getFreeVar lan ef

_getCtorParams :: ConstructorDef -> [Parameter]
_getCtorParams (MkVarConstructor consName _) = [ConstrParam (capitalize consName) [VarParam "var"]]
_getCtorParams cons = [ConstrParam (capitalize consName) ((map (\_ -> VarParam "b") (emptyOrToList (getCtorBindVarName cons))) ++ firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
  where
    consName = getName cons
    folds = getCtorFolds cons
    lists = getCtorLists cons
    sorts = getCtorSorts cons
    hTypes = getCtorHTypes cons

_varCtorFreeVar :: String -> Expression
_varCtorFreeVar name = IfExpr (FnCall "elem" [VarExpr "var", VarExpr "c"]) (ListExpr []) (ListExpr [VarExpr "var"])

_oneDeeper namespace expr = expr -- FnCall "concat" [ListExpr (ListExpr [VarExpr "b"] : expr)]

_substExpr sname consName =
  IfExpr (EQExpr (VarExpr "var") (VarExpr "c"))
    (VarExpr "sub")
    (ConstrInst (capitalize consName) [VarExpr "var"])

ef = EF {
  getCtorParams = _getCtorParams,
  varCtorFreeVar = _varCtorFreeVar,
  oneDeeper = (\n e -> head e),
  substExpr = _substExpr,
  includeBinders = True
}

-- Custom subst
getCustSubst :: Language -> [Function]
getCustSubst (nsd, sd, _, _) =
  let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) (getVarAccessTable sd))) sd
  in concatMap (\(MkDefSort sname namespaceDecl constr rewrite) ->
    let filteredNs = [INH x y | INH x y <- namespaceDecl]
    in map (\ctx ->
      let secondSort = lookForSortName (cnamespace ctx) nsd
      in Fn
        (toLowerCaseFirst sname ++ secondSort ++ "Substitute")
        (map (\c ->
          (
            [VarParam "orig", VarParam "sub"] ++ getCtorParams ef c
          ,
            getExpr sname secondSort c (map getSortNameAndInstances sd) (getVarAccessTable sd)
          )
        ) constr)
    ) filteredNs
  ) filtered
  where
    getExpr :: SortName -> SortName -> ConstructorDef -> [(SortName, [Context])] -> [(SortName, Bool)] -> Expression
    getExpr sname secondSort (MkVarConstructor consName _) table _ =
      IfExpr (EQExpr (VarExpr "var") (VarExpr "orig"))
        (VarExpr "sub")
        (ConstrInst (capitalize consName) [VarExpr "var"])
    getExpr sname secondSort cons table accessVarTable =
      let binder = if isBind cons then [VarExpr "b"] else []
      in ConstrInst (capitalize (getName cons)) (binder ++ map process idRules ++ [VarExpr (toLowerCaseFirst x ++ show n) | (x, n) <- zip (getCtorHTypes cons) [1 :: Int ..]])
      where
        rules = getCtorRules cons
        idRules = groupRulesByIden rules (folds ++ lists ++ sorts)
        folds = dropFold (getCtorFolds cons)
        lists = getCtorLists cons
        sorts = getCtorSorts cons

        isBind MkBindConstructor{} = True
        isBind _                   = False

        process (iden, idenRules)
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst folds) =
            FnCall "fmap" [FnCall (toLowerCaseFirst sname ++ secondSort ++ "Substitute") (addedBinders), VarExpr (toLowerCaseFirst iden)]
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst lists) =
            FnCall "map" [FnCall (toLowerCaseFirst sname ++ secondSort ++ "Substitute") (addedBinders), VarExpr (toLowerCaseFirst iden)]
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst sorts) =
            FnCall (toLowerCaseFirst sname ++ secondSort ++ "Substitute") (addedBinders ++ [VarExpr (toLowerCaseFirst iden)])
          | otherwise = VarExpr (toLowerCaseFirst iden)
          where
            addedBinders =
              applyRuleInheritedNamespaces
                ef
                sname
                rules
                (iden, idenRules)
                folds
                lists
                sorts
                table
                (getSortInheritedInstances sortnameInUse table)
            sortnameInUse = getSortForId iden (folds ++ lists ++ sorts)

            applyRuleInheritedNamespaces :: ExternalFunctions -> SortName -> [AttributeDef] -> (IdenName, [AttributeDef]) -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(SortName, [Context])] -> [Context] -> [Expression]
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
                recurse :: [Context] -> [Expression]
                recurse [] = [VarExpr "orig", VarExpr "sub"]
                recurse (x:xs) = case newString x (recurse xs) of
                  Just ex -> ex
                  Nothing -> recurse xs

                applyTheRuleOneInheritedNamespace :: ExternalFunctions -> SortName -> [AttributeDef] -> (IdenName, [AttributeDef]) -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(SortName, [Context])] -> Context -> [Expression] -> Maybe [Expression]
                applyTheRuleOneInheritedNamespace ef sname rules (_, rulesOfId) folds lists listSorts table currentCtx params
                  | isJust foundrule = applyOneRuleLogic ef sname currentCtx newrules (fromJust foundrule) folds lists listSorts newtable params
                  | otherwise = Nothing
                  where
                    foundrule = find (\x -> linst (fst x) == cinst currentCtx) rulesOfId
                    newtable = filterContextsForSameNamespace currentCtx table
                    newrules = filter (\(l, r) ->
                        let sortnameId = liden l
                            snameLookup = fromJust (lookup (capitalize sname) table)
                            sortnameIdlookup = fromJust (lookup (getSortForId sortnameId (folds ++ lists ++ listSorts)) table)
                        in (sortnameId == "" && any (\ctx -> linst l == cinst ctx) snameLookup)
                        || any (\ctx -> linst l == cinst ctx) sortnameIdlookup
                      ) rules

                applyOneRuleLogic :: ExternalFunctions -> SortName -> Context -> [AttributeDef] -> AttributeDef -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(IdenName, SortName)] -> [(SortName, [Context])] -> [Expression] -> Maybe [Expression]
                applyOneRuleLogic _ _ _ _ (_, RightLHS _) _ _ _ _ _ = Nothing
                applyOneRuleLogic ef sname ctx rules (l, RightAdd expr _) folds lists listSorts table params =
                  return (fromMaybe [] (applyOneRuleLogic ef sname ctx rules (l, expr) folds lists listSorts table []) ++ params)
                applyOneRuleLogic ef sname ctx rules (_, RightSub iden context) folds lists listSorts table params
                  | (elem iden (map fst lists) || elem iden (map fst folds)) && isJust newrule =
                    return [FnCall ("generateHnat" ++ cnamespace ctx) (FnCall "length" (VarExpr iden : nextStep) : params)]
                  | elem iden (map fst lists) || elem iden (map fst folds) =
                    return [FnCall ("generateHnat" ++ cnamespace ctx) (FnCall "length" [VarExpr iden] : params)]
                  | isJust newrule =
                    return [FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) ((VarExpr iden : nextStep) ++ params)]
                  | otherwise =
                    return [FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) (VarExpr iden : params)]
                  where
                    newrule = find (\(l, _) -> liden l == iden) rules
                    nextStep = fromMaybe [] (applyOneRuleLogic ef sname ctx rules (fromJust newrule) folds lists listSorts table [])
