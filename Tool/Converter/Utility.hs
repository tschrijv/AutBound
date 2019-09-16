{-# OPTIONS_GHC -Wall #-}

module Converter.Utility where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility

calculateInheritedNameSpace :: SortName -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance]
calculateInheritedNameSpace sname table = [INH x y | INH x y <- inst]
  where
    inst = fromJust (lookup sname table)

lookupIdToSort :: IdName -> [(IdName, SortName)] -> SortName
lookupIdToSort iden table = fromJust (lookup iden table)

listToSpaceslower :: [(String, String)] -> [Parameter]
listToSpaceslower = map (VarParam . toLowerCaseFirst . fst)

foldToNormalList :: [(String, String, String)] -> [(String, String)]
foldToNormalList = map (\(a, b, _) -> (a, b))

applyRuleInheritedNamespaces :: SortName -> [NameSpaceRule] -> (IdName, [NameSpaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance] -> Expression
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

applyTheRuleOneInheritedNamespace :: SortName -> [NameSpaceRule] -> (IdName, [NameSpaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> NamespaceInstance -> Expression -> Maybe Expression
applyTheRuleOneInheritedNamespace sname rules (_, rulesOfId) folds lists listSorts table currentinst params
  | isJust foundrule =
    applyOneRuleLogic sname currentinst newrules (fromJust foundrule) folds lists listSorts newtable params
  | otherwise = Nothing
  where
    foundrule = find (\x -> getInstanceNamesOfRuleLeft (fst x) == getName currentinst) rulesOfId
    newtable = filterTableBySameNamespace currentinst table
    newrules = getNewRules rules sname table (folds ++ lists ++ listSorts)

    getNewRules :: [NameSpaceRule] -> SortName -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)] -> [NameSpaceRule]
    getNewRules rules sname table listSorts = filter (\(l, r) ->
        let sortnameId = getLeftIdSub l
            snameLookup = fromJust (lookup (capitalize sname) table)
            sortnameIdlookup = fromJust (lookup (lookupIdToSort sortnameId listSorts) table)
        in (sortnameId == "" && any (\x -> getInstanceNamesOfRuleLeft l == getName x) snameLookup)
        || any (\x -> getInstanceNamesOfRuleLeft l == getName x) sortnameIdlookup
      ) rules

applyOneRuleLogic :: SortName -> NamespaceInstance -> [NameSpaceRule] -> NameSpaceRule -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> Expression -> Maybe Expression
applyOneRuleLogic _ _ _ (_, RightLHS _) _ _ _ _ _ = Nothing
applyOneRuleLogic sname inst rules (l, RightAdd expr _) folds lists listSorts table params =
  return (ConstrInst ("S" ++ getNameInstancenamespace inst) (stepLogic sname inst rules (l, expr) folds lists listSorts table ++ [params]))
applyOneRuleLogic sname inst rules (_, RightSub iden context) folds lists listSorts table params
  | (elem iden (map fst lists) || elem iden (map fst folds)) && isJust newrule =
    return (FnCall ("generateHnat" ++ getNameInstancenamespace inst) (FnCall "length" (VarExpr iden : nextStep) : [params]))
  | elem iden (map fst lists) || elem iden (map fst folds) =
    return (FnCall ("generateHnat" ++ getNameInstancenamespace inst) [FnCall "length" [VarExpr iden], params])
  | isJust newrule =
    return (FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) ((VarExpr iden : nextStep) ++ [params]))
  | otherwise =
    return (FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) [VarExpr iden, params])
  where
    newrule = find (\(l, _) -> getLeftIdSub l == iden) rules
    nextStep = stepLogic sname inst rules (fromJust newrule) folds lists listSorts table

stepLogic :: SortName -> NamespaceInstance -> [NameSpaceRule] -> NameSpaceRule -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [Expression]
stepLogic _ _ _ (_, RightLHS _) _ _ _ _ = []
stepLogic sname inst rules (l, RightAdd expr _) folds lists listSorts table =
  [ConstrInst ("S" ++ getNameInstancenamespace inst) (stepLogic sname inst rules (l, expr) folds lists listSorts table)]
stepLogic sname inst rules (_, RightSub iden context) folds lists listSorts table
  | (elem iden (map fst lists) || elem iden (map fst folds)) && isJust newrule =
    [FnCall ("generateHnat" ++ getNameInstancenamespace inst) [FnCall "length" (VarExpr iden : nextStep)]]
  | elem iden (map fst lists) || elem iden (map fst folds) =
    [FnCall ("generateHnat" ++ getNameInstancenamespace inst) [FnCall "length" [VarExpr iden]]]
  | isJust newrule =
    [FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) (VarExpr iden : nextStep)]
  | otherwise =
    [FnCall ("addToEnvironment" ++ fromJust (lookup iden listSorts) ++ context) [VarExpr iden]]
  where
    newrule = find (\(l, _) -> getLeftIdSub l == iden) rules
    nextStep =
      stepLogic sname inst rules (fromJust newrule) folds lists listSorts table
