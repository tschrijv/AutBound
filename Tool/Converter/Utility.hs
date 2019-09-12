{-# OPTIONS_GHC -Wall #-}

module Converter.Utility where

import Data.List
import Data.Maybe

import Abstract
import GeneralTerms
import Utility

calculateInheritedNameSpace :: SortName -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance]
calculateInheritedNameSpace sname table = [INH x y | INH x y <- instances]
  where
    instances = fromJust (lookup sname table)

lookupIdToSort :: IdName -> [(IdName, SortName)] -> SortName
lookupIdToSort id table = fromJust (lookup id table)

listToSpaceslower :: [(String, String)] -> [Parameter]
listToSpaceslower list = map (VarParam . toLowerCaseFirst . fst) list

foldToNormalList :: [(String, String, String)] -> [(String, String)]
foldToNormalList foldsWithFoldName = map (\(a, b, c) -> (a, b)) foldsWithFoldName

applyRuleInheritedNamespaces :: SortName -> [NamespaceInstance] -> [NameSpaceRule] -> (IdName, [NameSpaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance] -> [Expression]
applyRuleInheritedNamespaces sname inst rules (id, rulesOfId) folds lists listSorts table ihns = recurse ihns
  where
    newString x params =
      applyTheRuleOneInheritedNamespace
        sname
        rules
        (id, rulesOfId)
        folds
        lists
        listSorts
        table
        x
        params
    recurse [] = [VarExpr "c"]
    recurse (x:xs) = case newString x (recurse xs) of
      Just x -> [x] -- TODO: do we need list return?
      Nothing -> recurse xs

applyTheRuleOneInheritedNamespace :: SortName -> [NameSpaceRule] -> (IdName, [NameSpaceRule]) -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> NamespaceInstance -> [Expression] -> Maybe (Expression)
applyTheRuleOneInheritedNamespace sname rules (id, rulesOfId) folds lists listSorts table currentinst params
  | isJust foundrule =
    applyOneRuleLogic sname currentinst newrules (fromJust foundrule) folds lists listSorts newtable params
  | otherwise = Nothing
  where
    foundrule = find (\x -> getInstanceNamesOfRuleLeft (fst x) == getName currentinst) rulesOfId
    newtable = filterTableBySameNamespace currentinst table
    newrules = getNewRules rules [] sname table (folds ++ lists ++ listSorts)

applyOneRuleLogic :: SortName -> NamespaceInstance -> [NameSpaceRule] -> NameSpaceRule -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [Expression] -> Maybe (Expression)
applyOneRuleLogic sname inst rules (l, RightLHS _) folds lists listSorts table params = Nothing
applyOneRuleLogic sname inst rules (l, RightAdd expr _) folds lists listSorts table params =
  return (ConstrInst ("S" ++ (getNameInstancenamespace inst)) ((stepLogic sname inst rules (l, expr) folds lists listSorts table) ++ params))
applyOneRuleLogic sname inst rules (l, RightSub id context) folds lists listSorts table params
  | (elem id (map fst lists) || elem id (map fst folds)) && (isJust newrule) =
    return (FnCall ("generateHnat" ++ (getNameInstancenamespace inst)) ((FnCall "length" (VarExpr id : nextStep)) : params)) -- TODO: is removing the $ fine?
  | (elem id (map fst lists) || elem id (map fst folds)) =
    return (FnCall ("generateHnat" ++ (getNameInstancenamespace inst)) ((FnCall "length" [VarExpr id]) : params))
  | (isJust newrule) =
    return (FnCall ("addToEnvironment" ++ fromJust (lookup id listSorts) ++ context) ((VarExpr id : nextStep) ++ params)) -- TODO: is removing the $ fine?
  | otherwise =
    return (FnCall ("addToEnvironment" ++ fromJust (lookup id listSorts) ++ context) ((VarExpr id) : params))
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
