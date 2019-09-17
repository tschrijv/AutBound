{-# OPTIONS_GHC -Wall #-}

module Converter.Utility where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility

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
      | isJust foundrule =
        applyOneRuleLogic sname currentinst newrules (fromJust foundrule) folds lists listSorts newtable [param]
      | otherwise = Nothing
      where
        foundrule = find (\x -> getLeftSubInstanceName (fst x) == getName currentinst) rulesOfId
        newtable = filterTableBySameNamespace currentinst table
        newrules = getNewRules rules sname table (folds ++ lists ++ listSorts)

        getNewRules :: [NamespaceRule] -> SortName -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)] -> [NamespaceRule]
        getNewRules rules sname table listSorts = filter (\(l, r) ->
            let sortnameId = getLeftSubIden l
                snameLookup = fromJust (lookup (capitalize sname) table)
                sortnameIdlookup = fromJust (lookup (getSortForId sortnameId listSorts) table)
            in (sortnameId == "" && any (\x -> getLeftSubInstanceName l == getName x) snameLookup)
            || any (\x -> getLeftSubInstanceName l == getName x) sortnameIdlookup
          ) rules

    applyOneRuleLogic :: SortName -> NamespaceInstance -> [NamespaceRule] -> NamespaceRule -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [Expression] -> Maybe Expression
    applyOneRuleLogic _ _ _ (_, RightLHS _) _ _ _ _ _ = Nothing
    applyOneRuleLogic sname inst rules (l, RightAdd expr _) folds lists listSorts table params =
      return (ConstrInst ("S" ++ getInstanceNameSpace inst) (emptyOrToList (applyOneRuleLogic sname inst rules (l, expr) folds lists listSorts table []) ++ params))
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

    emptyOrToList :: Maybe Expression -> [Expression]
    emptyOrToList ex = maybe [] (\a -> [a]) ex
