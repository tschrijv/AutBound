{-# OPTIONS_GHC -Wall #-}

module Converter.FreeVariables (getFreeVar) where

import Data.Maybe

import Program
import GeneralTerms
import Utility
import Converter.Utility

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
