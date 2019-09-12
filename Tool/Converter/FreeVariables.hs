{-# OPTIONS_GHC -Wall #-}

module Converter.FreeVariables (getFreeVar) where

import Data.Maybe

import Program
import GeneralTerms
import Utility
import Converter.Utility

--generate free variable functions
getFreeVar :: Language -> [Function]
getFreeVar (_, sd, _, _) =
  let table = map getNameAndNSI sd
      accessVarTable = getVarAccessTable sd
      filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) accessVarTable)) sd
  in concatMap (\(MkDefSort sname _ cons _) ->
    -- generateTypingFreeVars sname <>
    map (\c ->
      generateFreeVariableFunction sname c table accessVarTable
    ) cons
  ) filtered

-- generateTypingFreeVars :: SortName -> Doc String
-- generateTypingFreeVars sname =
--   pretty "freeVariables" <> pretty sname <+>
--   pretty "::" <+>
--   pretty "HNat -> " <+>
--   pretty (capitalize sname) <+> pretty " ->[HNat]" <+> pretty "\n"

generateFreeVariableFunction :: SortName -> ConstructorDef -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> Function
generateFreeVariableFunction sname cons@(MkVarConstructor _ _) _ _ =
  Fn ("freeVariables" ++ sname) [([VarParam "c", generateFreeVariableConstructor cons], IfExpr (GTEExpr (VarExpr "hnat") (VarExpr "c")) (ListExpr [FnCall "minus" [VarExpr "hnat", VarExpr "c"]]) (ListExpr []))]
generateFreeVariableFunction sname cons table accessVarTable =
  Fn ("freeVariables" ++ sname) [([VarParam "c", generateFreeVariableConstructor cons],
    FnCall "nub" [
      FnCall "concat"
        [ListExpr (
          applyRulesIdentifiersFreeVariables
            sname
            rules
            (collectRulesAllField rules (foldToNormalList folds ++ lists ++ listSorts))
            (foldToNormalList folds)
            lists
            listSorts
            table
            accessVarTable
        )]
    ]
  )]
  where
    folds = getConstrFolds cons
    lists = getConstrLists cons
    listSorts = getConstrListSorts cons
    rules = getConstrRules cons
generateFreeVariableConstructor :: ConstructorDef -> Parameter
generateFreeVariableConstructor (MkVarConstructor consName _) =
  ConstrParam (capitalize consName) [VarParam "hnat"]
generateFreeVariableConstructor cons =
  ConstrParam (capitalize consName) (listToSpaceslower (foldToNormalList folds ++ lists ++ listSorts) ++ [VarParam "_" | _ <- hTypes])
  where
    consName = getName cons
    folds = getConstrFolds cons
    lists = getConstrLists cons
    listSorts = getConstrListSorts cons
    hTypes = getConstrHTypes cons

applyRulesIdentifiersFreeVariables :: SortName -> [NameSpaceRule] -> [(IdName, [NameSpaceRule])] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> [Expression]
applyRulesIdentifiersFreeVariables _ _ [] _ _ _ _ _ = [ListExpr []]
applyRulesIdentifiersFreeVariables sname rules [(iden, idRules)] folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) = [FnCall ("freeVariables" ++ sortnameInUse) (addedBinders ++ [VarExpr (toLowerCaseFirst iden)])]
  | otherwise = [ListExpr []]
  where
    addedBinders = applyRuleInheritedNamespaces sname rules (iden, idRules) folds lists listSorts table (calculateInheritedNameSpace sortnameInUse table)
    sortnameInUse = lookupIdToSort iden (lists ++ listSorts)
applyRulesIdentifiersFreeVariables sname rules ((iden, idRules):rest) folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (iden `elem` map fst folds) =
    FnCall "foldMap" [FnCall ("freeVariables" ++ sortnameInUse) addedBinders, VarExpr (toLowerCaseFirst iden)]
    :
    applyRulesIdentifiersFreeVariables sname rules rest folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (iden `elem` map fst lists) =
    FnCall "concatMap" [FnCall ("freeVariables" ++ sortnameInUse) addedBinders, VarExpr (toLowerCaseFirst iden)]
    :
    applyRulesIdentifiersFreeVariables sname rules rest folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) =
    FnCall ("freeVariables" ++ sortnameInUse) (addedBinders ++ [VarExpr (toLowerCaseFirst iden)])
    :
    applyRulesIdentifiersFreeVariables sname rules rest folds lists listSorts table accessVarTable
  | otherwise =
    applyRulesIdentifiersFreeVariables sname rules rest folds lists listSorts table accessVarTable
  where
    addedBinders = applyRuleInheritedNamespaces sname rules (iden, idRules) folds lists listSorts table (calculateInheritedNameSpace sortnameInUse table)
    sortnameInUse = lookupIdToSort iden (folds ++ lists ++ listSorts)
