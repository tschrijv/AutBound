{-# OPTIONS_GHC -Wall #-}

module Converter.FreeVariables (getFreeVar) where

import Data.Maybe

import Abstract
import GeneralTerms
import Utility
import Converter.Utility

--generate free variable functions
getFreeVar :: Language -> [Function]
getFreeVar (nsd, sd, _, _) =
  let table = map getNameAndNSI sd
      accessVarTable = getVarAccessTable sd
      filtered = filter (\(MkDefSort sname _ cdefs _) -> (lookup (capitalize sname) accessVarTable) /= Nothing) sd
  in concat $ map (\(MkDefSort sname inst cons _) ->
    -- generateTypingFreeVars sname <>
    map (\c ->
      generateFreeVariableFunction sname inst c table nsd accessVarTable
    ) cons
  ) filtered

-- generateTypingFreeVars :: SortName -> Doc String
-- generateTypingFreeVars sname =
--   pretty "freeVariables" <> pretty sname <+>
--   pretty "::" <+>
--   pretty "HNat -> " <+>
--   pretty (capitalize sname) <+> pretty " ->[HNat]" <+> pretty "\n"

generateFreeVariableFunction :: SortName -> [NamespaceInstance] -> ConstructorDef -> [(SortName, [NamespaceInstance])] -> [NameSpaceDef] -> [(SortName, Bool)] -> Function
generateFreeVariableFunction sname inst cons@(MkVarConstructor cname ctx) table namespaces accessVarTable =
  Fn ("freeVariables" ++ sname) [([VarParam "c", generateFreeVariableConstructor sname inst cons table], IfExpr (GTEExpr (VarExpr "hnat") (VarExpr "c")) (ListExpr [FnCall "minus" [VarExpr "hnat", VarExpr "c"]]) (ListExpr []))]
generateFreeVariableFunction sname inst cons table namespaces accessVarTable =
  Fn ("freeVariables" ++ sname) [([VarParam "c", generateFreeVariableConstructor sname inst cons table],
    FnCall "nub" [
      FnCall "concat" (
        [ListExpr (
          applyRulesIdentifiersFreeVariables
            sname
            inst
            rules
            (collectRulesAllField rules (foldToNormalList folds ++ lists ++ listSorts))
            (foldToNormalList folds)
            lists
            listSorts
            table
            accessVarTable
        )]
      )
    ]
  )]
  where
    consName = getName cons
    folds = getConstrFolds cons
    lists = getConstrLists cons
    listSorts = getConstrListSorts cons
    hTypes = getConstrHTypes cons
    rules = getConstrRules cons
generateFreeVariableConstructor :: SortName -> [NamespaceInstance] -> ConstructorDef -> [(SortName, [NamespaceInstance])] -> Parameter
generateFreeVariableConstructor sname inst (MkVarConstructor consName _) table =
  ConstrParam (capitalize consName) [VarParam "hnat"]
generateFreeVariableConstructor sname inst cons table =
  ConstrParam (capitalize consName) (listToSpaceslower (foldToNormalList folds ++ lists ++ listSorts) ++ [VarParam "_" | _ <- hTypes])
  where
    consName = getName cons
    folds = getConstrFolds cons
    lists = getConstrLists cons
    listSorts = getConstrListSorts cons
    hTypes = getConstrHTypes cons
    rules = getConstrRules cons

applyRulesIdentifiersFreeVariables :: SortName -> [NamespaceInstance] -> [NameSpaceRule] -> [(IdName, [NameSpaceRule])] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> [Expression]
applyRulesIdentifiersFreeVariables sname inst rules [] folds lists listSorts table accessVarTable = [ListExpr []]
applyRulesIdentifiersFreeVariables sname inst rules ((id, idRules):[]) folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) = [FnCall ("freeVariables" ++ sortnameInUse) (addedBinders ++ [VarExpr (toLowerCaseFirst id)])]
  | otherwise = [ListExpr []]
  where
    addedBinders = applyRuleInheritedNamespaces sname inst rules (id, idRules) folds lists listSorts table (calculateInheritedNameSpace sortnameInUse table)
    sortnameInUse = (lookupIdToSort id (lists ++ listSorts))
applyRulesIdentifiersFreeVariables sname inst rules ((id, idRules):rest) folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (elem id (map fst folds)) =
    FnCall "foldMap" [FnCall ("freeVariables" ++ sortnameInUse) addedBinders, VarExpr (toLowerCaseFirst id)]
    :
    applyRulesIdentifiersFreeVariables sname inst rules rest folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (elem id (map fst lists)) =
    FnCall "concatMap" [FnCall ("freeVariables" ++ sortnameInUse) addedBinders, VarExpr (toLowerCaseFirst id)]
    :
    applyRulesIdentifiersFreeVariables sname inst rules rest folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) =
    FnCall ("freeVariables" ++ sortnameInUse) (addedBinders ++ [VarExpr (toLowerCaseFirst id)])
    :
    applyRulesIdentifiersFreeVariables sname inst rules rest folds lists listSorts table accessVarTable
  | otherwise =
    applyRulesIdentifiersFreeVariables sname inst rules rest folds lists listSorts table accessVarTable
  where
    addedBinders = applyRuleInheritedNamespaces sname inst rules (id, idRules) folds lists listSorts table (calculateInheritedNameSpace sortnameInUse table)
    sortnameInUse = (lookupIdToSort id (folds ++ lists ++ listSorts))
