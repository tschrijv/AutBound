{-# OPTIONS_GHC -Wall #-}

module Converter.Environments (getEnvFunctions) where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility
import Converter.Utility

getEnvFunctions :: Language -> [Function]
getEnvFunctions (nsd, sd, _, _) = let table = map getNameAndNSI sd
  in concatMap (\s ->
    let nsi = [SYN x y | SYN x y <- getNSI s]
    in if null nsi then [] else
    map (\c ->
      generateSortSynSystemOneConstructor (getName s) nsd table c (head nsi)
    ) (getConstrDefs s)
  ) sd

generateSortSynSystemOneConstructor :: SortName -> [NameSpaceDef] -> [(SortName, [NamespaceInstance])] -> ConstructorDef -> NamespaceInstance -> Function
generateSortSynSystemOneConstructor sname _ _ (MkVarConstructor consName _) _ =
  Fn ("addToEnvironment" ++ sname) [([ConstrParam (capitalize consName) [VarParam "var"], VarParam "c"], VarExpr "c")]
generateSortSynSystemOneConstructor sname namespaces table cons inst =
  Fn ("addToEnvironment" ++ sname ++ getName inst) [([ConstrParam (capitalize consName) (listToSpaceslower listSorts ++ [VarParam "_" | _ <- hTypes]), VarParam "c"], getEnvFunctionGenerate sname inst namespaces newtable listSorts rules)]
  where
    newtable = filterTableBySameNamespace inst table
    consName = getName cons
    listSorts = getConstrListSorts cons
    hTypes = getConstrHTypes cons
    rules = getConstrRules cons

getEnvFunctionGenerate :: SortName -> NamespaceInstance -> [NameSpaceDef] -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)]  -> [NameSpaceRule] -> Expression
getEnvFunctionGenerate sname inst namespaces table listSorts rules
  | null $ fromJust (lookup "lhs" allrules) = VarExpr "c"
  | otherwise = navigateRules sname inst namespaces table listSorts rules start
  where
    allrules = collectRulesSyn rules listSorts
    start = fromJust (
      find
        (\x -> getInstanceNamesOfRuleLeft (fst x) == getName inst)
        (fromJust (lookup "lhs" allrules))
      )

    collectRulesSyn :: [NameSpaceRule] -> [(IdName, SortName)] -> [(IdName, [NameSpaceRule])]
    collectRulesSyn rules ids =
      foldl
        (++)
        [("lhs", [(LeftLHS c, r) | (LeftLHS c, r) <- rules])]
        (map (\(iden, _) -> [collectRulesOfIdSyn rules iden]) ids)
      where
        collectRulesOfIdSyn :: [NameSpaceRule] -> IdName -> (IdName, [NameSpaceRule])
        collectRulesOfIdSyn nsr i = (i, filter (\(LeftSub fieldname _, RightSub _ _) -> fieldname == i) nsr)

navigateRules :: SortName -> NamespaceInstance -> [NameSpaceDef] -> [(SortName, [NamespaceInstance])] -> [(IdName, SortName)] -> [NameSpaceRule] -> NameSpaceRule -> Expression
navigateRules sname inst namespaces table listSorts rules (l, RightAdd expr _) =
  FnCall ("S" ++ getNameInstancenamespace inst) [navigateRules sname inst namespaces table listSorts rules (l, expr)]
navigateRules _ _ _ _ _ _ (LeftLHS _, RightLHS _) =
  VarExpr "c"
navigateRules sname inst namespaces table listSorts rules (LeftLHS _, RightSub iden _)
  | isJust newrule =
    FnCall functionName [VarExpr iden, navigateRules sname inst namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
  where
    newrule = find (\(l, _) -> getLeftIdSub l == iden) rules
    functionName = "addToEnvironment" ++ fromJust (lookup iden listSorts) ++ getName inst -- TODO: iden was included in function name with a space?? included here both, below once + twice!!
navigateRules _ _ _ _ _ _ (LeftSub _ _, RightLHS _) =
  VarExpr "c"
navigateRules sname inst namespaces table listSorts rules (LeftSub _ _, RightSub iden _)
  | isJust newrule =
    FnCall functionName [VarExpr iden, navigateRules sname inst namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
  where
    newrule = find (\(l, _) -> getLeftIdSub l == iden) rules
    functionName =
      "addToEnvironment" ++ fromJust (lookup iden listSorts) ++ getName inst
