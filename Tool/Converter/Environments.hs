{-# OPTIONS_GHC -Wall #-}

module Converter.Environments (getEnvFunctions) where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility
import Converter.Utility

-- generation for all syn contexts
getEnvFunctions :: Language -> [Function]
getEnvFunctions (nsd, sd, _, _) = let table = map getNameAndNSI sd
  in concat $ map (\s ->
    let nsi = [SYN x y | SYN x y <- (getNSI s)]
    in if nsi == [] then [] else
    -- generateTypingsyn sname (getName x) <>
    map (\c ->
      generateSortSynSystemOneConstructor (getName s) nsd table c (head nsi)
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
