{-# OPTIONS_GHC -Wall #-}

module Converter.Mappings (getMappings) where

import Data.Maybe

import Abstract
import GeneralTerms
import Utility
import Converter.Utility

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
