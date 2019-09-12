{-# OPTIONS_GHC -Wall #-}

module Converter.Mappings (getMappings) where

import Data.Maybe

import Program
import GeneralTerms
import Utility
import Converter.Utility

getMappings :: Language -> [Function]
getMappings (_, sd, _, _) =
  let filtered = filter (\(MkDefSort name _ _ _) -> isJust (lookup name (getVarAccessTable sd))) sd
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
            getMapExpr name c table accessVarTable
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
    getMapParamConstr cons = [ConstrParam (capitalize consName) (listToSpaceslower (foldToNormalList folds) ++ listToSpaceslower lists ++ listToSpaceslower listSorts ++ [VarParam (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
      where
        consName = getName cons
        folds = getConstrFolds cons
        lists = getConstrLists cons
        listSorts = getConstrListSorts cons
        hTypes = getConstrHTypes cons

    getMapExpr :: SortName -> ConstructorDef -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> Expression
    getMapExpr sname (MkVarConstructor consName _) table _ =
      FnCall ("on" ++ getNameInstancenamespace (head (fromJust (lookup (capitalize sname) table)))) [
        VarExpr "c",
        ConstrInst (capitalize consName) [VarExpr "hnat"]
      ]
    getMapExpr sname cons table accessVarTable =
      ConstrInst (capitalize consName) (applyRulesIdentifiers
        sname
        rules
        (collectRulesAllField rules (foldToNormalList folds ++ lists ++ listSorts))
        (foldToNormalList folds)
        lists
        listSorts
        table
        accessVarTable ++
        [VarExpr (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])
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
    applyRulesIdentifiers :: SortName -> [NameSpaceRule] -> [(IdName, [NameSpaceRule])] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(IdName, SortName)] -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> [Expression]
    applyRulesIdentifiers sname rules idRules folds lists listSorts table accessVarTable = map process idRules where
      process (iden, idr)
        | fromJust (lookup (capitalize sortnameInUse) accessVarTable) && elem iden (map fst folds) =
          FnCall "fmap" [FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders), VarExpr (toLowerCaseFirst iden)]
        | fromJust (lookup (capitalize sortnameInUse) accessVarTable) && elem iden (map fst lists) =
          FnCall "map" [FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders), VarExpr (toLowerCaseFirst iden)]
        | fromJust (lookup (capitalize sortnameInUse) accessVarTable) && elem iden (map fst listSorts) =
          FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders ++ [VarExpr (toLowerCaseFirst iden)])
        | otherwise = VarExpr (toLowerCaseFirst iden)
        where
          addedBinders =
            applyRuleInheritedNamespaces
              sname
              rules
              (iden, idr)
              folds
              lists
              listSorts
              table
              (calculateInheritedNameSpace sortnameInUse table)
          sortnameInUse = lookupIdToSort iden (folds ++ lists ++ listSorts)
