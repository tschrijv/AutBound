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
      table = map getSortNameAndInstances sd
      accessVarTable = getVarAccessTable sd
  in map (
    \(MkDefSort name inst constr _) ->
        Fn (sortMapName name)
        (map (\c ->
          (
            [VarParam ("on" ++ namespace) | INH _ namespace <- inst] ++
            [VarParam "c"] ++
            getCtorParams c
          ,
            getExpr name c table accessVarTable
          )
        ) constr)
  ) filtered
  where
    sortMapName :: SortName -> String
    sortMapName sname = toLowerCaseFirst sname ++ "map"

    getCtorParams :: ConstructorDef -> [Parameter]
    getCtorParams (MkVarConstructor consName _) = [ConstrParam (capitalize consName) [VarParam "var"]]
    getCtorParams cons = [ConstrParam (capitalize consName) (firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
    -- getCtorParams cons = [ConstrParam (capitalize consName) ((map (\_ -> VarParam "b") (emptyOrToList (getCtorBindVarName cons))) ++ firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
      where
        consName = getName cons
        folds = getCtorFolds cons
        lists = getCtorLists cons
        sorts = getCtorSorts cons
        hTypes = getCtorHTypes cons

    getExpr :: SortName -> ConstructorDef -> [(SortName, [NamespaceInstance])] -> [(SortName, Bool)] -> Expression
    getExpr sname (MkVarConstructor consName _) table _ =
      FnCall ("on" ++ getInstanceNameSpace (head (fromJust (lookup sname table)))) [
        VarExpr "c",
        ConstrInst (capitalize consName) [VarExpr "var"]
      ]
    getExpr sname cons table accessVarTable =
      ConstrInst (capitalize (getName cons)) (map process idRules ++ [VarExpr (toLowerCaseFirst x ++ show n) | (x, n) <- zip (getCtorHTypes cons) [1 :: Int ..]])
      where
        rules = getCtorRules cons
        idRules = groupRulesByIden rules (folds ++ lists ++ sorts)
        folds = dropFold (getCtorFolds cons)
        lists = getCtorLists cons
        sorts = getCtorSorts cons

        process (iden, idenRules)
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst folds) =
            FnCall "fmap" [FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders), VarExpr (toLowerCaseFirst iden)]
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst lists) =
            FnCall "map" [FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders), VarExpr (toLowerCaseFirst iden)]
          | fromJust (lookup sortnameInUse accessVarTable) && elem iden (map fst sorts) =
            FnCall (sortMapName sortnameInUse) (nsiExprs (fromJust (lookup sortnameInUse table)) ++ addedBinders ++ [VarExpr (toLowerCaseFirst iden)])
          | otherwise = VarExpr (toLowerCaseFirst iden)
          where
            addedBinders =
              [applyRuleInheritedNamespaces
                sname
                rules
                (iden, idenRules)
                folds
                lists
                sorts
                table
                (getSortInheritedInstances sortnameInUse table)]
            sortnameInUse = getSortForId iden (folds ++ lists ++ sorts)

            nsiExprs :: [NamespaceInstance] -> [Expression]
            nsiExprs inst = [VarExpr ("on" ++ namespace) | INH _ namespace <- inst]
