{-# OPTIONS_GHC -Wall #-}

module Converter.Substitutions (getSubst) where

import Data.Maybe

import Program
import GeneralTerms
import Utility

getSubst :: Language -> [Function]
getSubst (nsd, sd, _, _) = let accessVarTable = getVarAccessTable sd
  in getSubstHelpers sd accessVarTable ++ getSubstFunctions sd nsd accessVarTable

getSubstHelpers :: [SortDef] -> [(SortName, Bool)] -> [Function]
getSubstHelpers sd varAccessTable =
  let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) varAccessTable)) sd
  in concatMap (\(MkDefSort sname _ cdefs _) ->
    [
      Fn (toLowerCaseFirst sname ++ "SubstituteHelp")
      [
        (
          [VarParam "sub", VarParam "c", ConstrParam (capitalize consName) [VarParam "var"]],
          IfExpr
            (EQExpr (VarExpr "var") (VarExpr "c"))
            (FnCall (toLowerCaseFirst sname ++ "shiftplus") [VarExpr "c", VarExpr "sub"])
            (ConstrInst (capitalize consName) [VarExpr "var"])
        )
      ]
    | MkVarConstructor consName _ <- cdefs]
  ) filtered

getSubstFunctions :: [SortDef] -> [NameSpaceDef] -> [(SortName, Bool)] -> [Function]
getSubstFunctions sd nsd varAccessTable =
  let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup (capitalize sname) varAccessTable)) sd
  in concatMap (\(MkDefSort sname namespaceDecl _ bool) ->
    let filteredNs = [INH x y | INH x y <- namespaceDecl]
    in map (\inst -> namespaceInstanceSubstFunction sname inst namespaceDecl nsd bool) filteredNs
  ) filtered
  where
    namespaceInstanceSubstFunction :: SortName -> NamespaceInstance -> [NamespaceInstance] -> [NameSpaceDef] -> Bool -> Function
    namespaceInstanceSubstFunction sname (INH instname namespaceName) namespaceDecl defs bool =
      Fn
        (toLowerCaseFirst sname ++ secondSort ++ "Substitute")
        [
          (
            [VarParam "sub", VarParam "orig", VarParam "t"],
            if bool then FnCall ("rewrite" ++ sname) [mapCall] else mapCall
          )
        ]
      where
        secondSort = lookForSortName namespaceName defs
        mapCall = FnCall (toLowerCaseFirst sname ++ "map") (declarationsToFunctionsSubst (INH instname namespaceName) namespaceDecl defs ++ [VarExpr "orig", VarExpr "t"])

    declarationsToFunctionsSubst :: NamespaceInstance -> [NamespaceInstance] -> [NameSpaceDef] -> [Expression]
    declarationsToFunctionsSubst (INH instname1 namespaceName) nsi nsd =
      [
        if instname1 == instname2
          then FnCall (lookForSortName namespaceName nsd ++ "SubstituteHelp") [VarExpr "sub"]
          else LambdaExpr [VarParam "c", VarParam "x"] (VarExpr "x")
      | INH instname2 _ <- nsi]
