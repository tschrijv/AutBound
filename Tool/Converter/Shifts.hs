{-# OPTIONS_GHC -Wall #-}

module Converter.Shifts (getShift) where

import Data.Maybe

import Program
import GeneralTerms
import Utility

getShift :: Language -> [Function]
getShift (nsd, sd, _, _) = let accessVarTable = getVarAccessTable sd
  in concat [getShiftHelpers sd op accessVarTable ++ getShiftFunctions sd nsd op accessVarTable | op <- ["plus", "minus"]]

getShiftHelpers :: [SortDef] -> String -> [(SortName, Bool)] -> [Function]
getShiftHelpers sd opName varAccessTable = let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup sname varAccessTable)) sd
  in concatMap (\(MkDefSort sname _ cdefs _) -> constructorsToCheckShift cdefs sname opName) filtered
  where
    constructorsToCheckShift :: [ConstructorDef] -> SortName -> String -> [Function]
    constructorsToCheckShift cdefs sname op = [
      Fn (toLowerCaseFirst sname ++ "shiftHelp" ++ op)
      [
        ([VarParam "d", VarParam "c", ConstrParam (capitalize consName) [VarParam "var"]],
        IfExpr
          (GTEExpr (VarExpr "var") (VarExpr "c"))
          (ConstrInst (capitalize consName) [FnCall op [VarExpr "var", VarExpr "d"]])
          (ConstrInst (capitalize consName) [VarExpr "var"])
        )
      ] | MkVarConstructor consName _ <- cdefs]

getShiftFunctions :: [SortDef] -> [NameSpaceDef] -> String -> [(SortName, Bool)] -> [Function]
getShiftFunctions sd defs opName varAccessTable = let filtered = filter (\s -> isJust (lookup (getName s) varAccessTable)) sd
  in map (\(MkDefSort sname namespaceDecl _ _) ->
    Fn
      (toLowerCaseFirst sname ++ "shift" ++ opName)
      [
        ([VarParam "d", VarParam "t"],
        FnCall
          (toLowerCaseFirst sname ++ "map")
          (declarationsToFunctions namespaceDecl defs opName ++ [ConstrInst "Z" [], VarExpr "t"])
        )
      ]
  ) filtered
  where
    declarationsToFunctions :: [NamespaceInstance] -> [NameSpaceDef] -> String -> [Expression]
    declarationsToFunctions nsi nsd op = let filtered = [INH x y | INH x y <- nsi]
      in map (\(INH _ namespaceName) ->
        FnCall (lookForSortName namespaceName nsd ++ "shiftHelp" ++ op) [VarExpr "d"]
      ) filtered
