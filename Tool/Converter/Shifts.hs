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
    constructorsToCheckShift cdefs sname op = let filtered = [MkVarConstructor c i | MkVarConstructor c i <- cdefs]
      in map (\c -> constructorDefineCheckShift c sname op) filtered

    constructorDefineCheckShift :: ConstructorDef -> SortName -> String -> Function
    constructorDefineCheckShift (MkVarConstructor consName _) sname op =
      Fn (toLowerCaseFirst sname ++ "shiftHelp" ++ op)
        [
          ([VarParam "d", VarParam "c", ConstrParam (capitalize consName) [VarParam "hnat"]],
          IfExpr
            (GTEExpr (VarExpr "hnat") (VarExpr "c"))
            (ConstrInst (capitalize consName) [FnCall op [VarExpr "hnat", VarExpr "d"]])
            (ConstrInst (capitalize consName) [VarExpr "hnat"])
          )
        ]

-- generation of all shift functions
getShiftFunctions :: [SortDef] -> [NameSpaceDef] -> String -> [(SortName, Bool)] -> [Function]
getShiftFunctions sd defs opName varAccessTable = let filtered = filter (\s -> isJust (lookup (getName s) varAccessTable)) sd
  in map (\(MkDefSort sname namespaceDecl _ _) ->
    -- generateTypingshift s defs opName <>
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
    -- generateTypingshift :: SortDef -> [NameSpaceDef] -> String -> Doc String
    -- generateTypingshift (MkDefSort sname _ _ _) namespaces str =
    --   pretty (toLowerCaseFirst sname) <> pretty "shift" <> pretty str <+>
    --   pretty "::" <+>
    --   pretty "HNat ->" <+> sorttype <+> pretty "->" <+> sorttype <+> pretty "\n"
    --   where
    --     sorttype = pretty (capitalize sname)

    declarationsToFunctions :: [NamespaceInstance] -> [NameSpaceDef] -> String -> [Expression]
    declarationsToFunctions nsi nsd op = let filtered = [INH x y | INH x y <- nsi]
      in map (\(INH _ namespaceName) ->
        FnCall (lookForSortName namespaceName nsd ++ "shiftHelp" ++ op) [VarExpr "d"]
      ) filtered
