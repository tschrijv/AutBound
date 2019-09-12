{-# OPTIONS_GHC -Wall #-}

module Converter.Substitutions (getSubst) where

import Abstract
import GeneralTerms
import Utility

getSubst :: Language -> [Function]
getSubst (nsd, sd, _, _) = let accessVarTable = getVarAccessTable sd
  in getSubstHelpers sd accessVarTable ++ getSubstFunctions sd nsd accessVarTable

getSubstHelpers :: [SortDef] -> [(SortName, Bool)] -> [Function]
getSubstHelpers sd varAccessTable =
  let filtered = filter (\(MkDefSort sname _ cdefs _) -> (lookup (capitalize sname) varAccessTable) /= Nothing) sd
  in concat $ map (\(MkDefSort sname _ cdefs _) ->
    let filteredCdefs = [MkVarConstructor x y | MkVarConstructor x y <- cdefs]
    in map (\c -> constructorDefineCheckSubst c sname) filteredCdefs
  ) sd
  where
    constructorDefineCheckSubst :: ConstructorDef -> SortName -> Function
    constructorDefineCheckSubst (MkVarConstructor consName _) sname =
      Fn ((toLowerCaseFirst sname) ++ "SubstituteHelp")
        [
          (
            [VarParam "sub", VarParam "c", ConstrParam (capitalize consName) [VarParam "hnat"]],
            IfExpr
              (EQExpr (VarExpr "hnat") (VarExpr "c"))
              (FnCall ((toLowerCaseFirst sname) ++ "shiftplus") [VarExpr "c", VarExpr "sub"])
              (ConstrInst (capitalize consName) [VarExpr "hnat"])
          )
        ]

getSubstFunctions :: [SortDef] -> [NameSpaceDef] -> [(SortName, Bool)] -> [Function]
getSubstFunctions sd defs varAccessTable =
  let filtered = filter (\(MkDefSort sname _ cdefs _) -> (lookup (capitalize sname) varAccessTable) /= Nothing) sd
  in concat $ map (\(MkDefSort sname namespaceDecl _ bool) ->
    let filteredNs = [INH x y | INH x y <- namespaceDecl]
    in map (\inst -> namespaceInstanceSubstFunction sname inst namespaceDecl defs bool) filteredNs
  ) filtered
  where
    namespaceInstanceSubstFunction :: SortName -> NamespaceInstance -> [NamespaceInstance] -> [NameSpaceDef] -> Bool -> Function
    namespaceInstanceSubstFunction sname (INH instname namespaceName) instances defs bool
      | bool =
        -- generateTypingsubst sname secondSort defs <>
        Fn
          (toLowerCaseFirst sname ++ secondSort ++ "Substitute")
          [
            (
              [VarParam "sub", VarParam "orig", VarParam "t"],
              FnCall ("rewrite" ++ sname) [
                FnCall (toLowerCaseFirst sname ++ "map") ((declarationsToFunctionsSubst (INH instname namespaceName) instances defs) ++ [VarExpr "orig", VarExpr "t"])
              ]
            )
          ]
      | otherwise =
        -- generateTypingsubst sname secondSort defs <>
        Fn
        (toLowerCaseFirst sname ++ secondSort ++ "Substitute")
        [
          (
            [VarParam "sub", VarParam "orig", VarParam "t"],
            FnCall (toLowerCaseFirst sname ++ "map") ((declarationsToFunctionsSubst (INH instname namespaceName) instances defs) ++ [VarExpr "orig", VarExpr "t"])
          )
        ]
      where
        secondSort = lookForSortName namespaceName defs

    -- generateTypingsubst :: SortName -> SortName -> [NameSpaceDef] -> Doc String
    -- generateTypingsubst snamefirst snamesecond namespaces =
    --   pretty ((toLowerCaseFirst snamefirst) ++ snamesecond) <> pretty "Substitute" <+>
    --   pretty "::" <+>
    --   pretty (capitalize snamesecond) <+>
    --   pretty "->HNat ->" <+> sorttype <+> pretty "->" <+> sorttype <+> pretty "\n"
    --   where
    --     sorttype = pretty (capitalize snamefirst)

    declarationsToFunctionsSubst :: NamespaceInstance -> [NamespaceInstance] -> [NameSpaceDef] -> [Expression]
    declarationsToFunctionsSubst (INH instname1 namespaceName) nsi defs =
      let filtered = [INH x y | INH x y <- nsi]
      in map (\(INH instname2 _) ->
        case instname1 == instname2 of
          True -> FnCall ((lookForSortName namespaceName defs) ++ "SubstituteHelp") [VarExpr "sub"]
          False -> VarExpr "id" -- TODO: substituted from: \c x->x
      ) filtered
