{-# OPTIONS_GHC -Wall #-}

module Converter.Shifts (getShift) where

import Program
import GeneralTerms
import Utility

getShift :: Language -> [Function]
getShift (nsd, sd, _, _) = let accessVarTable = getVarAccessTable sd
  in concat $ [getShiftHelpers sd op accessVarTable nsd ++ getShiftFunctions sd nsd op accessVarTable | op <- ["plus", "minus"]]

getShiftHelpers :: [SortDef] -> String -> [(SortName, Bool)] -> [NameSpaceDef] -> [Function]
getShiftHelpers sd opName varAccessTable namespaces = let filtered = filter (\(MkDefSort sname inst cdefs _) -> (lookup sname varAccessTable) /= Nothing) sd
  in concat $ map (\(MkDefSort sname inst cdefs _) -> constructorsToCheckShift cdefs sname opName namespaces inst) filtered
  where
    constructorsToCheckShift :: [ConstructorDef] -> SortName -> String -> [NameSpaceDef] -> [NamespaceInstance] -> [Function]
    constructorsToCheckShift cdefs sname opName namespaces inst = let filtered = [MkVarConstructor c i | MkVarConstructor c i <- cdefs]
      in map (\c -> constructorDefineCheckShift c sname opName namespaces inst) filtered

    constructorDefineCheckShift :: ConstructorDef -> SortName -> String -> [NameSpaceDef] -> [NamespaceInstance] -> Function
    constructorDefineCheckShift (MkVarConstructor consName instname) sname opName namespaces inst =
      Fn ((toLowerCaseFirst sname) ++ "shiftHelp" ++ opName)
        [
          ([VarParam "d", VarParam "c", ConstrParam (capitalize consName) [VarParam "hnat"]],
          IfExpr
            (GTEExpr (VarExpr "hnat") (VarExpr "c"))
            (ConstrInst (capitalize consName) [FnCall opName [VarExpr "hnat", VarExpr "d"]])
            (ConstrInst (capitalize consName) [VarExpr "hnat"])
          )
        ]
      where
        instanceNamespace = lookforInstance inst (instname)
        newname = lookForSortName (instanceNamespace) namespaces

    lookforInstance :: [NamespaceInstance] -> String -> String
    lookforInstance ((INH ctxname namespacename):rest) instname
      | ctxname == instname = namespacename
      | otherwise = lookforInstance rest instname
    lookforInstance ((SYN ctxname namespacename):rest) instname =
      lookforInstance rest instname

-- generation of all shift functions
getShiftFunctions :: [SortDef] -> [NameSpaceDef] -> String -> [(SortName, Bool)] -> [Function]
getShiftFunctions sd defs opName varAccessTable = let filtered = filter (\s -> (lookup (getName s) varAccessTable) /= Nothing) sd
  in map (\(MkDefSort sname namespaceDecl _ _) ->
    -- generateTypingshift s defs opName <>
    Fn
      ((toLowerCaseFirst sname) ++ "shift" ++ opName)
      [
        ([VarParam "d", VarParam "t"],
        FnCall
          ((toLowerCaseFirst sname) ++ "map")
          ((declarationsToFunctions namespaceDecl defs opName) ++ ([ConstrInst "Z" [], VarExpr "t"]))
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
    declarationsToFunctions nsd defs opName = let filtered = [INH x y | INH x y <- nsd]
      in map (\(INH _ namespaceName) ->
        FnCall ((lookForSortName namespaceName defs) ++ "shiftHelp" ++ opName) [VarExpr "d"]
      ) filtered
