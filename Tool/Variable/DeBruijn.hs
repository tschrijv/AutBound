module Variable.DeBruijn where

import Data.List
import Data.Maybe

import GeneralTerms
import Program
import Utility

getVariableType :: [NamespaceDef] -> (Type, [Constructor])
getVariableType nsd = ("Variable", Constr "Z" [] : map (\ns -> Constr ('S' : getName ns) ["Variable"]) nsd)

getVariableInstances :: (Type, [Constructor]) -> [(Type, Type, [Function])]
getVariableInstances (_, hnatc) =
  let cs = delete (Constr "Z" []) hnatc
  in [("Ord", "Variable", [
    Fn "compare" ([
      ([ConstrParam "Z" [], ConstrParam "Z" []], ConstrInst "EQ" []),
      ([ConstrParam "Z" [], VarParam "_"], ConstrInst "LT" []),
      ([VarParam "_", ConstrParam "Z" []], ConstrInst "GT" [])
    ] ++ map generateCompare [(left, right) | left <- cs, right <- cs])
  ])] where
    generateCompare :: (Constructor, Constructor) -> ([Parameter], Expression)
    generateCompare (Constr n1 _, Constr n2 _)
      | n1 == n2 = ([ConstrParam n1 [VarParam "h1"], ConstrParam n2 [VarParam "h2"]], FnCall "compare" [VarExpr "h1", VarExpr "h2"])
      | otherwise = ([ConstrParam n1 [VarParam "h1"], ConstrParam n2 [VarParam "h2"]], FnCall "error" [StringExpr "differing namespace found in compare"])

getVariableFunctions :: Language -> (Type, [Constructor]) -> [Function]
getVariableFunctions lan@(nsd, _, _, _) varT = getHNatModifiers varT ++ getGenerators nsd ++ getShift lan

getHNatModifiers :: (Type, [Constructor]) -> [Function]
getHNatModifiers (_, hnatc) =
  let cs = delete (Constr "Z" []) hnatc
  in [
    Fn "plus" ([
      ([ConstrParam "Z" [], VarParam "h"], VarExpr "h"),
      ([VarParam "h", ConstrParam "Z" []], VarExpr "h")
    ] ++ map generatePlus cs)
  ,
    Fn "minus" ([
      ([ConstrParam "Z" [], ConstrParam "Z" []], ConstrInst "Z" []),
      ([ConstrParam "Z" [], VarParam "_"], FnCall "error" [StringExpr "You cannot substract zero with a positive number"]),
      ([VarParam "result", ConstrParam "Z" []], VarExpr "result")
    ] ++ map generateMinus [(left, right) | left <- cs, right <- cs])
  ]
  where
    generatePlus :: Constructor -> ([Parameter], Expression)
    generatePlus (Constr n _) = ([VarParam "x1", ConstrParam n [VarParam "x2"]], ConstrInst n [FnCall "plus" [VarExpr "x1", VarExpr "x2"]])

    generateMinus :: (Constructor, Constructor) -> ([Parameter], Expression)
    generateMinus (Constr n1 _, Constr n2 _)
      | n1 == n2 = ([ConstrParam n1 [VarParam "h1"], ConstrParam n2 [VarParam "h2"]], FnCall "minus" [VarExpr "h1", VarExpr "h2"])
      | otherwise = ([ConstrParam n1 [VarParam "h1"], ConstrParam n2 [VarParam "h2"]], FnCall "error" [StringExpr "differing namespace found in minus"])

getGenerators :: [NamespaceDef] -> [Function]
getGenerators = map (
    \ns ->
      let name = getName ns
          fnName = "generateHnat" ++ name
          constr = 'S' : name
      in
      Fn fnName [
        ([IntParam 0, VarParam "c"], VarExpr "c"),
        ([VarParam "n", VarParam "c"], ConstrInst constr [FnCall fnName [Minus (VarExpr "n") (IntExpr 1), VarExpr "c"]])
      ]
  )

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

getShiftFunctions :: [SortDef] -> [NamespaceDef] -> String -> [(SortName, Bool)] -> [Function]
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
    declarationsToFunctions :: [NamespaceInstance] -> [NamespaceDef] -> String -> [Expression]
    declarationsToFunctions nsi nsd op = let filtered = [INH x y | INH x y <- nsi]
      in map (\(INH _ namespaceName) ->
        FnCall (lookForSortName namespaceName nsd ++ "shiftHelp" ++ op) [VarExpr "d"]
      ) filtered
