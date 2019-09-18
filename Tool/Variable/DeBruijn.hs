module Variable.DeBruijn (getFunctions) where

import Data.List
import Data.Maybe

import GeneralTerms
import Program
import Utility
import Converter
import Variable.Common

getFunctions :: ConvertFunctions
getFunctions
  = VF {
    variableType = getVariableType,
    envType = getEnvType,
    userTypes = getTypes,
    variableInstances = getVariableInstances,
    variableFunctions = getVariableFunctions,
    envFunctions = getEnvFunctions
  }

getVariableType :: Language -> (Type, [Constructor])
getVariableType (nsd, _, _, _) = ("Variable", Constr "Z" [] : map (\ns -> Constr ('S' : nname ns) ["Variable"]) nsd)

getTypes :: Language -> [(Type, [Constructor])]
getTypes (_, sd, _, _) = map (
    \(MkDefSort name _ cds _) -> (name, map getConstr cds)
  ) sd where
    getConstr :: ConstructorDef -> Constructor
    getConstr (MkDefConstructor n lists listSorts folds _ hTypes) =
      Constr n (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes)
    getConstr (MkBindConstructor n lists listSorts folds (var, ns) _ hTypes) =
      Constr n (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes)
    getConstr (MkVarConstructor n _) =
      Constr n ["Variable"]

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
getVariableFunctions lan@(nsd, _, _, _) varT = getHNatModifiers varT ++ getGenerators nsd ++ getShift lan ++ getMappings lan ef ++ getSubst lan ef ++ getFreeVar lan ef

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
      let name = nname ns
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
    declarationsToFunctions :: [Context] -> [NamespaceDef] -> String -> [Expression]
    declarationsToFunctions nsi nsd op = let filtered = [INH x y | INH x y <- nsi]
      in map (\(INH _ namespaceName) ->
        FnCall (lookForSortName namespaceName nsd ++ "shiftHelp" ++ op) [VarExpr "d"]
      ) filtered

_getCtorParams :: ConstructorDef -> [Parameter]
_getCtorParams (MkVarConstructor consName _) = [ConstrParam (capitalize consName) [VarParam "var"]]
_getCtorParams cons = [ConstrParam (capitalize consName) (firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (toLowerCaseFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
  where
    consName = getName cons
    folds = getCtorFolds cons
    lists = getCtorLists cons
    sorts = getCtorSorts cons
    hTypes = getCtorHTypes cons

_varCtorFreeVar :: String -> Expression
_varCtorFreeVar name = IfExpr (GTEExpr (VarExpr "var") (VarExpr "c")) (ListExpr [FnCall "minus" [VarExpr "var", VarExpr "c"]]) (ListExpr [])

_oneDeeper namespace expr = ConstrInst ("S" ++ namespace) expr

_substExpr sname consName =
  IfExpr (EQExpr (VarExpr "var") (VarExpr "c"))
    (FnCall (toLowerCaseFirst sname ++ "shiftplus") [VarExpr "c", VarExpr "sub"])
    (ConstrInst (capitalize consName) [VarExpr "var"])

ef = EF {
  getCtorParams = _getCtorParams,
  varCtorFreeVar = _varCtorFreeVar,
  oneDeeper = _oneDeeper,
  substExpr = _substExpr,
  includeBinders = False
}
