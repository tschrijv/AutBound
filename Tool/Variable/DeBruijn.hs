module Variable.DeBruijn where

import Data.List

import GeneralTerms
import Program

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
getVariableFunctions (nsd, _, _, _) varT = getHNatModifiers varT ++ getGenerators nsd

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
