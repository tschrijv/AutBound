{-# OPTIONS_GHC -Wall #-}

module Converter.Types where

import Data.List

import Abstract
import GeneralTerms

getTypes :: Language -> [(Type, [Constructor])]
getTypes (nsd, sd, imp, cd) = map (
    \(MkDefSort name _ cds _) -> (name, map getConstr cds)
  ) sd where
    getConstr :: ConstructorDef -> Constructor
    getConstr (MkDefConstructor n lists listSorts folds _ hTypes) =
      Constr n ((map (\(i, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds) ++ (map (\(_, t) -> "[" ++ t ++ "]") lists) ++ (map snd listSorts) ++ hTypes)
    getConstr (MkBindConstructor n lists listSorts folds _ _ hTypes) =
      Constr n ((map (\(i, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds) ++ (map (\(_, t) -> "[" ++ t ++ "]") lists) ++ (map snd listSorts) ++ hTypes)
    getConstr (MkVarConstructor n _) =
      Constr n ["HNat"]

getHNatType :: [NameSpaceDef] -> (Type, [Constructor])
getHNatType nsd = ("HNat", (Constr "Z" []) : map (\ns -> Constr ('S' : getName ns) ["HNat"]) nsd)

getEnvType :: [NameSpaceDef] -> (Type, [Constructor])
getEnvType nsd = ("Env", (Constr "Nil" []) : map (
    \(MkNameSpace ns _ inEnv) -> Constr ('E' : ns) (inEnv ++ ["Env"])
  ) nsd)

-- /////////////////////////////////////////////////////////////////////////////

getHNatOrd :: [NameSpaceDef] -> (Type, [Constructor]) -> (Type, Type, [Function])
getHNatOrd nsd (_, hnatc) =
  let cs = delete (Constr "Z" []) hnatc
  in ("Ord", "HNat", [
    Fn "compare" ([
      ([ConstrParam "Z" [], ConstrParam "_" []], ConstrInst "LT" []),
      ([ConstrParam "Z" [], ConstrParam "Z" []], ConstrInst "EQ" []),
      ([ConstrParam "_" [], ConstrParam "Z" []], ConstrInst "GT" [])
    ] ++ (map generateCompare [(left, right) | left <- cs, right <- cs]))
  ]) where
    generateCompare :: (Constructor, Constructor) -> ([Parameter], Expression)
    generateCompare ((Constr n1 _), (Constr n2 _))
      | n1 == n2 = ([(ConstrParam n1 [(VarParam "h1")]), (ConstrParam n2 [(VarParam "h2")])], FnCall "compare" [(VarExpr "h1"), (VarExpr "h2")])
      | otherwise = ([(ConstrParam n1 [(VarParam "h1")]), (ConstrParam n2 [(VarParam "h2")])], FnCall "error" [StringExpr "differing namespace found in compare"])

-- /////////////////////////////////////////////////////////////////////////////

getHNatModifiers :: (Type, [Constructor]) -> [Function]
getHNatModifiers (_, hnatc) =
  let cs = delete (Constr "Z" []) hnatc
  in [
    Fn "plus" ([
      ([ConstrParam "Z" [], VarParam "h"], VarExpr "h"),
      ([VarParam "h", ConstrParam "Z" []], VarExpr "h")
    ] ++ (map generatePlus cs))
  ,
    Fn "minus" ([
      ([ConstrParam "Z" [], ConstrParam "Z" []], ConstrInst "Z" []),
      ([ConstrParam "_" [], ConstrParam "Z" []], FnCall "error" [StringExpr "You cannot substract zero with a positive number"]),
      ([VarParam "result", ConstrParam "Z" []], VarExpr "result")
    ] ++ (map generateMinus [(left, right) | left <- cs, right <- cs]))
  ]
  where
    generatePlus :: Constructor -> ([Parameter], Expression)
    generatePlus (Constr n _) = ([VarParam "x1", ConstrParam n [VarParam "x2"]], ConstrInst n [FnCall "plus" [VarExpr "x1", VarExpr "x2"]])

    generateMinus :: (Constructor, Constructor) -> ([Parameter], Expression)
    generateMinus ((Constr n1 _), (Constr n2 _))
      | n1 == n2 = ([(ConstrParam n1 [(VarParam "h1")]), (ConstrParam n2 [(VarParam "h2")])], FnCall "minus" [(VarExpr "h1"), (VarExpr "h2")])
      | otherwise = ([(ConstrParam n1 [(VarParam "h1")]), (ConstrParam n2 [(VarParam "h2")])], FnCall "error" [StringExpr "differing namespace found in minus"])

getGenerators :: [NameSpaceDef] -> [Function]
getGenerators nsd = map (
    \ns ->
      let name = getName ns
          fnName = "generateHnat" ++ name
          constr = 'S' : name
      in
      Fn fnName [
        ([IntParam 0, VarParam "c"], VarExpr "c"),
        ([VarParam "n", VarParam "c"], ConstrInst constr [FnCall fnName [Minus (VarExpr "n") (IntExpr 1)], VarExpr "c"])
      ]
  ) nsd
