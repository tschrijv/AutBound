{-# OPTIONS_GHC -Wall #-}

module Converter.Types where

import Program
import GeneralTerms

getTypes :: Language -> [(Type, [Constructor])]
getTypes (_, sd, _, _) = map (
    \(MkDefSort name _ cds _) -> (name, map getConstr cds)
  ) sd where
    getConstr :: ConstructorDef -> Constructor
    getConstr (MkDefConstructor n lists listSorts folds _ hTypes) =
      Constr n (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes)
    getConstr (MkBindConstructor n lists listSorts folds _ _ hTypes) =
      Constr n (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes)
    getConstr (MkVarConstructor n _) =
      Constr n ["Variable"]

getEnvType :: [NameSpaceDef] -> (Type, [Constructor])
getEnvType nsd = ("Env", Constr "Nil" [] : map (
    \(MkNameSpace ns _ inEnv) -> Constr ('E' : ns) (inEnv ++ ["Env"])
  ) nsd)
