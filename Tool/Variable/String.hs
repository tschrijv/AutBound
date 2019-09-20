module Variable.String (getFunctions) where

import GeneralTerms
import Program
import Converter
import Variable.Common
import Utility

import Data.Maybe
import Data.List

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
getVariableType (nsd, _, _, _) = ("Variable", map (\ns -> Constr ('S' : nname ns) ["String"]) nsd)

getTypes :: Language -> [(Type, [Constructor])]
getTypes (_, sd, _, _) = map (
    \(MkDefSort name _ cds _) -> (name, map getConstr cds)
  ) sd where
    getConstr :: ConstructorDef -> Constructor
    getConstr (MkDefConstructor n lists listSorts folds _ hTypes) =
      Constr n (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes)
    getConstr (MkBindConstructor n lists listSorts folds (var, ns) _ hTypes) =
      Constr n ("Variable" : (map (\(_, s, f) -> "(" ++ f ++ " " ++ s ++ ")") folds ++ map (\(_, t) -> "[" ++ t ++ "]") lists ++ map snd listSorts ++ hTypes))
    getConstr (MkVarConstructor n _) =
      Constr n ["Variable"]

getVariableInstances :: (Type, [Constructor]) -> [(Type, Type, [Function])]
getVariableInstances _ = []

getVariableFunctions :: Language -> (Type, [Constructor]) -> [Function]
getVariableFunctions lan _ = mappingFunctions lan ef ++ freeVarFunctions lan ef -- ++ getCustSubst lan

_getCtorParams :: ConstructorDef -> [Parameter]
_getCtorParams (MkVarConstructor consName _) = [ConstrParam (upperFirst consName) [VarParam "var"]]
_getCtorParams cons = [ConstrParam (upperFirst consName) ((map (\_ -> VarParam "b") (maybeToList (cbinder cons))) ++ firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (lowerFirst x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
  where
    consName = cname cons
    folds = cfolds cons
    lists = clists cons
    sorts = csorts cons
    hTypes = cnatives cons

_varCtorFreeVar :: String -> Expression
_varCtorFreeVar name = IfExpr (FnCall "elem" [VarExpr "var", VarExpr "c"]) (ListExpr []) (ListExpr [VarExpr "var"])

_substExpr sname consName =
  IfExpr (EQExpr (VarExpr "var") (VarExpr "c"))
    (VarExpr "sub")
    (ConstrInst (upperFirst consName) [VarExpr "var"])

ef = EF {
  paramForCtor = _getCtorParams,
  freeVarExprForVarCtor = _varCtorFreeVar,
  transformForAddAttr = (\n e -> head e),
  substHelperExprForVarCtor = _substExpr,
  includeBinders = True
}

-- Custom subst
