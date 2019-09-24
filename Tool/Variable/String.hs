module Variable.String (getFunctions) where

import GeneralTerms
import Program
import Converter
import Variable.Common
import Utility

import Data.Maybe
import Data.List
import Debug.Trace

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
getVariableFunctions lan _ = mappingFunctions lan ef ++ freeVarFunctions lan ef ++ substFunctionsC lan

_getCtorParams :: ConstructorDef -> [Parameter]
_getCtorParams (MkVarConstructor consName _) = [ConstrParam consName [VarParam "var"]]
_getCtorParams cons = [ConstrParam consName ((map (\_ -> VarParam "b") (maybeToList (cbinder cons))) ++ firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
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
    (ConstrInst consName [VarExpr "var"])

ef = EF {
  paramForCtor = _getCtorParams,
  freeVarExprForVarCtor = _varCtorFreeVar,
  transformForAddAttr = (\n e -> head e),
  includeBinders = True
}

-- | Generates the following for sorts with variable access:
-- * Substitute functions for every sort that is related to the given sort by
-- the first sort having a context with a variable of the type of the second sort
substFunctionsC :: Language -> [Function]
substFunctionsC (nsd, sd, _, _) =
  concatMap (\(MkDefSort sortName ctxs ctors rewrite) ->
    let inhCtxs = [INH x y | INH x y <- ctxs]
    in Fn (sortName ++ "VarReplace") (map (\ctor ->
      ([VarParam "orig", VarParam "sub"] ++ _getCtorParams ctor, varReplaceCallForCtor ctor)
    ) ctors)
    : map (\ctx ->
      let sortOfCtxNamespace = sortNameForNamespaceName (xnamespace ctx) nsd
      in Fn (sortName ++ sortOfCtxNamespace ++ "Substitute") (map (\ctor ->
          ([VarParam "orig", VarParam "sub"] ++ _getCtorParams ctor, substExprForCtor sortName sortOfCtxNamespace ctor)
        ) ctors)
    ) inhCtxs
  ) sortsWithVarAccess
  where
    ctxsBySname = map snameAndCtxs sd
    varAccessBySname = varAccessBySortName sd
    sortsWithVarAccess = filter (\sort -> isJust (lookup (sname sort) varAccessBySname)) sd

    freeVariablesCall :: ConstructorDef -> (IdenName, SortName) -> Expression
    freeVariablesCall ctor (iden, idenSort)
      = if iden `elem` map fst folds
          then FnCall "concat" [FnCall "fmap" [FnCall fnName substParams, idenExpr]]
          else if iden `elem` map fst lists
            then FnCall "concat" [FnCall "map" [FnCall fnName substParams, idenExpr]]
            else FnCall fnName (substParams ++ [idenExpr])
      where
        folds = dropFold (cfolds ctor)
        lists = clists ctor
        fnName = "freeVariables" ++ idenSort
        idenExpr = VarExpr iden
        substParams = [ListExpr []]

    varReplaceCall :: ConstructorDef -> [Expression] -> IdenName -> Expression
    varReplaceCall ctor params iden
      = if iden `elem` map fst folds
          then FnCall "fmap" [FnCall fnName params, idenExpr]
          else if iden `elem` map fst lists
            then FnCall "map" [FnCall fnName params, idenExpr]
            else FnCall fnName (params ++ [idenExpr])
      where
        folds = dropFold (cfolds ctor)
        lists = clists ctor
        fnName = (sortNameForIden iden ctor ++ "VarReplace")
        idenExpr = VarExpr iden

    varReplaceCallForCtor :: ConstructorDef -> Expression
    varReplaceCallForCtor (MkVarConstructor ctorName _) =
      IfExpr (EQExpr (VarExpr "var") (VarExpr "orig"))
        (ConstrInst ctorName [VarExpr "sub"])
        (ConstrInst ctorName [VarExpr "var"])
    varReplaceCallForCtor ctor =
      ConstrInst
        (cname ctor)
        (
          binder
          ++ map varReplaceCallForIden idensAndAttrs
          ++ [VarExpr (x ++ show n) | (x, n) <- zip (cnatives ctor) [1 :: Int ..]]
        )
      where
        binder = if isBind ctor
          then [FnCall
            ("fresh" ++ snd (fromJust (cbinder ctor)))
            [VarExpr "b", FnCall "concat" [ListExpr (ListExpr [VarExpr "sub"] : map (freeVariablesCall ctor) (folds ++ lists ++ csorts ctor))]]]
          else []
        idensAndAttrs = attrsByIden ctor
        folds = dropFold (cfolds ctor)
        lists = clists ctor

        varReplaceCallForIden :: (IdenName, [AttributeDef]) -> Expression
        varReplaceCallForIden (iden, idenAttrs)
          = if fromJust (lookup sortNameOfIden varAccessBySname)
              then if iden `elem` map fst folds
                then FnCall "fmap" [FnCall fnName substParams, idenExpr]
                else if iden `elem` map fst lists
                  then FnCall "map" [FnCall fnName substParams, idenExpr]
                  else FnCall fnName (substParams ++ [idenExpr])
              else idenExpr
          where
            fnName = sortNameForIden iden ctor ++ "VarReplace"
            idenExpr = if null binder
              then VarExpr iden
              else varReplaceCall ctor [VarExpr "b", head binder] iden
            substParams = [VarExpr "orig", VarExpr "sub"]
            sortNameOfIden = sortNameForIden iden ctor

    substExprForCtor :: SortName -> SortName -> ConstructorDef -> Expression
    substExprForCtor sortName sortOfCtxNamespace (MkVarConstructor ctorName _)
      | sortName == sortOfCtxNamespace
        = IfExpr (EQExpr (VarExpr "var") (VarExpr "orig"))
            (VarExpr "sub")
            (ConstrInst ctorName [VarExpr "var"])
      | otherwise = ConstrInst ctorName [VarExpr "var"]
    substExprForCtor sortName sortOfCtxNamespace ctor =
      ConstrInst
        (cname ctor)
        (
          binder
          ++ map substCallForIden idensAndAttrs
          ++ [VarExpr (x ++ show n) | (x, n) <- zip (cnatives ctor) [1 :: Int ..]]
        )
      where
        binder = if isBind ctor
          then [FnCall
            ("fresh" ++ snd (fromJust (cbinder ctor)))
            [VarExpr "b", FnCall "concat" [
              ListExpr (
                map
                  (freeVariablesCall ctor)
                  (("sub", sortOfCtxNamespace) : folds ++ lists ++ csorts ctor)
              )
            ]]]
          else []
        idensAndAttrs = attrsByIden ctor
        folds = dropFold (cfolds ctor)
        lists = clists ctor

        -- | Construct a mapping function call for an identifier
        substCallForIden :: (IdenName, [AttributeDef]) -> Expression
        substCallForIden (iden, idenAttrs)
          | sortHasCtxForSort (sortNameForIden iden ctor) sortOfCtxNamespace nsd ctxsBySname
            = if fromJust (lookup sortNameOfIden varAccessBySname)
                then if iden `elem` map fst folds
                  then FnCall "fmap" [FnCall fnName substParams, idenExpr]
                  else if iden `elem` map fst lists
                    then FnCall "map" [FnCall fnName substParams, idenExpr]
                    else FnCall fnName (substParams ++ [idenExpr])
                else idenExpr
          | otherwise = VarExpr iden
          where
            fnName = sortNameForIden iden ctor ++ sortOfCtxNamespace ++ "Substitute"
            idenExpr = if null binder
              then VarExpr iden
              else varReplaceCall ctor [VarExpr "b", head binder] iden
            substParams = [VarExpr "orig", VarExpr "sub"]
            sortNameOfIden = sortNameForIden iden ctor
