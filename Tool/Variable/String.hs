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
getVariableFunctions lan _ = mappingFunctions lan ef ++ freeVarFunctions lan ef ++ substFunctionsC lan

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

-- | Generates the following for sorts with variable access:
-- * Substitute functions for every sort that is related to the given sort by
-- the first sort having a context with a variable of the type of the second sort
substFunctionsC :: Language -> [Function]
substFunctionsC (nsd, sd, _, _) =
  concatMap (\(MkDefSort sortName ctxs ctors rewrite) ->
    let inhCtxs = [INH x y | INH x y <- ctxs]
    in (map (\ctx ->
      let sortOfCtxNamespace = sortNameForNamespaceName (xnamespace ctx) nsd
      in Fn (lowerFirst sortName ++ sortOfCtxNamespace ++ "Substitute")
        (map (\ctor -> substFunctionForCtx sortName sortOfCtxNamespace ctor ctx ctxs nsd rewrite) ctors)
    ) inhCtxs)
  ) sortsWithVarAccess
  where
    ctxsBySname = map snameAndCtxs sd
    varAccessBySname = varAccessBySortName sd
    sortsWithVarAccess = filter (\sort -> isJust (lookup (sname sort) varAccessBySname)) sd
    -- | Generate a substitution function for a given sort's given context instance
    -- where parameters are
    -- * `orig` for the variable we want to substitute
    -- * `sub` for the term we want to replace `orig` with
    -- * `t` for the term we want to run the substitution on
    substFunctionForCtx :: SortName -> SortName -> ConstructorDef -> Context -> [Context] -> [NamespaceDef] -> Bool -> ([Parameter], Expression)
    substFunctionForCtx sortName sortOfCtxNamespace ctor ctx ctxs nsd rewrite
      = (
        [VarParam "orig", VarParam "sub"] ++ _getCtorParams ctor,
        substExprForCtor ctor
      )
      where
        -- | Generate the map function's body for a given contructor in the sort
        -- (a function call to the namespace's processing function in case of a variable,
        -- and a constructor call with its identifiers also mapped otherwise)
        substExprForCtor :: ConstructorDef -> Expression
        substExprForCtor (MkVarConstructor ctorName _) =
          IfExpr (EQExpr (VarExpr "var") (VarExpr "orig"))
            (VarExpr "sub")
            (ConstrInst (upperFirst ctorName) [VarExpr "var"])
        substExprForCtor ctor =
          ConstrInst
            (upperFirst (cname ctor))
            (
              binder
              ++ map substCallForIden idensAndAttrs
              ++ [VarExpr (lowerFirst x ++ show n) | (x, n) <- zip (cnatives ctor) [1 :: Int ..]]
            )
          where
            binder = if isBind ctor then [FnCall ("fresh" ++ snd (fromJust (cbinder ctor))) [VarExpr "b", FnCall "concat" [ListExpr (map (\(iden, namespace) -> FnCall ("freeVariables" ++ namespace) [ListExpr [], VarExpr iden]) (dropFold (cfolds ctor) ++ clists ctor ++ csorts ctor))]]] else []
            idensAndAttrs = attrsByIden ctor
            folds = dropFold (cfolds ctor)
            lists = clists ctor

            -- | Returns whether the given constructor has a binder
            isBind :: ConstructorDef -> Bool
            isBind MkBindConstructor{} = True
            isBind _                   = False

            -- | Construct a mapping function call for an identifier
            substCallForIden :: (IdenName, [AttributeDef]) -> Expression
            substCallForIden (iden, idenAttrs)
              = if fromJust (lookup sortNameOfIden varAccessBySname)
                  then if iden `elem` map fst folds
                    then FnCall "fmap" [FnCall fnName substParams, idenExpr]
                    else if iden `elem` map fst lists
                      then FnCall "map" [FnCall fnName substParams, idenExpr]
                      else FnCall fnName (substParams ++ [idenExpr])
                  else idenExpr
              where
                fnName = lowerFirst (sortNameForIden iden ctor) ++ sortOfCtxNamespace ++ "Substitute"
                idenExpr = if null binder then VarExpr (lowerFirst iden) else FnCall (lowerFirst (sortNameForIden iden ctor) ++ lowerFirst (sortName) ++ "Substitute") [VarExpr "b", head binder, VarExpr (lowerFirst iden)]
                substParams = [VarExpr "orig", VarExpr "sub"]
                sortNameOfIden = sortNameForIden iden ctor
