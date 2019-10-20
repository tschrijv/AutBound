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
    userTypes = getTypes,
    variableInstances = getVariableInstances,
    variableFunctions = getVariableFunctions,
    nativeCode = freshVarFunctions
  }

freshVarFunctions :: Language -> (Type, [Constructor]) -> [String]
freshVarFunctions _ varType
  = let ctors = snd varType
        names = map (\(Constr name _) -> tail name) ctors
    in ["fresh" ++ name ++ " x b = if not (x `elem` b) then x else head [S" ++ name ++ " ('v' : show n) | n <- [0..], not (S" ++ name ++ " ('v' : show n) `elem` b)]"
    | name <- names]

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
getVariableFunctions lan _ = mappingFunctions lan ef ++ freeVarFunctions lan ef ++ substFunctionsC lan ++ boundVarFunctions lan

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

_oneDeeper namespace expr = FnCall "concat" [ListExpr (ListExpr [VarExpr "b"] : expr)]

_applyInhCtxsToAttrs :: SortName -> ConstructorDef -> (IdenName, [AttributeDef]) -> [(SortName, [Context])] -> Expression
_applyInhCtxsToAttrs sname ctor (iden, idenAttrs) ctxsBySname
 = let inhCtxs = (inhCtxsForSortName (sortNameForIden iden ctor) ctxsBySname)
   in foldr (\ctx rest -> fromMaybe rest (applyOneCtx ctx rest)) (VarExpr "c") inhCtxs
  where
    -- | Runs `applyOneAttr` if the identifier's attribute definitions
    -- contain an assignment to an instance of the given context
    applyOneCtx :: Context -> Expression -> Maybe Expression
    applyOneCtx ctx param
      | isJust attrForCtx = applyOneAttr (fromJust attrForCtx) [param]
      | otherwise = Nothing
      where
        attrForCtx = find (\(left, _) -> linst left == xinst ctx) idenAttrs

        -- | Apply the necessary wrap based on the attribute assignment type
        applyOneAttr :: AttributeDef -> [Expression] -> Maybe Expression
        applyOneAttr (_, RightLHS _) _ = Nothing
        applyOneAttr (l, RightAdd expr _) params
          = return (_oneDeeper (xnamespace ctx) (nextStep ++ params))
          where
            nextStep = maybeToList (applyOneAttr (l, expr) [])
        applyOneAttr (_, RightSub iden context) params
          = if elem iden (map fst lists) || elem iden (map fst folds)
              then if isJust attrsForIden
                then return (FnCall ("generateHnat" ++ xnamespace ctx) (FnCall "length" (VarExpr iden : nextStep) : params))
                else return (FnCall ("generateHnat" ++ xnamespace ctx) (FnCall "length" [VarExpr iden] : params))
              else if isJust attrsForIden
                then return (FnCall "concat" [ListExpr (FnCall ("boundVariables" ++ fromJust (lookup iden sorts)) (ListExpr [] : VarExpr iden : nextStep) : params)])
                else return (FnCall ("addToEnvironment" ++ fromJust (lookup iden sorts) ++ context) (VarExpr iden : params))
          where
            newAttrs = filter (\(left, _) ->
                let iden = liden left
                    ctxsForSort = fromJust (lookup sname ctxsBySname)
                    ctxsForIdenSort = fromJust (lookup (sortNameForIden iden ctor) ctxsBySname)
                in (iden == "" && any (\ctx -> linst left == xinst ctx) ctxsForSort) || any (\ctx -> linst left == xinst ctx) ctxsForIdenSort
              ) (cattrs ctor)
            attrsForIden = find (\(left, _) -> liden left == iden) newAttrs
            nextStep = maybeToList (applyOneAttr (fromJust attrsForIden) [])
            lists = clists ctor
            folds = dropFold $ cfolds ctor
            sorts = csorts ctor

ef = EF {
  paramForCtor = _getCtorParams,
  freeVarExprForVarCtor = _varCtorFreeVar,
  applyInhCtxsToAttrs = _applyInhCtxsToAttrs,
  includeBinders = True
}

boundVarFunctions :: Language -> [Function]
boundVarFunctions (_, sd, _, _) =
  map (\sort ->
    Fn ("boundVariables" ++ sname sort)
    (map (\ctor ->
      (VarParam "c" : _getCtorParams ctor,
      case ctor of
        (MkVarConstructor name _)
          -> ListExpr []
        (MkBindConstructor {})
          -> FnCall "nub" [
              FnCall "concat"
                [ListExpr (VarExpr "c" : ListExpr [VarExpr "b"] :
                    boundVariableCallListForCtor sort ctor
                )]
             ]
        (MkDefConstructor {})
          -> FnCall "nub" [
              FnCall "concat"
                [ListExpr (VarExpr "c" :
                  boundVariableCallListForCtor sort ctor
                )]
            ]
      )
    ) (sctors sort))
  ) sd
  where
    -- | Generate a list of expressions, that when concatenated together give
    -- the union of free variables for a given constructor (free variable
    -- calls for every identifier of a sort that has access to variables)
    boundVariableCallListForCtor :: SortDef -> ConstructorDef -> [Expression]
    boundVariableCallListForCtor sort ctor
      = let relevantAttrs = filter (
                \(left, right) ->
                  liden left == ""
                    && isJust (riden right)
                    && any (\ctx -> (xinst ctx) == linst left) (synCtxs sort)
              ) (cattrs ctor)
            callList = concatMap helper relevantAttrs
        in if null callList then [ListExpr []] else callList
        where
          helper :: AttributeDef -> [Expression]
          helper (_, right)
            = let iden = fromJust (riden right)
                  sortNameOfIden = sortNameForIden iden ctor
                  assignedAttrs = filter (
                      \(left, right) ->
                        liden left == iden
                          && isJust (riden right)
                          && any (\ctx -> (xinst ctx) == linst left) (inhCtxs sort)
                    ) (cattrs ctor)
                  attrexp = if null assignedAttrs then [ListExpr []] else (concatMap helper assignedAttrs)
              in [concatCallForIden ctor iden ("boundVariables" ++ sortNameOfIden) attrexp]

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
    sortsWithVarAccess = filter (\sort -> fromJust (lookup (sname sort) varAccessBySname)) sd

    freeVariablesCall :: ConstructorDef -> (IdenName, SortName) -> Expression
    freeVariablesCall ctor (iden, idenSort)
      = concatCallForIden ctor iden ("freeVariables" ++ idenSort) [ListExpr []]

    varReplaceCall :: ConstructorDef -> [Expression] -> IdenName -> Expression
    varReplaceCall ctor params iden
      = fnCallForIden ctor iden (sortNameForIden iden ctor ++ "VarReplace") params

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
