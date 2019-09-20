{-# OPTIONS_GHC -Wall #-}

module Variable.Common (getEnvType, getEnvFunctions, freeVarFunctions, mappingFunctions, substFunctions, sortNameForIden, firstToVarParams, dropFold, ExternalFunctions(..)) where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility

data ExternalFunctions = EF {
  paramForCtor :: ConstructorDef -> [Parameter],
  freeVarExprForVarCtor :: String -> Expression,
  transformForAddAttr :: String -> [Expression] -> Expression,
  substHelperExprForVarCtor :: String -> String -> Expression,
  includeBinders :: Bool
}

-- * Types
-- ----------------------------------------------------------------------------

-- | Generate the data type definition for Env
getEnvType :: Language -> (Type, [Constructor])
getEnvType (nsd, _, _, _) =
  ("Env",
  Constr "Nil" []
  : map (
    \(MkNameSpace name _ env) -> Constr ('E' : name) (env ++ ["Env"])
  ) nsd)

-- | ??
getEnvFunctions :: Language -> [Function]
getEnvFunctions (nsd, sd, _, _) = let table = map snameAndCtxs sd
  in concatMap (\s ->
    let nsi = [SYN x y | SYN x y <- sctxs s]
    in if null nsi then [] else
    map (\c ->
      generateSortSynSystemOneConstructor (sname s) nsd table c (head nsi)
    ) (sctors s)
  ) sd

generateSortSynSystemOneConstructor :: SortName -> [NamespaceDef] -> [(SortName, [Context])] -> ConstructorDef -> Context -> Function
generateSortSynSystemOneConstructor sname _ _ (MkVarConstructor consName _) _ =
  Fn ("addToEnvironment" ++ sname) [([ConstrParam (upperFirst consName) [VarParam "var"], VarParam "c"], VarExpr "c")]
generateSortSynSystemOneConstructor sname namespaces table ctor ctx =
  Fn ("addToEnvironment" ++ sname ++ xinst ctx) [([ConstrParam (upperFirst consName) (firstToVarParams listSorts ++ [VarParam "_" | _ <- hTypes]), VarParam "c"], getEnvFunctionGenerate sname ctx namespaces newtable listSorts rules)]
  where
    newtable = filterCtxsByNamespace (xnamespace ctx) table
    consName = cname ctor
    listSorts = csorts ctor
    hTypes = cnatives ctor
    rules = cattrs ctor

getEnvFunctionGenerate :: SortName -> Context -> [NamespaceDef] -> [(SortName, [Context])] -> [(IdenName, SortName)]  -> [AttributeDef] -> Expression
getEnvFunctionGenerate sname ctx namespaces table listSorts rules
  | null $ fromJust (lookup "lhs" allrules) = VarExpr "c"
  | otherwise = navigateRules sname ctx namespaces table listSorts rules start
  where
    allrules = collectRulesSyn rules listSorts
    start = fromJust (
      find
        (\x -> linst (fst x) == xinst ctx)
        (fromJust (lookup "lhs" allrules))
      )

    collectRulesSyn :: [AttributeDef] -> [(IdenName, SortName)] -> [(IdenName, [AttributeDef])]
    collectRulesSyn rules ids =
      foldl
        (++)
        [("lhs", [(LeftLHS c, r) | (LeftLHS c, r) <- rules])]
        (map (\(iden, _) -> [collectRulesOfIdSyn rules iden]) ids)
      where
        collectRulesOfIdSyn :: [AttributeDef] -> IdenName -> (IdenName, [AttributeDef])
        collectRulesOfIdSyn nsr i = (i, filter (\(LeftSub fieldname _, RightSub _ _) -> fieldname == i) nsr)

navigateRules :: SortName -> Context -> [NamespaceDef] -> [(SortName, [Context])] -> [(IdenName, SortName)] -> [AttributeDef] -> AttributeDef -> Expression
navigateRules sname ctx namespaces table listSorts rules (l, RightAdd expr _) =
  FnCall ("S" ++ xnamespace ctx) [navigateRules sname ctx namespaces table listSorts rules (l, expr)]
navigateRules _ _ _ _ _ _ (LeftLHS _, RightLHS _) =
  VarExpr "c"
navigateRules sname ctx namespaces table listSorts rules (LeftLHS _, RightSub iden _)
  | isJust newrule =
    FnCall functionName [VarExpr iden, navigateRules sname ctx namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
  where
    newrule = find (\(l, _) -> liden l == iden) rules
    functionName = "addToEnvironment" ++ fromJust (lookup iden listSorts) ++ xinst ctx -- TODO: iden was included in function name with a space?? included here both, below once + twice!!
navigateRules _ _ _ _ _ _ (LeftSub _ _, RightLHS _) =
  VarExpr "c"
navigateRules sname ctx namespaces table listSorts rules (LeftSub _ _, RightSub iden _)
  | isJust newrule =
    FnCall functionName [VarExpr iden, navigateRules sname ctx namespaces table listSorts rules (fromJust newrule)]
  | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
  where
    newrule = find (\(l, _) -> liden l == iden) rules
    functionName = "addToEnvironment" ++ fromJust (lookup iden listSorts) ++ xinst ctx

-- * Free variables
-- ----------------------------------------------------------------------------

-- | Generate free variable functions for every sort that has access to variable
-- constructors
freeVarFunctions :: Language -> ExternalFunctions -> [Function]
freeVarFunctions (_, sd, _, _) ef =
  let ctxsBySname = map snameAndCtxs sd
      varAccessBySname = varAccessBySortName sd
      sortsWithVarAccess = filter (\(MkDefSort sname _ _ _) -> isJust (lookup sname varAccessBySname)) sd
  in map (\sort ->
    Fn ("freeVariables" ++ sname sort)
    (map (\ctor ->
      (VarParam "c" : paramForCtor ef ctor,
      case ctor of
        (MkVarConstructor name _)
          -> freeVarExprForVarCtor ef name
        _
          -> FnCall "nub" [
              FnCall "concat"
                [ListExpr (
                  freeVariableCallListForCtor ef (sname sort) ctor ctxsBySname varAccessBySname
                )]
             ]
      )
    ) (sctors sort))
  ) sortsWithVarAccess
  where
    -- | Generate a list of expressions, that when concatenated together give
    -- the union of free variables for a given constructor (free variable
    -- calls for every identifier of a sort that has access to variables)
    freeVariableCallListForCtor :: ExternalFunctions -> SortName -> ConstructorDef -> [(SortName, [Context])] -> [(SortName, Bool)] -> [Expression]
    freeVariableCallListForCtor ef sname ctor ctxsBySname varAccessBySname
      = let folds = dropFold $ cfolds ctor
            lists = clists ctor
            idensAndAttrs = attrsByIden ctor
            callList = concatMap (
              \(iden, iattrs) ->
                let addedBinders = applyInhCtxsToAttrs ef sname ctor (iden, iattrs) ctxsBySname
                    sortNameOfIden = sortNameForIden iden ctor
                in
                  if fromJust (lookup sortNameOfIden varAccessBySname)
                  then if iden `elem` map fst folds
                    then [FnCall "foldMap" [FnCall ("freeVariables" ++ sortNameOfIden) [addedBinders], VarExpr (lowerFirst iden)]]
                    else if iden `elem` map fst lists
                      then [FnCall "concatMap" [FnCall ("freeVariables" ++ sortNameOfIden) [addedBinders], VarExpr (lowerFirst iden)]]
                      else [FnCall ("freeVariables" ++ sortNameOfIden) (addedBinders : [VarExpr (lowerFirst iden)])]
                  else []
              ) idensAndAttrs
        in if null callList then [ListExpr []] else callList

-- * Mapping functions
-- ----------------------------------------------------------------------------

-- | Generate mapping functions for every sort that has access to variable
-- constructors
mappingFunctions :: Language -> ExternalFunctions -> [Function]
mappingFunctions (_, sd, _, _) ef =
  let ctxsBySname = map snameAndCtxs sd
      varAccessBySname = varAccessBySortName sd
      sortsWithVarAccess = filter (\(MkDefSort sname _ _ _) -> isJust (lookup sname varAccessBySname)) sd
  in map (
    \(MkDefSort sortName ctxs ctors _) ->
        Fn (mapFnForSortName sortName)
        (map (\ctor ->
          (
            [VarParam ("on" ++ namespace) | INH _ namespace <- ctxs]
            ++ [VarParam "c"]
            ++ paramForCtor ef ctor
          ,
            mappingExprForCtor sortName ctor ctxsBySname varAccessBySname
          )
        ) ctors)
  ) sortsWithVarAccess
  where
    -- | Return the name of the mapping function for the given sort name
    mapFnForSortName :: SortName -> String
    mapFnForSortName sname = lowerFirst sname ++ "map"

    -- | Generate the map function's body for a given contructor in the sort
    -- (a function call to the namespace's processing function in case of a variable,
    -- and a constructor call with its identifiers also mapped otherwise)
    mappingExprForCtor :: SortName -> ConstructorDef -> [(SortName, [Context])] -> [(SortName, Bool)] -> Expression
    mappingExprForCtor sortName (MkVarConstructor ctorName _) ctxsBySname _ =
      FnCall ("on" ++ xnamespace (head (fromJust (lookup sortName ctxsBySname)))) [ -- TODO: this is a suspicious head call
        VarExpr "c",
        ConstrInst (upperFirst ctorName) [VarExpr "var"]
      ]
    mappingExprForCtor sortName ctor ctxsBySname varAccessBySname =
      let binder = if includeBinders ef && isBind ctor then [VarExpr "b"] else []
      in
        ConstrInst
          (upperFirst (cname ctor))
          (
            binder
            ++ map mapFnCallForIden idensAndAttrs
            ++ [VarExpr (lowerFirst x ++ show n) | (x, n) <- zip (cnatives ctor) [1 :: Int ..]]
          )
      where
        idensAndAttrs = attrsByIden ctor
        folds = dropFold (cfolds ctor)
        lists = clists ctor

        -- | Returns whether the given constructor has a binder
        isBind :: ConstructorDef -> Bool
        isBind MkBindConstructor{} = True
        isBind _                   = False

        -- | Construct a mapping function call for an identifier
        mapFnCallForIden :: (IdenName, [AttributeDef]) -> Expression
        mapFnCallForIden (iden, idenAttrs)
          = if fromJust (lookup sortNameOfIden varAccessBySname)
              then if iden `elem` map fst folds
                then FnCall "fmap" [FnCall (mapFnForSortName sortNameOfIden) (fnCallsForCtxs (fromJust (lookup sortNameOfIden ctxsBySname)) ++ addedBinders), VarExpr (lowerFirst iden)]
                else if iden `elem` map fst lists
                  then FnCall "map" [FnCall (mapFnForSortName sortNameOfIden) (fnCallsForCtxs (fromJust (lookup sortNameOfIden ctxsBySname)) ++ addedBinders), VarExpr (lowerFirst iden)]
                  else FnCall (mapFnForSortName sortNameOfIden) (fnCallsForCtxs (fromJust (lookup sortNameOfIden ctxsBySname)) ++ addedBinders ++ [VarExpr (lowerFirst iden)])
              else VarExpr (lowerFirst iden)
          where
            addedBinders = [applyInhCtxsToAttrs ef sortName ctor (iden, idenAttrs) ctxsBySname]
            sortNameOfIden = sortNameForIden iden ctor

            -- | Return a function reference for the processing functions
            -- of the namespaces in the list of contexts
            fnCallsForCtxs :: [Context] -> [Expression]
            fnCallsForCtxs ctx = [VarExpr ("on" ++ namespace) | INH _ namespace <- ctx]

-- * Substitution functions
-- ----------------------------------------------------------------------------

-- | Generates the following for sorts with variable access:
-- * Substitute helper functions for variable constructors
-- * Substitute functions for every sort that is related to the given sort by
-- the first sort having a context with a variable of the type of the second sort
substFunctions :: Language -> ExternalFunctions -> [Function]
substFunctions (nsd, sd, _, _) ef =
  let varAccessBySname = varAccessBySortName sd
      sortsWithVarAccess = filter (\sort -> isJust (lookup (sname sort) varAccessBySname)) sd
  in concatMap (\(MkDefSort sortName ctxs ctors rewrite) ->
    let inhCtxs = [INH x y | INH x y <- ctxs]
    in
      [
        Fn (lowerFirst sortName ++ "SubstituteHelp")
        [
          (
            [VarParam "sub", VarParam "c", ConstrParam (upperFirst ctorName) [VarParam "var"]],
            substHelperExprForVarCtor ef sortName ctorName
          )
        ]
      | MkVarConstructor ctorName _ <- ctors]
      ++
      map (\ctx -> substFunctionForCtx sortName ctx ctxs nsd rewrite) inhCtxs
  ) sortsWithVarAccess
  where
    -- | Generate a substitution function for a given sort's given context instance
    -- where parameters are
    -- * `orig` for the variable we want to substitute
    -- * `sub` for the term we want to replace `orig` with
    -- * `t` for the term we want to run the substitution on
    substFunctionForCtx :: SortName -> Context -> [Context] -> [NamespaceDef] -> Bool -> Function
    substFunctionForCtx sortName ctx ctxs nsd rewrite
      = let sortOfCtxNamespace = sortNameForNamespaceName (xnamespace ctx) nsd
            mapCall = FnCall (lowerFirst sortName ++ "map") (paramFnCallsForCtxs ctx ctxs nsd ++ [VarExpr "orig", VarExpr "t"])
        in Fn
          (lowerFirst sortName ++ sortOfCtxNamespace ++ "Substitute")
          [
            (
              [VarParam "sub", VarParam "orig", VarParam "t"],
              if rewrite then FnCall ("rewrite" ++ sortName) [mapCall] else mapCall
            )
          ]
      where
        -- | For each inherited context instance in the list (a sort's contexts) generate
        -- either a function call to the helper function if the instance is the one
        -- being substituted, or a lambda function that just returns the variable's
        -- value
        paramFnCallsForCtxs :: Context -> [Context] -> [NamespaceDef] -> [Expression]
        paramFnCallsForCtxs (INH inst namespaceName) ctxs nsd =
          [if inst == inst'
              then FnCall (sortNameForNamespaceName namespaceName nsd ++ "SubstituteHelp") [VarExpr "sub"]
              else LambdaExpr [VarParam "c", VarParam "x"] (VarExpr "x")
          | INH inst' _ <- ctxs]

-- * Helper functions
-- ----------------------------------------------------------------------------

-- | Returns the list of inherited contexts for a given sort name
inhCtxsForSortName :: SortName -> [(SortName, [Context])] -> [Context]
inhCtxsForSortName sname ctxsForSortName = [INH x y | INH x y <- ctxs]
  where
    ctxs = fromJust (lookup sname ctxsForSortName)

-- | Looks up the sort name for a given identifier in a constructor
sortNameForIden :: IdenName -> ConstructorDef -> SortName
sortNameForIden iden ctor = fromJust (lookup iden (dropFold (cfolds ctor) ++ clists ctor ++ csorts ctor))

-- | In a list of tuples, converts the first elements to a list of variable parameters
firstToVarParams :: [(String, String)] -> [Parameter]
firstToVarParams = map (VarParam . lowerFirst . fst)

-- | For every inherited context of a sort, apply nested modifiers to the
-- returned "c" variable
applyInhCtxsToAttrs :: ExternalFunctions -> SortName -> ConstructorDef -> (IdenName, [AttributeDef]) -> [(SortName, [Context])] -> Expression
applyInhCtxsToAttrs ef sname ctor (iden, idenAttrs) ctxsBySname
 = let inhCtxs = (inhCtxsForSortName (sortNameForIden iden ctor) ctxsBySname)
   in foldr (\ctx rest -> fromMaybe rest (applyOneCtx ctx rest)) (VarExpr "c") inhCtxs
  where
    -- | Runs `applyOneRuleLogic` if the identifier's attribute definitions
    -- contain an assignment to an instance of the given context
    applyOneCtx :: Context -> Expression -> Maybe Expression
    applyOneCtx ctx param
      | isJust attrForCtx = applyOneRuleLogic (fromJust attrForCtx) [param]
      | otherwise = Nothing
      where
        attrForCtx = find (\(left, _) -> linst left == xinst ctx) idenAttrs

        -- | Apply the necessary wrap based on the attribute assignment type
        applyOneRuleLogic :: AttributeDef -> [Expression] -> Maybe Expression
        applyOneRuleLogic (_, RightLHS _) _ = Nothing
        applyOneRuleLogic (l, RightAdd expr _) params
          = return (transformForAddAttr ef (xnamespace ctx) (nextStep ++ params))
          where
            nextStep = maybeToList (applyOneRuleLogic (l, expr) [])
        applyOneRuleLogic (_, RightSub iden context) params
          = if elem iden (map fst lists) || elem iden (map fst folds)
              then if isJust attrsForIden
                then return (FnCall ("generateHnat" ++ xnamespace ctx) (FnCall "length" (VarExpr iden : nextStep) : params))
                else return (FnCall ("generateHnat" ++ xnamespace ctx) (FnCall "length" [VarExpr iden] : params))
              else if isJust attrsForIden
                then return (FnCall ("addToEnvironment" ++ fromJust (lookup iden sorts) ++ context) ((VarExpr iden : nextStep) ++ params))
                else return (FnCall ("addToEnvironment" ++ fromJust (lookup iden sorts) ++ context) (VarExpr iden : params))
          where
            newAttrs = filter (\(left, _) ->
                let iden = liden left
                    ctxsForSort = fromJust (lookup sname ctxsBySname)
                    ctxsForIdenSort = fromJust (lookup (sortNameForIden iden ctor) ctxsBySname)
                in (iden == "" && any (\ctx -> linst left == xinst ctx) ctxsForSort) || any (\ctx -> linst left == xinst ctx) ctxsForIdenSort
              ) (cattrs ctor)
            attrsForIden = find (\(left, _) -> liden left == iden) newAttrs
            nextStep = maybeToList (applyOneRuleLogic (fromJust attrsForIden) [])
            lists = clists ctor
            folds = dropFold $ cfolds ctor
            sorts = csorts ctor
