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
    userTypes = getTypes,
    variableInstances = getVariableInstances,
    variableFunctions = getVariableFunctions,
    nativeCode = (\_ _ -> [])
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
    Fn "compare" [] ("") 
    ([
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
getVariableFunctions lan@(nsd, _, _, _) varT = getHNatModifiers varT ++ getGenerators nsd ++ getShift lan ++ mappingFunctions lan ef ++ substFunctions lan ++ freeVarFunctions lan ef ++ getEnvFunctions lan

getHNatModifiers :: (Type, [Constructor]) -> [Function]
getHNatModifiers (_, hnatc) =
  let cs = delete (Constr "Z" []) hnatc
  in [
    Fn "plus" [TyVar, TyVar, TyVar] ("Add two Variables.") ([
      ([ConstrParam "Z" [], VarParam "h"], VarExpr "h"),
      ([VarParam "h", ConstrParam "Z" []], VarExpr "h")
    ] ++ map generatePlus cs)
  ,
    Fn "minus" [TyVar, TyVar, TyVar] 
    ("Substract the second Variable from the first. The first Variable has to\n\
    \be greater than the second one.") ([
      ([ConstrParam "Z" [], ConstrParam "Z" []], ConstrInst "Z" []),
      ([ConstrParam "Z" [], VarParam "_"], FnCall "error" [StringExpr "You cannot substract zero with a positive number"]),
      ([VarParam "result", ConstrParam "Z" []], VarExpr "result")
    ] ++ map generateMinus [(left, right) | left <- cs, right <- cs])
  ]
  where
    generatePlus :: Constructor -> ([Parameter], Expression)
    generatePlus (Constr n _) = ([ConstrParam n [VarParam "x1"], VarParam "x2"], ConstrInst n [FnCall "plus" [VarExpr "x1", VarExpr "x2"]])

    generateMinus :: (Constructor, Constructor) -> ([Parameter], Expression)
    generateMinus (Constr n1 _, Constr n2 _)
      | n1 == n2 = ([ConstrParam n1 [VarParam "h1"], ConstrParam n2 [VarParam "h2"]], FnCall "minus" [VarExpr "h1", VarExpr "h2"])
      | otherwise = (
          [ConstrParam n1 [VarParam "h1"], ConstrParam n2 [VarParam "h2"]],
          ConstrInst n1 [FnCall "minus" [VarExpr "h1", ConstrInst n2 [VarExpr "h2"]]])

getGenerators :: [NamespaceDef] -> [Function]
getGenerators = map (
    \ns ->
      let name = nname ns
          fnName = "generateHnat" ++ name
          constr = 'S' : name
      in
      Fn fnName [TyBasic "Int", TyVar, TyVar]
      ("Apply " ++ constr ++ " n times to the second argument c.") [
        ([IntParam 0, VarParam "c"], VarExpr "c"),
        ([VarParam "n", VarParam "c"], ConstrInst constr [FnCall fnName [Minus (VarExpr "n") (IntExpr 1), VarExpr "c"]])
      ]
  )

getShift :: Language -> [Function]
getShift (nsd, sd, _, _) = let accessVarTable = varAccessBySortName sd
  in concat [getShiftHelpers sd op accessVarTable ++ getShiftFunctions sd nsd op accessVarTable | op <- ["plus", "minus"]]

getShiftHelpers :: [SortDef] -> String -> [(SortName, Bool)] -> [Function]
getShiftHelpers sd opName varAccessTable = let filtered = filter (\(MkDefSort sname _ _ _) -> isJust (lookup sname varAccessTable)) sd
  in concatMap (\(MkDefSort sname _ cdefs _) -> constructorsToCheckShift cdefs sname opName) filtered
  where
    constructorsToCheckShift :: [ConstructorDef] -> SortName -> String -> [Function]
    constructorsToCheckShift cdefs sname op = [
      Fn (sname ++ "shiftHelp" ++ op) 
      [TyVar, TyVar, TyBasic sname, TyBasic sname] 
      ("Perform the shift operation on one " ++ sname ++ " with the " ++ consName ++ " constructor.")
      [
        ([VarParam "d", VarParam "c", ConstrParam consName [VarParam "var"]],
        IfExpr
          (GTEExpr (VarExpr "var") (VarExpr "c"))
          -- (plus c (plus d (minus var c))))
          (if (op == "plus") then (ConstrInst consName [FnCall "plus" [VarExpr "c", FnCall "plus" [VarExpr "d", FnCall "minus" [VarExpr "var", VarExpr "c"]]]]) else (ConstrInst consName [FnCall op [VarExpr "var", VarExpr "d"]]))
          (ConstrInst consName [VarExpr "var"])
        )
      ] | MkVarConstructor consName _ <- cdefs]

getShiftFunctions :: [SortDef] -> [NamespaceDef] -> String -> [(SortName, Bool)] -> [Function]
getShiftFunctions sd defs opName varAccessTable = let filtered = filter (\s -> fromJust (lookup (sname s) varAccessTable)) sd
  in map (\(MkDefSort sname namespaceDecl _ _) ->
    Fn
      (sname ++ "shift" ++ opName) 
      [TyVar, TyBasic sname, TyBasic sname] 
      ("Perform the shift operation on a " ++ sname ++ ".")
      [
        ([VarParam "d", VarParam "t"],
        FnCall
          (sname ++ "map")
          (declarationsToFunctions namespaceDecl defs opName ++ [ConstrInst "Z" [], VarExpr "t"])
        )
      ]
  ) filtered
  where
    declarationsToFunctions :: [Context] -> [NamespaceDef] -> String -> [Expression]
    declarationsToFunctions nsi nsd op = let filtered = [INH x y | INH x y <- nsi]
      in map (\(INH _ namespaceName) ->
        FnCall (sortNameForNamespaceName namespaceName nsd ++ "shiftHelp" ++ op) [VarExpr "d"]
      ) filtered

getEnvFunctions :: Language -> [Function]
getEnvFunctions (nsd, sd, _, _)
  = let ctxsBySname = map snameAndCtxs sd
    in concatMap (\sort ->
      let synCtxs = [SYN x y | SYN x y <- sctxs sort]
      in if null synCtxs then [] else
      mapAndMerge ( 
        splitFunctions (map (\ctor ->
          generateSortSynSystemOneConstructor (sname sort) nsd ctxsBySname ctor (head synCtxs)
        ) (sctors sort)) (sname sort) ([],[])
      )
    ) sd
    where
      -- | Splits the generated functions in two such that each has the same function name
      splitFunctions :: [Function] -> SortName -> ([Function], [Function]) -> ([Function], [Function])
      splitFunctions [] _ f12 = f12
      splitFunctions (x@(Fn name _ _ _):xs) sname (f1,f2) = 
        if name == "addToEnvironment" ++ sname
          then splitFunctions (xs) sname (f1 ++ [x], f2)
          else splitFunctions xs sname (f1, f2 ++ [x])

      -- | Merges the tuple of lists of functions to 2 functions: the first correspondends with the merged function of the first
      -- | argument in the tuple, the second with the merged function of the second argument.
      mapAndMerge :: ([Function], [Function]) -> [Function]
      mapAndMerge (f1, f2) = (mergeFunctions f1) ++ (mergeFunctions f2)

      -- | Merges a list of functions to another list of functions which contains a single function or the empty list if the empty
      -- | list was given as an argument. The new merged function has the same name, type signature and description as the first
      -- | function in the supplied list and contains all expressions as its expression.
      mergeFunctions :: [Function] -> [Function]
      mergeFunctions [] = []
      mergeFunctions [x] = [x]
      mergeFunctions (x1@(Fn name1 ts1 descr1 expr1):(x2@(Fn name2 ts2 descr2 expr2):xs)) = 
        mergeFunctions ((Fn name1 ts1 descr1 (expr1 ++ expr2)) : xs)


      generateSortSynSystemOneConstructor :: SortName -> [NamespaceDef] -> [(SortName, [Context])] -> ConstructorDef -> Context -> Function
      generateSortSynSystemOneConstructor sname _ _ (MkVarConstructor ctorName _) _
        = Fn ("addToEnvironment" ++ sname) 
        [TyBasic sname, TyVar, TyVar] 
        ("") 
        [([ConstrParam ctorName [VarParam "var"], VarParam "c"], VarExpr "c")]
      generateSortSynSystemOneConstructor sname nsd ctxsBySname ctor ctx
        = Fn ("addToEnvironment" ++ sname ++ xinst ctx) 
        [TyBasic sname, TyVar, TyVar] 
        ("Bring the variables that are bound by the given " ++ sname ++ " into scope.\n\
        \The second argument represents the number of bound variables with respect to the top\n\
        \level scope.") 
        [([ConstrParam ctorName (firstToVarParams sorts ++ [VarParam "_" | _ <- hTypes]), VarParam "c"], getEnvFunctionGenerate)]
          where
            filteredSnameAndCtxs = filterCtxsByNamespace (xnamespace ctx) ctxsBySname
            ctorName = cname ctor
            sorts = csorts ctor
            hTypes = cnatives ctor
            attrs = cattrs ctor

            getEnvFunctionGenerate :: Expression
            getEnvFunctionGenerate
              | null $ fromJust (lookup "lhs" allrules) = VarExpr "c"
              | otherwise = navigateAttrs start
              where
                allrules = collectRulesSyn
                start = fromJust (
                  find
                    (\x -> linst (fst x) == xinst ctx)
                    (fromJust (lookup "lhs" allrules))
                  )

            collectRulesSyn :: [(IdenName, [AttributeDef])]
            collectRulesSyn =
              foldl
                (++)
                [("lhs", [(LeftLHS c, r) | (LeftLHS c, r) <- attrs])]
                (map (\(iden, _) -> [collectRulesOfIdSyn iden]) sorts)
              where
                collectRulesOfIdSyn :: IdenName -> (IdenName, [AttributeDef])
                collectRulesOfIdSyn iden = (iden, filter (\(LeftSub fieldname _, RightSub _ _) -> fieldname == iden) attrs)

            navigateAttrs :: AttributeDef -> Expression
            navigateAttrs (l, RightAdd expr _) = ConstrInst ("S" ++ xnamespace ctx) [navigateAttrs (l, expr)]
            navigateAttrs (LeftLHS _, RightLHS _) = VarExpr "c"
            navigateAttrs (LeftSub _ _, RightLHS _) = VarExpr "c"
            navigateAttrs (_, RightSub iden _)
              | isJust newrule = FnCall functionName [VarExpr iden, navigateAttrs (fromJust newrule)]
              | otherwise = FnCall functionName [VarExpr iden, VarExpr "c"]
              where
                newrule = find (\(l, _) -> liden l == iden) attrs
                functionName = "addToEnvironment" ++ fromJust (lookup iden sorts) ++ xinst ctx

-- | Generates the following for sorts with variable access:
-- * Substitute helper functions for variable constructors
-- * Substitute functions for every sort that is related to the given sort by
-- the first sort having a context with a variable of the type of the second sort
substFunctions :: Language -> [Function]
substFunctions (nsd, sd, _, _) =
  let varAccessBySname = varAccessBySortName sd
      sortsWithVarAccess = filter (\sort -> fromJust (lookup (sname sort) varAccessBySname)) sd
  in concatMap (\(MkDefSort sortName ctxs ctors rewrite) ->
    let inhCtxs = [INH x y | INH x y <- ctxs]
    in
      [
        Fn (sortName ++ "SubstituteHelp") 
        [TyBasic sortName, TyVar, TyBasic sortName, TyBasic sortName] 
        ("Perform one substitution step on a " ++ sortName ++ " with the " ++ ctorName ++ " constructor.")
        [
          (
            [VarParam "sub", VarParam "c", ConstrParam ctorName [VarParam "var"]],
            _substExpr sortName ctorName
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
            mapCall = FnCall (sortName ++ "map") (paramFnCallsForCtxs ctx ctxs nsd ++ [VarExpr "orig", VarExpr "t"])
        in Fn
          (sortName ++ sortOfCtxNamespace ++ "Substitute") 
          [TyBasic sortName, TyVar, TyBasic sortName, TyBasic sortName] 
          ("Substitute every occurence of the second argument orig with the first\n\
          \argument sub in the given " ++ sortName ++ ".")
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

_getCtorParams :: ConstructorDef -> [Parameter]
_getCtorParams (MkVarConstructor consName _) = [ConstrParam consName [VarParam "var"]]
_getCtorParams cons = [ConstrParam consName (firstToVarParams (dropFold folds ++ lists ++ sorts) ++ [VarParam (x ++ show n) | (x, n) <- zip hTypes [1 :: Int ..]])]
  where
    consName = cname cons
    folds = cfolds cons
    lists = clists cons
    sorts = csorts cons
    hTypes = cnatives cons

_varCtorFreeVar :: String -> Expression
_varCtorFreeVar name = IfExpr (GTEExpr (VarExpr "var") (VarExpr "c")) (ListExpr [FnCall "minus" [VarExpr "var", VarExpr "c"]]) (ListExpr [])

_oneDeeper namespace expr = ConstrInst ("S" ++ namespace) expr

_substExpr sname consName =
  IfExpr (EQExpr (VarExpr "var") (VarExpr "c"))
    (FnCall (sname ++ "shiftplus") [VarExpr "c", VarExpr "sub"])
    (ConstrInst consName [VarExpr "var"])

-- | For every inherited context of a sort, apply nested modifiers to the
-- returned "c" variable
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
            nextStep = maybeToList (applyOneAttr (fromJust attrsForIden) [])
            lists = clists ctor
            folds = dropFold $ cfolds ctor
            sorts = csorts ctor

ef = EF {
  paramForCtor = _getCtorParams,
  freeVarExprForVarCtor = _varCtorFreeVar,
  applyInhCtxsToAttrs = _applyInhCtxsToAttrs,
  includeBinders = False
}
