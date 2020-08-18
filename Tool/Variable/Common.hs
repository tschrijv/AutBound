{-# OPTIONS_GHC -Wall #-}

module Variable.Common (freeVarFunctions, mappingFunctions, sortNameForIden, firstToVarParams, dropFold, ExternalFunctions(..), applyInhCtxsToAttrs, inhCtxsForSortName, fnCallForIden, concatCallForIden) where

import Data.List
import Data.Maybe

import Program
import GeneralTerms
import Utility

data ExternalFunctions = EF {
  paramForCtor :: ConstructorDef -> [Parameter],
  freeVarExprForVarCtor :: String -> Expression,
  applyInhCtxsToAttrs :: SortName -> ConstructorDef -> (IdenName, [AttributeDef]) -> [(SortName, [Context])] -> Expression,
  includeBinders :: Bool
}

-- * Free variables
-- ----------------------------------------------------------------------------

-- | Generate free variable functions for every sort that has access to variable
-- constructors
freeVarFunctions :: Language -> ExternalFunctions -> [Function]
freeVarFunctions (_, sd, _, _) ef =
  let ctxsBySname = map snameAndCtxs sd
      varAccessBySname = varAccessBySortName sd
      sortsWithVarAccess = filter (\(MkDefSort sname _ _ _) -> fromJust (lookup sname varAccessBySname)) sd
  in map (\sort ->
    Fn ("freeVariables" ++ sname sort)
    (getTypeSignature (sname sort))
    (getDescription (sname sort))
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
    -- | Return the typesignature of the free variable functions for the given sort name
    getTypeSignature :: SortName -> TypeSignature
    getTypeSignature sortName
      = if includeBinders ef
        then [TyList TyVar, TyBasic sortName, TyList TyVar]
        else [TyVar, TyBasic sortName, TyList TyVar]

    -- | Return the description of the free variable functions for the given sort name
    getDescription :: SortName -> Description
    getDescription sortName
      = "Return a list of the free variables of the given " ++ sortName ++ 
         (if includeBinders ef
           then ".\nThe first argument represents the bound variables that are accumulated\n\
           \during the execution and should be initialized with the empty list."
           else ".\nThe first argument represents the number of bound variables with respect to the top\n\
           \level scope.")

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
                let addedBinders = (applyInhCtxsToAttrs ef) sname ctor (iden, iattrs) ctxsBySname
                    sortNameOfIden = sortNameForIden iden ctor
                in
                  if fromJust (lookup sortNameOfIden varAccessBySname)
                  then [concatCallForIden ctor iden ("freeVariables" ++ sortNameOfIden) [addedBinders]]
                  else []
              ) idensAndAttrs
        in if null callList then [ListExpr []] else callList

-- * Mapping functions
-- ----------------------------------------------------------------------------

-- | Generate mapping functions for every sort that has access to variable
-- constructors
mappingFunctions :: Language -> ExternalFunctions -> [Function]
mappingFunctions (nsd, sd, _, _) ef =
  let ctxsBySname = map snameAndCtxs sd
      varAccessBySname = varAccessBySortName sd
      sortsWithVarAccess = filter (\(MkDefSort sname _ _ _) -> fromJust (lookup sname varAccessBySname)) sd
  in map (
    \(MkDefSort sortName ctxs ctors _) ->
        Fn (mapFnForSortName sortName)
        (getTypeSignature sortName ctxs nsd)
        (getDescription sortName ctxs nsd)
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
    -- | Return the typesignature of the mapping function for the given sort name
    getTypeSignature :: SortName -> [Context] -> [NamespaceDef] -> TypeSignature
    getTypeSignature sortName ctxs nsd
        = let sorts = [nsort | INH _ nsName2 <- ctxs, MkNameSpace nsName1 nsort <- nsd, nsName1 == nsName2] in
          (if includeBinders ef 
          then [TyFunc [TyVar, TyBasic sort, TyBasic sort] | sort <- sorts] ++ [TyList TyVar, TyBasic sortName, TyBasic sortName]
          else [TyFunc [TyVar, TyBasic sort, TyBasic sort] | sort <- sorts] ++ [TyVar, TyBasic sortName, TyBasic sortName]
          )

    -- | Return the description of the mapping function for the given sort name
    getDescription :: SortName -> [Context] -> [NamespaceDef] -> Description
    getDescription sortName ctxs nsd
        = let sorts = [(nsort, nsName1) | MkNameSpace nsName1 nsort <- nsd, INH _ nsName2 <- ctxs, nsName1 == nsName2] 
              len = length sorts
              mulplicity = head (map snd (filter fst [(len == 1, (" is", "function")),
                                                (len > 1, (" are", "functions"))])) in
          "Return the " ++ sortName ++ " where " ++
          (intercalate ", " ["on" ++ nsName | (_, nsName) <- sorts]) ++ fst mulplicity ++ " applied to each\n" ++
          (intercalate ", " [sname | (sname, _) <- sorts]) ++ " in the given " ++ sortName ++ " respectively.\n" ++
          (if includeBinders ef
           then "The second last argument represents the bound variables that are accumulated\n\
           \during the execution and should be initialized with the empty list.\n\
           \The accumulated bound variables are also passed as an argument to the supplied " ++ snd mulplicity ++ "."
           else "The second argument represents the number of bound variables with respect to the top\n\
           \level scope. It is also passed as an argument to the supplied " ++ snd mulplicity ++ ".")

    -- | Return the name of the mapping function for the given sort name
    mapFnForSortName :: SortName -> String
    mapFnForSortName sname = sname ++ "map"

    -- | Generate the map function's body for a given contructor in the sort
    -- (a function call to the namespace's processing function in case of a variable,
    -- and a constructor call with its identifiers also mapped otherwise)
    mappingExprForCtor :: SortName -> ConstructorDef -> [(SortName, [Context])] -> [(SortName, Bool)] -> Expression
    mappingExprForCtor sortName (MkVarConstructor ctorName _) ctxsBySname _ =
      FnCall ("on" ++ xnamespace (head (fromJust (lookup sortName ctxsBySname)))) [ -- TODO: this is a suspicious head call
        VarExpr "c",
        ConstrInst ctorName [VarExpr "var"]
      ]
    mappingExprForCtor sortName ctor ctxsBySname varAccessBySname =
      let binder = if includeBinders ef && isBind ctor then [VarExpr "b"] else []
      in
        ConstrInst
          (cname ctor)
          (
            binder
            ++ map mapFnCallForIden idensAndAttrs
            ++ [VarExpr (x ++ show n) | (x, n) <- zip (cnatives ctor) [1 :: Int ..]]
          )
      where
        idensAndAttrs = attrsByIden ctor
        folds = dropFold (cfolds ctor)
        lists = clists ctor

        -- | Construct a mapping function call for an identifier
        mapFnCallForIden :: (IdenName, [AttributeDef]) -> Expression
        mapFnCallForIden (iden, idenAttrs)
          = if fromJust (lookup sortNameOfIden varAccessBySname)
              then fnCallForIden ctor iden (mapFnForSortName sortNameOfIden) (fnCallsForCtxs (fromJust (lookup sortNameOfIden ctxsBySname)) ++ addedBinders)
              else VarExpr iden
          where
            addedBinders = [(applyInhCtxsToAttrs ef) sortName ctor (iden, idenAttrs) ctxsBySname]
            sortNameOfIden = sortNameForIden iden ctor

            -- | Return a function reference for the processing functions
            -- of the namespaces in the list of contexts
            fnCallsForCtxs :: [Context] -> [Expression]
            fnCallsForCtxs ctx = [VarExpr ("on" ++ namespace) | INH _ namespace <- ctx]

-- * Helper functions
-- ----------------------------------------------------------------------------

fnCallForIden :: ConstructorDef -> IdenName -> String -> [Expression] -> Expression
fnCallForIden ctor iden fnName params
  = if iden `elem` map fst folds
    then FnCall "fmap" [FnCall fnName params, VarExpr iden]
    else if iden `elem` map fst lists
      then FnCall "map" [FnCall fnName params, VarExpr iden]
      else FnCall fnName (params ++ [VarExpr iden])
    where
      folds = dropFold $ cfolds ctor
      lists = clists ctor

concatCallForIden :: ConstructorDef -> IdenName -> String -> [Expression] -> Expression
concatCallForIden ctor iden fnName params
  = if iden `elem` map fst folds
    then FnCall "concat" [FnCall "fmap" [FnCall fnName params, VarExpr iden]]
    else if iden `elem` map fst lists
      then FnCall "concat" [FnCall "map" [FnCall fnName params, VarExpr iden]]
      else FnCall fnName (params ++ [VarExpr iden])
    where
      folds = dropFold $ cfolds ctor
      lists = clists ctor

-- | Returns the list of inherited contexts for a given sort name
inhCtxsForSortName :: SortName -> [(SortName, [Context])] -> [Context]
inhCtxsForSortName sname ctxsForSortName = [INH x y | INH x y <- ctxs]
  where
    ctxs = fromJust (lookup sname ctxsForSortName)

-- | In a list of tuples, converts the first elements to a list of variable parameters
firstToVarParams :: [(String, String)] -> [Parameter]
firstToVarParams = map (VarParam . fst)
