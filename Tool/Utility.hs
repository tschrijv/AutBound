{-# OPTIONS_GHC -Wall #-}

module Utility where

import Data.Char
import GeneralTerms
import Data.Maybe

-- | Transform the first character of a string to lowercase
lowerFirst :: String -> String
lowerFirst [] = []
lowerFirst (first:rest) = toLower first : rest

-- | Transform the first character of a string to uppercase
upperFirst :: String -> String
upperFirst [] = []
upperFirst (first:rest) = toUpper first : rest

-- | Return the sort name for a given namespace name in a list of namespace
-- definitions
sortNameForNamespaceName :: NamespaceName -> [NamespaceDef] -> SortName
sortNameForNamespaceName name nsd = head [nsort ns | ns <- nsd, nname ns == name]

-- | Return a list of tuples with sort names and a boolean value indicating
-- whether they access variables
varAccessBySortName :: [SortDef] -> [(SortName, Bool)]
varAccessBySortName sd = map (\s -> (sname s, sortCanAccessVariables [] s)) sd
  where
    -- | Returns whether a given sort can access variables
    sortCanAccessVariables :: [SortName] -> SortDef -> Bool
    sortCanAccessVariables visited sort
      | hasVarCtor = True
      | name `elem` visited = False
      | otherwise = hasPathToVar
      where
        name = sname sort
        hasVarCtor = fromJust (lookup name sortsWithVarCtor)
        hasPathToVar = any (ctorHasVarAccess (name : visited)) (sctors sort)

        -- | Retuns a list of tuples containing a sort name and whether they
        -- contain any variable constructors
        sortsWithVarCtor :: [(SortName, Bool)]
        sortsWithVarCtor = [(sname s, hasVariables s) | s <- sd]
          where
            -- | Returns whether a sort definition contains any variable constructors
            hasVariables :: SortDef -> Bool
            hasVariables s = or [True | (MkVarConstructor _ _) <- sctors s]

        -- | Returns whether a given constructor accesses variables
        -- (either by being a variable constructor or by having an instance
        -- of a sort that accesses a variable)
        ctorHasVarAccess :: [SortName] -> ConstructorDef -> Bool
        ctorHasVarAccess _ (MkVarConstructor _ _) = True
        ctorHasVarAccess visited' ctor =
          any
            (\sortName ->
              sortCanAccessVariables visited' (head (filter (\s -> sname s == sortName) sd))
            )
            (cidenSorts ctor)

-- | Given a namespace name and a list of tuples containing a sort name
-- and assigned contexts, remove the contexts that use different namespaces
filterCtxsByNamespace :: NamespaceName -> [(SortName, [Context])] -> [(SortName, [Context])]
filterCtxsByNamespace namespace contextsBySortName = [
  (sortName, [ctx' | ctx' <- ctxs, xnamespace ctx' == namespace])
  | (sortName, ctxs) <- contextsBySortName]

-- Get the sort's name and contexts as a tuple
snameAndCtxs :: SortDef -> (SortName, [Context])
snameAndCtxs s = (sname s, sctxs s)

-- Return a list of tuples where the first element in the tuple is the sort name
-- and the second element is a list of constructors belonging to that sort
snameAndCtorsList :: [SortDef] -> [(SortName, [ConstructorDef])]
snameAndCtorsList s = map (\sort -> (sname sort, sctors sort)) s

-- Return a list of tuples where the first element in the tuple is the sort name
-- and the second element is a list of contexts belonging to that sort
snameAndCtxsList :: [SortDef] -> [(SortName, [Context])]
snameAndCtxsList = map snameAndCtxs

-- Get a list of tuples containing the instance names and their corresponding namespace name
-- of the sort with the given sort name
instanceAndNamespaceList :: [(SortName, [Context])] -> SortName -> [(InstanceName, NamespaceName)]
instanceAndNamespaceList ctxs sname 
  = let ctx = fromJust (lookup sname ctxs) in
      map (\c -> (xinst c, xnamespace c)) ctx

-- | Looks up the sort name for a given identifier in a constructor
sortNameForIden :: IdenName -> ConstructorDef -> SortName
sortNameForIden iden ctor = fromJust (lookup iden (dropFold (cfolds ctor) ++ clists ctor ++ csorts ctor))

-- | Produce a list of pairs with the first element being an identifier, the
-- second the list of attribute definitions that assign to this identifier
attrsByIden :: ConstructorDef -> [(IdenName, [AttributeDef])]
attrsByIden ctor = [
  (iden, filter (\(l, _) -> liden l == iden) (cattrs ctor))
  | iden <- cidens ctor]

-- | Drops the third element from each tuple in a list
dropFold :: [(String, String, String)] -> [(String, String)]
dropFold = map (\(a, b, _) -> (a, b))

-- | Determines if a given sort has a context for another sort
sortHasCtxForSort :: SortName -> SortName -> [NamespaceDef] -> [(SortName, [Context])] -> Bool
sortHasCtxForSort sortName ctxSort nsd ctxsBySname
  = let ctxs = [INH x y | INH x y <- fromJust (lookup sortName ctxsBySname)]
  in any (\ctx -> sortNameForNamespaceName (xnamespace ctx) nsd == ctxSort) ctxs
