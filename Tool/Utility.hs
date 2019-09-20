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
sortNameForNamespaceName name nsd = head [lowerFirst $ nsort ns | ns <- nsd, nname ns == name]

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
            (map snd (csorts ctor ++ clists ctor) ++ map (\(_, b, _) -> b) (cfolds ctor))

-- | Given a namespace name and a list of tuples containing a sort name
-- and assigned contexts, remove the contexts that use different namespaces
filterCtxsByNamespace :: NamespaceName -> [(SortName, [Context])] -> [(SortName, [Context])]
filterCtxsByNamespace namespace contextsBySortName = [
  (sortName, [ctx' | ctx' <- ctxs, xnamespace ctx' == namespace])
  | (sortName, ctxs) <- contextsBySortName]

-- TODO
snameAndCtxs :: SortDef -> (SortName, [Context])
snameAndCtxs s = (sname s, sctxs s)

-- | Produce a list of pairs with the first element being an identifier, the
-- second the list of attribute definitions that assign to this identifier
attrsByIden :: ConstructorDef -> [(IdenName, [AttributeDef])]
attrsByIden ctor = [
  (iden, filter (\(l, _) -> liden l == iden) (cattrs ctor))
  | (iden, _) <- (dropFold (cfolds ctor) ++ clists ctor ++ csorts ctor)]

-- | Drops the third element from each tuple in a list
dropFold :: [(String, String, String)] -> [(String, String)]
dropFold = map (\(a, b, _) -> (a, b))
