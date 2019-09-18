module Utility where

import Data.Char
import GeneralTerms
import Data.Maybe

toLowerCaseFirst :: String -> String
toLowerCaseFirst (first:rest) = ((toLower first) : rest)

capitalize :: String -> String
capitalize (first:rest) = ((toUpper first) : rest)

emptyOrToList :: Maybe a -> [a]
emptyOrToList ex = maybe [] (\a -> [a]) ex

lookForSortName :: NamespaceName -> [NamespaceDef] -> SortName
lookForSortName name ((MkNameSpace name2 sortname _):rest)
  | name2 == name = toLowerCaseFirst sortname
  | otherwise = lookForSortName name rest

getVarAccessTable :: [SortDef] -> [(SortName, Bool)]
getVarAccessTable sList = map (sortCanAccessVariables sList []) sList
  where
    sortCanAccessVariables :: [SortDef] -> [SortName] -> SortDef -> (SortName, Bool)
    sortCanAccessVariables allSorts listVisited s
      | hasAccess = (name, hasAccess)
      | otherwise = (name, findPathToVariable)
      where
        name = sname s
        hasAccess = fromJust (lookup name (getTableOfHasVariable allSorts))
        sortDefTable = map (\x -> (sname x, x)) allSorts
        findPathToVariable =
          or
            (map
              (constructorCanAccessVariables sortDefTable listVisited)
              (sctors s))

        getTableOfHasVariable :: [SortDef] -> [(SortName, Bool)]
        getTableOfHasVariable sd = [(sname s, hasVariables s) | s <- sd]

        -- function generating for each Sort, if it has access to some variable
        hasVariables :: SortDef -> Bool
        hasVariables s = or [True | (MkVarConstructor _ _) <- sctors s]

        constructorCanAccessVariables :: [(SortName, SortDef)] -> [SortName] -> ConstructorDef -> Bool
        constructorCanAccessVariables table visited (MkVarConstructor _ _) = True
        constructorCanAccessVariables table visited (MkBindConstructor _ listSorts sorts folds _ _ _) =
          or
            (map
              (hasAccessSortName table visited)
              ((map snd sorts) ++ (map snd listSorts) ++ map (\(a, b, c) -> b) folds))
        constructorCanAccessVariables table visited (MkDefConstructor _ listSorts sorts folds _ _) =
          or
            (map
              (hasAccessSortName table visited)
              ((map snd sorts) ++ (map snd listSorts) ++ map (\(a, b, c) -> b) folds))

        hasAccessSortName :: [(SortName, SortDef)] -> [SortName] -> SortName -> Bool
        hasAccessSortName table visited nextSort
          | any (\x -> x == nextSort) visited = False
          | otherwise =
            snd
              (sortCanAccessVariables
                (map snd table)
                (nextSort : visited)
                (fromJust (lookup nextSort table)))

filterContextsForSameNamespace :: Context -> [(SortName, [Context])] -> [(SortName, [Context])]
filterContextsForSameNamespace ctx table = [
  (sortName, [ctx' | ctx' <- ctxs, xnamespace ctx' == xnamespace ctx])
  | (sortName, ctxs) <- table]
