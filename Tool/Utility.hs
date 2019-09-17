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
      | hasAccess = (sname, hasAccess)
      | otherwise = (sname, findPathToVariable)
      where
        sname = getName s
        hasAccess = fromJust (lookup sname (getTableOfHasVariable allSorts))
        sortDefTable = map (\x -> (getName x, x)) allSorts
        findPathToVariable =
          or
            (map
              (constructorCanAccessVariables sortDefTable listVisited)
              (getSortCtors s))

        getTableOfHasVariable :: [SortDef] -> [(SortName, Bool)]
        getTableOfHasVariable sd = [(getName s, hasVariables s) | s <- sd]

        -- function generating for each Sort, if it has access to some variable
        hasVariables :: SortDef -> Bool
        hasVariables s = or [True | (MkVarConstructor _ _) <- getSortCtors s]

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

filterTableBySameNamespace :: NamespaceInstance -> [(SortName, [NamespaceInstance])] -> [(SortName, [NamespaceInstance])]
filterTableBySameNamespace inst table = map (filterTableBySameNamespaceSort (getInstanceNameSpace inst)) table
  where
    filterTableBySameNamespaceSort :: NamespaceName -> (SortName, [NamespaceInstance]) -> (SortName, [NamespaceInstance])
    filterTableBySameNamespaceSort namespacename (sname, list) = (sname, newlist)
      where
        newlist = filter (\x -> getInstanceNameSpace x == namespacename) list
