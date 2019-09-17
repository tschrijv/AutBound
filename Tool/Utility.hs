module Utility where

import Data.Char
import GeneralTerms
import Data.Maybe

--function to detect if all names are unique
isUniqueInList :: [String] -> String -> Either String Bool
isUniqueInList [] _ = return True
isUniqueInList (str:strs) err =
  if any (\x -> x == str) strs
    then Left (show (str) ++ err)
    else isUniqueInList strs err

--helper to detect if different lists have unique names
shouldNotBeInSecondList :: [String] -> [String] -> String -> Either String Bool
shouldNotBeInSecondList [] _ _ = return True
shouldNotBeInSecondList (str:crest) sorts err =
  if any (\x -> x == str) sorts
    then Left (show (str) ++ err)
    else (shouldNotBeInSecondList crest sorts err)

--helper to detect if names in the first list  exist in the available second list
shouldBeInSecondList :: [String] -> [String] -> String -> Either String Bool
shouldBeInSecondList [] _ _ = return True
shouldBeInSecondList (str:strs) sorts err =
  if any (\x -> x == str) sorts
    then (shouldBeInSecondList strs sorts err)
    else Left (show (str) ++ err)

toLowerCaseFirst :: String -> String
toLowerCaseFirst (first:rest) = ((toLower first) : rest)

capitalize :: String -> String
capitalize (first:rest) = ((toUpper first) : rest)

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

getNameInstancenamespace :: NamespaceInstance -> NamespaceName
getNameInstancenamespace (INH _ name) = name
getNameInstancenamespace (SYN _ name) = name
