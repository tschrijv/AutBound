module Utility where

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
