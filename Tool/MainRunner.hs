{-# OPTIONS_GHC -Wall #-}

import Data.Text.Prettyprint.Doc
import GeneralTerms
import WellFormed
import MyParser
import Text.Parsec.String
import ToHaskellPrint

main :: IO ()
main = do
  putStrLn "Name of input file:"
  name <- getLine
  result <- parseFromFile pLanguage name
  case result of
    Left err -> print err
    Right lang -> do
      toWrite <- toFileHaskell lang "haskellOutput"
      case toWrite of
        Left err    -> print err
        Right value -> writeFile "HaskellOutput.hs" (show value)

toFileHaskell :: Language -> String -> IO (Either String (Doc String))
toFileHaskell lang name =
  case wellFormed lang of
    Left failtxt2 -> return (Left failtxt2)
    Right _ -> return (Right (toHaskellLanguageStart lang name)) -- TODO: what about non well-formedness?
