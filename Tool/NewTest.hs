{-# OPTIONS_GHC -Wall #-}

import GeneralTerms
import WellFormed
import MyParser
import Abstract
import Converter
import Text.Parsec.String
import HaskellPrinter

main :: IO ()
main = do
  putStrLn "Name of input file:"
  name <- getLine
  result <- parseFromFile pLanguage name
  case result of
    Left err -> print err
    Right lang -> do
      toWrite <- toFileHaskell lang
      case toWrite of
        Left err    -> print err
        Right value -> writeFile "HaskellOutput.hs" (show (printProgram "HaskellOutput" value))

toFileHaskell :: Language -> IO (Either String Program)
toFileHaskell lang =
  case wellFormed lang of
    Left failtxt2 -> return (Left failtxt2)
    Right _ -> return (Right (convert lang)) -- TODO: what about non well-formedness?
