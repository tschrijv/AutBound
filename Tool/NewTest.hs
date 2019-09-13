{-# OPTIONS_GHC -Wall #-}

import GeneralTerms
import WellFormed
import MyParser
import Program
import Converter
import Text.Parsec.String
import HaskellPrinter

import System.Environment

main :: IO ()
main = do
  [inputName, outputLanguage, outputName] <- getArgs
  result <- parseFromFile pLanguage inputName
  case result of
    Left err -> print err
    Right lang -> do
      toWrite <- toFileHaskell lang
      case toWrite of
        Left err    -> print err
        Right value -> writeFile (outputName ++ ".hs") (show (printProgram outputName value))

toFileHaskell :: Language -> IO (Either String Program)
toFileHaskell lang =
  case wellFormed lang of
    Left failtxt2 -> return (Left failtxt2)
    Right True -> return (Right (convert lang))
    Right False -> error "Language is not well formed!"
