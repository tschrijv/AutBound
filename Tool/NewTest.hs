{-# OPTIONS_GHC -Wall #-}

import GeneralTerms
import WellFormed
import MyParser
import Program
import Converter
import Text.Parsec.String
import Printer.Haskell as PHS
import Printer.OCaml as POC

import System.Environment

main :: IO ()
main = do
  [inputName, outputLanguage, outputName] <- getArgs
  parsingResult <- parseFromFile pLanguage inputName
  case parsingResult of
    Left err -> print err
    Right lang -> do
      conversionResult <- checkAndConvert lang
      case conversionResult of
        Left err    -> print err
        Right program -> writeToLanguage program outputLanguage outputName

checkAndConvert :: Language -> IO (Either String Program)
checkAndConvert lang =
  case wellFormed lang of
    Left failtxt2 -> return (Left failtxt2)
    Right True -> return (Right (convert lang))
    Right False -> error "Language is not well formed!"

writeToLanguage :: Program -> String -> String -> IO ()
writeToLanguage program lang name = case lang of
  "Haskell" -> writeFile (name ++ ".hs") (show (PHS.printProgram name program))
  "OCaml" -> writeFile (name ++ ".ml") (show (POC.printProgram name program))
