{-# OPTIONS_GHC -Wall #-}

import GeneralTerms
import WellFormed
import MyParser
import Program
import Converter
import Text.Parsec.String
import Printer.Haskell as PHS
import Printer.OCaml as POC
import Variable.DeBruijn as VDB
import Variable.String as VS

import System.Environment

main :: IO ()
main = do
  [inputName, outputLanguage, varType, outputName] <- getArgs
  parsingResult <- parseFromFile pLanguage inputName
  case parsingResult of
    Left err -> print err
    Right lang -> do
      conversionResult <- checkAndConvert lang varType
      case conversionResult of
        Left err    -> print err
        Right program -> writeToLanguage program outputLanguage outputName

checkAndConvert :: Language -> String -> IO (Either String Program)
checkAndConvert lang varType =
  case wellFormed lang of
    Left failtxt2 -> return (Left failtxt2)
    Right True -> case varType of
      "DeBruijn" -> return (Right (convert lang (VF {variableType = VDB.getVariableType, variableInstances = VDB.getVariableInstances, variableFunctions = VDB.getVariableFunctions})))
      "String" -> return (Right (convert lang (VF {variableType = VS.getVariableType, variableInstances = VS.getVariableInstances, variableFunctions = VS.getVariableFunctions})))
    Right False -> error "Language is not well formed!"

writeToLanguage :: Program -> String -> String -> IO ()
writeToLanguage program lang name = case lang of
  "Haskell" -> writeFile (name ++ ".hs") (show (PHS.printProgram name program))
  "OCaml" -> writeFile (name ++ ".ml") (show (POC.printProgram name program))
