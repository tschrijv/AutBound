{-# OPTIONS_GHC -Wall #-}

module Main where

import System.Environment

import GeneralTerms
import WellFormed
import Parser
import Program
import Converter
import Text.Parsec.String
import Printer.Haskell as PHS
import Printer.OCaml as POC
import Variable.DeBruijn as VDB
import Variable.String as VS

-- | Read the following arguments from the command line:
-- * path of the input file
-- * name of the output language (Haskell or OCaml)
-- * variable representation type (DeBruijn or String)
-- * output module name
-- Outputs either an error message, or creates a module in the respective
-- language with the implementation of the input
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

-- | Check well-formedness of the input syntax and convert it if successful
checkAndConvert :: Language -> String -> IO (Either String Program)
checkAndConvert lang varType =
  case wellFormed lang of
    Left failtxt2 -> return (Left failtxt2)
    Right True -> case varType of
      "DeBruijn" -> return (Right (convert lang VDB.getFunctions))
      "String"   -> return (Right (convert lang VS.getFunctions))
      _          -> error "Unknown variable representation!"
    Right False -> error "Language is not well formed!"

-- | Convert the abstract syntax of the implementation to a specific language
-- and output it as a file
writeToLanguage :: Program -> String -> String -> IO ()
writeToLanguage program lang name = case lang of
  "Haskell" -> writeFile (name ++ ".hs") (show (PHS.printProgram name program))
  "OCaml"   -> writeFile (name ++ ".ml") (show (POC.printProgram name program))
  _         -> error "Unknown output language!"
