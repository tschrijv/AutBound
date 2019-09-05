import           Data.Text.Prettyprint.Doc
import           GeneralTerms
import           MyParser
import           System.Process
import           Text.Parsec.Error
import           Text.Parsec.String
import           ToHaskellPrint

toFileHaskell ::
     Language
  -> String
  -> IO (Either (Text.Parsec.Error.ParseError) (Either String (Doc String)))
toFileHaskell lang name =
  case wellFormed lang of
    Left failtxt2 -> return (Right (Left failtxt2))
    Right _ -> return (Right (Right (toHaskellLanguageStart lang name)))

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
        Right (Left err)    -> print err
        Right (Right value) -> writeFile "haskellOutput.hs" (show value)

genLangNoFormat :: String -> IO ()
genLangNoFormat name = do
  result <- parseFromFile pLanguage name
  case result of
    Left err -> print err
    Right lang -> do
      toWrite <- toFileHaskell lang "haskellOutput"
      case toWrite of
        Right (Left err) -> print err
        Right (Right value) -> do
          a <- writeFile "haskellOutput.hs" (show value)
         -- b <- callCommand "hfmt -w"
          return ()

genLang :: String -> IO ()
genLang name = do
  result <- parseFromFile pLanguage name
  case result of
    Left err -> print err
    Right lang -> do
      toWrite <- toFileHaskell lang "haskellOutput"
      case toWrite of
        Right (Left err) -> print err
        Right (Right value) -> do
          a <- writeFile "haskellOutput.hs" (show value)
          b <- callCommand "hfmt -w"
          return ()

genLangName :: String -> String -> IO ()
genLangName nameinput nameoutput = do
  result <- parseFromFile pLanguage nameinput
  case result of
    Left err -> print err
    Right lang -> do
      toWrite <- toFileHaskell lang nameoutput
      case toWrite of
        Right (Left err) -> print err
        Right (Right value) -> do
          a <- writeFile (nameoutput ++ ".hs") (show value)
          b <- callCommand "hfmt -w"
          return ()
