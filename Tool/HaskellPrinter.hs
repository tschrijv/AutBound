{-# OPTIONS_GHC -Wall #-}

module HaskellPrinter where

import Data.Text.Prettyprint.Doc
import Abstract

printProgram :: String -> Program -> Doc String
printProgram name program =
  hcat $ punctuate (pretty "\n") [
    printModuleDecl name,
    printImports (imports program),
    printTypeDecls (types program)
  ]

printModuleDecl :: String -> Doc String
printModuleDecl name = hsep [pretty "module", pretty name, pretty "where"]

printImports :: [(String, [String])] -> Doc String
printImports imp =
  foldl
    (<>)
    (pretty "")
    (map (\x -> genImports x <+> pretty "\n") imp)
  where
    genImports :: (String, [String]) -> Doc String
    genImports (str, []) = pretty "import" <+> pretty str
    genImports (str, rest) =
      pretty "import" <+> pretty str <+> parens (hsep (punctuate comma [pretty x | x <- rest]))

printTypeDecls :: [(Type, [Constructor])] -> Doc String
printTypeDecls decls =
  hcat $ punctuate (pretty "\n") (map printOneType decls) where
    printOneType :: (Type, [Constructor]) -> Doc String
    printOneType (t, cs) = hsep [
        pretty "data",
        pretty t,
        pretty "=",
        hsep $ punctuate (pretty "|") (map (\(n, pl) -> hsep (pretty n : map pretty pl)) cs),
        pretty "deriving(Show, Eq)"
      ]
