{-# OPTIONS_GHC -Wall #-}

module HaskellPrinter where

import Data.Text.Prettyprint.Doc
import Abstract

instance Pretty Constructor where
  pretty (Constr n ts) = hsep (pretty n : map pretty ts)

instance Pretty Parameter where
  pretty (VarParam n) = pretty n
  pretty (ConstrParam n ps) = parens (hsep (pretty n : map pretty ps))

instance Pretty Expression where
  pretty (FnCall n ps) = hsep (pretty n : map pretty ps)
  pretty (ConstrInst n ps) = hsep (pretty n : map pretty ps)

instance Pretty Function where
  pretty (Fn n lns) = intoLines (map oneLine lns) where
    oneLine :: ([Parameter], Expression) -> Doc a
    oneLine (ps, ex) = hsep $ (pretty n : map pretty ps) ++ [pretty "=", pretty ex]

nl :: Doc a
nl = pretty "\n"

intoLines :: [Doc a] -> Doc a
intoLines = hcat . punctuate nl

printProgram :: String -> Program -> Doc String
printProgram name program =
  intoLines [
    printModuleDecl name,
    printImports (imports program),
    printTypeDecls (types program),
    printFunctions (functions program),
    -- printInstances (instances program),
    printCode (code program)
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
  intoLines (map printOneType decls) where
    printOneType :: (Type, [Constructor]) -> Doc String
    printOneType (t, cs) = hsep [
        pretty "data",
        pretty t,
        pretty "=",
        hsep $ punctuate (pretty "|") (map pretty cs),
        pretty "deriving(Show, Eq)"
      ]

printFunctions :: [Function] -> Doc String
printFunctions fns = intoLines $ map pretty fns

printCode :: [String] -> Doc String
printCode lns = intoLines $ map pretty lns
