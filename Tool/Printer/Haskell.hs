{-# OPTIONS_GHC -Wall #-}

module Printer.Haskell where

import Data.Text.Prettyprint.Doc
import Data.Maybe
import Program
import Utility
import GeneralTerms
import Data.List (intersperse)

instance Pretty Constructor where
  pretty (Constr n ts) = hsep (pretty (upperFirst n) : map pretty ts)

instance Pretty Parameter where
  pretty (VarParam n) = pretty (lowerFirst n)
  pretty (ConstrParam n ps) = parens (hsep (pretty (upperFirst n) : map pretty ps))
  pretty (StringParam s) = pretty "\"" <> pretty s <> pretty "\""
  pretty (IntParam i) = pretty i

instance Pretty Expression where
  pretty (FnCall n ps) = parens $ hsep (pretty (lowerFirst n) : map pretty ps)
  pretty (ConstrInst n ps) = parens $ hsep (pretty (upperFirst n) : map pretty ps)
  pretty (VarExpr x) = pretty (lowerFirst x)
  pretty (Minus a b) = parens (pretty a <+> pretty "-" <+> pretty b)
  pretty (IntExpr i) = pretty i
  pretty (StringExpr s) = pretty "\"" <> pretty s <> pretty "\""
  pretty (IfExpr c t f) = pretty "if" <+> pretty c <+> pretty "then" <+> pretty t <+> pretty "else" <+> pretty f
  pretty (GTEExpr a b) = parens (pretty a <+> pretty ">=" <+> pretty b)
  pretty (EQExpr a b) = parens (pretty a <+> pretty "==" <+> pretty b)
  pretty (ListExpr l) = pretty "[" <> hcat (punctuate comma (map pretty l)) <> pretty "]"
  pretty (LambdaExpr ps ex) = parens (pretty "\\" <> hsep (map pretty ps) <+> pretty "->" <+> pretty ex)

instance Pretty TsType where
  pretty (TyBasic t) = pretty (upperFirst t)
  pretty (TyList t) = pretty "[" <> pretty t <> pretty "]"
  pretty (TyFunc t) = pretty "(" <> hsep (intersperse (pretty "->") (map pretty t)) <> pretty ")"
  pretty (TyVar) = pretty "Variable"
  pretty (TyGeneric s) = pretty s
  pretty (TyConstraints t) = 
    pretty "(" <> hsep (intersperse (pretty ",") (map (\(x,y) -> pretty (upperFirst x) <> pretty " " <> pretty y) t)) 
    <> pretty ")"

instance Pretty Function where
  pretty (Fn n ts descr lns) = 
    case (generateTypeSignature ts, generateDescription) of
      (Just prettyTs, Just prettyDescr) -> intoLines ([prettyDescr, prettyTs] ++ map oneLine lns) 
      (Nothing, Just prettyDescr) -> intoLines ([prettyDescr] ++ map oneLine lns)
      (Just prettyTs, Nothing) -> intoLines ([prettyTs] ++ map oneLine lns)
      (Nothing, Nothing) -> intoLines (map oneLine lns)
    where
    oneLine :: ([Parameter], Expression) -> Doc a
    oneLine (ps, ex) = hsep $ (pretty (lowerFirst n) : map pretty ps) ++ [pretty "=", pretty ex]

    generateTypeSignature :: TypeSignature -> Maybe (Doc a)
    generateTypeSignature [] = Nothing
    generateTypeSignature ty@(t:ts) = 
      case t of
      TyConstraints _ -> Just (hsep $ [pretty (lowerFirst n), pretty "::", pretty t,pretty "=>"] ++ 
                            (intersperse (pretty "->") (map (pretty) ts)))
      _ -> Just (hsep $ [pretty (lowerFirst n), pretty "::"] ++ (intersperse (pretty "->") (map (pretty) ty)))

    generateDescription :: Maybe (Doc a)
    generateDescription = if descr == "" then Nothing
                          else Just (pretty ("-- " ++ formatDescription descr))

    -- | Inserts "-- " after every new line "\n"
    formatDescription :: Description -> Description
    formatDescription [] = []
    formatDescription (x:xs)
      | x == '\n' = x : ("-- " ++ formatDescription xs)
      | otherwise = x : formatDescription xs

nl :: Doc a
nl = pretty "\n"

intoLines :: [Doc a] -> Doc a
intoLines = hcat . punctuate nl

printProgram :: String -> Program -> Doc String
printProgram name program =
  intoLines [
    printModuleDecl name,
    printImports (("Data.List", []) : imports program),
    printTypeDecls (types program),
    nl,
    printFunctions (functions program),
    printInstances (instances program),
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
  intoLines $ punctuate nl $ map printOneType decls where
    printOneType :: (Type, [Constructor]) -> Doc String
    printOneType (t, cs) = hsep [
        pretty "data",
        pretty (upperFirst t),
        pretty "=",
        hsep $ punctuate (pretty " |") (map pretty cs),
        pretty "deriving(Show, Eq)"
      ]

printFunctions :: [Function] -> Doc String
printFunctions fns = intoLines $ punctuate nl (map pretty fns)

printInstances :: [(Type, Type, [Function])] -> Doc String
printInstances ids = intoLines $ map (
    \(cls, typ, fns) -> intoLines [
      hsep [pretty "instance", pretty (upperFirst cls), pretty (upperFirst typ), pretty "where"],
      printFunctions (map (\(Fn n ts descr lns) -> Fn ("  " ++ n) ts descr lns) fns)
    ]
  ) ids

printCode :: [String] -> Doc String
printCode lns = intoLines $ map pretty lns
