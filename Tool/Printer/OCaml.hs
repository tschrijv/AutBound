{-# OPTIONS_GHC -Wall #-}

module Printer.OCaml where

import Data.Text.Prettyprint.Doc
import Program
import Utility
import GeneralTerms
import Data.List (intersperse)

instance Pretty Constructor where
  pretty (Constr n []) = pretty (upperFirst n)
  pretty (Constr n ts) = hsep (pretty (upperFirst n ++ " of") : punctuate (pretty " *") (map (\t -> pretty (lowerFirst t)) ts))

instance Pretty Parameter where
  pretty (VarParam n) = pretty (lowerFirst n)
  pretty (ConstrParam n ps) = parens (hsep (pretty (upperFirst n) : (punctuate comma (map pretty ps))))
  pretty (StringParam s) = pretty "\"" <> pretty s <> pretty "\""
  pretty (IntParam i) = pretty i

instance Pretty Expression where
  pretty (FnCall n ps) = parens $ hsep (pretty (lowerFirst n) : map pretty ps)
  pretty (ConstrInst n ps) = parens $ hsep (pretty (upperFirst n) : (punctuate comma (map pretty ps)))
  pretty (VarExpr x) = pretty (lowerFirst x)
  pretty (Minus a b) = parens (pretty a <+> pretty "-" <+> pretty b)
  pretty (IntExpr i) = pretty i
  pretty (StringExpr s) = pretty "\"" <> pretty s <> pretty "\""
  pretty (IfExpr c t f) = pretty "if" <+> pretty c <+> pretty "then" <+> pretty t <+> pretty "else" <+> pretty f
  pretty (GTEExpr a b) = parens (pretty a <+> pretty ">=" <+> pretty b)
  pretty (EQExpr a b) = parens (pretty a <+> pretty "==" <+> pretty b)
  pretty (ListExpr l) = pretty "[" <> hcat (punctuate comma (map pretty l)) <> pretty "]"
  pretty (LambdaExpr ps ex) = parens (pretty "fun" <+> hsep (map pretty ps) <+> pretty "->" <+> pretty ex)

instance Pretty TsType where
  pretty (TyBasic t) = pretty (lowerFirst t)
  pretty (TyList t) = pretty t <+> pretty "list"
  pretty (TyFunc t) = pretty "(" <> hsep (intersperse (pretty "->") (map pretty t)) <> pretty ")"
  pretty (TyVar) = pretty "Variable"
  pretty (TyGeneric s) = pretty "'" <> pretty s
  pretty (TyPrecondition t) = mempty

instance Pretty Function where
  pretty (Fn n ts descr lns) =
    let matchedParams = mapMatchedParams (map (\(ps, _) -> ps) lns)
        params = fst (head lns)
        replacedParams = replaceMatched matchedParams params
        matchedParamNames = [param | (param, b) <- zip replacedParams matchedParams, b]
    in 
      generateDescription <> nl <>
      (if or matchedParams
        then intoLines ((pretty "let rec" <+> pretty (lowerFirst n) <+> (hsep $ map pretty replacedParams) <+> pretty "= match" <+> hsep (punctuate comma (map pretty matchedParamNames)) <+> pretty "with") : map (oneMatchedLine matchedParams) lns)
        else pretty "let rec" <+> pretty (lowerFirst n) <+> hsep (map pretty (fst (head lns))) <+> pretty "=" <+> pretty (snd (head lns)) -- if no matched params, it should only have one line
      ) <> nl <>
      generateTypeSignature ts
    where
        mapMatchedParams :: [[Parameter]] -> [Bool]
        mapMatchedParams []      = []
        mapMatchedParams [params]    = map isMatched params
        mapMatchedParams (params:px) = [x || y | (x, y) <- zip (map isMatched params) (mapMatchedParams px)]

        isMatched :: Parameter -> Bool
        isMatched (ConstrParam _ _) = True
        isMatched (StringParam _)   = True
        isMatched (IntParam _)      = True
        isMatched _                 = False

        replaceMatched :: [Bool] -> [Parameter] -> [Parameter]
        replaceMatched ms params = [if matched then VarParam ("plv" ++ show i) else x | (matched, x, i) <- zip3 ms params [1..]]

        oneMatchedLine :: [Bool] -> ([Parameter], Expression) -> Doc a
        oneMatchedLine matched (ps, ex) = hsep $ (pretty "  |") : (punctuate comma [pretty p | (p, b) <- zip ps matched, b]) ++ [pretty "->", pretty ex]

        generateDescription :: Doc a
        generateDescription = if descr == "" then mempty
                                else pretty "(*" <+> pretty descr <+> pretty "*)"

        generateTypeSignature :: TypeSignature -> Doc a
        generateTypeSignature [] = mempty
        generateTypeSignature ty@(t:ts) = hsep $ 
          [pretty "val", pretty (lowerFirst n), pretty ":"] ++ (intersperse (pretty "->") (map (pretty) ty)) ++
          [pretty "= <fun>"]
        

nl :: Doc a
nl = pretty "\n"

intoLines :: [Doc a] -> Doc a
intoLines = hcat . punctuate nl

printProgram :: String -> Program -> Doc String
printProgram _ program =
  intoLines [
    printImports (imports program),
    printTypeDecls (types program),
    nl,
    printFunctions (functions program),
    printInstances (instances program),
    printCode (code program)
  ]

printImports :: [(String, [String])] -> Doc String
printImports imp =
  foldl
    (<>)
    (pretty "")
    (map (\x -> genImports x <+> pretty "\n") imp)
  where
    genImports :: (String, [String]) -> Doc String
    genImports (str, []) = pretty "open" <+> pretty str

printTypeDecls :: [(Type, [Constructor])] -> Doc String
printTypeDecls decls =
  intoLines $ punctuate nl $ map printOneType decls where
    printOneType :: (Type, [Constructor]) -> Doc String
    printOneType (t, cs) = hsep [
        pretty "type",
        pretty (lowerFirst t),
        pretty "=",
        hsep $ punctuate (pretty " |") (map pretty cs)
      ]

printFunctions :: [Function] -> Doc String
printFunctions fns = intoLines $ punctuate nl (map pretty fns)

printInstances :: [(Type, Type, [Function])] -> Doc String
printInstances ids = intoLines $ map (
    \(_, _, fns) -> intoLines [
      printFunctions (map (\(Fn n ts descr lns) -> Fn n ts descr lns) fns)
    ]
  ) ids

printCode :: [String] -> Doc String
printCode lns = intoLines $ map pretty lns
