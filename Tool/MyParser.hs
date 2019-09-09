{-# OPTIONS_GHC -Wall #-}

-- parser mostly inspired by the inbound haskell parser
module MyParser (pLanguage) where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Token

import GeneralTerms

myDef :: LanguageDef st
myDef =
  haskellStyle
    { opStart = oneOf ":!#$%&*+./<=>?@\\^|-~,;"
    , opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~,;"
    , reservedNames =
        [ "namespace"
        , "sort"
        , "lhs"
        , "syn"
        , "inh"
        , "c"
        , "rewrite"
        , "import"
        , "HaskellCode"
        ]
    , reservedOpNames = ["@", "=", ",", ".", ";"]
    }

inboundTokenParser = makeTokenParser myDef
pIdentifier        = identifier inboundTokenParser
pBrackets          = brackets inboundTokenParser
pSymbol            = symbol inboundTokenParser
pColon             = colon inboundTokenParser
pDot               = dot inboundTokenParser
pComma             = comma inboundTokenParser
pReserved          = reserved inboundTokenParser
pParens            = parens inboundTokenParser
pBraces            = braces inboundTokenParser
pWhiteSpace        = whiteSpace inboundTokenParser

pLanguage :: Parser Language
pLanguage = do
  pWhiteSpace
  idecls <- many pImports
  ndecls <- many pNameSpaceDecl
  sdecls <- manyTill pSortDecl pHaskellLiteral
  hsCode <- pEnd
  return (ndecls, sdecls, idecls, hsCode)

-- * Imports
-- ----------------------------------------------------------------------------

pImports :: Parser [String]
pImports = do
  pReserved "import"
  name <- pImportsName
  chooselist <- pImportChoose
  return (name : chooselist)

pImportsName :: Parser String
pImportsName =
  pParens $ do
    list <- many pNameDot
    a <- pIdentifier
    return (listToString list ++ a)

pNameDot :: Parser String
pNameDot =
  try
    (do a <- pIdentifier
        _ <- pDot
        return a)

listToString :: [String] -> String
listToString []       = ""
listToString (x:rest) = x ++ "." ++ listToString rest

pImportChoose :: Parser [String]
pImportChoose = try pSpecifically <|> return []

pSpecifically :: Parser [String]
pSpecifically =
  pParens $ many pIdentifier

-- * Namespaces
-- ----------------------------------------------------------------------------

pNameSpaceDecl :: Parser NameSpaceDef
pNameSpaceDecl =
  MkNameSpace <$ pReserved "namespace" <*> pNameSpaceName <* pColon <*>
  pSortName <*>
  pEnvAdd

pNameSpaceName :: Parser NameSpaceName
pNameSpaceName = pIdentifier

pEnvAdd :: Parser [String]
pEnvAdd =
  many $ do
    _ <- pComma
    pIdentifier

-- * Sort declarations
-- ----------------------------------------------------------------------------

pSortDecl :: Parser SortDef
pSortDecl = try pSortDeclRewrite <|> pSortDeclNoRewrite

pSortDeclRewrite :: Parser SortDef
pSortDeclRewrite = do
  _ <- pReserved "sort"
  b <- pSortName
  _ <- pReserved "rewrite"
  c <- many pInstance
  d <- many pCtorDecl
  return (MkDefSort b c d True)

pSortDeclNoRewrite :: Parser SortDef
pSortDeclNoRewrite = do
  _ <- pReserved "sort"
  b <- pSortName
  c <- many pInstance
  d <- many pCtorDecl
  return (MkDefSort b c d False)

pSortName :: Parser SortName
pSortName = pIdentifier

pInstance :: Parser NamespaceInstance
pInstance = pInh <|> pSyn

pCtorDecl :: Parser ConstructorDef
pCtorDecl = do
  _ <- pSymbol "|"
  a <- pCtorName
  try (pCtorVar a) <|>
   try (pCtorBindState (MkBindConstructor a [] [] [] ("", "") [] [])) <|>
   pCtorNotVarState (MkDefConstructor a [] [] [] [] [])

pInh :: Parser NamespaceInstance
pInh = do
  pReserved "inh"
  a <- pIdentifier
  b <- pIdentifier
  return (INH a b)

pSyn :: Parser NamespaceInstance
pSyn = do
  pReserved "syn"
  a <- pIdentifier
  b <- pIdentifier
  return (SYN a b)

pCtorName :: Parser ConstructorName
pCtorName = pIdentifier

pCtorVar :: String -> Parser ConstructorDef
pCtorVar name = do
  a <- pVarNameSpace
  return (MkVarConstructor name a)

pCtorBindState :: ConstructorDef -> Parser ConstructorDef
pCtorBindState (MkBindConstructor name lists sorts folds namespace rules haskelltypes) =
  try (pConstructorListsNameState cons) <|> try (pFoldState cons) <|>
  pConstructorSortNameState cons <|>
  pHaskellTypesState cons <|>
  pRuleStateBind cons
  where
    cons = MkBindConstructor name lists sorts folds namespace rules haskelltypes

pCtorNotVarState :: ConstructorDef -> Parser ConstructorDef
pCtorNotVarState (MkDefConstructor name lists sorts folds rules haskelltypes) =
  try (pConstructorListsNameState cons) <|> try (pFoldState cons) <|>
  pConstructorSortNameState cons <|>
  pHaskellTypesState cons <|>
  pRuleState cons
  where
    cons = MkDefConstructor name lists sorts folds rules haskelltypes

pVarNameSpace :: Parser NameSpaceName
pVarNameSpace =
  pParens $ do
    _ <- pIdentifier
    _ <- pSymbol "@"
    pIdentifier

pConstructorListsNameState :: ConstructorDef -> Parser ConstructorDef
pConstructorListsNameState (MkDefConstructor name lists sorts folds rules haskelltypes) = do
  a <- pConstructorListsName
  pCtorNotVarState
    (MkDefConstructor name (lists ++ [a]) sorts folds rules haskelltypes)
pConstructorListsNameState (MkBindConstructor name lists sorts folds namespace rules haskelltypes) = do
  a <- pConstructorListsName
  pCtorBindState
    (MkBindConstructor
        name
        (lists ++ [a])
        sorts
        folds
        namespace
        rules
        haskelltypes)

pFoldState :: ConstructorDef -> Parser ConstructorDef
pFoldState (MkDefConstructor name lists sorts folds rules haskelltypes) = do
  a <- pFolds
  pCtorNotVarState
    (MkDefConstructor name lists sorts (folds ++ [a]) rules haskelltypes)
pFoldState (MkBindConstructor name lists sorts folds namespace rules haskelltypes) = do
  a <- pFolds
  pCtorBindState
    (MkBindConstructor
        name
        lists
        sorts
        (folds ++ [a])
        namespace
        rules
        haskelltypes)

pConstructorSortNameState :: ConstructorDef -> Parser ConstructorDef
pConstructorSortNameState (MkDefConstructor name lists sorts folds rules haskelltypes) = do
  a <- pConstructorSortName
  pCtorNotVarState
    (MkDefConstructor name lists (sorts ++ [a]) folds rules haskelltypes)
pConstructorSortNameState (MkBindConstructor name lists sorts folds namespace rules haskelltypes) = do
  a <- pConstructorSortName
  pCtorBindState
    (MkBindConstructor
        name
        lists
        (sorts ++ [a])
        folds
        namespace
        rules
        haskelltypes)

pHaskellTypesState :: ConstructorDef -> Parser ConstructorDef
pHaskellTypesState (MkDefConstructor name lists sorts folds rules haskelltypes) = do
  a <- pHaskellTypes
  pCtorNotVarState
    (MkDefConstructor name lists sorts folds rules (haskelltypes ++ [a]))
pHaskellTypesState (MkBindConstructor name lists sorts folds namespace rules haskelltypes) = do
  a <- pHaskellTypes
  pCtorBindState
    (MkBindConstructor
        name
        lists
        sorts
        folds
        namespace
        rules
        (haskelltypes ++ [a]))

pRuleStateBind :: ConstructorDef -> Parser ConstructorDef
pRuleStateBind (MkBindConstructor name lists sorts folds _namespace _rules haskelltypes) = do
  a <- pConstructorNameSpaceName
  b <- many pRule
  return (MkBindConstructor name lists sorts folds a b haskelltypes)

pRuleState :: ConstructorDef -> Parser ConstructorDef
pRuleState (MkDefConstructor name lists sorts folds _rules haskelltypes) = do
  a <- many pRule
  return (MkDefConstructor name lists sorts folds a haskelltypes)

pConstructorListsName :: Parser (String, SortName)
pConstructorListsName =
  pParens $ do
    a <- pIdentifier
    _ <- pColon
    b <- pBracketSort
    return (a, b)

pFolds :: Parser (String, SortName, FoldName)
pFolds =
  pParens $ do
    iden <- pIdentifier
    _ <- pColon
    foldname <- pIdentifier
    sort <- pIdentifier
    return (iden, sort, foldname)

pConstructorSortName :: Parser (String, SortName)
pConstructorSortName =
  pParens $ do
    a <- pIdentifier
    _ <- pColon
    b <- pIdentifier
    return (a, b)

pHaskellTypes :: Parser HaskellTypeName
pHaskellTypes = pBraces pIdentifier

pConstructorNameSpaceName :: Parser (String, NameSpaceName)
pConstructorNameSpaceName =
  pBrackets $ do
    a <- pIdentifier
    _ <- pSymbol ":"
    b <- pIdentifier
    return (a, b)

pRule :: Parser NameSpaceRule
pRule = do
  a <- pLeftExpr
  _ <- pSymbol "="
  b <- pRightExpr
  return (a, b)

pBracketSort :: Parser SortName
pBracketSort = pBrackets pIdentifier

pLeftExpr :: Parser LeftExpr
pLeftExpr = pLHSLeftExpr <|> pSubLeftExpr

pRightExpr :: Parser RightExpr
pRightExpr = try pRightExprAdd <|> pRightExprLHS <|> pRightExprSub

pLHSLeftExpr :: Parser LeftExpr
pLHSLeftExpr = do
  pReserved "lhs"
  _ <- pDot
  a <- pIdentifier
  return (LeftLHS a)

pSubLeftExpr :: Parser LeftExpr
pSubLeftExpr = do
  a <- pIdentifier
  _ <- pDot
  b <- pIdentifier
  return (LeftSub a b)

pRightExprAdd :: Parser RightExpr
pRightExprAdd = do
  a <- pRightExprLHS <|> pRightExprSub
  _ <- pSymbol ","
  b <- pIdentifier
  return (RightAdd a b)

pRightExprLHS :: Parser RightExpr
pRightExprLHS = do
  pReserved "lhs"
  _ <- pSymbol "."
  a <- pIdentifier
  return (RightLHS a)

pRightExprSub :: Parser RightExpr
pRightExprSub = do
  a <- pIdentifier
  _ <- pSymbol "."
  b <- pIdentifier
  return (RightSub a b)

-- * Haskell code
-- ----------------------------------------------------------------------------

pHaskellLiteral :: Parser ()
pHaskellLiteral =
  pReserved "HaskellCode" <|> eof

pEnd :: Parser [String]
pEnd = try pHsCode <|> parseEOF

pHsCode :: Parser [String]
pHsCode = do
  x <- line
  xs <-
    many $ do
      _ <- newline
      line
  eof
  return (x : xs)

parseEOF :: Parser [String]
parseEOF = do
  eof
  return []

line :: Parser String
line = many $ noneOf "\n"
