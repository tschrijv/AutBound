{-# OPTIONS_GHC -Wall #-}

-- parser mostly inspired by the inbound haskell parser
module MyParser (pLanguage) where

import Data.List
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
    , reservedOpNames = ["@", "=", ",", ".", ";", ":", "|"]
    }

inboundTokenParser :: TokenParser st
inboundTokenParser = makeTokenParser myDef

pIdentifier :: Parser String
pIdentifier        = identifier inboundTokenParser

pBrackets :: Parser a -> Parser a
pBrackets          = brackets inboundTokenParser

pReserved :: String -> Parser ()
pReserved          = reserved inboundTokenParser

pParens :: Parser a -> Parser a
pParens            = parens inboundTokenParser

pBraces :: Parser a -> Parser a
pBraces            = braces inboundTokenParser

pWhiteSpace :: Parser ()
pWhiteSpace        = whiteSpace inboundTokenParser

pReservedOp :: String -> Parser ()
pReservedOp = reservedOp inboundTokenParser

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

-- | Parse one complete import line
pImports :: Parser (String, [String])
pImports = do
  pReserved "import"
  name <- pImportsName
  chooselist <- pImportChoose
  return (name, chooselist)

-- | Parse the module name (dot-separated strings)
pImportsName :: Parser String
pImportsName =
  pParens $ do
    list <- many pNameDot
    a <- pIdentifier
    return (intercalate "." (list ++ [a]))

-- | Parse one section of the module name
pNameDot :: Parser String
pNameDot =
  try
    (do a <- pIdentifier
        pReservedOp "."
        return a)

-- | Parse specifically selected entities from the module
pImportChoose :: Parser [String]
pImportChoose = try (pParens $ many pIdentifier) <|> return []

-- * Namespaces
-- ----------------------------------------------------------------------------

-- | Parse a namespace declaration
pNameSpaceDecl :: Parser NameSpaceDef
pNameSpaceDecl =
  MkNameSpace <$ pReserved "namespace" <*> pNameSpaceName <* pReservedOp ":" <*>
  pSortName <*>
  pEnvAdd

-- | Parse a namespace's name
pNameSpaceName :: Parser NameSpaceName
pNameSpaceName = pIdentifier

-- | Parse a sort's name
pSortName :: Parser SortName
pSortName = pIdentifier

-- | TODO: ???
pEnvAdd :: Parser [String]
pEnvAdd =
  many $ do
    pReservedOp ","
    pIdentifier

-- * Sort declarations
-- ----------------------------------------------------------------------------

-- | Parse a sort declaration
pSortDecl :: Parser SortDef
pSortDecl = try pSortDeclRewrite <|> pSortDeclNoRewrite

-- | Parse a sort declaration with a rewrite rule
pSortDeclRewrite :: Parser SortDef
pSortDeclRewrite = do
  pReserved "sort"
  b <- pSortName
  pReserved "rewrite"
  c <- many pInstance
  d <- many pCtorDecl
  return (MkDefSort b c d True)

-- | Parse a sort declaration with no rewrite rule
pSortDeclNoRewrite :: Parser SortDef
pSortDeclNoRewrite = do
  pReserved "sort"
  b <- pSortName
  c <- many pInstance
  d <- many pCtorDecl
  return (MkDefSort b c d False)

-- | Parse a namespace instance
pInstance :: Parser NamespaceInstance
pInstance = pInh <|> pSyn

-- | Parse an inherited namespace instance
pInh :: Parser NamespaceInstance
pInh = do
  pReserved "inh"
  a <- pInstanceName
  b <- pNameSpaceName
  return (INH a b)

-- | Parse a synthesized namespace instance
pSyn :: Parser NamespaceInstance
pSyn = do
  pReserved "syn"
  a <- pInstanceName
  b <- pNameSpaceName
  return (SYN a b)

-- | Parse a namespace instance's name
pInstanceName :: Parser SortName
pInstanceName = pIdentifier

-- | Parse a constructor definition
pCtorDecl :: Parser ConstructorDef
pCtorDecl = do
  pReservedOp "|"
  a <- pCtorName
  try (pCtorVar a) <|>
   try (pCtorBindState (MkBindConstructor a [] [] [] ("", "") [] [])) <|>
   pCtorNotVarState (MkDefConstructor a [] [] [] [] [])

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
    pReservedOp "@"
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
    pReservedOp ":"
    b <- pBracketSort
    return (a, b)

pFolds :: Parser (String, SortName, FoldName)
pFolds =
  pParens $ do
    iden <- pIdentifier
    pReservedOp ":"
    foldname <- pIdentifier
    sortName <- pIdentifier
    return (iden, sortName, foldname)

pConstructorSortName :: Parser (String, SortName)
pConstructorSortName =
  pParens $ do
    a <- pIdentifier
    pReservedOp ":"
    b <- pIdentifier
    return (a, b)

pHaskellTypes :: Parser HaskellTypeName
pHaskellTypes = pBraces pIdentifier

pConstructorNameSpaceName :: Parser (String, NameSpaceName)
pConstructorNameSpaceName =
  pBrackets $ do
    a <- pIdentifier
    pReservedOp ":"
    b <- pIdentifier
    return (a, b)

pRule :: Parser NameSpaceRule
pRule = do
  a <- pLeftExpr
  pReservedOp "="
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
  pReservedOp "."
  a <- pIdentifier
  return (LeftLHS a)

pSubLeftExpr :: Parser LeftExpr
pSubLeftExpr = do
  a <- pIdentifier
  pReservedOp "."
  b <- pIdentifier
  return (LeftSub a b)

pRightExprAdd :: Parser RightExpr
pRightExprAdd = do
  a <- pRightExprLHS <|> pRightExprSub
  pReservedOp ","
  b <- pIdentifier
  return (RightAdd a b)

pRightExprLHS :: Parser RightExpr
pRightExprLHS = do
  pReserved "lhs"
  pReservedOp "."
  a <- pIdentifier
  return (RightLHS a)

pRightExprSub :: Parser RightExpr
pRightExprSub = do
  a <- pIdentifier
  pReservedOp "."
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
