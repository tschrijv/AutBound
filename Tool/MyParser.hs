module MyParser
  (
    -- parseSpecification ,
  pLanguage
  ) where

-- parser mostly inspired by the inbound haskell parser
import           Control.Applicative
import           Control.Monad
import           Data.Char
import           Data.Either
-- import           Data.Set             (Set)
-- import qualified Data.Set             as S
import           System.IO

import qualified Text.Parsec          as P
import qualified Text.Parsec.Language as P
import qualified Text.Parsec.Token    as P

import           GeneralTerms

-- toLowerCaseFirst :: String -> String
-- toLowerCaseFirst (first:rest) = ((toLower first) : rest)

myDef :: P.LanguageDef st
myDef =
  P.haskellStyle
    { P.opStart = P.oneOf ":!#$%&*+./<=>?@\\^|-~,;"
    , P.opLetter = P.oneOf ":!#$%&*+./<=>?@\\^|-~,;"
    , P.reservedNames =
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
    , P.reservedOpNames = ["@", "=", ",", ".", ";"]
    }

inboundTokenParser = P.makeTokenParser myDef
pIdentifier        = P.identifier inboundTokenParser
pBrackets          = P.brackets inboundTokenParser
pSymbol            = P.symbol inboundTokenParser
pColon             = P.colon inboundTokenParser
pDot               = P.dot inboundTokenParser
pComma             = P.comma inboundTokenParser
pReserved          = P.reserved inboundTokenParser
pParens            = P.parens inboundTokenParser
pBraces            = P.braces inboundTokenParser
pWhiteSpace        = P.whiteSpace inboundTokenParser
pCommaSep1         = P.commaSep1 inboundTokenParser

type Parser a = P.Parsec String () a

pLanguage :: Parser Language
pLanguage = do
  pWhiteSpace
  idecls <- many pImports
  ndecls <- many pNameSpaceDecl
  sdecls <- P.manyTill pSortDecl pHaskellLiteral
  hsCode <- pEnd
  return $ (ndecls, sdecls, idecls, hsCode)

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
    return ((listToString list) ++ a)

pNameDot :: Parser String
pNameDot =
  P.try
    (do a <- pIdentifier
        pDot
        return a)

listToString :: [String] -> String
listToString []       = ""
listToString (x:rest) = x ++ "." ++ listToString rest

pImportChoose :: Parser [String]
pImportChoose = P.try (pSpecifically) <|> return []

pSpecifically :: Parser [String]
pSpecifically =
  pParens $ do
    a <- many pIdentifier
    return a

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
    pComma
    pIdentifier

-- * Sort declarations
-- ----------------------------------------------------------------------------

pSortDecl :: Parser SortDef
pSortDecl = (P.try pSortDeclRewrite) <|> pSortDeclNoRewrite

pSortDeclRewrite :: Parser SortDef
pSortDeclRewrite = do
  a <- pReserved "sort"
  b <- pSortName
  e <- pReserved "rewrite"
  c <- many pInstance
  d <- many pCtorDecl
  return (MkDefSort b c d True)

pSortDeclNoRewrite :: Parser SortDef
pSortDeclNoRewrite = do
  a <- pReserved "sort"
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
  pSymbol "|"
  a <- pCtorName
  (P.try (pCtorVar a) <|>
   P.try (pCtorBindState (MkBindConstructor a [] [] [] ("", "") [] [])) <|>
   (pCtorNotVarState (MkDefConstructor a [] [] [] [] [])))

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
  (P.try (pConstructorListsNameState cons)) <|> (P.try (pFoldState cons)) <|>
  (pConstructorSortNameState cons) <|>
  (pHaskellTypesState cons) <|>
  pRuleStateBind cons
  where
    cons =
      (MkBindConstructor name lists sorts folds namespace rules haskelltypes)

pCtorNotVarState :: ConstructorDef -> Parser ConstructorDef
pCtorNotVarState (MkDefConstructor name lists sorts folds rules haskelltypes) =
  (P.try (pConstructorListsNameState cons)) <|> (P.try (pFoldState cons)) <|>
  (pConstructorSortNameState cons) <|>
  (pHaskellTypesState cons) <|>
  pRuleState cons
  where
    cons = (MkDefConstructor name lists sorts folds rules haskelltypes)

pVarNameSpace :: Parser NameSpaceName
pVarNameSpace =
  pParens $ do
    pIdentifier
    pSymbol "@"
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
pRuleStateBind (MkBindConstructor name lists sorts folds namespace rules haskelltypes) = do
  a <- pConstructorNameSpaceName
  b <- many pRule
  return (MkBindConstructor name lists sorts folds a b haskelltypes)

pRuleState :: ConstructorDef -> Parser ConstructorDef
pRuleState (MkDefConstructor name lists sorts folds rules haskelltypes) = do
  a <- many pRule
  return (MkDefConstructor name lists sorts folds a haskelltypes)

pConstructorListsName :: Parser (String, SortName)
pConstructorListsName =
  pParens $ do
    a <- pIdentifier
    pColon
    b <- pBracketSort
    return (a, b)

pFolds :: Parser (String, SortName, FoldName)
pFolds =
  pParens $ do
    id <- pIdentifier
    pColon
    foldname <- pIdentifier
    sort <- pIdentifier
    return (id, sort, foldname)

pConstructorSortName :: Parser (String, SortName)
pConstructorSortName =
  pParens $ do
    a <- pIdentifier
    pColon
    b <- pIdentifier
    return (a, b)

pHaskellTypes :: Parser HaskellTypeName
pHaskellTypes =
  pBraces $ do
    a <- pIdentifier
    return a

pConstructorNameSpaceName :: Parser (String, NameSpaceName)
pConstructorNameSpaceName =
  pBrackets $ do
    a <- pIdentifier
    pSymbol ":"
    b <- pIdentifier
    return (a, b)

pRule :: Parser NameSpaceRule
pRule = do
  a <- pLeftExpr
  pSymbol "="
  b <- pRightExpr
  return (a, b)

pBracketSort :: Parser SortName
pBracketSort =
  pBrackets $ do
    b <- pIdentifier
    return b

pLeftExpr :: Parser LeftExpr
pLeftExpr = pLHSLeftExpr <|> pSubLeftExpr

pRightExpr :: Parser RightExpr
pRightExpr = P.try (pRightExprAdd) <|> pRightExprLHS <|> pRightExprSub

pLHSLeftExpr :: Parser LeftExpr
pLHSLeftExpr = do
  pReserved "lhs"
  pDot
  a <- pIdentifier
  return (LHS a)

pSubLeftExpr :: Parser LeftExpr
pSubLeftExpr = do
  a <- pIdentifier
  pDot
  b <- pIdentifier
  return (Sub a b)

pRightExprAdd :: Parser RightExpr
pRightExprAdd = do
  a <- (pRightExprLHS <|> pRightExprSub)
  pSymbol ","
  b <- pIdentifier
  return (ExprAdd a b)

pRightExprLHS :: Parser RightExpr
pRightExprLHS = do
  pReserved "lhs"
  pSymbol "."
  a <- pIdentifier
  return (ExprLHS a)

pRightExprSub :: Parser RightExpr
pRightExprSub = do
  a <- pIdentifier
  pSymbol "."
  b <- pIdentifier
  return (ExprSub a b)

-- * Haskell code
-- ----------------------------------------------------------------------------

pHaskellLiteral :: Parser ()
pHaskellLiteral =
  (do a <- pReserved "HaskellCode"
      return a) <|>
  P.eof

pEnd :: Parser [String]
pEnd = P.try (pHsCode) <|> parseEOF

pHsCode :: Parser [String]
pHsCode = do
  x <- line
  xs <-
    many $ do
      P.newline
      line
  P.eof
  return (x : xs)

parseEOF :: Parser [String]
parseEOF = do
  P.eof
  return []

line :: Parser String
line = many $ P.noneOf "\n"

-- parseSpecification :: String -> Either P.ParseError Language
-- parseSpecification = P.parse (pLanguage) ""
