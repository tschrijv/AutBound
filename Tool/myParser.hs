module MyParser
  ( parseSpecification
  , pLanguage
  ) where

-- parser mostly inspired by the inbound haskell parser
import           Control.Applicative
import           Control.Monad
import           Data.Char
import           Data.Either
import           Data.Set             (Set)
import qualified Data.Set             as S
import           System.IO

import qualified Text.Parsec          as P
import qualified Text.Parsec.Language as P
import qualified Text.Parsec.Token    as P

import           GeneralTerms

toLowerCaseFirst :: String -> String
toLowerCaseFirst (first:rest) = ((toLower first) : rest)

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

pIdentifier = P.identifier inboundTokenParser

pBrackets = P.brackets inboundTokenParser

pSymbol = P.symbol inboundTokenParser

pColon = P.colon inboundTokenParser

pDot = P.dot inboundTokenParser

pComma = P.comma inboundTokenParser

pReserved = P.reserved inboundTokenParser

pParens = P.parens inboundTokenParser

pBraces = P.braces inboundTokenParser

pWhiteSpace = P.whiteSpace inboundTokenParser

pCommaSep1 = P.commaSep1 inboundTokenParser

type Parser a = P.Parsec String () a

pNameSpaceName :: Parser NameSpaceName
pNameSpaceName = pIdentifier

pSortName :: Parser SortName
pSortName = pIdentifier

pCtorName :: Parser ConstructorName
pCtorName = pIdentifier

pConstructorNameSpaceName :: Parser (String, NameSpaceName)
pConstructorNameSpaceName =
  pBrackets $ do
    a <- pIdentifier
    pSymbol ":"
    b <- pIdentifier
    return (a, b)

pConstructorSortName :: Parser (String, SortName)
pConstructorSortName =
  pParens $ do
    a <- pIdentifier
    pColon
    b <- pIdentifier
    return (a, b)

pConstructorListsName :: Parser (String, SortName)
pConstructorListsName =
  pParens $ do
    a <- pIdentifier
    pColon
    b <- pBracketSort
    return (a, b)

pBracketSort :: Parser SortName
pBracketSort =
  pBrackets $ do
    b <- pIdentifier
    return b

pHaskellTypes :: Parser HaskellTypeName
pHaskellTypes =
  pBraces $ do
    a <- pIdentifier
    return a

pFolds :: Parser (String, SortName, FoldName)
pFolds =
  pParens $ do
    id <- pIdentifier
    pColon
    foldname <- pIdentifier
    sort <- pIdentifier
    return (id, sort, foldname)

pCtorNotVarState :: ConstructorDef -> Parser ConstructorDef
pCtorNotVarState (MkDefConstructor name lists sorts folds rules haskelltypes) =
  (P.try (pConstructorListsNameState cons)) <|> (P.try (pFoldState cons)) <|>
  (pConstructorSortNameState cons) <|>
  (pHaskellTypesState cons) <|>
  pRuleState cons
  where
    cons = (MkDefConstructor name lists sorts folds rules haskelltypes)

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

pRuleState :: ConstructorDef -> Parser ConstructorDef
pRuleState (MkDefConstructor name lists sorts folds rules haskelltypes) = do
  a <- many pRule
  return (MkDefConstructor name lists sorts folds a haskelltypes)

pCtorBindState :: ConstructorDef -> Parser ConstructorDef
pCtorBindState (MkBindConstructor name lists sorts folds namespace rules haskelltypes) =
  (P.try (pConstructorListsNameState cons)) <|> (P.try (pFoldState cons)) <|>
  (pConstructorSortNameState cons) <|>
  (pHaskellTypesState cons) <|>
  pRuleStateBind cons
  where
    cons =
      (MkBindConstructor name lists sorts folds namespace rules haskelltypes)

pRuleStateBind :: ConstructorDef -> Parser ConstructorDef
pRuleStateBind (MkBindConstructor name lists sorts folds namespace rules haskelltypes) = do
  a <- pConstructorNameSpaceName
  b <- many pRule
  return (MkBindConstructor name lists sorts folds a b haskelltypes)

pCtorVar :: String -> Parser ConstructorDef
pCtorVar name = do
  a <- pVarNameSpace
  return (MkVarConstructor name a)

pSubLeftExpr :: Parser LeftExpr
pSubLeftExpr = do
  a <- pIdentifier
  pDot
  b <- pIdentifier
  return (Sub a b)

pLHSLeftExpr :: Parser LeftExpr
pLHSLeftExpr = do
  pReserved "lhs"
  pDot
  a <- pIdentifier
  return (LHS a)

pLeftExpr :: Parser LeftExpr
pLeftExpr = pLHSLeftExpr <|> pSubLeftExpr

pRightExprLHS :: Parser RightExpr
pRightExprLHS = do
  pReserved "lhs"
  pSymbol "."
  a <- pIdentifier
  return (ExprLHS a)

pRightExprAdd :: Parser RightExpr
pRightExprAdd = do
  a <- (pRightExprLHS <|> pRightExprSub)
  pSymbol ","
  b <- pIdentifier
  return (ExprAdd a b)

pRightExprSub :: Parser RightExpr
pRightExprSub = do
  a <- pIdentifier
  pSymbol "."
  b <- pIdentifier
  return (ExprSub a b)

pRightExpr :: Parser RightExpr
pRightExpr = P.try (pRightExprAdd) <|> pRightExprLHS <|> pRightExprSub

pRule :: Parser NameSpaceRule
pRule = do
  a <- pLeftExpr
  pSymbol "="
  b <- pRightExpr
  return (a, b)

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

pInstance :: Parser NamespaceInstance
pInstance = pInh <|> pSyn

pCtorDecl :: Parser ConstructorDef
pCtorDecl = do
  pSymbol "|"
  a <- pCtorName
  (P.try (pCtorVar a) <|>
   P.try (pCtorBindState (MkBindConstructor a [] [] [] ("", "") [] [])) <|>
   (pCtorNotVarState (MkDefConstructor a [] [] [] [] [])))

pVarNameSpace :: Parser NameSpaceName
pVarNameSpace =
  pParens $ do
    pIdentifier
    pSymbol "@"
    pIdentifier

pSortDeclNoRewrite :: Parser SortDef
pSortDeclNoRewrite = do
  a <- pReserved "sort"
  b <- pSortName
  c <- many pInstance
  d <- many pCtorDecl
  return (MkDefSort b c d False)

pSortDeclRewrite :: Parser SortDef
pSortDeclRewrite = do
  a <- pReserved "sort"
  b <- pSortName
  e <- pReserved "rewrite"
  c <- many pInstance
  d <- many pCtorDecl
  return (MkDefSort b c d True)

pSortDecl :: Parser SortDef
pSortDecl = (P.try pSortDeclRewrite) <|> pSortDeclNoRewrite

pNameSpaceDecl :: Parser NameSpaceDef
pNameSpaceDecl =
  MkNameSpace <$ pReserved "namespace" <*> pNameSpaceName <* pColon <*>
  pSortName <*>
  pEnvAdd

pEnvAdd :: Parser [String]
pEnvAdd =
  many $ do
    pComma
    pIdentifier

pNameDot :: Parser String
pNameDot =
  P.try
    (do a <- pIdentifier
        pDot
        return a)

pImportsName :: Parser String
pImportsName =
  pParens $ do
    list <- many pNameDot
    a <- pIdentifier
    return ((listToString list) ++ a)

pSpecifically :: Parser [String]
pSpecifically =
  pParens $ do
    a <- many pIdentifier
    return a

pImportChoose :: Parser [String]
pImportChoose = P.try (pSpecifically) <|> return []

pImports :: Parser [String]
pImports = do
  pReserved "import"
  name <- pImportsName
  chooselist <- pImportChoose
  return (name : chooselist)

listToString :: [String] -> String
listToString []       = ""
listToString (x:rest) = x ++ "." ++ listToString rest

pHsCode :: Parser [String]
pHsCode = do
  x <- line
  xs <-
    many $ do
      P.newline
      line
  P.eof
  return (x : xs)

line :: Parser String
line = many $ P.noneOf "\n"

parseEOF :: Parser [String]
parseEOF = do
  P.eof
  return []

pHaskellLiteral :: Parser ()
pHaskellLiteral =
  (do a <- pReserved "HaskellCode"
      return a) <|>
  P.eof

pEnd :: Parser [String]
pEnd = P.try (pHsCode) <|> parseEOF

pLanguage :: Parser Language
pLanguage = do
  pWhiteSpace
  idecls <- many pImports
  ndecls <- many pNameSpaceDecl
  sdecls <- P.manyTill pSortDecl pHaskellLiteral
  hsCode <- pEnd
  return $ (ndecls, sdecls, idecls, hsCode)

parseSpecification :: String -> Either P.ParseError Language
parseSpecification = P.parse (pLanguage) ""
