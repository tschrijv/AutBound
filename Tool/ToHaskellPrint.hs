{-# OPTIONS_GHC -Wall #-}

module ToHaskellPrint (toHaskellLanguageStart) where

import Data.Char
import Data.List
import Data.Maybe
import Data.Text.Prettyprint.Doc
import GeneralTerms

toHaskellLanguageStart :: Language -> String -> Doc String
toHaskellLanguageStart lan name = toHaskellLanguage lan [] [] [] name []

toHaskellLanguage ::
     Language
  -> [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> [SortDef]
  -> String
  -> [[String]]
  -> Doc String
toHaskellLanguage ([], [], [], code) namespaces table accsorts name imports =
  generateModule namespaces table accsorts name <+>
  pretty "\n" <> pretty "import Data.List \n" <> genImportsAll imports <>
  toHaskellSort accsorts <>
  pretty "data HNat = Z" <+>
  (toHaskellHnat namespaces) <+>
  pretty "\n" <> toHaskellHnatOperations namespaces <>
  pretty "instance Ord HNat where \n\n" <>
  generateOrdHnat namespaces namespaces <>
  pretty "\n\n" <>
  generateMinusHnat namespaces namespaces <>
  pretty "\n\n" <>
  pretty "data Env = Nil" <+>
  toHaskellEnv namespaces <+>
  pretty "\n" <> generateListSNamespaces namespaces <+>
  pretty "\n\n" <> toHaskellmapStart table accsorts namespaces varTable <+>
  pretty "\n\n" <>
  sortDefineCheckShiftMultiple accsorts "plus" varTable namespaces <+>
  pretty "\n\n" <> sortDefineShiftMultiple accsorts namespaces "plus" varTable <+>
  pretty "\n\n" <>
  sortDefineCheckShiftMultiple accsorts "minus" varTable namespaces <+>
  pretty "\n\n" <> sortDefineShiftMultiple accsorts namespaces "minus" varTable <+>
  pretty "\n\n" <> sortDefineCheckSubstMultiple accsorts varTable <+>
  pretty "\n\n" <> sortDefineSubstMultiple accsorts namespaces varTable <+>
  pretty "\n\n" <> generateSortSynSystem namespaces table accsorts <+>
  pretty "\n\n" <>
  generateFreeVariableFunctionStart namespaces table accsorts varTable <>
  genCode code
  where
    varTable = getTableOfHasAccessVariable accsorts

    genCode :: [String] -> Doc String
    genCode []          = pretty ""
    genCode (line:rest) = pretty line <> pretty "\n" <> genCode rest

toHaskellLanguage (s:srest, sorts, imp, code) namespaces table accsorts name imports =
  toHaskellLanguage
    (srest, sorts, imp, code)
    (s : namespaces)
    table
    accsorts
    name
    imports
toHaskellLanguage ([], s:srest, imp, code) namespaces table accsorts name imports =
  toHaskellLanguage
    ([], srest, imp, code)
    namespaces
    (getTableOfInstancesToNamespacesSortWithSortName s : table)
    (s : accsorts)
    name
    imports
toHaskellLanguage ([], [], (imp:imprest), code) namespaces table accsorts name imports =
  toHaskellLanguage
    ([], [], imprest, code)
    namespaces
    table
    accsorts
    name
    (imp : imprest)

-- * Module declaration
-- ----------------------------------------------------------------------------

generateModule ::
     [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> [SortDef]
  -> String
  -> Doc String
generateModule namespaces table accsorts name =
  pretty "module" <+>
  pretty (capitalize name) <+>
  pretty "(  Env(..), HNat(..) " <+>
  generateFunctionsModule namespaces table varTable accsorts <+>
  generateHnatFunctions namespaces <+> pretty ") \n where "
  where
    varTable = getTableOfHasAccessVariable accsorts

generateFunctionsModule ::
     [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> [(SortName, Bool)]
  -> [SortDef]
  -> Doc String
generateFunctionsModule namespaces table canAccessVarTable [] = pretty ""
generateFunctionsModule namespaces table canAccessVarTable (sort:srest)
  | fromJust (lookup sname canAccessVarTable) =
    generateSortNames sname <+>
    generateInstanceFunctions namespaces table sname <+>
    genFunctionModule sname <+>
    generateFunctionsModule namespaces table canAccessVarTable srest
  | otherwise =
    generateSortNames sname <+>
    generateInstanceSynFunctions namespaces synInstances sname <+>
    generateFunctionsModule namespaces table canAccessVarTable srest
  where
    sname = getname sort
    synInstances = filter isSyn (fromJust (lookup sname table))

generateSortNames :: String -> Doc String
generateSortNames sname =
  pretty "," <+> pretty (capitalize sname) <+> pretty "(..)"

generateInstanceFunctions ::
     [NameSpaceDef] -> [(SortName, [NamespaceInstance])] -> String -> Doc String
generateInstanceFunctions namespaces table sname =
  generateInstanceInhFunctions namespaces inhInstances sname <+>
  generateInstanceSynFunctions namespaces synInstances sname
  where
    inhInstances = filter isInh (fromJust (lookup sname table))
    synInstances = filter isSyn (fromJust (lookup sname table))

generateInstanceInhFunctions ::
     [NameSpaceDef] -> [NamespaceInstance] -> String -> Doc String
generateInstanceInhFunctions namespaces [] sname = pretty ""
generateInstanceInhFunctions namespaces ((INH ctxname namespacename):rest) sname =
  pretty "," <+>
  pretty (toLowerCaseFirst sname) <> pretty (toLowerCaseFirst secondSort) <>
  pretty "Substitute" <+>
  generateInstanceInhFunctions namespaces rest sname
  where
    secondSort = lookForSortName namespacename namespaces

generateInstanceSynFunctions ::
     [NameSpaceDef] -> [NamespaceInstance] -> String -> Doc String
generateInstanceSynFunctions namespaces [] sname = pretty ""
generateInstanceSynFunctions namespaces ((SYN ctxname namespacename):rest) sname =
  pretty ", addToEnvironment" <> pretty sname <> pretty ctxname <>
  generateInstanceSynFunctions namespaces rest sname

genFunctionModule :: String -> Doc String
genFunctionModule sname =
  pretty ", freeVariables" <> pretty sname <+>
  pretty ", " <+>
  pretty (toLowerCaseFirst sname) <> pretty "shiftplus" <+>
  pretty "," <+> pretty (toLowerCaseFirst sname) <> pretty "shiftminus"

generateHnatFunctions :: [NameSpaceDef] -> Doc String
generateHnatFunctions [] = pretty ""
generateHnatFunctions (def:rest) =
  pretty ", generateHnat" <> pretty (getname def) <+>
  pretty "\n" <> generateHnatFunctions rest

lookForSortName :: NameSpaceName -> [NameSpaceDef] -> SortName
lookForSortName name ((MkNameSpace name2 sortname _):rest)
  | name2 == name = toLowerCaseFirst sortname
  | otherwise = lookForSortName name rest

-- * Imports
-- ----------------------------------------------------------------------------

genImportsAll :: [[String]] -> Doc String
genImportsAll [] = pretty ""
genImportsAll (str:rest) = genImports str <+> pretty "\n" <> genImportsAll rest

genImports :: [String] -> Doc String
genImports (str:[]) = pretty "import" <+> pretty str
genImports (str:rest) =
  pretty "import" <+> pretty str <+> pretty "(" <+> genImportsRest rest

genImportsRest :: [String] -> Doc String
genImportsRest []         = pretty ")"
genImportsRest (str:rest) = pretty str <+> pretty "," <+> genImportsRest rest

-- * Sorts
-- ----------------------------------------------------------------------------

toHaskellSort :: [SortDef] -> Doc String
toHaskellSort [] = pretty ""
toHaskellSort ((MkDefSort sname _ (c:crest) _):rest) =
  pretty "data" <+>
  pretty (capitalize sname) <+>
  pretty "=" <+>
  toHaskellConstructor c <+>
  prettyListToSpaces (map (toHaskellConstructor) crest) <+>
  pretty " deriving(Show,Eq) \n" <> toHaskellSort rest

toHaskellConstructor :: ConstructorDef -> Doc String
toHaskellConstructor (MkDefConstructor consName lists listSorts folds _ hTypes) =
  pretty (capitalize consName) <+>
  foldableToSpaces folds <+>
  listToSpacesList lists <+>
  (listToSpaces listSorts) <+> haskellTypesToPretty (map capitalize hTypes)
toHaskellConstructor (MkBindConstructor consName lists listSorts folds _ _ hTypes) =
  pretty (capitalize consName) <+>
  foldableToSpaces folds <+>
  listToSpacesList lists <+>
  (listToSpaces listSorts) <+> haskellTypesToPretty (map capitalize hTypes)
toHaskellConstructor (MkVarConstructor consName _) =
  pretty (capitalize consName) <+> pretty "HNat"

prettyListToSpaces :: [Doc String] -> Doc String
prettyListToSpaces (l:lrest) = pretty "|" <+> l <+> prettyListToSpaces lrest
prettyListToSpaces []        = pretty ""

foldableToSpaces :: [(String, String, String)] -> Doc String
foldableToSpaces folds = seperate folds
  where
    seperate [] = pretty ""
    seperate ((id, sort, foldname):xrest) =
      pretty "(" <+>
      pretty (capitalize foldname) <+>
      pretty (capitalize sort) <+> pretty ")" <+> (seperate xrest)

listToSpacesList :: [(String, String)] -> Doc String
listToSpacesList list = seperate (map snd list)
  where
    seperate [] = pretty ""
    seperate ((x:srest):xrest) =
      pretty "[" <+>
      pretty (((toUpper) x : srest)) <+> pretty "]" <+> (seperate xrest)

listToSpaces :: [(String, String)] -> Doc String
listToSpaces list = seperate (map snd list)
  where
    seperate [] = pretty ""
    seperate ((x:srest):xrest) =
      pretty (((toUpper) x : srest)) <+> (seperate xrest)

haskellTypesToPretty :: [String] -> Doc String
haskellTypesToPretty []        = pretty ""
haskellTypesToPretty (x:xrest) = pretty x <+> haskellTypesToPretty xrest

-- * HNat type
-- ----------------------------------------------------------------------------

toHaskellHnat :: [NameSpaceDef] -> Doc String
toHaskellHnat [] = pretty " deriving(Show,Eq)"
toHaskellHnat ((MkNameSpace sortname _ _):nsrest) =
  pretty "| S" <> pretty (capitalize sortname) <+>
  pretty "HNat" <+> toHaskellHnat nsrest

-- * HNat plus function
-- ----------------------------------------------------------------------------

toHaskellHnatOperations :: [NameSpaceDef] -> Doc String
toHaskellHnatOperations [] = pretty "plus Z h = h \nplus h Z = h \n"
toHaskellHnatOperations ((MkNameSpace sname _ _):nsrest) =
  pretty "plus x1 (S" <> pretty (capitalize sname) <+>
  pretty "x2)" <+>
  pretty "=" <+>
  pretty "S" <> pretty (capitalize sname) <+>
  pretty "(plus x1 x2)" <+> pretty "\n" <> toHaskellHnatOperations nsrest

-- * HNat Ord type class
-- ----------------------------------------------------------------------------

generateOrdHnat :: [NameSpaceDef] -> [NameSpaceDef] -> Doc String
generateOrdHnat [] _ =
  pretty "  compare Z Z = EQ\n  compare Z _ = LT\n  compare _ Z  = GT"
generateOrdHnat (namespace:namespacerest) namespaces =
  listToEndings (map (generateNamespaceOrd namespace) namespaces) <+>
  pretty " \n" <> generateOrdHnat namespacerest namespaces

listToEndings :: [Doc String] -> Doc String
listToEndings list = seperate list
  where
    seperate []           = pretty ""
    seperate (name:xrest) = name <> pretty "\n" <> (seperate xrest)

generateNamespaceOrd :: NameSpaceDef -> NameSpaceDef -> Doc String
generateNamespaceOrd namespace1 namespace2
  | namespace1 == namespace2 =
    pretty "  compare" <+>
    pretty "(" <+>
    pretty (generateHnatName namespace1) <+>
    pretty "h1)" <+>
    pretty "(" <+>
    pretty (generateHnatName namespace2) <+>
    pretty "h2)" <+> pretty "= compare  h1 h2 "
  | otherwise =
    pretty "  compare" <+>
    pretty "(" <+>
    pretty (generateHnatName namespace1) <+>
    pretty "h1)" <+>
    pretty "(" <+>
    pretty (generateHnatName namespace2) <+>
    pretty "h2)" <+>
    pretty "=  error \"differing namespace found in compare \" "

generateHnatName :: NameSpaceDef -> String
generateHnatName (MkNameSpace sname _ _) = "S" ++ (capitalize sname)

-- * HNat minus function
-- ----------------------------------------------------------------------------

generateMinusHnat :: [NameSpaceDef] -> [NameSpaceDef] -> Doc String
generateMinusHnat [] _ =
  pretty
    "minus Z Z = Z\nminus Z _ = error \" You cannot substract zero with a positive number \" \nminus result Z = result"
generateMinusHnat (namespace:namespacerest) namespaces =
  listToEndings (map (generateMinus namespace) namespaces) <+>
  pretty "\n" <> generateMinusHnat namespacerest namespaces

generateMinus :: NameSpaceDef -> NameSpaceDef -> Doc String
generateMinus namespace1 namespace2
  | namespace1 == namespace2 =
    pretty "minus" <+>
    pretty "(" <+>
    pretty (generateHnatName namespace1) <+>
    pretty "h1)" <+>
    pretty "(" <+>
    pretty (generateHnatName namespace2) <+>
    pretty "h2)" <+> pretty "= minus h1 h2 "
  | otherwise =
    pretty "minus" <+>
    pretty "(" <+>
    pretty (generateHnatName namespace1) <+>
    pretty "h1)" <+>
    pretty "(" <+>
    pretty (generateHnatName namespace2) <+>
    pretty "h2)" <+> pretty "=  error \"differing namespace found in minus \" "

-- * Env data type
-- ----------------------------------------------------------------------------

toHaskellEnv :: [NameSpaceDef] -> Doc String
toHaskellEnv [] = pretty " deriving(Show,Eq)"
toHaskellEnv ((MkNameSpace sname _ inEnv):nsrest) =
  pretty "| E" <> pretty (capitalize sname) <+>
  addToEnvPrint inEnv <+> pretty "Env" <+> toHaskellEnv nsrest

addToEnvPrint :: [String] -> Doc String
addToEnvPrint []          = pretty ""
addToEnvPrint (name:rest) = pretty (capitalize name) <+> addToEnvPrint rest

-- * HNat generator functions
-- ----------------------------------------------------------------------------

generateListSNamespaces :: [NameSpaceDef] -> Doc String
generateListSNamespaces [] = pretty ""
generateListSNamespaces (namespace:rest) =
  gen0name (getname namespace) <+>
  pretty "\n" <> generatenNamespace (getname namespace) <+>
  pretty "\n" <> generateListSNamespaces rest

gen0name :: String -> Doc String
gen0name name =
  pretty "generateHnat" <> pretty name <+> pretty " 0 c =" <+> pretty "c"

generatenNamespace :: String -> Doc String
generatenNamespace name =
  pretty "generateHnat" <> pretty name <+>
  pretty " n c=" <+>
  pretty "S" <> pretty name <+>
  pretty "(generateHnat" <> pretty name <+> pretty "(n-1) c)"

-- * Mapping functions
-- ----------------------------------------------------------------------------

toHaskellmapStart ::
     [(SortName, [NamespaceInstance])]
  -> [SortDef]
  -> [NameSpaceDef]
  -> [(SortName, Bool)]
  -> Doc String
toHaskellmapStart _ [] _ _ = pretty ""
toHaskellmapStart table ((MkDefSort sname instances cdefs _):rest) namespaces accessVarTable
  | fromJust (lookup (capitalize sname) accessVarTable) =
    generateTypingmap sname instances namespaces <>
    (toHaskellmap
       (toLowerCaseFirst sname)
       instances
       cdefs
       table
       namespaces
       accessVarTable) <+>
    pretty "\n" <> toHaskellmapStart table rest namespaces accessVarTable
  | otherwise = toHaskellmapStart table rest namespaces accessVarTable

generateTypingmap ::
     SortName -> [NamespaceInstance] -> [NameSpaceDef] -> Doc String
generateTypingmap sname instances namespaces =
  pretty (toLowerCaseFirst sname) <> pretty "map" <+>
  pretty "::" <+>
  generateTypingInstancemap (filter isInh instances) namespaces <+>
  pretty "HNat ->" <+> sorttype <+> pretty "->" <+> sorttype <+> pretty "\n"
  where
    sorttype = pretty (capitalize sname)

toHaskellmap ::
     SortName
  -> [NamespaceInstance]
  -> [ConstructorDef]
  -> [(SortName, [NamespaceInstance])]
  -> [NameSpaceDef]
  -> [(SortName, Bool)]
  -> Doc String
toHaskellmap sname inst [] _ _ _ = pretty ""
toHaskellmap sname inst (c:cdefs) table namespaces accessVarTable =
  sortNamemapname sname <+>
  namespaceInstanceFunctions [namespace | INH _ namespace <- inst] <+>
  pretty " c" <+>
  pretty "(" <+>
  toHaskellmapConstructor sname inst c table <+>
  pretty ")" <+>
  pretty " =" <+>
  toHaskellmapConstructorMappingFunction
    sname
    inst
    c
    table
    namespaces
    accessVarTable <+>
  pretty "\n" <> toHaskellmap sname inst cdefs table namespaces accessVarTable

generateTypingInstancemap :: [NamespaceInstance] -> [NameSpaceDef] -> Doc String
generateTypingInstancemap [] _ = pretty ""
generateTypingInstancemap (INH _ namespaceName:rest) namespaces =
  pretty "(HNat->" <> sortType <+>
  pretty "->" <+>
  sortType <> pretty ")->" <+> generateTypingInstancemap rest namespaces
  where
    sortType = pretty (capitalize (lookForSortName namespaceName namespaces))

sortNamemapname :: SortName -> Doc String
sortNamemapname sname = pretty (toLowerCaseFirst sname) <> pretty "map"

namespaceInstanceFunctions :: [NameSpaceName] -> Doc String
namespaceInstanceFunctions [] = pretty ""
namespaceInstanceFunctions (name:rest) =
  instancePretty name <+> namespaceInstanceFunctions rest

instancePretty :: NameSpaceName -> Doc String
instancePretty namespace = pretty "on" <> pretty namespace

--before = part
toHaskellmapConstructor ::
     SortName
  -> [NamespaceInstance]
  -> ConstructorDef
  -> [(SortName, [NamespaceInstance])]
  -> Doc String
toHaskellmapConstructor sname inst (MkDefConstructor consName lists listSorts folds _ hTypes) table =
  pretty (capitalize consName) <+>
  listToSpaceslower (foldToNormalList folds) <+>
  listToSpaceslower lists <+>
  listToSpaceslower listSorts <+> haskellTypesToPrettyLower hTypes 0
toHaskellmapConstructor sname inst (MkBindConstructor consName lists listSorts folds (id, namespace) _ hTypes) table =
  pretty (capitalize consName) <+>
  listToSpaceslower (foldToNormalList folds) <+>
  listToSpaceslower lists <+>
  listToSpaceslower listSorts <+> haskellTypesToPrettyLower hTypes 0
toHaskellmapConstructor sname inst (MkVarConstructor consName _) table =
  pretty (capitalize consName) <+> pretty "hnat"

--after = part
toHaskellmapConstructorMappingFunction ::
     SortName
  -> [NamespaceInstance]
  -> ConstructorDef
  -> [(SortName, [NamespaceInstance])]
  -> [NameSpaceDef]
  -> [(SortName, Bool)]
  -> Doc String
toHaskellmapConstructorMappingFunction sname inst (MkDefConstructor consName lists listSorts folds rules hTypes) table namespaces accessVarTable =
  pretty (capitalize consName) <+>
  applyRulesIdentifiers
    sname
    inst
    rules
    (collectRulesAllField
       rules
       (foldToNormalList folds ++ lists ++ listSorts)
       [])
    (foldToNormalList folds)
    lists
    listSorts
    table
    accessVarTable <+>
  haskellTypesToPrettyLower hTypes 0
toHaskellmapConstructorMappingFunction sname inst (MkBindConstructor consName lists listSorts folds (id, namespace) rules hTypes) table namespaces accessVarTable =
  pretty (capitalize consName) <+>
  applyRulesIdentifiers
    sname
    inst
    rules
    (collectRulesAllField
       rules
       (foldToNormalList folds ++ lists ++ listSorts)
       [])
    (foldToNormalList folds)
    lists
    listSorts
    table
    accessVarTable <+>
  haskellTypesToPrettyLower hTypes 0
toHaskellmapConstructorMappingFunction sname inst (MkVarConstructor consName contextName) table namespaces accessVarTable =
  pretty "on" <>
  pretty
    (getnameInstancenamespace
       (head (fromJust (lookup (capitalize sname) table)))) <+>
  pretty "c" <+>
  pretty "(" <+> pretty (capitalize consName) <+> pretty " hnat )"

haskellTypesToPrettyLower :: [String] -> Int -> Doc String
haskellTypesToPrettyLower [] _ = pretty ""
haskellTypesToPrettyLower (x:xrest) n =
  pretty (toLowerCaseFirst x) <> pretty n <+>
  haskellTypesToPrettyLower xrest (n + 1)

listToSpaceslower :: [(String, String)] -> Doc String
listToSpaceslower list = seperate (map fst list)
  where
    seperate [] = pretty ""
    seperate (name:xrest) = pretty (toLowerCaseFirst name) <+> (seperate xrest)

foldToNormalList :: [(String, String, String)] -> [(String, String)]
foldToNormalList foldsWithFoldName =
  map (\(a, b, c) -> (a, b)) foldsWithFoldName

getnameInstancenamespace :: NamespaceInstance -> NameSpaceName
getnameInstancenamespace (INH _ name) = name
getnameInstancenamespace (SYN _ name) = name

--calculate the inherited namespace of an identifier and for every inherited namespace, check what happens
applyRulesIdentifiers ::
     SortName
  -> [NamespaceInstance]
  -> [NameSpaceRule]
  -> [(IdName, [NameSpaceRule])]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> [(SortName, Bool)]
  -> Doc String
applyRulesIdentifiers sname inst rules [] folds lists listSorts table _ =
  pretty ""
applyRulesIdentifiers sname inst rules ((id, idRules):rest) folds lists listSorts table accessVarTable
  | fromJust (lookup (capitalize sortnameInUse) accessVarTable) &&
      elem id (map fst folds) =
    pretty "(fmap (" <> sortNamemapname sortnameInUse <+>
    namespaceInstanceFunctions
      [namespace | INH _ namespace <- (fromJust (lookup sortnameInUse table))] <+>
    addedBinders <+>
    pretty ")" <+>
    pretty (toLowerCaseFirst id) <+>
    pretty "  )" <+>
    applyRulesIdentifiers
      sname
      inst
      rules
      rest
      folds
      lists
      listSorts
      table
      accessVarTable
  | fromJust (lookup (capitalize sortnameInUse) accessVarTable) &&
      elem id (map fst lists) =
    pretty "(map (" <> sortNamemapname sortnameInUse <+>
    namespaceInstanceFunctions
      [namespace | INH _ namespace <- (fromJust (lookup sortnameInUse table))] <+>
    addedBinders <+>
    pretty ")" <+>
    pretty (toLowerCaseFirst id) <+>
    pretty "  )" <+>
    applyRulesIdentifiers
      sname
      inst
      rules
      rest
      folds
      lists
      listSorts
      table
      accessVarTable
  | fromJust (lookup (capitalize sortnameInUse) accessVarTable) &&
      elem id (map fst listSorts) =
    pretty "(" <> sortNamemapname sortnameInUse <+>
    namespaceInstanceFunctions
      [namespace | INH _ namespace <- (fromJust (lookup sortnameInUse table))] <+>
    addedBinders <+>
    pretty (toLowerCaseFirst id) <+>
    pretty "  )" <+>
    applyRulesIdentifiers
      sname
      inst
      rules
      rest
      folds
      lists
      listSorts
      table
      accessVarTable
  | otherwise =
    pretty (toLowerCaseFirst id) <+>
    applyRulesIdentifiers
      sname
      inst
      rules
      rest
      folds
      lists
      listSorts
      table
      accessVarTable
  where
    addedBinders =
      applyRuleInheritedNamespaces
        sname
        inst
        rules
        (id, idRules)
        folds
        lists
        listSorts
        table
        (calculateInheritedNameSpace sortnameInUse table)
    sortnameInUse = (lookupIdToSort id (folds ++ lists ++ listSorts))

applyRuleInheritedNamespaces ::
     SortName
  -> [NamespaceInstance]
  -> [NameSpaceRule]
  -> (IdName, [NameSpaceRule])
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> [NamespaceInstance]
  -> Doc String
applyRuleInheritedNamespaces sname inst rules (id, rulesOfId) folds lists listSorts table [] =
  pretty "c"
applyRuleInheritedNamespaces sname inst rules (id, rulesOfId) folds lists listSorts table (x:xrest)
  | isJust newString =
    pretty "(" <+>
    fromJust newString <+>
    applyRuleInheritedNamespaces
      sname
      inst
      rules
      (id, rulesOfId)
      folds
      lists
      listSorts
      table
      xrest <+>
    pretty ")"
  | otherwise =
    applyRuleInheritedNamespaces
      sname
      inst
      rules
      (id, rulesOfId)
      folds
      lists
      listSorts
      table
      xrest
  where
    newString =
      applyTheRuleOneInheritedNamespace
        sname
        rules
        (id, rulesOfId)
        folds
        lists
        listSorts
        table
        x

applyTheRuleOneInheritedNamespace ::
     SortName
  -> [NameSpaceRule]
  -> (IdName, [NameSpaceRule])
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> NamespaceInstance
  -> Maybe (Doc String)
applyTheRuleOneInheritedNamespace sname rules (id, rulesOfId) folds lists listSorts table currentinst
  | isJust foundrule =
    applyOneRuleLogic
      sname
      currentinst
      newrules
      (fromJust foundrule)
      folds
      lists
      listSorts
      newtable
  | otherwise = Nothing
  where
    foundrule =
      find
        (\x -> getInstanceNamesOfRuleLeft (fst x) == getname currentinst)
        rulesOfId
    newtable = filterTableBySameNamespace currentinst table
    newrules = getNewRules rules [] sname table (folds ++ lists ++ listSorts)

applyOneRuleLogic ::
     SortName
  -> NamespaceInstance
  -> [NameSpaceRule]
  -> NameSpaceRule
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> Maybe (Doc String)
applyOneRuleLogic sname inst rules (l, ExprLHS _) folds lists listSorts table =
  Nothing
applyOneRuleLogic sname inst rules (l, ExprAdd expr _) folds lists listSorts table =
  return
    (pretty " S" <> pretty (getnameInstancenamespace inst) <+>
     stepLogic sname inst rules (l, expr) folds lists listSorts table)
applyOneRuleLogic sname inst rules (l, ExprSub id context) folds lists listSorts table
  | (elem id (map fst lists) || elem id (map fst folds)) && (isJust newrule) =
    return
      (pretty "generateHnat" <> pretty (getnameInstancenamespace inst) <+>
       pretty "( length" <+>
       pretty id <+> pretty ")" <+> pretty "$" <+> nextStep)
  | (elem id (map fst lists) || elem id (map fst folds)) =
    return
      (pretty "generateHnat" <> pretty (getnameInstancenamespace inst) <+>
       pretty "( length" <+> pretty id <+> pretty ")" <+> pretty "")
  | (isJust newrule) =
    return
      (pretty "addToEnvironment" <> pretty (lookup id listSorts) <>
       pretty context <+>
       pretty id <+> pretty "$" <+> nextStep)
  | otherwise =
    return
      (pretty "addToEnvironment" <> pretty (lookup id listSorts) <>
       pretty context <+>
       pretty id <+> pretty "")
  where
    newrule = find (\(l, r) -> (getLeftIdSub l) == id) rules
    nextStep =
      stepLogic sname inst rules (fromJust newrule) folds lists listSorts table

stepLogic ::
     SortName
  -> NamespaceInstance
  -> [NameSpaceRule]
  -> NameSpaceRule
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> Doc String
stepLogic sname inst rules (l, ExprLHS _) folds lists listSorts table =
  pretty ""
stepLogic sname inst rules (l, ExprAdd expr _) folds lists listSorts table =
  (pretty " S" <> pretty (getnameInstancenamespace inst) <+>
   stepLogic sname inst rules (l, expr) folds lists listSorts table) <+>
  pretty ""
stepLogic sname inst rules (l, ExprSub id context) folds lists listSorts table
  | (elem id (map fst lists) || elem id (map fst folds)) && (isJust newrule) =
    (pretty "generateHnat" <> pretty (getnameInstancenamespace inst) <+>
     pretty "( length" <+> pretty id <+> pretty ")" <+> nextStep)
  | (elem id (map fst lists) || elem id (map fst folds)) =
    (pretty "(generateHnat" <> pretty (getnameInstancenamespace inst) <+>
     pretty "( length" <+> pretty id <+> pretty ")" <+> pretty ")")
  | (isJust newrule) =
    (pretty "addToEnvironment" <> pretty (lookup id listSorts) <> pretty context <+>
     pretty id <+> pretty "$" <+> nextStep)
  | otherwise =
    (pretty " addToEnvironment" <> pretty (lookup id listSorts) <>
     pretty context <+>
     pretty id <+> pretty "")
  where
    newrule = find (\(l, r) -> (getLeftIdSub l) == id) rules
    nextStep =
      stepLogic sname inst rules (fromJust newrule) folds lists listSorts table

getNewRules ::
     [NameSpaceRule]
  -> [NameSpaceRule]
  -> SortName
  -> [(SortName, [NamespaceInstance])]
  -> [(IdName, SortName)]
  -> [NameSpaceRule]
getNewRules [] acc _ _ _ = acc
getNewRules ((l, r):rest) acc sname table listSorts
  | sortnameId == "" &&
      any (\x -> getInstanceNamesOfRuleLeft l == getname x) snameLookup =
    getNewRules rest ((l, r) : acc) sname table listSorts
  | any (\x -> getInstanceNamesOfRuleLeft l == getname x) sortnameIdlookup =
    getNewRules rest ((l, r) : acc) sname table listSorts
  | otherwise = getNewRules rest acc sname table listSorts
  where
    sortnameId = getLeftIdSub l
    snameLookup = fromJust (lookup (capitalize sname) table)
    sortnameIdlookup =
      fromJust (lookup (lookupIdToSort sortnameId listSorts) table)

calculateInheritedNameSpace ::
     SortName -> [(SortName, [NamespaceInstance])] -> [NamespaceInstance]
calculateInheritedNameSpace sname table = filter isInh instances
  where
    instances = fromJust (lookup sname table)

lookupIdToSort :: IdName -> [(IdName, SortName)] -> SortName
lookupIdToSort id table = fromJust (lookup id table)


-- * Shift functions
-- ----------------------------------------------------------------------------

-- checker for shift operation generation
sortDefineCheckShiftMultiple ::
     [SortDef] -> String -> [(SortName, Bool)] -> [NameSpaceDef] -> Doc String
sortDefineCheckShiftMultiple [] opName varAccessTable _ = pretty ""
sortDefineCheckShiftMultiple (s:srest) opName varAccessTable namespaces =
  sortDefineCheckShift s opName varAccessTable namespaces <+>
  pretty "\n" <>
  sortDefineCheckShiftMultiple srest opName varAccessTable namespaces

sortDefineCheckShift ::
     SortDef -> String -> [(SortName, Bool)] -> [NameSpaceDef] -> Doc String
sortDefineCheckShift (MkDefSort sname inst cdefs _) opName varAccessTable namespaces
  | fromJust (lookup sname varAccessTable) =
    constructorsToCheckShift cdefs sname opName namespaces inst
  | otherwise = pretty ""

constructorsToCheckShift ::
     [ConstructorDef]
  -> SortName
  -> String
  -> [NameSpaceDef]
  -> [NamespaceInstance]
  -> Doc String
constructorsToCheckShift [] sname opName _ _ = pretty ""
constructorsToCheckShift (c:cdefsrest) sname opName namespaces inst =
  constructorDefineCheckShift c sname opName namespaces inst <>
  constructorsToCheckShift cdefsrest sname opName namespaces inst

constructorDefineCheckShift ::
     ConstructorDef
  -> SortName
  -> String
  -> [NameSpaceDef]
  -> [NamespaceInstance]
  -> Doc String
constructorDefineCheckShift (MkVarConstructor consName instname) sname opName namespaces inst =
  pretty (toLowerCaseFirst sname) <> pretty "shiftHelp" <> pretty opName <+>
  pretty "d c (" <+>
  pretty (capitalize consName) <+>
  pretty "hnat) \n  |hnat >= c =" <+>
  pretty (capitalize consName) <+>
  pretty "(" <+>
  pretty opName <+>
  pretty " hnat  d) \n  | otherwise =" <+>
  pretty (capitalize consName) <+> pretty "hnat \n"
  where
    instanceNamespace = lookforInstance inst (instname)
    newname = lookForSortName (instanceNamespace) namespaces
constructorDefineCheckShift _ _ _ _ _ = pretty ""

lookforInstance :: [NamespaceInstance] -> String -> String
lookforInstance ((INH ctxname namespacename):rest) instname
  | ctxname == instname = namespacename
  | otherwise = lookforInstance rest instname
lookforInstance ((SYN ctxname namespacename):rest) instname =
  lookforInstance rest instname

-- * Multiple shift functions??
-- ----------------------------------------------------------------------------

-- generation of all shift functions
sortDefineShiftMultiple ::
     [SortDef] -> [NameSpaceDef] -> String -> [(SortName, Bool)] -> Doc String
sortDefineShiftMultiple [] _ opName varAccessTable = pretty ""
sortDefineShiftMultiple (s:srest) defs opName varAccessTable
  | fromJust (lookup (getname s) varAccessTable) =
    generateTypingshift s defs opName <> sortDefineShift s defs opName <+>
    pretty "\n" <> sortDefineShiftMultiple srest defs opName varAccessTable
  | otherwise = sortDefineShiftMultiple srest defs opName varAccessTable

generateTypingshift :: SortDef -> [NameSpaceDef] -> String -> Doc String
generateTypingshift (MkDefSort sname _ _ _) namespaces str =
  pretty (toLowerCaseFirst sname) <> pretty "shift" <> pretty str <+>
  pretty "::" <+>
  pretty "HNat ->" <+> sorttype <+> pretty "->" <+> sorttype <+> pretty "\n"
  where
    sorttype = pretty (capitalize sname)

sortDefineShift :: SortDef -> [NameSpaceDef] -> String -> Doc String
sortDefineShift (MkDefSort sname namespaceDecl _ _) defs opName =
  pretty (toLowerCaseFirst sname) <> pretty "shift" <> pretty opName <+>
  pretty "d t =" <+>
  pretty (toLowerCaseFirst sname) <> pretty "map" <+>
  declarationsToFunctions namespaceDecl defs opName <+> pretty "Z  t "

declarationsToFunctions ::
     [NamespaceInstance] -> [NameSpaceDef] -> String -> Doc String
declarationsToFunctions [] _ _ = pretty ""
declarationsToFunctions ((INH _ namespaceName):rest) defs opName =
  pretty "(" <+>
  pretty (lookForSortName namespaceName defs) <> pretty "shiftHelp" <>
  pretty opName <+>
  pretty "d )" <+> declarationsToFunctions rest defs opName
declarationsToFunctions (_:rest) defs opName =
  declarationsToFunctions rest defs opName

-- * //
-- ----------------------------------------------------------------------------

-- checker for substition generation
sortDefineCheckSubstMultiple :: [SortDef] -> [(SortName, Bool)] -> Doc String
sortDefineCheckSubstMultiple [] _ = pretty ""
sortDefineCheckSubstMultiple (s:srest) varAccessTable =
  sortDefineCheckSubst s varAccessTable <+>
  pretty "\n" <> sortDefineCheckSubstMultiple srest varAccessTable

sortDefineCheckSubst :: SortDef -> [(SortName, Bool)] -> Doc String
sortDefineCheckSubst (MkDefSort sname _ cdefs _) varAccessTable
  | fromJust (lookup (capitalize sname) varAccessTable) =
    constructorsToCheckSubst cdefs sname
  | otherwise = pretty ""

constructorsToCheckSubst :: [ConstructorDef] -> SortName -> Doc String
constructorsToCheckSubst [] sname = pretty "" --pretty (toLowerCaseFirst sname)  <> pretty "SubstituteHelp _ _ _ t = t"
constructorsToCheckSubst (c:cdefsrest) sname =
  constructorDefineCheckSubst c sname <>
  constructorsToCheckSubst cdefsrest sname

constructorDefineCheckSubst :: ConstructorDef -> SortName -> Doc String
constructorDefineCheckSubst (MkVarConstructor consName _) sname =
  pretty (toLowerCaseFirst sname) <> pretty "SubstituteHelp sub  c (" <+>
  pretty (capitalize consName) <+>
  pretty "hnat) \n  |hnat ==   c =" <+>
  pretty (toLowerCaseFirst sname) <> pretty "shiftplus c  sub \n  | otherwise =" <+>
  pretty (capitalize consName) <+> pretty "hnat \n"
constructorDefineCheckSubst _ _ = pretty ""

-- * //
-- ----------------------------------------------------------------------------

-- generation of all substition functions
sortDefineSubstMultiple ::
     [SortDef] -> [NameSpaceDef] -> [(SortName, Bool)] -> Doc String
sortDefineSubstMultiple [] _ _ = pretty ""
sortDefineSubstMultiple (s:srest) defs varAccessTable =
  sortDefineSubst s defs varAccessTable <+>
  pretty "\n" <> sortDefineSubstMultiple srest defs varAccessTable

sortDefineSubst :: SortDef -> [NameSpaceDef] -> [(SortName, Bool)] -> Doc String
sortDefineSubst (MkDefSort sname namespaceDecl _ bool) defs varAccessTable
  | fromJust (lookup (capitalize sname) varAccessTable) =
    namespaceInstanceSubst sname namespaceDecl namespaceDecl defs bool
  | otherwise = pretty ""

namespaceInstanceSubst ::
     SortName
  -> [NamespaceInstance]
  -> [NamespaceInstance]
  -> [NameSpaceDef]
  -> Bool
  -> Doc String
namespaceInstanceSubst _ [] _ _ _ = pretty ""
namespaceInstanceSubst sname (inst:rest) instances namespaces bool =
  namespaceInstanceSubstFunction sname inst instances namespaces bool <>
  namespaceInstanceSubst sname rest instances namespaces bool

namespaceInstanceSubstFunction ::
     SortName
  -> NamespaceInstance
  -> [NamespaceInstance]
  -> [NameSpaceDef]
  -> Bool
  -> Doc String
namespaceInstanceSubstFunction _ _ [] _ _ = pretty ""
namespaceInstanceSubstFunction sname (INH instname namespaceName) instances defs bool
  | bool =
    generateTypingsubst sname secondSort defs <>
    pretty (toLowerCaseFirst sname ++ secondSort) <>
    pretty "Substitute sub orig t =" <+>
    pretty "rewrite" <> pretty sname <+>
    pretty "$" <+>
    pretty (toLowerCaseFirst sname) <> pretty "map" <+>
    declarationsToFunctionsSubst (INH instname namespaceName) instances defs <+>
    pretty " orig t  \n"
  | otherwise =
    generateTypingsubst sname secondSort defs <>
    pretty (toLowerCaseFirst sname ++ secondSort) <>
    pretty "Substitute sub orig t =" <+>
    pretty (toLowerCaseFirst sname) <> pretty "map" <+>
    declarationsToFunctionsSubst (INH instname namespaceName) instances defs <+>
    pretty " orig t  \n"
  where
    secondSort = lookForSortName namespaceName defs
namespaceInstanceSubstFunction sname _ instances defs _ = pretty ""

generateTypingsubst :: SortName -> SortName -> [NameSpaceDef] -> Doc String
generateTypingsubst snamefirst snamesecond namespaces =
  pretty ((toLowerCaseFirst snamefirst) ++ snamesecond) <> pretty "Substitute" <+>
  pretty "::" <+>
  pretty (capitalize snamesecond) <+>
  pretty "->HNat ->" <+> sorttype <+> pretty "->" <+> sorttype <+> pretty "\n"
  where
    sorttype = pretty (capitalize snamefirst)

declarationsToFunctionsSubst ::
     NamespaceInstance -> [NamespaceInstance] -> [NameSpaceDef] -> Doc String
declarationsToFunctionsSubst _ [] _ = pretty ""
declarationsToFunctionsSubst (INH instname1 namespaceName) ((INH instname2 _):rest) defs
  | instname1 == instname2 =
    pretty "(" <+>
    pretty (lookForSortName namespaceName defs) <> pretty "SubstituteHelp sub )" <+>
    declarationsToFunctionsSubst (INH instname1 namespaceName) rest defs
  | otherwise =
    pretty "(\\c x->x)" <+>
    declarationsToFunctionsSubst (INH instname1 namespaceName) rest defs
declarationsToFunctionsSubst (INH instname1 namespaceName) (_:rest) defs =
  declarationsToFunctionsSubst (INH instname1 namespaceName) rest defs
declarationsToFunctionsSubst _ _ _ = pretty ""

-- * //
-- ----------------------------------------------------------------------------

-- generation for all syn contexts
generateSortSynSystem ::
     [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> [SortDef]
  -> Doc String
generateSortSynSystem namespaces table [] = pretty ""
generateSortSynSystem namespaces table (s:srest) =
  generateSortSynSystemSort (getname s) namespaces table s <+>
  pretty "\n" <> generateSortSynSystem namespaces table srest

generateSortSynSystemSort ::
     SortName
  -> [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> SortDef
  -> Doc String
generateSortSynSystemSort sname namespaces table sort =
  generateSortSynSystemSortPerSyn
    sname
    namespaces
    table
    sort
    (filter isSyn (getInstanceSorts sort))

generateSortSynSystemSortPerSyn ::
     SortName
  -> [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> SortDef
  -> [NamespaceInstance]
  -> Doc String
generateSortSynSystemSortPerSyn sname namespaces table sort [] = pretty ""
generateSortSynSystemSortPerSyn sname namespaces table sort (x:xrest) =
  generateTypingsyn sname (getname x) <>
  generateSortSynSystemConstructors
    sname
    namespaces
    table
    (getConstructorDefsSort sort)
    x

generateTypingsyn :: SortName -> InstanceName -> Doc String
generateTypingsyn sname instname =
  pretty "addToEnvironment" <> pretty sname <> pretty instname <+>
  pretty "::" <+>
  pretty (capitalize sname) <+> pretty "->HNat -> HNat" <+> pretty "\n"

generateSortSynSystemConstructors ::
     SortName
  -> [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> [ConstructorDef]
  -> NamespaceInstance
  -> Doc String
generateSortSynSystemConstructors sname namespaces table [] inst = pretty ""
generateSortSynSystemConstructors sname namespaces table (c:crest) inst =
  generateSortSynSystemOneConstructor sname namespaces table c inst <>
  generateSortSynSystemConstructors sname namespaces table crest inst

generateSortSynSystemOneConstructor ::
     SortName
  -> [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> ConstructorDef
  -> NamespaceInstance
  -> Doc String
generateSortSynSystemOneConstructor sname namespaces table (MkVarConstructor consName _) inst =
  pretty "addToEnvironment" <> pretty sname <+>
  pretty "(" <+>
  pretty (capitalize consName) <+> pretty "hnat) c= c" <> pretty "\n"
generateSortSynSystemOneConstructor sname namespaces table (MkDefConstructor consName _ listSorts folds rules hTypes) inst =
  pretty "addToEnvironment" <> pretty sname <> pretty (getname inst) <+>
  pretty "(" <+>
  pretty (capitalize consName) <+>
  listToSpaceslower listSorts <+>
  haskellTypesToUnderscore hTypes <+>
  pretty ") c= " <+>
  getEnvFunctionGenerate sname inst namespaces newtable listSorts rules <>
  pretty "\n"
  where
    newtable = filterTableBySameNamespace inst table
generateSortSynSystemOneConstructor sname namespaces table (MkBindConstructor consName _ listSorts folds (id, namespace) rules hTypes) inst =
  pretty "addToEnvironment" <> pretty sname <> pretty (getname inst) <+>
  pretty "(" <+>
  pretty (capitalize consName) <+>
  listToSpaceslower listSorts <+>
  haskellTypesToUnderscore hTypes <+>
  pretty ")  c= " <+>
  getEnvFunctionGenerate sname inst namespaces newtable listSorts rules <>
  pretty "\n"
  where
    newtable = filterTableBySameNamespace inst table
                -- newrules = rules --getNewRules rules [] sname newtable listSorts

haskellTypesToUnderscore :: [String] -> Doc String
haskellTypesToUnderscore []     = pretty ""
haskellTypesToUnderscore (x:xs) = pretty "_" <+> haskellTypesToUnderscore xs

-- isExprAdd :: RightExpr -> Bool
-- isExprAdd (ExprAdd _ _) = True
-- isExprAdd _             = False

-- isEndPoint :: NameSpaceRule -> Bool
-- isEndPoint (l, ExprLHS _)      = True
-- isEndPoint (l, ExprAdd expr _) = isEndPoint (l, expr)
-- isEndPoint _                   = False

--after = part logic of the syn functions
getEnvFunctionGenerate ::
     SortName
  -> NamespaceInstance
  -> [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> [(IdName, SortName)]
  -> [NameSpaceRule]
  -> Doc String
getEnvFunctionGenerate sname inst namespaces table listSorts rules
  | fromJust (lookup "lhs" allrules) == [] = pretty "c"
  | otherwise = navigateRules sname inst namespaces table listSorts rules start
  where
    allrules = (collectRulesSyn rules listSorts [])
    start =
      fromJust
        (find
           (\x -> getInstanceNamesOfRuleLeft (fst x) == getname inst)
           (fromJust (lookup "lhs" allrules)))

navigateRules ::
     SortName
  -> NamespaceInstance
  -> [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> [(IdName, SortName)]
  -> [NameSpaceRule]
  -> NameSpaceRule
  -> Doc String
navigateRules sname inst namespaces table listSorts rules (l, ExprAdd expr _) =
  pretty "S" <> pretty (getnameInstancenamespace inst) <+>
  navigateRules sname inst namespaces table listSorts rules (l, expr)
navigateRules sname inst namespaces table listSorts rules (LHS _, ExprLHS _) =
  pretty "c"
navigateRules sname inst namespaces table listSorts rules (LHS _, ExprSub id _)
  | isJust newrule =
    functionName <+>
    pretty "(" <+>
    navigateRules sname inst namespaces table listSorts rules (fromJust newrule) <+>
    pretty ")"
  | otherwise = functionName <+> pretty "c"
  where
    newrule = find (\(l, r) -> (getLeftIdSub l) == id) rules
    functionName =
      pretty "addToEnvironment" <> pretty (lookup id listSorts) <>
      pretty (getname inst) <+>
      pretty id
navigateRules sname inst namespaces table listSorts rules (Sub _ _, ExprLHS _) =
  pretty "c"
navigateRules sname inst namespaces table listSorts rules (Sub _ _, ExprSub id _)
  | isJust newrule =
    pretty "(" <+>
    functionName <+>
    navigateRules sname inst namespaces table listSorts rules (fromJust newrule) <+>
    pretty ")"
  | otherwise = functionName <+> pretty id <+> pretty "c"
  where
    newrule = find (\(l, r) -> (getLeftIdSub l) == id) rules
    functionName =
      pretty "addToEnvironment" <> pretty (lookup id listSorts) <>
      pretty (getname inst) <+>
      pretty id

-- * //
-- ----------------------------------------------------------------------------

--generate free variable functions
generateFreeVariableFunctionStart ::
     [NameSpaceDef]
  -> [(SortName, [NamespaceInstance])]
  -> [SortDef]
  -> [(SortName, Bool)]
  -> Doc String
generateFreeVariableFunctionStart _ _ [] _ = pretty ""
generateFreeVariableFunctionStart namespaces table (MkDefSort sname instances cons _:srest) accessVarTable
  | fromJust (lookup sname accessVarTable) =
    generateTypingFreeVars sname <>
    generateFreeVariableFunction
      sname
      instances
      cons
      table
      namespaces
      accessVarTable <>
    generateFreeVariableFunctionStart namespaces table srest accessVarTable
  | otherwise =
    generateFreeVariableFunctionStart namespaces table srest accessVarTable

generateTypingFreeVars :: SortName -> Doc String
generateTypingFreeVars sname =
  pretty "freeVariables" <> pretty sname <+>
  pretty "::" <+>
  pretty "HNat -> " <+>
  pretty (capitalize sname) <+> pretty " ->[HNat]" <+> pretty "\n"

generateFreeVariableFunction ::
     SortName
  -> [NamespaceInstance]
  -> [ConstructorDef]
  -> [(SortName, [NamespaceInstance])]
  -> [NameSpaceDef]
  -> [(SortName, Bool)]
  -> Doc String
generateFreeVariableFunction sname inst [] _ _ _ = pretty ""
generateFreeVariableFunction sname inst (MkVarConstructor cname ctx:cdefs) table namespaces accessVarTable =
  pretty "freeVariables" <> pretty sname <+>
  pretty "c (" <+>
  generateFreeVariableConstructor sname inst (MkVarConstructor cname ctx) table <+>
  pretty ")" <+>
  pretty " " <+>
  generateFreeVariableFunctionConstructor
    sname
    inst
    (MkVarConstructor cname ctx)
    table
    namespaces
    accessVarTable <+>
  pretty "\n" <>
  generateFreeVariableFunction sname inst cdefs table namespaces accessVarTable
generateFreeVariableFunction sname inst (c:cdefs) table namespaces accessVarTable =
  pretty "freeVariables" <> pretty sname <+>
  pretty "c (" <+>
  generateFreeVariableConstructor sname inst c table <+>
  pretty ")" <+>
  pretty " =" <+>
  generateFreeVariableFunctionConstructor
    sname
    inst
    c
    table
    namespaces
    accessVarTable <+>
  pretty "\n" <>
  generateFreeVariableFunction sname inst cdefs table namespaces accessVarTable

--before = part
generateFreeVariableConstructor ::
     SortName
  -> [NamespaceInstance]
  -> ConstructorDef
  -> [(SortName, [NamespaceInstance])]
  -> Doc String
generateFreeVariableConstructor sname inst (MkDefConstructor consName lists listSorts folds _ hTypes) table =
  pretty (capitalize consName) <+>
  listToSpaceslower (foldToNormalList folds ++ lists ++ listSorts) <+>
  haskellTypesToUnderscore hTypes
generateFreeVariableConstructor sname inst (MkBindConstructor consName lists listSorts folds (id, namespace) _ hTypes) table =
  pretty (capitalize consName) <+>
  listToSpaceslower (foldToNormalList folds ++ lists ++ listSorts) <+>
  haskellTypesToUnderscore hTypes
generateFreeVariableConstructor sname inst (MkVarConstructor consName _) table =
  pretty (capitalize consName) <+> pretty "hnat"

--after = part
generateFreeVariableFunctionConstructor ::
     SortName
  -> [NamespaceInstance]
  -> ConstructorDef
  -> [(SortName, [NamespaceInstance])]
  -> [NameSpaceDef]
  -> [(SortName, Bool)]
  -> Doc String
generateFreeVariableFunctionConstructor sname inst (MkDefConstructor consName lists listSorts folds rules _) table namespaces accessVarTable =
  applyRulesFreeVariables
    sname
    inst
    rules
    (collectRulesAllField
       rules
       (foldToNormalList folds ++ lists ++ listSorts)
       [])
    (foldToNormalList folds)
    lists
    listSorts
    table
    accessVarTable
generateFreeVariableFunctionConstructor sname inst (MkBindConstructor consName lists listSorts folds (id, namespace) rules _) table namespaces accessVarTable =
  applyRulesFreeVariables
    sname
    inst
    rules
    (collectRulesAllField
       rules
       (foldToNormalList folds ++ lists ++ listSorts)
       [])
    (foldToNormalList folds)
    lists
    listSorts
    table
    accessVarTable
generateFreeVariableFunctionConstructor sname inst (MkVarConstructor consName _) table namespaces accessVarTable =
  pretty "\n | hnat >= c = " <+>
  pretty "[minus hnat c]\n" <+> pretty "|otherwise = []"

applyRulesFreeVariables ::
     SortName
  -> [NamespaceInstance]
  -> [NameSpaceRule]
  -> [(IdName, [NameSpaceRule])]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> [(SortName, Bool)]
  -> Doc String
applyRulesFreeVariables sname inst rules idRules folds lists listSorts table accessVarTable =
  pretty "nub (" <+>
  applyRulesIdentifiersFreeVariables
    sname
    inst
    rules
    idRules
    folds
    lists
    listSorts
    table
    accessVarTable <+>
  pretty ")"

applyRulesIdentifiersFreeVariables ::
     SortName
  -> [NamespaceInstance]
  -> [NameSpaceRule]
  -> [(IdName, [NameSpaceRule])]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(IdName, SortName)]
  -> [(SortName, [NamespaceInstance])]
  -> [(SortName, Bool)]
  -> Doc String
applyRulesIdentifiersFreeVariables sname inst rules [] folds lists listSorts table accessVarTable =
  pretty "[]"
applyRulesIdentifiersFreeVariables sname inst rules ((id, idRules):[]) folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) =
    pretty "(" <> pretty "freeVariables" <> pretty sortnameInUse <+>
    addedBinders <+> pretty (toLowerCaseFirst id) <+> pretty "  ) "
  | otherwise = pretty "[]"
  where
    addedBinders =
      applyRuleInheritedNamespaces
        sname
        inst
        rules
        (id, idRules)
        folds
        lists
        listSorts
        table
        (calculateInheritedNameSpace sortnameInUse table)
    sortnameInUse = (lookupIdToSort id (lists ++ listSorts))
applyRulesIdentifiersFreeVariables sname inst rules ((id, idRules):rest) folds lists listSorts table accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (elem id (map fst folds)) =
    pretty "(foldMap (" <> pretty "freeVariables" <> pretty sortnameInUse <+>
    addedBinders <+>
    pretty ")" <+>
    pretty (toLowerCaseFirst id) <+>
    pretty "  ) ++" <+>
    applyRulesIdentifiersFreeVariables
      sname
      inst
      rules
      rest
      folds
      lists
      listSorts
      table
      accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) && (elem id (map fst lists)) =
    pretty "(concatMap (" <> pretty "freeVariables" <> pretty sortnameInUse <+>
    addedBinders <+>
    pretty ")" <+>
    pretty (toLowerCaseFirst id) <+>
    pretty "  ) ++" <+>
    applyRulesIdentifiersFreeVariables
      sname
      inst
      rules
      rest
      folds
      lists
      listSorts
      table
      accessVarTable
  | fromJust (lookup sortnameInUse accessVarTable) =
    pretty "(" <> pretty "freeVariables" <> pretty sortnameInUse <+>
    addedBinders <+>
    pretty (toLowerCaseFirst id) <+>
    pretty "  ) ++" <+>
    applyRulesIdentifiersFreeVariables
      sname
      inst
      rules
      rest
      folds
      lists
      listSorts
      table
      accessVarTable
  | otherwise =
    applyRulesIdentifiersFreeVariables
      sname
      inst
      rules
      rest
      folds
      lists
      listSorts
      table
      accessVarTable
  where
    addedBinders =
      applyRuleInheritedNamespaces
        sname
        inst
        rules
        (id, idRules)
        folds
        lists
        listSorts
        table
        (calculateInheritedNameSpace sortnameInUse table)
    sortnameInUse = (lookupIdToSort id (folds ++ lists ++ listSorts))
