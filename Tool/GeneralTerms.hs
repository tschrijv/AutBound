{-# OPTIONS_GHC -Wall #-}

module GeneralTerms where

type FoldName         = String
type ConstructorName  = String
type SortName         = String
type NamespaceName    = String
type IdenName           = String
type HaskellTypeName  = String
type InstanceName     = String

--the inherited or synthesised contexts
data Context
  = INH { inst :: InstanceName, namespace :: NamespaceName }
  | SYN { inst :: InstanceName, namespace :: NamespaceName }
  deriving (Show, Eq)

--the left part of an expression like t1.ctx=lhs.ctx
data LeftExpr
  = LeftLHS InstanceName
  | LeftSub IdenName InstanceName
  deriving (Show, Eq)

--the right part of an expression like t1.ctx=lhs.ctx
data RightExpr
  = RightLHS InstanceName
  | RightSub IdenName InstanceName
  | RightAdd RightExpr IdenName
  deriving (Show, Eq)

--the complete expression of like t1.ctx=lhs.ctx
type NamespaceRule = (LeftExpr, RightExpr)

--the definition of a namespace declaration
data NamespaceDef
  = MkNameSpace NamespaceName SortName [String]
  deriving (Show, Eq)

--definition of a sort
data SortDef
  = MkDefSort SortName [Context] [ConstructorDef] Bool
  deriving (Show, Eq)

--definition of a constructor
data ConstructorDef
  = MkDefConstructor
      ConstructorName
      [(IdenName, SortName)] -- lists
      [(IdenName, SortName)] -- sorts
      [(IdenName, SortName, FoldName)] -- folds
      [NamespaceRule] -- rules
      [HaskellTypeName]
  | MkBindConstructor
      ConstructorName
      [(IdenName, SortName)] -- lists
      [(IdenName, SortName)] -- sorts
      [(IdenName, SortName, FoldName)] -- folds
      (String, NamespaceName) -- namespace
      [NamespaceRule]
      [HaskellTypeName]
  | MkVarConstructor
      ConstructorName
      InstanceName
  deriving (Show, Eq)

type Language         = ([NamespaceDef], [SortDef], [(String, [String])], [String])

class Named a where
  getName :: a -> String

instance Named SortDef where
  getName (MkDefSort sname _ _ _) = sname

instance Named NamespaceDef where
  getName (MkNameSpace name _ _) = name

-- get the name of definition of a constructor
instance Named ConstructorDef where
  getName (MkDefConstructor cname _ _ _ _ _)    = cname
  getName (MkVarConstructor cname _)            = cname
  getName (MkBindConstructor cname _ _ _ _ _ _) = cname

getCtorLists :: ConstructorDef -> [(IdenName, SortName)]
getCtorLists (MkDefConstructor _ lists _ _ _ _) = lists
getCtorLists (MkBindConstructor _ lists _ _ _ _ _) = lists
getCtorLists MkVarConstructor{} = error "invalid method for var constructor"

getCtorSorts :: ConstructorDef -> [(IdenName, SortName)]
getCtorSorts (MkDefConstructor _ _ listSorts _ _ _) = listSorts
getCtorSorts (MkBindConstructor _ _ listSorts _ _ _ _) = listSorts
getCtorSorts MkVarConstructor{} = error "invalid method for var constructor"

getCtorBindVarName :: ConstructorDef -> Maybe String
getCtorBindVarName (MkBindConstructor _ _ _ _ (s, _) _ _) = Just s
getCtorBindVarName _ = Nothing

getCtorBindVarNamespace :: ConstructorDef -> Maybe String
getCtorBindVarNamespace (MkBindConstructor _ _ _ _ (s, _) _ _) = Just s
getCtorBindVarNamespace _ = Nothing

getCtorFolds :: ConstructorDef -> [(IdenName, SortName, FoldName)]
getCtorFolds (MkDefConstructor _ _ _ folds _ _) = folds
getCtorFolds (MkBindConstructor _ _ _ folds _ _ _) = folds
getCtorFolds MkVarConstructor{} = error "invalid method for var constructor"

getCtorRules :: ConstructorDef -> [NamespaceRule]
getCtorRules (MkDefConstructor _ _ _ _ rules _) = rules
getCtorRules (MkBindConstructor _ _ _ _ _ rules _) = rules
getCtorRules MkVarConstructor{} = error "invalid method for var constructor"

getCtorHTypes :: ConstructorDef -> [HaskellTypeName]
getCtorHTypes (MkDefConstructor _ _ _ _ _ hTypes) = hTypes
getCtorHTypes (MkBindConstructor _ _ _ _ _ _ hTypes) = hTypes
getCtorHTypes MkVarConstructor{} = error "invalid method for var constructor"

--get the defs of constructors in the sort
getSortCtors :: SortDef -> [ConstructorDef]
getSortCtors (MkDefSort _ _ cdefs _) = cdefs

-- get the instances by the sorts in the
getSortInstances :: SortDef -> [Context]
getSortInstances (MkDefSort _ instances _ _) = instances

--get the names   contexts and the namespaces it refers to for a sorts in a tuple
getSortNameAndInstances :: SortDef -> (SortName, [Context])
getSortNameAndInstances s = (getName s, getSortInstances s)

getLeftSubIden :: LeftExpr -> IdenName
getLeftSubIden (LeftLHS _)    = ""
getLeftSubIden (LeftSub iden _) = iden

--get the name of the context of a left expr
getLeftSubInstanceName :: LeftExpr -> InstanceName
getLeftSubInstanceName (LeftLHS name)   = name
getLeftSubInstanceName (LeftSub _ name) = name

--collects all the rules of the identifiers used in the constructor and groups them in a list with each identifier getting a list of rules
groupRulesByIden :: [NamespaceRule] -> [(IdenName, SortName)] -> [(IdenName, [NamespaceRule])]
groupRulesByIden rules sorts = [
    (iden, filter (\(l, r) -> getLeftSubIden l == iden) rules)
  | (iden, _) <- sorts]
