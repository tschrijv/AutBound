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
  = INH { xinst :: InstanceName, xnamespace :: NamespaceName }
  | SYN { xinst :: InstanceName, xnamespace :: NamespaceName }
  deriving (Show, Eq)

--the left part of an expression like t1.ctx=lhs.ctx
data LeftExpr
  = LeftLHS { linst :: InstanceName }
  | LeftSub { _liden :: IdenName, linst :: InstanceName }
  deriving (Show, Eq)

liden :: LeftExpr -> IdenName
liden left@LeftSub{} = _liden left
liden _                = ""

--the right part of an expression like t1.ctx=lhs.ctx
data RightExpr
  = RightLHS { rinst :: InstanceName }
  | RightSub { riden :: IdenName, rinst :: InstanceName }
  | RightAdd { rexp :: RightExpr, riden :: IdenName }
  deriving (Show, Eq)

--the complete expression of like t1.ctx=lhs.ctx
type AttributeDef = (LeftExpr, RightExpr)

--the definition of a namespace declaration
data NamespaceDef
  = MkNameSpace { nname :: NamespaceName,  nsort :: SortName, nenv :: [String] } -- TODO: what are the envs for?
  deriving (Show, Eq)

--definition of a sort
data SortDef
  = MkDefSort { sname :: SortName, sctxs :: [Context], sctors :: [ConstructorDef], srewrite :: Bool }
  deriving (Show, Eq)

--definition of a constructor
data ConstructorDef
  = MkDefConstructor {
    cname :: ConstructorName,
    clists :: [(IdenName, SortName)],
    csorts :: [(IdenName, SortName)],
    cfolds :: [(IdenName, SortName, FoldName)],
    cattrs :: [AttributeDef],
    cnatives :: [HaskellTypeName]
  }
  | MkBindConstructor {
    cname :: ConstructorName,
    clists :: [(IdenName, SortName)],
    csorts :: [(IdenName, SortName)],
    cfolds :: [(IdenName, SortName, FoldName)],
    cbinder :: (IdenName, NamespaceName),
    cattrs :: [AttributeDef],
    cnatives :: [HaskellTypeName]
  }
  | MkVarConstructor {
    cname :: ConstructorName,
    cinst :: InstanceName
  }
  deriving (Show, Eq)

type Language         = ([NamespaceDef], [SortDef], [(String, [String])], [String])

class Named a where
  getName :: a -> String

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

getCtorRules :: ConstructorDef -> [AttributeDef]
getCtorRules (MkDefConstructor _ _ _ _ rules _) = rules
getCtorRules (MkBindConstructor _ _ _ _ _ rules _) = rules
getCtorRules MkVarConstructor{} = error "invalid method for var constructor"

getCtorHTypes :: ConstructorDef -> [HaskellTypeName]
getCtorHTypes (MkDefConstructor _ _ _ _ _ hTypes) = hTypes
getCtorHTypes (MkBindConstructor _ _ _ _ _ _ hTypes) = hTypes
getCtorHTypes MkVarConstructor{} = error "invalid method for var constructor"

-- TODO
getSortNameAndInstances :: SortDef -> (SortName, [Context])
getSortNameAndInstances s = (sname s, sctxs s)

--collects all the rules of the identifiers used in the constructor and groups them in a list with each identifier getting a list of rules
groupRulesByIden :: [AttributeDef] -> [(IdenName, SortName)] -> [(IdenName, [AttributeDef])]
groupRulesByIden rules sorts = [
    (iden, filter (\(l, r) -> liden l == iden) rules)
  | (iden, _) <- sorts]
