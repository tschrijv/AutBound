{-# OPTIONS_GHC -Wall #-}

module GeneralTerms where

type FoldName         = String
type ConstructorName  = String
type SortName         = String
type NamespaceName    = String
type IdenName         = String
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
  = MkNameSpace {
    nname :: NamespaceName,
    nsort :: SortName,
    nenv :: [String]  -- TODO: what are the envs for?
  }
  deriving (Show, Eq)

--definition of a sort
data SortDef
  = MkDefSort {
    sname :: SortName,
    sctxs :: [Context],
    sctors :: [ConstructorDef],
    srewrite :: Bool
  }
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
    _cbinder :: (IdenName, NamespaceName),
    cattrs :: [AttributeDef],
    cnatives :: [HaskellTypeName]
  }
  | MkVarConstructor {
    cname :: ConstructorName,
    cinst :: InstanceName
  }
  deriving (Show, Eq)

cbinder :: ConstructorDef -> Maybe (IdenName, NamespaceName)
cbinder ctor@MkBindConstructor{} = Just (_cbinder ctor)
cbinder _                        = Nothing

type Language = ([NamespaceDef], [SortDef], [(String, [String])], [String])

-- TODO
getSortNameAndInstances :: SortDef -> (SortName, [Context])
getSortNameAndInstances s = (sname s, sctxs s)

-- | Produce a list of pairs with the first element being an identifier, the
-- second the list of attribute definitions that assign to this identifier
attrByIden :: [AttributeDef] -> [(IdenName, SortName)] -> [(IdenName, [AttributeDef])]
attrByIden attrs sorts = [
  (iden, filter (\(l, _) -> liden l == iden) attrs)
  | (iden, _) <- sorts]
