{-# OPTIONS_GHC -Wall #-}

module GeneralTerms where

type FoldName         = String
type ConstructorName  = String
type SortName         = String
type NamespaceName    = String
type IdenName         = String
type HaskellTypeName  = String
type InstanceName     = String

-- | Definition of an inherited or a synthesized context
data Context
  = INH { xinst :: InstanceName, xnamespace :: NamespaceName }
  | SYN { xinst :: InstanceName, xnamespace :: NamespaceName }
  deriving (Show, Eq)

-- | The left side of an attribute definition
data LeftExpr
  = LeftLHS { linst :: InstanceName }
  | LeftSub { _liden :: IdenName, linst :: InstanceName }
  deriving (Show, Eq)

-- | Returns the identifier on the left side of the attribute definition
-- or an empty string if it is a LHS definition
liden :: LeftExpr -> IdenName
liden left@LeftSub{} = _liden left
liden _                = ""

-- | The right side of an attribute definition
data RightExpr
  = RightLHS { rinst :: InstanceName }
  | RightSub { riden :: IdenName, rinst :: InstanceName }
  | RightAdd { rexp :: RightExpr, riden :: IdenName }
  deriving (Show, Eq)

-- | Attribute definition (e.g. t1.ctx = lhs.ctx, T)
type AttributeDef = (LeftExpr, RightExpr)

-- | Namespace declaration
data NamespaceDef
  = MkNameSpace {
    nname :: NamespaceName,
    nsort :: SortName
  }
  deriving (Show, Eq)

-- | Sort declaration
data SortDef
  = MkDefSort {
    sname    :: SortName,
    sctxs    :: [Context],
    sctors   :: [ConstructorDef],
    srewrite :: Bool
  }
  deriving (Show, Eq)

-- | Constructor declaration
data ConstructorDef
  = MkDefConstructor {
    cname    :: ConstructorName,
    clists   :: [(IdenName, SortName)],
    csorts   :: [(IdenName, SortName)],
    cfolds   :: [(IdenName, SortName, FoldName)],
    cattrs   :: [AttributeDef],
    cnatives :: [HaskellTypeName]
  }
  | MkBindConstructor {
    cname    :: ConstructorName,
    clists   :: [(IdenName, SortName)],
    csorts   :: [(IdenName, SortName)],
    cfolds   :: [(IdenName, SortName, FoldName)],
    _cbinder :: (IdenName, NamespaceName),
    cattrs   :: [AttributeDef],
    cnatives :: [HaskellTypeName]
  }
  | MkVarConstructor {
    cname :: ConstructorName,
    cinst :: InstanceName
  }
  deriving (Show, Eq)

-- | Returns the binder of a constructor or Nothing if it is not a bind
-- constructor
cbinder :: ConstructorDef -> Maybe (IdenName, NamespaceName)
cbinder ctor@MkBindConstructor{} = Just (_cbinder ctor)
cbinder _                        = Nothing

-- | Returns whether the given constructor has a binder
isBind :: ConstructorDef -> Bool
isBind MkBindConstructor{} = True
isBind _                   = False

-- | Complete definition of a language
type Language = ([NamespaceDef], [SortDef], [(String, [String])], [String])
