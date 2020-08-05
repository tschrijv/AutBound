module SystemFDeBruijnShow where
import SystemFDeBruijnBase

-- show functions

getVarIndex :: Variable -> Int
getVarIndex Z = 0
getVarIndex (SVarType v) = getVarIndex v + 1
getVarIndex (SVarValue v) = getVarIndex v + 1

prettyVar :: Variable -> String
prettyVar Z = ""
prettyVar (SVarValue v) = "v" ++ prettyVar v
prettyVar (SVarType v) = "t" ++ prettyVar v

prettyTerm :: Term -> String
prettyTerm (TmVariable var) = "v_" ++ prettyVar var
prettyTerm (TmApply t1 t2) = "(" ++ prettyTerm t1 ++ " <: " ++ prettyTerm t2 ++ ")"
prettyTerm (TmTypeApply term typ) = "(" ++ prettyTerm term ++ " <:: " ++ prettyType typ ++ ")"
prettyTerm (TmValue v) = prettyValue v

prettyValue :: Value -> String
prettyValue (Abstraction term typ) = "(" ++ prettyType typ ++ " /-> " ++ prettyTerm term ++ ")"
prettyValue (TypeAbstraction term) = "template " ++ prettyTerm term

prettyType :: Type -> String
prettyType (TypVariable v) = "t_" ++ prettyVar v
prettyType (TypFunction from to) = "(" ++ prettyType from ++ " --> " ++ prettyType to ++ ")"
prettyType (TypUniversal v) = "A.X " ++ prettyType v
prettyType (Typ s) = "{" ++ s ++ "}"

instance Show Variable where
  show = prettyVar
instance Show Term where
  show = prettyTerm
instance Show Type where
  show = prettyType
instance Show Value where
  show = prettyValue


-- operators to construct terms and types

t_ :: Type
t_ = TypVariable Z
t_v :: Type
t_v = TypVariable (SVarValue Z)
t_t :: Type
t_t = TypVariable (SVarType Z)
t_vv :: Type
t_vv = TypVariable (SVarValue (SVarValue Z))
t_tt :: Type
t_tt = TypVariable (SVarType (SVarType Z))
t_vt :: Type
t_vt = TypVariable (SVarValue (SVarType Z))
t_tv :: Type
t_tv = TypVariable (SVarType (SVarValue Z))

v_ :: Term
v_ = TmVariable Z
v_v :: Term
v_v = TmVariable (SVarValue Z)
v_t :: Term
v_t = TmVariable (SVarType Z)
v_vv :: Term
v_vv = TmVariable (SVarValue (SVarValue Z))
v_tt :: Term
v_tt = TmVariable (SVarType (SVarType Z))
v_vt :: Term
v_vt = TmVariable (SVarValue (SVarType Z))
v_tv :: Term
v_tv = TmVariable (SVarType (SVarValue Z))

-- create an Abstraction
(/->) :: Type -> Term -> Term
typ /-> term = TmValue (Abstraction term typ)

-- create a Type Abstraction
template :: Term -> Term
template t = TmValue (TypeAbstraction t)

-- instantiate a Type Abstraction witha type
(<::) :: Term -> Type -> Term
term <:: typ = TmTypeApply term typ

-- apply a term onto another term
(<:) :: Term -> Term -> Term
func <: arg = TmApply func arg

-- create a function type
(-->) :: Type -> Type -> Type
from --> to = TypFunction from to
