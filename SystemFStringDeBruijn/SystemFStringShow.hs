module SystemFStringShow where
import SystemFStringBase

-- show functions

prettyVar :: Variable -> String
prettyVar (SVarValue v) = v
prettyVar (SVarType v) = v

prettyTerm :: Term -> String
prettyTerm (TmVariable var) = prettyVar var
prettyTerm (TmApply t1 t2) = "(" ++ prettyTerm t1 ++ " " ++ prettyTerm t2 ++ ")"
prettyTerm (TmTypeApply term typ) = "(" ++ prettyTerm term ++ " [" ++ prettyType typ ++ "])"
prettyTerm (TmValue v) = prettyValue v

prettyValue :: Value -> String
prettyValue (Abstraction var term typ) = "(\\" ++ prettyVar var ++ ": " ++ prettyType typ ++ " -> " ++ prettyTerm term ++ ")"
prettyValue (TypeAbstraction var term) = "(template<" ++ prettyVar var ++ "> " ++ prettyTerm term ++ ")"

prettyType :: Type -> String
prettyType (TypVariable v) = prettyVar v
prettyType (TypFunction from to) = "(" ++ prettyType from ++ " --> " ++ prettyType to ++ ")"
prettyType (TypUniversal var typ) = "∀." ++ prettyVar var ++ " " ++ prettyType typ
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

-- create an Abstraction
data TypedVar = TypedVar String Type

(=:) :: String -> Type -> TypedVar
s =: t = TypedVar s t

(/->) :: TypedVar -> Term -> Term
(TypedVar name typ) /-> term = TmValue (Abstraction (SVarValue name) term typ)

-- create a Type Abstraction
template :: String -> Term -> Term
template name t = TmValue (TypeAbstraction (SVarType name) t)

-- instantiate a Type Abstraction witha type
(<::) :: Term -> Type -> Term
term <:: typ = TmTypeApply term typ

-- apply a term onto another term
(<:) :: Term -> Term -> Term
func <: arg = TmApply func arg

-- create a function type
(-->) :: Type -> Type -> Type
from --> to = TypFunction from to


