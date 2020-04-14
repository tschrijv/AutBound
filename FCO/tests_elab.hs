import           Elaborate
import           FiPlusBase
import           FiImpl

test1 = elaborate (TmApp (TmAbs (TmVar Z) TyTop) (TmInt 5)) Nil

test2 = elaborate (TmAnn (TmInt 5) (TyTop)) Nil

test3 = elaborate (TmAnn (TmInt 5) (TyInt)) Nil

test4 = elaborate (TmAnn (TmInt 5) (TyBot)) Nil

test5 = goodelaborate (TypeApp (TmAll (TyBot) (TmTop)) TyInt)

test6 = goodelaborate (TmAnn (TmInt 5) (TyTop))
