import           FiImpl

test1 = typeOf (TmApp (TmAbs (TmVar Z) TyTop) TmTop) Nil

test2 = typeOf (TmApp (TmAbs (TmVar Z) TyTop) (TmInt 5)) Nil

test3 = typeOf (TmApp (TmAbs (TmVar Z) TyBot) (TmInt 5)) Nil

test4 = typeOf (TmMerge (TmAbs (TmVar Z) TyBot) (TmInt 5)) Nil

test5 = typeOf (TmMerge (TmAbs (TmVar Z) TyTop) (TmInt 5)) Nil

test6 = typeOf (TmMerge (TmAbs (TmVar Z) TyInt) (TmInt 5)) Nil

test7 = typeOf (TmMerge (TmInt 5) (TmAbs (TmVar Z) TyInt)) Nil

test8 = typeOf (TypeApp (TmAll (TyBot) (TmTop)) TyInt) Nil
