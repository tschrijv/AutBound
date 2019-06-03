import           HaskellOutputFCo

test1 = fullEval (TmApp (TmAbs (TmVar Z) TyInt) (TmInt 5))

test2 =
  fullEval (TmTApp (TmTAbs (TmApp (TmAbs (TmVar Z) (TyVar Z)) (TmInt 5))) TyInt)

test3 = typeOf (TmApp (TmAbs (TmVar Z) TyInt) (TmInt 5)) Nil

test4 =
  typeOf (TmTApp (TmTAbs (TmApp (TmAbs (TmVar Z) TyInt) (TmInt 5))) TyInt) Nil

test5 = fullEval (TmApp (TmCast CoTopArrow TmTop) TmTop)

test6 = typeOf (TmCast (CoArrow CoTop CoId) (TmAbs (TmVar Z) TyTop)) Nil

test7 =
  typeOf (TmApp (TmCast (CoArrow CoId CoId) (TmAbs (TmVar Z) TyTop)) TmTop) Nil

test8 =
  fullEval
    (TmApp (TmCast (CoArrow CoId CoTop) (TmAbs (TmVar Z) TyInt)) (TmInt 5))

test9 =
  typeOf
    (TmApp (TmCast (CoArrow CoId CoTop) (TmAbs (TmVar Z) TyInt)) (TmInt 5))
    Nil
