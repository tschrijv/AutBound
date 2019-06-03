import           HaskellOutputFCoSecond

test1 = fullEval (TmApp (TmAbs (TmVar Z) TyInt) (TmInt 5))

test2 =
  fullEval (TmTApp (TmTAbs (TmApp (TmAbs (TmVar Z) (TyVar Z)) (TmInt 5))) TyInt)

test3 = typeOf (TmApp (TmAbs (TmVar Z) TyInt) (TmInt 5)) Nil

test4 =
  typeOf (TmTApp (TmTAbs (TmApp (TmAbs (TmVar Z) TyInt) (TmInt 5))) TyInt) Nil

test5 = fullEval (TmApp (TmCast CoTopArrow TmTop) TmTop)

test6 = typeOf (TmCast (CoArrow (CoTop TyTop) CoId) (TmAbs (TmVar Z) TyTop)) Nil

test7 =
  typeOf (TmApp (TmCast (CoArrow CoId CoId) (TmAbs (TmVar Z) TyTop)) TmTop) Nil

test8 =
  fullEval
    (TmApp
       (TmCast (CoArrow CoId (CoTop TyTop)) (TmAbs (TmVar Z) TyInt))
       (TmInt 5))

test9 =
  typeOf
    (TmApp
       (TmCast (CoArrow CoId (CoTop TyTop)) (TmAbs (TmVar Z) TyInt))
       (TmInt 5))
    Nil

test10 =
  fullEval (TmApp (TmAbs (TmAbs (TmVar (STypeVar Z)) TyInt) TyInt) (TmInt 5))

test11 =
  fullEval
    (TmApp
       (TmAbs (TmAbs (TmVar (STermVar Z)) TyTop) (TyArr TyTop TyTop))
       (TmAbs (TmVar Z) TyTop))

test12 =
  typeOf
    (TmApp
       (TmAbs (TmAbs (TmVar (STermVar Z)) TyTop) (TyArr TyTop TyTop))
       (TmAbs (TmVar Z) TyTop))
    Nil

test14 = fullEval (TmCast (CoTrans (CoTop TyTop) (CoTop TyTop)) (TmInt 5))
