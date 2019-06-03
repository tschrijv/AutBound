import           ExEffImpl
import Operations 
test1 = ReturnComp TmUnit

test2 =
  fullEvalComputation
    (HandleComp
       (ReturnComp TmUnit)
       (TmHandler (ReturnHandler [] ValTUnit (ReturnComp (TmVar Z)))))

test3 =
  fullEvalComputation
    (ComputationApp (TmFun (ReturnComp (TmVar Z)) ValTUnit) TmUnit)

test4 =
  fullEvalComputation
    (ComputationApp (TmFun (ReturnComp (TmVar (STypeVar Z))) ValTUnit) TmUnit)

test5 = fullEvalComputation
    (HandleComp (OpComp TmUnit) (TmHandler  (ReturnHandler [OpAndComp (ReturnComp TmUnit) IdOp  ] ValTUnit (ReturnComp (TmVar Z)))   ) )