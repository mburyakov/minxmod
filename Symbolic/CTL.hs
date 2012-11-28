module Symbolic.CTL where

import Data.Boolean

import Types
import Arithmetic
import Predicates
import Symbolic
import Symbolic.Step

data CTL p =
    CTLPred p
  | CTLExistsFinally (CTL p)

calcCTL :: Kripke -> CTL ProgStates -> ProgStates
calcCTL _ (CTLPred p) = p
calcCTL prog (CTLExistsFinally ctl) =
  last steplist
    where
      p = calcCTL prog ctl
      steplist = stepList StepBackward StepExists prog p

onPosition :: Integral s => s -> Prog -> ProgStates
onPosition n prog =
  predToProgStates $ withFirst $ withAddressStack $ predIs $ valToBin (lineV 0)
    where
      (enumprog, lineV) = valueEnumerateProg prog

stackLength :: Int ->  ProgStates
stackLength n =
  predToProgStates $ foldl (&&*) (PredArg [1,n,1]) valsStack
    where
      valsStack = map (notB . PredArg . (\x->[0,x,1])) [0..n-1]

initState opts prog =
  if
    lookup "bottom" opts == Nothing
  then
    onPosition 0 prog
  else
    onPosition 0 prog &&* stackLength 0
