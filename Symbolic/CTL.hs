module Symbolic.CTL where

import Data.Boolean

import Types hiding (initState)
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
  predToProgStates $ withAddressStack $ withFirst $ predIs $ valToBin (lineV n)
    where
      (enumprog, lineV) = valueEnumerateProg prog

stackLength :: Options -> Int ->  ProgStates
stackLength opts n | lookup "bottom" opts /= Nothing =
  predToProgStates $ foldl (&&*) (withStack $ withNth n $ withSecond $ predIsTrue) valsStack
    where
      valsStack = map (\x -> notB $ withStack $ withNth x $ withSecond $ predIsTrue) [0..n-1]

inPosOfStack :: Options -> Int -> Value -> ProgStates
inPosOfStack opts n v =
  predToProgStates $ withIt $ predIs $ valToBin v
    where
      withIt =
        if lookup "bottom" opts /= Nothing
	then
          (withStack . withNth n . withFirst)
	else
          (withStack . withNth n)

initState opts prog =
  if
    lookup "bottom" opts == Nothing
  then
    onPosition 0 prog
  else
    onPosition 0 prog &&* stackLength opts 0

verify :: Options -> Prog -> CTL ProgStates -> Bool
verify opts prog ctl =
  Just False /= (toBool $ progStatesBDD $ calcCTL (progToBDD opts prog) ctl &&* initState opts prog)
