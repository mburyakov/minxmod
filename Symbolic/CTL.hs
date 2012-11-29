module Symbolic.CTL where

import Data.Boolean

import Types hiding (initState)
import Arithmetic
import Predicates
import Symbolic
import Symbolic.Step
import CTL

instance Boolean p => Boolean (CTL p) where
  true = CTLTrue
  false = CTLFalse
  notB = CTLNeg
  (&&*) = CTLAnd
  (||*) = CTLOr

calcCTL :: Kripke -> CTL ProgStates -> ProgStates
calcCTL _ CTLTrue = true
calcCTL _ CTLFalse = false
calcCTL prog (CTLNeg p) = notB $ calcCTL prog p
calcCTL prog (CTLAnd a b) = calcCTL prog a &&* calcCTL prog b
calcCTL prog (CTLOr a b) = calcCTL prog a ||* calcCTL prog b
calcCTL _ (CTLPred p) = p
calcCTL prog (CTLExistsNext ctl) =
  step StepBackward StepExists prog $ calcCTL prog ctl
calcCTL prog (CTLAllNext ctl) =
  step StepBackward StepAll prog $ calcCTL prog ctl
calcCTL prog (CTLExistsFinally ctl) =
  last steplist
    where
      p = calcCTL prog ctl
      steplist = stepList StepBackward StepExists prog p
calcCTL prog (CTLAllFinally ctl) =
  last steplist
    where
      p = calcCTL prog ctl
      steplist = stepList StepBackward StepAll prog p
calcCTL prog (CTLAllGlobally ctl) =
  calcCTL prog (notB $ CTLExistsFinally $ notB ctl)
calcCTL prog (CTLExistsGlobally ctl) =
  calcCTL prog (notB $ CTLAllFinally $ notB ctl)


onPosition :: Integral s => s -> Prog -> ProgStates
onPosition n prog =
  predToProgStates $ withAddressStack $ withFirst $ predIs $ valToBin (lineV n)
    where
      (enumprog, lineV) = valueEnumerateProg prog

onLabel :: String -> Prog -> ProgStates
onLabel label prog =
  onPosition n prog
    where
      (Just n) = lookup label $ enum_prog_counter $ integerEnumerateProg prog

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

initState :: Options -> Prog -> ProgStates
initState opts prog =
  if
    lookup "bottom" opts == Nothing
  then
    onPosition 0 prog
  else
    onPosition 0 prog &&* stackLength opts 0


finalState :: Prog -> ProgStates
finalState prog =
  onPosition n prog
    where
      n = length $ enum_prog_insns $ integerEnumerateProg prog

verify :: Options -> Prog -> CTL ProgStates -> Bool
verify opts prog ctl =
  Just False /= (toBool $ progStatesBDD $ calcCTL (progToBDD opts prog) ctl &&* initState opts prog)
