module Symbolic.Step where

import Symbolic
import Predicates
import BDD
import ArgTree
import Data.Boolean
import DebugStub
import qualified Debug1
import Arithmetic

data ProgStates = ProgStates {progStatesBDD :: BDD}
  deriving Show
instance Eq ProgStates where
  s1 == s2 =
    impl == Just True
      where    
        impl = toBool $ red $ reducePred stateOrd $ (notB (PredBDD $ progStatesBDD s2)) ||* (PredBDD $ progStatesBDD s1)

instance Boolean ProgStates where
  true  = ProgStates $ red $ reducePred stateOrd true
  false = ProgStates $ red $ reducePred stateOrd false
  notB  = ProgStates . red . reducePred stateOrd . notB . PredBDD . progStatesBDD
  a &&* b = ProgStates . red . reducePred stateOrd $ (PredBDD $ progStatesBDD a) &&* (PredBDD $ progStatesBDD b)
  a ||* b = ProgStates . red . reducePred stateOrd $ (PredBDD $ progStatesBDD a) ||* (PredBDD $ progStatesBDD b)

red bdd = let Just ans = getBDD (putBDD bdd emptyBox) in ans

predToProgStates =
  ProgStates . reducePred stateOrd

type Kripke = BDD

data StepDirection = StepForward | StepBackward
data StepQuantifier = StepAll | StepExists
data StepType = StepFinally | StepGlobally

step :: StepDirection -> StepQuantifier -> Kripke -> ProgStates -> ProgStates
step dir quantif gr st =
  ProgStates $ reducePred stateOrd or
    where
      permSt = fromperm $ PredBDD $ progStatesBDD st
      and = case quantif of
        StepExists -> PredBDD gr &&* permSt
        StepAll -> notB (PredBDD gr) ||* permSt
      ex1 = quant quantside $ PredBDD $ processForces (const Nothing) $ reducePred globalOrd $ and
      ex2 = predExists quantside $ PredBDD $ processForces (const Nothing) $ reducePred globalOrd $ PredBDD $ gr
      ex3 = case quantif of
        StepExists ->
          ex1
        StepAll ->
          ex1 &&* ex2
      permEx = toperm $ PredBDD $ reducePred globalOrd ex3
      or = permEx ||* PredBDD (progStatesBDD st)
      fromperm = case dir of
        StepForward  -> withFirst
        StepBackward -> withSecond
      toperm = case dir of
        StepForward  -> withParentSecond
        StepBackward -> withParentFirst
      quant = case quantif of
        StepExists -> predExists
        StepAll -> predForAll
      quantside = case dir of
        StepForward  -> [0,0]
        StepBackward -> [1,0]

stepList :: StepDirection -> StepQuantifier -> Kripke -> ProgStates -> [ProgStates] 
stepList dir quantif gr st =
  st:rest
    where
      newSt = step dir quantif gr st
      rest' = stepList dir quantif gr newSt
      rest = if st==newSt then [] else rest'

