module Symbolic.Step (ProgStates, Kripke, step, fixedPoint) where

import Symbolic
import Predicates hiding (trace', trace'')
import ArgTree
import Data.Boolean
import Debug.Trace
import Arithmetic
--trace' x = x
--trace'' x y = y
trace' x = trace ("trace' :'" ++ show x ++ "' ++ \n") x
--trace'' x y = trace ("trace' :''" ++ show x ++ "' ++ \n") y
--error' x = error $ show x

type ProgStates = BDD

type Kripke = BDD


step :: ProgStates -> Kripke -> ProgStates
step st gr =
  reducePred stateOrd or
    where
      permSt = withFirst $ PredBDD st
      and = permSt &&* PredBDD gr
      ex = predExists [0,0] and
      permEx = withParentSecond $ PredBDD $ reducePred globalOrd ex
      or = permEx ||* PredBDD st

fixedPoint :: Int -> ProgStates -> Kripke -> (ProgStates, Int)
fixedPoint 0 st _ = (st, 0)
fixedPoint n st gr =
  trace (show st) $ if
    impl == Just False
  then
    (st, n)
  else
    fixedPoint (n-1) newSt gr
    
    where
      impl = toBool $ reducePred stateOrd $ notB (PredBDD st) ||* PredBDD newSt
      newSt = step st gr
