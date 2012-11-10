module Symbolic.Step (ProgStates, Kripke, step, fixedPoint) where

import Symbolic hiding (trace', trace'')
import Predicates hiding (trace', trace'')
import BDD
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


step :: Kripke -> ProgStates -> ProgStates
step gr st =
  reducePred stateOrd or
    where
      permSt = withFirst $ PredBDD st
      and = permSt &&* PredBDD gr
      ex = predExists [0,0] and
      permEx = withParentSecond $ PredBDD $ reducePred globalOrd ex
      or = permEx ||* PredBDD st

fixedPoint :: Int -> Kripke -> ProgStates -> (ProgStates, Int)
fixedPoint 0 _ st = (st, 0)
fixedPoint n gr st =
  if
    impl == Just True
  then
    (st, n)
  else
    fixedPoint (n-1) gr newSt
     where    
       impl = toBool $ trace' $ red $ reducePred stateOrd $ (notB (PredBDD $ newSt)) ||* (PredBDD st)
       newSt = step gr st
       red bdd = let Just ans = getBDD (putBDD bdd emptyBox) in ans
