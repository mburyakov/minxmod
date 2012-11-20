module Symbolic.Step where

import Symbolic
import Predicates
import BDD
import ArgTree
import Data.Boolean
import DebugStub
--import Debug1
import Arithmetic

data ProgStates = ProgStates {progStatesBDD :: BDD}
instance Eq ProgStates where
  s1 == s2 =
    impl == Just True
      where    
        impl = toBool $ red $ reducePred stateOrd $ (notB (PredBDD $ progStatesBDD s2)) ||* (PredBDD $ progStatesBDD s1)
        red bdd = let Just ans = getBDD (putBDD bdd emptyBox) in ans


type Kripke = BDD


step :: Kripke -> ProgStates -> ProgStates
step gr st =
  ProgStates $ reducePred stateOrd or
    where
      permSt = withFirst $ PredBDD $ progStatesBDD st
      and = permSt &&* PredBDD gr
      ex = predExists [0,0] $ PredBDD $ processForces (const Nothing) $ reducePred globalOrd $ and
      permEx = withParentSecond $ PredBDD $ reducePred globalOrd ex
      or = permEx ||* PredBDD (progStatesBDD st)

stepList :: Kripke -> ProgStates -> [ProgStates] 
stepList gr st =
  st:rest
    where
      newSt = step gr st
      rest' = stepList gr newSt
      rest = if st==newSt then [] else rest'
      
fixedPoint n gr st =
  if
    drop n lst == []
  then
    (last $ lst, n - length lst + 1)
  else  
    (lst !! n, 0)
    where
      lst = stepList gr st
