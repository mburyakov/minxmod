module Symbolic.Step where

import Symbolic
import Predicates
import ArgTree
import Data.Boolean

type ProgStates = BDD

type Kripke = BDD


step :: ProgStates -> Kripke -> ProgStates
step st gr =
  reducePred globalOrd $ permEx
    where
      permSt = trace' $ PredPerm (PermPerm $ ArgArg[0,0]) $ PredBDD st
      and = trace' $ permSt &&* PredBDD gr
      ex = trace' $ predExists [0] and
      permEx = trace' $ PredPerm (PermPerm $ ArgList[ArgArg[0]]) $ ex
