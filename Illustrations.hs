module Illustrations where

import Examples
import Predicates
import Data.Boolean
import ArgTree
import Checker


ill1 =
  reducePred ao $ (PredBDD $ BDDeq [0,1] [1,0] BDDTrue BDDFalse)||*(PredBDD $ BDDv [0,0] BDDTrue BDDFalse)
    where
      ao = ArgOrd (\x y -> compare (reverse x) (reverse y)) ""
-- output: BDDv [0,0] PredTrue (BDDeq [0,1] [1,0] PredTrue PredFalse)

ill1' =
  reducePred ao $ (PredBDD $ BDDeq [0,0] [1,0] BDDTrue BDDFalse)||*(PredBDD $ BDDv [0,0,0] BDDTrue BDDFalse)
    where
      ao = ArgOrd (\x y -> compare (reverse x) (reverse y)) ""

ill2 =
  reducePred arByteAddStacksOrdering $ x


x = predArithStacks arByteAdd
PredNeg x1 = x
PredOr x11 x12 = x1
PredNeg x111 = x11

ill3 =
  toFunc (predAdd 1 1 2) $ toArgList [[[T],[T]],[[F,T]]]
  
ill4 =
  checkPredReduce arByteAddStacksOrdering x $ toArgList [[[T,T,T,T,T,F,T,T],[F,F,F,F,F,T,F,F],[]],[[T,T,T,T,T,T,T,T],[]]]

data B = T | F
instance Binarizable B where
  toArgList T = toArgList True
  toArgList F = toArgList False
