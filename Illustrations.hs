module Illustrations where

import Examples
import Predicates
import Data.Boolean
import ArgTree

ill1 =
  reducePred ao $ (PredBDD $ BDDeq [0,1] [1,0] BDDTrue BDDFalse)||*(PredBDD $ BDDv [0,0] BDDTrue BDDFalse)
    where
      ao = ArgOrd (\x y -> compare (reverse x) (reverse y)) ""
-- output: BDDv [0,0] PredTrue (BDDeq [0,1] [1,0] PredTrue PredFalse)


ill2 =
  reducePred arByteAddStacksOrdering $ x


x = predArithStacks arByteAdd
PredNeg x1 = x
PredOr x11 x12 = x1
PredNeg x111 = x11

ill3 =
  toFunc (predAdd 1 1 2) $ toArgList [[[T],[T]],[[F,T]]]

data B = T | F
instance Binarizable B where
  toArgList T = toArgList True
  toArgList F = toArgList False
