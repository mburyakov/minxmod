module Illustrations where

import Types
import Examples
import Predicates
import Data.Boolean
import ArgTree
import Checker
import Symbolic
import Main


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

ill5 =
  toFunc p $ toArgList[[toArgList[T,F,F,F,F,F,F,F],toArgList[[[F,F,F,F,F,F,F,F],[F,F,F,F,F,F,F,F]],[]]],[toArgList[F,T,F,F,F,F,F,F],toArgList[[[F,F,F,F,F,F,F,F]],[]]]]
    where
      p = predArByteAddLine 1
      predArByteAddLine n = 
        predLine n (Arith arByteAdd)
-- output: True  

ill6 =
  toFunc p $ toArgList[[toArgList[T,F,F,F,F,F,F,F],toArgList[[[F,F,F,F,F,F,F,F]],[]]],[toArgList[F,T,F,F,F,F,F,F],toArgList[[[T,F,T,F,F,F,F,F],[F,F,F,F,F,F,F,F]],[]]]]
    where
      p = predArBytePushLine 1 (byteV 5)
      predArBytePushLine n v = 
        predLine n (Arith $ arBytePush v)
-- output: True  

ill7 = do
  putStrLn $ show $ incrementer "var"
  putStrLn $ show $ integerEnumerateProg $ incrementer "var"

data B = T | F
instance Binarizable B where
  toArgList T = toArgList True
  toArgList F = toArgList False
