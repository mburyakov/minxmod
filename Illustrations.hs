module Illustrations where

import Types
import Examples
import Predicates
import BDD
import qualified Data.Map as Map
import Data.Graph.Inductive.Tree
import qualified Data.Graph.Inductive.Graph as Graph
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import Data.Boolean
import ArgTree
import Checker
import Symbolic
import Main
import Data.Text.Encoding
import qualified Data.Text.Lazy as Lazy
import qualified Data.ByteString as ByteString


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
        predLine byteV (EnumInsn n (Arith arByteAdd))
-- output: True

ill6 =
  toFunc p $ toArgList[[toArgList[T,F,F,F,F,F,F,F],toArgList[[[F,F,F,F,F,F,F,F]],[]]],[toArgList[F,T,F,F,F,F,F,F],toArgList[[[T,F,T,F,F,F,F,F],[F,F,F,F,F,F,F,F]],[]]]]
    where
      p = predArBytePushLine 1 5
      predArBytePushLine n v =
        predLine byteV (EnumInsn n (Arith $ arBytePush v))
-- output: True

ill7 = do
  putStrLn $ show $ incrementer "var"
  putStrLn $ show $ integerEnumerateProg $ incrementer "var"

ill8 =
  progToBDD simpleProgram1

boxedBDD1 =
  putBDD (BDDv [0] BDDTrue (BDDeq [1] [2] BDDFalse BDDTrue)) emptyBox

ill9 =
  getBDD boxedBDD1

printDotFile fileName dot =
  ByteString.writeFile fileName $ encodeUtf8 $ Lazy.toStrict $ printDotGraph dot

ill10 =
  printDotFile "boxedBDD1.dot" $ defaultVis $ toGraph $ bddBox boxedBDD1
  
ill11 =
  printDotFile "simpleProgram1.dot" $ defaultVis $ toGraph $ bddBox $ putBDD (progToBDD simpleProgram1) emptyBox

predTestExists =
  predExists 2 $ PredAll 3

ill12 =
  (toFunc predTestExists $ toArgList [T], toFunc predTestExists $ toArgList [F])
-- output: (True, False)


data B = T | F
instance Binarizable B where
  toArgList T = toArgList True
  toArgList F = toArgList False
