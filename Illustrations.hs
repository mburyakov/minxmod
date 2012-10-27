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
import Symbolic.Step
import Main
import Data.Text.Encoding
import qualified Data.Text.Lazy as Lazy
import qualified Data.ByteString as ByteString


ill1 =
  reducePred' ao $ (PredBDD $ BDDeq [0,1] [1,0] BDDTrue BDDFalse)||*(PredBDD $ BDDv [0,0] BDDTrue BDDFalse)
-- output: BDDv [0,0] BDDTrue (BDDeq [0,1] [1,0] BDDTrue BDDFalse)

ill1'' =
  reducePred' ao $ (PredBDD $ BDDeq [0,0] [1,0] BDDTrue BDDFalse)||*(PredBDD $ BDDv [0,1,0] BDDTrue BDDFalse)
-- output:
-- BDDeq [0,0,0] [1,0,0]
--         (BDDv [0,1,0] BDDTrue
--                       (BDDv [1,1,0] BDDFalse
--                                     (BDDeq [0,1,1] [1,1,1] (BDDeq [0,2] [1,2] BDDTrue BDDFalse)
--                       BDDFalse)))
--         (BDDv [0,1,0] BDDTrue BDDFalse)
  
  
ao = ArgOrd (\x y -> compare (tail x, head x) (tail y, head y)) ""
-- ao = ArgOrd (\x y -> compare (reverse x) (reverse y)) ""


ill1' =
  reducePred' ao $ (PredBDD $ BDDeq [0,0] [1,0] BDDTrue BDDFalse)||*
                   (PredBDD $ BDDv [0,0,0] BDDTrue BDDFalse)
-- output: BDDv [0,0,0] BDDTrue
--                      (BDDv [1,0,0] BDDFalse
--                                    (BDDeq [0,0,1] [1,0,1] (BDDeq [0,1] [1,1] BDDTrue BDDFalse)
--                                                           BDDFalse))

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
  reducePred stateOrd $ predExists [1] $ PredAll 3

predTestExistsEq =
  reducePred stateOrd $ predExists [0,0] $ eq [0,0] [1,0]

ill12 =
  (toFunc predTestExists $ toArgList [T], toFunc predTestExists $ toArgList [F])
-- output: (True, False)

sampleEq2 = BDDeq [0,0] [1,0] BDDTrue BDDFalse
openedSampleEq2 =
  op sampleEq2
    where 
      op (BDDeq i1 j1 a1 b1) = BDDeq
        (passInto i1)
        (passInto j1)
        (BDDeq (nipOne i1) (nipOne j1) a1 b1)
        b1

ill13 = do
  printDotFile "sampleEq2.dot" $ defaultVis $ toGraph $ bddBox $ putBDD sampleEq2 emptyBox
  printDotFile "openedSampleEq2.dot" $ defaultVis $ toGraph $ bddBox $ putBDD openedSampleEq2 emptyBox

ill14 = 
  step start bdd
    where
      bdd = trace' $ progToBDD simpleProgram2
      start = trace' $ reducePred stateOrd $ notB $ PredArg [0,0]
  
data B = T | F
instance Binarizable B where
  toArgList T = toArgList True
  toArgList F = toArgList False
