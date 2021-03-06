{-# LANGUAGE DeriveDataTypeable #-}

module Examples where

import Symbolic.CTL
import Permutations
import Types hiding (initState)
import Predicates
import ArgTree
import ArgOrd
import Symbolic
import Symbolic.Step
import Data.Boolean
import Data.Typeable
import Arithmetic
import BDD

arByteAddStacksOrdering = ArgOrd $ OrdUnknown {
  argUnknownCompare = \x y ->
    Just $ case (isTail x, isTail y) of
      (False, False) -> compare (permute x) (permute y)
      (True,  False) -> GT
      (False, True)  -> LT
      (True,  True)  -> compare x y,
  argUnknownShow = "arByteAddStacksOrdering"
}
  where
    permute l = ((tail.tail) l, [l!!0, l!!1])
    isTail l = l!!1>=2 || (l!!0==1 && l!!1==1)

data OrdUnknown = OrdUnknown { argUnknownCompare :: ArgIndex -> ArgIndex -> Maybe Ordering, argUnknownShow :: String}
  deriving Typeable
instance Show OrdUnknown where
  show ou = argUnknownShow ou
instance Eq OrdUnknown where
  _ == _ = False
instance ArgOrdClass OrdUnknown where
  argCompare ou = argUnknownCompare ou

templateValueType t =
  argTemplate $ binSize t
      
templateArith ar =
  ArgList [
    ArgArg $ map templateValueType $ fst  $ arithSignature ar,
    ArgArg $ map templateValueType $ snd $ arithSignature ar
  ]

arBytePush val = arPush $ byteV val

arBoolPush val = arPush $ boolV $ if val then 1 else 0

simpleProgram1 =
  compile [
    Label "begin" $ Arith $ arBoolPush False,
    Arith $ arBoolPush True,
    Arith $ arOr,
    Arith $ arNot,
    Arith $ arNop,
    Arith $ arPop boolT
  ]

defaultState :: Integral s => Options -> (s -> Value) -> ProgStates
defaultState opts lineV =
  ProgStates $ reducePred stateOrd $ if lookup "bottom" opts == Nothing then pred1 else pred1 &&* pred2
    where
      pred1 = withPerm (ArgArg[0,0,0]) (predIs $ valToBin (lineV 0))
      pred2 = PredArg [1,0,1]

defaultProgState' opts prog =
  defaultState opts lineV
    where
      (enumprog, lineV) = valueEnumerateProg prog

defaultProgState = initState

simpleProgram2 =
  compile [
    Label "label" $ Arith arNop,
    JmpRet
  ]

simpleProgram3 =
  compile [
    Arith $ arPush $ toBoolValue True,
    Arith $ arPush $ toBoolValue False,
    JmpCall "func",
    Jmp "end",
    Label "func" $ Arith arNop,
    Arith arNot,
    Arith arOr,
    JmpRet,
    Label "end" $ Arith arNop
  ]

simpleProgram4 =
  compile [
    Arith $ arPush $ byteV 1,
    Arith $ arPush $ byteV 2,
    Arith $ arByteAdd
  ]

simpleProgram5 =
  compile [
    Label "begin" $ Arith $ arPush $ SmallBoundedValue 0 3 0,
    Jmp "begin"
  ]

simpleProgram6 =
  compile [
    Arith $ arRand $ boolT
  ]

simpleProgram7 =
  compile [
    Arith $ arRand boolT,
    Arith $ arDup boolT,
    Arith $ arNot,
    Arith $ arOr,
    Label "end" $ Arith arNop
  ]
  
simpleProgram8 =
  compile [
    Jmp "begin",
    
    Label "function" $      
      Arith $ arDup boolT,
      Arith $ arNot,
      Arith $ arOr,
      Arith $ arOr,
    JmpRet,
    
    Label "begin" $
      Arith $ arRand boolT,
      Arith $ arRand boolT,
      JmpCall "function",
    Label "end" $ Arith arNop
  ]

xorList _ [] = []
xorList True  (x:xs) = (not x) : xorList x xs
xorList False (x:xs) = x : xorList x xs

deXorList _ [] = []
deXorList True  (x:xs) = (not x) : deXorList (not x) xs
deXorList False (x:xs) = x : deXorList x xs

grayCode n =
  reverse $ xorList False $ reverse $ intToBin (intBinSize n) n

fromGrayCode l =
  binToInt $ reverse $ deXorList False $ reverse l

-- predicate on whole input and output stacks and pools      
predArithThread ar =
      withPerm (ArgList [ArgArg [0,0,0], ArgArg [1,0,0]]) (predArithStacks ar)
  &&* withPerm (ArgList [ArgArg [0,1], ArgArg [1,1]]) (eq [0,0] [1,0])

predLine :: Integral s => (s -> Value) -> EnumInsn s -> Predicate
predLine lineV (EnumInsn n (Arith ar)) =
  withPerm (ArgArg[0,0,0]) (predIs $ valToBin (lineV un))
    &&* withPerm (ArgArg[1,0,0]) (predIs $ valToBin (lineV (un+1)))
      &&* withPerm (ArgList [ArgArg[0,1,0],ArgArg[1,1,0]]) (predArithThread ar)
        where
          un = fromIntegral n

progToPred prog =
  foldl (||*) (false) preds
    where
      (veprog, valfun) = valueEnumerateProg prog
      veinsns = map (fmap sbValue) $ enum_prog_insns veprog
      preds = map (predLine valfun) veinsns

countBDDNodes bdd =
  bddRoot $ putBDD bdd emptyBox

countNodes options prog =
  countBDDNodes $ progToBDD options prog

countStatesNodes options prog =
  map (countBDDNodes.progStatesBDD) (stepList StepForward StepExists kripke start)
    where
      kripke = progToBDD options prog
      start = defaultProgState options prog


fixedPoint n gr st =
  if
    drop n lst == []
  then
    (last $ lst, n - length lst + 1)
  else  
    (lst !! n, 0)
    where
      lst = stepList StepForward StepExists gr st