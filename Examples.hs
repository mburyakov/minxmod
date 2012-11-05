module Examples where

import Types
import Predicates
import ArgTree
import Symbolic
import Symbolic.Step
import Data.Boolean
import Arithmetic

arByteAddStacksOrdering = ArgOrd {
  ordShow = "arByteAddStacksOrdering",
  argCompare = \x y ->
    case (isTail x, isTail y) of
      (False, False) -> compare (permute x) (permute y)
      (True, False) -> GT
      (False, True) -> LT
      (True, True) -> compare x y
  }
    where
      permute l = ((tail.tail) l) ++ [l!!0, l!!1]
      isTail l = l!!1>=2 || (l!!0==1 && l!!1==1)

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
    --Jmp "begin"
  ]

defaultState lineV =
  withPerm (ArgArg[0,0]) (predIs $ valToBin (lineV 0))

simpleProgram2 =
  compile [
    Arith $ arPop byteT
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
      PredPerm (PermPerm $ ArgList [ArgArg [0,0,0], ArgArg [1,0,0]]) (predArithStacks ar)
  &&* PredPerm (PermPerm $ ArgList [ArgArg [0,1], ArgArg [1,1]]) (eq [0,0] [1,0])

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
      
      