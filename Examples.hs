module Examples where

import Types
import Predicates
import ArgTree
import Symbolic
import Data.Boolean

predEq 0 m =
  withAfter  $ notB (PredAny m)
predEq n 0 =
  withBefore $ notB (PredAny n)
predEq n m =
  ifB
    ((PredArg [0,0]) ==* (PredArg [1,0]))
    (PredPerm (PermPerm $ ArgList [ArgArg [0,1], ArgArg [1,1]]) $ predEq (n-1) (m-1))
    false


predInc n 0 =
  false
predInc 0 m =
  withAfter $ (PredArg [0]) &&* (PredPerm (PermPerm $ ArgArg [1]) (notB (PredAny (m-1))))
predInc n m =
  ifB
    ((PredArg [0,0]) ==* (PredArg [1,0]))
    false
    (ifB
      (PredArg [0,0])
      (PredPerm (PermPerm $ ArgList [ArgArg [0,1], ArgArg [1,1]]) $ predInc (n-1) (m-1))
      (PredPerm (PermPerm $ ArgList [ArgArg [0,1], ArgArg [1,1]]) $ predEq (n-1) (m-1)))


predAdd 0 n2 na =
  withPerm (ArgList [ArgArg [0,0,0], ArgArg [1,0,0]]) (predEq n2 na)

predAdd n1 0 na =
  withPerm (ArgList [ArgArg [0,1,0], ArgArg [1,0,0]]) (predEq n1 na)
  
predAdd n1 n2 0 =
      (withFirst.withBefore  $ notB (PredAny n1))
  &&* (withSecond.withBefore $ notB (PredAny n2))

predAdd n1 n2 na =
  ifB
    (((PredArg [0,0,0]) /=* (PredArg [0,1,0])) /=* (PredArg [1,0,0]))
    false
    (ifB
      ((PredArg [0,0,0]) &&* (PredArg [0,1,0]))
      (PredPerm (PermPerm $ ArgList [ArgList [ArgArg [0,0,1], ArgArg [0,1,1]], ArgList [ArgArg [1,0,1]]]) (predIncAdd (n1-1) (n2-1) (na-1)))
      (PredPerm (PermPerm $ ArgList [ArgList [ArgArg [0,0,1], ArgArg [0,1,1]], ArgList [ArgArg [1,0,1]]]) (predAdd (n1-1) (n2-1) (na-1))))


predIncAdd 0 n2 na =
  withPerm (ArgList [ArgArg [0,0,0], ArgArg [1,0,0]]) (predInc n2 na)

predIncAdd n1 0 na =
  withPerm (ArgList [ArgArg [0,1,0], ArgArg [1,0,0]]) (predInc n1 na)

predIncAdd n1 n2 0 =
  false

predIncAdd n1 n2 na =
  ifB
    (((PredArg [0,0,0]) /=* (PredArg [0,1,0])) ==* (PredArg [1,0,0]))
    false
    (ifB
      ((PredArg [0,0,0]) ||* (PredArg [0,1,0]))
        (PredPerm (PermPerm $ ArgList [ArgList [ArgArg [0,0,1], ArgArg [0,1,1]], ArgList [ArgArg [1,0,1]]]) (predIncAdd (n1-1) (n2-1) (na-1)))
        (PredPerm (PermPerm $ ArgList [ArgList [ArgArg [0,0,1], ArgArg [0,1,1]], ArgList [ArgArg [1,0,1]]]) (predAdd (n1-1) (n2-1) (na-1))))

byteT = SmallBoundedType (-0) 1
byteV = SmallBoundedValue (-0) 1

arByteAdd = Arithmetic {
  arithSignature = ([byteT, byteT], [byteT]),
  arithFunc = \s -> [byteV (sbValue (s!!0) + sbValue (s!!1)): drop 2 s],
  arithPredicate = predAdd size size size
}
  where
    size = binSize byteT

arBytePush val = Arithmetic {
  arithSignature = ([], [byteT]),
  arithFunc = \s -> [byteV val : s],
  arithPredicate = withPerm (ArgArg[1,0,0]) $ predIs $ valToBin $ byteV val
}
  where
    size = binSize byteT

arBytePop = Arithmetic {
  arithSignature = ([byteT], []),
  arithFunc = \s -> [tail s],
  arithPredicate = true
}
  where
    size = binSize byteT
  
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

simpleProgram1 =
  compile [
    Label "begin" $ Arith $ arBytePush 5,
    Arith $ arBytePush 3,
    Arith $ arByteAdd,
    Arith $ arBytePop
  ]

simpleProgram2 =
  compile [
    Arith $ arBytePop
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