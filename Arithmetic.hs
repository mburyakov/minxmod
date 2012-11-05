module Arithmetic where

import Types
import Predicates
import ArgTree
import Data.Boolean

withPerm perm pred = PredPerm (PermPerm perm) pred

withBefore = withFirst
withAfter  = withSecond

permFirst  = PermPerm $ ArgArg [0,0]
permSecond = PermPerm $ ArgArg [1,0]
permParentFirst  = PermPerm $ ArgList [ArgArg [0], undefined]
permParentSecond = PermPerm $ ArgList [undefined, ArgArg [0]]

withFirst  = PredPerm permFirst
withSecond = PredPerm permSecond
withParentFirst  = PredPerm permParentFirst
withParentSecond = PredPerm permParentSecond

withStacks = withPerm (ArgList [ArgArg[0,1,0],ArgArg[1,1,0]])

withAddressStack = withPerm (ArgArg[0,0])

predIs [] =
  true       
predIs (x:xs) =
  (if x then (PredArg [0]) else notB (PredArg [0]))
   &&* withPerm (ArgArg[1]) (predIs xs) 

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

byteT = SmallBoundedType 0 255
byteV = SmallBoundedValue 0 255

arByteAdd = Arithmetic {
  arithSignature = ([byteT, byteT], [byteT]),
  arithFunc = \s -> [byteV (sbValue (s!!0) + sbValue (s!!1)): drop 2 s],
  arithPredicate = predAdd size size size
}
  where
    size = binSize byteT

arPush val = Arithmetic {
  arithSignature = ([], [valType val]),
  arithFunc = \s -> [val : s],
  arithPredicate = withPerm (ArgArg[1,0,0]) $ predIs $ valToBin $ val
}

arPop t = Arithmetic {
  arithSignature = ([t], []),
  arithFunc = \s -> [tail s],
  arithPredicate = true
}

boolV = SmallBoundedValue 0 1
boolT = SmallBoundedType 0 1
fromBoolValue x =
  case sbValue x of
    0 -> False
    1 -> True
toBoolValue False =
  boolV 0
toBoolValue True =
  boolV 1

arOr = Arithmetic {
  arithSignature = ([boolT, boolT], [boolT]),
  arithFunc = \s -> [toBoolValue (fromBoolValue (s!!0) || fromBoolValue (s!!1)): drop 2 s],
  arithPredicate = ((PredArg [0,0,0]) ||* (PredArg [0,1,0])) ==* (PredArg [1,0,0])
}

arNot = Arithmetic {
  arithSignature = ([boolT], [boolT]),
  arithFunc = \s -> [toBoolValue (not $ fromBoolValue (s!!0)): tail s],
  arithPredicate = (PredArg [0,0,0]) /=* (PredArg [1,0,0])
}

arNop = Arithmetic {
  arithSignature = ([], []),
  arithFunc = \s -> [s],
  arithPredicate = true
}
