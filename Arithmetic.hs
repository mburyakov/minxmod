module Arithmetic where

import Types
import ArgTree
import Permutations
import Predicates

import Data.Boolean
import Data.Monoid

withPerm perm pred = PredPerm (Permutation $ PermPerm perm) pred

doPerm = Permutation . PermPerm

withBefore = withFirst
withAfter  = withSecond

permFirst  = doPerm $ ArgArg [0,0]
permSecond = doPerm $ ArgArg [1,0]
permParentFirst  = doPerm $ ArgList [ArgArg [0]]
--permParentSecond = PermPerm $ ArgList [error "undefined in permParentSecond", ArgArg [0]]
permParentSecond = doPerm (ArgArg[-1]) `mappend` permParentFirst

withFirst  = PredPerm permFirst
withSecond = PredPerm permSecond
withParentFirst  = PredPerm permParentFirst
withParentSecond = PredPerm permParentSecond


permStacks = doPerm $ ArgList [ArgArg[0,1,0],ArgArg[1,1,0]]
withStacks = PredPerm permStacks

permAddressStack = doPerm $ ArgArg[0,0]
withAddressStack = PredPerm permAddressStack

permAddressStacks = doPerm $ ArgList [ArgArg[0,0,0],ArgArg[1,0,0]]
withAddressStacks = PredPerm permAddressStacks


permAddressStacksRest = doPerm $ ArgList [ArgArg[0,0,1],ArgArg[1,0,1]]
withAddressStacksRest = PredPerm permAddressStacksRest

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
    (withPerm (ArgList [ArgArg [0,1], ArgArg [1,1]]) (predEq (n-1) (m-1)))
    false


predInc n 0 =
  false
predInc 0 m =
  withAfter $ (PredArg [0]) &&* (withPerm (ArgArg [1]) (notB (PredAny (m-1))))
predInc n m =
  ifB
    ((PredArg [0,0]) ==* (PredArg [1,0]))
    false
    (ifB
      (PredArg [0,0])
      (withPerm (ArgList [ArgArg [0,1], ArgArg [1,1]]) (predInc (n-1) (m-1)))
      (withPerm (ArgList [ArgArg [0,1], ArgArg [1,1]]) (predEq (n-1) (m-1))))


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
      (withPerm (ArgList [ArgList [ArgArg [0,0,1], ArgArg [0,1,1]], ArgList [ArgArg [1,0,1]]]) (predIncAdd (n1-1) (n2-1) (na-1)))
      (withPerm (ArgList [ArgList [ArgArg [0,0,1], ArgArg [0,1,1]], ArgList [ArgArg [1,0,1]]]) (predAdd (n1-1) (n2-1) (na-1))))


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
        (withPerm (ArgList [ArgList [ArgArg [0,0,1], ArgArg [0,1,1]], ArgList [ArgArg [1,0,1]]]) (predIncAdd (n1-1) (n2-1) (na-1)))
        (withPerm (ArgList [ArgList [ArgArg [0,0,1], ArgArg [0,1,1]], ArgList [ArgArg [1,0,1]]]) (predAdd (n1-1) (n2-1) (na-1))))

byteLimit = 256
byteT = SmallBoundedType 0 (byteLimit-1)
byteV = SmallBoundedValue 0 (byteLimit-1)

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

arRand t@(SmallBoundedType from to) = Arithmetic {
  arithSignature = ([], [t]),
  arithFunc = \s -> map ((:s).v) [from .. to],
  arithPredicate = true
}
  where
    v = SmallBoundedValue from to

arPop t = Arithmetic {
  arithSignature = ([t], []),
  arithFunc = \s -> [tail s],
  arithPredicate = true
}

arReplace val = Arithmetic {
  arithSignature = ([valType val], [valType val]),
  arithFunc = \s -> [val : tail s],
  arithPredicate = withPerm (ArgArg[1,0,0]) $ predIs $ valToBin $ val
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
