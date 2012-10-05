module Examples where

import Types
import Predicates
import ArgTree
import Data.Boolean

withPerm perm pred = PredPerm (PermPerm perm) pred

withBefore = withFirst
withAfter  = withSecond

withFirst  = withPerm $ ArgArg [0,0]
withSecond = withPerm $ ArgArg [1,0]

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

first  (x,y) = x
second (x,y) = y

byteT = SmallBoundedType (-127) 128
byteV = SmallBoundedValue (-127) 128

arByteAdd = Arithmetic {
  arithSignature = ([byteT, byteT], [byteT]),
  arithFunc = \s -> [byteV (sbValue (s!!0) + sbValue (s!!1)): drop 2 s],
  arithPredicate = predAdd 1 1 2
}

inputDepth :: Arithmetic -> Int
inputDepth = length.first.arithSignature

outputDepth :: Arithmetic -> Int
outputDepth = length.second.arithSignature

-- predicate on whole input and output stacks
predArithStacks ar = 
  pred &&* (PredBDD $ BDDeq [0,inl] [1,outl] BDDTrue BDDFalse)
    where
      pred = arithPredicate ar
      inl = inputDepth ar
      outl = outputDepth ar

-- predicate on whole input and output stacks and pools      
predArithThread ar = 
      PredPerm (PermPerm $ ArgList [ArgArg [0,0,0], ArgArg [1,0,0]]) (predArithStacks ar)
  &&* PredPerm (PermPerm $ ArgList [ArgArg [0,1], ArgArg [1,1]]) (PredBDD $ BDDeq [0,0] [1,0] BDDTrue BDDFalse)
  
arByteAddStacksOrdering = ArgOrd {
  show' = "Base",
  argCompare = \x y -> 
                        compare (permute x) (permute y)               
  }
    where
      permute l = [l!!1, l!!0] ++ (tail.tail) l
  
-- predicate on whole input and output stacks and pools
predGet var =
  PredPerm (PermPerm $ ArgList [])
      
templateValueType t =
  argTemplate $ binSize t
      
templateArith ar =
  ArgList [
    ArgArg $ map templateValueType $ first  $ arithSignature ar,
    ArgArg $ map templateValueType $ second $ arithSignature ar
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

--predLine n (Arith (Arithmetic sign func pred) =