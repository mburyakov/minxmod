module Predicates where

import Data.Boolean

data Predicate =
    PredTrue
  | PredFalse
  | PredArg   Int
  | PredNeg       (Predicate)
  | PredOr        (Predicate) (Predicate)
  | PredAnd       (Predicate) (Predicate)
  | PredImpl      (Predicate) (Predicate)
  | PredEquiv     (Predicate) (Predicate)
  | PredXor       (Predicate) (Predicate)
  | PredIf        (Predicate) (Predicate) (Predicate)
  | PredPerm      (Permutation Bool) (Predicate)
  | PredAll   Int
  | PredAny   Int
  | PredSat Int (Predicate)
  deriving (Show)

data Permutation a =
    PermId
  | PermShift Int
  | PermPerm [Int]
  deriving (Show)

toFunc :: Predicate -> [Bool] -> Bool
toFunc PredTrue        x = true
toFunc PredFalse       x = false
toFunc (PredArg i)     x = x !! i
toFunc (PredNeg a)     x = notB $ toFunc a x
toFunc (PredOr a b)    x = (toFunc a x) ||* (toFunc b x)
toFunc (PredAnd a b)   x = (toFunc a x) &&* (toFunc b x)
toFunc (PredImpl a b)  x = toFunc (PredOr (PredNeg a) b) x
toFunc (PredEquiv a b) x = toFunc (PredOr (PredAnd a b) (PredAnd (PredNeg a) (PredNeg b))) x
toFunc (PredXor a b)   x = notB $ toFunc (PredEquiv a b) x
toFunc (PredIf a b c)  x = if toFunc a x then toFunc b x else toFunc c x
toFunc (PredPerm p a)  x = toFunc a $ toPerm p x
toFunc (PredAll n)     x = foldl (&&*) true  $ take n x
toFunc (PredAny n)     x = foldl (||*) false $ take n x

toPerm :: Permutation a -> [a] -> [a]
toPerm PermId x        = id x
toPerm (PermShift n) x = drop n x       
toPerm (PermPerm indexes) x = [ x !! i | i <- indexes]