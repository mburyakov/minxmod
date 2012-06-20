module Predicates where

import Data.Boolean

data Predicate p =
    PredTrue
  | PredFalse
  | PredArg Int
  | PredNeg (Predicate p)
  | PredOr (Predicate p) (Predicate p)
  | PredAnd (Predicate p) (Predicate p)
  | PredImpl (Predicate p) (Predicate p)
  | PredEquiv (Predicate p) (Predicate p)
  deriving (Show)
  
toFunc :: (Boolean p) => (Predicate p) -> [p] -> p
toFunc PredTrue        x = true
toFunc PredFalse       x = false
toFunc (PredArg n)     x = flip (!!) n x
toFunc (PredNeg a)     x = notB $ toFunc a x
toFunc (PredOr a b)    x = (toFunc a x) ||* (toFunc b x)
toFunc (PredAnd a b)   x = (toFunc a x) &&* (toFunc b x)
toFunc (PredImpl a b)  x = toFunc (PredOr (PredNeg a) b) x
toFunc (PredEquiv a b) x = toFunc (PredOr (PredAnd a b) (PredAnd (PredNeg a) (PredNeg b))) x
