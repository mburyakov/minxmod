--{-# LANGUAGE ScopedTypeVariables #-}

module Checker where

import Test.QuickCheck
import Types
import ArgTree
import Examples
import Illustrations
import Predicates
import Data.Boolean

data Bimorphism a b = Bimorphism {
  to   :: a -> b,
  from :: b -> a
}

flipBimorphism (Bimorphism to from) = (Bimorphism from to)

checkInjection :: Eq a => Bimorphism a b -> a -> Bool
checkInjection i x = 
  x == from i (to i x)

viewInjection :: Bimorphism a b -> a -> (a, b, a)
viewInjection i x = 
  (x, to i x, from i $ to i x)

checkIntBin (NonNegative n) = checkInjection (Bimorphism (intToHisBin::Int->[Bool]) binToInt) n
checkIntegerBin (NonNegative n) = checkInjection (Bimorphism (intToHisBin::Integer->[Bool]) binToInt) n

checkXorList = checkInjection (Bimorphism (xorList False) (deXorList False))

checkGrayCode (NonNegative n) = checkInjection (Bimorphism (grayCode::Int->[Bool]) fromGrayCode) n
checkIntegerGrayCode (NonNegative n) = checkInjection (Bimorphism (grayCode::Integer->[Bool]) fromGrayCode) n



checkPredReduce o pred x =
  toFunc pred x == (toFunc $ reducePred o pred) x