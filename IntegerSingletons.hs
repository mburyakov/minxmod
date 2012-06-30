{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ScopedTypeVariables #-}

module IntegerSingletons where

type family Add a b :: *

data Zero
data Succ a

type instance Add a Zero     = a
type instance Add a (Succ b) = Succ (Add a b)

class Nat a where
  toInt :: a -> Int
  
instance Nat Zero where
  toInt = const 0
  
instance Nat a => Nat (Succ a) where
  toInt x = 1 + toInt (undefined :: a)