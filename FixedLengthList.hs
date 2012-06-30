{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FixedLengthList where

import SimpleHList
import IntegerSingletons

class FList a l

instance FList a HNil
instance FList a l => FList a (HCons a l)

-- | fMap

type family FMap f l :: *

type instance FMap f HNil = HNil
type instance FMap (a -> b) (HCons a l) = HCons b (FMap (a -> b) l)

class FMapable f l where
  fMap :: f -> l -> FMap f l
  
instance (FMapable (a->b) HNil) where
  fMap f HNil = HNil

instance (FMapable (a->b) l, HList l, FList a l, HList (FMap (a->b) l), FList b (FMap (a->b) l)) => (FMapable (a->b) (HCons a l)) where
  fMap f (HCons elem tail) = 
    HCons (f elem) $ fMap f tail

-- | fLength

type family FLength l :: *

type instance FLength (HNil) = Zero
type instance FLength (HCons e l) = Succ (FLength l)

fLength :: l -> FLength l
fLength list = undefined

{--class FLengthable a where
  fLength :: a -> FLength a
  
instance FLengthable (HNil) where
  fLength HNil = undefined::Zero
  
instance (FLengthable l, HList l, FList a l, HList (FLength l), FList a (FLength l)) => FLengthable (HCons e l) where
  fLength list = undefined :: FLength (HCons e l)
--}