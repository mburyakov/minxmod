{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module SimpleHList where

--data HList e l = HNil_ HNil

class HList a
data HNil = HNil
instance HList HNil
data HCons e l = HCons e l
instance HList l => HList (HCons e l)

-- | show

class Show' a where
  show' :: a -> String
  
instance Show' HNil where
  show' HNil = "]"
instance (Show e, Show' l) => Show' (HCons e l) where
  show' (HCons elem tail) = "," ++ (show elem) ++ (show' tail)

instance Show HNil where
  show HNil = "[]"
instance (Show e, Show' l) => Show (HCons e l) where
  show (HCons elem tail) = "[" ++ (show elem) ++ (show' tail)
	
-- | hHead
	
hHead :: HList l => HCons e l -> e
hHead (HCons elem tail) = elem

-- | hTail

hTail :: HList l => HCons e l -> l
hTail (HCons elem tail) = tail

-- | hReverse

type family HReverse' l r :: *

type instance HReverse' HNil l2 = l2
type instance HReverse' (HCons e1 l1) l2 = HReverse' l1 (HCons e1 l2)

class HReversable a b where
  hReverse' :: a -> b -> HReverse' a b
  
instance (HReversable HNil l2) where
  hReverse' HNil list2 = list2

instance (HReversable l1 (HCons e1 l2)) => (HReversable (HCons e1 l1) l2)	 where
  hReverse' (HCons elem tail) accum =
    hReverse' tail (HCons elem accum)

hReverse list =
  hReverse' list HNil

--hReverse :: l1 -> l2  -> HReverse' l1 l2
--hReverse HNil accum =
--  accum
--hReverse (HCons elem tail) accum =
--  hReverse tail (HCons elem accum)

{--hReverseStep :: (HListable l1, HListable l2) =>  HList e1 l1 -> l2 -> (HList e1 l2)
hReverseStep left right = 
  hCons h right
    where
      h = hHead left
--}
{--hReverse :: (HListable l1, HListable l2) => l1 -> l2 -> l1
hReverse accum HNil =
  accum
hReverse accum (HCons elem tail) =
  hReverse (HCons elem accum) tail
  
  
--}
--hFoldl 

dup1 :: (a0 -> a1) -> a0 -> a1
dup1 f x = f x

dup2 :: (a0 -> a1) -> (a1 -> a2) -> a0 -> a2
dup2 f0 f1 x = (f1.f0) x

dup2' f = dup2 hTail hTail


{--data HPair e1 e2 l1 l2 = HPair (HList e1 l1) (HList e2 l2) deriving Show
instance HListable (HPair e1 e2 l1 l2)

applyStep :: HPair (e1->e2) e1 (HList d1 l1) (HList d2 l2) -> (HList e2 (HPair d1 d2 l1 l2))
applyStep (HPair left right) = 
  hCons (lh rh) (HPair lt rt)
    where
      lh = hHead left
      rh = hHead right
      lt = hTail left
      rt = hTail right
  
--}
{--hApply :: HList (e1->e2) l1 -> HList e1 l2 -> HList e2 l3

hApply left right =
  hCons (lh rh) (hApply lt rt)
    where
      lh = hHead left
      rh = hHead right
      lt = hTail left
      rt = hTail right
--}
--hAppend :: (HListable l1, HListable l2) => l1 -> l2 ->
--hAppend left right = 
--  if hEmpty left
--  then right
--  else hCons h a
--    where
--      h = hHead left
--      t = hTail left
--      a = hAppend t right

--hAppend (HNil) x = x
--hAppend (HCons elem tail) x = HCons elem (append tail x)