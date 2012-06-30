{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DatatypeContexts #-}
--{-# LANGUAGE ScopedTypeVariables #-}
--{-# LANGUAGE ExplicitForAll #-}
--{-# LANGUAGE TypeSynonymInstances#-}

module SimpleHList where

class HList l
data HNil = HNil
instance HList HNil
data HList l => HCons e l = HCons e l
instance (HList l) => HList (HCons e l)

-- | show

class Show' a where
  show' :: a -> String
  
instance Show' (HNil) where
  show' HNil = "]"
instance (Show e, Show' l, HList l) => Show' (HCons e l) where
  show' (HCons elem tail) = "," ++ (show elem) ++ (show' tail)

instance Show (HNil) where
  show HNil = "[]"
instance (Show e, Show' l, HList l) => Show (HCons e l) where
  show (HCons elem tail) = "[" ++ (show elem) ++ (show' tail)

-- | hNil

hNil = HNil

-- | hCons

--hCons :: hList 
	
-- | hHead
	
hHead :: HList l => HCons e l -> e
hHead (HCons elem tail) = elem

-- | hTail

hTail :: HList l => HCons e l -> l
hTail (HCons elem tail) = tail

-- | hReverse

type family HReverse' l r :: *
type family HReverse l  :: *

type instance HReverse' (HNil) l2 = l2
type instance HReverse' (HCons e1 l1) l2 = HReverse' l1 (HCons e1 l2)

type instance HReverse (HNil) = HReverse' (HNil) (HNil)
type instance HReverse (HCons e l) = HReverse' (HCons e l) (HNil)

class HReversable a b where
  hReverse' :: a -> b -> HReverse' a b

instance (HReversable (HNil) l2) where
  hReverse' HNil list2 = list2

instance (HList l1, HList l2, HReversable l1 (HCons e1 l2)) => (HReversable (HCons e1 l1) l2) where
  hReverse' (HCons elem tail) accum =
    hReverse' tail (HCons elem accum)

hReverse list =
  hReverse' list HNil


-- | hConcat

hConcat l1 l2 = 
  hReverse' (hReverse l1) l2


-- | hMap

type family HMap' f l :: *

type instance HMap' (HNil) (HNil) = (HNil)
type instance HMap' (HCons (a->b) lf) (HCons a ll) = HCons b (HMap' lf ll)

class HMapable a b where
  hMap' :: a -> b -> HMap' a b
  
instance (HMapable (HNil) (HNil)) where
  hMap' HNil HNil = HNil::HNil

instance (HMapable l1 l2, HList l1, HList l2, HList (HMap' l1 l2)) => (HMapable (HCons (e1->e2) l1) (HCons e1 l2)) where
  hMap' (HCons fun ftail) (HCons arg atail) = 
    HCons (fun arg) $ hMap' ftail atail

-- | hLength

class HLengthable a where
  hLength :: a -> Int
  
instance HLengthable (HNil) where
  hLength HNil = 0
  
instance (HLengthable l, HList l) => HLengthable (HCons e l) where
  hLength (HCons elem list) = 1 + hLength list

type family HLength' l :: *

type instance HLength' (HNil) = HNil
type instance HLength' (HCons e l) = HCons () (HLength' l)

class HLengthable' a where
  hLength' :: a -> HLength' a
  
instance HLengthable' (HNil) where
  hLength' HNil = HNil
  
instance (HLengthable' l, HList l, HList (HLength' l)) => HLengthable' (HCons e l) where
  hLength' (HCons elem list) = HCons () (hLength' list)

-- | hTake

class HTakeable a b where
  hTake :: a -> b
  
instance HTakeable a (HNil) where
  hTake _ = HNil
  
instance (HList a, HList b, HTakeable a b) => HTakeable (HCons e a) (HCons e b) where
  hTake (HCons elem tail) = 
    HCons elem (hTake tail)

-- | hDrop

class HDropable a b c | a b -> c where
  hTakeDrop :: a -> (b, c)
  
instance HDropable a (HNil) a where
  hTakeDrop list = (HNil, list)
  
instance (HList a, HList b, HList c, HDropable a b c) => HDropable (HCons e a) (HCons e b) c where
  hTakeDrop (HCons elem tail) = 
    (HCons elem t, d)
      where
        (t, d) = (hTakeDrop tail)

{--test =
  (tk,dr)
    where
      dr = ((\(x,y) -> (y)) tkdr)
      tk = ((\(x,y) -> (x)) tkdr)::(HCons Bool HNil)
      full = tkdr::(HCons Bool HNil, HCons () HNil)
      tkdr = (hTakeDrop lst)
      lst = (HCons True $ HCons () HNil)
--}

{-- | hTake_ (do not use it)

type family HTake_' a b c :: *
type instance HTake_' l1 l2 HNil = l2
type instance HTake_' (HCons e1 l1) l2 (HCons e1 l3) = HTake_' l1 (HCons e1 l2) l3

class HTakeable_' a b c where
  hTake_' :: a -> b -> c -> HTake_' a b c

instance HTakeable_' l1 l2 HNil where
  hTake_' left right _ = right

instance (HTakeable_' l1 (HCons e1 l2) l4, HList l1, HList l2) => HTakeable_' (HCons e1 l1) l2 (HCons e1 l4) where
  hTake_' (HCons elem list1) list2 example =
    hTake_' list1 (HCons elem list2) (tmpfun example)
      where
        tmpfun :: HCons e l -> l
        tmpfun _ = undefined

hTakeRev_ template list =
  hTake_' list HNil (undefined `asTypeOf` hReverse template)
  
hTake_ template list = 
  hReverse $ hTake_' list HNil (undefined `asTypeOf` template)

hReverse list = hTake_' list HNil (undefined `asTypeOf` list)
--}
--hTakeRev list =
--  hTake' list HNil

--hTake list example = 
--  hReverse (hTake' list HNil example)
  
--lst = 
-- (HCons True $ HCons (1::Int) HNil)
--tmp = 
-- hTake lst (undefined :: HCons Bool (HCons Int HNil))

{--
type family HTake l r a :: *
type instance HTake l HNil a = HReverse a
type instance HTake l (HCons e r) (HCons e a) = HTake (HCons e l) r a
--}
--class HT l r h a
--instance HT l r (HTake l r a) a
--instance HT (HCons el l) r (HCons eh h) a => HT l (HCons el r) h a

{-class HTakeable l r a where
  hTake :: l -> r -> HTake l r a -> a

instance (HT l r (HTake l r r) r) => HTakeable l r r where
  hTake left right ex = right

instance (HTakeable l (HCons e r) a) => HTakeable (HCons e l) r a where
  hTake (HCons elem left) right ex = 
    hTake left (HCons elem right) (tmpfun ex)
      where
        tmpfun :: HCons e_ l_ -> l_
        tmpfun _ = undefined

instance (HTakeable' l1 (HCons e1 l2) l4) => HTakeable' (HCons e1 l1) l2 (HCons e1 l4) where
  hTake' (HCons elem list1) list2 example =
    hTake' list1 (HCons elem list2) (tmpfun example)
      where
--        (r, list4) = hTake' list1 (HCons elem list2)
        tmpfun :: HCons e l -> l
        tmpfun _ = undefined
-}
-- hTake__ :: (HTakeable' a d c) => a -> HTake' a HNil c --(HTake a HNil b)
{--hTake__ list = t
  where
    t = hTake' list HNil (undefined::HTake a HNil b)
-}
{-class HTakeable a c where
  hTake__ :: a -> c

instance HTakeable l1 l2 where
  hTake__ list = 
    hTake' list HNil (undefined::HTake l2 HNil)

--instance HTakeable l1 (HCons elem list) where
  hTakeRev list =
    hTake' list HNil
-}
--hTakeRev :: l1 -> l2 -> l2
--hTakeRev list example = r
--  where
--     (r, _) = (hTake' list HNil) `asTypeOf` (example, hReverse example)

--  hDrop' (HCons elem tail1) tail2 =
--    HCons elem tail2
--  hReverse' (HCons elem tail) accum =
--    hReverse' tail (HCons elem accum)


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
{--
dup1 :: (a0 -> a1) -> a0 -> a1
dup1 f x = f x

dup2 :: (a0 -> a1) -> (a1 -> a2) -> a0 -> a2
dup2 f0 f1 x = (f1.f0) x

dup2' f = dup2 hTail hTail
--}

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