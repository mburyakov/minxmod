{-# LANGUAGE MultiParamTypeClasses #-}

module Predicates where

import Data.Boolean

data ArgTree a = ArgArg { argArg :: a } | ArgList { argList :: [ArgTree a] } deriving Eq

instance Functor ArgTree where
  fmap f (ArgArg e)  = ArgArg  $ f e
  fmap f (ArgList l) = ArgList $ map (fmap f) l

instance Show a => Show (ArgTree a) where
  show (ArgArg  b) = show b
  show (ArgList l) = show l

class ArgListable l where
  toArgList :: [l] -> ArgTree Bool
  
instance ArgListable Char where
  toArgList l = ArgList $ map (ArgArg.(\x -> case x of '0' -> False; '1' -> True)) l
instance ArgListable Bool where
  toArgList l = ArgList $ map ArgArg l
instance ArgListable Integer where
  toArgList l = ArgList $ map (ArgArg.(\x -> case x of 0 -> False; 1 -> True)) l
instance ArgListable Int where
  toArgList l = ArgList $ map (ArgArg.(\x -> case x of 0 -> False; 1 -> True)) l


type ArgIndex = [Int]


drop' n x | length x >= n = drop n x
take' n x | length x >= n = take n x

argDrop ::  ArgIndex -> ArgTree a -> ArgTree a
argDrop [0]    t@(ArgArg arg) = t
argDrop [i]    (ArgList list) = ArgList $ drop' i list
argDrop (i:il) (ArgList list) = argDrop il (list !! i)

argHead (ArgList list) = head list

(!!!) :: ArgTree a -> ArgIndex -> ArgTree a
tree !!! [] = tree
tree !!! i = argHead $ argDrop i tree

(!!!!) :: ArgTree a -> ArgIndex -> a
tree !!!! i = argArg $ tree !!! i


data Predicate =
    PredTrue
  | PredFalse
  | PredArg   ArgIndex
  | PredNeg       (Predicate)
  | PredOr        (Predicate) (Predicate)
  | PredAnd       (Predicate) (Predicate)
--  | PredImpl      (Predicate) (Predicate)
--  | PredEquiv     (Predicate) (Predicate)
--  | PredXor       (Predicate) (Predicate)
--  | PredIf        (Predicate) (Predicate) (Predicate)
  | PredPerm      (Permutation Bool) (Predicate)
  | PredAll   Int
  | PredAny   Int
--  | PredSat [ArgIndex] (Predicate)
  | BDDv ArgIndex (Predicate) (Predicate)
  | BDDeq ArgIndex ArgIndex (Predicate) (Predicate)
  deriving (Show)

instance Boolean Predicate where
  true = PredTrue
  false = PredFalse
  notB = PredNeg
  (&&*) = PredAnd
  (||*) = PredOr

instance EqB Predicate Predicate where
  l ==* r = (l &&* r) ||* (notB l &&* notB r)

instance IfB Predicate Predicate where
  ifB c l r = (c &&* l) ||* (notB c &&* r)

--predArg = PredArg
--predAll = PredAll
--predAny = PredAny
--predPerm = PredPerm
--predIf c l r =
--  (c &&* l) ||* (notB c &&* r)  
--predEquiv l r =
--  (l &&* r) ||* (notB l &&* notB r)
--predXor :: Predicate -> Predicate -> Predicate
--predXor =
--  notB predEquiv


data Permutation a =
--  PermId
    PermComp (Permutation a) (Permutation a)   
  | PermPerm (ArgTree ArgIndex)
  deriving (Show)

toFunc :: Predicate -> ArgTree Bool -> Bool
toFunc PredTrue        x = true
toFunc PredFalse       x = false
toFunc (PredArg i)     x = x !!!! i
toFunc (PredNeg a)     x = notB $ toFunc a x
toFunc (PredOr a b)    x = (toFunc a x) ||* (toFunc b x)
toFunc (PredAnd a b)   x = (toFunc a x) &&* (toFunc b x)
--toFunc (PredImpl a b)  x = toFunc (PredOr (PredNeg a) b) x
--toFunc (PredEquiv a b) x = toFunc (PredOr (PredAnd a b) (PredAnd (PredNeg a) (PredNeg b))) x
--toFunc (PredXor a b)   x = notB $ toFunc (PredEquiv a b) x
--toFunc (PredIf a b c)  x = if toFunc a x then toFunc b x else toFunc c x
toFunc (PredPerm p a)  x = toFunc a $ toPerm p x
toFunc (PredAll n) (ArgList l) = foldl (&&*) true  $ map argArg (take' n l)
toFunc (PredAny n) (ArgList l) = foldl (||*) false $ map argArg (take' n l)
toFunc (BDDv i a b) x = if x !!!! i then toFunc a x else toFunc b x
toFunc (BDDeq i1 i2 a b) x = if argDrop i1 x == argDrop i2 x then toFunc a x else toFunc b x
toFunc t1 t2 = error (show t1 ++ show t2)

toPerm :: Permutation a -> ArgTree a -> ArgTree a
--toPerm PermId x        = id x
toPerm (PermComp p1 p2) x =
  (toPerm p1).(toPerm p2) $ x
toPerm (PermPerm indices) x =
  case indices of
    (ArgArg  i ) -> argDrop i x
    (ArgList il) -> ArgList [ toPerm (PermPerm i) x | i <- il]

data ArgOrd = ArgOrd {
  argCompare :: ArgIndex -> ArgIndex -> Ordering
}

reducePred :: ArgOrd -> Predicate -> Predicate
reducePred _ PredTrue = PredTrue
reducePred _ PredFalse = PredFalse
reducePred _ (PredArg i) = BDDv i PredTrue PredFalse
reducePred _ (PredNeg (BDDv i a b)) = BDDv i b a
reducePred o (PredOr t1@(BDDv i1 a1 b1) t2@(BDDv i2 a2 b2)) =
  case argCompare o i1 i2 of
    EQ -> BDDv i1 (reducePred o (a1||*a2)) (reducePred o (b1||*b2))
    LT -> BDDv i1 (reducePred o (a1||*t2)) (reducePred o (b1||*t2))
    GT -> BDDv i2 (reducePred o (a2||*t1)) (reducePred o (b2||*t1))