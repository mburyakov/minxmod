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

argSoftDrop ::  ArgIndex -> ArgTree a -> (ArgIndex, ArgTree a)
argSoftDrop l    t@(ArgArg arg) = (l, t)
argSoftDrop [i]    (ArgList list) = ([], ArgList $ drop' i list)
argSoftDrop (i:il) (ArgList list) = argSoftDrop il (list !! i)

argHead (ArgList list) = head list

(!!!) :: ArgTree a -> ArgIndex -> ArgTree a
tree !!! [] = tree
tree !!! i = argHead $ argDrop i tree

(!!!!) :: ArgTree a -> ArgIndex -> a
tree !!!! i = argArg $ tree !!! i


type ArgTemplate = ArgTree ()

argTemplate n = ArgList $ map ArgArg $ replicate n ()

data Predicate =
    PredTrue
  | PredFalse
  | PredArg   ArgIndex
  | PredNeg       (Predicate)
  | PredOr        (Predicate) (Predicate)
  | PredAnd       (Predicate) (Predicate)
  | PredPerm      (Permutation Bool) (Predicate)
  | PredAll   Int
  | PredAny   Int
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


data Permutation a =
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
toFunc (PredPerm p a)  x = toFunc a $ toPerm p x
toFunc (PredAll n) (ArgList l) = foldl (&&*) true  $ map argArg (take' n l)
toFunc (PredAny n) (ArgList l) = foldl (||*) false $ map argArg (take' n l)
toFunc (BDDv i a b) x = if x !!!! i then toFunc a x else toFunc b x
toFunc (BDDeq i1 i2 a b) x = if argDrop i1 x == argDrop i2 x then toFunc a x else toFunc b x
toFunc t1 t2 = error (show t1 ++ show t2)

toPerm :: Permutation a -> ArgTree a -> ArgTree a
toPerm (PermComp p1 p2) x =
  (toPerm p1).(toPerm p2) $ x
toPerm (PermPerm indices) x =
  case indices of
    (ArgArg  i ) -> argDrop i x
    (ArgList il) -> ArgList [ toPerm (PermPerm i) x | i <- il]

toIndexFunc :: Permutation a -> ArgIndex -> ArgIndex
toIndexFunc (PermComp p1 p2) x = 
  (toIndexFunc p2).(toIndexFunc p1) $ x
toIndexFunc (PermPerm indices) x =
  reverse rleft ++ [(e1+e2)] ++ rest
    where
      (e1:rest, ArgArg left) = argSoftDrop x indices
      (e2:rleft) = reverse left


data ArgOrd = ArgOrd {
  argCompare :: ArgIndex -> ArgIndex -> Ordering
}

reducePred :: ArgOrd -> Predicate -> Predicate
reducePred _ PredTrue = PredTrue
reducePred _ PredFalse = PredFalse
reducePred _ (PredArg i) = BDDv i PredTrue PredFalse
reducePred o (PredNeg (BDDv i a b)) = BDDv i (reducePred o (notB a)) (reducePred o (notB b))
reducePred _ (PredNeg PredTrue)  = PredFalse
reducePred _ (PredNeg PredFalse) = PredTrue
reducePred o (PredNeg x) = reducePred o $ PredNeg $ reducePred o x
reducePred o (PredOr t1@(BDDv i1 a1 b1) t2@(BDDv i2 a2 b2)) =
  case argCompare o i1 i2 of
    EQ -> BDDv i1 (reducePred o (a1||*a2)) (reducePred o (b1||*b2))
    LT -> BDDv i1 (reducePred o (a1||*t2)) (reducePred o (b1||*t2))
    GT -> BDDv i2 (reducePred o (a2||*t1)) (reducePred o (b2||*t1))
reducePred o (PredOr _ PredTrue) =
  PredTrue
reducePred o (PredOr PredTrue _) =
  PredTrue
reducePred o (PredOr t1 PredFalse) =
  reducePred o t1
reducePred o (PredOr PredFalse t2) =
  reducePred o t2
reducePred o (PredOr x y) =
  reducePred o $ PredOr (reducePred o x) (reducePred o y)
reducePred o (PredAnd t1@(BDDv i1 a1 b1) t2@(BDDv i2 a2 b2)) =
  case argCompare o i1 i2 of
    EQ -> BDDv i1 (reducePred o (a1&&*a2)) (reducePred o (b1&&*b2))
    LT -> BDDv i1 (reducePred o (a1&&*t2)) (reducePred o (b1&&*t2))
    GT -> BDDv i2 (reducePred o (a2&&*t1)) (reducePred o (b2&&*t1))
reducePred o (PredAnd _ PredFalse) =
  PredFalse
reducePred o (PredAnd PredFalse _) =
  PredFalse
reducePred o (PredAnd t1 PredTrue) =
  reducePred o t1
reducePred o (PredAnd PredTrue t2) =
  reducePred o t2
reducePred o (PredAnd x y) =
  reducePred o $ PredAnd (reducePred o x) (reducePred o y)
reducePred o (PredAny n) =
  reducePred' PredTrue o (PredAny n)
    where
      reducePred' _ _ (PredAny 0) =
        PredFalse
      reducePred' prTrue o (PredAny n) =
        BDDv [0] prTrue $ reducePred o (PredPerm (PermPerm $ ArgArg [1]) (reducePred' prTrue o $ PredAny (n-1)))      
reducePred o (PredAll n) =
  reducePred' PredFalse o (PredAll n)
    where
      reducePred' _ _ (PredAll 0) =
        PredTrue
      reducePred' prFalse o (PredAll n) =
        BDDv [0] (reducePred o (PredPerm (PermPerm $ ArgArg [1]) (reducePred' prFalse o $ PredAll (n-1)))) prFalse
reducePred o (PredPerm perm1 (PredPerm perm2 x)) =
 reducePred o (PredPerm (PermComp perm2 perm1) x)
reducePred o (PredPerm perm (BDDv i a b)) | case b of {PredFalse -> True; _ -> True} =
  BDDv (toIndexFunc perm i) (reducePred o $ PredPerm perm a) (reducePred o $ PredPerm perm b)
reducePred o (PredPerm perm PredTrue) =
  PredTrue
reducePred o (PredPerm perm PredFalse) =
  PredFalse
reducePred o (PredPerm perm x) =
  reducePred o (PredPerm perm $ reducePred o x)
reducePred _ x@(BDDv i a b) = x
reducePred _ x = error $ show x