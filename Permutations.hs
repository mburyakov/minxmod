{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}

module Permutations where

import ArgTree
import ArgOrd

import Data.Monoid
import Data.Typeable

class PermutationClass a where
  toPerm :: a -> ArgTree b -> ArgTree b
  toIndexFunc :: a -> ArgIndex -> ArgIndex

data Permutation = forall a . (PermutationClass a, Show a, Eq a, Typeable a) => Permutation a
instance PermutationClass Permutation where
  toPerm (Permutation p) = toPerm p
  toIndexFunc (Permutation p) = toIndexFunc p
instance Show Permutation where
  show (Permutation perm) = "(Permutation (" ++ show perm ++ ")"
instance Eq Permutation where
  (Permutation v1) == (Permutation v2) =
    mv2' /= Nothing && v1 == v2'
      where
        mv2' = cast v2
	Just v2' = mv2'

data PermPerm = PermPerm (ArgTree ArgIndex)
  deriving (Eq, Show, Typeable)
instance PermutationClass PermPerm where
  toPerm (PermPerm indices) x =
    case indices of
      (ArgArg  i ) -> argDrop i x
      (ArgList il) -> ArgList [ toPerm (PermPerm i) x | i <- il]
  toIndexFunc (PermPerm indices) x =
    reverse rleft ++ [(e1+e2)] ++ rest
      where
        (e1:rest, ArgArg left) = argSoftDrop x indices
        (e2:rleft) = reverse left

data PermComp = PermComp Permutation Permutation
  deriving (Eq, Show, Typeable)
instance PermutationClass PermComp where
  toPerm (PermComp p1 p2) x =
    (toPerm p1).(toPerm p2) $ x
  toIndexFunc (PermComp p1 p2) x = 
    (toIndexFunc p2).(toIndexFunc p1) $ x

instance Monoid Permutation where
  mempty = Permutation $ PermPerm (ArgArg [0])
  mappend p1 p2 = Permutation $ PermComp p1 p2


data OrdPerm = OrdPerm Permutation ArgOrd
  deriving (Eq, Show, Typeable)
instance ArgOrdClass OrdPerm where
  argCompare (OrdPerm perm ord) x y =
    argCompare ord (toIndexFunc perm x) (toIndexFunc perm y)

--should not use it
permOrd perm ord =
  ArgOrd $ OrdPerm perm ord
