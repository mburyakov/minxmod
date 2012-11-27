{-# LANGUAGE DeriveDataTypeable #-}

module Permutations where

import ArgTree
import ArgOrd

import Data.Monoid
import Data.Typeable

data Permutation =
    PermComp Permutation Permutation  
  | PermPerm (ArgTree ArgIndex)
  deriving (Show, Eq)

instance Monoid Permutation where
  mempty = PermPerm (ArgArg [0])
  mappend p1 p2 = PermComp p1 p2


toPerm :: Permutation -> ArgTree a -> ArgTree a
toPerm (PermComp p1 p2) x =
  (toPerm p1).(toPerm p2) $ x
toPerm (PermPerm indices) x =
  case indices of
    (ArgArg  i ) -> argDrop i x
    (ArgList il) -> ArgList [ toPerm (PermPerm i) x | i <- il]

toIndexFunc :: Permutation -> ArgIndex -> ArgIndex
toIndexFunc (PermComp p1 p2) x = 
  (toIndexFunc p2).(toIndexFunc p1) $ x
toIndexFunc (PermPerm indices) x =
  reverse rleft ++ [(e1+e2)] ++ rest
    where
      (e1:rest, ArgArg left) = argSoftDrop x indices
      (e2:rleft) = reverse left


data OrdPerm = OrdPerm Permutation ArgOrd
  deriving (Eq, Show, Typeable)
instance ArgOrdClass OrdPerm where
  argCompare (OrdPerm perm ord) x y =
    argCompare ord (toIndexFunc perm x) (toIndexFunc perm y)

--should not use it
permOrd perm ord =
  ArgOrd $ OrdPerm perm ord
