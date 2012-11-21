{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}

module ArgOrd where

import Data.Typeable
import Data.Monoid
import Control.Monad
import ArgTree

class ArgOrdClass a where
  argCompare :: a -> ArgIndex -> ArgIndex -> Maybe Ordering



data ArgOrd = forall a . (ArgOrdClass a, Show a, Eq a, Typeable a) => ArgOrd a
instance ArgOrdClass ArgOrd where
  argCompare (ArgOrd o) = argCompare o
instance Show ArgOrd where
  show (ArgOrd a) = "(ArgOrd " ++ show (typeOf a) ++ " " ++ show a ++ ")"
instance Eq ArgOrd where
  (ArgOrd v1) == (ArgOrd v2) =
    mv2' /= Nothing && v1 == v2'
      where
        mv2' = cast v2
	Just v2' = mv2'
instance Monoid ArgOrd where
  mempty = ArgOrd OrdEmpty
  mappend a b = ArgOrd (OrdComp a b)

data OrdEmpty = OrdEmpty
  deriving (Show, Eq, Typeable)
instance ArgOrdClass OrdEmpty where
  argCompare OrdEmpty = const $ const $ Nothing


data OrdComp = OrdComp ArgOrd ArgOrd
  deriving (Show, Eq, Typeable)
instance ArgOrdClass OrdComp where
  argCompare (OrdComp a b) x y =
    argCompare a x y `mplus`
    argCompare b x y

