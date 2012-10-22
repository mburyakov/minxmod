{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module ArgTree where 

data ArgTree a = ArgArg { argArg :: a } | ArgList { argList :: [ArgTree a] } deriving Eq

instance Functor ArgTree where
  fmap f (ArgArg e)  = ArgArg  $ f e
  fmap f (ArgList l) = ArgList $ map (fmap f) l

argFlatten :: ArgTree (ArgTree v) -> ArgTree v
argFlatten (ArgArg e) =
  e
argFlatten (ArgList l) =
  ArgList $ map argFlatten l  
  
instance Show a => Show (ArgTree a) where
  show (ArgArg  b) = show b
  show (ArgList l) = show l

class Binarizable v where
  toArgList :: v -> ArgTree Bool
  
--instance Binarizable [Char] where
--  toArgList l = ArgList $ map (ArgArg.(\x -> case x of '0' -> False; '1' -> True)) l
instance Binarizable Bool where
  toArgList b = ArgArg b
--instance Binarizable (ArgTree Bool) where
--  toArgList l = l
--instance Binarizable [Integer] where
--  toArgList l = ArgList $ map (ArgArg.(\x -> case x of 0 -> False; 1 -> True)) l
--instance Binarizable [Int] where
--  toArgList l = ArgList $ map (ArgArg.(\x -> case x of 0 -> False; 1 -> True)) l
instance Binarizable v => Binarizable [v] where
  toArgList l = ArgList $ map toArgList l
instance Binarizable v => Binarizable (ArgTree v) where
  toArgList l = argFlatten $ fmap toArgList l

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

nipOne :: ArgIndex -> ArgIndex
nipOne list =
  reverse $ (1 + head rev):(tail rev)
    where
      rev = reverse list

nipN :: Int -> ArgIndex -> ArgIndex
nipN n list =
  reverse $ (n + head rev):(tail rev)
    where
      rev = reverse list

nipInfinity :: ArgIndex -> ArgIndex
nipInfinity list =
  reverse $ (maxBound `asTypeOf` head rev):(tail rev)
    where
      rev = reverse list
      
passInto :: ArgIndex -> ArgIndex
passInto list = 
  list ++ [0]

passOut :: ArgIndex -> ArgIndex
passOut list = 
  reverse (tail (reverse list))
  
contains :: ArgIndex -> ArgIndex -> Bool
infix 7 `contains`
b `contains` a =
  ta == tb && hb < ha
    where
      ta = tail $ reverse a
      tb = tail $ reverse b
      ha = head $ reverse a
      hb = head $ reverse b
  
type ArgTemplate = ArgTree ()

argTemplate n = ArgList $ map ArgArg $ replicate n ()
