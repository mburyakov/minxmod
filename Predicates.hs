{-# LANGUAGE MultiParamTypeClasses #-}

module Predicates where

import Data.Boolean
import ArgTree
import Debug.Trace

data Predicate =
--    PredTrue
--  | PredFalse
    PredArg   ArgIndex
  | PredNeg       (Predicate)
  | PredOr        (Predicate) (Predicate)
--  | PredAnd       (Predicate) (Predicate)
  | PredPerm      (Permutation Bool) (Predicate)
  | PredAll   Int
  | PredAny   Int
  | PredBDD   BDD
  deriving (Show, Eq)

data BDD =
    BDDTrue
  | BDDFalse
  | BDDv ArgIndex (BDD) (BDD)
  | BDDeq ArgIndex ArgIndex (BDD) (BDD)
  | BDDPerm (Permutation Bool) (BDD)
  deriving (Show, Eq)
  
instance Boolean Predicate where
  true = PredBDD BDDTrue
  false = PredBDD BDDFalse
  notB = PredNeg
  (&&*) a b = notB (notB a ||* notB b)
  (||*) = PredOr
  
instance EqB Predicate Predicate where
  l ==* r = (l &&* r) ||* (notB l &&* notB r)

instance IfB Predicate Predicate where
  ifB c l r = (c &&* l) ||* (notB c &&* r)


data Permutation a =
    PermComp (Permutation a) (Permutation a)   
  | PermPerm (ArgTree ArgIndex)
  deriving (Show, Eq)

class ToFuncable p where
  toFunc :: p -> ArgTree Bool -> Bool
  
instance ToFuncable Predicate where  
  toFunc (PredBDD f)     x = toFunc f x
  toFunc (PredArg i)     x = x !!!! i
  toFunc (PredNeg a)     x = notB $ toFunc a x
  toFunc (PredOr a b)    x = (toFunc a x) ||* (toFunc b x)
  --toFunc (PredAnd a b)   x = (toFunc a x) &&* (toFunc b x)
  toFunc (PredPerm p a)  x = toFunc a $ toPerm p x
  toFunc (PredAll n) (ArgList l) = foldl (&&*) true  $ map argArg (take' n l)
  toFunc (PredAny n) (ArgList l) = foldl (||*) false $ map argArg (take' n l)
  toFunc t1 t2 = error (show t1 ++ show t2)

instance ToFuncable BDD where  
  toFunc (BDDv i a b) x = if x !!!! i then toFunc a x else toFunc b x
  toFunc (BDDeq i1 i2 a b) x = if argDrop i1 x == argDrop i2 x then toFunc a x else toFunc b x
  toFunc BDDTrue _ = True
  toFunc BDDFalse _ = False
  
  
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
  argCompare :: ArgIndex -> ArgIndex -> Ordering,
  show' :: String
}
instance Show ArgOrd where
  show ao = show' ao

permOrd :: Permutation Bool -> ArgOrd -> ArgOrd
permOrd perm ord =
  ArgOrd {
    show' = "permOrd",
    argCompare = \x y ->
      {--trace ("permOrd " ++ show (toIndexFunc perm x)) --}argCompare ord (toIndexFunc perm x) (toIndexFunc perm y)
  }

-- if using BDDv or BDDeq, variable order must correspond
reducePred :: ArgOrd -> Predicate -> BDD
--reducePred o x | trace ("reducePred " ++ show o ++ "\n      " ++ show x) False = undefined
reducePred _ (PredBDD x)  = x
--reducePred _ (PredBDD BDDTrue)  = BDDTrue
--reducePred _ (PredBDD BDDFalse) = BDDFalse
reducePred _ (PredArg i) = BDDv i BDDTrue BDDFalse
reducePred o (PredNeg (PredBDD(BDDv i a b))) = BDDv i (reducePred o (notB $ PredBDD a)) (reducePred o (notB $ PredBDD b))
reducePred _ (PredNeg (PredBDD BDDTrue))  = BDDFalse
reducePred _ (PredNeg (PredBDD BDDFalse)) = BDDTrue
reducePred o (PredNeg (PredBDD(BDDeq i j a b))) = BDDeq i j (reducePred o (notB $ PredBDD a)) (reducePred o (notB $ PredBDD b))
--reducePred o (PredNeg (PredPerm perm x)) = (PredPerm perm $ reducePred o (PredNeg x))
reducePred o (PredNeg x) =
  --error $ show x
  reducePred o $ PredNeg $ PredBDD $ reducePred o x
reducePred o (PredOr t1@(PredBDD(BDDv i1 a1 b1)) t2@(PredBDD(BDDv i2 a2 b2))) =
 {--trace (show $ argCompare o i1 i2) a where
  a = --}
   case argCompare o i1 i2 of
    EQ -> BDDv i1 (reducePred o (PredBDD a1||*PredBDD a2)) (reducePred o (PredBDD b1||*PredBDD b2))
    LT -> BDDv i1 (reducePred o (PredBDD a1||*t2)) (reducePred o (PredBDD b1||*t2))
    GT -> BDDv i2 (reducePred o (PredBDD a2||*t1)) (reducePred o (PredBDD b2||*t1))
reducePred o (PredOr _ (PredBDD BDDTrue)) =
  BDDTrue
reducePred o (PredOr (PredBDD BDDTrue) _) =
  BDDTrue
reducePred o (PredOr t1 (PredBDD BDDFalse)) =
  reducePred o t1
reducePred o (PredOr (PredBDD BDDFalse) t2) =
  reducePred o t2
reducePred o (PredOr t1@(PredBDD (BDDeq i1 j1 a1 b1)) t2@(PredBDD (BDDv i2 a2 b2))) =
  case (argCompare o i1 i2, argCompare o j1 i2) of
    (EQ, _) ->
      reducePred o (PredOr lhs t2)
    (_, EQ) ->
      reducePred o (PredOr lhs t2)
    (GT, GT) ->
      BDDv i2 (reducePred o (PredBDD a2||*t1)) (reducePred o (PredBDD b2||*t1))
    (LT, LT) ->
      if
        (i1 `contains` i2) || (j1 `contains` i2)
      then
        reducePred o (PredOr lhs t2)
      else
        case (argCompare o (nipInfinity i1) i2, argCompare o (nipInfinity j1) i2) of
          (LT, LT) ->
            (BDDeq i1 j1 (reducePred o (PredBDD a1||*t2)) (reducePred o (PredBDD b1||*t2)))
          (GT, GT) ->
            reducePred o (PredOr lhs t2)
          _ -> error "Variable order does not correspond to BDDeq container"
    (LT, GT) -> reducePred o (PredOr lhs t2)
    (GT, LT) -> reducePred o (PredOr lhs t2)    
  where
    lhs = case (argCompare o i1 j1) of
            LT ->
			  PredBDD $ BDDv (passInto i1)
                (BDDv (passInto j1)
                  (BDDeq (nipOne i1) (nipOne j1) a1 b1)
                  b1)
                (BDDv (passInto j1)
                  a1
                  (BDDeq (nipOne i1) (nipOne j1) b1 a1))
            GT ->
			  PredBDD $ BDDv (passInto j1)
                (BDDv (passInto i1)
                  (BDDeq (nipOne j1) (nipOne i1) a1 b1)
                  b1)
                (BDDv (passInto i1)
                  a1
                  (BDDeq (nipOne j1) (nipOne i1) b1 a1))
reducePred o (PredOr (PredBDD (BDDv i2 a2 b2)) (PredBDD (BDDeq i1 j1 a1 b1))) =
  reducePred o (PredOr (PredBDD (BDDeq i1 j1 a1 b1)) (PredBDD (BDDv i2 a2 b2)))
reducePred o (PredOr x y) =
  reducePred o $ PredOr (PredBDD (reducePred o x)) (PredBDD (reducePred o y))
{--reducePred o (PredAnd t1@(BDDv i1 a1 b1) t2@(BDDv i2 a2 b2)) =
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
  reducePred o $ PredAnd (reducePred o x) (reducePred o y)--}
reducePred o (PredAny n) =
  reducePred' BDDTrue o (PredAny n)
    where
      reducePred' _ _ (PredAny 0) =
        BDDFalse
      reducePred' prTrue o (PredAny n) =
        BDDv [0] prTrue $ reducePred o (PredPerm (PermPerm $ ArgArg [1]) (PredBDD $ reducePred' prTrue o $ PredAny (n-1)))      
reducePred o (PredAll n) =
  reducePred' BDDFalse o (PredAll n)
    where
      reducePred' _ _ (PredAll 0) =
        BDDTrue
      reducePred' prFalse o (PredAll n) =
        BDDv [0] (reducePred o (PredPerm (PermPerm $ ArgArg [1]) (PredBDD $ reducePred' prFalse o $ PredAll (n-1)))) prFalse
reducePred o (PredPerm perm1 (PredPerm perm2 x)) =
  reducePred o (PredPerm (PermComp perm2 perm1) (PredBDD $ reducePred (permOrd (PermComp perm2 perm1) o) x))
reducePred o (PredPerm perm (PredBDD (BDDv i a b))) =
  {--(trace ("a="++show a++" ")) --}BDDv (toIndexFunc perm i) (reducePred o $ PredPerm perm (PredBDD a)) (reducePred o $ PredPerm perm (PredBDD b))
reducePred o (PredPerm perm (PredBDD (BDDeq i j a b))) =
  BDDeq (toIndexFunc perm i) (toIndexFunc perm j) (reducePred o $ PredPerm perm (PredBDD a)) (reducePred o $ PredPerm perm (PredBDD b))
reducePred o (PredPerm perm (PredBDD BDDTrue)) =
  BDDTrue
reducePred o (PredPerm perm (PredBDD BDDFalse)) =
  BDDFalse
--reducePred o (PredPerm perm x) =
--  reducePred o (PredPerm perm $ reducePred o x)
reducePred o (PredPerm perm x) = 
  --BDDPerm perm $ reducePred o x
  reducePred o (PredPerm perm (PredBDD $ reducePred (permOrd perm o) x))
--reducePred _ x@(BDDv i a b) = x
--reducePred _ x@(BDDeq i j a b) = x
--reducePred o x@(BDDeq i j a b) = BDDv (i++[0])
--                                 (BDDv (j++[0])
--                                   (PredPerm (PermPerm $ ArgList [ArgArg [0,1],ArgArg [1,1]]) x) b)
--                                   b
--reducePred _ x = error $ show x