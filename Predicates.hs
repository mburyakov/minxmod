{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Predicates where

import Data.Boolean
import ArgTree
import Debug.Trace

--trace' x = x
trace'' x y = y
trace' x = trace ("trace' :'" ++ show x ++ "' ++ \n") x
--trace'' x y = trace ("trace' :''" ++ show x ++ "' ++ \n") y
error' x = error $ show x

data Predicate =
    PredArg   ArgIndex
  | PredNeg       (Predicate)
  | PredOr        (Predicate) (Predicate)
  | PredPerm      (Permutation Bool) (Predicate)
  | PredAll   Int
  | PredAny   Int
  | PredExists ArgIndex Predicate
  | PredBDD   BDD
  deriving Show

data BDD =
    BDDTrue
  | BDDFalse
  | BDDv ArgIndex (BDD) (BDD)
  | BDDeq ArgIndex ArgIndex (BDD) (BDD)
  | BDDforceOrd ArgOrd BDD
  deriving Show

instance Boolean Predicate where
  true = PredBDD BDDTrue
  false = PredBDD BDDFalse
  notB = PredNeg
  (&&*) a b = notB (notB a ||* notB b)
  (||*) = PredOr

eq i j = PredBDD (BDDeq i j BDDTrue BDDFalse)
predExists n pred = 
  PredExists n pred
predForAll n pred = 
  notB (PredExists n $ notB pred)


type instance BooleanOf Predicate = Predicate

instance EqB Predicate where
  l ==* r = (l &&* r) ||* (notB l &&* notB r)

instance IfB Predicate where
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
  toFunc (PredPerm p a)  x = toFunc a $ toPerm p x
  toFunc (PredAll n) (ArgList l) = foldl (&&*) true  $ map argArg (take' n l)
  toFunc (PredAny n) (ArgList l) = foldl (||*) false $ map argArg (take' n l)
  --toFunc (PredExists 0 a) (ArgList l) =
  --  toFunc a (ArgList l)
  --toFunc (PredExists n a) (ArgList l) =
  --    toFunc rec (ArgList $ ArgArg True:l)
  -- || toFunc rec (ArgList $ ArgArg False:l)
  --    where
  --      rec = PredPerm (PermPerm $ ArgArg[-1]) $ PredExists (n-1) a
  toFunc t1 t2 = error (show t1 ++ show t2)

instance ToFuncable BDD where  
  toFunc (BDDv i a b) x = if x !!!! i then toFunc a x else toFunc b x
  toFunc (BDDeq i1 i2 a b) x = if argDrop i1 x == argDrop i2 x then toFunc a x else toFunc b x
  toFunc BDDTrue _ = True
  toFunc BDDFalse _ = False
  toFunc (BDDforceOrd _ b) x = toFunc b x


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
  ordShow :: String
}
instance Show ArgOrd where
  show ao = ordShow ao

permOrd :: Permutation Bool -> ArgOrd -> ArgOrd
permOrd perm ord =
  ArgOrd {    
    argCompare = \x y ->
      argCompare ord (toIndexFunc perm x) (toIndexFunc perm y),
    ordShow = "permOrd (" ++ show perm ++ ", " ++ show ord ++ ")"
  }

fixReduce o b = BDDforceOrd o $ reducePred o b

reducePred' o x = trace'' x $ reducePred o x
--reducePred' o x = reducePred o x

-- if using BDDv or BDDeq, variable order must correspond
reducePred :: ArgOrd -> Predicate -> BDD
reducePred _ (PredBDD x) = x
reducePred _ (PredArg i) = BDDv i BDDTrue BDDFalse
reducePred o (PredNeg (PredBDD(BDDv i a b))) = BDDv i (reducePred' o (notB $ PredBDD a)) (reducePred' o (notB $ PredBDD b))
reducePred _ (PredNeg (PredBDD BDDTrue))  = BDDFalse
reducePred _ (PredNeg (PredBDD BDDFalse)) = BDDTrue
reducePred _ (PredNeg (PredBDD (BDDforceOrd newo b))) = reducePred' newo (notB $ PredBDD b)
reducePred o (PredNeg (PredBDD(BDDeq i j a b))) = BDDeq i j (reducePred' o (notB $ PredBDD a)) (reducePred' o (notB $ PredBDD b))
reducePred o (PredNeg x) =
  reducePred' o $ PredNeg $ PredBDD $ reducePred' o x
reducePred o (PredOr t1@(PredBDD(BDDv i1 a1 b1)) t2@(PredBDD(BDDv i2 a2 b2))) =
   case argCompare o i1 i2 of
    EQ -> BDDv i1 (reducePred' o (PredBDD a1||*PredBDD a2)) (reducePred' o (PredBDD b1||*PredBDD b2))
    LT -> BDDv i1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2))
    GT -> BDDv i2 (reducePred' o (PredBDD a2||*t1)) (reducePred' o (PredBDD b2||*t1))
reducePred o (PredOr _ (PredBDD BDDTrue)) =
  BDDTrue
reducePred o (PredOr t1 (PredBDD BDDFalse)) =
  reducePred' o t1
reducePred o (PredOr t1@(PredBDD (BDDeq i1 j1 a1 b1)) t2@(PredBDD (BDDv i2 a2 b2))) =
  if
    (argCompare o i1 (passInto i2) == EQ || argCompare o j1 (passInto i2) == EQ)
  then
    reducePred' o (PredOr lhs' t2)
  else
   case trace' $ (argCompare o i1 i2, argCompare o j1 i2) of
    (EQ, _) ->
      reducePred' o (PredOr lhs t2)
    (_, EQ) ->
      reducePred' o (PredOr lhs t2)
    (GT, GT) ->
      BDDv i2 (reducePred' o (PredBDD a2||*t1)) (reducePred' o (PredBDD b2||*t1))
    (LT, LT) ->
      if
        (i1 `contains` i2) || (j1 `contains` i2)
      then
        reducePred' o (PredOr lhs t2)
      else
        case trace' $ (argCompare o (nipInfinity i1) i2, argCompare o (nipInfinity j1) i2) of
          (LT, LT) ->
            (BDDeq i1 j1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2)))
          (GT, GT) ->
            BDDeq i1 j1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2))
          _ -> error "Variable order does not correspond to BDDeq container"
    (LT, GT) -> reducePred' o (PredOr lhs t2)
    (GT, LT) -> reducePred' o (PredOr lhs t2)
  where
    lhs =
      trace ("ord = " ++ show o ++ " i1 = " ++ show i1 ++ " j1 = " ++ show j1 ++ " i2 = " ++ show i2) $ PredBDD $ BDDeq
        (passInto i1)
        (passInto j1)
        (BDDeq (nipOne i1) (nipOne j1) a1 b1)
        b1
    lhs' =
      case argCompare o i1 j1 of
        LT ->
          PredBDD $ BDDv (passOut i1)
            (BDDv (passOut j1)
              a1
              b1)
            (BDDv (passOut j1)
              b1
              a1)
        GT ->
          PredBDD $ BDDv (passOut j1)
            (BDDv (passOut i1)
              a1
              b1)
            (BDDv (passOut i1)
              b1
              a1)
reducePred _ (PredOr x (PredBDD (BDDforceOrd newo y))) =
  reducePred' newo (PredOr x (PredBDD y))
reducePred o (PredOr (PredBDD (BDDeq i1 j1 a1 b1)) (PredBDD (BDDeq i2 j2 a2 b2))) =
  undefined
reducePred o (PredOr x y) =
  reducePred' o $ PredOr (PredBDD (reducePred' o y)) (PredBDD (reducePred' o x))
reducePred o (PredAny n) =
  reducePred'' BDDTrue o (PredAny n)
    where
      reducePred'' _ _ (PredAny 0) =
        BDDFalse
      reducePred'' prTrue o (PredAny n) =
        BDDv [0] prTrue $ reducePred' o (PredPerm (PermPerm $ ArgArg [1]) (PredBDD $ reducePred'' prTrue o $ PredAny (n-1)))      
reducePred o (PredAll n) =
  reducePred'' BDDFalse o (PredAll n)
    where
      reducePred'' _ _ (PredAll 0) =
        BDDTrue
      reducePred'' prFalse o (PredAll n) =
        BDDv [0] (reducePred' o (PredPerm (PermPerm $ ArgArg [1]) (PredBDD $ reducePred'' prFalse o $ PredAll (n-1)))) prFalse
reducePred o (PredPerm perm1 (PredPerm perm2 x)) =
  reducePred' o (PredPerm (PermComp perm2 perm1) (PredBDD $ reducePred' (permOrd (PermComp perm2 perm1) o) x))
reducePred o (PredPerm perm (PredBDD (BDDv i a b))) =
  BDDv (toIndexFunc perm i) (reducePred' o $ PredPerm perm (PredBDD a)) (reducePred' o $ PredPerm perm (PredBDD b))
reducePred o (PredPerm perm (PredBDD (BDDeq i j a b))) =
  BDDeq (toIndexFunc perm i) (toIndexFunc perm j) (reducePred' o $ PredPerm perm (PredBDD a)) (reducePred' o $ PredPerm perm (PredBDD b))
reducePred o (PredPerm perm (PredBDD BDDTrue)) =
  BDDTrue
reducePred o (PredPerm perm (PredBDD BDDFalse)) =
  BDDFalse
reducePred o (PredPerm perm (PredBDD (BDDforceOrd newo x))) =
  reducePred' newo (PredPerm perm (PredBDD x))
reducePred o (PredPerm perm x) =
  reducePred' o (PredPerm perm (PredBDD $ reducePred' (permOrd perm o) x))
reducePred o x@(PredExists t (PredBDD bdd@(BDDv i a b))) =
  if
    t `containsVar` i
  then
    reducePred' o (PredOr (PredExists t (PredBDD a)) (PredExists t (PredBDD b)))
  else
    reducePred' o (PredBDD (BDDv i (reducePred o $ PredExists t (PredBDD a)) (reducePred o $ PredExists t (PredBDD b))))
reducePred o x@(PredExists t (PredBDD bdd@(BDDeq i j a b))) =
  if
    t `containsVar` i || t `containsVar` j
  then
    reducePred' o (PredOr (PredExists t (PredBDD a)) (PredExists t (PredBDD b)))
  else
    if 
      i `containsVar` t || j `containsVar` t
    then
      undefined
    else
      reducePred' o (PredBDD (BDDeq i j (reducePred o $ PredExists t (PredBDD a)) (reducePred o $ PredExists t (PredBDD b))))
reducePred o (PredExists t (PredBDD BDDTrue)) =
  BDDTrue
reducePred o (PredExists t (PredBDD BDDFalse)) =
  BDDFalse
reducePred o x@(PredExists t a) =
  reducePred' o (PredExists t $ PredBDD $ reducePred' o a)
--reducePred _ x = error $ show x