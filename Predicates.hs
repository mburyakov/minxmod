{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE DeriveDataTypeable #-}

module Predicates where

import DebugStub
import qualified Debug1

import ArgTree
import ArgOrd
import Permutations

import Data.Boolean
import Data.Monoid
import Data.Typeable

data Predicate =
    PredArg   ArgIndex
  | PredNeg       (Predicate)
  | PredOr        (Predicate) (Predicate)
  | PredPerm      Permutation (Predicate)
  | PredAll   Int
  | PredAny   Int
  | PredExists ArgIndex Predicate
  | PredBDD   BDD
  deriving Show

data ForceOrdUsage = Comp | Step deriving (Eq, Show)

data BDD =
    BDDTrue
  | BDDFalse
  | BDDv ArgIndex (BDD) (BDD)
  | BDDeq ArgIndex ArgIndex (BDD) (BDD)
  | BDDforceOrd ForceOrdUsage ArgOrd BDD
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

toBool BDDTrue  = Just True
toBool BDDFalse = Just False
toBool (BDDforceOrd _ _ a) = toBool a
toBool _ = Nothing

type instance BooleanOf Predicate = Predicate

instance EqB Predicate where
  l ==* r = (l &&* r) ||* (notB l &&* notB r)

instance IfB Predicate where
  ifB c l r = (c &&* l) ||* (notB c &&* r)

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
  toFunc (BDDforceOrd _ _ b) x = toFunc b x


fixReduce o b = BDDforceOrd Comp o $ reducePred o b

processForces :: (ForceOrdUsage -> Maybe ForceOrdUsage) -> BDD -> BDD
processForces f (BDDforceOrd t ord bdd) =
  case f t of
    Just newf -> BDDforceOrd newf ord bdd
    Nothing   -> bdd
processForces f BDDTrue =
  BDDTrue
processForces f BDDFalse =
  BDDFalse
processForces f (BDDv i a b) =
  BDDv i (processForces f a) (processForces f b)
processForces f (BDDeq i j a b) =
  BDDeq i j (processForces f a) (processForces f b)

processBDDv :: Permutation -> BDD -> BDD
processBDDv f (BDDforceOrd t ord bdd) =
  BDDforceOrd t ord (processBDDv f bdd)
processBDDv f BDDTrue =
  BDDTrue
processBDDv f BDDFalse =
  BDDFalse
processBDDv f (BDDv i a b) =
  BDDv (toIndexFunc f i) (processBDDv f a) (processBDDv f b)
processBDDv f (BDDeq i j a b) =
  BDDeq i j (processBDDv f a) (processBDDv f b)

reducePred' o x = trace'' x $ reducePred o x
--reducePred' o x = reducePred o x

-- if using BDDv or BDDeq, variable order must correspond
reducePred :: ArgOrd -> Predicate -> BDD
reducePred _ (PredBDD x) = x
reducePred _ (PredArg i) = BDDv i BDDTrue BDDFalse
reducePred o (PredNeg (PredBDD(BDDv i a b))) = BDDv i (reducePred' o (notB $ PredBDD a)) (reducePred' o (notB $ PredBDD b))
reducePred _ (PredNeg (PredBDD BDDTrue))  = BDDFalse
reducePred _ (PredNeg (PredBDD BDDFalse)) = BDDTrue
reducePred o (PredNeg (PredBDD (BDDforceOrd t newo b))) =
  BDDforceOrd t newo $ reducePred' reso (PredNeg $ PredBDD b)
    where
      reso = newo <> o
reducePred o (PredNeg (PredBDD(BDDeq i j a b))) = BDDeq i j (reducePred' o (notB $ PredBDD a)) (reducePred' o (notB $ PredBDD b))
reducePred o (PredNeg x) =
  reducePred' o $ PredNeg $ PredBDD $ reducePred' o x
reducePred o (PredOr t1@(PredBDD(BDDv i1 a1 b1)) t2@(PredBDD(BDDv i2 a2 b2))) =
  case argCompare o i1 i2 of
    Just EQ -> BDDv i1 (reducePred' o (PredBDD a1||*PredBDD a2)) (reducePred' o (PredBDD b1||*PredBDD b2))
    Just LT -> BDDv i1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2))
    Just GT -> BDDv i2 (reducePred' o (PredBDD a2||*t1)) (reducePred' o (PredBDD b2||*t1))
reducePred o (PredOr _ (PredBDD BDDTrue)) =
  BDDTrue
reducePred o (PredOr t1 (PredBDD BDDFalse)) =
  reducePred' o t1
reducePred o (PredOr t1@(PredBDD (BDDeq i1 j1 a1 b1)) t2@(PredBDD (BDDv i2 a2 b2))) =
  if
    (argCompare o i1 (passInto i2) == Just EQ || argCompare o j1 (passInto i2) == Just EQ)
  then
    reducePred' o (PredOr lhs' t2)
  else
   case trace' $ (argCompare o i1 i2, argCompare o j1 i2) of
    (Just EQ, _) ->
      reducePred' o (PredOr lhs t2)
    (_, Just EQ) ->
      reducePred' o (PredOr lhs t2)
    (Just GT, Just GT) ->
      BDDv i2 (reducePred' o (PredBDD a2||*t1)) (reducePred' o (PredBDD b2||*t1))
    (Just LT, Just LT) ->
      if
        (i1 `contains` i2) || (j1 `contains` i2)
      then
        reducePred' o (PredOr lhs t2)
      else
        case trace' $ (argCompare o (nipInfinity i1) i2, argCompare o (nipInfinity j1) i2) of
          (Just LT, Just LT) ->
            (BDDeq i1 j1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2)))
          (Just GT, Just GT) ->
            BDDeq i1 j1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2))
          _ -> error "Variable order does not correspond to BDDeq container"
    (Just LT, Just GT) -> reducePred' o (PredOr lhs t2)
    (Just GT, Just LT) -> reducePred' o (PredOr lhs t2)
  where
    lhs =
      trace'' ("ord = " ++ show o ++ " i1 = " ++ show i1 ++ " j1 = " ++ show j1 ++ " i2 = " ++ show i2) $ PredBDD $ BDDeq
        (passInto i1)
        (passInto j1)
        (BDDeq (nipOne i1) (nipOne j1) a1 b1)
        b1
    lhs' =
      case argCompare o i1 j1 of
        Just LT ->
          PredBDD $ BDDv (passOut i1)
            (BDDv (passOut j1)
              a1
              b1)
            (BDDv (passOut j1)
              b1
              a1)
        Just GT ->
          PredBDD $ BDDv (passOut j1)
            (BDDv (passOut i1)
              a1
              b1)
            (BDDv (passOut i1)
              b1
              a1)
reducePred o (PredOr t1@(PredBDD (BDDeq i1 j1 a1 b1)) t2@(PredBDD (BDDeq i2 j2 a2 b2))) =
  case (argCompare o i1 i2, argCompare o j1 j2) of
    (Just LT, Just LT) ->
      BDDeq i1 j1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2))
    (Just GT, Just GT) ->
      BDDeq i2 j2 (reducePred' o (PredBDD a2||*t1)) (reducePred' o (PredBDD b2||*t1))
    _ -> error "Different BDDeq should not overlap"
reducePred o (PredOr t1@(PredBDD(BDDv i1 a1 b1)) t2@(PredBDD (BDDforceOrd Comp newo (BDDv i2 a2 b2)))) =
  case argCompare reso i1 i2 of
    Just LT -> BDDv i1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2))
    _ -> error "Invalid BDDforceOrd usage 1"
    where
      reso = newo <> o
reducePred o (PredOr t1@(PredBDD (BDDeq i1 j1 a1 b1)) t2@(PredBDD (BDDforceOrd Comp newo (BDDv i2 a2 b2)))) =
  if
    (argCompare reso i1 (passInto i2) == Just EQ || argCompare reso j1 (passInto i2) == Just EQ)
  then
    reducePred' o (PredOr lhs' t2)
  else
   case trace' $ (argCompare reso i1 i2, argCompare reso j1 i2) of
    (Just EQ, _) ->
      reducePred' o (PredOr lhs t2)
    (_, Just EQ) ->
      reducePred' o (PredOr lhs t2)
    (Just LT, Just LT) ->
      if
        (i1 `contains` i2) || (j1 `contains` i2)
      then
        reducePred' o (PredOr lhs t2)
      else
        case trace' $ (argCompare reso (nipInfinity i1) i2, argCompare reso (nipInfinity j1) i2) of
          (Just LT, Just LT) ->
            (BDDeq i1 j1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2)))
          (Just GT, Just GT) ->
            BDDeq i1 j1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2))
          _ -> error "Variable order does not correspond to BDDeq container"
    (Just LT, Just GT) -> reducePred' o (PredOr lhs t2)
    (Just GT, Just LT) -> reducePred' o (PredOr lhs t2)
    _ -> error "Invalid BDDforceOrd usage 2 "
  where
    lhs =
      PredBDD $ BDDeq
        (passInto i1)
        (passInto j1)
        (BDDeq (nipOne i1) (nipOne j1) a1 b1)
        b1
    lhs' =
      case argCompare o i1 j1 of
        Just LT ->
          PredBDD $ BDDv (passOut i1)
            (BDDv (passOut j1)
              a1
              b1)
            (BDDv (passOut j1)
              b1
              a1)
        Just GT ->
          PredBDD $ BDDv (passOut j1)
            (BDDv (passOut i1)
              a1
              b1)
            (BDDv (passOut i1)
              b1
              a1)
    reso = newo <> o
reducePred o (PredOr t1@(PredBDD (BDDforceOrd Comp newo (BDDeq i1 j1 a1 b1))) t2@(PredBDD (BDDv i2 a2 b2))) =
  if
    (argCompare reso i1 (passInto i2) == Just EQ || argCompare reso j1 (passInto i2) == Just EQ)
  then
    error "Invalid BDDforceOrd usage 3 "
  else
   case trace' $ (argCompare reso i1 i2, argCompare reso j1 i2) of
    (Just GT, Just GT) ->
      BDDv i2 (reducePred' o (PredBDD a2||*t1)) (reducePred' o (PredBDD b2||*t1))
    _ -> error $ "Invalid BDDforceOrd usage 4 " ++ show t1 ++ show t2
    where
      reso = newo <> o
reducePred o (PredOr t1@(PredBDD (BDDeq i1 j1 a1 b1)) t2@(PredBDD (BDDforceOrd Comp newo (BDDeq i2 j2 a2 b2)))) =
  case (argCompare reso i1 i2, argCompare reso j1 j2) of
    (Just LT, Just LT) ->
      BDDeq i1 j1 (reducePred' o (PredBDD a1||*t2)) (reducePred' o (PredBDD b1||*t2))
    _ -> error "Invalid BDDforceOrd usage 5"
    where
      reso = newo <> o
reducePred o (PredOr x (PredBDD (BDDforceOrd Step newo y))) =
  reducePred' reso (PredOr x (PredBDD y))
    where
      reso = newo <> o
reducePred o (PredOr x y) =
  reducePred' o $ PredOr (PredBDD (reducePred' o y)) (PredBDD (reducePred' o x))
reducePred o (PredAny n) =
  reducePred'' BDDTrue o (PredAny n)
    where
      reducePred'' _ _ (PredAny 0) =
        BDDFalse
      reducePred'' prTrue o (PredAny n) =
        BDDv [0] prTrue $ reducePred' o (PredPerm (Permutation $ PermPerm $ ArgArg [1]) (PredBDD $ reducePred'' prTrue o $ PredAny (n-1)))      
reducePred o (PredAll n) =
  reducePred'' BDDFalse o (PredAll n)
    where
      reducePred'' _ _ (PredAll 0) =
        BDDTrue
      reducePred'' prFalse o (PredAll n) =
        BDDv [0] (reducePred' o (PredPerm (Permutation $ PermPerm $ ArgArg [1]) (PredBDD $ reducePred'' prFalse o $ PredAll (n-1)))) prFalse
reducePred o (PredPerm perm1 (PredPerm perm2 x)) =
  reducePred' o (PredPerm newPerm (PredBDD $ reducePred' (permOrd newPerm o) x))
    where newPerm = perm2 <> perm1
reducePred o (PredPerm perm (PredBDD (BDDv i a b))) =
  BDDv (toIndexFunc perm i) (reducePred' o $ PredPerm perm (PredBDD a)) (reducePred' o $ PredPerm perm (PredBDD b))
reducePred o (PredPerm perm (PredBDD (BDDeq i j a b))) =
  BDDeq (toIndexFunc perm i) (toIndexFunc perm j) (reducePred' o $ PredPerm perm (PredBDD a)) (reducePred' o $ PredPerm perm (PredBDD b))
reducePred o (PredPerm perm (PredBDD BDDTrue)) =
  BDDTrue
reducePred o (PredPerm perm (PredBDD BDDFalse)) =
  BDDFalse
reducePred o (PredPerm perm (PredBDD (BDDforceOrd _ newo x))) =
  error "not realized yet"
reducePred o (PredPerm perm x) =
  reducePred' o (PredPerm perm (PredBDD $ reducePred' (permOrd perm o) x))
reducePred o x@(PredExists t (PredBDD bdd@(BDDv i a b))) =
  if
    t `containsVar` i
  then
    reducePred' o (PredOr (PredExists t (PredBDD a)) (PredExists t (PredBDD b)))
  else
    reducePred' o (PredBDD (BDDv i (reducePred o $ PredExists t (PredBDD a)) (reducePred o $ PredExists t (PredBDD b))))
reducePred o x@(PredExists t (PredBDD bdd@(BDDforceOrd _ newo a))) =
  error "not realized yet"
reducePred o x@(PredExists t (PredBDD bdd@(BDDeq i j a b))) =
  if
    t `containsVar` i || t `containsVar` j
  then
    reducePred' o (PredOr (PredExists t (PredBDD a)) (PredExists t (PredBDD b)))
  else
    if 
      i `containsVar` t || j `containsVar` t
    then
      error' x
    else
      reducePred' o (PredBDD (BDDeq i j (reducePred o $ PredExists t (PredBDD a)) (reducePred o $ PredExists t (PredBDD b))))
reducePred o (PredExists t (PredBDD BDDTrue)) =
  BDDTrue
reducePred o (PredExists t (PredBDD BDDFalse)) =
  BDDFalse
reducePred o x@(PredExists t a) =
  reducePred' o (PredExists t $ PredBDD $ reducePred' o a)
--reducePred _ x = error $ show x