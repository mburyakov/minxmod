module Examples where

import Types
import Predicates
import Data.Boolean

predEq 0 m =
  PredNeg (PredAny m)
predEq n 0 =
  PredNeg (PredAny n)
predEq n m =
  PredIf
    (PredEquiv (PredArg 0) (PredArg n))
    (PredPerm (PermPerm $ filter (/=n) [1..n+m-1]) (predEq (n-1) (m-1)))
    PredFalse
  
    
    
predInc n 0 =
  PredFalse
predInc 0 m =
  PredAnd (PredArg 0) (PredPerm (PermShift 1) (PredNeg (PredAny m)))
predInc n m =
  PredIf
    (PredEquiv (PredArg 0) (PredArg n))
    PredFalse
    (PredIf
      (PredArg 0)
        (PredPerm (PermPerm $ filter (/=n) [1..n+m-1]) (predInc (n-1) (m-1)))
        (PredPerm (PermPerm $ filter (/=n) [1..n+m-1]) (predEq (n-1) (m-1))))

        
        
predAdd 0 n2 na =
  predEq n2 na

predAdd n1 0 na =
  predEq n1 na
  
predAdd n1 n2 0 =
  PredNeg (PredAny (n1+n2))
  
predAdd n1 n2 na =
  PredIf
    (PredXor (PredXor (PredArg 0) (PredArg n1)) (PredArg (n1+n2)))
    PredFalse
    (PredIf
      (PredAnd (PredArg 0) (PredArg n1))
        (PredPerm (PermPerm $ filter ((/=n1)&&*(/=n1+n2)) [1..n1+n2+na-1]) (predIncAdd (n1-1) (n2-1) (na-1)))
        (PredPerm (PermPerm $ filter ((/=n1)&&*(/=n1+n2)) [1..n1+n2+na-1]) (predAdd (n1-1) (n2-1) (na-1))))

        
        
predIncAdd 0 n2 na =
  predInc n2 na

predIncAdd n1 0 na =
  predInc n1 na
  
predIncAdd n1 n2 0 =
  PredFalse

predIncAdd n1 n2 na =
  PredIf
    (PredEquiv (PredXor (PredArg 0) (PredArg n1)) (PredArg (n1+n2)))
    PredFalse
    (PredIf
      (PredOr (PredArg 0) (PredArg n1))
        (PredPerm (PermPerm $ filter ((/=n1)&&*(/=n1+n2)) [1..n1+n2+na-1]) (predIncAdd (n1-1) (n2-1) (na-1)))
        (PredPerm (PermPerm $ filter ((/=n1)&&*(/=n1+n2)) [1..n1+n2+na-1]) (predAdd (n1-1) (n2-1) (na-1))))