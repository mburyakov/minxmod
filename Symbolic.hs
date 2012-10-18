module Symbolic where

import Types
import Predicates
import ArgTree
import Data.Boolean

withPerm perm pred = PredPerm (PermPerm perm) pred

withBefore = withFirst
withAfter  = withSecond

withFirst  = withPerm $ ArgArg [0,0]
withSecond = withPerm $ ArgArg [1,0]

predIs [] =
  true       
predIs (x:xs) =
  (if x then (PredArg [0]) else notB (PredArg [0]))
   &&* withPerm (ArgArg[1]) (predIs xs) 

data EnumInsn i = EnumInsn {
  insnNum  :: i,
  insnBody :: Insn
}

instance Functor EnumInsn where
  fmap f (EnumInsn n b) = EnumInsn (f n) b

instance Show i => Show (EnumInsn i) where
  show (EnumInsn num insn) = (show num) ++ ": " ++ show insn

data EnumProg i = EnumProg {
  enum_prog_insns :: [EnumInsn i],
  enum_prog_bindings :: [(String, i)]
} deriving Show

integerEnumerateProg prog = integerEnumerateProg' 0 $ prog_insns prog 

integerEnumerateProg' :: Integer -> [Insn] -> EnumProg Integer
integerEnumerateProg' start ((Label str insn):insns) =
  EnumProg eninsns newbindings
    where
      eninsns = enum_prog_insns others
      newbindings = (str,start): enum_prog_bindings others
      others = integerEnumerateProg' start (insn:insns)
integerEnumerateProg' start ((Block block):insns) =
  integerEnumerateProg' start (block++insns)
integerEnumerateProg' start (insn:insns) =
  EnumProg eninsns newbindings
    where
      eninsns = (EnumInsn start insn):enum_prog_insns others
      newbindings = enum_prog_bindings others
      others = integerEnumerateProg' (start+1) insns
integerEnumerateProg' start [] =
  EnumProg [] []
  
valueEnumerateProg :: Integral s => Prog -> (EnumProg Value, s -> Value)
valueEnumerateProg prog =
  (valprog, fun)
    where
      intprog = integerEnumerateProg prog
      intinsns = enum_prog_insns intprog
      num = length intinsns
      fun x = SmallBoundedValue 0 (fromIntegral num) (fromIntegral x)
      intbindings = enum_prog_bindings intprog
      valinsns = map (fmap fun) intinsns
      valbindings = map (fmap fun) intbindings
      valprog = EnumProg valinsns valbindings

first  (x,y) = x
second (x,y) = y      
      
inputDepth :: Arithmetic -> Int
inputDepth = length.first.arithSignature

outputDepth :: Arithmetic -> Int
outputDepth = length.second.arithSignature      
      
-- predicate on whole input and output stacks
predArithStacks ar = 
  pred &&* (PredBDD $ BDDeq [0,inl] [1,outl] BDDTrue BDDFalse)
    where
      pred = arithPredicate ar
      inl = inputDepth ar
      outl = outputDepth ar

-- predicate on whole input and output stacks and pools      
predArithThread ar = 
      PredPerm (PermPerm $ ArgList [ArgArg [0,0,0], ArgArg [1,0,0]]) (predArithStacks ar)
  &&* PredPerm (PermPerm $ ArgList [ArgArg [0,1], ArgArg [1,1]]) (PredBDD $ BDDeq [0,0] [1,0] BDDTrue BDDFalse)
      
predLine :: Integral s => (s -> Value) -> EnumInsn s -> Predicate
predLine lineV (EnumInsn n (Arith ar)) =
  withPerm (ArgArg[0,0,0]) (predIs $ valToBin (lineV un))
    &&* withPerm (ArgArg[1,0,0]) (predIs $ valToBin (lineV (un+1)))
      &&* withPerm (ArgList [ArgArg[0,1,0],ArgArg[1,1,0]]) (predArithThread ar)
        where
          un = fromIntegral n         
      
progToPred prog = 
  foldl (&&*) (false) preds
    where
      (veprog, valfun) = valueEnumerateProg prog
      veinsns = map (fmap sbValue) $ enum_prog_insns veprog
      preds = map (predLine valfun) veinsns
