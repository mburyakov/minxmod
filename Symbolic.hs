{-# LANGUAGE DeriveDataTypeable #-}

module Symbolic where

import DebugStub
import qualified Debug1

import Types
import ArgTree
import ArgOrd
import Permutations
import Predicates
import Arithmetic

import Data.Boolean
import Data.Monoid
import Data.Typeable

data EnumInsn i = EnumInsn {
  insnNum  :: i,
  insnBody :: Insn
}

type Counter i = [(String, i)]

instance Functor EnumInsn where
  fmap f (EnumInsn n b) = EnumInsn (f n) b

instance Show i => Show (EnumInsn i) where
  show (EnumInsn num insn) = (show num) ++ ": " ++ show insn

data EnumProg i = EnumProg {
  enum_prog_insns :: [EnumInsn i],
  enum_prog_counter :: Counter i
} deriving Show

integerEnumerateProg prog = integerEnumerateProg' 0 $ prog_insns prog 

integerEnumerateProg' :: Integer -> [Insn] -> EnumProg Integer
integerEnumerateProg' start ((Label str insn):insns) =
  EnumProg eninsns newcounter
    where
      eninsns = enum_prog_insns others
      newcounter = (str,start): enum_prog_counter others
      others = integerEnumerateProg' start (insn:insns)
integerEnumerateProg' start ((Block block):insns) =
  integerEnumerateProg' start (block++insns)
integerEnumerateProg' start (insn:insns) =
  EnumProg eninsns newcounter
    where
      eninsns = (EnumInsn start insn):enum_prog_insns others
      newcounter = enum_prog_counter others
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
      intcounter = enum_prog_counter intprog
      valinsns = map (fmap fun) intinsns
      valcounter = map (fmap fun) intcounter
      valprog = EnumProg valinsns valcounter

inputDepth :: Arithmetic -> Int
inputDepth = length.fst.arithSignature

outputDepth :: Arithmetic -> Int
outputDepth = length.snd.arithSignature      
      
-- predicate on whole input and output stacks
predArithStacks ar =
  pred &&* (eq [0,inl] [1,outl])
    where
      pred = PredBDD bdd
      bdd = reducePred (permOrd permStacks (lineOrd (Arith ar))) (arithPredicate ar)
      inl = inputDepth ar
      outl = outputDepth ar
      f ls = ls !! 0 : ls !! 1 : 0 : drop 2 ls

-- predicate on bottomed input and output stacks
predArithBottomedStacks ar =
  pred &&* (eq [0,inl] [1,outl])
    &&* foldl (&&*) true valsBefore
      &&* foldl (&&*) true valsAfter
    where
      valsBefore = map (notB . PredArg . (\x->[0,x,0])) [0..inl -1]
      valsAfter  = map (notB . PredArg . (\x->[1,x,1])) [0..outl-1]
      pred = PredBDD bdd
      bdd = processBDDv f $ reducePred (permOrd permStacks (lineOrd (Arith ar))) (arithPredicate ar)
      inl = inputDepth ar
      outl = outputDepth ar
      f ls = ls !! 0 : ls !! 1 : 0 : drop 2 ls

-- ord on state set
data OrdState = OrdState
  deriving (Eq, Show, Typeable)
instance ArgOrdClass OrdState where
  argCompare OrdState x y =
    Just $ compare x y

--should not use it
stateOrd = ArgOrd OrdState

lineOrdPermute n i = [i !! 1] ++ [(i !! 2) + n] ++ (drop 3 i) ++ [i !! 0]

--should not use it
lineOrd insn = ArgOrd $ OrdLine insn

data OrdLine = OrdLine Insn
  deriving (Eq, Show, Typeable)
instance ArgOrdClass OrdLine where
  argCompare (OrdLine insn@(Arith ar)) x y =
      let
        xp = case (x !! 0, x !! 1) of
          (0, 1) ->
            lineOrdPermute (outputDepth ar) x
          (1, 1) ->
            lineOrdPermute (inputDepth ar) x
          (_, 0) ->
            lineOrdPermute 0 x
        yp = case (y !! 0, y !! 1) of
          (0, 1) ->
            lineOrdPermute (outputDepth ar) y
          (1, 1) ->
            lineOrdPermute (inputDepth ar) y
          (_, 0) ->
            lineOrdPermute 0 y
      in case (x !! 0, y !! 0) of
            (0, 0) ->
              argCompare (permOrd permFirst  stateOrd) x y
            (1, 1) ->
              argCompare (permOrd permSecond stateOrd) x y
            (1, 0) ->
              argCompare stateOrd xp yp
            (0, 1) ->
              argCompare stateOrd xp yp
  argCompare (OrdLine insn@(Jmp str)) x y =
      let
        xp =
            lineOrdPermute 0 x
        yp =
            lineOrdPermute 0 y
      in case (x !! 0, y !! 0) of
            (0, 0) ->
              argCompare (permOrd permFirst  stateOrd) x y
            (1, 1) ->
              argCompare (permOrd permSecond stateOrd) x y
            (1, 0) ->
              argCompare stateOrd xp yp
            (0, 1) ->
              argCompare stateOrd xp yp
  argCompare (OrdLine insn@(JmpCall str)) x y =
      let
        xp = case (x !! 0, x !! 1) of
          (_, 1) ->
            lineOrdPermute 0 x
          (0, 0) ->
            lineOrdPermute 1 x
          (1, 0) ->
            lineOrdPermute 0 x
        yp = case (y !! 0, y !! 1) of
          (_, 1) ->
            lineOrdPermute 0 y
          (0, 0) ->
            lineOrdPermute 1 y
          (1, 0) ->
            lineOrdPermute 0 y
      in case (x !! 0, y !! 0) of
            (0, 0) ->
              argCompare (permOrd permFirst  stateOrd) x y
            (1, 1) ->
              argCompare (permOrd permSecond stateOrd) x y
            (1, 0) ->
              argCompare stateOrd xp yp
            (0, 1) ->
              argCompare stateOrd xp yp
  argCompare (OrdLine insn@JmpRet) x y =
      let
        xp = case (x !! 0, x !! 1) of
          (_, 1) ->
            lineOrdPermute 0 x
          (0, 0) ->
            lineOrdPermute 0 x
          (1, 0) ->
            lineOrdPermute 1 x
        yp = case (y !! 0, y !! 1) of
          (_, 1) ->
            lineOrdPermute 0 y
          (0, 0) ->
            lineOrdPermute 0 y
          (1, 0) ->
            lineOrdPermute 1 y
      in case (x !! 0, y !! 0) of
            (0, 0) ->
              argCompare (permOrd permFirst  stateOrd) x y
            (1, 1) ->
              argCompare (permOrd permSecond stateOrd) x y
            (1, 0) ->
              argCompare stateOrd xp yp
            (0, 1) ->
              argCompare stateOrd xp yp

--globalOrd on Kripke structure
data OrdGlobal = OrdGlobal
  deriving (Eq, Show, Typeable)
instance ArgOrdClass OrdGlobal where
  argCompare OrdGlobal x y =
    Just $ compare (permute x) (permute y)
      where
        permute i = (i !! 1, i !! 2, drop 3 i, i !! 0)


--should not use it
globalOrd =
  ArgOrd OrdGlobal

type Options = [(String, String)]

bddLine :: Integral s => Options -> (s -> Value) -> Counter Value -> EnumInsn s -> Predicate
bddLine opts lineV c (EnumInsn n insn@(Arith ar)) =
  (withFirst $ withAddressStack $ withFirst $ predIs $ valToBin (lineV un))
    &&* (withSecond $ withAddressStack $ withFirst $ predIs $ valToBin (lineV (un+1)))
    &&* (PredBDD $ trace' $ fixReduce (lineOrd insn) (
            (withAddressStacksRest $ predArithStacks arNop)
              &&* (withStacks (if lookup "bottom" opts == Nothing then predArithStacks ar else predArithBottomedStacks ar))))
        where
          un = fromIntegral n
bddLine opts lineV c (EnumInsn n insn@(Jmp str)) =
  (withFirst $ withAddressStack $ withFirst $ predIs $ valToBin (lineV un))
    &&* (withSecond $ withAddressStack $ withFirst $ predIs $ valToBin (lineV trois))
    &&* (PredBDD $ fixReduce (lineOrd insn) (
            (withAddressStacksRest $ predArithStacks arNop)
              &&* (withStacks (predArithStacks arNop))))
        where
          un = fromIntegral n
          (Just deux) = lookup str c
          trois = (fromIntegral.sbValue) deux
bddLine opts lineV c (EnumInsn n insn@(JmpCall str)) =
  (withFirst $ withAddressStack $ withFirst $ predIs $ valToBin (lineV un))
    &&* (withSecond $ withAddressStack $ withFirst $ predIs $ valToBin (lineV trois))
    &&* (PredBDD $ fixReduce (lineOrd insn) (
            (withAddressStacksRest $ predArithStacks $ addrOp)
              &&* (withStacks (predArithStacks arNop))))
        where
          un = fromIntegral n
          (Just deux) = lookup str c
          trois = (fromIntegral.sbValue) deux
          addrOp = arPush $ lineV un
-- should use more compact ordering
bddLine opts lineV c (EnumInsn n insn@(JmpRet)) =
  (withFirst $ withAddressStack $ withFirst $ predIs $ valToBin (lineV un))
   &&* (withPerm (ArgList[ArgArg[0,0,1,0],ArgArg[1,0,0,0]]) (predInc size size))
    &&* (PredBDD $ fixReduce (lineOrd insn) (
            (withAddressStacksRest $ predArithStacks $ addrOp)
              &&* (withStacks (predArithStacks arNop))))
        where
          un = fromIntegral n
          size = binSize $ valType $ lineV undefined
          addrOp = arPop $ valType $ lineV undefined

progToBDD options prog =
  processForces (const $ Just Step) $ reducePred globalOrd $ foldl (||*) (false) bdds
    where
      (veprog, valfun) = valueEnumerateProg prog
      veinsns = map (fmap sbValue) $ enum_prog_insns veprog
      bdds = map (bddLine options valfun $ enum_prog_counter veprog) veinsns
