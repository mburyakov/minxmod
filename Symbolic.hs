module Symbolic where

import Types
import Predicates
import ArgTree
import Arithmetic
import Data.Boolean

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
      pred = arithPredicate ar
      inl = inputDepth ar
      outl = outputDepth ar

-- ord on state set
stateOrd :: ArgOrd
stateOrd =
  ArgOrd {
    ordShow = "stateOrd",
    argCompare = compare
  }

lineOrdPermute n i = [i !! 1] ++ [(i !! 2) + n] ++ (drop 3 i) ++ [i !! 0]

lineOrd :: Insn -> ArgOrd
lineOrd (Arith ar) =
  ArgOrd {
    ordShow = "lineOrd",
    argCompare = \x y ->
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
  }
lineOrd (Jmp str) =
  ArgOrd {
    ordShow = "lineOrd",
    argCompare = \x y ->
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
  }
lineOrd (JmpCall str) =
  ArgOrd {
    ordShow = "lineOrd",
    argCompare = \x y ->
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
  }

--globalOrd on Kripke structure
globalOrd =
  ArgOrd {
    ordShow = "globalOrd",
    argCompare = \x y ->
      compare (permute x) (permute y)
  }
    where
      permute i = (drop 1 i) ++ [i !! 0]

bddLine :: Integral s => (s -> Value) -> Counter Value -> EnumInsn s -> Predicate
bddLine lineV c (EnumInsn n insn@(Arith ar)) =
  (withFirst $ withAddressStack $ withFirst $ predIs $ valToBin (lineV un))
    &&* (withSecond $ withAddressStack $ withFirst $ predIs $ valToBin (lineV (un+1)))
    &&* (PredBDD $ fixReduce (lineOrd insn) (
            (withAddressStacksRest $ predArithStacks arNop)
              &&* (withStacks (predArithStacks ar))))
        where
          un = fromIntegral n
bddLine lineV c (EnumInsn n insn@(Jmp str)) =
  (withFirst $ withAddressStack $ withFirst $ predIs $ valToBin (lineV un))
    &&* (withSecond $ withAddressStack $ withFirst $ predIs $ valToBin (lineV trois))
    &&* (PredBDD $ fixReduce (lineOrd insn) (
            (withAddressStacksRest $ predArithStacks arNop)
              &&* (withStacks (predArithStacks arNop))))
        where
          un = fromIntegral n
          (Just deux) = lookup str c
          trois = (fromIntegral.sbValue) deux
bddLine lineV c (EnumInsn n insn@(JmpCall str)) =
  (withFirst $ withAddressStack $ withFirst $ predIs $ valToBin (lineV un))
    &&* (withSecond $ withAddressStack $ withFirst $ predIs $ valToBin (lineV trois))
    &&* (PredBDD $ fixReduce (lineOrd insn) (
            (withAddressStacksRest $ predArithStacks $ arPush (lineV un))
              &&* (withStacks (predArithStacks arNop))))
        where
          un = fromIntegral n
	  (Just deux) = lookup str c
	  trois = (fromIntegral.sbValue) deux
	  addrOp = arPush $ lineV trois

progToBDD prog =
  reducePred globalOrd $ foldl (||*) (false) bdds
    where
      (veprog, valfun) = valueEnumerateProg prog
      veinsns = map (fmap sbValue) $ enum_prog_insns veprog
      bdds = map (bddLine valfun $ enum_prog_counter veprog) veinsns


