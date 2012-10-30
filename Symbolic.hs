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

-- predicate on whole input and output stacks and pools      
predArithThread ar = 
      PredPerm (PermPerm $ ArgList [ArgArg [0,0,0], ArgArg [1,0,0]]) (predArithStacks ar)
  &&* PredPerm (PermPerm $ ArgList [ArgArg [0,1], ArgArg [1,1]]) (eq [0,0] [1,0])

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
      case (x !! 0, y !! 0) of
      (0, 0) ->
        argCompare (permOrd permFirst  stateOrd) x y
      (1, 1) ->
        argCompare (permOrd permSecond stateOrd) x y
      (1, 0) ->
        argCompare stateOrd (lineOrdPermute (inputDepth ar) x) (lineOrdPermute (outputDepth ar) y)
      (0, 1) ->
        argCompare stateOrd (lineOrdPermute (outputDepth ar) x) (lineOrdPermute (inputDepth ar) y)
  }
lineOrd (Jmp str) =
  lineOrd (Arith arNop) 

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
  withPerm (ArgArg[0,0,0]) (predIs $ valToBin (lineV un))
    &&* withPerm (ArgArg[1,0,0]) (predIs $ valToBin (lineV (un+1)))
      &&* (PredBDD $ fixReduce (lineOrd insn) $ withStacks (predArithStacks ar))
        where
          un = fromIntegral n
bddLine lineV c (EnumInsn n insn@(Jmp str)) =
  withPerm (ArgArg[0,0,0]) (predIs $ valToBin (lineV un))
    &&* withPerm (ArgArg[1,0,0]) (predIs $ valToBin (lineV $ trois))
      &&* (PredBDD $ fixReduce (lineOrd insn) $ withStacks (predArithStacks arNop))
        where
          un = fromIntegral n
	  (Just deux) = lookup str c
	  trois = (fromIntegral.sbValue) deux

progToBDD prog =
  reducePred globalOrd $ foldl (||*) (false) bdds
    where
      (veprog, valfun) = valueEnumerateProg prog
      veinsns = map (fmap sbValue) $ enum_prog_insns veprog
      bdds = map (bddLine valfun $ enum_prog_counter veprog) veinsns


