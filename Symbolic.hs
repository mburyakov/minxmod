module Symbolic where

import Types

data EnumInsn i = EnumInsn {
  insnNum  :: i,
  insnBody :: Insn
}

instance Show i => Show (EnumInsn i) where
  show (EnumInsn num insn) = (show num) ++ ": " ++ show insn

data EnumProg i = EnumProg {
  enum_prog_insns :: [EnumInsn i],
  enum_prog_bindings :: [(String, Integer)]
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
