--{-# LANGUAGE ExistentialQuantification #-}
--{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
--{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DatatypeContexts #-}
--{-# LANGUAGE GADTs #-}

module Types where

import qualified Data.Map as M
import Data.Bits
--import Data.Typeable
--import Data.Boolean
import SimpleHList

data Insn i o =
--    Label String Insn
--  | Block [Insn]
  Jmp String
  | JmpCond String
  | Get String
  | Set String
  | Arith (Arithmetic i o)
  | Enter String
  | TryEnter String
  | Leave String
--  | Spawn String Prog
  | Assert String

data (Stack i, Stack o) => Arithmetic i o = Arithmetic {
  arOp     :: (i -> [o]),
  --arInput  :: [Int],
  --arOutput :: [Int],
  predicate:: [[Bool]] -> [[Bool]] -> Bool
}

arNeg = Arithmetic {
  arOp = \(HCons (BoolValue a) HNil) -> [HCons (BoolValue (not a)) HNil],
  predicate = undefined
}

applyArith arith input = 
  hConcat outp rest
    where
      (inp, rest) = (hTakeDrop input)
      outp = head (op inp)
      op = arOp arith

class Stack s where
  stackToBinList :: s -> [[Bool]]

instance Stack (HNil) where
  stackToBinList _ = []

instance (Value v, Stack s, HList s) => Stack (HCons v s) where
  stackToBinList (HCons value tail) = 
    toBinary value : stackToBinList tail

class Binarizable a where
  binLength   :: a -> Int    -- independent of argument
  toBinary :: a -> [Bool] -- TODO: wanted: length $ toBinary x == binLength x (for all x) 
  binLength x = length $ toBinary x

class Binarizable a => Value a

checkValLength x = binLength x == length (toBinary x) -- it must be always True
      
data EnumValue a = EnumValue a deriving Show
instance Bits a => Value (EnumValue a)
instance Bits a => Binarizable (EnumValue a) where
  binLength   (EnumValue x) = bitSize x
  toBinary v@(EnumValue x) = map (testBit x) [0..(binLength v)-1]

data BoolValue = BoolValue Bool deriving Show
instance Value BoolValue
instance Binarizable BoolValue where
  binLength _ = 1
  toBinary (BoolValue x) = [x]

--TODO: do not push PidValue when spawning
data PidValue  = PidValue Pid deriving Show
instance Value PidValue
instance Binarizable PidValue where
  binLength _ = error "I'm a PidValue - your memory leak!"
  toBinary _ = error "I'm a PidValue - do not disturb me!"
  
--There is no IntValue because of unknown length (Int8, Int16, ...)

data Pid = Pid Int deriving (Eq, Ord)

instance Show Pid where
  show (Pid p) = show p

class Env e where
  envToBinList :: e -> [(String, [Bool])]  

instance Env (HNil) where
  envToBinList _ = []

instance (Value v, Env e, HList e) => Env (HCons (String, v) e) where
  envToBinList (HCons (name, value) tail) = 
    (name, toBinary value) : envToBinList tail

data (Stack s, Env e) => Point s e = Point {
  pointStack :: s,
  pointEnv   :: e
}

first  (x,y) = x
second (x,y) = y

instance (Stack s, Env e) => Binarizable (Point s e) where
  toBinary point = 
    envbin ++ stackbin
      where
        envbin   = concat $ map second $ envToBinList env
	stackbin = concat $ stackToBinList stack
	env = pointEnv point
	stack = pointStack point
  

{--
data Prog = Prog 
  { 
    prog_insns :: [Insn] 
  }

data Model = Model
  {    
    mod_vars :: [(String,Value)],
    mod_mons :: [String],
    mod_prog :: Prog
  }

data ProcState = Running
  { 
    proc_prog :: Prog,
    proc_ip :: Int,
    proc_stack :: [Value],
    proc_waitedMon :: Maybe String
  }
  | Finished

data MonState = MonFree | MonOccupied { mon_owner :: Pid, mon_depth :: Int {- , mon_waiters :: Queue Pid -} } deriving (Ord, Eq, Show)

data ProgramState = ProgramState
  { 
    st_procs :: M.Map Pid (String, ProcState),
    st_vars :: M.Map String Value,
    st_mons :: M.Map String MonState
  }

instance Show ProgramState where
  show st = show (st_vars st, st_mons st, [(pid, name, showProc p) | (pid,(name,p)) <- M.toList (st_procs st)]) 
    where
      showProc Finished = "<finished>"
      showProc r@Running{proc_waitedMon=Nothing, proc_ip=ip} = show ip
      showProc r@Running{proc_waitedMon=Just m,  proc_ip=ip} = show ip ++ "?" ++ m

stateSig s = (st_vars s, st_mons s, [(pid, sigP p) | (pid,(name,p)) <- M.toList (st_procs s)] )
  where
    sigP Finished = Nothing
    sigP r@Running{} = Just (proc_ip r, proc_stack r, proc_waitedMon r)

instance Eq ProgramState where
  (==) a b = (stateSig a == stateSig b)
instance Ord ProgramState where
  compare a b = compare (stateSig a) (stateSig b)

initState :: Model -> ProgramState
initState Model {mod_vars = vars, mod_mons = mons, mod_prog = entryPoint} = ProgramState {
    st_procs = M.fromList [(Pid 0, ("entry", Running {proc_prog = entryPoint, proc_ip = 0, proc_stack = [], proc_waitedMon = Nothing}))],
    st_vars  = M.fromList vars,
    st_mons  = M.fromList [(m, MonFree) | m <- mons]
  }

compile :: [Insn] -> Prog
compile is = Prog {prog_insns = expandBlocks is}
  where
    expandBlocks = concatMap (\i -> case i of { Block is -> expandBlocks is ; j -> [j] })

--}