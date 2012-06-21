{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Types where

import qualified Data.Map as M
import Data.Bits
import Data.Typeable
import Data.Boolean

data Insn =
    Label String Insn
  | Block [Insn]
  | Jmp String
  | JmpCond String
  | Get String
  | Set String
  | Arith ([Value] -> [[Value]])
  | Enter String
  | TryEnter String
  | Leave String
  | Spawn String Prog
  | Assert String
  
class (Show a, Typeable a) => Value_ a where
  valLength   :: a -> Int    -- independent of argument
  valToBinary :: a -> [Bool] -- TODO: wanted: length $ valToBinary x == valLength x (for all x) 
  valLength x = length $ valToBinary x
  
data Value = forall a. Value_ a => Value a

instance Show (Value) where
  show (Value x) = show x
instance Eq (Value) where
  (Value x) == (Value y) = (typeOf x == typeOf y) && (valToBinary x == valToBinary y)
instance Ord (Value) where
  compare (Value x) (Value y) = case typeCmp of
      EQ -> valCmp
      _  -> typeCmp
    where
      typeCmp = compare (typeOf x)   (typeOf y)
      valCmp = compare (valToBinary x) (valToBinary y)
      
data EnumValue a = EnumValue a deriving (Show, Typeable)
instance (Show a, Bits a, Typeable a) => Value_ (EnumValue a) where
  valLength   (EnumValue x) = bitSize x
  valToBinary v@(EnumValue x) = map (testBit x) [0..(valLength v)]

data BoolValue = BoolValue Bool deriving (Show, Typeable)
instance Value_ BoolValue where
  valLength _ = 1
  valToBinary (BoolValue x) = [x]

--TODO: do not push PidValue when spawning
data PidValue  = PidValue Pid deriving (Show, Typeable)
instance Value_ PidValue where
  valLength _ = error "I'm a PidValue - your memory leak!"
  valToBinary _ = error "I'm a PidValue - do not disturb me!"
  
--There is no IntValue because of unknown length (Int8, Int16, ...)

data Pid = Pid Int deriving (Eq, Ord)

instance Show Pid where
  show (Pid p) = show p

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

