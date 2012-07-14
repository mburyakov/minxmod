module Types where

import qualified Data.Map as M
import Data.Bits
import Data.Int
--import Data.Word
import Predicates

data Insn =
    Label String Insn
  | Block [Insn]
  | Jmp String
  | JmpCond String
  | Get String
  | Set String
  | Arith Arithmetic
  | Enter String
  | TryEnter String
  | Leave String
  | Spawn String Prog
  | Assert String

data Value =
    BoolValue Bool 
  | IntValue Int8
  | SmallBoundedValue {smallFrom::Int32, smallTo::Int32, sbValue::Int32   }
  | BigBoundedValue   {bigFrom::Integer, bigTo::Integer, bbValue::Integer }
  | BitSetValue       {                                  bsValue::[Bool]  }
  | PidValue Pid
  | ErrorValue String deriving (Ord, Eq)

instance Show Value where
  show (BoolValue b) = show b
  show (IntValue i) = show i
  show (SmallBoundedValue from to i) = show i ++ " in [" ++ show from ++ ".." ++ show to ++ "]"
  show (BigBoundedValue   from to i) = show i ++ " in [" ++ show from ++ ".." ++ show to ++ "]"
  show (BitSetValue l) = "[" ++ map (\b -> if b then '1' else '0') l ++ "]"
  show (PidValue p) = show p
  show (ErrorValue s) = "!!error " ++ show s ++ "!!"

fullCheckValue v = 
  bv == v
    where
      ifChValThenChType = if chVal then chType else True
      chVal  = checkValue v
      chType = checkValType t
      t = valType v
      b = valToBin v
      bv = binToVal t b


-- is value valid?
checkValue :: Value -> Bool
checkValue (BoolValue _) = True
checkValue (IntValue _)  = True
checkValue (SmallBoundedValue from to v) = v>=from && v<=to
checkValue (BigBoundedValue   from to v) = v>=from && v<=to
checkValue (BitSetValue l) = (length l)<=2^29
checkValue (PidValue _) = False
checkValue (ErrorValue _) = True

data ValueType =
    BoolType
  | IntType
  | SmallBoundedType Int32   Int32
  | BigBoundedType   Integer Integer
  | BitSetType Int
  | PidType
  | ErrorType String

-- value should be valid
-- return: valid type
valType :: Value -> ValueType
valType (BoolValue        _) = BoolType
valType (IntValue         _) = IntType
valType (SmallBoundedValue from to _) = SmallBoundedType from to
valType (BigBoundedValue   from to _) = BigBoundedType   from to
valType (BitSetValue      l) = BitSetType $ length l
valType (PidValue         _) = PidType
valType (ErrorValue       s) = ErrorType s

-- is type valid (populated) (exists acceptable value of this type)?
checkValType :: ValueType -> Bool
checkValType BoolType = True
checkValType IntType  = True
checkValType (SmallBoundedType _ _) = True
checkValType (BigBoundedType   from to) = intBinSize (to-from) < 2^29
checkValType (BitSetType s) = s<=2^29 && s>=0
checkValType PidType = False
checkValType (ErrorType _) = True

bitsToBin :: Bits a => a -> [Bool]
bitsToBin i =
  intToBin (bitSize i) i

intToBin :: (Bits a) => Int -> a -> [Bool]
intToBin length i =
  map (testBit i) [0..length-1]

intToHisBin n = 
  intToBin (intBinSize n) n

binToInt :: Integral a => [Bool] -> a
binToInt [] = 0
binToInt (h:t) =
  2*(binToInt t) + if h then 1 else 0

intBinSize :: Integral a => a -> Int
intBinSize 0 = 0
intBinSize 1 = 1
intBinSize x | x>1 =
  1 + intBinSize (x `div` 2)

checkIntBinBijection n =
  n == (binToInt $ intToHisBin n)

boundInt :: Integral a => a -> a -> a -> a
boundInt from to v =
  from + (v-from) `mod` 2^len
    where
      len = intBinSize (to-from)

-- type should be valid
binSize :: ValueType -> Int
binSize BoolType = 1
binSize IntType = 8
binSize (SmallBoundedType from to) = intBinSize (to-from)
binSize (BigBoundedType from to) = intBinSize (to-from)
binSize (BitSetType s) = s
binSize PidType = error "binSize PidType"
binSize (ErrorType _) = 0

-- value should be valid
valToBin :: Value -> [Bool]
valToBin (BoolValue b) = [b]
valToBin (IntValue i) = bitsToBin i
valToBin (SmallBoundedValue from to i) = intToBin (intBinSize (to-from)) i
valToBin (BigBoundedValue   from to i) = intToBin (intBinSize (to-from)) i
valToBin (BitSetValue l) = l
valToBin (PidValue p) = error "valToBin PidType"
valToBin (ErrorValue s) = []

-- length should be correct
-- return: value can be invalid
binToVal :: ValueType -> [Bool] -> Value
binToVal BoolType [bool] = BoolValue bool
binToVal IntType b = IntValue $ binToInt b
binToVal (SmallBoundedType from to) b = SmallBoundedValue from to $ boundInt from to $ binToInt b
binToVal (BigBoundedType   from to) b = BigBoundedValue   from to $ boundInt from to $ binToInt b
binToVal (BitSetType _) b = BitSetValue b
binToVal PidType b = error "binToVal PidType"
binToVal (ErrorType s) [] = ErrorValue s

data Arithmetic = Arithmetic {
  -- input top of stack, output top of stack
  arithSignature :: ([ValueType], [ValueType]),
  -- apply the function to the top of stack (shouldn't modify bottom)
  -- input should have valid type
  arithFunc :: [Value] -> [[Value]],
  -- arithPredicate :: Predicate on [beforeTop, afterTop]
  arithPredicate :: Predicate
}

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

