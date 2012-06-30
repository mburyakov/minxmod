module Types where

import qualified Data.Map as M
import Data.Bits
import Data.Int

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

--All integer value are unsigned (machine-representation).
--Signed values are simulated with labels
data Value =
    BoolValue Bool 
  | IntValue Int8           --TODO:unsigned
  | SmallIntValue {valSize ::Int,   siValue::Int32,   valLabel::String} --TODO:unsigned
  | BigIntValue   {valSize ::Int,   biValue::Integer, valLabel::String} --TODO:unsigned
  | EnumValue     {valSpace::Int32, enValue::Int32 } --TODO:unsigned
  | BitSetValue   {                 bsValue::[Bool] }
  | PidValue Pid deriving (Ord, Eq)

instance Show Value where
  show (BoolValue b) = show b
  show (IntValue i) = show i
  show (SmallIntValue _ i label) = show i ++ "/" ++ label ++ "/"
  show (BigIntValue _ i label) = show i ++ "/" ++ label ++ "/"	
  show (BitSetValue l) = "[" ++ map (\b -> if b then '1' else '0') l ++ "]"
  show (PidValue p) = show p

{-fullCheckValue v = 
  checkValue v && checkValType t && checkValBinary v b
    where
      t = valueType v
      b = vatToBinary v
-}
-- is value acceptable?
checkValue :: Value -> Bool
checkValue (BoolValue _) = True
checkValue (IntValue _)  = True
checkValue (SmallIntValue s v _) = (intBinSize v) <= s
checkValue (BigIntValue   s v _) = (intBinSize v) <= s
checkValue (EnumValue     sp v) = v < sp
checkValue (BitSetValue l) = (length l)<=32
checkValue (PidValue _) = False

data ValueType =
    BoolType
  | IntType
  | SmallIntType Int --TODO:unsigned
  | BigIntType Int --TODO:unsigned
  | EnumType Int32 --TODO:unsigned
  | BitSetType Int --TODO:unsigned
  | PidType

valType :: Value -> ValueType
valType (BoolValue        _) = BoolType
valType (IntValue         _) = IntType
valType (SmallIntValue s  _ lab) = SmallIntType s
valType (BigIntValue   s  _ lab) = BigIntType s
valType (EnumValue     sp _) = EnumType sp
valType (BitSetValue      l) = BitSetType $ length l
valType (PidValue         _) = PidType

-- is type acceptable?
checkValType :: ValueType -> Bool
checkValType BoolType = True
checkValType IntType = True
checkValType (SmallIntType s) = s <= 32
checkValType (BigIntType s) = True
checkValType (EnumType sp) = sp>0
checkValType (BitSetType s) = s<=32
checkValType PidType = False

bitsToBinary :: Bits a => a -> [Bool]
bitsToBinary i =
  map (testBit i) [0..bitSize i-1]

intBinSize :: Bits a => a -> Int
intBinSize v = 
  length $ dropWhile not $ reverse $ bitsToBinary v

binSize :: ValueType -> Int
binSize BoolType = 1
binSize IntType = 8
binSize (SmallIntType s) = s
binSize (BigIntType s) = s
binSize (EnumType sp) = intBinSize (sp-1)
binSize (BitSetType s) = s
binSize PidType = error "binSize PidType"

valToBinary :: Value -> [Bool]
valToBinary (BoolValue b) = [b]
valToBinary (IntValue i) = bitsToBinary i
valToBinary (SmallIntValue s i label) = take s (bitsToBinary i)
--valToBinary (BigIntValue s i label) = 
--valToBinary (BitSetValue l) = 
--valToBinary (PidValue p) = 

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

