module Debug1 where

import qualified Debug.Trace as Tr

trace = Tr.trace
trace' x = trace ("trace' :'" ++ show x ++ "' ++ \n") x
trace'' x y = trace ("trace' :''" ++ show x ++ "' ++ \n") y
error' x = error $ show x
assert cond str ret = if cond then ret else error str
