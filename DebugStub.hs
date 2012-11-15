module DebugStub where

trace x y = y 
trace' x = x
trace'' x y = y
error' x = error $ show x
assert cond str ret = ret
