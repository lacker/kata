module Main

import Data.Nat

-- A sorted list where all elements are >= the lower bound
data SortedList : (lower : Nat) -> Type where
  SNil  : SortedList lower
  SCons : (x : Nat) -> LTE lower x -> SortedList x -> SortedList lower

-- A sorted list with no lower bound constraint (starts at 0)
OrderedList : Type
OrderedList = SortedList 0

-- Examples
empty : OrderedList
empty = SNil

-- [1, 3, 5]
example1 : OrderedList
example1 = SCons 1 LTEZero (SCons 3 (LTESucc LTEZero) (SCons 5 (LTESucc (LTESucc (LTESucc LTEZero))) SNil))

-- Helper to show a sorted list
showSorted : SortedList n -> String
showSorted SNil = "[]"
showSorted (SCons x _ rest) = show x ++ " :: " ++ showSorted rest

main : IO ()
main = do
  putStrLn "Hello, World!"
  putStrLn $ "Sorted list: " ++ showSorted example1
