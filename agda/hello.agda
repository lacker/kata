data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello


data Nat : Set where
  zero : Nat
  suc : Nat -> Nat


add : Nat -> Nat -> Nat
add zero y = y
add (suc x) y = suc (add x y)
