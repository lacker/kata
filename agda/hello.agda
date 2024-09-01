data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello


data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
