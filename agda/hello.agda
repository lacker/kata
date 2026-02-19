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


infixl 6 _+_

_+_ : Nat -> Nat -> Nat
x + y = add x y


mul : Nat -> Nat -> Nat
mul zero y = zero
mul (suc x) y = y + mul x y


infixl 7 _*_

_*_ : Nat -> Nat -> Nat
x * y = mul x y
