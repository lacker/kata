constant n : nat

constants p q : Prop

example : p → p := assume hp: p, show p, from hp

theorem or_swap (p q : Prop) : p ∨ q → q ∨ p := assume h: p ∨ q,
or.elim
h
(assume hp: p, show q ∨ p, from or.intro_right q hp)
(assume hq: q, show q ∨ p, from or.intro_left p hq)

example : p ∨ q ↔ q ∨ p :=
iff.intro
(or_swap p q)
(or_swap q p)

/- TODO: prove that times_successor(x) is even -/

def times_successor (n : nat) := n * ( n + 1)

def is_even (a : nat) := ∃ b, 2 * b = a

/-
theorem even_times {a b : nat } (h : is_even a) : is_even (a * b) := sorr
-/
