constant n : nat

#reduce (n + 2) - 2

/- TODO: prove that times_successor(x) is even -/

def times_successor (n : nat) := n * ( n + 1)

def is_even (a : nat) := ∃ b, 2 * b = a

theorem even_times {a b : nat } (h : is_even a) : is_even (a * b) := sorry

