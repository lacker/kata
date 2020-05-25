import data.nat.basic

constants p q : Prop

example : p → p := assume hp: p, show p, from hp

theorem or_swap (p q : Prop) : p ∨ q → q ∨ p :=
assume h: p ∨ q,
or.elim h
(assume hp: p, show q ∨ p, from or.intro_right q hp)
(assume hq: q, show q ∨ p, from or.intro_left p hq)

example : p ∨ q ↔ q ∨ p :=
iff.intro
(or_swap p q)
(or_swap q p)

/- TODO: prove that times_successor(x) is even -/
def times_successor (n : ℕ) := n * (n + 1)

def is_even (a : ℕ) := ∃ b, 2 * b = a

def is_odd (a : ℕ) := ∃ b, 2 * b + 1 = a

theorem zero_is_even: is_even 0 :=
exists.intro 0 (zero_mul 2)

theorem even_plus_one_is_odd (a : ℕ) (h: is_even a) : is_odd (a + 1) :=
exists.elim h
(assume b, assume hb: 2 * b = a, show is_odd (a + 1), from
exists.intro b
  (calc
  2 * b + 1 = a + 1 : by rw hb
  )       
)

lemma l1: 2 * 1 = 1 + 1 := rfl

theorem odd_plus_one_is_even (a : ℕ) (h: is_odd a) : is_even (a + 1) :=
exists.elim h
(assume b, assume hb: 2 * b + 1 = a, show is_even (a + 1), from
exists.intro (b + 1)
(calc
  2 * (b + 1) = 2 * b + 2 * 1 : by rw mul_add
  ... = 2 * b + 1 + 1 : by rw l1
  ... = a + 1 : by rw hb
)
)

theorem even_or_odd (a : ℕ) : (is_even a) ∨ (is_odd a) := sorry

/-

TODO: get library_search working
TODO: avoid using this stupid lemma l1

-/
