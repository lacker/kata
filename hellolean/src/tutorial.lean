import data.nat.basic
import data.set.basic
import tactic.basic
import tactic.suggest

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

lemma two_times_one: 2 * 1 = 1 + 1 := rfl

theorem odd_plus_one_is_even (a : ℕ) (h: is_odd a) : is_even (a + 1) :=
exists.elim h
(assume b, assume hb: 2 * b + 1 = a, show is_even (a + 1), from
exists.intro (b + 1)
(calc
  2 * (b + 1) = 2 * b + 2 * 1 : by rw mul_add
  ... = 2 * b + 1 + 1 : by rw two_times_one
  ... = a + 1 : by rw hb
)
)

def eoro (a : ℕ) := (is_even a) ∨ (is_odd a)

lemma even_plus_one_eoro (a : ℕ) (h: is_even a) : eoro (a + 1) :=
(or.intro_right (is_even (a + 1)) (even_plus_one_is_odd a h))

lemma odd_plus_one_eoro (a : ℕ) (h: is_odd a) : eoro (a + 1) :=
(or.intro_left (is_odd (a + 1)) (odd_plus_one_is_even a h))

lemma eoro_inducts (a : ℕ) (h: eoro a) : eoro (a + 1) :=
or.elim h
(assume he: is_even a, show eoro (a + 1), from even_plus_one_eoro a he)
(assume ho: is_odd a, show eoro (a + 1), from odd_plus_one_eoro a ho)

lemma zero_eoro : (eoro 0) := or.intro_left (is_odd 0) zero_is_even

theorem all_eoro (n : ℕ) : eoro n :=
nat.rec_on n
(show eoro 0, from zero_eoro)
(assume n,
 assume hn : eoro n,
 show eoro (n + 1),
 from eoro_inducts n hn)

def times_successor (n : ℕ) := n * (n + 1)

theorem even_times_any (a b : ℕ) (h: is_even a) : is_even (a * b) :=
exists.elim h
(assume c, assume hc: 2 * c = a, show is_even (a * b), from
 exists.intro (c * b)
 (calc
  2 * (c * b) = (2 * c) * b : by rw mul_assoc 2 c b
  ... = a * b : by rw hc))

theorem any_times_even (a b : ℕ) (h: is_even b): is_even (a * b) :=
have h1: b * a = a * b, from (mul_comm b a),
have h2: is_even (b * a), from (even_times_any b a h),
h1 ▸ h2

lemma even_tse (a : ℕ) (h: is_even a) : is_even (times_successor a) :=
even_times_any a (a + 1) h

lemma odd_tse (a : ℕ) (h1: is_odd a) : is_even (times_successor a) :=
have h2: is_even (a + 1), from (odd_plus_one_is_even a h1),
any_times_even a (a + 1) h2

theorem times_successor_even (a : ℕ) : is_even (times_successor a) :=
have h: eoro a, from all_eoro a,
or.elim h
(assume he: is_even a, show is_even (times_successor a), from even_tse a he)
(assume ho: is_odd a, show is_even (times_successor a), from odd_tse a ho)

/-
TODO: perhaps work towards FLT: x^p congruent to x, mod p?
subgoals:

prove bounded_smallest
prove any subset of naturals has a smallest element

define gcd
∃ c, d s.t. ac + bd = gcd(a, b)
euclid's lemma
-/

def is_composite (a : ℕ) := ∃ b, ∃ c, b > 1 ∧ c > 1 ∧ b * c = a

def is_prime (p : ℕ) := p > 1 ∧ not (is_composite p)

def divides (a b : ℕ) := ∃ c, a * c = b

def mod : ℕ → ℕ → ℕ
| a m :=
  if h : 0 < m ∧ m ≤ a then
    have ha: 0 < a,
      from lt_of_lt_of_le h.left h.right,
    have a - m < a,
      from nat.sub_lt ha h.left,
    mod (a - m) m
  else
    a

def is_empty (s : set ℕ) := ∀ a : ℕ, a ∉ s
def lower_bound (a : ℕ) (s : set ℕ) := ∀ b : ℕ, b ∈ s → a ≤ b
def strict_lower_bound (a : ℕ) (s : set ℕ) := ∀ b : ℕ, b ∈ s → a < b
def is_smallest (a : ℕ) (s : set ℕ) := a ∈ s ∧ lower_bound a s

def bounded_subset (s : set ℕ) (a : ℕ) := {b : ℕ | b ∈ s ∧ b < a}

theorem not_ltz (a : ℕ) : ¬ (a < 0) := not_lt_bot

lemma bsz_sub_e (s : set ℕ) : bounded_subset s 0 ⊆ ∅ :=
assume x,
assume h : x ∈ bounded_subset s 0,
have h1: x < 0, from h.right,
show x ∈ ∅, from absurd h1 (not_ltz x)

lemma bsz_empty (s : set ℕ) : bounded_subset s 0 = ∅ :=
set.eq_of_subset_of_subset
  (bsz_sub_e s)
  (bounded_subset s 0).empty_subset

def bsn (s : set ℕ) (n : ℕ) :=
(bounded_subset s n) = ∅ ∨ ∃ a : ℕ, is_smallest a (bounded_subset s n)

lemma bsnz (s : set ℕ) : bsn s 0 := or.inl (bsz_empty s)

lemma bounded_smallest_inducts (s : set ℕ) (n : ℕ) (h : bsn s n) : bsn s (n + 1) := sorry

lemma bounded_smallest (s : set ℕ) : ∀ n : ℕ, bsn s n := sorry

theorem euclids_lemma (p a b : ℕ) (hp : is_prime p) (hd : divides p (a * b))
: divides p a ∨ divides p b := sorry

