import data.nat.basic
import data.set.basic
import logic.basic
import tactic.basic
import tactic.suggest
open classical

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
def upper_bound (a : ℕ) (s : set ℕ) := ∀ b : ℕ, b ∈ s → a ≥ b
def is_smallest (a : ℕ) (s : set ℕ) := a ∈ s ∧ lower_bound a s
def is_largest (a : ℕ) (s : set ℕ) := a ∈ s ∧ upper_bound a s

theorem not_ltz (a : ℕ) : ¬ (a < 0) := not_lt_bot

lemma lower_bound_union (s1 s2 : set ℕ) (a1 a2 : ℕ)
(h1: lower_bound a1 s1) (h2: lower_bound a2 s2) (h3 : a1 ≤ a2) :
lower_bound a1 (s1 ∪ s2) :=
assume b : ℕ,
assume h4: b ∈ (s1 ∪ s2),
or.elim h4
(assume h5: b ∈ s1, show a1 ≤ b, from h1 b h5)
(assume h6: b ∈ s2,
 have h7: a2 ≤ b, from h2 b h6,
 show a1 ≤ b, from le_trans h3 h7)

lemma upper_bound_union (s1 s2 : set ℕ) (a1 a2 : ℕ)
(h1: upper_bound a1 s1) (h2: upper_bound a2 s2) (h3 : a1 ≤ a2) :
upper_bound a2 (s1 ∪ s2) :=
assume b : ℕ,
assume h4: b ∈ s1 ∪ s2,
or.elim h4
(assume h5: b ∈ s1,
 have h6: a1 ≥ b, from h1 b h5,
 show a2 ≥ b, from le_trans h6 h3)
(assume h7: b ∈ s2,
 show a2 ≥ b, from h2 b h7)

lemma is_smallest_union (s1 s2 : set ℕ) (a1 a2 : ℕ)
(h1 : is_smallest a1 s1) (h2 : is_smallest a2 s2) (h3 : a1 ≤ a2) :
is_smallest a1 (s1 ∪ s2) :=
have h4: a1 ∈ (s1 ∪ s2), from set.mem_union_left s2 h1.left,
have h5: lower_bound a1 (s1 ∪ s2), from lower_bound_union s1 s2 a1 a2 h1.right h2.right h3,
and.intro h4 h5

lemma inne (s : set ℕ) (a b : ℕ) (ha : a ∈ s) (hb : b ∉ s) : a ≠ b :=
have h1: a = b ∨ a ≠ b, from em(a=b),
or.elim h1
  (assume h2: a = b,
   have h3: b ∈ s, from eq.subst h2 ha,
   show a ≠ b, from absurd h3 hb)
  (assume h4: a ≠ b, show a ≠ b, from h4)

lemma lbih (s : set ℕ) (n : ℕ) (h1 : lower_bound n s) (h2 : n ∉ s) : lower_bound (n+1) s :=
assume b : ℕ,
assume h3 : b ∈ s,
have h4: b ≠ n, from inne s b n h3 h2,
have h5: b ≥ n, from h1 b h3,
have h6: b > n, from lt_of_le_of_ne h5 (ne.symm h4),
show b ≥ n + 1, from h6

lemma lbi1 (s : set ℕ) (n : ℕ) (h : lower_bound n s) : is_smallest n s ∨ lower_bound (n+1) s :=
have h1: n ∈ s ∨ n ∉ s, from em(n ∈ s),
or.elim h1
  (assume h2: n ∈ s,
   have h3: is_smallest n s, from and.intro h2 h,
   or.inl h3)
  (assume h3: n ∉ s,
   have h4: lower_bound (n+1) s, from lbih s n h h3,
   or.inr h4)

lemma lbiz (s : set ℕ) : lower_bound 0 s :=
assume b : ℕ,
assume h: b ∈ s,
show b ≥ 0, from bot_le

lemma lbi2 (s : set ℕ) (n : ℕ) : lower_bound n s ∨ ∃ a, is_smallest a s :=
nat.rec_on n
(or.inl (lbiz s))
(assume n,
 assume h1: lower_bound n s ∨ ∃ a, is_smallest a s,
 or.elim h1
 (assume h2: lower_bound n s,
  have h3: is_smallest n s ∨ lower_bound (n+1) s, from lbi1 s n h2,
  or.elim h3
    (assume h4: is_smallest n s,
     have h5: ∃ a, is_smallest a s, from exists.intro n h4,
     or.inr h5)
    (assume h6: lower_bound (n+1) s,
     or.inl h6)
  )
 (assume ha: ∃ a, is_smallest a s,
  or.inr ha)
)

lemma nlb (s : set ℕ) (n : ℕ) (h1: n ∈ s) (h2: lower_bound (n+1) s) : false := 
have h3: n + 1 ≤ n, from h2 n h1,
have h4: n + 1 > n, from lt_add_one n,
show false, from nat.lt_le_antisymm h4 h3

theorem well_ordered (s : set ℕ) (h1: s.nonempty) : ∃ a, is_smallest a s :=
exists.elim h1
 (assume n,
  assume h2: n ∈ s,
  have h3: lower_bound (n+1) s ∨ ∃ a, is_smallest a s, from lbi2 s (n+1),
  or.elim h3
    (assume h4: lower_bound (n+1) s,
     have h5: false, from nlb s n h2 h4,
     false.rec (∃ a, is_smallest a s) h5)
    (assume h6: ∃ a, is_smallest a s, show ∃ a, is_smallest a s, from h6))

/-
TODO: perhaps work towards FLT: x^p congruent to x, mod p?
subgoals:

prove these unproved lemmas and theorems, top to bottom

define gcd
∃ c, d s.t. ac + bd = gcd(a, b)
euclid's lemma
-/

theorem one_divides (n : ℕ) : divides 1 n :=
have h: 1 * n = n, from one_mul n,
exists.intro n h

def divisors (n : ℕ) := { d : ℕ | divides d n }

theorem divisors_nonempty (n : ℕ) : (divisors n).nonempty :=
have 1 ∈ (divisors n), from one_divides n,
show (divisors n).nonempty, from set.nonempty_of_mem this

lemma divisor_nonzero (a b c : ℕ) (h1 : c > 0) (h2 : a * b = c) : b > 0 :=
have h3: b = 0 ∨ b > 0, from nat.eq_zero_or_pos b,
or.elim h3
  (assume h4: b = 0,
   have h5: a * 0 = 0, from rfl,
   have h6: a * b = 0, from eq.subst (eq.symm h4) h5,
   have h7: c = 0, from eq.subst h2 h6,
   have h8: ¬ (0 > 0), from irrefl 0,
   have h9: ¬ (c > 0), from eq.subst (eq.symm h7) h8,
   absurd h1 h9)
  (assume h10: b > 0,
   h10)

theorem divisors_bounded (n : ℕ) (h : n > 0) : upper_bound n (divisors n) :=
assume a,
assume h1: a ∈ divisors n,
have h2: divides a n, from h1,
have h3: 0 < n, from h,
have h4: ∃ c, a * c = n, from h1,
exists.elim h4
  (assume b,
   assume h5: a * b = n,
   have h6: b > 0, from divisor_nonzero a b n h h5,
   have h7: a ≤ a * b, from nat.le_mul_of_pos_right h6,
   show a ≤ n, from eq.subst h5 h7)

def flip_set (s : set ℕ) (n : ℕ) := { a : ℕ | a ≤ n ∧ n - a ∈ s }

lemma df1 (s : set ℕ) (n : ℕ) : flip_set (flip_set s n) n ⊆ s :=
assume a,
assume h1: a ∈ flip_set (flip_set s n) n,
have h2: a ≤ n, from h1.left,
have h3: n - a ∈ flip_set s n, from h1.right,
have h4: n - (n - a) ∈ s, from h3.right,
have h5: n - (n - a) = a, from nat.sub_sub_self h2,
show a ∈ s, from eq.subst h5 h4

lemma df2 (s : set ℕ) (n : ℕ) (h1 : upper_bound n s) : s ⊆ flip_set (flip_set s n) n :=
assume a,
assume h2: a ∈ s,
have h3: n - a ≤ n, from nat.sub_le n a,
have h4: a ≤ n, from h1 a h2,
have h5: n - (n - a) = a, from nat.sub_sub_self h4,
have h6: n - (n - a) ∈ s, from eq.subst (eq.symm h5) h2,
have h7: n - a ∈ flip_set s n, from and.intro h3 h6,
show a ∈ flip_set (flip_set s n) n, from and.intro h4 h7

def double_flip (s : set ℕ) (n : ℕ) (h1: upper_bound n s) : flip_set (flip_set s n) n = s :=
set.subset.antisymm (df1 s n) (df2 s n h1)

lemma lb_flips (s : set ℕ) (a n : ℕ) (h1: lower_bound a s) :
upper_bound (n - a) (flip_set s n) :=
(assume b,
 assume h2: b ∈ (flip_set s n),
 have h3: n - b ∈ s, from h2.right,
 have h4: a ≤ n - b, from h1 (n-b) h3,
 have h5: b ≤ n, from h2.left,
 have h6: a + b ≤ n, from (nat.add_le_to_le_sub a h5).mpr h4,
 show n - a ≥ b, from nat.le_sub_left_of_add_le h6)

lemma smallest_flips (s : set ℕ) (a n : ℕ) (h1: upper_bound n s) (h2: is_smallest a s) :
is_largest (n-a) (flip_set s n) :=
have h3: a ∈ s, from h2.left,
have h4: n ≥ a, from h1 a h3,
have h5: n - (n - a) = a, from nat.sub_sub_self h4,
have h6: n - (n - a) ∈ s, from set.mem_of_eq_of_mem h5 h3,
have h7: n - a ≤ n, from nat.sub_le n a,
have h8: n - a ∈ (flip_set s n), from and.intro h7 h6,
have h9: upper_bound (n - a) (flip_set s n), from lb_flips s a n h2.right,
and.intro h8 h9

lemma nonempty_flips (s : set ℕ) (n : ℕ) (h1: upper_bound n s) (h2: s.nonempty) :
(flip_set s n).nonempty :=
exists.elim h2
(assume a,
 assume h3: a ∈ s,
 have h4: a ≤ n, from h1 a h3,
 have h5: n - (n - a) = a, from nat.sub_sub_self h4,
 have h6: n - a ≤ n, from nat.sub_le n a,
 have h7: n - (n - a) ∈ s, from eq.subst (eq.symm h5) h3,
 have h6: n - a ∈ flip_set s n, from set.mem_sep h6 h7,
 show (flip_set s n).nonempty, from set.nonempty_of_mem h6)

theorem bounded_has_largest (s : set ℕ) (n : ℕ) (h1: upper_bound n s) (h2: s.nonempty) :
∃ a, is_largest a s :=
have h3: (flip_set s n).nonempty, from nonempty_flips s n h1 h2,
have h4: ∃ x, is_smallest x (flip_set s n), from well_ordered (flip_set s n) h3,
exists.elim h4
(assume b,
 assume h5: is_smallest b (flip_set s n),
 have h6: upper_bound n (flip_set s n), from lb_flips s 0 n (lbiz s),
 have h7: is_largest (n-b) (flip_set (flip_set s n) n),
   from (smallest_flips (flip_set s n) b n h6 h5),
 have h8: flip_set (flip_set s n) n = s, from double_flip s n h1,
 have h9: is_largest (n-b) s, from eq.subst h8 h7,
 show ∃ a, is_largest a s, from exists.intro (n-b) h9)

theorem euclids_lemma (p a b : ℕ) (hp : is_prime p) (hd : divides p (a * b))
: divides p a ∨ divides p b := sorry



