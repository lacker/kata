import data.nat.basic
import data.set.basic
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

/-
TODO: perhaps work towards FLT: x^p congruent to x, mod p?
subgoals:

prove these unproved lemmas and theorems, top to bottom

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

lemma bsnib (s : set ℕ) (a n : ℕ) (h : a ∈ bounded_subset s (n+1)) :
a ∈ bounded_subset s n ∨ a = n :=
if h1: a = n then
  or.inr h1
else
  have h2: a < n + 1, from h.right,
  have h3: a ≠ n, from h1,
  have h4: a < n, from array.push_back_idx h2 h1,
  have h5: a ∈ s, from h.left,
  have hc: a ∈ bounded_subset s n, from and.intro h5 h4,
  or.inl hc

lemma bs_containment (s : set ℕ) (n : ℕ) : (bounded_subset s n) ⊆ (bounded_subset s (n+1)) := 
assume x,
assume h : x ∈ bounded_subset s n,
have hc : x ∈ s, from h.left,
have hni : x < (n + 1), from nat.lt.step h.right,
show x ∈ bounded_subset s (n + 1),
from set.mem_sep hc hni

lemma lbbsi (s : set ℕ) (a n : ℕ) (h: lower_bound a (bounded_subset s n)) (ha : a < n) :
lower_bound a (bounded_subset s (n+1)) :=
assume b : ℕ,
assume h1: b ∈ (bounded_subset s (n+1)),
have h2: b ∈ bounded_subset s n ∨ b = n, from bsnib s b n h1,
or.elim h2
  (assume h3: b ∈ bounded_subset s n,
   show a ≤ b, from h b h3)
  (assume h4: b = n,
   have h5: n = b, from eq.symm h4,
   have h6: a < b, from eq.subst h5 ha,
   show a ≤ b, from le_of_lt h6)

lemma isbsi (s : set ℕ) (a n : ℕ) (h : is_smallest a (bounded_subset s n)) :
is_smallest a (bounded_subset s (n+1)) :=
have h1: a ∈ bounded_subset s n, from h.left,
have h2: bounded_subset s n ⊆ bounded_subset s (n+1), from bs_containment s n,
have h3: a ∈ bounded_subset s (n+1), from set.mem_of_subset_of_mem h2 h1,
have h4: lower_bound a (bounded_subset s n), from h.right,
have h5: a < n, from h1.right,
have h6: lower_bound a (bounded_subset s (n+1)), from lbbsi s a n h4 h5,
show is_smallest a (bounded_subset s (n+1)), from and.intro h3 h6

lemma lower_bound_union (s1 s2 : set ℕ) (a1 a2 : ℕ)
(h1 : lower_bound a1 s1) (h2 : lower_bound a2 s2) (h3 : a1 ≤ a2) :
lower_bound a1 (s1 ∪ s2) :=
assume b : ℕ,
assume h4: b ∈ (s1 ∪ s2),
or.elim h4
(assume h5: b ∈ s1, show a1 ≤ b, from h1 b h5)
(assume h6: b ∈ s2,
 have h7: a2 ≤ b, from h2 b h6,
 show a1 ≤ b, from le_trans h3 h7)

lemma is_smallest_union (s1 s2 : set ℕ) (a1 a2 : ℕ)
(h1 : is_smallest a1 s1) (h2 : is_smallest a2 s2) (h3 : a1 ≤ a2) :
is_smallest a1 (s1 ∪ s2) :=
have h4: a1 ∈ (s1 ∪ s2), from set.mem_union_left s2 h1.left,
have h5: lower_bound a1 (s1 ∪ s2), from lower_bound_union s1 s2 a1 a2 h1.right h2.right h3,
and.intro h4 h5

lemma bsnlb (s : set ℕ) (n : ℕ) (h : bounded_subset s n = ∅) : lower_bound n s :=
assume a : ℕ,
assume h1 : a ∈ s,
have h2: a ∉ bounded_subset s n, from not_of_eq_false (congr_arg (has_mem.mem a) h),
have h3: ¬ (a < n), from not_and.mp h2 h1,
show n ≤ a, from not_lt.mp h3

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

theorem well_ordered (s : set ℕ) : s = ∅ ∨ ∃ a, is_smallest a s :=
have h1: s = ∅ ∨ s ≠ ∅, from em(s = ∅),
or.elim h1
  (assume h2: s = ∅, or.inl h2)
  (assume h3: s ≠ ∅,
   have h4: s.nonempty, from set.nmem_singleton_empty.mp h3,
   have h5: ∃ a, a ∈ s, from h4,
   exists.elim h4
     (assume n,
      assume h6: n ∈ s,
      have h7: lower_bound (n+1) s ∨ ∃ a, is_smallest a s, from lbi2 s (n+1),
      or.elim h7
        (assume h8: lower_bound (n+1) s,
         have h9: false, from nlb s n h6 h8,
         false.rec (s = ∅ ∨ ∃ a, is_smallest a s) h9)
        (assume h10: ∃ a, is_smallest a s,
         or.inr h10
         )
     )
)

theorem euclids_lemma (p a b : ℕ) (hp : is_prime p) (hd : divides p (a * b))
: divides p a ∨ divides p b := sorry

