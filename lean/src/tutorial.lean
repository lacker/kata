import data.nat.basic
import data.set.basic
import logic.basic
import tactic.basic
import tactic.suggest
open classical

-- So that we can ignore the difference between computable and uncomputable sets.
-- open_locale classical
-- noncomputable theory

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

theorem composite_divisor_lt (a b c : ℕ) (h1: a * b = c) (h2: a > 1) (h3: b > 1) : a < c :=
have h4: 0 < b, from nat.lt_of_succ_lt h3,
have h5: a ≤ a * b, from nat.le_mul_of_pos_right h4,
have h6: a ≤ c, from eq.subst h1 h5,
have h7: a = c ∨ a ≠ c, from em(a=c),
or.elim h7
 (assume h8: a = c,
  have h9: a * b = a, from (rfl.congr (eq.symm h8)).mp h1,
  have h10: 0 < a, from nat.lt_of_succ_lt h2,
  have h11: b = 1, from (nat.mul_right_eq_self_iff h10).mp h9,
  have h12: b ≠ 1, from ne_of_gt h3,
  absurd h11 h12)
 (assume : a ≠ c,
  show a < c, from lt_of_le_of_ne h6 this)

def is_prime (p : ℕ) := p > 1 ∧ ¬ (is_composite p)

theorem prime_pos (p : ℕ) (h1: is_prime p) : p > 0 :=
have p > 1, from h1.left,
show p > 0, from nat.lt_of_succ_lt this

def divides (a b : ℕ) := ∃ c, a * c = b

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

theorem one_divides (n : ℕ) : divides 1 n :=
have h: 1 * n = n, from one_mul n,
exists.intro n h

theorem divides_zero (n : ℕ) : divides n 0 :=
have h: n * 0 = 0, from rfl,
exists.intro 0 h

theorem divides_nonzero (a b : ℕ) (h1: ¬ divides a b) : b ≠ 0 :=
have h2: b = 0 ∨ b ≠ 0, from (em(b = 0)),
or.elim h2
  (assume h3: b = 0,
   have h4: divides a 0, from divides_zero a,
   have h5: divides a b, from eq.subst (eq.symm h3) h4,
   show b ≠ 0, from absurd h5 h1)
  (assume h6: b ≠ 0, show b ≠ 0, from h6)

def divisors (n : ℕ) := { d : ℕ | divides d n }

theorem divisors_nonempty (n : ℕ) : (divisors n).nonempty :=
have 1 ∈ (divisors n), from one_divides n,
show (divisors n).nonempty, from set.nonempty_of_mem this

lemma rdivisor_nonzero (a b c : ℕ) (h1 : c > 0) (h2 : a * b = c) : b > 0 :=
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

theorem divisors_nonzero (a b c : ℕ) (h1 : c > 0) (h2 : a * b = c) : a > 0 ∧ b > 0 :=
have h3: b > 0, from rdivisor_nonzero a b c h1 h2,
have h4: b * a = c, from eq.subst (mul_comm a b) h2,
have h5: a > 0, from rdivisor_nonzero b a c h1 h4,
and.intro h5 h3

theorem prime_divisors (d p : ℕ) (h1: is_prime p) (h2: divides d p) : d = 1 ∨ d = p :=
have h3: (d = 1 ∨ d = p) ∨ ¬ (d = 1 ∨ d = p), from em(d = 1 ∨ d = p),
or.elim h3
 (assume h4: d = 1 ∨ d = p,
  h4)
 (assume h5: ¬ (d = 1 ∨ d = p),
  have h6: ¬ (d = 1) ∧ ¬ (d = p), from or_imp_distrib.mp h5,
  have h7: d ≠ 1, from h6.left,
  have h8: d ≠ p, from h6.right,
  have h9: p > 1, from h1.left,
  exists.elim h2
   (assume c,
    assume h10: d * c = p,
    have h11: p > 0, from nat.lt_of_succ_lt h9,
    have h12: d > 0 ∧ c > 0, from divisors_nonzero d c p h11 h10,
    have h13: d > 0, from h12.left,
    have h14: d > 1, from lt_of_le_of_ne h13 (ne.symm h7),
    have h15: c > 0, from h12.right,
    have h16: c = 1 ∨ c ≠ 1, from em(c = 1),
    or.elim h16
     (assume h17: c = 1,
      have h18: d * 1 = p, from eq.subst h17 h10,
      have h19: d = p, from eq.subst (mul_one d) h18,
      absurd h19 h8)
     (assume h20: c ≠ 1,
      have h21: c > 1, from lt_of_le_of_ne h15 (ne.symm h20),
      have h22: d > 1 ∧ c > 1 ∧ d * c = p, from and.intro h14 (and.intro h21 h10),
      have h23: is_composite p, from exists.intro d (exists.intro c h22),
      absurd h23 h1.right)))

theorem divisors_bounded (n : ℕ) (h : n > 0) : upper_bound n (divisors n) :=
assume a,
assume h1: a ∈ divisors n,
have h2: divides a n, from h1,
have h3: 0 < n, from h,
have h4: ∃ c, a * c = n, from h1,
exists.elim h4
  (assume b,
   assume h5: a * b = n,
   have h6: b > 0, from rdivisor_nonzero a b n h h5,
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

def common_divisors (a b : ℕ) := (divisors a) ∩ (divisors b)

def is_gcd (d a b : ℕ) := is_largest d (common_divisors a b)

def relatively_prime (a b : ℕ) := is_gcd 1 a b

theorem division (a m : ℕ) (h1: m > 0) : ∃ c : ℕ, ∃ d : ℕ, m * c + d = a ∧ d < m :=
nat.rec_on a
(have h2: m * 0 + 0 = 0, from rfl,
 have h3: m * 0 + 0 = 0 ∧ 0 < m, from and.intro h2 h1,
 have h4: ∃ d : ℕ, m * 0 + d = 0 ∧ d < m, from exists.intro 0 h3,
 show ∃ c : ℕ, ∃ d : ℕ, m * c + d = 0 ∧ d < m, from exists.intro 0 h4)
(assume n,
 assume h5: ∃ c : ℕ, ∃ d : ℕ, m * c + d = n ∧ d < m,
 exists.elim h5
 (assume c,
  assume h6: ∃ d : ℕ, m * c + d = n ∧ d < m,
  exists.elim h6
  (assume d,
   assume h7: m * c + d = n ∧ d < m,
   have h8: d + 1 = m ∨ d + 1 ≠ m, from em(d + 1 = m),
   have h9: m * c + d = n, from h7.left,
   have h10: m * c + d + 1 = n + 1, from congr_fun (congr_arg has_add.add h9) 1,
   or.elim h8
   (assume h11: d + 1 = m,
    have h12: m * (c + 1) + 0 = n + 1, from (congr_arg (has_add.add (m * c)) (eq.symm h11)).trans h10,
    have h13: ∃ f : ℕ, m * (c + 1) + f = n + 1 ∧ f < m, from exists.intro 0 (and.intro h12 h1),
    show ∃ e : ℕ, ∃ f : ℕ, m * e + f = n + 1 ∧ f < m, from exists.intro (c+1) h13)
   (assume h14: d + 1 ≠ m,
    have h15: d < m, from h7.right,
    have h16: d + 1 < m, from lt_of_le_of_ne h15 h14,
    have h17: ∃ f : ℕ, m * c + f = n + 1 ∧ f < m, from exists.intro (d+1) (and.intro h10 h16),
    show ∃ e : ℕ, ∃ f : ℕ, m * e + f = n + 1 ∧ f < m, from exists.intro c h17)
)))

theorem divides_self (n : ℕ) : divides n n :=
have h1: n * 1 = n, from mul_one n,
exists.intro 1 h1

theorem divides_add (d a b : ℕ) (h1: divides d a) (h2: divides d b) : divides d (a + b) :=
exists.elim h1
 (assume e,
  assume h3: d * e = a,
  exists.elim h2
   (assume f,
    assume h4: d * f = b, 
    have h5: d * (e + f) = d * e + d * f, from mul_add d e f,
    have h6: d * (e + f) = a + d * f, from eq.subst h3 h5,
    have h7: d * (e + f) = a + b, from eq.subst h4 h6,
    show divides d (a + b), from exists.intro (e + f) h7))

theorem divides_sub (d a b : ℕ) (h1: divides d a) (h2: divides d b) : divides d (a - b) :=
exists.elim h1
 (assume e,
  assume h3: d * e = a,
  exists.elim h2
   (assume f,
    assume h4: d * f = b, 
    have h5: d * (e - f) = d * e - d * f, from nat.mul_sub_left_distrib d e f,
    have h6: d * (e - f) = a - d * f, from eq.subst h3 h5,
    have h7: d * (e - f) = a - b, from eq.subst h4 h6,
    show divides d (a - b), from exists.intro (e - f) h7))

theorem divides_mul (d a b : ℕ) (h1: divides d a) : divides d (a * b) :=
exists.elim h1
 (assume c,
  assume h2: d * c = a,
  have h3: d * c * b = a * b, from congr_fun (congr_arg has_mul.mul h2) b,
  have h4: d * (c * b) = a * b, from eq.subst (mul_assoc d c b) h3,
  exists.intro (c*b) h4)

theorem divides_trans (a b c : ℕ) (h1: divides a b) (h2: divides b c) : divides a c :=
exists.elim h2
 (assume e,
  assume h3: b * e = c,
  have h4: divides a (b * e), from divides_mul a b e h1,
  show divides a c, from eq.subst h3 h4)

theorem divides_le (a b : ℕ) (h1: divides a b) (h2: b > 0) : a ≤ b :=
exists.elim h1
 (assume c,
  assume h3: a * c = b,
  have h4: c = 0 ∨ c ≠ 0, from em(c = 0),
  or.elim h4
   (assume h5: c = 0,
    have h6: a * 0 = 0, from rfl,
    have h7: a * c = 0, from eq.subst h5.symm h6,
    have h8: b = 0, from eq.subst h3 h7,
    have h9: b ≠ 0, from ne_of_gt h2,
    absurd h8 h9)
   (assume h10: c ≠ 0,
    have h11: 0 < c, from bot_lt_iff_ne_bot.mpr h10,
    have h12: a ≤ a * c, from nat.le_mul_of_pos_right h11,
    eq.subst h3 h12))

def eset (p b : ℕ) (h: is_prime p) := { x : ℕ | x > 0 ∧ divides p (x*b) }

theorem eset_nonempty (p b : ℕ) (h1: is_prime p) : (eset p b h1).nonempty :=
have h2: p > 0, from prime_pos p h1,
have h3: divides p (p*b), from exists.intro b rfl,
have h4: p ∈ (eset p b h1), from and.intro h2 h3,
show (eset p b h1).nonempty, from set.nonempty_of_mem h4

lemma ehelp (a b p x0 x : ℕ) (h1: is_prime p) (h2: is_smallest x0 (eset p b h1)) (h3: x ∈ eset p b h1) :
divides x0 x :=
have h4: x0 > 0, from h2.left.left,
have h5: ∃ q : ℕ, ∃ r : ℕ, x0 * q + r = x ∧ r < x0, from division x x0 h4,
exists.elim h5
 (assume q,
  assume h6: ∃ r : ℕ, x0 * q + r = x ∧ r < x0,
  exists.elim h6
   (assume r,
    assume h7: x0 * q + r = x ∧ r < x0,
    have h8: x - x0 * q = r, from nat.sub_eq_of_eq_add (eq.symm h7.left),
    have h9: (x - x0 * q) * b = r * b, from congr_fun (congr_arg has_mul.mul h8) b,
    have h10: x * b - x0 * q * b = r * b, from eq.subst (nat.mul_sub_right_distrib x (x0*q) b) h9,
    have h11: divides p (x * b), from h3.right,
    have h12: divides p (x0 * b), from h2.left.right,
    have h13: divides p (x0 * b * q), from divides_mul p (x0 * b) q h12,
    have h14: divides p (x0 * (b * q)), from eq.subst (mul_assoc x0 b q) h13,
    have h15: divides p (x0 * (q * b)), from eq.subst (mul_comm b q) h14,
    have h16: divides p (x0 * q * b), from eq.subst (eq.symm (mul_assoc x0 q b)) h15,
    have h17: divides p (x * b - x0 * q * b), from divides_sub p (x * b) (x0 * q * b) h11 h16,
    have h18: divides p (r * b), from eq.subst h10 h17,
    have h19: r = 0 ∨ r ≠ 0, from em(r=0),
    or.elim h19
     (assume h20: r = 0,
      have h21: x0 * q + 0 = x, from eq.subst h20 h7.left,
      have h22: x0 * q = x, from h21,
      show divides x0 x, from exists.intro q h22)
     (assume h23: r ≠ 0,
      have h24: r > 0, from bot_lt_iff_ne_bot.mpr h23,
      have h25: r ∈ eset p b h1, from and.intro h24 h18,
      have h26: r < x0, from h7.right,
      have h27: lower_bound x0 (eset p b h1), from h2.right,
      have h28: x0 ≤ r, from h27 r h25,
      have h29: ¬ (r < x0), from not_lt.mpr h28,
      show divides x0 x, from absurd h26 h29)))

theorem euclids_lemma (p a b : ℕ) (h1 : is_prime p) (h2 : divides p (a * b))
: divides p a ∨ divides p b :=
have h3: divides p a ∨ ¬ divides p a, from em(divides p a),
or.elim h3
 (assume h4: divides p a, or.inl h4)
 (assume h5: ¬ divides p a,
  have h6: (eset p b h1).nonempty, from eset_nonempty p b h1,
  have h7: ∃ x0, is_smallest x0 (eset p b h1), from well_ordered (eset p b h1) h6,
  exists.elim h7
   (assume x0,
    assume h8: is_smallest x0 (eset p b h1),
    have h9: divides p (p * b), from exists.intro b rfl,
    have h10: p ∈ eset p b h1, from and.intro (prime_pos p h1) h9,
    have h11: a ≠ 0, from divides_nonzero p a h5,
    have h12: a > 0, from bot_lt_iff_ne_bot.mpr h11,
    have h13: a ∈ eset p b h1, from and.intro h12 h2,
    have h14: divides x0 p, from ehelp a b p x0 p h1 h8 h10,
    have h15: divides x0 a, from ehelp a b p x0 a h1 h8 h13,
    have h16: x0 = 1 ∨ x0 = p, from prime_divisors x0 p h1 h14,
    or.elim h16
     (assume h17: x0 = 1,
      have h18: divides p (x0 * b), from h8.left.right,
      have h19: 1 * b = b, from one_mul b,
      have h20: x0 * b = b, from eq.subst (eq.symm h17) h19,
      have h21: divides p b, from eq.subst h20 h18,
      or.inr h21)
     (assume h22: x0 = p,
      have h23: divides p a, from eq.subst h22 h15,
      absurd h23 h5)))

def g1_divisors (n : ℕ) := { d : ℕ | d > 1 ∧ divides d n }

theorem smallest_g1_divisor_prime (p n : ℕ) (h1: is_smallest p (g1_divisors n)) : is_prime p :=
have h2: is_composite p ∨ ¬ is_composite p, from em(is_composite p),
have h3: p > 1, from h1.left.left,
or.elim h2
 (assume h3: is_composite p,
  exists.elim h3
   (assume b,
    assume h4: ∃ c, b > 1 ∧ c > 1 ∧ b * c = p,
    exists.elim h4
     (assume c,
      assume h5: b > 1 ∧ c > 1 ∧ b * c = p,
      have h6: divides b p, from exists.intro c h5.right.right,
      have h7: divides b n, from divides_trans b p n h6 h1.left.right,
      have h8: b ∈ g1_divisors n, from and.intro h5.left h7,
      have h9: b < p, from composite_divisor_lt b c p h5.right.right h5.left h5.right.left,
      have h10: p ≤ b, from h1.right b h8,
      have h11: ¬ (b < p), from not_lt.mpr h10,
      absurd h9 h11)))
 (assume hz: ¬ is_composite p, and.intro h3 hz)

theorem g1_divisors_nonempty (n : ℕ) (h1: n > 1) : (g1_divisors n).nonempty :=
have h2: divides n n, from divides_self n,
have h3: n ∈ g1_divisors n, from and.intro h1 h2,
set.nonempty_of_mem h3

theorem has_prime_divisor (n : ℕ) (h1: n > 1) : ∃ p, is_prime p ∧ divides p n :=
have h2: ∃ p, is_smallest p (g1_divisors n),
    from well_ordered (g1_divisors n) (g1_divisors_nonempty n h1),
exists.elim h2
 (assume p,
  assume h2: is_smallest p (g1_divisors n),
  have h3: is_prime p, from smallest_g1_divisor_prime p n h2,
  have h4: divides p n, from h2.left.right,
  exists.intro p (and.intro h3 h4))

def codivisors (a b : ℕ) := {d : ℕ | divides d a ∧ divides d b}

theorem codivisors_comm (a b: ℕ) : codivisors a b = codivisors b a :=
have h1: codivisors a b = divisors a ∩ divisors b, from rfl,
have h2: divisors a ∩ divisors b = divisors b ∩ divisors a,
    from set.inter_comm (divisors a) (divisors b),
have h3: codivisors b a = divisors b ∩ divisors a, from rfl,
by rw [h1, h2, h3.symm]

def coprime (a b : ℕ) := upper_bound 1 (codivisors a b)

theorem coprime_comm (a b: ℕ) (h1: coprime a b) : coprime b a :=
have h2: upper_bound 1 (codivisors a b), from h1,
have h3: upper_bound 1 (codivisors b a), from eq.subst (codivisors_comm a b) h2,
h3

lemma not_coprime (x y : ℕ) (h1: ¬ coprime x y) : ∃ z, z > 1 ∧ divides z x ∧ divides z y :=
have h2: ∃ b : ℕ, ¬ (b ∈ codivisors x y → 1 ≥ b), from classical.not_forall.mp h1,
exists.elim h2
 (assume b,
  assume h4: ¬ (b ∈ codivisors x y → 1 ≥ b),
  have h5: b ∈ codivisors x y ∧ ¬ (1 ≥ b), from classical.not_imp.mp h4,
  have h6: divides b x ∧ divides b y, from h5.left,
  have h7: ¬ (1 ≥ b), from h5.right,
  have h8: b > 1, from not_le.mp h7,
  have h9: b > 1 ∧ divides b x ∧ divides b y, from and.intro h8 h6,
  exists.intro b h9)

lemma div_not_coprime (p a b: ℕ) (h1: is_prime p) (h2: divides p a) (h3: divides p b) :
¬ coprime a b :=
have h4: p > 1, from h1.left,
have h5: p ∈ codivisors a b, from set.mem_sep h2 h3,
have h6: coprime a b ∨ ¬ coprime a b, from em(coprime a b),
or.elim h6
 (assume h7: coprime a b,
  have h8: 1 ≥ p, from h7 p h5,
  have h9: ¬ (p > 1), from not_lt.mpr h8,
  absurd h4 h9)
 (assume: ¬ coprime a b, this)

theorem single_cofactor (a b : ℕ) (h1: a > 0) (h2: b > 0) :
coprime a b ∨ ∃ p, is_prime p ∧ divides p a ∧ divides p b :=
have h3: coprime a b ∨ ¬ coprime a b, from em(coprime a b),
or.elim h3
 (assume h4: coprime a b,
  or.inl h4)
 (assume h5: ¬ coprime a b,
  have h6: ∃ d : ℕ, d > 1 ∧ divides d a ∧ divides d b, from not_coprime a b h5,
  exists.elim h6
   (assume d,
    assume h7: d > 1 ∧ divides d a ∧ divides d b,
    have h8: ∃ p, is_prime p ∧ divides p d, from has_prime_divisor d h7.left,
    exists.elim h8
     (assume p,
      assume h9: is_prime p ∧ divides p d,
      have h10: divides p a, from divides_trans p d a h9.right h7.right.left,
      have h11: divides p b, from divides_trans p d b h9.right h7.right.right,
      or.inr (exists.intro p (and.intro h9.left (and.intro h10 h11))))))

theorem coprime_mult (a b c: ℕ) (h1: a > 0) (h2: b > 0) (h3: c > 0)
(h4: coprime a b) (h5: coprime a c) :
coprime a (b*c) :=
have h6: b*c > 0, from mul_pos h2 h3,
have h7: coprime a (b*c) ∨ ∃ p, is_prime p ∧ divides p a ∧ divides p (b*c),
    from single_cofactor a (b*c) h1 h6,
or.elim h7
 (assume: coprime a (b*c), this)
 (assume h8: ∃ p, is_prime p ∧ divides p a ∧ divides p (b*c),
  exists.elim h8
   (assume p,
    assume h9: is_prime p ∧ divides p a ∧ divides p (b*c),
    have h10: divides p b ∨ divides p c, from euclids_lemma p b c h9.left h9.right.right,
    or.elim h10
     (assume h11: divides p b,
      have h12: ¬ coprime a b, from div_not_coprime p a b h9.left h9.right.left h11,
      absurd h4 h12)
     (assume h13: divides p c,
      have h14: ¬ coprime a c, from div_not_coprime p a c h9.left h9.right.left h13,
      absurd h5 h14)))

theorem coprime_nonzero (a b: ℕ) (h1: a > 1) (h2: coprime a b) : b > 0 :=
have h3: b = 0 ∨ b ≠ 0, from em(b = 0),
or.elim h3
 (assume h4: b = 0, 
  have h5: divides a 0, from divides_zero a,
  have h6: divides a b, from eq.subst h4.symm h5,
  have h7: divides a a, from divides_self a,
  have h8: a ∈ codivisors a b, from set.mem_sep h7 h6,
  have h9: 1 ≥ a, from h2 a h8,
  have h10: ¬ (a > 1), from not_lt.mpr h9,
  absurd h1 h10)
 (assume h11: b ≠ 0,
  bot_lt_iff_ne_bot.mpr h11)

def linear_combo (a b : ℕ) := { e : ℕ | ∃ c : ℕ, ∃ d : ℕ, a * c = b * d + e }

theorem lc_left (a b : ℕ) : a ∈ linear_combo a b :=
have h1: a * 1 = b * 0 + a, from rfl,
exists.intro 1 (exists.intro 0 h1)

theorem lc_right (a b : ℕ) (h1: a > 0) : b ∈ linear_combo a b :=
have h2: b*(a-1) + b = b * (a-1) + b, from rfl,
have h3: b*(a-1) = b*a - b, from nat.mul_pred_right b (nat.sub a 0),
have h4: b*a - b + b = b * (a-1) + b, from eq.subst h3 h2,
have h5: b ≤ b*a, from nat.le_mul_of_pos_right h1,
have h6: b*a - b + b = b*a + b - b, from nat.sub_add_eq_add_sub h5,
have h7: b*a + b - b = b*a, from (b*a).add_sub_cancel b,
have h8: a * b = b * a, from mul_comm a b,
have h9: a * b = b * (a-1) + b, by rw [h8, h7.symm, h6.symm, h4],
exists.intro b (exists.intro (a-1) h9)

theorem lc_zero (a b : ℕ) : 0 ∈ linear_combo a b :=
have h1: a * 0 = b * 0 + 0, from rfl,
exists.intro 0 (exists.intro 0 h1)

theorem lc_mul (a b x y : ℕ) (h1: x ∈ linear_combo a b) : x * y ∈ linear_combo a b :=
exists.elim h1
 (assume c, assume : ∃ d, a * c = b * d + x,
  exists.elim this
   (assume d,
    assume h2: a * c = b * d + x,
    have h3: (b*d+x)*y = b*d*y + x*y, from add_mul (b*d) x y,
    have h4: a*c*y = b*d*y + x*y, from eq.subst h2.symm h3,
    have h5: a*(c*y) = b*d*y + x*y, from eq.subst (mul_assoc a c y) h4,
    have h6: a*(c*y) = b*(d*y) + x*y, from eq.subst (mul_assoc b d y) h5,
    exists.intro (c*y) (exists.intro (d*y) h6)))

lemma sub_to_zero (a b : ℕ) (h1: a > b) : b - a = 0 :=
have h2: b ≤ a, from le_of_lt h1,
have h3: b - a ≤ a - a, from nat.sub_le_sub_right h2 a,
have h4: a - a = 0, from nat.sub_self a,
have h5: b - a ≤ 0, from eq.subst h4 h3,
eq_bot_iff.mpr h5

lemma lc_minus_bx (a b e x : ℕ) (h1: e ∈ linear_combo a b) :
(e - b*x) ∈ linear_combo a b :=
exists.elim h1
 (assume c, assume : ∃ d, a * c = b * d + e,
  exists.elim this
   (assume d,
    assume h2: a * c = b * d + e,
    have h3: b*x + e - b*x = e, from nat.sub_eq_of_eq_add rfl,
    have h4: a * c = b * d + (b*x + e - b*x), from eq.subst h3.symm h2,
    have h5: b*x > e ∨ ¬ (b*x > e), from em(b*x > e),
    or.elim h5
     (assume h6: b*x > e,
      have h7: e - b*x = 0, from sub_to_zero (b*x) e h6,
      eq.subst h7.symm (lc_zero a b))
     (assume h8: ¬ (b*x > e),
      have h9: b*x ≤ e, from not_lt.mp h8,
      have h10: b*x + e - b*x = b*x + (e - b*x), from nat.add_sub_assoc h9 (b*x),
      have h11: a * c = b * d + (b*x + (e-b*x)), from eq.subst h10 h4,
      have h12: a * c = (b * d + b * x) + (e-b*x), by rw [h11, add_assoc],
      have h13: b * d + b * x = b * (d + x), from (mul_add b d x).symm,
      have h14: a * c = b * (d + x) + (e-b*x), from eq.subst h13 h12,
      exists.intro c (exists.intro (d + x) h14))))

lemma lc_minus_ax (a b e x : ℕ) (h1: e ∈ linear_combo a b) : e - a*x ∈ linear_combo a b :=
exists.elim h1
 (assume c, assume : ∃ d : ℕ, a * c = b * d + e,
  exists.elim this
   (assume d,
    assume h4: a * c = b * d + e,
    have h5: a * (c - x) = a * c - a * x, from nat.mul_sub_left_distrib a c x,
    have h6: a * (c - x) = (b * d + e) - a*x, from eq.subst h4 h5,
    have h7: a*x > e ∨ ¬ (a*x > e), from em(a*x > e),
    or.elim h7
     (assume h8: a*x > e,
      have h9: e - a*x = 0, from sub_to_zero (a*x) e h8,
      eq.subst h9.symm (lc_zero a b))
     (assume h10: ¬ (a * x > e),
      have h11: a*x ≤ e, from not_lt.mp h10,
      have h12: (b * d + e) - a*x = b*d + (e - a*x), from nat.add_sub_assoc h11 (b*d),
      have h13: a * (c - x) = b*d + (e - a*x), from eq.subst h12 h6,
      exists.intro (c-x) (exists.intro d h13))))

theorem lc_add (a b c d : ℕ) (h1: c ∈ linear_combo a b) (h2: d ∈ linear_combo a b) :
(c + d) ∈ linear_combo a b :=
exists.elim h1
 (assume e, assume : ∃ f : ℕ, a * e = b * f + c, 
  exists.elim this
   (assume f,
    assume h3: a * e = b * f + c,
    exists.elim h2
     (assume g, assume : ∃ h : ℕ, a * g = b * h + d,
      exists.elim this
       (assume h,
        assume h4: a * g = b * h + d,
        have h5: a * e + a * g = a * e + a * g, from rfl,
        have h6: a * e + a * g = b * f + c + a * g, from eq.subst h3 h5,
        have h7: a*e + a*g = b*f + c + (b*h + d), from eq.subst h4 h6,
        have h8: a*(e+g) = b*f + c + (b*h + d), from eq.subst (mul_add a e g).symm h7,
        have h9: b*f + c + (b*h + d) = (b*f + b*h) + (c+d),
            from add_add_add_comm (b*f) c (b*h) d,
        have h10: a*(e+g) = (b*f + b*h) + (c+d), from eq.subst h9 h8,
        have h11: a*(e+g) = b*(f+h) + (c+d), from eq.subst (mul_add b f h).symm h10,
        exists.intro (e+g) (exists.intro (f+h) h11)))))

lemma lc_comm_subset (a b : ℕ) (h1: b > 0) : linear_combo a b ⊆ linear_combo b a :=
assume e,
assume h2: e ∈ linear_combo a b,
exists.elim h2
 (assume c, assume : ∃ d, a*c = b*d + e,
  exists.elim this
   (assume d,
    assume h3: a*c = b*d + e,
    have h4: e = a*c - b*d, from (nat.sub_eq_of_eq_add h3).symm,
    have h5: a ∈ linear_combo b a, from lc_right b a h1,
    have h6: a*c ∈ linear_combo b a, from lc_mul b a a c h5,
    have h7: a*c - b*d ∈ linear_combo b a, from lc_minus_ax b a (a*c) d h6,
    eq.subst h4.symm h7))

theorem lc_comm (a b : ℕ) (h1: a > 0) (h2: b > 0) : linear_combo a b = linear_combo b a :=
set.eq_of_subset_of_subset
 (lc_comm_subset a b h2)
 (lc_comm_subset b a h1)

theorem lc_a_minus (a b e : ℕ) (ha: a > 0) (hb: b > 0) (h1: e ∈ linear_combo a b) :
a - e ∈ linear_combo a b :=
exists.elim h1
 (assume c, assume : ∃ d, a*c = b*d + e,
  exists.elim this
   (assume d,
    assume h2: a*c = b*d + e,
    have h3: a*c - e = a*c - e, from rfl,
    have h4: b*d + e - e = a*c - e, from eq.subst h2 h3,
    have h5: b*d + e - e = b*d, from (b*d).add_sub_cancel e,
    have h6: b*d = a*c - e, from eq.subst h5 h4,
    have h7: a*(c-1) = a*c - a*1, from nat.mul_sub_left_distrib a c 1,
    have h8: a*(c-1) = a*c - a, by rw [h7, mul_one],
    have h9: a*(c-1) + a = a*c - a + a, from congr (congr_arg has_add.add h8) rfl,
    have h10: c = 0 ∨ c ≠ 0, from em(c=0),
    or.elim h10
     (assume h11: c = 0,
      have h12: a*0 = 0, from rfl,
      have h13: a*c = 0, from eq.subst h11.symm h12,
      have h14: 0 = b*d + e, from eq.subst h13 h2,
      have h15: e ≤ b*d + e, from nat.le_add_left e (b*d),
      have h16: e ≤ 0, from eq.subst h14.symm h15,
      have h17: e = 0, from eq_bot_iff.mpr h16,
      have h18: a - 0 = a, from rfl,
      have h19: a - e = a, from eq.subst h17.symm h18,
      eq.subst h19.symm (lc_left a b))
     (assume h20: c ≠ 0,
      have h21: c ≥ 1, from bot_lt_iff_ne_bot.mpr h20,
      have h22: a*c ≥ a, from nat.le_mul_of_pos_right h21,
      have h23: a*c - a + a = a*c, from nat.sub_add_cancel h22,
      have h24: a*(c-1) + a = a*c, by rw [h9, h23],
      have h25: b*d = a*(c-1) + a - e, from eq.subst h24.symm h6,
      have h26: e > a ∨ ¬ (e > a), from em(e > a),
      or.elim h26
       (assume h27: e > a,
        have h28: a - e = 0, from sub_to_zero e a h27,
        eq.subst h28.symm (lc_zero a b))
       (assume h29: ¬ e > a,
        have h30: e ≤ a, from not_lt.mp h29,
        have h31: a*(c-1) + a - e = a*(c-1) + (a-e), from nat.add_sub_assoc h30 (a*(c-1)),
        have h32: b*d = a*(c-1) + (a-e), from eq.subst h31 h25,
        have h33: (a-e) ∈ linear_combo b a, from exists.intro d (exists.intro (c-1) h32),
        eq.subst (lc_comm b a hb ha) h33))))

def pos_linear_combo (a b : ℕ) := { e : ℕ | e > 0 ∧ e ∈ linear_combo a b }

lemma plc_nonempty (a b : ℕ) (h1: a > 0) : (pos_linear_combo a b).nonempty :=
have h2: a ∈ linear_combo a b, from lc_left a b,
have h3: a ∈ pos_linear_combo a b, from and.intro h1 h2,
set.nonempty_of_mem h3

lemma plc_comm_subset (a b : ℕ) (h1: a > 0) (h2: b > 0) : pos_linear_combo a b ⊆ pos_linear_combo b a :=
assume e,
assume h3: e ∈ pos_linear_combo a b,
have h4: e ∈ linear_combo b a, from eq.subst (lc_comm a b h1 h2) h3.right,
and.intro h3.left h4

theorem plc_comm (a b : ℕ) (h1: a > 0) (h2: b > 0) : pos_linear_combo a b = pos_linear_combo b a :=
set.eq_of_subset_of_subset
 (plc_comm_subset a b h1 h2)
 (plc_comm_subset b a h2 h1)

lemma bezdiv (a b s : ℕ) (h1: a > 0) (h2: b > 0) (h3: is_smallest s (pos_linear_combo a b)) : divides s a :=
exists.elim (division a s h3.left.left)
 (assume q, assume : ∃ r : ℕ, s * q + r = a ∧ r < s,
  exists.elim this
   (assume r,
    assume h6: s * q + r = a ∧ r < s,
    have h7: r = 0 ∨ ¬ r = 0, from em(r=0),
    or.elim h7
     (assume h8: r = 0,
      have h9: s * q + 0 = a, from eq.subst h8 h6.left,
      have h10: s * q = a, from h9,
      exists.intro q h10)
     (assume h11: ¬ r = 0,
      have h12: r > 0, from bot_lt_iff_ne_bot.mpr h11,
      have h13: a - s*q = r, from nat.sub_eq_of_eq_add (h6.left.symm),
      have h14: (s*q) ∈ linear_combo a b, from lc_mul a b s q h3.left.right,
      have h15: (a - s*q) ∈ linear_combo a b, from lc_a_minus a b (s*q) h1 h2 h14,
      have h16: r ∈ linear_combo a b, from eq.subst h13 h15,
      have h17: r ∈ pos_linear_combo a b, from and.intro h12 h16,
      have h18: s ≤ r, from h3.right r h17,
      have h19: ¬ (r < s), from not_lt.mpr h18,
      absurd h6.right h19)))

theorem bezout (a b : ℕ) (h1: a > 0) (h2: b > 0) (h3: coprime a b) : 1 ∈ linear_combo a b :=
have h4: (pos_linear_combo a b).nonempty, from plc_nonempty a b h1,
have h5: ∃ s, is_smallest s (pos_linear_combo a b), from well_ordered (pos_linear_combo a b) h4,
exists.elim h5
 (assume s,
  assume h6: is_smallest s (pos_linear_combo a b),
  have h7: divides s a, from bezdiv a b s h1 h2 h6,
  have h8: is_smallest s (pos_linear_combo b a), from eq.subst (plc_comm a b h1 h2) h6,
  have h9: divides s b, from bezdiv b a s h2 h1 h8,
  have h10: s ∈ codivisors a b, from and.intro h7 h9,
  have h11: 1 ≥ s, from h3 s h10,
  have h12: s > 0, from h6.left.left,
  have h13: s = 1, from le_antisymm h11 h12,
  eq.subst h13 h6.left.right)

def mod : ℕ → ℕ → ℕ
| a m :=
  if h1 : m ≥ 1 ∧ m ≤ a then
    have a - m < a, from nat.sub_lt (le_trans h1.left h1.right) h1.left,
    mod (a-m) m
  else
    a
   
lemma mdl (a m : ℕ) (h: m ≥ 1 ∧ m ≤ a) : mod a m = mod (a-m) m := by rw [mod, if_pos h]

lemma mdr (a m : ℕ) (h: ¬ (m ≥ 1 ∧ m ≤ a)) : mod a m = a := by rw [mod, if_neg h]

def counterexamples_mod_less (m : ℕ) := { a : ℕ | mod a m ≥ m }

theorem mod_zero (a: ℕ) : mod a 0 = a :=
have h1: ¬ (0 ≥ 1 ∧ 0 ≤ a), from of_to_bool_ff rfl,
mdr a 0 h1

theorem mod_less (a m : ℕ) (h1: m > 0) : mod a m < m :=
have h2: (mod a m < m) ∨ ¬ (mod a m < m), from em(mod a m < m),
or.elim h2
 (assume : mod a m < m, this)
 (assume h3: ¬ (mod a m < m),
  have h4: mod a m ≥ m, from not_lt.mp h3,
  have h5: (counterexamples_mod_less m).nonempty, from set.nonempty_of_mem h4,
  have h6: ∃ s, is_smallest s (counterexamples_mod_less m),
      from well_ordered (counterexamples_mod_less m) h5,
  exists.elim h6
   (assume s,
    assume h7: is_smallest s (counterexamples_mod_less m),
    have h8: m ≤ s ∨ ¬ (m ≤ s), from em(m ≤ s),
    or.elim h8
     (assume h9: m ≤ s,
      have h10: m ≥ 1 ∧ m ≤ s, from and.intro h1 h9,
      have h11: mod s m = mod (s-m) m, from mdl s m h10,
      have h12: mod (s-m) m ≥ m, from eq.subst h11 h7.left,
      have h13: s - m ≥ s, from h7.right (s-m) h12,
      have h14: s - m < s, from nat.sub_lt_of_pos_le m s h1 h9,
      have h15: ¬ (s - m < s), from not_lt.mpr h13,
      absurd h14 h15)
     (assume h16: ¬ (m ≤ s),
      have h17: ¬ (m ≥ 1 ∧ m ≤ s), from not_and_of_not_right (m ≥ 1) h16,
      have h18: mod s m = s, from mdr s m h17,
      have h19: ¬ (mod s m ≥ m), from eq.subst h18.symm h16,
      absurd h7.left h19)))

theorem mod_cyclic (a m : ℕ) : mod (a + m) m = mod a m :=
have h1: m = 0 ∨ m ≠ 0, from em(m=0),
or.elim h1
 (assume h2: m = 0,
  have h3: a + 0 = a, from rfl,
  have h4: a + m = a, from eq.subst h2.symm h3,
  show mod (a+m) m = mod a m, by rw [h4])
 (assume h5: m ≠ 0,
  have h6: m ≥ 1, from bot_lt_iff_ne_bot.mpr h5,
  have h7: m ≤ a + m, from nat.le_add_left m a,
  have h8: mod (a+m) m = mod (a+m-m) m, from mdl (a+m) m (and.intro h6 h7),
  have h9: a+m-m = a, from nat.add_sub_cancel a m,
  show mod (a+m) m = mod a m, by rw [h8, h9])

theorem mod_rem (a m r : ℕ) : mod (a*m + r) m = mod r m :=
nat.rec_on a
 (show mod (0*m + r) m = mod r m, by rw [zero_mul, zero_add])
 (assume a,
  assume h1: mod (a*m + r) m = mod r m,
  have h2: mod ((a+1)*m + r) m = mod (a*m + r + m) m,
      by rw [add_mul, one_mul, add_assoc, (add_comm m r), add_assoc],
  have h3: mod (a*m + r + m) m = mod (a*m + r) m, from mod_cyclic (a*m+r) m,
  have h4: mod (a*m + r + m) m = mod r m, from eq.subst h1 h3,
  eq.subst h4 h2)

theorem mod_base (a m : ℕ) (h1: a < m) : mod a m = a :=
have h2: ¬ (m ≤ a), from not_le.mpr h1,
have h3: ¬ (m ≥ 1 ∧ m ≤ a), from not_and_of_not_right (m ≥ 1) h2,
mdr a m h3

lemma mod_div_pos (a m: ℕ) (h1: m > 0) : ∃ q, m*q + mod a m = a :=
have h2: ∃ c, ∃ d, m*c + d = a ∧ d < m, from division a m h1,
exists.elim h2
 (assume c,
  assume: ∃ d, m*c + d = a ∧ d < m, 
  exists.elim this
   (assume d,
    assume h3: m*c + d = a ∧ d < m,
    have h4: c*m + d = a, from eq.subst (mul_comm m c) h3.left,
    have h5: mod (c*m + d) m = mod d m, from mod_rem c m d,
    have h6: mod a m = mod d m, from eq.subst h4 h5,
    have h7: mod d m = d, from mod_base d m h3.right,
    have h8: mod a m = d, by rw [h6, h7],
    have h9: m*c + mod a m = a, from eq.subst h8.symm h3.left,
    exists.intro c h9))

theorem mod_div (a m: ℕ) : ∃ q, m*q + mod a m = a :=
have h1: m = 0 ∨ m ≠ 0, from em(m = 0),
or.elim h1
 (assume h2: m = 0,
  have h3: mod a m = a, from eq.subst h2.symm (mod_zero a),
  have h4: m*1 + a = a, from eq.subst h2.symm (mul_one a),
  have h5: m*1 + mod a m = a, from eq.subst h3.symm h4,
  exists.intro 1 h5)
 (assume h6: m ≠ 0,
  have h7: m > 0, from bot_lt_iff_ne_bot.mpr h6,
  mod_div_pos a m h7)

theorem zero_mod_divides (a m: ℕ) (h1: mod a m = 0) : divides m a :=
have h2: ∃ q, m*q + mod a m = a, from mod_div a m,
exists.elim h2
 (assume q,
  assume h3: m*q + mod a m = a,
  have h4: m*q + 0 = a, from eq.subst h1 h3,
  have h5: m*q = a, from h4,
  exists.intro q h5)

theorem mod_nondivisor (a m: ℕ) (h1: ¬ divides m a) : mod a m > 0 :=
have h2: mod a m = 0 ∨ mod a m ≠ 0, from em(mod a m = 0),
or.elim h2
 (assume h3: mod a m = 0,
  have h4: divides m a, from zero_mod_divides a m h3,
  absurd h4 h1)
 (assume: mod a m ≠ 0,
  bot_lt_iff_ne_bot.mpr this)

def range (n : ℕ) := { x : ℕ | x < n }

def surj (s1 s2 : set ℕ) (f : ℕ → ℕ) := ∀ x2: ℕ, x2 ∈ s2 → ∃ x1: ℕ, x1 ∈ s1 ∧ f x1 = x2

def covers (s1 s2 : set ℕ) := ∃ f: ℕ → ℕ, surj s1 s2 f

def bijects (s1 s2 : set ℕ) := covers s1 s2 ∧ covers s2 s1

def has_size (s : set ℕ) (n : ℕ) := bijects (range n) s

theorem bijects_comm (s1 s2 : set ℕ) (h: bijects s1 s2) : bijects s2 s1 :=
and.intro h.right h.left

def nat_id (n : ℕ) := n

theorem superset_covers (s1 s2 : set ℕ) (h1: s1 ⊇ s2) : covers s1 s2 :=
have h2: surj s1 s2 nat_id ∨ ¬ (surj s1 s2 nat_id), from em(surj s1 s2 nat_id),
or.elim h2
 (assume: surj s1 s2 nat_id, exists.intro nat_id this)
 (assume h3: ¬ (surj s1 s2 nat_id),
  have h4: ∃ x2 : ℕ, ¬ (x2 ∈ s2 → ∃ x1: ℕ, x1 ∈ s1 ∧ nat_id x1 = x2),
      from classical.not_forall.mp h3,
  exists.elim h4
   (assume x2,
    assume h5: ¬ (x2 ∈ s2 → ∃ x1: ℕ, x1 ∈ s1 ∧ nat_id x1 = x2),
    have h6: x2 ∈ s2 ∧ ¬ (∃ x1: ℕ, x1 ∈ s1 ∧ nat_id x1 = x2), from classical.not_imp.mp h5,
    have h7: nat_id x2 = x2, from rfl,
    have h8: x2 ∈ s1, from set.mem_of_mem_of_subset h6.left h1,
    have h9: ∃ x1: ℕ, x1 ∈ s1 ∧ nat_id x1 = x2, from exists.intro x2 (and.intro h8 h7),
    absurd h9 h6.right))

theorem covers_rfl (s : set ℕ) : covers s s :=
have h1: s ⊆ s, from set.subset.refl s,
superset_covers s s h1

theorem bijects_refl (s : set ℕ) : bijects s s :=
have h1: s ⊆ s, from set.subset.refl s,
have h2: covers s s, from superset_covers s s h1,
and.intro h2 h2

lemma rzse : range 0 ⊆ ∅ :=
assume x,
assume h1: x ∈ range 0,
have h2: x < 0, from h1,
have h3: ¬ (x < 0), from not_ltz x,
show x ∈ ∅, from absurd h2 h3

theorem range_zero : range 0 = ∅ := set.eq_empty_of_subset_empty rzse

theorem range_size (n: ℕ) : has_size (range n) n := bijects_refl (range n)

theorem range_subset (a b : ℕ) (h1: a ≤ b) : range a ⊆ range b :=
assume x,
assume h2: x ∈ range a,
have h3: x < b, from lt_of_lt_of_le h2 h1,
show x ∈ range b, from h3

theorem empty_size : has_size ∅ 0 := eq.subst range_zero (range_size 0)

theorem surj_trans (s1 s2 s3 : set ℕ) (f1 f2 : ℕ → ℕ)
(h1: surj s1 s2 f1) (h2: surj s2 s3 f2) :
surj s1 s3 (f2 ∘ f1) :=
assume x3,
assume h3: x3 ∈ s3,
have h4: ∃ x2: ℕ, x2 ∈ s2 ∧ f2 x2 = x3, from h2 x3 h3,
exists.elim h4
 (assume x2,
  assume h5: x2 ∈ s2 ∧ f2 x2 = x3,
  have h6: ∃ x1: ℕ, x1 ∈ s1 ∧ f1 x1 = x2, from h1 x2 h5.left,
  exists.elim h6
   (assume x1,
    assume h7: x1 ∈ s1 ∧ f1 x1 = x2,
    have h8: (f2 ∘ f1) x1 = x3, from eq.subst h5.right (congr_arg f2 h7.right),
    exists.intro x1 (and.intro h7.left h8)))

theorem covers_trans (s1 s2 s3 : set ℕ) (h1: covers s1 s2) (h2: covers s2 s3) :
covers s1 s3 :=
exists.elim h1
 (assume f1,
  assume h3: surj s1 s2 f1,
  exists.elim h2
   (assume f2,
    assume h4: surj s2 s3 f2,
    have h5: surj s1 s3 (f2 ∘ f1), from surj_trans s1 s2 s3 f1 f2 h3 h4,
    exists.intro (f2 ∘ f1) h5))

theorem bijects_trans (s1 s2 s3 : set ℕ) (h1: bijects s1 s2) (h2: bijects s2 s3) :
bijects s1 s3 :=
have h3: covers s1 s3, from covers_trans s1 s2 s3 h1.left h2.left,
have h4: covers s3 s1, from covers_trans s3 s2 s1 h2.right h1.right,
and.intro h3 h4

def single (n: ℕ) := {x | x = n}

theorem range_one : range 1 = single 0 :=
set.eq_of_subset_of_subset
 (assume x,
  assume h1: x ∈ range 1,
  have h2: x ≤ 0, from nat.lt_succ_iff.mp h1,
  have h3: x = 0, from eq_bot_iff.mpr h2,
  show x ∈ single 0, from h3)
 (assume x,
  assume h4: x ∈ single 0,
  have h5: x < 1, from eq.subst (h4.symm) (lt_add_one 0),
  show x ∈ range 1, from h5)

theorem single_covers (a b : ℕ) : covers (single a) (single b) :=
have h1: ∃ x1: ℕ, x1 ∈ single a ∧ (λ x: ℕ, b) a = b, from exists_eq_left.mpr rfl,
have h2: ∀ x2: ℕ, x2 ∈ single b → ∃ x1: ℕ, x1 ∈ single a ∧ (λ x: ℕ, b) a = x2, from
 (assume x2,
  assume h3: x2 ∈ single b,
  have h4: x2 = b, from h3,
  eq.subst h4.symm h1),
have h5: surj (single a) (single b) (λ x: ℕ, b), from h2,
exists.intro (λ x : ℕ, b) h5

theorem single_bijects (a b : ℕ) : bijects (single a) (single b) :=
and.intro (single_covers a b) (single_covers b a)

theorem single_size (a: ℕ) : has_size (single a) 1 := 
have h1: bijects (single 0) (single a), from single_bijects 0 a,
have h2: bijects (range 1) (single a), from eq.subst range_one.symm h1,
h2

theorem bijects_size (s1 s2 : set ℕ) (h1: bijects s1 s2) (n: ℕ) (h2: has_size s1 n) :
has_size s2 n :=
have h3: bijects (range n) s1, from h2,
have h4: bijects (range n) s2, from bijects_trans (range n) s1 s2 h3 h1,
h4

theorem surj_empty (s : set ℕ) (f : ℕ → ℕ) : surj s (∅: set ℕ) f :=
assume x2: ℕ,
assume h1: x2 ∈ (∅: set ℕ),
have h2: x2 ∉ (∅: set ℕ), from not_false,
absurd h1 h2

theorem covers_empty (s : set ℕ) : covers s (∅: set ℕ) :=
have h1: surj s (∅: set ℕ) nat_id, from surj_empty s nat_id,
exists.intro nat_id h1

theorem surj_nonempty (s1 s2: set ℕ) (f: ℕ → ℕ) (h1: surj s1 s2 f) (h2: s2.nonempty) :
s1.nonempty :=
have h3: ∃ x2: ℕ, x2 ∈ s2, from h2,
exists.elim h3
 (assume x2,
  assume h4: x2 ∈ s2,
  have h5: ∃ x1: ℕ, x1 ∈ s1 ∧ f x1 = x2, from h1 x2 h4,
  exists.elim h5
   (assume x1,
    assume h6: x1 ∈ s1 ∧ f x1 = x2,
    set.nonempty_of_mem h6.left))

theorem empty_surj (s : set ℕ) (f : ℕ → ℕ) (h1: surj (∅: set ℕ) s f) : s = ∅ :=
have h2: s = ∅ ∨ s.nonempty, from set.eq_empty_or_nonempty s,
or.elim h2
 (assume: s = ∅, this)
 (assume h3: s.nonempty,
  have h4: (∅: set ℕ).nonempty, from surj_nonempty ∅ s f h1 h3,
  absurd h4 exists_false)

theorem empty_covers (s : set ℕ) (h1: covers (∅: set ℕ) s) : s = ∅ :=
exists.elim h1
 (assume f: ℕ → ℕ,
  assume h2: surj (∅: set ℕ) s f,
  empty_surj s f h2)

theorem size_zero_empty (s: set ℕ) (h1: has_size s 0) : s = ∅ :=
have h2: covers (range 0) s, from h1.left,
have h3: covers ∅ s, from eq.subst range_zero h2,
empty_covers s h3

theorem covers_nonempty (s1 s2: set ℕ) (h1: covers s1 s2) (h2: s2.nonempty) :
s1.nonempty :=
exists.elim h1
 (assume f: ℕ → ℕ,
  assume h3: surj s1 s2 f,
  surj_nonempty s1 s2 f h3 h2)

theorem bijects_empty (s: set ℕ) (h1: bijects s ∅) : s = ∅ :=
empty_covers s h1.right

theorem bijects_nonempty (s1 s2: set ℕ) (h1: bijects s1 s2) (h2: s2.nonempty) :
s1.nonempty :=
covers_nonempty s1 s2 h1.left h2

theorem range_nonempty (n: ℕ) (h1: n > 0) : (range n).nonempty :=
have h2: 0 ∈ range n, from h1,
set.nonempty_of_mem h2

theorem pos_size (n : ℕ) (s: set ℕ) (h1: n > 0) (h2: has_size s n) : s.nonempty :=
have h3: bijects s (range n), from bijects_comm (range n) s h2,
have h4: (range n).nonempty, from range_nonempty n h1,
bijects_nonempty s (range n) h3 h4

def remove (s: set ℕ) (a: ℕ) := {x | x ∈ s ∧ x ≠ a}

lemma remove_nmem (s: set ℕ) (a: ℕ) (h1: a ∉ s) : remove s a = s :=
set.diff_singleton_eq_self h1

theorem remove_subset (s: set ℕ) (a: ℕ) : (remove s a) ⊆ s :=
set.sep_subset s (λ x: ℕ, x ≠ a)

theorem remove_union (s1 s2: set ℕ) (x: ℕ) :
remove (s1 ∪ s2) x = (remove s1 x) ∪ (remove s2 x) := set.union_diff_distrib

lemma surj_dec (a: ℕ) (s1 s2: set ℕ) (f: ℕ → ℕ) (h2: surj s1 s2 f):
surj (remove s1 a) (remove s2 (f a)) f :=
assume x2,
assume h4: x2 ∈ (remove s2 (f a)),
have h5: x2 ∈ s2, from h4.left,
have h6: ∃ x1: ℕ, x1 ∈ s1 ∧ f x1 = x2, from h2 x2 h5,
exists.elim h6
 (assume x1,
  assume h7: x1 ∈ s1 ∧ f x1 = x2,
  have h8: x2 ≠ f a, from h4.right,
  have h9: f x1 ≠ f a, from eq.subst h7.right.symm h8, 
  have x1 = a ∨ x1 ≠ a, from em(x1 = a),
  or.elim this
   (assume h10: x1 = a,
    have h11: f x1 = f a, from congr_arg f h10,
    absurd h11 h9)
   (assume h12: x1 ≠ a,
    have h13: x1 ∈ (remove s1 a), from and.intro h7.left h12,
    exists.intro x1 (and.intro h13 h7.right)))

def swap : ℕ → ℕ → ℕ → ℕ
| a b c :=
if a = c then b else (if b = c then a else c)

lemma swapl (a b : ℕ) : swap a b a = b := if_pos rfl

lemma swapr (a b : ℕ) : swap a b b = a :=
have h1: a = b ∨ a ≠ b, from em(a=b),
or.elim h1
 (assume h2: a = b,
  have h3: swap a a a = a, from swapl a a,
  have h4: swap a b b = a, from eq.subst h2 h3,
  h4)
 (assume h5: a ≠ b,
  have h6: swap a b b = (if b = b then a else b), from if_neg h5,
  have h7: (if b = b then a else b) = a, from if_pos rfl,
  have h8: swap a b b = a, by rw [h6, h7],
  h8)

lemma swapne (a b c : ℕ) (h1: a ≠ c) (h2: b ≠ c) : swap a b c = c :=
have h3: swap a b c = (if b = c then a else c), from if_neg h1,
have h4: (if b = c then a else c) = c, from if_neg h2,
by rw [h3, h4]

lemma surj_swap (a b : ℕ) (s : set ℕ) (h2: b ∈ s) (h3: a ≠ b) :
surj (remove s a) (remove s b) (swap a b) :=
assume x2,
assume h4: x2 ∈ (remove s b),
have h5: x2 = a ∨ x2 ≠ a, from em(x2 = a),
or.elim h5
 (assume h6: x2 = a,
  have h7: b ∈ (remove s a), from set.mem_sep h2 h3.symm,
  have h8: (swap a b) b = x2, from eq.subst h6.symm (swapr a b),
  exists.intro b (and.intro h7 h8))
 (assume h9: x2 ≠ a,
  have h10: x2 ∈ (remove s a), from and.intro h4.left h9,
  have h11: x2 ≠ b, from h4.right,
  have h12: (swap a b) x2 = x2, from swapne a b x2 h9.symm h11.symm,
  exists.intro x2 (and.intro h10 h12))

lemma covers_swap (a b : ℕ) (s : set ℕ) (h2: b ∈ s) :
covers (remove s a) (remove s b) :=
have h3: a = b ∨ a ≠ b, from em(a = b),
or.elim h3
 (assume h4: a = b,
  have h5: covers (remove s a) (remove s a), from covers_rfl (remove s a),
  have h6: remove s b = remove s a, from congr_arg (remove s) h4.symm,
  have h7: remove s b ⊆ remove s a, from (set.subset.antisymm_iff.mp h6).left,
  superset_covers (remove s a) (remove s b) h7)
 (assume h8: a ≠ b,
  exists.intro (swap a b) (surj_swap a b s h2 h8))

lemma bijects_swap (a b : ℕ) (s : set ℕ) (h1: a ∈ s) (h2: b ∈ s):
bijects (remove s a) (remove s b) :=
and.intro (covers_swap a b s h2) (covers_swap b a s h1)

lemma rrn (n: ℕ) : range n = remove (range (n+1)) n :=
set.eq_of_subset_of_subset
 (assume x,
  assume h1: x ∈ range n,
  have h2: x < n + 1, from nat.lt.step h1,
  have h3: x ≠ n, from ne_of_lt h1,
  and.intro h2 h3)
 (assume x,
  assume h4: x ∈ remove (range (n+1)) n,
  have h5: x < n + 1, from h4.left,
  have h6: x ≠ n, from h4.right,
  array.push_back_idx h5 h6)

lemma range_remove (a n : ℕ) (h1: a ∈ range (n+1)) :
bijects (range n) (remove (range (n+1)) a) :=
have h2: n ∈ range (n+1), from lt_add_one n,
have h3: bijects (remove (range (n+1)) n) (remove (range (n+1)) a),
    from bijects_swap n a (range (n+1)) h2 h1,
eq.subst (rrn n).symm h3

def overcovers (n: ℕ) := covers (range n) (range (n+1))

lemma noc_zero : ¬ overcovers 0 :=
have h1: overcovers 0 ∨ ¬ overcovers 0, from em(overcovers 0),
or.elim h1
 (assume h2: overcovers 0,
  have h3: covers ∅ (range 1), from eq.subst range_zero h2,
  have h4: (range 1) = ∅, from empty_covers (range 1) h3,
  have h5: 1 > 0, from lt_add_one 0,
  have h6: (range 1).nonempty, from range_nonempty 1 h5,
  have h7: ¬ (range 1 = ∅), from set.nmem_singleton_empty.mpr h6,
  absurd h4 h7)
 (assume: ¬ overcovers 0, this)

lemma ocai (n: ℕ) (h1: overcovers (n+1)) : overcovers n :=
exists.elim h1
 (assume f,
  assume h2: ∀ x2: ℕ, x2 ∈ range ((n+1)+1) → ∃ x1: ℕ, x1 ∈ range (n+1) ∧ f x1 = x2,
  have h3: n+1 ∈ range((n+1)+1), from lt_add_one (n+1),
  have h4: ∃ x1: ℕ, x1 ∈ range (n+1) ∧ f x1 = (n+1), from h2 (n+1) h3,
  exists.elim h4
   (assume x1,
    assume h5: x1 ∈ range (n+1) ∧ f x1 = (n+1),
    have h6: surj (remove (range (n+1)) x1) (remove (range ((n+1)+1)) (f x1)) f,
        from surj_dec x1 (range (n+1)) (range ((n+1)+1)) f h2,
    have h7: range (n+1) = remove (range ((n+1)+1)) (f x1),
        from eq.subst h5.right.symm (rrn (n+1)),
    have h8: bijects (range n) (remove (range (n+1)) x1) , from range_remove x1 n h5.left,
    have h9: covers (remove (range (n+1)) x1) (remove (range ((n+1)+1)) (f x1)),
        from exists.intro f h6,
    have h10: covers (range n) (remove (range ((n+1)+1)) (f x1)),
        from covers_trans (range n) (remove (range (n+1)) x1)
             (remove (range ((n+1)+1)) (f x1)) h8.left h9,
    have h11: covers (range n) (range (n+1)), from eq.subst h7.symm h10,
    h11))

lemma noc_any (n: ℕ) : ¬ overcovers n :=
nat.rec_on n
 (noc_zero)
 (assume n,
  assume h1: ¬ overcovers n,
  have h2: overcovers (n+1) ∨ ¬ overcovers (n+1), from em(overcovers (n+1)),
  or.elim h2
   (assume h3: overcovers (n+1),
    have h4: overcovers n, from ocai n h3,
    absurd h4 h1)
   (assume: ¬ overcovers (n+1), this))

lemma suhelp (s: set ℕ) (a b: ℕ) (h1: has_size s a) (h2: has_size s b) (h3: a > b) :
a = b :=
have h4: bijects (range a) s, from h1,
have h5: bijects (range b) s, from h2,
have h6: bijects s (range b), from bijects_comm (range b) s h5,
have h7: bijects (range a) (range b), from bijects_trans (range a) s (range b) h4 h6,
have h8: b+1 ≤ a, from h3,
have h9: range (b+1) ⊆ range a, from range_subset (b+1) a h8,
have h10: covers (range a) (range (b+1)), from superset_covers (range a) (range (b+1)) h9,
have h11: covers (range b) (range (b+1)),
    from covers_trans (range b) (range a) (range (b+1)) h7.right h10,
absurd h11 (noc_any b)

theorem size_unique (s : set ℕ) (a b : ℕ) (h1: has_size s a) (h2: has_size s b) : a = b :=
have h3: a < b ∨ ¬ (a < b), from em(a < b),
or.elim h3
 (assume h4: a < b,
  have h6: b = a, from suhelp s b a h2 h1 h4,
  h6.symm)
 (assume h7: ¬ (a < b),
  have h8: a = b ∨ a > b, from eq_or_lt_of_not_lt h7,
  or.elim h8
   (assume: a = b, this)
   (assume h9: a > b,
    suhelp s a b h1 h2 h9))

theorem covers_remove (s1 s2: set ℕ) (x1 x2: ℕ) (h2: x2 ∈ s2) (h3: covers s1 s2) :
covers (remove s1 x1) (remove s2 x2) :=
exists.elim h3
 (assume f,
  assume h4: surj s1 s2 f,
  have h5: surj (remove s1 x1) (remove s2 (f x1)) f, from surj_dec x1 s1 s2 f h4,
  have h6: covers (remove s1 x1) (remove s2 (f x1)), from exists.intro f h5,
  have h7: covers (remove s2 (f x1)) (remove s2 x2), from covers_swap (f x1) x2 s2 h2,
  covers_trans (remove s1 x1) (remove s2 (f x1)) (remove s2 x2) h6 h7)

theorem bijects_remove (s1 s2: set ℕ) (x1 x2: ℕ) (h1: x1 ∈ s1) (h2: x2 ∈ s2)
(h3: bijects s1 s2) :
bijects (remove s1 x1) (remove s2 x2) :=
and.intro (covers_remove s1 s2 x1 x2 h2 h3.left) (covers_remove s2 s1 x2 x1 h1 h3.right)

theorem remove_size (s: set ℕ) (a n: ℕ) (h1: has_size s (n+1)) (h2: a ∈ s) :
has_size (remove s a) n :=
have h3: bijects (range (n+1)) s, from h1,
have h4: n ∈ range (n+1), from lt_add_one n,
have h5: bijects (remove (range (n+1)) n) (remove s a),
    from bijects_remove (range (n+1)) s n a h4 h2 h3,
have h6: bijects (range n) (remove s a), from eq.subst (rrn n).symm h5,
h6

def patch : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ
| f a b x :=
if x = a then b else (f x)

lemma patchl (f: ℕ → ℕ) (a b : ℕ) : patch f a b a = b := if_pos rfl
lemma patchr (f: ℕ → ℕ) (a b x : ℕ) (h1: x ≠ a) : patch f a b x = f x := if_neg h1

lemma surj_insert (a: ℕ) (s1 s2: set ℕ) (f: ℕ → ℕ) (h1: a ∈ s1)
(h2: surj (remove s1 a) (remove s2 (f a)) f) :
surj s1 s2 f :=
assume x2,
assume h3: x2 ∈ s2,
have h4: x2 = (f a) ∨ x2 ≠ (f a), from em(x2 = (f a)),
or.elim h4
 (assume h5: x2 = (f a),
  have h6: a ∈ s1 ∧ f a = x2, from and.intro h1 h5.symm,
  exists.intro a h6)
 (assume h7: x2 ≠ (f a),
  have h8: x2 ∈ remove s2 (f a), from set.mem_sep h3 h7,
  have h9: ∃ x1: ℕ, x1 ∈ (remove s1 a) ∧ f x1 = x2, from h2 x2 h8,
  exists.elim h9
   (assume x1,
    assume h10: x1 ∈ (remove s1 a) ∧ f x1 = x2,
    have h11: x1 ∈ s1, from h10.left.left,
    exists.intro x1 (and.intro h11 h10.right)))

lemma surj_patch (a b: ℕ) (s1 s2: set ℕ) (f: ℕ → ℕ) (h1: a ∉ s1) (h2: surj s1 s2 f) :
surj s1 s2 (patch f a b) :=
assume x2,
assume h3: x2 ∈ s2,
have h4: ∃ x1: ℕ, x1 ∈ s1 ∧ f x1 = x2, from h2 x2 h3,
exists.elim h4
 (assume x1,
  assume h5: x1 ∈ s1 ∧ f x1 = x2,
  have h6: x1 = a ∨ x1 ≠ a, from em(x1 = a),
  or.elim h6
   (assume h7: x1 = a,
    have h8: x1 ∉ s1, from eq.subst h7.symm h1,
    absurd h5.left h8)
   (assume h9: x1 ≠ a,
    have h10: (patch f a b) x1 = x2, from eq.subst h5.right (patchr f a b x1 h9),
    exists.intro x1 (and.intro h5.left h10)))

theorem covers_insert (s1 s2: set ℕ) (x1 x2: ℕ) (h1: x1 ∈ s1)
(h2: covers (remove s1 x1) (remove s2 x2)) :
covers s1 s2 :=
exists.elim h2
 (assume f,
  assume h3: surj (remove s1 x1) (remove s2 x2) f,
  have h4: x1 ∉ (remove s1 x1), from not_and_not_right.mpr (congr_fun rfl),
  have h5: surj (remove s1 x1) (remove s2 x2) (patch f x1 x2),
      from surj_patch x1 x2 (remove s1 x1) (remove s2 x2) f h4 h3,
  have h6: surj (remove s1 x1) (remove s2 ((patch f x1 x2) x1)) (patch f x1 x2),
      from eq.subst (patchl f x1 x2).symm h5,
  have h7: surj s1 s2 (patch f x1 x2), from surj_insert x1 s1 s2 (patch f x1 x2) h1 h6,
  exists.intro (patch f x1 x2) h7)

theorem bijects_insert (s1 s2: set ℕ) (x1 x2: ℕ) (h1: x1 ∈ s1) (h2: x2 ∈ s2)
(h3: bijects (remove s1 x1) (remove s2 x2)) :
bijects s1 s2 :=
and.intro (covers_insert s1 s2 x1 x2 h1 h3.left) (covers_insert s2 s1 x2 x1 h2 h3.right)

theorem insert_size (s: set ℕ) (a n: ℕ) (h1: a ∈ s) (h2: has_size (remove s a) n) :
has_size s (n+1) :=
have h3: bijects (range n) (remove s a), from h2,
have h4: n ∈ range (n+1), from lt_add_one n,
have h5: bijects (remove (range (n+1)) n) (remove s a), from eq.subst (rrn n) h3,
bijects_insert (range (n+1)) s n a h4 h1 h5

def rcfn (n: ℕ) := ∀ s: set ℕ, covers (range n) s → ∃ a: ℕ, has_size s a

lemma rcfz : rcfn 0 :=
assume s,
assume h1: covers (range 0) s,
have h2: covers ∅ s, from eq.subst range_zero h1,
have h3: s = ∅, from empty_covers s h2,
have h4: has_size s 0, from eq.subst h3.symm empty_size,
exists.intro 0 h4

lemma range_covers_finite (n: ℕ) : rcfn n :=
nat.rec_on n
 (rcfz)
 (assume n,
  assume h1: rcfn n,
  assume s,
  assume h2: covers (range (n+1)) s,
  exists.elim h2
   (assume f,
    assume h3: surj (range (n+1)) s f,
    have h5: surj (remove (range (n+1)) n) (remove s (f n)) f,
        from surj_dec n (range (n+1)) s f h3,
    have h6: surj (range n) (remove s (f n)) f, from eq.subst (rrn n).symm h5,
    have h7: covers (range n) (remove s (f n)), from exists.intro f h6,
    have h8: ∃ a: ℕ, has_size (remove s (f n)) a, from h1 (remove s (f n)) h7,
    exists.elim h8
     (assume a,
      assume h9: has_size (remove s (f n)) a,
      have h10: (f n) ∈ s ∨ (f n) ∉ s, from em((f n) ∈ s),
      or.elim h10
       (assume h11: (f n) ∈ s,
        have h12: has_size s (a+1), from insert_size s (f n) a h11 h9,
        exists.intro (a+1) h12)
       (assume h13: (f n) ∉ s,
        have h14: (remove s (f n)) = s, from remove_nmem s (f n) h13,
        have h15: has_size s a, from eq.subst h14 h9,
        exists.intro a h15))))


theorem subset_finite (s1 s2: set ℕ) (n2: ℕ) (h1: s1 ⊆ s2) (h2: has_size s2 n2) :
∃ n1: ℕ, has_size s1 n1 :=
have h3: covers (range n2) s2, from h2.left,
have h4: covers s2 s1, from superset_covers s2 s1 h1,
have h5: covers (range n2) s1, from covers_trans (range n2) s2 s1 h3 h4,
range_covers_finite n2 s1 h5

def ssn (n1: ℕ) := ∀ s1: set ℕ, ∀ s2: set ℕ, ∀ n2: ℕ,
has_size s1 n1 ∧ has_size s2 n2 ∧ s1 ∩ s2 = ∅ → has_size (s1 ∪ s2) (n1 + n2)

lemma ssnz : ssn 0 :=
assume s1,
assume s2,
assume n2,
assume h1: has_size s1 0 ∧ has_size s2 n2 ∧ s1 ∩ s2 = ∅,
have h2: s1 = ∅, from size_zero_empty s1 h1.left,
have h3: ∅ ∪ s2 = s2, from set.empty_union s2,
have h4: s1 ∪ s2 = s2, from eq.subst h2.symm h3,
have h5: 0 + n2 = n2, from mul_one n2,
have h6: has_size (s1 ∪ s2) n2, from eq.subst h4.symm h1.right.left,
eq.subst h5.symm h6

lemma nmem_nonint (s1 s2: set ℕ) (x1: ℕ) (h1: x1 ∈ s1) (h2: s1 ∩ s2 = ∅) : x1 ∉ s2 :=
have h3: x1 ∈ s2 ∨ x1 ∉ s2, from em(x1 ∈ s2),
or.elim h3
 (assume h4: x1 ∈ s2,
  have h5: x1 ∈ s1 ∩ s2, from set.mem_sep h1 h4,
  have h6: x1 ∉ ∅, from list.not_mem_nil x1,
  have h7: x1 ∉ s1 ∩ s2, from eq.subst h2.symm h6,
  absurd h5 h7)
 (assume: x1 ∉ s2, this)

lemma ssni (n1: ℕ) (h1: ssn n1) : ssn (n1+1) :=
assume s1,
assume s2,
assume n2,
assume h2: has_size s1 (n1+1) ∧ has_size s2 n2 ∧ s1 ∩ s2 = ∅,
have h3: covers s1 (range (n1+1)), from h2.left.right,
have h4: n1+1 > 0, from nat.succ_pos n1,
have h5: (range (n1+1)).nonempty, from range_nonempty (n1+1) h4,
have h6: s1.nonempty, from covers_nonempty s1 (range (n1+1)) h3 h5,
have h7: ∃ x, x ∈ s1, from h6,
exists.elim h7
 (assume x,
  assume h8: x ∈ s1,
  have h9: has_size (remove s1 x) n1, from remove_size s1 x n1 h2.left h8,
  have h10: (remove s1 x) ⊆ s1, from remove_subset s1 x,
  have h11: (remove s1 x) ∩ s2 ⊆ s1 ∩ s2, from set.inter_subset_inter_left s2 h10,
  have h12: (remove s1 x) ∩ s2 ⊆ ∅, from eq.subst h2.right.right h11,
  have h13: (remove s1 x) ∩ s2 = ∅, from set.subset_eq_empty h12 rfl,
  have h14: has_size ((remove s1 x) ∪ s2) (n1 + n2),
      from h1 (remove s1 x) s2 n2 (and.intro h9 (and.intro h2.right.left h13)),
  have h15: remove (s1 ∪ s2) x = (remove s1 x) ∪ (remove s2 x), from remove_union s1 s2 x,
  have h16: x ∉ s2, from nmem_nonint s1 s2 x h8 h2.right.right,
  have h17: (remove s2 x) = s2, from remove_nmem s2 x h16,
  have h18: remove (s1 ∪ s2) x = (remove s1 x) ∪ s2,
      from eq.trans h15 (congr_arg (has_union.union (remove s1 x)) h17),
  have h19: has_size (remove (s1 ∪ s2) x) (n1 + n2), from eq.subst h18.symm h14,
  have h20: x ∈ s1 ∪ s2, from set.mem_union_left s2 h8,
  have h21: has_size (s1 ∪ s2) (n1 + n2 + 1),
      from insert_size (s1 ∪ s2) x (n1 + n2) h20 h19,
  have h22: (n1+1) + n2 = (n1 + n2 + 1), from nat.succ_add n1 n2,
  eq.subst h22.symm h21)

lemma ssn_any (n: ℕ) : ssn n :=
nat.rec_on n
 (ssnz)
 (assume n,
  assume h1: ssn n,
  ssni n h1)

theorem size_sum (s1 s2: set ℕ) (n1 n2: ℕ) (h1: has_size s1 n1) (h2: has_size s2 n2)
(h3: s1 ∩ s2 = ∅) : has_size (s1 ∪ s2) (n1 + n2) :=
ssn_any n1 s1 s2 n2 (and.intro h1 (and.intro h2 h3))

def set_mod_mult (s: set ℕ) (a m: ℕ) := { c | ∃ b: ℕ, b ∈ s ∧ mod (a*b) m = c }

def prange (n: ℕ) := remove (range n) 0

theorem prange_pos (a b: ℕ) (h1: a ∈ prange b) : a > 0 :=
have h2: a ≠ 0, from h1.right,
bot_lt_iff_ne_bot.mpr h2

theorem prange_coprime (x p: ℕ) (h1: is_prime p) (h2: x ∈ prange p) : coprime x p :=
have h3: coprime x p ∨ ¬ coprime x p, from em(coprime x p),
or.elim h3
 (assume: coprime x p, this)
 (assume: ¬ coprime x p, 
  have h4: ∃ y, y > 1 ∧ divides y x ∧ divides y p, from not_coprime x p this,
  exists.elim h4
   (assume y,
    assume h5: y > 1 ∧ divides y x ∧ divides y p,
    have h6: y = 1 ∨ y = p, from prime_divisors y p h1 h5.right.right,
    have h7: y ≠ 1, from ne_of_gt h5.left,
    have h8: y = p, from or.resolve_left h6 h7,
    have h9: divides p x, from eq.subst h8 h5.right.left,
    have h11: x > 0, from prange_pos x p h2,
    have h12: p ≤ x, from divides_le p x h9 h11,
    have h13: x < p, from h2.left,
    have h14: ¬ (x < p), from not_lt.mpr h12,
    absurd h13 h14))

theorem prange_nondivisor (x p: ℕ) (h1: is_prime p) (h2: x ∈ prange p) : ¬ divides p x :=
have h3: coprime x p, from prange_coprime x p h1 h2,
have h4: divides p x ∨ ¬ divides p x, from em(divides p x),
or.elim h4
 (assume h5: divides p x,
  have h6: divides p p, from divides_self p,
  have h7: ¬ coprime x p, from div_not_coprime p x p h1 h5 h6,
  absurd h3 h7)
 (assume: ¬ divides p x, this)

theorem right_inv (x p: ℕ) (h1: is_prime p) (h2: x ∈ prange p) :
∃ y: ℕ, mod (x*y) p = 1 :=
have h3: coprime x p, from prange_coprime x p h1 h2,
have h4: x > 0, from prange_pos x p h2,
have h5: p > 0, from prime_pos p h1,
have h6: 1 ∈ linear_combo x p, from bezout x p h4 h5 h3,
exists.elim h6
 (assume y,
  assume: ∃ m:ℕ, x*y = p*m + 1,
  exists.elim this
   (assume m,
    assume h7: x*y = p*m + 1,
    have h8: mod (m*p + 1) p = mod 1 p, from mod_rem m p 1,
    have h9: mod 1 p = 1, from mod_base 1 p h1.left,
    have h10: mod (m*p + 1) p = 1, by rw [h8, h9],
    have h11: m*p = p*m, from mul_comm m p,
    have h12: x*y = m*p + 1, from eq.subst h11.symm h7,
    have h13: mod (x*y) p = 1, from eq.subst h12.symm h10,
    exists.intro y h13))

theorem left_inv (x p: ℕ) (h1: is_prime p) (h2: x ∈ prange p) :
∃ y: ℕ, mod (y*x) p = 1 :=
exists.elim (right_inv x p h1 h2)
 (assume y,
  assume h3: mod (x*y) p = 1,
  have h4: x*y = y*x, from mul_comm x y,
  exists.intro y (eq.subst h4 h3))

theorem prange_closed (x y p: ℕ) (h1: is_prime p) (h2: x ∈ prange p) (h3: y ∈ prange p) :
mod (x*y) p ∈ prange p :=
have h4: coprime x p, from prange_coprime x p h1 h2,
have h5: coprime y p, from prange_coprime y p h1 h3,
have h6: x > 0, from prange_pos x p h2,
have h7: y > 0, from prange_pos y p h3,
have h8: p > 0, from prime_pos p h1,
have h9: coprime p (x*y), from coprime_mult p x y h8 h6 h7 (coprime_comm x p h4) (coprime_comm y p h5),
have h10: coprime (x*y) p, from coprime_comm p (x*y) h9,
have h11: divides p (x*y) ∨ ¬ divides p (x*y), from em(divides p (x*y)),
or.elim h11
 (assume h12: divides p (x*y),
  have h13: divides p x ∨ divides p y, from euclids_lemma p x y h1 h12,
  or.elim h13
   (assume: divides p x,
    absurd this (prange_nondivisor x p h1 h2))
   (assume: divides p y,
    absurd this (prange_nondivisor y p h1 h3)))
 (assume h14: ¬ divides p (x*y),
  have h15: mod (x*y) p > 0, from mod_nondivisor (x*y) p h14,
  have h16: mod (x*y) p < p, from mod_less (x*y) p h8,
  have h17: mod (x*y) p ≠ 0, from ne_of_gt h15,
  and.intro h16 h17)

lemma smm_subset (x p: ℕ) (h1: is_prime p) (h2: x ∈ prange p) :
set_mod_mult (prange p) x p ⊆ prange p :=
assume z,
assume h3: z ∈ set_mod_mult (prange p) x p,
exists.elim h3
 (assume y,
  assume h4: y ∈ (prange p) ∧ mod (x*y) p = z,
  have h5: mod (x*y) p ∈ prange p, from prange_closed x y p h1 h2 h4.left,
  eq.subst h4.right h5)

theorem mod_rmult (a b m: ℕ): mod (a * (mod b m)) m = mod (a*b) m :=
have h1: ∃ q, m*q + mod b m = b, from mod_div b m,
exists.elim h1
 (assume q,
  assume h2: m*q + mod b m = b,
  have h3: mod (a*b) m = mod (a*(m*q + mod b m)) m, from eq.subst h2.symm rfl,
  have h4: a*(m*q + mod b m) = (a*q)*m + a*(mod b m), by rw [mul_add, (mul_comm m q), mul_assoc],
  have h5: mod ((a*q)*m + a*(mod b m)) m = mod (a*(mod b m)) m, from mod_rem (a*q) m (a*(mod b m)),
  have h6: mod (a*b) m = mod (a*(mod b m)) m, by rw [h3, h4, h5],
  h6.symm)

theorem mod_lmult (a b m: ℕ): mod ((mod a m) * b) m = mod (a*b) m :=
by rw [(mul_comm (mod a m) b), mod_rmult, (mul_comm b a)]

lemma smm_assoc_1 (x y p: ℕ) :
set_mod_mult (set_mod_mult (prange p) x p) y p ⊆ set_mod_mult (prange p) (x*y) p :=
assume z,
assume h4: z ∈ set_mod_mult (set_mod_mult (prange p) x p) y p,
exists.elim h4
 (assume a,
  assume h5: a ∈ (set_mod_mult (prange p) x p) ∧ mod (y*a) p = z,
  exists.elim h5.left
   (assume b,
    assume h6: b ∈ prange p ∧ mod (x*b) p = a,
    have h7: mod (y * (mod (x*b) p)) p = z, from eq.subst h6.right.symm h5.right,
    have h8: mod (y*(x*b)) p = z, from eq.subst (mod_rmult y (x*b) p) h7,
    have h9: (x*y)*b = y*(x*b), by rw [(mul_comm x y), mul_assoc],
    have h10: mod ((x*y)*b) p = z, from eq.subst h9.symm h8,
    exists.intro b (and.intro h6.left h10)))

lemma smm_assoc_2 (x y p: ℕ) :
set_mod_mult (prange p) (x*y) p ⊆ set_mod_mult (set_mod_mult (prange p) x p) y p :=
assume z,
assume h4: z ∈ set_mod_mult (prange p) (x*y) p,
exists.elim h4
 (assume a,
  assume h5: a ∈ (prange p) ∧ mod ((x*y)*a) p = z,
  have h6: mod (x*a) p ∈ set_mod_mult (prange p) x p, from exists.intro a (and.intro h5.left rfl),
  have h7: mod (y*(mod (x*a) p)) p ∈ set_mod_mult (set_mod_mult (prange p) x p) y p,
      from exists.intro (mod (x*a) p) (and.intro h6 rfl),
  have h8: mod (y*(mod (x*a) p)) p = mod (y*(x*a)) p, from mod_rmult y (x*a) p,
  have h9: (x*y)*a = y*(x*a), by rw [(mul_comm x y), mul_assoc],
  have h8: mod (y*(mod (x*a) p)) p = z, by rw [h8, h9.symm, h5.right],
  eq.subst h8 h7)

theorem smm_assoc (x y p: ℕ) :
set_mod_mult (set_mod_mult (prange p) x p) y p = set_mod_mult (prange p) (x*y) p :=
set.subset.antisymm (smm_assoc_1 x y p) (smm_assoc_2 x y p)

lemma smm_mod_1 (x m: ℕ) (s: set ℕ): set_mod_mult s x m ⊆ set_mod_mult s (mod x m) m :=
assume y,
assume h1: y ∈ set_mod_mult s x m,
exists.elim h1
 (assume a,
  assume h2: a ∈ s ∧ mod (x*a) m = y,
  have h3: mod ((mod x m)*a) m = mod (x*a) m, from mod_lmult x a m,
  have h4: mod ((mod x m)*a) m = y, by rw [h3, h2.right],
  show y ∈ set_mod_mult s (mod x m) m, from exists.intro a (and.intro h2.left h4))

lemma smm_mod_2 (x m: ℕ) (s: set ℕ): set_mod_mult s (mod x m) m ⊆ set_mod_mult s x m :=
assume y,
assume h1: y ∈ set_mod_mult s (mod x m) m,
show y ∈ set_mod_mult s x m, from sorry

theorem smm_mod (x m: ℕ) (s: set ℕ): set_mod_mult s x m = set_mod_mult s (mod x m) m :=
set.subset.antisymm (smm_mod_1 x m s) (smm_mod_2 x m s)

theorem smm_eq (x p: ℕ) (h1: is_prime p) (h2: x ∈ prange p) : set_mod_mult (prange p) x p = prange p :=
sorry

/-
TODO: Fermat's Little Theorem.

smm_mod - that set_mod_mult'ing by x is the same as x mod p
smm_one - that smm 1 is the same set
smm_eq

Then we need to prove things about set-products. 

Then we need to calculate (p-1)! two ways, before and after multiplying by a.

I should also check out the community. If there's a future, it's in there somewhere.
-/

