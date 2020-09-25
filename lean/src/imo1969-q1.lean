import tactic
import tactic.basic
import tactic.linarith
import tactic.norm_cast
import tactic.ring

open classical
open nat

/-
The 1969 IMO, problem 1:
Prove that there are infinitely many natural numbers $a$ with the following property:
the number $z = n^4 + a$ is not prime for any natural number $n$.

The key to the solution is that you can factor this out, if a = 4*m^4. To formally prove this, first we
demonstrate the factorization, and then there is a bunch of fairly mundane shuffling polynomials around
to show that each of the factors is sufficiently large.
(For human mathematicians, everything is considered trivial once you've found the factorization.)
-/

lemma the_factorization (m: ℤ) (n: ℤ) :
(n^2 + 2 * m^2 - 2 * n * m) * (n^2 + 2 * m^2 + 2 * n * m) = n^4 + 4 * m ^ 4 :=
by ring

lemma square_ge_zero (a: ℤ) : a * a ≥ 0 :=
have h1: a ≥ 0 ∨ ¬ a ≥ 0, from em(a ≥ 0),
or.elim h1
  (assume h2: a ≥ 0, show a * a ≥ 0, from mul_nonneg h2 h2)
  (assume h3: ¬ a ≥ 0,
   have h4: a < 0, from not_le.mp h3,
   have h5: a * a > 0, from mul_pos_of_neg_of_neg h4 h4,
   show a * a ≥ 0, from le_of_lt h5)

/- Proving that the first of the two factors is large enough. -/   
lemma first_factor_large (m: ℤ) (n: ℤ) (h1: m ≥ 2) (h2: n ≥ 0) : (n^2 + 2 * m^2 - 2 * n * m) ≥ 2 :=
have h3: (n^2 + 2 * m^2 - 2 * n * m) = (n-m)*(n-m) + m*m, by ring,
have h4: (n-m)*(n-m) ≥ 0, from square_ge_zero (n-m),
have h5: m*m ≥ 2*2, from mul_self_le_mul_self trivial h1,
have h6: (2:ℤ)*2 ≥ 2, from sup_eq_left.mp rfl,
have h7: m*m ≥ 2, from ge_trans h5 h6,
have h8: (n-m)*(n-m) + m*m ≥ 2, from le_add_of_nonneg_of_le h4 h7,
eq.subst h3.symm h8

/- Proving that the second of the two factors is large enough. -/
lemma second_factor_large (m: ℤ) (n: ℤ) (h1: m ≥ 2) (h2: n ≥ 0) : (n^2 + 2 * m^2 + 2 * n * m) ≥ 2:=
have h3: m ≥ 0, from ge_trans h1 trivial,
have h4: n*m ≥ 0, from mul_nonneg h2 h3,
have h6: 4*(n*m) ≥ 0, from mul_nonneg trivial h4,
have h7: (n^2 + 2 * m^2 + 2 * n * m) - (n^2 + 2 * m^2 - 2 * n * m) = 4*(n*m), by ring,
have h8: (n^2 + 2 * m^2 + 2 * n * m) - (n^2 + 2 * m^2 - 2 * n * m) ≥ 0, from eq.subst h7.symm h6,
have h9: (n^2 + 2 * m^2 + 2 * n * m) ≥ (n^2 + 2 * m^2 - 2 * n * m), from sub_nonneg.mp h8,
ge_trans h9 (first_factor_large m n h1 h2)

/-
It was easier to do arithmetic over ℤ. We'll need to be in ℕ to show primality though.
-/

/-
lemma int_version (n m : ℤ) : (n^2 + 2 * m^2 - 2 * n * m) * (n^2 + 2 * m^2 + 2 * n * m) = n^4 + 4 * m ^ 4 := by ring
example (n m : ℕ) : (n^2 + 2 * m^2 - 2 * n * m) * (n^2 + 2 * m^2 + 2 * n * m) = n^4 + 4 * m ^ 4 := begin
  zify,
  rw ← int_version,
  congr,
  norm_cast,
  refine int.of_nat_sub _, -- suggest told me this
  nlinarith,
end
-/

lemma ge_lifting (x: ℤ) (h1: x ≥ 2) : x.nat_abs ≥ 2 := 
have h2: x = ↑(x.nat_abs) ∨ x = -↑(x.nat_abs), from int.nat_abs_eq x,
or.elim h2
  (assume h3: x = ↑(x.nat_abs),
   have h4: ↑(x.nat_abs) ≥ (2:ℤ), from eq.subst h3 h1,
   int.coe_nat_le.mp h4)
  (assume h5: x = -↑(x.nat_abs),
   have h6: -↑(x.nat_abs) ≤ (0:ℤ), from neg_le.mp trivial,
   have h7: x ≤ 0, from eq.subst h5.symm h6,
   have h8: ¬ x > 0, from not_lt.mpr h7,
   have h9: x > 0, from forall_lt_iff_le.mpr h1 trivial,
   absurd h9 h8)

lemma primality_lifting (x: ℤ) (y: ℤ) (k: ℕ) (h1: x ≥ 2) (h2: y ≥ 2) (h3: x*y = ↑k) : ¬ prime k :=
have h4: (x*y).nat_abs = k, from (congr_arg int.nat_abs h3).trans rfl,
have h5: (x*y).nat_abs = x.nat_abs * y.nat_abs, from int.nat_abs_mul x y,
have h6: x.nat_abs * y.nat_abs = k, from eq.subst h5 h4,
have h7: x.nat_abs ≥ 2, from ge_lifting x h1,
have h8: y.nat_abs ≥ 2, from ge_lifting y h2,
norm_num.not_prime_helper x.nat_abs y.nat_abs k h6 h7 h8

lemma factorization_lifting (m: ℕ) (n: ℕ) (h1: m ≥ 2) : ¬ prime (n^4 + 4 * m ^ 4) :=
sorry

/- have h2: ↑(n^4 + 4 * m ^ 4) = (↑n)^4 + 4*(↑m)^4, -/

/-
Now we just need to pick an appropriate a to prove there are infinitely many of them.
-/

theorem imo1969_q1 : ∀ b: ℕ, ∃ a: ℕ, a ≥ b ∧ ∀ n: ℕ, ¬ prime (n^4 + a) := sorry

