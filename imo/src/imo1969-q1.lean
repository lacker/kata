import tactic
import tactic.basic
import tactic.linarith
import tactic.norm_cast
import tactic.ring
import tactic.zify

open nat

/-
The 1969 IMO, problem 1:
Prove that there are infinitely many natural numbers $a$ with the following property:
the number $z = n^4 + a$ is not prime for any natural number $n$.

The key to the solution is that you can factor this into the product of two polynomials, if a = 4*m^4.
-/

lemma int_factors (m n : ℤ): (n^2 + 2 * m^2 - 2 * n * m) * (n^2 + 2 * m^2 + 2 * n * m) = n^4 + 4 * m ^ 4
:= by ring

lemma nat_factors (m n : ℕ): (n^2 + 2 * m^2 - 2 * n * m) * (n^2 + 2 * m^2 + 2 * n * m) = n^4 + 4 * m ^ 4
:= begin
  zify,
  rw ← int_factors,
  congr,
  norm_cast,
  refine int.of_nat_sub _,
  nlinarith,
end

/-
To show that the product is not prime, we need to show each of the factors is at least 2, which we can
do with a sum-of-squares expression.
-/
lemma left_factor_large (m n: ℤ) (m ≥ 2) : (n^2 + 2 * m^2 - 2 * n * m) ≥ 2 :=
have h: (n^2 + 2 * m^2 - 2 * n * m) = (m-n)^2 + m^2, by ring,
begin
  rw h,
  nlinarith,
end

lemma right_factor_large (m n: ℤ) (m ≥ 2) : (n^2 + 2 * m^2 + 2 * n * m) ≥ 2 :=
have h: (n^2 + 2 * m^2 + 2 * n * m) = (m+n)^2 + m^2, by ring,
begin
  rw h,
  nlinarith,
end

/-
Now we just need to show this works for an arbitrarily large a, to prove there are infinitely many of them.
-/

theorem imo1969_q1 : ∀ b: ℕ, ∃ a: ℕ, a ≥ b ∧ ∀ n: ℕ, ¬ prime (n^4 + a) := sorry

