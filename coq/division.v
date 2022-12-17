Inductive cnat : Set :=
| Zero : cnat
| Suc : cnat -> cnat.

Fixpoint add (a : cnat) (b : cnat) : cnat :=
match a with
| Zero => b
| (Suc c) => Suc (add c b)
end.

Theorem add_zero_right : forall (x : cnat), add x Zero = x.
Proof.
intros x.
induction x.
simpl.
trivial.
simpl.
rewrite IHx.
trivial.
Qed.

Theorem add_suc_right : forall (x : cnat) (y : cnat), add x (Suc y) = Suc (add x y).
Proof.
intros x y.
induction x.
simpl.
trivial.
simpl.
rewrite IHx.
trivial.
Qed.

Theorem add_comm : forall (x : cnat) (y : cnat), add x y = add y x.
Proof.
intros x y.
induction x.
simpl.
rewrite add_zero_right.
trivial.
simpl.
rewrite add_suc_right.
rewrite IHx.
trivial.
Qed.

Theorem add_assoc : forall (x : cnat) (y : cnat) (z : cnat), add (add x y) z = add x (add y z).
Proof.
intros x y z.
induction x.
simpl.
trivial.
simpl.
rewrite IHx.
trivial.
Qed.

Fixpoint mul (a : cnat) (b : cnat) : cnat :=
match a with
| Zero => Zero
| (Suc c) => add b (mul c b)
end.

Theorem mul_zero_right : forall (x : cnat), mul x Zero = Zero.
intros x.
induction x.
simpl.
trivial.
simpl.
rewrite IHx.
trivial.
Qed.

Theorem mul_suc_right : forall (x : cnat) (y : cnat), mul x (Suc y) = add x (mul x y).
intros x y.
induction x.
simpl.
trivial.
simpl.
rewrite IHx.
rewrite add_comm.
rewrite add_assoc.
replace (add (mul x y) y) with (add y (mul x y)).
trivial.
rewrite add_comm.
trivial.
Qed.

Theorem mul_comm : forall (x : cnat) (y : cnat), mul x y = mul y x.
intros x y.
induction x.
simpl.
rewrite mul_zero_right.
trivial.
simpl.
rewrite mul_suc_right.
rewrite IHx.
trivial.
Qed.

Theorem distrib : forall (x : cnat) (y : cnat) (z : cnat),
  mul x (add y z) = add (mul x y) (mul x z).
intros x y z.
induction x.
simpl.
trivial.
simpl.
rewrite IHx.
rewrite add_assoc.
rewrite add_assoc.
replace (add z (add (mul x y) (mul x z))) with (add (mul x y) (add z (mul x z))).
trivial.
rewrite <- add_assoc.
rewrite <- add_assoc.
replace (add (mul x y) z) with (add z (mul x y)).
trivial.
rewrite add_comm.
trivial.
Qed.

Theorem mul_assoc : forall (x : cnat) (y : cnat) (z : cnat),
  mul (mul x y) z = mul x (mul y z).
intros x y z.
induction x.
simpl.
trivial.
simpl.
rewrite mul_comm.
rewrite distrib.
rewrite <- IHx.
rewrite mul_comm.
replace (mul z (mul x y)) with (mul (mul x y) z).
trivial.
rewrite mul_comm.
trivial.
Qed.
























