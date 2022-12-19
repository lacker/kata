inductive Cnat where
  | zero : Cnat
  | succ : Cnat → Cnat

def add (a b : Cnat) : Cnat :=
  match a with
  | Cnat.zero => b
  | Cnat.succ c => Cnat.succ (add c b)

theorem add_zero_right (x : Cnat) : add x Cnat.zero = x := by
  induction x
  case zero => rfl
  case succ x' ih => simp [ih, add]

theorem add_suc_right (x y : Cnat) : add x (Cnat.succ y) = Cnat.succ (add x y) := by
  induction x
  case zero => rfl
  case succ x' ih => simp [ih, add]

theorem add_comm (x y : Cnat) : add x y = add y x := by
  induction x
  case zero => simp [add, add_zero_right]
  case succ x' ih => simp [ih, add, add_suc_right]

theorem add_assoc (x y z : Cnat) : add (add x y) z = add x (add y z) := by
  induction x
  case zero => simp [add]
  case succ x' ih => simp [ih, add]

def mul (a b : Cnat) : Cnat :=
  match a with
  | Cnat.zero => Cnat.zero
  | Cnat.succ c => add b (mul c b)

theorem mul_zero_right (x : Cnat) : mul x Cnat.zero = Cnat.zero := by
  induction x
  case zero => rfl
  case succ x' ih => simp [ih, mul, add]

theorem mul_suc_right (x y : Cnat) : mul x (Cnat.succ y) = add x (mul x y) := by
  induction x
  case zero => simp [mul, add]
  case succ x' ih => simp [mul, add, ih, <-add_assoc, add_comm]

theorem mul_comm (x y : Cnat) : mul x y = mul y x := by
  induction x
  case zero => simp [mul, mul_zero_right]
  case succ x' ih => simp [mul, mul_suc_right, ih]

theorem distrib (x y z : Cnat) : mul x (add y z) = add (mul x y) (mul x z) := by
  induction x
  case zero => simp [mul, add]
  case succ x' ih => rw [mul, mul, mul, add_assoc, ih, add_assoc,
                         <- add_assoc (mul x' y), <- add_assoc z, add_comm z]

