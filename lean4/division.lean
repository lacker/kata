open Classical

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

theorem mul_assoc (x y z : Cnat) : mul (mul x y) z = mul x (mul y z) := by
  induction x
  case zero => simp [mul]
  case succ x' ih => simp [mul, mul_comm, distrib, <- ih]

def lt (a b : Cnat) : Prop :=
  match b with
  | Cnat.zero => False
  | Cnat.succ d => match a with
                   | Cnat.zero => True
                   | Cnat.succ c => lt c d

theorem lt_not_ref (x : Cnat) : ¬ lt x x := by
  induction x
  case zero => simp [lt]
  case succ x' ih => simp [lt, ih]

theorem lt_not_symm (a b : Cnat) : lt a b → ¬ lt b a := by
  induction a generalizing b
  case zero => simp [lt]
  case succ a' ih => match b with
    | Cnat.zero => simp [lt]
    | Cnat.succ b' => simp [lt]; apply ih

theorem lt_trans (a b c : Cnat) : lt a b ∧ lt b c → lt a c := by
  induction c generalizing a b
  case zero => simp [lt]
  case succ c' ih => match a with
    | Cnat.zero => simp [lt]
    | Cnat.succ a' => match b with
      | Cnat.zero => simp [lt]
      | Cnat.succ b' => simp [lt]; apply ih

theorem lt_to_sub (a b : Cnat) : lt a b → ∃ c, b = add a c := by
  induction a generalizing b
  case zero => simp [add]; intro; apply Exists.intro b; rfl
  case succ a ih =>
    simp [add]
    match b with
      | Cnat.zero => simp [lt]
      | Cnat.succ b' => simp [lt]; apply ih 

theorem lt_add_suc (a b : Cnat) : lt a (add a b.succ) := by
  induction a generalizing b
  case zero => simp [add, lt]
  case succ a ih => simp [add, lt]; apply ih

theorem add_cancels_left (a b c : Cnat) : add a b = add a c → b = c := by
  induction a generalizing b
  case zero => simp [add]; intro h; exact h
  case succ a ih => simp [add]; apply ih

theorem add_cancels_right (a b c : Cnat) : add a c = add b c → a = b := by
  induction c
  case zero => simp [add_zero_right]; intro h; exact h
  case succ c ih => simp [add_suc_right]; exact ih

theorem lt_suc (a b : Cnat) (h1: lt a b) : a.succ = b ∨ lt a.succ b := by
  let ⟨c, h2⟩ := lt_to_sub a b h1
  match c with
    | Cnat.zero => {
      simp [add_zero_right] at h2; rw [h2] at h1; simp [lt_not_ref] at h1
    }
    | Cnat.succ c' => match c' with
      | Cnat.zero => {
        simp [add_suc_right, add_zero_right] at h2
        simp [h2]
      }
      | Cnat.succ c'' => {
        apply Or.inr
        rw [add_suc_right] at h2
        rw [h2]
        simp [lt]
        exact lt_add_suc _ _
      }

theorem division_theorem (m n : Cnat) (h1: lt Cnat.zero n) :
  ∃ q r, lt r n ∧ m = add (mul q n) r := by
  induction m
  case zero => {
    apply Exists.intro Cnat.zero
    apply Exists.intro Cnat.zero
    simp [h1, mul, add] 
  }
  case succ m ih => {
    let ⟨q, r, h2, h3⟩ := ih
    apply Or.elim (em (r.succ = n))
    case left => {
      intro h4
      apply Exists.intro q.succ
      apply Exists.intro Cnat.zero
      simp [h1, add_zero_right, h3, mul]
      rw [<- h4, add, add_comm]
    }
    case right => {
      intro h5
      apply Exists.intro q
      apply Exists.intro r.succ
      apply And.intro
      case left => {
        apply Or.elim (lt_suc r n h2)
        case left => simp [h5]
        case right => intro h6; exact h6  
      }
      case right => {
        rw [h3]
        simp [add_suc_right]
      }
    }
  }

def is_prime (p : Cnat) : Prop := sorry
