inductive Cnat where
  | zero : Cnat
  | succ : Cnat → Cnat

def add (a b : Cnat) : Cnat :=
  match a with
  | Cnat.zero => b
  | Cnat.succ c => Cnat.succ (add c b)

theorem add_zero_right (x : Cnat) : add x Cnat.zero = x :=
  sorry