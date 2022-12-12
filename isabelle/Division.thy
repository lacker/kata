theory Division
  imports Main
begin

(* "custom naturals" *)
datatype cnat = Zero | Suc cnat

fun add :: "cnat \<Rightarrow> cnat \<Rightarrow> cnat" where
"add Zero x = x" |
"add (Suc x) y = Suc (add x y)"

lemma add_zero_right [simp]: "add x Zero = x"
  apply(induction x)
  apply(auto)
  done

lemma add_suc_right [simp]: "add x (Suc y) = Suc (add x y)"
  apply(induction x)
  apply(auto)
  done

lemma add_comm: "add x y = add y x"
  apply(induction x)
  apply(auto)
  done

lemma add_assoc: "add (add x y) z = add x (add y z)"
  apply(induction x)
  apply(auto)
  done

fun mul :: "cnat \<Rightarrow> cnat \<Rightarrow> cnat" where
"mul Zero x = Zero" |
"mul (Suc x) y = add y (mul x y)"

lemma mul_zero_right [simp]: "mul x Zero = Zero"
  apply(induction x)
  apply(auto)
  done

lemma mul_suc_right [simp]: "mul x (Suc y) = add x (mul x y)"
  apply(induction x)
  apply(simp)
  using add_assoc add_comm by auto

lemma mul_comm: "mul x y = mul y x"
  apply(induction x)
  apply(auto)
  done

lemma distrib [simp]: "mul x (add y z) = add (mul x y) (mul x z)"
  apply(induction x)
  apply(auto)
  by (metis add_assoc add_comm)

lemma mul_assoc: "mul (mul x y) z = mul x (mul y z)"
  apply(induction x)
  apply(auto)
  by (simp add: mul_comm)

fun lt :: "cnat \<Rightarrow> cnat \<Rightarrow> bool" where
"lt x Zero = False" |
"lt Zero x = True" |
"lt (Suc x) (Suc y) = lt x y"

lemma lt_not_ref: "~ lt x x"
  apply(induction x)
  apply(auto)
  done

lemma lt_not_symm: "lt a b \<Longrightarrow> ~ lt b a"
  apply(induction a arbitrary: b)
  apply(auto)
  by (metis lt.elims(2) lt.simps(3))

lemma lt_trans: "lt a b \<Longrightarrow> lt b c \<Longrightarrow> lt a c"
  apply(induction c arbitrary: a b)
  apply(auto)
  by (metis cnat.distinct(1) cnat.inject lt.elims(1) lt.simps(3))

lemma lt_to_sub: "lt a b \<Longrightarrow> \<exists> c. b = add a c"
  apply(induction a arbitrary: b)
  apply(auto)
  by (metis cnat.distinct(2) cnat.inject lt.elims(2))

lemma lt_add_suc: "lt a (add a (Suc b))"
  apply(induction a arbitrary: b)
  apply(auto)
  done

lemma add_cancels_left: "add a b = add a c \<Longrightarrow> b = c"
  apply(induction a arbitrary: b c)
  apply(auto)
  done

lemma add_cancels_right: "add a c = add b c \<Longrightarrow> a = b"
  using add_cancels_left add_comm by presburger

(*
lemma division_theorem: "lt Zero n \<Longrightarrow> \<exists> q r. lt r n \<and> m = add (mul q n) r"
  apply(induction m)
  apply(auto)
  apply (metis add_zero_right mul.simps(1))
*)

end