theory Division
  imports Main
begin
(* Let's get to the Division Theorem in the "structured" style. *)

datatype cnat = Zero | Suc cnat

fun add :: "cnat \<Rightarrow> cnat \<Rightarrow> cnat" where
"add Zero x = x" |
"add (Suc x) y = Suc (add x y)"

lemma add_zero_right [simp]: "add x Zero = x"
proof (induct x)
  case Zero show ?case by simp 
next
  case (Suc x) then show ?case by simp 
qed

lemma add_suc_right [simp]: "add x (Suc y) = Suc (add x y)"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    by simp 
qed

lemma add_comm: "add x y = add y x"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    by simp 
qed

lemma add_assoc: "add (add x y) z = add x (add y z)"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    by simp
qed




end