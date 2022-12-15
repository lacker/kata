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

fun mul :: "cnat \<Rightarrow> cnat \<Rightarrow> cnat" where
"mul Zero x = Zero" |
"mul (Suc x) y = add y (mul x y)"

lemma mul_zero_right [simp]: "mul x Zero = Zero"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    by simp 
qed

lemma mul_suc_right [simp]: "mul x (Suc y) = add x (mul x y)"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    using add_assoc add_comm by fastforce 
qed

lemma mul_comm: "mul x y = mul y x"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    by simp
qed

lemma distrib [simp]: "mul x (add y z) = add (mul x y) (mul x z)"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    by (metis add_assoc add_comm mul.simps(2))
qed

lemma mul_assoc: "mul (mul x y) z = mul x (mul y z)"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    by (simp add: mul_comm)
qed

fun lt :: "cnat \<Rightarrow> cnat \<Rightarrow> bool" where
"lt x Zero = False" |
"lt Zero x = True" |
"lt (Suc x) (Suc y) = lt x y"

lemma lt_not_ref: "~ lt x x"
proof (induct x)
  case Zero
  then show ?case
    by simp 
next
  case (Suc x)
  then show ?case
    by simp
qed

lemma lt_not_symm: "lt a b \<Longrightarrow> ~ lt b a"
proof (induct a arbitrary: b)
  case Zero
  then show ?case
    by simp 
next
  case (Suc a)
  then show ?case
    by (metis lt.elims(2) lt.simps(3))
qed

lemma lt_trans: "lt a b \<Longrightarrow> lt b c \<Longrightarrow> lt a c"
proof (induct c arbitrary: a b)
  case Zero
  then show ?case
    by simp 
next
  case (Suc c)
  then show ?case
    by (metis cnat.distinct(1) cnat.inject lt.elims(1) lt.simps(3)) 
qed

lemma lt_to_sub: "lt a b \<Longrightarrow> \<exists> c. b = add a c"
proof (induct a arbitrary: b)
  case Zero
  then show ?case
    by simp 
next
  case (Suc a)
  then show ?case
    by (metis add.elims add.simps(2) lt.simps(1) lt.simps(3))
qed

lemma lt_add_suc: "lt a (add a (Suc b))"
proof (induct a arbitrary: b)
  case Zero
  then show ?case
    by simp 
next
  case (Suc a)
  then show ?case
    by simp
qed

lemma add_cancels_left: "add a b = add a c \<Longrightarrow> b = c"
proof (induct a arbitrary: b)
  case Zero
  then show ?case
    by simp 
next
  case (Suc a)
  then show ?case
    by simp
qed

lemma add_cancels_right: "add a c = add b c \<Longrightarrow> a = b"
  using add_cancels_left add_comm by presburger

lemma lt_suc: "lt a b \<Longrightarrow> (Suc a) = b \<or> lt (Suc a) b"
  by (smt (verit, ccfv_threshold) add.elims add_comm add_zero_right cnat.inject lt.elims(1) lt_add_suc lt_not_ref lt_to_sub)

lemma division_theorem: "lt Zero n \<Longrightarrow> \<exists> q r. lt r n \<and> m = add (mul q n) r"
proof (induct m)
  case Zero
  then show ?case
    by (metis add_zero_right mul.simps(1)) 
next
  case (Suc m)
  obtain q and r where "lt r n \<and> m = add (mul q n) r"
    using Suc.hyps Suc.prems by blast
  show ?case
  proof (cases "Suc r = n")
    case True
    then show ?thesis
      by (metis Suc.prems \<open>lt r n \<and> m = add (mul q n) r\<close> add.simps(2) add_comm add_zero_right mul_comm mul_suc_right) 
  next
    case False
    have "Suc m = add (mul q n) (Suc r)"
      by (simp add: \<open>lt r n \<and> m = add (mul q n) r\<close>)
    have "lt (Suc r) n"
      using False \<open>lt r n \<and> m = add (mul q n) r\<close> lt_suc by blast 
    then show ?thesis
      using \<open>cnat.Suc m = add (mul q n) (cnat.Suc r)\<close> by blast 
  qed

qed






end