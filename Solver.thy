theory Solver
  imports Main
begin

datatype formula = Var string | Const bool | Not formula | And formula formula | Or formula formula

type_synonym state = "string \<Rightarrow> bool"

fun eval :: "formula \<Rightarrow> state \<Rightarrow> bool"
  where
    "eval (Const b) s = b"
  | "eval (Var x) s = s x"
  | "eval (Not F) s = (\<not>(eval F s))"
  | "eval (And F G) s = (eval F s \<and> eval G s)"
  | "eval (Or F G) s = (eval F s \<or> eval G s)"

definition satisfiable :: "formula \<Rightarrow> bool"
  where "satisfiable F \<equiv> (\<exists>s. eval F s = True)"

lemma "satisfiable (Const True)"
proof -
  have "eval (Const True) (\<lambda>x. True)" by simp
  thus ?thesis using satisfiable_def by simp
qed

lemma "\<not>satisfiable (Const False)"
proof -
  have "\<forall>s. eval (Const False) s = False" by simp
  thus ?thesis using satisfiable_def by simp
qed

datatype literal = P string | N string

type_synonym clauseCNF = "literal list"

type_synonym formulaCNF = "clauseCNF list"

fun leval :: "literal \<Rightarrow> state \<Rightarrow> bool"
  where
    "leval (P x) s = s x"
  | "leval (N x) s = (\<not>s x)"

fun ceval :: "clauseCNF \<Rightarrow> state \<Rightarrow> bool"
  where
    "ceval [] s = True"
  | "ceval (l # ls) s = (leval l s \<or> ceval ls s)"

fun evalCNF :: "formulaCNF \<Rightarrow> state \<Rightarrow> bool"
  where
    "evalCNF [] s = False"
  | "evalCNF [c] s = ceval c s"
  | "evalCNF (c # c' # cs) s = (ceval c s \<and> evalCNF (c' # cs) s)"

(*TODO: convert formula to formulaCNF*)


end