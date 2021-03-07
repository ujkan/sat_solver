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

fun literal_to_formula :: "literal \<Rightarrow> formula"
  where
    "literal_to_formula (P x) = Var x"
  | "literal_to_formula (N x) = Not (Var x)"

fun clause_to_formula :: "clauseCNF \<Rightarrow> formula"
  where
    "clause_to_formula [] = Const True"
  | "clause_to_formula (l # ls) = Or (literal_to_formula l) (clause_to_formula ls)"

fun cnf_to_formula :: "formulaCNF \<Rightarrow> formula"
  where
    "cnf_to_formula [] = Const False"
  | "cnf_to_formula [c] = (if c = [] then Const True else clause_to_formula c)"
  | "cnf_to_formula (c#cs) = And (clause_to_formula c) (cnf_to_formula cs)"


thm "list.induct"

lemma "Q [] \<Longrightarrow> (\<And>x. Q [x]) \<Longrightarrow> (\<And>x y xs. Q xs \<Longrightarrow> Q (y # xs) \<Longrightarrow> Q (x # y # xs)) \<Longrightarrow> Q xs"
  sorry

lemma ltf_correct: "leval l s \<longleftrightarrow> eval (literal_to_formula l) s"
  by (induction l) auto

lemma ctf_correct: "ceval c s \<longleftrightarrow> eval (clause_to_formula c) s"
  apply (induction c)
   apply (auto simp: ltf_correct)
  done

lemma conv_correct: "evalCNF cs s \<longleftrightarrow> eval (cnf_to_formula cs) s"
  apply (induction cs rule: induct_list012)
  apply (auto simp: ctf_correct)
  done


end