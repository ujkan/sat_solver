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
    "ceval [] s = False"
  | "ceval (l # ls) s = (leval l s \<or> ceval ls s)"

fun evalCNF :: "formulaCNF \<Rightarrow> state \<Rightarrow> bool"
  where
    "evalCNF [] s = True"
  | "evalCNF (c # cs) s = (ceval c s \<and> evalCNF cs s)"

fun literal_to_formula :: "literal \<Rightarrow> formula"
  where
    "literal_to_formula (P x) = Var x"
  | "literal_to_formula (N x) = Not (Var x)"

fun clause_to_formula :: "clauseCNF \<Rightarrow> formula"
  where
    "clause_to_formula [] = Const False"
  | "clause_to_formula (l # ls) = Or (literal_to_formula l) (clause_to_formula ls)"

fun toFormula :: "formulaCNF \<Rightarrow> formula"
  where
    "toFormula [] = Const True"
  | "toFormula (c # cs) = And (clause_to_formula c) (toFormula cs)"


lemma ltf_eval: "leval l s \<longleftrightarrow> eval (literal_to_formula l) s"
  by (induction l) auto

lemma ctf_eval: "ceval c s \<longleftrightarrow> eval (clause_to_formula c) s"
  by (induction c) (auto simp: ltf_eval)

lemma toFormula_eval: "evalCNF cs s \<longleftrightarrow> eval (toFormula cs) s"
  by (induction cs) (auto simp: ctf_eval)

fun toCNF :: "formula \<Rightarrow> formulaCNF"
  where
    "toCNF (Var x) = [[P x]]"
  | "toCNF (Const b) = (if b then [] else [[]])"
(*| "toCNF (Not F) = (case F of (Var x) \<Rightarrow> [[N x]] 
                                | Const b \<Rightarrow> toCNF (Const (\<not>b)) 
                                | Not G \<Rightarrow> toCNF G
                                | And G H \<Rightarrow> [c1@c2 . c1 \<leftarrow> toCNF (Not G), c2 \<leftarrow> toCNF (Not H)]
                                | Or G H \<Rightarrow> toCNF (Not G) @ toCNF (Not H))"*)
  | "toCNF (Not (Var x)) = [[N x]]"
  | "toCNF (Not (Const b)) = toCNF (Const (\<not>b))"
  | "toCNF (Not (Not G)) = toCNF G"
  | "toCNF (Not (And F G)) = [c1@c2 . c1 \<leftarrow> toCNF (Not F), c2 \<leftarrow> toCNF (Not G)]"
  | "toCNF (Not (Or F G)) = toCNF (Not F) @ toCNF (Not G)"
  | "toCNF (And F G) = (toCNF F) @ (toCNF G)"
  | "toCNF (Or F G) = [c1@c2 . c1 \<leftarrow> toCNF F, c2 \<leftarrow> toCNF G]"


lemma evalCNF_app: "evalCNF (cs1 @ cs2) s = (evalCNF cs1 s \<and> evalCNF cs2 s)"
  by (induction cs1) auto

lemma evalCNF_fold_aux: "(b \<and> evalCNF cs s) = fold (\<lambda>c b. ceval c s \<and> b) cs b"
  by (induction cs arbitrary: b) (simp_all, metis)

lemma evalCNF_is_fold: "evalCNF cs s = fold (\<lambda>c b. ceval c s \<and> b) cs True"
  using evalCNF_fold_aux by auto

lemma ceval_app: "ceval (c1 @ c2) s = (ceval c1 s \<or> ceval c2 s)"
  by (induction c1) auto


lemma cnf_or_distr: "evalCNF (map ((@) a) cs) s = (ceval a s \<or> evalCNF cs s)"
  by (induction cs) (auto simp: ceval_app)

lemma cnf_or: "evalCNF [c1@c2 . c1 \<leftarrow> cs1, c2 \<leftarrow> cs2] s = (evalCNF cs1 s \<or> evalCNF cs2 s)"
  by (induction cs1) (auto simp: evalCNF_app cnf_or_distr)
  
lemma deMorgan_NAND: "eval (Not (And F G)) = eval (Or (Not F) (Not G))"
  by (induction F) auto

lemma deMorgan_NOR: "eval (Not (Or F G)) = eval (And (Not F) (Not G))"
  by (induction F) auto

lemma evalCNF_not: "evalCNF (toCNF (formula.Not F)) s = (\<not>evalCNF (toCNF F) s)"
  by (induction F) (auto split: if_splits simp: evalCNF_app cnf_or)

lemma toCNF_eval: "eval F s \<longleftrightarrow> evalCNF (toCNF F) s"
  by (induction F) (auto simp: evalCNF_app cnf_or evalCNF_not)
  
end