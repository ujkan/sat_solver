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

fun literal_var :: "literal \<Rightarrow> string"
  where
    "literal_var (P x) = x"
  | "literal_var (N x) = x"

fun clause_vars :: "clauseCNF \<Rightarrow> string list"
  where
    "clause_vars [] = []"
  | "clause_vars (l # ls) = literal_var l # clause_vars ls"

fun cnf_vars :: "formulaCNF \<Rightarrow> string list"
  where
    "cnf_vars [] = []"
  | "cnf_vars (c # cs) = clause_vars c @ cnf_vars cs"

fun vals :: "string list \<Rightarrow> state list"
  where
    "vals [] = [\<lambda>s. False]"
  | "vals (x # xs) = [s(x:=False) . s \<leftarrow> vals xs] @ [s(x:=True) . s \<leftarrow> vals xs]"

definition solver_bruteforce :: "formulaCNF \<Rightarrow> bool"
  where
    "solver_bruteforce cs = fold (\<or>) [evalCNF cs s . s \<leftarrow> vals (cnf_vars cs)] (False)"

lemma not_foldOrFalse_if_not_contains_True: "True \<notin> set ls \<Longrightarrow> fold (\<or>) ls (False) = False"
  by (induction ls) auto

lemma foldOr_true: "fold (\<or>) ls True = True"
  by (induction ls) auto

lemma foldOrFalse_weaker: "fold (\<or>) ls False \<Longrightarrow> fold (\<or>) ls b"
proof (induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  have "fold (\<or>) (a # ls) False = fold (\<or>) ls a" by simp
  then show ?case using Cons by (cases a, auto)
qed

lemma fold_or_False_if_contains_True: "True \<in> set ls \<Longrightarrow> fold (\<or>) ls False"
proof (induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  then have "a = True \<or> True \<in> set ls" by simp
  then show ?case 
  proof (rule disjE)
    assume "a = True"
    then show "fold (\<or>) (a # ls) False" using foldOr_true \<open>a = True\<close> by auto
  next
    assume "True \<in> set ls"
    then have "fold (\<or>) ls False" using Cons by simp
    then show "fold (\<or>) (a # ls) False" using foldOrFalse_weaker by simp
  qed
qed

lemma foldOr_iff_contains_True: "fold (\<or>) ls False = (True \<in> set ls)"
  using not_foldOrFalse_if_not_contains_True fold_or_False_if_contains_True by auto
  
lemma solver_bruteforce_alt_def:"solver_bruteforce cs = (\<exists>s \<in> set (vals (cnf_vars cs)). evalCNF cs s)"
  unfolding solver_bruteforce_def
  using foldOr_iff_contains_True by auto
 
lemma solver_bruteforce_correct: "solver_bruteforce cs \<Longrightarrow> satisfiable (toFormula cs)"
  unfolding satisfiable_def
  using solver_bruteforce_alt_def toFormula_eval by blast

lemma vals_false_everywhere_else: "(\<And>x. x \<notin> set cs \<Longrightarrow> t x = False) \<Longrightarrow> (t \<in> set (vals cs))"
  apply (induction cs arbitrary: t)
   apply auto
  by (smt (z3) fun_upd_def fun_upd_triv fun_upd_upd image_iff)
  

lemma vals_contains_aux: "\<forall>s. \<exists>t \<in> set (vals (cnf_vars cs)). \<forall>x \<in> set (cnf_vars cs). (s x = t x)"
proof
  fix s
  let ?t = "(\<lambda>x. (if x \<in> set (cnf_vars cs) then s x else False))"
  have *: "?t \<in> set (vals (cnf_vars cs))" using vals_false_everywhere_else by simp
  have "\<forall>x \<in> set (cnf_vars cs). (s x = ?t x)" by simp
  then show "\<exists>t \<in> set (vals (cnf_vars cs)). \<forall>x \<in> set (cnf_vars cs). (s x = t x)" using * 
    by (metis (no_types, lifting))
qed

lemma leval_state_inj: "s (literal_var l) = t (literal_var l) \<Longrightarrow> leval l s = leval l t"
  apply (induction l)
  apply auto
  done

lemma ceval_state_inj: "(\<forall>x \<in> set (clause_vars ls). s x = t x) \<Longrightarrow> (ceval ls s = ceval ls t)"
  apply (induction ls)
   apply (auto)
  using leval_state_inj 
     apply blast
  using leval_state_inj apply blast
  using leval_state_inj apply metis
  using leval_state_inj apply metis
  done

lemma evalCNF_state_inj: "(\<forall>x \<in> set (cnf_vars cs). s x = t x) \<Longrightarrow> (evalCNF cs s = evalCNF cs t)"
  apply (induction cs)
   apply auto
  using ceval_state_inj apply blast+
  done

lemma vals_contains: "\<forall>s. \<exists>t \<in> set (vals (cnf_vars cs)). evalCNF cs s = evalCNF cs t"
proof 
  fix s
  have "\<exists>t \<in> set (vals (cnf_vars cs)). \<forall>x \<in> set (cnf_vars cs). (s x = t x)" using vals_contains_aux by simp
  then show "\<exists>t \<in> set (vals (cnf_vars cs)). evalCNF cs s = evalCNF cs t" using evalCNF_state_inj by blast
qed

lemma solver_bruteforce_complete: "satisfiable (toFormula cs) \<Longrightarrow> solver_bruteforce cs"
  unfolding satisfiable_def
  apply (simp add: toFormula_eval[symmetric])
proof -
  assume assm: "\<exists>s. evalCNF cs s"
  then obtain s where s_def: "evalCNF cs s" by blast
  then have "\<exists>t \<in> set (vals (cnf_vars cs)). evalCNF cs s = evalCNF cs t" using assm vals_contains by auto
  then have "\<exists>t \<in> set (vals (cnf_vars cs)). evalCNF cs t" using s_def by simp
  then obtain t where "t \<in> set (vals (cnf_vars cs)) \<and> evalCNF cs t" by blast
  then show ?thesis using solver_bruteforce_alt_def[symmetric] by auto
qed

lemma solver_bruteforce_runtime: "length (vals cs) = 2 ^ (length cs)"
  by (induction cs) auto

fun contains :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where
    "contains x [] = False"
  | "contains x (y # ys) = (if x = y then True else contains x ys)"

fun not :: "literal \<Rightarrow> literal"
  where
    "not (P x) = N x"
  | "not (N x) = P x"



fun unit_clauses :: "formulaCNF \<Rightarrow> clauseCNF list"
  where
    "unit_clauses [] = []"
  | "unit_clauses (c # cs) = (if length c = 1 then c # unit_clauses cs else unit_clauses cs)"

fun delete :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "delete x [] = []" 
  | "delete x (y # ys) = (if x = y then delete x ys else y # (delete x ys))"

fun unit_propagate :: "clauseCNF \<Rightarrow> formulaCNF \<Rightarrow> formulaCNF"
  where 
    "unit_propagate c [] = []"
  | "unit_propagate c (c' # cs) = (let l = hd c 
                                   in
                                     (if contains l c' 
                                      then unit_propagate c cs
                                      else if contains (not l) c' then removeAll (not l) c' # unit_propagate c cs
                                      else c' # unit_propagate c cs)
                                   )" 


definition literals :: "formulaCNF \<Rightarrow> literal list"
  where
    "literals cs \<equiv> concat cs"

declare literals_def[simp]

definition pure_literal :: "literal \<Rightarrow> formulaCNF \<Rightarrow> bool"
  where
    "pure_literal l cs = (l \<in> set (literals cs) \<and> (not l) \<notin> set (literals cs))"

value "1 \<notin> ({}::nat set)"
fun pure_literall :: "literal \<Rightarrow> formulaCNF \<Rightarrow> bool"
  where
    "pure_literall l [] = False"
  | "pure_literall l (c # cs) = (contains l c \<and> \<not>contains (not l) c \<and> pure_literall l cs)"

definition pure_literals :: "formulaCNF \<Rightarrow> literal list"
  where
    "pure_literals cs = filter (\<lambda>l. pure_literall l cs ) (literals cs)"

declare pure_literals_def[simp]

fun pure_literal_assign :: "literal \<Rightarrow> formulaCNF \<Rightarrow> formulaCNF"
  where
    "pure_literal_assign l [] = []"
  | "pure_literal_assign l (c # cs) = (if contains l c then pure_literal_assign l cs else c # (pure_literal_assign l cs))"



fun pure_literal_elimm :: "formulaCNF \<Rightarrow> literal list \<Rightarrow> formulaCNF"
  where
    "pure_literal_elimm cs [] = cs"
  | "pure_literal_elimm cs (l # ls) = pure_literal_elimm (pure_literal_assign l cs) ls"

fun pure_literal_elim :: "formulaCNF \<Rightarrow> formulaCNF"
  where
    "pure_literal_elim cs = fold (\<lambda>l cs. pure_literal_assign l cs) (pure_literals cs) cs"


fun falt :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a"
  where
    "falt f a [] = a"
  | "falt f a (x # xs) = falt f (f x a) xs"

fun unit_propagate_all :: "formulaCNF \<Rightarrow> clauseCNF list \<Rightarrow> formulaCNF"
  where
    "unit_propagate_all cs [] = cs"
  | "unit_propagate_all cs (uc # ucs) = unit_propagate_all (unit_propagate uc cs) ucs"

lemma "unit_propagate_all cs ucs = fold (\<lambda>uc. unit_propagate uc) ucs cs"
  apply (induction ucs arbitrary: cs)
  apply auto
  done

definition uprog :: "formulaCNF \<Rightarrow> formulaCNF" where "uprog cs \<equiv> fold (\<lambda>uc. unit_propagate uc) (unit_clauses cs) cs"

text\<open>
uprog cs (u # uc) = uprog (uprog cs u) uc"
\<close>

fun choose_literal :: "formulaCNF \<Rightarrow> literal"
  where
    "choose_literal cs = (if (literals cs) = [] then undefined else (hd (literals cs)))"

fun subst :: "formulaCNF \<Rightarrow> literal \<Rightarrow> bool \<Rightarrow> formulaCNF"
  where
    "subst [] l b = []"
  | "subst (c # cs) l b = (case b of False \<Rightarrow> removeAll l c # subst cs l b |
                                     True \<Rightarrow> (if contains l c then subst cs l b else c # subst cs l b)) "

definition consistent :: "formulaCNF \<Rightarrow> bool"
  where
    "consistent cs = (\<forall>l \<in> set (literals cs). (not l) \<notin> set (literals cs))"

declare consistent_def[simp]

text
\<open>
http://poincare.matf.bg.ac.rs/~filip/phd/classic-dpll-verification.pdf

Termination proof can be made manually ! 


\<close>

value "solver_bruteforce [[P ''x'', P ''y''], [P ''z'', P ''y''], [N ''y'']]"
value "pure_literal_elim (uprog [[P ''x'', P ''y''], [P ''z'', P ''y''], [N ''y'']])"
value "consistent (subst (pure_literal_elim (uprog [[P ''x'', P ''y''], [P ''z'', P ''y''], [N ''y'']])) (P ''x'') True)"
value "subst (pure_literal_elim (uprog [[P ''x'', P ''y''], [P ''z'', P ''y''], [N ''y'']])) (P ''z'') True"

fun size :: "formulaCNF \<Rightarrow> nat"
  where
    "size []  = 0"
  | "size (c # cs) = length c + size cs"


lemma size_unit_propagate: "size (unit_propagate c cs) \<le> size cs"
  apply (induction cs arbitrary: c)
   apply auto
  by (smt add_mono_thms_linordered_semiring(1) le_add1 le_add_same_cancel1 length_removeAll_less_eq list.inject nat_add_left_cancel_le size.elims trans_le_add2)


declare uprog_def[simp]

lemma size_unit_propagate_all: "size (unit_propagate_all cs ucs) \<le> size cs"
  apply (induction ucs arbitrary: cs)
   apply auto
  using le_trans size_unit_propagate by blast

lemma size_pure_literal_assign: "size (pure_literal_assign l cs) \<le> size cs"
  apply (induction cs)
   apply auto
  done
lemma size_pure_literal_elim: "size (pure_literal_elimm cs ls) \<le> size cs"
  apply (induction ls arbitrary: cs)
   apply auto
  using size_pure_literal_assign le_trans by blast

lemma size_subst_weak: "size (subst cs l b) \<le> size cs"
  apply (induction cs)
   apply (auto split: bool.split)
  by (simp add: add_mono_thms_linordered_semiring(1))



lemma size_subst_False:"l \<in> set (literals cs) \<Longrightarrow> size (subst cs l False) < size cs"
  apply (induction cs)
   apply auto
   apply (simp add: add_less_le_mono length_removeAll_less size_subst_weak)
  by (meson add_le_less_mono length_removeAll_less_eq)



lemma contains_iff_elem: "contains l c \<longleftrightarrow> l \<in> set c"
  apply (induction c)
   apply auto
  done


lemma size_partition_filter: "size cs = size (filter (\<lambda>x. K x) cs) + size (filter (\<lambda>x. \<not>K x) cs)"
  apply (induction cs)
   apply auto
  done
lemma subst_True_filter_def: "subst cs l True = filter (\<lambda>c. \<not>contains l c) cs"
  apply (induction cs)
  apply auto
  done

lemma contains_size: "contains c cs \<Longrightarrow> size [c] \<le> size cs"
  apply (induction cs)
   apply (auto split: if_splits)
  done

lemma size_subst_True: "l \<in> set (literals cs) \<Longrightarrow> size (subst cs l True) < size cs"
proof-
  assume assm: "l \<in> set (literals cs)"
  then have "\<exists>c \<in> set cs. contains l c" using contains_iff_elem[symmetric] by force
  then obtain c where cdef:"c \<in> set cs \<and> contains l c" by blast
  then have "length c > 0" using assm by auto


  have "contains c (filter (\<lambda>c. contains l c) cs)" using cdef by (simp add: contains_iff_elem)
  then have "size (filter (\<lambda>c. contains l c) cs) \<ge> size [c]" using contains_size cdef by blast
  then have *: "size (filter (\<lambda>c. contains l c) cs) > 0" using \<open>length c > 0\<close> 
    using gr_zeroI by fastforce

   
  have "size cs = size (filter (\<lambda>c. contains l c) cs) + size (subst cs l True)" using size_partition_filter subst_True_filter_def by auto
  
  then show "size (subst cs l True) < size cs" using subst_True_filter_def * by simp
qed
  
lemma size_subst_strong: "l \<in> set (literals cs) \<Longrightarrow> size (subst cs l b) < size cs"
  using size_subst_True size_subst_False by (cases b) auto


lemma size_subst_main: "literals cs \<noteq> [] \<Longrightarrow> l = choose_literal cs \<Longrightarrow> size (subst cs l b) < size cs"
proof -
  assume assms: "literals cs \<noteq> []" "l = choose_literal cs"
  then have " l = hd (literals cs)" by auto
  then have " l \<in> set (literals cs)" using assms 
    using list.set_sel(1) by blast
  then show ?thesis using size_subst_strong by simp
qed



function solver_dpll :: "formulaCNF \<Rightarrow> bool"
  where
    "solver_dpll cs = (if consistent cs then True
                       else if contains [] cs then False
                       else
                         let cs\<^sub>1 = unit_propagate_all cs (unit_clauses cs); cs\<^sub>2 = pure_literal_elimm cs\<^sub>1 (pure_literals cs\<^sub>1); l = choose_literal cs\<^sub>2
                         in 
                           (if literals cs\<^sub>2 = [] then (if contains [] cs\<^sub>2 then False else True)
                            else
                              solver_dpll (subst cs\<^sub>2 l True) \<or> (solver_dpll (subst cs\<^sub>2 l False))
                           )
                       )"
  by pat_completeness auto
termination 
  apply (relation "measure (\<lambda>cs. (size cs))") 
    apply (auto simp: size_pure_literal_elim size_unit_propagate_all size_subst_main split: if_splits)
   apply (smt Nil_eq_concat_conv le_trans list.set_sel(1) literals_def not_le size_pure_literal_elim size_subst_strong size_unit_propagate_all)
  by (smt Nil_eq_concat_conv antisym leI le_trans list.set_sel(1) literals_def size_pure_literal_elim size_subst_weak size_subst_strong size_unit_propagate_all)
  
  

end