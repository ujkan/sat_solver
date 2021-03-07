theory Solver
  imports Main
begin

datatype Formula = Var string | Const bool | Not Formula | And Formula Formula | Or Formula Formula

type_synonym state = "string \<Rightarrow> bool"

fun eval :: "Formula \<Rightarrow> state \<Rightarrow> bool"
  where
    "eval (Const b) s = b"
  | "eval (Var x) s = s x"
  | "eval (Not F) s = (\<not>(eval F s))"
  | "eval (And F G) s = (eval F s \<and> eval G s)"
  | "eval (Or F G) s = (eval F s \<or> eval G s)"






end