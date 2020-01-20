(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Corres_Adjust_Preconds

imports
  "Corres_UL"

begin

text \<open>
Gadget for adjusting preconditions in a corres rule or similar.

Probably only useful for predicates with two or more related
preconditions, such as corres.

Used to do some_corres_rule[adj_corres some_intro_rule],
given e.g. some_intro_rule: @{prop "(s, t) \<in> sr \<Longrightarrow> P s \<Longrightarrow> Q t"}
Will apply this rule to solve @{prop "Q t"} components in either
precondition or any sub-conjunct, and will then try to put the
assumptions @{prop "P s"}, @{prop "(s, t) \<in> sr"} into the right
places. The premises of the rule can be in any given order.

Concrete example at the bottom.
\<close>

named_theorems corres_adjust_precond_structures

locale corres_adjust_preconds begin

text \<open>Worker predicates. Broadly speaking, a goal
of the form "preconds ?A ?B ?C ?D ==> P" expects to
establish P by instantiating ?A, or failing that ?B,
etc.

A goal of the form finalise_preconds A exists to
make sure that schematic conjuncts of A are resolved
to True.\<close>
definition
  preconds :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "preconds A B C D = (A \<and> B \<and> C \<and> D)"

definition
  finalise_preconds :: "bool \<Rightarrow> bool"
where
  "finalise_preconds A = True"

text \<open>Use a precond directly to establish goal.\<close>
lemma consume_preconds:
  "preconds A True True True \<Longrightarrow> A"
  "preconds True B True True \<Longrightarrow> B"
  "preconds True True C True \<Longrightarrow> C"
  "preconds True True True D \<Longrightarrow> D"
  by (simp_all add: preconds_def)

lemmas consume_preconds_True = consume_preconds(1)[where A=True]

text \<open>For use as a drule, split a set of schematic preconds
to give two sets that can be instantiated separately.\<close>
lemma split_preconds_left:
  "preconds (A \<and> A') (B \<and> B') (C \<and> C') (D \<and> D') \<Longrightarrow> preconds A B C D"
  "preconds (A \<and> A') (B \<and> B') (C \<and> C') True \<Longrightarrow> preconds A B C True"
  "preconds (A \<and> A') (B \<and> B') True True \<Longrightarrow> preconds A B True True"
  "preconds (A \<and> A') True True True \<Longrightarrow> preconds A True True True"
  by (simp_all add: preconds_def)

lemma split_preconds_right:
  "preconds (A \<and> A') (B \<and> B') (C \<and> C') (D \<and> D') \<Longrightarrow> preconds A' B' C' D'"
  "preconds (A \<and> A') (B \<and> B') (C \<and> C') True \<Longrightarrow> preconds A' B' C' True"
  "preconds (A \<and> A') (B \<and> B') True True \<Longrightarrow> preconds A' B' True True"
  "preconds (A \<and> A') True True True \<Longrightarrow> preconds A' True True True"
  by (simp_all add: preconds_def)

text \<open>For use as an erule. Initiate the precond process,
creating a finalise goal to be solved later.\<close>
lemma preconds_goal_initiate:
  "preconds A B C D \<Longrightarrow> (preconds A B C D \<Longrightarrow> Q)
    \<Longrightarrow> finalise_preconds (A \<and> B \<and> C \<and> D) \<Longrightarrow> Q"
  by simp

text \<open>Finalise preconds, trying to replace conjuncts with
True if they are not yet instantiated.\<close>
lemma finalise_preconds:
  "finalise_preconds True"
  "finalise_preconds A \<Longrightarrow> finalise_preconds B \<Longrightarrow> finalise_preconds (A \<and> B)"
  "finalise_preconds X"
  by (simp_all add: finalise_preconds_def)

text \<open>Shape of the whole process for application to regular corres goals.\<close>
lemma corres_adjust_pre:
  "corres_underlying R nf nf' rs P Q  f f'
    \<Longrightarrow> (\<And>s s'. (s, s') \<in> R \<Longrightarrow> preconds (P1 s) (Q1 s') True True \<Longrightarrow> P s)
    \<Longrightarrow> (\<And>s s'. (s, s') \<in> R \<Longrightarrow> preconds (Q2 s') (P2 s) True True \<Longrightarrow> Q s')
    \<Longrightarrow> corres_underlying R nf nf' rs (\<lambda>s. P1 s \<and> P2 s) (\<lambda>s'. Q1 s' \<and> Q2 s') f f'"
  apply (erule stronger_corres_guard_imp)
   apply (simp add: preconds_def)+
  done

ML \<open>

structure Corres_Adjust_Preconds = struct

val def_intros = @{thms conjI pred_conj_app[THEN iffD2]
    bipred_conj_app[THEN fun_cong, THEN iffD2]}

(* apply an intro rule, splitting preconds assumptions to
   provide unique assumptions for each goal. *)
fun intro_split ctxt intros i =
  ((resolve_tac ctxt intros
        THEN_ALL_NEW (TRY o assume_tac ctxt))
    THEN_ALL_NEW (fn j => (EVERY (replicate (j - i) (dresolve_tac ctxt @{thms split_preconds_left} j)))
        THEN dresolve_tac ctxt @{thms split_preconds_right} j)) i

fun handle_preconds ctxt intros =
  TRY o (eresolve_tac ctxt [@{thm preconds_goal_initiate}]
    THEN' REPEAT_ALL_NEW (eresolve_tac ctxt @{thms consume_preconds_True}
        ORELSE' intro_split ctxt (intros @ def_intros)
        ORELSE' eresolve_tac ctxt @{thms consume_preconds})
    THEN' REPEAT_ALL_NEW (resolve_tac ctxt @{thms finalise_preconds})
  )

fun mk_adj_preconds ctxt intros rule = let
    val xs = [rule] RL (Named_Theorems.get ctxt @{named_theorems corres_adjust_precond_structures})
    val x = case xs of
        [] => raise THM ("no unifier with corres_adjust_precond_structures", 1, [rule])
      | xs => hd xs
  in x
    |> ALLGOALS (handle_preconds ctxt intros)
    |> Seq.hd
    |> Simplifier.simplify (clear_simpset ctxt addsimps @{thms conj_assoc simp_thms(21-22)})
  end

val setup =
      Attrib.setup @{binding "adj_corres"}
          ((Attrib.thms -- Args.context)
              >> (fn (intros, ctxt) => Thm.rule_attribute [] (K (mk_adj_preconds ctxt intros))))
          "use argument theorems to adjust a corres theorem."

end

\<close>

end

declare corres_adjust_preconds.corres_adjust_pre[corres_adjust_precond_structures]

setup Corres_Adjust_Preconds.setup

experiment begin

definition
  test_sr :: "(nat \<times> nat) set"
where
  "test_sr = {(x, y). y = 2 * x}"

lemma test_corres:
  "corres_underlying test_sr nf nf' dc (\<lambda>x. x < 40) (\<lambda>y. y < 30 \<and> y = 6)
    (modify (\<lambda>x. x + 2)) (modify (\<lambda>y. 10))"
  by (simp add: corres_underlying_def simpler_modify_def test_sr_def)

lemma test_adj_precond:
  "(x, y) \<in> test_sr \<Longrightarrow> x = 3 \<Longrightarrow> y = 6"
  by (simp add: test_sr_def)

ML \<open>
Corres_Adjust_Preconds.mk_adj_preconds @{context} [@{thm test_adj_precond}] @{thm test_corres}
\<close>

lemma foo_adj_corres:
  "corres_underlying test_sr nf nf' dc (\<lambda>s. s < 40 \<and> s = 3) (\<lambda>s'. s' < 30) (modify (\<lambda>x. x + 2))
       (modify (\<lambda>y. 10))"
  by (rule test_corres[adj_corres test_adj_precond])

text \<open>A more general demo of what it does.\<close>
lemma
  assumes my_corres: "corres_underlying my_sr nf nf' rvrel P Q a c"
  assumes my_adj: "\<And>s s'. (s,s') \<in> my_sr \<Longrightarrow> P s \<Longrightarrow> Q s'"
  shows "corres_underlying my_sr nf nf' rvrel (\<lambda>s. P s \<and> P s) (\<lambda>s'. True) a c"
  apply (rule my_corres[adj_corres my_adj])
  done

end

end
