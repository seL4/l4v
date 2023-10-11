(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Peep-hole L1 optimisations. *)

theory L1Peephole
imports L1Defs
begin

(* Simplification rules run after L1. *)
named_theorems L1opt

lemma L1_seq_assoc [L1opt]: "(L1_seq (L1_seq X Y) Z) = (L1_seq X (L1_seq Y Z))"
  by (clarsimp simp: L1_seq_def bindE_assoc)

lemma L1_seq_skip [L1opt]:
  "L1_seq A L1_skip = A"
  "L1_seq L1_skip A = A"
  by (clarsimp simp: L1_seq_def L1_skip_def)+

lemma L1_condition_true [L1opt]: "L1_condition (\<lambda>_. True) A B = A"
  by (clarsimp simp: L1_condition_def condition_def)

lemma L1_condition_false [L1opt]: "L1_condition (\<lambda>_. False) A B = B"
  by (clarsimp simp: L1_condition_def condition_def)

lemma L1_condition_same [L1opt]: "L1_condition C A A = A"
  by (clarsimp simp: L1_condition_def condition_def)

lemma L1_fail_seq [L1opt]: "L1_seq L1_fail X = L1_fail"
  by (clarsimp simp: L1_seq_def L1_fail_def)

lemma L1_throw_seq [L1opt]: "L1_seq L1_throw X = L1_throw"
  by (clarsimp simp: L1_seq_def L1_throw_def)

lemma L1_fail_propagates [L1opt]:
  "L1_seq L1_skip L1_fail = L1_fail"
  "L1_seq (L1_modify M) L1_fail = L1_fail"
  "L1_seq (L1_spec S) L1_fail = L1_fail"
  "L1_seq (L1_guard G) L1_fail = L1_fail"
  "L1_seq (L1_init I) L1_fail = L1_fail"
  "L1_seq L1_fail L1_fail = L1_fail"
  unfolding L1_defs
  by (auto intro!: bindE_fail_propagates empty_fail_bindE no_throw_bindE [where B="\<top>"] hoare_TrueI
           simp: empty_fail_error_bits)

lemma L1_condition_distrib:
  "L1_seq (L1_condition C L R) X = L1_condition C (L1_seq L X) (L1_seq R X)"
  unfolding L1_defs
  by (fastforce simp: condition_def cong: bindE_apply_cong split: condition_splits)

lemmas L1_fail_propagate_condition [L1opt] = L1_condition_distrib [where X=L1_fail]

lemma L1_fail_propagate_catch [L1opt]:
  "(L1_seq (L1_catch L R) L1_fail) = (L1_catch (L1_seq L L1_fail) (L1_seq R L1_fail))"
  unfolding L1_defs
  apply (clarsimp simp: bindE_def handleE'_def handleE_def bind_assoc)
  apply (rule arg_cong [where f="Nondet_Monad.bind L"])
  apply (fastforce split: sum.splits simp: throwError_def)
  done

lemma L1_guard_false [L1opt]:
  "L1_guard (\<lambda>_. False) = L1_fail"
  by (monad_eq simp: L1_guard_def L1_fail_def)

lemma L1_guard_true [L1opt]:
  "L1_guard (\<lambda>_. True) = L1_skip"
  by (monad_eq simp: L1_guard_def L1_skip_def)

lemma L1_condition_fail_lhs [L1opt]:
  "L1_condition C L1_fail A = L1_seq (L1_guard (\<lambda>s. \<not> C s)) A"
  by (monad_eq simp: L1_condition_def L1_guard_def L1_fail_def L1_seq_def) blast

lemma L1_condition_fail_rhs [L1opt]:
  "L1_condition C A L1_fail = L1_seq (L1_guard C) A"
  by (monad_eq simp: L1_condition_def L1_guard_def L1_fail_def L1_seq_def)

lemma L1_catch_fail [L1opt]: "L1_catch L1_fail A = L1_fail"
  by (clarsimp simp: L1_catch_def L1_fail_def)

lemma L1_while_fail [L1opt]: "L1_while C L1_fail = L1_guard (\<lambda>s. \<not> C s)"
  unfolding L1_while_def
  by (clarsimp split: condition_splits simp: whileLoopE_unroll)
     (monad_eq simp: L1_fail_def L1_guard_def)

lemma L1_while_infinite [L1opt]: "L1_while C L1_skip = L1_guard (\<lambda>s. \<not> C s)"
  apply (clarsimp simp: L1_while_def L1_guard_def L1_skip_def whileLoopE_def)
  apply (rule ext)
  apply (case_tac "C x")
   apply (rule whileLoop_rule_strong)
       apply (rule_tac I="\<lambda>r s. (\<exists>x. r = Inr x) \<and> s = x \<and> C s" in valid_whileLoop)
        apply simp
       apply (monad_eq simp: valid_def split: sum.splits)
      apply simp
     apply (subst whileLoop_unroll)
     apply (monad_eq simp: exs_valid_def Bex_def split: if_split_asm)
    apply (rule snd_whileLoop [where I="\<lambda>_ _. True"])
      apply simp
     apply simp
    apply (monad_eq simp: exs_valid_def Bex_def split: sum.splits cong: HOL.conj_cong)
   apply monad_eq
  apply (subst whileLoop_unroll)
  apply monad_eq
  done

lemma L1_while_false [L1opt]:
  "L1_while (\<lambda>_. False) B = L1_skip"
  apply (clarsimp simp: L1_while_def L1_skip_def)
  apply (subst whileLoopE_unroll)
  apply clarsimp
  done

declare ucast_id [L1opt]
declare scast_id [L1opt]
declare L1_set_to_pred_def [L1opt]

(*
 * The following sets of rules are used to simplify conditionals,
 * removing set notation (converting into predicate notation) and
 * generally removing logical cruft without being too aggressive in our
 * simplification.
 *)

lemma in_set_to_pred [L1opt]: "(\<lambda>s. s \<in> {x. P x}) = P"
  by simp

lemma in_set_if_then [L1opt]: "(s \<in> (if P then A else B)) = (if P then (s \<in> A) else (s \<in> B))"
  by simp

lemmas if_simps =
  if_x_Not if_Not_x if_cancel if_True if_False if_bool_simps

declare empty_iff [L1opt]
declare UNIV_I [L1opt]
declare singleton_iff [L1opt]
declare if_simps [L1opt]
declare simp_thms [L1opt]

end
