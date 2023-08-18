(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Nondet_Det
  imports
    Nondet_Monad
begin

subsection "Determinism"

text \<open>A monad of type @{text nondet_monad} is deterministic iff it returns exactly one state and
  result and does not fail\<close>
definition det :: "('a,'s) nondet_monad \<Rightarrow> bool" where
  "det f \<equiv> \<forall>s. \<exists>r. f s = ({r},False)"

text \<open>A deterministic @{text nondet_monad} can be turned into a normal state monad:\<close>
definition the_run_state :: "('s,'a) nondet_monad \<Rightarrow> 's \<Rightarrow> 'a \<times> 's" where
  "the_run_state M \<equiv> \<lambda>s. THE s'. fst (M s) = {s'}"


lemma det_set_iff:
  "det f \<Longrightarrow> (r \<in> fst (f s)) = (fst (f s) = {r})"
  unfolding det_def
  by (metis fst_conv singleton_iff)

lemma return_det[iff]:
  "det (return x)"
  by (simp add: det_def return_def)

lemma put_det[iff]:
  "det (put s)"
  by (simp add: det_def put_def)

lemma get_det[iff]:
  "det get"
  by (simp add: det_def get_def)

lemma det_gets[iff]:
  "det (gets f)"
  by (auto simp add: gets_def det_def get_def return_def bind_def)

lemma det_UN:
  "det f \<Longrightarrow> (\<Union>x \<in> fst (f s). g x) = (g (THE x. x \<in> fst (f s)))"
  unfolding det_def
  by (smt (verit) SUP_eq_const emptyE fst_conv singletonD singletonI the1_equality)

lemma bind_detI[simp, intro!]:
  "\<lbrakk> det f; \<forall>x. det (g x) \<rbrakk> \<Longrightarrow> det (f >>= g)"
  unfolding bind_def det_def
  apply clarsimp
  apply (erule_tac x=s in allE)
  apply clarsimp
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)
  apply clarsimp
  done

lemma det_modify[iff]:
  "det (modify f)"
  by (simp add: modify_def)

lemma the_run_stateI:
  "fst (M s) = {s'} \<Longrightarrow> the_run_state M s = s'"
  by (simp add: the_run_state_def)

lemma the_run_state_det:
  "\<lbrakk> s' \<in> fst (M s); det M \<rbrakk> \<Longrightarrow> the_run_state M s = s'"
  by (simp add: the_run_stateI det_set_iff)

end
