(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_Det
  imports
    Trace_Monad
begin

subsection "Determinism"

text \<open>
  A monad of type @{text tmonad} is deterministic iff it
  returns an empty trace, exactly one state and result and does not fail\<close>
definition det :: "('a,'s) tmonad \<Rightarrow> bool" where
  "det f \<equiv> \<forall>s. \<exists>r. f s = {([], Result r)}"

text \<open>A deterministic @{text tmonad} can be turned into a normal state monad:\<close>
definition the_run_state :: "('s,'a) tmonad \<Rightarrow> 's \<Rightarrow> 'a \<times> 's" where
  "the_run_state M \<equiv> \<lambda>s. THE s'. mres (M s) = {s'}"


lemma det_set_iff:
  "det f \<Longrightarrow> (r \<in> mres (f s)) = (mres (f s) = {r})"
  unfolding det_def mres_def
  by (fastforce elim: allE[where x=s])

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
  "det f \<Longrightarrow> (\<Union>x \<in> mres (f s). g x) = (g (THE x. x \<in> mres (f s)))"
  unfolding det_def mres_def
  apply simp
  apply (drule spec [of _ s])
  apply (clarsimp simp: vimage_def)
  done

lemma bind_detI[simp, intro!]:
  "\<lbrakk> det f; \<forall>x. det (g x) \<rbrakk> \<Longrightarrow> det (f >>= g)"
  unfolding bind_def det_def
  apply clarsimp
  apply (erule_tac x=s in allE)
  apply clarsimp
  done

lemma det_modify[iff]:
  "det (modify f)"
  by (simp add: modify_def)

lemma the_run_stateI:
  "mres (M s) = {s'} \<Longrightarrow> the_run_state M s = s'"
  by (simp add: the_run_state_def)

lemma the_run_state_det:
  "\<lbrakk> s' \<in> mres (M s); det M \<rbrakk> \<Longrightarrow> the_run_state M s = s'"
  by (simp add: the_run_stateI det_set_iff)

end
