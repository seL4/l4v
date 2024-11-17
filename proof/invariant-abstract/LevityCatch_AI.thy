(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory LevityCatch_AI
imports
  ArchLevityCatch_AI
begin

(* FIXME: eliminate mapM_UNIV_wp, use mapM_wp' directly *)
lemmas mapM_UNIV_wp = mapM_wp'

arch_requalify_consts
  ptrFromPAddr addrFromPPtr

arch_requalify_facts
  ptrFormPAddr_addFromPPtr
  aobj_ref_arch_cap
  arch_finalise_cap_bcorres
  prepare_thread_delete_bcorres

lemmas aobj_ref_arch_cap_simps[simp] = aobj_ref_arch_cap

lemmas [wp] = arch_finalise_cap_bcorres prepare_thread_delete_bcorres

lemma detype_arch_state:
  "arch_state (detype S s) = arch_state s"
  by (simp add: detype_def)

lemma obj_ref_elemD:
  "r \<in> obj_refs cap \<Longrightarrow> obj_refs cap = {r}"
  by (cases cap; simp)

lemma get_cap_id:
  "(v, s') \<in> fst (get_cap p s) \<Longrightarrow> (s' = s)"
  by (clarsimp simp: get_cap_def get_object_def read_object_def gets_the_def
                     split_def gets_def get_def assert_opt_def bind_def
                     return_def fail_def assert_def
              split: option.splits)
     (rename_tac ko a; case_tac ko;
      simp add: fail_def bind_def return_def assert_def split: if_split_asm)

lemmas cap_irq_opt_simps[simp] =
  cap_irq_opt_def [split_simps cap.split sum.split]

lemmas cap_irqs_simps[simp] =
    cap_irqs_def [unfolded cap_irq_opt_def, split_simps cap.split sum.split, simplified option.simps]

declare liftE_wp[wp]
declare case_sum_True[simp]

crunch_ignore (add: do_extended_op)

lemma None_Some_strg:
  "x = None \<Longrightarrow> x \<noteq> Some y"
  by simp

(* Weakest precondition lemmas that need ASpec concepts: *)

lemma const_on_failure_wp:
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>rv. Q n\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> const_on_failure n m \<lbrace>Q\<rbrace>"
  by (wpsimp simp: const_on_failure_def)

(* Weaker wp rule for arguments "a" which do not take type det_ext state.
   The stronger rule below will take precendence, because it is declared [wp]
   later than this one. This rule here will fire when the stronger one does not
   apply because of a looser type than det_ext state. The looser type tends to
   happen in goals that are stated by crunch. *)
lemma select_ext_weak_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>x\<in>S. Q x s\<rbrace> select_ext a S \<lbrace>Q\<rbrace>"
  by (wpsimp simp: select_ext_def)

(* The "real" wp rule for select_ext, requires det_ext state: *)
lemma select_ext_wp[wp]:
  "\<lbrace>\<lambda>s. a s \<in> S \<longrightarrow> Q (a s) s\<rbrace> select_ext a S \<lbrace>Q\<rbrace>"
  unfolding select_ext_def unwrap_ext_det_ext_ext_def
  by (wpsimp simp: select_switch_det_ext_ext_def)

end
