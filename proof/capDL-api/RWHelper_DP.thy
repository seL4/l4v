(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory RWHelper_DP
imports ProofHelpers_DP KHeap_DP
begin

lemma intent_reset_twice[simp]:
 "intent_reset (intent_reset z) = intent_reset z"
  apply (case_tac z)
  apply (simp_all add:intent_reset_def)
  done

(* We need some predicates in the future to make sure schedule will do the right thing *)

definition "scheduable_cap cap \<equiv> case cap of
  RunningCap \<Rightarrow> True | RestartCap \<Rightarrow> True | _ \<Rightarrow> False"

definition tcb_scheduable :: "cdl_tcb \<Rightarrow> bool"
  where "tcb_scheduable \<equiv> \<lambda>tcb. (cdl_tcb_caps tcb) tcb_pending_op_slot
  = Some RunningCap \<or> (cdl_tcb_caps tcb) tcb_pending_op_slot = Some RestartCap"

abbreviation "tcb_at_heap \<equiv> \<lambda>P ptr heap.
  object_at_heap (\<lambda>obj. \<exists>tcb. obj = Tcb tcb  \<and>  P tcb)  ptr heap"

definition all_scheduable_tcbs :: "(word32 \<Rightarrow> cdl_object option) \<Rightarrow> cdl_object_id set"
where  "all_scheduable_tcbs \<equiv> \<lambda>m. {ptr. tcb_at_heap tcb_scheduable ptr m}"

definition sep_all_scheduable_tcbs :: "(32 word \<times> cdl_component_id \<Rightarrow> cdl_component option) \<Rightarrow> cdl_object_id set"
where "sep_all_scheduable_tcbs m \<equiv> {ptr. \<exists>obj cap. m (ptr,Fields) = Some (CDL_Object obj) \<and> is_tcb obj
  \<and> m (ptr,Slot tcb_pending_op_slot) = Some (CDL_Cap (Some cap)) \<and> scheduable_cap cap}"

lemma is_tcb_obj_type:
  "is_tcb = (\<lambda>x. object_type x = TcbType)"
  by (auto simp:is_tcb_def object_type_def split:cdl_object.splits)

lemma all_scheduable_tcbs_rewrite:
  "all_scheduable_tcbs (cdl_objects s) =
  sep_all_scheduable_tcbs (sep_heap (sep_state_projection s))"
 apply (intro set_eqI iffI)
  apply (clarsimp simp:all_scheduable_tcbs_def sep_state_projection_def
    sep_all_scheduable_tcbs_def object_at_heap_def object_project_def
    is_tcb_obj_type)
  apply (clarsimp simp:object_type_def object_slots_object_clean
    tcb_scheduable_def object_slots_def scheduable_cap_def)
  apply (fastforce simp:object_clean_def asid_reset_def update_slots_def
    reset_cap_asid_def intent_reset_def object_slots_def
    split:if_splits)
 apply (clarsimp simp:all_scheduable_tcbs_def sep_state_projection_def
    sep_all_scheduable_tcbs_def object_at_heap_def object_project_def
    is_tcb_obj_type split:option.splits)
 apply (clarsimp simp:object_type_def tcb_scheduable_def
   scheduable_cap_def object_slots_def object_clean_def asid_reset_def
   update_slots_def intent_reset_def reset_cap_asid_def
   split:cdl_object.splits cdl_cap.splits option.splits)
 done

lemma sep_inv_to_all_scheduable_tcbs:
  assumes sep: "\<And>P. \<lbrace><P>\<rbrace> f \<lbrace>\<lambda>r. <P>\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (all_scheduable_tcbs (cdl_objects s))\<rbrace> f
   \<lbrace>\<lambda>r s. P (all_scheduable_tcbs (cdl_objects s))\<rbrace>"
  apply (clarsimp simp:valid_def all_scheduable_tcbs_rewrite)
  apply (erule use_valid)
   apply (rule hoare_strengthen_post)
    apply (rule sep)
   apply assumption
  apply simp
  done

end
