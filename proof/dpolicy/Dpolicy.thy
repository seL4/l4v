(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Dpolicy
imports
  "Access.ArchAccess_AC"
  "DRefine.Refine_D"
  "DBaseRefine.Include_D"
begin

(*
This file proves that the authority granted by any abstract state that
satisfies the extended invariants agrees with the authority granted by the
corresponding capDL state. This result is given by the final lemma in the file,
pas_refined_transform.

More details of this result and how it is used can be found in Section 6.1 of
"Comprehensive Formal Verification of an OS Microkernel", which can be
downloaded from
https://trustworthy.systems/publications/nictaabstracts/Klein_AEMSKH_14.abstract
*)

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  cdl_cap_auth_conferred :: "cdl_cap \<Rightarrow> auth set"
where
 "cdl_cap_auth_conferred cap \<equiv>
    case cap of
      cdl_cap.NullCap \<Rightarrow> {}
    | cdl_cap.UntypedCap dev refs frange \<Rightarrow> {Control}
    | cdl_cap.EndpointCap oref badge r \<Rightarrow>
         cap_rights_to_auth r True
    | cdl_cap.NotificationCap oref badge r \<Rightarrow>
         cap_rights_to_auth (r - {AllowGrant, AllowGrantReply}) False
    | cdl_cap.ReplyCap oref r \<Rightarrow> reply_cap_rights_to_auth False r
    | cdl_cap.MasterReplyCap oref \<Rightarrow> UNIV
    | cdl_cap.CNodeCap oref bits guard sz \<Rightarrow> {Control}
    | cdl_cap.TcbCap obj_ref \<Rightarrow> {Control}
    | cdl_cap.DomainCap \<Rightarrow> {Control}
    | cdl_cap.PendingSyncSendCap oref badge call grant grant_reply fault \<Rightarrow>
          {SyncSend} \<union> (if grant then {Types.Grant, Call} else {})
          \<union> (if grant_reply then {Call} else {})
    | cdl_cap.PendingSyncRecvCap oref fault grant \<Rightarrow>
          (if fault then {} else {Receive}) \<union> (if grant then {Types.Grant} else {})
    | cdl_cap.PendingNtfnRecvCap oref \<Rightarrow> {Receive}
    | cdl_cap.RestartCap \<Rightarrow> {}
    | cdl_cap.IrqControlCap \<Rightarrow> {Control}
    | cdl_cap.IrqHandlerCap irq \<Rightarrow> {Control}
    | cdl_cap.FrameCap dev oref r sz is_real asid \<Rightarrow> vspace_cap_rights_to_auth r
    | cdl_cap.PageTableCap oref is_real asid\<Rightarrow> {Control}
    | cdl_cap.PageDirectoryCap oref is_real asid \<Rightarrow> {Control}
    | cdl_cap.AsidControlCap \<Rightarrow> {Control}
    | cdl_cap.AsidPoolCap oref asid \<Rightarrow> {Control}
    | cdl_cap.ZombieCap ptr \<Rightarrow> {Control}
    | cdl_cap.BoundNotificationCap word \<Rightarrow> {Receive, Reset}
    | _ \<Rightarrow> {}"

fun
  cdl_obj_refs :: "cdl_cap \<Rightarrow> obj_ref set"
where
  "cdl_obj_refs cdl_cap.NullCap = {}"
| "cdl_obj_refs (cdl_cap.UntypedCap dev rs frange) = rs"
| "cdl_obj_refs (cdl_cap.EndpointCap r b cr) = {r}"
| "cdl_obj_refs (cdl_cap.NotificationCap r b cr) = {r}"
| "cdl_obj_refs (cdl_cap.ReplyCap r cr) = {r}"
| "cdl_obj_refs (cdl_cap.MasterReplyCap r) = {r}"
| "cdl_obj_refs (cdl_cap.CNodeCap r guard bits sz) = {r}"
| "cdl_obj_refs (cdl_cap.TcbCap r) = {r}"
| "cdl_obj_refs (cdl_cap.DomainCap) = UNIV"
| "cdl_obj_refs (cdl_cap.PendingSyncSendCap r badge call grant grant_reply fault) = {r}"
| "cdl_obj_refs (cdl_cap.PendingSyncRecvCap r grant fault) = {r}"
| "cdl_obj_refs (cdl_cap.PendingNtfnRecvCap r) = {r}"
| "cdl_obj_refs cdl_cap.RestartCap = {}"
| "cdl_obj_refs cdl_cap.IrqControlCap = {}"
| "cdl_obj_refs (cdl_cap.IrqHandlerCap irq) = {}"
| "cdl_obj_refs (cdl_cap.FrameCap dev x rs sz is_real asid) = ptr_range x sz"
| "cdl_obj_refs (cdl_cap.PageDirectoryCap x is_real asid) = {x}"
| "cdl_obj_refs (cdl_cap.PageTableCap x is_real asid) = {x}"
| "cdl_obj_refs (cdl_cap.AsidPoolCap p asid) = {p}"
| "cdl_obj_refs cdl_cap.AsidControlCap = {}"
| "cdl_obj_refs (cdl_cap.ZombieCap ptr) = {ptr}"
| "cdl_obj_refs (cdl_cap.BoundNotificationCap word) = {word}"
| "cdl_obj_refs _ = {}"

inductive cdl_cap_is_transferable for opt_cap
where
  cdl_it_None: "opt_cap = None \<Longrightarrow> cdl_cap_is_transferable opt_cap" |
  cdl_it_Null: "opt_cap = Some cdl_cap.NullCap \<Longrightarrow> cdl_cap_is_transferable opt_cap" |
  cdl_it_Reply: "opt_cap = Some (cdl_cap.ReplyCap t R) \<Longrightarrow> cdl_cap_is_transferable opt_cap"

inductive_set
  cdl_state_bits_to_policy for caps cdt
where
  csbta_caps: "\<lbrakk> caps ptr = Some cap; oref \<in> cdl_obj_refs cap;
                                            auth \<in> cdl_cap_auth_conferred cap \<rbrakk>
           \<Longrightarrow> (fst ptr, auth, oref) \<in> cdl_state_bits_to_policy caps cdt"
| csbta_cdt: "\<lbrakk> cdt slot' = Some slot; \<not>cdl_cap_is_transferable (caps slot') \<rbrakk>
           \<Longrightarrow> (fst slot, Control, fst slot') \<in> cdl_state_bits_to_policy caps cdt"
| csbta_cdt_transferable: "\<lbrakk> cdt slot' = Some slot \<rbrakk>
           \<Longrightarrow> (fst slot, DeleteDerived, fst slot') \<in> cdl_state_bits_to_policy caps cdt"

definition
  "cdl_state_objs_to_policy s = cdl_state_bits_to_policy (\<lambda>ref. opt_cap ref s)
                                               (cdl_cdt s)"

fun
  cdl_cap_irqs_controlled :: "cdl_cap \<Rightarrow> cdl_irq set"
where
  "cdl_cap_irqs_controlled cdl_cap.IrqControlCap = UNIV"
  | "cdl_cap_irqs_controlled (cdl_cap.IrqHandlerCap irq) = {irq}"
  | "cdl_cap_irqs_controlled _ = {}"

inductive_set
  cdl_state_irqs_to_policy_aux for aag caps
where
  csita_controlled: "\<lbrakk> caps ref = Some cap; irq \<in> cdl_cap_irqs_controlled cap \<rbrakk>
  \<Longrightarrow> (pasObjectAbs aag (fst ref), Control, pasIRQAbs aag irq) \<in>
                       cdl_state_irqs_to_policy_aux aag caps"

abbreviation
  "cdl_state_irqs_to_policy aag s \<equiv> cdl_state_irqs_to_policy_aux aag
                                                        (\<lambda>ref. opt_cap ref s)"

definition
  transform_asid_rev :: "cdl_asid \<Rightarrow> asid"
where
  "transform_asid_rev asid = (of_nat (fst asid) << asid_low_bits) + of_nat (snd asid)"

fun
  cdl_cap_asid' :: "cdl_cap \<Rightarrow> asid set"
where
    "cdl_cap_asid' (Types_D.FrameCap _ _ _ _ _ asid) = (transform_asid_rev o fst) ` set_option asid"
  | "cdl_cap_asid' (Types_D.PageTableCap _ _ asid) = (transform_asid_rev o fst) ` set_option asid"
  | "cdl_cap_asid' (Types_D.PageDirectoryCap _ _ asid) = transform_asid_rev ` set_option asid"
  | "cdl_cap_asid' (Types_D.AsidPoolCap _ asid) =
                                        {x. fst (transform_asid x) = asid \<and> x \<noteq> 0}"
  | "cdl_cap_asid' (Types_D.AsidControlCap) = UNIV"
  | "cdl_cap_asid' _ = {}"

definition
  is_null_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_null_cap cap \<equiv> case cap of
    cdl_cap.NullCap \<Rightarrow> True
  | _ \<Rightarrow> False"

inductive_set
  cdl_state_asids_to_policy_aux for aag caps asid_tab
where
    csata_asid: "\<lbrakk> caps ptr = Some cap; asid \<in> cdl_cap_asid' cap \<rbrakk> \<Longrightarrow>
                (pasObjectAbs aag (fst ptr), Control, pasASIDAbs aag asid) \<in>
                        cdl_state_asids_to_policy_aux aag caps asid_tab"
  | csata_asid_lookup: "\<lbrakk> asid_tab (fst (transform_asid asid)) = Some poolcap;
                          \<not> is_null_cap poolcap; \<not> is_null_cap pdcap; pdptr = cap_object pdcap;
                          caps (cap_object poolcap, snd (transform_asid asid)) = Some pdcap \<rbrakk> \<Longrightarrow>
                       (pasASIDAbs aag asid, Control, pasObjectAbs aag pdptr) \<in>
                                 cdl_state_asids_to_policy_aux aag caps asid_tab"
  | csata_asidpool: "\<lbrakk> asid_tab (fst (transform_asid asid)) = Some poolcap;
                       \<not> is_null_cap poolcap; asid \<noteq> 0 \<rbrakk> \<Longrightarrow>
                  (pasObjectAbs aag (cap_object poolcap), AAuth ASIDPoolMapsASID, pasASIDAbs aag asid) \<in>
                              cdl_state_asids_to_policy_aux aag caps asid_tab"

abbreviation
  "cdl_state_asids_to_policy aag s \<equiv> cdl_state_asids_to_policy_aux aag
                                (\<lambda>ref. opt_cap ref s) (cdl_asid_table s)"

definition
  "cdl_irq_map_wellformed_aux aag irqs \<equiv>
                  \<forall>irq. pasObjectAbs aag (irqs irq) = pasIRQAbs aag irq"

abbreviation
  "cdl_irq_map_wellformed aag s \<equiv> cdl_irq_map_wellformed_aux aag (cdl_irq_node s)"

inductive_set
  cdl_domains_of_state_aux for cdl_heap
where
  domtcbs: "\<lbrakk> cdl_heap ptr = Some (Tcb cdl_tcb);
              d = cdl_tcb_domain cdl_tcb\<rbrakk>
           \<Longrightarrow> (ptr, d) \<in> cdl_domains_of_state_aux cdl_heap" |
  domidle: "(idle_thread_ptr, default_domain) \<in> cdl_domains_of_state_aux cdl_heap"

abbreviation
  "cdl_domains_of_state s \<equiv> cdl_domains_of_state_aux (cdl_objects s)"

definition
  "cdl_tcb_domain_map_wellformed_aux aag tcbs_doms \<equiv>
      \<forall>(ptr, d) \<in> tcbs_doms. pasObjectAbs aag ptr \<in> pasDomainAbs aag d"

abbreviation
  "cdl_tcb_domain_map_wellformed aag s \<equiv>
   cdl_tcb_domain_map_wellformed_aux aag (cdl_domains_of_state s)"

definition
  pcs_refined :: "'a PAS \<Rightarrow> cdl_state \<Rightarrow> bool"
where
 "pcs_refined aag s \<equiv>
     pas_wellformed aag
   \<and> cdl_irq_map_wellformed aag s
   \<and> cdl_tcb_domain_map_wellformed aag s
   \<and> auth_graph_map (pasObjectAbs aag) (cdl_state_objs_to_policy s) \<subseteq> (pasPolicy aag)
   \<and> cdl_state_asids_to_policy aag s \<subseteq> pasPolicy aag
   \<and> cdl_state_irqs_to_policy aag s \<subseteq> pasPolicy aag"

lemmas cdl_state_objs_to_policy_mem = eqset_imp_iff[OF cdl_state_objs_to_policy_def]

lemmas cdl_state_objs_to_policy_intros
    = cdl_state_bits_to_policy.intros[THEN cdl_state_objs_to_policy_mem[THEN iffD2]]

lemmas csta_caps = cdl_state_objs_to_policy_intros(1)
  and csta_cdt = cdl_state_objs_to_policy_intros(2)

lemmas cdl_state_objs_to_policy_cases
    = cdl_state_bits_to_policy.cases[OF cdl_state_objs_to_policy_mem[THEN iffD1]]

lemma transform_asid_rev [simp]:
  "asid \<le> 2 ^ ARM_A.asid_bits - 1 \<Longrightarrow> transform_asid_rev (transform_asid asid) = asid"
  apply (clarsimp simp:transform_asid_def transform_asid_rev_def
                       asid_high_bits_of_def ARM_A.asid_low_bits_def)
  apply (subgoal_tac "asid >> 10 < 2 ^ asid_high_bits")
   apply (simp add:ARM_A.asid_high_bits_def ARM_A.asid_bits_def)
   apply (subst ucast_ucast_len)
    apply simp
   apply (subst shiftr_shiftl1)
    apply simp
   apply (subst ucast_ucast_mask)
   apply (simp add:mask_out_sub_mask)
  apply (simp add:ARM_A.asid_high_bits_def)
  apply (rule shiftr_less_t2n[where m=7, simplified])
  apply (simp add:ARM_A.asid_bits_def)
  done

abbreviation
  "valid_asid_mapping mapping \<equiv> (case mapping of
    None \<Rightarrow> True
  | Some (asid, ref) \<Rightarrow> asid \<le>  2 ^ ARM_A.asid_bits - 1)"

lemma transform_asid_rev_transform_mapping [simp]:
  "valid_asid_mapping mapping \<Longrightarrow>
   (transform_asid_rev o fst) ` set_option (transform_mapping mapping) = fst ` set_option mapping"
  apply (simp add:transform_mapping_def map_option_case)
  apply (case_tac mapping)
   apply clarsimp+
  done

lemma fst_transform_cslot_ptr:
  "fst ptr = fst (transform_cslot_ptr ptr)"
  apply (case_tac ptr)
  apply (clarsimp simp:transform_cslot_ptr_def)
  done

definition
  transform_cslot_ptr_rev :: "cdl_cap_ref \<Rightarrow> cslot_ptr"
where
  "transform_cslot_ptr_rev \<equiv> \<lambda>(a, b). (a, the (nat_to_bl word_bits b))"

lemma transform_cslot_pre_onto:
  "snd ptr < 2 ^ word_bits \<Longrightarrow> \<exists>ptr'. ptr = transform_cslot_ptr ptr'"
  apply (rule_tac x="transform_cslot_ptr_rev ptr" in exI)
  apply (case_tac ptr)
  apply (clarsimp simp: transform_cslot_ptr_def transform_cslot_ptr_rev_def)
  apply (clarsimp simp: nat_to_bl_def bin_bl_bin' bintrunc_mod2p)
  done

definition
  is_thread_state_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_thread_state_cap cap \<equiv> case cap of
    cdl_cap.PendingSyncSendCap _ _ _ _ _ _ \<Rightarrow> True
  | cdl_cap.PendingSyncRecvCap _ _ _ \<Rightarrow> True
  | cdl_cap.PendingNtfnRecvCap _ \<Rightarrow> True
  | cdl_cap.RestartCap \<Rightarrow> True
  | cdl_cap.RunningCap \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  is_bound_ntfn_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_bound_ntfn_cap cap \<equiv> case cap of
     BoundNotificationCap a \<Rightarrow> True
   | _ \<Rightarrow> False"

definition
  is_real_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_real_cap cap \<equiv> case cap of
    cdl_cap.FrameCap _ _ _ _ Fake _ \<Rightarrow> False
  | cdl_cap.PageTableCap _ Fake _ \<Rightarrow> False
  | cdl_cap.PageDirectoryCap _ Fake _ \<Rightarrow> False
  | _ \<Rightarrow> True"

lemma is_real_cap_transform:
  "cap = transform_cap cap' \<Longrightarrow> is_real_cap cap"
  by (auto simp:transform_cap_def is_real_cap_def split:cap.splits arch_cap.splits)

lemma is_real_cap_infer_tcb_pending_op:
  "is_real_cap (infer_tcb_pending_op a tcb)"
  by (auto simp:infer_tcb_pending_op_def is_real_cap_def split:Structures_A.thread_state.splits)

lemma is_real_cap_infer_tcb_bound_notification:
  "is_real_cap (infer_tcb_bound_notification a)"
  by (auto simp: infer_tcb_bound_notification_def is_real_cap_def split: cdl_cap.splits option.splits)

definition
  is_untyped_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_untyped_cap cap \<equiv> case cap of
    cdl_cap.UntypedCap _ _ _ \<Rightarrow> True
  | _ \<Rightarrow> False"

lemma valid_sched_etcbs[elim]:
  "valid_sched s \<Longrightarrow> valid_etcbs s"
  by (simp add: valid_sched_def)

lemma caps_of_state_transform_opt_cap_rev:
  "\<lbrakk> einvs s; opt_cap ptr (transform s) = Some cap;
     is_real_cap cap; \<not> is_thread_state_cap cap; \<not> is_null_cap cap; \<not> is_bound_ntfn_cap cap \<rbrakk> \<Longrightarrow>
     \<exists>cap' ptr'. cap = transform_cap cap' \<and> ptr = transform_cslot_ptr ptr' \<and>
                 caps_of_state s ptr' = Some cap'"
  apply clarify
  apply (drule invs_valid_objs)
  apply (case_tac ptr)
  apply (clarsimp simp:opt_cap_def transform_def transform_objects_def
                       transform_cslot_ptr_def slots_of_def)
  apply (rule_tac P="a=idle_thread s" in case_split)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (case_tac "kheap s a")
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (clarsimp simp:valid_objs_def dom_def)
  apply (drule_tac x=a in spec, clarsimp)
  apply (case_tac aa, simp_all add: object_slots_def caps_of_state_def2 nat_split_conv_to_if
                             split: if_split_asm)
     apply (clarsimp simp:valid_obj_def valid_cs_def valid_cs_size_def)
     apply (clarsimp simp:transform_cnode_contents_def)
     apply (rule_tac x=z in exI, simp)
     apply (rule_tac x="the (nat_to_bl 0 b)" in exI)
     apply (clarsimp simp:option_map_join_def split:option.splits)
     apply (rule nat_to_bl_to_bin, simp+)
    apply (clarsimp simp:valid_obj_def valid_cs_def valid_cs_size_def)
    apply (clarsimp simp:transform_cnode_contents_def)
    apply (rule_tac x=z in exI, simp)
    apply (rename_tac n list cap')
    apply (rule_tac x="the (nat_to_bl n b)" in exI)
    apply (clarsimp simp:option_map_join_def split:option.splits)
    apply (rule nat_to_bl_to_bin, simp+)
   apply (drule valid_etcbs_tcb_etcb [rotated], fastforce)
   apply clarsimp
   apply (clarsimp simp:transform_tcb_def tcb_slot_defs split:if_split_asm)
         apply (clarsimp simp: is_null_cap_def is_bound_ntfn_cap_def infer_tcb_bound_notification_def
                         split: option.splits)
        apply (simp add:is_thread_state_cap_def infer_tcb_pending_op_def is_null_cap_def is_real_cap_def
                    split:Structures_A.thread_state.splits option.splits)
       apply (rule exI, rule conjI, simp, rule exI, rule conjI,
              (rule bl_to_bin_tcb_cnode_index | rule bl_to_bin_tcb_cnode_index[symmetric]),
              simp, simp add:tcb_cap_cases_def)+
   apply (rule exI, rule conjI, simp)
   apply (rule_tac x="tcb_cnode_index 0" in exI)
   apply (subst bl_to_bin_tcb_cnode_index_le0; simp)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj; simp)
    apply (clarsimp simp:transform_asid_pool_contents_def unat_map_def split:if_split_asm)
    apply (clarsimp simp:is_real_cap_def is_null_cap_def transform_asid_pool_entry_def
                    split:option.splits)
   apply (clarsimp simp:transform_page_table_contents_def unat_map_def split:if_split_asm)
   apply (clarsimp simp:is_real_cap_def is_null_cap_def transform_pte_def
                   split:ARM_A.pte.splits)
  apply (clarsimp simp:transform_page_directory_contents_def unat_map_def split:if_split_asm)
  apply (clarsimp simp:is_real_cap_def is_null_cap_def transform_pde_def
                  split:ARM_A.pde.splits)
  done

abbreviation
  "get_size cap \<equiv> case cap of
     cdl_cap.FrameCap _ _ _ sz _ _ \<Rightarrow> sz
   | cdl_cap.PageTableCap _ _ _ \<Rightarrow> 0"

lemma opt_cap_None_word_bits:
  "\<lbrakk> einvs s; snd ptr \<ge> 2 ^ word_bits \<rbrakk> \<Longrightarrow> opt_cap ptr (transform s) = None"
  apply (case_tac ptr)
  apply (clarsimp simp:opt_cap_def transform_def transform_objects_def slots_of_def)
  apply (rule_tac P="a=idle_thread s" in case_split)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (case_tac "kheap s a")
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (drule invs_valid_objs)
  apply (simp add:object_slots_def valid_objs_def)
  apply (case_tac aa, simp_all add: nat_split_conv_to_if
                             split: if_split_asm)
    apply (clarsimp simp:transform_cnode_contents_def object_slots_def)
    apply (drule_tac x=a in bspec)
     apply (simp add:dom_def)+
    apply (clarsimp simp:valid_obj_def valid_cs_def valid_cs_size_def)
    apply (rule conjI)
     apply (clarsimp simp:option_map_join_def nat_to_bl_def)
     apply (metis gr0I le_antisym less_eq_Suc_le less_eq_nat.simps(1)
                  lt_word_bits_lt_pow zero_less_Suc)
    apply (clarsimp simp:option_map_join_def nat_to_bl_def)
    apply (drule not_le_imp_less)
    apply (subgoal_tac "b < 2 ^ word_bits")
     apply simp
    apply (rule less_trans)
     apply simp
    apply (rule power_strict_increasing, simp+)
   apply (frule valid_etcbs_tcb_etcb[rotated], fastforce)
   apply (clarsimp simp:transform_tcb_def tcb_slot_defs word_bits_def)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj; simp)
    apply (simp add:transform_asid_pool_contents_def transform_page_table_contents_def
                    transform_page_directory_contents_def unat_map_def word_bits_def)+
  done

lemma opt_cap_Some_rev:
  "\<lbrakk> einvs s; opt_cap ptr (transform s) = Some cap \<rbrakk> \<Longrightarrow> \<exists>ptr'. ptr = transform_cslot_ptr ptr'"
  apply (rule transform_cslot_pre_onto)
  apply (subst not_le[symmetric])
  apply (rule notI)
  apply (drule_tac ptr=ptr in opt_cap_None_word_bits; simp)
  done

lemma obj_refs_transform:
  "\<not> (\<exists>x sz i dev. cap = cap.UntypedCap dev x sz i) \<Longrightarrow> obj_refs_ac cap = cdl_obj_refs (transform_cap cap)"
  apply (case_tac cap; clarsimp)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; clarsimp)
  done

lemma untyped_range_transform:
  "(\<exists>x sz i dev. cap = cap.UntypedCap dev x sz i) \<Longrightarrow> untyped_range cap = cdl_obj_refs (transform_cap cap)"
  by auto

lemma cap_auth_conferred_transform:
  "cap_auth_conferred cap = cdl_cap_auth_conferred (transform_cap cap)"
  apply (case_tac cap;
         clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def
                        cdl_cap_auth_conferred_def reply_cap_rights_to_auth_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; clarsimp simp: is_page_cap_def)
  done

lemma thread_st_auth_transform:
  "\<lbrakk> einvs s; (oref', auth) \<in> thread_st_auth s oref \<rbrakk> \<Longrightarrow>
         (oref, auth, oref') \<in> cdl_state_objs_to_policy (transform s)"
  apply clarify
  apply (simp add:thread_st_auth_def tcb_states_of_state_def)
  apply (cases "get_tcb oref s")
   apply simp+
  apply (frule valid_etcbs_get_tcb_get_etcb[rotated], fastforce)
  apply clarsimp
  apply (rule_tac cap="infer_tcb_pending_op oref (tcb_state a)" in csta_caps[where ptr="(oref, 5)"
                          and auth=auth and oref=oref' and s="transform s", simplified])
    apply (rule opt_cap_tcb[where sl=5, unfolded tcb_slot_defs, simplified])
      apply simp
     apply simp
    apply (rule notI, drule invs_valid_idle, simp add:valid_idle_def pred_tcb_def2)
   apply (simp add:infer_tcb_pending_op_def, case_tac "tcb_state a";
          fastforce split:if_splits)
  apply (simp add:infer_tcb_pending_op_def cdl_cap_auth_conferred_def, case_tac "tcb_state a";
         fastforce split:if_splits)
  done

lemma thread_bound_ntfns_transform:
  "\<lbrakk> einvs s; thread_bound_ntfns s oref = Some oref'; auth \<in> {Receive, Reset} \<rbrakk> \<Longrightarrow>
         (oref, auth, oref') \<in> cdl_state_objs_to_policy (transform s)"
  apply clarify
  apply (simp add: thread_bound_ntfns_def  )
  apply (cases "get_tcb oref s")
   apply simp+
  apply (frule valid_etcbs_get_tcb_get_etcb[rotated], fastforce)
  apply clarsimp
  apply (rule_tac cap="infer_tcb_bound_notification (tcb_bound_notification a)" in csta_caps[where ptr="(oref, tcb_boundntfn_slot)"
                          and auth=auth and oref=oref' and s="transform s", simplified])
    apply (unfold tcb_boundntfn_slot_def)
    apply (rule opt_cap_tcb[where sl=tcb_boundntfn_slot, unfolded tcb_slot_defs, simplified])
      apply simp
     apply simp
    apply (rule notI, drule invs_valid_idle, simp add:valid_idle_def pred_tcb_def2)
   apply (clarsimp simp: infer_tcb_bound_notification_def cdl_cap_auth_conferred_def)+
  done

lemma thread_state_cap_transform_tcb:
  "\<lbrakk> opt_cap ptr (transform s) = Some cap; is_thread_state_cap cap \<rbrakk> \<Longrightarrow>
     \<exists>tcb. get_tcb (fst ptr) s = Some tcb"
  apply (case_tac ptr)
  apply (simp add:opt_cap_def slots_of_def transform_def transform_objects_def)
  apply (rule_tac P="a = idle_thread s" in case_split)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (case_tac "kheap s (fst ptr)")
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (simp add:get_tcb_def object_slots_def)
  apply (case_tac aa, simp_all add: nat_split_conv_to_if
                             split: if_split_asm)
    apply (clarsimp simp:transform_cnode_contents_def)
    apply (case_tac z, simp_all add:is_thread_state_cap_def split:if_split_asm)
    apply (rename_tac arch_cap)
    apply (case_tac arch_cap; simp)
   apply (clarsimp simp:transform_cnode_contents_def)
   apply (case_tac z, simp_all add:is_thread_state_cap_def split:if_split_asm)
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap; simp)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj; simp)
    apply (clarsimp simp:transform_asid_pool_contents_def unat_map_def transform_asid_pool_entry_def
                    split:if_split_asm option.splits)
   apply (clarsimp simp:transform_page_table_contents_def unat_map_def transform_pte_def
                   split:if_split_asm ARM_A.pte.splits)
  apply (clarsimp simp:transform_page_directory_contents_def unat_map_def transform_pde_def
                   split:if_split_asm ARM_A.pde.splits)
  done


lemma not_is_bound_ntfn_cap_transform_cap[simp]: "\<not>is_bound_ntfn_cap (transform_cap cn)"
  apply (case_tac cn; simp add: is_bound_ntfn_cap_def)
  apply (rename_tac foo)
  apply (case_tac foo; simp)
done

lemma thread_bound_ntfn_cap_transform_tcb:
  "\<lbrakk> opt_cap ptr (transform s) = Some cap; is_bound_ntfn_cap cap \<rbrakk> \<Longrightarrow>
     \<exists>tcb. get_tcb (fst ptr) s = Some tcb"
  apply (case_tac ptr)
  apply (simp add:opt_cap_def slots_of_def transform_def transform_objects_def)
  apply (rule_tac P="a = idle_thread s" in case_split)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (case_tac "kheap s (fst ptr)")
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (simp add:get_tcb_def object_slots_def)
  apply (case_tac aa, simp_all)
  apply (case_tac x11; simp)
   apply (clarsimp simp:transform_cnode_contents_def)
  apply (clarsimp simp:transform_cnode_contents_def)
  apply (rename_tac arch_obj)
  apply (case_tac arch_obj;clarsimp simp:transform_asid_pool_contents_def unat_map_def split:if_split_asm)
  apply (clarsimp simp:transform_asid_pool_entry_def is_bound_ntfn_cap_def split:option.splits)
     apply (clarsimp simp:transform_page_table_contents_def unat_map_def transform_pte_def is_bound_ntfn_cap_def
                   split:if_split_asm ARM_A.pte.splits)
  apply (clarsimp simp:transform_page_directory_contents_def unat_map_def transform_pde_def is_bound_ntfn_cap_def
                   split:if_split_asm ARM_A.pde.splits)
  done


lemma thread_st_auth_transform_rev:
  "\<lbrakk> einvs s; opt_cap ptr (transform s) = Some cap; is_thread_state_cap cap;
     oref \<in> cdl_obj_refs cap; auth \<in> cdl_cap_auth_conferred cap; (fst ptr) \<noteq> idle_thread s \<rbrakk> \<Longrightarrow>
     (oref, auth) \<in> thread_st_auth s (fst ptr)"
  apply (frule thread_state_cap_transform_tcb, simp)
  apply (case_tac ptr)
  apply (clarsimp simp:thread_st_auth_def tcb_states_of_state_def)
  apply (frule valid_etcbs_get_tcb_get_etcb[rotated], fastforce)
  apply (frule_tac sl=b in opt_cap_tcb, assumption, simp)
  apply (clarsimp split:if_split_asm)
    apply (case_tac "aa tcb"; simp add:is_thread_state_cap_def split:if_split_asm)
    apply (rename_tac arch_cap)
    apply (case_tac "arch_cap"; simp split:if_split_asm)
   apply (case_tac "tcb_state tcb";
          fastforce simp:cdl_cap_auth_conferred_def split:option.splits if_splits)
  apply (fastforce simp:is_thread_state_cap_def infer_tcb_pending_op_def
                        infer_tcb_bound_notification_def
                   split:option.splits if_splits)
  done

lemma thread_bound_ntfns_transform_rev:
  "\<lbrakk> einvs s; opt_cap ptr (transform s) = Some cap; is_bound_ntfn_cap cap;
     oref \<in> cdl_obj_refs cap; auth \<in> cdl_cap_auth_conferred cap; (fst ptr) \<noteq> idle_thread s \<rbrakk> \<Longrightarrow>
     thread_bound_ntfns s (fst ptr) = Some oref"
  apply (frule thread_bound_ntfn_cap_transform_tcb, simp)
  apply (case_tac ptr)
  apply (clarsimp simp:thread_bound_ntfns_def)
  apply (frule valid_etcbs_get_tcb_get_etcb[rotated], fastforce)
  apply (frule_tac sl=b in opt_cap_tcb, assumption, simp)
  apply (clarsimp split:if_split_asm)
   apply (case_tac "tcb"; simp add:is_thread_state_cap_def is_bound_ntfn_cap_def split:if_split_asm)
   apply (rename_tac arch_cap)
   apply (case_tac "arch_cap", simp_all split:if_split_asm)
  apply (clarsimp simp: infer_tcb_pending_op_def split: Structures_A.thread_state.splits)
  apply (case_tac "tcb_bound_notification tcb",
         auto simp: infer_tcb_pending_op_def cdl_cap_auth_conferred_def
                    infer_tcb_bound_notification_def
              split: option.splits)
  done

lemma idle_thread_null_cap:
  "\<lbrakk> invs s; caps_of_state s ptr = Some cap; fst ptr = idle_thread s \<rbrakk> \<Longrightarrow> cap = cap.NullCap"
  apply (rule_tac s=s and v="snd ptr" in valid_idle_has_null_cap,
                                    (simp add:invs_def valid_state_def)+)
  apply (drule_tac s="fst x" for x in sym, simp)
  done

lemma idle_thread_no_authority:
  "\<lbrakk> invs s; caps_of_state s ptr = Some cap; auth \<in> cap_auth_conferred cap \<rbrakk> \<Longrightarrow>
     fst ptr \<noteq> idle_thread s"
  apply (rule notI)
  apply (drule idle_thread_null_cap, simp+)
  apply (simp add:cap_auth_conferred_def)
  done

lemma idle_thread_no_untyped_range:
  "\<lbrakk> invs s; caps_of_state s ptr = Some cap; auth \<in> untyped_range cap \<rbrakk> \<Longrightarrow> fst ptr \<noteq> idle_thread s"
  apply (rule notI)
  apply (drule idle_thread_null_cap, simp+)
  done

lemma fst':
  "(a :: cdl_object_id) = fst (a, b)"
  apply simp
  done

lemma opt_cap_pt_Some':
  "\<lbrakk> valid_idle s; kheap s a = Some (ArchObj (arch_kernel_obj.PageTable fun)) \<rbrakk>
         \<Longrightarrow>  (opt_cap (a, unat slot) (transform s)) = Some (transform_pte (fun slot))"
  apply (clarsimp simp:opt_cap_def transform_def slots_of_def object_slots_def
                       transform_objects_def map_add_def restrict_map_def not_idle_thread_def)
  apply (frule arch_obj_not_idle,simp)
  apply (clarsimp simp:transform_page_table_contents_def unat_map_def not_idle_thread_def)
  apply (rule unat_lt2p[where 'a=8, simplified])
  done

lemma pte_cdl_obj_refs:
  "\<lbrakk> pte_ref pte = Some (a, b, c); ptr \<in> ptr_range a b \<rbrakk> \<Longrightarrow>
     ptr \<in> cdl_obj_refs (transform_pte pte)"
  apply (case_tac pte; simp add: pte_ref_def transform_pte_def)
  done

lemma pte_cdl_cap_auth_conferred:
  "\<lbrakk> pte_ref pte = Some (a, b, c); auth \<in> c \<rbrakk> \<Longrightarrow>
     auth \<in> cdl_cap_auth_conferred (transform_pte pte)"
  apply (case_tac pte; simp add: pte_ref_def transform_pte_def cdl_cap_auth_conferred_def)
  done

lemma opt_cap_pd_Some':
  "\<lbrakk> valid_idle s; kheap s a = Some (ArchObj (arch_kernel_obj.PageDirectory fun));
     slot < ucast (kernel_base >> 20) \<rbrakk> \<Longrightarrow>
     (opt_cap (a, unat slot) (transform s)) = Some (transform_pde (fun slot))"
  apply (clarsimp simp:opt_cap_def transform_def slots_of_def object_slots_def
                       transform_objects_def restrict_map_def map_add_def not_idle_thread_def)
  apply (frule arch_obj_not_idle,simp)
  apply (clarsimp simp:transform_page_directory_contents_def unat_map_def not_idle_thread_def
                       kernel_pde_mask_def word_not_le[symmetric])
  apply (rule unat_lt2p[where 'a="12", simplified])
  done

lemma pde_cdl_obj_refs:
  "\<lbrakk> pde_ref2 pde = Some (a, b, c); ptr \<in> ptr_range a b \<rbrakk> \<Longrightarrow>
     ptr \<in> cdl_obj_refs (transform_pde pde)"
  apply (case_tac pde; simp add: pde_ref2_def transform_pde_def ptr_range_def)
  done

lemma pde_cdl_cap_auth_conferred:
  "\<lbrakk> pde_ref2 pde = Some (a, b, c); auth \<in> c \<rbrakk> \<Longrightarrow>
     auth \<in> cdl_cap_auth_conferred (transform_pde pde)"
  apply (case_tac pde; simp add: pde_ref2_def transform_pde_def cdl_cap_auth_conferred_def)
  done

lemma state_vrefs_transform:
  "\<lbrakk> invs s; ptr \<noteq> idle_thread s; (ptr', ref, aat, auth) \<in> state_vrefs s ptr \<rbrakk> \<Longrightarrow>
     (ptr, auth, ptr') \<in> cdl_state_objs_to_policy (transform s)"
  apply (simp add:state_vrefs_def, case_tac "kheap s ptr", simp+)
  apply (case_tac a, simp_all add:vs_refs_no_global_pts_def)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj; simp add: vs_refs_no_global_pts_def)
    apply (clarsimp simp:graph_of_def)
    apply (subst fst')
    apply (rule csta_caps)
      apply (drule_tac asid="ucast aa" in opt_cap_asid_pool_Some[rotated])
       apply (simp add:invs_valid_idle)
      apply (simp add:ucast_up_ucast_id is_up_def source_size_def target_size_def word_size)
     apply (simp add:transform_asid_pool_entry_def)
    apply (simp add:transform_asid_pool_entry_def cdl_cap_auth_conferred_def)
   apply (clarsimp simp:graph_of_def)
   apply (subst fst')
   apply (rule csta_caps)
     apply (drule_tac slot=aa in opt_cap_pt_Some'[rotated])
      apply (simp add:invs_valid_idle)
     apply simp
    apply (rule_tac a=ab and b=ac and c=b in pte_cdl_obj_refs, simp+)
   apply (rule_tac a=ab and b=ac and c=b in pte_cdl_cap_auth_conferred, simp+)
  apply (erule bexE)
  apply (clarsimp simp:graph_of_def)
  apply (subst fst')
  apply (rule csta_caps)
    apply (drule_tac slot=aa in opt_cap_pd_Some'[rotated])
      apply (simp add:word_not_le[symmetric])
     apply (simp add:invs_valid_idle)
    apply simp
   apply (rule_tac a=ab and b=ac and c=b in pde_cdl_obj_refs, simp+)
  apply (rule_tac a=ab and b=ac and c=b in pde_cdl_cap_auth_conferred, simp+)
  done

lemma pte_ref_transform_rev:
  "ptr' \<in> cdl_obj_refs (transform_pte pte) \<Longrightarrow>
       pte_ref pte = Some (cap_object (transform_pte pte), get_size (transform_pte pte),
                           cdl_cap_auth_conferred (transform_pte pte)) \<and>
       ptr' \<in> ptr_range (cap_object (transform_pte pte)) (get_size (transform_pte pte))"
  apply (case_tac pte)
    apply (simp_all add:pte_ref_def transform_pte_def
                        vspace_cap_rights_to_auth_def cdl_cap_auth_conferred_def)
  done

lemma pde_ref_transform_rev:
  "ptr' \<in> cdl_obj_refs (transform_pde pde) \<Longrightarrow>
       pde_ref2 pde = Some (cap_object (transform_pde pde), get_size (transform_pde pde),
                           cdl_cap_auth_conferred (transform_pde pde)) \<and>
       ptr' \<in> ptr_range (cap_object (transform_pde pde)) (get_size (transform_pde pde))"
  apply (case_tac pde)
     apply (simp_all add:pde_ref2_def transform_pde_def ptr_range_def
                         vspace_cap_rights_to_auth_def cdl_cap_auth_conferred_def)
  done

lemma state_vrefs_transform_rev:
  "\<lbrakk> einvs s; opt_cap ptr (transform s) = Some cap; ptr' \<in> cdl_obj_refs cap;
     auth \<in> cdl_cap_auth_conferred cap; \<not> is_real_cap cap \<rbrakk> \<Longrightarrow>
     \<exists>ref aat. (ptr', ref, aat, auth) \<in> state_vrefs s (fst ptr)"
  apply (case_tac ptr, clarsimp)
  apply (subgoal_tac "a \<noteq> idle_thread s")
   prefer 2
   apply (clarsimp simp:state_vrefs_def transform_def transform_objects_def
                        opt_cap_def slots_of_def)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (case_tac "kheap s a")
   apply (clarsimp simp: state_vrefs_def transform_def transform_objects_def
                         opt_cap_def slots_of_def)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (clarsimp simp:state_vrefs_def transform_def transform_objects_def
                       opt_cap_def slots_of_def)
  apply (case_tac aa, simp_all add: transform_object_def object_slots_def nat_split_conv_to_if
                             split: if_split_asm)
     apply (clarsimp simp:transform_cnode_contents_def is_real_cap_transform)
    apply (clarsimp simp:transform_cnode_contents_def is_real_cap_transform)
   apply (frule valid_etcbs_tcb_etcb [rotated], fastforce)
   apply (clarsimp simp: transform_tcb_def is_real_cap_transform is_real_cap_infer_tcb_pending_op
                         is_real_cap_infer_tcb_bound_notification
                   split:if_split_asm)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all add:vs_refs_no_global_pts_def graph_of_def)
    apply (clarsimp simp:transform_asid_pool_contents_def unat_map_def split:if_split_asm)
    apply (rule exI)
    apply (rename_tac "fun")
    apply (case_tac "fun (of_nat b)")
     apply (clarsimp simp:transform_asid_pool_entry_def)
     apply (fastforce simp:transform_asid_pool_entry_def cdl_cap_auth_conferred_def)
    apply (clarsimp simp:transform_asid_pool_entry_def)
   apply (clarsimp simp:transform_page_table_contents_def unat_map_def split:if_split_asm)
   apply (rule exI)+
   apply (drule pte_ref_transform_rev)
   apply safe[1]
    apply simp
   apply (rule_tac x="(ptr', auth)" in image_eqI)
    apply simp
   apply simp
  apply (clarsimp simp:transform_page_directory_contents_def unat_map_def split:if_split_asm)
  apply (subgoal_tac "(of_nat b :: 12 word) < ucast (kernel_base >> 20)")
   prefer 2
   apply (subst word_not_le[symmetric])
   apply (rule notI)
   apply (clarsimp simp:kernel_pde_mask_def transform_pde_def)
  apply (simp add:kernel_pde_mask_def not_less[symmetric])
  apply (rule exI)
  apply (drule pde_ref_transform_rev, clarsimp)
  apply fastforce
  done

lemma cdl_cdt_transform_rev:
  "\<lbrakk> invs s; cdl_cdt (transform s) slot' = Some slot \<rbrakk> \<Longrightarrow>
     \<exists>ptr' ptr. slot' = transform_cslot_ptr ptr' \<and> slot = transform_cslot_ptr ptr \<and>
                cdt s ptr' = Some ptr"
  apply (clarsimp simp:cdt_transform map_lift_over_def split:if_split_asm)
  apply (rule_tac x=a in exI, rule_tac x=b in exI)
  apply (subst (asm) inv_into_f_f)
    apply (rule subset_inj_on)
     apply (simp add:dom_def)+
  done

(* Prove that transform preserves transferable caps. *)
lemma cdl_transform_null_cap:
  "\<lbrakk> einvs s; caps_of_state s (ptr, slot) = Some cap;
     opt_cap (transform_cslot_ptr (ptr, slot)) (transform s) = Some cdl_cap.NullCap \<rbrakk> \<Longrightarrow>
   cap = cap.NullCap"
  apply (case_tac "ptr = idle_thread s")
   apply (clarsimp simp: opt_cap_def slots_of_def
                         transform_def transform_cslot_ptr_def transform_objects_def
                         map_add_def)
  apply (subst (asm) caps_of_state_transform_opt_cap, assumption)
    apply fastforce
   apply fastforce
  apply (clarsimp simp: transform_cap_def split: cap.splits arch_cap.splits if_splits)
  done

lemma cdl_transform_reply_cap:
  "\<lbrakk> einvs s; caps_of_state s (ptr, slot) = Some cap;
     opt_cap (transform_cslot_ptr (ptr, slot)) (transform s) = Some (cdl_cap.ReplyCap t R) \<rbrakk> \<Longrightarrow>
   cap = cap.ReplyCap t False R"
  apply (case_tac "ptr = idle_thread s")
   apply (clarsimp simp: opt_cap_def slots_of_def
                         transform_def transform_cslot_ptr_def transform_objects_def
                         map_add_def)
  apply (subst (asm) caps_of_state_transform_opt_cap, assumption)
    apply fastforce
   apply fastforce
  apply (clarsimp simp: transform_cap_def split: cap.splits arch_cap.splits if_splits)
  done

lemma cdl_transferable_implies_transferable:
  "\<lbrakk> einvs s; cdt s (ptr, slot) = Some (pptr, pslot);
     cdl_cap_is_transferable (opt_cap (transform_cslot_ptr (ptr, slot)) (transform s)) \<rbrakk>
       \<Longrightarrow> is_transferable_in (ptr, slot) s"
  apply clarsimp
  apply (frule invs_mdb_cte, drule mdb_cte_at_rewrite, clarsimp simp: mdb_cte_at_def)
  apply ((drule spec)+, erule(1) impE, clarsimp)
  apply (erule cdl_cap_is_transferable.cases)
    apply (erule contrapos_pp[where Q="opt_cap _ _ = _"], clarsimp)
    apply (rule exI)
    apply (rule caps_of_state_transform_opt_cap)
      apply assumption
     apply fastforce
    apply (blast dest: idle_thread_null_cap)
   apply (fastforce dest: cdl_transform_null_cap[rotated])
  apply (fastforce simp: is_transferable.simps dest: cdl_transform_reply_cap[rotated])
  done

lemma state_objs_transform:
  "\<lbrakk> einvs s; (x, a, y) \<in> state_objs_to_policy s \<rbrakk> \<Longrightarrow>
               (x, a, y) \<in> cdl_state_objs_to_policy (transform s)"
  apply (erule state_objs_to_policy_cases)
      apply (simp add:fst_transform_cslot_ptr)
      apply (rule_tac ptr="transform_cslot_ptr ptr" and auth=auth and oref=oref and
                      cap="transform_cap cap" and s="transform s" in csta_caps)
        apply (rule caps_of_state_transform_opt_cap)
          apply simp
         apply fastforce
        apply (simp add:idle_thread_no_authority)
       apply (case_tac cap; simp)
       apply (rename_tac arch_cap)
       apply (case_tac arch_cap; simp)
      apply (simp add:cap_auth_conferred_transform)
     apply (simp add:fst_transform_cslot_ptr)
     apply (rule_tac ptr="transform_cslot_ptr ptr" and auth=Control and oref=oref and
                      cap="transform_cap cap" and s="transform s" in csta_caps)
       apply (rule caps_of_state_transform_opt_cap)
         apply simp
        apply fastforce
       apply (simp add:idle_thread_no_untyped_range)
      apply (case_tac cap, (simp add:untyped_range_transform del:untyped_range.simps(1))+)
     apply (case_tac cap, (simp add:cdl_cap_auth_conferred_def)+)
    apply (rule thread_st_auth_transform, simp+)
   apply (rule thread_bound_ntfns_transform, simp+)

    apply (simp add:fst_transform_cslot_ptr)
    apply (rule_tac slot="transform_cslot_ptr slot" and slot'="transform_cslot_ptr slot'"
                    and s="transform s" in csta_cdt)
     apply (simp add:transform_def)
     apply (rule transform_cdt_some)
      apply (simp add:invs_mdb_cte)
     apply simp
    apply (fastforce intro: cdl_transferable_implies_transferable)

   apply (clarsimp split: prod.splits)
   subgoal for slot pslot
     apply (rule cdl_state_objs_to_policy_intros(3)
                   [where slot'="(y, nat (bl_to_bin slot))" and slot="(x, nat (bl_to_bin pslot))",
                    simplified])
     apply (frule transform_cdt_slot_inj_on_mdb_cte_at[OF invs_mdb_cte])
     apply (clarsimp simp: cdt_transform map_lift_over_def transform_cslot_ptr_def)
     apply safe
      apply (rule_tac x=pslot in exI)
      apply (subst inv_into_f_eq[where x="(y, slot)"])
         apply (fastforce simp: inj_on_def)
        apply blast
       apply simp
      apply blast
     apply blast
     done

  apply (subgoal_tac "ptr \<noteq> idle_thread s")
   apply (simp add:state_vrefs_transform)
  apply (clarsimp simp:state_vrefs_def vs_refs_no_global_pts_def invs_def valid_state_def
                       valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma state_objs_transform_rev:
  "\<lbrakk> einvs s; (x, a, y) \<in> cdl_state_objs_to_policy (transform s) \<rbrakk> \<Longrightarrow>
               (x, a, y) \<in> state_objs_to_policy s"
  apply (rule cdl_state_objs_to_policy_cases, simp)
    apply (rule_tac P="is_thread_state_cap cap" in case_split)
     apply simp
     apply (rule sta_ts)
     apply (rule thread_st_auth_transform_rev, simp+)
     apply (clarsimp simp:opt_cap_def transform_def transform_objects_def slots_of_def)
     apply (clarsimp simp: map_add_def object_slots_def)
    apply (rule_tac P="is_real_cap cap" in case_split[rotated])
     apply (drule state_vrefs_transform_rev, simp+)
     apply clarsimp
     apply (rule sta_vref)
     apply simp
    apply (subgoal_tac "\<not> is_null_cap cap")
     prefer 2
     apply (clarsimp simp:is_null_cap_def split:cdl_cap.splits)
    apply (rule_tac P="is_bound_ntfn_cap cap" in case_split)
     apply simp
     apply (rule sta_bas)
      apply (rule thread_bound_ntfns_transform_rev, simp+)
      apply (clarsimp simp: opt_cap_def transform_def transform_objects_def slots_of_def)
      apply (clarsimp simp: map_add_def object_slots_def)
     apply (clarsimp simp: cdl_cap_auth_conferred_def is_bound_ntfn_cap_def split: cdl_cap.splits)
    apply (frule caps_of_state_transform_opt_cap_rev, simp+)
    apply (rule_tac P="is_untyped_cap cap" in case_split)
     apply (subgoal_tac "a = Control")
      apply clarsimp
      apply (subst fst_transform_cslot_ptr[symmetric])
      apply (rule_tac cap=cap' in sta_untyped)
       apply simp
      apply (subst (asm) untyped_range_transform[symmetric])
       apply (simp add:is_untyped_cap_def transform_cap_def
                   split:cap.splits arch_cap.splits if_split_asm)
      apply simp
     apply (simp add:cdl_cap_auth_conferred_def is_untyped_cap_def split:cdl_cap.splits)
    apply clarsimp
    apply (subst fst_transform_cslot_ptr[symmetric])
    apply (rule_tac cap=cap' in sta_caps)
      apply simp
     apply (subst (asm) obj_refs_transform[symmetric])
      apply (simp add:is_untyped_cap_def transform_cap_def
                  split:cap.splits arch_cap.splits if_split_asm)
     apply simp
    apply (simp add:cap_auth_conferred_transform)

   apply (drule cdl_cdt_transform_rev [rotated], simp+)
   apply clarsimp
   apply (subst fst_transform_cslot_ptr[symmetric])+
   apply (rule sta_cdt)
    apply simp
   apply (erule contrapos_nn)
   apply (frule invs_mdb_cte, drule mdb_cte_at_rewrite, clarsimp simp: mdb_cte_at_def)
   apply (erule is_transferable.cases)
      apply fastforce
     apply fastforce
    apply ((drule spec)+, erule(1) impE, clarsimp)
    apply (subst caps_of_state_transform_opt_cap)
      apply assumption
     apply fastforce
    apply (blast dest: idle_thread_null_cap)
   apply (clarsimp simp: transform_cap_def)
   apply (blast intro: cdl_cap_is_transferable.intros)

  apply clarsimp
  apply (frule(1) cdl_cdt_transform_rev)
  apply (clarsimp simp: transform_cslot_ptr_def)
  apply (erule sta_cdt_transferable
                 [where slot="(x, slot)" and slot'="(y, slot')" for slot slot', simplified])
  done

lemma state_vrefs_asidpool_control:
  "(pdptr, asid, AASIDPool, auth) \<in> state_vrefs s poolptr \<Longrightarrow> auth = Control"
  apply (clarsimp simp:state_vrefs_def )
  apply (cases "kheap s poolptr")
   apply clarsimp
  apply (simp add: vs_refs_no_global_pts_def, case_tac a; clarsimp)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj; clarsimp)
  done

lemma idle_thread_no_asid:
  "\<lbrakk> invs s; caps_of_state s ptr = Some cap;
     asid \<in> cap_asid' cap \<rbrakk> \<Longrightarrow> fst ptr \<noteq> idle_thread s"
  apply (rule notI)
  apply (drule idle_thread_null_cap, simp+)
  done

lemma asid_table_entry_transform:
  "arm_asid_table (arch_state s) (asid_high_bits_of asid) = poolptr \<Longrightarrow>
   cdl_asid_table (transform s) (fst (transform_asid asid)) =
                        Some (transform_asid_table_entry poolptr)"
  apply (clarsimp simp:transform_def transform_asid_table_def unat_map_def
                       transform_asid_table_entry_def transform_asid_def)
  apply (simp add:transform_asid_def asid_high_bits_of_def asid_low_bits_def)
  apply (rule unat_lt2p[where 'a=7, simplified])
  done

lemma transform_asid_high_bits_of:
  "of_nat (fst (transform_asid asid)) = asid_high_bits_of asid"
  apply (clarsimp simp:transform_asid_def asid_high_bits_of_def)
  done

lemma transform_asid_high_bits_of':
  "fst (transform_asid asid) = unat (asid_high_bits_of asid)"
  apply (clarsimp simp:transform_asid_def asid_high_bits_of_def)
  done

lemma transform_asid_low_bits_of:
  "of_nat (snd (transform_asid asid)) = (ucast asid :: 10 word)"
  apply (clarsimp simp:transform_asid_def)
  done

lemma cap_asid'_transform:
  "\<lbrakk> invs s; caps_of_state s ptr = Some cap \<rbrakk> \<Longrightarrow> cap_asid' cap = cdl_cap_asid' (transform_cap cap)"
  supply image_cong_simp [cong del]
  apply (case_tac cap; simp)
  apply (drule caps_of_state_valid, simp)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; simp)
     apply (clarsimp simp:transform_asid_high_bits_of' valid_cap_def split:option.splits)+
  done

lemma state_asids_transform:
  "\<lbrakk> einvs s; (x, a, y) \<in> state_asids_to_policy aag s \<rbrakk> \<Longrightarrow>
                               (x, a, y) \<in> cdl_state_asids_to_policy aag (transform s)"
  apply (unfold state_asids_to_policy_arch_def)
  apply (drule state_asids_to_policy_aux.induct)
     prefer 4
     apply simp
    apply (simp add: fst_transform_cslot_ptr)
    apply (rule_tac cap="transform_cap (ArchObjectCap acap)" in csata_asid)
     apply (rule caps_of_state_transform_opt_cap)
       apply simp
      apply fastforce
     apply (clarsimp simp: idle_thread_no_asid)
    apply (fastforce dest: cap_asid'_transform)
   apply (frule state_vrefs_asidpool_control, simp)
   apply (simp add: state_vrefs_def, case_tac "kheap s poolptr", simp_all)
   apply (case_tac aa, simp_all add:vs_refs_no_global_pts_def)
   apply (rename_tac arch_kernel_obj)
   apply (case_tac arch_kernel_obj, simp_all add:graph_of_def, safe)
   apply (rule_tac pdcap="cdl_cap.PageDirectoryCap b Fake None" in csata_asid_lookup)
       apply (simp add: asid_table_entry_transform)
      apply (simp add: is_null_cap_def transform_asid_table_entry_def)
     apply (simp add: is_null_cap_def transform_asid_table_entry_def)
    apply (simp add: ucast_up_ucast_id is_up_def source_size_def target_size_def word_size)
   apply (simp add: transform_asid_table_entry_def)
   apply (drule_tac asid="asid" in opt_cap_asid_pool_Some[rotated])
    apply (simp add: invs_valid_idle)
   apply (subst (asm) mask_asid_low_bits_ucast_ucast)
   apply (subst (asm) up_ucast_inj_eq)
    apply simp
   apply (simp add: transform_asid_pool_entry_def)
  apply (cut_tac aag=aag and asid=asid and asid_tab="cdl_asid_table (transform s)" in csata_asidpool)
     apply (clarsimp simp: transform_def transform_asid_table_def unat_map_def)
     apply safe[1]
      apply (simp add: transform_asid_table_entry_def transform_asid_high_bits_of)
     apply (simp add: transform_asid_def unat_lt2p[where 'a=7, simplified])
    apply (simp add: is_null_cap_def)
   apply simp
  apply simp
  done

lemma opt_cap_Some_asid_real:
  "\<lbrakk> opt_cap ref (transform s) = Some cap; asid \<in> cdl_cap_asid' cap; einvs s \<rbrakk> \<Longrightarrow> is_real_cap cap"
  apply (case_tac ref)
  apply (clarsimp simp:opt_cap_def transform_def transform_objects_def slots_of_def)
  apply (rule_tac P="a=idle_thread s" in case_split)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (case_tac "kheap s a")
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (case_tac aa, simp_all add:object_slots_def valid_objs_def nat_split_conv_to_if
                             split: if_split_asm)
     apply (clarsimp simp:transform_cnode_contents_def is_real_cap_transform)
    apply (clarsimp simp:transform_cnode_contents_def is_real_cap_transform)
   apply (frule valid_etcbs_tcb_etcb[rotated], fastforce)
   apply (clarsimp simp: transform_tcb_def tcb_slot_defs is_real_cap_infer_tcb_bound_notification
                         is_real_cap_transform is_real_cap_infer_tcb_pending_op
                  split: if_split_asm)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj; simp)
    apply (clarsimp simp:transform_asid_pool_contents_def unat_map_def split:if_split_asm)
    apply (clarsimp simp:transform_asid_pool_entry_def split:option.splits)
   apply (clarsimp simp:transform_page_table_contents_def unat_map_def split:if_split_asm)
   apply (clarsimp simp:transform_pte_def split:ARM_A.pte.splits)
  apply (clarsimp simp:transform_page_directory_contents_def unat_map_def split:if_split_asm)
  apply (clarsimp simp:transform_pde_def split:ARM_A.pde.splits)
  done

lemma state_vrefs_asid_pool_transform_rev:
  "\<lbrakk> einvs s; cdl_asid_table (transform s) (fst (transform_asid asid)) = Some poolcap;
     \<not> is_null_cap poolcap; \<not> is_null_cap pdcap; pdptr = cap_object pdcap;
     opt_cap (cap_object poolcap, snd (transform_asid asid)) (transform s) = Some pdcap \<rbrakk> \<Longrightarrow>
     (pdptr, asid && mask ARM_A.asid_low_bits, AASIDPool, Control)
          \<in> state_vrefs s (cap_object poolcap)"
  apply (subgoal_tac "cap_object poolcap \<noteq> idle_thread s")
   prefer 2
   apply (clarsimp simp:state_vrefs_def transform_def transform_objects_def
                        opt_cap_def slots_of_def)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (case_tac "kheap s (cap_object poolcap)")
   apply (clarsimp simp:state_vrefs_def transform_def transform_objects_def
                        opt_cap_def slots_of_def)
   apply (clarsimp simp: map_add_def object_slots_def)
  apply (clarsimp simp:transform_asid_high_bits_of')
  apply (simp add:asid_table_transform transform_asid_table_entry_def is_null_cap_def
              split:option.splits)
  apply (clarsimp simp:state_vrefs_def transform_def transform_objects_def
                       opt_cap_def slots_of_def)
  apply (drule invs_valid_asid_table)
  apply (clarsimp simp:valid_asid_table_def)
  apply (drule bspec)
   apply fastforce
  apply (case_tac a, simp_all add:transform_object_def object_slots_def)
    apply (clarsimp simp:obj_at_def a_type_def split:if_split_asm)+
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj; simp add:vs_refs_no_global_pts_def graph_of_def)
  apply (simp add:transform_asid_pool_contents_def unat_map_def transform_asid_low_bits_of
              split:if_split_asm)
  apply (rule_tac x="(ucast asid, cap_object pdcap)" in image_eqI)
   apply (simp add:mask_asid_low_bits_ucast_ucast)
  apply (clarsimp simp:transform_asid_pool_entry_def split:option.splits)
  done

lemma state_asids_transform_rev:
  "\<lbrakk> einvs s; (x, a, y) \<in> cdl_state_asids_to_policy aag (transform s) \<rbrakk> \<Longrightarrow>
                               (x, a, y) \<in> state_asids_to_policy aag s"
  apply (erule cdl_state_asids_to_policy_aux.induct)
    apply (rule_tac P="is_thread_state_cap cap" in case_split)
     apply (clarsimp simp:is_thread_state_cap_def split:cdl_cap.splits)
    apply (rule_tac P="is_bound_ntfn_cap cap" in case_split)
     apply (clarsimp simp: is_bound_ntfn_cap_def split: cdl_cap.splits)
    apply (rule_tac P="\<not> is_real_cap cap" in case_split)
     apply (clarsimp simp:opt_cap_Some_asid_real)
    apply (rule_tac P="is_null_cap cap" in case_split)
     apply (clarsimp simp:is_null_cap_def split:cdl_cap.splits)
    apply (frule caps_of_state_transform_opt_cap_rev, simp+)
    apply clarsimp
    apply (subst fst_transform_cslot_ptr[symmetric])
    apply (drule (1) cap_asid'_transform[symmetric])
    apply (simp only: cap_asid'_member)
    apply (erule exE)
    apply (rule sata_asid; fastforce)
   apply simp
   apply (rule_tac poolptr="cap_object poolcap" in sata_asid_lookup)
    apply (clarsimp simp:transform_asid_high_bits_of')
    apply (simp add:asid_table_transform transform_asid_table_entry_def is_null_cap_def
                split:option.splits)
    apply (drule_tac t=poolcap in sym)
    apply simp
   apply (rule state_vrefs_asid_pool_transform_rev, simp_all)
  apply (rule sata_asidpool)
   apply (clarsimp simp:transform_asid_high_bits_of')
   apply (simp add:asid_table_transform transform_asid_table_entry_def is_null_cap_def
               split:option.splits)
  apply simp
  done

lemma idle_thread_no_irqs:
  "\<lbrakk> invs s; caps_of_state s ptr = Some cap;
     irq \<in> cap_irqs_controlled cap \<rbrakk> \<Longrightarrow> fst ptr \<noteq> idle_thread s"
  apply (rule notI)
  apply (drule idle_thread_null_cap, simp+)
  done

lemma cap_irqs_controlled_transform:
  "cap_irqs_controlled cap = cdl_cap_irqs_controlled (transform_cap cap)"
  apply (case_tac cap; simp)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; simp)
  done

lemma state_irqs_transform:
  "\<lbrakk> einvs s; (x, a, y) \<in> state_irqs_to_policy aag s \<rbrakk> \<Longrightarrow>
   (x, a, y) \<in> cdl_state_irqs_to_policy aag (transform s)"
  apply (erule state_irqs_to_policy_aux.induct)
  apply (simp add: fst_transform_cslot_ptr)
  apply (rule_tac cap="transform_cap cap" in csita_controlled)
   apply (rule caps_of_state_transform_opt_cap)
     apply simp
    apply fastforce
   apply (clarsimp simp:idle_thread_no_irqs)
  apply (simp add: cap_irqs_controlled_transform)
  done

lemma state_irqs_transform_rev:
  "\<lbrakk> einvs s; (x, a, y) \<in> cdl_state_irqs_to_policy aag (transform s) \<rbrakk> \<Longrightarrow>
   (x, a, y) \<in> state_irqs_to_policy aag s"
  apply (erule cdl_state_irqs_to_policy_aux.induct)
  apply (rule_tac P="is_thread_state_cap cap" in case_split)
   apply (clarsimp simp:is_thread_state_cap_def split:cdl_cap.splits)
  apply (rule_tac P="is_bound_ntfn_cap cap" in case_split)
   apply (clarsimp simp:is_bound_ntfn_cap_def split:cdl_cap.splits)
  apply (rule_tac P="\<not> is_real_cap cap" in case_split)
   apply (clarsimp simp:is_real_cap_def split:cdl_cap.splits)
  apply (rule_tac P="is_null_cap cap" in case_split)
   apply (clarsimp simp:is_null_cap_def split:cdl_cap.splits)
  apply (frule caps_of_state_transform_opt_cap_rev, simp+)
  apply clarsimp
  apply (subst fst_transform_cslot_ptr[symmetric])
  apply (rule_tac cap=cap' in sita_controlled)
   apply simp
  apply (simp add:cap_irqs_controlled_transform)
  done

lemma irq_map_wellformed_transform:
  "irq_map_wellformed aag s = cdl_irq_map_wellformed aag (transform s)"
  apply (clarsimp simp:irq_map_wellformed_aux_def cdl_irq_map_wellformed_aux_def
                       transform_def)
  done

lemma einvs_idle:
  "einvs s \<Longrightarrow> idle_thread s = idle_thread_ptr"
  by (simp add: invs_def valid_state_def valid_idle_def)

lemma einvs_idle_domain:
  "einvs s \<Longrightarrow> \<exists>etcb. ekheap s idle_thread_ptr = Some etcb \<and> tcb_domain etcb = default_domain"
  apply (clarsimp simp: valid_sched_def valid_idle_etcb_def etcb_at_def
                        valid_etcbs_def invs_def valid_state_def valid_idle_def pred_tcb_at_def obj_at_def is_etcb_at_def
                       split: option.splits)
  apply (erule_tac x="idle_thread s" in allE)
  apply simp
  done

lemma cdl_domains_of_state_transform:
  assumes e: "einvs s"
  shows "cdl_domains_of_state (transform s) = domains_of_state s"
proof -
  { fix ptr d
    assume "(ptr, d) \<in> cdl_domains_of_state (transform s)"
    hence "(ptr, d) \<in> domains_of_state s"
    apply (cases)
     using e
     apply (clarsimp simp: transform_def transform_objects_def restrict_map_def
                     split: if_split_asm Structures_A.kernel_object.splits)
     apply (case_tac z, simp_all add: nat_split_conv_to_if
                               split: if_split_asm)
      prefer 2
      apply (rename_tac arch_kernel_obj)
      apply (case_tac arch_kernel_obj; simp)
     apply (drule valid_etcbs_tcb_etcb [rotated], fastforce)
     apply clarsimp
     apply (rule domains_of_state_aux.intros, assumption)
     apply (clarsimp simp: transform_tcb_def transform_full_intent_def Let_def)
    apply (insert einvs_idle [OF e])
    apply (insert einvs_idle_domain [OF e])
    apply clarsimp
    apply (erule domains_of_state_aux.domtcbs)
    apply simp
    done
  }
  note a = this
  {
    fix ptr d
    assume "(ptr, d) \<in> domains_of_state s"
    hence "(ptr, d) \<in> cdl_domains_of_state (transform s)"
    apply cases
    apply (case_tac "ptr = idle_thread_ptr")
     apply (insert einvs_idle [OF e])[1]
     apply (insert einvs_idle_domain [OF e])[1]
     apply simp
     apply (rule domidle)
    apply (frule ekheap_kheap_dom)
     using e apply fastforce
    apply clarsimp
    apply (drule (1) cdl_objects_tcb)
     apply (insert einvs_idle [OF e])[1]
     apply simp
    apply (erule domtcbs)
    apply (clarsimp simp: transform_full_intent_def Let_def)
    done
  }
  note b = this
  show ?thesis
  apply (rule set_eqI)
  apply clarify
  apply (blast intro!: a b)
  done
qed

lemma tcb_domain_map_wellformed_transform:
  "einvs s \<Longrightarrow>
  tcb_domain_map_wellformed aag s = cdl_tcb_domain_map_wellformed aag (transform s)"
  by (clarsimp simp: tcb_domain_map_wellformed_aux_def cdl_tcb_domain_map_wellformed_aux_def
                     cdl_domains_of_state_transform)

lemma pas_refined_transform:
  "einvs s \<Longrightarrow> pas_refined aag s = pcs_refined aag (transform s)"
  apply (clarsimp simp:pcs_refined_def pas_refined_def irq_map_wellformed_transform tcb_domain_map_wellformed_transform)
  apply safe
       apply (rule subsetD, simp)
       apply (clarsimp simp:auth_graph_map_mem)
       apply (rule_tac x="x'" in exI, clarsimp, rule_tac x="y'" in exI, clarsimp)
       apply (clarsimp simp:state_objs_transform_rev)
      apply (rule_tac A="state_asids_to_policy aag s" in subsetD, simp)
      apply (clarsimp simp:state_asids_transform_rev[simplified])
     apply (rule_tac A="state_irqs_to_policy aag s" in subsetD, simp)
     apply (clarsimp simp:state_irqs_transform_rev)
    apply (rule subsetD, simp)
    apply (clarsimp simp:auth_graph_map_mem)
    apply (rule_tac x="x'" in exI, clarsimp, rule_tac x="y'" in exI, clarsimp)
    apply (clarsimp simp:state_objs_transform)
   apply (rule_tac A="cdl_state_asids_to_policy aag (transform s)" in subsetD, simp)
   apply (clarsimp simp:state_asids_transform)
  apply (rule_tac A="cdl_state_irqs_to_policy aag (transform s)" in subsetD, simp)
  apply (clarsimp simp:state_irqs_transform)
  done

end

end
