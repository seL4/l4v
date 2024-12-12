(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAccess_AC
imports Access_AC
begin

section\<open>Arch-specific AC proofs\<close>

context Arch begin global_naming AARCH64

named_theorems Access_AC_assms

lemma acap_class_reply[Access_AC_assms]:
  "acap_class acap \<noteq> ReplyClass t"
  by (cases acap; simp)

lemma arch_troa_tro_alt[Access_AC_assms, elim!]:
  "arch_integrity_obj_atomic aag subjects l ko ko'
   \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko'"
  by (fastforce elim: arch_integrity_obj_atomic.cases intro: arch_integrity_obj_alt.intros)

lemma clear_asidpool_trans[elim]:
  "\<lbrakk> asid_pool_integrity subjects aag pool pool';
     asid_pool_integrity subjects aag pool' pool'' \<rbrakk>
     \<Longrightarrow> asid_pool_integrity subjects aag pool pool''"
  unfolding asid_pool_integrity_def by metis

lemma cap_asid'_member[simp]:
  "asid \<in> cap_asid' cap = (\<exists>acap. cap = ArchObjectCap acap \<and> asid \<in> acap_asid' acap)"
  by (cases cap; clarsimp)

lemma clas_caps_of_state[Access_AC_assms]:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk>
     \<Longrightarrow> cap_links_asid_slot aag (pasObjectAbs aag (fst slot)) cap"
  apply (clarsimp simp: cap_links_asid_slot_def label_owns_asid_slot_def pas_refined_def)
  apply (drule state_asids_to_policy_aux.intros)
   apply assumption
  apply (blast dest: state_asids_to_policy_aux.intros)
  done

lemma arch_tro_alt_trans_spec[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_alt aag subjects l ko ko';
     arch_integrity_obj_alt aag subjects l ko' ko'' \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko''"
  by (fastforce simp: arch_integrity_obj_alt.simps)

end


global_interpretation Access_AC_1?: Access_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Access_AC_assms)
qed


context Arch begin global_naming AARCH64

lemma auth_ipc_buffers_tro[Access_AC_assms]:
  "\<lbrakk> integrity_obj_state aag activate subjects s s';
     x \<in> auth_ipc_buffers s' p; pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> x \<in> auth_ipc_buffers s p "
  by (drule_tac x = p in spec)
     (erule integrity_objE;
      fastforce simp: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def
               split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)

lemma trasids_trans[Access_AC_assms]:
  "\<lbrakk> (\<forall>x a. integrity_asids aag subjects x a s s');
     (\<forall>x a. integrity_asids aag subjects x a  s' s'') \<rbrakk>
     \<Longrightarrow> (\<forall>x a. integrity_asids aag subjects x a s s'')"
  by clarsimp metis

lemma integrity_asids_refl[Access_AC_assms, simp]:
  "integrity_asids aag subjects x a s s"
  by simp

lemma integrity_asids_update_autarch[Access_AC_assms]:
  "\<lbrakk> \<forall>x a. integrity_asids aag {pasSubject aag} x a st s; is_subject aag ptr \<rbrakk>
     \<Longrightarrow> \<forall>x a. integrity_asids aag {pasSubject aag} x a st (s\<lparr>kheap := (kheap s)(ptr \<mapsto> obj)\<rparr>)"
  by (auto simp: opt_map_def)

end


global_interpretation Access_AC_2?: Access_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Access_AC_assms)?)
qed


context Arch begin global_naming AARCH64

lemma ipcframe_subset_page:
  "\<lbrakk> valid_objs s; get_tcb p s = Some tcb;
     tcb_ipcframe tcb = ArchObjectCap (FrameCap p' R vms d xx);
     x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits \<rbrakk>
     \<Longrightarrow> x \<in> ptr_range p' (pageBitsForSize vms)"
   apply (frule (1) valid_tcb_objs)
   apply (clarsimp simp add: valid_tcb_def ran_tcb_cap_cases)
   apply (erule set_mp[rotated])
   apply (rule ptr_range_subset)
     apply (simp add: valid_cap_def cap_aligned_def)
    apply (simp add: valid_tcb_def valid_ipc_buffer_cap_def is_aligned_andI1 split:bool.splits)
   apply (rule order_trans [OF _ pbfs_atleast_pageBits])
   apply (simp add: msg_align_bits pageBits_def)
  apply (rule and_mask_less')
  apply (simp add: pbfs_less_wb' [unfolded word_bits_conv])
  done

lemma auth_ipc_buffers_member_def:
  "x \<in> auth_ipc_buffers s p =
   (\<exists>tcb p' R vms xx. get_tcb p s = Some tcb
                   \<and> tcb_ipcframe tcb = (ArchObjectCap (FrameCap p' R vms False xx))
                   \<and> caps_of_state s (p, tcb_cnode_index 4) =
                      Some (ArchObjectCap (FrameCap p' R vms False xx))
                   \<and> AllowWrite \<in> R
                   \<and> x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms)))
                                    msg_align_bits)"
  unfolding auth_ipc_buffers_def
  by (clarsimp simp: caps_of_state_tcb' split: option.splits cap.splits arch_cap.splits bool.splits)

lemma auth_ipc_buffers_member[Access_AC_assms]:
  "\<lbrakk> x \<in> auth_ipc_buffers s p; valid_objs s \<rbrakk>
     \<Longrightarrow> \<exists>tcb acap. get_tcb p s = Some tcb
                  \<and> tcb_ipcframe tcb = (ArchObjectCap acap)
                  \<and> caps_of_state s (p, tcb_cnode_index 4) = Some (ArchObjectCap acap)
                  \<and> Write \<in> arch_cap_auth_conferred acap
                  \<and> x \<in> aobj_ref' acap"
  by (fastforce simp: auth_ipc_buffers_def caps_of_state_tcb' arch_cap_auth_conferred_def
                      vspace_cap_rights_to_auth_def ipcframe_subset_page
               split: option.splits cap.splits arch_cap.splits bool.splits if_splits)

lemma asid_pool_integrity_mono[Access_AC_assms]:
  "\<lbrakk> asid_pool_integrity S aag cont cont'; S \<subseteq> T \<rbrakk> \<Longrightarrow> asid_pool_integrity T aag cont cont'"
  unfolding asid_pool_integrity_def by fastforce

lemma integrity_asids_mono[Access_AC_assms]:
    "\<lbrakk> integrity_asids aag S x a s s'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
       \<Longrightarrow> integrity_asids aag T x a s s'"
  by fastforce

lemma arch_integrity_obj_atomic_mono[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_atomic aag S l ao ao'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_atomic aag T l ao ao'"
  by (clarsimp simp: arch_integrity_obj_atomic.simps asid_pool_integrity_mono)

end


global_interpretation Access_AC_3?: Access_AC_3
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Access_AC_assms)
qed


context Arch begin global_naming AARCH64

lemma pas_refined_irq_state_independent[intro!, simp]:
  "pas_refined x (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>) =
   pas_refined x s"
  by (simp add: pas_refined_def)

(* FIXME AARCH64: try to use in_opt_map_eq where possible *)
lemma vspace_objs_of_Some:
  "(vspace_objs_of s p = Some ao) = (aobjs_of s p = Some ao \<and> \<not>is_VCPU ao)"
  by (clarsimp simp: in_opt_map_eq vspace_obj_of_Some)

lemma state_irqs_to_policy_eq_caps:
  "\<lbrakk> x \<in> state_irqs_to_policy_aux aag caps; caps = caps' \<rbrakk>
     \<Longrightarrow> x \<in> state_irqs_to_policy_aux aag caps'"
  by (erule subst)

lemma vs_lookup_table_eqI':
    "\<lbrakk> asid_table s' (asid_high_bits_of asid) = asid_table s (asid_high_bits_of asid);
       \<forall>pool_ptr. asid_table s' (asid_high_bits_of asid) = Some pool_ptr
                  \<longrightarrow> bot_level \<le> max_pt_level
                  \<longrightarrow> vspace_for_pool pool_ptr asid (asid_pools_of s') =
                      vspace_for_pool pool_ptr asid (asid_pools_of s);
       bot_level < max_pt_level \<longrightarrow> pts_of s' = pts_of s \<rbrakk>
   \<Longrightarrow> vs_lookup_table bot_level asid vref s' = vs_lookup_table bot_level asid vref s"
  by (auto simp: obind_def vs_lookup_table_def asid_pool_level_eq[symmetric]
                 pool_for_asid_def entry_for_pool_def vspace_for_pool_def
          split: option.splits)

lemma vs_refs_aux_eqI:
  assumes "pts_of s' = pts_of s"
  and "\<forall>p sz. data_at sz p s' = data_at sz p s"
  and "\<forall>pool_ptr asid. (asid_pools_of s' |> oapply asid |> ogets ap_vspace) pool_ptr
                     = (asid_pools_of s |> oapply asid |> ogets ap_vspace) pool_ptr"
  and "aobjs_of s p = Some ao"
  and "aobjs_of s' p = Some ao'"
  shows "vs_refs_aux level ao = vs_refs_aux level ao'"
  apply (insert assms)
  apply (clarsimp simp: fun_eq_iff)
  apply (erule_tac x=p in allE)+
  apply (fastforce simp: vs_refs_aux_def graph_of_def image_iff opt_map_def ogets_def
                  split: option.splits arch_kernel_obj.splits)
  done

lemma state_vrefs_eqI':
  assumes "asid_table s' = asid_table s"
    and "pts_of s' = pts_of s"
    and "\<forall>p sz. data_at sz p s' = data_at sz p s"
    and "\<forall>pool_ptr asid. (asid_pools_of s' |> oapply asid |> ogets ap_vspace) pool_ptr
                       = (asid_pools_of s |> oapply asid |> ogets ap_vspace) pool_ptr"
  shows "state_vrefs s' = state_vrefs s"
  apply (insert assms)
  apply (prop_tac "\<And>level asid vref. vs_lookup_table level asid vref s' = vs_lookup_table level asid vref s")
   apply (rule vs_lookup_table_eqI')
     apply (auto simp: fun_eq_iff vspace_for_pool_def entry_for_pool_def obind_def ogets_def opt_map_def)[3]
  apply (rule ext)+
  apply (intro equalityI subsetI; subst (asm) state_vrefs_def; clarsimp)

   apply (clarsimp simp: vspace_objs_of_Some)
   apply (case_tac "vspace_objs_of s x"; clarsimp?)
    apply (clarsimp simp: fun_eq_iff)
    apply (erule_tac x=x in allE)+
    apply (fastforce simp: vspace_obj_of_def vs_refs_aux_def graph_of_def
                           image_iff opt_map_def ogets_def is_VCPU_def
                    split: option.splits arch_kernel_obj.splits if_splits )[1]
   apply (prop_tac "\<forall>level. vs_refs_aux level ao = vs_refs_aux level ac")
    apply (intro allI vs_refs_aux_eqI; fastforce simp: vspace_objs_of_Some)
   apply (fastforce intro: state_vrefsD)

  apply (clarsimp simp: vspace_objs_of_Some)
  apply (case_tac "vspace_objs_of s' x"; clarsimp?)
   apply (clarsimp simp: fun_eq_iff)
   apply (erule_tac x=x in allE)+
   apply (fastforce simp: vspace_obj_of_def vs_refs_aux_def graph_of_def
                          image_iff opt_map_def ogets_def is_VCPU_def
                   split: option.splits arch_kernel_obj.splits if_splits )[1]
  apply (prop_tac "\<forall>level. vs_refs_aux level ac = vs_refs_aux level ao")
   apply (intro allI vs_refs_aux_eqI; fastforce simp: vspace_objs_of_Some)
  apply (fastforce intro!: state_vrefsD)
  done

lemma state_vrefs_eqI:
  assumes "asid_table s' = asid_table s"
    and "vspace_objs_of s' = vspace_objs_of s"
  shows "state_vrefs s' = state_vrefs s"
  apply (prop_tac "\<forall>level asid vref. vs_lookup_table level asid vref s = vs_lookup_table level asid vref s'")
   apply (intro allI vs_lookup_table_eqI')
  using assms apply (fastforce simp: obj_at_def)
  using vspace_objs_of_aps_eq assms apply fastforce
  using vspace_objs_of_pts_eq assms apply fastforce
  using assms apply (fastforce simp: state_vrefs_def)
  done

end

end
