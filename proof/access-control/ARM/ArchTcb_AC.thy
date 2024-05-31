(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTcb_AC
imports Tcb_AC
begin

context Arch begin global_naming ARM_A

named_theorems Tcb_AC_assms

declare arch_get_sanitise_register_info_inv[Tcb_AC_assms]

crunches arch_post_modify_registers
  for pas_refined[Tcb_AC_assms, wp]: "pas_refined aag"

lemma arch_post_modify_registers_respects[Tcb_AC_assms]:
  "\<lbrace>integrity aag X st and K (is_subject aag t)\<rbrace>
   arch_post_modify_registers cur t
   \<lbrace>\<lambda>_ s. integrity aag X st s\<rbrace>"
  by wpsimp

lemma invoke_tcb_tc_respects_aag[Tcb_AC_assms]:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and simple_sched_action
                       and tcb_inv_wf (ThreadControl t sl ep mcp priority croot vroot buf)
                       and K (authorised_tcb_inv aag (ThreadControl t sl ep mcp priority croot vroot buf))\<rbrace>
   invoke_tcb (ThreadControl t sl ep mcp priority croot vroot buf)
   \<lbrace>\<lambda>_. integrity aag X st and pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (subst invoke_tcb.simps)
  apply (subst option_update_thread_def)
  apply (subst set_priority_extended.dxo_eq)
  apply (rule hoare_weaken_pre)
   apply (rule_tac P="case ep of Some v \<Rightarrow> length v = word_bits | _ \<Rightarrow> True"
                 in hoare_gen_asm)
   apply (simp only: split_def)
   apply (((simp add: conj_comms del: hoareE_R_TrueI,
           strengthen imp_consequent[where Q="x = None" for x], simp cong: conj_cong)
          | strengthen invs_psp_aligned invs_vspace_objs invs_arch_state
          | rule wp_split_const_if wp_split_const_if_R hoare_vcg_all_liftE_R
                 hoare_vcg_E_elim hoare_vcg_const_imp_lift_R hoare_vcg_R_conj
          | wp restart_integrity_autarch set_mcpriority_integrity_autarch
               as_user_integrity_autarch thread_set_integrity_autarch
               option_update_thread_integrity_autarch
               opt_update_thread_valid_sched hoare_weak_lift_imp
               cap_insert_integrity_autarch checked_insert_pas_refined
               cap_delete_respects' cap_delete_pas_refined'
               check_cap_inv2[where Q="\<lambda>_. integrity aag X st"]
               as_user_pas_refined restart_pas_refined
               thread_set_pas_refined
               out_invs_trivial case_option_wpE cap_delete_deletes
               cap_delete_valid_cap cap_insert_valid_cap out_cte_at
               cap_insert_cte_at cap_delete_cte_at out_valid_cap out_tcb_valid
               hoare_vcg_const_imp_lift_R hoare_vcg_all_liftE_R
               thread_set_tcb_ipc_buffer_cap_cleared_invs
               thread_set_invs_trivial[OF ball_tcb_cap_casesI]
               hoare_vcg_all_lift thread_set_valid_cap out_emptyable
               check_cap_inv[where P="valid_cap c" for c]
               check_cap_inv[where P="tcb_cap_valid c p" for c p]
               check_cap_inv[where P="cte_at p0" for p0]
               check_cap_inv[where P="tcb_at p0" for p0]
               check_cap_inv[where P="simple_sched_action"]
               check_cap_inv[where P="valid_list"]
               check_cap_inv[where P="valid_sched"]
               check_cap_inv[where P="valid_arch_state"]
               check_cap_inv[where P="valid_vspace_objs"]
               check_cap_inv[where P="pspace_aligned"]
               thread_set_not_state_valid_sched
               thread_set_cte_at
               thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
               thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
               checked_insert_no_cap_to
               out_no_cap_to_trivial[OF ball_tcb_cap_casesI]
               thread_set_ipc_tcb_cap_valid
               cap_delete_pas_refined'[THEN valid_validE_E] thread_set_cte_wp_at_trivial
          | simp add: ran_tcb_cap_cases dom_tcb_cap_cases[simplified]
                      emptyable_def a_type_def partial_inv_def
                 del: hoareE_R_TrueI
          | wpc
          | strengthen invs_mdb use_no_cap_to_obj_asid_strg
                       tcb_cap_always_valid_strg[where p="tcb_cnode_index 0"]
                       tcb_cap_always_valid_strg[where p="tcb_cnode_index (Suc 0)"]))+
  apply (clarsimp simp: authorised_tcb_inv_def)
  apply (clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified]
                        is_cap_simps is_valid_vtable_root_def
                        is_cnode_or_valid_arch_def tcb_cap_valid_def
                        tcb_at_st_tcb_at[symmetric] invs_valid_objs
                        cap_asid_def vs_cap_ref_def
                        clas_no_asid cli_no_irqs
                        emptyable_def
         | rule conjI | erule pas_refined_refl)+
  done

end


global_interpretation Tcb_AC_1?: Tcb_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Tcb_AC_assms)
qed

end
