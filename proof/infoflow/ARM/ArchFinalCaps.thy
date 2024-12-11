(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalCaps
imports FinalCaps
begin

context Arch begin global_naming ARM

named_theorems FinalCaps_assms

lemma FIXME_arch_gen_refs[FinalCaps_assms]:
  "arch_gen_refs cap = {}"
  by (clarsimp simp: arch_cap_set_map_def arch_gen_obj_refs_def split: cap.splits)

lemma aobj_ref_same_aobject[FinalCaps_assms]:
  "same_aobject_as cp cp' \<Longrightarrow> aobj_ref cp = aobj_ref cp'"
  by (cases cp; cases cp'; clarsimp)

lemma set_pt_silc_inv[wp]:
  "set_pt ptr pt \<lbrace>silc_inv aag st\<rbrace>"
  unfolding set_pt_def
  apply (rule silc_inv_pres)
    apply (wpsimp wp: set_object_wp_strong simp: a_type_def split: kernel_object.splits)
    apply (fastforce simp: silc_inv_def obj_at_def is_cap_table_def)
   apply (wp set_object_wp get_object_wp | simp)+
  apply (case_tac "ptr = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (fastforce elim: cte_wp_atE simp: obj_at_def)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma set_pd_silc_inv[wp]:
  "set_pd ptr pd \<lbrace>silc_inv aag st\<rbrace>"
  unfolding set_pd_def
  apply (rule silc_inv_pres)
    apply (wpsimp wp: set_object_wp_strong simp: a_type_def split: kernel_object.splits)
    apply (fastforce simp: silc_inv_def obj_at_def is_cap_table_def)
   apply (wp set_object_wp get_object_wp | simp)+
  apply (case_tac "ptr = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (fastforce elim: cte_wp_atE simp: obj_at_def)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma set_asid_pool_silc_inv[wp]:
   "set_asid_pool ptr pool \<lbrace>silc_inv aag st\<rbrace>"
  unfolding set_asid_pool_def
  apply (rule silc_inv_pres)
    apply (wpsimp wp: set_object_wp_strong simp: a_type_def split: kernel_object.splits)
    apply (fastforce simp: silc_inv_def obj_at_def is_cap_table_def)
   apply (wp set_object_wp get_object_wp | simp)+
  apply (case_tac "ptr = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (fastforce elim: cte_wp_atE simp: obj_at_def)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunch arch_finalise_cap, prepare_thread_delete, init_arch_objects
  for silc_inv[FinalCaps_assms, wp]: "silc_inv aag st"
  (wp: crunch_wps modify_wp simp: crunch_simps ignore: set_object)

declare finalise_cap_makes_halted[FinalCaps_assms]

crunch handle_reserved_irq, handle_vm_fault, handle_hypervisor_fault, handle_arch_fault_reply,
         arch_invoke_irq_handler, arch_mask_irq_signal,
         arch_post_cap_deletion, arch_post_modify_registers,
         arch_activate_idle_thread, arch_switch_to_idle_thread, arch_switch_to_thread
for silc_inv[FinalCaps_assms, wp]: "silc_inv aag st"

declare init_arch_objects_cte_wp_at[FinalCaps_assms]
declare handle_vm_fault_cur_thread[FinalCaps_assms]

lemma arch_derive_cap_silc[FinalCaps_assms]:
  "\<lbrace>\<lambda>s. cap = ArchObjectCap acap \<and>
        (\<not> cap_points_to_label aag cap l \<longrightarrow> R (slots_holding_overlapping_caps cap s))\<rbrace>
   arch_derive_cap acap
   \<lbrace>\<lambda>cap' s. \<not> cap_points_to_label aag cap' l \<longrightarrow> R (slots_holding_overlapping_caps cap' s)\<rbrace>, -"
  apply (simp add: arch_derive_cap_def)
  apply wpsimp
  apply (auto simp: cap_points_to_label_def slots_holding_overlapping_caps_def)
  done

end


global_interpretation FinalCaps_1?: FinalCaps_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact FinalCaps_assms)?)
qed


context Arch begin global_naming ARM

lemma perform_page_table_invocation_silc_inv_get_cap_helper:
   "\<lbrace>silc_inv aag st and cte_wp_at (is_pt_cap or is_pg_cap) xa\<rbrace>
    get_cap xa
    \<lbrace>(\<lambda>capa s. (\<not> cap_points_to_label aag (ArchObjectCap $ update_map_data capa None)
                                           (pasObjectAbs aag (fst xa))
                \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps
                                       (ArchObjectCap $ update_map_data capa None) s \<and>
                             pasObjectAbs aag (fst lslot) = SilcLabel))) \<circ> the_arch_cap\<rbrace>"
  apply (wp get_cap_wp)
  apply clarsimp
  apply (drule cte_wp_at_norm)
  apply (clarify)
  apply (drule (1) cte_wp_at_eqD2)
  apply (case_tac cap, simp_all add: is_pg_cap_def is_pt_cap_def)
  apply (clarsimp simp: cap_points_to_label_def update_map_data_def split: arch_cap.splits)
   apply (drule silc_invD)
     apply assumption
    apply (fastforce simp: intra_label_cap_def cap_points_to_label_def)
   apply (fastforce simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
  apply (drule silc_invD)
    apply assumption
   apply (fastforce simp: intra_label_cap_def cap_points_to_label_def)
  apply (fastforce simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
  done

lemmas perform_page_table_invocation_silc_inv_get_cap_helper' =
  perform_page_table_invocation_silc_inv_get_cap_helper[simplified o_def fun_app_def]

lemma mapM_x_swp_store_pte_silc_inv[wp]:
  "mapM_x (swp store_pte A) slots \<lbrace>silc_inv aag st\<rbrace>"
  by (wp mapM_x_wp[OF _ subset_refl] | simp add: swp_def)+

lemma is_arch_eq_pt_is_pt_or_pg_cap:
  "cte_wp_at ((=) (ArchObjectCap (PageTableCap xa xb))) slot s
   \<Longrightarrow> cte_wp_at (\<lambda>a. is_pt_cap a \<or> is_pg_cap a) slot s"
  apply (erule cte_wp_at_weakenE)
  by (clarsimp simp: is_pg_cap_def is_pt_cap_def)

lemma is_arch_eq_pg_is_pt_or_pg_cap:
  "cte_wp_at ((=) (ArchObjectCap (PageCap dev x xa xb xc))) slot s
   \<Longrightarrow> cte_wp_at (\<lambda>a. is_pt_cap a \<or> is_pg_cap a) slot s"
  apply (erule cte_wp_at_weakenE)
  by (clarsimp simp: is_pg_cap_def is_pt_cap_def)

lemma perform_page_table_invocation_silc_inv:
  "\<lbrace>silc_inv aag st and valid_pti blah and K (authorised_page_table_inv aag blah)\<rbrace>
   perform_page_table_invocation blah
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding perform_page_table_invocation_def
  apply (rule hoare_pre)
  apply (wp set_cap_silc_inv mapM_x_wp[OF _ subset_refl]
            perform_page_table_invocation_silc_inv_get_cap_helper'[where st=st]
         | wpc | simp only: o_def fun_app_def K_def swp_def)+
  apply (clarsimp simp: valid_pti_def authorised_page_table_inv_def
                 split: page_table_invocation.splits)
   apply (rule conjI)
    apply (clarsimp)
    defer
    apply (fastforce simp: silc_inv_def)
   apply (fastforce dest: is_arch_eq_pt_is_pt_or_pg_cap simp: silc_inv_def)
  apply (drule_tac slot="(aa,ba)" in overlapping_slots_have_labelled_overlapping_caps[rotated])
    apply (fastforce)
   apply (fastforce elim: is_arch_update_overlaps[rotated] cte_wp_at_weakenE)
  apply fastforce
  done

lemma perform_page_directory_invocation_silc_inv:
  "perform_page_directory_invocation iv \<lbrace>silc_inv aag st\<rbrace>"
  unfolding perform_page_directory_invocation_def
  apply (cases iv)
   apply (wp | simp)+
  done

crunch invalidate_tlb_by_asid
  for silc_inv[wp]: "silc_inv aag st"

lemma perform_page_invocation_silc_inv:
  "\<lbrace>silc_inv aag st and valid_page_inv blah and K (authorised_page_inv aag blah)\<rbrace>
   perform_page_invocation blah
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding perform_page_invocation_def
  apply (rule hoare_pre)
  apply (wp mapM_wp[OF _ subset_refl] set_cap_silc_inv
            mapM_x_wp[OF _ subset_refl]
            perform_page_table_invocation_silc_inv_get_cap_helper'[where st=st]
            hoare_vcg_all_lift hoare_vcg_if_lift hoare_weak_lift_imp
         | wpc
         | simp only: swp_def o_def fun_app_def K_def
         | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: valid_page_inv_def authorised_page_inv_def
                  split: page_invocation.splits)
   apply (intro allI impI conjI)
      apply (drule_tac slot="(aa,bb)" in overlapping_slots_have_labelled_overlapping_caps[rotated])
        apply (fastforce)
       apply (fastforce elim: is_arch_update_overlaps[rotated] cte_wp_at_weakenE)
      apply fastforce
     apply (fastforce simp: silc_inv_def)
    apply (drule_tac slot="(aa,bb)" in overlapping_slots_have_labelled_overlapping_caps[rotated])
      apply (fastforce)
     apply (fastforce elim: is_arch_update_overlaps[rotated] cte_wp_at_weakenE)
    apply fastforce
   apply (fastforce simp: silc_inv_def)
  apply (fastforce dest: is_arch_eq_pg_is_pt_or_pg_cap simp: silc_inv_def)
  done

lemma perform_asid_control_invocation_silc_inv:
  notes blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  shows
  "\<lbrace>silc_inv aag st and valid_aci blah and invs and K (authorised_asid_control_inv aag blah)\<rbrace>
   perform_asid_control_invocation blah
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  unfolding perform_asid_control_invocation_def
  apply (rule hoare_pre)
  apply (wp modify_wp cap_insert_silc_inv' retype_region_silc_inv[where sz=pageBits]
            set_cap_silc_inv get_cap_slots_holding_overlapping_caps[where st=st]
            delete_objects_silc_inv hoare_weak_lift_imp
         | wpc | simp )+
  apply (clarsimp simp: authorised_asid_control_inv_def silc_inv_def valid_aci_def ptr_range_def page_bits_def)
  apply (rule conjI)
   apply (clarsimp simp: range_cover_def obj_bits_api_def default_arch_object_def asid_bits_def pageBits_def)
   apply (rule of_nat_inverse)
    apply simp
    apply (drule is_aligned_neg_mask_eq'[THEN iffD1, THEN sym])
    apply (erule_tac t=x in ssubst)
    apply (simp add: mask_AND_NOT_mask)
   apply simp
  apply (simp add: p_assoc_help)
  apply (clarsimp simp: cap_points_to_label_def)
  apply (erule bspec)
  apply (fastforce intro: is_aligned_no_wrap' simp: blah)
  done

lemma perform_asid_pool_invocation_silc_inv:
  "\<lbrace>silc_inv aag st and K (authorised_asid_pool_inv aag blah)\<rbrace>
   perform_asid_pool_invocation blah
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  unfolding perform_asid_pool_invocation_def
  apply (rule hoare_pre)
   apply (wp set_cap_silc_inv get_cap_wp | wpc)+
  apply clarsimp
  apply (rule conjI, intro impI)
   apply (drule silc_invD)
     apply assumption
    apply (fastforce simp: intra_label_cap_def simp: cap_points_to_label_def)
   apply (clarsimp simp: slots_holding_overlapping_caps_def)
  apply (fastforce simp: authorised_asid_pool_inv_def silc_inv_def)
  done

lemma arch_perform_invocation_silc_inv[FinalCaps_assms]:
  "\<lbrace>silc_inv aag st and invs and valid_arch_inv ai and authorised_arch_inv aag ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding arch_perform_invocation_def
  apply (rule hoare_pre)
  apply (wp perform_page_table_invocation_silc_inv
            perform_page_directory_invocation_silc_inv
            perform_page_invocation_silc_inv
            perform_asid_control_invocation_silc_inv
            perform_asid_pool_invocation_silc_inv
         | wpc)+
  apply (clarsimp simp: authorised_arch_inv_def valid_arch_inv_def split: arch_invocation.splits)
  done

lemma arch_invoke_irq_control_silc_inv[FinalCaps_assms]:
  "\<lbrace>silc_inv aag st and pas_refined aag and arch_irq_control_inv_valid arch_irq_cinv
                    and K (arch_authorised_irq_ctl_inv aag arch_irq_cinv)\<rbrace>
   arch_invoke_irq_control arch_irq_cinv
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding arch_authorised_irq_ctl_inv_def
  apply (rule hoare_gen_asm)
  apply (case_tac arch_irq_cinv)
  apply (wp cap_insert_silc_inv'' hoare_vcg_ex_lift slots_holding_overlapping_caps_lift
         | simp add: authorised_irq_ctl_inv_def arch_irq_control_inv_valid_def)+
  apply (fastforce dest: new_irq_handler_caps_are_intra_label)
  done

crunch set_priority
  for silc_inv[wp]: "silc_inv aag st"
  (simp: tcb_cap_cases_def)

lemma invoke_tcb_silc_inv[FinalCaps_assms]:
  notes hoare_weak_lift_imp [wp]
        hoare_weak_lift_imp_conj [wp]
  shows "\<lbrace>silc_inv aag st and einvs and simple_sched_action and pas_refined aag and tcb_inv_wf tinv
                          and K (authorised_tcb_inv aag tinv)\<rbrace>
         invoke_tcb tinv
         \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (case_tac tinv)
         apply ((wp restart_silc_inv hoare_vcg_if_lift suspend_silc_inv mapM_x_wp[OF _ subset_refl]
                    hoare_weak_lift_imp
                 | wpc
                 | simp split del: if_split add: authorised_tcb_inv_def check_cap_at_def
                 | clarsimp
                 | strengthen invs_mdb
                 | force intro: notE[rotated,OF idle_no_ex_cap,simplified])+)[3]
      defer
      apply ((wp suspend_silc_inv restart_silc_inv | simp add: authorised_tcb_inv_def | force)+)[2]
    (* NotificationControl *)
    apply (rename_tac option)
    apply (case_tac option; (wp | simp)+)
   (* SetTLSBase *)
   apply (wpsimp split: option.splits)
  (* just ThreadControl left *)
  apply (simp add: split_def cong: option.case_cong)
  (* slow, ~2 mins *)
  apply (simp only: conj_ac cong: conj_cong imp_cong |
         wp checked_insert_pas_refined checked_cap_insert_silc_inv hoare_vcg_all_liftE_R
            hoare_vcg_all_lift hoare_vcg_const_imp_liftE_R
            cap_delete_silc_inv_not_transferable
            cap_delete_pas_refined' cap_delete_deletes
            cap_delete_valid_cap cap_delete_cte_at
            check_cap_inv[where P="valid_cap c" for c]
            check_cap_inv[where P="cte_at p0" for p0]
            check_cap_inv[where P="\<lambda>s. \<not> tcb_at t s" for t]
            check_cap_inv2[where Q="\<lambda>_. valid_list"]
            check_cap_inv2[where Q="\<lambda>_. valid_sched"]
            check_cap_inv2[where Q="\<lambda>_. simple_sched_action"]
            checked_insert_no_cap_to
            thread_set_tcb_fault_handler_update_invs
            thread_set_pas_refined thread_set_emptyable thread_set_valid_cap
            thread_set_not_state_valid_sched thread_set_cte_at
            thread_set_no_cap_to_trivial
        | wpc
        | simp add: emptyable_def tcb_cap_cases_def tcb_cap_valid_def st_tcb_at_triv
                   option_update_thread_def
        | strengthen use_no_cap_to_obj_asid_strg invs_mdb
                    invs_psp_aligned invs_vspace_objs invs_arch_state
        | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: authorised_tcb_inv_def emptyable_def)
  (* also slow, ~15s *)
  by (clarsimp simp: is_cap_simps is_cnode_or_valid_arch_def is_valid_vtable_root_def
      | intro impI
      | rule conjI)+

end


global_interpretation FinalCaps_2?: FinalCaps_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact FinalCaps_assms)?)
qed

end