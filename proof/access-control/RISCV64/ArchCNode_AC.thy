(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchCNode_AC
imports CNode_AC
begin

section\<open>Arch-specific CNode AC.\<close>

context Arch begin global_naming RISCV64

declare arch_post_modify_registers_def[simp]
declare arch_post_cap_deletion_def[simp]
declare arch_cap_cleanup_opt_def[simp]
declare arch_mask_irq_signal_def[simp]

named_theorems CNode_AC_assms

lemma sata_cdt_update[CNode_AC_assms, simp]:
  "state_asids_to_policy aag (cdt_update f s) = state_asids_to_policy aag s"
  by simp

lemma sata_is_original_cap_update[CNode_AC_assms, simp]:
  "state_asids_to_policy aag (is_original_cap_update f s) = state_asids_to_policy aag s"
  by simp

lemma sata_interrupt_states_update[CNode_AC_assms, simp]:
  "state_asids_to_policy aag (interrupt_states_update f s) = state_asids_to_policy aag s"
  by simp

lemma sata_machine_state_update[CNode_AC_assms, simp]:
  "state_asids_to_policy aag (machine_state_update f s) = state_asids_to_policy aag s"
  by simp

lemma sata_update[CNode_AC_assms]:
  "\<lbrakk> pas_wellformed aag;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr)) cap;
     state_asids_to_policy_arch aag caps as vrefs \<subseteq> pasPolicy aag \<rbrakk>
     \<Longrightarrow> state_asids_to_policy_arch aag (caps(ptr \<mapsto> cap)) as vrefs \<subseteq> pasPolicy aag"
  by (fastforce intro: state_asids_to_policy_aux.intros
                 elim!: state_asids_to_policy_aux.cases
                 simp: cap_links_asid_slot_def label_owns_asid_slot_def
                split: if_split_asm)

lemma sata_update2[CNode_AC_assms]:
  "\<lbrakk> pas_wellformed aag;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr)) cap;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr')) cap';
     state_asids_to_policy_arch aag caps as vrefs \<subseteq> pasPolicy aag \<rbrakk>
     \<Longrightarrow> state_asids_to_policy_arch aag (caps(ptr \<mapsto> cap, ptr' \<mapsto> cap')) as vrefs \<subseteq> pasPolicy aag"
  by (fastforce intro: state_asids_to_policy_aux.intros
                elim!: state_asids_to_policy_aux.cases
                 simp: cap_links_asid_slot_def label_owns_asid_slot_def
                split: if_split_asm)

lemma vs_lookup_table_eqI':
    "\<lbrakk> asid_table s' (asid_high_bits_of asid) = asid_table s (asid_high_bits_of asid);
       \<forall>pool_ptr. asid_table s' (asid_high_bits_of asid) = Some pool_ptr
                  \<longrightarrow> bot_level \<le> max_pt_level
                  \<longrightarrow> vspace_for_pool pool_ptr asid (asid_pools_of s') =
                      vspace_for_pool pool_ptr asid (asid_pools_of s);
       bot_level < max_pt_level \<longrightarrow> pts_of s' = pts_of s \<rbrakk>
   \<Longrightarrow> vs_lookup_table bot_level asid vref s' = vs_lookup_table bot_level asid vref s"
  by (auto simp: obind_def vs_lookup_table_def asid_pool_level_eq[symmetric]
                 pool_for_asid_def vspace_for_pool_def
          split: option.splits)

lemma state_vrefs_eqI:
  assumes "asid_table s' = asid_table s"
  and "aobjs_of s' = aobjs_of s"
  shows "state_vrefs s' = state_vrefs s"
  apply (prop_tac "\<forall>level asid vref. vs_lookup_table level asid vref s = vs_lookup_table level asid vref s'")
   apply (intro allI vs_lookup_table_eqI')
  using assms by (auto simp: vspace_for_pool_def state_vrefs_def)

lemma set_cap_state_vrefs[CNode_AC_assms, wp]:
  "set_cap cap slot \<lbrace>\<lambda>s :: det_ext state. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_cap_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply safe
        apply (all \<open>subst state_vrefs_eqI\<close>)
  by (fastforce simp: valid_arch_state_def obj_at_def opt_map_def
               split: option.splits kernel_object.splits)+

crunch maskInterrupt
  for underlying_memory[CNode_AC_assms, wp]: "\<lambda>s. P (underlying_memory s)"
  and device_state[CNode_AC_assms, wp]: "\<lambda>s. P (device_state s)"
  (simp: maskInterrupt_def)

crunch set_cdt
  for state_vrefs[CNode_AC_assms, wp]: "\<lambda>s. P (state_vrefs s)"
  and state_asids_to_policy[CNode_AC_assms, wp]: "\<lambda>s. P (state_asids_to_policy aag s)"

crunch prepare_thread_delete, arch_finalise_cap
  for cur_domain[CNode_AC_assms, wp]:"\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps hoare_vcg_if_lift2 simp: unless_def)

lemma state_vrefs_tcb_upd[CNode_AC_assms]:
  "tcb_at t s \<Longrightarrow> state_vrefs (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>) = state_vrefs s"
  apply (rule state_vrefs_eqI)
  by (fastforce simp: opt_map_def obj_at_def is_obj_defs valid_arch_state_def)+

lemma state_vrefs_simple_type_upd[CNode_AC_assms]:
  "\<lbrakk> ko_at ko ptr s; is_simple_type ko; a_type ko = a_type (f val) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := (kheap s)(ptr \<mapsto> f val)\<rparr>) = state_vrefs s"
  apply (case_tac ko; case_tac "f val"; clarsimp)
  by (fastforce intro!: state_vrefs_eqI simp: opt_map_def obj_at_def is_obj_defs valid_arch_state_def)+

lemma a_type_arch_object_not_tcb[CNode_AC_assms, simp]:
  "a_type (ArchObj arch_kernel_obj) \<noteq> ATCB"
  by auto

lemma arch_post_cap_deletion_cur_domain[CNode_AC_assms, wp]:
  "arch_post_cap_deletion acap \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  by wpsimp

lemma arch_post_cap_deletion_integrity[CNode_AC_assms]:
  "arch_post_cap_deletion acap \<lbrace>integrity aag X st\<rbrace>"
  by wpsimp

end


context is_extended begin interpretation Arch .

lemma list_integ_lift[CNode_AC_assms]:
  assumes li:
    "\<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
     f
     \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag}  (cdt st) (tcb_states_of_state st)) st\<rbrace>"
  assumes ekh: "\<And>P. f \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  assumes rq: "\<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  shows "\<lbrace>integrity aag X st and Q\<rbrace> f \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_pre)
   apply (unfold integrity_def[abs_def] integrity_asids_def)
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (rule hoare_lift_Pf2[where f="ekheap"])
    apply (simp add: tcb_states_of_state_def get_tcb_def)
    apply (wp li[simplified tcb_states_of_state_def get_tcb_def] ekh rq)+
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (simp add: tcb_states_of_state_def get_tcb_def)
  done

end


global_interpretation CNode_AC_1?: CNode_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact CNode_AC_assms)
qed


context Arch begin global_naming RISCV64

lemma integrity_asids_set_cap_Nullcap[CNode_AC_assms]:
  "\<lbrace>(=) s\<rbrace> set_cap NullCap slot \<lbrace>\<lambda>_. integrity_asids aag subjects x a s\<rbrace>"
  unfolding integrity_asids_def by wpsimp

crunch set_original
  for state_asids_to_policy[CNode_AC_assms, wp]: "\<lambda>s. P (state_asids_to_policy aag s)"
  and state_objs_to_policy[CNode_AC_assms, wp]: "\<lambda>s. P (state_objs_to_policy s)"
  (simp: state_objs_to_policy_def)

crunch set_cdt_list, update_cdt_list
  for state_vrefs[CNode_AC_assms, wp]: "\<lambda>s. P (state_vrefs s)"
  and state_asids_to_policy[CNode_AC_assms, wp]: "\<lambda>s. P (state_asids_to_policy aag s)"
  (simp: set_cdt_list_def)

end


global_interpretation CNode_AC_2?: CNode_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact CNode_AC_assms)
qed


context Arch begin global_naming RISCV64

lemma arch_post_cap_deletion_pas_refined[CNode_AC_assms, wp]:
  "arch_post_cap_deletion irqopt \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp simp: post_cap_deletion_def)

lemma aobj_ref'_same_aobject[CNode_AC_assms]:
  "same_aobject_as ao' ao \<Longrightarrow> aobj_ref' ao = aobj_ref' ao'"
  by (cases ao; clarsimp split: arch_cap.splits)

crunch set_untyped_cap_as_full
  for valid_arch_state[CNode_AC_assms, wp]: valid_arch_state

end


context is_extended begin interpretation Arch .

lemma pas_refined_tcb_domain_map_wellformed[CNode_AC_assms, wp]:
  assumes tdmw: "f \<lbrace>tcb_domain_map_wellformed aag\<rbrace>"
  shows "f \<lbrace>pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def)
  apply (wp tdmw)
   apply (wp lift_inv)
   apply simp+
  done

end


global_interpretation CNode_AC_3?: CNode_AC_3
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact CNode_AC_assms)
qed


context Arch begin global_naming RISCV64

lemma arch_derive_cap_auth_derived[CNode_AC_assms]:
  "\<lbrace>\<lambda>s. cte_wp_at (auth_derived (ArchObjectCap cap)) src_slot s\<rbrace>
   arch_derive_cap cap
   \<lbrace>\<lambda>rv s. cte_wp_at (auth_derived rv) src_slot s\<rbrace>, -"
  apply (rule hoare_pre)
   apply (wp | wpc | simp add: arch_derive_cap_def)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (safe)
  apply (clarsimp simp: auth_derived_def arch_cap_auth_conferred_def cap_auth_conferred_def)
  done

lemma cap_asid'_cap_rights_update[CNode_AC_assms, simp]:
  "acap_asid' (acap_rights_update rights ao) = acap_asid' ao"
  by (cases ao; clarsimp simp: cap_rights_update_def acap_rights_update_def)

lemma untyped_range_cap_rights_update[CNode_AC_assms, simp]:
  "untyped_range (cap_rights_update rights (ArchObjectCap ao)) = untyped_range (ArchObjectCap ao)"
  by (cases ao; clarsimp simp: cap_rights_update_def)

lemma obj_refs_cap_rights_update[CNode_AC_assms, simp]:
  "aobj_ref' (acap_rights_update rights ao) = aobj_ref' ao"
  by (cases ao; clarsimp simp: cap_rights_update_def acap_rights_update_def)

lemma auth_derived_arch_update_cap_data[CNode_AC_assms]:
  "auth_derived (ArchObjectCap ao) cap' \<Longrightarrow> auth_derived (arch_update_cap_data pres w ao) cap'"
  by (simp add: update_cap_data_def is_cap_simps arch_update_cap_data_def
                  split del: if_split cong: if_cong)

lemma acap_auth_conferred_acap_rights_update[CNode_AC_assms]:
  "arch_cap_auth_conferred (acap_rights_update (acap_rights acap \<inter> R) acap)
   \<subseteq> arch_cap_auth_conferred acap"
  by (auto simp: arch_cap_auth_conferred_def vspace_cap_rights_to_auth_def acap_rights_update_def
                 validate_vm_rights_def vm_kernel_only_def vm_read_only_def
          split: arch_cap.splits)

lemma arch_derive_cap_clas[CNode_AC_assms]:
  "\<lbrace>\<lambda>s. cap_links_asid_slot aag p (ArchObjectCap acap)\<rbrace>
   arch_derive_cap acap
   \<lbrace>\<lambda>rv s. cap_links_asid_slot aag p rv\<rbrace>, -"
  apply (simp add: arch_derive_cap_def cong: cap.case_cong)
  apply (rule hoare_pre)
  apply (wp | wpc)+
  apply (auto simp: is_cap_simps cap_links_asid_slot_def)
  done

lemma arch_derive_cap_obj_refs_auth[CNode_AC_assms]:
  "\<lbrace>K (\<forall>r\<in>obj_refs_ac (ArchObjectCap cap).
       \<forall>auth\<in>cap_auth_conferred (ArchObjectCap cap). aag_has_auth_to aag auth r)\<rbrace>
   arch_derive_cap cap
   \<lbrace>(\<lambda>x s. \<forall>r\<in>obj_refs_ac x. \<forall>auth\<in>cap_auth_conferred x. aag_has_auth_to aag auth r)\<rbrace>, -"
  unfolding arch_derive_cap_def
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
  done

(* FIXME: move *)
lemma arch_derive_cap_obj_refs_subset[CNode_AC_assms]:
  "\<lbrace>\<lambda>s. (\<forall>x \<in> aobj_ref' acap. P x s)\<rbrace> arch_derive_cap acap \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs_ac rv. P x s\<rbrace>, -"
  by (wpsimp simp: arch_derive_cap_def) fastforce

lemma arch_derive_cap_clip[CNode_AC_assms]:
  "\<lbrace>K (cap_links_irq aag l (ArchObjectCap ac))\<rbrace>
   arch_derive_cap ac
   \<lbrace>\<lambda>x s. cap_links_irq aag l x\<rbrace>, -"
  by (wpsimp simp: arch_derive_cap_def comp_def cli_no_irqs)

(* FIXME: move *)
lemma arch_derive_cap_untyped_range_subset[CNode_AC_assms]:
  "\<lbrace>\<lambda>s. \<forall>x \<in> untyped_range (ArchObjectCap acap). P x s\<rbrace>
   arch_derive_cap acap
   \<lbrace>\<lambda>rv s. \<forall>x \<in> untyped_range rv. P x s\<rbrace>, -"
  by (wpsimp simp: arch_derive_cap_def)

lemma arch_update_cap_obj_refs_subset[CNode_AC_assms]:
  "\<lbrakk> x \<in> obj_refs_ac (arch_update_cap_data pres data cap) \<rbrakk> \<Longrightarrow> x \<in> aobj_ref' cap"
  by (simp add: arch_update_cap_data_def)

lemma arch_update_cap_untyped_range_empty[CNode_AC_assms, simp]:
  "untyped_range (arch_update_cap_data pres data cap) = {}"
  by (simp add: arch_update_cap_data_def)

lemma arch_update_cap_irqs_controlled_empty[CNode_AC_assms, simp]:
  "cap_irqs_controlled (arch_update_cap_data pres data cap) = {}"
  by (simp add: arch_update_cap_data_def)

lemma arch_update_cap_links_asid_slot[CNode_AC_assms]:
  "cap_links_asid_slot aag p (arch_update_cap_data pres w acap) =
   cap_links_asid_slot aag p (ArchObjectCap acap)"
  by (simp add: arch_update_cap_data_def)

lemma arch_update_cap_cap_auth_conferred_subset[CNode_AC_assms]:
  "y \<in> cap_auth_conferred (arch_update_cap_data b w acap) \<Longrightarrow> y \<in> arch_cap_auth_conferred acap"
  by (simp add: arch_update_cap_data_def cap_auth_conferred_def)

end


global_interpretation CNode_AC_4?: CNode_AC_4
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact CNode_AC_assms)?)
qed


end
