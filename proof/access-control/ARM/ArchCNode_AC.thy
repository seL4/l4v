(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchCNode_AC
imports CNode_AC
begin

section\<open>Arch-specific CNode AC.\<close>

context Arch begin global_naming ARM_A

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

lemma set_cap_state_vrefs[CNode_AC_assms, wp]:
  "set_cap cap ptr \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  apply (wpsimp wp: get_object_wp simp: set_cap_def split_def set_object_def)
  apply (auto simp: obj_at_def state_vrefs_def
             elim!: rsubst[where P=P, OF _ ext]
             split: if_split_asm simp: vs_refs_no_global_pts_def)
  done

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
  apply (rule ext)
  apply (auto simp: state_vrefs_def vs_refs_no_global_pts_def tcb_at_def dest!: get_tcb_SomeD)
  done

lemma state_vrefs_simple_type_upd[CNode_AC_assms]:
  "\<lbrakk> ko_at ko ptr s; is_simple_type ko; a_type ko = a_type (f val) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := (kheap s)(ptr \<mapsto> f val)\<rparr>) = state_vrefs s"
  apply (rule ext)
  apply (auto simp: state_vrefs_def vs_refs_no_global_pts_def obj_at_def partial_inv_def a_type_def
             split: kernel_object.splits arch_kernel_obj.splits if_splits)
  done

(* FIXME: move *)
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
  shows "\<lbrace>integrity aag X st and Q\<rbrace> f \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_pre)
   apply (unfold integrity_def[abs_def] integrity_asids_def)
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (simp add: tcb_states_of_state_def get_tcb_def)
   apply (wp li[simplified tcb_states_of_state_def get_tcb_def])+
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (simp add: tcb_states_of_state_def get_tcb_def)
  done

end


global_interpretation CNode_AC_1?: CNode_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact CNode_AC_assms | solves \<open>wp only: CNode_AC_assms; simp\<close>)?)
qed


context Arch begin global_naming ARM_A

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
    by (unfold_locales; (fact CNode_AC_assms)?)
qed


context Arch begin global_naming ARM_A

lemma arch_post_cap_deletion_pas_refined[CNode_AC_assms, wp]:
  "arch_post_cap_deletion irqopt \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp simp: post_cap_deletion_def)

lemma aobj_ref'_same_aobject[CNode_AC_assms]:
  "same_aobject_as ao' ao \<Longrightarrow> aobj_ref' ao = aobj_ref' ao'"
  by (cases ao; clarsimp split: arch_cap.splits)

crunch set_untyped_cap_as_full
  for valid_arch_state[CNode_AC_assms]: valid_arch_state

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
    by (unfold_locales; (fact CNode_AC_assms)?)
qed


context Arch begin global_naming ARM_A

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


context Arch begin global_naming ARM_A

lemma pas_refined_arch_state_update_not_asids[simp]:
 "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s)
  \<Longrightarrow> pas_refined aag (arch_state_update f s) = pas_refined aag s"
  by (simp add: pas_refined_def state_objs_to_policy_def)

crunch store_pte
  for cdt[wp]: "\<lambda>s. P (cdt s)"

lemma store_pte_state_refs[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def state_refs_of_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma all_rsubst:
  "\<lbrakk> \<forall>v. P (f v); \<exists>v. f v = r \<rbrakk> \<Longrightarrow> P r"
  by clarsimp

lemma store_pte_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. \<forall>S. P ((state_vrefs s) (p && ~~ mask pt_bits :=
                                  (state_vrefs s (p && ~~ mask pt_bits) - S) \<union>
                                  (\<Union>(p', sz, auth)\<in>set_option (pte_ref pte).
                                     (\<lambda>(p'', a). (p'', (p && mask pt_bits) >> 2, APageTable, a)) `
                                                                       (ptr_range p' sz \<times> auth))))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def obj_at_def)
  apply (simp add: fun_upd_def[symmetric] fun_upd_comp)
  apply (erule all_rsubst[where P=P])
  apply (subst fun_eq_iff, clarsimp simp: split_def)
  apply (cases "pte_ref pte")
   apply (auto simp: ucast_ucast_mask shiftr_over_and_dist
                     word_bw_assocs mask_def pt_bits_def pageBits_def)
  done

lemma store_pte_thread_st_auth[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_st_auth_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma store_pte_thread_bound_ntfns[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma auth_graph_map_def2:
  "auth_graph_map f S = (\<lambda>(x, auth, y). (f x, auth, f y)) ` S"
  by (auto simp add: auth_graph_map_def image_def intro: rev_bexI)

crunch store_pte
  for etcbs_of[wp]: "\<lambda>s. P (etcbs_of s)"
  and asid_table_inv[wp]: "\<lambda>s. P (asid_table s)"

lemma store_pte_pas_refined[wp]:
  "\<lbrace>pas_refined aag and
    K (\<forall>x. pte_ref pte = Some x
           \<longrightarrow> (\<forall>a \<in> snd (snd x). \<forall>p' \<in> (ptr_range (fst x) (fst (snd x))).
                auth_graph_map (pasObjectAbs aag) {(p && ~~ mask pt_bits, a, p')} \<subseteq> pasPolicy aag))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: auth_graph_map_def2)
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD split del: if_split)
   apply (erule state_bits_to_policy.cases,
          auto intro: state_bits_to_policy.intros auth_graph_map_memI
               split: if_split_asm)[1]
  apply (erule_tac B="state_asids_to_policy_aux _ _ _ _" in subset_trans[rotated])
  apply (auto intro: state_asids_to_policy_aux.intros
              elim!: state_asids_to_policy_aux.cases
               elim: subset_trans[rotated]
              split: if_split_asm)
  done

lemma store_pde_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. \<forall>S. P ((state_vrefs s) (p && ~~ mask pd_bits :=
                                  (state_vrefs s (p && ~~ mask pd_bits) - S) \<union>
                                  (if ucast (kernel_base >> 20) \<le> (ucast (p && mask pd_bits >> 2)::12 word)
                                   then {}
                                   else (\<Union>(p', sz, auth)\<in>set_option (pde_ref2 pde).
                                        (\<lambda>(p'', a). (p'', (p && mask pd_bits) >> 2, APageDirectory, a)) `
                                                                             (ptr_range p' sz \<times> auth)))))\<rbrace>
   store_pde p pde
   \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def split del: if_split)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule all_rsubst[where P=P], subst fun_eq_iff)
  apply (clarsimp simp add: state_vrefs_def vs_refs_no_global_pts_def
                            fun_upd_def[symmetric] fun_upd_comp)
  apply (cases "pde_ref2 pde")
  by (auto simp: split_def insert_Diff_if Un_ac ucast_ucast_mask_shift_helper)

lemma store_pde_thread_st_auth[wp]:
  "store_pde p pde \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_st_auth_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma store_pde_thread_bound_ntfns[wp]:
  "store_pde p pde \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma store_pde_pas_refined[wp]:
  "\<lbrace>pas_refined aag and
    K ((ucast (p && mask pd_bits >> 2)::12 word) < (ucast (kernel_base >> 20))
       \<longrightarrow> (\<forall>x. pde_ref2 pde = Some x \<longrightarrow>  (\<forall>a \<in> snd (snd x). \<forall>p' \<in> ptr_range (fst x) (fst (snd x)).
            auth_graph_map (pasObjectAbs aag) {(p && ~~ mask pd_bits, a, p')} \<subseteq> pasPolicy aag)))\<rbrace>
   store_pde p pde
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: auth_graph_map_def2)
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply (clarsimp split del: if_split)
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD split del: if_split)
   apply (erule state_bits_to_policy.cases,
          auto intro: state_bits_to_policy.intros auth_graph_map_memI
               split: if_split_asm)[1]
  apply (erule_tac B="state_asids_to_policy_aux _ _ _ _" in subset_trans[rotated])
  apply (auto intro: state_asids_to_policy_aux.intros
              elim!: state_asids_to_policy_aux.cases
              split: if_split_asm)
  done

lemmas pde_ref_simps = pde_ref_def[split_simps pde.split] pde_ref2_def[split_simps pde.split]

lemma set_asid_pool_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P ((state_vrefs s) (p := (\<lambda>(r, p). (p, ucast r, AASIDPool, Control)) ` graph_of pool))\<rbrace>
   set_asid_pool p pool
   \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def fun_upd_def[symmetric] fun_upd_comp obj_at_def
                        vs_refs_no_global_pts_def
                 split: kernel_object.split_asm arch_kernel_obj.split_asm
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma set_asid_pool_thread_st_auth[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: thread_st_auth_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma set_asid_pool_thread_bound_ntfns[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma set_asid_pool_pas_refined[wp]:
  "\<lbrace>pas_refined aag and
    (\<lambda>s. \<forall>(x, y) \<in> graph_of pool.
           auth_graph_map (pasObjectAbs aag) {(p, Control, y)} \<subseteq> pasPolicy aag \<and>
           (\<forall>asid. asid_table s (asid_high_bits_of asid) = Some p \<and>
                   asid && mask asid_low_bits = ucast x
                   \<longrightarrow> (pasASIDAbs aag asid, Control, pasObjectAbs aag y) \<in> pasPolicy aag))\<rbrace>
         set_asid_pool p pool \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: auth_graph_map_def2 image_UN split_def)
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD)
   apply (erule state_bits_to_policy.cases,
          auto intro: state_bits_to_policy.intros auth_graph_map_memI
               split: if_split_asm)[1]
  apply (auto intro: state_asids_to_policy_aux.intros
               simp: subsetD[OF _ state_asids_to_policy_aux.intros(2)]
              elim!: state_asids_to_policy_aux.cases
              split: if_split_asm)
  apply fastforce+
  done

lemma pas_refined_clear_asid:
  "pas_refined aag s
   \<Longrightarrow> pas_refined aag (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := \<lambda>a. if a = asid then None
                                                                           else asid_table s a\<rparr>\<rparr>)"
  by (fastforce simp: pas_refined_def state_objs_to_policy_def
               intro: state_asids_to_policy_aux.intros
               elim!: state_asids_to_policy_aux.cases
               split: if_split_asm)

crunch set_asid_pool
  for integrity_autarch: "integrity aag X st"
  (wp: crunch_wps)

end

end
