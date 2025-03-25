(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_AC
imports Finalise_AC
begin

context Arch begin global_naming RISCV64

named_theorems Finalise_AC_assms

lemma state_vrefs_clear_asid_table:
  "state_vrefs (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                     then None
                                                                     else asid_table s a\<rparr>\<rparr>) x
   \<subseteq> state_vrefs s x"
  by (fastforce simp: state_vrefs_def dest: vs_lookup_clear_asid_table[simplified fun_upd_def])

lemma state_vrefs_clear_asid_pool:
  assumes "asid_table s (asid_high_bits_of asid) = Some pool_ptr"
  and "ako_at (ASIDPool pool) pool_ptr s"
  shows "state_vrefs (s\<lparr>kheap := \<lambda>a. if a = pool_ptr
                                     then Some (ArchObj (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid
                                                                       then None
                                                                       else pool a)))
                                     else kheap s a\<rparr>) x
         \<subseteq> state_vrefs s x"
  (is "state_vrefs ?s' _ \<subseteq> state_vrefs _ _")
  using assms
  apply -
  apply (clarsimp simp: state_vrefs_def)
  apply (rule exI, rule conjI)
   apply (rule_tac x=lvl in exI)
   apply (rule_tac x="if x = pool_ptr then ASIDPool pool else ao" in exI)
   apply (rule conjI, rule refl)
   apply (rule_tac x=bot in exI)
   apply (rule_tac x=asida in exI)
   apply (rule_tac x=vref in exI)
   apply (prop_tac "ptes_of ?s' = ptes_of s")
    apply (fastforce simp: obj_at_def all_ext ptes_of_def obind_def opt_map_def)
   apply (fastforce simp: vs_lookup_table_def vspace_for_pool_def obj_at_def obind_def opt_map_def
                   split: option.split_asm if_split_asm)
  apply (fastforce simp: vs_refs_aux_def graph_of_def opt_map_def split: if_splits)
  done

crunch set_vm_root for pas_refined[wp]: "pas_refined aag"

lemma delete_asid_pool_pas_refined[wp]:
  "delete_asid_pool base ptr \<lbrace>pas_refined aag\<rbrace>"
  unfolding delete_asid_pool_def
  apply wpsimp
  apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
  apply (rule conjI; clarsimp)
   apply (erule subsetD)
   apply (clarsimp simp: auth_graph_map_def)
   apply (rule exI, rule conjI, rule refl)+
   apply (erule state_bits_to_policy_vrefs_subseteq; fastforce?)
   apply (clarsimp simp: allI state_vrefs_clear_asid_table)
  apply (erule subsetD, erule state_asids_to_policy_vrefs_subseteq)
    apply clarsimp
   apply (clarsimp simp: allI state_vrefs_clear_asid_table)
  apply clarsimp
  done

lemma delete_asid_pas_refined[wp]:
  "delete_asid asid pt \<lbrace>pas_refined aag\<rbrace>"
  unfolding delete_asid_def
  apply (rule bind_wp)
   apply (wpsimp simp: set_asid_pool_def wp: set_object_wp hoare_vcg_imp_lift' hoare_vcg_all_lift)
    apply (rule_tac Q'="\<lambda>_ s. riscv_asid_table (arch_state s) = asid_table \<and>
                             ako_at (ASIDPool pool) x2 s \<and> pas_refined aag s"
                 in hoare_strengthen_post[rotated])
     defer
     apply wpsimp+
  apply (clarsimp simp: pas_refined_def)
  apply (intro conjI)
    apply (clarsimp simp: state_objs_to_policy_def)
    apply (subst (asm) caps_of_state_fun_upd[simplified fun_upd_def])
     apply (clarsimp simp: obj_at_def)
    apply (erule subsetD)
    apply (clarsimp simp: auth_graph_map_def)
    apply (rule exI, rule conjI, rule refl)+
    apply (erule state_bits_to_policy_vrefs_subseteq)
        apply clarsimp
       apply (clarsimp simp: all_ext thread_st_auth_def tcb_states_of_state_def get_tcb_def obj_at_def)
      apply (clarsimp simp: all_ext thread_bound_ntfns_def get_tcb_def obj_at_def)
     apply clarsimp
    apply (rule allI[OF state_vrefs_clear_asid_pool]; simp)
   apply clarsimp
   apply (erule subsetD, erule state_asids_to_policy_vrefs_subseteq)
     apply (fastforce simp: obj_at_def caps_of_state_fun_upd[simplified fun_upd_def])
    apply (rule allI[OF state_vrefs_clear_asid_pool]; fastforce)
   apply fastforce
  apply (fastforce simp: obj_at_def caps_of_state_fun_upd[simplified fun_upd_def])
  done

lemma arch_finalise_cap_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and valid_arch_cap c\<rbrace> arch_finalise_cap c x \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding arch_finalise_cap_def
  apply (wpsimp wp: unmap_page_pas_refined unmap_page_table_pas_refined)
  apply (auto simp: valid_arch_cap_def wellformed_mapdata_def)
  done

crunch prepare_thread_delete
  for pas_refined[wp]: "pas_refined aag"

crunch prepare_thread_delete
  for respects[Finalise_AC_assms, wp]: "integrity aag X st"

lemma sbn_st_vrefs[Finalise_AC_assms]:
  "set_bound_notification t st \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (subst state_vrefs_tcb_upd)
      apply (auto simp: tcb_at_def)
  done

lemma arch_finalise_cap_auth'[Finalise_AC_assms]:
  "\<lbrace>pas_refined aag\<rbrace> arch_finalise_cap x12 final \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag (fst rv)\<rbrace>"
  unfolding arch_finalise_cap_def
  by (wp | wpc | simp add: comp_def hoare_TrueI[where P = \<top>] split del: if_split)+

lemma arch_finalise_cap_obj_refs[Finalise_AC_assms]:
  "\<lbrace>\<lambda>s. \<forall>x \<in> aobj_ref' acap. P x\<rbrace>
   arch_finalise_cap acap slot
   \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs_ac (fst rv). P x\<rbrace>"
  by (wpsimp simp: arch_finalise_cap_def)

lemma arch_finalise_cap_makes_halted[Finalise_AC_assms]:
  "\<lbrace>\<top>\<rbrace> arch_finalise_cap arch_cap ex \<lbrace>\<lambda>rv s. \<forall>t\<in>obj_refs_ac (fst rv). halted_if_tcb t s\<rbrace>"
  apply (case_tac arch_cap, simp_all add: arch_finalise_cap_def)
  by (wpsimp simp: valid_cap_def split: option.split bool.split)+

lemma arch_cap_cleanup_wf[Finalise_AC_assms]:
  "\<lbrakk> arch_cap_cleanup_opt acap \<noteq> NullCap; \<not> is_arch_cap (arch_cap_cleanup_opt acap) \<rbrakk>
     \<Longrightarrow> (\<exists>irq. arch_cap_cleanup_opt acap = IRQHandlerCap irq \<and> is_subject_irq aag irq)"
  by simp

lemma set_vm_root_integrity[wp]:
  "set_vm_root param_a \<lbrace>integrity aag X st\<rbrace> "
  unfolding set_vm_root_def
  by (wpsimp wp: dmo_wp mol_respects get_cap_wp simp: setVSpaceRoot_def)

lemma delete_asid_pool_respects[wp]:
  "\<lbrace>integrity aag X st and
    K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of x
               \<longrightarrow> is_subject_asid aag asid')\<rbrace>
   delete_asid_pool x y
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding delete_asid_pool_def
  by (wpsimp wp: mapM_wp[OF _ subset_refl]  simp: integrity_asid_table_entry_update' integrity_def)

crunch set_vm_root
  for integrity_obj[wp]: "integrity_obj_state aag activate subjects st"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and is_original_cap[wp]: "\<lambda>s. P (is_original_cap s x)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_states s x)"
  and underlying_memory[wp]: "\<lambda>s. P (underlying_memory (machine_state s) x)"
  and device_state[wp]: "\<lambda>s. P (device_state (machine_state s) x)"
  and tcb_states_of_state[wp]: "\<lambda>s. P (tcb_states_of_state s)"
  (wp: dmo_wp)

crunch set_asid_pool
  for is_original_cap[wp]: "\<lambda>s. P (is_original_cap s x)"
  and cdt_list[wp]: "\<lambda>s. P (cdt_list s x)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s x y)"
  and machine_state[wp]: "\<lambda>s. P (machine_state s)"

lemma set_asid_pool_tcb_states_of_state[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def  set_asid_pool_def)
  apply (prop_tac "\<forall>x. get_tcb x (s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (ASIDPool pool))\<rparr>) = get_tcb x s")
   apply (auto simp: tcb_states_of_state_def get_tcb_def)
  done

lemma delete_asid_integrity_asids:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> invs s \<and> is_subject aag pt \<and>
        (\<forall>x a. integrity_asids aag {pasSubject aag} x a st s)\<rbrace>
   delete_asid asid pt
   \<lbrace>\<lambda>_ s. integrity_asids aag {pasSubject aag} x a st s\<rbrace>"
  unfolding integrity_def
  apply (wpsimp wp: dmo_wp mol_respects set_object_wp hoare_vcg_all_lift hoare_vcg_imp_lift
              simp: delete_asid_def hwASIDFlush_def set_asid_pool_def)
  apply (intro conjI impI allI; clarsimp)
   apply fastforce
  apply (clarsimp simp: opt_map_def)
  apply (erule_tac x=asid in allE, fastforce)
  done

lemma set_asid_pool_respects_clear:
  "\<lbrace>integrity_obj_state aag activate subjects st and
    (\<lambda>s. \<forall>pool'. ako_at (ASIDPool pool') ptr s \<longrightarrow> asid_pool_integrity subjects aag pool' pool)\<rbrace>
   set_asid_pool ptr pool
   \<lbrace>\<lambda>_. integrity_obj_state aag activate subjects st\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def set_asid_pool_def)
  using arch_troa_asidpool_clear tro_arch tro_trans_spec by fastforce

lemma delete_asid_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and K (is_subject aag pd)\<rbrace>
   delete_asid asid pd
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding integrity_def
  supply integrity_asids_def[simp del]
  apply (rule hoare_pre)
   apply (simp only: conj_assoc[symmetric])
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: delete_asid_def)
    apply (wp | wpc | wps)+
       apply (wpsimp wp: set_asid_pool_respects_clear dmo_wp
                         delete_asid_integrity_asids hoare_vcg_all_lift)+
  apply (clarsimp simp: pas_refined_refl obj_at_def asid_pool_integrity_def)
  done

lemma arch_finalise_cap_respects[Finalise_AC_assms, wp]:
  "\<lbrace>integrity aag X st and invs and pas_refined aag and valid_cap (ArchObjectCap cap)
                       and K (pas_cap_cur_auth aag (ArchObjectCap cap))\<rbrace>
   arch_finalise_cap cap final
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (wpsimp wp: unmap_page_respects unmap_page_table_respects delete_asid_respects)
  apply (auto simp: cap_auth_conferred_def arch_cap_auth_conferred_def wellformed_mapdata_def
                    aag_cap_auth_def pas_refined_all_auth_is_owns valid_cap_simps
                    cap_links_asid_slot_def label_owns_asid_slot_def
             intro: pas_refined_Control_into_is_subject_asid)
  done

declare prepare_thread_delete_st_tcb_at_halted[Finalise_AC_assms]
declare finalise_cap_valid_list[Finalise_AC_assms]
declare arch_finalise_cap_pas_refined[Finalise_AC_assms]
declare prepare_thread_delete_pas_refined[Finalise_AC_assms]
declare finalise_cap_replaceable[Finalise_AC_assms]

end


global_interpretation Finalise_AC_1?: Finalise_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Finalise_AC_assms | solves \<open>wp only: Finalise_AC_assms; simp\<close>)?)
qed


context Arch begin global_naming RISCV64

lemma cap_revoke_respects'[Finalise_AC_assms]:
  "s \<turnstile> \<lbrace>(\<lambda>s. trp \<longrightarrow> integrity aag X st s) and K (is_subject aag (fst slot))
                                           and pas_refined aag and einvs and simple_sched_action\<rbrace>
       cap_revoke slot
       \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>,
       \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>"
proof (induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
    apply (subst cap_revoke.simps)
    apply (rule hoare_pre_spec_validE)
     apply (wp "1.hyps")
            apply ((wp preemption_point_inv' | simp add: integrity_subjects_def pas_refined_def)+)[1]
           apply (wp select_ext_weak_wp cap_delete_respects cap_delete_pas_refined
                  | simp split del: if_split | wp (once) hoare_vcg_const_imp_lift hoare_drop_imps)+
    by (auto simp: emptyable_def descendants_of_def
             dest: reply_slot_not_descendant
            intro: cca_owned)
qed

lemma finalise_cap_caps_of_state_nullinv[Finalise_AC_assms]:
  "\<lbrace>\<lambda>s. P (caps_of_state s) \<and> (\<forall>p. P ((caps_of_state s)(p \<mapsto> NullCap)))\<rbrace>
   finalise_cap cap final
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (cases cap;
      wpsimp wp: suspend_caps_of_state unbind_notification_caps_of_state
                 unbind_notification_cte_wp_at
                 hoare_vcg_all_lift hoare_drop_imps
                 deleting_irq_handler_caps_of_state_nullinv
           simp: fun_upd_def[symmetric] if_apply_def2 split_del: if_split)

lemma finalise_cap_fst_ret[Finalise_AC_assms]:
  "\<lbrace>\<lambda>_. P NullCap \<and> (\<forall>a b c. P (Zombie a b c))\<rbrace>
   finalise_cap cap is_final
   \<lbrace>\<lambda>rv _. P (fst rv)\<rbrace>"
  including classic_wp_pre
  apply (cases cap, simp_all add: arch_finalise_cap_def split del: if_split)
  apply (wp | simp add: comp_def split del: if_split | fastforce)+
  apply (rule hoare_pre)
  apply (wp | simp | (rule hoare_pre, wpc))+
  done

end


global_interpretation Finalise_AC_2?: Finalise_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Finalise_AC_assms)?)
qed

end