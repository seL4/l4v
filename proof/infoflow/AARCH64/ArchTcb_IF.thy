(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTcb_IF
imports Tcb_IF
begin

context Arch begin arch_global_naming

named_theorems Tcb_IF_assms

crunch set_irq_state, suspend
  for arm_us_global_vspace[wp]: "\<lambda>s. P (arm_us_global_vspace (arch_state s))"
  (wp: mapM_x_wp select_inv hoare_vcg_if_lift2 hoare_drop_imps dxo_wp_weak
   simp: unless_def
   ignore: empty_slot_ext reschedule_required)

crunch as_user, restart
  for arm_us_global_vspace[wp]: "\<lambda>s. P (arm_us_global_vspace (arch_state s))" (wp: dxo_wp_weak)

lemma cap_ne_global_pt:
  "\<lbrakk> ex_nonz_cap_to word s; valid_global_refs s; valid_global_arch_objs s \<rbrakk>
     \<Longrightarrow> word \<noteq> arm_us_global_vspace (arch_state s)"
  unfolding ex_nonz_cap_to_def
  apply (simp only: cte_wp_at_caps_of_state zobj_refs_to_obj_refs)
  apply (elim exE conjE)
  apply (drule valid_global_refsD2,simp)
  apply (unfold global_refs_def)
  apply clarsimp
  apply (unfold cap_range_def)
  apply blast
  done

lemma valid_arch_caps_vs_lookup[Tcb_IF_assms]:
  "valid_arch_caps s \<Longrightarrow> valid_vs_lookup s"
  by (simp add: valid_arch_caps_def)

lemma no_cap_to_idle_thread'[Tcb_IF_assms]:
  "valid_global_refs s \<Longrightarrow> \<not> ex_nonz_cap_to (idle_thread s) s"
  apply (clarsimp simp add: ex_nonz_cap_to_def valid_global_refs_def valid_refs_def)
  apply (drule_tac x=a in spec)
  apply (drule_tac x=b in spec)
  apply (clarsimp simp: cte_wp_at_def global_refs_def cap_range_def)
  apply (case_tac cap,simp_all)
  done

lemma no_cap_to_idle_thread''[Tcb_IF_assms]:
  "valid_global_refs s \<Longrightarrow> caps_of_state s ref \<noteq> Some (ThreadCap (idle_thread s))"
  apply (clarsimp simp add: valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)
  apply (drule_tac x="fst ref" in spec)
  apply (drule_tac x="snd ref" in spec)
  apply (simp add: cap_range_def global_refs_def)
  done

crunch arch_post_modify_registers
  for globals_equiv[Tcb_IF_assms, wp]: "globals_equiv st"
  and valid_arch_state[Tcb_IF_assms, wp]: valid_arch_state

lemma arch_post_modify_registers_reads_respects_f[Tcb_IF_assms, wp]:
  "reads_respects_f aag l \<top> (arch_post_modify_registers cur t)"
  by wpsimp

lemma reads_equiv_valid_inv_f:
  assumes a: "reads_equiv_valid_inv A aag P f"
  assumes b: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "equiv_valid_inv (reads_equiv_f aag) A P f"
  supply equiv_valid_2_def[simp] equiv_valid_def2[simp]
  apply (clarsimp simp: reads_equiv_f_def)
  apply (insert a, clarsimp)
  apply (drule_tac x=s in spec, drule_tac x=t in spec, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (drule state_unchanged[OF b])+
  by simp

lemma arch_get_sanitise_register_info_reads_respects_f[Tcb_IF_assms, wp]:
  "reads_respects_f aag l (K (aag_can_read_or_affect aag l rv)) (arch_get_sanitise_register_info rv)"
  unfolding arch_get_sanitise_register_info_def
  by (wpsimp wp: reads_equiv_valid_inv_f)

end


global_interpretation Tcb_IF_1?: Tcb_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Tcb_IF_assms)?)
qed


context Arch begin arch_global_naming

lemma valid_ipc_buffer_cap_is_nondevice_page_cap:
  "\<lbrakk>valid_ipc_buffer_cap cap ptr; cap \<noteq> NullCap\<rbrakk> \<Longrightarrow> is_nondevice_page_cap cap"
  by (clarsimp simp: valid_ipc_buffer_cap_def split: cap.splits arch_cap.splits)

lemma is_valid_vtable_root_def2:
  "is_valid_vtable_root c = (\<exists>r a. c = ArchObjectCap (PageTableCap r VSRootPT_T (Some a)))"
  by (auto simp: is_valid_vtable_root_def split: cap.splits arch_cap.splits option.splits pt_type.splits)

(* FIXME: Pretty general. Probably belongs somewhere else *)
lemma invoke_tcb_thread_preservation[Tcb_IF_assms]:
  notes is_nondevice_page_cap_simps[simp del]
  assumes cap_delete_P: "\<And>slot. \<lbrace>invs and P and emptyable slot\<rbrace> cap_delete slot \<lbrace>\<lambda>_. P\<rbrace>"
  assumes cap_insert_P: "\<And>new_cap src dest. \<lbrace>invs and P\<rbrace> cap_insert new_cap src dest \<lbrace>\<lambda>_. P\<rbrace>"
  assumes thread_set_P: "\<And>f ptr. \<lbrace>invs and P\<rbrace> thread_set (tcb_ipc_buffer_update f) ptr \<lbrace>\<lambda>_. P\<rbrace>"
  assumes thread_set_P': "\<And>f ptr. \<lbrace>invs and P\<rbrace> thread_set (tcb_fault_handler_update f) ptr \<lbrace>\<lambda>_. P\<rbrace>"
  assumes set_mcpriority_P: "\<And>mcp ptr. \<lbrace>invs and P\<rbrace> set_mcpriority ptr mcp \<lbrace>\<lambda>_.P\<rbrace>"
  assumes set_priority_P: "\<And>prio ptr. \<lbrace>invs and P\<rbrace> set_priority ptr prio \<lbrace>\<lambda>_.P\<rbrace>"
  assumes reschedule_required_P: "reschedule_required \<lbrace>P\<rbrace>"
  assumes P_trans[simp]: "\<And>f s. P (trans_state f s) = P s"
  shows
    "\<lbrace>P and invs and tcb_inv_wf (tcb_invocation.ThreadControl t sl ep mcp prio croot vroot buf)\<rbrace>
     invoke_tcb (tcb_invocation.ThreadControl t sl ep mcp prio croot vroot buf)
     \<lbrace>\<lambda>rv s :: det_state. P s\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: split_def cong: option.case_cong)
  apply (rule hoare_weaken_pre)
   apply (rule_tac P="case ep of Some v \<Rightarrow> length v = word_bits | _ \<Rightarrow> True"
                in hoare_gen_asm)
   apply wp
        apply (wpsimp wp: set_priority_P)
       apply (rule_tac Q'="\<lambda>_. invs and P" and E'="\<lambda>_. P" in hoare_post_impE; clarsimp)
       apply ((simp add: conj_comms(1, 2)
               | rule wp_split_const_if wp_split_const_if_R hoare_vcg_all_liftE_R
                      hoare_vcg_conj_elimE hoare_vcg_const_imp_liftE_R hoare_vcg_conj_liftE_R
               | (wp check_cap_inv2[where Q="\<lambda>_ s. t \<noteq> idle_thread s"]
                     out_invs_trivial case_option_wpE cap_delete_deletes
                     cap_delete_valid_cap cap_insert_valid_cap out_cte_at
                     cap_insert_cte_at cap_delete_cte_at out_valid_cap out_tcb_valid
                     hoare_vcg_const_imp_liftE_R hoare_vcg_all_liftE_R
                     thread_set_tcb_ipc_buffer_cap_cleared_invs
                     thread_set_invs_trivial[OF ball_tcb_cap_casesI]
                     hoare_vcg_all_lift thread_set_valid_cap out_emptyable
                     check_cap_inv [where P="valid_cap c" for c]
                     check_cap_inv [where P="tcb_cap_valid c p" for c p]
                     check_cap_inv[where P="cte_at p0" for p0]
                     check_cap_inv[where P="tcb_at p0" for p0]
                     thread_set_cte_at thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
                     checked_insert_no_cap_to
                     thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
                     out_no_cap_to_trivial[OF ball_tcb_cap_casesI] thread_set_ipc_tcb_cap_valid
                     check_cap_inv2[where Q="\<lambda>_. P"] cap_delete_P cap_insert_P
                     thread_set_P thread_set_P' set_mcpriority_P set_mcpriority_idle_thread
                     reschedule_required_P dxo_wp_weak hoare_weak_lift_imp)
               | simp add: ran_tcb_cap_cases dom_tcb_cap_cases[simplified] emptyable_def
               | wpc
               | strengthen use_no_cap_to_obj_asid_strg[simplified conj_comms]
                            tcb_cap_always_valid_strg[where p="tcb_cnode_index 0"]
                            tcb_cap_always_valid_strg[where p="tcb_cnode_index (Suc 0)"])+) (*slow*)
     apply (unfold option_update_thread_def)
     apply (wp itr_wps thread_set_P thread_set_P'
            | simp add: emptyable_def | wpc)+ (*also slow*)
  apply clarsimp
  by (clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified]
                     is_cap_simps is_valid_vtable_root_def2
                     is_cnode_or_valid_arch_def tcb_cap_valid_def
                     tcb_at_st_tcb_at[symmetric] invs_valid_objs
                     cap_asid_def vs_cap_ref_def
                     clas_no_asid cli_no_irqs no_cap_to_idle_thread
                     valid_ipc_buffer_cap_is_nondevice_page_cap
              split: option.split_asm)

lemma tc_reads_respects_f[Tcb_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  and tc[simp]: "ti = ThreadControl x41 x42 x43 x44 x45 x46 x47 x48"
  notes validE_valid[wp del] hoare_weak_lift_imp [wp]
  shows
    "reads_respects_f aag l
       (silc_inv aag st and only_timer_irq_inv irq st' and einvs and simple_sched_action
                        and pas_refined aag and pas_cur_domain aag and tcb_inv_wf ti
                        and is_subject aag \<circ> cur_thread
                        and K (authorised_tcb_inv aag ti \<and> authorised_tcb_inv_extra aag ti))
       (invoke_tcb ti)"
  apply (simp add: split_def cong: option.case_cong)
  apply (wpsimp wp: set_priority_reads_respects[THEN reads_respects_f[where  st=st and Q=\<top>]])
                    apply (wpsimp wp: hoare_vcg_const_imp_liftE_R simp: when_def | wpc)+
                    apply (rule conjI)
                     apply ((wpsimp wp: reschedule_required_reads_respects_f)+)[4]
                 apply ((wp reads_respects_f[OF cap_insert_reads_respects, where st=st]
                           reads_respects_f[OF thread_set_reads_respects, where st=st and Q="\<top>"]
                           set_priority_reads_respects[THEN
                                               reads_respects_f[where aag=aag and st=st and Q=\<top>]]
                           set_mcpriority_reads_respects[THEN
                                               reads_respects_f[where aag=aag and st=st and Q=\<top>]]
                           check_cap_inv[OF check_cap_inv[OF cap_insert_valid_list]]
                           check_cap_inv[OF check_cap_inv[OF cap_insert_valid_sched]]
                           check_cap_inv[OF check_cap_inv[OF cap_insert_schedact]]
                           check_cap_inv[OF check_cap_inv[OF cap_insert_cur_domain]]
                           check_cap_inv[OF check_cap_inv[OF cap_insert_ct]]
                           get_thread_state_rev[THEN
                                               reads_respects_f[where aag=aag and st=st and Q=\<top>]]
                           hoare_vcg_all_liftE_R hoare_vcg_all_lift
                           cap_delete_reads_respects[where st=st] checked_insert_pas_refined
                           thread_set_pas_refined
                           reads_respects_f[OF checked_insert_reads_respects, where st=st]
                           checked_cap_insert_silc_inv[where st=st]
                           cap_delete_silc_inv_not_transferable[where st=st]
                           checked_cap_insert_only_timer_irq_inv[where st=st' and irq=irq]
                           cap_delete_only_timer_irq_inv[where st=st' and irq=irq]
                           set_priority_only_timer_irq_inv[where st=st' and irq=irq]
                           set_mcpriority_only_timer_irq_inv[where st=st' and irq=irq]
                           cap_delete_deletes cap_delete_valid_cap cap_delete_cte_at
                           cap_delete_pas_refined' itr_wps(12) itr_wps(14) cap_insert_cte_at
                           checked_insert_no_cap_to hoare_vcg_const_imp_liftE_R hoare_vcg_conj_lift
                           as_user_reads_respects_f thread_set_mdb cap_delete_invs
                           thread_set_valid_arch_state
                      | wpc
                      | simp add: emptyable_def tcb_cap_cases_def tcb_cap_valid_def
                                  tcb_at_st_tcb_at when_def
                      | strengthen use_no_cap_to_obj_asid_strg invs_mdb
                      | solves auto)+)[7]
          apply ((simp add: conj_comms, strengthen imp_consequent[where Q="x = None" for x]
                                      , simp cong: conj_cong)
                 | wp reads_respects_f[OF cap_insert_reads_respects, where st=st]
                      reads_respects_f[OF thread_set_reads_respects, where st=st and Q="\<top>"]
                      set_priority_reads_respects[THEN reads_respects_f[where st=st and Q=\<top>]]
                      set_mcpriority_reads_respects[THEN reads_respects_f[where st=st and Q=\<top>]]
                      check_cap_inv[OF check_cap_inv[OF cap_insert_valid_list]]
                      check_cap_inv[OF check_cap_inv[OF cap_insert_valid_sched]]
                      check_cap_inv[OF check_cap_inv[OF cap_insert_schedact]]
                      check_cap_inv[OF check_cap_inv[OF cap_insert_cur_domain]]
                      check_cap_inv[OF check_cap_inv[OF cap_insert_ct]]
                      get_thread_state_rev[THEN reads_respects_f[where st=st and Q=\<top>]]
                      hoare_vcg_all_liftE_R hoare_vcg_all_lift
                      cap_delete_reads_respects[where st=st] checked_insert_pas_refined
                      thread_set_pas_refined reads_respects_f[OF checked_insert_reads_respects]
                      checked_cap_insert_silc_inv[where st=st]
                      cap_delete_silc_inv_not_transferable[where st=st]
                      checked_cap_insert_only_timer_irq_inv[where st=st' and irq=irq]
                      cap_delete_only_timer_irq_inv[where st=st' and irq=irq]
                      set_priority_only_timer_irq_inv[where st=st' and irq=irq]
                      set_mcpriority_only_timer_irq_inv[where st=st' and irq=irq]
                      cap_delete_deletes cap_delete_valid_cap cap_delete_cte_at
                      cap_delete_pas_refined' itr_wps(12) itr_wps(14) cap_insert_cte_at
                      checked_insert_no_cap_to hoare_vcg_const_imp_liftE_R
                      as_user_reads_respects_f cap_delete_invs
                 | wpc
                 | simp add: emptyable_def tcb_cap_cases_def tcb_cap_valid_def when_def st_tcb_at_triv
                 | strengthen use_no_cap_to_obj_asid_strg invs_mdb
                 | wp (once) hoare_drop_imp)+
    apply (simp add: option_update_thread_def tcb_cap_cases_def
           | wp hoare_weak_lift_imp hoare_weak_lift_imp_conj thread_set_pas_refined
                reads_respects_f[OF thread_set_reads_respects, where st=st and Q="\<top>"]
                thread_set_valid_arch_state
           | wpc)+
   apply (wp hoare_vcg_all_lift thread_set_tcb_fault_handler_update_invs
             thread_set_tcb_fault_handler_update_silc_inv
             thread_set_not_state_valid_sched
             thread_set_pas_refined thread_set_emptyable thread_set_valid_cap
             thread_set_cte_at thread_set_no_cap_to_trivial
             thread_set_tcb_fault_handler_update_only_timer_irq_inv
             thread_set_valid_arch_state
          | simp add: tcb_cap_cases_def | wpc | wp (once) hoare_drop_imp)+
  apply (clarsimp simp: authorised_tcb_inv_def authorised_tcb_inv_extra_def emptyable_def)
  apply (clarsimp cong: conj_cong)
  apply (intro conjI impI allI)
  (* slow *)
 by (clarsimp simp: is_cap_simps is_cnode_or_valid_arch_def is_valid_vtable_root_def
                    det_setRegister option.disc_eq_case[symmetric]
             split: cap.splits arch_cap.splits option.split pt_type.splits)+

crunch lazy_fpu_restore
  for cdt[wp]: "\<lambda>s. P (cdt s)"
  and is_original_cap[wp]: "\<lambda>s. P (is_original_cap s)"
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and asid_pools_of[wp]: "\<lambda>s. P (asid_pools_of s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and numlistregs[wp]: "\<lambda>s. P (numlistregs s)"
  and vcpu_state[wp]: "\<lambda>s. P (vcpu_state (machine_state s))"
  and underlying_memory[wp]: "\<lambda>s. P (underlying_memory (machine_state s))"
  and device_state[wp]: "\<lambda>s. P (device_state (machine_state s))"
  (wp: dmo_wp crunch_wps ignore: arch_thread_set)

lemma equiv_but_for_labels_guard_imp:
  "\<lbrakk> equiv_but_for_labels aag L' st s; L' \<subseteq> L \<rbrakk>
     \<Longrightarrow> equiv_but_for_labels aag L st s"
  by (auto simp: equiv_but_for_labels_def elim!: states_equiv_for_guard_imp)

definition is_subject_cur_fpu_2 where
  "is_subject_cur_fpu_2 aag cf \<equiv> \<forall>ptr. cf = Some ptr \<longrightarrow> is_subject aag ptr"

locale_abbrev is_subject_cur_fpu where
  "is_subject_cur_fpu aag \<equiv> \<lambda>s. is_subject_cur_fpu_2 aag (arm_current_fpu_owner (arch_state s))"

lemmas is_subject_cur_fpu_def = is_subject_cur_fpu_2_def

lemma dmo_enableFpu_reads_respects[wp]:
  "reads_respects aag l \<top> (do_machine_op enableFpu)"
  unfolding enableFpu_def dmo_distr
  apply wpsimp
     apply (rule use_spec_ev)
     apply (wpsimp wp: do_machine_op_reads_respects modify_ev)
        apply (clarsimp simp: equiv_for_def)
    apply (wpsimp wp: dmo_mol_reads_respects)+
  done

lemma dmo_disableFpu_reads_respects[wp]:
  "reads_respects aag l \<top> (do_machine_op disableFpu)"
  unfolding disableFpu_def dmo_distr
  apply wpsimp
     apply (rule use_spec_ev)
     apply (wpsimp wp: do_machine_op_reads_respects modify_ev)
        apply (clarsimp simp: equiv_for_def)
    apply (wpsimp wp: dmo_mol_reads_respects)+
  done

(* FIXME AARCH64 IF: consolidate cur_fpu_of and is_arch_cur_fpu *)
lemma equiv_kheap_equiv_cur_fpu_of:
  "\<lbrakk> equiv_for P kheap s s'; P t; valid_cur_fpu s; valid_cur_fpu s' \<rbrakk>
     \<Longrightarrow> cur_fpu_of s t = cur_fpu_of s' t"
  by (clarsimp simp: valid_cur_fpu_def equiv_for_def is_tcb_cur_fpu_def obj_at_def)

lemma lazy_fpu_restore_reads_respects:
  "reads_respects aag l (valid_cur_fpu and K (is_subject aag t)) (lazy_fpu_restore t)"
  unfolding lazy_fpu_restore_def
  apply (subst gets_comp)
  apply (case_tac "aag_can_read_or_affect aag l t")
   apply (wpsimp simp: lazy_fpu_restore_def wp: thread_get_reads_respects gets_ev'')
       apply (rename_tac s s')
       apply (prop_tac "valid_cur_fpu s")
        apply assumption
       apply (prop_tac "valid_cur_fpu s'")
        apply assumption
       apply clarsimp
       apply (prop_tac "equiv_for (aag_can_read_or_affect aag l) kheap s s'")
        apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_for_disj)
       apply (clarsimp simp: equiv_kheap_equiv_cur_fpu_of)
      apply wpsimp
     apply (wpsimp wp: thread_get_reads_respects)
    apply (wpsimp wp: thread_get_wp')
   apply clarsimp
  apply (rule gen_asm_ev)
  apply clarsimp
  done

lemma arch_post_set_flags_reads_respects_f[Tcb_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_f aag l (silc_inv aag st and valid_cur_fpu and K (is_subject aag t)) (arch_post_set_flags t flags)"
  unfolding arch_post_set_flags_def
  apply (rule equiv_valid_guard_imp)
   apply (wpsimp wp: when_ev reads_respects_f[OF fpu_release_reads_respects]
                     reads_respects_f[OF lazy_fpu_restore_reads_respects])
  apply fastforce
  done

lemma arch_tcb_context_get_cur_fpu_update[simp]:
  "arch_tcb_context_get (tcb_arch tcb\<lparr>tcb_cur_fpu := fpu\<rparr>) = arch_tcb_context_get (tcb_arch tcb)"
  by (simp add: arch_tcb_context_get_def)

lemma globals_equiv_fpu_owner_update[simp]:
  "globals_equiv st (s\<lparr>arch_state := arch_state s\<lparr>arm_current_fpu_owner := t\<rparr>\<rparr>)  =
   globals_equiv st s"
  by (auto simp add: globals_equiv_def idle_equiv_def)

lemma set_arm_current_fpu_owner_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   set_arm_current_fpu_owner t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding set_arm_current_fpu_owner_def arch_thread_set_is_thread_set
  by (wpsimp wp: thread_set_globals_equiv thread_set_valid_arch_state hoare_vcg_all_lift hoare_drop_imps
       | fastforce simp: ran_tcb_cap_cases)+

lemma dmo_enableFpu_globals_equiv[wp]:
  "do_machine_op enableFpu \<lbrace>globals_equiv st\<rbrace>"
  by (wpsimp wp: bind_wp_skip
           simp: globals_equiv_def idle_equiv_def enableFpu_def dmo_distr dmo_modify_distr)

lemma dmo_disableFpu_globals_equiv[wp]:
  "do_machine_op disableFpu \<lbrace>globals_equiv st\<rbrace>"
  apply (clarsimp simp: disableFpu_def dmo_distr dmo_modify_distr)
  apply (rule bind_wp_skip)
   apply (unfold globals_equiv_def arch_globals_equiv_def idle_equiv_def enableFpu_def)[1]
   apply wpsimp
  apply wpsimp
  done

lemma dmo_state_assert_inv[wp]:
  "do_machine_op (state_assert f) \<lbrace>P\<rbrace>"
  unfolding state_assert_def
  by (wpsimp wp: dmo_wp)

lemma dmo_readFpuState_globals_equiv[wp]:
  "do_machine_op readFpuState \<lbrace>globals_equiv st\<rbrace>"
  by (wpsimp simp: readFpuState_def dmo_distr dmo_modify_distr)

lemma dmo_writeFpuState_globals_equiv[wp]:
  "do_machine_op (writeFpuState fpustate) \<lbrace>globals_equiv st\<rbrace>"
  apply (clarsimp simp: writeFpuState_def dmo_distr dmo_modify_distr)
  apply wpsimp
  apply (clarsimp simp: globals_equiv_def idle_equiv_def)
  done

lemma as_user_getRestart_inv[wp]:
  "as_user t getFPUState \<lbrace>P\<rbrace>"
  unfolding getFPUState_def
  by (wpsimp wp: as_user_inv)

lemma load_fpu_state_globals_equiv[wp]:
  "load_fpu_state t \<lbrace>globals_equiv st\<rbrace>"
  unfolding load_fpu_state_def
  by wpsimp

lemma save_fpu_state_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   save_fpu_state t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding save_fpu_state_def
  by wpsimp

crunch load_fpu_state, save_fpu_state
  for valid_arch_state[wp]: "valid_arch_state"

lemma switch_local_fpu_owner_globals_equiv:
  "\<lbrace>globals_equiv st and invs\<rbrace>
   switch_local_fpu_owner new_owner
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding switch_local_fpu_owner_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_weak_lift_imp)
  apply (fastforce simp: invs_def valid_state_def valid_pspace_def valid_cur_fpu_def
                         is_tcb_cur_fpu_def live_def arch_tcb_live_def
                   dest: idle_no_ex_cap if_live_then_nonz_capD)
  done

lemma lazy_fpu_restore_globals_equiv:
  "\<lbrace>globals_equiv st and invs\<rbrace>
   lazy_fpu_restore t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding lazy_fpu_restore_def
  by (wpsimp wp: switch_local_fpu_owner_globals_equiv hoare_drop_imps)

crunch arch_post_set_flags
  for globals_equiv[Tcb_IF_assms]: "globals_equiv st"
  (simp: crunch_simps)

end


global_interpretation Tcb_IF_2?: Tcb_IF_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Tcb_IF_assms)?)
qed

end
