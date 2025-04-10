(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Tcb_IF
imports ArchIpc_IF
begin

section "valid global objs"

crunch cancel_ipc, restart, deleting_irq_handler, suspend, cap_swap_for_delete
  for valid_global_objs[wp]: "valid_global_objs"
  (wp: mapM_x_wp select_inv hoare_drop_imps hoare_vcg_if_lift2 dxo_wp_weak simp: unless_def)


section "globals equiv"

lemma setup_reply_master_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   setup_reply_master t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding setup_reply_master_def
  apply (wp set_cap_globals_equiv'' set_original_globals_equiv get_cap_wp)
  apply clarsimp
  done

lemma restart_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   restart t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding restart_def
  by (wpsimp wp: dxo_wp_weak set_thread_state_globals_equiv setup_reply_master_globals_equiv gts_wp)

lemma globals_equiv_ioc_update[simp]:
  "globals_equiv st (is_original_cap_update f s) = globals_equiv st s"
  by (simp add: globals_equiv_def idle_equiv_def)

lemma cap_swap_for_delete_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   cap_swap_for_delete a b
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding cap_swap_for_delete_def cap_swap_def set_original_def
  by (wp modify_wp set_cdt_globals_equiv set_cap_globals_equiv'' dxo_wp_weak | simp)+

lemma rec_del_preservation2':
  assumes finalise_cap_P: "\<And>cap final. \<lbrace>R cap and P\<rbrace> finalise_cap cap final \<lbrace>\<lambda>_. P\<rbrace>"
  assumes set_cap_P: "\<And>cap b. \<lbrace>Q and P\<rbrace> set_cap cap b \<lbrace>\<lambda>_. P\<rbrace>"
  assumes set_cap_Q: "\<And>cap b. \<lbrace>Q\<rbrace> set_cap cap b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes empty_slot_P: "\<And>slot free. \<lbrace>Q and P\<rbrace> empty_slot slot free \<lbrace>\<lambda>_. P\<rbrace>"
  assumes empty_slot_Q: "\<And>slot free. \<lbrace>Q\<rbrace> empty_slot slot free \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes cap_swap_for_delete_Q: "\<And>a b. \<lbrace>Q\<rbrace> cap_swap_for_delete a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes cap_swap_for_delete_P: "\<And>a b. \<lbrace>Q and P\<rbrace> cap_swap_for_delete a b \<lbrace>\<lambda>_. P\<rbrace>"
  assumes preemption_point_Q: "\<And>a b. \<lbrace>Q\<rbrace> preemption_point \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes preemption_point_P: "\<And>a b. \<lbrace>Q and P\<rbrace> preemption_point \<lbrace>\<lambda>_. P\<rbrace>"
  assumes invs_Q: "\<And>s. invs s \<Longrightarrow> Q s"
  assumes invs_R: "\<And>s slot cap. invs s \<Longrightarrow> caps_of_state s slot = Some cap \<Longrightarrow> R cap s"
  shows "s \<turnstile> \<lbrace>\<lambda>s. invs s \<and> P s \<and> Q s \<and> emptyable (slot_rdcall call) s \<and> valid_rec_del_call call s\<rbrace>
             rec_del call
             \<lbrace>\<lambda>rv s :: det_state. P s \<and> Q s\<rbrace>, \<lbrace>\<lambda>rv s. P s \<and> Q s\<rbrace>"
proof (induct rule: rec_del.induct, simp_all only: rec_del_fails)
  case (1 slot exposed s)
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply (rule hoare_pre_spec_validE)
     apply (rule split_spec_bindE)
      apply (wp empty_slot_P empty_slot_Q)[1]
     apply (rule spec_strengthen_postE)
      apply (rule "1.hyps")
     apply auto
    done
next
  case (2 slot exposed s)
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply (rule hoare_pre_spec_validE)
     apply wp
         apply (wp set_cap_P set_cap_Q "2.hyps")+
          apply ((wp preemption_point_Q preemption_point_P preemption_point_inv | simp)+)[1]
         apply (simp(no_asm))
         apply (rule spec_strengthen_postE)
          apply (rule spec_valid_conj_liftE1, rule valid_validE_R, rule rec_del_invs)
          apply (rule spec_valid_conj_liftE1, rule reduce_zombie_cap_to)
          apply (rule spec_valid_conj_liftE1, rule rec_del_emptyable)
          apply (rule "2.hyps")
                apply simp
               apply (simp add: conj_comms)
              apply (wp set_cap_P set_cap_Q replace_cap_invs
                        final_cap_same_objrefs set_cap_cte_cap_wp_to
                        set_cap_cte_wp_at hoare_vcg_const_Ball_lift hoare_weak_lift_imp
                     | rule finalise_cap_not_reply_master
                     | simp add: in_monad)+
       apply (rule hoare_strengthen_post)
        apply (rule_tac Q="\<lambda>fin s. invs s \<and> cte_wp_at ((=) rv) slot s \<and> s \<turnstile> (fst fin)
                                          \<and> P s
                                          \<and> replaceable s slot (fst fin) rv
                                          \<and> emptyable slot s
                                          \<and> (\<forall>t\<in>obj_refs_ac (fst fin). halted_if_tcb t s)
                                          \<and> ex_cte_cap_wp_to (appropriate_cte_cap rv) slot s"
                     in hoare_vcg_conj_lift)
         apply (wp finalise_cap_invs[where slot=slot]
                   finalise_cap_replaceable[where sl=slot]
                   Finalise_AC_1.finalise_cap_makes_halted[where slot=slot]
                   finalise_cap_P)[1]
        apply (rule finalise_cap_cases[where slot=slot])
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       apply (frule invs_valid_global_objs)
       apply (frule invs_Q)
       apply (erule disjE)
        apply clarsimp
       apply (clarsimp simp: is_cap_simps cap_auth_conferred_def clas_no_asid aag_cap_auth_def
                             pas_refined_all_auth_is_owns cli_no_irqs gen_obj_refs_eq)
       apply (drule appropriate_Zombie[symmetric, THEN trans, symmetric])
       apply clarsimp
       apply (erule_tac s = "{r}" in subst)
       apply simp
      apply (simp add: is_final_cap_def)
      apply wp
     apply (wp get_cap_wp)
    apply (clarsimp simp: cte_wp_at_caps_of_state conj_comms)
    apply (frule (1) caps_of_state_valid)
    apply (clarsimp simp: conj_comms invs_def valid_state_def valid_pspace_def invs_R)
    apply (frule if_unsafe_then_capD [OF caps_of_state_cteD],clarsimp+)
    done
next
  case (3 ptr bits n slot s)
  show ?case
    apply (simp add: spec_validE_def)
    apply (rule hoare_pre, wp cap_swap_for_delete_P cap_swap_for_delete_Q)
    apply (clarsimp)
    done
next
  case (4 ptr bits n slot s)
  show ?case
    apply (subst rec_del.simps)
    apply (rule hoare_pre_spec_validE)
     apply (rule split_spec_bindE)
      apply (rule split_spec_bindE[rotated])
       apply (rule "4.hyps", assumption+)
      apply (wpsimp wp: set_cap_P set_cap_Q get_cap_wp)
     apply simp
     apply wp
    apply (clarsimp simp add: zombie_is_cap_toE)
    apply (clarsimp simp: cte_wp_at_caps_of_state zombie_ptr_emptyable)
    done
qed

lemma rec_del_preservation2:
  assumes "\<And>cap final. \<lbrace>R cap and P\<rbrace> finalise_cap cap final \<lbrace>\<lambda>_. P\<rbrace>"
  assumes "\<And>cap b. \<lbrace>Q and P\<rbrace> set_cap cap b \<lbrace>\<lambda>_. P\<rbrace>"
  assumes "\<And>cap b. set_cap cap b \<lbrace>Q\<rbrace>"
  assumes "\<And>slot free. \<lbrace>Q and P\<rbrace> empty_slot slot free \<lbrace>\<lambda>_. P\<rbrace>"
  assumes "\<And>slot free. empty_slot slot free \<lbrace>Q\<rbrace>"
  assumes "\<And>a b. cap_swap_for_delete a b \<lbrace>Q\<rbrace>"
  assumes "\<And>a b. \<lbrace>Q and P\<rbrace> cap_swap_for_delete a b \<lbrace>\<lambda>_. P\<rbrace>"
  assumes "\<And>s. invs s \<Longrightarrow> Q s"
  assumes "\<And>s slot cap. invs s \<Longrightarrow> caps_of_state s slot = Some cap \<Longrightarrow> R cap s"
  assumes "preemption_point \<lbrace>Q\<rbrace>"
  assumes "\<lbrace>Q and P\<rbrace> preemption_point \<lbrace>\<lambda>_. P\<rbrace>"
  shows
    "\<lbrace>\<lambda>s :: det_state. invs s \<and> P s \<and> emptyable (slot_rdcall call) s \<and> valid_rec_del_call call s\<rbrace>
     rec_del call
     \<lbrace>\<lambda>r. P\<rbrace>"
  apply (insert assms)
  apply (rule_tac P'="\<lambda>s. invs s \<and> P s \<and> Q s
                                \<and> emptyable (slot_rdcall call) s
                                \<and> valid_rec_del_call call s" in hoare_pre_imp)
   apply simp
  apply (rule_tac Q'="\<lambda>rv s. P s \<and> Q s" in hoare_strengthen_post)
   apply (rule validE_valid)
   apply (rule use_spec)
   apply (rule rec_del_preservation2' [where R=R],simp+)
  done


locale Tcb_IF_1 =
  fixes aag :: "'a subject_label PAS"
  assumes valid_arch_caps_vs_lookup:
    "valid_arch_caps s \<Longrightarrow> valid_vs_lookup s"
  and no_cap_to_idle_thread':
    "valid_global_refs s \<Longrightarrow> \<not> ex_nonz_cap_to (idle_thread s) s"
  and no_cap_to_idle_thread'':
    "valid_global_refs s \<Longrightarrow> caps_of_state s ref \<noteq> Some (ThreadCap (idle_thread s))"
  and arch_post_modify_registers_globals_equiv[wp]:
    "arch_post_modify_registers cur t \<lbrace>globals_equiv s\<rbrace>"
  and arch_post_modify_registers_valid_arch_state[wp]:
    "arch_post_modify_registers cur t \<lbrace>\<lambda>s :: det_state. valid_arch_state s\<rbrace>"
  and arch_post_modify_registers_reads_respects_f[wp]:
    "reads_respects_f aag l \<top> (arch_post_modify_registers cur t)"
  and arch_get_sanitise_register_info_reads_respects_f[wp]:
    "reads_respects_f aag l \<top> (arch_get_sanitise_register_info t)"
begin

crunch cap_swap_for_delete
  for valid_arch_state[wp]: valid_arch_state
  (wp: dxo_wp_weak simp: crunch_simps)

lemma rec_del_globals_equiv:
  "\<lbrace>\<lambda>s. invs s \<and> globals_equiv st s \<and> emptyable (slot_rdcall call) s \<and> valid_rec_del_call call s\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (wpsimp wp: finalise_cap_globals_equiv
                    rec_del_preservation2[where Q="valid_arch_state"
                                            and R="\<lambda>cap s. invs s \<and> valid_cap cap s
                                                      \<and> (\<forall>p. cap = ThreadCap p \<longrightarrow> p \<noteq> idle_thread s)"])
            apply (wp set_cap_globals_equiv'')
            apply simp
           apply (wp empty_slot_globals_equiv)+
          apply simp
         apply (wp)+
       apply simp
      apply fastforce
     apply (fastforce simp: invs_def valid_state_def valid_arch_caps_vs_lookup
                            valid_pspace_def no_cap_to_idle_thread''
                      dest: caps_of_state_valid)
    apply (wp preemption_point_inv | simp)+
  done

lemma cap_delete_globals_equiv:
  "\<lbrace>globals_equiv st and invs and emptyable a\<rbrace>
   cap_delete a
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding cap_delete_def
  apply (wp rec_del_globals_equiv)
  apply simp
  done

lemma no_cap_to_idle_thread:
   "invs (s :: det_state) \<Longrightarrow> \<not> ex_nonz_cap_to (idle_thread s) s"
  apply (rule no_cap_to_idle_thread')
  apply clarsimp
  done

end


crunch set_mcpriority
  for idle_thread_inv[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: syscall_valid crunch_wps rec_del_preservation cap_revoke_preservation)

crunch restart
  for idle_thread'[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: dxo_wp_weak)

lemma bind_notification_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   bind_notification t ntfnptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding bind_notification_def
  by (wp set_bound_notification_globals_equiv set_notification_globals_equiv | wpc | simp)+

lemma invoke_tcb_NotificationControl_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   invoke_tcb (NotificationControl t ntfn)
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (case_tac ntfn, simp_all)
  apply (wp unbind_notification_globals_equiv bind_notification_globals_equiv)+
  done

crunch set_mcpriority, set_priority
  for globals_equiv: "globals_equiv st"

lemma dxo_globals_equiv[wp]:
  "do_extended_op eop \<lbrace>globals_equiv st\<rbrace>"
  by (simp | wp dxo_wp_weak)+


definition authorised_tcb_inv_extra where
  "authorised_tcb_inv_extra aag ti \<equiv>
    (case ti of ThreadControl _ slot _ _ _ _ _ _ \<Rightarrow> is_subject aag (fst slot) | _ \<Rightarrow> True)"


locale Tcb_IF_2 = Tcb_IF_1 +
  assumes invoke_tcb_thread_preservation:
    "\<lbrakk> \<And>slot. \<lbrace>invs and P and emptyable slot\<rbrace> cap_delete slot \<lbrace>\<lambda>_.P\<rbrace>;
       \<And>new_cap src dest. \<lbrace>invs and P\<rbrace> cap_insert new_cap src dest \<lbrace>\<lambda>_.P\<rbrace>;
       \<And>f ptr. \<lbrace>invs and P\<rbrace> thread_set (tcb_ipc_buffer_update f) ptr \<lbrace>\<lambda>_.P\<rbrace>;
       \<And>f ptr. \<lbrace>invs and P\<rbrace> thread_set (tcb_fault_handler_update f) ptr \<lbrace>\<lambda>_.P\<rbrace>;
       \<And>mcp ptr. \<lbrace>invs and P\<rbrace> set_mcpriority ptr mcp \<lbrace>\<lambda>_.P\<rbrace>;
       \<And>prio ptr. \<lbrace>invs and P\<rbrace> set_priority ptr prio \<lbrace>\<lambda>_.P\<rbrace>;
       reschedule_required \<lbrace>P\<rbrace>;
       \<And>f s. P (trans_state f s) = P s \<rbrakk>
       \<Longrightarrow> \<lbrace>P and invs and tcb_inv_wf (ThreadControl t sl ep mcp prio croot vroot buf)\<rbrace>
           invoke_tcb (ThreadControl t sl ep mcp prio croot vroot buf)
           \<lbrace>\<lambda>rv s :: det_state. P s\<rbrace>"
  and tc_reads_respects_f:
    "\<lbrakk> pas_domains_distinct aag; ti = ThreadControl x41 x42 x43 x44 x45 x46 x47 x48 \<rbrakk>
       \<Longrightarrow> reads_respects_f aag l
             (silc_inv aag st and only_timer_irq_inv irq st' and einvs and simple_sched_action
                              and pas_refined aag and pas_cur_domain aag and tcb_inv_wf ti
                              and is_subject aag \<circ> cur_thread
                              and K (authorised_tcb_inv aag ti \<and> authorised_tcb_inv_extra aag ti))
             (invoke_tcb ti)"
  and arch_post_set_flags_globals_equiv[wp]:
    "arch_post_set_flags t flags \<lbrace>globals_equiv st\<rbrace>"
  and arch_post_set_flags_reads_respects_f:
    "reads_respects_f aag l \<top> (arch_post_set_flags t flags)"
begin

crunch suspend, restart
  for valid_arch_state[wp]: "\<lambda>s :: det_state. valid_arch_state s"
  (wp: dxo_wp_weak)

crunch set_flags
  for globals_equiv[wp]: "globals_equiv st"

lemma invoke_tcb_globals_equiv:
  "\<lbrace>invs and globals_equiv st and tcb_inv_wf ti\<rbrace>
   invoke_tcb ti
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (case_tac ti; (solves \<open>(wp mapM_x_wp' as_user_globals_equiv
                                   invoke_tcb_NotificationControl_globals_equiv
                                | simp
                                | intro conjI impI
                                | clarsimp simp: no_cap_to_idle_thread)+\<close>)?)
   apply wpsimp
       apply (rename_tac word1 word2 bool1 bool2 bool3 bool4 arch_copy_register_sets)
       apply (rule_tac Q'="\<lambda>_. valid_arch_state and globals_equiv st and
                              (\<lambda>s. word1 \<noteq> idle_thread s) and (\<lambda>s. word2 \<noteq> idle_thread s)"
                    in hoare_strengthen_post)
        apply (wpsimp wp: mapM_x_wp' as_user_globals_equiv invoke_tcb_NotificationControl_globals_equiv
                          weak_if_wp')+
   apply (intro conjI impI; clarsimp simp: no_cap_to_idle_thread)+
  apply (simp del: invoke_tcb.simps tcb_inv_wf.simps)
  apply (wp invoke_tcb_thread_preservation cap_delete_globals_equiv
            cap_insert_globals_equiv'' thread_set_globals_equiv set_mcpriority_globals_equiv
            set_priority_globals_equiv
         | fastforce)+
  done

end


section "reads respects"

lemma setup_reply_master_reads_respects:
  "reads_respects aag l (K (is_subject aag t)) (setup_reply_master t)"
  apply (simp add: setup_reply_master_def when_def)
  apply (wp set_cap_reads_respects set_original_reads_respects get_cap_rev | simp)+
   apply (wp | wp (once) hoare_drop_imps)+
  apply clarsimp
  done

lemmas gets_cur_thread_respects_f =
  gets_cur_thread_ev[THEN reads_respects_f[where Q=\<top>],simplified,wp]

lemma restart_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects_f aag l (silc_inv aag st and pas_refined aag and pas_cur_domain aag and invs
                                             and tcb_at t and (\<lambda>s. is_subject aag (cur_thread s))
                                             and K (is_subject aag t)) (restart t)"
  apply (rule gen_asm_ev | elim conjE)+
  apply (simp add: restart_def when_def)
  apply (wp reads_respects_f[OF set_thread_state_reads_respects, where Q="\<top>"]
            reads_respects_f[OF setup_reply_master_reads_respects setup_reply_master_silc_inv]
            gets_cur_thread_ev set_thread_state_pas_refined setup_reply_master_pas_refined
            reads_respects_f[OF possible_switch_to_reads_respects, where Q="\<top>"]
            reads_respects_f[OF tcb_sched_action_reads_respects, where Q="\<top>"]
            cancel_ipc_reads_respects_f setup_reply_master_silc_inv cancel_ipc_silc_inv
         | simp
         | strengthen invs_mdb)+
    apply (simp add: get_thread_state_def thread_get_def)
    apply wp
   apply (wp hoare_drop_imps)
  apply clarsimp
  apply (rule requiv_get_tcb_eq | rule conjI | assumption | clarsimp simp: reads_equiv_f_def)+
  done

lemma det_zipWithM:
  assumes "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set ys \<rbrakk> \<Longrightarrow> det (f x y)"
  shows "det (zipWithM f xs ys)"
  apply (simp add: zipWithM_mapM)
  apply (rule det_mapM[OF _ subset_refl])
  apply (simp add: split_def)
  apply (case_tac x)
  apply (clarsimp)
  apply (erule in_set_zipE)
  apply (erule (1) assms)
  done

lemma checked_insert_reads_respects:
  "reads_respects aag l
     (K (is_subject aag (fst b) \<and> is_subject aag (fst d) \<and> is_subject aag (fst e)))
     (check_cap_at a b (check_cap_at c d (cap_insert a b e)))"
  apply (rule equiv_valid_guard_imp)
   apply (simp add: check_cap_at_def)
   apply (wp when_ev cap_insert_reads_respects get_cap_wp get_cap_rev | simp)+
  done

lemmas as_user_reads_respects_f =
  reads_respects_f[OF as_user_reads_respects, where Q="\<top>", simplified, OF as_user_silc_inv]

declare gts_st_tcb_at[wp del]

lemma thread_set_priority_pas_refined:
  "thread_set (tcb_priority_update f) thread \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp wp: thread_set_pas_refined)

lemma set_priority_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag (l :: 'a subject_label)
           (pas_refined aag and K (is_subject aag word) and pas_cur_domain aag
                            and (\<lambda>s. is_subject aag (cur_thread s)))
           (set_priority word prio)"
  apply (simp add: set_priority_def thread_set_priority_def)
  apply (wpsimp wp: when_ev possible_switch_to_reads_respects get_thread_state_rev hoare_drop_imps
                    thread_set_reads_respects thread_set_priority_pas_refined
                    tcb_sched_action_reads_respects)
  apply force
  done

lemma set_mcpriority_reads_respects:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag (l :: 'a subject_label) \<top> (set_mcpriority x y)"
  unfolding set_mcpriority_def
  by (rule thread_set_reads_respects[OF domains_distinct])

lemma checked_cap_insert_only_timer_irq_inv:
  "check_cap_at a b (check_cap_at c d (cap_insert a b e)) \<lbrace>only_timer_irq_inv irq (st :: det_state)\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres checked_cap_insert_domain_sep_inv | clarsimp | simp)+
  done

lemma cap_delete_only_timer_irq_inv:
  "cap_delete slot \<lbrace>only_timer_irq_inv irq (st :: det_state)\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres cap_delete_irq_masks | force)+
  done

crunch set_priority
  for machine_state[wp]: "\<lambda>s. P (machine_state s)"

lemma set_priority_only_timer_irq_inv:
  "set_priority t prio \<lbrace>only_timer_irq_inv irq (st :: det_state)\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres | force)+
  done

lemma set_mcpriority_only_timer_irq_inv:
  "set_mcpriority t prio \<lbrace>only_timer_irq_inv irq (st :: det_state)\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres | force)+
  done

lemma thread_set_tcb_fault_handler_update_only_timer_irq_inv:
  "thread_set (tcb_fault_handler_update blah) t \<lbrace>only_timer_irq_inv irq (st :: det_state)\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres | force)+
  done

lemma bind_notification_reads_respects:
  "reads_respects aag l
     (pas_refined aag and invs and
      K (is_subject aag t \<and>
         (\<forall>auth\<in>{Receive, Reset}. (pasSubject aag, auth, pasObjectAbs aag nptr) \<in> pasPolicy aag)))
     (bind_notification t nptr)"
  apply (clarsimp simp: bind_notification_def)
  apply (wp set_bound_notification_owned_reads_respects set_simple_ko_reads_respects
            get_simple_ko_reads_respects get_bound_notification_reads_respects
            gbn_wp[unfolded get_bound_notification_def, simplified]
         | wpc
         | simp add: get_bound_notification_def)+
  apply (clarsimp dest!: reads_ep)
  done

lemmas thread_get_reads_respects_f =
  reads_respects_f[OF thread_get_reads_respects, where Q="\<top>", simplified, OF thread_get_inv]

lemmas reschedule_required_reads_respects_f =
  reads_respects_f[OF reschedule_required_reads_respects, where Q="\<top>", simplified,
                   OF _ reschedule_required_silc_inv]


context Tcb_IF_2 begin

lemma thread_set_tcb_flags_update_silc_inv[wp]:
  "thread_set (tcb_flags_update f) t \<lbrace>silc_inv aag st\<rbrace>"
  by (rule thread_set_silc_inv; simp add: tcb_cap_cases_def)

lemma set_flags_reads_respects_f:
  assumes "pas_domains_distinct aag"
  shows "reads_respects_f aag l (silc_inv aag st) (set_flags t flags)"
  unfolding set_flags_def
  by (wpsimp wp: reads_respects_f thread_set_reads_respects equiv_valid_guard_imp | simp add: assms)+

lemma invoke_tcb_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes validE_valid[wp del] hoare_weak_lift_imp [wp]
  shows
    "reads_respects_f aag l
       (silc_inv aag st and only_timer_irq_inv irq st' and einvs
                        and simple_sched_action and pas_refined aag and pas_cur_domain aag
                        and tcb_inv_wf ti and is_subject aag \<circ> cur_thread
                        and K (authorised_tcb_inv aag ti \<and> authorised_tcb_inv_extra aag ti))
       (invoke_tcb ti)"
  including classic_wp_pre
  apply (case_tac ti)
          \<comment> \<open>WriteRegisters\<close>
          apply (strengthen invs_mdb
                 | wpsimp wp: when_ev restart_reads_respects_f reschedule_required_reads_respects_f
                              as_user_reads_respects_f restart_silc_inv restart_pas_refined hoare_vcg_if_lift)+
             apply (rule hoare_strengthen_post[where Q'="\<lambda>_ s. \<forall>rv. Q rv s" and Q=Q for Q, rotated])
              apply (rename_tac rv s)
              apply (erule_tac x=rv in allE, assumption)
             apply wpsimp+
          apply (solves \<open>auto intro!: det_zipWithM
                               simp: det_setRegister det_getRestartPC det_setNextPC
                                     authorised_tcb_inv_def reads_equiv_f_def\<close>)
         apply (wp as_user_reads_respects_f suspend_silc_inv when_ev  suspend_reads_respects_f
                | simp | elim conjE, assumption)+
         apply (solves \<open>auto simp: authorised_tcb_inv_def  det_getRegister reads_equiv_f_def
                          intro!: det_mapM[OF _ subset_refl]\<close>)
        apply (wp when_ev mapM_x_ev'' reschedule_required_reads_respects_f[where st=st]
                  as_user_reads_respects_f[where st=st] hoare_vcg_ball_lift
                  restart_reads_respects_f restart_silc_inv hoare_vcg_if_lift
                  suspend_reads_respects_f suspend_silc_inv hoare_drop_imp
                  restart_silc_inv restart_pas_refined
               | simp split del: if_split add: det_setRegister det_setNextPC
               | strengthen invs_mdb
               | (rule hoare_strengthen_post[where Q'="\<lambda>_. silc_inv aag st and pas_refined aag",
                                             OF mapM_x_wp', rotated], fastforce)
               | wp mapM_x_wp')+
        apply (solves \<open>auto simp: authorised_tcb_inv_def det_getRestartPC det_getRegister
                                 idle_no_ex_cap[OF invs_valid_global_refs invs_valid_objs]\<close>)
       defer
       apply ((wp suspend_reads_respects_f[where st=st] restart_reads_respects_f[where st=st]
               | simp add: authorised_tcb_inv_def )+)[2]
     \<comment> \<open>NotificationControl\<close>
     apply (rename_tac option)
     apply (case_tac option, simp_all)[1]
      apply ((wp unbind_notification_is_subj_reads_respects
                 unbind_notification_silc_inv bind_notification_reads_respects
              | clarsimp simp: authorised_tcb_inv_def
              | rule_tac Q=\<top> and st=st in reads_respects_f)+)[2]
    \<comment> \<open>SetTLSBase\<close>
    apply (wpsimp wp: when_ev reschedule_required_reads_respects_f
                      as_user_reads_respects_f hoare_drop_imps)+
    apply (auto simp: det_setRegister authorised_tcb_inv_def)[1]
   \<comment> \<open>SetFlags\<close>
   apply (wpsimp wp: set_flags_reads_respects_f thread_get_reads_respects_f
                     arch_post_set_flags_reads_respects_f)
   apply (auto simp: authorised_tcb_inv_def)[1]
  \<comment> \<open>ThreadControl\<close>
  apply (fastforce intro: tc_reads_respects_f[OF assms])
  done

lemma invoke_tcb_reads_respects_f_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "reads_respects_f_g aag l
       (silc_inv aag st and only_timer_irq_inv irq st' and pas_refined aag and pas_cur_domain aag
                        and einvs and simple_sched_action and tcb_inv_wf ti
                        and (\<lambda>s. is_subject aag (cur_thread s))
                        and K (authorised_tcb_inv aag ti \<and> authorised_tcb_inv_extra aag ti))
       (invoke_tcb ti)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_f_g)
    apply (rule invoke_tcb_reads_respects_f[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp invoke_tcb_globals_equiv | clarsimp | assumption | force)+
  done

end


lemma decode_tcb_invocation_authorised_extra:
  "\<lbrace>K (is_subject aag (fst slot))\<rbrace>
   decode_tcb_invocation label msg (ThreadCap t) slot excaps
   \<lbrace>\<lambda>rv s. authorised_tcb_inv_extra aag rv\<rbrace>, -"
  apply (simp add: authorised_tcb_inv_extra_def)
  apply (simp add: decode_tcb_invocation_def)
  apply (rule hoare_pre)
   apply (wp OR_choice_E_weak_wp
          | wpc | simp add: decode_read_registers_def
                            decode_write_registers_def
                            decode_copy_registers_def
                            decode_tcb_configure_def
                            decode_set_priority_def
                            decode_set_mcpriority_def
                            decode_set_sched_params_def
                            decode_set_ipc_buffer_def
                            decode_bind_notification_def
                            decode_unbind_notification_def
                            decode_set_tls_base_def
                            decode_set_flags_def
                            split_def decode_set_space_def
                 split del: if_split)+
  done

end
