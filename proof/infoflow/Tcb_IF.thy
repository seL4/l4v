(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Tcb_IF
imports    "Finalise_IF"

begin

context begin interpretation Arch . (*FIXME: arch_split*)

section "arm global pd"

crunch arm_global_pd[wp]: set_irq_state, suspend "\<lambda>s. P (arm_global_pd (arch_state s))"
  (wp: mapM_x_wp select_inv hoare_vcg_if_lift2 hoare_drop_imps dxo_wp_weak
   simp: unless_def
   ignore: empty_slot_ext reschedule_required)

crunch arm_global_pd[wp]: as_user, restart "\<lambda>s. P (arm_global_pd (arch_state s))" (wp: dxo_wp_weak)


section "valid global objs"

crunch valid_global_objs[wp]: deleted_irq_handler "valid_global_objs"
crunch valid_global_objs[wp]: cancel_ipc "valid_global_objs"
  (wp: mapM_x_wp select_inv hoare_drop_imps hoare_vcg_if_lift2 dxo_wp_weak
   simp: unless_def
   ignore: empty_slot_ext)
crunch valid_global_objs[wp]: restart "valid_global_objs" (wp: dxo_wp_weak)
crunch valid_global_objs: cap_swap_for_delete, deleting_irq_handler, suspend "valid_global_objs"
  (wp: dxo_wp_weak)


section "globals equiv"

(* FIXME: move *)
lemma dmo_maskInterrupt_globals_equiv[wp]:
  "invariant (do_machine_op (maskInterrupt b irq)) (globals_equiv s)"
  unfolding maskInterrupt_def
  apply(rule dmo_no_mem_globals_equiv)
   apply(wp modify_wp | simp)+
   done


lemma setup_reply_master_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm\<rbrace> setup_reply_master a \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding setup_reply_master_def
  apply (wp set_cap_globals_equiv'' set_original_globals_equiv get_cap_wp)
  apply clarsimp
done

lemma cancel_signal_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm\<rbrace> cancel_signal a b \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding cancel_signal_def
  by (wpsimp wp: set_thread_state_globals_equiv set_notification_globals_equiv
                 set_notification_valid_ko_at_arm hoare_drop_imps
           simp: crunch_simps)

crunch globals_equiv[wp]: cancel_ipc "globals_equiv st"
  (wp: mapM_x_wp select_inv hoare_drop_imps hoare_vcg_if_lift2 cancel_signal_valid_ko_at_arm
   simp: unless_def)

crunch valid_ko_at_arm[wp]: setup_reply_master "valid_ko_at_arm"

crunch globals_equiv[wp]: restart "globals_equiv st"
  (wp: cancel_ipc_valid_ko_at_arm hoare_vcg_if_lift2 dxo_wp_weak hoare_drop_imps
   ignore: reschedule_required possible_switch_to)

declare as_user_globals_equiv[wp]

lemma cap_ne_global_pd : "ex_nonz_cap_to word s \<Longrightarrow> valid_global_refs s \<Longrightarrow> word \<noteq> arm_global_pd (arch_state s)"
  unfolding ex_nonz_cap_to_def
  apply (simp only : cte_wp_at_caps_of_state zobj_refs_to_obj_refs)
  apply (elim exE conjE)
  apply (drule valid_global_refsD2,simp)
  apply (unfold global_refs_def)
  apply clarsimp
  apply (unfold cap_range_def)
  apply blast
  done

lemma globals_equiv_ioc_update[simp]: "globals_equiv st (is_original_cap_update f s) = globals_equiv st s"
  apply (simp add: globals_equiv_def idle_equiv_def)
  done




lemma cap_swap_for_delete_globals_equiv[wp]: "\<lbrace>globals_equiv st and valid_ko_at_arm\<rbrace> (cap_swap_for_delete a b) \<lbrace>\<lambda>_.(globals_equiv st )\<rbrace>"
  unfolding cap_swap_for_delete_def cap_swap_def set_original_def
  apply (wp modify_wp set_cdt_globals_equiv set_cap_globals_equiv'' dxo_wp_weak | simp)+
done

(*FIXME: Lots of this stuff should be in arch *)
crunch globals_equiv[wp]: deleting_irq_handler "globals_equiv st"

lemma get_thread_state_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace> get_thread_state ref \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding get_thread_state_def
  apply(wp set_object_globals_equiv dxo_wp_weak |simp)+
  done

lemma suspend_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and (\<lambda>s. t \<noteq> idle_thread s) and valid_ko_at_arm\<rbrace> suspend t \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding suspend_def
  apply (wp tcb_sched_action_extended.globals_equiv dxo_wp_weak)
       apply simp
      apply (wp set_thread_state_globals_equiv)
     apply wp+
      unfolding update_restart_pc_def
      apply wp+
    apply clarsimp
    apply (rule hoare_vcg_conj_lift)
     prefer 2
     apply (rule hoare_drop_imps)
     apply wp+
    apply (rule hoare_drop_imps)
    apply wp+
  apply auto
  done

crunch globals_equiv[wp]: prepare_thread_delete "globals_equiv st"
  (wp: dxo_wp_weak)

lemma finalise_cap_globals_equiv:
  "\<lbrace>globals_equiv st and (\<lambda>s. \<forall>p. cap = ThreadCap p \<longrightarrow> p \<noteq> idle_thread s)
    and valid_global_objs and valid_arch_state and pspace_aligned and valid_vspace_objs and valid_global_refs and valid_vs_lookup\<rbrace>
    finalise_cap cap b
   \<lbrace>\<lambda> _. globals_equiv st\<rbrace>"
  apply (induct cap)
             apply (simp_all)
             apply (wp liftM_wp when_def cancel_all_ipc_globals_equiv cancel_all_ipc_valid_global_objs
                       cancel_all_signals_globals_equiv cancel_all_signals_valid_global_objs
                       arch_finalise_cap_globals_equiv unbind_maybe_notification_globals_equiv
                       unbind_notification_globals_equiv
                       | clarsimp simp add: valid_arch_state_ko_at_arm | intro impI conjI)+
  done

crunch valid_ko_at_arm[wp]: cap_swap_for_delete, restart "valid_ko_at_arm"
  (wp: dxo_wp_weak ignore: cap_swap_ext)

lemma rec_del_preservation2':
  assumes finalise_cap_P: "\<And>cap final. \<lbrace>R cap and P\<rbrace> finalise_cap cap final \<lbrace>\<lambda>_.P\<rbrace>"
  assumes set_cap_P : "\<And> cap b. \<lbrace>Q and P\<rbrace> set_cap cap b \<lbrace>\<lambda>_.P\<rbrace>"
  assumes set_cap_Q : "\<And> cap b. \<lbrace>Q\<rbrace> set_cap cap b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes empty_slot_P: "\<And> slot free. \<lbrace>Q and P\<rbrace> empty_slot slot free \<lbrace>\<lambda>_. P\<rbrace>"
  assumes empty_slot_Q: "\<And> slot free. \<lbrace>Q\<rbrace> empty_slot slot free \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes cap_swap_for_delete_Q: "\<And> a b. \<lbrace>Q\<rbrace> cap_swap_for_delete a b \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes cap_swap_for_delete_P: "\<And> a b. \<lbrace>Q and P\<rbrace> cap_swap_for_delete a b \<lbrace>\<lambda>_. P\<rbrace>"
  assumes preemption_point_Q: "\<And> a b. \<lbrace>Q\<rbrace> preemption_point \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes preemption_point_P: "\<And> a b. \<lbrace>Q and P\<rbrace> preemption_point \<lbrace>\<lambda>_. P\<rbrace>"
  assumes invs_Q: "\<And> s. invs s \<Longrightarrow> Q s"
  assumes invs_R: "  \<And>s slot cap. invs s \<Longrightarrow> caps_of_state s slot = Some cap \<Longrightarrow> R cap s"
  shows
  "s \<turnstile> \<lbrace>\<lambda>s. invs s \<and> P s \<and> Q s \<and> emptyable (slot_rdcall call) s \<and> valid_rec_del_call call s\<rbrace>
     rec_del call
   \<lbrace>\<lambda>rv s. P s \<and> Q s\<rbrace>,\<lbrace>\<lambda>rv s. P s \<and> Q s\<rbrace>"
proof (induct rule: rec_del.induct,
       simp_all only: rec_del_fails)
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
          apply ((wp preemption_point_Q preemption_point_P | simp | wp (once) preemption_point_inv)+)[1]
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
                  set_cap_cte_wp_at hoare_vcg_const_Ball_lift static_imp_wp
                       | rule finalise_cap_not_reply_master
                       | simp add: in_monad)+
         apply (rule hoare_strengthen_post)
        apply (rule_tac Q="\<lambda>fin s. invs s \<and> cte_wp_at ((=) rv) slot s \<and> s \<turnstile> (fst fin)
                                          \<and> P s
                                          \<and> replaceable s slot (fst fin) rv
                                          \<and> emptyable slot s
                                          \<and> (\<forall>t\<in>obj_refs (fst fin). halted_if_tcb t s)
                                          \<and> ex_cte_cap_wp_to (appropriate_cte_cap rv) slot s"
                   in hoare_vcg_conj_lift)
         apply (wp finalise_cap_invs[where slot=slot]
                   finalise_cap_replaceable[where sl=slot]
                   Finalise_IF.finalise_cap_makes_halted[where slot=slot]
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
    apply (clarsimp simp:   conj_comms invs_def valid_state_def valid_pspace_def valid_arch_caps_def invs_R)
    apply (frule if_unsafe_then_capD [OF caps_of_state_cteD],clarsimp+)
done
next

  case (3 ptr bits n slot s)
  show ?case
    apply (simp add: spec_validE_def)
    apply (rule hoare_pre, wp cap_swap_for_delete_P cap_swap_for_delete_Q)
    apply (clarsimp simp: invs_valid_ko_at_arm)
    done

next

  case (4 ptr bits n slot s)
  show ?case
    apply (subst rec_del.simps)
    apply (rule hoare_pre_spec_validE)
     apply (rule split_spec_bindE)
      apply (rule split_spec_bindE[rotated])
       apply (rule "4.hyps", assumption+)

      apply (wp set_cap_P set_cap_Q get_cap_wp | simp)
      apply simp
      apply simp
      apply wp
      apply (clarsimp simp add: zombie_is_cap_toE)
      apply (clarsimp simp: cte_wp_at_caps_of_state zombie_ptr_emptyable)
done
qed

lemma rec_del_preservation2:
  "\<lbrakk>\<And>cap final. \<lbrace>R cap and P\<rbrace> finalise_cap cap final \<lbrace>\<lambda>_. P\<rbrace>; \<And>cap b. \<lbrace>Q and P\<rbrace> set_cap cap b \<lbrace>\<lambda>_. P\<rbrace>;
  \<And>cap b. invariant (set_cap cap b) Q; \<And>slot free. \<lbrace>Q and P\<rbrace> empty_slot slot free \<lbrace>\<lambda>_. P\<rbrace>;
  \<And>slot free. invariant (empty_slot slot free) Q; \<And>a b. invariant (cap_swap_for_delete a b) Q;
  \<And>a b. \<lbrace>Q and P\<rbrace> cap_swap_for_delete a b \<lbrace>\<lambda>_. P\<rbrace>; \<And>s. invs s \<Longrightarrow> Q s;
  \<And>s slot cap. invs s \<Longrightarrow> caps_of_state s slot = Some cap \<Longrightarrow> R cap s;
  invariant preemption_point Q; \<lbrace>Q and P\<rbrace> preemption_point \<lbrace>\<lambda>_. P\<rbrace>\<rbrakk>
 \<Longrightarrow> \<lbrace>\<lambda>s. invs s \<and> P s \<and> emptyable (slot_rdcall call) s \<and> valid_rec_del_call call s\<rbrace> rec_del call
    \<lbrace>\<lambda>r. P\<rbrace>"
  apply (rule_tac Q="\<lambda>s. invs s \<and> P s \<and> Q s \<and> emptyable (slot_rdcall call) s \<and> valid_rec_del_call call s" in hoare_pre_imp)
   apply simp
  apply (rule_tac Q="\<lambda>rv s. P s \<and> Q s" in hoare_strengthen_post)
   apply (rule validE_valid)
   apply (rule use_spec)
   apply (rule rec_del_preservation2' [where R=R],simp+)
  done

lemma valid_ko_at_arm_irq_state_independent_A[simp, intro!]:
  "irq_state_independent_A (valid_ko_at_arm)"
  apply(auto simp: irq_state_independent_A_def valid_ko_at_arm_def)
  done

lemma no_cap_to_idle_thread'': "valid_global_refs s \<Longrightarrow> caps_of_state s ref \<noteq> Some (ThreadCap (idle_thread s))"
  apply (clarsimp simp add: valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)
  apply (drule_tac x="fst ref" in spec)
  apply (drule_tac x="snd ref" in spec)
  apply (simp add: cap_range_def global_refs_def)
  done

lemma rec_del_globals_equiv:
  "\<lbrace>\<lambda>s. invs s \<and> globals_equiv st s \<and> emptyable (slot_rdcall call) s
     \<and> valid_rec_del_call call s\<rbrace>
     rec_del call
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (wp rec_del_preservation2[where Q="valid_ko_at_arm"
            and R="\<lambda>cap s. valid_global_objs s \<and> valid_arch_state s
                       \<and> pspace_aligned s \<and> valid_vspace_objs s
                       \<and> valid_global_refs s  \<and> valid_vs_lookup s
                       \<and> (\<forall>p. cap = ThreadCap p \<longrightarrow> p \<noteq> idle_thread s)
                     "]  finalise_cap_globals_equiv)
             apply simp
            apply (wp set_cap_globals_equiv'')
            apply simp
           apply (wp set_cap_valid_ko_at_arm empty_slot_globals_equiv)+
          apply simp
         apply (wp empty_slot_valid_ko_at_arm)+
       apply simp
      apply (simp add: invs_valid_ko_at_arm)
     apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def valid_pspace_def no_cap_to_idle_thread'')
    apply (wp preemption_point_inv | simp)+
  done

lemma cap_delete_globals_equiv : "\<lbrace>globals_equiv st and invs and emptyable a\<rbrace> (cap_delete a) \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding cap_delete_def
  apply (wp rec_del_globals_equiv)
  apply simp
  done

lemma no_cap_to_idle_thread': "valid_global_refs s \<Longrightarrow> \<not> ex_nonz_cap_to (idle_thread s) s"
  apply (clarsimp simp add: ex_nonz_cap_to_def valid_global_refs_def valid_refs_def)
  apply (drule_tac x=a in spec)
  apply (drule_tac x=b in spec)
  apply (clarsimp simp: cte_wp_at_def global_refs_def cap_range_def)
  apply (case_tac cap,simp_all)
  done

lemma no_cap_to_idle_thread: "invs s \<Longrightarrow> \<not> ex_nonz_cap_to (idle_thread s) s"
  apply (rule no_cap_to_idle_thread')
  apply clarsimp
  done

crunch idle_thread_inv [wp]: set_mcpriority "\<lambda>s. P (idle_thread s)"
  (wp: syscall_valid crunch_wps rec_del_preservation cap_revoke_preservation)


(* FIXME: Pretty general. Probably belongs somewhere else *)
lemma invoke_tcb_thread_preservation:
  assumes cap_delete_P: "\<And>slot. \<lbrace>invs and P and emptyable slot \<rbrace> cap_delete slot \<lbrace>\<lambda>_.P\<rbrace>"
  assumes cap_insert_P: "\<And>new_cap src dest. \<lbrace>invs and P\<rbrace> cap_insert new_cap src dest \<lbrace>\<lambda>_.P\<rbrace>"
  assumes thread_set_P: "\<And>f ptr. \<lbrace>invs and P\<rbrace> thread_set (tcb_ipc_buffer_update f) ptr \<lbrace>\<lambda>_.P\<rbrace>"
  assumes thread_set_P': "\<And>f ptr. \<lbrace>invs and P\<rbrace> thread_set (tcb_fault_handler_update f) ptr \<lbrace>\<lambda>_.P\<rbrace>"
  assumes set_mcpriority_P: "\<And>mcp ptr. \<lbrace>invs and P\<rbrace> set_mcpriority ptr mcp \<lbrace>\<lambda>_.P\<rbrace>"
  assumes set_register_P[wp]: "\<And>d. \<lbrace>P and invs and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace> as_user t (setRegister TPIDRURW d) \<lbrace>\<lambda>_. P\<rbrace>"
  assumes P_trans[simp]: "\<And>f s. P (trans_state f s) = P s"
shows "
   \<lbrace>P and invs and Tcb_AI.tcb_inv_wf (tcb_invocation.ThreadControl t sl ep mcp prio croot vroot buf)\<rbrace>
     invoke_tcb (tcb_invocation.ThreadControl t sl ep mcp prio croot vroot buf)
   \<lbrace>\<lambda>rv. P\<rbrace>"

  apply (simp add: split_def cong: option.case_cong)

  apply (rule hoare_vcg_precond_imp)
   apply (rule_tac P="case ep of Some v \<Rightarrow> length v = word_bits | _ \<Rightarrow> True"
                in hoare_gen_asm)
   apply wp
      apply ((simp add: conj_comms(1, 2) del: hoare_post_taut hoare_True_E_R
        | rule wp_split_const_if wp_split_const_if_R
                   hoare_vcg_all_lift_R
                   hoare_vcg_E_elim hoare_vcg_const_imp_lift_R
                   hoare_vcg_R_conj
        | (wp
             check_cap_inv2[where Q="\<lambda>_. pas_refined aag"]
             check_cap_inv2[where Q="\<lambda>_ s. t \<noteq> idle_thread s"]
             out_invs_trivial case_option_wpE cap_delete_deletes
             cap_delete_valid_cap cap_insert_valid_cap out_cte_at
             cap_insert_cte_at cap_delete_cte_at out_valid_cap out_tcb_valid
             hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
             thread_set_tcb_ipc_buffer_cap_cleared_invs
             thread_set_invs_trivial[OF ball_tcb_cap_casesI]
             hoare_vcg_all_lift thread_set_valid_cap out_emptyable
             check_cap_inv [where P="valid_cap c" for c]
             check_cap_inv [where P="tcb_cap_valid c p" for c p]
             check_cap_inv[where P="cte_at p0" for p0]
             check_cap_inv[where P="tcb_at p0" for p0]
             thread_set_cte_at
             thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
             thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             checked_insert_no_cap_to
             out_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             thread_set_ipc_tcb_cap_valid
             check_cap_inv2[where Q="\<lambda>_. P"]
             cap_delete_P
             cap_insert_P
             thread_set_P thread_set_P'
             set_mcpriority_P
             dxo_wp_weak
             static_imp_wp
             set_mcpriority_idle_thread
            )
        | simp add: ran_tcb_cap_cases dom_tcb_cap_cases[simplified]
                    emptyable_def
               del: hoare_post_taut hoare_True_E_R
        | wpc
        | strengthen use_no_cap_to_obj_asid_strg
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index 0"]
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index (Suc 0)"])+)
              apply (unfold option_update_thread_def)
      apply (wp itr_wps thread_set_P thread_set_P'
              | simp add: emptyable_def | wpc)+ (*slow*)
  apply (clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified]
                        is_cap_simps is_valid_vtable_root_def
                        is_cnode_or_valid_arch_def tcb_cap_valid_def
                        tcb_at_st_tcb_at[symmetric] invs_valid_objs
                        cap_asid_def vs_cap_ref_def
                        clas_no_asid cli_no_irqs no_cap_to_idle_thread
                 split: option.split_asm
       | rule conjI)+ (* also slow *)
done

crunch idle_thread'[wp]: restart "\<lambda>s. P (idle_thread s)" (wp: dxo_wp_weak)

lemma bind_notification_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm\<rbrace>
   bind_notification t ntfnptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding bind_notification_def
  by (wp set_bound_notification_globals_equiv set_notification_globals_equiv
            set_notification_valid_ko_at_arm | wpc | simp)+

lemma bind_notification_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace>
   bind_notification t ntfnptr
   \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding bind_notification_def
  by (wp set_bound_notification_valid_ko_at_arm set_notification_valid_ko_at_arm | wpc | simp)+

lemma invoke_tcb_NotificationControl_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm\<rbrace>
   invoke_tcb (NotificationControl t ntfn)
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (case_tac ntfn, simp_all)
  apply (wp unbind_notification_globals_equiv bind_notification_globals_equiv)+
  done

crunch globals_equiv: set_mcpriority "globals_equiv st"

lemma dxo_globals_equiv[wp]:
  "\<lbrace>globals_equiv st\<rbrace> do_extended_op eop  \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  by (simp | wp dxo_wp_weak)+

lemma invoke_tcb_globals_equiv:
  "\<lbrace> invs and globals_equiv st and Tcb_AI.tcb_inv_wf ti\<rbrace>
   invoke_tcb ti
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply(case_tac ti;
    (solves \<open>
        (wp mapM_x_wp' as_user_globals_equiv invoke_tcb_NotificationControl_globals_equiv
               | simp add: invs_valid_ko_at_arm
               | intro conjI impI
               | clarsimp simp: no_cap_to_idle_thread)+
    \<close>)?)
   defer
   apply (simp del: invoke_tcb.simps Tcb_AI.tcb_inv_wf.simps )
   apply ((wp invoke_tcb_thread_preservation cap_delete_globals_equiv
             cap_insert_globals_equiv'' thread_set_globals_equiv
             set_mcpriority_globals_equiv
          | clarsimp simp add: invs_valid_ko_at_arm split del: if_split)+)[1]
  apply wpsimp
      apply (rename_tac word1 word2 bool1 bool2 bool3 bool4 arm_copy_register_sets)
      apply (rule_tac Q="\<lambda>_. valid_ko_at_arm and globals_equiv st and (\<lambda>s. word1 \<noteq> idle_thread s)
                         and (\<lambda>s. word2 \<noteq> idle_thread s)" in hoare_strengthen_post)
       apply (wp mapM_x_wp' as_user_globals_equiv invoke_tcb_NotificationControl_globals_equiv
               | simp add: invs_valid_ko_at_arm
               | intro conjI impI
               | clarsimp simp: no_cap_to_idle_thread)+
  done


section "reads respects"

lemma setup_reply_master_reads_respects:
  "reads_respects aag l (K (is_subject aag t)) (setup_reply_master t)"
  apply (simp add: setup_reply_master_def when_def)
  apply (wp set_cap_reads_respects set_original_reads_respects get_cap_rev | simp)+
   apply (wp | wp (once) hoare_drop_imps)+
  apply clarsimp
  done

(*Clagged*)
(*
crunch states_equiv[wp]: switch_if_required_to "states_equiv_for P Q R X st"
*)

lemmas gets_cur_thread_respects_f =
       gets_cur_thread_ev[THEN reads_respects_f[where Q=\<top>],simplified,wp]

lemma restart_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and pas_cur_domain aag and invs
                           and tcb_at t
                           and (\<lambda>s. is_subject aag (cur_thread s)) and K (is_subject aag t))
      (restart t)"
  apply (rule gen_asm_ev | elim conjE)+
  apply (simp add: restart_def when_def)
  apply (wp reads_respects_f[OF set_thread_state_reads_respects, where Q="\<top>"]
            reads_respects_f[OF setup_reply_master_reads_respects setup_reply_master_silc_inv]
            gets_cur_thread_ev
            set_thread_state_pas_refined
            setup_reply_master_pas_refined
            reads_respects_f[OF possible_switch_to_reads_respects, where Q="\<top>"]
            reads_respects_f[OF tcb_sched_action_reads_respects, where Q="\<top>"]
            cancel_ipc_reads_respects_f setup_reply_master_silc_inv cancel_ipc_silc_inv
      | simp
      | strengthen invs_mdb)+

    apply (simp add: get_thread_state_def thread_get_def)
    apply wp
   apply (wp hoare_drop_imps)
  apply clarsimp
  apply (rule requiv_get_tcb_eq, simp+ |
         rule conjI | assumption | clarsimp simp: reads_equiv_f_def)+
  done

lemma det_zipWithM:
  assumes "\<And> x y. \<lbrakk>x \<in> set xs; y \<in> set ys\<rbrakk> \<Longrightarrow> det (f x y)"
  shows "det (zipWithM f xs ys)"
  apply(simp add: zipWithM_mapM)
  apply(rule det_mapM[OF _ subset_refl])
  apply(simp add: split_def)
  apply(case_tac x)
  apply(clarsimp)
  apply(erule in_set_zipE)
  apply(erule (1) assms)
  done

lemma checked_insert_reads_respects:
  "reads_respects aag l (K (is_subject aag (fst b) \<and> is_subject aag (fst d) \<and> is_subject aag (fst e)))
     (check_cap_at a b (check_cap_at c d (cap_insert a b e)))"
  apply(rule equiv_valid_guard_imp)
   apply(simp add: check_cap_at_def)
   apply (wp when_ev cap_insert_reads_respects get_cap_wp get_cap_rev | simp)+
  done





definition authorised_tcb_inv_extra where
  "authorised_tcb_inv_extra aag ti \<equiv>
    (case ti of ThreadControl _ slot _ _ _ _ _ _ \<Rightarrow> is_subject aag (fst slot) | _ \<Rightarrow> True)"

lemmas as_user_reads_respects_f = reads_respects_f[OF as_user_reads_respects, where Q="\<top>", simplified, OF as_user_silc_inv]


lemma ethread_set_reads_respects: "reads_respects aag l \<top>
        (ethread_set f word)"
  apply (simp add: ethread_set_def)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def put_def
                   get_def bind_def set_eobject_def return_def
                   gets_def gets_the_def assert_opt_def
                   get_etcb_def fail_def cong: option.case_cong split: option.splits)
  apply (fastforce intro: equiv_forI reads_equiv_ekheap_updates affects_equiv_ekheap_update simp: reads_equiv_def2 affects_equiv_def2 elim: states_equiv_forE_ekheap)
  done


declare gts_st_tcb_at[wp del]

lemma ethread_set_priority_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace>
     ethread_set (tcb_priority_update f) thread
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (erule_tac x="(a, b)" in ballE)
   apply force
  apply (erule notE)
  apply (erule domains_of_state_aux.cases, simp add: get_etcb_def split: if_split_asm)
   apply (force intro: domtcbs)+
   done

lemma set_priority_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l
           (pas_refined aag and K (is_subject aag word)
            and pas_cur_domain aag and (\<lambda>s. is_subject aag (cur_thread s)))
           (set_priority word prio)"
  apply (simp add: set_priority_def thread_set_priority_def)
  apply (wp get_thread_state_rev gets_cur_thread_ev gts_wp when_ev
            hoare_vcg_all_lift hoare_vcg_imp_lift'
            ethread_set_reads_respects
            tcb_sched_action_reads_respects
            possible_switch_to_reads_respects
         | simp split del: if_split
         | wp (once) hoare_drop_imps
         | (rule hoare_strengthen_post, rule ethread_set_priority_pas_refined)
         | force)+
  done

lemma set_mcpriority_reads_respects:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects aag l \<top> (set_mcpriority x y)"
  unfolding set_mcpriority_def
  by (rule thread_set_reads_respects[OF domains_distinct])

lemma checked_cap_insert_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state)\<rbrace>
  check_cap_at a b (check_cap_at c d (cap_insert a b e))
   \<lbrace>\<lambda>rv. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres checked_cap_insert_domain_sep_inv | clarsimp | simp)+
  done

lemma cap_delete_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state)\<rbrace>
   cap_delete slot
   \<lbrace>\<lambda>rv. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres cap_delete_irq_masks | force)+
  done

lemma set_priority_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state)\<rbrace>
   set_priority t prio
   \<lbrace>\<lambda>rv. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres | force)+
  done

lemma set_mcpriority_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state)\<rbrace>
   set_mcpriority t prio
   \<lbrace>\<lambda>rv. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres | force)+
  done

lemma thread_set_tcb_fault_handler_update_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state)\<rbrace>
   thread_set (tcb_fault_handler_update blah) t
   \<lbrace>\<lambda>rv. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres | force)+
  done

lemma bind_notification_reads_respects:
  "reads_respects aag l (pas_refined aag and invs and K (is_subject aag t \<and> (\<forall>auth\<in>{Receive, Reset}. (pasSubject aag, auth, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag)))
       (bind_notification t ntfnptr)"
  apply (clarsimp simp: bind_notification_def)
  apply (wp set_bound_notification_owned_reads_respects set_simple_ko_reads_respects
            get_simple_ko_reads_respects get_bound_notification_reads_respects
            gbn_wp[unfolded get_bound_notification_def, simplified]
       | wpc
       | simp add: get_bound_notification_def)+
  apply (clarsimp dest!: reads_ep)
  done

lemmas thread_get_reads_respects_f = reads_respects_f[OF thread_get_reads_respects, where Q="\<top>", simplified, OF thread_get_inv]

lemmas reschedule_required_reads_respects_f = reads_respects_f[OF reschedule_required_reads_respects, where Q="\<top>", simplified, OF _ reschedule_required_ext_extended.silc_inv]
crunch pas_refined[wp]: restart "pas_refined aag"

lemma invoke_tcb_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes validE_valid[wp del]
        static_imp_wp [wp]
  shows
  "reads_respects_f aag l (silc_inv aag st and only_timer_irq_inv irq st' and einvs
         and simple_sched_action and pas_refined aag and pas_cur_domain aag
         and Tcb_AI.tcb_inv_wf ti and is_subject aag \<circ> cur_thread
         and K (authorised_tcb_inv aag ti \<and> authorised_tcb_inv_extra aag ti))
     (invoke_tcb ti)"
  including no_pre
  apply(case_tac ti)
         apply(wpsimp wp: thread_get_reads_respects_f when_ev restart_reads_respects_f
                          reschedule_required_reads_respects_f as_user_reads_respects_f
                          static_imp_wp thread_get_wp' restart_silc_inv restart_pas_refined
                          hoare_vcg_if_lift)+
         apply(solves\<open>auto intro!: det_zipWithM
                             simp: det_setRegister det_getRestartPC det_setNextPC
                                   authorised_tcb_inv_def  reads_equiv_f_def\<close>)
        apply(wp as_user_reads_respects_f suspend_silc_inv when_ev  suspend_reads_respects_f
             | simp | elim conjE, assumption)+
        apply(solves\<open>auto simp: authorised_tcb_inv_def  det_getRegister reads_equiv_f_def
                        intro!: det_mapM[OF _ subset_refl]\<close>)
       apply(wp when_ev mapM_x_ev'' reschedule_required_reads_respects_f[where st=st]
                as_user_reads_respects_f[where st=st] hoare_vcg_ball_lift mapM_x_wp'
                restart_reads_respects_f restart_silc_inv hoare_vcg_if_lift
                suspend_reads_respects_f suspend_silc_inv hoare_drop_imp
                restart_silc_inv restart_pas_refined
            | simp split del: if_split add: det_setRegister det_setNextPC
            | strengthen invs_mdb)+
       apply(solves\<open>auto simp: authorised_tcb_inv_def
                        idle_no_ex_cap[OF invs_valid_global_refs invs_valid_objs] det_getRestartPC
                        det_getRegister\<close>)
      defer
      apply((wp suspend_reads_respects_f[where st=st] restart_reads_respects_f[where st=st]
              | simp add: authorised_tcb_inv_def )+)[2]
    \<comment> \<open>NotificationControl\<close>
    apply (rename_tac option)
    apply (case_tac option, simp_all)[1]
     apply ((wp unbind_notification_is_subj_reads_respects unbind_notification_silc_inv
           bind_notification_reads_respects
         | clarsimp simp: authorised_tcb_inv_def
         | rule_tac Q=\<top> and st=st in reads_respects_f)+)[2]
   \<comment> \<open>SetTLSBase\<close>
   apply (rename_tac tcb tls_base)
   apply(wpsimp wp: when_ev reschedule_required_reads_respects_f
                    as_user_reads_respects_f hoare_drop_imps)+
   apply(auto simp: det_setRegister authorised_tcb_inv_def)[1]
  \<comment> \<open>ThreadControl\<close>
  apply (simp add: split_def cong: option.case_cong)
  apply (wpsimp wp: set_priority_reads_respects[THEN
                     reads_respects_f[where aag=aag and st=st and Q=\<top>]])
                    apply (wpsimp wp: hoare_vcg_const_imp_lift_R simp: when_def | wpc)+
                    apply (rule conjI)
                     apply ((wpsimp wp: reschedule_required_reads_respects_f)+)[4]
                 apply((wp reads_respects_f[OF cap_insert_reads_respects, where st=st]
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
                           hoare_vcg_all_lift_R hoare_vcg_all_lift
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
                           checked_insert_no_cap_to hoare_vcg_const_imp_lift_R hoare_vcg_conj_lift
                           as_user_reads_respects_f thread_set_mdb
                      | wpc
                      | simp add: emptyable_def tcb_cap_cases_def tcb_cap_valid_def
                                  tcb_at_st_tcb_at when_def
                      | strengthen use_no_cap_to_obj_asid_strg invs_mdb
                      | solves auto)+)[7]
                    (* 9 subgoals here *)
          apply ((simp add: conj_comms,
                  strengthen imp_consequent[where Q="x = None" for x],
                  simp cong: conj_cong)
                | wp reads_respects_f[OF cap_insert_reads_respects, where st=st]
                     reads_respects_f[OF thread_set_reads_respects, where st=st and Q="\<top>"]
                     set_priority_reads_respects[THEN reads_respects_f[where aag=aag and st=st and Q=\<top>]]
                     set_mcpriority_reads_respects[THEN reads_respects_f[where aag=aag and st=st and Q=\<top>]]
                     check_cap_inv[OF check_cap_inv[OF cap_insert_valid_list]]
                     check_cap_inv[OF check_cap_inv[OF cap_insert_valid_sched]]
                     check_cap_inv[OF check_cap_inv[OF cap_insert_schedact]]
                     check_cap_inv[OF check_cap_inv[OF cap_insert_cur_domain]]
                     check_cap_inv[OF check_cap_inv[OF cap_insert_ct]]
                     get_thread_state_rev[THEN reads_respects_f[where aag=aag and st=st and Q=\<top>]]
                     hoare_vcg_all_lift_R hoare_vcg_all_lift
                     cap_delete_reads_respects[where st=st] checked_insert_pas_refined
                     thread_set_pas_refined reads_respects_f[OF checked_insert_reads_respects, where st=st]
                     checked_cap_insert_silc_inv[where st=st] cap_delete_silc_inv_not_transferable[where st=st]
                     checked_cap_insert_only_timer_irq_inv[where st=st' and irq=irq]
                     cap_delete_only_timer_irq_inv[where st=st' and irq=irq]
                     set_priority_only_timer_irq_inv[where st=st' and irq=irq]
                     set_mcpriority_only_timer_irq_inv[where st=st' and irq=irq]
                     cap_delete_deletes cap_delete_valid_cap cap_delete_cte_at
                     cap_delete_pas_refined' itr_wps(12) itr_wps(14) cap_insert_cte_at
                     checked_insert_no_cap_to hoare_vcg_const_imp_lift_R
                     as_user_reads_respects_f
                |wpc
                |simp add: emptyable_def tcb_cap_cases_def tcb_cap_valid_def
                           when_def st_tcb_at_triv
                |strengthen use_no_cap_to_obj_asid_strg invs_mdb
                |wp (once) hoare_drop_imp)+
    apply(simp add: option_update_thread_def tcb_cap_cases_def
         | wp static_imp_wp static_imp_conj_wp reads_respects_f[OF thread_set_reads_respects, where st=st and Q="\<top>"]
              thread_set_pas_refined | wpc)+
   apply(wp hoare_vcg_all_lift thread_set_tcb_fault_handler_update_invs
            thread_set_tcb_fault_handler_update_silc_inv
            thread_set_not_state_valid_sched
            thread_set_pas_refined thread_set_emptyable thread_set_valid_cap
            thread_set_cte_at  thread_set_no_cap_to_trivial
            thread_set_tcb_fault_handler_update_only_timer_irq_inv
        | simp add: tcb_cap_cases_def | wpc | wp (once) hoare_drop_imp)+
  apply (clarsimp simp: authorised_tcb_inv_def  authorised_tcb_inv_extra_def emptyable_def)
  by (clarsimp simp: is_cap_simps is_cnode_or_valid_arch_def is_valid_vtable_root_def
                     det_setRegister
                   | intro impI
                   | rule conjI)+

lemma invoke_tcb_reads_respects_f_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
"reads_respects_f_g aag l (silc_inv aag st and only_timer_irq_inv irq st' and pas_refined aag and pas_cur_domain aag and einvs and simple_sched_action and Tcb_AI.tcb_inv_wf ti and (\<lambda>s. is_subject aag (cur_thread s)) and K (authorised_tcb_inv aag ti \<and> authorised_tcb_inv_extra aag ti))
    (invoke_tcb ti)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_f_g)
    apply(rule invoke_tcb_reads_respects_f[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp invoke_tcb_globals_equiv | clarsimp | assumption | force)+
  done

lemma decode_tcb_invocation_authorised_extra:
  "\<lbrace>K (is_subject aag (fst slot))\<rbrace>
  decode_tcb_invocation label msg (ThreadCap t) slot excaps
  \<lbrace>\<lambda>rv s. authorised_tcb_inv_extra aag rv\<rbrace>, -"
  apply(simp add: authorised_tcb_inv_extra_def)
  apply(simp add: decode_tcb_invocation_def)
  apply(rule hoare_pre)
   apply(wp OR_choice_E_weak_wp
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
                              split_def decode_set_space_def
                   split del: if_split)+
  done

end

end
