(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Invariant preservation for all syscalls.
*)

theory Syscall_AI
imports
  ArchBCorres2_AI
  ArchTcb_AI
  ArchArch_AI
  ArchInterrupt_AI
begin

context begin interpretation Arch .
requalify_facts
  arch_decode_invocation_inv
  lookup_cap_and_slot_inv
  data_to_cptr_def
  arch_post_cap_deletion_cur_thread
  arch_post_cap_deletion_state_refs_of
  arch_invoke_irq_handler_typ_at
  getCurrentTime_invs
  resetTimer_device_state_inv
end

lemmas [wp] =
  arch_decode_invocation_inv
  lookup_cap_and_slot_inv
  getCurrentTime_invs

lemmas [simp] =
  data_to_cptr_def


lemma next_domain_invs[wp]:
  "next_domain \<lbrace> invs \<rbrace>"
  unfolding next_domain_def
  apply (wpsimp simp: Let_def)
  apply (simp add: invs_def cur_tcb_def cur_sc_tcb_def sc_tcb_sc_at_def valid_state_def
                   valid_mdb_def mdb_cte_at_def valid_ioc_def valid_irq_states_def
                   valid_machine_state_def)
  done

lemma next_domain_scheduler_action[wp]:
  "next_domain \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
  unfolding next_domain_def
  by (wpsimp simp: Let_def)

crunches awaken
  for invs[wp]: invs
  (wp: crunch_wps simp: tcb_release_dequeue_def)

crunches check_domain_time
  for invs[wp]: invs
  (simp: crunch_simps)

lemma set_scheduler_action_valid_state_cur_tcb [wp]:
  "\<lbrace>invs\<rbrace> set_scheduler_action action \<lbrace>\<lambda>_ s. valid_state s \<and> cur_tcb s\<rbrace>"
  apply (wpsimp simp: set_scheduler_action_def)
  apply (clarsimp simp: invs_def valid_state_def cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)
  done

lemma cur_thread_update_invs:
  "\<lbrace>\<lambda>s. invs s \<and> scheduler_action s \<noteq> resume_cur_thread \<and> tcb_at tptr s\<rbrace>
   modify (cur_thread_update (\<lambda>_. tptr))
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def valid_machine_state_def
                   state_refs_of_def cur_tcb_def cur_sc_tcb_def)

lemma switch_to_idle_thread_invs:
  "\<lbrace>\<lambda>s. invs s \<and> scheduler_action s \<noteq> resume_cur_thread\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: switch_to_idle_thread_def
                  wp: cur_thread_update_invs arch_stit_scheduler_action)
  apply (clarsimp simp: invs_def valid_state_def valid_idle_def pred_tcb_at_def obj_at_def is_tcb)
  done

lemma switch_to_thread_invs:
  "\<lbrace>\<lambda>s. invs s \<and> scheduler_action s \<noteq> resume_cur_thread\<rbrace>
   switch_to_thread tptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: switch_to_thread_def get_tcb_obj_ref_def thread_get_def is_tcb
               wp: cur_thread_update_invs arch_stt_scheduler_action)

lemma guarded_switch_to_invs:
  "\<lbrace>\<lambda>s. invs s \<and> scheduler_action s \<noteq> resume_cur_thread\<rbrace>
   guarded_switch_to thread
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: guarded_switch_to_def
               wp: switch_to_thread_invs hoare_drop_imps)

(* still true without scheduler_action s \<noteq> resume_cur_thread, but the proof for schedule_invs
   will be simpler with it *)
lemma schedule_choose_new_thread_valid_state_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. invs s \<and> scheduler_action s \<noteq> resume_cur_thread\<rbrace>
   schedule_choose_new_thread
   \<lbrace>\<lambda>_ s. valid_state s \<and> cur_tcb s\<rbrace>"
  by (wpsimp simp: schedule_choose_new_thread_def choose_thread_def
               wp: set_scheduler_action_valid_state_cur_tcb switch_to_idle_thread_invs
                   guarded_switch_to_invs hoare_drop_imps)

lemma schedule_invs[wp]:
  "schedule \<lbrace>invs\<rbrace>"
  apply (simp add: schedule_def)
  apply (wpsimp wp: switch_to_thread_invs hoare_drop_imps sc_and_timer_invs
              simp: if_apply_def2 set_scheduler_action_def)
    apply (rule_tac Q="\<lambda>_. invs" in hoare_strengthen_post)
     apply (wpsimp simp: invs_def)+
  done

lemma invs_domain_time_update[simp]:
  "invs (domain_time_update f s) = invs s"
  by (simp add: invs_def valid_state_def cur_sc_tcb_def)

lemma invs_domain_index_update[simp]:
  "invs (domain_index_update f s) = invs s"
  by (simp add: invs_def valid_state_def valid_mdb_def mdb_cte_at_def valid_ioc_def
                valid_irq_states_def valid_machine_state_def cur_tcb_def cur_sc_tcb_def)

lemma invs_cur_domain_update[simp]:
  "invs (cur_domain_update f s) = invs s"
  by (simp add: invs_def valid_state_def valid_mdb_def mdb_cte_at_def valid_ioc_def
                valid_irq_states_def valid_machine_state_def cur_tcb_def cur_sc_tcb_def)

lemma choose_thread_ct_activatable[wp]:
  "\<lbrace> invs \<rbrace> choose_thread \<lbrace>\<lambda>_. ct_in_state activatable \<rbrace>"
proof -
  have P: "\<And>t s. ct_in_state activatable (cur_thread_update (\<lambda>_. t) s) = st_tcb_at activatable t s"
    by (fastforce simp: ct_in_state_def st_tcb_at_def intro: obj_at_pspaceI)
  show ?thesis
    unfolding choose_thread_def guarded_switch_to_def
    apply (wpsimp wp: stit_activatable stt_activatable split_del: if_split wp_del: get_sched_context_wp)
         apply (wpsimp wp: is_schedulable_wp)
        apply (wpsimp wp: assert_wp)
       apply (wpsimp simp: thread_get_def)+
    apply (clarsimp simp: schedulable_def pred_tcb_at_def obj_at_def
        dest!: get_tcb_SomeD split: option.splits)
    done
qed

lemma schedule_choose_new_thread_ct_activatable[wp]:
  "\<lbrace> invs \<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>_. ct_in_state activatable \<rbrace>"
    unfolding schedule_choose_new_thread_def by wpsimp

lemma guarded_switch_to_ct_in_state_activatable[wp]:
  "\<lbrace>\<top>\<rbrace> guarded_switch_to t \<lbrace>\<lambda>a. ct_in_state activatable\<rbrace>"
  unfolding guarded_switch_to_def
  apply (wpsimp wp: hoare_vcg_imp_lift gts_wp is_schedulable_wp stt_activatable assert_wp
             simp: thread_get_def)
  apply (clarsimp simp: schedulable_def get_tcb_ko_at st_tcb_at_def obj_at_def
                 split: option.splits)
  done

declare sc_and_timer_activatable[wp]

lemma awaken_schact_not_rct[wp]:
  "awaken \<lbrace>\<lambda>s. scheduler_action s \<noteq> resume_cur_thread\<rbrace>"
  unfolding awaken_def awaken_body_def tcb_release_dequeue_def possible_switch_to_def
  apply (rule whileLoop_wp)
   apply (wpsimp wp: hoare_drop_imps simp: set_scheduler_action_def)+
  done

crunches awaken
  for ct_in_state[wp]: "ct_in_state P"
  (wp: crunch_wps)

lemma get_tcb_None:
  "(get_tcb t s = None) = (\<forall>x. \<not>kheap s t = Some (TCB x))"
  by (auto simp: obj_at_def get_tcb_def
           split: option.splits Structures_A.kernel_object.splits)

lemma syscall_valid:
  assumes x:
             "\<And>ft. \<lbrace>P_flt ft\<rbrace> h_flt ft \<lbrace>Q\<rbrace>"
             "\<And>err. \<lbrace>P_err err\<rbrace> h_err err \<lbrace>Q\<rbrace>"
             "\<And>rv. \<lbrace>P_no_err rv\<rbrace> m_fin rv \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
             "\<And>rv. \<lbrace>P_no_flt rv\<rbrace> m_err rv \<lbrace>P_no_err\<rbrace>, \<lbrace>P_err\<rbrace>"
             "\<lbrace>P\<rbrace> m_flt \<lbrace>P_no_flt\<rbrace>, \<lbrace>P_flt\<rbrace>"
  shows "\<lbrace>P\<rbrace> Syscall_A.syscall m_flt h_flt m_err h_err m_fin \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (simp add: Syscall_A.syscall_def liftE_bindE
             cong: sum.case_cong)
  apply (rule hoare_split_bind_case_sumE)
    apply (wp x)[1]
   apply (rule hoare_split_bind_case_sumE)
     apply (wp x|simp)+
  done


(* In order to assert conditions that must hold for the appropriate
   handleInvocation and handle_invocation calls to succeed, we must have
   some notion of what a valid invocation is.
   This function defines that.
   For example, a InvokeEndpoint requires an endpoint at its first
   constructor argument. *)

primrec
  valid_invocation :: "Invocations_A.invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_invocation (InvokeUntyped i) = valid_untyped_inv i"
| "valid_invocation (InvokeEndpoint w w2 b gr) = (ep_at w and ex_nonz_cap_to w)"
| "valid_invocation (InvokeNotification w w2) = (ntfn_at w and ex_nonz_cap_to w)"
| "valid_invocation (InvokeTCB i) = tcb_inv_wf i"
| "valid_invocation (InvokeDomain thread domain) = (tcb_at thread and (\<lambda>s. thread \<noteq> idle_thread s))"
| "valid_invocation (InvokeReply reply grant) = (reply_at reply and ex_nonz_cap_to reply)"
| "valid_invocation (InvokeIRQControl i) = irq_control_inv_valid i"
| "valid_invocation (InvokeIRQHandler i) = irq_handler_inv_valid i"
| "valid_invocation (InvokeCNode i) = valid_cnode_inv i"
| "valid_invocation (InvokeSchedContext i) = valid_sched_context_inv i"
| "valid_invocation (InvokeSchedControl i) = valid_sched_control_inv i"
| "valid_invocation (InvokeArchObject i) = valid_arch_inv i"

lemma sts_Restart_invs[wp]:
  "\<lbrace>st_tcb_at active t and invs\<rbrace>
   set_thread_state t Structures_A.Restart
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp wp: sts_invs_minor2)
  apply (intro conjI)
     apply (fastforce elim: pred_tcb_weakenE simp: runnable_eq_active)
    apply (fastforce elim: st_tcb_ex_cap simp: runnable_eq_active)
   apply (erule not_idle_thread'[rotated]; clarsimp)
  apply (fastforce elim: fault_tcbs_valid_states_active[rotated])
  done

lemma check_budget_restart_invs[wp]:
  "\<lbrace>\<lambda>s. invs s\<rbrace> check_budget_restart \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: check_budget_restart_def)
  apply (rule hoare_seq_ext[rotated])
   apply (rule check_budget_invs)
  apply (wpsimp wp: gts_wp)
  apply (frule invs_fault_tcbs_valid_states)
  apply (frule_tac t="cur_thread s" in fault_tcbs_valid_states_not_fault_tcb_states)
   apply (fastforce simp: pred_neg_def is_blocked_thread_state_defs
                    elim: pred_tcb_weakenE)
  apply (case_tac st; clarsimp)
   apply (frule invs_iflive,
          clarsimp simp: if_live_then_nonz_cap_def pred_tcb_at_def obj_at_def live_def)+
  done

lemma invoke_tcb_tcb[wp]:
  "invoke_tcb i \<lbrace>tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ, rule invoke_tcb_typ_at [where P=id, simplified])

lemma invoke_domain_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_domain thread domain \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_domain_typ_at [where P=id, simplified])

lemma simple_from_active:
  "st_tcb_at active t s \<Longrightarrow> st_tcb_at simple t s"
  by (fastforce elim!: pred_tcb_weakenE)

lemma simple_from_running:
  "ct_running s \<Longrightarrow> st_tcb_at simple (cur_thread s) s"
  by (fastforce simp: ct_in_state_def
               elim!: pred_tcb_weakenE)

locale Systemcall_AI_Pre =
  fixes proj:: "itcb \<Rightarrow> 'a"
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes handle_arch_fault_reply_pred_tcb_at[wp]:
    "\<And> P t f obj d dl.
      \<lbrace> pred_tcb_at proj P t :: 'state_ext state \<Rightarrow> _\<rbrace>
        handle_arch_fault_reply f obj d dl
      \<lbrace> \<lambda>_ . pred_tcb_at proj P t \<rbrace>"
  assumes handle_arch_fault_reply_invs[wp]:
    "\<And> f obj d dl.
      \<lbrace> invs :: 'state_ext state \<Rightarrow> _ \<rbrace> handle_arch_fault_reply f obj d dl \<lbrace> \<lambda>_ . invs \<rbrace>"
  assumes handle_arch_fault_reply_cap_to[wp]:
    "\<And> f obj d dl c.
      \<lbrace> ex_nonz_cap_to c :: 'state_ext state \<Rightarrow> _ \<rbrace>
        handle_arch_fault_reply f obj d dl
      \<lbrace> \<lambda>_ . ex_nonz_cap_to c \<rbrace>"
  assumes handle_arch_fault_reply_it[wp]:
    "\<And> P f obj d dl.
      \<lbrace> \<lambda>s :: 'state_ext state. P (idle_thread s) \<rbrace>
        handle_arch_fault_reply f obj d dl
      \<lbrace> \<lambda>_ s. P (idle_thread s) \<rbrace>"
  assumes handle_arch_fault_reply_caps[wp]:
    "\<And> P f obj d dl.
      \<lbrace> \<lambda>s  :: 'state_ext state . P (caps_of_state s) \<rbrace>
        handle_arch_fault_reply f obj d dl
      \<lbrace> \<lambda>_ s. P (caps_of_state s) \<rbrace>"
  assumes handle_arch_fault_reply_cte_wp_at[wp]:
     "\<And> P P' p x4 t d dl.
       \<lbrace>\<lambda>s ::'state_ext state . P (cte_wp_at P' p s)\<rbrace>
         handle_arch_fault_reply x4 t d dl
       \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  assumes handle_arch_fault_reply_cur_thread[wp]:
    "\<And> P  x4 t d dl.
       \<lbrace>\<lambda>s ::'state_ext state . P (cur_thread s)\<rbrace>
         handle_arch_fault_reply x4 t d dl
       \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  assumes handle_arch_fault_st_tcb_at_simple[wp]:
    "\<And> x4 t' t d dl.
       \<lbrace>st_tcb_at simple t' :: 'state_ext state \<Rightarrow> _\<rbrace>
         handle_arch_fault_reply x4 t d dl
       \<lbrace>\<lambda>_ .st_tcb_at simple t'\<rbrace>"
  assumes handle_arch_fault_valid_objs[wp]:
    "\<And> x4 t d dl.
       \<lbrace> valid_objs :: 'state_ext state \<Rightarrow> _\<rbrace>
         handle_arch_fault_reply x4 t d dl
       \<lbrace>\<lambda>_ .valid_objs\<rbrace>"
  assumes arch_get_sanitise_register_info_pred_tcb_at[wp]:
    "\<And> P t g.
      \<lbrace> pred_tcb_at proj P t :: 'state_ext state \<Rightarrow> _\<rbrace>
        arch_get_sanitise_register_info g
      \<lbrace> \<lambda>_ . pred_tcb_at proj P t \<rbrace>"
  assumes arch_get_sanitise_register_info_invs[wp]:
    "\<And> f.
      \<lbrace> invs :: 'state_ext state \<Rightarrow> _ \<rbrace> arch_get_sanitise_register_info f  \<lbrace> \<lambda>_ . invs \<rbrace>"
  assumes arch_get_sanitise_register_info_cap_to[wp]:
    "\<And> f c.
      \<lbrace> ex_nonz_cap_to c :: 'state_ext state \<Rightarrow> _ \<rbrace>
        arch_get_sanitise_register_info f
      \<lbrace> \<lambda>_ . ex_nonz_cap_to c \<rbrace>"
  assumes arch_get_sanitise_register_info_it[wp]:
    "\<And> P f .
      \<lbrace> \<lambda>s :: 'state_ext state. P (idle_thread s) \<rbrace>
        arch_get_sanitise_register_info f
      \<lbrace> \<lambda>_ s. P (idle_thread s) \<rbrace>"
  assumes arch_get_sanitise_register_info_caps[wp]:
    "\<And> P f .
      \<lbrace> \<lambda>s  :: 'state_ext state . P (caps_of_state s) \<rbrace>
        arch_get_sanitise_register_info f
      \<lbrace> \<lambda>_ s. P (caps_of_state s) \<rbrace>"
  assumes arch_get_sanitise_register_info_cte_wp_at[wp]:
     "\<And> P P' p x4.
       \<lbrace>\<lambda>s ::'state_ext state . P (cte_wp_at P' p s)\<rbrace>
         arch_get_sanitise_register_info x4
       \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  assumes arch_get_sanitise_register_info_cur_thread[wp]:
    "\<And> P  x4.
       \<lbrace>\<lambda>s ::'state_ext state . P (cur_thread s)\<rbrace>
         arch_get_sanitise_register_info x4
       \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  assumes arch_get_sanitise_register_info_st_tcb_at_simple[wp]:
    "\<And> x4 t'.
       \<lbrace>st_tcb_at simple t' :: 'state_ext state \<Rightarrow> _\<rbrace>
         arch_get_sanitise_register_info x4
       \<lbrace>\<lambda>_ .st_tcb_at simple t'\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_objs[wp]:
    "\<And> x4.
       \<lbrace> valid_objs :: 'state_ext state \<Rightarrow> _\<rbrace>
         arch_get_sanitise_register_info x4
       \<lbrace>\<lambda>_ .valid_objs\<rbrace>"

begin

crunch pred_tcb_at[wp]: handle_fault_reply "pred_tcb_at proj P t :: 'state_ext state \<Rightarrow> _"
crunch invs[wp]: handle_fault_reply "invs :: 'state_ext state \<Rightarrow> _"
crunch cap_to[wp]: handle_fault_reply "ex_nonz_cap_to c :: 'state_ext state \<Rightarrow> _"
crunch it[wp]: handle_fault_reply "\<lambda>s :: 'state_ext state. P (idle_thread s) "
crunch caps[wp]: handle_fault_reply "\<lambda>s :: 'state_ext state. P (caps_of_state s)"

end

lemma st_tcb_at_eq:
  "\<lbrakk> st_tcb_at (\<lambda>s. s = st) t s; st_tcb_at (\<lambda>s. s = st') t s \<rbrakk> \<Longrightarrow> st = st'"
  by (clarsimp simp add: pred_tcb_at_def obj_at_def)

lemma do_ipc_transfer_tcb_at [wp]:
  "\<lbrace>\<lambda>s. P (tcb_at t s)\<rbrace> do_ipc_transfer s ep bg grt r \<lbrace>\<lambda>rv s. P (tcb_at t s)\<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma do_ipc_transfer_non_null_cte_wp_at2:
  fixes P
  assumes PNN: "\<And>cap. P cap \<Longrightarrow> cap \<noteq> cap.NullCap"
  assumes PUC: "\<And>cap. P cap \<Longrightarrow> \<not> is_untyped_cap cap"
  shows "\<lbrace>valid_objs and cte_wp_at P ptr\<rbrace> do_ipc_transfer st ep b gr rt \<lbrace>\<lambda>_. cte_wp_at P ptr\<rbrace>"
  proof -
    have PimpQ: "\<And>P Q ptr s. \<lbrakk> cte_wp_at P ptr s; \<And>cap. P cap \<Longrightarrow> Q cap \<rbrakk> \<Longrightarrow> cte_wp_at (P and Q) ptr s"
      by (erule cte_wp_at_weakenE, clarsimp)
    show ?thesis
      apply (rule hoare_chain [OF do_ipc_transfer_non_null_cte_wp_at])
       apply (erule PUC)
       apply (clarsimp )
       apply (erule PimpQ)
       apply (drule PNN, clarsimp)
      apply (erule cte_wp_at_weakenE)
      apply (clarsimp)
      done
  qed


lemma thread_set_cap_to:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb)
  \<Longrightarrow> \<lbrace>ex_nonz_cap_to p\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  apply (clarsimp simp add: ex_nonz_cap_to_def)
  apply (wpsimp wp: hoare_vcg_ex_lift thread_set_cte_wp_at_trivial
    | fast)+
  done


lemma thread_set_has_no_reply_cap:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb)
  \<Longrightarrow> \<lbrace>\<lambda>s. \<not>has_reply_cap tt s\<rbrace> thread_set f t \<lbrace>\<lambda>_ s. \<not>has_reply_cap tt s\<rbrace>"
  apply (clarsimp simp add: has_reply_cap_def)
  apply (wpsimp wp: hoare_vcg_all_lift thread_set_cte_wp_at_trivial
    | fast)+
  done

lemma (in Systemcall_AI_Pre) handle_fault_reply_cte_wp_at:
  "\<lbrace>\<lambda>s :: 'state_ext state. P (cte_wp_at P' p s)\<rbrace>
     handle_fault_reply f t d dl
   \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  proof -
    have SC:
      "\<And>p' s tcb nc. get_tcb p' s = Some tcb
       \<Longrightarrow> obj_at (same_caps (TCB (tcb \<lparr>tcb_arch := arch_tcb_context_set nc (tcb_arch tcb)\<rparr>))) p' s"
      apply (drule get_tcb_ko_at [THEN iffD1])
      apply (erule ko_at_weakenE)
      apply (clarsimp simp add: tcb_cap_cases_def)
      done
    have NC:
      "\<And>p' s tcb P nc. get_tcb p' s = Some tcb
      \<Longrightarrow> cte_wp_at P p (s\<lparr>kheap := (kheap s)(p' \<mapsto> TCB (tcb\<lparr>tcb_arch := arch_tcb_context_set nc (tcb_arch tcb)\<rparr>))\<rparr>)
          = cte_wp_at P p s"
      apply (drule_tac nc=nc in SC)
      apply (drule_tac P=P and p=p in cte_wp_at_after_update)
      apply (drule sym)
      apply (clarsimp)
      apply (rule_tac x="s \<lparr> kheap := p \<rparr>" for p in arg_cong)
      apply (clarsimp)
      done
    show ?thesis
      apply (case_tac f; clarsimp simp: as_user_def)
       apply (wp set_object_wp thread_get_wp' | simp add: split_def NC | wp (once) hoare_drop_imps)+
      done
  qed


lemma (in Systemcall_AI_Pre) handle_fault_reply_has_no_reply_cap:
  "\<lbrace>\<lambda>s :: 'state_ext state. \<not>has_reply_cap t s\<rbrace> handle_fault_reply f t d dl \<lbrace>\<lambda>_ s. \<not>has_reply_cap t s\<rbrace>"
  apply (clarsimp simp add: has_reply_cap_def)
  apply (wpsimp wp: hoare_vcg_all_lift handle_fault_reply_cte_wp_at)
  done

crunches refill_unblock_check
  for pred_tcb[wp]: "\<lambda>s. P (pred_tcb_at f Q t s)"
  (wp: crunch_wps hoare_vcg_if_lift2)

lemmas si_invs[wp] = si_invs'[where Q=\<top>,OF hoare_TrueI hoare_TrueI hoare_TrueI hoare_TrueI,simplified]

locale Systemcall_AI_Pre2 = Systemcall_AI_Pre itcb_state state_ext_t +
                            Systemcall_AI_Pre itcb_fault state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself"
begin

lemma do_reply_invs[wp]:
  "\<lbrace>tcb_at t and reply_at r and invs\<rbrace>
   do_reply_transfer t r g
   \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wpsimp wp: handle_timeout_Timeout_invs hoare_vcg_all_lift hoare_drop_imps
                    refill_unblock_check_invs get_tcb_obj_ref_wp)
           apply (wpsimp wp: gts_wp)
          apply (rule_tac Q = "\<lambda>_ s. invs s" in hoare_strengthen_post[rotated])
           apply (clarsimp simp: pred_tcb_at_def obj_at_def runnable_eq)
          apply (wpsimp wp: sts_invs_minor2)+
              apply (intro conjI impI)
               apply (wpsimp wp: thread_set_cap_to
                                 thread_set_no_change_tcb_state
                                 thread_set_pred_tcb_at_sets_true gts_wp
                                 get_simple_ko_wp thread_get_fault_wp
                                 hoare_vcg_all_lift
                           simp: ran_tcb_cap_cases)+
          apply (simp flip: cases_imp_eq imp_conjL not_None_eq)
          apply (wpsimp wp: hoare_drop_imps)
         apply wpsimp
        apply (wpsimp wp: hoare_drop_imps reply_remove_invs)
       apply (clarsimp cong: conj_cong)
       apply (wpsimp wp: gts_wp get_simple_ko_wp)+
  apply (clarsimp simp: reply_tcb_reply_at_def obj_at_def pred_tcb_at_def is_tcb is_reply)
  apply (frule invs_valid_idle)
  apply (fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def live_def
                 intro!: if_live_then_nonz_cap_invs)
  done

lemma pinv_invs[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> ct_active s \<and> valid_invocation i s \<and>
        scheduler_action s = resume_cur_thread\<rbrace>
     perform_invocation blocking call can_donate i
   \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (cases i
         ; wpsimp wp: tcbinv_invs send_signal_interrupt_states invoke_domain_invs
                simp: ct_in_state_def)
   apply (auto simp: invs_def valid_state_def valid_pspace_def cur_sc_tcb_def pred_tcb_at_def
                     obj_at_def sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[symmetric]
                     if_live_then_nonz_capD2 live_def)
  done

end

lemma do_reply_transfer_typ_at[wp]:
  "do_reply_transfer s r g \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  unfolding do_reply_transfer_def
  by (wpsimp wp: gts_wp hoare_vcg_if_lift2 hoare_drop_imps hoare_vcg_all_lift split_del: if_split)

crunch typ_at[wp]: invoke_irq_handler "\<lambda>s. P (typ_at T p s)"


locale Syscall_AI = Systemcall_AI_Pre:Systemcall_AI_Pre _ state_ext_t
                  + Systemcall_AI_Pre2 state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself" +
  assumes invoke_irq_control_typ_at[wp]:
    "\<And>P T p irq_inv.
      \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace> invoke_irq_control irq_inv \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  assumes obj_refs_cap_rights_update[simp]:
    "\<And>rs cap. obj_refs (cap_rights_update rs cap) = obj_refs cap"
  assumes table_cap_ref_mask_cap:
    "\<And>R cap. table_cap_ref (mask_cap R cap) = table_cap_ref cap"
  assumes eq_no_cap_to_obj_with_diff_ref:
    "\<And>cap p (s::'state_ext state) S.
      \<lbrakk> cte_wp_at ((=) cap) p s; valid_arch_caps s \<rbrakk>
        \<Longrightarrow> no_cap_to_obj_with_diff_ref cap S s"
  assumes hv_invs[wp]:
    "\<And>t' flt. \<lbrace>invs :: 'state_ext state \<Rightarrow> bool\<rbrace> handle_vm_fault t' flt \<lbrace>\<lambda>r. invs\<rbrace>"
  assumes handle_vm_fault_valid_fault[wp]:
    "\<And>thread ft.
      \<lbrace>\<top>::'state_ext state \<Rightarrow> bool\<rbrace> handle_vm_fault thread ft -,\<lbrace>\<lambda>rv s. valid_fault rv\<rbrace>"
  assumes hvmf_st_tcb_at[wp]:
    "\<And>t w N P t'.
      handle_vm_fault t w \<lbrace>\<lambda>s::'state_ext state. N (st_tcb_at P t' s)\<rbrace>"
  assumes hvmf_ex_cap[wp]:
    "\<And>p t b.
      \<lbrace>ex_nonz_cap_to p::'state_ext state \<Rightarrow> bool\<rbrace> handle_vm_fault t b \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  assumes hh_invs[wp]:
  "\<And>thread fault.
    \<lbrace>invs and ct_active and st_tcb_at active thread and ex_nonz_cap_to thread\<rbrace>
      handle_hypervisor_fault thread fault
    \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_fault_msg_cur_thread[wp]:
    "\<And>ft t P. make_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. P (cur_thread s)\<rbrace>"
  assumes make_fault_msg_cur_sc[wp]:
    "\<And>ft t P. make_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. P (cur_sc s)\<rbrace>"
  assumes make_fault_msg_fault_tcb_at[wp]:
    "\<And>ft t t' P. make_fault_msg ft t \<lbrace>fault_tcb_at P t' :: 'state_ext state \<Rightarrow> _\<rbrace>"


context Syscall_AI begin

lemma pinv_tcb[wp]:
  "\<And>tptr blocking call can_donate i.
    \<lbrace>\<lambda>s. invs s \<and> st_tcb_at active tptr s \<and> ct_active s \<and> valid_invocation i s \<and>
         scheduler_action s = resume_cur_thread\<rbrace>
    perform_invocation blocking call can_donate i
    \<lbrace>\<lambda>rv. tcb_at tptr :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (case_tac i, simp_all split:option.splits)
             apply (wpsimp simp: st_tcb_at_tcb_at)+
            apply ((wpsimp wp: tcb_at_typ_at simp: st_tcb_at_tcb_at)+)[3]
         apply ((wpsimp simp: st_tcb_at_tcb_at)+)[5]
    apply ((simp add: tcb_at_typ, wpsimp simp: st_tcb_at_tcb_at tcb_at_typ[symmetric])+)[2]
  apply (wpsimp wp: invoke_arch_tcb)
  done

end


lemmas sts_typ_at = set_thread_state_typ_at [where P="\<lambda>x. x"]

lemma cte_wp_cdt_lift:
  assumes c: "\<And>P. \<lbrace>cte_wp_at P p\<rbrace> f \<lbrace>\<lambda>r. cte_wp_at P p\<rbrace>"
  assumes m: "\<And>P. \<lbrace>\<lambda>s. P (cdt s)\<rbrace> f \<lbrace>\<lambda>r s. P (cdt s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. cte_wp_at (P (cdt s)) p s\<rbrace> f \<lbrace>\<lambda>r s. cte_wp_at (P (cdt s)) p s\<rbrace>"
  apply (clarsimp simp add: valid_def)
  apply (frule_tac P1="(=) (cdt s)" in use_valid [OF _  m], rule refl)
  apply simp
  apply (erule use_valid [OF _ c])
  apply simp
  done

lemma sts_cte_wp_cdt [wp]:
  "\<lbrace>\<lambda>s. cte_wp_at (P (cdt s)) p s\<rbrace>
  set_thread_state t st
  \<lbrace>\<lambda>rv s. cte_wp_at (P (cdt s)) p s\<rbrace>"
  by (rule cte_wp_cdt_lift; wp)

lemma sts_nasty_bit:
  shows
  "\<lbrace>\<lambda>s. \<forall>r\<in>obj_refs cap. \<forall>a b. ptr' \<noteq> (a, b) \<and> cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') (a, b) s
              \<longrightarrow> cte_wp_at (Not \<circ> is_zombie) (a, b) s \<and> \<not> is_zombie cap\<rbrace>
     set_thread_state t st
   \<lbrace>\<lambda>rv s. \<forall>r\<in>obj_refs cap. \<forall>a b. ptr' \<noteq> (a, b) \<and> cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') (a, b) s
              \<longrightarrow> cte_wp_at (Not \<circ> is_zombie) (a, b) s \<and> \<not> is_zombie cap\<rbrace>"
  apply (intro hoare_vcg_const_Ball_lift hoare_vcg_all_lift)
  apply (wpsimp wp: hoare_vcg_const_Ball_lift hoare_vcg_all_lift
            hoare_vcg_imp_lift hoare_vcg_disj_lift valid_cte_at_neg_typ
          | simp add: cte_wp_at_neg2[where P="\<lambda>c. x \<in> obj_refs c" for x])+
  apply (clarsimp simp: o_def cte_wp_at_def)
  done

lemma sts_no_cap_asid[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     set_thread_state t st
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  by (simp add: no_cap_to_obj_with_diff_ref_def
                cte_wp_at_caps_of_state, wp)

lemma sts_mcpriority_tcb_at[wp]:
  "\<lbrace>mcpriority_tcb_at P t\<rbrace> set_thread_state p ts \<lbrace>\<lambda>rv. mcpriority_tcb_at P t\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp | simp)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (drule get_tcb_SomeD)
  apply clarsimp
  done

lemma sts_mcpriority_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. mcpriority_tcb_at P (cur_thread s) s\<rbrace> set_thread_state p ts \<lbrace>\<lambda>rv s. mcpriority_tcb_at P (cur_thread s) s\<rbrace>"
  apply wp_pre
  by (wpsimp | wps)+

lemma option_None_True: "case_option (\<lambda>_. True) f x = (\<lambda>s. \<forall>y. x = Some y \<longrightarrow> f y s)"
  by (cases x; simp)

lemma option_None_True_const: "case_option True f x = (\<forall>y. x = Some y \<longrightarrow> f y)"
  by (cases x; simp)

(* FIXME: move *)
lemma hoare_case_option_lift:
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (E rv = None \<longrightarrow> P rv s) \<and> (\<forall>x2. E rv = Some x2 \<longrightarrow> Q rv x2 s) \<rbrace> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv. case_option (P rv) (\<lambda>rv'. Q rv rv') (E rv)\<rbrace>"
  by (fastforce simp: valid_def split: option.splits)

crunches set_thread_state
  for cur_time[wp]: "\<lambda>s. P (cur_time s)"

lemma sts_tcb_inv_wf [wp]:
  "\<lbrace>tcb_inv_wf i and K (\<not> ipc_queued_thread_state st)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. tcb_inv_wf i\<rbrace>"
  apply (case_tac i)
  apply (wpsimp wp: set_thread_state_bound_sc_tcb_at sts_st_tcb_at_cases
                    set_thread_state_valid_cap hoare_vcg_all_lift
                    hoare_vcg_const_imp_lift sts_st_tcb_at_cases_strong
              simp: option_None_True option_None_True_const
         | wp sts_obj_at_impossible
         | wp hoare_case_option_lift hoare_vcg_imp_lift
         | wps
         | clarsimp simp: pred_conj_def split: option.splits)+
  done

lemma sts_valid_sched_context_inv[wp]:
  "\<lbrace>valid_sched_context_inv i and K (\<not> ipc_queued_thread_state st)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv. valid_sched_context_inv i\<rbrace>"
  apply (cases i; wpsimp split: cap.splits; (intro conjI)?)
  by (wpsimp wp: sts_obj_at_impossible set_thread_state_bound_sc_tcb_at hoare_vcg_imp_lift
                    sts_st_tcb_at_cases_strong hoare_case_option_wp
           simp: pred_conj_def
    | wps)+

lemma sts_valid_cnode_inv[wp]:
  "\<lbrace>valid_cnode_inv i\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_cnode_inv i\<rbrace>"
  by (cases i
      ; wpsimp wp: sts_nasty_bit[where ptr'="(p_a, p_b)" for p_a p_b, simplified]
                   hoare_vcg_const_imp_lift)

declare sts_arch_irq_control_inv_valid[wp]

lemma sts_irq_control_inv_valid[wp]:
  "\<lbrace>irq_control_inv_valid i\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. irq_control_inv_valid i\<rbrace>"
  by (cases i; wpsimp)

lemma sts_irq_handler_inv_valid[wp]:
  "\<lbrace>irq_handler_inv_valid i\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. irq_handler_inv_valid i\<rbrace>"
  by (cases i; wpsimp wp: hoare_vcg_ex_lift)

declare sts_valid_arch_inv[wp]

lemma sts_valid_inv[wp]:
  "\<lbrace>valid_invocation i and K (\<not> ipc_queued_thread_state st)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_invocation i\<rbrace>"
  by (cases i; wpsimp)


lemma sts_Restart_stay_simple:
  "\<lbrace>st_tcb_at simple t\<rbrace>
     set_thread_state t' Structures_A.Restart
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (rule hoare_pre)
   apply (wp sts_st_tcb_at_cases)
  apply simp
  done

lemma decode_inv_inv[wp]:
  notes if_split [split del]
  shows
  "\<lbrace>P\<rbrace> decode_invocation first_phase label args cap_index slot cap excaps buffer \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (case_tac cap, simp_all add: decode_invocation_def)
          apply (wp decode_tcb_inv_inv decode_domain_inv_inv
                    decode_sched_context_inv_inv decode_sched_control_inv_inv
                      | rule conjI | clarsimp
                      | simp split: bool.split)+
  done

lemma ex_cte_cap_wp_to_cnode_real_cte:
  "ex_cte_cap_wp_to is_cnode_cap slot s \<Longrightarrow> valid_objs s \<Longrightarrow> real_cte_at slot s"
  apply (clarsimp simp add: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule (1) caps_of_state_valid_cap)
  apply (case_tac cap; clarsimp simp: valid_cap_simps)
  done

lemma cnode_eq_strg:
  "(\<exists>ptr. cte_wp_at ((=) cap) ptr s)
    \<longrightarrow> (is_cnode_cap cap \<longrightarrow> (\<forall>ref \<in> cte_refs cap (interrupt_irq_node s).
                                    ex_cte_cap_wp_to is_cnode_cap ref s))"
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  by (intro exI, erule cte_wp_at_weakenE, simp)

declare invs_valid_arch_capsI[elim!]

context Syscall_AI begin

lemma decode_inv_wf[wp]:
  "\<lbrace>valid_cap cap and invs and cte_wp_at ((=) cap) slot
           and real_cte_at slot
           and ex_cte_cap_to slot
           and case_option \<top> in_user_frame buffer
           and (\<lambda>s::'state_ext state. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
           and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>cte_refs (fst cap) (interrupt_irq_node s). ex_cte_cap_to r s)
           and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x))
           and (\<lambda>s. \<forall>x \<in> set excaps. \<forall>r\<in>zobj_refs (fst x). ex_nonz_cap_to r s)
           and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. ex_cte_cap_wp_to is_cnode_cap (snd x) s)\<rbrace>
     decode_invocation first_phase label args cap_index slot cap excaps buffer
   \<lbrace>valid_invocation\<rbrace>,-"
  apply (simp add: decode_invocation_def cong: cap.case_cong if_cong split del: if_split)
  apply (wpsimp wp: decode_tcb_inv_wf decode_domain_inv_wf[simplified split_def]
                    decode_sched_context_inv_wf decode_sched_control_inv_wf
              simp: o_def uncurry_def split_def invs_valid_objs invs_valid_global_refs
          simp_del: is_cnode_cap.simps cte_refs.simps)
  apply (strengthen cnode_eq_strg)
  apply (cases slot)
  apply (rule_tac V="\<forall>x \<in> set excaps. real_cte_at (snd x) s
                                      \<and> cte_wp_at ((=) (fst x)) (snd x) s"
           in revcut_rl
         , fastforce elim: valid_cap_wellformed
                           ex_cte_cap_wp_to_cnode_real_cte)
  apply (intro conjI allI impI ballI
         ; clarsimp simp: cte_wp_at_eq_simp valid_cap_def[of cap] valid_cap_simps
         ; fastforce elim: cte_wp_at_weakenE ex_cte_cap_wp_to_weakenE
                   intro!: eq_no_cap_to_obj_with_diff_ref)
  done

end

lemma lcs_valid [wp]:
  "\<lbrace>invs\<rbrace> lookup_cap_and_slot t xs \<lbrace>\<lambda>x s. s \<turnstile> fst x\<rbrace>, -"
  unfolding lookup_cap_and_slot_def
  apply (rule hoare_pre)
   apply (wp|clarsimp simp: split_def)+
  done

lemma lec_valid_cap [wp]:
  "\<lbrace>invs\<rbrace> lookup_extra_caps t xa mi \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. s \<turnstile> fst x)\<rbrace>, -"
  unfolding lookup_extra_caps_def
  by (wpsimp wp: mapME_set)

lemma lcs_ex_cap_to [wp]:
  "\<lbrace>invs\<rbrace> lookup_cap_and_slot t xs \<lbrace>\<lambda>x s. \<forall>r\<in>cte_refs (fst x) (interrupt_irq_node s). ex_cte_cap_to r s\<rbrace>, -"
  unfolding lookup_cap_and_slot_def by wpsimp

lemma lcs_ex_nonz_cap_to [wp]:
  "\<lbrace>invs\<rbrace> lookup_cap_and_slot t xs \<lbrace>\<lambda>x s. \<forall>r\<in>zobj_refs (fst x). ex_nonz_cap_to r s\<rbrace>, -"
  unfolding lookup_cap_and_slot_def by wpsimp

lemma lcs_cte_at[wp]:
  "\<lbrace>valid_objs\<rbrace> lookup_cap_and_slot t xs \<lbrace>\<lambda>rv. cte_at (snd rv)\<rbrace>,-"
  apply (simp add: lookup_cap_and_slot_def split_def)
  apply (wp | simp)+
  done

lemma lcs_real_cte_at[wp]:
  "\<lbrace>valid_objs\<rbrace> lookup_cap_and_slot t xs \<lbrace>\<lambda>rv. real_cte_at (snd rv)\<rbrace>,-"
  by (wpsimp simp: lookup_cap_and_slot_def split_def)

lemma lec_ex_cap_to [wp]:
  "\<lbrace>invs\<rbrace>
  lookup_extra_caps t xa mi
  \<lbrace>\<lambda>rv s. (\<forall>cap \<in> set rv. \<forall>r\<in>cte_refs (fst cap) (interrupt_irq_node s). ex_cte_cap_to r s)\<rbrace>, -"
  unfolding lookup_extra_caps_def
  by (wp mapME_set | simp)+

lemma lec_ex_nonz_cap_to [wp]:
  "\<lbrace>invs\<rbrace>
  lookup_extra_caps t xa mi
  \<lbrace>\<lambda>rv s. (\<forall>cap \<in> set rv. \<forall>r\<in>zobj_refs (fst cap). ex_nonz_cap_to r s)\<rbrace>, -"
  unfolding lookup_extra_caps_def
  by (wp mapME_set | simp)+

lemma lookup_extras_real_ctes[wp]:
  "\<lbrace>valid_objs\<rbrace> lookup_extra_caps t xs info \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. real_cte_at (snd x) s\<rbrace>,-"
  apply (simp add: lookup_extra_caps_def
              split del: if_split)
  apply (rule hoare_pre)
   apply (wp mapME_set)
      apply (simp add: lookup_cap_and_slot_def split_def)
      apply (wp case_options_weak_wp mapM_wp'
                 | simp add: load_word_offs_word_def)+
  done

lemma lookup_extras_ctes[wp]:
  "\<lbrace>valid_objs\<rbrace> lookup_extra_caps t xs info \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_at (snd x) s\<rbrace>,-"
  apply (rule hoare_post_imp_R)
   apply (rule lookup_extras_real_ctes)
  apply (simp add: real_cte_at_cte)
  done

lemma lsft_ex_cte_cap_to:
  "\<lbrace>invs and K (\<forall>cap. is_cnode_cap cap \<longrightarrow> P cap)\<rbrace>
     lookup_slot_for_thread t cref
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to P (fst rv) s\<rbrace>,-"
  apply (simp add: lookup_slot_for_thread_def)
  apply (wp rab_cte_cap_to)
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (frule cte_wp_at_tcbI[where t="(t', tcb_cnode_index 0)" and P="(=) v" for t' v, simplified])
    apply fastforce
   apply fastforce
  apply (intro exI, erule cte_wp_at_weakenE)
  apply clarsimp
  done

(* FIXME: move / generalize lemma in GenericLib *)
lemma mapME_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>E\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapME f xs \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>E\<rbrace>"
  apply (induct xs)
   apply (simp add: mapME_def sequenceE_def)
   apply wp
  apply (simp add: mapME_Cons)
  apply (wpsimp wp: x|assumption)+
  done

lemmas mapME_wp' = mapME_wp [OF _ subset_refl]

(* FIXME: move to CSpace_R *)
lemma resolve_address_bits_valid_fault:
  "\<lbrace> valid_objs and valid_cap (fst param)\<rbrace>
   resolve_address_bits param
   \<lbrace>\<lambda>_. valid_objs\<rbrace>,
   \<lbrace>\<lambda>f s. valid_fault (ExceptionTypes_A.fault.CapFault x y f)\<rbrace>"
unfolding resolve_address_bits_def
proof (induct param rule: resolve_address_bits'.induct)
  case (1 cap cref)
  show ?case
    apply (clarsimp simp: validE_R_def validE_def valid_def  split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (split cap.splits)
              defer 6 (* cnode *)
              apply (simp_all add: spec_validE_def validE_def valid_def
                         throwError_def return_def valid_fault_def)[13]
    apply (simp only: split: cap.splits if_split_asm)
     apply (simp add: fail_def)
    apply (simp only: K_bind_def in_bindE)
    apply (elim conjE exE disjE)
        apply ((clarsimp simp: whenE_def bindE_def bind_def lift_def liftE_def
                    throwError_def returnOk_def return_def valid_fault_def
                    valid_cap_def2 wellformed_cap_def word_bits_def
                  split: if_split_asm cap.splits)+)[4]
    apply (split if_split_asm)
     apply (clarsimp simp: whenE_def bindE_def bind_def lift_def liftE_def
                throwError_def returnOk_def return_def valid_fault_def
                valid_cap_def2 wellformed_cap_def
              split: if_split_asm cap.splits)
    apply (simp only: K_bind_def in_bindE)
    apply (elim conjE exE disjE)
     apply (clarsimp simp: whenE_def bindE_def bind_def lift_def liftE_def
                throwError_def returnOk_def return_def valid_fault_def
                valid_cap_def2 wellformed_cap_def
              split: if_split_asm cap.splits)
    apply (split if_split_asm)
     apply (frule (8) "1.hyps")
     apply (clarsimp simp add: validE_def valid_def whenE_def bindE_def
               bind_def lift_def liftE_def throwError_def
               returnOk_def return_def valid_fault_def
             split: if_split_asm cap.splits sum.splits)
     apply (frule in_inv_by_hoareD [OF get_cap_inv])
     apply simp
     apply (frule (1) post_by_hoare [OF get_cap_valid])
     apply (erule_tac x=s in allE, erule impE, simp)
     apply (drule (1) bspec, clarsimp)
    apply (clarsimp simp add: returnOk_def return_def)
    apply (frule in_inv_by_hoareD [OF get_cap_inv])
    apply (clarsimp simp: whenE_def bindE_def bind_def throwError_def
                          returnOk_def return_def
                    split: if_split_asm cap.splits sum.splits)
    done
qed

lemma resolve_address_bits_valid_fault2:
  "\<lbrace>invs and valid_cap (fst param)\<rbrace>
   resolve_address_bits param
   -,\<lbrace>\<lambda>f s. valid_fault (ExceptionTypes_A.fault.CapFault x y f)\<rbrace>"
  apply (cut_tac resolve_address_bits_valid_fault[of param x y])
  apply (clarsimp simp add: validE_E_def validE_def valid_def
                  split: sum.splits)
  apply (drule invs_valid_objs)
  apply fastforce
  done

lemma lookup_cap_and_slot_valid_fault:
  "\<lbrace>valid_objs\<rbrace> lookup_cap_and_slot thread cptr
   \<lbrace>\<lambda>_. valid_objs\<rbrace>,
   \<lbrace>\<lambda>ft s. valid_fault (ExceptionTypes_A.CapFault (of_bl cptr) rp ft)\<rbrace>"
  apply (simp add: lookup_cap_and_slot_def split_def lookup_slot_for_thread_def
         | wp resolve_address_bits_valid_fault)+
  apply (clarsimp simp: objs_valid_tcb_ctable)
  done

lemma lookup_cap_and_slot_valid_fault2[wp]:
  "\<lbrace>invs\<rbrace> lookup_cap_and_slot thread p
   -,\<lbrace>\<lambda>ft s. valid_fault (ExceptionTypes_A.CapFault (of_bl p) rp ft)\<rbrace>"
  using lookup_cap_and_slot_valid_fault
  apply (clarsimp simp add: validE_E_def validE_def valid_def
                  split: sum.splits)
  apply (drule invs_valid_objs)
  apply fastforce
  done

lemma lec_valid_fault:
  "\<lbrace>valid_objs\<rbrace>
   lookup_extra_caps thread buffer info
   \<lbrace>\<lambda>_. valid_objs\<rbrace>,\<lbrace>\<lambda>rv s. valid_fault rv\<rbrace>"
  apply (simp add: lookup_extra_caps_def split del: if_split)
  apply (wp mapME_wp' lookup_cap_and_slot_valid_fault)
  done

lemma lec_valid_fault2[wp]:
  "\<lbrace>invs\<rbrace> lookup_extra_caps thread buffer info -,\<lbrace>\<lambda>rv s. valid_fault rv\<rbrace>"
  apply (cut_tac lec_valid_fault[of thread buffer info])
  apply (clarsimp simp add: validE_E_def validE_def valid_def
                  split: sum.splits )
  apply (drule invs_valid_objs)
  apply fastforce
  done

lemma lec_caps_to[wp]:
  "\<lbrace>invs and K (\<forall>cap. is_cnode_cap cap \<longrightarrow> P cap)\<rbrace> lookup_extra_caps t buffer info
   \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. ex_cte_cap_wp_to P (snd x) s)\<rbrace>,-"
  apply (simp add: lookup_extra_caps_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp mapME_set)
      apply (simp add: lookup_cap_and_slot_def split_def)
      apply (wp lsft_ex_cte_cap_to mapM_wp'
                    | simp add: load_word_offs_word_def | wpc)+
  done

lemma get_cap_int_derived[wp]:
  "\<lbrace>\<top>\<rbrace> get_cap slot \<lbrace>\<lambda>rv. cte_wp_at (interrupt_derived rv) slot\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state interrupt_derived_def)
  done

lemma lec_derived[wp]:
  "\<lbrace>invs\<rbrace>
     lookup_extra_caps t buffer info
   \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. cte_wp_at (interrupt_derived (fst x)) (snd x) s)\<rbrace>,-"
  apply (simp add: lookup_extra_caps_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp mapME_set)
      apply (simp add: lookup_cap_and_slot_def split_def)
      apply (wp | simp)+
  done

lemma lookup_cap_and_slot_cte_wp_at_P:
  assumes P: "\<And>s ref cap. P s \<Longrightarrow> caps_of_state s ref = Some cap \<Longrightarrow> Q cap cap"
  shows "\<lbrace>P\<rbrace> lookup_cap_and_slot thread cptr \<lbrace>\<lambda>x. cte_wp_at (Q (fst x)) (snd x)\<rbrace>, -"
  apply (simp add: lookup_cap_and_slot_def split_def)
  apply (wp get_cap_wp)
   apply (rule hoare_post_imp_R [where Q'="\<lambda>_. P"], wp)
   apply (clarsimp simp: cte_wp_at_caps_of_state P)
  apply simp
  done

lemma lookup_cap_and_slot_eq [wp]:
  "\<lbrace>\<top>\<rbrace> lookup_cap_and_slot thread cptr \<lbrace>\<lambda>rv. cte_wp_at ((=) (fst rv)) (snd rv)\<rbrace>, -"
  by (simp add: lookup_cap_and_slot_cte_wp_at_P)

lemma lookup_extra_caps_eq [wp]:
  "\<lbrace>\<top>\<rbrace> lookup_extra_caps thread xb info \<lbrace>\<lambda>rv s. \<forall>x\<in>set rv. cte_wp_at ((=) (fst x)) (snd x) s\<rbrace>,-"
  by (wpsimp simp: lookup_extra_caps_def wp: mapME_set)

(*FIXME: move to Nondet_VCG.valid_validE_R *)
lemma valid_validE_R_gen:
  "\<lbrakk>\<And>rv s. Q' (Inr rv) s \<Longrightarrow> Q rv s; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -"
  by (fastforce simp: validE_R_def validE_def valid_def split_def)

lemma valid_validE_R_eq:
  "\<lbrakk>Q = Q'\<circ>Inr; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -"
  by (fastforce simp: validE_R_def validE_def valid_def split_def)


crunch tcb_at[wp]: reply_from_kernel "tcb_at t"
  (simp: crunch_simps)

crunch pred_tcb_at[wp]: reply_from_kernel "pred_tcb_at proj P t"
  (simp: crunch_simps)

crunch cap_to[wp]: reply_from_kernel "ex_nonz_cap_to p"
  (simp: crunch_simps)

crunch it[wp]: reply_from_kernel "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps)

crunch cte_wp_at[wp]: reply_from_kernel "cte_wp_at P p"
  (simp: crunch_simps)


lemma ts_Restart_case_helper:
  "(case ts of Structures_A.Restart \<Rightarrow> A | _ \<Rightarrow> B)
 = (if ts = Structures_A.Restart then A else B)"
  by (case_tac ts, simp_all)


lemma lcs_ex_cap_to2[wp]:
  "\<lbrace>invs and K (\<forall>cap. is_cnode_cap cap \<longrightarrow> P cap)\<rbrace>
      lookup_cap_and_slot t cref \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P (snd rv)\<rbrace>,-"
  apply (rule hoare_pre)
   apply (simp add: lookup_cap_and_slot_def split_def)
   apply (wp lsft_ex_cte_cap_to | simp)+
  done

(* FIXME AARCH64: this should really not be wp *)
declare hoare_vcg_const_imp_lift_E[wp]

context Syscall_AI begin

(* This lemma will probably be proved as part of the update to liveness coming.
   When that update comes this can either be deleted or proven and moved to
   Invariants_AI.*)
lemma cur_sc_tcb_invs:
  "invs s \<and> scheduler_action s = resume_cur_thread
   \<Longrightarrow> bound_sc_tcb_at (\<lambda>a. \<exists>y. a = Some y) (cur_thread s) s"
  by (clarsimp simp: invs_def valid_state_def valid_pspace_def cur_sc_tcb_def pred_tcb_at_def
                     obj_at_def sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[symmetric])

lemma stsa_schedulable_scheduler_action:
  "\<lbrace>\<lambda>s. P (scheduler_action s) \<and>
        schedulable thread s\<rbrace>
   set_thread_state_act thread
   \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  apply (simp add: set_thread_state_act_def)
  apply (rule hoare_seq_ext[OF _ hoare_gets_sp])+
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (simp add: when_def)
  apply (intro conjI)
   apply (wpsimp wp: hoare_pre_cont)
  apply wpsimp
  done

lemma sts_schedulable_scheduler_action:
  "\<lbrace>\<lambda>s. P (scheduler_action s) \<and>
        schedulable thread s\<rbrace>
   set_thread_state thread Restart
  \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  apply (wpsimp wp: stsa_schedulable_scheduler_action set_object_wp simp: set_thread_state_def)
  apply (fastforce simp: schedulable_def is_sc_active_def get_tcb_def
                         in_release_queue_def
                  split: option.splits kernel_object.splits)
  done

lemma hinv_invs':
  fixes Q :: "'state_ext state \<Rightarrow> bool" and calling blocking
  assumes perform_invocation_Q[wp]:
    "\<And>block class can_donate i.
      \<lbrace>invs and Q and ct_active and (\<lambda>s. scheduler_action s = resume_cur_thread)
       and valid_invocation i\<rbrace>
        perform_invocation block class can_donate i
      \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes handle_fault_Q[wp]:
    "\<And>t f.
      \<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t and (\<lambda>_. valid_fault f)\<rbrace>
        handle_fault t f
      \<lbrace>\<lambda>r. Q\<rbrace>"
  assumes reply_from_kernel_Q[wp]:
    "\<And>a b. \<lbrace>invs and Q\<rbrace> reply_from_kernel a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]:
    "\<And>a b. \<lbrace>invs and Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  shows
    "\<lbrace>invs and Q and (\<lambda>s. scheduler_action s = resume_cur_thread) and
      ct_schedulable\<rbrace>
       handle_invocation calling blocking can_donate first_phase cptr
     \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc)
  apply (wpsimp wp: syscall_valid sts_invs_minor2 rfk_invs split_del: if_split)+
         apply (rule_tac Q = "\<lambda>st. st_tcb_at ((=) st) thread and (invs and Q)" in
                hoare_post_imp)
          apply (auto elim!: pred_tcb_weakenE st_tcb_ex_cap
                            fault_tcbs_valid_states_not_fault_tcb_states
                      dest: st_tcb_at_idle_thread invs_fault_tcbs_valid_states
                      simp: st_tcb_at_tcb_at pred_neg_def)[1]
         apply (wpsimp wp: gts_sp)+
       apply (simp add: ct_in_state_def conj_commute conj_left_commute)
       apply (wpsimp wp: sts_schedulable_scheduler_action)
       apply (rule_tac Q = "\<lambda>rv s. st_tcb_at active thread s \<and> cur_thread s = thread" in
              hoare_post_imp)
        apply simp
       apply (wpsimp)
      apply (simp only: simp_thms K_def if_apply_def2)
      apply (rule hoare_vcg_E_elim)
       apply (wpsimp wp: decode_inv_inv simp: if_apply_def2)+
  apply (auto simp: ct_in_state_def cur_sc_tcb_invs fault_tcbs_valid_states_active schedulable_def'
              dest: invs_fault_tcbs_valid_states
              elim: st_tcb_ex_cap)
  done

lemmas hinv_invs[wp] = hinv_invs'
  [where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI,simplified]

lemma get_cap_reg_inv[wp]: "\<lbrace>P\<rbrace> get_cap_reg r \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: get_cap_reg_def)

lemma hs_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. scheduler_action s = resume_cur_thread) and ct_schedulable\<rbrace>
   handle_send blocking
   \<lbrace>\<lambda>_. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule validE_valid)
  apply (simp add: handle_send_def whenE_def)
  apply (wp | simp add: tcb_at_invs)+
  done

end

lemma ex_nonz_cap_to_tcb_strg:
  "(\<exists>cref. cte_wp_at (\<lambda>cap. is_thread_cap cap \<and> p \<in> zobj_refs cap) cref s)
       \<longrightarrow> ex_nonz_cap_to p s"
  by (fastforce simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state)

lemma ex_tcb_cap_to_tcb_at_strg:
  "ex_nonz_cap_to p s \<and> tcb_at p s \<and> valid_objs s \<longrightarrow>
   (\<exists>cref. cte_wp_at (\<lambda>cap. is_thread_cap cap \<and> p \<in> zobj_refs cap) cref s)"
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state
                        zobj_refs_to_obj_refs)
  apply (drule(1) caps_of_state_valid_cap[rotated])
  apply (drule(2) valid_cap_tcb_at_tcb_or_zomb)
  apply fastforce
  done

lemma invs_valid_tcb_ctable_strengthen:
  "invs s \<longrightarrow> ((\<exists>y. get_tcb thread s = Some y) \<longrightarrow>
               invs s \<and> s \<turnstile> tcb_ctable (the (get_tcb thread s)))"
  by (clarsimp simp: invs_valid_tcb_ctable)

context Syscall_AI begin

crunches lookup_reply
  for invs[wp]: invs
  and pred_tcb_at[wp]: "pred_tcb_at proj' P t"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"

lemma lookup_reply_valid_fault[wp]:
  "\<lbrace>invs\<rbrace> lookup_reply -, \<lbrace>\<lambda>rv _. valid_fault rv\<rbrace>"
  apply (simp add: lookup_reply_def lookup_cap_def lookup_slot_for_thread_def)
  apply (wpsimp wp: hoare_drop_imps resolve_address_bits_valid_fault2
              simp: valid_fault_def)+
  apply (frule invs_cur)
  apply (auto simp: cur_tcb_def tcb_at_def invs_valid_tcb_ctable)
  done

lemma lookup_reply_ex_cap[wp]:
  "\<lbrace>\<top>\<rbrace> lookup_reply \<lbrace>\<lambda>rv s. \<forall>r\<in>zobj_refs rv. ex_nonz_cap_to r s\<rbrace>,-"
  apply (simp add: lookup_reply_def )
  apply (wpsimp wp: hoare_drop_imps)
  done

crunches lookup_reply
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

lemma hw_invs[wp]:
  "\<lbrace>invs and ct_active\<rbrace>
     handle_recv is_blocking can_reply
   \<lbrace>\<lambda>r. invs\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
             cong: if_cong split del: if_split)
  apply (wpsimp wp: get_sk_obj_ref_wp hoare_vcg_ball_lift)
     apply (rule hoare_vcg_E_elim)
      apply (simp add: lookup_cap_def lookup_slot_for_thread_def)
      apply wp
       apply (simp add: split_def)
       apply (wp resolve_address_bits_valid_fault2)+
     apply (simp add: valid_fault_def)
     apply ((wp hoare_vcg_all_lift_R lookup_cap_ex_cap
          | simp add: obj_at_def
          | simp add: conj_disj_distribL ball_conj_distrib
          | wp (once) hoare_drop_imps)+)
  apply (simp add: ct_in_state_def cur_sc_tcb_invs)
  apply (fastforce elim!: invs_valid_tcb_ctable st_tcb_ex_cap)
  done

end

crunch tcb_at[wp]: lookup_reply, handle_recv "tcb_at t"
  (wp: crunch_wps simp: crunch_simps)

lemma sts_st_tcb_at_pred:
  "\<lbrace>K (t = t' \<and> Q (P ts)) \<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv s. Q (st_tcb_at P t' s)\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule sts_st_tcb_at)
   apply simp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma null_cap_on_failure_wp[wp]:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv. Q cap.NullCap\<rbrace>"
  shows      "\<lbrace>P\<rbrace> null_cap_on_failure f \<lbrace>Q\<rbrace>"
  unfolding ncof_is_a_catch
  by (wp x)

crunch_ignore (add:null_cap_on_failure)

lemma hy_invs[wp]: "handle_yield \<lbrace>invs\<rbrace>"
  apply (simp add: handle_yield_def)
  apply (wpsimp wp: charge_budget_invs)
  done

declare hoare_seq_ext[wp] hoare_vcg_precond_imp [wp_comb]

lemma ct_active_simple [elim!]:
  "ct_active s \<Longrightarrow> st_tcb_at simple (cur_thread s) s"
  by (fastforce simp: ct_in_state_def elim!: pred_tcb_weakenE)

lemma active_from_running:
  "ct_running  s  \<Longrightarrow> ct_active  s"
  by (clarsimp elim!: pred_tcb_weakenE
               simp: ct_in_state_def)+

crunch cur_thread[wp]: set_extra_badge "\<lambda>s. P (cur_thread s)"

crunch cur_sc[wp]: set_extra_badge "\<lambda>s. P (cur_sc s)"

lemmas cap_delete_one_st_tcb_at_simple[wp] =
    cap_delete_one_st_tcb_at[where P=simple, simplified]

lemma simple_if_Restart_Inactive:
  "simple (if P then Structures_A.Restart else Structures_A.Inactive)"
  by simp

crunch (in Syscall_AI) vo[wp]: handle_fault_reply "valid_objs :: 'state_ext state \<Rightarrow> _"

lemmas handle_fault_reply_typ_ats[wp] =
    abs_typ_at_lifts [OF handle_fault_reply_typ_at]

lemma tcb_state_If_valid[simp]:
  "valid_tcb_state (if P then Structures_A.Restart else Structures_A.Inactive)
      = \<top>"
  by (rule ext, simp add: valid_tcb_state_def)

lemma drop_when_dxo_wp: "(\<And>f s. P (trans_state f s) = P s ) \<Longrightarrow> \<lbrace>P\<rbrace> when b (do_extended_op e) \<lbrace>\<lambda>_.P\<rbrace>"
  apply (clarsimp simp add: when_def)
  apply (wp | simp)+
  done

crunch ex_nonz_cap_to[wp]: handle_timeout "ex_nonz_cap_to p"
  (wp: crunch_wps thread_set_cap_to simp: crunch_simps ran_tcb_cap_cases)

context Syscall_AI begin

lemma do_reply_transfer_nonz_cap:
  "\<lbrace>\<lambda>s :: 'state_ext state. ex_nonz_cap_to p s\<rbrace>
     do_reply_transfer sender reply grant
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  by (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift get_tcb_obj_ref_wp
                 thread_set_cap_to gts_wp
           simp: ran_tcb_cap_cases
      | rule conjI)+

lemma hc_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. scheduler_action s = resume_cur_thread) and ct_schedulable\<rbrace>
   handle_call
   \<lbrace>\<lambda>_. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  by (simp add: handle_call_def) wpsimp

end
(* FIXME: move *) (* FIXME: should we add this to the simpset? *)
lemma select_insert:
  "select (insert x X) = (return x \<sqinter> select X)"
  by (simp add: alternative_def select_def return_def)

lemma update_time_stamp_ct_in_release_queue [wp]:
  "update_time_stamp
   \<lbrace>\<lambda>s. P (in_release_queue (cur_thread s) s)\<rbrace>"
  by (wpsimp simp: update_time_stamp_def do_machine_op_def
                   is_sc_active_def get_tcb_def in_release_queue_def
            split: option.splits)

lemma update_time_stamp_invs[wp]:
  "update_time_stamp \<lbrace>invs\<rbrace>"
  by (wpsimp simp: update_time_stamp_def)

crunches update_time_stamp
  for valid_objs[wp]: valid_objs
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and sc_refills_sc_at[wp]: "sc_refills_sc_at P sc_ptr"
  and cur_sc_tcb[wp]: cur_sc_tcb
  and pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at p P t s)"
  and pred_tcb_at_ct[wp]: "\<lambda>s. Q (pred_tcb_at proj P (cur_thread s) s)"
  and schact[wp]: "\<lambda>s. P (scheduler_action s)"
  and ct[wp]: "\<lambda>s. P (cur_thread s)"
  and ct_active[wp]: "ct_active"
  and ct_running[wp]: ct_running
  (wp: hoare_drop_imps simp: crunch_simps do_machine_op_def cur_sc_tcb_def ct_in_state_def)

crunches preemption_point
  for valid_objs[wp]: valid_objs
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and pspace_no_overlap[wp]: "pspace_no_overlap S"
  and cte_wp_at[wp]: "cte_wp_at P p"
  and cur_sc_tcb[wp]: cur_sc_tcb
  and invs[wp]: invs
  (rule: preemption_point_inv simp: cur_sc_tcb_def ignore_del: preemption_point)

lemma update_time_stamp_ct_schedulable[wp]:
  "update_time_stamp \<lbrace>ct_schedulable\<rbrace>"
  by (wpsimp simp: schedulable_def' in_release_queue_def
               wp: hoare_vcg_ex_lift update_time_stamp_wp)

crunches thread_set
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"

crunches reply_from_kernel
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and ct_in_state[wp]: "ct_in_state P"
  (rule: ct_in_state_thread_state_lift)

crunches update_time_stamp, check_budget_restart
  for ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"
  (wp: hoare_drop_imps simp: crunch_simps)

context Syscall_AI begin

crunches check_budget_restart, handle_fault_reply, reply_remove
  for cur_thread[wp]: "\<lambda>s :: 'state_ext state. P (cur_thread s)"
  (wp: transfer_caps_loop_pres mapM_wp' hoare_drop_imps
   simp: crunch_simps)

crunches check_budget_restart
  for cur_sc[wp]: "\<lambda>s :: 'state_ext state. P (cur_sc s)"
  (wp: transfer_caps_loop_pres mapM_wp' hoare_drop_imps
   simp: crunch_simps)

crunches
  possible_switch_to, do_ipc_transfer, maybe_donate_sc, handle_fault_reply, postpone,
  if_cond_refill_unblock_check
  for ct_in_state[wp]: "ct_in_state P :: 'state_ext state \<Rightarrow> _"
  (rule: ct_in_state_thread_state_lift wp: crunch_wps simp: crunch_simps)

lemma update_waiting_ntfn_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  by (wpsimp wp: set_thread_state_ct_in_state hoare_drop_imps)

lemma send_signal_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     send_signal ntfnptr badge
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: send_signal_def)
  by (wpsimp wp: set_thread_state_ct_in_state hoare_drop_imps)

crunches reply_push
  for ct_active[wp]: "ct_active :: 'state_ext state \<Rightarrow> _"
  (wp: sts_ctis_neq crunch_wps simp: crunch_simps)

lemma send_ipc_not_cur_ct_active[wp]:
  "\<lbrace>\<lambda>s. ct_active s \<and> thread \<noteq> cur_thread s\<rbrace>
     send_ipc block call badge can_grant can_reply_grant can_donate thread epptr
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac ep; simp)
    apply (wpsimp wp: set_thread_state_ct_st)
   apply (wpsimp wp: set_thread_state_ct_st)
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (wpsimp wp: set_thread_state_ct_st hoare_drop_imps hoare_vcg_all_lift
         | rule conjI)+
  done

lemma send_fault_ipc_ct_active_for_timeout[wp]:
  "\<lbrace>\<lambda>s. ct_active s \<and> tptr \<noteq> cur_thread s\<rbrace>
     send_fault_ipc tptr ep f can_donate
   \<lbrace>\<lambda>_.  ct_active :: 'state_ext state \<Rightarrow> _\<rbrace>"
   apply (clarsimp simp: send_fault_ipc_def)
  by (wpsimp simp: send_fault_ipc_def wp: thread_set_ct_in_state)

lemma handle_timeout_ct_active[wp]:
  "\<lbrace>\<lambda>s. ct_active s \<and> tptr \<noteq> cur_thread s\<rbrace>
     handle_timeout tptr f
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> _\<rbrace>"
  by (wpsimp simp: handle_timeout_def)

lemma do_reply_transfer_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace>
     do_reply_transfer sender reply grant
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  apply (wpsimp wp: set_thread_state_ct_st hoare_vcg_all_lift hoare_drop_imps
                    get_tcb_obj_ref_wp gts_wp | rule conjI)+
              apply (wpsimp wp: thread_set_ct_in_state hoare_vcg_all_lift gts_wp
                                get_simple_ko_wp)+
  apply (auto simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma send_ipc_not_blocking_not_calling_ct_active[wp]:
  "\<lbrace>ct_active and fault_tcb_at ((=) None) t\<rbrace>
     send_ipc False False bdg cg crg can_donate t epptr
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac ep; simp)
    apply wpsimp
   apply wpsimp
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (wpsimp wp: set_thread_state_ct_st hoare_drop_imp wp_del: reply_push_ct_active)+
            apply (rule hoare_pre_cont)
           apply (rule hoare_pre_cont)
          apply (wpsimp wp: hoare_drop_imp)
         apply (wpsimp wp: thread_get_wp')
        apply (rule_tac Q="\<lambda>_. ct_active and fault_tcb_at ((=) None) t"
               in hoare_post_imp)
         apply (clarsimp simp: pred_tcb_at_def obj_at_def)
        apply (wpsimp wp: hoare_drop_imps)+
  done

crunches retype_region, create_cap, reset_untyped_cap
  for cur_thread[wp]: "\<lambda>s :: 'state_ext state. P (cur_thread s)"
  (simp: crunch_simps wp: mapME_x_inv_wp preemption_point_inv crunch_wps)

crunches create_cap, set_cap
  for ct_in_state[wp]: "ct_in_state P :: 'state_ext state \<Rightarrow> _"
  (wp: ct_in_state_thread_state_lift mapME_x_inv_wp preemption_point_inv crunch_wps)

lemma reset_untyped_cap_ct_in_state[wp]:
  "\<lbrace>\<lambda>s. ct_in_state P s \<and>
     cte_wp_at (\<lambda>cp. cur_thread s \<notin> cap_range cp \<and> is_untyped_cap cp) src_slot s\<rbrace>
     reset_untyped_cap src_slot
   \<lbrace>\<lambda>_. ct_in_state P :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: reset_untyped_cap_def)
  by (wpsimp wp: mapME_x_inv_wp preemption_point_inv hoare_drop_imps get_cap_wp
         | fastforce simp: ct_in_state_def cte_wp_at_caps_of_state bits_of_def is_cap_simps)+

lemma retype_region_ct_in_state:
  "\<lbrace>\<lambda>(s::'state_ext::state_ext state). pspace_no_overlap_range_cover ptr' sz s
          \<and> ct_in_state P s \<and> range_cover ptr' sz (obj_bits_api ty us) n
          \<and> valid_objs s \<and> pspace_aligned s\<rbrace>
     retype_region ptr' n us ty dev \<lbrace>\<lambda>rv. ct_in_state P\<rbrace>"
  apply (wpsimp wp: ct_in_state_thread_state_lift' retype_region_st_tcb_at[where sz=sz])
   apply assumption
  apply clarsimp
  done

lemma invoke_untyped_ct_active[wp]:
  "\<lbrace>invs and valid_untyped_inv ui and ct_active and
    (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q,
    (wp init_arch_objects_wps | simp)+)
     apply (rule hoare_name_pre_state, clarsimp)
     apply (wp retype_region_ct_in_state; auto)
    apply wpsimp+
  apply (cases ui, clarsimp simp: ct_in_state_def)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply fastforce
  apply (drule ex_nonz_cap_to_overlap,
    ((simp add:cte_wp_at_caps_of_state descendants_range_def2
            empty_descendants_range_in)+))
  done

crunches test_possible_switch_to, sched_context_resume, if_cond_refill_unblock_check
  for cur_thread[wp]: "\<lambda>s :: 'state_ext state. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunches
  sched_context_bind_tcb, sched_context_unbind_tcb, sched_context_yield_to
  for ct_in_state: "ct_in_state P :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps ct_in_state_thread_state_lift ignore: set_tcb_obj_ref
   simp: crunch_simps)

crunches invoke_domain, invoke_sched_context
  for ct_in_state[wp]: "ct_in_state P :: 'state_ext state \<Rightarrow> _"
  (wp: crunch_wps simp: crunch_simps)

fun
  safe_invocation :: "invocation \<Rightarrow> bool"
where
  "safe_invocation (InvokeCNode cnode_inv)     = False"
| "safe_invocation (InvokeTCB tcb_inv)         = False"
| "safe_invocation (InvokeSchedControl sc_inv) = False"
| "safe_invocation (InvokeSchedContext _) = False"
| "safe_invocation (InvokeDomain _ _) = False"
| "safe_invocation _ = True"

lemma perform_invocation_not_blocking_not_calling_ct_active[wp]:
  "\<lbrace>invs and ct_active and valid_invocation i and
    (\<lambda>s. fault_tcb_at ((=) None) (cur_thread s) s \<and>
         scheduler_action s = resume_cur_thread) and
    K (safe_invocation i)\<rbrace>
     perform_invocation False False can_donate i
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_gen_asm)
  by (cases i; wpsimp)

lemma decode_invocation_safe_invocation[wp]:
  "\<lbrace>\<top>\<rbrace>
     decode_invocation True label args cap_index slot cap excaps buffer
   \<lbrace>\<lambda>i _. safe_invocation i\<rbrace>,-"
  apply (simp add: decode_invocation_def)
  by (wpsimp simp: o_def split_def)

lemma handle_invocation_not_blocking_not_calling_first_phase_ct_active[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> ct_active s \<and> scheduler_action s = resume_cur_thread \<and>
        ct_schedulable s\<rbrace>
     handle_invocation False False can_donate True cptr
   \<lbrace>\<lambda>_. ct_active :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (simp add: handle_invocation_def split_def ts_Restart_case_helper)
  apply (wpsimp wp: syscall_valid set_thread_state_ct_st hoare_drop_imps
                    set_thread_state_pred_tcb_at sts_schedulable_scheduler_action
         | wps)+
  apply (auto simp: ct_in_state_def fault_tcbs_valid_states_active
              dest: invs_fault_tcbs_valid_states
              elim: st_tcb_ex_cap)
  done

lemma he_invs[wp]:
  "\<And>e.
    \<lbrace>\<lambda>s. invs s \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s) \<and>
         scheduler_action s = resume_cur_thread \<and>
         (ct_running s \<longrightarrow> ct_schedulable s)\<rbrace>
    handle_event e
    \<lbrace>\<lambda>_. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (case_tac e, simp_all)
       apply (rename_tac syscall)
       apply (case_tac syscall, simp_all)
                 by (wpsimp wp: hoare_vcg_imp_conj_lift' check_budget_restart_true
                          comb: hoare_drop_imps hoare_drop_imp_conj'
                          simp: if_apply_def2 valid_fault_def
                     | wps | erule active_from_running
                     | fastforce simp: tcb_at_invs ct_in_state_def valid_fault_def
                                elim!: st_tcb_ex_cap dest: active_from_running)+

end

(* Lemmas related to preservation of runnability over handle_recv for woken threads
   these are presently unused, but have proven useful in the past *)
context notes if_cong[cong] begin

lemma complete_signal_sym_refsf:
  "complete_signal ntfnc t \<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<rbrace>"
  unfolding complete_signal_def
  apply (rule hoare_pre)
   apply (wpsimp wp: get_simple_ko_wp maybe_donate_sc_sym_refs hoare_vcg_all_lift hoare_drop_imps)
  apply clarsimp
  apply (rename_tac ntfn badge)
  apply (subgoal_tac " get_refs NTFNBound (ntfn_bound_tcb ntfn) \<union>
                       get_refs NTFNSchedContext (ntfn_sc ntfn) = state_refs_of s ntfnc")
   apply (clarsimp simp: if_apply_def2 split: if_splits if_split_asm)
   subgoal by (subst eq_commute, auto cong: if_cong)
  apply (clarsimp simp: state_refs_of_def obj_at_def)
  done

lemma do_nbrecv_failed_transfer_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s) \<rbrace> do_nbrecv_failed_transfer t \<lbrace>\<lambda>rv s. P (state_refs_of s) \<rbrace>"
  unfolding do_nbrecv_failed_transfer_def
  apply (rule hoare_pre)
   apply (wp get_simple_ko_wp | wpc | simp)+
  done

lemma fast_finalise_sym_refs:
  "\<lbrace>\<lambda>s. invs s \<and> (\<exists>slot. cte_wp_at ((=) cap) slot s)\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>y s. sym_refs (state_refs_of s)\<rbrace>"
  by (strengthen invs_sym_refs, rule fast_finalise_invs)

crunch state_refs_of[wp]: empty_slot "\<lambda>s. P (state_refs_of s)"
  (wp: crunch_wps simp: crunch_simps interrupt_update.state_refs_update)

lemma reply_unlink_runnable[wp]:
  "\<lbrace>st_tcb_at runnable t'\<rbrace> reply_unlink_tcb t rptr \<lbrace>\<lambda>rv. st_tcb_at runnable t'\<rbrace>"
  apply (rule hoare_strengthen_pre_via_assert_backward[of "st_tcb_at (Not \<circ> runnable) t", rotated]
         , wpsimp wp: reply_unlink_tcb_st_tcb_at simp: pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp, OF hoare_gen_asm_conj])
  apply (rule hoare_weaken_pre[where Q=\<bottom>])
  by (auto simp: pred_tcb_at_def obj_at_def)

(* FIXME: move; this should be much higher up *)
lemma in_get_refs:
  "((p', r') \<in> get_refs r p) = (r' = r \<and> p = Some p')"
  by (auto simp: get_refs_def split: option.splits)

lemma runnable_not_queued:
  "\<lbrakk> st_tcb_at runnable t s; ko_at (Endpoint (RecvEP qs)) epptr s; t \<in> set qs;
     sym_refs (state_refs_of s) \<rbrakk>
  \<Longrightarrow> False"
  apply (frule st_tcb_at_state_refs_ofD)
  apply (frule (1) sym_refs_ko_atD)
  apply (clarsimp simp: obj_at_def)
  apply (drule (1) bspec)
  apply (clarsimp simp: state_refs_of_def in_get_refs)
  apply (auto simp: runnable_eq)
  done

lemma send_ipc_st_tcb_at_runnable:
  "\<lbrace>st_tcb_at runnable t and (\<lambda>s. sym_refs (state_refs_of s)) and K (thread \<noteq> t) \<rbrace>
   send_ipc block call badge can_grant can_grant_reply can_donate thread epptr
   \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  unfolding send_ipc_def
  supply if_split[split del]
  apply (wpsimp wp: sts_st_tcb_at_other get_tcb_obj_ref_wp hoare_vcg_all_lift hoare_vcg_if_lift
                    reply_unlink_runnable get_simple_ko_wp | wp (once) hoare_drop_imp)+
  apply (auto dest: runnable_not_queued)
  done

lemma send_fault_ipc_st_tcb_at_runnable:
  "\<lbrace>st_tcb_at runnable t and (\<lambda>s. sym_refs (state_refs_of s)) and tcb_at t' and K (t' \<noteq> t)\<rbrace>
   send_fault_ipc t' handler_cap fault can_donate \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  unfolding send_fault_ipc_def
  apply (rule hoare_pre, wp)
     apply wpc
                apply (wp send_ipc_st_tcb_at_runnable thread_set_no_change_tcb_state thread_set_refs_trivial
                          hoare_vcg_all_lift_R thread_get_wp
                        | clarsimp
                        | wp (once) hoare_drop_imps)+
  done

lemma handle_fault_st_tcb_at_runnable:
  "\<lbrace>st_tcb_at runnable t and invs and K (t' \<noteq> t) \<rbrace>
    handle_fault t' x \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: handle_fault_def handle_no_fault_def)
  apply (wpsimp simp: unless_when wp: sts_st_tcb_at_other send_fault_ipc_st_tcb_at_runnable)
  apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def is_tcb)
  done

end (* Lemmas related to preservation of runnability over handle_recv for woken threads *)

end
