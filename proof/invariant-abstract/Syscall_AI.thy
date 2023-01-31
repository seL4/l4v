(* Copyright 2014, General Dynamics C4 Systems
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
  arch_decode_invocation_tainv
  lookup_cap_and_slot_tainv
  data_to_cptr_def
  arch_post_cap_deletion_cur_thread
  arch_post_cap_deletion_state_refs_of
  arch_invoke_irq_handler_typ_at
  resetTimer_device_state_inv
end

lemmas [wp] =
  arch_decode_invocation_tainv
  lookup_cap_and_slot_tainv

lemmas [simp] =
  data_to_cptr_def

crunch inv[wp]: ethread_get, ethread_get_when P

lemma schedule_invs[wp]: "\<lbrace>invs\<rbrace> (Schedule_A.schedule :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_split[split del]
  apply (simp add: Schedule_A.schedule_def)
  apply (wp dmo_invs thread_get_inv gts_wp
            do_machine_op_tcb when_def hoare_vcg_all_lift
          | wpc
          | clarsimp simp: guarded_switch_to_def get_tcb_def choose_thread_def ethread_get_def
                           ethread_get_when_def
          | wp (once) hoare_drop_imps
          | simp add: schedule_choose_new_thread_def if_apply_def2)+
  sorry (* FIXME: Broken by experimental-tpspec. -robs
  done
  *)

lemma schedule_choose_new_thread_ct_activatable[wp]:
  "\<lbrace> invs \<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>_. ct_in_state activatable \<rbrace>"
  proof -
  have P: "\<And>t s. ct_in_state activatable (cur_thread_update (\<lambda>_. t) s) = st_tcb_at activatable t s"
    by (fastforce simp: ct_in_state_def st_tcb_at_def intro: obj_at_pspaceI)
  show ?thesis
  unfolding schedule_choose_new_thread_def choose_thread_def guarded_switch_to_def
    apply (simp add: P set_scheduler_action_def guarded_switch_to_def choose_thread_def
                             next_domain_def Let_def tcb_sched_action_def set_tcb_queue_def
                             get_tcb_queue_def ethread_get_def bind_assoc)
    apply (wpsimp wp: stt_activatable stit_activatable gts_wp touch_object_wp')+
    sorry (* FIXME: Broken by experimental-tpspec. -robs
    apply (force simp: ct_in_state_def pred_tcb_at_def obj_at_def invs_def valid_state_def
                       valid_idle_def split: if_split_asm)+
  done
  *)
qed

lemma guarded_switch_to_ct_in_state_activatable[wp]:
  "\<lbrace>\<top>\<rbrace> guarded_switch_to t \<lbrace>\<lambda>a. ct_in_state activatable\<rbrace>"
  unfolding guarded_switch_to_def
  apply (wp stt_activatable)
  apply (wp hoare_vcg_imp_lift gts_wp touch_object_wp)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma schedule_ct_activateable[wp]:
  "\<lbrace>invs\<rbrace> (Schedule_A.schedule :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. ct_in_state activatable\<rbrace>"
  apply (simp add: Schedule_A.schedule_def)
  apply wp
      apply wpc
        (* resume current thread *)
        apply wp
       prefer 2
       (* choose new thread *)
       apply wp
      (* switch to thread *)
      apply wpsimp
              apply (simp add: set_scheduler_action_def)
              apply (simp | wp gts_wp touch_object_wp | wp (once) hoare_drop_imps)+
  apply (frule invs_valid_idle)
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def valid_idle_def)
  done

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
| "valid_invocation (InvokeTCB i) = Tcb_AI.tcb_inv_wf i"
| "valid_invocation (InvokeDomain thread domain) = (tcb_at thread and (\<lambda>s. thread \<noteq> idle_thread s))"
| "valid_invocation (InvokeReply thread slot grant) =
       (tcb_at thread and cte_wp_at (\<lambda>cap. \<exists> R. cap = ReplyCap thread False R) slot)"
| "valid_invocation (InvokeIRQControl i) = irq_control_inv_valid i"
| "valid_invocation (InvokeIRQHandler i) = irq_handler_inv_valid i"
| "valid_invocation (InvokeCNode i) = valid_cnode_inv i"
| "valid_invocation (InvokeArchObject i) = valid_arch_inv i"


(* TODO: Check if this is still needed for lookup_cap_and_slot,
   as the "crunch inv" for it was deleted on mainline. -robs *)
crunch inv_ta [wp]: lookup_cap_and_slot "ignore_ta P"

lemma sts_Restart_invs[wp]:
  "\<lbrace>st_tcb_at active t and invs and ex_nonz_cap_to t\<rbrace>
     set_thread_state t Structures_A.Restart
   \<lbrace>\<lambda>rv. invs\<rbrace>"

  apply (wp sts_invs_minor2)
  apply (auto elim!: pred_tcb_weakenE
           notE [rotated, OF _ idle_no_ex_cap]
           simp: invs_def valid_state_def valid_pspace_def)
  done

lemma invoke_tcb_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_tcb i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_tcb_typ_at [where P=id, simplified])

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

crunch pred_tcb_at[wp]: handle_fault_reply "pred_tcb_at proj (P :: 'a \<Rightarrow> _) t :: 'state_ext state \<Rightarrow> _"
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

lemma do_ipc_transfer_emptyable[wp]:
  "\<lbrace>emptyable sl\<rbrace> do_ipc_transfer sender ep badge grant receiver \<lbrace>\<lambda>_. emptyable sl\<rbrace>"
  apply (clarsimp simp add: emptyable_def)
  apply (wp hoare_convert_imp | clarsimp)+
  done

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
  apply (wpsimp wp: hoare_ex_wp thread_set_cte_wp_at_trivial
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
      "\<And>p' s tcb nc. get_tcb True p' s = Some tcb
       \<Longrightarrow> obj_at (same_caps (TCB (tcb \<lparr>tcb_arch := arch_tcb_context_set nc (tcb_arch tcb)\<rparr>))) p' s"
      apply (drule get_tcb_ko_atD)
      apply (erule ko_at_weakenE)
      apply (clarsimp simp add: tcb_cap_cases_def)
      done
    have NC:
      "\<And>p' s tcb P nc. get_tcb True p' s = Some tcb
      \<Longrightarrow> cte_wp_at P p (s\<lparr>kheap := kheap s(p' \<mapsto> TCB (tcb\<lparr>tcb_arch := arch_tcb_context_set nc (tcb_arch tcb)\<rparr>))\<rparr>)
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
        apply (wp set_object_wp thread_get_wp' touch_object_wp' | simp add: split_def NC | wp (once) hoare_drop_imps)+
         sorry (* FIXME: broken by touched-addrs -robs
      done
    *)
  qed


lemma (in Systemcall_AI_Pre) handle_fault_reply_has_no_reply_cap:
  "\<lbrace>\<lambda>s :: 'state_ext state. \<not>has_reply_cap t s\<rbrace> handle_fault_reply f t d dl \<lbrace>\<lambda>_ s. \<not>has_reply_cap t s\<rbrace>"
  apply (clarsimp simp add: has_reply_cap_def)
  apply (wpsimp wp: hoare_vcg_all_lift handle_fault_reply_cte_wp_at)
  done

locale Systemcall_AI_Pre2 = Systemcall_AI_Pre itcb_state state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself"

lemma (in Systemcall_AI_Pre2) do_reply_invs[wp]:
  "\<lbrace>tcb_at t and tcb_at t' and cte_wp_at (is_reply_cap_to t) slot and
    invs\<rbrace>
     do_reply_transfer t' t slot grant
   \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def is_reply_cap_to_def)
  apply (wp | wpc |simp)+
        apply (wp sts_invs_minor)
       apply (clarsimp)
       apply (wp cap_delete_one_st_tcb_at)
       apply (rule_tac Q = "\<lambda>_. invs and if_live_then_nonz_cap and
                                st_tcb_at awaiting_reply t and
                                (\<lambda>s. \<not>has_reply_cap t s)" in
              hoare_strengthen_post[rotated])
        apply (clarsimp)
        apply (rule conjI, erule(1) st_tcb_ex_cap, clarsimp)
        apply (rule conjI)
         apply (clarsimp simp add: invs_def valid_state_def valid_idle_def)
         apply (drule st_tcb_at_eq, erule pred_tcb_weaken_strongerE, simp)
         apply (clarsimp)
        apply (rule disjI1)
        apply (erule pred_tcb_weakenE)
        apply (clarsimp)
       apply (rule_tac Q = "\<lambda>_. invs and st_tcb_at awaiting_reply t and
                           (\<lambda>s. \<not>has_reply_cap t s)" in
              hoare_strengthen_post[rotated], clarsimp)
       apply (wp cap_delete_one_reply_st_tcb_at cap_delete_one_deletes_reply | simp)+
      apply (rule_tac Q = "\<lambda>_. valid_reply_caps and
                          cte_wp_at (is_reply_cap_to t) slot" in
             hoare_strengthen_post[rotated], clarsimp)
       apply (erule cte_wp_at_weakenE, simp)
      apply (wp)
      apply (rule do_ipc_transfer_non_null_cte_wp_at2, clarsimp simp add: is_reply_cap_to_def)
      apply (clarsimp simp: is_cap_simps is_reply_cap_to_def)
     apply (wp sts_invs_minor | simp split del: if_split)+
          apply (wp sts_invs_minor thread_set_no_change_tcb_state)
           apply (clarsimp)
          apply (clarsimp)
          apply (rule conjI)
           apply (clarsimp)
           apply (wp thread_set_cap_to thread_set_it |
                  clarsimp simp add: tcb_cap_cases_def)+
           apply (rule_tac Q = "\<lambda>_. invs and st_tcb_at awaiting_reply t and
                               (\<lambda>s. \<not>has_reply_cap t s)" in
                  hoare_strengthen_post[rotated])
            apply (clarsimp)
            apply (erule pred_tcb_weakenE)
            apply (clarsimp)
           apply (wp thread_set_invs_trivial thread_set_no_change_tcb_state
                     thread_set_has_no_reply_cap | clarsimp simp add: tcb_cap_cases_def)+
         apply (rule_tac Q = "\<lambda>_. st_tcb_at (\<lambda>s. tcb_st_refs_of s = {}) t and invs and
                             st_tcb_at awaiting_reply t and (\<lambda>s. \<not>has_reply_cap t s)" in
                hoare_strengthen_post[rotated])
          apply (clarsimp)
          apply (rule conjI)
           apply (erule(1) st_tcb_ex_cap'[where P=awaiting_reply])
           apply (clarsimp)
          apply (clarsimp simp add: invs_def valid_state_def valid_idle_def)
          apply (drule st_tcb_at_eq, erule pred_tcb_weaken_strongerE, simp)
          apply clarsimp
         apply (wp handle_fault_reply_has_no_reply_cap)
     apply (rule_tac Q = "\<lambda>_. st_tcb_at awaiting_reply t and invs and
                         (\<lambda>s. \<not>has_reply_cap t s)" in hoare_strengthen_post[rotated])
      apply (clarsimp)
      apply (erule pred_tcb_weakenE)
      apply (clarsimp)
     apply (wp cap_delete_one_deletes_reply cap_delete_one_reply_st_tcb_at)+
    apply (clarsimp)
    sorry (* FIXME: broken by touched-addrs -robs
    apply (wp hoare_drop_imp hoare_allI)[1]
   apply (wp assert_wp)
  apply (clarsimp)
  apply (rule_tac Q = "\<lambda>rv. st_tcb_at ((=) rv) t and tcb_at t' and invs and
                      emptyable slot and
                      cte_wp_at (is_reply_cap_to t) slot" in
         hoare_strengthen_post[rotated])
   apply (clarsimp simp add: st_tcb_at_tcb_at)
   apply (rule conjI, erule pred_tcb_weakenE, clarsimp)+
   apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule conjI, erule pred_tcb_weakenE, clarsimp)
   apply (assumption)
  apply (wp gts_sp)
   apply (clarsimp simp add:is_reply_cap_to_def)+
   apply (erule emptyable_cte_wp_atD)
    apply (clarsimp simp add: invs_def valid_state_def is_master_reply_cap_def)+
  done
*)


lemmas si_invs[wp] = si_invs'[where Q=\<top>,OF hoare_TrueI hoare_TrueI hoare_TrueI hoare_TrueI,simplified]

lemma (in Systemcall_AI_Pre2) pinv_invs[wp]:
  "\<lbrace>invs and ct_active and valid_invocation i\<rbrace>
    perform_invocation blocking call i \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (case_tac i, simp_all)
       apply (wp tcbinv_invs send_signal_interrupt_states invoke_domain_invs
         | clarsimp simp:ct_in_state_def is_reply_cap_to_def
         | erule st_tcb_ex_cap
         | fastforce simp:ct_in_state_def is_reply_cap_to_def | rule conjI)+
  done

lemma get_mrs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> get_mrs param_a param_b param_c \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  sorry (* FIXME: broken by touched-addrs -robs *)

crunch typ_at[wp]: do_reply_transfer "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imps)

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
  assumes hvmf_active:
    "\<And>t w.
      \<lbrace>st_tcb_at active t::'state_ext state \<Rightarrow> bool\<rbrace> handle_vm_fault t w \<lbrace>\<lambda>rv. st_tcb_at active t\<rbrace>"
  assumes hvmf_ex_cap[wp]:
    "\<And>p t b.
      \<lbrace>ex_nonz_cap_to p::'state_ext state \<Rightarrow> bool\<rbrace> handle_vm_fault t b \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  assumes hh_invs[wp]:
  "\<And>thread fault.
    \<lbrace>invs and ct_active and st_tcb_at active thread and ex_nonz_cap_to thread\<rbrace>
      handle_hypervisor_fault thread fault
    \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_fault_msg_cur_thread[wp]:
    "\<And>ft t. make_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. P (cur_thread s)\<rbrace>"




context Syscall_AI begin

lemma pinv_tcb[wp]:
  "\<And>tptr blocking call i.
    \<lbrace>invs and st_tcb_at active tptr and ct_active and valid_invocation i\<rbrace>
      perform_invocation blocking call i
    \<lbrace>\<lambda>rv. tcb_at tptr :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (case_tac i, simp_all split:option.splits,
    (wp invoke_arch_tcb
              | simp | clarsimp elim!: st_tcb_at_tcb_at
              | wp (once) tcb_at_typ_at)+
    )
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

crunch is_original_cap[wp]: set_thread_state "\<lambda>s. P (is_original_cap s)"
  (wp: touch_object_wp')

lemma sts_no_cap_asid[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     set_thread_state t st
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  by (simp add: no_cap_to_obj_with_diff_ref_def
                cte_wp_at_caps_of_state, wp)

lemma sts_mcpriority_tcb_at[wp]:
  "\<lbrace>mcpriority_tcb_at P t\<rbrace> set_thread_state p ts \<lbrace>\<lambda>rv. mcpriority_tcb_at P t\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp touch_object_wp' | simp)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (drule get_tcb_SomeD')
  apply clarsimp
  done

lemma sts_mcpriority_tcb_at_ct[wp]:
  "\<lbrace>\<lambda>s. mcpriority_tcb_at P (cur_thread s) s\<rbrace> set_thread_state p ts \<lbrace>\<lambda>rv s. mcpriority_tcb_at P (cur_thread s) s\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp touch_object_wp' | simp)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (drule get_tcb_SomeD')
  apply clarsimp
  done


lemma sts_tcb_inv_wf [wp]:
  "\<lbrace>tcb_inv_wf i\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. tcb_inv_wf i\<rbrace>"
  apply (case_tac i)
  (* long-running *)
  by (wp set_thread_state_valid_cap hoare_vcg_all_lift hoare_vcg_const_imp_lift
         | simp add: tcb_at_typ split: option.split
         | safe
         | wp sts_obj_at_impossible)+


lemma sts_valid_inv[wp]:
  "\<lbrace>valid_invocation i\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_invocation i\<rbrace>"
  by (cases i; wpsimp simp: sts_valid_untyped_inv sts_valid_arch_inv;
      rename_tac i'; case_tac i'; simp;
      wpsimp wp: set_thread_state_valid_cap sts_nasty_bit
                 sts_nasty_bit[where ptr'="(p_a, p_b)" for p_a p_b, simplified]
                 hoare_vcg_const_imp_lift hoare_vcg_ex_lift;
      auto)

lemma sts_Restart_stay_simple:
  "\<lbrace>st_tcb_at simple t\<rbrace>
     set_thread_state t' Structures_A.Restart
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (rule hoare_pre)
   apply (wp sts_st_tcb_at_cases)
  apply simp
  done

lemma decode_inv_tainv[wp]:
  notes if_split [split del]
  shows
  "\<lbrace>ignore_ta P\<rbrace> decode_invocation label args cap_index slot cap excaps \<lbrace>\<lambda>rv. ignore_ta P\<rbrace>"
  apply (case_tac cap, simp_all add: decode_invocation_def,
    (wpsimp wp: decode_tcb_inv_tainv decode_domain_inv_inv)+)
  done

lemma cnode_eq_strg:
  "(\<exists>ptr. cte_wp_at ((=) cap) ptr s)
    \<longrightarrow> (is_cnode_cap cap \<longrightarrow> (\<forall>ref \<in> cte_refs cap (interrupt_irq_node s).
                                    ex_cte_cap_wp_to is_cnode_cap ref s))"
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  by (intro exI, erule cte_wp_at_weakenE, simp)


lemma invs_valid_arch_caps[elim!]:
  "invs s \<Longrightarrow> valid_arch_caps s"
  by (clarsimp simp: invs_def valid_state_def)


context Syscall_AI begin

lemma decode_inv_wf[wp]:
  "\<lbrace>valid_cap cap and invs and cte_wp_at ((=) cap) slot
           and real_cte_at slot
           and ex_cte_cap_to slot
           and (\<lambda>s::'state_ext state. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
           and (\<lambda>s. \<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_to r s)
           and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>cte_refs (fst cap) (interrupt_irq_node s). ex_cte_cap_to r s)
           and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x))
           and (\<lambda>s. \<forall>x \<in> set excaps. \<forall>r\<in>zobj_refs (fst x). ex_nonz_cap_to r s)
           and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. real_cte_at (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. ex_cte_cap_wp_to is_cnode_cap (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at (interrupt_derived (fst x)) (snd x) s)\<rbrace>
     decode_invocation label args cap_index slot cap excaps
   \<lbrace>valid_invocation\<rbrace>,-"
  apply (simp add: decode_invocation_def cong: cap.case_cong if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp Tcb_AI.decode_tcb_inv_wf decode_domain_inv_wf[simplified split_def] | wpc |
          simp add: o_def uncurry_def split_def del: is_cnode_cap.simps cte_refs.simps)+
  apply (strengthen cnode_eq_strg)
  apply (clarsimp simp: valid_cap_def cte_wp_at_eq_simp is_cap_simps
                        cap_rights_update_def ex_cte_cap_wp_to_weakenE[OF _ TrueI]
                        cte_wp_at_caps_of_state
                 split: cap.splits option.splits)
       apply (thin_tac " \<forall>x\<in>set excaps. P x \<and> Q x" for P Q)+
       apply (drule (1) bspec)+
       apply (subst split_paired_Ex[symmetric], rule exI, simp)
      apply (thin_tac " \<forall>x\<in>set excaps. P x \<and> Q x" for P Q)+
      apply (rule conjI)
       apply (subst split_paired_Ex[symmetric], rule_tac x=slot in exI, simp)
      apply clarsimp
      apply (drule (1) bspec)+
      apply (subst split_paired_Ex[symmetric], rule exI, simp)
     apply (thin_tac " \<forall>x\<in>set excaps. P x \<and> Q x" for P Q)+
     apply (drule (1) bspec)+
     apply (clarsimp simp add: ex_cte_cap_wp_to_weakenE[OF _ TrueI])
     apply (rule eq_no_cap_to_obj_with_diff_ref)
      apply (fastforce simp add: cte_wp_at_caps_of_state)
     apply (simp add: invs_valid_arch_caps)
    apply (simp add: invs_valid_objs invs_valid_global_refs)
   apply (thin_tac " \<forall>x\<in>set excaps. P x \<and> Q x" for P Q)+
   apply (drule (1) bspec)+
   apply (subst split_paired_Ex[symmetric], rule exI, simp)
  apply (thin_tac " \<forall>x\<in>set excaps. P x \<and> Q x" for P Q)+
  apply (subst split_paired_Ex[symmetric], rule exI, simp)
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
  sorry
(*  unfolding lookup_extra_caps_def
  apply (wpsimp wp: mapME_set)
*)

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
  sorry
(*  unfolding lookup_extra_caps_def
  by (wp mapME_set | simp)+ *)

lemma lec_ex_nonz_cap_to [wp]:
  "\<lbrace>invs\<rbrace>
  lookup_extra_caps t xa mi
  \<lbrace>\<lambda>rv s. (\<forall>cap \<in> set rv. \<forall>r\<in>zobj_refs (fst cap). ex_nonz_cap_to r s)\<rbrace>, -"
  sorry
(*  unfolding lookup_extra_caps_def
  by (wp mapME_set | simp)+ *)

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
  apply (wp rab_cte_cap_to touch_object_wp')
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  apply (clarsimp dest!: get_tcb_SomeD')
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
sorry (* FIXME: broken by touched-addrs v1 (Dec 2021) *)
(*
unfolding resolve_address_bits_def
proof (induct param rule: resolve_address_bits'.induct)
  case (1 cap cref)
  show ?case
    apply (clarsimp simp: validE_R_def validE_def valid_def  split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (split cap.splits)
              defer 6 (* cnode *)
              apply (simp_all add: spec_validE_def validE_def valid_def
                         throwError_def return_def valid_fault_def)[11]
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
qed *)

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
         | wp resolve_address_bits_valid_fault touch_object_wp')+
  apply clarsimp
  apply (frule get_tcb_ko_atD)
  apply clarsimp
  apply (frule get_tcb_True_False)
  apply (clarsimp simp: obj_at_def objs_valid_tcb_ctable)
  done

lemma lookup_cap_and_slot_valid_fault2[wp]:
  "\<lbrace>invs\<rbrace> lookup_cap_and_slot thread (to_bl p)
   -,\<lbrace>\<lambda>ft s. valid_fault (ExceptionTypes_A.CapFault p rp ft)\<rbrace>"
  using lookup_cap_and_slot_valid_fault[of thread "to_bl p"]
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

sublocale touched_addresses_inv \<subseteq> ex_cte_cap_wp_to:touched_addresses_P_inv _ _ "ex_cte_cap_wp_to a b"
  by unfold_locales (simp add:ta_agnostic_def)

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
  "\<lbrace>\<top>\<rbrace> get_cap True slot \<lbrace>\<lambda>rv. cte_wp_at (interrupt_derived rv) slot\<rbrace>"
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

lemma lookup_cap_and_slot_dimished [wp]:
  "\<lbrace>valid_objs\<rbrace>
    lookup_cap_and_slot thread cptr
   \<lbrace>\<lambda>x. cte_wp_at ((=) (fst x)) (snd x)\<rbrace>, -"
  by (wpsimp wp: get_cap_wp simp: lookup_cap_and_slot_def)

lemma lookup_extra_caps_eq [wp]:
  "\<lbrace>valid_objs\<rbrace> lookup_extra_caps thread xb info
  \<lbrace>\<lambda>rv s. (\<forall>x\<in>set rv. cte_wp_at ((=) (fst x)) (snd x) s)\<rbrace>,-"
  by (wpsimp wp: mapME_set simp: lookup_extra_caps_def)


(*FIXME: move to NonDetMonadVCG.valid_validE_R *)
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

lemma hoare_vcg_const_imp_lift_E[wp]:
  "\<lbrace>P\<rbrace> f -, \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. F \<longrightarrow> P s\<rbrace> f -, \<lbrace>\<lambda>rv s. F \<longrightarrow> Q rv s\<rbrace>"
  apply (cases F) apply auto
  apply wp
  done

context Syscall_AI begin

lemma hinv_invs':
  fixes Q :: "'state_ext state \<Rightarrow> bool" and calling blocking
  assumes perform_invocation_Q[wp]:
    "\<And>block class i.
      \<lbrace>invs and Q and ct_active and valid_invocation i\<rbrace>
        perform_invocation block class i
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
    "\<lbrace>invs and Q and ct_active\<rbrace> handle_invocation calling blocking \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  sorry
  (*
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc)

  apply (wp syscall_valid sts_invs_minor2 rfk_invs
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp split del: if_split)+
  apply (rule_tac Q = "\<lambda>st. st_tcb_at ((=) st) thread and (invs and Q)" in
         hoare_post_imp)
  apply (auto elim!: pred_tcb_weakenE st_tcb_ex_cap
              dest: st_tcb_at_idle_thread
              simp: st_tcb_at_tcb_at)[1]
  apply (rule gts_sp)
  apply wp
  apply (simp add: ct_in_state_def conj_commute conj_left_commute)
  apply wp
  apply (rule_tac Q = "\<lambda>rv s. st_tcb_at active thread s \<and> cur_thread s = thread" in
         hoare_post_imp)
  apply simp
  apply (wp sts_st_tcb_at')
  apply (simp only: simp_thms K_def if_apply_def2)
  apply (rule hoare_vcg_E_elim)
  apply (wp | simp add: if_apply_def2)+
  apply (auto simp: ct_in_state_def elim: st_tcb_ex_cap)
  done *)

lemmas hinv_invs[wp] = hinv_invs'
  [where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI,simplified]

(* FIXME: move *)
lemma hinv_tcb[wp]:
  "\<And>t calling blocking.
    \<lbrace>st_tcb_at active t and invs and ct_active\<rbrace>
      handle_invocation calling blocking
    \<lbrace>\<lambda>rv. tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  sorry
  (*
  apply (simp add: handle_invocation_def split_def
                   ts_Restart_case_helper
                   liftE_liftM_liftME liftME_def bindE_assoc)
  apply (wp syscall_valid sts_st_tcb_at_cases
            ct_in_state_set lec_caps_to
            | simp)+
  apply (clarsimp simp: st_tcb_at_tcb_at invs_valid_objs
                        ct_in_state_def)
  apply (fastforce elim!: st_tcb_ex_cap)
  done *)

lemma hs_tcb_on_err:
  "\<lbrace>st_tcb_at active t and invs and ct_active\<rbrace>
     handle_send blocking
   -,\<lbrace>\<lambda>e. tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (unfold handle_send_def whenE_def fun_app_def validE_E_def validE_def)
  apply (rule hoare_strengthen_post [OF hinv_tcb])
  apply (clarsimp split: sum.split)
  done

lemma hs_invs[wp]: "\<lbrace>invs and ct_active\<rbrace> handle_send blocking \<lbrace>\<lambda>r. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule validE_valid)
  apply (simp add: handle_send_def whenE_def)
  apply (wp | simp add: ct_in_state_def tcb_at_invs)+
  done

end


lemma tcb_cnode_index_3_reply_or_null:
  "\<lbrakk> tcb_at t s; tcb_cap_valid cap (t, tcb_cnode_index 3) s \<rbrakk> \<Longrightarrow> is_reply_cap cap \<or> cap = cap.NullCap"
  apply (clarsimp  simp: tcb_cap_valid_def st_tcb_def2 tcb_at_def)
  apply (clarsimp split: Structures_A.thread_state.split_asm)
  done

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

lemma delete_caller_cap_nonz_cap:
  "\<lbrace>ex_nonz_cap_to p and tcb_at t and valid_objs\<rbrace>
      delete_caller_cap t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: delete_caller_cap_def ex_nonz_cap_to_def cte_wp_at_caps_of_state)
  apply (rule hoare_pre)
  apply (wp hoare_vcg_ex_lift cap_delete_one_caps_of_state)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply clarsimp
  apply (drule (1) tcb_cap_valid_caps_of_stateD)
  apply (drule (1) tcb_cnode_index_3_reply_or_null)
  apply (auto simp: is_cap_simps)
  done

lemma delete_caller_cap_invs[wp]:
  "\<lbrace>invs and tcb_at t\<rbrace> delete_caller_cap t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: delete_caller_cap_def, wp)
  apply (clarsimp simp: emptyable_def)
  done

lemma delete_caller_cap_simple[wp]:
  "\<lbrace>st_tcb_at active t\<rbrace> delete_caller_cap t' \<lbrace>\<lambda>rv. st_tcb_at active t\<rbrace>"
  apply (simp add: delete_caller_cap_def)
  apply (wp cap_delete_one_st_tcb_at)
  apply simp
  done

lemma delete_caller_deletes_caller[wp]:
  "\<lbrace>\<top>\<rbrace> delete_caller_cap t \<lbrace>\<lambda>rv. cte_wp_at ((=) cap.NullCap) (t, tcb_cnode_index 3)\<rbrace>"
  apply (rule_tac Q="\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) (t, tcb_cnode_index 3)"
               in hoare_post_imp,
         clarsimp elim!: cte_wp_at_weakenE)
  apply (simp add: delete_caller_cap_def cap_delete_one_def unless_def, wp)
   apply (simp add: if_apply_def2, wp get_cap_wp, wp touch_object_wp')
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done

lemma delete_caller_cap_deleted[wp]:
  "\<lbrace>\<top>\<rbrace> delete_caller_cap thread \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) (thread, tcb_cnode_index 3)\<rbrace>"
  by (simp add: delete_caller_cap_def, wp)

lemma invs_valid_tcb_ctable_strengthen:
  "invs s \<longrightarrow> ((\<exists>y. get_tcb False thread s = Some y) \<longrightarrow>
               invs s \<and> s \<turnstile> tcb_ctable (the (get_tcb False thread s)))"
  by (clarsimp simp: invs_valid_tcb_ctable)

lemma hw_invs[wp]: "\<lbrace>invs and ct_active\<rbrace> handle_recv is_blocking \<lbrace>\<lambda>r. invs\<rbrace>"
  sorry (* FIXME: broken by touched-addrs v1 (Dec 2021) *)
  (*
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
    cong: if_cong)
  apply (wp get_simple_ko_wp | clarsimp)+
  apply (wp delete_caller_cap_nonz_cap get_simple_ko_wp hoare_vcg_ball_lift | simp)+
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
  apply (simp add: ct_in_state_def)
  apply (fold obj_at_def)
  apply (fastforce elim!: invs_valid_tcb_ctable st_tcb_ex_cap)
  done *)

crunch typ_at[wp]: delete_caller_cap "\<lambda>s. P (typ_at T p s)"

lemmas delete_caller_cap_tcb[wp]
  = tcb_at_typ_at [OF delete_caller_cap_typ_at]

lemma hw_tcb[wp]: "\<lbrace>tcb_at t\<rbrace> handle_recv is_blocking \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
             cong: if_cong)
  apply (wp hoare_vcg_if_lift2 hoare_vcg_conj_lift hoare_drop_imps | wpc | simp)+
  done

lemma sts_st_tcb_at'':
  "\<lbrace>K (t = t' \<and> P st)\<rbrace>
     set_thread_state t st
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (cases "t = t'")
   apply (simp only: simp_thms)
   apply (rule sts_st_tcb_at')
  apply simp
  done

lemma null_cap_on_failure_wp[wp]:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv. Q cap.NullCap\<rbrace>"
  shows      "\<lbrace>P\<rbrace> null_cap_on_failure f \<lbrace>Q\<rbrace>"
  unfolding ncof_is_a_catch
  by (wp x)

crunch_ignore (add:null_cap_on_failure)

lemma hy_inv: "(\<And>s f. P (trans_state f s) = P s) \<Longrightarrow> \<lbrace>P\<rbrace> handle_yield \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: handle_yield_def)
  apply (wp | simp)+
  done

declare hoare_seq_ext[wp] hoare_vcg_precond_imp [wp_comb]

lemma ct_active_simple [elim!]:
  "ct_active s \<Longrightarrow> st_tcb_at simple (cur_thread s) s"
  by (fastforce simp: ct_in_state_def elim!: pred_tcb_weakenE)

lemma active_from_running:
  "ct_running  s  \<Longrightarrow> ct_active  s"
  by (clarsimp elim!: pred_tcb_weakenE
               simp: ct_in_state_def)+

lemma tcb_caller_cap:
  "\<lbrakk>tcb_at t s; valid_objs s\<rbrakk> \<Longrightarrow>
   cte_wp_at (is_reply_cap or (=) cap.NullCap) (t, tcb_cnode_index 3) s"
  by (fastforce intro: tcb_cap_wp_at split: Structures_A.thread_state.split_asm)

lemma (in Syscall_AI) hr_invs[wp]:
  "\<lbrace>invs :: 'state_ext state \<Rightarrow> _\<rbrace> handle_reply \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: handle_reply_def)
  sorry (* FIXME: broken by touched-addrs. need sp rule for touch_object -robs
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_seq_ext [OF _ get_cap_sp])
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply (clarsimp simp: cte_wp_at_eq_simp)
  apply (frule cte_wp_at_valid_objs_valid_cap)
   apply clarsimp+
  apply (fastforce simp: valid_cap_def is_reply_cap_to_def
                 split: cap.splits
                  elim: cte_wp_at_weakenE)
  done
*)

sublocale touched_addresses_inv \<subseteq> cur_thread:touched_addresses_P_inv _ _ "\<lambda>s. P (cur_thread s)"
  by unfold_locales (simp add:ta_agnostic_def)

crunch cur_thread[wp]: set_extra_badge "\<lambda>s. P (cur_thread s)"

crunch (in Syscall_AI) cur_thread[wp]: handle_reply "\<lambda>s :: 'state_ext state. P (cur_thread s)"
  (wp: crunch_wps simp: unless_def crunch_simps
   ignore: make_fault_msg rule: transfer_caps_loop_pres)

lemmas cap_delete_one_st_tcb_at_simple[wp] =
    cap_delete_one_st_tcb_at[where P=simple, simplified]

lemma simple_if_Restart_Inactive:
  "simple (if P then Structures_A.Restart else Structures_A.Inactive)"
  by simp

crunch (in Syscall_AI) st_tcb_at_simple[wp]: handle_reply "st_tcb_at simple t' :: 'state_ext state \<Rightarrow> _"
  (wp: hoare_post_taut crunch_wps sts_st_tcb_at_cases
       thread_set_no_change_tcb_state
     ignore: set_thread_state simp: simple_if_Restart_Inactive)

lemmas (in Syscall_AI) hr_ct_in_state_simple[wp]
    = ct_in_state_thread_state_lift [OF handle_reply_cur_thread
                                       handle_reply_st_tcb_at_simple]

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

context Syscall_AI begin

lemma do_reply_transfer_nonz_cap:
  "\<lbrace>\<lambda>s :: 'state_ext state. ex_nonz_cap_to p s \<and> valid_objs s \<and> tcb_at p s \<and> valid_mdb s
            \<and> tcb_at receiver s\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: do_reply_transfer_def)
  sorry (* FIXME: broken by touched-addrs. need sp rule for touch_object -robs
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (rule hoare_pre)
   apply (wp cap_delete_one_cte_wp_at_preserved hoare_vcg_ex_lift | simp split del: if_split
          | wpc | strengthen ex_nonz_cap_to_tcb_strg)+
       apply (clarsimp simp add: tcb_cap_cases_def is_cap_simps can_fast_finalise_def)
      apply (strengthen ex_tcb_cap_to_tcb_at_strg)

      apply (wp drop_when_dxo_wp hoare_vcg_ex_lift
             thread_set_no_change_tcb_state thread_set_cte_wp_at_trivial
             ex_nonz_cap_to_pres [OF thread_set_cte_wp_at_trivial]
             | simp add: tcb_cap_cases_def)+
     apply (wp hoare_vcg_ex_lift cap_delete_one_cte_wp_at_preserved
            | strengthen ex_nonz_cap_to_tcb_strg)+
     apply (clarsimp simp add: tcb_cap_cases_def is_cap_simps can_fast_finalise_def)
    apply (strengthen ex_tcb_cap_to_tcb_at_strg)
    apply (wp hoare_drop_imp hoare_allI)+
  apply (clarsimp)
  done
*)

lemma handle_reply_nonz_cap:
  "\<lbrace>\<lambda>s :: 'state_ext state. ex_nonz_cap_to p s \<and> valid_objs s \<and> valid_mdb s \<and> tcb_at p s\<rbrace>
     handle_reply
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: handle_reply_def)
  apply (wp delete_caller_cap_nonz_cap do_reply_transfer_nonz_cap | wpc)+
   apply (wp get_cap_wp touch_object_wp)+
  apply clarsimp
  apply (drule(1) cte_wp_valid_cap)
  apply (clarsimp simp: valid_cap_def)
  done

lemma handle_reply_nonz_cap_to_ct:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s \<and> valid_objs s \<and> valid_mdb s \<and> tcb_at (cur_thread s) s\<rbrace>
     handle_reply
   \<lbrace>\<lambda>rv s :: 'state_ext state. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. \<exists>ct. (ct = cur_thread s) \<and> ex_nonz_cap_to ct s"
               in hoare_post_imp)
   apply simp
  apply (wp hoare_vcg_ex_lift handle_reply_nonz_cap)
  apply simp
  done

(* FIXME: move *)
lemma do_reply_transfer_st_tcb_at_active:
  "\<lbrace>valid_objs and st_tcb_at active t and st_tcb_at awaiting_reply t' and
    cte_wp_at (is_reply_cap_to t') sl\<rbrace>
    do_reply_transfer t t' sl grant
   \<lbrace>\<lambda>rv. st_tcb_at active t :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: do_reply_transfer_def is_reply_cap_to_def)
  apply (wp drop_when_dxo_wp sts_st_tcb_at' sts_st_tcb_at_neq cap_delete_one_reply_st_tcb_at
            hoare_drop_imps thread_set_no_change_tcb_state
            do_ipc_transfer_non_null_cte_wp_at2
       | wpc | clarsimp simp: is_reply_cap_to_def)+
  sorry (* FIXME: broken by touched-addrs -robs
  apply (wp hoare_allI hoare_drop_imp)+
  apply (fastforce simp add: st_tcb_def2 is_reply_cap_to_def)
  done
*)

lemma hc_invs[wp]:
  "\<lbrace>invs and ct_active\<rbrace> handle_call \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  by (simp add: handle_call_def) wp

lemma hr_ct_active[wp]:
  "\<lbrace>invs and ct_active\<rbrace> handle_reply \<lbrace>\<lambda>rv. ct_active :: 'state_ext state \<Rightarrow> _\<rbrace>"
  apply (simp add: handle_reply_def)
  apply (rule hoare_seq_ext)
   apply (rule_tac t=thread in ct_in_state_decomp)
    apply ((wp hoare_drop_imps hoare_vcg_all_lift | wpc | simp)+)[1]
   apply (wp hoare_vcg_all_lift get_cap_wp do_reply_transfer_st_tcb_at_active touch_object_wp
        | wpc | simp)+
  apply (fastforce simp: ct_in_state_def cte_wp_at_caps_of_state is_reply_cap_to_def
                  dest: invs_valid_reply_caps
                  elim: valid_reply_caps_of_stateD)
  done

end
(* FIXME: move *) (* FIXME: should we add this to the simpset? *)
lemma select_insert:
  "select (insert x X) = (return x \<sqinter> select X)"
  by (simp add: alternative_def select_def return_def)


context Syscall_AI begin

lemma he_invs[wp]:
  "\<And>e.
    \<lbrace>\<lambda>s. invs s \<and> (e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
      handle_event e
    \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (case_tac e, simp_all)
      apply (rename_tac syscall)
      apply (case_tac syscall, simp_all)
      apply (((rule hoare_pre, wp hvmf_active hr_invs hy_inv ) |
                 wpc | wp hoare_drop_imps hoare_vcg_all_lift |
                 simp add: if_apply_def2 |
                 fastforce simp: tcb_at_invs ct_in_state_def valid_fault_def
                         elim!: st_tcb_ex_cap)+)
  done

end

(* Lemmas related to preservation of runnability over handle_recv for woken threads
   these are presently unused, but have proven useful in the past *)
context notes if_cong[cong] begin

lemma complete_signal_state_refs_of:
  "\<lbrace>\<lambda>s. P (state_refs_of s) \<rbrace> complete_signal ntfnc t \<lbrace>\<lambda>rv s. P (state_refs_of s) \<rbrace>"
  unfolding complete_signal_def
  apply (rule hoare_pre)
   apply (wp get_simple_ko_wp touch_object_wp' | wpc | simp)+
  apply clarsimp
  apply (subgoal_tac " ntfn_bound_refs (ntfn_bound_tcb ntfn) = state_refs_of s ntfnc")
   apply (clarsimp simp: if_apply_def2 split: if_splits if_split_asm)
   subgoal by (subst eq_commute, auto cong: if_cong simp: state_refs_of_def obj_at_def)
  apply (clarsimp simp: state_refs_of_def obj_at_def)
  done

lemma do_nbrecv_failed_transfer_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s) \<rbrace> do_nbrecv_failed_transfer t \<lbrace>\<lambda>rv s. P (state_refs_of s) \<rbrace>"
  unfolding do_nbrecv_failed_transfer_def
  apply (rule hoare_pre)
   apply (wp get_simple_ko_wp | wpc | simp)+
  done

crunch st_tcb_at_runnable[wp]: do_nbrecv_failed_transfer "st_tcb_at runnable t"

lemma fast_finalise_sym_refs:
  "\<lbrace>invs\<rbrace> fast_finalise cap final \<lbrace>\<lambda>y s. sym_refs (state_refs_of s)\<rbrace>"
  apply (cases cap; clarsimp simp: when_def)
     apply (wp cancel_all_signals_invs cancel_all_ipc_invs unbind_maybe_notification_invs
             | strengthen invs_sym_refs
             | clarsimp)+
  done

crunch state_refs_of[wp]: empty_slot "\<lambda>s::det_ext state. P (state_refs_of s)"
  (wp: crunch_wps simp: crunch_simps interrupt_update.state_refs_update)

lemma delete_caller_cap_sym_refs:
  "\<lbrace>invs\<rbrace> delete_caller_cap t \<lbrace>\<lambda>rv s::det_ext state. sym_refs (state_refs_of s) \<rbrace>"
  apply (simp add: delete_caller_cap_def cap_delete_one_def unless_def)
  apply (wp fast_finalise_sym_refs get_cap_wp)
  sorry (* FIXME: broken by touched-addrs -robs
  apply fastforce
  done
*)

lemmas sts_st_tcb_at_other = sts_st_tcb_at_neq[where proj=itcb_state]

lemma if_pred_distrib: "(if b then f else g) = (\<lambda>s. (b \<longrightarrow> f s) \<and> (\<not> b \<longrightarrow> g s))"
  by simp

lemma send_ipc_st_tcb_at_runnable:
  "\<lbrace>st_tcb_at runnable t and (\<lambda>s. sym_refs (state_refs_of s)) and K (t' \<noteq> t) \<rbrace>
   send_ipc block call badge can_grant can_grant_reply t' epptr
   \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  unfolding send_ipc_def
  apply (rule hoare_gen_asm)
  apply (wpc | wp sts_st_tcb_at_other | clarsimp)+
          apply (simp add: setup_caller_cap_def)
          apply (rule conjI)
          apply (wpc
                | wp sts_st_tcb_at_other dxo_wp_weak hoare_drop_imps
                | clarsimp simp: if_fun_split)+
    apply (wp get_simple_ko_wp)
   apply (wp touch_object_wp')
  apply clarsimp
  apply (drule st_tcb_at_state_refs_ofD)
  apply (drule (1) sym_refs_ko_atD)
  apply clarsimp
  apply (case_tac ts; clarsimp simp: obj_at_def state_refs_of_def dest!:refs_in_tcb_bound_refs)
  done

lemma receive_ipc_st_tcb_at_runnable:
  "\<lbrace>st_tcb_at runnable t and (\<lambda>s. sym_refs (state_refs_of s)) and K (t' \<noteq> t) \<rbrace>
   receive_ipc t' a b
   \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  unfolding receive_ipc_def
  apply (rule hoare_gen_asm)
  apply (wpc | wp sts_st_tcb_at_other
        | clarsimp simp: do_nbrecv_failed_transfer_def setup_caller_cap_def | rule conjI)+
               apply (wp hoare_drop_imps)
              apply (wp hoare_drop_imps)
             apply wpc
                    apply ((wp gts_wp gbn_wp  hoare_vcg_all_lift sts_st_tcb_at_other | wpc
                           | simp add: do_nbrecv_failed_transfer_def | wp (once) hoare_drop_imps)+)[8]
             apply clarsimp
             apply (wp gts_wp)
            apply (wp touch_object_wp')
           apply (wp hoare_drop_imps hoare_vcg_all_lift)[1]
           sorry (* FIXME: broken by touched-addrs -robs 
          apply ((wp sts_st_tcb_at_other get_simple_ko_wp gbn_wp get_simple_ko_wp | wpc)+)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rename_tac sendq)
   apply (frule list.collapse[symmetric])
   apply (drule st_tcb_at_state_refs_ofD)
   apply (frule (1) sym_refs_ko_atD)
   apply clarsimp
   apply (drule_tac x="hd sendq" in bspec, clarsimp)
   apply (case_tac ts; clarsimp simp: obj_at_def state_refs_of_def dest!: refs_in_tcb_bound_refs)
  apply clarsimp
  apply (rename_tac sendq)
  apply (frule list.collapse[symmetric])
  apply (drule st_tcb_at_state_refs_ofD)
  apply (frule (1) sym_refs_ko_atD)
  apply clarsimp
  apply (drule_tac x="hd sendq" in bspec, clarsimp)
  apply (case_tac ts; clarsimp simp: obj_at_def state_refs_of_def dest!: refs_in_tcb_bound_refs)
  done
*)

lemma send_fault_ipc_st_tcb_at_runnable:
  "\<lbrace>st_tcb_at runnable t and (\<lambda>s. sym_refs (state_refs_of s)) and tcb_at t' and K (t' \<noteq> t)\<rbrace> send_fault_ipc t' f \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  unfolding send_fault_ipc_def
  apply (rule hoare_pre, wp)
     apply (clarsimp simp: Let_def)
     apply wpc
                apply (wp send_ipc_st_tcb_at_runnable thread_set_no_change_tcb_state thread_set_refs_trivial
                          hoare_vcg_all_lift_R thread_get_wp touch_object_wp'
                        | clarsimp
                        | wp (once) hoare_drop_imps)+
  apply (clarsimp simp:  pred_tcb_at_def obj_at_def is_tcb)
  done

lemma handle_fault_st_tcb_at_runnable:
  "\<lbrace>st_tcb_at runnable t and invs and K (t' \<noteq> t) \<rbrace> handle_fault t' x \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: handle_fault_def handle_double_fault_def)
  apply wp
     apply (simp add: handle_fault_def handle_double_fault_def)
     apply (wp sts_st_tcb_at_other send_fault_ipc_st_tcb_at_runnable touch_object_wp' | simp)+
  apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def is_tcb ta_filter_def)
  done

lemma delete_caller_cap_runnable[wp]:
  "\<lbrace>st_tcb_at runnable t\<rbrace> delete_caller_cap t' \<lbrace>\<lambda>rv. st_tcb_at runnable t\<rbrace>"
  apply (simp add: delete_caller_cap_def)
  apply (wp cap_delete_one_st_tcb_at)
  apply simp
  done

lemma handle_recv_st_tcb_at:
  "\<lbrace>invs and st_tcb_at runnable t and (\<lambda>s. cur_thread s \<noteq> t)\<rbrace> handle_recv True
  \<lbrace>\<lambda>rv s::det_ext state. st_tcb_at runnable t s\<rbrace>"
  apply (simp add: handle_recv_def Let_def ep_ntfn_cap_case_helper
             cong: if_cong)
  apply (rule hoare_pre)
   apply (wp handle_fault_st_tcb_at_runnable receive_ipc_st_tcb_at_runnable
             delete_caller_cap_sym_refs rai_pred_tcb_neq touch_object_wp'
             get_simple_ko_wp hoare_drop_imps hoare_vcg_all_lift_R)
    apply clarsimp
    apply wp+
  sorry (* FIXME: broken by touched-addrs -robs
  apply fastforce
  done
*)

end (* Lemmas related to preservation of runnability over handle_recv for woken threads *)

end
