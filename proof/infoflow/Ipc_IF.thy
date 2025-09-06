(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_IF
imports ArchFinalise_IF
begin

section "reads_respects"

subsection "Notifications"

definition ipc_buffer_has_read_auth :: "'a PAS \<Rightarrow> 'a \<Rightarrow> obj_ref option \<Rightarrow> bool" where
  "ipc_buffer_has_read_auth aag l \<equiv>
     case_option True
       (\<lambda>buf'. is_aligned buf' msg_align_bits \<and>
               (\<forall>x \<in> ptr_range buf' msg_align_bits. (l,Read,pasObjectAbs aag x) \<in> (pasPolicy aag)))"

abbreviation aag_can_read_or_affect where
  "aag_can_read_or_affect aag l x \<equiv>
    aag_can_read aag x \<or> aag_can_affect aag l x"


lemma get_cap_reads_respects:
  "reads_respects aag l (K (aag_can_read aag (fst slot) \<or> aag_can_affect aag l (fst slot))) (get_cap slot)"
  apply (simp add: get_cap_def split_def)
  apply (wp get_object_reads_respects | wpc | simp)+
  done

lemma set_thread_state_act_runnable_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L) and st_tcb_at runnable thread\<rbrace>
   set_thread_state_act thread
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (simp add: set_thread_state_act_def)
  apply (wp gts_wp | rule hoare_pre_cont)+
  apply (force simp: st_tcb_at_def obj_at_def)
  done


definition all_to_which_has_auth where
  "all_to_which_has_auth aag auth source \<equiv> {t. (source,auth,t) \<in> pasPolicy aag}"

definition all_with_auth_to where
  "all_with_auth_to aag auth target \<equiv> {x. (x, auth, target) \<in> pasPolicy aag}"


lemma valid_ntfn_WaitingNtfn_tl:
  "\<lbrakk> ntfn_obj ntfn = (WaitingNtfn list); valid_ntfn ntfn s;
     tl list \<noteq> []; ntfn' = ntfn\<lparr>ntfn_obj := (WaitingNtfn (tl list))\<rparr> \<rbrakk>
     \<Longrightarrow> valid_ntfn ntfn' s"
  apply (case_tac list, simp_all)
  apply (rename_tac a lista)
  apply (case_tac lista, simp_all)
  apply (clarsimp simp: valid_ntfn_def split: option.splits)
  done

lemma tcb_sched_action_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L) and pas_refined aag\<rbrace>
   tcb_sched_action action thread
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: etcb_at_def equiv_but_for_labels_def split: option.splits)
  apply (rule states_equiv_forI)
          apply (fastforce intro!: equiv_forI elim!: states_equiv_forE dest: equiv_forD[where f=kheap])
         apply (simp add: states_equiv_for_def)
        apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=cdt])
       apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=cdt_list])
      apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=is_original_cap])
     apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=interrupt_states])
    apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=interrupt_irq_node])
   apply (fastforce simp: equiv_asids_def elim: states_equiv_forE)
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def split: option.splits)
  apply (rule equiv_forI)
  apply (erule_tac x="(thread, etcb_domain (the (etcbs_of s thread)))" in ballE)
   apply (fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=ready_queues] ko_at_etcbD)
  apply (force intro: domtcbs dest: ko_at_etcbD)
  done

lemma possible_switch_to_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and (\<lambda>s. etcb_at (\<lambda>etcb. etcb_domain etcb \<noteq> cur_domain s) target s)
                                  and K (pasObjectAbs aag target \<in> L) and pas_refined aag\<rbrace>
   possible_switch_to target
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (simp add: possible_switch_to_def)
  apply (wp tcb_sched_action_equiv_but_for_labels)
       (* possible_switch_to does not modify scheduler action if target is in different domain *)
       apply (rule hoare_pre_cont)
      apply (wp tcb_sched_action_equiv_but_for_labels)
      apply (rule hoare_pre_cont)
     apply (wp tcb_sched_action_equiv_but_for_labels)+
  apply (clarsimp simp: etcb_at_def etcbs_of'_def obj_at_def split: option.splits)
  done

crunch set_thread_state
  for etcb_at_cdom[wp]: "\<lambda>s. etcb_at (P (cur_domain s)) t s"
  (wp: crunch_wps set_object_wp)


locale Ipc_IF_1 =
  fixes aag :: "'a subject_label PAS"
  assumes lookup_ipc_buffer_reads_respects:
    "reads_respects aag l (K (aag_can_read aag thread \<or> aag_can_affect aag l thread))
                          (lookup_ipc_buffer is_receiver thread)"
  and as_user_equiv_but_for_labels:
    "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L)\<rbrace>
     as_user thread (f :: unit user_monad)
     \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  and storeWord_equiv_but_for_labels:
    "\<lbrace>\<lambda>ms. equiv_but_for_labels aag L st (s\<lparr>machine_state := ms\<rparr>) \<and>
           for_each_byte_of_word (\<lambda>x. pasObjectAbs aag x \<in> L) p\<rbrace>
     storeWord p v
     \<lbrace>\<lambda>_ ms. equiv_but_for_labels aag L st (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  and set_thread_state_runnable_equiv_but_for_labels:
    "runnable tst
     \<Longrightarrow> \<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L)\<rbrace>
         set_thread_state thread tst
         \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  and set_endpoint_equiv_but_for_labels:
    "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag epptr \<in> L)\<rbrace>
     set_endpoint epptr ep
     \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  and lookup_ipc_buffer_has_read_auth:
    "\<lbrace>pas_refined aag and valid_objs\<rbrace>
     lookup_ipc_buffer is_receiver thread
     \<lbrace>\<lambda>rv _. ipc_buffer_has_read_auth aag (pasObjectAbs aag thread) rv\<rbrace>"
  and dmo_loadWord_reads_respects:
    "reads_respects aag l (K (for_each_byte_of_word (\<lambda> x. aag_can_read_or_affect aag l x) p))
                          (do_machine_op (loadWord p))"
  and arch_derive_cap_reads_respects:
    "reads_respects aag l \<top> (arch_derive_cap acap)"
  and arch_derive_cap_rev:
    "reads_equiv_valid_inv A aag \<top> (arch_derive_cap acap)"
  and cptrs_in_ipc_buffer:
    "\<lbrakk> n \<in> set [buffer_cptr_index ..< buffer_cptr_index + unat (mi_extra_caps mi)];
       is_aligned p msg_align_bits;
       buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
       \<Longrightarrow> ptr_range (p + of_nat n * of_nat word_size) word_size_bits \<subseteq> ptr_range p msg_align_bits"
  and msg_in_ipc_buffer:
    "\<lbrakk> n = msg_max_length \<or> n < msg_max_length; is_aligned p msg_align_bits;
       unat (mi_length mi) < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
       \<Longrightarrow> ptr_range (p + of_nat n * of_nat word_size) word_size_bits \<subseteq> ptr_range p msg_align_bits"
  and captransfer_in_ipc_buffer:
    "\<lbrakk> is_aligned (buf :: obj_ref) msg_align_bits; p \<in> {0..2} \<rbrakk>
       \<Longrightarrow> ptr_range (buf + (2 + (of_nat msg_max_length + of_nat msg_max_extra_caps))
                          * word_size + p * word_size) word_size_bits
           \<subseteq> ptr_range buf msg_align_bits"
  and mrs_in_ipc_buffer:
    "\<lbrakk> n \<in> set [length msg_registers + 1 ..< Suc n'];
       is_aligned buf msg_align_bits; n' < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
       \<Longrightarrow> ptr_range (buf + of_nat n * of_nat word_size) word_size_bits
           \<subseteq> ptr_range buf msg_align_bits"
  and complete_signal_reads_respects:
    "pas_domains_distinct aag
     \<Longrightarrow> reads_respects aag l (K (aag_can_read aag nptr \<or> aag_can_affect aag l nptr))
                        (complete_signal nptr receiver)"
  and handle_arch_fault_reply_reads_respects:
    "reads_respects aag l (K (aag_can_read aag thread)) (handle_arch_fault_reply afault thread x y)"
  and arch_get_sanitise_register_info_reads_respects[wp]:
    "reads_respects aag l \<top> (arch_get_sanitise_register_info t)"
  and arch_get_sanitise_register_info_valid_global_objs[wp]:
    "arch_get_sanitise_register_info t \<lbrace>\<lambda>s :: det_state. valid_global_objs s\<rbrace>"
  and handle_arch_fault_reply_valid_global_objs[wp]:
    "handle_arch_fault_reply vmf thread x y \<lbrace>\<lambda>s :: det_state. valid_global_objs s\<rbrace>"
  and lookup_ipc_buffer_ptr_range':
    "\<lbrace>valid_objs\<rbrace>
     lookup_ipc_buffer True t
     \<lbrace>\<lambda>rv s :: det_state. rv = Some buf' \<longrightarrow> auth_ipc_buffers s t = ptr_range buf' msg_align_bits\<rbrace>"
  and lookup_ipc_buffer_aligned':
    "\<lbrace>valid_objs\<rbrace>
     lookup_ipc_buffer True t
     \<lbrace>\<lambda>rv s :: det_state. rv = Some buf' \<longrightarrow> is_aligned buf' msg_align_bits\<rbrace>"
  and handle_arch_fault_reply_globals_equiv:
    "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
     handle_arch_fault_reply vmf thread x y
     \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  and handle_arch_fault_reply_valid_arch_state[wp]:
    "handle_arch_fault_reply vmf thread x y \<lbrace>\<lambda>s :: det_state. valid_arch_state s\<rbrace>"
  (* FIXME IF: This assumption precludes X64 (its valid_arch_state includes caps) *)
  and transfer_caps_loop_valid_arch[wp]:
    "transfer_caps_loop epptr_opt buffer n caps slots mi \<lbrace>valid_arch_state :: det_ext state \<Rightarrow> _\<rbrace>"
begin

lemma store_word_offs_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and
    K (for_each_byte_of_word (\<lambda>x. pasObjectAbs aag x \<in> L) (ptr + of_nat offs * of_nat word_size))\<rbrace>
   store_word_offs ptr offs v
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding store_word_offs_def
  apply (wp modify_wp | simp add: do_machine_op_def split_def)+
  apply clarsimp
  apply (erule use_valid[OF _ storeWord_equiv_but_for_labels])
  apply simp
  done

(* FIXME: many redundant conditions *)
lemma update_waiting_ntfn_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects aag l (valid_objs and sym_refs \<circ> state_refs_of and pas_refined aag
                                      and pas_cur_domain aag and ko_at (Notification ntfn) nptr
                                      and (\<lambda>s. is_subject aag (cur_thread s))
                                      and K (ntfn_obj ntfn = WaitingNtfn queue))
                    (update_waiting_ntfn nptr queue bound_tcb badge)"
  unfolding update_waiting_ntfn_def fun_app_def
  apply (wp assert_sp possible_switch_to_reads_respects gets_cur_thread_ev | simp add: split_def)+
  by (wp as_user_set_register_reads_respects' set_thread_state_reads_respects
         set_simple_ko_reads_respects set_thread_state_pas_refined
         set_simple_ko_valid_objs hoare_vcg_disj_lift set_simple_ko_pas_refined
      | simp add: split_def)+

lemma update_waiting_ntfn_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and pas_refined aag and
    valid_objs and ko_at (Notification ntfn) nptr and sym_refs \<circ> state_refs_of and
    (\<lambda>s. \<forall>t\<in> set list. etcb_at (\<lambda>etcb. etcb_domain etcb \<noteq> cur_domain s) t s) and
    K (ntfn_obj ntfn = WaitingNtfn list \<and> pasObjectAbs aag nptr \<in> L \<and>
       all_with_auth_to aag Receive (pasObjectAbs aag nptr) \<subseteq> L \<and>
       \<Union> (all_to_which_has_auth aag Write ` all_with_auth_to aag Receive (pasObjectAbs aag nptr)) \<subseteq> L)\<rbrace>
   update_waiting_ntfn nptr list boundtcb badge
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding update_waiting_ntfn_def
  apply (wp hoare_weak_lift_imp as_user_equiv_but_for_labels set_thread_state_runnable_equiv_but_for_labels
            set_thread_state_pas_refined set_notification_equiv_but_for_labels
            set_simple_ko_pred_tcb_at set_simple_ko_pas_refined
            hoare_vcg_disj_lift possible_switch_to_equiv_but_for_labels
         | wpc | simp add: split_def | wps)+
  apply clarsimp
  apply (frule_tac P="receive_blocked_on nptr" and t="hd list" in ntfn_queued_st_tcb_at')
      apply (fastforce)
     apply assumption
    apply assumption
   apply simp
  apply (subgoal_tac "pasObjectAbs aag (hd list) \<in> all_with_auth_to aag Receive (pasObjectAbs aag nptr)")
   apply (fastforce)
  apply (clarsimp simp: all_with_auth_to_def)
  apply (erule pas_refined_mem[rotated])
  apply (rule sta_ts)
  apply (clarsimp simp: thread_st_auth_def tcb_states_of_state_def st_tcb_def2)
  apply (case_tac "tcb_state tcb", simp_all)
  done

end


lemma invisible_ntfn_invisible_receivers_and_ipcbuffers:
  "\<lbrakk> labels_are_invisible aag l {pasObjectAbs aag nptr};
     (pasSubject aag, Notify, pasObjectAbs aag nptr) \<in> pasPolicy aag\<rbrakk>
     \<Longrightarrow> labels_are_invisible aag l ({pasObjectAbs aag nptr} \<union>
                                     all_with_auth_to aag Receive (pasObjectAbs aag nptr) \<union>
                                     \<Union>(all_to_which_has_auth aag Write
                                        ` all_with_auth_to aag Receive (pasObjectAbs aag nptr)))"
  by (auto simp: labels_are_invisible_def aag_can_affect_label_def
                 all_to_which_has_auth_def all_with_auth_to_def
           dest: reads_read_page_read_thread reads_read_queued_thread_read_ep)

lemma invisible_ntfn_invisible_receivers_and_receivers[rotated 1]:
  "\<lbrakk> auth \<in> {Notify,Receive,SyncSend}; labels_are_invisible aag l {pasObjectAbs aag nptr};
     (pasSubject aag, auth, pasObjectAbs aag nptr) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> labels_are_invisible aag l ({pasObjectAbs aag nptr} \<union>
                                     all_with_auth_to aag Receive (pasObjectAbs aag nptr) \<union>
                                     (\<Union>(all_to_which_has_auth aag Receive
                                         ` all_with_auth_to aag Receive (pasObjectAbs aag nptr))) \<union>
                                     (\<Union>(all_to_which_has_auth aag Write
                                         ` all_with_auth_to aag Receive (pasObjectAbs aag nptr))))"
  by (auto simp: labels_are_invisible_def aag_can_affect_label_def
                 all_to_which_has_auth_def all_with_auth_to_def
           dest: read_sync_ep_read_senders read_sync_ep_read_receivers
                 reads_read_queued_thread_read_ep reads_read_page_read_thread reads_ep)

lemma read_queued_thread_reads_ntfn:
  "\<lbrakk> ko_at (Notification ntfn) ntfnptr s; t \<in> set queue; aag_can_read aag t; valid_objs s;
     sym_refs (state_refs_of s); pas_refined aag s; ntfn_obj ntfn = WaitingNtfn queue;
     (pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> aag_can_read aag ntfnptr"
  apply (frule_tac P="receive_blocked_on ntfnptr" and t=t in ntfn_queued_st_tcb_at')
      apply (fastforce)
     apply assumption
    apply assumption
   apply simp
  apply (rule_tac t="pasObjectAbs aag t" and auth="Receive" and auth'="Notify"
               in reads_read_queued_thread_read_ep)
      apply assumption
     apply simp
    apply (erule pas_refined_mem[rotated])
    apply (rule sta_ts)
    apply (clarsimp simp: thread_st_auth_def tcb_states_of_state_def st_tcb_def2)
    apply (case_tac "tcb_state tcb", simp_all)[1]
   apply simp
  apply simp
  done

lemma not_etcb_at_not_cdom_can_read:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "\<lbrakk> \<not> etcb_at (\<lambda>etcb. etcb_domain etcb \<noteq> cur_domain s) t s;
           tcb_at t s; pas_refined aag s; pas_cur_domain aag s \<rbrakk>
           \<Longrightarrow> aag_can_read aag t"
  apply (clarsimp simp: obj_at_def etcb_at_def
                        pas_refined_def tcb_domain_map_wellformed_aux_def
                 split: option.splits)
  apply (erule_tac x="(t, cur_domain s)" in ballE)
   apply (force dest: domains_distinct[THEN pas_domains_distinct_inj])
  apply (force intro: domtcbs)
  done

lemma tcb_at_ntfn_queue:
  "\<lbrakk> valid_objs s; t \<in> set q; ko_at (Notification ntfn) nptr s; ntfn_obj ntfn = WaitingNtfn q \<rbrakk>
     \<Longrightarrow> tcb_at t s"
  by (fastforce simp: obj_at_def valid_obj_def valid_ntfn_def)

lemma invisible_ep_invisible_receiver:
  "\<lbrakk> labels_are_invisible aag l {pasObjectAbs aag epptr};
     (pasObjectAbs aag tcb, Receive, pasObjectAbs aag epptr) \<in> pasPolicy aag;
     (pasObjectAbs aag tcb, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> labels_are_invisible aag l ({pasObjectAbs aag epptr} \<union> {pasObjectAbs aag tcb})"
  by (auto simp: labels_are_invisible_def aag_can_affect_label_def all_with_auth_to_def
           dest: reads_ep reads_read_queued_thread_read_ep)

lemma no_fail_gts:
  "no_fail (tcb_at tcb) (get_thread_state tcb)"
  apply (clarsimp simp: get_thread_state_def thread_get_def)
  apply (rule no_fail_pre)
   apply wp
  by (clarsimp simp: get_tcb_def tcb_at_def)

lemma sts_noop:
   "monadic_rewrite True True (tcb_at tcb and (\<lambda>s. tcb \<noteq> cur_thread s))
                    (set_thread_state_act tcb) (return ())"
  apply (clarsimp simp: set_thread_state_act_def when_def)
  apply (monadic_rewrite_l monadic_rewrite_if_l_False \<open>wpsimp wp: gts_wp\<close>)
   apply (monadic_rewrite_symb_exec_l_drop)+
   apply (rule monadic_rewrite_refl)
  by (auto simp: pred_tcb_at_def obj_at_def is_tcb_def get_tcb_def)

lemma sts_to_modify':
  "monadic_rewrite True True (tcb_at tcb and (\<lambda>s :: det_state. tcb \<noteq> cur_thread s))
     (set_thread_state tcb st)
     (modify (\<lambda>s. s\<lparr>kheap := (kheap s)(tcb \<mapsto> TCB (the (get_tcb tcb s)\<lparr>tcb_state := st\<rparr>))\<rparr>))"
  apply (clarsimp simp: set_thread_state_def set_object_def)
  apply (monadic_rewrite_l sts_noop \<open>wpsimp wp: get_object_wp\<close>)
   apply (simp add: bind_assoc)
   apply monadic_rewrite_symb_exec_l+
       apply (rule_tac P="\<lambda>s'. s' = s \<and> tcba = the (get_tcb tcb s)" in monadic_rewrite_pre_imp_eq)
       apply (clarsimp simp: put_def modify_def get_def bind_def)
      apply (wpsimp wp: get_object_wp)+
  by (clarsimp simp: get_tcb_def tcb_at_def)

lemma sts_no_fail:
  "no_fail (\<lambda>s :: det_state. tcb_at tcb s) (set_thread_state tcb st)"
  apply (simp add: set_thread_state_def set_object_def)
  apply (simp add: set_thread_state_act_def get_thread_state_def
                   thread_get_def set_scheduler_action_def)
  apply (rule no_fail_pre)
   apply (wpsimp wp: get_object_wp)+
  apply (clarsimp simp: get_tcb_def tcb_at_def obj_at_def a_type_def is_tcb_def
                 split: kernel_object.splits option.splits)
  by (metis kernel_object.exhaust option.inject)

lemmas sts_to_modify =
  monadic_rewrite_weaken_failure[OF sts_to_modify' sts_no_fail no_fail_modify,simplified]


definition "blocked_cancel_ipc_nosts tcb \<equiv>
  do state <- get_thread_state tcb;
     epptr \<leftarrow> get_blocking_object state;
     ep \<leftarrow> get_endpoint epptr;
     queue \<leftarrow> get_ep_queue ep;
     queue' \<leftarrow> return $ remove1 tcb queue;
     ep' \<leftarrow> return (case queue' of [] \<Rightarrow> IdleEP | a # list \<Rightarrow> update_ep_queue ep queue');
     set_endpoint epptr ep';
     set_thread_state tcb Running
  od"


lemma cancel_ipc_to_blocked_nosts:
  "monadic_rewrite False False (\<lambda>s :: det_state. st_tcb_at receive_blocked tcb s \<and> cur_thread s \<noteq> tcb)
     (blocked_cancel_ipc_nosts tcb)
     (cancel_ipc tcb >>= (\<lambda>_. set_thread_state tcb Running))"
  apply (simp add: cancel_ipc_def bind_assoc blocked_cancel_ipc_nosts_def)
  apply (rule monadic_rewrite_bind_tail)
   apply (rule monadic_rewrite_transverse)
    apply (rename_tac state)
    apply (rule_tac P="\<lambda>_. \<exists>xa pl. state = BlockedOnReceive xa pl" in monadic_rewrite_bind_head)
    apply (rule monadic_rewrite_gen_asm[where Q=\<top>,simplified])
    apply clarsimp
    apply (rule monadic_rewrite_refl)
   apply (simp add: blocked_cancel_ipc_def blocked_cancel_ipc_nosts_def bind_assoc)
   apply (rule monadic_rewrite_bind_tail)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule monadic_rewrite_trans)
        apply (rule sts_to_modify)
       apply (rule monadic_rewrite_transverse)
        apply (rule monadic_rewrite_bind)
          apply (rule sts_to_modify)
         apply (rule sts_to_modify)
        apply (rule hoare_modifyE_var[where P="tcb_at tcb and (\<lambda>s. tcb \<noteq> cur_thread s)"])
        apply (clarsimp simp: tcb_at_def get_tcb_def)
       apply (simp add: modify_modify)
       apply (rule monadic_rewrite_is_refl)
       apply (fastforce simp add: simpler_modify_def o_def get_tcb_def)
      apply (wp gts_wp)+
  apply (simp add: set_thread_state_def bind_assoc gets_the_def)
  apply (clarsimp simp: pred_tcb_at_def receive_blocked_def obj_at_def is_tcb_def)
  by (case_tac "tcb_state tcba"; fastforce)

lemma gts_reads_respects:
  "reads_respects aag l (K (aag_can_read aag t \<or> aag_can_affect aag l t)) (get_thread_state t)"
  unfolding get_thread_state_def
  by (wp thread_get_reads_respects)

lemma ev2_invisible_simple:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "\<lbrakk> labels_are_invisible aag l L; modifies_at_most aag L Q f \<rbrakk>
           \<Longrightarrow> reads_respects aag l Q (f :: (det_state, unit) nondet_monad)"
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_2_guard_imp)
    apply (rule ev2_invisible[OF domains_distinct])
  by fastforce+

crunch blocked_cancel_ipc_nosts
  for silc_inv[wp]: "silc_inv aag st"


context Ipc_IF_1 begin

lemma blocked_cancel_ipc_nosts_equiv_but_for_labels:
  "\<lbrace>pas_refined aag and st_tcb_at (\<lambda>st. st = BlockedOnReceive x pl) t
                    and bound_tcb_at ((=) (Some ntfnptr)) t
                    and equiv_but_for_labels aag L st
                    and K (pasObjectAbs aag x \<in> L)
                    and K (pasObjectAbs aag t \<in> L)\<rbrace>
   blocked_cancel_ipc_nosts t
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding blocked_cancel_ipc_nosts_def get_blocking_object_def
  apply (wp set_endpoint_equiv_but_for_labels get_object_wp gts_wp
            set_thread_state_runnable_equiv_but_for_labels
         | wpc | simp)+
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma blocked_cancel_ipc_nosts_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l
     (pas_refined aag and st_tcb_at (\<lambda>st. \<exists>xa. st = (BlockedOnReceive x pl)) t
                      and bound_tcb_at ((=) (Some ntfnptr)) t
                      and (\<lambda>s. is_subject aag (cur_thread s))
                      and K ((pasObjectAbs aag t, Receive, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag
                           \<and> (pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag
                           \<and> (pasObjectAbs aag t, Receive, pasObjectAbs aag x) \<in> pasPolicy aag))
     (blocked_cancel_ipc_nosts t)"
  unfolding blocked_cancel_ipc_nosts_def
  apply (simp only:bind_assoc[symmetric])
  apply (rule bind_ev[where P''=\<top>,simplified])
    apply (wp set_thread_state_runnable_reads_respects,simp)
    subgoal proof (cases "aag_can_read_label aag (pasObjectAbs aag x) \<or> aag_can_affect aag l x")
      case True thus ?thesis \<comment> \<open>boring case, can read or affect ep\<close>
      unfolding blocked_cancel_ipc_nosts_def get_blocking_object_def
      apply clarsimp
      apply (rule pre_ev)
       apply (wpsimp wp: set_thread_state_reads_respects get_ep_queue_reads_respects
                         get_simple_ko_reads_respects get_blocking_object_reads_respects
                         gts_reads_respects set_simple_ko_reads_respects gts_wp
                   simp: get_blocking_object_def get_thread_state_rev)+
      apply (clarsimp simp: pred_tcb_at_def obj_at_def)
      by (fastforce dest:read_sync_ep_read_receivers )

    next
      case False thus ?thesis apply -  \<comment> \<open>can't read or affect ep\<close>
      apply (rule gen_asm_ev)
      apply (drule label_is_invisible[THEN iffD2])
      apply clarsimp
      apply (rule ev2_invisible_simple[OF domains_distinct],assumption)
      apply (simp add: get_blocking_object_def)
      apply (rule modifies_at_mostI)
      apply (rule hoare_pre)
       apply (wpsimp wp: set_thread_state_runnable_equiv_but_for_labels
                         set_endpoint_equiv_but_for_labels get_object_wp gts_wp
                         set_thread_state_runnable_equiv_but_for_labels)+
      by (fastforce simp: pred_tcb_at_def obj_at_def)
    qed
  by wp

lemmas blocked_cancel_ipc_nosts_reads_respects_f =
  reads_respects_f[where Q=\<top>, simplified,
                   OF blocked_cancel_ipc_nosts_reads_respects
                      blocked_cancel_ipc_nosts_silc_inv,
                      simplified]

end


lemma monadic_rewrite_reads_respects:
  "\<lbrakk> monadic_rewrite False False P f f'; reads_respects aag l P' (do x <- f; g x od) \<rbrakk>
     \<Longrightarrow> reads_respects aag l (P and P') (do x <- f'; g x od)"
  apply (clarsimp simp: monadic_rewrite_def spec_equiv_valid_def
                        equiv_valid_def equiv_valid_2_def bind_def)
  apply (frule_tac x=st in spec)
  apply (drule_tac x=t in spec)
  by fastforce

lemmas cancel_ipc_reads_respects_rewrite =
  monadic_rewrite_reads_respects[OF cancel_ipc_to_blocked_nosts, simplified bind_assoc]

lemmas cancel_ipc_valid_rewrite =
  monadic_rewrite_is_valid[OF cancel_ipc_to_blocked_nosts, simplified bind_assoc]

crunch blocked_cancel_ipc_nosts
  for etcb_at[wp]: "etcb_at P t"
crunch blocked_cancel_ipc_nosts
  for cur_domain[wp]: "\<lambda>s::det_state. P (cur_domain s)"
crunch blocked_cancel_ipc_nosts
  for pas_refined[wp]: "pas_refined aag"
crunch blocked_cancel_ipc_nosts
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

lemma BlockedOnReceive_inj:
  "x = (case (BlockedOnReceive x pl) of BlockedOnReceive x pl \<Rightarrow> x)"
  "pl = (case (BlockedOnReceive x pl) of BlockedOnReceive x pl \<Rightarrow> pl)"
  by auto

lemma receive_blockedD:
  "receive_blocked st \<Longrightarrow> \<exists>epptr pl. st = BlockedOnReceive epptr pl"
  by (cases st; simp add: receive_blocked_def)


context Ipc_IF_1 begin

lemma send_signal_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes set_thread_state_owned_reads_respects[wp del]
        cancel_ipc_pas_refined[wp del]
  shows
    "reads_respects aag l
       (pas_refined aag and pas_cur_domain aag
                        and (\<lambda>s. is_subject aag (cur_thread s))
                        and ct_active
                        and (\<lambda>s. sym_refs (state_refs_of s)) and valid_objs
                        and K ((pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag))
       (send_signal ntfnptr badge)"
  unfolding send_signal_def fun_app_def
  subgoal proof (cases "aag_can_read aag ntfnptr \<or> aag_can_affect aag l ntfnptr")
    case True
    note visible = this
    show ?thesis
    apply (rule pre_ev)
     apply (simp split del: if_split
            | rule_tac ntfnptr=ntfnptr in blocked_cancel_ipc_nosts_reads_respects
            | rule cancel_ipc_reads_respects_rewrite
            | wp (once) set_simple_ko_reads_respects possible_switch_to_reads_respects
                        as_user_set_register_reads_respects' set_thread_state_pas_refined
                        set_simple_ko_reads_respects cancel_ipc_receive_blocked_pas_refined
                        gts_reads_respects gts_wp hoare_vcg_imp_lift get_simple_ko_wp
                        get_simple_ko_reads_respects update_waiting_ntfn_reads_respects
            | wpc
            | simp )+
    apply (insert visible)
    apply clarsimp
    apply (rule conjI[rotated])
     apply fastforce
    apply (rule disjI2)
    apply (intro impI allI)
    apply (simp add: obj_at_def)
    apply (rule conjI)
     apply (frule (3) ntfn_bound_tcb_at[where P="(=) (Some ntfnptr)",OF _ _ _ _ refl])
     apply (frule (1) bound_tcb_at_implies_receive)
     apply (elim disjE)
      apply (rule disjI1)
      apply (fastforce dest:read_sync_ep_read_receivers)
     apply (rule disjI2)
     apply (fastforce dest:read_sync_ep_read_receivers)
    apply (clarsimp)
    apply (frule (1) ntfn_bound_tcb_at[where P="(=) (Some ntfnptr)",OF _ _ _ _ refl])
      apply (fastforce simp: obj_at_def)
     apply assumption
    apply (rule conjI)
     apply (fastforce simp: pred_tcb_at_def receive_blocked_def obj_at_def)
    apply (rule conjI[rotated])
     apply (frule (1) bound_tcb_at_implies_receive)
     apply (frule (1) bound_tcb_at_implies_reset)
     apply (clarsimp simp: pred_tcb_at_def get_tcb_def obj_at_def)
     apply (rule context_conjI)
      apply (fastforce dest!: receive_blockedD intro: BlockedOnReceive_inj)
     apply (frule_tac t=x and tcb=tcb and ep = "case (tcb_state tcb) of BlockedOnReceive a pl \<Rightarrow> a"
                   in get_tcb_recv_blocked_implies_receive)
       apply (fastforce simp: pred_tcb_at_def get_tcb_def obj_at_def)
      apply (fastforce simp: receive_blocked_def split:thread_state.splits)
     apply (fastforce simp: receive_blocked_def intro!: BlockedOnReceive_inj)
    by (fastforce simp: pred_tcb_at_def get_tcb_def obj_at_def receive_blocked_def ct_in_state_def)
  next
    case False note invisible = this show ?thesis
    apply (insert label_is_invisible[THEN iffD2, OF invisible])
    apply (rule gen_asm_ev)
    apply (drule (1) invisible_ntfn_invisible_receivers_and_receivers)
     apply simp
     apply (rule ev2_invisible_simple[OF domains_distinct],assumption)
     apply (rule modifies_at_mostI)
     apply (simp split del: if_split
            | rule cancel_ipc_valid_rewrite
            | wp (once) set_thread_state_pas_refined set_notification_equiv_but_for_labels
                        possible_switch_to_equiv_but_for_labels as_user_equiv_but_for_labels
                        set_thread_state_runnable_equiv_but_for_labels get_simple_ko_wp
                        gts_wp update_waiting_ntfn_equiv_but_for_labels
                        blocked_cancel_ipc_nosts_equiv_but_for_labels
            \<comment> \<open>FIXME: The following line is working around the fact that wp (once) doesn't invoke
                      wp_pre. If that is changed then it could be removed.\<close>
            | wp_pre0
            | wpc
            | wps)+
    apply (elim conjE)
    apply (match premises in "ntfn_bound_tcb _ = _" \<Rightarrow> \<open>fail\<close>
                                               \<bar> _ \<Rightarrow> \<open>rule allI impI conjI\<close>)+
     prefer 2
     apply (intro conjI allI impI; fastforce?)
     subgoal waiting_ntfn
       apply clarsimp
       apply (rule ccontr)
       apply (frule (2) not_etcb_at_not_cdom_can_read[OF domains_distinct, rotated 2])
        apply (rule tcb_at_ntfn_queue;assumption)
       apply (frule (7) read_queued_thread_reads_ntfn)
       using invisible
       by (fastforce simp add: all_with_auth_to_def all_to_which_has_auth_def)
     apply (frule (1) ntfn_bound_tcb_at[where P="(=) (Some ntfnptr)", OF _ _ _ _ refl])
       apply (fastforce simp: obj_at_def)
      apply assumption
     apply (intro allI conjI impI)
            apply (fastforce simp: pred_tcb_at_def receive_blocked_def obj_at_def
                            split: thread_state.splits
                           intro!: BlockedOnReceive_inj)
           apply assumption
          apply distinct_subgoals
         apply (fold_subgoals (prefix))
     apply (frule st_tcb_at_tcb_at)
     subgoal bound_ntfn premises prems for st s ntfn x sta
       prefer 2
           apply (rule disjI2)
           apply (rule disjI1)
           subgoal bound_tcb_can_receive
             using prems
             apply (clarsimp simp: all_with_auth_to_def obj_at_def)
             by (rule bound_tcb_at_implies_receive;assumption)
          apply (rule disjI2)
          apply (rule disjI2)
          apply (rule disjI1)
          subgoal bound_ep_can_receive
            apply (rule bexI[OF _ bound_tcb_can_receive])
            apply (simp add: all_with_auth_to_def all_to_which_has_auth_def)
            using prems
            apply (case_tac sta; (clarsimp simp: pred_tcb_at_def obj_at_def receive_blocked_def))
            apply (rule get_tcb_recv_blocked_implies_receive, assumption)
             apply (fastforce simp: get_tcb_def)
            by (fastforce split: thread_state.splits)
         apply (rule ccontr)
         apply (insert prems)
         apply (frule (3) not_etcb_at_not_cdom_can_read[OF domains_distinct])
         using bound_tcb_can_receive
         apply (fastforce simp: labels_are_invisible_def all_with_auth_to_def all_to_which_has_auth_def)
        apply (fastforce simp: pred_tcb_at_def receive_blocked_def obj_at_def)
       apply (rule ccontr)
       apply clarsimp
       using invisible bound_tcb_can_receive reads_ep
       by (fastforce simp add: all_with_auth_to_def all_to_which_has_auth_def)
    done
  qed
  done

end


lemma receive_signal_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag (l :: 'a subject_label)
     (valid_objs and pas_refined aag and (\<lambda>s. is_subject aag (cur_thread s))
                 and K ((\<forall>ntfnptr \<in> obj_refs_ac cap.
                           (pasSubject aag, Receive, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag \<and>
                           is_subject aag thread)))
     (receive_signal thread cap is_blocking)"
  unfolding receive_signal_def fun_app_def do_nbrecv_failed_transfer_def
  by (wp set_simple_ko_reads_respects set_thread_state_reads_respects
         as_user_set_register_reads_respects' get_simple_ko_reads_respects hoare_vcg_all_lift
      | wpc
      | wp (once) hoare_drop_imps
      | force dest: reads_ep)+


subsection "Sync IPC"

definition aag_can_read_or_affect_ipc_buffer :: "'a PAS \<Rightarrow> 'a \<Rightarrow> obj_ref option \<Rightarrow> bool" where
  "aag_can_read_or_affect_ipc_buffer aag l \<equiv>
     case_option True
       (\<lambda>buf'. is_aligned buf' msg_align_bits \<and>
               (\<forall>x \<in> ptr_range buf' msg_align_bits. aag_can_read aag x \<or> aag_can_affect aag l x))"

lemma for_each_byte_of_word_def2:
  "for_each_byte_of_word P ptr \<equiv> (\<forall>x\<in>ptr_range ptr word_size_bits. P x)"
  by (simp add: for_each_byte_of_word_def ptr_range_def word_size_size_bits_word add_diff_eq)


context Ipc_IF_1 begin

lemma lookup_ipc_buffer_aag_can_read_or_affect:
  "\<lbrace>pas_refined aag and valid_objs and K (aag_can_read aag thread \<or> aag_can_affect aag l thread)\<rbrace>
   lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda>rv s. aag_can_read_or_affect_ipc_buffer aag l rv\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post[OF lookup_ipc_buffer_has_read_auth])
  apply (auto simp: ipc_buffer_has_read_auth_def aag_can_read_or_affect_ipc_buffer_def
             intro: reads_read_thread_read_pages
              simp: aag_can_affect_label_def split: option.splits)
  done

lemma aag_has_auth_to_read_cptrs:
  "\<lbrakk> x \<in> set [buffer_cptr_index ..< buffer_cptr_index + unat (mi_extra_caps mi)];
     ipc_buffer_has_read_auth aag (pasSubject aag) (Some a);
     buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
     \<Longrightarrow> for_each_byte_of_word (\<lambda> y. aag_can_read aag y) (a + of_nat x * of_nat word_size)"
  apply (simp add: for_each_byte_of_word_def2 ipc_buffer_has_read_auth_def)
  apply (rule ballI)
  apply (rule reads_read)
  apply (clarify)
  apply (erule bspec)
  apply (rule subsetD[OF cptrs_in_ipc_buffer])
     apply fastforce
    apply assumption
   apply assumption
  apply assumption
  done

lemma get_extra_cptrs_rev:
  "reads_equiv_valid_inv A aag
     (K (ipc_buffer_has_read_auth aag (pasSubject aag) buffer \<and>
         (buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits))))
     (get_extra_cptrs buffer mi)"
  unfolding get_extra_cptrs_def
  apply (rule gen_asm_ev)
  apply clarsimp
  apply (case_tac buffer, simp_all add: return_ev_pre)
  apply (wp mapM_ev equiv_valid_guard_imp[OF load_word_offs_rev]
         | erule (2) aag_has_auth_to_read_cptrs)+
  done

lemma lookup_extra_caps_rev:
  "reads_equiv_valid_inv A aag
     (pas_refined aag and (K (is_subject aag thread)) and
      (\<lambda>s. ipc_buffer_has_read_auth aag (pasSubject aag) buffer \<and>
           buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits)))
     (lookup_extra_caps thread buffer mi)"
  unfolding lookup_extra_caps_def fun_app_def
  by (wpsimp wp: mapME_ev cap_fault_on_failure_rev lookup_cap_and_slot_rev get_extra_cptrs_rev)

lemmas lookup_extra_caps_reads_respects_g =
  reads_respects_g_from_inv[OF lookup_extra_caps_rev lookup_extra_caps_inv]

lemma aag_has_auth_to_read_msg:
  "\<lbrakk> n = msg_max_length \<or> n < msg_max_length;
     ipc_buffer_has_read_auth aag (pasSubject aag) (Some p);
     unat (mi_length mi) < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
     \<Longrightarrow> for_each_byte_of_word (aag_can_read aag) (p + of_nat n * of_nat word_size)"
  apply (simp add: for_each_byte_of_word_def2 ipc_buffer_has_read_auth_def)
  apply (rule ballI)
  apply (rule reads_read)
  apply (clarify)
  apply (erule bspec)
  apply (rule subsetD[OF msg_in_ipc_buffer[where n=n]])
     apply assumption
    apply assumption
   apply assumption
  apply assumption
  done

(* only called within do_reply_transfer for which access assumes sender
   and receiver in same domain *)
lemma get_mrs_rev:
  "reads_equiv_valid_inv A aag
     (K (is_subject aag thread \<and> ipc_buffer_has_read_auth aag (pasSubject aag) buf
                               \<and> unat (mi_length mi) < 2 ^ (msg_align_bits - word_size_bits)))
     (get_mrs thread buf mi)"
  unfolding get_mrs_def
  apply (rule gen_asm_ev)
  apply (wp mapM_ev'' load_word_offs_rev thread_get_rev
         | wpc
         | rule aag_has_auth_to_read_msg[where mi=mi]
         | clarsimp split: if_split_asm)+
  done

lemmas get_mrs_reads_respects_g = reads_respects_g_from_inv[OF get_mrs_rev get_mrs_inv]

end


lemma setup_caller_cap_reads_respects:
  "reads_respects aag l (K (aag_can_read aag sender \<and> aag_can_read aag receiver))
                  (setup_caller_cap sender receiver grant)"
  unfolding setup_caller_cap_def
  by (wp cap_insert_reads_respects set_thread_state_owned_reads_respects | simp)+

lemma const_on_failure_ev:
  "equiv_valid_inv I A P m
   \<Longrightarrow> equiv_valid_inv I A P (const_on_failure c m)"
  unfolding const_on_failure_def catch_def
  by (wp | wpc | simp)+

lemma set_extra_badge_reads_respects:
  "reads_respects aag l \<top> (set_extra_badge buffer badge n)"
  unfolding set_extra_badge_def
  by (rule store_word_offs_reads_respects)

lemma reads_equiv_cdt_has_children0:
  "\<lbrakk> pas_refined aag s; pas_refined aag s'; aag_can_read aag (fst slot);
     equiv_for (aag_can_read aag \<circ> fst) cdt s s' \<rbrakk>
     \<Longrightarrow> (cdt s) c = Some slot \<longleftrightarrow> (cdt s') c = Some slot"
  apply (rule iffI)
   apply (drule equiv_forD)
    apply (erule(1) all_children_subjectReads[THEN all_childrenD];fastforce)
   apply fastforce
  apply (drule equiv_forD)
   apply (erule(1) all_children_subjectReads[THEN all_childrenD];fastforce)
  apply fastforce
  done

lemma reads_equiv_cdt_has_children:
  "\<lbrakk> pas_refined aag s; pas_refined aag s'; is_subject aag (fst slot);
     equiv_for (aag_can_read aag \<circ> fst) cdt s s' \<rbrakk>
     \<Longrightarrow> (\<exists>c. (cdt s) c = Some slot) = (\<exists>c. (cdt s') c = Some slot)"
  apply (rule iff_exI)
  by (erule reads_equiv_cdt_has_children0; force)


lemma ensure_no_children_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and K (is_subject aag (fst slot)))
                        (ensure_no_children slot)"
  unfolding ensure_no_children_def fun_app_def equiv_valid_def2
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule_tac Q="\<lambda> rv s. pas_refined aag s \<and> is_subject aag (fst slot) \<and> rv = cdt s"
                in equiv_valid_rv_liftE_bindE[OF equiv_valid_rv_guard_imp[OF gets_cdt_revrv']])
     apply (rule TrueI)
    apply (clarsimp simp: equiv_valid_2_def)
    apply (drule reads_equiv_cdt_has_children)
       apply assumption
      apply assumption
     apply (fastforce elim: reads_equivE)
    apply (fastforce simp: in_whenE in_throwError)
   apply (wp, simp)
  done

(* FIXME MOVE *)
lemma ball_subsetE:
  "\<lbrakk> \<forall>x \<in> S. P x; S' \<subseteq> S; \<And>x. P x \<Longrightarrow> Q x \<rbrakk>
     \<Longrightarrow> \<forall>x \<in> S'. Q x"
  by blast


context Ipc_IF_1 begin

lemma derive_cap_rev':
  "reads_equiv_valid_inv A aag (\<lambda>s. (\<exists>x xa xb d. cap = cap.UntypedCap d x xa xb)
                                    \<longrightarrow> pas_refined aag s \<and> is_subject aag (fst slot))
                         (derive_cap slot cap)"
  unfolding derive_cap_def
  apply (rule equiv_valid_guard_imp)
  apply (wp ensure_no_children_rev arch_derive_cap_rev | wpc | simp)+
  done

lemma derive_cap_rev:
  "reads_equiv_valid_inv A aag (\<lambda>s. pas_refined aag s \<and> is_subject aag (fst slot))
                         (derive_cap slot cap)"
  by (blast intro: equiv_valid_guard_imp[OF derive_cap_rev'])

lemma transfer_caps_loop_reads_respects':
  "reads_respects aag l
     (pas_refined aag and valid_mdb and valid_objs and
      (\<lambda>s. (\<forall>cap\<in>set caps. valid_cap (fst cap) s
                         \<and> is_subject aag (fst (snd cap))
                         \<and> pas_cap_cur_auth aag (fst cap)
                         \<and> cte_wp_at (\<lambda>cp. fst cap \<noteq> NullCap
                                           \<longrightarrow> cp \<noteq> fst cap
                                           \<longrightarrow> cp = masked_as_full (fst cap) (fst cap)) (snd cap) s)
         \<and> (\<forall>slot\<in>set slots. is_subject aag (fst slot)
                           \<and> cte_wp_at ((=) NullCap) slot s
                           \<and> real_cte_at slot s)
         \<and> distinct slots))
     (transfer_caps_loop ep rcv_buffer n caps slots mi)"
  apply (induct caps arbitrary: slots n mi)
   apply simp
   apply (rule return_ev_pre)
  apply (case_tac a, rename_tac cap obj ind)
  apply (simp split del: if_split)
  apply (rule equiv_valid_guard_imp)
   apply (wp const_on_failure_ev | simp | intro conjI impI)+
      apply fast
     apply (wp set_extra_badge_reads_respects hoare_vcg_ball_lift | simp)+
          apply fast
         apply (wp cap_insert_reads_respects cap_insert_pas_refined whenE_throwError_wp
                   derive_cap_rev derive_cap_cap_cur_auth derive_cap_is_derived
                   hoare_vcg_ball_lift cap_insert_cte_wp_at
                | simp split del: if_split)+
    apply (rule_tac Q'="\<lambda>capd s. (capd \<noteq> NullCap
                                  \<longrightarrow> cte_wp_at (is_derived (cdt s) (obj,ind) capd) (obj, ind) s)
                               \<and> (capd \<noteq> NullCap \<longrightarrow> QM s capd)" for QM
                 in hoare_strengthen_postE_R)
     prefer 2
     apply (clarsimp simp: cte_wp_at_caps_of_state split del: if_split)
     apply (strengthen is_derived_is_transferable[mk_strg I' O], assumption, solves\<open>simp\<close>)
    apply (rule hoare_vcg_conj_liftE_R')
     apply (rule derive_cap_is_derived)
    apply (wp derive_cap_is_derived_foo')
   apply wp
  apply (clarsimp simp: remove_rights_cur_auth cte_wp_at_caps_of_state split del: if_split)
  apply (rename_tac actual_cap)
  apply (strengthen real_cte_tcb_valid)
  apply (clarsimp)
  apply (intro conjI)
   subgoal
     by (fastforce simp: masked_as_full_def is_cap_simps cap_master_cap_simps split: if_splits)
  apply clarsimp
  apply (intro conjI)
      apply (fastforce dest: auth_derived_pas_cur_auth)
     apply fastforce
    subgoal
      apply (erule ball_subsetE, fastforce)
      by (fastforce simp: cte_wp_at_caps_of_state masked_as_full_def is_cap_simps split: if_splits)
   subgoal by (fastforce simp: neq_Nil_conv cte_wp_at_caps_of_state)
  by (rule distinct_tl)

lemma transfer_caps_loop_reads_respects:
  "reads_respects aag l
     (pas_refined aag and valid_mdb and valid_objs and
      (\<lambda>s. (\<forall>cap\<in>set caps. valid_cap (fst cap) s
                         \<and> is_subject aag (fst (snd cap))
                         \<and> pas_cap_cur_auth aag (fst cap)
                         \<and> cte_wp_at (\<lambda>cp. fst cap \<noteq> NullCap \<longrightarrow> cp = fst cap) (snd cap) s)
         \<and> (\<forall>slot\<in>set slots. is_subject aag (fst slot)
                           \<and> cte_wp_at ((=) NullCap) slot s
                           \<and> real_cte_at slot s)
         \<and> distinct slots))
     (transfer_caps_loop ep rcv_buffer n caps slots mi)"
  apply (rule equiv_valid_guard_imp, rule transfer_caps_loop_reads_respects')
  by (fastforce elim: cte_wp_at_weakenE)

end


lemma empty_on_failure_ev:
  "equiv_valid_inv I A P m \<Longrightarrow>
  equiv_valid_inv I A P (empty_on_failure m)"
  unfolding empty_on_failure_def catch_def
  by (wp | wpc | simp)+

lemma unify_failure_ev:
  "equiv_valid_inv I A P m \<Longrightarrow>
  equiv_valid_inv I A P (unify_failure m)"
  unfolding unify_failure_def handleE'_def
  by (wp | wpc | simp)+

lemma lookup_slot_for_cnode_op_rev:
  "reads_equiv_valid_inv A aag
     (\<lambda>s. (depth \<noteq> 0 \<and> depth \<le> word_bits)
          \<longrightarrow> (pas_refined aag s \<and> (is_cnode_cap croot \<longrightarrow> is_subject aag (obj_ref_of croot))))
     (lookup_slot_for_cnode_op is_source croot ptr depth)"
  unfolding lookup_slot_for_cnode_op_def
  apply (clarsimp split del: if_split)
  apply (wp resolve_address_bits_rev lookup_error_on_failure_rev
            whenE_throwError_wp
         | wpc
         | rule hoare_strengthen_postE_R[OF wp_post_tautE_R]
         | simp add: split_def split del: if_split)+
  done

lemma lookup_slot_for_cnode_op_reads_respects:
  "reads_respects aag l (pas_refined aag and K (is_subject aag (obj_ref_of croot)))
     (lookup_slot_for_cnode_op is_source croot ptr depth)"
  apply (rule equiv_valid_guard_imp[OF lookup_slot_for_cnode_op_rev])
  by simp

lemma lookup_cap_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and K (is_subject aag thread))
     (lookup_cap thread ref)"
  unfolding lookup_cap_def split_def fun_app_def
  apply (wp lookup_slot_for_thread_rev get_cap_rev | simp | strengthen aag_can_read_self)+
   apply (rule lookup_slot_for_thread_authorised)
  apply simp
  done

lemma word_plus_power_2_offset_le:
  "\<lbrakk> is_aligned (p :: 'l :: len word) n; is_aligned q m; p < q; n \<le> m; n < len_of TYPE('l) \<rbrakk>
     \<Longrightarrow> p + 2^n \<le> q"
  apply (drule is_aligned_weaken, assumption)
  apply (clarsimp simp: is_aligned_def)
  apply (elim dvdE)
  apply (rename_tac k ka)
  apply (rule_tac ua=0 and n="int k" and n'="int ka" in udvd_incr')
    apply assumption
   apply (clarsimp simp: uint_nat)+
  done


context Ipc_IF_1 begin

lemma aag_has_auth_to_read_captransfer:
  "\<lbrakk> ipc_buffer_has_read_auth aag (pasSubject aag) (Some buffer); x \<in> {0..2} \<rbrakk>
     \<Longrightarrow> for_each_byte_of_word (aag_can_read aag)
           (buffer + (2 + (of_nat msg_max_length + of_nat msg_max_extra_caps)) * word_size
                                                                               + x * word_size)"
  apply (simp add: for_each_byte_of_word_def2 ipc_buffer_has_read_auth_def)
  apply (rule ballI)
  apply (rule reads_read)
  apply (clarify)
  apply (erule bspec)
  apply (rule subsetD[OF captransfer_in_ipc_buffer])
    apply fastforce+
  done

lemma load_cap_transfer_rev:
  "reads_equiv_valid_inv A aag (K (ipc_buffer_has_read_auth aag (pasSubject aag) (Some buffer)))
     (load_cap_transfer buffer)"
  unfolding load_cap_transfer_def fun_app_def captransfer_from_words_def
  apply (wp dmo_loadWord_rev | simp)+
  apply safe
    apply (erule aag_has_auth_to_read_captransfer[where x=0, simplified])
   apply (erule aag_has_auth_to_read_captransfer[where x=1, simplified])
  apply (erule aag_has_auth_to_read_captransfer[where x=2, simplified])
  done

end


lemma get_endpoint_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_endpoint ptr)"
  unfolding get_simple_ko_def
  by (wp get_object_rev | wpc | simp)+

lemma send_endpoint_threads_blocked:
  "\<lbrakk> valid_objs s; (sym_refs \<circ> state_refs_of) s; ko_at (Endpoint (SendEP list)) ep s; x \<in> set list \<rbrakk>
     \<Longrightarrow> st_tcb_at (send_blocked_on ep) x s"
  apply (rule ep_queued_st_tcb_at'')
  apply simp+
  done

lemma send_blocked_threads_have_SyncSend_auth:
  "\<lbrakk> pas_refined aag s; valid_objs s; sym_refs (state_refs_of s); st_tcb_at (send_blocked_on ep) x s \<rbrakk>
     \<Longrightarrow> (pasObjectAbs aag x, SyncSend, pasObjectAbs aag ep) \<in> pasPolicy aag"
  apply (drule_tac auth="SyncSend" and x=x in pas_refined_mem[rotated])
   apply (rule sta_ts)
   apply (clarsimp simp: thread_st_auth_def split: option.split simp: tcb_states_of_state_def st_tcb_def2)
   apply (case_tac "tcb_state tcb", simp_all)
  done

lemma get_thread_state_reads_respects:
  "reads_respects aag l (\<lambda>s. aag_can_read aag t \<or> aag_can_affect aag l t) (get_thread_state t)"
  unfolding get_thread_state_def
  apply (rule equiv_valid_guard_imp)
   apply (wp thread_get_reads_respects | simp)+
  done

lemma send_endpoint_reads_affects_queued:
  "\<lbrakk> (pasSubject aag, auth, pasObjectAbs aag epptr) \<in> pasPolicy aag;
     auth \<in> {Receive,Reset};
     aag_can_read aag epptr \<or> aag_can_affect aag l epptr;
     pas_refined aag s; valid_objs s; sym_refs (state_refs_of s);
     ko_at (Endpoint (SendEP list)) epptr s; ep = SendEP list; x \<in> set list \<rbrakk>
     \<Longrightarrow> aag_can_read aag x \<or> aag_can_affect aag l x"
  apply (frule send_endpoint_threads_blocked, (simp | assumption)+)
  apply (drule send_blocked_threads_have_SyncSend_auth, (simp | assumption)+)
  apply (auto dest: read_sync_ep_read_senders)
  done

lemma mapM_ev''':
  assumes reads_res: "\<And>x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A (Q and P x) (m x)"
  assumes inv: "\<And>x. x \<in> set lst \<Longrightarrow> m x \<lbrace>\<lambda>s. Q s \<and> (\<forall>x \<in> set lst. P x s)\<rbrace>"
  shows "equiv_valid_inv D A (\<lambda>s. Q s \<and> (\<forall>x \<in> set lst. P x s)) (mapM m lst)"
  apply (rule mapM_ev)
   apply (rule equiv_valid_guard_imp[OF reads_res], simp+)
  apply (wpsimp wp: inv)
  done

lemma cancel_badged_sends_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes gts_st_tcb_at[wp del]
  shows
    "reads_respects aag (l :: 'a subject_label)
       (pas_refined aag and valid_objs and (sym_refs \<circ> state_refs_of)
                        and (\<lambda>s. is_subject aag (cur_thread s)) and K (is_subject aag epptr))
       (cancel_badged_sends epptr badge)"
  apply (rule gen_asm_ev)+
  apply (simp add: cancel_badged_sends_def)
  apply wp
     apply ((wp mapM_ev''  get_thread_state_reads_respects set_thread_state_runnable_reads_respects
                set_simple_ko_reads_respects get_simple_ko_reads_respects hoare_vcg_ball_lift
                tcb_sched_action_reads_respects set_thread_state_pas_refined mapM_wp
             | wpc | simp add: filterM_mapM tcb_at_st_tcb_at[symmetric]
             | wp (once) hoare_drop_imps | rule subset_refl | force)+)[1]
    apply (wp get_simple_ko_reads_respects)
   apply (wp get_simple_ko_wp)
  apply simp
  apply (intro conjI allI impI ballI, elim conjE)
  by (rule send_endpoint_reads_affects_queued[where epptr = epptr];
      (assumption | force simp: pas_refined_def policy_wellformed_def))

lemma get_cap_ret_is_subject':
  "\<lbrace>pas_refined aag and K (is_subject aag (fst ptr))\<rbrace>
   get_cap ptr
   \<lbrace>\<lambda>rv s. is_cnode_cap rv \<longrightarrow> (\<forall>x\<in>obj_refs_ac rv. is_subject aag x)\<rbrace>"
  apply (rule hoare_strengthen_post[OF get_cap_ret_is_subject])
  apply (clarsimp simp: is_cap_simps)
  done


context Ipc_IF_1 begin

lemma get_receive_slots_rev:
  "reads_equiv_valid_inv A aag
     (pas_refined aag and (K (is_subject aag thread \<and>
                              ipc_buffer_has_read_auth aag (pasSubject aag) buf)))
     (get_receive_slots thread buf)"
  apply (case_tac buf)
   apply (fastforce intro: return_ev_pre)
  apply (simp add: lookup_cap_def split_def
         | wp empty_on_failure_ev unify_failure_ev lookup_slot_for_cnode_op_rev get_cap_rev
              lookup_slot_for_thread_rev lookup_slot_for_thread_authorised
              get_cap_ret_is_subject get_cap_ret_is_subject' load_cap_transfer_rev
         | wp (once) hoare_drop_imps
         | strengthen aag_can_read_self)+
  done

lemma transfer_caps_reads_respects:
  "reads_respects aag l
     (pas_refined aag and valid_mdb and valid_objs
                      and (\<lambda>s. (\<forall>cap\<in>set caps. s \<turnstile> fst cap
                                             \<and> is_subject aag (fst (snd cap))
                                             \<and> pas_cap_cur_auth aag (fst cap)
                                             \<and> cte_wp_at (\<lambda>cp. fst cap \<noteq> NullCap \<longrightarrow> cp = fst cap)
                                                         (snd cap) s))
                      and K (is_subject aag receiver \<and>
                             ipc_buffer_has_read_auth aag (pasSubject aag) receive_buffer))
     (transfer_caps mi caps endpoint receiver receive_buffer)"
  unfolding transfer_caps_def fun_app_def
  by (wp transfer_caps_loop_reads_respects get_receive_slots_rev
         get_receive_slots_authorised hoare_vcg_all_lift hoare_weak_lift_imp
      | wpc | simp add: ball_conj_distrib)+

lemma aag_has_auth_to_read_mrs:
  "\<lbrakk> aag_can_read_or_affect_ipc_buffer aag l (Some buf);
     n \<in> set [length msg_registers + 1..<Suc n'];
     n' < 2 ^ (msg_align_bits - word_size_bits) \<rbrakk>
     \<Longrightarrow> for_each_byte_of_word
           (\<lambda>x. aag_can_read_label aag (pasObjectAbs aag x) \<or> aag_can_affect aag l x)
           (buf + of_nat n * of_nat word_size)"
  apply (simp add: for_each_byte_of_word_def2 aag_can_read_or_affect_ipc_buffer_def)
  apply (rule ballI)
  apply (erule conjE)
  apply (erule bspec)
  apply (rule subsetD[OF mrs_in_ipc_buffer[where n=n and n'=n']])
     apply (clarsimp split: if_splits)
    apply assumption
   apply assumption
  apply assumption
  done

lemma load_word_offs_reads_respects:
  "reads_respects aag l (\<lambda>s. for_each_byte_of_word (\<lambda>x. aag_can_read_or_affect aag l x)
                                                   (a + of_nat x * of_nat word_size))
                  (load_word_offs a x)"
  unfolding load_word_offs_def fun_app_def
  apply (rule equiv_valid_guard_imp[OF dmo_loadWord_reads_respects])
  apply (clarsimp)
  done

end


lemma as_user_reads_respects:
  "reads_respects aag l (K (det f \<and> aag_can_read_or_affect aag l thread)) (as_user thread f)"
  apply (simp add: as_user_def split_def)
  apply (rule gen_asm_ev)
  apply (wp set_object_reads_respects select_f_ev gets_the_ev)
  apply (auto intro: reads_affects_equiv_get_tcb_eq[where aag=aag])
  done

lemma get_mi_length':
   "\<lbrace>\<top>\<rbrace> get_message_info sender \<lbrace>\<lambda>rv s. buffer_cptr_index + unat (mi_extra_caps rv)
                                         < 2 ^ (msg_align_bits - word_size_bits)\<rbrace>"
  apply (rule hoare_post_imp[OF _ get_mi_valid'])
  apply (clarsimp simp: valid_message_info_def msg_align_bits' msg_max_length_def word_le_nat_alt
                       buffer_cptr_index_def msg_max_extra_caps_def)
  done

lemma validE_E_wp_post_taut:
   "\<lbrace>P\<rbrace> f -, \<lbrace>\<top>\<top>\<rbrace>"
  by (auto simp: validE_E_def validE_def valid_def)

lemma aag_has_read_auth_can_read_or_affect_ipc_buffer:
  "ipc_buffer_has_read_auth aag (pasSubject aag) buf
   \<Longrightarrow> aag_can_read_or_affect_ipc_buffer aag l buf"
  apply (clarsimp simp: ipc_buffer_has_read_auth_def aag_can_read_or_affect_ipc_buffer_def
                 split: option.splits)
  apply (rule reads_read)
  apply blast
  done

lemma ev_irrelevant_bind:
  assumes inv: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  assumes ev: "equiv_valid I A A P g"
  shows "equiv_valid I A A P (do y \<leftarrow> f; g od)"
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule equiv_valid_2_bind)
      apply (rule ev[simplified equiv_valid_def2])
     apply (wp equiv_valid_rv_trivial[OF inv] inv | simp)+
  done

lemma set_mrs_returns_a_constant:
  "\<exists>x. \<lbrace>\<top>\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv s. rv = x\<rbrace>"
  apply (case_tac buf)
   apply (rule exI)
   apply ((simp add: set_mrs_def | wp | rule impI)+)[1]
  apply (rule exI)
  apply (simp add: set_mrs_def split del: if_split | wp | rule impI)+
  done

lemma set_mrs_ret_eq:
  "\<forall>(s::'s::state_ext state) (t::'s::state_ext state).
   \<forall>(rva, s') \<in> fst (set_mrs thread buf msgs s).
   \<forall>(rvb, t') \<in> fst (set_mrs thread buf msgs t). rva = rvb"
  apply (clarsimp)
  apply (cut_tac thread=thread and buf=buf and msgs=msgs in set_mrs_returns_a_constant)
  apply (erule exE)
  apply (subgoal_tac "a = x \<and> aa = x")
   apply simp
  apply (rule conjI)
   apply (erule (1) use_valid | simp)+
  done

lemma tl_tl_in_set:
  "tl xs = (x # xs') \<Longrightarrow> set xs' \<subseteq> set xs"
  by (case_tac xs, auto)

(* GENERALIZE the following is possible *)
lemma ptr_in_obj_range:
  "\<lbrakk>valid_objs s; pspace_aligned s; kheap s ptr = Some obj\<rbrakk>
  \<Longrightarrow> ptr + (a && mask (obj_bits obj)) \<in> obj_range ptr obj"
  apply (simp add: obj_range_def)
  apply (rule context_conjI)
  apply (frule(1) pspace_alignedD)
  apply (erule is_aligned_no_wrap')
   apply (rule and_mask_less')
    apply (drule valid_obj_sizes)
    apply fastforce
   apply (simp add: word_bits_def)
  apply (simp add: p_assoc_help)
  apply (rule word_plus_mono_right)
   apply (rule word_less_sub_1)
    apply (drule valid_obj_sizes)
    apply fastforce
   apply (simp add: word_bits_def and_mask_less')
  apply (rule is_aligned_no_overflow')
  apply (erule(1) pspace_alignedD)
  done

lemma ko_at_eq:
  "ko_at obj pos s \<longleftrightarrow> kheap s pos = Some obj"
  by (force simp:obj_at_def)


locale Ipc_IF_2 = Ipc_IF_1 +
  assumes copy_mrs_reads_respects:
    "pas_domains_distinct aag
     \<Longrightarrow> reads_respects aag l (K (aag_can_read_or_affect aag l sender \<and>
                                  aag_can_read_or_affect_ipc_buffer aag l sbuf \<and>
                                  unat w < 2 ^ (msg_align_bits - word_size_bits)))
                        (copy_mrs sender sbuf receiver rbuf w)"
  and get_message_info_reads_respects:
    "reads_respects aag l (K (aag_can_read_or_affect aag l ptr)) (get_message_info ptr)"
  and do_normal_transfer_reads_respects:
    "pas_domains_distinct aag
     \<Longrightarrow> reads_respects aag l (pas_refined aag and valid_mdb and valid_objs and
                               K (aag_can_read_or_affect aag l sender \<and>
                                  ipc_buffer_has_read_auth aag (pasObjectAbs aag sender) sbuf \<and>
                                  ipc_buffer_has_read_auth aag (pasObjectAbs aag receiver) rbuf \<and>
                                  (grant \<longrightarrow> (is_subject aag sender \<and> is_subject aag receiver))))
                        (do_normal_transfer sender sbuf endpoint badge grant receiver rbuf)"
  and make_arch_fault_msg_reads_respects:
    "reads_respects aag l (\<lambda>y. aag_can_read_or_affect aag l sender) (make_arch_fault_msg x4 sender)"
  and set_mrs_equiv_but_for_labels:
    "\<lbrace>equiv_but_for_labels aag L st and
      K (pasObjectAbs aag thread \<in> L \<and>
         (case buf of (Some buf') \<Rightarrow> is_aligned buf' msg_align_bits \<and>
                                     (\<forall>x \<in> ptr_range buf' msg_align_bits. pasObjectAbs aag x \<in> L)
                              | _ \<Rightarrow> True))\<rbrace>
     set_mrs thread buf msgs
     \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  and set_mrs_reads_respects':
    "pas_domains_distinct aag
     \<Longrightarrow> reads_respects aag l (K (ipc_buffer_has_auth aag thread buf \<and>
                                  (case buf of (Some buf') \<Rightarrow> is_aligned buf' msg_align_bits
                                                       | _ \<Rightarrow> True))) (set_mrs thread buf msgs)"
begin

lemma make_fault_msg_reads_respects:
  "reads_respects aag l (K (aag_can_read_or_affect aag l sender)) (make_fault_msg rva sender)"
  apply (case_tac rva)
  by (wp as_user_reads_respects make_arch_fault_msg_reads_respects
       | simp split del: if_split add: det_getRegister det_getRestartPC
       | rule det_mapM
       | rule subset_refl)+

lemma do_fault_transfer_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects aag l
       (K (aag_can_read_or_affect aag l sender \<and> ipc_buffer_has_auth aag receiver buf \<and>
           (case buf of None \<Rightarrow> True | Some buf' \<Rightarrow> is_aligned buf' msg_align_bits)))
       (do_fault_transfer badge sender receiver buf)"
  unfolding do_fault_transfer_def
  by (wp as_user_set_register_reads_respects' as_user_reads_respects set_message_info_reads_respects
         set_mrs_reads_respects' make_fault_msg_reads_respects thread_get_reads_respects
      | wpc
      | simp add: split_def det_setRegister
      | wp (once) hoare_drop_imps)+

lemma do_ipc_transfer_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (valid_objs and valid_mdb and pas_refined aag and
                         K ((grant \<longrightarrow> (is_subject aag sender \<and>
                                       is_subject aag receiver)) \<and>
                           aag_can_read_or_affect aag l sender \<and>
                           aag_can_read_or_affect aag l receiver
                           ))
     (do_ipc_transfer sender ep badge grant receiver)"
  unfolding do_ipc_transfer_def
  apply (wp do_normal_transfer_reads_respects lookup_ipc_buffer_reads_respects
            lookup_ipc_buffer_has_read_auth do_fault_transfer_reads_respects
            thread_get_reads_respects lookup_ipc_buffer_has_auth
            lookup_ipc_buffer_aligned
        | wpc
        | simp
        | wp (once) hoare_drop_imps
        | fastforce)+
  done

lemma receive_ipc_base_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes do_nbrecv_failed_transfer_def[simp]
  shows "reads_respects aag (l :: 'a subject_label)
     (invs and pas_refined aag and pas_cur_domain aag
      and ko_at (Endpoint ep) epptr
      and is_subject aag \<circ> cur_thread
      and K (is_subject aag receiver
           \<and> aag_has_auth_to aag Receive epptr
           \<and> (\<forall>auth \<in> cap_rights_to_auth rights True . aag_has_auth_to aag auth epptr)))
     (receive_ipc_base aag receiver ep epptr rights is_blocking)"
  apply (rule gen_asm_ev)
  apply (simp add: thread_get_def split: endpoint.split)
  apply (intro conjI impI)
    prefer 2 defer
    apply ((wp set_thread_state_reads_respects set_simple_ko_reads_respects
               as_user_set_register_reads_respects'
        | simp | intro allI impI | rule pre_ev, wpc)+)[2]
  apply (intro allI impI)
  apply (wp hoare_weak_lift_imp set_simple_ko_reads_respects set_thread_state_reads_respects
            setup_caller_cap_reads_respects do_ipc_transfer_reads_respects
            possible_switch_to_reads_respects gets_cur_thread_ev set_thread_state_pas_refined
            set_simple_ko_reads_respects hoare_vcg_all_lift
            hoare_vcg_imp_lift[OF set_simple_ko_get_tcb, unfolded disj_not1]
            set_thread_state_reads_respects get_simple_ko_reads_respects
            get_simple_ko_wp do_ipc_transfer_pas_refined
        | wpc | simp add: get_thread_state_def thread_get_def)+
  apply (clarsimp simp:neq_Nil_conv)
  subgoal for s sender queue
    apply (frule(1) receive_ipc_valid_ep_helper)
    apply (frule(1) sym_ref_endpoint_sendD[OF invs_sym_refs,where t= "sender"], force)
    apply (clarsimp simp:st_tcb_at_def elim!:obj_atE dest!:sym[where t = "tcb_state _"])
    apply (subgoal_tac "aag_can_read aag sender")
     apply (fastforce simp: get_tcb_def
                      elim: receive_ipc_sender_can_grant_helper
                     intro: requiv_get_tcb_eq')
    apply (frule(2) receive_ipc_sender_helper)
    apply (solves \<open>auto intro:reads_ep read_sync_ep_read_senders\<close>)
    done
  done

lemma receive_ipc_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag (l :: 'a subject_label)
                      (invs and
                         pas_refined aag and pas_cur_domain aag and valid_cap cap
                     and is_subject aag \<circ> cur_thread
                     and K (is_subject aag receiver \<and> pas_cap_cur_auth aag cap
                          \<and> AllowRead \<in> cap_rights cap))
     (receive_ipc receiver cap is_blocking)"
  apply (rule gen_asm_ev)
  apply (simp add: receive_ipc_def thread_get_def split: cap.split)
  apply (clarsimp simp: fail_ev_pre)
  apply (rename_tac epptr badge rights)
  apply (wp receive_ipc_base_reads_respects
            complete_signal_reads_respects
            hoare_weak_lift_imp set_simple_ko_reads_respects set_thread_state_reads_respects
            setup_caller_cap_reads_respects
            complete_signal_reads_respects thread_get_reads_respects
            get_thread_state_reads_respects
            possible_switch_to_reads_respects
            gets_cur_thread_ev
            set_thread_state_pas_refined
            do_ipc_transfer_reads_respects do_ipc_transfer_pas_refined
            hoare_vcg_all_lift
            get_bound_notification_reads_respects' gbn_wp
            get_simple_ko_reads_respects get_simple_ko_wp
        | wpc
        | simp)+
  by (fastforce simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def
                dest: bound_tcb_at_implies_receive reads_ep)

end


lemma receive_endpoint_threads_blocked:
"\<lbrakk>valid_objs s; (sym_refs \<circ> state_refs_of) s;
  ko_at (Endpoint (RecvEP list)) ep s; x\<in>set list\<rbrakk> \<Longrightarrow>
  st_tcb_at (receive_blocked_on ep) x s"
  apply (rule ep_queued_st_tcb_at'')
  apply simp+
  done

lemma receive_blocked_threads_have_Receive_auth:
  "\<lbrakk>pas_refined aag s; valid_objs s; sym_refs (state_refs_of s);
    st_tcb_at (receive_blocked_on ep) x s\<rbrakk> \<Longrightarrow>
  (pasObjectAbs aag x,Receive,pasObjectAbs aag ep) \<in> pasPolicy aag"
  apply (drule_tac auth="Receive" and x=x in pas_refined_mem[rotated])
   apply (rule sta_ts)
   apply (clarsimp simp: thread_st_auth_def split: option.split simp: tcb_states_of_state_def st_tcb_def2)
   apply (case_tac "tcb_state tcb", simp_all)
  done

lemma receive_endpoint_reads_affects_queued:
  "\<lbrakk>(pasSubject aag, SyncSend, pasObjectAbs aag epptr) \<in> pasPolicy aag;
        aag_can_read_label aag (pasObjectAbs aag epptr) \<or>
        aag_can_affect aag l epptr;
        pas_refined aag s; valid_objs s; sym_refs (state_refs_of s);
        ko_at (Endpoint (RecvEP list)) epptr s; ep = RecvEP list;
        x \<in> set list\<rbrakk>
       \<Longrightarrow>
             aag_can_read_label aag (pasObjectAbs aag x) \<or>
             aag_can_affect aag l x"
  apply (frule receive_endpoint_threads_blocked, (simp | assumption)+)
  apply (drule receive_blocked_threads_have_Receive_auth, (simp | assumption)+)
  apply (auto dest: read_sync_ep_read_receivers)
  done


context Ipc_IF_2 begin

lemma send_ipc_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag (l :: 'a subject_label)
        (pas_refined aag and invs and pas_cur_domain aag
          and is_subject aag \<circ> cur_thread
          and K (can_grant \<longrightarrow> (aag_has_auth_to aag Grant epptr))
          and K (is_subject aag thread \<and> aag_has_auth_to aag SyncSend epptr))
     (send_ipc block call badge can_grant can_grant_reply thread epptr)"
  apply (rule gen_asm_ev)
  apply (subgoal_tac "aag_can_read aag epptr")
   prefer 2
   apply (fastforce intro: reads_ep)
  apply (simp add: send_ipc_def)
  apply (wp set_simple_ko_reads_respects set_thread_state_reads_respects
            when_ev setup_caller_cap_reads_respects thread_get_reads_respects
            set_thread_state_reads_respects
            do_ipc_transfer_reads_respects
            set_simple_ko_reads_respects
            hoare_vcg_imp_lift [OF set_simple_ko_get_tcb, unfolded disj_not1] hoare_vcg_all_lift
            get_simple_ko_reads_respects get_simple_ko_wp
            possible_switch_to_reads_respects
            gets_cur_thread_ev set_thread_state_pas_refined
            do_ipc_transfer_pas_refined
        | wpc
        | simp add: get_thread_state_def thread_get_def split del: if_split)+
  apply clarsimp
  apply (rename_tac receiver queue)
  apply (subgoal_tac "aag_can_read aag receiver \<and> (can_grant \<longrightarrow> is_subject aag receiver)")
   prefer 2
   apply (frule(2) pas_refined_ep_recv, rule head_in_set)
   apply (rule conjI)
    subgoal by (rule read_sync_ep_read_receivers)
   apply (fastforce dest: aag_wellformed_grant_Control_to_recv[OF _ _ pas_refined_wellformed]
                    simp: aag_has_Control_iff_owns)
  by (fastforce elim: send_ipc_valid_ep_helper reads_equivE equiv_forD
      intro: kheap_get_tcb_eq)


subsection "Faults"

lemma send_fault_ipc_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag (l :: 'a subject_label) (invs and pas_refined aag and pas_cur_domain aag
         and is_subject aag \<circ> cur_thread and K (is_subject aag thread \<and> valid_fault fault))
     (send_fault_ipc thread fault)"
  apply (rule gen_asm_ev)
  apply (simp add: send_fault_ipc_def Let_def lookup_cap_def split_def)
  apply (wp send_ipc_reads_respects thread_set_reads_respects
            thread_set_refs_trivial thread_set_obj_at_impossible
            thread_set_valid_objs''
            hoare_vcg_conj_lift hoare_vcg_ex_lift hoare_vcg_all_lift
            thread_set_pas_refined cap_fault_on_failure_rev
            lookup_slot_for_thread_rev
            lookup_slot_for_thread_authorised hoare_vcg_all_liftE_R
            thread_get_reads_respects get_cap_auth_wp[where aag=aag] get_cap_rev
            thread_set_tcb_fault_set_invs
       | wpc
       | simp add: split_def add: tcb_cap_cases_def
       | strengthen aag_can_read_self)+
  (* clagged from Ipc_AC *)
  apply (rule_tac Q'="\<lambda>rv s. pas_refined aag s
                          \<and> is_subject aag (cur_thread s)
                          \<and> invs s
                          \<and> pas_cur_domain aag s
                          \<and> valid_fault fault
                          \<and> is_subject aag (fst (fst rv))"
               in hoare_strengthen_postE_R[rotated])
       apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)
      apply (wp get_cap_auth_wp[where aag=aag] lookup_slot_for_thread_authorised
                thread_get_reads_respects
            | simp add: add: lookup_cap_def split_def)+
  done


lemma handle_fault_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag (l :: 'a subject_label) (invs and pas_refined aag and pas_cur_domain aag
        and is_subject aag \<circ> cur_thread
        and K (is_subject aag thread \<and> valid_fault fault))
     (handle_fault thread fault)"
  unfolding handle_fault_def catch_def fun_app_def handle_double_fault_def
  apply (wp (once) hoare_drop_imps |
        wp set_thread_state_reads_respects send_fault_ipc_reads_respects | wpc | simp)+
  apply (fastforce intro: reads_affects_equiv_get_tcb_eq)
  done

end


subsection "Replies"

context Ipc_IF_1 begin

lemma handle_fault_reply_reads_respects:
  "reads_respects aag l (K (aag_can_read aag thread)) (handle_fault_reply fault thread x y)"
  apply (case_tac fault)
     apply (wp as_user_reads_respects thread_get_reads_respects
               thread_get_wp' handle_arch_fault_reply_reads_respects[simplified K_def]
            | simp add: det_zipWithM_x det_setRegister)+
  done

lemma lookup_ipc_buffer_has_read_auth':
  "\<lbrace>pas_refined aag and valid_objs and K (is_subject aag thread)\<rbrace>
   lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda>rv s. ipc_buffer_has_read_auth aag (pasSubject aag) rv\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post[OF lookup_ipc_buffer_has_read_auth])
  apply (drule sym, simp)
  done

end

context Ipc_IF_2 begin

lemma do_reply_transfer_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects_f aag l
       (silc_inv aag st and invs and pas_refined aag and pas_cur_domain aag and tcb_at receiver
                        and tcb_at sender and emptyable slot  and is_subject aag \<circ> cur_thread
                        and K (grant \<longrightarrow> is_subject aag receiver)
                        and K (is_subject aag sender \<and> aag_can_read aag receiver
                                                     \<and> is_subject aag (fst slot)))
       (do_reply_transfer sender receiver slot grant)"
  unfolding do_reply_transfer_def
  apply (rule gen_asm_ev)+
  apply (wp gets_cur_thread_ev[THEN reads_respects_f[where aag=aag and st=st and Q=\<top>]]
            set_thread_state_reads_respects cap_delete_one_reads_respects_f
            do_ipc_transfer_reads_respects do_ipc_transfer_pas_refined
            thread_set_reads_respects handle_fault_reply_reads_respects
            get_mrs_rev lookup_ipc_buffer_reads_respects
            lookup_ipc_buffer_has_read_auth' get_message_info_rev
            get_mi_length
            cap_delete_one_silc_inv do_ipc_transfer_silc_inv
            set_thread_state_pas_refined thread_set_fault_pas_refined'
            possible_switch_to_reads_respects[THEN reads_respects_f[where aag=aag and st=st and Q=\<top>]]
            when_ev thread_set_valid_arch_state
         | wpc
         | simp split del: if_split add: tcb_cap_cases_def
         | wp (once) reads_respects_f[where aag=aag and st=st]
         | elim conjE
         | wp (once) hoare_drop_imps)+
         apply (rule_tac Q'="\<lambda> rv s. pas_refined aag s \<and> pas_cur_domain aag s \<and> invs s
                                 \<and> is_subject aag (cur_thread s)
                                 \<and> silc_inv aag st s"
                     in hoare_strengthen_post[rotated])
          apply ((wp (once) hoare_drop_imps
                  | wp cap_delete_one_invs  hoare_vcg_all_lift
                       cap_delete_one_silc_inv reads_respects_f[OF thread_get_reads_respects]
                       reads_respects_f[OF get_thread_state_rev]
                  | simp add: invs_valid_objs invs_psp_aligned invs_valid_global_refs
                              invs_distinct invs_arch_state
                              invs_psp_aligned invs_vspace_objs invs_arch_state
                  | rule conjI
                  | elim conjE
                  | assumption)+)[8]
  by (fastforce dest: silc_inv_not_subject)

lemma handle_reply_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects_f aag l (silc_inv aag st and invs and pas_refined aag and pas_cur_domain aag
                                             and is_subject aag \<circ> cur_thread) handle_reply"
  unfolding handle_reply_def
  apply (wp do_reply_transfer_reads_respects_f hoare_vcg_all_lift
            get_cap_wp reads_respects_f[OF get_cap_reads_respects, where Q="\<top>" and st=st]
         | wpc | blast)+
  apply (rule conjI)
   apply (fastforce simp: reads_equiv_f_def)
  apply clarsimp
  apply (rule conjI)
   apply assumption
  apply (rule conjI)
   apply (drule cte_wp_valid_cap)
    apply (erule invs_valid_objs)
   apply (simp add: valid_cap_simps)
  apply (rule conjI, fastforce simp: tcb_at_invs)
  apply (rule conjI)
   apply (erule emptyable_cte_wp_atD)
    apply (erule invs_valid_objs)
   apply (simp add: is_master_reply_cap_def)
  apply (frule_tac p="(cur_thread s, tcb_cnode_index 3)" in cap_cur_auth_caps_of_state[rotated])
    apply simp
   apply (simp add: cte_wp_at_caps_of_state)
  apply (fastforce intro: read_reply_thread_read_thread_rev
                    simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
                    dest: aag_Control_into_owns)
  done

lemma reply_from_kernel_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (K (is_subject aag thread)) (reply_from_kernel thread x)"
  unfolding reply_from_kernel_def fun_app_def
  by (wp set_message_info_reads_respects set_mrs_reads_respects
         as_user_reads_respects lookup_ipc_buffer_reads_respects
      | simp add: split_def det_setRegister)+

end


(* FIXME in whole section replace preconditions with 10 differents invariants by invs *)
section "globals_equiv"

subsection "Sync IPC"

lemma setup_caller_cap_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state and valid_global_objs\<rbrace>
   setup_caller_cap sender receiver grant
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding setup_caller_cap_def
  apply (wp cap_insert_globals_equiv'' set_thread_state_globals_equiv)
  apply (simp_all)
  done

lemma set_extra_badge_globals_equiv:
  "set_extra_badge buffer badge n \<lbrace>globals_equiv s\<rbrace>"
  unfolding set_extra_badge_def
  by (wp store_word_offs_globals_equiv)

lemma transfer_caps_loop_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and valid_global_objs\<rbrace>
   transfer_caps_loop ep rcv_buffer n caps slots mi
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
proof (induct caps arbitrary: slots n mi)
  case Nil
  thus ?case by (simp, wp, simp)
next
  case (Cons c caps')
  show ?case
    apply (cases c)
    apply (simp split del: if_split cong: if_cong)
    apply (rule hoare_pre)
     apply (wp)
       apply (erule conjE, erule subst, rule Cons.hyps)
      apply (clarsimp)
      apply (wp set_extra_badge_globals_equiv)+
         apply (rule Cons.hyps)
        apply (simp)
        apply (wp cap_insert_globals_equiv'')
       apply (rule_tac Q'="\<lambda>_. globals_equiv st and valid_arch_state and valid_global_objs"
                   and E'="\<lambda>_. globals_equiv st and valid_arch_state and valid_global_objs"
                    in hoare_strengthen_postE)
         apply (simp add: whenE_def, rule conjI)
          apply (rule impI, wp)+
         apply (simp)+
       apply wp+
    apply (fastforce)
    done
qed

lemma transfer_caps_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and valid_global_objs\<rbrace>
   transfer_caps info caps endpoint receiver recv_buffer
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding transfer_caps_def
  by (wp transfer_caps_loop_globals_equiv | wpc | simp)+

lemma copy_mrs_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. receiver \<noteq> idle_thread s)\<rbrace>
   copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding copy_mrs_def including classic_wp_pre
  apply (wp | wpc)+
    apply (rule_tac Q'="\<lambda>_. globals_equiv s" in hoare_strengthen_post)
     apply (wp mapM_wp' | wpc)+
      apply (wp store_word_offs_globals_equiv)+
    apply fastforce
   apply simp
   apply (rule_tac Q'="\<lambda>_. globals_equiv s and valid_arch_state and (\<lambda>sa. receiver \<noteq> idle_thread sa)"
                in hoare_strengthen_post)
    apply (wp mapM_wp' as_user_globals_equiv)
    apply (simp)
   apply (fastforce)
  apply simp
  done

(* FIXME: move *)
lemma validE_to_valid:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>v. rv = Inr v \<longrightarrow> Q v s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>v. Q v\<rbrace>, -"
  apply (rule validE_validE_R)
  apply (simp add: validE_def valid_def)
  done

context Ipc_IF_1 begin

crunch transfer_caps, copy_mrs
  for valid_arch[wp]: "\<lambda>s :: det_state. valid_arch_state s"
  (wp: mapM_wp_inv)

lemma do_normal_transfer_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and valid_global_objs and (\<lambda>sa. receiver \<noteq> idle_thread sa)\<rbrace>
   do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding do_normal_transfer_def
  apply (wp as_user_globals_equiv set_message_info_globals_equiv transfer_caps_globals_equiv)
     apply (wp copy_mrs_globals_equiv)
    apply (subst K_def)
    apply (wp | rule impI)+
  apply (clarsimp)
  done

end

lemma do_fault_transfer_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>sa. receiver \<noteq> idle_thread sa)\<rbrace>
   do_fault_transfer badge sender receiver buf
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding do_fault_transfer_def
  apply (wp)
      apply (simp add: split_def)
      apply (wp as_user_globals_equiv set_message_info_globals_equiv
               set_mrs_globals_equiv | wpc)+
   apply (clarsimp)
   apply (rule hoare_drop_imps)
   apply (wp thread_get_inv, simp)
  done

lemma set_collection: "a = {x. x\<in>a}"
  by simp

lemma valid_ep_send_enqueue:
  "\<lbrakk> ko_at (Endpoint (SendEP (t # ts))) a s; valid_objs s \<rbrakk>
     \<Longrightarrow> valid_ep (case ts of [] \<Rightarrow> IdleEP | b # bs \<Rightarrow> SendEP (b # bs)) s"
  unfolding valid_objs_def valid_obj_def valid_ep_def obj_at_def
  apply (drule bspec)
  apply (auto split: list.splits)
  done

crunch complete_signal, possible_switch_to
  for globals_equiv[wp]: "globals_equiv st"

lemma case_list_cons_cong:
  "(case xxs of [] \<Rightarrow> f | x # xs \<Rightarrow> g xxs) =
   (case xxs of [] \<Rightarrow> f | x # xs \<Rightarrow> g (x # xs))"
  by (simp split: list.split)


context Ipc_IF_1 begin

lemma do_ipc_transfer_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and valid_objs
                     and valid_global_objs and (\<lambda>s. receiver \<noteq> idle_thread s)\<rbrace>
   do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wp do_normal_transfer_globals_equiv do_fault_transfer_globals_equiv | wpc)+
    apply (rule_tac Q'="\<lambda>_. globals_equiv st and valid_arch_state and valid_global_objs and
                           (\<lambda>sa. receiver \<noteq> idle_thread sa) and
                           (\<lambda>sa. (\<forall>rb. recv_buffer = Some rb
                                 \<longrightarrow> auth_ipc_buffers sa receiver = ptr_range rb msg_align_bits) \<and>
                                 (\<forall>rb. recv_buffer = Some rb \<longrightarrow> is_aligned rb msg_align_bits))"
                 in hoare_strengthen_post)
     apply (wp)
    apply (clarsimp | rule conjI)+
   apply (wp hoare_vcg_all_lift lookup_ipc_buffer_ptr_range' lookup_ipc_buffer_aligned' | fastforce)+
  done

lemma send_ipc_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
                     and valid_global_objs and valid_idle and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   send_ipc block call badge can_grant can_grant_reply thread epptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding send_ipc_def
  apply (wp set_simple_ko_globals_equiv set_thread_state_globals_equiv
            setup_caller_cap_globals_equiv | wpc)+
        apply (rule_tac Q'="\<lambda>_. globals_equiv st and valid_arch_state and valid_global_objs"
                     in hoare_strengthen_post[rotated])
         apply (fastforce)
        apply (wp set_thread_state_globals_equiv dxo_wp_weak | simp)+
      apply wpc
             apply (wp do_ipc_transfer_globals_equiv)+
     apply (clarsimp)
     apply (rule hoare_drop_imps)
     apply (wp set_simple_ko_globals_equiv)+
   apply (rule_tac Q'="\<lambda>ep. ko_at (Endpoint ep) epptr and globals_equiv st and valid_objs and
                           valid_arch_state and valid_global_refs and valid_global_objs and
                           (\<lambda>s. sym_refs (state_refs_of s)) and valid_idle"
                in hoare_strengthen_post)
    apply (wp get_simple_ko_sp)
   apply (clarsimp)+
   apply (rule context_conjI)
    apply (rule valid_ep_recv_dequeue')
     apply (simp)+
   apply (frule_tac x=xa in receive_endpoint_threads_blocked,simp+)
  by (clarsimp simp add: valid_idle_def pred_tcb_at_def obj_at_def)+

lemma receive_ipc_globals_equiv:
  notes do_nbrecv_failed_transfer_def[simp]
  shows "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
                           and valid_global_objs and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
         receive_ipc thread cap is_blocking
         \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding receive_ipc_def thread_get_def including no_pre
  apply (wp)
   apply (simp add: split_def)
   apply (wp set_simple_ko_globals_equiv set_thread_state_globals_equiv
             setup_caller_cap_globals_equiv dxo_wp_weak as_user_globals_equiv
          | wpc
          | simp split del: if_split)+
             apply (rule hoare_strengthen_post[where Q'="\<lambda>_. globals_equiv st and valid_arch_state
                                                                              and valid_global_objs"])
              apply (wp do_ipc_transfer_globals_equiv as_user_globals_equiv)
             apply clarsimp
            apply (wp gts_wp get_simple_ko_sp | wpc)+
          apply (wp hoare_vcg_all_lift hoare_drop_imps)[1]
           apply (wp set_simple_ko_globals_equiv | wpc)+
       apply (wp set_thread_state_globals_equiv)
      apply (wp get_simple_ko_wp gbn_wp get_simple_ko_wp as_user_globals_equiv | wpc | simp)+
  apply (rule hoare_pre)
   apply (wpc)
              apply (rule fail_wp | rule return_wp)+
  by (auto intro: valid_ep_send_enqueue simp: neq_Nil_conv cong: case_list_cons_cong)

end


subsection "Notifications"

lemma valid_ntfn_dequeue:
  "\<lbrakk> ko_at (Notification ntfn) ntfnptr s;
     ntfn_obj ntfn = (WaitingNtfn (t # ts)); valid_objs s; ts \<noteq> [] \<rbrakk>
     \<Longrightarrow> valid_ntfn ntfn s"
  unfolding valid_objs_def valid_obj_def valid_ntfn_def obj_at_def
  apply (drule bspec)
  apply (auto split: list.splits)
  done

(* FIXME: NTFN OBJECT CHANGED *)
lemma update_waiting_ntfn_globals_equiv:
  "\<lbrace>globals_equiv s and valid_objs and valid_arch_state and valid_global_refs
                    and ko_at (Notification ntfn) ntfnptr and pspace_distinct
                    and sym_refs \<circ> state_refs_of and (\<lambda>s. idle_thread s \<notin> set queue)
                    and K (ntfn_obj ntfn = WaitingNtfn queue)\<rbrace>
   update_waiting_ntfn ntfnptr queue bound_tcb badge
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding update_waiting_ntfn_def
  apply (wpsimp wp: set_thread_state_globals_equiv as_user_globals_equiv
                    set_notification_globals_equiv dxo_wp_weak)
  by (auto simp: neq_Nil_conv)

lemma cancel_ipc_blocked_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and st_tcb_at receive_blocked a\<rbrace>
   cancel_ipc a
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding cancel_ipc_def
  apply (rule bind_wp[OF _ gts_sp])
  apply (rule hoare_pre)
   apply (wpc; (simp,rule blocked_cancel_ipc_globals_equiv)?)
        apply (rule hoare_pre_cont)+
  apply clarsimp
  apply (case_tac state;(clarsimp simp: pred_tcb_at_def obj_at_def receive_blocked_def))
  by (simp add: eq_commute)

lemma send_signal_globals_equiv:
  "\<lbrace>globals_equiv s and valid_objs and valid_arch_state and valid_global_refs
                    and sym_refs \<circ> state_refs_of and pspace_distinct and valid_idle\<rbrace>
   send_signal ntfnptr badge
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding send_signal_def
  apply (wp set_notification_globals_equiv possible_switch_to_globals_equiv
            set_thread_state_globals_equiv as_user_globals_equiv cancel_ipc_blocked_globals_equiv
            update_waiting_ntfn_globals_equiv get_simple_ko_wp gts_wp
         | wpc | simp)+
  apply clarsimp
  apply (frule (1) sym_refs_ko_atD)
  apply (intro allI impI conjI)
           prefer 4
           apply clarsimp
           apply (frule_tac t="idle_thread sa" and P="\<lambda>ref. \<not> idle ref" in ntfn_queued_st_tcb_at')
  by (auto simp: pred_tcb_at_def obj_at_def valid_idle_def receive_blocked_def)


(* FIXME: belongs in Arch_IF *)
lemma receive_signal_globals_equiv:
  "\<lbrace>globals_equiv s and valid_objs and valid_arch_state and valid_global_refs
                    and pspace_distinct and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
   receive_signal thread cap is_blocking
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding receive_signal_def fun_app_def do_nbrecv_failed_transfer_def
  apply (rule hoare_pre)
   apply (wpsimp wp: set_notification_globals_equiv set_thread_state_globals_equiv
                     as_user_globals_equiv get_simple_ko_wp)+
  done

lemma handle_double_fault_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   handle_double_fault tptr ex1 ex2
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding handle_double_fault_def
  by (wp set_thread_state_globals_equiv)

lemma send_ipc_valid_global_objs:
  "\<lbrace>valid_global_objs\<rbrace>
   send_ipc block call badge can_grant can_grant_reply thread epptr
   \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  unfolding send_ipc_def
  by (wp dxo_wp_weak hoare_drop_imps hoare_vcg_all_lift | simp | wpc | intro conjI impI)+

lemma send_fault_ipc_valid_global_objs:
  "send_fault_ipc tptr fault \<lbrace>valid_global_objs\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wp)
     apply (simp add: Let_def)
     apply (wp send_ipc_valid_global_objs | wpc)+
    apply (rule_tac Q'="\<lambda>_. valid_global_objs" in hoare_strengthen_postE_R)
     apply (wp | simp)+
  done


context Ipc_IF_1 begin

lemma send_fault_ipc_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs and valid_global_objs
                     and valid_idle and (\<lambda>s. sym_refs (state_refs_of s)) and K (valid_fault fault)\<rbrace>
   send_fault_ipc tptr fault
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding send_fault_ipc_def
  apply (wp)
     apply (simp add: Let_def)
     apply (wp send_ipc_globals_equiv thread_set_globals_equiv thread_set_valid_objs''
               thread_set_fault_valid_global_refs thread_set_valid_idle_trivial
               thread_set_refs_trivial thread_set_valid_arch_state
               thread_set_tcb_fault_update_valid_mdb
            | wpc | simp add: tcb_cap_cases_def)+
    apply (rule_tac Q'="\<lambda>_. globals_equiv st and valid_objs and valid_arch_state and
                            valid_global_refs and valid_global_objs and K (valid_fault fault) and
                            valid_idle and (\<lambda>s. sym_refs (state_refs_of s))" in hoare_strengthen_postE_R)
     apply (wp | simp)+
    apply (clarsimp)
    apply (rule valid_tcb_fault_update)
     apply (wp | simp)+
  done

crunch send_fault_ipc
  for valid_arch_statex[wp]: valid_arch_state
  (wp: dxo_wp_weak hoare_drop_imps thread_set_valid_arch_state crunch_wps
   simp: crunch_simps tcb_cap_cases_def)

lemma handle_fault_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs and valid_global_objs
                     and valid_idle and (\<lambda>s. sym_refs (state_refs_of s)) and K (valid_fault ex)\<rbrace>
   handle_fault thread ex
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding handle_fault_def
  apply (wp handle_double_fault_globals_equiv)
    apply (rule_tac Q'="\<lambda>_. globals_equiv st and valid_arch_state" and
                    E'="\<lambda>_. globals_equiv st and valid_arch_state" in hoare_strengthen_postE)
      apply (wp send_fault_ipc_globals_equiv | simp)+
  done

lemma handle_fault_reply_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
   handle_fault_reply fault thread x y
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  by (cases fault; wpsimp wp: as_user_globals_equiv handle_arch_fault_reply_globals_equiv)

crunch handle_fault_reply
  for valid_arch_state[wp]: "\<lambda>s :: det_state. valid_arch_state s"

lemma do_reply_transfer_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
                     and valid_global_objs and valid_idle\<rbrace>
   do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding do_reply_transfer_def
  apply (wp set_thread_state_globals_equiv cap_delete_one_globals_equiv do_ipc_transfer_globals_equiv
            thread_set_globals_equiv handle_fault_reply_globals_equiv dxo_wp_weak
            thread_set_valid_arch_state
         | wpc | simp split del: if_split add: tcb_cap_cases_def)+
     apply (rule_tac Q'="\<lambda>_. globals_equiv st and valid_arch_state and valid_objs and valid_arch_state
                                             and valid_global_refs and valid_global_objs
                                             and (\<lambda>s. receiver \<noteq> idle_thread s) and valid_idle"
                  in hoare_strengthen_post)
      apply (wp gts_wp | fastforce simp: pred_tcb_at_def obj_at_def valid_idle_def)+
  done

lemma handle_reply_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
                     and valid_global_objs and valid_idle\<rbrace>
   handle_reply
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding handle_reply_def
  apply (wp do_reply_transfer_globals_equiv | wpc)+
    apply (rule_tac Q'="\<lambda>_. globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
                                            and valid_global_objs and valid_idle"
                 in hoare_strengthen_post)
     apply (wp | simp)+
  done

end


lemma reply_from_kernel_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
   reply_from_kernel thread x
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding reply_from_kernel_def
  by (wpsimp wp: set_message_info_globals_equiv set_mrs_globals_equiv as_user_globals_equiv)


section "reads_respects_g"

subsection "Notifications"

context Ipc_IF_1 begin

lemma send_signal_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l
     (pas_refined aag and pas_cur_domain aag and valid_objs
                      and valid_arch_state and valid_global_refs
                      and pspace_distinct and valid_idle and ct_active
                      and sym_refs \<circ> state_refs_of and is_subject aag \<circ> cur_thread
                      and K ((pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag))
     (send_signal ntfnptr badge)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule send_signal_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp send_signal_globals_equiv | simp)+
  done

end


lemma receive_signal_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "reads_respects_g aag (l :: 'a subject_label)
       (valid_global_objs and valid_objs and valid_arch_state and valid_global_refs
                          and pspace_distinct and pas_refined aag and (\<lambda>s. thread \<noteq> idle_thread s)
                          and is_subject aag \<circ> cur_thread
                          and K (\<forall>nptr\<in>obj_refs_ac cap.
                                   (pasSubject aag, Receive, pasObjectAbs aag nptr) \<in> pasPolicy aag
                                 \<and> is_subject aag thread))
       (receive_signal thread cap is_blocking)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule receive_signal_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp receive_signal_globals_equiv | simp)+
  done


context Ipc_IF_2 begin

subsection "Sync IPC"

lemma send_ipc_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "reads_respects_g aag l
       (pas_refined aag and pas_cur_domain aag and invs and is_subject aag \<circ> cur_thread
                        and (\<lambda>s. (can_grant \<longrightarrow> aag_has_auth_to aag Grant epptr))
                        and K (is_subject aag thread \<and> aag_has_auth_to aag SyncSend epptr))
       (send_ipc block call badge can_grant can_grant_reply thread epptr)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule send_ipc_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp send_ipc_globals_equiv | simp)+
  by fastforce

lemma receive_ipc_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "reads_respects_g aag l
       (invs and (\<lambda>s. receiver \<noteq> idle_thread s) and pas_refined aag
             and pas_cur_domain aag and valid_cap cap and is_subject aag \<circ> cur_thread
             and K (is_subject aag receiver \<and> pas_cap_cur_auth aag cap \<and> AllowRead \<in> cap_rights cap))
       (receive_ipc receiver cap is_blocking)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule receive_ipc_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp receive_ipc_globals_equiv | simp)+
  by fastforce

subsection "Faults"

lemma send_fault_ipc_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l
   (invs and pas_refined aag and pas_cur_domain aag
         and is_subject aag \<circ> cur_thread and K (is_subject aag thread \<and> valid_fault fault))
     (send_fault_ipc thread fault)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule send_fault_ipc_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp send_fault_ipc_globals_equiv | simp)+
  by fastforce

lemma handle_fault_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "reads_respects_g aag l
       (invs and pas_refined aag and pas_cur_domain aag
             and is_subject aag \<circ> cur_thread and K (is_subject aag thread \<and> valid_fault fault))
       (handle_fault thread fault)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule handle_fault_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp handle_fault_globals_equiv | simp)+
  by fastforce

subsection "Replies"

lemma handle_fault_reply_reads_respects_g:
  "reads_respects_g aag l
     (valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s) and K (is_subject aag thread))
     (handle_fault_reply fault thread x y)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule handle_fault_reply_reads_respects)
   apply (rule doesnt_touch_globalsI)
   apply (wp handle_fault_reply_globals_equiv | simp)+
  done

lemma do_reply_transfer_reads_respects_f_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "reads_respects_f_g aag l (silc_inv aag st and invs and pas_refined aag and pas_cur_domain aag
                                               and tcb_at receiver and tcb_at sender
                                               and emptyable slot and is_subject aag \<circ> cur_thread
                                               and K (grant \<longrightarrow> is_subject aag receiver)
                                               and K (is_subject aag sender \<and>
                                                      aag_can_read aag receiver \<and>
                                                      is_subject aag (fst slot)))
                        (do_reply_transfer sender receiver slot grant)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_f_g])
    apply (rule do_reply_transfer_reads_respects_f[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp do_reply_transfer_globals_equiv | simp)+
  apply (simp add: invs_def valid_state_def valid_pspace_def | blast)+
  done

lemma handle_reply_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "reads_respects_f_g aag l (silc_inv aag st and invs and pas_refined aag and pas_cur_domain aag
                                               and is_subject aag \<circ> cur_thread) (handle_reply)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_f_g])
    apply (rule handle_reply_reads_respects_f[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp handle_reply_globals_equiv | simp)+
  apply (simp add: invs_def valid_state_def valid_pspace_def | blast)+
  done

lemma reply_from_kernel_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "reads_respects_g aag l (valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)
                                              and K (is_subject aag thread))
                      (reply_from_kernel thread x)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule reply_from_kernel_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp reply_from_kernel_globals_equiv | simp)+
  done

lemmas lookup_ipc_buffer_reads_respects_g =
  reads_respects_g_from_inv[OF lookup_ipc_buffer_reads_respects lookup_ipc_buffer_inv]

end

end
