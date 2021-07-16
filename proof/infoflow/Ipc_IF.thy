(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_IF
imports Finalise_IF
begin

context begin interpretation Arch . (*FIXME: arch_split*)

section "reads_respects"
subsection "Notifications"

lemma equiv_valid_2_get_assert:
  "equiv_valid_2 I A A R P P' f f' \<Longrightarrow>
   equiv_valid_2 I A A R P P' (get >>= (\<lambda> s. assert (g s) >>= (\<lambda> y. f))) (get >>= (\<lambda> s. assert (g' s) >>= (\<lambda> y. f')))"
  apply(rule equiv_valid_2_guard_imp)
   apply(rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
       apply(rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
          apply assumption
         apply(simp add: assert_ev2)
        apply(wp equiv_valid_rv_trivial | simp)+
  done

lemma dummy_machine_state_update:
  "st = st\<lparr>machine_state := machine_state st\<rparr>"
  apply simp
  done

lemma dmo_storeWord_modifies_at_most:
  "modifies_at_most aag (pasObjectAbs aag ` ptr_range p 2) \<top>
        (do_machine_op (storeWord p w))"
  apply(rule modifies_at_mostI)
  apply(simp add: do_machine_op_def storeWord_def)
  apply(wp modify_wp | simp add: split_def)+
  apply clarsimp
  apply(erule use_valid)
  apply(wp modify_wp)
  apply(clarsimp simp: equiv_but_for_labels_def)
  apply(subst (asm) is_aligned_mask[symmetric])
  apply(subst dummy_machine_state_update)
  apply(rule states_equiv_for_machine_state_update)
   apply assumption
  apply (erule states_equiv_forE_mem)
  apply (intro conjI equiv_forI)
   apply(fastforce simp: image_def dest: distinct_lemma[where f="pasObjectAbs aag"] intro: ptr_range_memI ptr_range_add_memI)+
  done



lemma get_object_reads_respects:
  "reads_respects aag l (K (aag_can_read aag oref \<or> aag_can_affect aag l oref)) (get_object oref)"
  unfolding get_object_def
  apply(subst gets_apply)
  apply(wp gets_apply_ev | wpc | simp)+
  apply(blast intro: reads_affects_equiv_kheap_eq)
  done

lemma get_cap_reads_respects:
  "reads_respects aag l (K (aag_can_read aag (fst slot) \<or> aag_can_affect aag l (fst slot))) (get_cap slot)"
  apply(simp add: get_cap_def split_def)
  apply(wp get_object_reads_respects | wpc | simp)+
  done

lemma lookup_ipc_buffer_reads_respects:
  "reads_respects aag l (K (aag_can_read aag thread \<or> aag_can_affect aag l thread)) (lookup_ipc_buffer is_receiver thread)"
  unfolding lookup_ipc_buffer_def
  apply(wp thread_get_reads_respects get_cap_reads_respects | wpc | simp)+
  done


lemmas lookup_ipc_buffer_reads_respects_g = reads_respects_g_from_inv[OF lookup_ipc_buffer_reads_respects lookup_ipc_buffer_inv]

lemma as_user_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L)\<rbrace>
    as_user thread f
    \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding as_user_def
  apply (wp set_object_equiv_but_for_labels | simp add: split_def)+
  apply(blast dest: get_tcb_not_asid_pool_at)
  done

crunch equiv_but_for_labels: set_message_info "equiv_but_for_labels aag L st"


lemma storeWord_equiv_but_for_labels:
  "\<lbrace>\<lambda>ms. equiv_but_for_labels aag L st (s\<lparr>machine_state := ms\<rparr>) \<and>
        for_each_byte_of_word (\<lambda> x. pasObjectAbs aag x \<in> L) p\<rbrace>
    storeWord p v \<lbrace>\<lambda>a b. equiv_but_for_labels aag L st (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  unfolding storeWord_def
  apply (wp modify_wp)
  apply (clarsimp simp: equiv_but_for_labels_def)
  apply (rule states_equiv_forI)
            apply(fastforce intro!: equiv_forI elim!: states_equiv_forE dest: equiv_forD[where f=kheap])
           apply (simp add: states_equiv_for_def)
          apply (rule conjI)
           apply(rule equiv_forI)
           apply clarsimp
           apply(drule_tac f=underlying_memory in equiv_forD,fastforce)
           apply(fastforce intro: is_aligned_no_wrap' word_plus_mono_right simp: is_aligned_mask for_each_byte_of_word_def)
           apply(rule equiv_forI)
          apply clarsimp
          apply(drule_tac f=device_state in equiv_forD,fastforce)
          apply clarsimp
         apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=cdt])
        apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=ekheap])
       apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=cdt_list])
      apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=is_original_cap])
     apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=interrupt_states])
    apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=interrupt_irq_node])
   apply(fastforce simp: equiv_asids_def equiv_asid_def elim: states_equiv_forE)
  apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=ready_queues])
  done

lemma store_word_offs_equiv_but_for_labels:
  "\<lbrace> equiv_but_for_labels aag L st and K (for_each_byte_of_word (\<lambda>x. pasObjectAbs aag x \<in> L) (ptr + of_nat offs * of_nat word_size)) \<rbrace>
   store_word_offs ptr offs v
   \<lbrace> \<lambda>_. equiv_but_for_labels aag L st \<rbrace>"
  unfolding store_word_offs_def
  apply(wp modify_wp | simp add: do_machine_op_def split_def)+
  apply clarsimp
  apply(erule use_valid[OF _ storeWord_equiv_but_for_labels])
  apply simp
  done

definition
  ipc_buffer_has_read_auth :: "'a PAS \<Rightarrow> 'a \<Rightarrow> word32 option \<Rightarrow> bool"
where
"ipc_buffer_has_read_auth aag l \<equiv>
    case_option True (\<lambda>buf'. is_aligned buf' msg_align_bits \<and> (\<forall>x \<in> ptr_range buf' msg_align_bits. (l,Read,pasObjectAbs aag x) \<in> (pasPolicy aag)))"


lemma set_mrs_equiv_but_for_labels:
  "\<lbrace> equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L \<and>
       (case buf of (Some buf') \<Rightarrow>
        is_aligned buf' msg_align_bits \<and>
        (\<forall>x \<in> ptr_range buf' msg_align_bits. pasObjectAbs aag x \<in> L)
                 | _ \<Rightarrow> True)) \<rbrace>
   set_mrs thread buf msgs
   \<lbrace> \<lambda>_. equiv_but_for_labels aag L st \<rbrace>"
  unfolding set_mrs_def
  apply (wp | wpc)+
       apply(subst zipWithM_x_mapM_x)
       apply(rule_tac Q="\<lambda>_. equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L  \<and>
       (case buf of (Some buf') \<Rightarrow>
        is_aligned buf' msg_align_bits \<and>
        (\<forall>x \<in> ptr_range buf' msg_align_bits. pasObjectAbs aag x \<in> L)
                 | _ \<Rightarrow> True))" in hoare_strengthen_post)
       apply(wp mapM_x_wp' store_word_offs_equiv_but_for_labels | simp add: split_def)+
        apply(case_tac xa, clarsimp split: if_split_asm elim!: in_set_zipE)
        apply(clarsimp simp: for_each_byte_of_word_def)
        apply(erule bspec)
        apply(clarsimp simp: ptr_range_def)
        apply(rule conjI)
         apply(erule order_trans[rotated])
         apply(erule is_aligned_no_wrap')
         apply(rule mul_word_size_lt_msg_align_bits_ofnat)
         apply(fastforce simp: msg_max_length_def msg_align_bits')
        apply(erule order_trans)
        apply(subst p_assoc_help)
        apply(simp add: add.assoc)
        apply(rule word_plus_mono_right)
         apply(rule word_less_sub_1)
         apply(rule_tac y="of_nat msg_max_length * of_nat word_size + 3" in le_less_trans)
          apply(rule word_plus_mono_left)
           apply(rule word_mult_le_mono1)
             apply(erule disjE)
              apply(rule word_of_nat_le)
              apply(simp add: msg_max_length_def)
             apply clarsimp
             apply(rule word_of_nat_le)
             apply(simp add: msg_max_length_def)
            apply(simp add: word_size_def)
           apply(simp add: msg_max_length_def word_size_def)
          apply(simp add: msg_max_length_def word_size_def)
         apply(rule mul_add_word_size_lt_msg_align_bits_ofnat)
          apply(simp add: msg_max_length_def msg_align_bits')
         apply(simp add: word_size_def)
        apply(erule is_aligned_no_overflow')
       apply simp
      apply(wp set_object_equiv_but_for_labels hoare_vcg_all_lift static_imp_wp | simp)+
   apply (fastforce dest: get_tcb_not_asid_pool_at)+
  done


definition all_to_which_has_auth where
  "all_to_which_has_auth aag auth source \<equiv> {t. (source,auth,t) \<in> pasPolicy aag}"

definition all_with_auth_to where
  "all_with_auth_to aag auth target \<equiv> {x. (x, auth, target) \<in> pasPolicy aag}"

lemma valid_ntfn_WaitingNtfn_tl:
  "\<lbrakk>ntfn_obj ntfn = (WaitingNtfn list); valid_ntfn ntfn s; tl list \<noteq> []; ntfn' = ntfn\<lparr>ntfn_obj := (WaitingNtfn (tl list))\<rparr> \<rbrakk> \<Longrightarrow>
   valid_ntfn ntfn' s"
  apply(case_tac list, simp_all)
  apply(rename_tac a lista)
  apply(case_tac lista, simp_all)
  apply(clarsimp simp: valid_ntfn_def split: option.splits)
  done

(* FIXME: many redundant conditions *)
lemma update_waiting_ntfn_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pspace_aligned and valid_vspace_objs and valid_arch_state and valid_objs and
                         sym_refs \<circ> state_refs_of and pas_refined aag and pas_cur_domain aag and
                         ko_at (Notification ntfn) ntfnptr and (\<lambda>s. is_subject aag (cur_thread s)) and
                         K (ntfn_obj ntfn = WaitingNtfn queue)) (update_waiting_ntfn ntfnptr queue bound_tcb badge)"
  unfolding update_waiting_ntfn_def fun_app_def
  apply (wp assert_sp possible_switch_to_reads_respects gets_cur_thread_ev | simp add: split_def)+
  apply (wp as_user_set_register_reads_respects' set_thread_state_reads_respects
            set_simple_ko_reads_respects set_thread_state_pas_refined
            set_simple_ko_valid_objs hoare_vcg_disj_lift set_simple_ko_pas_refined
         | simp add: split_def)+
  done

lemma set_thread_state_ext_runnable_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L) and st_tcb_at runnable thread\<rbrace>
    set_thread_state_ext thread
    \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (simp add: set_thread_state_ext_def)
  apply wp
     apply (rule hoare_pre_cont)
    apply (wp gts_wp)+
  apply (force simp: st_tcb_at_def obj_at_def)
  done

lemma set_thread_state_runnable_equiv_but_for_labels:
  "runnable tst \<Longrightarrow> \<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L)\<rbrace>
    set_thread_state thread tst
    \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_equiv_but_for_labels[THEN hoare_set_object_weaken_pre]
                    set_thread_state_ext_runnable_equiv_but_for_labels)
    apply (wpsimp wp: set_object_wp)+
  apply (fastforce dest: get_tcb_not_asid_pool_at simp: st_tcb_at_def obj_at_def)
  done

lemma tcb_sched_action_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag thread \<in> L) and pas_refined aag\<rbrace>
    tcb_sched_action action thread
    \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (simp add: tcb_sched_action_def, wp)
  apply (clarsimp simp: etcb_at_def equiv_but_for_labels_def split: option.splits)
  apply (rule states_equiv_forI)
           apply(fastforce intro!: equiv_forI elim!: states_equiv_forE dest: equiv_forD[where f=kheap])
          apply (simp add: states_equiv_for_def)
         apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=cdt])
        apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=ekheap])
       apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=cdt_list])
      apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=is_original_cap])
     apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=interrupt_states])
    apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=interrupt_irq_node])
   apply(fastforce simp: equiv_asids_def equiv_asid_def elim: states_equiv_forE)
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def split: option.splits)
  apply (rule equiv_forI)
  apply (erule_tac x="(thread, tcb_domain (the (ekheap s thread)))" in ballE)
   apply(fastforce elim: states_equiv_forE intro: equiv_forI dest: equiv_forD[where f=ready_queues])
  apply (force intro: domtcbs)
  done

lemma possible_switch_to_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and (\<lambda>s. etcb_at (\<lambda>etcb. tcb_domain etcb \<noteq> cur_domain s) target s) and K (pasObjectAbs aag target \<in> L) and pas_refined aag\<rbrace>
    possible_switch_to target
    \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (simp add: possible_switch_to_def)
  apply (wp tcb_sched_action_equiv_but_for_labels)
       (* possible_switch_to does not modify scheduler action if target is in different domain *)
       apply (rule hoare_pre_cont)
      apply (wp tcb_sched_action_equiv_but_for_labels)
      apply (rule hoare_pre_cont)
     apply (wp tcb_sched_action_equiv_but_for_labels)+
  apply (clarsimp simp: etcb_at_def split: option.splits)
  done

crunch etcb_at_cdom[wp]: set_thread_state_ext, set_thread_state, set_simple_ko
   "\<lambda>s. etcb_at (P (cur_domain s)) t s"
  (wp: crunch_wps)

lemma update_waiting_ntfn_equiv_but_for_labels:
  "\<lbrace> equiv_but_for_labels aag L st and pas_refined aag and
     pspace_aligned and valid_vspace_objs and valid_arch_state and valid_objs and
     ko_at (Notification ntfn) ntfnptr and
     sym_refs \<circ> state_refs_of and
     (\<lambda>s. \<forall>t\<in> set list. etcb_at (\<lambda>etcb. tcb_domain etcb \<noteq> cur_domain s) t s) and
     K (ntfn_obj ntfn = WaitingNtfn list \<and> pasObjectAbs aag ntfnptr \<in> L \<and>
        all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr) \<subseteq> L \<and>
       \<Union> ((all_to_which_has_auth aag Write) ` (all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr))) \<subseteq> L)\<rbrace>
   update_waiting_ntfn ntfnptr list boundtcb badge
   \<lbrace> \<lambda>_. equiv_but_for_labels aag L st \<rbrace>"
  unfolding update_waiting_ntfn_def
  apply (wp static_imp_wp as_user_equiv_but_for_labels set_thread_state_runnable_equiv_but_for_labels
            set_thread_state_pas_refined set_notification_equiv_but_for_labels
            set_simple_ko_pred_tcb_at set_simple_ko_pas_refined
            hoare_vcg_disj_lift possible_switch_to_equiv_but_for_labels
        | wpc | simp add: split_def)+
  apply clarsimp
  apply(frule_tac P="receive_blocked_on ntfnptr" and t="hd list" in ntfn_queued_st_tcb_at')
      apply(fastforce)
     apply assumption
    apply assumption
   apply simp
  apply (subgoal_tac "pasObjectAbs aag (hd list) \<in> all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr)")
   apply(fastforce)
  apply(clarsimp simp: all_with_auth_to_def)
  apply (erule pas_refined_mem[rotated])
  apply (rule sta_ts)
  apply(clarsimp simp: thread_st_auth_def split: option.split simp: tcb_states_of_state_def st_tcb_def2)
  apply(case_tac "tcb_state tcb", simp_all)
  done


lemma update_waiting_ntfn_modifies_at_most:
  "modifies_at_most aag
          ({pasObjectAbs aag ntfnptr} \<union>
           all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr) \<union>
           \<Union> ((all_to_which_has_auth aag Write) ` (all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr))))
          (pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state and
           valid_objs and ko_at (Notification ntfn) ntfnptr and
           (\<lambda>s. \<forall>t\<in> set list. etcb_at (\<lambda>etcb. tcb_domain etcb \<noteq> cur_domain s) t s) and
           sym_refs \<circ> state_refs_of and K (ntfn_obj ntfn = WaitingNtfn list))
          (update_waiting_ntfn ntfnptr list boundtcb badge)"
  apply(rule modifies_at_mostI)
  apply(wp update_waiting_ntfn_equiv_but_for_labels | fastforce)+
  done


lemma invisible_ntfn_invisible_receivers_and_ipcbuffers:
  "\<lbrakk>labels_are_invisible aag l {pasObjectAbs aag ntfnptr};
    (pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag\<rbrakk>
    \<Longrightarrow> labels_are_invisible aag l
        ({pasObjectAbs aag ntfnptr} \<union>
         all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr) \<union>
         \<Union>(all_to_which_has_auth aag Write `
          all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr)))"
  apply(auto simp: labels_are_invisible_def aag_can_affect_label_def dest: reads_read_page_read_thread reads_read_queued_thread_read_ep simp: all_to_which_has_auth_def all_with_auth_to_def)
  done

lemma invisible_ntfn_invisible_receivers_and_receivers:
  "\<lbrakk>labels_are_invisible aag l {pasObjectAbs aag ntfnptr};
    (pasSubject aag, auth, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag;
    auth \<in> {Notify,Receive,SyncSend}\<rbrakk>
    \<Longrightarrow> labels_are_invisible aag l
        ({pasObjectAbs aag ntfnptr} \<union>
         all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr) \<union>
         (\<Union>(all_to_which_has_auth aag Receive `
          all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr))) \<union>
         (\<Union>(all_to_which_has_auth aag Write `
          all_with_auth_to aag Receive (pasObjectAbs aag ntfnptr))))"
  by (auto simp: labels_are_invisible_def aag_can_affect_label_def
        dest: read_sync_ep_read_senders_strong read_sync_ep_read_receivers_strong
              reads_read_queued_thread_read_ep
              reads_read_page_read_thread
              reads_ep
        simp: all_to_which_has_auth_def all_with_auth_to_def)

lemma read_queued_thread_reads_ntfn:
  "\<lbrakk>ko_at (Notification ntfn) ntfnptr s; t \<in> set queue; aag_can_read aag t;
    valid_objs s; sym_refs (state_refs_of s); pas_refined aag s; ntfn_obj ntfn = WaitingNtfn queue;
    (pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag\<rbrakk>
  \<Longrightarrow> aag_can_read aag ntfnptr"
  apply(frule_tac P="receive_blocked_on ntfnptr" and t=t in ntfn_queued_st_tcb_at')
      apply(fastforce)
     apply assumption
    apply assumption
   apply simp
  apply (rule_tac t="pasObjectAbs aag t" and auth="Receive" and auth'="Notify" in reads_read_queued_thread_read_ep)
      apply assumption
     apply simp
    apply (erule pas_refined_mem[rotated])
    apply (rule sta_ts)
    apply(clarsimp simp: thread_st_auth_def split: option.split simp: tcb_states_of_state_def st_tcb_def2)
    apply (case_tac "tcb_state tcb", simp_all)[1]
   apply simp
  apply simp
  done

lemma not_etcb_at_not_cdom_can_read:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrakk>\<not> etcb_at (\<lambda>etcb. tcb_domain etcb \<noteq> cur_domain s) t s;
   tcb_at t s; valid_etcbs s; pas_refined aag s; pas_cur_domain aag s\<rbrakk>
  \<Longrightarrow> aag_can_read aag t"
  apply (clarsimp simp: valid_etcbs_def tcb_at_st_tcb_at etcb_at_def is_etcb_at_def
                        pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (erule_tac x="(t, cur_domain s)" in ballE)
   apply (force dest: domains_distinct[THEN pas_domains_distinct_inj])
  apply (force intro: domtcbs)
  done

lemma tcb_at_ntfn_queue:
  "\<lbrakk>valid_objs s; t \<in> set queue; ko_at (Notification ntfn) ntfnptr s; ntfn_obj ntfn = WaitingNtfn queue\<rbrakk>
  \<Longrightarrow> tcb_at t s"
  apply (erule valid_objsE, force simp: obj_at_def)
  apply (simp add: valid_obj_def valid_ntfn_def)
  done


lemma invisible_ep_invisible_receiver:
  "\<lbrakk>labels_are_invisible aag l {pasObjectAbs aag epptr};
    (pasObjectAbs aag tcb, Receive, pasObjectAbs aag epptr) \<in> pasPolicy aag;
    (pasObjectAbs aag tcb, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag\<rbrakk>
   \<Longrightarrow> labels_are_invisible aag l
          ({pasObjectAbs aag epptr} \<union> {pasObjectAbs aag tcb})"
  apply (auto simp: labels_are_invisible_def aag_can_affect_label_def
                    all_with_auth_to_def
                  dest: reads_ep reads_read_queued_thread_read_ep)
  done


lemma no_fail_gts:"no_fail (tcb_at tcb) (get_thread_state tcb)"
  apply (clarsimp simp: get_thread_state_def thread_get_def)
  apply (rule no_fail_pre)
   apply wp
  by (clarsimp simp: get_tcb_def tcb_at_def)

lemma monadic_rewrite_impossible: "monadic_rewrite F E (\<lambda>_. False) f g"
  by (clarsimp simp: monadic_rewrite_def)

lemma monadic_rewrite_add_get:
  "monadic_rewrite F E P (do x <- get; f od) (do x <- get; g od) \<Longrightarrow>
       monadic_rewrite F E P f g"
       by (clarsimp simp: bind_def get_def)

lemma sts_noop:
   "monadic_rewrite True True (tcb_at tcb and (\<lambda>s. tcb \<noteq> cur_thread s))
   (set_thread_state_ext tcb)
   (return ())"
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_add_get)
   apply (rule monadic_rewrite_bind_tail)
    apply (clarsimp simp: set_thread_state_ext_def)
    apply (rule_tac x="tcb_state (the (get_tcb tcb x))" in monadic_rewrite_symb_exec)
       apply (wp gts_wp | simp)+
    apply (rule monadic_rewrite_symb_exec)
       apply wp+
    apply (rule monadic_rewrite_symb_exec)
       apply wp+
    apply (simp only: when_def)
    apply (rule monadic_rewrite_trans)
     apply (rule monadic_rewrite_if)
      apply (rule monadic_rewrite_impossible[where g="return ()"])
     apply (rule monadic_rewrite_refl)
    apply simp
    apply (rule monadic_rewrite_refl)
   apply wp
  by (auto simp: pred_tcb_at_def obj_at_def is_tcb_def get_tcb_def)

lemma sts_to_modify':
  "monadic_rewrite True True (tcb_at tcb and (\<lambda>s :: det_ext state. tcb \<noteq> cur_thread s))
       (set_thread_state tcb st)  (modify (\<lambda>s. s\<lparr>kheap := kheap s(tcb \<mapsto> TCB (the (get_tcb tcb s)\<lparr>tcb_state := st\<rparr>))\<rparr>))"
  apply (clarsimp simp: set_thread_state_def set_object_def)
  apply (rule monadic_rewrite_add_get)
  apply (rule monadic_rewrite_bind_tail)
   apply (rule monadic_rewrite_imp)
    apply (rule monadic_rewrite_trans)
     apply (simp only: bind_assoc[symmetric])
     apply (rule monadic_rewrite_bind_tail)
      apply (rule sts_noop)
     apply (wpsimp wp: get_object_wp, simp)
    apply (rule_tac x="the (get_tcb tcb x)" in monadic_rewrite_symb_exec, (wp | simp)+)
    apply (rule_tac x="x" in  monadic_rewrite_symb_exec, (wp | simp)+)
        apply (wpsimp wp: get_object_wp simp: a_type_def)+
    apply (rule_tac P="(=) x" in monadic_rewrite_refl3)
    apply (clarsimp simp add: put_def modify_def get_def bind_def)
   apply assumption
  apply wp
  by (clarsimp simp: get_tcb_def tcb_at_def)


lemma
  monadic_rewrite_weaken_failure:
  "monadic_rewrite True True P f f' \<Longrightarrow>
  no_fail P' f \<Longrightarrow> no_fail Q' f' \<Longrightarrow>
   monadic_rewrite F E (P and P' and Q') f f'"
  by (clarsimp simp: monadic_rewrite_def no_fail_def)

lemma
  sts_no_fail:
  "no_fail (\<lambda>s :: det_ext state. tcb_at tcb s) (set_thread_state tcb st)"
  apply (simp add: set_thread_state_def set_object_def)
  apply (simp add: set_thread_state_ext_def get_thread_state_def thread_get_def set_scheduler_action_def)
  apply (rule no_fail_pre)
   apply (wpsimp wp: get_object_wp)+
  apply (clarsimp simp: get_tcb_def tcb_at_def obj_at_def a_type_def is_tcb_def split: kernel_object.splits option.splits)
  by (metis kernel_object.exhaust option.inject)

lemmas sts_to_modify = monadic_rewrite_weaken_failure[OF sts_to_modify' sts_no_fail no_fail_modify,simplified]

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
      "monadic_rewrite False False
       (\<lambda>s. st_tcb_at receive_blocked tcb (s :: det_ext state) \<and>
       cur_thread s \<noteq> tcb)
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
       apply (rule monadic_rewrite_refl2)
       apply (fastforce simp add: simpler_modify_def o_def get_tcb_def)
      apply (wp gts_wp)+
  apply (simp add: set_thread_state_def bind_assoc gets_the_def)
  apply (clarsimp simp add: pred_tcb_at_def receive_blocked_def obj_at_def is_tcb_def split: thread_state.splits)
  by (case_tac "tcb_state tcba";fastforce)


lemma gts_reads_respects:
  "reads_respects aag l (K (aag_can_read aag thread \<or> aag_can_affect aag l thread)) (get_thread_state thread)"
  unfolding get_thread_state_def
  by (wp thread_get_reads_respects)


lemma ev2_invisible_simple:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "labels_are_invisible aag l L \<Longrightarrow>
       modifies_at_most aag L Q f \<Longrightarrow>
       reads_respects aag l Q (f :: det_ext state \<Rightarrow> (unit \<times> det_ext state) set \<times> bool)"
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_2_guard_imp)
    apply (rule ev2_invisible[OF domains_distinct])
        by fastforce+

lemma blocked_cancel_ipc_nosts_equiv_but_for_labels:
  "\<lbrace>pas_refined aag and
    st_tcb_at (\<lambda>st. st = BlockedOnReceive x pl) t and
    bound_tcb_at ((=) (Some ntfnptr)) t and
    equiv_but_for_labels aag L st and
    K(pasObjectAbs aag x \<in> L) and
    K(pasObjectAbs aag t \<in> L) \<rbrace>
   blocked_cancel_ipc_nosts t
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding blocked_cancel_ipc_nosts_def get_blocking_object_def
  apply (wp set_endpoint_equiv_but_for_labels get_object_wp gts_wp
            set_thread_state_runnable_equiv_but_for_labels
       | wpc
       | simp)+
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma blocked_cancel_ipc_nosts_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pas_refined aag
                          and st_tcb_at (\<lambda>st. \<exists>xa. st = (BlockedOnReceive x pl)) t

                          and bound_tcb_at ((=) (Some ntfnptr)) t
                          and (\<lambda>s. is_subject aag (cur_thread s))
                          and K (
                              (pasObjectAbs aag t, Receive, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag
                            \<and> (pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag
                            \<and> (pasObjectAbs aag t, Receive, pasObjectAbs aag x) \<in> pasPolicy aag))
           (blocked_cancel_ipc_nosts t)"
  unfolding blocked_cancel_ipc_nosts_def
  apply (simp only:bind_assoc[symmetric])
  apply (rule bind_ev[where P''=\<top>,simplified])
    apply (wp set_thread_state_runnable_reads_respects,simp)

    subgoal
    proof (cases "aag_can_read_label aag (pasObjectAbs aag x) \<or> aag_can_affect aag l x")
      case True thus ?thesis \<comment> \<open>boring case, can read or affect ep\<close>
      unfolding blocked_cancel_ipc_nosts_def get_blocking_object_def
      apply clarsimp
      apply (rule pre_ev)
       apply ((wp set_thread_state_reads_respects get_ep_queue_reads_respects
                  get_simple_ko_reads_respects get_blocking_object_reads_respects
                  gts_reads_respects set_simple_ko_reads_respects
                  gts_wp
                  | wpc
                  | simp add: get_blocking_object_def get_thread_state_rev)+)[2]
      apply (clarsimp simp: pred_tcb_at_def obj_at_def)
      by (fastforce dest:read_sync_ep_read_receivers_strong )

    next
      case False thus ?thesis apply -  \<comment> \<open>can't read or affect ep\<close>
      apply (rule gen_asm_ev)
      apply (drule label_is_invisible[THEN iffD2])
      apply clarsimp
      apply (rule ev2_invisible_simple[OF domains_distinct],assumption)
      apply (simp add: get_blocking_object_def)
      apply (rule modifies_at_mostI)
      apply (rule hoare_pre)
       apply (wp set_thread_state_runnable_equiv_but_for_labels
                 set_endpoint_equiv_but_for_labels get_object_wp gts_wp
                 set_thread_state_runnable_equiv_but_for_labels
            | wpc
            | simp)+
      by (fastforce simp: pred_tcb_at_def obj_at_def)
    qed
  by wp

crunch silc_inv[wp]: "blocked_cancel_ipc_nosts" "silc_inv aag st"

lemmas blocked_cancel_ipc_nosts_reads_respects_f =
  reads_respects_f[where Q=\<top>,simplified,
                   OF blocked_cancel_ipc_nosts_reads_respects
                      blocked_cancel_ipc_nosts_silc_inv,
                      simplified]

lemma monadic_rewrite_is_valid:
  "monadic_rewrite False False P' f f' \<Longrightarrow>
  \<lbrace>P\<rbrace> do x <- f; g x od \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P and P'\<rbrace> do x <- f'; g x od  \<lbrace>Q\<rbrace>"
  by (fastforce simp: monadic_rewrite_def valid_def bind_def)

lemma monadic_rewrite_reads_respects:
  "monadic_rewrite False False P f f' \<Longrightarrow>
   reads_respects l aag P' (do x <- f; g x od) \<Longrightarrow>
   reads_respects l aag (P and P') (do x <- f'; g x od)"
  apply (clarsimp simp: monadic_rewrite_def equiv_valid_def
                        spec_equiv_valid_def equiv_valid_2_def
                        bind_def)
  apply (frule_tac x=st in spec)
  apply (drule_tac x=t in spec)
  by fastforce


lemmas cancel_ipc_reads_respects_rewrite =
  monadic_rewrite_reads_respects[OF cancel_ipc_to_blocked_nosts, simplified bind_assoc]

lemmas cancel_ipc_valid_rewrite =
  monadic_rewrite_is_valid[OF cancel_ipc_to_blocked_nosts, simplified bind_assoc]

crunch etcb_at[wp]: blocked_cancel_ipc_nosts "etcb_at P t"
crunch cur_domain[wp]: blocked_cancel_ipc_nosts "\<lambda>s. P (cur_domain s)"
crunch pas_refined[wp]: blocked_cancel_ipc_nosts "pas_refined aag"
crunch cur_thread[wp]: blocked_cancel_ipc_nosts "\<lambda>s. P (cur_thread s)"

lemma BlockedOnReceive_inj:
  "x = (case (BlockedOnReceive x pl) of BlockedOnReceive x pl \<Rightarrow> x)"
  "pl = (case (BlockedOnReceive x pl) of BlockedOnReceive x pl \<Rightarrow> pl)"
  by auto

lemma receive_blockedD:
  "receive_blocked st \<Longrightarrow> \<exists>epptr pl. st = BlockedOnReceive epptr pl"
  by (cases st; simp add: receive_blocked_def)

crunches blocked_cancel_ipc_nosts
  for pspace_aligned[wp]: pspace_aligned
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_arch_state[wp]: valid_arch_state

lemma send_signal_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes set_thread_state_owned_reads_respects[wp del]
        cancel_ipc_pas_refined[wp del]
  shows
  "reads_respects aag l (pas_refined aag and pas_cur_domain aag and
                         pspace_aligned and valid_vspace_objs and valid_arch_state and
                         (\<lambda>s. is_subject aag (cur_thread s)) and valid_etcbs and ct_active and
                         (\<lambda>s. sym_refs (state_refs_of s)) and valid_objs and
                         K ((pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag))
                        (send_signal ntfnptr badge)"
  unfolding send_signal_def fun_app_def
  subgoal
  proof (cases "aag_can_read aag ntfnptr \<or> aag_can_affect aag l ntfnptr")
    case True
    note visible = this
    show ?thesis
    apply (rule pre_ev)
     apply (simp split del: if_split
          | rule_tac ntfnptr=ntfnptr in blocked_cancel_ipc_nosts_reads_respects
          | rule cancel_ipc_reads_respects_rewrite
          | wp (once)
              set_simple_ko_reads_respects
              possible_switch_to_reads_respects
              as_user_set_register_reads_respects'
              set_thread_state_pas_refined
              set_thread_state_pas_refined
              set_simple_ko_reads_respects
              gts_reads_respects
              cancel_ipc_receive_blocked_pas_refined
              gts_wp
              hoare_vcg_imp_lift
              update_waiting_ntfn_reads_respects
              get_simple_ko_wp
              get_simple_ko_reads_respects
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
      apply (fastforce dest:read_sync_ep_read_receivers_strong)
     apply (rule disjI2)
     apply (fastforce dest:read_sync_ep_read_receivers_strong)
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
     apply (fastforce simp: receive_blocked_def intro!: BlockedOnReceive_inj split:thread_state.splits)
    by (fastforce simp: pred_tcb_at_def get_tcb_def obj_at_def receive_blocked_def
                        ct_in_state_def
                  split:thread_state.splits)

  next
    case False note invisible = this show ?thesis
    apply (insert label_is_invisible[THEN iffD2, OF invisible])
    apply (rule gen_asm_ev)
    apply (drule (1) invisible_ntfn_invisible_receivers_and_receivers)
     apply simp
     apply (rule ev2_invisible_simple[OF domains_distinct],assumption)
     apply (rule modifies_at_mostI)

     apply ( simp split del: if_split
           | rule cancel_ipc_valid_rewrite
           | wp (once)
               set_notification_equiv_but_for_labels
               possible_switch_to_equiv_but_for_labels
               as_user_equiv_but_for_labels
               set_thread_state_runnable_equiv_but_for_labels
               set_thread_state_pas_refined
               blocked_cancel_ipc_nosts_equiv_but_for_labels
               gts_wp
               update_waiting_ntfn_equiv_but_for_labels
               get_simple_ko_wp
           | wpc
           | wps
           )+

    apply (elim conjE)
    apply (match premises in "ntfn_bound_tcb _ = _" \<Rightarrow> \<open>fail\<close>
                                               \<bar> _ \<Rightarrow> \<open>rule allI impI conjI\<close>)+
     prefer 2
     apply (intro conjI allI impI; fastforce?)
     subgoal waiting_ntfn
       apply clarsimp
       apply (rule ccontr)
       apply (frule (3) not_etcb_at_not_cdom_can_read[OF domains_distinct, rotated 2])
        apply (rule tcb_at_ntfn_queue;assumption)
       apply(frule (7) read_queued_thread_reads_ntfn)
       using invisible
       by (fastforce simp add: all_with_auth_to_def all_to_which_has_auth_def)

     apply (frule (1)
       ntfn_bound_tcb_at[where P="(=) (Some ntfnptr)",OF _ _ _ _ refl])
       apply (fastforce simp: obj_at_def)
      apply assumption
     apply (intro allI conjI impI)
            apply (fastforce simp: pred_tcb_at_def receive_blocked_def obj_at_def split:thread_state.splits
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
            apply (case_tac sta;(clarsimp simp: pred_tcb_at_def obj_at_def receive_blocked_def split:thread_state.splits))
            apply (rule get_tcb_recv_blocked_implies_receive, assumption)
             apply (fastforce simp: get_tcb_def)
            by (fastforce  split:thread_state.splits)
         apply (rule ccontr)
         apply (insert prems)
         apply (frule (4) not_etcb_at_not_cdom_can_read[OF domains_distinct])
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

lemma receive_signal_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (valid_objs and pas_refined aag and
        (\<lambda>s. is_subject aag (cur_thread s)) and
        K ((\<forall>ntfnptr\<in>Access.obj_refs cap.
            (pasSubject aag, Receive, pasObjectAbs aag ntfnptr)
             \<in> pasPolicy aag \<and> is_subject aag thread)))
         (receive_signal thread cap is_blocking)"
  unfolding receive_signal_def fun_app_def do_nbrecv_failed_transfer_def
  apply(wp set_simple_ko_reads_respects set_thread_state_reads_respects
           as_user_set_register_reads_respects' get_simple_ko_reads_respects hoare_vcg_all_lift
       | wpc
       | wp (once) hoare_drop_imps)+
  apply(force dest: reads_ep)
  done

subsection "Sync IPC"

(* FIXME move *)
lemma conj_imp:
  "\<lbrakk>Q \<longrightarrow> R; P \<longrightarrow> Q; P' \<longrightarrow> Q\<rbrakk> \<Longrightarrow>
    (P \<longrightarrow> R) \<and> (P' \<longrightarrow> R)"
  by(fastforce)

(* basically clagged directly from lookup_ipc_buffer_has_auth *)
lemma lookup_ipc_buffer_has_read_auth:
  "\<lbrace>pas_refined aag and valid_objs\<rbrace>
   lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda>rv s. ipc_buffer_has_read_auth aag (pasObjectAbs aag thread) rv\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: lookup_ipc_buffer_def)
   apply (wp get_cap_wp thread_get_wp'
        | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_read_auth_def get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (frule (1) caps_of_state_valid_cap)
  apply (clarsimp simp: vm_read_only_def vm_read_write_def)
  apply (rule_tac Q="AllowRead \<in> xc" in conj_imp)
    apply (clarsimp simp: valid_cap_simps cap_aligned_def)
    apply (rule conjI)
     apply (erule aligned_add_aligned)
      apply (rule is_aligned_andI1)
      apply (drule (1) valid_tcb_objs)
      apply (clarsimp simp: valid_obj_def valid_tcb_def valid_ipc_buffer_cap_def
                     split: if_splits)
     apply (rule order_trans [OF _ pbfs_atleast_pageBits])
     apply (simp add: msg_align_bits pageBits_def)
    apply (drule (1) cap_auth_caps_of_state)
    apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                          vspace_cap_rights_to_auth_def vm_read_only_def)
    apply (drule bspec)
     apply (erule (3) ipcframe_subset_page)
    apply (clarsimp split: if_split_asm simp: vspace_cap_rights_to_auth_def is_page_cap_def)
   apply(simp_all)
  done


definition
  aag_can_read_or_affect_ipc_buffer :: "'a PAS \<Rightarrow> 'a \<Rightarrow> word32 option \<Rightarrow> bool"
where
"aag_can_read_or_affect_ipc_buffer aag l \<equiv>
    case_option True (\<lambda>buf'. is_aligned buf' msg_align_bits \<and> (\<forall>x \<in> ptr_range buf' msg_align_bits. aag_can_read aag x \<or> aag_can_affect aag l x))"


lemma lookup_ipc_buffer_aag_can_read_or_affect:
  "\<lbrace>pas_refined aag and valid_objs and K (aag_can_read aag thread \<or> aag_can_affect aag l thread)\<rbrace>
    lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda>rv s. aag_can_read_or_affect_ipc_buffer aag l rv\<rbrace>"
  apply(rule hoare_gen_asm)
  apply(rule hoare_strengthen_post[OF lookup_ipc_buffer_has_read_auth])
  apply(auto simp: ipc_buffer_has_read_auth_def aag_can_read_or_affect_ipc_buffer_def intro: reads_read_thread_read_pages simp: aag_can_affect_label_def split: option.splits)
  done

lemma cptrs_in_ipc_buffer:
  "\<lbrakk>x \<in> set [buffer_cptr_index..<
             buffer_cptr_index + unat (mi_extra_caps mi)];
    is_aligned a msg_align_bits;
    buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits)\<rbrakk>
   \<Longrightarrow>
     ptr_range (a + of_nat x * of_nat word_size) 2 \<subseteq>
     ptr_range (a :: word32) msg_align_bits"
  apply(rule ptr_range_subset)
     apply assumption
    apply(simp add: msg_align_bits')
   apply(simp add: msg_align_bits word_size_bits_def word_bits_def)
  apply(simp add: word_size_def)
  apply(subst upto_enum_step_shift_red[where us=2, simplified])
     apply (simp add: msg_align_bits word_bits_def word_size_bits_def)+
  done

lemma for_each_byte_of_word_def2:
  "for_each_byte_of_word P ptr \<equiv> (\<forall> x\<in>ptr_range ptr 2. P x)"
  apply(simp add: for_each_byte_of_word_def ptr_range_def add.commute)
  done

lemma aag_has_auth_to_read_cptrs:
  "\<lbrakk>x \<in> set [buffer_cptr_index..<
             buffer_cptr_index + unat (mi_extra_caps mi)];
    ipc_buffer_has_read_auth aag (pasSubject aag) (Some a);
    buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits)\<rbrakk>
   \<Longrightarrow>
   for_each_byte_of_word (\<lambda> y. aag_can_read aag y)
     (a + of_nat x * of_nat word_size)"
  apply(simp add: for_each_byte_of_word_def2 ipc_buffer_has_read_auth_def)
  apply(rule ballI)
  apply(rule reads_read)
  apply(clarify)
  apply(erule bspec)
  apply(rule subsetD[OF cptrs_in_ipc_buffer])
     apply fastforce
    apply assumption
   apply assumption
  apply assumption
  done

lemma get_extra_cptrs_rev:
  "reads_equiv_valid_inv A aag (K (ipc_buffer_has_read_auth aag (pasSubject aag) buffer \<and> (buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits))))
      (get_extra_cptrs buffer mi)"
  unfolding get_extra_cptrs_def
  apply (rule gen_asm_ev)
  apply clarsimp
  apply(case_tac buffer, simp_all add: return_ev_pre)
  apply (wp mapM_ev equiv_valid_guard_imp[OF load_word_offs_rev]
       | erule (2) aag_has_auth_to_read_cptrs)+
  done

lemma lookup_extra_caps_rev:
  shows "reads_equiv_valid_inv A aag (pas_refined aag and (K (is_subject aag thread))  and (\<lambda> s. ipc_buffer_has_read_auth aag (pasSubject aag) buffer \<and> buffer_cptr_index + unat (mi_extra_caps mi) < 2 ^ (msg_align_bits - word_size_bits)))
     (lookup_extra_caps thread buffer mi)"
  apply(rule gen_asm_ev)
  unfolding lookup_extra_caps_def fun_app_def
  apply (wp mapME_ev cap_fault_on_failure_rev lookup_cap_and_slot_rev
            get_extra_cptrs_rev)
  apply simp
  done

lemmas lookup_extra_caps_reads_respects_g =  reads_respects_g_from_inv[OF lookup_extra_caps_rev lookup_extra_caps_inv]

lemma msg_in_ipc_buffer:
  "\<lbrakk>x = msg_max_length \<or> x < msg_max_length;
    unat (mi_length mi) < 2 ^ (msg_align_bits - word_size_bits);
    is_aligned a msg_align_bits\<rbrakk>
   \<Longrightarrow>
     ptr_range (a + of_nat x * of_nat word_size) 2 \<subseteq>
     ptr_range (a::word32) msg_align_bits"
  apply(rule ptr_range_subset)
     apply assumption
    apply(simp add: msg_align_bits)
   apply(simp add: msg_align_bits word_bits_def)
  apply(simp add: word_size_def)
  apply(subst upto_enum_step_shift_red[where us=2, simplified])
     apply (simp add: msg_align_bits word_bits_def)+
  apply(simp add: image_def)
  apply(rule_tac x=x in bexI)
   apply(rule refl)
  apply(auto simp: msg_max_length_def)
  done


lemma aag_has_auth_to_read_msg:
  "\<lbrakk>x = msg_max_length \<or> x < msg_max_length;
    ipc_buffer_has_read_auth aag (pasSubject aag) (Some a);
    unat (mi_length mi) < 2 ^ (msg_align_bits - word_size_bits)\<rbrakk>
   \<Longrightarrow>
   for_each_byte_of_word (aag_can_read aag)
     (a + of_nat x * of_nat word_size)"
  apply(simp add: for_each_byte_of_word_def2 ipc_buffer_has_read_auth_def)
  apply(rule ballI)
  apply(rule reads_read)
  apply(clarify)
  apply(erule bspec)
  apply(rule subsetD[OF msg_in_ipc_buffer[where x=x]])
     apply assumption
    apply assumption
   apply assumption
  apply assumption
  done

(* only called within do_reply_transfer for which access assumes sender
   and receiver in same domain *)
lemma get_mrs_rev:
  shows "reads_equiv_valid_inv A aag ((K (is_subject aag thread \<and> ipc_buffer_has_read_auth aag (pasSubject aag) buf \<and> unat (mi_length mi) < 2 ^ (msg_align_bits - word_size_bits)))) (get_mrs thread buf mi)"
  apply (rule gen_asm_ev)
  unfolding get_mrs_def
  apply (wp mapM_ev'' load_word_offs_rev thread_get_rev
       | wpc
       | rule aag_has_auth_to_read_msg[where mi=mi]
       | clarsimp split: if_split_asm)+
  done

lemmas get_mrs_reads_respects_g = reads_respects_g_from_inv[OF get_mrs_rev get_mrs_inv]



lemma setup_caller_cap_reads_respects:
  "reads_respects aag l (K (aag_can_read aag sender \<and> aag_can_read aag receiver))
    (setup_caller_cap sender receiver grant)"
  unfolding setup_caller_cap_def
  apply(wp cap_insert_reads_respects set_thread_state_owned_reads_respects | simp)+
  done


lemma const_on_failure_ev:
  "equiv_valid_inv I A P m \<Longrightarrow>
   equiv_valid_inv I A P (const_on_failure c m)"
  unfolding const_on_failure_def catch_def
  apply(wp | wpc | simp)+
  done


lemma set_extra_badge_reads_respects:
  "reads_respects aag l \<top> (set_extra_badge buffer badge n)"
  unfolding set_extra_badge_def
  by (rule store_word_offs_reads_respects)

lemma reads_equiv_cdt_has_children0:
  "\<lbrakk>pas_refined aag s; pas_refined aag s'; aag_can_read aag (fst slot);
    equiv_for (aag_can_read aag \<circ> fst) cdt s s'\<rbrakk> \<Longrightarrow>
    (cdt s) c = Some slot \<longleftrightarrow> (cdt s') c = Some slot"
  apply(rule iffI)
   apply (drule equiv_forD)
   apply (erule(1) all_children_subjectReads[THEN all_childrenD];fastforce)
   apply fastforce
  apply (drule equiv_forD)
   apply (erule(1) all_children_subjectReads[THEN all_childrenD];fastforce)
   apply fastforce
  done

lemma reads_equiv_cdt_has_children:
  "\<lbrakk>pas_refined aag s; pas_refined aag s'; is_subject aag (fst slot);
    equiv_for (aag_can_read aag \<circ> fst) cdt s s'\<rbrakk> \<Longrightarrow>
    (\<exists> c. (cdt s) c = Some slot) = (\<exists> c. (cdt s') c = Some slot)"
  apply (rule iff_exI)
  by (erule reads_equiv_cdt_has_children0; force)


lemma ensure_no_children_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and K (is_subject aag (fst slot)))
  (ensure_no_children slot)"
  unfolding ensure_no_children_def fun_app_def equiv_valid_def2
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule_tac Q="\<lambda> rv s. pas_refined aag s \<and> is_subject aag (fst slot) \<and> rv = cdt s"
                  in equiv_valid_rv_liftE_bindE[OF equiv_valid_rv_guard_imp[OF gets_cdt_revrv']])
     apply(rule TrueI)
    apply(clarsimp simp: equiv_valid_2_def)
    apply(drule reads_equiv_cdt_has_children)
       apply assumption
      apply assumption
     apply(fastforce elim: reads_equivE)
    apply(fastforce simp: in_whenE in_throwError)
   apply(wp, simp)
  done

lemma arch_derive_cap_reads_respects:
  "reads_respects aag l \<top> (arch_derive_cap cap)"
  unfolding arch_derive_cap_def
  apply(rule equiv_valid_guard_imp)
   apply(wp | wpc)+
  apply(simp)
  done

lemma derive_cap_rev':
  "reads_equiv_valid_inv A aag (\<lambda> s. (\<exists>x xa xb d. cap = cap.UntypedCap d x xa xb) \<longrightarrow>
         pas_refined aag s \<and> is_subject aag (fst slot)) (derive_cap slot cap)"
  unfolding derive_cap_def arch_derive_cap_def
  apply(rule equiv_valid_guard_imp)
  apply(wp ensure_no_children_rev | wpc | simp)+
  done

lemma derive_cap_rev:
  "reads_equiv_valid_inv A aag (\<lambda> s. pas_refined aag s \<and> is_subject aag (fst slot))
       (derive_cap slot cap)"
  by (blast intro: equiv_valid_guard_imp[OF derive_cap_rev'])

(* FIXME MOVE *)
lemma ball_subsetE:
  "\<lbrakk> \<forall> x \<in> S. P x; S' \<subseteq> S; \<And> x. P x \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> \<forall> x \<in> S'. Q x" by blast

lemma transfer_caps_loop_reads_respects':
  "reads_respects aag l
       (pas_refined aag and pspace_aligned and valid_vspace_objs and
        valid_arch_state and valid_mdb and valid_objs and
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
  apply(induct caps arbitrary: slots n mi)
   apply simp
   apply(rule return_ev_pre)
  apply(case_tac a,rename_tac cap obj ind)
  apply(simp split del: if_split)
  apply(rule equiv_valid_guard_imp)
  apply(wp const_on_failure_ev
       | simp | intro conjI impI)+
       apply fast
      apply(wp set_extra_badge_reads_respects hoare_vcg_ball_lift | simp)+
           apply fast
          apply(wp cap_insert_reads_respects cap_insert_pas_refined whenE_throwError_wp
                   derive_cap_rev derive_cap_cap_cur_auth derive_cap_is_derived
                   hoare_vcg_ball_lift cap_insert_cte_wp_at
               | simp split del: if_split)+
    apply (rule_tac Q' ="\<lambda>capd s. (capd\<noteq> cap.NullCap \<longrightarrow>
          cte_wp_at (is_derived (cdt s) (obj,ind) capd) (obj, ind) s)
          \<and> (capd\<noteq> cap.NullCap \<longrightarrow> QM s capd)" for QM
          in hoare_post_imp_R)
     prefer 2
     apply (clarsimp simp: cte_wp_at_caps_of_state split del: if_split)
     apply (strengthen is_derived_is_transferable[mk_strg I' O], assumption, solves\<open>simp\<close>)
    apply (rule hoare_vcg_conj_liftE_R)
     apply (rule derive_cap_is_derived)
    apply (wp derive_cap_is_derived_foo')
   apply wp
  apply(clarsimp simp: remove_rights_cur_auth cte_wp_at_caps_of_state split del: if_split)
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
       (pas_refined aag and pspace_aligned and valid_vspace_objs and
        valid_arch_state and valid_mdb and valid_objs and
        (\<lambda>s. (\<forall>cap\<in>set caps. valid_cap (fst cap) s
                           \<and> is_subject aag (fst (snd cap))
                           \<and> pas_cap_cur_auth aag (fst cap)
                           \<and> cte_wp_at (\<lambda>cp. fst cap \<noteq> NullCap \<longrightarrow> cp = fst cap) (snd cap) s)
           \<and> (\<forall>slot\<in>set slots. is_subject aag (fst slot)
                             \<and> cte_wp_at ((=) NullCap) slot s
                             \<and> real_cte_at slot s)
           \<and> distinct slots))
    (transfer_caps_loop ep rcv_buffer n caps slots mi)"
  apply(rule equiv_valid_guard_imp, rule transfer_caps_loop_reads_respects')
  by (fastforce elim:cte_wp_at_weakenE)


lemma empty_on_failure_ev:
  "equiv_valid_inv I A P m \<Longrightarrow>
  equiv_valid_inv I A P (empty_on_failure m)"
  unfolding empty_on_failure_def catch_def
  apply(wp | wpc | simp)+
  done

lemma unify_failure_ev:
  "equiv_valid_inv I A P m \<Longrightarrow>
  equiv_valid_inv I A P (unify_failure m)"
  unfolding unify_failure_def handleE'_def
  apply(wp | wpc | simp)+
  done

lemma lookup_slot_for_cnode_op_rev:
  "reads_equiv_valid_inv A aag (\<lambda>s. ((depth \<noteq> 0 \<and> depth \<le> word_bits)
                                \<longrightarrow> (pas_refined aag s
                                    \<and> (is_cnode_cap croot \<longrightarrow> is_subject aag (obj_ref_of croot)))))
     (lookup_slot_for_cnode_op is_source croot ptr depth)"
  unfolding lookup_slot_for_cnode_op_def
  apply (clarsimp split del: if_split)
  apply (wp resolve_address_bits_rev lookup_error_on_failure_rev
            whenE_throwError_wp
       | wpc
       | rule hoare_post_imp_R[OF hoare_True_E_R[where P="\<top>"]]
       | simp add: split_def split del: if_split)+
  done

lemma lookup_slot_for_cnode_op_reads_respects:
  "reads_respects aag l (pas_refined aag and K (is_subject aag (obj_ref_of croot)))
     (lookup_slot_for_cnode_op is_source croot ptr depth)"
  apply(rule equiv_valid_guard_imp[OF lookup_slot_for_cnode_op_rev])
  by simp

lemma lookup_cap_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and K (is_subject aag thread))
     (lookup_cap thread ref)"
  unfolding lookup_cap_def split_def fun_app_def
  apply (wp lookup_slot_for_thread_rev get_cap_rev | simp | strengthen aag_can_read_self)+
   apply (rule lookup_slot_for_thread_authorised)
  apply simp
  done

lemma captransfer_indices_in_range:
  "x \<in> {0..2} \<Longrightarrow>
  ((2::word32) + (of_nat msg_max_length + of_nat msg_max_extra_caps)) * word_size + (x * word_size) \<le> 2 ^ msg_align_bits - 1"
  apply(rule order_trans)
   prefer 2
   apply(rule word_less_sub_1)
   apply(rule_tac p=127 in mul_word_size_lt_msg_align_bits_ofnat)
   apply(simp add: msg_align_bits')
  apply(rule_tac y="0x7F * word_size" in order_trans)
   apply(clarsimp simp: msg_max_length_def msg_max_extra_caps_def word_size_def)
   apply(drule_tac k=4 in word_mult_le_mono1)
     apply simp
    apply simp
   apply(drule_tac x="0x1F4" in word_plus_mono_right)
    apply simp
   apply simp
  apply (simp add: word_size_def)
  done


lemma word_plus_power_2_offset_le:
  "\<lbrakk>is_aligned (p :: 'a :: len word) n; is_aligned q m; p < q; n \<le> m; n < len_of TYPE('a)\<rbrakk> \<Longrightarrow> p + (2^n) \<le> q"
  apply(drule is_aligned_weaken, assumption)
  apply(clarsimp simp: is_aligned_def)
  apply(elim dvdE)
  apply(rename_tac k ka)
  apply(rule_tac ua=0 and n="int k" and n'="int ka" in udvd_incr')
    apply assumption
  apply(clarsimp simp: uint_nat)+
  done


lemma is_aligned_mult_word_size:
  "is_aligned (p * word_size) 2"
  apply(rule_tac k=p in is_alignedI)
  apply(fastforce simp: word_size_def)
  done


lemma captransfer_in_ipc_buffer:
  "\<lbrakk>is_aligned (buffer :: word32) msg_align_bits;
    x \<in> {0..2}\<rbrakk> \<Longrightarrow>
  ptr_range (buffer + (2 + (of_nat msg_max_length + of_nat msg_max_extra_caps)) *
          word_size + x * word_size) 2 \<subseteq> ptr_range buffer msg_align_bits"
  apply(rule ptr_range_subset)
     apply assumption
    apply(simp add: msg_align_bits)
   apply(simp add: msg_align_bits word_bits_def)
  apply(simp add: word_size_def)
  apply(subst upto_enum_step_shift_red[where us=2, simplified])
     apply (simp add: msg_align_bits word_bits_def)+
  apply(simp add: image_def msg_max_length_def msg_max_extra_caps_def)
  apply(rule_tac x="(125::nat) + unat x"  in bexI)
   apply simp+
  apply(fastforce intro: unat_less_helper word_leq_minus_one_le)
  done

lemma aag_has_auth_to_read_captransfer:
  "\<lbrakk>ipc_buffer_has_read_auth aag (pasSubject aag) (Some buffer);
    x \<in> {0..2}\<rbrakk> \<Longrightarrow>
  for_each_byte_of_word (aag_can_read aag) (buffer + (2 + (of_nat msg_max_length + of_nat msg_max_extra_caps)) *
          word_size + x * word_size)"
  apply(simp add: for_each_byte_of_word_def2 ipc_buffer_has_read_auth_def)
  apply(rule ballI)
  apply(rule reads_read)
  apply(clarify)
  apply(erule bspec)
  apply(rule subsetD[OF captransfer_in_ipc_buffer])
     apply fastforce+
  done

lemma load_cap_transfer_rev:
  "reads_equiv_valid_inv A aag (K (ipc_buffer_has_read_auth aag (pasSubject aag) (Some buffer)))
    (load_cap_transfer buffer)"
  unfolding load_cap_transfer_def fun_app_def captransfer_from_words_def
  apply(wp dmo_loadWord_rev | simp)+
  apply safe
      apply(erule aag_has_auth_to_read_captransfer[where x=0, simplified])
    apply(erule aag_has_auth_to_read_captransfer[where x=1, simplified])
  apply(erule aag_has_auth_to_read_captransfer[where x=2, simplified])
  done


lemma get_endpoint_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_endpoint ptr)"
  unfolding get_simple_ko_def
  apply(wp get_object_rev | wpc | simp)+
  done

lemma send_endpoint_threads_blocked:
"\<lbrakk>valid_objs s; (sym_refs \<circ> state_refs_of) s;
  ko_at (Endpoint (SendEP list)) ep s; x\<in>set list\<rbrakk> \<Longrightarrow>
  st_tcb_at (send_blocked_on ep) x s"
  apply (rule ep_queued_st_tcb_at'')
  apply simp+
  done

lemma send_blocked_threads_have_SyncSend_auth:
  "\<lbrakk>pas_refined aag s; valid_objs s; sym_refs (state_refs_of s);
    st_tcb_at (send_blocked_on ep) x s\<rbrakk> \<Longrightarrow>
  (pasObjectAbs aag x,SyncSend,pasObjectAbs aag ep) \<in> pasPolicy aag"
  apply(drule_tac auth="SyncSend" and x=x in pas_refined_mem[rotated])
   apply(rule sta_ts)
   apply(clarsimp simp: thread_st_auth_def split: option.split simp: tcb_states_of_state_def st_tcb_def2)
   apply(case_tac "tcb_state tcb", simp_all)
  done


(*MOVE*)
lemma ev_invisible:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "\<lbrakk>labels_are_invisible aag l L; modifies_at_most aag L Q f; \<forall>s t. P s \<and> P t \<longrightarrow> (\<forall>(rva, s') \<in> fst (f s). \<forall>(rvb, t') \<in> fst(f t). W rva rvb)\<rbrakk> \<Longrightarrow>
  equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) W (P and Q) (P and Q) f f"
  apply (rule ev2_invisible[OF domains_distinct])
  apply simp+
  done


lemma get_thread_state_reads_respects:
  "reads_respects aag l (\<lambda> s. aag_can_read aag thread \<or> aag_can_affect aag l thread) (get_thread_state thread)"
  unfolding get_thread_state_def
  apply(rule equiv_valid_guard_imp)
   apply(wp thread_get_reads_respects | simp)+
  done

lemma send_endpoint_reads_affects_queued:
  "\<lbrakk>(pasSubject aag, auth, pasObjectAbs aag epptr) \<in> pasPolicy aag;
    auth \<in> {Receive,Reset};
    aag_can_read aag epptr \<or>
    aag_can_affect aag l epptr;
    pas_refined aag s; valid_objs s; sym_refs (state_refs_of s);
    ko_at (Endpoint (SendEP list)) epptr s; ep = SendEP list;
    x \<in> set list\<rbrakk>
   \<Longrightarrow> aag_can_read aag x \<or> aag_can_affect aag l x"
  apply(frule send_endpoint_threads_blocked, (simp | assumption)+)
  apply(drule send_blocked_threads_have_SyncSend_auth, (simp | assumption)+)
  apply(auto dest: read_sync_ep_read_senders)
  done

lemma mapM_ev''':
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A (Q and P x) (m x)"
  assumes inv: "\<And> x. x \<in> set lst \<Longrightarrow> invariant (m x) (\<lambda> s. Q s \<and> (\<forall>x\<in>set lst. P x s))"
  shows "equiv_valid_inv D A (\<lambda> s. Q s \<and> (\<forall>x\<in>set lst. P x s)) (mapM m lst)"
  apply(rule mapM_ev)
  apply(rule equiv_valid_guard_imp[OF reads_res], simp+)
  apply(wpsimp wp: inv)
  done

lemma cancel_badged_sends_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes gts_st_tcb_at[wp del]
  shows
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs and
                         valid_arch_state and valid_objs and (sym_refs \<circ> state_refs_of) and
                         (\<lambda>s. is_subject aag (cur_thread s)) and K (is_subject aag epptr))
      (cancel_badged_sends epptr badge)"
  apply (rule gen_asm_ev)+
  apply(simp add: cancel_badged_sends_def)
  apply wp
     apply ((wp mapM_ev'' mapM_wp get_thread_state_reads_respects set_thread_state_runnable_reads_respects
                set_simple_ko_reads_respects get_simple_ko_reads_respects hoare_vcg_ball_lift
                tcb_sched_action_reads_respects set_thread_state_pas_refined
            | wpc | simp add: filterM_mapM tcb_at_st_tcb_at[symmetric] | wp (once) hoare_drop_imps | rule subset_refl | force)+)[1]
    apply (wp get_simple_ko_reads_respects)
   apply (wp get_simple_ko_wp)
  apply simp
  apply (intro conjI allI impI ballI, elim conjE)
  by (rule send_endpoint_reads_affects_queued[where epptr = epptr];
      (assumption | force simp: pas_refined_def policy_wellformed_def))


lemma get_cap_ret_is_subject':
  "\<lbrace>pas_refined aag and K (is_subject aag (fst ptr))\<rbrace> get_cap ptr
       \<lbrace>\<lambda>rv s. is_cnode_cap rv \<longrightarrow> (\<forall>x\<in>Access.obj_refs rv. is_subject aag x)\<rbrace>"
  apply(rule hoare_strengthen_post[OF get_cap_ret_is_subject])
  apply(clarsimp simp: is_cap_simps)
  done


lemma get_receive_slots_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and (K (is_subject aag thread \<and>
         ipc_buffer_has_read_auth aag (pasSubject aag) buf)))
   (get_receive_slots thread buf)"
  apply(case_tac buf)
   apply(fastforce intro: return_ev_pre)
  apply(simp add: lookup_cap_def split_def
       | wp empty_on_failure_ev unify_failure_ev lookup_slot_for_cnode_op_rev get_cap_rev
            lookup_slot_for_thread_rev lookup_slot_for_thread_authorised
            get_cap_ret_is_subject get_cap_ret_is_subject' load_cap_transfer_rev
       | wp (once) hoare_drop_imps
       | strengthen aag_can_read_self)+
  done

lemma transfer_caps_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs and
                         valid_arch_state and valid_mdb and valid_objs and
                         (\<lambda>s. (\<forall>cap\<in>set caps. s \<turnstile> fst cap
                                            \<and> is_subject aag (fst (snd cap))
                                            \<and> pas_cap_cur_auth aag (fst cap)
                                            \<and> cte_wp_at (\<lambda>cp. fst cap \<noteq> NullCap \<longrightarrow> cp = fst cap)
                                                        (snd cap) s)) and
                         K (is_subject aag receiver \<and>
                            ipc_buffer_has_read_auth aag (pasSubject aag) receive_buffer))
     (transfer_caps mi caps endpoint receiver receive_buffer)"
  unfolding transfer_caps_def fun_app_def
  apply (wp transfer_caps_loop_reads_respects get_receive_slots_rev get_receive_slots_authorised
           hoare_vcg_all_lift static_imp_wp
        | wpc | simp add: ball_conj_distrib)+
  done

lemma mrs_in_ipc_buffer:
  "\<lbrakk>is_aligned (buf :: word32) msg_align_bits;
    x \<in> set [length msg_registers + 1..<Suc n];
    n < 2 ^ (msg_align_bits - word_size_bits)\<rbrakk>
       \<Longrightarrow> ptr_range
           (buf + of_nat x * of_nat word_size) 2 \<subseteq> ptr_range buf msg_align_bits"
  apply(rule ptr_range_subset)
     apply assumption
    apply(simp add: msg_align_bits)
   apply(simp add: msg_align_bits word_bits_def)
  apply(simp add: word_size_def)
  apply(subst upto_enum_step_shift_red[where us=2, simplified])
     apply (simp add: msg_align_bits word_bits_def word_size_bits_def)+
  apply(simp add: image_def)
  apply(rule_tac x=x in bexI)
   apply(rule refl)
  apply (fastforce split: if_split_asm)
  done

lemma aag_has_auth_to_read_mrs:
  "\<lbrakk>aag_can_read_or_affect_ipc_buffer aag l (Some buf);
    x \<in> set [length msg_registers + 1..<Suc n];
    n < 2 ^ (msg_align_bits - word_size_bits)\<rbrakk>
       \<Longrightarrow> for_each_byte_of_word (\<lambda>x. aag_can_read_label aag (pasObjectAbs aag x) \<or> aag_can_affect aag l x)
           (buf + of_nat x * of_nat word_size)"
  apply(simp add: for_each_byte_of_word_def2 aag_can_read_or_affect_ipc_buffer_def)
  apply(rule ballI)
  apply(erule conjE)
  apply(erule bspec)
  apply(rule subsetD[OF mrs_in_ipc_buffer[where x=x and n=n]])
     apply assumption
    apply (clarsimp split: if_splits)
   apply assumption
  apply assumption
  done


abbreviation aag_can_read_or_affect where
  "aag_can_read_or_affect aag l x \<equiv>
    aag_can_read aag x \<or> aag_can_affect aag l x"

lemma dmo_loadWord_reads_respects:
  "reads_respects aag l (K (for_each_byte_of_word (\<lambda> x. aag_can_read_or_affect aag l x) p))
     (do_machine_op (loadWord p))"
  apply(rule gen_asm_ev)
  apply(rule use_spec_ev)
  apply(rule spec_equiv_valid_hoist_guard)

  apply(rule do_machine_op_spec_reads_respects)
  apply(simp add: loadWord_def equiv_valid_def2 spec_equiv_valid_def)
  apply(rule_tac R'="\<lambda> rv rv'. for_each_byte_of_word (\<lambda> y. rv y = rv' y) p" and Q="\<top>\<top>" and Q'="\<top>\<top>" and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
       apply(rule_tac R'="(=)" and Q="\<lambda> r s. p && mask 2 = 0" and Q'="\<lambda> r s. p && mask 2 = 0" and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
            apply(rule return_ev2)
            apply(rule_tac f="word_rcat" in arg_cong)
            apply(fastforce intro: is_aligned_no_wrap' word_plus_mono_right simp: is_aligned_mask for_each_byte_of_word_def) (* slow *)
           apply(rule assert_ev2[OF refl])
          apply(rule assert_wp)+
        apply simp+
       apply(clarsimp simp: equiv_valid_2_def in_monad for_each_byte_of_word_def)
       apply(fastforce elim: equiv_forD orthD1 simp: ptr_range_def add.commute)
      apply (wp wp_post_taut loadWord_inv | simp)+
  done

lemma load_word_offs_reads_respects:
  "reads_respects aag l (\<lambda> s. for_each_byte_of_word (\<lambda> x. aag_can_read_or_affect aag l x) (a + of_nat x * of_nat word_size)) (load_word_offs a x)"
  unfolding load_word_offs_def fun_app_def
  apply(rule equiv_valid_guard_imp[OF dmo_loadWord_reads_respects])
  apply(clarsimp)
  done

lemma as_user_reads_respects:
  "reads_respects aag l (K (det f \<and> aag_can_read_or_affect aag l thread)) (as_user thread f)"
  apply (simp add: as_user_def split_def)
  apply (rule gen_asm_ev)
  apply (wp set_object_reads_respects select_f_ev gets_the_ev)
  apply (auto intro: reads_affects_equiv_get_tcb_eq[where aag=aag])
  done

lemma copy_mrs_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (K (aag_can_read_or_affect aag l sender \<and> aag_can_read_or_affect_ipc_buffer aag l sbuf \<and> unat n < 2 ^ (msg_align_bits - word_size_bits))) (copy_mrs sender sbuf receiver rbuf n)"
  unfolding copy_mrs_def fun_app_def
  apply(rule gen_asm_ev)
  apply(wp mapM_ev'' store_word_offs_reads_respects
           load_word_offs_reads_respects as_user_set_register_reads_respects'
           as_user_reads_respects
       | wpc
       | simp add: det_setRegister det_getRegister split del: if_split)+
  apply clarsimp
  apply(rename_tac n')
  apply(subgoal_tac " ptr_range (x + of_nat n' * of_nat word_size) 2
          \<subseteq> ptr_range x msg_align_bits")
   apply(simp add: for_each_byte_of_word_def2)
   apply(simp add: aag_can_read_or_affect_ipc_buffer_def)
   apply(erule conjE)
   apply(rule ballI)
   apply(erule bspec)
   apply(erule (1) subsetD[rotated])
  apply(rule ptr_range_subset)
     apply(simp add: aag_can_read_or_affect_ipc_buffer_def)
    apply(simp add: msg_align_bits)
    apply(simp add: msg_align_bits word_bits_def)
   apply(simp add: word_size_def word_size_bits_def)
  apply(subst upto_enum_step_shift_red[where us=2, simplified])
     apply (simp add: msg_align_bits word_bits_def aag_can_read_or_affect_ipc_buffer_def )+
  apply(fastforce simp: image_def)
  done

lemma get_mi_length':
   "\<lbrace>\<top>\<rbrace> get_message_info sender
    \<lbrace>\<lambda>rv s. buffer_cptr_index + unat (mi_extra_caps rv)
            < 2 ^ (msg_align_bits - word_size_bits)\<rbrace>"
  apply(rule hoare_post_imp[OF _ get_mi_valid'])
  apply(clarsimp simp: valid_message_info_def msg_align_bits' msg_max_length_def word_le_nat_alt
                       buffer_cptr_index_def msg_max_extra_caps_def)
  done

lemma validE_E_wp_post_taut:
   "\<lbrace> P \<rbrace> f -, \<lbrace>\<lambda> r s. True \<rbrace>"
  by(auto simp: validE_E_def validE_def valid_def)

lemma aag_has_read_auth_can_read_or_affect_ipc_buffer:
  "ipc_buffer_has_read_auth aag (pasSubject aag) buf \<Longrightarrow>
   aag_can_read_or_affect_ipc_buffer aag l buf"
  apply(clarsimp simp: ipc_buffer_has_read_auth_def
                       aag_can_read_or_affect_ipc_buffer_def
                 split: option.splits)
  apply(rule reads_read)
  apply blast
  done

lemma ev_irrelevant_bind:
  assumes inv: "\<And> P. \<lbrace> P \<rbrace> f \<lbrace>\<lambda>_. P \<rbrace>"
  assumes ev: "equiv_valid I A A P g"
  shows "equiv_valid I A A P (do y \<leftarrow> f; g od)"
  apply(simp add: equiv_valid_def2)
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule equiv_valid_2_bind)
      apply(rule ev[simplified equiv_valid_def2])
     apply(wp equiv_valid_rv_trivial[OF inv] inv | simp)+
  done

lemma get_message_info_reads_respects:
  "reads_respects aag l (K (aag_can_read_or_affect aag l ptr)) (get_message_info ptr)"
  apply (simp add: get_message_info_def)
  apply (wp as_user_reads_respects | clarsimp simp: getRegister_def)+
  done

lemma do_normal_transfer_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs and
                         valid_arch_state and valid_mdb and valid_objs and
                         K (aag_can_read_or_affect aag l sender \<and>
                            ipc_buffer_has_read_auth aag (pasObjectAbs aag sender) sbuf \<and>
                            ipc_buffer_has_read_auth aag (pasObjectAbs aag receiver) rbuf \<and>
                            (grant \<longrightarrow> (is_subject aag sender \<and> is_subject aag receiver))))
                        (do_normal_transfer sender sbuf endpoint badge grant receiver rbuf)"
  apply(cases grant)
   apply(rule gen_asm_ev)
   apply(simp add: do_normal_transfer_def)
   apply(wp copy_mrs_pas_refined get_message_info_rev lookup_extra_caps_rev
            as_user_set_register_reads_respects' set_message_info_reads_respects
            transfer_caps_reads_respects copy_mrs_reads_respects
            lookup_extra_caps_rev lookup_extra_caps_authorised
            lookup_extra_caps_auth get_message_info_rev
            get_mi_length' get_mi_length validE_E_wp_post_taut
            copy_mrs_cte_wp_at
            hoare_vcg_ball_lift lec_valid_cap'
            lookup_extra_caps_srcs[simplified ball_conj_distrib,THEN hoare_conjDR1]
            lookup_extra_caps_srcs[simplified ball_conj_distrib,THEN hoare_conjDR2]
        | wpc
        | simp add: det_setRegister ball_conj_distrib)+
   apply (fastforce intro: aag_has_read_auth_can_read_or_affect_ipc_buffer)
  apply(rule gen_asm_ev)
  apply(simp add: do_normal_transfer_def transfer_caps_def)
  apply(wp ev_irrelevant_bind[where f="get_receive_slots receiver rbuf"]
           as_user_set_register_reads_respects'
           set_message_info_reads_respects copy_mrs_reads_respects
           get_message_info_reads_respects get_mi_length
       |wpc
       |simp)+
  apply(auto simp: ipc_buffer_has_read_auth_def aag_can_read_or_affect_ipc_buffer_def dest: reads_read_thread_read_pages split: option.splits)
  done

lemma getRestartPC_det:
  "det getRestartPC"
  apply (clarsimp simp: getRestartPC_def getRegister_def)
  done

lemma getRegister_det:
  "det (getRegister x)"
  by (clarsimp simp: getRegister_def)

lemma make_fault_msg_reads_respects:
  "reads_respects aag l (K (aag_can_read_or_affect aag l sender)) (make_fault_msg rva sender)"
  apply(case_tac rva)
     apply (wp as_user_reads_respects
           | simp split del: if_split
                  add: getRestartPC_det getRegister_det
           | rule det_mapM
           | rule subset_refl)+
  apply (case_tac x4)
  apply (wp as_user_reads_respects
        | simp split del: if_split
               add: getRestartPC_det getRegister_det)+
  done

lemma set_mrs_returns_a_constant:
  "\<exists> x. \<lbrace> \<top> \<rbrace> set_mrs thread buf msgs \<lbrace> \<lambda> rv s. rv = x \<rbrace>"
  apply(case_tac buf)
   apply(rule exI)
   apply((simp add: set_mrs_def | wp | rule impI)+)[1]
  apply(rule exI)
  apply((simp add: set_mrs_def split del: if_split | wp | rule impI)+)[1]
  done

lemma set_mrs_ret_eq:
  "\<forall>(s::'a::state_ext state) (t::'a::state_ext state). \<forall>(rva, s')\<in>fst (set_mrs thread buf msgs s).
                \<forall>(rvb, t')\<in>fst (set_mrs thread  buf msgs t). rva = rvb"
  apply(clarsimp)
  apply(cut_tac thread=thread and buf=buf and msgs=msgs in set_mrs_returns_a_constant)
  apply(erule exE)
  apply(subgoal_tac "a = x \<and> aa = x")
   apply simp
  apply(rule conjI)
   apply(erule (1) use_valid | simp)+
  done


lemma set_mrs_reads_respects':
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (K (ipc_buffer_has_auth aag thread buf \<and>  (case buf of (Some buf') \<Rightarrow>
        is_aligned buf' msg_align_bits | _ \<Rightarrow> True))) (set_mrs thread buf msgs)"
  apply(case_tac "aag_can_read_or_affect aag l thread")
   apply((wp equiv_valid_guard_imp[OF set_mrs_reads_respects] | simp)+)[1]
  apply(rule gen_asm_ev)
  apply(simp add: equiv_valid_def2)
  apply(rule equiv_valid_rv_guard_imp)
  apply(case_tac buf)
   apply(rule_tac Q="\<top>" and P="\<top>" and L="{pasObjectAbs aag thread}" in ev_invisible[OF domains_distinct])
      apply(clarsimp simp: labels_are_invisible_def)
     apply(rule modifies_at_mostI)
     apply(simp add: set_mrs_def)
     apply((wp set_object_equiv_but_for_labels | simp | auto dest: get_tcb_not_asid_pool_at)+)[1]
    apply(simp)
    apply(rule set_mrs_ret_eq)
   apply(rename_tac buf')
   apply(rule_tac Q="\<top>" and L="{pasObjectAbs aag thread} \<union> (pasObjectAbs aag) ` (ptr_range buf' msg_align_bits)" in ev_invisible[OF domains_distinct])
     apply(auto simp: labels_are_invisible_def ipc_buffer_has_auth_def dest: reads_read_page_read_thread simp: aag_can_affect_label_def)[1]
    apply(rule modifies_at_mostI)
    apply(wp set_mrs_equiv_but_for_labels | simp)+
   apply(rule set_mrs_ret_eq)
  by simp

lemma do_fault_transfer_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (K (aag_can_read_or_affect aag l sender \<and> ipc_buffer_has_auth aag receiver buf \<and>
    (case buf of None \<Rightarrow> True | Some buf' \<Rightarrow> is_aligned buf' msg_align_bits))) (do_fault_transfer badge sender receiver buf)"
  unfolding do_fault_transfer_def
  apply (wp as_user_set_register_reads_respects' as_user_reads_respects set_message_info_reads_respects
            set_mrs_reads_respects' make_fault_msg_reads_respects thread_get_reads_respects
         | wpc
         | simp add: split_def det_setRegister
         | wp (once) hoare_drop_imps)+
  done



lemma tl_tl_in_set:
  "tl xs = (x # xs') \<Longrightarrow> set xs' \<subseteq> set xs"
  apply(case_tac xs, auto)
  done

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

lemma do_ipc_transfer_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pspace_aligned and valid_vspace_objs and valid_arch_state and
                         valid_objs and valid_mdb and pas_refined aag and
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

lemma complete_signal_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l ( K(aag_can_read aag ntfnptr \<or> aag_can_affect aag l ntfnptr))
     (complete_signal ntfnptr receiver)"
  unfolding complete_signal_def
  apply (wp set_simple_ko_reads_respects
            get_simple_ko_reads_respects
            as_user_set_register_reads_respects'
        | wpc
        | simp)+
  done

lemma ko_at_eq:
  "ko_at obj pos s \<longleftrightarrow> kheap s pos = Some obj"
  by (force simp:obj_at_def)

lemma receive_ipc_base_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes do_nbrecv_failed_transfer_def[simp]
  shows "reads_respects aag l
     (invs and pas_refined aag and pas_cur_domain aag
      and ko_at (Endpoint ep) epptr
      and is_subject aag \<circ> cur_thread
      and K (is_subject aag receiver
           \<and> aag_has_auth_to aag Receive epptr
           \<and> (\<forall> auth \<in> cap_rights_to_auth rights True . aag_has_auth_to aag auth epptr)))
     (receive_ipc_base aag receiver ep epptr rights is_blocking)"
  apply (rule gen_asm_ev)
  apply (simp add: thread_get_def split: endpoint.split)
  apply (intro conjI impI)
    prefer 2 defer
    apply ((wp set_thread_state_reads_respects set_simple_ko_reads_respects
               as_user_set_register_reads_respects'
        | simp | intro allI impI | rule pre_ev, wpc)+)[2]
  apply (intro allI impI)
  apply (wp static_imp_wp set_simple_ko_reads_respects set_thread_state_reads_respects
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
    apply (solves \<open>auto intro:reads_ep read_sync_ep_read_senders_strong\<close>)
    done
  done

lemma receive_ipc_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (invs and
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
            static_imp_wp set_simple_ko_reads_respects set_thread_state_reads_respects
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
  apply(drule_tac auth="Receive" and x=x in pas_refined_mem[rotated])
   apply(rule sta_ts)
   apply(clarsimp simp: thread_st_auth_def split: option.split simp: tcb_states_of_state_def st_tcb_def2)
   apply(case_tac "tcb_state tcb", simp_all)
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
  apply(frule receive_endpoint_threads_blocked, (simp | assumption)+)
  apply(drule receive_blocked_threads_have_Receive_auth, (simp | assumption)+)
  apply(auto dest: read_sync_ep_read_receivers)
  done

lemma send_ipc_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pas_refined aag and invs and pas_cur_domain aag
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
    subgoal by (rule read_sync_ep_read_receivers_strong)
   apply (fastforce dest: aag_wellformed_grant_Control_to_recv[OF _ _ pas_refined_wellformed]
                    simp: aag_has_Control_iff_owns)
  by (fastforce elim: send_ipc_valid_ep_helper reads_equivE equiv_forD
      intro: kheap_get_tcb_eq)


subsection "Faults"

lemma send_fault_ipc_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (invs and pas_refined aag and pas_cur_domain aag
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
            lookup_slot_for_thread_authorised hoare_vcg_all_lift_R
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
               in hoare_post_imp_R[rotated])
       apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)
      apply (wp get_cap_auth_wp[where aag=aag] lookup_slot_for_thread_authorised
                thread_get_reads_respects
            | simp add: add: lookup_cap_def split_def)+
  done


lemma handle_fault_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (invs and pas_refined aag and pas_cur_domain aag
        and is_subject aag \<circ> cur_thread
        and K (is_subject aag thread \<and> valid_fault fault))
     (handle_fault thread fault)"
  unfolding handle_fault_def catch_def fun_app_def handle_double_fault_def
  apply(wp (once) hoare_drop_imps |
        wp set_thread_state_reads_respects send_fault_ipc_reads_respects | wpc | simp)+
  apply(fastforce intro: reads_affects_equiv_get_tcb_eq)
  done



subsection "Replies"

lemma handle_arch_fault_reply_reads_respects:
  "reads_respects aag l (K (aag_can_read aag thread)) (handle_arch_fault_reply afault thread x y)"
  by (simp add: handle_arch_fault_reply_def, wp)

lemma handle_fault_reply_reads_respects:
  "reads_respects aag l (K (aag_can_read aag thread)) (handle_fault_reply fault thread x y)"
  apply(case_tac fault)
     apply (wp as_user_reads_respects thread_get_reads_respects
               thread_get_wp' handle_arch_fault_reply_reads_respects[simplified K_def]
          | simp add: det_zipWithM_x det_setRegister)+
  done

lemma lookup_ipc_buffer_has_read_auth':
  "\<lbrace>pas_refined aag and valid_objs and K (is_subject aag thread)\<rbrace>
   lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda>rv s. ipc_buffer_has_read_auth aag (pasSubject aag) rv\<rbrace>"
  apply(rule hoare_gen_asm)
  apply(rule hoare_strengthen_post[OF lookup_ipc_buffer_has_read_auth])
  apply(drule sym, simp)
  done


crunch valid_ko_at_arm[wp]: handle_fault_reply "valid_ko_at_arm"

lemma do_reply_transfer_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_f aag l (silc_inv aag st and invs and pas_refined aag and pas_cur_domain aag
         and tcb_at receiver and tcb_at sender and emptyable slot  and is_subject aag \<circ> cur_thread
         and K (grant \<longrightarrow> is_subject aag receiver)
         and K (is_subject aag sender \<and> aag_can_read aag receiver \<and> is_subject aag (fst slot)))
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
            when_ev
        | wpc
        | simp split del: if_split
        | wp (once) reads_respects_f[where aag=aag and st=st]
        | elim conjE
        | wp (once) hoare_drop_imps)+
         apply(rule_tac Q="\<lambda> rv s. pas_refined aag s \<and> pas_cur_domain aag s \<and> invs s
                                 \<and> is_subject aag (cur_thread s)
                                 \<and> silc_inv aag st s"
                     in hoare_strengthen_post[rotated])
          apply((wp (once) hoare_drop_imps
               | wp cap_delete_one_invs  hoare_vcg_all_lift
                    cap_delete_one_silc_inv reads_respects_f[OF thread_get_reads_respects]
                    reads_respects_f[OF get_thread_state_rev]
               | simp add: invs_valid_objs invs_psp_aligned invs_valid_global_refs
                           invs_distinct invs_arch_state invs_valid_ko_at_arm
                           invs_psp_aligned invs_vspace_objs invs_arch_state
               | rule conjI
               | elim conjE
               | assumption)+)[8]
   by (fastforce dest: silc_inv_not_subject)

lemma handle_reply_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_f aag l (silc_inv aag st and invs and pas_refined aag and pas_cur_domain aag
                           and is_subject aag \<circ> cur_thread)
     (handle_reply)"
  unfolding handle_reply_def
  apply (wp do_reply_transfer_reads_respects_f get_cap_wp reads_respects_f[OF get_cap_reads_respects, where Q="\<top>" and st=st] hoare_vcg_all_lift | wpc | blast)+
  apply(rule conjI)
   apply(fastforce simp: reads_equiv_f_def)
  apply clarsimp
  apply(rule conjI)
   apply assumption
  apply(rule conjI)
   apply(drule cte_wp_valid_cap)
    apply(erule invs_valid_objs)
   apply(simp add: valid_cap_simps)
  apply(rule conjI, fastforce simp: tcb_at_invs)
  apply(rule conjI)
   apply(erule emptyable_cte_wp_atD)
    apply(erule invs_valid_objs)
   apply(simp add: is_master_reply_cap_def)
  apply(frule_tac p="(cur_thread s, tcb_cnode_index 3)" in cap_cur_auth_caps_of_state[rotated])
    apply simp
   apply(simp add: cte_wp_at_caps_of_state)
  apply(fastforce intro: read_reply_thread_read_thread_rev
                   simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
                   dest: aag_Control_into_owns)
  done

lemma reply_from_kernel_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (K (is_subject aag thread)) (reply_from_kernel thread x)"
  unfolding reply_from_kernel_def fun_app_def
  apply (wp set_message_info_reads_respects set_mrs_reads_respects
            as_user_reads_respects lookup_ipc_buffer_reads_respects
        | simp add: split_def det_setRegister)+
  done


(* FIXME in whole section replace preconditions with 10 differents invariants by invs *)
section "globals_equiv"

subsection "Sync IPC"

lemma setup_caller_cap_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm and valid_global_objs\<rbrace>
     setup_caller_cap sender receiver grant
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding setup_caller_cap_def
  apply(wp cap_insert_globals_equiv'' set_thread_state_globals_equiv)
   apply(simp_all)
   done

lemma set_extra_badge_globals_equiv:
  "\<lbrace>globals_equiv s \<rbrace>
    set_extra_badge buffer badge n
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_extra_badge_def
  apply(wp store_word_offs_globals_equiv)
  done

lemma transfer_caps_loop_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm and valid_global_objs\<rbrace>
    transfer_caps_loop ep rcv_buffer n caps slots mi
    \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
proof (induct caps arbitrary: slots n mi)
  case Nil
  thus ?case by (simp, wp, simp)
next
  case (Cons c caps')
  show ?case
    apply(cases c)
    apply(simp split del: if_split cong: if_cong)
    apply(rule hoare_pre)
     apply(wp)
       apply(erule conjE, erule subst, rule Cons.hyps)
      apply(clarsimp)
      apply(wp set_extra_badge_globals_equiv)+
         apply(rule Cons.hyps)
        apply(simp)
        apply(wp cap_insert_globals_equiv'')
       apply(rule_tac Q="\<lambda>_. globals_equiv st and valid_ko_at_arm and valid_global_objs"
                  and E="\<lambda>_. globals_equiv st and valid_ko_at_arm and valid_global_objs"
                   in hoare_post_impErr)
         apply(simp add: whenE_def, rule conjI)
          apply(rule impI, wp)+
         apply(simp)+
       apply wp+
    apply(fastforce)
    done
qed

lemma transfer_caps_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm and valid_global_objs\<rbrace>
    transfer_caps info caps endpoint receiver recv_buffer
    \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding transfer_caps_def
  apply(wp transfer_caps_loop_globals_equiv | wpc | simp)+
  done

lemma copy_mrs_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm and (\<lambda>s. receiver \<noteq> idle_thread s)\<rbrace>
    copy_mrs sender sbuf receiver rbuf n
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding copy_mrs_def including no_pre
  apply(wp | wpc)+
    apply(rule_tac Q="\<lambda>_. globals_equiv s"
         in hoare_strengthen_post)
     apply(wp mapM_wp' | wpc)+
      apply(wp store_word_offs_globals_equiv)+
     apply fastforce
    apply simp
   apply(rule_tac Q="\<lambda>_. globals_equiv s and valid_ko_at_arm and (\<lambda>sa. receiver \<noteq> idle_thread sa)"
          in hoare_strengthen_post)
    apply(wp mapM_wp' as_user_globals_equiv)
    apply(simp)
   apply(fastforce)
  apply simp
  done

(* FIXME: move *)
lemma validE_to_valid:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>v. rv = Inr v \<longrightarrow> Q v s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>v. Q v\<rbrace>, -"
  apply(rule validE_validE_R)
  apply(simp add: validE_def valid_def)
  done


lemma do_normal_transfer_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm and valid_global_objs and
    (\<lambda>sa. receiver \<noteq> idle_thread sa)\<rbrace>
    do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
    \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding do_normal_transfer_def
  apply(wp as_user_globals_equiv set_message_info_globals_equiv transfer_caps_globals_equiv)
    apply(wp copy_mrs_globals_equiv)
     apply(subst K_def)
     apply(wp | rule impI)+
  apply(clarsimp)
  done



lemma do_fault_transfer_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm and
    (\<lambda>sa. receiver \<noteq> idle_thread sa)\<rbrace>
      do_fault_transfer badge sender receiver buf
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding do_fault_transfer_def
  apply(wp)
     apply(simp add: split_def)
     apply(wp as_user_globals_equiv set_message_info_globals_equiv
              set_mrs_globals_equiv | wpc)+
  apply(clarsimp)
  apply(rule hoare_drop_imps)
  apply(wp thread_get_inv, simp)
  done

lemma lookup_ipc_buffer_ptr_range':
  "\<lbrace>valid_objs\<rbrace>
  lookup_ipc_buffer True thread
  \<lbrace>\<lambda>rv s. rv = Some buf' \<longrightarrow> auth_ipc_buffers s thread = ptr_range buf' msg_align_bits\<rbrace>"
  unfolding lookup_ipc_buffer_def
  apply (rule hoare_pre)
  apply (wp get_cap_wp thread_get_wp' | wpc)+
  apply (clarsimp simp: cte_wp_at_caps_of_state ipc_buffer_has_auth_def get_tcb_ko_at [symmetric])
  apply (frule caps_of_state_tcb_cap_cases [where idx = "tcb_cnode_index 4"])
   apply (simp add: dom_tcb_cap_cases)
  apply (clarsimp simp: auth_ipc_buffers_def get_tcb_ko_at [symmetric])
  apply (drule(1) valid_tcb_objs)
  apply (drule get_tcb_SomeD)+
  apply (simp add: vm_read_write_def valid_tcb_def valid_ipc_buffer_cap_def split: bool.splits)
  done

lemma lookup_ipc_buffer_aligned':
  "\<lbrace>valid_objs\<rbrace> lookup_ipc_buffer True thread
\<lbrace>\<lambda>rv s. rv = Some buf' \<longrightarrow> is_aligned buf' msg_align_bits\<rbrace>"
  apply(insert lookup_ipc_buffer_aligned)
  apply(fastforce simp: valid_def)
  done

lemma set_collection: "a = {x. x\<in>a}"
  by simp

lemma do_ipc_transfer_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm and valid_objs and valid_arch_state and valid_global_refs
    and pspace_distinct and pspace_aligned and valid_global_objs and (\<lambda>s. receiver \<noteq> idle_thread s)\<rbrace>
    do_ipc_transfer sender ep badge grant receiver
    \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding do_ipc_transfer_def
  apply(wp do_normal_transfer_globals_equiv do_fault_transfer_globals_equiv | wpc)+
    apply(rule_tac Q="\<lambda>_. globals_equiv st and valid_ko_at_arm and valid_global_objs and
           (\<lambda>sa. receiver \<noteq> idle_thread sa) and
           (\<lambda>sa. (\<forall>rb. recv_buffer = Some rb \<longrightarrow>
           auth_ipc_buffers sa receiver = ptr_range rb msg_align_bits) \<and>
           (\<forall>rb. recv_buffer = Some rb \<longrightarrow> is_aligned rb msg_align_bits))"
           in hoare_strengthen_post)
     apply(wp)
    apply(clarsimp | rule conjI)+
   apply(wp hoare_vcg_all_lift lookup_ipc_buffer_ptr_range' lookup_ipc_buffer_aligned' | fastforce)+
  done

crunch valid_ko_at_arm[wp]: do_ipc_transfer "valid_ko_at_arm"

lemma send_ipc_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
    and pspace_distinct and pspace_aligned and valid_global_objs and valid_idle and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
    send_ipc block call badge can_grant can_grant_reply thread epptr
    \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding send_ipc_def
  apply(wp set_simple_ko_globals_equiv set_thread_state_globals_equiv
           setup_caller_cap_globals_equiv | wpc)+
         apply(rule_tac Q="\<lambda>_. globals_equiv st and valid_ko_at_arm and valid_global_objs"
               in hoare_strengthen_post[rotated])
         apply(fastforce)
        apply(wp set_thread_state_globals_equiv dxo_wp_weak | simp)+
        apply wpc
      apply(wp do_ipc_transfer_globals_equiv)+
    apply(clarsimp)
    apply(rule hoare_drop_imps)
    apply(wp set_simple_ko_globals_equiv)+
  apply(rule_tac Q="\<lambda>ep. ko_at (Endpoint ep) epptr and globals_equiv st and valid_objs
        and valid_arch_state and valid_global_refs and pspace_distinct and pspace_aligned
        and valid_global_objs and (\<lambda>s. sym_refs (state_refs_of s)) and valid_idle"
        in hoare_strengthen_post)
   apply(wp get_simple_ko_sp)
    apply(clarsimp simp: valid_arch_state_ko_at_arm)+
  apply (rule context_conjI)
   apply(rule valid_ep_recv_dequeue')
    apply(simp)+
  apply (frule_tac x=xa in receive_endpoint_threads_blocked,simp+)
  by (clarsimp simp add: valid_idle_def pred_tcb_at_def obj_at_def)+


lemma valid_ep_send_enqueue: "\<lbrakk>ko_at (Endpoint (SendEP (t # ts))) a s; valid_objs s\<rbrakk>
       \<Longrightarrow> valid_ep (case ts of [] \<Rightarrow> IdleEP | b # bs \<Rightarrow> SendEP (b # bs)) s"
  unfolding valid_objs_def valid_obj_def valid_ep_def obj_at_def
  apply (drule bspec)
  apply (auto split: list.splits)
  done

crunch globals_equiv[wp]: complete_signal "globals_equiv st"

lemma case_list_cons_cong:
  "(case xxs of [] \<Rightarrow> f | x # xs \<Rightarrow> g xxs)
 = (case xxs of [] \<Rightarrow> f | x # xs \<Rightarrow> g (x # xs))"
  by (simp split: list.split)

lemma receive_ipc_globals_equiv:
  notes do_nbrecv_failed_transfer_def[simp]
  shows "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs and pspace_distinct
     and pspace_aligned and valid_global_objs and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
     receive_ipc thread cap is_blocking
    \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding receive_ipc_def thread_get_def including no_pre
  apply(wp)
   apply(simp add: split_def)
   apply(wp set_simple_ko_globals_equiv set_thread_state_globals_equiv
             setup_caller_cap_globals_equiv dxo_wp_weak as_user_globals_equiv
       | wpc
       | simp split del: if_split)+
             apply (rule hoare_strengthen_post[where Q= "\<lambda>_. globals_equiv st and valid_ko_at_arm and valid_global_objs"])
              apply (wp do_ipc_transfer_globals_equiv as_user_globals_equiv)
             apply clarsimp
            apply (wp gts_wp get_simple_ko_sp | wpc)+
          apply (wp hoare_vcg_all_lift hoare_drop_imps)[1]
           apply(wp set_simple_ko_globals_equiv | wpc)+
       apply(wp set_thread_state_globals_equiv)
      apply (wp get_simple_ko_wp gbn_wp get_simple_ko_wp as_user_globals_equiv | wpc | simp)+
  apply (rule hoare_pre)
   apply(wpc)
              apply(rule fail_wp | rule return_wp)+
  by (auto intro: valid_arch_state_ko_at_arm valid_ep_send_enqueue
          simp: neq_Nil_conv cong: case_list_cons_cong)


subsection "Notifications"

lemma valid_ntfn_dequeue:
  "\<lbrakk> ko_at (Notification ntfn) ntfnptr s; ntfn_obj ntfn = (WaitingNtfn (t # ts));
     valid_objs s; ts \<noteq> []\<rbrakk>
     \<Longrightarrow> valid_ntfn ntfn s"
  unfolding valid_objs_def valid_obj_def valid_ntfn_def obj_at_def
  apply (drule bspec)
  apply (auto split: list.splits)
  done


(* FIXME: NTFN OBJECT CHANGED *)

lemma update_waiting_ntfn_globals_equiv:
  "\<lbrace>globals_equiv s and valid_objs and valid_arch_state and valid_global_refs and ko_at (Notification ntfn) ntfnptr and pspace_distinct and sym_refs \<circ> state_refs_of and (\<lambda>s. idle_thread s \<notin> set queue) and K (ntfn_obj ntfn = WaitingNtfn queue)\<rbrace>
    update_waiting_ntfn ntfnptr queue bound_tcb badge
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding update_waiting_ntfn_def
  apply(wp)
    apply(simp add: split_def)
    apply(wp set_thread_state_globals_equiv as_user_globals_equiv
             set_notification_globals_equiv set_notification_valid_ko_at_arm
             dxo_wp_weak | simp)+
  by (auto intro: valid_arch_state_ko_at_arm simp: neq_Nil_conv)

lemma
  blocked_cancel_ipc_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and valid_ko_at_arm\<rbrace> blocked_cancel_ipc a b \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding blocked_cancel_ipc_def
  by (wp set_thread_state_globals_equiv set_simple_ko_globals_equiv | wpc | simp)+




lemma cancel_ipc_blocked_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm and st_tcb_at receive_blocked a\<rbrace>
    cancel_ipc a \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding cancel_ipc_def
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (rule hoare_pre)
  apply (wpc; (simp,rule blocked_cancel_ipc_globals_equiv)?)
  apply (rule hoare_pre_cont)+
  apply clarsimp
  apply (case_tac state;(clarsimp simp: pred_tcb_at_def obj_at_def receive_blocked_def))
  by (simp add: eq_commute)


crunch globals_equiv[wp]: possible_switch_to "globals_equiv (st :: det_ext state)"
  (wp: tcb_sched_action_extended.globals_equiv reschedule_required_ext_extended.globals_equiv
   ignore_del: possible_switch_to)

lemma send_signal_globals_equiv:
  "\<lbrace>globals_equiv (s :: det_ext state) and valid_objs and valid_arch_state
     and valid_global_refs and sym_refs \<circ> state_refs_of and
     pspace_distinct and valid_idle\<rbrace> send_signal ntfnptr badge
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding send_signal_def
  apply (wp set_notification_globals_equiv
            possible_switch_to_globals_equiv
            set_thread_state_globals_equiv
            as_user_globals_equiv
            cancel_ipc_blocked_globals_equiv
            update_waiting_ntfn_globals_equiv
            get_simple_ko_wp
            gts_wp
       | wpc
       | simp)+
  apply clarsimp
  apply (frule (1) sym_refs_ko_atD)
  apply (intro allI impI conjI)
           prefer 8
           apply clarsimp
           apply (frule_tac t="idle_thread sa" and P="\<lambda>ref. \<not> idle ref" in ntfn_queued_st_tcb_at')
               by (auto intro: valid_arch_state_ko_at_arm
                         simp: pred_tcb_at_def obj_at_def valid_idle_def receive_blocked_def)

(*FIXME: belongs in Arch_IF*)

lemma receive_signal_globals_equiv:
  "\<lbrace>globals_equiv s and valid_objs and valid_arch_state and valid_global_refs
     and pspace_distinct and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
     receive_signal thread cap is_blocking
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding receive_signal_def fun_app_def do_nbrecv_failed_transfer_def
  apply (rule hoare_pre)
  apply(wp set_notification_globals_equiv set_thread_state_globals_equiv
           as_user_globals_equiv get_simple_ko_wp
       | wpc)+
   apply(simp add: valid_arch_state_ko_at_arm)
  done

lemma set_object_valid_global_refs:
  "\<lbrace>valid_global_refs and
      (\<lambda>s. \<forall>b. (\<forall>sz fun. obj=CNode sz fun \<longrightarrow> well_formed_cnode_n sz fun \<longrightarrow>
        (\<forall>cap. fun b = Some cap \<longrightarrow> global_refs s \<inter> cap_range cap = {})) \<and>
      (\<forall>tcb. obj = (TCB tcb) \<longrightarrow> (\<forall>get. (\<forall>set restr. tcb_cap_cases b \<noteq> Some (get, set, restr) \<or>
        global_refs s \<inter> cap_range(get tcb) = {}))))\<rbrace>
    set_object ptr obj
    \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  unfolding valid_global_refs_def valid_refs_def
  apply (wpsimp wp: set_object_wp simp: cte_wp_at_cases)
  apply (erule_tac x=b in allE)
  apply (erule_tac x=get in allE)
  apply (simp)
  done


lemma send_fault_ipc_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
    and pspace_distinct and pspace_aligned
    and valid_global_objs and valid_idle and (\<lambda>s. sym_refs (state_refs_of s)) and K (valid_fault fault)\<rbrace>
    send_fault_ipc tptr fault
    \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding send_fault_ipc_def
  apply(wp)
    apply(simp add: Let_def)
    apply(wp send_ipc_globals_equiv thread_set_globals_equiv thread_set_valid_objs'' thread_set_fault_valid_global_refs thread_set_valid_idle_trivial thread_set_refs_trivial | wpc | simp)+
   apply(rule_tac Q'="\<lambda>_. globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
        and pspace_distinct and pspace_aligned and
        valid_global_objs and K (valid_fault fault) and valid_idle and (\<lambda>s. sym_refs (state_refs_of s))"
        in hoare_post_imp_R)
    apply(wp | simp)+
   apply(clarsimp simp: valid_arch_state_ko_at_arm)
   apply(rule valid_tcb_fault_update)
    apply(wp | simp)+
    done

lemma handle_double_fault_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace>
     handle_double_fault tptr ex1 ex2
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding handle_double_fault_def
  by (wp set_thread_state_globals_equiv)

lemma send_ipc_valid_global_objs:
  "\<lbrace>valid_global_objs \<rbrace>
     send_ipc block call badge can_grant can_grant_reply thread epptr
   \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  unfolding send_ipc_def
  by (wp dxo_wp_weak hoare_drop_imps hoare_vcg_all_lift | simp | wpc | intro conjI impI)+

lemma send_fault_ipc_valid_global_objs:
  "\<lbrace>valid_global_objs \<rbrace> send_fault_ipc tptr fault
    \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  unfolding send_fault_ipc_def
  apply(wp)
     apply(simp add: Let_def)
     apply(wp send_ipc_valid_global_objs | wpc)+
    apply(rule_tac Q'="\<lambda>_. valid_global_objs" in hoare_post_imp_R)
     apply(wp | simp)+
  done

crunch valid_ko_at_arm[wp]: send_ipc "valid_ko_at_arm"
  (wp: hoare_drop_imps hoare_vcg_if_lift2 dxo_wp_weak)

lemma send_fault_ipc_valid_ko_at_arm[wp]:
  "invariant (send_fault_ipc a b) valid_ko_at_arm"
  unfolding send_fault_ipc_def
  apply wp
    apply(simp add: Let_def)
    apply (wp send_ipc_valid_ko_at_arm | wpc)+
   apply(rule_tac Q'="\<lambda>_. valid_ko_at_arm" in hoare_post_imp_R)
  apply (wp | simp)+
done

lemma handle_fault_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
       and pspace_distinct and pspace_aligned
       and valid_global_objs and valid_idle and (\<lambda>s. sym_refs (state_refs_of s))
       and K (valid_fault ex)\<rbrace>
     handle_fault thread ex
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding handle_fault_def
  apply(wp handle_double_fault_globals_equiv)
   apply(rule_tac Q="\<lambda>_. globals_equiv st and valid_ko_at_arm" and
             E="\<lambda>_. globals_equiv st and valid_ko_at_arm" in hoare_post_impErr)
     apply(wp send_fault_ipc_globals_equiv
          | simp add: valid_arch_state_ko_at_arm)+
     done


lemma handle_fault_reply_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
      handle_fault_reply fault thread x y
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply(case_tac fault)
     apply(wp as_user_globals_equiv | simp add: handle_arch_fault_reply_def)+
     done

crunch valid_global_objs: handle_fault_reply "valid_global_objs"

lemma do_reply_transfer_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs and pspace_distinct
       and pspace_aligned and valid_global_objs and valid_idle\<rbrace>
     do_reply_transfer sender receiver slot grant
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding do_reply_transfer_def
  apply(wp set_thread_state_globals_equiv cap_delete_one_globals_equiv do_ipc_transfer_globals_equiv
           thread_set_globals_equiv handle_fault_reply_globals_equiv dxo_wp_weak
       | wpc
       | simp split del: if_split)+
    apply(rule_tac Q="\<lambda>_. globals_equiv st and valid_ko_at_arm and valid_objs and valid_arch_state
                          and valid_global_refs and pspace_distinct and pspace_aligned
                          and valid_global_objs and (\<lambda>s. receiver \<noteq> idle_thread s) and valid_idle"
                in hoare_strengthen_post)
    apply (wp gts_wp
          | fastforce simp: valid_arch_state_ko_at_arm pred_tcb_at_def obj_at_def valid_idle_def)+
    done

lemma handle_reply_globals_equiv:
  "\<lbrace>globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
       and pspace_distinct and pspace_aligned and valid_global_objs and valid_idle\<rbrace>
     handle_reply
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding handle_reply_def
  apply(wp do_reply_transfer_globals_equiv | wpc)+
   apply(rule_tac Q="\<lambda>_. globals_equiv st and valid_objs and valid_arch_state and valid_global_refs
        and pspace_distinct and pspace_aligned and valid_global_objs and valid_idle"
        in hoare_strengthen_post)
    apply(wp | simp)+
    done

lemma reply_from_kernel_globals_equiv:
  "\<lbrace>globals_equiv s and valid_objs and valid_arch_state and valid_global_refs and pspace_distinct
       and pspace_aligned and  (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
     reply_from_kernel thread x
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding reply_from_kernel_def
  apply(wp set_message_info_globals_equiv set_mrs_globals_equiv
           as_user_globals_equiv | simp add: split_def)+
  apply(insert length_msg_lt_msg_max)
  apply(simp add: valid_arch_state_ko_at_arm)
  done

section "reads_respects_g"

subsection "Notifications"

lemma send_signal_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l (pas_refined aag and pas_cur_domain aag and valid_etcbs and
                           pspace_aligned and valid_vspace_objs and valid_arch_state and
                           valid_objs and valid_global_objs and valid_arch_state and
                           valid_global_refs and pspace_distinct and valid_idle and ct_active and
                           sym_refs \<circ> state_refs_of and is_subject aag \<circ> cur_thread and
                           K ((pasSubject aag, Notify, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag))
                          (send_signal ntfnptr badge)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule send_signal_reads_respects[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp send_signal_globals_equiv | simp)+
  done

lemma receive_signal_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l (valid_global_objs and valid_objs and valid_arch_state and valid_global_refs and pspace_distinct and pas_refined aag and (\<lambda>s. thread \<noteq> idle_thread s) and is_subject aag \<circ> cur_thread and K ((\<forall>ntfnptr\<in>Access.obj_refs cap.
          (pasSubject aag, Receive, pasObjectAbs aag ntfnptr)
          \<in> pasPolicy aag \<and>
      is_subject aag thread))) (receive_signal thread cap is_blocking)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule receive_signal_reads_respects[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp receive_signal_globals_equiv | simp)+
  done

subsection "Sycn IPC"

lemma send_ipc_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l (pas_refined aag and pas_cur_domain aag and invs
         and is_subject aag \<circ> cur_thread
         and (\<lambda> s. (can_grant \<longrightarrow> aag_has_auth_to aag Grant epptr))
         and K (is_subject aag thread \<and> aag_has_auth_to aag SyncSend epptr))
  (send_ipc block call badge can_grant can_grant_reply thread epptr)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule send_ipc_reads_respects[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp send_ipc_globals_equiv | simp)+
  by fastforce

lemma receive_ipc_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l (invs and (\<lambda>s. receiver \<noteq> idle_thread s) and pas_refined aag
         and pas_cur_domain aag and valid_cap cap and is_subject aag \<circ> cur_thread
         and K (is_subject aag receiver \<and> pas_cap_cur_auth aag cap \<and> AllowRead \<in> cap_rights cap))
   (receive_ipc receiver cap is_blocking)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule receive_ipc_reads_respects[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp receive_ipc_globals_equiv | simp)+
  by fastforce


subsection "Faults"

lemma send_fault_ipc_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l (invs and pas_refined aag and pas_cur_domain aag
         and is_subject aag \<circ> cur_thread and K (is_subject aag thread \<and> valid_fault fault))
     (send_fault_ipc thread fault)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule send_fault_ipc_reads_respects[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp send_fault_ipc_globals_equiv | simp)+
  by fastforce


lemma handle_fault_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l (invs and pas_refined aag and pas_cur_domain aag
         and is_subject aag \<circ> cur_thread and K (is_subject aag thread \<and> valid_fault fault))
     (handle_fault thread fault)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule handle_fault_reads_respects[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp handle_fault_globals_equiv | simp)+
  by fastforce

subsection "Replies"

lemma handle_fault_reply_reads_respects_g:
  "reads_respects_g aag l (valid_ko_at_arm and (\<lambda>s. thread \<noteq> idle_thread s) and K (is_subject aag thread)) (handle_fault_reply fault thread x y)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule handle_fault_reply_reads_respects)
   apply(rule doesnt_touch_globalsI)
   apply(wp handle_fault_reply_globals_equiv | simp)+
  done

lemma do_reply_transfer_reads_respects_f_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_f_g aag l (silc_inv aag st and invs and pas_refined aag and pas_cur_domain aag
         and tcb_at receiver and tcb_at sender and emptyable slot and is_subject aag \<circ> cur_thread
          and K (grant \<longrightarrow> is_subject aag receiver)
         and K (is_subject aag sender \<and> aag_can_read aag receiver \<and> is_subject aag (fst slot)))
     (do_reply_transfer sender receiver slot grant)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_f_g])
    apply(rule do_reply_transfer_reads_respects_f[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp do_reply_transfer_globals_equiv | simp)+
  apply(simp add: invs_def valid_state_def valid_pspace_def | blast)+
  done

lemma handle_reply_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_f_g aag l (silc_inv aag st and invs and
        pas_refined aag and pas_cur_domain aag and
        is_subject aag \<circ> cur_thread) (handle_reply)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_f_g])
    apply(rule handle_reply_reads_respects_f[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp handle_reply_globals_equiv | simp)+
  apply(simp add: invs_def valid_state_def valid_pspace_def | blast)+
  done

lemma reply_from_kernel_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_g aag l (valid_global_objs and
        valid_objs and valid_arch_state and valid_global_refs and pspace_distinct
        and pspace_aligned and (\<lambda>s. thread \<noteq> idle_thread s) and K (is_subject aag thread)) (reply_from_kernel thread x)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule reply_from_kernel_reads_respects[OF domains_distinct])
   apply(rule doesnt_touch_globalsI)
   apply(wp reply_from_kernel_globals_equiv | simp)+
  done

end

end
