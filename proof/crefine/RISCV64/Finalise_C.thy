(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_C
imports IpcCancel_C IsolatedThreadAction
begin

context kernel_m
begin

(* FIXME RISCV: move to CCorres_UL, remove previous ccorres_cases *)
(* note: moving this lemma outside of kernel_m locale currently causes some proofs to fail *)
lemma ccorres_cases:
  assumes P:    " P \<Longrightarrow> ccorres_underlying srel Ga rrel xf arrel axf G G' hs a b"
  assumes notP: "\<not>P \<Longrightarrow> ccorres_underlying srel Ga rrel xf arrel axf H H' hs  a b"
  shows "ccorres_underlying  srel Ga rrel xf arrel axf (\<lambda>s. (P \<longrightarrow> G s) \<and> (\<not>P \<longrightarrow> H s))
                      ({s. P \<longrightarrow> s \<in> G'} \<inter> {s. \<not>P \<longrightarrow> s \<in> H'})
                      hs a b"
  apply (cases P, auto simp: P notP)
  done

(* FIXME RISCV: move up, make ccorres_underlying, check if it could be made [simp] *)
(* Provide full ccorres context so it will work with ccorres_prog_only_cong enabled *)
lemma ccorres_dc_comp:
  "ccorres (dc \<circ> R) xf P P' hs m c = ccorres dc xf P P' hs m c "
  by simp

declare if_split [split del]

definition
  "option_map2 f m = option_map f \<circ> m"

lemma thread_state_ptr_set_tcbQueued_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> \<lbrace>s. s \<Turnstile>\<^sub>c (cparent \<^bsup>s\<^esup>thread_state_ptr [''tcbState_C''] :: tcb_C ptr)\<rbrace>
       Call thread_state_ptr_set_tcbQueued_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre, vcg)
  apply clarsimp \<comment> \<open>for speed\<close>
  apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff)
  apply (frule h_t_valid_clift)
  apply (clarsimp simp: packed_heap_update_collapse_hrs)
  apply (intro conjI;
         fwd_all_new \<open>subst parent_update_child\<close>
                     \<open>fastforce intro!: h_t_valid_c_guard
                                  simp: option_map2_def fun_eq_iff typ_heap_simps
                                 split: if_splits\<close>)
  done

lemma thread_state_ptr_set_tsType_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> \<lbrace>s. s \<Turnstile>\<^sub>c (cparent \<^bsup>s\<^esup>thread_state_ptr [''tcbState_C''] :: tcb_C ptr)\<rbrace>
       Call thread_state_ptr_set_tsType_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre, vcg)
  apply clarsimp \<comment> \<open>for speed\<close>
  apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff)
  apply (frule h_t_valid_clift)
  apply (clarsimp simp: packed_heap_update_collapse_hrs)
  apply (intro conjI;
         fwd_all_new \<open>subst parent_update_child\<close>
                     \<open>fastforce intro!: h_t_valid_c_guard
                                  simp: option_map2_def fun_eq_iff typ_heap_simps
                                 split: if_splits\<close>)
  done

lemma tcb_queue_prepend_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call tcb_queue_prepend_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply vcg
  apply (clarsimp simp: option_map2_def fun_eq_iff typ_heap_simps h_t_valid_clift_Some_iff
                 split: if_splits)
  done

lemma addToBitmap_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call addToBitmap_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply vcg
  apply clarsimp
  done

lemma ready_queues_index_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call ready_queues_index_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre)
  apply vcg
  apply clarsimp
  done

lemma tcbSchedEnqueue_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> \<lbrace>s. True\<rbrace>
       Call tcbSchedEnqueue_'proc
      {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
           \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
           \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
           \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre)
   apply (vcg exspec=thread_state_ptr_set_tcbQueued_spec_tcb_fields
              exspec=tcb_queue_prepend_spec_tcb_fields
              exspec=addToBitmap_spec_tcb_fields
              exspec=ready_queues_index_spec_tcb_fields)
  apply simp
  done

lemma isSchedulable_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call isSchedulable_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply (vcg exspec=isRunnable_modifies)
  apply clarsimp
  done

lemma rescheduleRequired_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call rescheduleRequired_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply (vcg exspec=tcbSchedEnqueue_spec_tcb_fields exspec=isSchedulable_spec_tcb_fields)
  apply clarsimp
  done

lemma possibleSwitchTo_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call possibleSwitchTo_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply (vcg exspec=rescheduleRequired_spec_tcb_fields exspec=tcbSchedEnqueue_spec_tcb_fields)
  apply clarsimp
  done

lemma setThreadState_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call setThreadState_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply (vcg exspec=rescheduleRequired_spec_tcb_fields
             exspec=thread_state_ptr_set_tsType_spec_tcb_fields
             exspec=isSchedulable_spec_tcb_fields)
  apply clarsimp
  done

lemma refill_head_overlapping_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call refill_head_overlapping_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply vcg
  apply clarsimp
  done

lemma refill_pop_head_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call refill_pop_head_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply (vcg exspec=refill_head_modifies exspec=refill_next_modifies exspec=refill_size_modifies)
  apply (clarsimp simp: typ_heap_simps)
  done

lemma merge_overlapping_head_refill_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call merge_overlapping_head_refill_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply (vcg exspec=refill_pop_head_spec_tcb_fields exspec=refill_head_modifies
             exspec=refill_index_modifies)
  apply (clarsimp simp: typ_heap_simps)
  done

lemma refill_unblock_check_spec_tcb_fields:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call refill_unblock_check_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  (is "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} ?f ({s'. ?post s s'})")
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (clarsimp simp: whileAnno_def)
  apply (rule_tac I1="{t. ?post t s}" in subst[OF whileAnno_def])
  apply (vcg exspec=merge_overlapping_head_refill_spec_tcb_fields
             exspec=refill_head_overlapping_spec_tcb_fields)
    subgoal by (clarsimp simp: option_map2_def typ_heap_simps split: if_splits)
   apply fastforce
  apply fastforce
  done

lemma restart_thread_if_no_fault_spec_tcb_fields:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s}
       Call restart_thread_if_no_fault_'proc
       {s'. option_map2 tcbEPNext_C (cslift s') = option_map2 tcbEPNext_C (cslift s)
            \<and> option_map2 tcbEPPrev_C (cslift s') = option_map2 tcbEPPrev_C (cslift s)
            \<and> option_map2 tcbPriority_C (cslift s') = option_map2 tcbPriority_C (cslift s)
            \<and> option_map2 tcbDomain_C (cslift s') = option_map2 tcbDomain_C (cslift s)}"
  apply (rule allI, rule conseqPre)
  apply (vcg exspec=possibleSwitchTo_spec_tcb_fields exspec=setThreadState_spec_tcb_fields
             exspec=refill_unblock_check_spec_tcb_fields)
  apply clarsimp
  done

lemma ep_queue_relation_shift:
  "(option_map2 tcbEPNext_C (cslift s')
         = option_map2 tcbEPNext_C (cslift s)
    \<and> option_map2 tcbEPPrev_C (cslift s')
         = option_map2 tcbEPPrev_C (cslift s))
     \<longrightarrow> ep_queue_relation (cslift s') ts qPrev qHead
          = ep_queue_relation (cslift s) ts qPrev qHead"
  apply clarsimp
  apply (induct ts arbitrary: qPrev qHead)
   apply simp
  apply simp
  apply (simp add: option_map2_def fun_eq_iff
                   map_option_case)
  apply (drule_tac x=qHead in spec)+
  apply (clarsimp split: option.split_asm)
  done

lemma obj_at_ko_at2':
  "\<lbrakk> obj_at' P p s; ko_at' ko p s \<rbrakk> \<Longrightarrow> P ko"
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (drule ko_at_obj_congD', simp+)
  done

lemma ctcb_relation_tcbDomain:
  "ctcb_relation tcb tcb' \<Longrightarrow> ucast (tcbDomain tcb) = tcbDomain_C tcb'"
  by (simp add: ctcb_relation_def)

lemma ctcb_relation_tcbPriority:
  "ctcb_relation tcb tcb' \<Longrightarrow> ucast (tcbPriority tcb) = tcbPriority_C tcb'"
  by (simp add: ctcb_relation_def)

lemma ctcb_relation_tcbDomain_maxDomain_numDomains:
  "\<lbrakk> ctcb_relation tcb tcb'; tcbDomain tcb \<le> maxDomain \<rbrakk>
   \<Longrightarrow> unat (tcbDomain_C tcb') < Kernel_Config.numDomains"
  apply (subst ctcb_relation_tcbDomain[symmetric], simp)
  apply (simp add: le_maxDomain_eq_less_numDomains)
  done

lemma ctcb_relation_tcbPriority_maxPriority_numPriorities:
  "\<lbrakk> ctcb_relation tcb tcb'; tcbPriority tcb \<le> maxPriority \<rbrakk>
    \<Longrightarrow> unat (tcbPriority_C tcb') < numPriorities"
  apply (subst ctcb_relation_tcbPriority[symmetric], simp)
  apply (simp add: maxPriority_def numPriorities_def word_le_nat_alt)
  done

lemma isRoundRobin_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     \<top> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> [] (isRoundRobin scPtr) (Call isRoundRobin_'proc)"
  apply cinit
   apply (rule ccorres_pre_getObject_sc)
   apply (ctac add: ccorres_return_C)
  apply (fastforce simp: rf_sr_def csched_context_relation_def typ_heap_simps split: if_splits)
  done

lemma refill_ready_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     \<top> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> hs
     (refillReady scPtr) (Call refill_ready_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  unfolding refillReady_def readRefillReady_def gets_the_obind ohaskell_state_assert_def
            gets_the_ostate_assert
  apply (rule ccorres_symb_exec_l'
               [OF _ _ stateAssert_sp[simplified HaskellLib_H.stateAssert_def]];
         (solves wpsimp)?)+
  apply (cinit' lift: sc_'
                simp: readCurTime_def gets_the_ogets getRefillHead_def[symmetric]
                      getCurTime_def[symmetric])
   apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                in ccorres_split_nothrow_call)
          apply (fastforce intro: refill_head_ccorres)
         apply fastforce
        apply fastforce
       apply fastforce
      apply ceqv
     apply (rule ccorres_pre_getCurTime)
     apply (rule ccorres_Guard)
     apply (fastforce intro: ccorres_return_C)
    apply wpsimp
   apply vcg
  apply (clarsimp simp: active_sc_at'_def)
  apply (normalise_obj_at', rename_tac sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (frule (1) obj_at_cslift_sc)
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def)
   apply fastforce
  by (fastforce simp: csched_context_relation_def crefill_relation_def typ_heap_simps
                      h_val_field_from_bytes' sc_ptr_to_crefill_ptr_def
               split: if_splits)

crunch refillReady
 for (empty_fail) empty_fail[wp]

lemma refill_next_ccorres:
  "ccorres (\<lambda>next next'. next = unat next') ret__unsigned_long_'
     (valid_objs' and K (Suc idx < 2 ^ word_bits))
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>index = word_of_nat idx\<rbrace>) []
     (getRefillNext scPtr idx) (Call refill_next_'proc)"
  supply len_bit0[simp del]
  unfolding getRefillNext_def readRefillNext_def gets_the_obind ohaskell_state_assert_def
            gets_the_ostate_assert
  apply (rule ccorres_symb_exec_l'
               [OF _ _ stateAssert_sp[simplified HaskellLib_H.stateAssert_def]];
         (solves wpsimp)?)+
  apply (cinit' lift: sc_' index_'
                simp: refillNext_def readSchedContext_def getObject_def[symmetric]
                      getSchedContext_def[symmetric])
   apply (rule ccorres_pre_getObject_sc, rename_tac sc)
   apply (rule ccorres_move_c_guard_sc)
   apply (rule ccorres_return_C; clarsimp)
  apply (rule conjI)
   apply clarsimp
  apply (clarsimp simp: active_sc_at'_def)
  apply normalise_obj_at'
  apply (rename_tac sc' sc)
  apply (frule (1) obj_at_cslift_sc)
  apply (clarsimp simp: typ_heap_simps csched_context_relation_def split: if_splits)
  apply (prop_tac "0 < scRefillMax sc")
   apply (clarsimp simp: active_sc_at'_def obj_at'_def)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: word_bits_def)
  apply (frule (1) length_scRefills_bounded)
  apply (intro conjI impI allI)
   apply (cut_tac x=idx
              and y="unat (scRefillMax_C sc') - Suc 0"
              and 'a1=machine_word_len
               in inj_on_contraD[OF inj_on_word_of_nat])
      apply assumption
     apply fastforce
    apply (fastforce simp: valid_sched_context'_def word_bits_def refillSizeBytes_def)
   apply fastforce
  apply (fastforce simp: unat_of_nat_eq unat_add_lem')
  done

lemma refill_pop_head_ccorres:
  "ccorres crefill_relation ret__struct_refill_C_'
     no_0_obj' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (refillPopHead scPtr) (Call refill_pop_head_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  unfolding refillPopHead_def K_bind_apply
  apply (rule ccorres_symb_exec_l'[OF _ _ stateAssert_sp]; (solves wpsimp)?)+
  apply (cinit' lift: sc_')
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                  in ccorres_split_nothrow_call)
            apply (fastforce intro: refill_head_ccorres)
           apply fastforce
          apply fastforce
         apply fastforce
        apply ceqv
       apply (rule ccorres_Guard_Seq)
       apply csymbr
       apply (rule ccorres_pre_getObject_sc)
       apply (rule ccorres_move_c_guard_sc)
       apply (ctac add: refill_next_ccorres, rename_tac next')
         apply (rule ccorres_split_nothrow)
             apply (rule_tac P=\<top> in updateSchedContext_ccorres_lemma2)
               apply vcg
              apply fastforce
             apply clarsimp
             apply (rename_tac sc sc')
             apply (rule conjI)
              apply (clarsimp simp: typ_heap_simps')
             apply (rule_tac sc'="scRefillHead_C_update (\<lambda>_. next') sc'"
                          in rf_sr_sc_update_no_refill_buffer_update2;
                    fastforce?)
               apply (clarsimp simp: typ_heap_simps')
              apply (clarsimp simp: csched_context_relation_def)
             apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
            apply ceqv
           apply (fastforce intro: ccorres_return_C)
          apply wpsimp
         apply vcg
        apply (wpsimp wp: getRefillNext_wp)
       apply (vcg exspec=refill_next_modifies)
      apply wpsimp
     apply vcg
    apply vcg
   apply (rule conseqPre, vcg, clarsimp)
  apply (clarsimp simp: active_sc_at'_def)
  apply (normalise_obj_at', rename_tac sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply clarsimp
  apply (frule (1) length_scRefills_bounded)
  apply (frule (1) obj_at_cslift_sc)
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def)
   apply fastforce
  apply (fastforce simp: crefill_relation_def typ_heap_simps csched_context_relation_def
                         sc_ptr_to_crefill_ptr_def refillSizeBytes_def valid_sched_context'_def)
  done

lemma refill_single_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (sc_at' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> [] (refillSingle scPtr) (Call refill_single_'proc)"
  apply (cinit lift: sc_'
               simp: readRefillSingle_def readSchedContext_def
                     getObject_def[symmetric] getSchedContext_def[symmetric])
   apply (rule ccorres_pre_getObject_sc)
   apply (ctac add: ccorres_return_C)
  by (clarsimp simp: csched_context_relation_def typ_heap_simps split: if_splits)

lemma refill_head_overlapping_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (valid_objs' and no_0_obj' and active_sc_at' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (gets_the (refillHeadOverlapping scPtr))
     (Call refill_head_overlapping_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  apply (simp add: refillHeadOverlapping_def oliftM_def gets_the_if_distrib)
  apply (subst gets_the_obind)+
  apply (subst getRefillHead_def[symmetric])
  apply (cinit' lift: sc_')
   apply (simp flip: refillSingle_def)
   apply (ctac add: refill_single_ccorres)
     apply (rule ccorres_cond[where R=\<top>])
       apply (fastforce simp: to_bool_def)
      apply (rule ccorres_rhs_assoc)+
      apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                   in ccorres_split_nothrow_call)
             apply (fastforce intro: refill_head_ccorres)
            apply fastforce
           apply fastforce
          apply fastforce
         apply ceqv
        apply (simp add: readSchedContext_def flip: getObject_def getSchedContext_def)
        apply (rule ccorres_Guard_Seq)
        apply csymbr+
        apply (rule ccorres_move_c_guard_sc)
        apply (rule ccorres_pre_getObject_sc)
        apply (simp flip: getRefillNext_def)
        apply (ctac add: refill_next_ccorres)
          apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                       in ccorres_split_nothrow_call)
                 apply (fastforce intro: refill_index_ccorres)
                apply fastforce
               apply fastforce
              apply fastforce
             apply ceqv
            apply (rule ccorres_Guard)
            apply (fastforce intro: ccorres_return_C)
           apply wpsimp
          apply vcg
         apply (wpsimp wp: getRefillNext_wp)
        apply vcg
       apply wpsimp
      apply vcg
     apply (fastforce intro: ccorres_return_C)
    apply (wpsimp simp: refillSingle_def)
   apply (vcg exspec=refill_single_modifies)
  apply (clarsimp simp: active_sc_at'_def)
  apply (normalise_obj_at', rename_tac sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply clarsimp
  apply (frule (1) length_scRefills_bounded)
  apply (frule valid_objs'_valid_refills')
    apply fastforce
   apply (clarsimp simp: is_active_sc'_def opt_pred_def opt_map_def obj_at'_def)
  apply (frule (1) obj_at_cslift_sc)
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n=0 in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def)
   apply fastforce
  apply (frule_tac n=1 in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def MIN_REFILLS_def)
   apply fastforce
  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def)
   apply fastforce
  apply (frule_tac n="refillNext sc (scRefillHead sc)" in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def)
    apply (metis refillNext_less_length_scRefills)
   apply fastforce
  apply normalise_obj_at'
  apply (rename_tac sc sc')
  apply (rule conjI)
   apply (clarsimp simp: refillSizeBytes_def valid_sched_context'_def
                         opt_pred_def opt_map_def obj_at'_def)
   apply (metis refillNext_less_length_scRefills)
  apply (clarsimp simp: typ_heap_simps csched_context_relation_def crefill_relation_def
                        h_val_field_from_bytes' sc_ptr_to_crefill_ptr_def
                 split: if_splits)
  apply (frule valid_refills'_nonzero_scRefillCount)
  apply (case_tac "scRefillHead sc = scRefillMax sc - 1")
   apply (prop_tac "scRefillHead_C sc' = scRefillMax_C sc' - 1")
    apply (subst word_unat_eq_iff)
    apply (clarsimp simp: unat_sub word_le_nat_alt)
   apply clarsimp
  apply (prop_tac "scRefillHead_C sc' \<noteq> scRefillMax_C sc' - 1")
   apply (fastforce simp: unat_sub word_le_nat_alt csched_context_relation_def)
  apply (clarsimp simp: refillNext_def add_ac)
  done

lemma merge_overlapping_head_refill_ccorres:
  "ccorres dc xfdc
     (valid_objs' and no_0_obj' and pspace_aligned' and pspace_distinct' and pspace_bounded'
      and (\<lambda>s. active_sc_at' scPtr s \<and> ((\<lambda>sc. 1 < refillSize sc) |< scs_of' s) scPtr))
     \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (mergeOverlappingRefills scPtr) (Call merge_overlapping_head_refill_'proc)"
  (is "ccorres _ _ (?abs and _) _ _ _ _")
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  apply (cinit lift: sc_')
   apply (ctac add: refill_pop_head_ccorres, rename_tac old_head old_head')
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow)
         apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
         apply (rule updateSchedContext_ccorres_lemma3
                      [where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)" and P'="?abs"])
           apply vcg
          apply fastforce
         apply clarsimp
         apply (rename_tac sc sc')
         apply (frule (1) sc_ko_at_valid_objs_valid_sc')
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
         apply (intro conjI)
            apply (clarsimp simp: typ_heap_simps)
           apply (rule disjCI2)
           apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
            apply (fastforce intro: sc_at_array_assertion')
           apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
          apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps
                                csched_context_relation_def)
         apply (clarsimp simp: crefill_relation_def csched_context_relation_def
                         cong: StateSpace.state.fold_congs)
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
         apply clarsimp
         apply (rule_tac old_sc=sc and n="scRefillHead sc"
                     and fa="rTime_update (\<lambda>_. rTime old_head)"
                      in rf_sr_refill_update2; fastforce?)
            apply (fastforce simp: sched_context.expand)
           apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def)
          apply (fastforce simp: csched_context_relation_def)
         apply (fastforce dest: crefill_relationD simp: typ_heap_simps' crefill_relation_def)
        apply ceqv
       apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
       apply (rule updateSchedContext_ccorres_lemma3
                    [where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)" and P'="?abs"])
         apply vcg
        apply fastforce
       apply clarsimp
       apply (rename_tac sc sc')
       apply (frule (1) sc_ko_at_valid_objs_valid_sc')
       apply (frule rf_sr_refill_buffer_relation)
       apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
       apply (intro conjI)
            apply (clarsimp simp: typ_heap_simps)
           apply (rule disjCI2)
           apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
            apply (fastforce intro: sc_at_array_assertion')
           apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
          apply (clarsimp simp: typ_heap_simps)
         apply (rule disjCI2)
         apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
          apply (fastforce intro: sc_at_array_assertion')
         apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
        apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
       apply (clarsimp simp: crefill_relation_def csched_context_relation_def)
       apply (frule rf_sr_refill_buffer_relation)
       apply (frule h_t_valid_clift_Some_iff[THEN iffD1])
       apply (clarsimp cong: StateSpace.state.fold_congs)
       apply (rule_tac old_sc=sc and n="scRefillHead sc"
                       and fa="\<lambda>head. rAmount_update (\<lambda>_. rAmount head + rAmount old_head) head"
                        in rf_sr_refill_update2; fastforce?)
          apply (fastforce simp: sched_context.expand)
         apply (clarsimp simp: typ_heap_simps)
         apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
        apply (fastforce simp: csched_context_relation_def)
       apply (fastforce dest: crefill_relationD
                        simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def crefill_relation_def)
      apply (rule_tac Q'="\<lambda>_. ?abs and active_sc_at' scPtr" in hoare_post_imp)
       apply (clarsimp simp: active_sc_at'_def)
       apply normalise_obj_at'
       apply (frule (1) sc_ko_at_valid_objs_valid_sc')
       apply (clarsimp simp: valid_sched_context'_def)
      apply (wpsimp wp: updateRefillHd_valid_objs')
     apply vcg
    apply (rule_tac Q'="\<lambda>_.?abs and active_sc_at' scPtr" in hoare_post_imp)
     apply (clarsimp simp: active_sc_at'_def)
     apply normalise_obj_at'
     apply (frule (1) sc_ko_at_valid_objs_valid_sc')
     apply (clarsimp simp: valid_sched_context'_def)
    apply wpsimp
   apply vcg
  apply clarsimp
  done

(* FIXME RT: move to Corres_UL_C? *)
lemma ccorres_to_vcg_Normal':
  "\<lbrakk>ccorres_underlying srel \<Gamma> rrel xf arrel axf P P' [] a c\<rbrakk>
   \<Longrightarrow> \<Gamma> \<turnstile> {s'. P s \<and> \<not> snd (a s) \<and> s' \<in> P' \<and> (s, s') \<in> srel} c UNIV"
  apply (frule ccorres_to_vcg_with_prop'[where R="\<top>\<top>" and s=s])
   apply wpsimp
  apply (fastforce elim: conseqPost)
  done

lemma ccorres_to_vcg_Normal:
  "\<lbrakk>ccorres_underlying srel \<Gamma> rrel xf arrel axf P P' [] a c; no_fail Q a\<rbrakk>
   \<Longrightarrow> \<Gamma> \<turnstile> {s'. P s \<and> Q s \<and> s' \<in> P' \<and> (s, s') \<in> srel} c UNIV"
  by (fastforce elim: ccorres_to_vcg_Normal' intro: conseqPre simp: no_fail_def)

crunch scActive
 for (empty_fail) empty_fail[wp]

lemma refill_unblock_check_ccorres:
  "ccorres dc xfdc
     (no_0_obj' and pspace_aligned' and pspace_distinct' and pspace_bounded')
     \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (refillUnblockCheck scPtr) (Call refill_unblock_check_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  apply (cinit lift: sc_')
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_assert2)
      apply (ctac add: isRoundRobin_ccorres, rename_tac is_round_robin)
        apply clarsimp
        apply (rule ccorres_cond_seq)
        apply ccorres_rewrite
        apply (rule_tac P="to_bool is_round_robin" in ccorres_cases)
         apply clarsimp
         apply (rule ccorres_cond_true)
         apply (rule ccorres_symb_exec_l)
            apply (rule ccorres_return_void_C)
           apply wpsimp+
        apply (rule ccorres_cond_false)
        apply (ctac add: refill_ready_ccorres)
          apply (clarsimp simp: when_def simp del: Collect_const)
          apply (rule_tac ccorres_cond[where R=\<top>])
            apply (fastforce simp: to_bool_def)
           apply (rule ccorres_pre_getCurTime, rename_tac curTime)
           apply (rule ccorres_rhs_assoc)
           apply (rule ccorres_rhs_assoc)
           apply (rule ccorres_split_nothrow)
               apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
               apply (rule_tac P'="?abs and valid_objs' and (\<lambda>s. ksCurTime s = curTime)"
                            in updateSchedContext_ccorres_lemma3
                                [where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)"])
                 apply vcg
                apply fastforce
               apply clarsimp
               apply (rename_tac sc sc')
               apply (frule (1) sc_ko_at_valid_objs_valid_sc')
               apply (frule rf_sr_refill_buffer_relation)
               apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
               apply (intro conjI)
                  apply (clarsimp simp: typ_heap_simps)
                 apply (rule disjCI2)
                 apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                  apply (fastforce intro: sc_at_array_assertion')
                 apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
                apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps
                                      csched_context_relation_def)
               apply (clarsimp cong: StateSpace.state.fold_congs)
               apply (rule_tac old_sc=sc and n="scRefillHead sc"
                           and fa="rTime_update (\<lambda>_. ksCurTime s)"
                            in rf_sr_refill_update2;
                      fastforce?)
                  apply (fastforce simp: sched_context.expand)
                 apply (clarsimp simp: valid_sched_context'_def)
                 apply (fastforce simp: typ_heap_simps sc_ptr_to_crefill_ptr_def
                                        csched_context_relation_def)
                apply (clarsimp simp: csched_context_relation_def)
               apply (fastforce dest: crefill_relationD rf_sr_ksCurTime
                                simp: crefill_relation_def sc_ptr_to_crefill_ptr_def
                                      csched_context_relation_def)
              apply ceqv
             apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                 apply (rule_tac ccorres_from_vcg[where P=\<top> and P'=UNIV])
                 apply (rule allI, rule conseqPre, vcg)
                 apply (clarsimp simp: setReprogramTimer_def modify_def get_def put_def bind_def
                                       rf_sr_def cstate_relation_def Let_def
                                       carch_state_relation_def cmachine_state_relation_def)
                apply ceqv
               apply (clarsimp simp: whileAnno_def refillHeadOverlappingLoop_def)
               apply (rule ccorres_handlers_weaken)
               apply (rule_tac G="\<lambda>_. ?abs and valid_objs' and active_sc_at' scPtr" and G'=UNIV
                            in ccorres_While')
                    apply (rule ccorres_guard_imp)
                      apply (ctac add: merge_overlapping_head_refill_ccorres)
                     apply (clarsimp simp: active_sc_at'_rewrite runReaderT_def)
                     apply (fastforce dest: use_ovalid[OF refillHeadOverlapping_refillSize]
                                     intro: valid_objs'_valid_refills')
                    apply clarsimp
                   apply (clarsimp simp: runReaderT_def)
                   apply (rule ccorres_guard_imp)
                     apply (ctac add: refill_head_overlapping_ccorres)
                    apply clarsimp
                   apply clarsimp
                  apply wpsimp
                  apply (clarsimp simp: active_sc_at'_def)
                  apply (wpsimp wp: no_ofail_refillHeadOverlapping
                              simp: runReaderT_def active_sc_at'_def)
                 apply (wpsimp wp: updateRefillHd_valid_objs' mergeOverlappingRefills_valid_objs')
                 apply (clarsimp simp: active_sc_at'_rewrite runReaderT_def)
                 apply (fastforce dest: use_ovalid[OF refillHeadOverlapping_refillSize]
                                 intro: valid_objs'_valid_refills')
                apply (rule conseqPre)
                 apply (rule_tac s=s and xf=xfdc in ccorres_to_vcg_Normal)
                  apply (fastforce intro: ccorres_call[OF merge_overlapping_head_refill_ccorres])
                 apply wpsimp
                apply (clarsimp simp: active_sc_at'_rewrite runReaderT_def)
                apply (fastforce dest: use_ovalid[OF refillHeadOverlapping_refillSize]
                                intro: valid_objs'_valid_refills')
               apply (rule conseqPre)
                apply clarsimp
                apply (rule_tac s=s and xf=ret__unsigned_long_' in ccorres_to_vcg_Normal)
                 apply (fastforce intro: ccorres_call
                                          [OF refill_head_overlapping_ccorres[where scPtr=scPtr]])
                apply (rule no_ofail_gets_the)
                apply (wpsimp wp: no_ofail_refillHeadOverlapping)
               apply (clarsimp simp: active_sc_at'_rewrite)
              apply wpsimp
             apply vcg
            apply (wpsimp wp: updateRefillHd_valid_objs')
           apply vcg
          apply (rule ccorres_return_Skip)
         apply (rule_tac Q'="\<lambda>_.?abs and valid_objs' and active_sc_at' scPtr" in hoare_post_imp)
          apply (clarsimp simp: active_sc_at'_def)
          apply normalise_obj_at'
          apply (frule (1) sc_ko_at_valid_objs_valid_sc')
          apply (clarsimp simp: obj_at'_def valid_sched_context'_def)
         apply wpsimp
        apply clarsimp
        apply vcg
       apply (wpsimp wp: isRoundRobin_wp)
      apply vcg
     apply wpsimp+
  apply (clarsimp simp: active_sc_at'_def obj_at'_def to_bool_def)
  done

lemma cancel_all_ccorres_helper:
  "ccorres dc xfdc
     (\<lambda>s. valid_objs' s
          \<and> (\<forall>t\<in>set ts. tcb_at' t s \<and> t \<noteq> 0)
          \<and> sch_act_wf (ksSchedulerAction s) s)
     {s'. \<exists>p. ep_queue_relation (cslift s') ts p (thread_' s')} hs
     (mapM_x cancelAllIPC_loop_body ts)
     (WHILE \<acute>thread \<noteq> NULL DO
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>thread\<rbrace>
            (\<acute>ret__unsigned_longlong :== CALL thread_state_get_replyObject(h_val (hrs_mem \<acute>t_hrs)
                                              (Ptr &(\<acute>thread\<rightarrow>[''tcbState_C'']) )));;
      \<acute>reply :== reply_Ptr (scast \<acute>ret__unsigned_longlong);;
      IF PTR_COERCE(reply_C \<rightarrow> unit) \<acute>reply \<noteq> PTR(unit) (scast 0)
        THEN CALL reply_unlink(\<acute>reply,\<acute>thread)
      FI;;
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>thread\<rbrace>
                    (\<acute>ret__unsigned_longlong :== CALL seL4_Fault_get_seL4_FaultType(h_val (hrs_mem \<acute>t_hrs)
                                                      (Ptr &(\<acute>thread\<rightarrow>[''tcbFault_C'']))));;
      IF \<acute>ret__unsigned_longlong = scast seL4_Fault_NullFault
        THEN CALL setThreadState(\<acute>thread,scast ThreadState_Restart);;
             Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>thread\<rbrace>
                           (\<acute>ret__unsigned_long :== CALL sc_sporadic(h_val (hrs_mem \<acute>t_hrs)
                                                         (Ptr &(\<acute>thread\<rightarrow>[''tcbSchedContext_C'']))));;
             IF \<acute>ret__unsigned_long \<noteq> 0
               THEN SKIP;;
                    Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>thread\<rbrace>
                    (IF h_val (hrs_mem \<acute>t_hrs) (Ptr &(\<acute>thread\<rightarrow>[''tcbSchedContext_C''])) \<noteq> \<acute>ksCurSC
                      THEN Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>thread\<rbrace>
                                         (CALL refill_unblock_check(h_val (hrs_mem \<acute>t_hrs)
                                               (Ptr &(\<acute>thread\<rightarrow>[''tcbSchedContext_C'']))))
                     FI)
             FI;;
             CALL possibleSwitchTo(\<acute>thread)
        ELSE CALL setThreadState(\<acute>thread,scast ThreadState_Inactive)
      FI;;
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>thread\<rbrace>
            (\<acute>thread :== h_val (hrs_mem \<acute>t_hrs) (Ptr &(\<acute>thread\<rightarrow>[''tcbEPNext_C''])))
    OD)"
  unfolding whileAnno_def
proof (induct ts)
  case Nil
  show ?case
    apply (simp del: Collect_const)
    apply (rule iffD1 [OF ccorres_expand_while_iff])
    apply (rule ccorres_tmp_lift2[where G'=UNIV and G''="\<lambda>x. UNIV", simplified])
     apply ceqv
    apply (simp add: ccorres_cond_iffs mapM_x_def sequence_x_def)
    apply (rule ccorres_guard_imp2, rule ccorres_return_Skip)
    apply simp
    done
next
  case (Cons thread threads)
  show ?case
    apply (rule iffD1 [OF ccorres_expand_while_iff])
    apply (simp del: Collect_const
                add: mapM_x_Cons)
    apply (rule ccorres_guard_imp2)
     apply (rule_tac xf'=thread_' in ccorres_abstract)
      apply ceqv
     apply (rule_tac P="rv' = tcb_ptr_to_ctcb_ptr thread"
                     in ccorres_gen_asm2)
     apply (rule_tac P="tcb_ptr_to_ctcb_ptr thread \<noteq> Ptr 0"
                     in ccorres_gen_asm)
     apply (clarsimp simp add: Collect_True ccorres_cond_iffs
                     simp del: Collect_const)
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow[where F=UNIV])
         apply (intro ccorres_rhs_assoc)
sorry (* FIXME RT: cancel_all_ccorres_helper *) (*
         apply (ctac(no_vcg) add: setThreadState_ccorres)
          apply (rule ccorres_add_return2)
          apply (ctac(no_vcg) add: tcbSchedEnqueue_ccorres)
           apply (rule_tac P="tcb_at' thread"
                      in ccorres_from_vcg[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
           apply (drule obj_at_ko_at', clarsimp)
           apply (erule cmap_relationE1 [OF cmap_relation_tcb])
            apply (erule ko_at_projectKO_opt)
           apply (fastforce intro: typ_heap_simps)
          apply (wp  | simp)+
        apply (rule ceqv_refl)
       apply (rule "Cons.hyps")
      apply (wp sts_valid_objs' sts_sch_act sch_act_wf_lift hoare_vcg_const_Ball_lift
                sts_st_tcb' | simp)+

     apply (vcg exspec=setThreadState_cslift_spec exspec=tcbSchedEnqueue_cslift_spec)
    apply (clarsimp simp: tcb_at_not_NULL Collect_const_mem valid_tcb_state'_def
                          ThreadState_defs mask_def valid_objs'_maxDomain valid_objs'_maxPriority)
    apply (drule(1) obj_at_cslift_tcb)
    apply (clarsimp simp: typ_heap_simps)
    apply (rule conjI)
     apply clarsimp
     apply (frule rf_sr_cscheduler_relation)
     apply (clarsimp simp: cscheduler_action_relation_def
                           st_tcb_at'_def
                    split: scheduler_action.split_asm)
     apply (rename_tac word)
     apply (frule_tac x=word in tcbSchedEnqueue_cslift_precond_discharge; clarsimp?)
     apply simp
    apply clarsimp
    apply (rule conjI)
     apply (frule(3) tcbSchedEnqueue_cslift_precond_discharge)
     apply clarsimp
    apply clarsimp+
    apply (subst ep_queue_relation_shift, fastforce)
    apply (drule_tac x="tcb_ptr_to_ctcb_ptr thread"
                in fun_cong)+
    apply (clarsimp simp add: option_map2_def typ_heap_simps)
    apply fastforce
    done
 *)
qed

lemma cancelAllIPC_ccorres:
  "ccorres dc xfdc invs' (UNIV \<inter> {s. epptr_' s = Ptr epptr}) []
   (cancelAllIPC epptr) (Call cancelAllIPC_'proc)"
  apply (cinit lift: epptr_')
sorry (* FIXME RT: cancelAllIPC_ccorres *) (*
   apply (rule ccorres_symb_exec_l [OF _ getEndpoint_inv _ empty_fail_getEndpoint])
    apply (rule_tac xf'=ret__unsigned_longlong_'
                and val="case ep of IdleEP \<Rightarrow> scast EPState_Idle
                            | RecvEP _ \<Rightarrow> scast EPState_Recv | SendEP _ \<Rightarrow> scast EPState_Send"
                and R="ko_at' ep epptr"
             in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply vcg
       apply clarsimp
       apply (erule cmap_relationE1 [OF cmap_relation_ep])
        apply (erule ko_at_projectKO_opt)
       apply (clarsimp simp add: typ_heap_simps)
       apply (simp add: cendpoint_relation_def Let_def
                 split: endpoint.split_asm)
      apply ceqv
     apply (rule_tac A="invs' and ksReadyQueues_asrt and ko_at' ep epptr"
              in ccorres_guard_imp2[where A'=UNIV])
      apply wpc
        apply (rename_tac list)
        apply (simp add: endpoint_state_defs
                         Collect_False Collect_True
                         ccorres_cond_iffs
                    del: Collect_const)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply (rule ccorres_abstract_cleanup)
        apply csymbr
        apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
        apply (rule_tac r'=dc and xf'=xfdc
                       in ccorres_split_nothrow)
            apply (rule_tac P="ko_at' (RecvEP list) epptr and invs'"
                     in ccorres_from_vcg[where P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply clarsimp
            apply (rule cmap_relationE1 [OF cmap_relation_ep])
              apply assumption
             apply (erule ko_at_projectKO_opt)
            apply (clarsimp simp: typ_heap_simps setEndpoint_def)
            apply (rule rev_bexI)
             apply (rule setObject_eq; simp add: objBits_simps')[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  carch_state_relation_def carch_globals_def
                                  cmachine_state_relation_def
                                  packed_heap_update_collapse_hrs)
            apply (clarsimp simp: cpspace_relation_def
                                  update_ep_map_tos typ_heap_simps')
            apply (erule(2) cpspace_relation_ep_update_ep)
             subgoal by (simp add: cendpoint_relation_def endpoint_state_defs)
            subgoal by simp
           apply (rule ceqv_refl)
          apply (simp only: ccorres_seq_skip)
          apply (rule ccorres_split_nothrow_novcg)
              apply (rule cancel_all_ccorres_helper)
             apply ceqv
            apply (ctac add: rescheduleRequired_ccorres)
           apply (wp weak_sch_act_wf_lift_linear
                  | simp)+
              apply (rule mapM_x_wp', wp)+
             apply (wp sts_st_tcb')
             apply (clarsimp split: if_split)
            apply (rule mapM_x_wp', wp sts_valid_objs')+
           apply (clarsimp simp: valid_tcb_state'_def)
          apply (simp add: guard_is_UNIV_def)
         apply (wp set_ep_valid_objs' hoare_vcg_const_Ball_lift
                   weak_sch_act_wf_lift_linear)
        apply vcg
       apply (simp add: ccorres_cond_iffs)
       apply (rule ccorres_return_Skip)
      apply (rename_tac list)
      apply (simp add: endpoint_state_defs Collect_False Collect_True ccorres_cond_iffs
                  del: Collect_const)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply (rule ccorres_abstract_cleanup)
      apply csymbr
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
      apply (rule_tac r'=dc and xf'=xfdc
                     in ccorres_split_nothrow)
          apply (rule_tac P="ko_at' (SendEP list) epptr and invs'"
                   in ccorres_from_vcg[where P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply clarsimp
          apply (rule cmap_relationE1 [OF cmap_relation_ep])
            apply assumption
           apply (erule ko_at_projectKO_opt)
          apply (clarsimp simp: typ_heap_simps setEndpoint_def)
          apply (rule rev_bexI)
           apply (rule setObject_eq, simp_all add: objBits_simps')[1]
          apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                carch_state_relation_def carch_globals_def
                                cmachine_state_relation_def
                                packed_heap_update_collapse_hrs)
          apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                update_ep_map_tos)
          apply (erule(2) cpspace_relation_ep_update_ep)
           subgoal by (simp add: cendpoint_relation_def endpoint_state_defs)
          subgoal by simp
         apply (rule ceqv_refl)
        apply (simp only: ccorres_seq_skip)
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule cancel_all_ccorres_helper)
           apply ceqv
          apply (ctac add: rescheduleRequired_ccorres)
         apply (wp mapM_x_wp' weak_sch_act_wf_lift_linear sts_valid_objs'
                   sts_st_tcb' | clarsimp simp: valid_tcb_state'_def split: if_split)+
        apply (simp add: guard_is_UNIV_def)
       apply (wp set_ep_valid_objs' hoare_vcg_const_Ball_lift
                 weak_sch_act_wf_lift_linear)
      apply vcg
     apply (clarsimp simp: valid_ep'_def invs_valid_objs')
     apply (rule cmap_relationE1[OF cmap_relation_ep], assumption)
      apply (erule ko_at_projectKO_opt)
     apply (frule obj_at_valid_objs', clarsimp+)
     apply (clarsimp simp: valid_obj'_def valid_ep'_def)
     apply (frule invs_pspace_aligned')
     apply (frule invs_pspace_distinct')
     apply (frule ksReadyQueues_asrt_ksReadyQueues_head_end)
     apply (frule (2) ksReadyQueues_asrt_ksReadyQueues_head_end_tcb_at')
     subgoal by (auto simp: typ_heap_simps cendpoint_relation_def
                       Let_def tcb_queue_relation'_def
                       invs_valid_objs' valid_objs'_maxDomain valid_objs'_maxPriority
               intro!: obj_at_conj')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (wp getEndpoint_wp)
  apply clarsimp
  done *)

lemma cancelAllSignals_ccorres:
  "ccorres dc xfdc
   invs' (UNIV \<inter> {s. ntfnPtr_' s = Ptr ntfnptr}) []
   (cancelAllSignals ntfnptr) (Call cancelAllSignals_'proc)"
  apply (cinit lift: ntfnPtr_')
sorry (* FIXME RT: cancelAllSignals_ccorres *) (*
   apply (rule ccorres_symb_exec_l [OF _ get_ntfn_inv' _ empty_fail_getNotification])
    apply (rule_tac xf'=ret__unsigned_longlong_'
                and val="case ntfnObj ntfn of IdleNtfn \<Rightarrow> scast NtfnState_Idle
                            | ActiveNtfn _ \<Rightarrow> scast NtfnState_Active | WaitingNtfn _ \<Rightarrow> scast NtfnState_Waiting"
                and R="ko_at' ntfn ntfnptr"
             in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply vcg
       apply clarsimp
       apply (erule cmap_relationE1 [OF cmap_relation_ntfn])
        apply (erule ko_at_projectKO_opt)
       apply (clarsimp simp add: typ_heap_simps)
       apply (simp add: cnotification_relation_def Let_def
                 split: ntfn.split_asm)
      apply ceqv
     apply (rule_tac A="invs' and ksReadyQueues_asrt and ko_at' ntfn ntfnptr"
              in ccorres_guard_imp2[where A'=UNIV])
      apply wpc
        apply (simp add: notification_state_defs ccorres_cond_iffs)
        apply (rule ccorres_return_Skip)
       apply (simp add: notification_state_defs ccorres_cond_iffs)
       apply (rule ccorres_return_Skip)
      apply (rename_tac list)
      apply (simp add: notification_state_defs ccorres_cond_iffs Collect_True
                  del: Collect_const)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply (rule ccorres_abstract_cleanup)
      apply csymbr
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
      apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
          apply (rule_tac P="ko_at' ntfn ntfnptr and invs'"
                   in ccorres_from_vcg[where P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply clarsimp
          apply (rule_tac x=ntfnptr in cmap_relationE1 [OF cmap_relation_ntfn], assumption)
           apply (erule ko_at_projectKO_opt)
          apply (clarsimp simp: typ_heap_simps setNotification_def)
          apply (rule rev_bexI)
           apply (rule setObject_eq, simp_all add: objBits_simps')[1]
          apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                carch_state_relation_def carch_globals_def
                                cmachine_state_relation_def
                                packed_heap_update_collapse_hrs)
          apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                update_ntfn_map_tos)
          apply (erule(2) cpspace_relation_ntfn_update_ntfn)
           subgoal by (simp add: cnotification_relation_def notification_state_defs Let_def)
          subgoal by simp
         apply (rule ceqv_refl)
        apply (simp only: ccorres_seq_skip)
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule cancel_all_ccorres_helper)
           apply ceqv
          apply (ctac add: rescheduleRequired_ccorres)
         apply (wp mapM_x_wp' weak_sch_act_wf_lift_linear sts_valid_objs'
                   sts_st_tcb' | clarsimp simp: valid_tcb_state'_def split: if_split)+
        apply (simp add: guard_is_UNIV_def)
       apply (wp set_ntfn_valid_objs' hoare_vcg_const_Ball_lift
                 weak_sch_act_wf_lift_linear)
      apply vcg
     apply clarsimp
     apply (rule cmap_relationE1[OF cmap_relation_ntfn], assumption)
      apply (erule ko_at_projectKO_opt)
     apply (frule obj_at_valid_objs', clarsimp+)
     apply (clarsimp simp add: valid_obj'_def valid_ntfn'_def)
     apply (frule invs_pspace_aligned')
     apply (frule invs_pspace_distinct')
     apply (frule ksReadyQueues_asrt_ksReadyQueues_head_end)
     apply (frule (2) ksReadyQueues_asrt_ksReadyQueues_head_end_tcb_at')
     subgoal by (auto simp: typ_heap_simps cnotification_relation_def
                       Let_def tcb_queue_relation'_def
                       invs_valid_objs' valid_objs'_maxDomain valid_objs'_maxPriority
               intro!: obj_at_conj')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (wp getNotification_wp)
  apply clarsimp
  done *)

lemma tcb_queue_concat:
  "tcb_queue_relation getNext getPrev mp (xs @ z # ys) qprev qhead
        \<Longrightarrow> tcb_queue_relation getNext getPrev mp (z # ys)
                (tcb_ptr_to_ctcb_ptr (last ((ctcb_ptr_to_tcb_ptr qprev) # xs))) (tcb_ptr_to_ctcb_ptr z)"
  apply (induct xs arbitrary: qprev qhead)
   apply clarsimp
  apply clarsimp
  apply (elim meta_allE, drule(1) meta_mp)
  apply (clarsimp cong: if_cong)
  done

lemma tcb_fields_ineq_helper:
  "\<lbrakk> tcb_at' (ctcb_ptr_to_tcb_ptr x) s; tcb_at' (ctcb_ptr_to_tcb_ptr y) s \<rbrakk> \<Longrightarrow>
     &(x\<rightarrow>[''tcbSchedPrev_C'']) \<noteq> &(y\<rightarrow>[''tcbSchedNext_C''])"
  apply (clarsimp dest!: tcb_aligned'[OF obj_at'_weakenE, OF _ TrueI]
                         ctcb_ptr_to_tcb_ptr_aligned)
  apply (clarsimp simp: field_lvalue_def ctcb_size_bits_def)
  apply (subgoal_tac "is_aligned (ptr_val y - ptr_val x) 9" (*ctcb_size_bits*))
   apply (drule sym, fastforce simp: is_aligned_def dvd_def)
  apply (erule(1) aligned_sub_aligned)
   apply (simp add: word_bits_conv)
  done

end

primrec
  tcb_queue_relation2 :: "(tcb_C \<Rightarrow> tcb_C ptr) \<Rightarrow> (tcb_C \<Rightarrow> tcb_C ptr)
                               \<Rightarrow> (tcb_C ptr \<rightharpoonup> tcb_C) \<Rightarrow> tcb_C ptr list
                               \<Rightarrow> tcb_C ptr \<Rightarrow> tcb_C ptr \<Rightarrow> bool"
where
  "tcb_queue_relation2 getNext getPrev hp [] before after = True"
| "tcb_queue_relation2 getNext getPrev hp (x # xs) before after =
   (\<exists>tcb. hp x = Some tcb \<and> getPrev tcb = before
      \<and> getNext tcb = hd (xs @ [after])
      \<and> tcb_queue_relation2 getNext getPrev hp xs x after)"

lemma use_tcb_queue_relation2:
  "tcb_queue_relation getNext getPrev hp xs qprev qhead
     = (tcb_queue_relation2 getNext getPrev hp
            (map tcb_ptr_to_ctcb_ptr xs) qprev (tcb_Ptr 0)
           \<and> qhead = (hd (map tcb_ptr_to_ctcb_ptr xs @ [tcb_Ptr 0])))"
  apply (induct xs arbitrary: qhead qprev)
   apply simp
  apply (simp add: conj_comms cong: conj_cong)
  done

lemma tcb_queue_relation2_concat:
  "tcb_queue_relation2 getNext getPrev hp
            (xs @ ys) before after
     = (tcb_queue_relation2 getNext getPrev hp
            xs before (hd (ys @ [after]))
         \<and> tcb_queue_relation2 getNext getPrev hp
              ys (last (before # xs)) after)"
  apply (induct xs arbitrary: before)
   apply simp
  apply (rename_tac x xs before)
  apply (simp split del: if_split)
  apply (case_tac "hp x")
   apply simp
  apply simp
  done

lemma tcb_queue_relation2_cong:
  "\<lbrakk>queue = queue'; before = before'; after = after';
   \<And>p. p \<in> set queue' \<Longrightarrow> mp p = mp' p\<rbrakk>
  \<Longrightarrow> tcb_queue_relation2 getNext getPrev mp queue before after =
     tcb_queue_relation2 getNext getPrev mp' queue' before' after'"
  using [[hypsubst_thin = true]]
  apply clarsimp
  apply (induct queue' arbitrary: before')
   apply simp+
  done

context kernel_m begin

lemma setThreadState_ccorres_simple:
  "ccorres dc xfdc
     (\<lambda>s. tcb_at' thread s \<and> sch_act_simple s \<and> no_0_obj' s
          \<and> weak_sch_act_wf (ksSchedulerAction s) s)
     (\<lbrace>\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := \<acute>ts && mask 4\<rparr>, fl)\<rbrace>
      \<inter> \<lbrace>\<acute>tptr = tcb_ptr_to_ctcb_ptr thread\<rbrace>) []
     (setThreadState st thread) (Call setThreadState_'proc)"
  apply (cinit lift: tptr_' cong add: call_ignore_cong)
   apply (ctac (no_vcg) add: threadSet_tcbState_simple_corres)
    apply (ctac add: scheduleTCB_ccorres_simple)
   apply (wpsimp wp: threadSet_valid_objs')
  apply clarsimp
  done

lemma updateRestartPC_ccorres:
  "ccorres dc xfdc (tcb_at' thread) \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr thread \<rbrace> hs
     (updateRestartPC thread) (Call updateRestartPC_'proc)"
  apply (cinit lift: tcb_')
   apply (subst asUser_bind_distrib; (wp add: empty_fail_getRegister)?)
   apply (ctac (no_vcg) add: getRegister_ccorres)
    apply (ctac (no_vcg) add: setRegister_ccorres)
   apply wpsimp+
   apply (simp add: RISCV64_H.faultRegister_def RISCV64_H.nextInstructionRegister_def
                    RISCV64.faultRegister_def RISCV64.nextInstructionRegister_def)
  done

crunch updateRestartPC
  for sch_act_simple[wp]: sch_act_simple
  and valid_objs'[wp]: valid_objs'
  and tcb_at'[wp]: "tcb_at' p"

crunch setReleaseQueue, getReleaseQueue
 for (empty_fail) empty_fail[wp]

lemma threadSet_tcbInReleaseQueue_ccorres[corres]:
  "ccorres dc xfdc
     (tcb_at' thread)
     {s. v64_' s = from_bool v
         \<and> thread_state_ptr_' s = Ptr &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C''])} []
     (threadSet (tcbInReleaseQueue_update (\<lambda>_. v)) thread)
     (Call thread_state_ptr_set_tcbInReleaseQueue_'proc)"
  apply (rule threadSet_corres_lemma)
     apply (rule thread_state_ptr_set_tcbInReleaseQueue_spec)
    apply (rule thread_state_ptr_set_tcbInReleaseQueue_modifies)
   apply clarsimp
   apply (frule (1) obj_at_cslift_tcb)
   apply clarsimp
   apply (rule rf_sr_tcb_update_no_queue_gen, assumption+, simp, simp_all)
   apply (rule ball_tcb_cte_casesI, simp_all)
   apply (simp add: ctcb_relation_def cthread_state_relation_def)
   apply (case_tac "tcbState ko"; simp)
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps)
  done

lemma tcbBoundYieldTo_caps_safe[simp]:
  "\<forall>(getF, setF)\<in>ran tcb_cte_cases.
     getF (tcbYieldTo_update f tcb) = getF tcb"
  by (case_tac tcb, simp add: tcb_cte_cases_def cteSizeBits_def)

lemma schedContext_cancelYieldTo_ccorres:
  "ccorres dc xfdc
     (tcb_at' tptr and no_0_obj')
     \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tptr\<rbrace> []
     (schedContextCancelYieldTo tptr) (Call schedContext_cancelYieldTo_'proc)"
  unfolding schedContextCancelYieldTo_def K_bind_apply
  apply (rule ccorres_symb_exec_l'[OF _ _ stateAssert_sp]; (solves wpsimp)?)
  apply (cinit' lift: tcb_')
   apply csymbr
   apply simp
   apply (rule ccorres_cond_true_seq)
   apply (rule ccorres_pre_gettcbYieldTo_P, rename_tac scPtrOpt)
   apply (rule ccorres_move_c_guard_tcb)
   apply (clarsimp simp: when_def)
   apply (rule_tac val="from_bool (\<exists>y. scPtrOpt = Some y)"
               and R="obj_at' (\<lambda>tcb. tcbYieldTo tcb = scPtrOpt) tptr and no_0_obj' and valid_objs'"
               and R'=UNIV
               and xf'=ret__int_'
                in ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg)
      apply normalise_obj_at'
      apply (frule (1) obj_at_cslift_tcb)
      apply (clarsimp simp: typ_heap_simps ctcb_relation_def split: if_splits)
      apply (rule conjI)
       using option_to_ptr_not_0 subgoal by force
      apply (fastforce dest: tcb_ko_at_valid_objs_valid_tcb'
                       simp: valid_tcb'_def from_bool_0 option_to_ptr_NULL_eq)
     apply ceqv
    apply ccorres_rewrite
    apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top> and U=\<top> and U'=UNIV])
      apply (clarsimp split: if_splits)
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_move_c_guard_tcb)
     apply (rule ccorres_split_nothrow)
         apply (rule_tac P=\<top>
                     and P'="obj_at' (\<lambda>tcb. tcbYieldTo tcb = scPtrOpt) tptr
                             and valid_bound_sc' scPtrOpt"
                     and Q="\<lambda>s sc. {s'. (s, s') \<in> rf_sr
                                        \<and> (bound scPtrOpt \<longrightarrow> ko_at' sc (the scPtrOpt) s)
                                        \<and> obj_at' (\<lambda>tcb. tcbYieldTo tcb = scPtrOpt) tptr s}"
                      in updateSchedContext_ccorres_lemma3;
                fastforce?)
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (rename_tac yield_sc)
         apply (frule_tac thread=tptr in obj_at_cslift_tcb[rotated, where P=\<top>])
          apply clarsimp
         apply normalise_obj_at'
         apply (rename_tac tcb')
         apply (frule (1) obj_at_cslift_sc)
         apply (prop_tac "tcbYieldTo_C tcb' = Ptr yield_sc")
          apply (clarsimp simp: obj_at_simps ctcb_relation_def)
         apply clarsimp
         apply (rule rf_sr_sc_update_no_refill_buffer_update2; fastforce?)
           apply (simp add: typ_heap_simps')
          apply (clarsimp simp: csched_context_relation_def Let_def option_to_ctcb_ptr_def
                         split: if_splits)
         apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
        apply ceqv
       apply (rule ccorres_move_c_guard_tcb)
       apply (rule_tac Q="\<lambda>s tcb. {s'. (s,s') \<in> rf_sr \<and> ko_at' tcb tptr s}"
                   and P=\<top> and R=UNIV
                    in threadSet_ccorres_lemma4)
        apply (rule conseqPre, vcg)
        apply clarsimp
        apply (frule_tac thread=tptr in obj_at_cslift_tcb[rotated, where P=\<top>])
        apply normalise_obj_at'
        apply (rule rf_sr_tcb_update_no_queue2, (simp add: typ_heap_simps' ctcb_relation_def)+)
       apply clarsimp
      apply wpsimp
     apply (rule conseqPre, vcg)
     apply (clarsimp simp: typ_heap_simps')
    apply (rule ccorres_return_Skip)
   apply vcg
  apply (clarsimp simp: typ_heap_simps)
  apply normalise_obj_at'
  apply (frule (1) obj_at_cslift_tcb)
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (intro conjI impI allI)
      apply (clarsimp simp: valid_tcb'_def)
     apply (clarsimp simp: valid_bound_obj'_def valid_tcb'_def)
    apply force
   apply (clarsimp simp: h_t_valid_clift_Some_iff ctcb_relation_def)
   apply (frule (1) obj_at_cslift_sc)
   apply force
  apply (fastforce dest: typ_heap_simps' split: if_splits)
  done

lemma active_runnable':
  "active' state \<Longrightarrow> runnable' state"
  by fastforce

crunch updateRestartPC
  for no_0_obj'[wp]: no_0_obj'
  and weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps)

lemma suspend_ccorres:
  assumes cteDeleteOne_ccorres:
  "\<And>w slot.
   ccorres dc xfdc
     (invs'
      and cte_wp_at' (\<lambda>ct. w = -1 \<or> cteCap ct = NullCap
          \<or> (\<forall>cap'. ccap_relation (cteCap ct) cap' \<longrightarrow> cap_get_tag cap' = w)) slot)
     ({s. gs_get_assn cteDeleteOne_'proc (ghost'state_' (globals s)) = w}
        \<inter> {s. slot_' s = Ptr slot}) []
   (cteDeleteOne slot) (Call cteDeleteOne_'proc)"
  shows
  "ccorres dc xfdc
     (invs' and sch_act_simple and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and tcb_at' thread
      and (\<lambda>s. thread \<noteq> ksIdleThread s))
     \<lbrace>\<acute>target = tcb_ptr_to_ctcb_ptr thread\<rbrace> []
     (suspend thread) (Call suspend_'proc)"
  apply (cinit lift: target_')
   apply (rule ccorres_stateAssert)
   apply (ctac(no_vcg) add: cancelIPC_ccorres1 [OF cteDeleteOne_ccorres])
    apply (rule getThreadState_ccorres_foo)
    apply (rename_tac threadState)
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule_tac xf'=ret__unsigned_longlong_'
            and val="thread_state_to_tsType threadState"
            and R="st_tcb_at' ((=) threadState) thread"
            and R'=UNIV
            in
            ccorres_symb_exec_r_known_rv)
       apply clarsimp
       apply (rule conseqPre, vcg)
       apply (clarsimp simp: st_tcb_at'_def)
       apply (frule (1) obj_at_cslift_tcb)
       apply (clarsimp simp: typ_heap_simps ctcb_relation_thread_state_to_tsType)
      apply ceqv
     supply Collect_const[simp del]
     apply (rule ccorres_split_nothrow)
         apply (rule ccorres_cond[where R=\<top> and xf=xfdc])
           apply clarsimp
           apply (rule iffI)
            apply simp
           apply (erule thread_state_to_tsType.elims; simp add: ThreadState_defs)
          apply (ctac (no_vcg) add: updateRestartPC_ccorres)
         apply (rule ccorres_return_Skip)
        apply ceqv
       apply (ctac(no_vcg) add: setThreadState_ccorres_simple)
        apply (ctac (no_vcg) add: tcbSchedDequeue_ccorres)
         apply (ctac (no_vcg) add: tcbReleaseRemove_ccorres)
          apply (ctac (no_vcg) add: schedContext_cancelYieldTo_ccorres)
         apply (wpsimp wp: tcbReleaseRemove_invs')+
     apply (rule conseqPre, vcg exspec=updateRestartPC_modifies)
     apply (rule subset_refl)
    apply clarsimp
    apply (rule conseqPre, vcg)
    apply (rule subset_refl)
   apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> tcb_at' thread s \<and> sch_act_simple s
                            \<and> weak_sch_act_wf (ksSchedulerAction s) s" in hoare_post_imp)
    apply fastforce
   apply (wpsimp wp: hoare_vcg_all_lift)
  apply (auto simp: ThreadState_defs)
  done

lemma cap_to_H_NTFNCap_tag:
  "\<lbrakk> cap_to_H cap = NotificationCap word1 word2 a b;
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_notification_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     by (simp_all add: Let_def cap_lift_def split: if_splits)

lemmas ccorres_pre_getBoundNotification = ccorres_pre_threadGet [where f=tcbBoundNotification, folded getBoundNotification_def]

lemma option_to_ptr_not_NULL:
  "option_to_ptr x \<noteq> NULL \<Longrightarrow> x \<noteq> None"
  by (auto simp: option_to_ptr_def option_to_0_def split: option.splits)

lemma doUnbindNotification_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. sym_refs (state_refs_of' s)) and tcb_at' tcb)
    (UNIV \<inter> {s. ntfnPtr_' s = ntfn_Ptr ntfnptr} \<inter> {s. tcbptr_' s = tcb_ptr_to_ctcb_ptr tcb}) []
   (do ntfn \<leftarrow> getNotification ntfnptr; doUnbindNotification ntfnptr ntfn tcb od)
   (Call doUnbindNotification_'proc)"
  apply (cinit' lift: ntfnPtr_' tcbptr_')
   apply (rule ccorres_symb_exec_l [OF _ get_ntfn_inv' _ empty_fail_getNotification])
    apply (rule_tac P="invs' and (\<lambda>s. sym_refs (state_refs_of' s)) and ko_at' ntfn ntfnptr" and P'=UNIV
             in ccorres_split_nothrow_novcg)
        apply (rule ccorres_from_vcg[where rrel=dc and xf=xfdc])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: option_to_ptr_def option_to_0_def)
        apply (frule cmap_relation_ntfn)
        apply (erule (1) cmap_relation_ko_atE)
        apply (rule conjI)
         apply (erule h_t_valid_clift)
        apply (clarsimp simp: setNotification_def split_def)
        apply (rule bexI [OF _ setObject_eq])
            apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                             typ_heap_simps'
                             cpspace_relation_def update_ntfn_map_tos)
            apply (elim conjE)
            apply (intro conjI)
            \<comment> \<open>tcb relation\<close>
              apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
               apply (clarsimp simp: cnotification_relation_def Let_def
                                     mask_def [where n=2] NtfnState_Waiting_def)
               apply (case_tac "ntfnObj ntfn", ((simp add: option_to_ctcb_ptr_def)+)[4])
              apply (simp add: refill_buffer_relation_def image_def dom_def Let_def typ_heap_simps
                               update_ntfn_map_tos)
             subgoal by (simp add: carch_state_relation_def)
            subgoal by (simp add: cmachine_state_relation_def)
           subgoal by (simp add: h_t_valid_clift_Some_iff)
          subgoal by (simp add: objBits_simps')
         subgoal by (simp add: objBits_simps)
        apply assumption
       apply ceqv
      apply (rule ccorres_move_c_guard_tcb)
      apply (simp add: setBoundNotification_def)
      apply (rule_tac P'="\<top>" and P="\<top>"
                   in threadSet_ccorres_lemma3)
       apply vcg
      apply simp
      apply (erule(1) rf_sr_tcb_update_no_queue2)
              apply (simp add: typ_heap_simps')+
       apply (simp add: tcb_cte_cases_def cteSizeBits_def)
      apply (simp add: ctcb_relation_def option_to_ptr_def option_to_0_def)
     apply (simp add: invs'_def)
     apply (wp get_ntfn_ko' | simp add: guard_is_UNIV_def)+
  done

lemma doUnbindNotification_ccorres':
  "ccorres dc xfdc (invs' and (\<lambda>s. sym_refs (state_refs_of' s)) and tcb_at' tcb and ko_at' ntfn ntfnptr)
    (UNIV \<inter> {s. ntfnPtr_' s = ntfn_Ptr ntfnptr} \<inter> {s. tcbptr_' s = tcb_ptr_to_ctcb_ptr tcb}) []
   (doUnbindNotification ntfnptr ntfn tcb)
   (Call doUnbindNotification_'proc)"
  apply (cinit' lift: ntfnPtr_' tcbptr_')
    apply (rule_tac P="invs' and (\<lambda>s. sym_refs (state_refs_of' s)) and ko_at' ntfn ntfnptr" and P'=UNIV
                in ccorres_split_nothrow_novcg)
        apply (rule ccorres_from_vcg[where rrel=dc and xf=xfdc])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: option_to_ptr_def option_to_0_def)
        apply (frule cmap_relation_ntfn)
        apply (erule (1) cmap_relation_ko_atE)
        apply (rule conjI)
        apply (erule h_t_valid_clift)
       apply (clarsimp simp: setNotification_def split_def)
       apply (rule bexI [OF _ setObject_eq])
           apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                            typ_heap_simps'
                            cpspace_relation_def update_ntfn_map_tos)
           apply (elim conjE)
           apply (intro conjI)
             apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
              apply (clarsimp simp: cnotification_relation_def Let_def
                                    mask_def [where n=2] NtfnState_Waiting_def)
              apply (fold_subgoals (prefix))[2]
              subgoal premises prems using prems
                      by (case_tac "ntfnObj ntfn", (simp add: option_to_ctcb_ptr_def)+)
             apply (simp add: refill_buffer_relation_def image_def dom_def Let_def typ_heap_simps
                              update_ntfn_map_tos)
            subgoal by (simp add: carch_state_relation_def)
           subgoal by (simp add: cmachine_state_relation_def)
          subgoal by (simp add: h_t_valid_clift_Some_iff)
         subgoal by (simp add: objBits_simps')
        subgoal by (simp add: objBits_simps)
       apply assumption
      apply ceqv
     apply (rule ccorres_move_c_guard_tcb)
     apply (simp add: setBoundNotification_def)
     apply (rule_tac P'="\<top>" and P="\<top>"
                  in threadSet_ccorres_lemma3)
      apply vcg
     apply simp
     apply (erule(1) rf_sr_tcb_update_no_queue2)
             apply (simp add: typ_heap_simps')+
       apply (simp add: tcb_cte_cases_def cteSizeBits_def)
     apply (simp add: ctcb_relation_def option_to_ptr_def option_to_0_def)
    apply (simp add: invs'_def)
    apply (wp get_ntfn_ko' | simp add: guard_is_UNIV_def)+
  done


lemma unbindNotification_ccorres:
  "ccorres dc xfdc
    (invs' and (\<lambda>s. sym_refs (state_refs_of' s))) (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr tcb}) []
    (unbindNotification tcb) (Call unbindNotification_'proc)"
  supply option.case_cong[cong]
  apply (cinit lift: tcb_')
   apply (rule_tac xf'=ntfnPtr_'
                    and r'="\<lambda>rv rv'. rv' = option_to_ptr rv \<and> rv \<noteq> Some 0"
                    in ccorres_split_nothrow)
       apply (simp add: getBoundNotification_def)
       apply (rule_tac P="no_0_obj' and valid_objs'" in threadGet_vcg_corres_P)
       apply (rule allI, rule conseqPre, vcg)
       apply clarsimp
       apply (drule obj_at_ko_at', clarsimp)
       apply (drule spec, drule(1) mp, clarsimp)
       apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
       apply (drule(1) ko_at_valid_objs', simp)
       apply (clarsimp simp: option_to_ptr_def option_to_0_def valid_obj'_def valid_tcb'_def)
      apply ceqv
     apply simp
     apply wpc
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip)
     apply (rule ccorres_cond_true)
     apply (ctac (no_vcg) add: doUnbindNotification_ccorres[simplified])
    apply (wp gbn_wp')
   apply vcg
  apply (clarsimp simp: option_to_ptr_def option_to_0_def pred_tcb_at'_def
                        obj_at'_weakenE[OF _ TrueI]
                 split: option.splits)
  apply (clarsimp simp: invs'_def valid_pspace'_def)
  done


lemma unbindMaybeNotification_ccorres:
  "ccorres dc xfdc
     (invs' and (\<lambda>s. sym_refs (state_refs_of' s))) (UNIV \<inter> {s. ntfnPtr_' s = ntfn_Ptr ntfnptr}) []
     (unbindMaybeNotification ntfnptr) (Call unbindMaybeNotification_'proc)"
  supply option.case_cong[cong]
  apply (cinit lift: ntfnPtr_')
   apply (rule ccorres_symb_exec_l [OF _ get_ntfn_inv' _ empty_fail_getNotification])
    apply (rule ccorres_rhs_assoc2)
    apply (rule_tac P="ntfnBoundTCB ntfn \<noteq> None \<longrightarrow>
                         option_to_ctcb_ptr (ntfnBoundTCB ntfn) \<noteq> NULL"
             in ccorres_gen_asm)
    apply (rule_tac xf'=boundTCB_'
                and val="option_to_ctcb_ptr (ntfnBoundTCB ntfn)"
                and R="ko_at' ntfn ntfnptr and valid_bound_tcb' (ntfnBoundTCB ntfn)"
             in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply vcg
       apply clarsimp
       apply (erule cmap_relationE1[OF cmap_relation_ntfn])
        apply (erule ko_at_projectKO_opt)
       apply (clarsimp simp: typ_heap_simps cnotification_relation_def Let_def)
      apply ceqv
     apply wpc
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip)
     apply (rule ccorres_cond_true)
     apply (rule ccorres_call[where xf'=xfdc])
        apply (rule doUnbindNotification_ccorres'[simplified])
       apply simp
      apply simp
     apply simp
    apply (clarsimp simp add: guard_is_UNIV_def option_to_ctcb_ptr_def )
   apply (wp getNotification_wp)
  apply clarsimp
  apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn'[OF _ invs_valid_objs'])
  by (auto simp: valid_ntfn'_def valid_bound_tcb'_def obj_at'_def
                 objBitsKO_def is_aligned_def option_to_ctcb_ptr_def tcb_at_not_NULL
          split: ntfn.splits)

(* TODO: move *)
definition
  irq_opt_relation_def:
  "irq_opt_relation (airq :: (6 word) option) (cirq :: machine_word) \<equiv>
       case airq of
         Some irq \<Rightarrow> (cirq = ucast irq \<and>
                      irq \<noteq> ucast irqInvalid \<and>
                      ucast irq \<le> UCAST(32 signed \<rightarrow> 6) Kernel_C.maxIRQ)
       | None \<Rightarrow> cirq = ucast irqInvalid"

lemma finaliseCap_True_cases_ccorres:
  "\<And>final. isEndpointCap cap \<or> isNotificationCap cap
             \<or> isReplyCap cap \<or> isDomainCap cap \<or> cap = NullCap \<Longrightarrow>
   ccorres (\<lambda>rv rv'. ccap_relation (fst rv) (finaliseCap_ret_C.remainder_C rv')
                   \<and> ccap_relation (snd rv) (finaliseCap_ret_C.cleanupInfo_C rv'))
   ret__struct_finaliseCap_ret_C_'
   (invs') (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. final_' s = from_bool final}
                        \<inter> {s. exposed_' s = from_bool flag \<comment> \<open>dave has name wrong\<close>}) []
   (finaliseCap cap final flag) (Call finaliseCap_'proc)"
  apply (subgoal_tac "\<not> isArchCap \<top> cap")
   prefer 2
   apply (clarsimp simp: isCap_simps)
  apply (cinit lift: cap_' final_' exposed_' cong: call_ignore_cong)
   apply csymbr
   apply (simp add: cap_get_tag_isCap Collect_False del: Collect_const)
   apply (fold case_bool_If)
   apply simp
   apply csymbr
   apply wpc
    apply (simp add: cap_get_tag_isCap ccorres_cond_univ_iff Let_def)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_split_nothrow_novcg)
        apply (simp add: when_def)
        apply (rule ccorres_cond2)
          apply (clarsimp simp: Collect_const_mem from_bool_0)
         apply csymbr
sorry (* FIXME RT: finaliseCap_True_cases_ccorres *) (*
         apply (rule ccorres_call[where xf'=xfdc], rule cancelAllIPC_ccorres)
           apply simp
          apply simp
         apply simp
        apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
        apply (simp add: return_def, vcg)
       apply (rule ceqv_refl)
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_split_throws)
       apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp add: return_def ccap_relation_NullCap_iff
                                 irq_opt_relation_def)
      apply vcg
     apply wp
    apply (simp add: guard_is_UNIV_def)
   apply wpc
    apply (simp add: cap_get_tag_isCap Let_def
                     ccorres_cond_empty_iff ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_split_nothrow_novcg)
        apply (simp add: when_def)
        apply (rule ccorres_cond2)
          apply (clarsimp simp: Collect_const_mem from_bool_0)
          apply (subgoal_tac "cap_get_tag capa = scast cap_notification_cap") prefer 2
          apply (clarsimp simp: ccap_relation_def isNotificationCap_def)
          apply (case_tac cap, simp_all)[1]
          apply (clarsimp simp: option_map_def split: option.splits)
          apply (drule (2) cap_to_H_NTFNCap_tag[OF sym])
         apply (rule ccorres_rhs_assoc)
         apply (rule ccorres_rhs_assoc)
         apply csymbr
         apply csymbr
         apply (ctac (no_vcg) add: unbindMaybeNotification_ccorres)
          apply (rule ccorres_call[where xf'=xfdc], rule cancelAllSignals_ccorres)
            apply simp
           apply simp
          apply simp
         apply (wp | wpc | simp add: guard_is_UNIV_def)+
        apply (rule ccorres_return_Skip')
       apply (rule ceqv_refl)
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_split_throws)
       apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp add: return_def ccap_relation_NullCap_iff
                                 irq_opt_relation_def)
      apply vcg
     apply wp
    apply (simp add: guard_is_UNIV_def)
   apply wpc
    apply (simp add: cap_get_tag_isCap Let_def
                     ccorres_cond_empty_iff ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_split_throws)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp add: return_def ccap_relation_NullCap_iff
                               irq_opt_relation_def)
    apply vcg
   apply wpc
    apply (simp add: cap_get_tag_isCap Let_def
                     ccorres_cond_empty_iff ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_split_throws)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp add: return_def ccap_relation_NullCap_iff)
     apply (clarsimp simp add: irq_opt_relation_def)
    apply vcg
   \<comment> \<open>NullCap case by exhaustion\<close>
   apply (simp add: cap_get_tag_isCap Let_def
                    ccorres_cond_empty_iff ccorres_cond_univ_iff)
   apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
          rule ccorres_split_throws)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp add: return_def ccap_relation_NullCap_iff
                              irq_opt_relation_def)
   apply vcg
  apply (clarsimp simp: Collect_const_mem cap_get_tag_isCap)
  apply (rule TrueI conjI impI TrueI)+
   apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def isNotificationCap_def
                         isEndpointCap_def valid_obj'_def valid_ntfn'_def valid_bound_tcb'_def
                  dest!: obj_at_valid_objs')
  apply clarsimp
  apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
  apply clarsimp
  done *)

lemma finaliseCap_True_standin_ccorres:
  "\<And>final.
   ccorres (\<lambda>rv rv'. ccap_relation (fst rv) (finaliseCap_ret_C.remainder_C rv')
                   \<and> ccap_relation (snd rv) (finaliseCap_ret_C.cleanupInfo_C rv'))
   ret__struct_finaliseCap_ret_C_'
   (invs') (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. final_' s = from_bool final}
                        \<inter> {s. exposed_' s = from_bool True \<comment> \<open>dave has name wrong\<close>}) []
   (finaliseCapTrue_standin cap final) (Call finaliseCap_'proc)"
  unfolding finaliseCapTrue_standin_simple_def
  apply (case_tac "P :: bool" for P)
   apply (erule finaliseCap_True_cases_ccorres)
  apply (simp add: finaliseCap_def ccorres_fail')
  done

lemma offset_xf_for_sequence:
  "\<forall>s f. offset_' (offset_'_update f s) = f (offset_' s)
          \<and> globals (offset_'_update f s) = globals s"
  by simp

lemma deleteASIDPool_ccorres:
  "ccorres dc xfdc (invs' and cur_tcb' and (\<lambda>_. asid_wf base \<and> pool \<noteq> 0))
      (UNIV \<inter> {s. asid_base_' s = base} \<inter> {s. pool_' s = Ptr pool}) []
      (deleteASIDPool base pool) (Call deleteASIDPool_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_base_' pool_' simp: whileAnno_def)
   apply (rule ccorres_assert)
   apply (clarsimp simp: liftM_def when_def)
   apply (rule ccorres_Guard)+
   apply (rule ccorres_pre_gets_riscvKSASIDTable_ksArchState)
   apply (rule_tac R="\<lambda>s. rv = riscvKSASIDTable (ksArchState s)" in ccorres_cond2)
     apply clarsimp
     apply (subst rf_sr_riscvKSASIDTable, assumption)
      apply (simp add: asid_high_bits_word_bits asid_wf_def mask_def)
      apply (rule shiftr_less_t2n)
      apply (simp add: asid_low_bits_def asid_high_bits_def asid_bits_def)
     apply (subst ucast_asid_high_bits_is_shift, assumption)
     apply (simp add: option_to_ptr_def option_to_0_def split: option.split)
    apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+
    apply (rule ccorres_pre_getObject_asidpool)
    apply (rename_tac poolKO)
    apply (rule ccorres_split_nothrow_novcg_dc)
       apply (rule_tac P="\<lambda>s. rv = riscvKSASIDTable (ksArchState s)"
                    in ccorres_from_vcg[where P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: simpler_modify_def)
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def ucast_asid_high_bits_is_shift
                             carch_state_relation_def cmachine_state_relation_def
                             carch_globals_def h_t_valid_clift_Some_iff riscvKSGlobalPT_def)
       apply (erule array_relation_update[unfolded fun_upd_def], rule refl)
        subgoal by (simp add: option_to_ptr_def option_to_0_def)
       subgoal by (simp add: asid_high_bits_def)
      apply (rule ccorres_pre_getCurThread)
      apply (ctac add: setVMRoot_ccorres)
     apply wp
    apply (simp add: guard_is_UNIV_def)
   apply (rule ccorres_return_Skip)
  apply (clarsimp simp: asid_wf_table_guard simp flip: fun_upd_def)
  apply (strengthen invs_asid_update_strg')
  apply (auto simp: cur_tcb'_def)
  done

lemma deleteASID_ccorres:
  "ccorres dc xfdc (invs' and cur_tcb' and K (asid_wf asid \<and> vs \<noteq> 0))
      ({s. asid___unsigned_long_' s = asid} \<inter> {s. vspace_' s = Ptr vs}) []
      (deleteASID asid vs) (Call deleteASID_'proc)"
  apply (cinit lift: asid___unsigned_long_' vspace_' cong: call_ignore_cong)
   apply (rule ccorres_Guard_Seq)+
   apply (rule_tac r'="\<lambda>rv rv'. case rv (ucast (asid_high_bits_of (ucast asid))) of
                                None \<Rightarrow> rv' = NULL
                              | Some v \<Rightarrow> rv' = Ptr v \<and> rv' \<noteq> NULL"
               and xf'="poolPtr_'" in ccorres_split_nothrow)
       apply (rule_tac P="invs' and cur_tcb' and K (asid_wf asid)"
                   and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: simpler_gets_def Let_def ucast_asid_high_bits_is_shift)
       apply (erule(1) getKSASIDTable_ccorres_stuff, rule refl)
       apply (simp add: asid_wf_table_guard asid_high_bits_def)
      apply ceqv
     apply wpc
      apply simp
      apply (rule ccorres_from_vcg[where P="\<top>" and P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (simp add: return_def)
     apply (clarsimp simp: when_def liftM_def
                     cong: conj_cong call_ignore_cong)
     apply (rename_tac asidTable ap)
     apply csymbr
     apply ccorres_rewrite
     apply (rule ccorres_pre_getObject_asidpool)
     apply (rule ccorres_move_c_guard_ap)
     apply (rename_tac pool)
     apply (rule_tac xf'=ret__int_'
                 and val="from_bool (inv ASIDPool pool (asid && mask asid_low_bits) = Some vs)"
                   and R="ko_at' pool ap and K (vs \<noteq> 0)"
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
        apply (vcg, clarsimp)
        apply (clarsimp dest!: rf_sr_cpspace_asidpool_relation)
        apply (erule(1) cmap_relation_ko_atE)
        apply (clarsimp simp: typ_heap_simps casid_pool_relation_def
                              array_relation_def asid_low_bits_of_mask_eq
                        simp flip: mask_2pm1
                       split: asidpool.split_asm asid_pool_C.split_asm)
        apply (drule_tac x="asid && mask asid_low_bits" in spec)
        apply (clarsimp simp: word_and_le1 case_bool_If inv_ASIDPool)
        apply (fastforce simp: option_to_ptr_def option_to_0_def split: if_splits option.splits)
       apply ceqv
      apply (rule ccorres_cond2[where R=\<top>])
        apply (simp add: Collect_const_mem from_bool_0)
       apply (rule ccorres_rhs_assoc)+
        apply (ctac (no_vcg) add: hwASIDFlush_ccorres)
         apply (rule ccorres_move_c_guard_ap)
         apply (rule ccorres_split_nothrow_novcg_dc)
            apply (rule_tac P="ko_at' pool ap" in ccorres_from_vcg[where P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply clarsimp
            apply (rule cmap_relationE1[OF rf_sr_cpspace_asidpool_relation],
                   assumption, erule ko_at_projectKO_opt)
            apply (rule bexI [OF _ setObject_eq],
                   simp_all add: objBits_simps pageBits_def)[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps)
            apply (rule conjI)
             apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                   update_asidpool_map_tos
                                   update_asidpool_map_to_asidpools)
             apply (rule cmap_relation_updI, simp_all)[1]
             apply (clarsimp simp: casid_pool_relation_def fun_upd_def[symmetric]
                                   inv_ASIDPool
                             split: asidpool.split_asm asid_pool_C.split_asm)
             apply (rule conjI, erule array_relation_update)
                subgoal by (simp add: mask_def asid_low_bits_of_mask_eq)
               subgoal by (clarsimp)
              subgoal by (simp add: asid_low_bits_def)
             subgoal by (blast intro!: not_in_ran_None_upd)
            subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                                  carch_globals_def update_asidpool_map_tos
                                  refill_buffer_relation_def typ_heap_simps)
           apply (rule ccorres_pre_getCurThread)
           apply (ctac add: setVMRoot_ccorres)
          apply (simp add: cur_tcb'_def[symmetric])
          apply wp
         apply (clarsimp simp: rf_sr_def guard_is_UNIV_def
                               cstate_relation_def Let_def)
        apply wp
      apply (rule ccorres_return_Skip)
     apply (solves \<open>clarsimp simp: Collect_const_mem guard_is_UNIV_def\<close>)
    apply wp
   apply vcg
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule obj_at_valid_objs'; clarsimp)
   apply (clarsimp simp: typ_at_to_obj_at_arches obj_at'_weakenE[OF _ TrueI])
  apply (simp add: asid_wf_table_guard)
  done

lemma setObject_ccorres_lemma:
  fixes val :: "'a :: pspace_storable" shows
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> (Q s) c {s'. (s \<lparr> ksPSpace := (ksPSpace s)(ptr \<mapsto> injectKO val) \<rparr>, s') \<in> rf_sr},{};
     \<And>s s' val'::'a. \<lbrakk> ko_at' val' ptr s; (s, s') \<in> rf_sr \<rbrakk>
           \<Longrightarrow> s' \<in> Q s;
     \<And>val :: 'a. updateObject val = updateObject_default val;
     \<And>val :: 'a. (1 :: machine_word) < 2 ^ objBits val;
     \<And>(val :: 'a) (val' :: 'a). objBits val = objBits val';
     \<Gamma> \<turnstile> Q' c UNIV \<rbrakk>
    \<Longrightarrow> ccorres dc xfdc \<top> Q' hs
             (setObject ptr val) c"
  apply (rule ccorres_from_vcg_nofail)
  apply (rule allI)
  apply (case_tac "obj_at' (\<lambda>x :: 'a. True) ptr \<sigma>")
   apply (rule_tac P'="Q \<sigma>" in conseqPre, rule conseqPost, assumption)
     apply clarsimp
     apply (rule bexI [OF _ setObject_eq], simp+)
   apply (drule obj_at_ko_at')
   apply clarsimp
  apply clarsimp
  apply (rule conseqPre, erule conseqPost)
    apply clarsimp
    apply (subgoal_tac "fst (setObject ptr val \<sigma>) = {}")
     apply simp
     apply (erule notE, erule_tac s=\<sigma> in empty_failD[rotated])
     apply (simp add: setObject_def split_def empty_fail_cond)
    apply (rule ccontr)
    apply (clarsimp elim!: nonemptyE)
    apply (frule use_valid [OF _ obj_at_setObject3[where P=\<top>]], simp_all)[1]
    apply (simp add: typ_at_to_obj_at'[symmetric])
    apply (frule(1) use_valid [OF _ setObject_typ_at'])
    apply simp
   apply simp
  apply clarsimp
  done

lemma findVSpaceForASID_nonzero:
  "\<lbrace>\<top>\<rbrace> findVSpaceForASID asid \<lbrace>\<lambda>rv s. rv \<noteq> 0\<rbrace>,-"
  apply (simp add: findVSpaceForASID_def cong: option.case_cong)
  apply (wp | wpc | simp only: o_def simp_thms)+
  done

lemma ccorres_ul_pre_getObject_pte:
  assumes cc: "\<And>rv. ccorres_underlying rf_sr \<Gamma> (inr_rrel r') xf' (inl_rel r) xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres_underlying rf_sr \<Gamma> (inr_rrel r') xf' (inl_rel r) xf
                  (\<lambda>s. (\<forall>pte. ko_at' pte p s \<longrightarrow> P pte s))
                  {s. \<forall>pte pte'. cslift s (pte_Ptr p) = Some pte' \<and> cpte_relation pte pte'
                           \<longrightarrow> s \<in> P' pte}
                          hs (getObject p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wp getPTE_wp empty_fail_getObject | simp)+
  apply clarsimp
  apply (erule cmap_relationE1 [OF rf_sr_cpte_relation],
         erule ko_at_projectKO_opt)
  apply simp
  done

lemma lookupPTFromLevel_ccorres:
  notes Collect_const[simp del] call_ignore_cong[cong]
  defines "idx i \<equiv> 0x1E - 9 * i"
  defines "vshift vaddr i \<equiv> (vaddr >> unat (idx i)) && 0x1FF"
  defines "maxPT \<equiv> 2"
  assumes max: "level \<le> maxPTLevel"
  shows
    "ccorres_underlying rf_sr \<Gamma>
      (inr_rrel (\<lambda>ptSlot ptSlot_C. ptSlot_C = pte_Ptr ptSlot)) ptSlot_' (inl_rrel dc) xfdc
      (page_table_at' pt)
      (\<lbrace>\<acute>i = of_nat (maxPTLevel - level)\<rbrace> \<inter> \<lbrace>\<acute>pt = pte_Ptr pt\<rbrace>)
      [SKIP]
      (lookupPTFromLevel level pt vaddr target_pt)
      (      WHILE \<acute>i < maxPT \<and> \<acute>pt \<noteq> pte_Ptr target_pt DO
               Guard ShiftError \<lbrace>idx \<acute>i < 0x40\<rbrace>
                (Guard MemorySafety
                  \<lbrace>vshift vaddr \<acute>i = 0 \<or>
                   array_assertion \<acute>pt (unat (vshift vaddr \<acute>i)) (hrs_htd \<acute>t_hrs)\<rbrace>
                  (\<acute>ptSlot :== \<acute>pt +\<^sub>p uint (vshift vaddr \<acute>i)));;
               \<acute>ret__unsigned_long :== CALL isPTEPageTable(\<acute>ptSlot);;
               IF \<acute>ret__unsigned_long = 0 THEN
                 return_void_C
               FI;;
               \<acute>pt :== CALL getPPtrFromHWPTE(\<acute>ptSlot);;
               \<acute>i :== \<acute>i + 1
             OD;;
             IF \<acute>pt \<noteq> pte_Ptr target_pt THEN
               return_void_C
             FI)"
using max
proof (induct level arbitrary: pt)
  case 0
  show ?case
    apply (subst lookupPTFromLevel.simps)
    apply (simp add: 0 whileAnno_def maxPT_def maxPTLevel_def)
    apply (rule ccorres_assertE)
    apply (rule ccorres_expand_while_iff_Seq[THEN iffD1])
    apply (subst Int_commute)
    apply (cinitlift i_')
    apply (simp add: throwError_def)
    apply ccorres_rewrite
    apply (cinitlift pt_')
    apply (rule ccorres_guard_imp)
      apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
      apply (simp add: return_def)
      apply (rule allI, rule conseqPre, vcg)
      apply clarsimp
     apply simp
    apply simp
    done
next
  have [simp]: "of_nat maxPTLevel = maxPT"
    by (simp add: maxPTLevel_def maxPT_def)

  case (Suc level)
  then
  have level: "level < maxPTLevel" by simp
  then
  have [simp]: "maxPT - (1 + of_nat level) < maxPT" (is "?i < maxPT")
    by (simp add: maxPTLevel_def maxPT_def unat_arith_simps  unat_of_nat)

  from level
  have [simp]: "idx ?i < 0x40"
    by (simp add: idx_def maxPT_def maxPTLevel_def unat_word_ariths unat_arith_simps unat_of_nat)

  from level
  have [simp]: "pt + vshift vaddr ?i * 8 = ptSlotIndex (Suc level) pt vaddr"
    by (simp add: ptSlotIndex_def vshift_def maxPT_def ptIndex_def idx_def ptBitsLeft_def
                  bit_simps mask_def unat_word_ariths unat_of_nat maxPTLevel_def shiftl_t2n)

  have [simp]: "\<And>pte pte'. \<lbrakk> cpte_relation pte pte'; isPageTablePTE pte \<rbrakk> \<Longrightarrow>
                            ptrFromPAddr (pte_CL.ppn_CL (pte_lift pte') << pageBits) =
                            getPPtrFromHWPTE pte"
    by (auto simp: cpte_relation_def isPageTablePTE_def Let_def getPPtrFromHWPTE_def bit_simps
             split: pte.splits)

  have mask_simp[simp]: "(0x1FF::machine_word) = mask ptTranslationBits"
    by (simp add: bit_simps mask_def)

  show ?case
    supply if_cong[cong] option.case_cong[cong]
    apply (simp add: Suc(2) lookupPTFromLevel.simps whileAnno_def cong: if_weak_cong)
    apply (rule ccorres_assertE)
    apply (rule ccorres_expand_while_iff_Seq[THEN iffD1])
    apply (cinitlift i_' pt_')
    apply ccorres_rewrite
    apply (simp add: liftE_bindE)
    apply (rule ccorres_guard_imp)
      supply ccorres_prog_only_cong[cong]
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_ul_pre_getObject_pte, rename_tac pte)
      apply (rule ccorres_move_Guard_Seq [where P="page_table_at' pt" and P'="\<lambda>s. True"])
       apply (intro allI impI, simp)
       apply (rule disjCI2)
       apply clarsimp
       apply (erule (1) page_table_at'_array_assertion)
        apply (clarsimp simp: unat_and_mask_le_ptTrans vshift_def)
       apply (simp add: neq_0_unat)
      apply (rule ccorres_symb_exec_r2)
        apply (rule ccorres_add_return)
        apply (rule ccorres_split_nothrow)
            apply (rule ccorres_call[where xf'=ret__unsigned_long_'])
               apply (rule_tac pte=pte in isPTEPageTable_corres)
              apply simp
             apply simp
            apply simp
           apply ceqv
          apply (simp add: from_bool_0)
          apply (rule ccorres_Cond_rhs_Seq)
           apply ccorres_rewrite
           apply simp
           apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
           apply (simp add: return_def throwError_def)
           apply (rule allI, rule conseqPre, vcg)
           apply clarsimp
          apply simp
          apply (rule_tac P="getPPtrFromHWPTE pte = target_pt" in ccorres_cases; simp)
           apply (rule ccorres_symb_exec_r2)
             apply csymbr
             apply (rule ccorres_expand_while_iff_Seq[THEN iffD1])
             apply (rule_tac P'="P' \<inter> \<lbrace> \<acute>pt = pte_Ptr (getPPtrFromHWPTE pte) \<rbrace>" for P' in ccorres_inst)
             apply (cinitlift pt_')
             apply ccorres_rewrite
             apply (rule ccorres_inst[where P=\<top> and
                                            P'="\<lbrace> \<acute>ptSlot = pte_Ptr (pt + vshift vaddr ?i * 8) \<rbrace>"])
             apply (rule ccorres_from_vcg)
             apply (rule allI, rule conseqPre, vcg, clarsimp)
             apply (clarsimp simp: returnOk_def return_def)
            apply (vcg exspec=getPPtrFromHWPTE_spec')
           apply (vcg exspec=getPPtrFromHWPTE_modifies)
           apply (simp add: mex_def meq_def)
          apply (rule ccorres_checkPTAt)
          apply (rule ccorres_symb_exec_r2)
            apply (rule ccorres_symb_exec_r2)
              apply (rule Suc.hyps[unfolded whileAnno_def])
             using level apply simp
             apply vcg
            apply (vcg spec=modifies)
           apply (vcg exspec=getPPtrFromHWPTE_spec')
          apply (vcg exspec=getPPtrFromHWPTE_modifies)
          apply (simp add: mex_def meq_def)
         apply simp
         apply wp
        apply (clarsimp)
        apply (vcg exspec=isPTEPageTable_spec')
       apply vcg
      apply (vcg spec=modifies)
     apply fastforce
    using level
    apply (clarsimp simp: typ_heap_simps maxPT_def maxPTLevel_def)
    done
qed


lemma unmapPageTable_ccorres:
  "ccorres dc xfdc (invs' and page_table_at' ptPtr and (\<lambda>s. asid_wf asid))
      (\<lbrace>\<acute>asid___unsigned_long = asid\<rbrace> \<inter> \<lbrace>\<acute>vptr = vaddr\<rbrace> \<inter> \<lbrace>\<acute>target_pt = pte_Ptr ptPtr\<rbrace>)
      [] (unmapPageTable asid vaddr ptPtr) (Call unmapPageTable_'proc)"
  supply ccorres_prog_only_cong[cong] Collect_const[simp del] ccorres_dc_comp[simp]
  apply (rule ccorres_gen_asm)
  apply (rule ccorres_guard_imp[where Q'="\<lbrace>\<acute>vptr = vaddr\<rbrace> \<inter> \<lbrace>\<acute>target_pt = pte_Ptr ptPtr\<rbrace> \<inter>
                                          \<lbrace>\<acute>asid___unsigned_long = asid\<rbrace> \<inter> \<lbrace>\<acute>vptr = vaddr\<rbrace> \<inter>
                                          \<lbrace>\<acute>target_pt = pte_Ptr ptPtr\<rbrace>" and
                                      Q=A and A=A for A]; simp?)
  apply (cinit lift: asid___unsigned_long_' vptr_' target_pt_')
   apply (clarsimp simp add: ignoreFailure_liftM)
   apply (ctac add: findVSpaceForASID_ccorres,rename_tac vspace find_ret)
      prefer 2
      apply ccorres_rewrite
      apply (clarsimp simp: throwError_def)
      apply (rule ccorres_return_void_C)
     apply ccorres_rewrite
     apply csymbr
     apply (rule ccorres_symb_exec_r2)
       apply (rule ccorres_symb_exec_r2)
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_splitE_novcg[OF lookupPTFromLevel_ccorres])
             apply (simp add: maxPTLevel_def)
            apply ceqv
           apply (simp add: liftE_bindE)
           apply csymbr
           apply (rule ccorres_split_nothrow_novcg)
               apply (rule storePTE_Basic_ccorres)
               apply (clarsimp simp: cpte_relation_def)
              apply ceqv
             apply (rule ccorres_liftE)
             apply (rule ccorres_rel_imp)
              apply (rule ccorres_call[where xf'=xfdc])
                 apply (rule sfence_ccorres)
                apply simp
               apply simp
              apply simp
             apply simp
            apply wp
           apply (simp add: guard_is_UNIV_def)
          apply wpsimp
         apply (simp add: guard_is_UNIV_def)
        apply vcg
       apply (vcg spec=modifies)
      apply vcg
     apply (vcg spec=modifies)
    apply wp
   apply (vcg exspec=findVSpaceForASID_modifies)
  apply clarsimp
  done

lemma return_Null_ccorres:
  "ccorres ccap_relation ret__struct_cap_C_'
   \<top> UNIV (SKIP # hs)
   (return NullCap) (\<acute>ret__struct_cap_C :== CALL cap_null_cap_new()
                       ;; return_C ret__struct_cap_C_'_update ret__struct_cap_C_')"
  apply (rule ccorres_from_vcg_throws)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp add: ccap_relation_NullCap_iff return_def)
  done

lemma no_0_page_table_at'[elim!]:
  "\<lbrakk> page_table_at' 0 s; no_0_obj' s \<rbrakk> \<Longrightarrow> P"
  apply (clarsimp simp: page_table_at'_def)
  apply (drule spec[where x=0], clarsimp simp: bit_simps)
  done

lemma isFinalCapability_ccorres:
  "ccorres ((=) \<circ> from_bool) ret__unsigned_long_'
   (cte_wp_at' ((=) cte) slot and invs')
   (UNIV \<inter> {s. cte_' s = Ptr slot}) []
   (isFinalCapability cte) (Call isFinalCapability_'proc)"
  apply (cinit lift: cte_')
   apply (rule ccorres_Guard_Seq)
   apply (simp add: Let_def del: Collect_const)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'="mdb_'" in ccorres_abstract)
      apply ceqv
     apply (rule_tac P="mdb_node_to_H (mdb_node_lift rv') = cteMDBNode cte" in ccorres_gen_asm2)
     apply csymbr
     apply (rule_tac r'="(=) \<circ> from_bool" and xf'="prevIsSameObject_'"
               in ccorres_split_nothrow_novcg)
         apply (rule ccorres_cond2[where R=\<top>])
           apply (clarsimp simp: Collect_const_mem nullPointer_def)
           apply (simp add: mdbPrev_to_H[symmetric])
          apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (simp add: return_def)
         apply (rule ccorres_rhs_assoc)+
         apply (rule ccorres_symb_exec_l[OF _ getCTE_inv getCTE_wp empty_fail_getCTE])
         apply (rule_tac P="cte_wp_at' ((=) cte) slot
                             and cte_wp_at' ((=) rv) (mdbPrev (cteMDBNode cte))
                             and valid_cap' (cteCap rv)
                             and K (capAligned (cteCap cte) \<and> capAligned (cteCap rv))"
                    and P'=UNIV in ccorres_from_vcg)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def mdbPrev_to_H[symmetric])
         apply (simp add: rf_sr_cte_at_validD)
         apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (rule cmap_relationE1 [OF cmap_relation_cte], assumption+,
                    simp?, simp add: typ_heap_simps)+
         apply (drule ccte_relation_ccap_relation)+
         apply (rule exI, rule conjI, assumption)+
         apply (auto)[1]
        apply ceqv
       apply (clarsimp simp del: Collect_const)
       apply (rule ccorres_cond2[where R=\<top>])
         apply (simp add: from_bool_0 Collect_const_mem)
        apply (rule ccorres_return_C, simp+)[1]
       apply csymbr
       apply (rule ccorres_cond2[where R=\<top>])
         apply (simp add: nullPointer_def Collect_const_mem mdbNext_to_H[symmetric])
        apply (rule ccorres_return_C, simp+)[1]
       apply (rule ccorres_symb_exec_l[OF _ getCTE_inv getCTE_wp empty_fail_getCTE])
       apply (rule_tac P="cte_wp_at' ((=) cte) slot
                           and cte_wp_at' ((=) rva) (mdbNext (cteMDBNode cte))
                           and K (capAligned (cteCap rva) \<and> capAligned (cteCap cte))
                           and valid_cap' (cteCap cte)"
                  and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def from_bool_eq_if from_bool_0
                             mdbNext_to_H[symmetric] rf_sr_cte_at_validD)
       apply (clarsimp simp: cte_wp_at_ctes_of split: if_split)
       apply (rule cmap_relationE1 [OF cmap_relation_cte], assumption+,
                  simp?, simp add: typ_heap_simps)+
       apply (drule ccte_relation_ccap_relation)+
       apply (auto simp: from_bool_def split: bool.splits)[1]
      apply (wp getCTE_wp')
     apply (clarsimp simp add: guard_is_UNIV_def Collect_const_mem)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: Collect_const_mem)
  apply (frule(1) rf_sr_cte_at_validD, simp add: typ_heap_simps)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
  apply (simp add: typ_heap_simps)
  apply (clarsimp simp add: ccte_relation_def map_option_Some_eq2)
  by (auto,
         auto dest!: ctes_of_valid' [OF _ invs_valid_objs']
              elim!: valid_capAligned)

lemmas cleanup_info_wf'_simps[simp] = cleanup_info_wf'_def[split_simps capability.split]

lemma cteDeleteOne_ccorres:
  "ccorres dc xfdc
   (invs' and cte_wp_at' (\<lambda>ct. w = -1 \<or> cteCap ct = NullCap
        \<or> (\<forall>cap'. ccap_relation (cteCap ct) cap' \<longrightarrow> cap_get_tag cap' = w)) slot)
   ({s. gs_get_assn cteDeleteOne_'proc (ghost'state_' (globals s)) = w}
        \<inter> {s. slot_' s = Ptr slot}) []
   (cteDeleteOne slot) (Call cteDeleteOne_'proc)"
  unfolding cteDeleteOne_def
  apply (rule ccorres_symb_exec_l'
                [OF _ getCTE_inv getCTE_sp empty_fail_getCTE])
  apply (cinit' lift: slot_' cong: call_ignore_cong)
   apply (rule ccorres_move_c_guard_cte)
   apply csymbr
   apply (rule ccorres_abstract_cleanup)
   apply csymbr
   apply (rule ccorres_gen_asm2,
          erule_tac t="ret__unsigned_longlong = scast cap_null_cap"
                and s="cteCap cte = NullCap"
                 in ssubst)
   apply (clarsimp simp only: when_def unless_def)
   apply (rule ccorres_cond2[where R=\<top>])
     apply (clarsimp simp: Collect_const_mem)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (rule ccorres_Guard_Seq)
    apply (rule ccorres_basic_srnoop)
      apply (ctac(no_vcg) add: isFinalCapability_ccorres[where slot=slot])
       apply (rule_tac A="invs'  and cte_wp_at' ((=) cte) slot"
                     in ccorres_guard_imp2[where A'=UNIV])
        apply (simp add: split_def
                    del: Collect_const)
        apply (rule ccorres_move_c_guard_cte)
        apply (ctac(no_vcg) add: finaliseCap_True_standin_ccorres)
         apply (rule ccorres_assert)
         apply simp
         apply csymbr
         apply (ctac add: emptySlot_ccorres)
        apply (simp add: pred_conj_def finaliseCapTrue_standin_simple_def)
        apply (strengthen invs_mdb_strengthen' invs_urz)
        apply (wp typ_at_lifts isFinalCapability_inv
            | strengthen invs_valid_objs')+
       apply (clarsimp simp: irq_opt_relation_def invs_pspace_aligned' cte_wp_at_ctes_of)
       apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
       apply (clarsimp simp: typ_heap_simps ccte_relation_ccap_relation ccap_relation_NullCap_iff)
      apply (wp isFinalCapability_inv)
     apply simp
    apply (simp del: Collect_const)
   apply (rule ccorres_return_Skip)
  apply (clarsimp simp: Collect_const_mem cte_wp_at_ctes_of)
  apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
  apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap
                 dest!: ccte_relation_ccap_relation)
  apply (auto simp: o_def)
  done

lemma getIRQSlot_ccorres_stuff:
  "\<lbrakk> (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow>
   CTypesDefs.ptr_add intStateIRQNode_Ptr (uint (irq :: 6 word))
     = Ptr (irq_node' s + 2 ^ cte_level_bits * ucast irq)"
  apply (clarsimp simp add: rf_sr_def cstate_relation_def Let_def
                            cinterrupt_relation_def)
  apply (simp add: objBits_simps cte_level_bits_def
                   size_of_def mult.commute mult.left_commute of_int_uint_ucast )
  done

lemma deletingIRQHandler_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
                   ({s. irq_opt_relation (Some irq) (irq_' s)}) []
   (deletingIRQHandler irq) (Call deletingIRQHandler_'proc)"
  apply (cinit lift: irq_' cong: call_ignore_cong)
   apply (clarsimp simp: irq_opt_relation_def ptr_add_assertion_def
                   cong: call_ignore_cong )
   apply (rule_tac r'="\<lambda>rv rv'. rv' = Ptr rv"
                and xf'="slot_'" in ccorres_split_nothrow)
       apply (rule ccorres_Guard_intStateIRQNode_array_Ptr)
       apply (rule ccorres_move_array_assertion_irq)
       apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])

       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: getIRQSlot_def liftM_def getInterruptState_def
                             locateSlot_conv)
       apply (simp add: bind_def simpler_gets_def return_def getIRQSlot_ccorres_stuff[simplified])
      apply ceqv
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_symb_exec_l)
           apply (rule ccorres_symb_exec_r)
             apply (ctac add: cteDeleteOne_ccorres[where w="scast cap_notification_cap"])
            apply vcg
           apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
                gs_set_assn_Delete_cstate_relation[unfolded o_def])
          apply (wp getCTE_wp' | simp add: getSlotCap_def getIRQSlot_def locateSlot_conv
                                           getInterruptState_def)+
   apply vcg
  apply (clarsimp simp: cap_get_tag_isCap ghost_assertion_data_get_def
                        ghost_assertion_data_set_def)
  apply (simp add: cap_tag_defs)
  apply (clarsimp simp: cte_wp_at_ctes_of Collect_const_mem
                        irq_opt_relation_def Kernel_C.maxIRQ_def)
  apply (drule word_le_nat_alt[THEN iffD1])
  apply (clarsimp simp: uint_0_iff unat_gt_0 uint_up_ucast is_up)
  done

(* 6 = wordRadix,
   5 = tcb_cnode_radix + 1,
   7 = wordRadix+1*)
lemma Zombie_new_spec:
  "\<forall>s. \<Gamma>\<turnstile> ({s} \<inter> {s. type_' s = 64 \<or> type_' s < 63}) Call Zombie_new_'proc
          {s'. cap_zombie_cap_lift (ret__struct_cap_C_' s') =
                \<lparr> capZombieID_CL = \<^bsup>s\<^esup>ptr && ~~ mask (if \<^bsup>s\<^esup>type = (1 << 6) then 5 else unat (\<^bsup>s\<^esup>type + 1))
                                    || \<^bsup>s\<^esup>number___unsigned_long && mask (if \<^bsup>s\<^esup>type = (1 << 6) then 5 else unat (\<^bsup>s\<^esup>type + 1)),
                  capZombieType_CL = \<^bsup>s\<^esup>type && mask 7 \<rparr>
               \<and> cap_get_tag (ret__struct_cap_C_' s') = scast cap_zombie_cap}"
  apply vcg
  apply (clarsimp simp: word_sle_def)
  apply (simp add: mask_def word_log_esimps[where 'a=machine_word_len, simplified])
  apply clarsimp
  apply (simp add: word_add_less_mono1[where k=1 and j="0x3F", simplified])
  done

lemma irq_opt_relation_Some_ucast:
  "\<lbrakk> x && mask 6 = x; ucast x \<noteq> irqInvalid;
    ucast x \<le> (scast Kernel_C.maxIRQ :: 6 word) \<or> x \<le> (scast Kernel_C.maxIRQ :: machine_word) \<rbrakk>
   \<Longrightarrow> irq_opt_relation (Some (ucast x)) x"
  unfolding irq_opt_relation_def
  apply simp
  using ucast_ucast_mask[where x=x and 'a=6, symmetric]
  apply (simp add: irq_opt_relation_def)
  apply (clarsimp simp: irqInvalid_def Kernel_C.maxIRQ_def)
  apply (simp only: unat_arith_simps )
  apply (clarsimp simp: word_le_nat_alt Kernel_C.maxIRQ_def)
  done

lemma ccap_relation_IRQHandler_mask:
  "\<lbrakk> ccap_relation acap ccap; isIRQHandlerCap acap \<rbrakk>
    \<Longrightarrow> capIRQ_CL (cap_irq_handler_cap_lift ccap) && mask 6
        = capIRQ_CL (cap_irq_handler_cap_lift ccap)"
  apply (simp only: cap_get_tag_isCap[symmetric])
  apply (drule ccap_relation_c_valid_cap)
  apply (simp add: c_valid_cap_def cap_irq_handler_cap_lift cl_valid_cap_def)
  done

lemma option_to_ctcb_ptr_not_0:
  "\<lbrakk> tcb_at' p s; option_to_ctcb_ptr v = tcb_ptr_to_ctcb_ptr p\<rbrakk> \<Longrightarrow> v = Some p"
  apply (clarsimp simp: option_to_ctcb_ptr_def tcb_ptr_to_ctcb_ptr_def
                  split: option.splits)
  apply (frule tcb_aligned')
  apply (frule_tac y=ctcb_offset and n=tcbBlockSizeBits in aligned_offset_non_zero)
    apply (clarsimp simp: ctcb_offset_defs objBits_defs)+
  done

lemma update_tcb_map_to_tcb:
  "map_to_tcbs ((ksPSpace s)(p \<mapsto> KOTCB tcb)) = (map_to_tcbs (ksPSpace s))(p \<mapsto> tcb)"
  by (rule ext, clarsimp simp: map_comp_def split: if_split)

lemma ep_queue_relation_shift2:
  "(option_map2 tcbEPNext_C (f (cslift s)) = option_map2 tcbEPNext_C (cslift s)
    \<and> option_map2 tcbEPPrev_C (f (cslift s)) = option_map2 tcbEPPrev_C (cslift s))
     \<Longrightarrow> ep_queue_relation (f (cslift s)) ts qPrev qHead
          = ep_queue_relation (cslift s) ts qPrev qHead"
  apply (induct ts arbitrary: qPrev qHead; clarsimp)
  apply (simp add: option_map2_def fun_eq_iff map_option_case)
  apply (drule_tac x=qHead in spec)+
  apply (clarsimp split: option.split_asm)
  done

lemma cendpoint_relation_udpate_arch:
  "\<lbrakk> cslift x p = Some tcb ; cendpoint_relation (cslift x) v v' \<rbrakk>
    \<Longrightarrow> cendpoint_relation ((cslift x)(p \<mapsto> tcbArch_C_update f tcb)) v v'"
  apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def
                  split: endpoint.splits)
   apply (subst ep_queue_relation_shift2; simp add: fun_eq_iff)
   apply (safe ; case_tac "xa = p" ; clarsimp simp: option_map2_def map_option_case)
  apply (subst ep_queue_relation_shift2; simp add: fun_eq_iff)
  apply (safe ; case_tac "xa = p" ; clarsimp simp: option_map2_def map_option_case)
  done

lemma cnotification_relation_udpate_arch:
  "\<lbrakk> cslift x p = Some tcb ;  cnotification_relation (cslift x) v v' \<rbrakk>
    \<Longrightarrow>  cnotification_relation ((cslift x)(p \<mapsto> tcbArch_C_update f tcb)) v v'"
  apply (clarsimp simp: cnotification_relation_def Let_def tcb_queue_relation'_def
                  split: notification.splits ntfn.splits)
  apply (subst ep_queue_relation_shift2; simp add: fun_eq_iff)
  apply (safe ; case_tac "xa = p" ; clarsimp simp: option_map2_def map_option_case)
  done

lemma case_option_both[simp]:
  "(case f of None \<Rightarrow> P | _ \<Rightarrow> P) = P"
  by (auto split: option.splits)

lemma if_case_opt_same_branches:
  "cond \<longrightarrow> Option.is_none opt \<Longrightarrow>
   (if cond then
      case opt of
        None \<Rightarrow> f
      | Some x \<Rightarrow> g x
    else f) = f"
  by (cases cond; cases opt; clarsimp)

method return_NullCap_pair_ccorres =
   solves \<open>((rule ccorres_rhs_assoc2)+), (rule ccorres_from_vcg_throws),
          (rule allI, rule conseqPre, vcg), (clarsimp simp: return_def ccap_relation_NullCap_iff)\<close>

lemma ccap_relation_capFMappedASID_CL_0:
  "ccap_relation (ArchObjectCap (FrameCap x0 x1 x2 x3 None)) cap \<Longrightarrow>
   capFMappedASID_CL (cap_frame_cap_lift cap) = 0"
  apply (clarsimp simp: ccap_relation_def cap_frame_cap_lift_def)
  apply (case_tac "cap_lift cap")
   apply (fastforce simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)+
  done

lemma Arch_finaliseCap_ccorres:
  notes Collect_const[simp del] if_weak_cong[cong]
  shows
  "ccorres (\<lambda>rv rv'. ccap_relation (fst rv) (remainder_C rv') \<and>
                     ccap_relation (snd rv) (finaliseCap_ret_C.cleanupInfo_C rv'))
      ret__struct_finaliseCap_ret_C_'
   (invs' and cur_tcb' and valid_cap' (ArchObjectCap cp)
       and (\<lambda>s. 2 ^ acapBits cp \<le> gsMaxObjectSize s))
   (UNIV \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
                        \<inter> {s. final_' s = from_bool is_final}) []
   (Arch.finaliseCap cp is_final) (Call Arch_finaliseCap_'proc)"
  (is "ccorres _ _ ?abstract_pre ?c_pre _ _ _")
  supply if_cong[cong] option.case_cong[cong]
  apply (cinit lift: cap_' final_' cong: call_ignore_cong)
   apply csymbr
   apply (simp add: RISCV64_H.finaliseCap_def cap_get_tag_isCap_ArchObject)
   apply (rule ccorres_cases[where P=is_final]; clarsimp cong: arch_capability.case_cong)
    prefer 2
    apply (subgoal_tac "isFrameCap cp \<longrightarrow> \<not> isPageTableCap cp \<and> \<not> isASIDPoolCap cp \<and> \<not> isASIDControlCap cp")
     apply (rule ccorres_cases[where P="isFrameCap cp"]; clarsimp)
      prefer 2
      apply (rule ccorres_inst[where P="?abstract_pre" and P'=UNIV])
      apply (cases cp; clarsimp simp: isCap_simps; ccorres_rewrite)
             apply return_NullCap_pair_ccorres (* ASIDPoolCap *)
            apply return_NullCap_pair_ccorres (* ASIDControlCap *)
         \<comment> \<open>PageTableCap\<close>
         apply (subst ccorres_cond_seq2_seq[symmetric])
         apply (rule ccorres_guard_imp)
           apply (rule ccorres_rhs_assoc)
           apply csymbr
           apply clarsimp
           apply ccorres_rewrite
           apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
           apply (return_NullCap_pair_ccorres, simp+)
     \<comment> \<open>FrameCap\<close>
     apply (clarsimp simp: isCap_simps)
     apply (rule ccorres_guard_imp[where A="?abstract_pre" and A'=UNIV])
       apply ccorres_rewrite
       apply (rule ccorres_add_return2)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply wpc
        apply (prop_tac "ret__unsigned_longlong = 0")
         apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
         apply (drule cap_to_H_Frame_unfold, clarsimp)
         apply (simp add: cap_frame_cap_lift_def split: if_split_asm)
        apply ccorres_rewrite
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply simp
        apply (rule ccorres_return_C; simp)
       apply (prop_tac "ret__unsigned_longlong \<noteq> 0")
        apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
        apply (drule cap_to_H_Frame_unfold, clarsimp)
        apply (simp add: cap_frame_cap_lift_def split: if_split_asm)
       apply ccorres_rewrite
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply wpc
       apply simp
       apply (ctac (no_vcg) add: unmapPage_ccorres)
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (rule ccorres_return_C; simp)
       apply wp
      apply (clarsimp simp: valid_cap'_def wellformed_mapdata'_def)
     apply (clarsimp simp: ccap_relation_NullCap_iff ccap_relation_frame_tags)
     apply (clarsimp simp: ccap_relation_def c_valid_cap_def map_option_Some_eq2
                           cl_valid_cap_def
                     dest!: cap_to_H_Frame_unfold)
     apply (simp add: cap_frame_cap_lift_def split: if_splits)
    apply (clarsimp simp: isCap_simps)
   apply (wpc; simp add: isCap_simps; ccorres_rewrite)
      \<comment> \<open>ASIDControlCap\<close>
      apply (rule ccorres_inst[where P="?abstract_pre" and P'=UNIV])
      apply return_NullCap_pair_ccorres
     \<comment> \<open>ASIDPoolCap\<close>
     apply (rule ccorres_inst[where P="?abstract_pre" and P'=UNIV])
     apply (rule ccorres_guard_imp)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply csymbr
       apply (ctac (no_vcg) add: deleteASIDPool_ccorres)
        apply (csymbr, csymbr, csymbr, csymbr)
        apply (rule ccorres_return_C; simp)
       apply wp
      apply (clarsimp simp: valid_cap'_def)
     apply (clarsimp simp: ccap_relation_NullCap_iff cap_get_tag_isCap_unfolded_H_cap)
     apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
     apply (clarsimp simp: cap_to_H_def Let_def cap_asid_pool_cap_lift_def
                     split: cap_CL.splits if_splits)
    \<comment> \<open>FrameCap\<close>
    apply (rule ccorres_inst[where P="?abstract_pre" and P'=UNIV])
    apply (rule ccorres_guard_imp)
      apply (rule ccorres_add_return2)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply wpc
       apply (prop_tac "ret__unsigned_longlong = 0")
        apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
        apply (drule cap_to_H_Frame_unfold, clarsimp)
        apply (simp add: cap_frame_cap_lift_def split: if_split_asm)
       apply ccorres_rewrite
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply simp
       apply (rule ccorres_return_C; simp)
      apply (prop_tac "ret__unsigned_longlong \<noteq> 0")
       apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
       apply (drule cap_to_H_Frame_unfold, clarsimp)
       apply (simp add: cap_frame_cap_lift_def split: if_split_asm)
      apply ccorres_rewrite
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply csymbr
      apply csymbr
      apply wpc
      apply simp
      apply (ctac (no_vcg) add: unmapPage_ccorres)
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply (rule ccorres_return_C; simp)
      apply wp
     apply (clarsimp simp: valid_cap'_def wellformed_mapdata'_def)
    apply (clarsimp simp: ccap_relation_NullCap_iff cap_get_tag_isCap_unfolded_H_cap)
    apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_frame_cap_lift_def
                          c_valid_cap_def cl_valid_cap_def
                    dest!: cap_to_H_Frame_unfold
                    split: if_splits)
   \<comment> \<open>PageTableCap\<close>
   apply (rule ccorres_inst[where P="?abstract_pre" and P'=UNIV])
   apply (rule ccorres_guard_imp)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply ccorres_rewrite
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr
     apply wpc
      apply (prop_tac "ret__unsigned_longlong = 0")
       apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 dest!: cap_to_H_PTCap)
       apply (simp add: cap_page_table_cap_lift_def to_bool_def split: if_split_asm)
      apply ccorres_rewrite
      apply simp
      apply (csymbr, csymbr, csymbr, csymbr)
      apply (rule ccorres_return_C; simp)
     apply (prop_tac "ret__unsigned_longlong \<noteq> 0")
      apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 dest!: cap_to_H_PTCap)
      apply (simp add: cap_page_table_cap_lift_def split: if_split_asm)
     apply ccorres_rewrite
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr
     apply wpc
     apply (simp add: bindE_assoc cong: ccorres_prog_only_cong)
     apply (simp add: catch_is_if bind_assoc catch_throwError catch_liftE if_catch_distrib if3_fold
                      if_swap[where P="P \<or> Q" for P Q]
                 cong: if_cong ccorres_prog_only_cong)
     apply (rule ccorres_split_nothrow)
         apply (ctac add: findVSpaceForASID_ccorres)
        apply ceqv
       apply csymbr
       apply csymbr
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac R'="{s. rv' = liftxf errstate
                                                findVSpaceForASID_ret_C.status_C
                                                findVSpaceForASID_ret_C.vspace_root_C
                                                find_ret_' s }"
                           in ccorres_cond_strong[where R=\<top>])
             apply (rename_tac rv rv' base_ptr)
             apply (case_tac rv; clarsimp)
             apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_page_table_cap_lift_def
                             dest!: cap_to_H_PTCap)
            apply (rule ccorres_call[where xf'=xfdc, OF deleteASID_ccorres]; simp)
           apply csymbr
           apply (ctac (no_vcg) add: unmapPageTable_ccorres)
          apply ceqv
         apply csymbr
         apply csymbr
         apply csymbr
         apply csymbr
         apply (rule ccorres_return_C; simp)
        apply wp
       apply (simp add: ccap_relation_NullCap_iff guard_is_UNIV_def)
      apply (wp hoare_drop_imps)
     apply (clarsimp simp: cap_get_tag_isCap_unfolded_H_cap)
     apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 dest!: cap_to_H_PTCap)
     apply (simp add: cap_page_table_cap_lift_def)
     apply (vcg expspec=findVSpaceForASID_modifies)
    apply (clarsimp simp: valid_cap'_def wellformed_mapdata'_def)
    apply fastforce
   apply (clarsimp simp: ccap_relation_NullCap_iff cap_get_tag_isCap_unfolded_H_cap)
   apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 dest!: cap_to_H_PTCap)
   apply (clarsimp simp: cap_page_table_cap_lift_def)
  apply fastforce
  done

lemma prepareThreadDelete_ccorres:
  "ccorres dc xfdc
     (invs' and tcb_at' thread)
     (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread}) hs
   (prepareThreadDelete thread) (Call Arch_prepareThreadDelete_'proc)"
  apply (cinit lift: thread_', rename_tac cthread)
   apply (rule ccorres_return_Skip)
  apply fastforce
  done

lemma tcb_ptr_to_ctcb_ptr_alignment:
  "\<lbrakk> is_aligned tcb tcbBlockSizeBits; bits \<le> ctcb_size_bits \<rbrakk>
   \<Longrightarrow> ptr_val (tcb_ptr_to_ctcb_ptr tcb) && ~~ mask bits = ptr_val (tcb_ptr_to_ctcb_ptr tcb)"
  apply (clarsimp simp: tcb_ptr_to_ctcb_ptr_def)
  apply (rule is_aligned_neg_mask_eq)
  apply (erule aligned_add_aligned)
   apply (erule is_aligned_weaken[rotated])
   by (auto simp add: is_aligned_def objBits_defs ctcb_offset_defs)

lemma option_to_ctcb_ptr_canonical:
  "\<lbrakk>pspace_canonical' s; tcb_at' tcb s\<rbrakk>
   \<Longrightarrow> option_to_ctcb_ptr (Some tcb)
       = tcb_Ptr (sign_extend canonical_bit (ptr_val (tcb_ptr_to_ctcb_ptr tcb)))"
  apply (clarsimp simp: option_to_ctcb_ptr_def)
  apply (frule (1) obj_at'_is_canonical)
  by (fastforce dest: canonical_address_tcb_ptr
                simp: obj_at'_def objBits_simps' canonical_address_sign_extended
                      sign_extended_iff_sign_extend)

lemma schedContext_unbindNtfn_ccorres:
  "ccorres dc xfdc
    (invs' and sc_at' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> hs
    (schedContextUnbindNtfn scPtr) (Call schedContext_unbindNtfn_'proc)"
  supply Collect_const[simp del]
   apply (cinit lift: sc_')
    apply (rule ccorres_stateAssert)
    apply (rule ccorres_pre_getObject_sc, rename_tac sc)
    apply (rule_tac val="from_bool True"
                and R="sc_at' scPtr and no_0_obj'"
                and xf'=ret__int_'
                 in ccorres_symb_exec_r_known_rv[where R'=UNIV])
       apply (rule conseqPre, vcg)
       apply (fastforce split: if_splits)
      apply ceqv
     apply ccorres_rewrite
     apply (rule ccorres_move_c_guard_sc)
     apply (rule_tac val="from_bool (scNtfn sc \<noteq> None)"
                 and R="ko_at' sc scPtr and no_0_obj' and valid_objs'"
                 and xf'=ret__int_'
                  in ccorres_symb_exec_r_known_rv[where R'=UNIV])
        apply (rule conseqPre, vcg)
        apply (clarsimp split: if_splits)
        apply (frule (1) obj_at_cslift_sc)
        apply (frule (1) sc_ko_at_valid_objs_valid_sc')
        apply clarsimp
        apply (intro conjI impI allI)
         apply (clarsimp simp: typ_heap_simps csched_context_relation_def option_to_ptr_def
                               option_to_0_def
                        split: option.splits)
        apply (clarsimp simp: typ_heap_simps csched_context_relation_def option_to_ptr_def
                              option_to_0_def valid_sched_context'_def
                       split: option.splits)
       apply ceqv
      apply (simp add: option.case_eq_if)
      apply (subst if_swap)
      apply (rule ccorres_cond_both'[where Q=\<top> and Q'="\<top>"])
        apply fastforce
       apply (rule ccorres_pre_getNotification, rename_tac ntfn)
       apply (rule_tac P="\<lambda>s. invs' s \<and> sym_refs (state_refs_of' s)
                              \<and> ko_at' sc scPtr s \<and> ko_at' ntfn (the (scNtfn sc)) s"
                   and P'=UNIV
                   in ccorres_split_nothrow_novcg)
           apply (rule ccorres_from_vcg[where rrel=dc and xf=xfdc])
           apply (rule allI, rule conseqPre, vcg)
           apply clarsimp
           apply (rename_tac ntfnPtr)
           apply (frule cmap_relation_ntfn)
           apply (frule (1) obj_at_cslift_sc)
           apply (frule (1) invs'_ko_at_valid_sched_context')
           apply normalise_obj_at'
           apply (rename_tac sc')
           apply (erule (1) cmap_relation_ko_atE)
           apply (rule conjI)
            apply (erule h_t_valid_clift)
           apply (rule conjI)
            apply (clarsimp simp: typ_heap_simps' csched_context_relation_def)
           apply (clarsimp simp: setNotification_def split_def)
           apply (rule bexI[OF _ setObject_eq])
               apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                                cpspace_relation_def update_ntfn_map_tos
                                csched_context_relation_def typ_heap_simps')
               apply (prop_tac "scNotification_C sc' = ntfn_Ptr ntfnPtr", simp)
               apply clarsimp
               apply (intro conjI)
                  apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
                   apply (clarsimp simp: cnotification_relation_def Let_def split: ntfn.splits)
                  apply fastforce
                 apply (simp add: refill_buffer_relation_def image_def dom_def Let_def typ_heap_simps
                                  update_ntfn_map_tos)
                apply (simp add: carch_state_relation_def)
               apply (simp add: cmachine_state_relation_def)
              apply (simp add: h_t_valid_clift_Some_iff)
             apply (simp add: objBits_simps')
            apply (simp add: objBits_simps)
           apply assumption
          apply ceqv
         apply clarsimp
         apply (rule ccorres_move_c_guard_sc)
         apply (rule updateSchedContext_ccorres_lemma2[where P=\<top>])
           apply vcg
          apply fastforce
         apply clarsimp
         apply (rule_tac sc'="scNotification_C_update (\<lambda>_. NULL) sc'"
                      in rf_sr_sc_update_no_refill_buffer_update2;
                fastforce?)
           apply (clarsimp simp: typ_heap_simps')
          apply (clarsimp simp: csched_context_relation_def)
         apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
        apply clarsimp
        apply (wpsimp wp: hoare_vcg_conj_lift)
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (rule ccorres_return_Skip)
     apply vcg
    apply vcg
   apply (fastforce simp: sym_refs_asrt_def)
   done

lemma schedContext_unbindTCB_ccorres:
  "ccorres dc xfdc
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and sc_at' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> hs
     (schedContextUnbindTCB scPtr) (Call schedContext_unbindTCB_'proc)"
  apply (cinit lift: sc_')
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_pre_getObject_sc, rename_tac sc)
   apply (rule ccorres_assert2)
   apply (rule ccorres_pre_getCurThread)
   apply (rule_tac val="tcb_ptr_to_ctcb_ptr (the (scTCB sc))"
               and R="ko_at' sc scPtr and no_0_obj' and valid_objs'"
               and R'=UNIV
               and xf'=tcb_'
                in ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg, clarsimp)
      apply (frule (1) obj_at_cslift_sc)
      apply (clarsimp simp: typ_heap_simps csched_context_relation_def option_to_ctcb_ptr_def)
     apply ceqv
    apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
        apply (simp add: when_def)
        apply (rule_tac R="\<lambda>s. cur = ksCurThread s" in ccorres_cond)
          apply (fastforce dest: rf_sr_ksCurThread)
         apply (ctac add: rescheduleRequired_ccorres)
        apply (rule ccorres_return_Skip)
       apply ceqv
      apply (ctac add: tcbSchedDequeue_ccorres)
        apply (ctac add: tcbReleaseRemove_ccorres)
          apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
              apply (rule_tac P'="ko_at' sc scPtr and valid_objs'"
                           in threadSet_ccorres_lemma3[where P=\<top>])
               apply vcg
              apply clarsimp
              apply (frule (1) sc_ko_at_valid_objs_valid_sc')
              apply (rule conjI)
               apply (clarsimp simp: typ_heap_simps valid_sched_context'_def valid_bound_obj'_def
                              split: option.splits)
              apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                simp: typ_heap_simps' ctcb_relation_def tcb_cte_cases_def
                                      cteSizeBits_def)
             apply ceqv
            apply (rule updateSchedContext_ccorres_lemma2[where P=\<top>])
              apply vcg
             apply fastforce
            apply clarsimp
            apply (rule conjI)
             apply (clarsimp simp: typ_heap_simps')
            apply (rule_tac sc'="scTcb_C_update (\<lambda>_. NULL) sc'"
                         in rf_sr_sc_update_no_refill_buffer_update2;
                   fastforce?)
              apply (clarsimp simp: typ_heap_simps')
             apply (clarsimp simp: csched_context_relation_def option_to_ctcb_ptr_def)
            apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
           apply wpsimp
          apply vcg
         apply wpsimp
        apply (vcg exspec=tcbReleaseRemove_modifies)
       apply wpsimp
      apply clarsimp
      apply (vcg exspec=tcbSchedDequeue_modifies)
     apply wpsimp
    apply (vcg exspec=rescheduleRequired_modifies)
   apply vcg
  apply (fastforce dest: invs_valid_objs' sc_ko_at_valid_objs_valid_sc'
                   simp: valid_sched_context'_def split: option.splits if_splits)
  done

lemma schedContext_unbindAllTCBs_ccorres:
  "ccorres dc xfdc
    (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and sc_at' scPtr) \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> hs
    (schedContextUnbindAllTCBs scPtr) (Call schedContext_unbindAllTCBs_'proc)"
  apply (cinit lift: sc_')
   apply (rule ccorres_pre_getObject_sc, rename_tac sc)
   apply (rule ccorres_move_c_guard_sc)
   apply (clarsimp simp: when_def)
   apply (rule_tac R="ko_at' sc scPtr and valid_objs' and no_0_obj'" in ccorres_cond)
     apply clarsimp
     apply (frule (1) obj_at_cslift_sc)
     apply (frule (1) sc_ko_at_valid_objs_valid_sc')
     apply normalise_obj_at'
     subgoal
       by (fastforce dest!: tcb_at_not_NULL
                      simp: typ_heap_simps valid_sched_context'_def valid_bound_obj'_def
                            csched_context_relation_def option_to_ctcb_ptr_def
                     split: option.splits)
    apply (ctac add: schedContext_unbindTCB_ccorres)
   apply (rule ccorres_return_Skip)
  apply fastforce
  done

lemma schedContext_updateConsumed_ccorres:
  "ccorres (=) ret__unsigned_longlong_' \<top> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (schedContextUpdateConsumed scPtr)
     (Call schedContext_updateConsumed_'proc)"
  apply (cinit lift: sc_')
   apply (rule ccorres_pre_getObject_sc)
   apply clarsimp
   apply (rename_tac sc)
   apply (rule ccorres_move_c_guard_sc)
   apply (rule_tac val="scConsumed sc"
               and xf'=consumed_'
               and R="ko_at' sc scPtr"
                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply (rule conseqPre, vcg)
      apply (fastforce dest: obj_at_cslift_sc simp: typ_heap_simps csched_context_relation_def)
     apply ceqv
    apply csymbr
    apply (rule ccorres_cond[where R=\<top>])
      apply (fastforce split: if_splits)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply clarsimp
     apply (rule ccorres_move_c_guard_sc)
     apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
         apply (rule updateSchedContext_ccorres_lemma2[where P=\<top>])
           apply vcg
          apply fastforce
         apply (clarsimp simp: typ_heap_simps)
         apply (rule_tac sc'="scConsumed_C_update (\<lambda>_. scConsumed_C sc' - maxTicksToUs) sc'"
                      in rf_sr_sc_update_no_refill_buffer_update2;
                fastforce?)
           apply (clarsimp simp: typ_heap_simps')
          apply (clarsimp simp: csched_context_relation_def)
         apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
        apply ceqv
       apply csymbr+
       apply (fastforce intro: ccorres_return_C)
      apply wpsimp
     apply vcg
    apply (rule ccorres_rhs_assoc)
    apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
        apply clarsimp
        apply (rule updateSchedContext_ccorres_lemma2[where P=\<top>])
          apply vcg
         apply fastforce
        apply (clarsimp simp: typ_heap_simps)
        apply (rule_tac sc'="scConsumed_C_update (\<lambda>_. 0) sc'"
                     in rf_sr_sc_update_no_refill_buffer_update2;
               fastforce?)
          apply (clarsimp simp: typ_heap_simps')
         apply (clarsimp simp: csched_context_relation_def)
        apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
       apply ceqv
      apply clarsimp
      apply csymbr
      apply (fastforce intro: ccorres_return_C)
     apply wpsimp
    apply vcg
   apply vcg
  apply clarsimp
  done

lemma mode_setTimeArg_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = of_nat i + 1) ret__unsigned_long_'
     (tcb_at' thread and K (TCB_H.msgRegisters ! i = reg \<and> i < length msgRegisters))
     (\<lbrace>\<acute>time = val\<rbrace>
      \<inter> \<lbrace>\<acute>i = of_nat i\<rbrace>
      \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
    (asUser thread (setRegister reg val)) (Call mode_setTimeArg_'proc)"
  apply (rule ccorres_grab_asm)
  apply (cinit' lift:  time_' i_' thread_')
   apply (rule ccorres_add_return2)
   apply (ctac add: setMR_as_setRegister_ccorres[where offset=i])
     apply (fastforce intro: ccorres_return_C)
    apply fastforce
   apply (vcg exspec=setMR_modifies)
  apply clarsimp
  apply (intro conjI impI)
   apply (clarsimp simp: ucast_of_nat_small n_msgRegisters_def length_msgRegisters)
  apply (rule_tac s="of_nat (Suc i)" and t="of_nat i + 1" in subst, fastforce)
  apply (rule_tac s="of_nat (Suc i)" and t="of_nat i + 1" in subst, fastforce)
  apply (subst ucast_of_nat_small; clarsimp simp: n_msgRegisters_def length_msgRegisters)
  done

lemma replyFromKernel_consumed_ccorres:
  "ccorres dc xfdc
     (tcb_at' tcbPtr)
     (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace>
      \<inter> \<lbrace>\<acute>consumed = consumed\<rbrace>) hs
     (replyFromKernel tcbPtr (0, wordsOfTime consumed))
     (Call replyFromKernel_consumed_'proc)"
  apply (cinit lift: thread_' consumed_')
   apply (ctac add: lookupIPCBuffer_ccorres)
     apply (ctac add: setRegister_ccorres)
       apply (simp add: wordsOfTime_def words_from_time_def setMRs_single)
       apply (ctac add: mode_setTimeArg_ccorres[where i=0])
         apply csymbr
         apply (simp only: setMessageInfo_def bind_assoc)
         apply ctac
           apply simp
           apply (ctac add: setRegister_ccorres)
          apply wpsimp
         apply vcg
        apply wpsimp
       apply (clarsimp simp: msgInfoRegister_def RISCV64.msgInfoRegister_def
                             Kernel_C.msgInfoRegister_def Kernel_C.a1_def)
       apply (vcg exspec= mode_setTimeArg_modifies)
      apply wpsimp
     apply (vcg exspec=setRegister_modifies)
    apply wpsimp
   apply (vcg exspec=lookupIPCBuffer_modifies)
  apply (clarsimp simp: msgRegisters_unfold message_info_to_H_def mask_def RISCV64.badgeRegister_def
                        RISCV64_H.badgeRegister_def Kernel_C.badgeRegister_def Kernel_C.a0_def)
  done

lemma replyOnRestart_replyFromKernel_rewrite:
  "monadic_rewrite False True (st_tcb_at' ((=) Restart) tcbPtr)
     (replyOnRestart tcbPtr reply isCall)
     (do when isCall (replyFromKernel tcbPtr (0, reply)); setThreadState Running tcbPtr od)"
  apply (clarsimp simp: replyOnRestart_def when_def)
  apply monadic_rewrite_symb_exec_l
    apply (monadic_rewrite_l monadic_rewrite_if_l_True)
    apply (rule monadic_rewrite_refl)
   apply wpsimp
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
  done

lemma setConsumed_returnConsumed_ccorres:
  "ccorres dc xfdc
     (tcb_at' tcbPtr)
     (\<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace>
      \<inter> \<lbrace>\<acute>write_msg = from_bool isCall\<rbrace>) hs
     (do reply \<leftarrow> returnConsumed scPtr;
         when isCall (replyFromKernel tcbPtr (0, reply))
      od)
     (Call setConsumed_'proc)"
  apply (cinit' lift: sc_' thread_' write_msg_' simp: returnConsumed_def bind_assoc)
  apply (rule ccorres_stateAssert)
  apply (ctac add: schedContext_updateConsumed_ccorres)
     apply (clarsimp simp: when_def)
     apply (rule ccorres_cond[where R=\<top>])
       apply (fastforce split: if_splits)
      apply (simp flip: wordsOfTime_eq_words_from_time)
      apply (ctac add: replyFromKernel_consumed_ccorres)
     apply (rule ccorres_return_Skip)
    apply wpsimp
   apply (vcg exspec=schedContext_updateConsumed_modifies)
  apply clarsimp
  done

lemma setConsumed_def2:
  "setConsumed scPtr tcbPtr
   = (do reply \<leftarrow> returnConsumed scPtr; replyFromKernel tcbPtr (0, reply) od)"
  by (clarsimp simp: setConsumed_def returnConsumed_def bind_assoc)

lemma setConsumed_setConsumed_ccorres:
  "ccorres dc xfdc
     (tcb_at' tcbPtr)
     (\<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace>
      \<inter> \<lbrace>\<acute>write_msg = ucast true\<rbrace>) hs
     (setConsumed scPtr tcbPtr) (Call setConsumed_'proc)"
  apply (clarsimp simp: setConsumed_def2)
  apply (rule monadic_rewrite_ccorres_assemble[where P=P and Q=P for P, simplified])
   apply (fastforce intro: setConsumed_returnConsumed_ccorres ccorres_guard_imp)+
  apply (fastforce intro: monadic_rewrite_guard_imp monadic_rewrite_refl)
  done

crunch setConsumed
  for no_0_obj'[wp]: no_0_obj'

lemma schedContext_completeYieldTo_ccorres:
  "ccorres dc xfdc
    (invs' and tcb_at' tptr) \<lbrace>\<acute>yielder = tcb_ptr_to_ctcb_ptr tptr\<rbrace> hs
    (schedContextCompleteYieldTo tptr) (Call schedContext_completeYieldTo_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: yielder_')
   apply (rule_tac xf'=ret__int_'
               and val="from_bool True"
               and R="tcb_at' tptr"
                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply (rule conseqPre, vcg, clarsimp)
      apply (frule (1) obj_at_cslift_tcb)
      apply (fastforce dest: tcb_at_not_NULL)
     apply ceqv
    apply ccorres_rewrite
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule ccorres_pre_threadGet)
    apply (rule_tac xf'=ret__int_'
                and val="from_bool (scPtrOpt \<noteq> None)"
                and R="obj_at' (\<lambda>tcb. tcbYieldTo tcb = scPtrOpt) tptr and valid_objs' and no_0_obj'"
                 in ccorres_symb_exec_r_known_rv[where R'=UNIV])
       apply (rule conseqPre, vcg)
       apply normalise_obj_at'
       apply (rename_tac tcb)
       apply (frule (1) obj_at_cslift_tcb)
       apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
       apply (case_tac "tcbYieldTo tcb";
              clarsimp simp: ctcb_relation_def typ_heap_simps valid_tcb'_def
                      split: if_splits bool.splits)
      apply ceqv
     apply (clarsimp simp: when_def)
     apply (rule ccorres_cond[where R=\<top>])
       apply fastforce
      apply (rule ccorres_move_c_guard_tcb)
      apply (ctac add: setConsumed_setConsumed_ccorres)
        apply (ctac add: schedContext_cancelYieldTo_ccorres)
       apply wpsimp
      apply (vcg exspec=setConsumed_modifies)
     apply (rule ccorres_return_Skip)
    apply vcg
   apply vcg
  apply (fastforce simp: obj_at'_def typ_heap_simps true_def ctcb_relation_def)
  done

lemma finaliseCap_ccorres:
  "\<And>final.
   ccorres (\<lambda>rv rv'. ccap_relation (fst rv) (finaliseCap_ret_C.remainder_C rv')
                   \<and> ccap_relation (snd rv) (finaliseCap_ret_C.cleanupInfo_C rv'))
   ret__struct_finaliseCap_ret_C_'
   (invs' and valid_cap' cap and (\<lambda>s. ksIdleThread s \<notin> capRange cap)
          and (\<lambda>s. 2 ^ capBits cap \<le> gsMaxObjectSize s))
   (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. final_' s = from_bool final}
                        \<inter> {s. exposed_' s = from_bool flag \<comment> \<open>dave has name wrong\<close>}) []
   (finaliseCap cap final flag) (Call finaliseCap_'proc)"
  apply (rule_tac F="capAligned cap" in Corres_UL_C.ccorres_req)
   apply (clarsimp simp: valid_capAligned)
  apply (case_tac "P :: bool" for P)
   apply (rule ccorres_guard_imp2, erule finaliseCap_True_cases_ccorres)
   apply simp
  apply (subgoal_tac "\<exists>acap. (0 <=s (-1 :: word8)) \<or> acap = capCap cap")
   prefer 2 apply simp
  apply (erule exE)
  apply (cinit lift: cap_' final_' exposed_' cong: call_ignore_cong)
   apply csymbr
   apply (simp del: Collect_const)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (clarsimp simp: cap_get_tag_isCap isCap_simps
                    cong: if_cong)
    apply (clarsimp simp: word_sle_def)
    apply (rule ccorres_if_lhs)
     apply (rule ccorres_fail)
    apply (simp add: liftM_def del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_add_return2)
    apply (ccorres_rewrite)
    apply (ctac add: Arch_finaliseCap_ccorres)
      apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def Collect_const_mem)
     apply wp
    apply (vcg exspec=Arch_finaliseCap_modifies)
   apply (simp add: cap_get_tag_isCap Collect_False
               del: Collect_const)
   apply csymbr
   apply (simp add: cap_get_tag_isCap Collect_False Collect_True
               del: Collect_const)
   apply (rule ccorres_if_lhs)
    apply (simp, rule ccorres_fail)
   apply (simp add: from_bool_0 Collect_True Collect_False
               del: Collect_const)
   apply csymbr
   apply (simp add: cap_get_tag_isCap Collect_False Collect_True
               del: Collect_const)
   apply (rule ccorres_if_lhs)
    apply (simp add: Let_def)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: cap_get_tag_isCap word_sle_def
                          return_def word_mod_less_divisor
                          less_imp_neq [OF word_mod_less_divisor])
    apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
    apply (clarsimp simp: isCap_simps capAligned_def
                          objBits_simps word_bits_conv
                          signed_shift_guard_simpler_64)
    apply (rule conjI)
     apply (simp add: word_less_nat_alt)
    apply (rule conjI)
     apply (auto simp: word_less_nat_alt word_le_not_less[symmetric] bit_simps objBits_defs)[1]
    apply (simp add: ccap_relation_def cap_zombie_cap_lift)
    apply (simp add: cap_to_H_def isZombieTCB_C_def ZombieTCB_C_def)
    apply (simp add: less_mask_eq word_less_nat_alt less_imp_neq)
    apply (simp add: mod_mask_drop[where n=6] mask_def[where n=6]
                     less_imp_neq [OF word_mod_less_divisor]
                     less_imp_neq Let_def objBits_simps')
    apply (thin_tac "a = b" for a b)+
    apply (subgoal_tac "P" for P)
     apply (subst add.commute, subst unatSuc, assumption)+
     apply clarsimp
     apply (rule conjI)
      apply (rule word_eqI)
      apply (simp add: word_size word_ops_nth_size nth_w2p
                       less_Suc_eq_le is_aligned_nth)
      apply (safe, simp_all)[1]
     apply (simp add: shiftL_nat ccap_relation_NullCap_iff[symmetric, simplified ccap_relation_def])
     apply (rule trans, rule unat_power_lower64[symmetric])
      apply (simp add: word_bits_conv)
     apply (rule unat_cong, rule word_eqI)
     apply (simp add: word_size word_ops_nth_size nth_w2p
                      is_aligned_nth less_Suc_eq_le)
     apply (safe, simp_all)[1]
    apply (subst add.commute, subst eq_diff_eq[symmetric])
    apply (clarsimp simp: minus_one_norm)
   apply (rule ccorres_if_lhs)
    apply (simp add: Let_def getThreadCSpaceRoot_def locateSlot_conv
                     Collect_True Collect_False
                del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply csymbr
    apply csymbr
    apply (rule ccorres_Guard_Seq)+
    apply csymbr
sorry (* FIXME RT: finaliseCap_ccorres *) (*
    apply (ctac(no_vcg) add: unbindNotification_ccorres)
     apply (ctac(no_vcg) add: suspend_ccorres[OF cteDeleteOne_ccorres])
     apply (ctac(no_vcg) add: prepareThreadDelete_ccorres)
      apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: word_sle_def return_def)
      apply (subgoal_tac "cap_get_tag capa = scast cap_thread_cap")
       apply (drule(1) cap_get_tag_to_H)
       apply (clarsimp simp: isCap_simps capAligned_def ccap_relation_NullCap_iff)
       apply (simp add: ccap_relation_def cap_zombie_cap_lift)
       apply (simp add: cap_to_H_def isZombieTCB_C_def ZombieTCB_C_def
                        mask_def)
       apply (simp add: cte_level_bits_def tcbCTableSlot_def
                        Kernel_C.tcbCTable_def tcbCNodeEntries_def
                        bit.conj_disj_distrib2
                        word_bw_assocs)
       apply (simp add: objBits_simps ctcb_ptr_to_tcb_ptr_def)
       apply (frule is_aligned_add_helper[where p="tcbptr - ctcb_offset" and d=ctcb_offset for tcbptr])
        apply (simp add: ctcb_offset_defs objBits_defs)
       apply (simp add: mask_def objBits_defs)
      apply (simp add: cap_get_tag_isCap)
     apply wp+
   apply (rule ccorres_if_lhs)
    apply (simp add: Let_def)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: return_def ccap_relation_NullCap_iff)
   apply (simp add: isArchCap_T_isArchObjectCap[symmetric]
               del: Collect_const)
   apply (rule ccorres_if_lhs)
    apply (simp add: Collect_False Collect_True Let_def
                del: Collect_const)
    apply (rule_tac P="(capIRQ cap) \<le>  RISCV64.maxIRQ" in ccorres_gen_asm)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
      apply (rule_tac xf'=irq_' in ccorres_abstract,ceqv)
      apply (rule_tac P="rv' = ucast (capIRQ cap)" in ccorres_gen_asm2)
      apply (ctac(no_vcg) add: deletingIRQHandler_ccorres)
       apply (rule ccorres_from_vcg_throws[where P=\<top> ])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
       apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
       apply (simp add: ccap_relation_NullCap_iff split: if_split)
      apply wp
   apply (rule ccorres_if_lhs)
    apply simp
    apply (rule ccorres_fail)
   apply (rule ccorres_add_return, rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
       apply (rule ccorres_Cond_rhs)
        apply (simp add: ccorres_cond_iffs)
        apply (rule ccorres_return_Skip)
       apply (rule ccorres_Cond_rhs)
        apply (simp add: ccorres_cond_iffs)
        apply (rule ccorres_return_Skip)
       apply (rule ccorres_Cond_rhs)
        apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
        apply simp
       apply (rule ccorres_Cond_rhs)
        apply (simp add: ccorres_cond_iffs)
        apply (rule ccorres_return_Skip)
       apply (simp add: ccorres_cond_iffs)
       apply (rule ccorres_return_Skip)
      apply (rule ceqv_refl)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def ccap_relation_NullCap_iff
                           irq_opt_relation_def)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap word_sle_def Collect_const_mem)
  apply (intro impI conjI)
                apply (clarsimp split: bool.splits)
               apply (clarsimp split: bool.splits)
              apply (clarsimp simp: valid_cap'_def isCap_simps)
             apply (clarsimp simp: isCap_simps capRange_def capAligned_def)
            apply (clarsimp simp: isCap_simps valid_cap'_def)
           apply (clarsimp simp: isCap_simps capRange_def capAligned_def)
          apply (clarsimp simp: isCap_simps valid_cap'_def )
         apply clarsimp
        apply (clarsimp simp: isCap_simps valid_cap'_def )
       apply (clarsimp simp: tcb_ptr_to_ctcb_ptr_def ccap_relation_def isCap_simps
                             c_valid_cap_def cap_thread_cap_lift_def cap_to_H_def
                             ctcb_ptr_to_tcb_ptr_def Let_def
                    split: option.splits cap_CL.splits if_splits)
      apply clarsimp
      apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
      apply (clarsimp simp: isCap_simps)
     apply (clarsimp simp: tcb_cnode_index_defs ptr_add_assertion_def)
    apply clarsimp
    apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
    apply (frule(1) ccap_relation_IRQHandler_mask)
    apply (clarsimp simp: isCap_simps irqInvalid_def valid_cap'_def)
    apply (rule irq_opt_relation_Some_ucast)
      apply fastforce
     apply (simp add: irqInvalid_def)
    apply (simp add: Kernel_C.maxIRQ_def maxIRQ_def)
   apply fastforce
  apply clarsimp
  apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap [THEN iffD2])
  apply (frule(1) ccap_relation_IRQHandler_mask)
  apply (clarsimp simp add:mask_eq_ucast_eq)
  done *)

end

end
