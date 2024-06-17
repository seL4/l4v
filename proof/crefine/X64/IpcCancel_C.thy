(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IpcCancel_C
imports SyscallArgs_C
begin

context kernel_m
begin

lemma cready_queues_index_to_C_in_range':
  assumes prems: "qdom \<le> maxDomain" "prio \<le> maxPriority"
  shows "cready_queues_index_to_C qdom prio < num_tcb_queues"
proof -
  have P: "unat prio < numPriorities"
    using prems
    by (simp add: numPriorities_def Suc_le_lessD unat_le_helper maxDomain_def maxPriority_def)
  have Q: "unat qdom < numDomains"
    using prems
    by (simp add: maxDom_to_H le_maxDomain_eq_less_numDomains word_le_nat_alt)
  show ?thesis
    using mod_lemma[OF _ P, where q="unat qdom" and c=numDomains] Q
    by (clarsimp simp: num_tcb_queues_calculation cready_queues_index_to_C_def field_simps)
qed

lemmas cready_queues_index_to_C_in_range =
  cready_queues_index_to_C_in_range'[simplified num_tcb_queues_val]

lemma cready_queues_index_to_C_inj:
  "\<lbrakk> cready_queues_index_to_C qdom prio = cready_queues_index_to_C qdom' prio';
     prio \<le> maxPriority; prio' \<le> maxPriority \<rbrakk> \<Longrightarrow> prio = prio' \<and> qdom = qdom'"
  apply (rule context_conjI)
  apply (auto simp: cready_queues_index_to_C_def numPriorities_def maxPriority_def
                    seL4_MaxPrio_def word_le_nat_alt dest: arg_cong[where f="\<lambda>x. x mod 256"])
  done

lemma cready_queues_index_to_C_distinct:
  "\<lbrakk> qdom = qdom' \<longrightarrow> prio \<noteq> prio'; prio \<le> maxPriority; prio' \<le> maxPriority \<rbrakk>
   \<Longrightarrow> cready_queues_index_to_C qdom prio \<noteq> cready_queues_index_to_C qdom' prio'"
  apply (auto simp: cready_queues_index_to_C_inj)
  done

lemma cmap_relation_drop_fun_upd:
  "\<lbrakk> cm x = Some v; \<And>v''. rel v'' v = rel v'' v' \<rbrakk>
      \<Longrightarrow> cmap_relation am (cm (x \<mapsto> v')) f rel
            = cmap_relation am cm f rel"
  apply (simp add: cmap_relation_def)
  apply (rule conj_cong[OF refl])
  apply (rule ball_cong[OF refl])
  apply (auto split: if_split)
  done

lemma ntfn_ptr_get_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> \<sigma> \<Turnstile>\<^sub>c \<^bsup>\<sigma>\<^esup>ntfnPtr} \<acute>ret__struct_tcb_queue_C :== PROC ntfn_ptr_get_queue(\<acute>ntfnPtr)
       \<lbrace>head_C \<acute>ret__struct_tcb_queue_C = Ptr (ntfnQueue_head_CL (notification_lift (the (cslift s \<^bsup>s\<^esup>ntfnPtr)))) \<and>
        end_C \<acute>ret__struct_tcb_queue_C = Ptr (ntfnQueue_tail_CL (notification_lift (the (cslift s \<^bsup>s\<^esup>ntfnPtr))))\<rbrace>"
  apply vcg
  apply clarsimp
  done

(* Although tcb_C contains an user_fpu_state_C field,
   none of the uses of this abbreviation involve modifying
   any user_fpu_state_C within a tcb_C.
   It is therefore convenient to include user_fpu_state_C here
   to cover preservation of the global FPU null state. *)
abbreviation
  "cslift_all_but_tcb_C s t \<equiv> (cslift s :: cte_C typ_heap) = cslift t
          \<and> (cslift s :: endpoint_C typ_heap) = cslift t
          \<and> (cslift s :: notification_C typ_heap) = cslift t
          \<and> (cslift s :: asid_pool_C typ_heap) = cslift t
          \<and> (cslift s :: pte_C typ_heap) = cslift t
          \<and> (cslift s :: pde_C typ_heap) = cslift t
          \<and> (cslift s :: pdpte_C typ_heap) = cslift t
          \<and> (cslift s :: pml4e_C typ_heap) = cslift t
          \<and> (cslift s :: user_data_C typ_heap) = cslift t
          \<and> (cslift s :: user_data_device_C typ_heap) = cslift t
          \<and> (cslift s :: ioport_table_C typ_heap) = cslift t
          \<and> (cslift s :: user_fpu_state_C typ_heap) = cslift t"

lemma tcbEPDequeue_spec:
  "\<forall>s queue. \<Gamma> \<turnstile> \<lbrace>s. \<exists>t. (t, s) \<in> rf_sr
               \<and> (\<forall>tcb\<in>set queue. tcb_at' tcb t) \<and> distinct queue
               \<and> (ctcb_ptr_to_tcb_ptr \<acute>tcb \<in> set queue)
               \<and> ep_queue_relation' (cslift s) queue (head_C \<acute>queue) (end_C \<acute>queue) \<rbrace>
            Call tcbEPDequeue_'proc
            {t. (head_C (ret__struct_tcb_queue_C_' t) =
                 (if (tcbEPPrev_C (the (cslift s (\<^bsup>s\<^esup>tcb)))) = NULL then
                    (tcbEPNext_C (the (cslift s (\<^bsup>s\<^esup>tcb))))
                 else
                    (head_C \<^bsup>s\<^esup>queue)))
              \<and> (end_C (ret__struct_tcb_queue_C_' t) =
                 (if (tcbEPNext_C (the (cslift s (\<^bsup>s\<^esup>tcb)))) = NULL then
                    (tcbEPPrev_C (the (cslift s (\<^bsup>s\<^esup>tcb))))
                 else
                    (end_C \<^bsup>s\<^esup>queue)))
              \<and> (ep_queue_relation' (cslift t)
                                    (Lib.delete (ctcb_ptr_to_tcb_ptr \<^bsup>s\<^esup>tcb) queue)
                                    (head_C (ret__struct_tcb_queue_C_' t))
                                    (end_C (ret__struct_tcb_queue_C_' t))
                \<and> (cslift t |` (- tcb_ptr_to_ctcb_ptr ` set queue)) =
                  (cslift s |` (- tcb_ptr_to_ctcb_ptr ` set queue))
                \<and> option_map tcb_null_ep_ptrs \<circ> (cslift t) =
                  option_map tcb_null_ep_ptrs \<circ> (cslift s))
                \<and> cslift_all_but_tcb_C t s
                \<and> (\<forall>rs. zero_ranges_are_zero rs (\<^bsup>t\<^esup>t_hrs)
                    = zero_ranges_are_zero rs (\<^bsup>s\<^esup>t_hrs))
                \<and> (hrs_htd \<^bsup>t\<^esup>t_hrs) = (hrs_htd \<^bsup>s\<^esup>t_hrs)}"
  apply (intro allI)
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp split del: if_split)
  apply (frule (4) tcb_queue_valid_ptrsD [OF _ _ _ _ tcb_queue_relation'_queue_rel])
  apply (elim conjE exE)
  apply (frule (3) tcbEPDequeue_update)
   apply simp
  apply (unfold upd_unless_null_def)
  apply (frule (2) tcb_queue_relation_ptr_rel' [OF tcb_queue_relation'_queue_rel])
    prefer 2
    apply assumption
   apply simp
  apply (frule c_guard_clift)
  apply (simp add: typ_heap_simps')
  apply (intro allI conjI impI)
            apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff)
           apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff
                           cong: if_weak_cong)
          apply (rule ext)
          apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def)
         apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff c_guard_clift)
        apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff)
       apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def
                       cong: if_weak_cong)
      apply (rule ext)
      apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def)
     apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff c_guard_clift)
    apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff
                    cong: if_weak_cong)
   apply (rule ext)
   apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def)
  apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff c_guard_clift)
  done

lemma ntfn_ptr_set_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. s \<Turnstile>\<^sub>c \<acute>ntfnPtr\<rbrace> Call ntfn_ptr_set_queue_'proc
           {t. (\<exists>ntfn'. notification_lift ntfn' =
  (notification_lift (the (cslift s (\<^bsup>s\<^esup>ntfnPtr))))\<lparr>
    ntfnQueue_head_CL := sign_extend 47 (ptr_val (head_C \<^bsup>s\<^esup>ntfn_queue)),
    ntfnQueue_tail_CL := sign_extend 47 (ptr_val (end_C \<^bsup>s\<^esup>ntfn_queue)) \<rparr>
            \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (\<^bsup>s\<^esup>ntfnPtr) ntfn')
                (t_hrs_' (globals s)))}"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: packed_heap_update_collapse_hrs typ_heap_simps')
  done


lemma cancelSignal_ccorres_helper:
  "ccorres dc xfdc (invs' and st_tcb_at' ((=) (BlockedOnNotification ntfn)) thread and ko_at' ntfn' ntfn)
        UNIV
        []
        (setNotification ntfn (ntfnObj_update
          (\<lambda>_. if remove1 thread (ntfnQueue (ntfnObj ntfn')) = []
           then ntfn.IdleNtfn
           else ntfnQueue_update (\<lambda>_. remove1 thread (ntfnQueue (ntfnObj ntfn'))) (ntfnObj ntfn')) ntfn'))
        (\<acute>ntfn_queue :== CALL ntfn_ptr_get_queue(Ptr ntfn);;
         \<acute>ntfn_queue :== CALL tcbEPDequeue(tcb_ptr_to_ctcb_ptr thread,\<acute>ntfn_queue);;
         CALL ntfn_ptr_set_queue(Ptr ntfn,\<acute>ntfn_queue);;
         IF head_C \<acute>ntfn_queue = NULL THEN
           CALL notification_ptr_set_state(Ptr ntfn,
           scast NtfnState_Idle)
         FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp split del: if_split)
  apply (frule (2) ntfn_blocked_in_queueD)
  apply (frule (1) ko_at_valid_ntfn' [OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) valid_ntfn_isWaitingNtfnD)
  apply (elim conjE)
  apply (frule cmap_relation_ntfn)
  apply (erule (1) cmap_relation_ko_atE)
  apply (rule conjI)
   apply (erule h_t_valid_clift)
  apply (rule impI)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x = \<sigma> in exI)
   apply (intro conjI, assumption+)
   apply (drule (2) ntfn_to_ep_queue)
   apply (simp add: tcb_queue_relation'_def)
  apply (clarsimp simp: typ_heap_simps cong: imp_cong split del: if_split)
  apply (frule null_ep_queue [simplified comp_def])
  apply (intro impI conjI allI)
   \<comment> \<open>empty case\<close>
   apply clarsimp
   apply (frule iffD1 [OF tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel]])
     apply (rule ballI, erule bspec)
     apply (erule subsetD [rotated])
     apply clarsimp
    apply simp
   apply (simp add: setNotification_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: remove1_empty rf_sr_def cstate_relation_def Let_def
                        cpspace_relation_def update_ntfn_map_tos
                        typ_heap_simps')
       apply (elim conjE)
       apply (intro conjI)
           \<comment> \<open>tcb relation\<close>
           apply (erule ctcb_relation_null_ep_ptrs)
           apply (clarsimp simp: comp_def)
          \<comment> \<open>ep relation\<close>
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule cendpoint_relation_ntfn_queue [OF invs_sym'], assumption+)
          apply simp
          apply (erule (1) map_to_ko_atI')
         \<comment> \<open>ntfn relation\<close>
         apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
         apply (simp add: cnotification_relation_def Let_def NtfnState_Idle_def)
         apply (simp add: carch_state_relation_def carch_globals_def)
        apply (clarsimp simp: carch_state_relation_def carch_globals_def
                              typ_heap_simps' packed_heap_update_collapse_hrs
                              fpu_null_state_heap_update_tag_disj_simps
                       elim!: fpu_null_state_typ_heap_preservation)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps')
    apply (simp add: objBits_simps)
   apply assumption
  \<comment> \<open>non empty case\<close>
  apply (frule tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel])
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
   apply clarsimp
  apply (simp add: setNotification_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (frule (1) st_tcb_at_h_t_valid)
      apply (simp add: remove1_empty rf_sr_def cstate_relation_def Let_def
                       cpspace_relation_def update_ntfn_map_tos
                       typ_heap_simps')
      apply (elim conjE)
      apply (intro conjI)
           \<comment> \<open>tcb relation\<close>
          apply (erule ctcb_relation_null_ep_ptrs)
          apply (clarsimp simp: comp_def)
         \<comment> \<open>ep relation\<close>
         apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
         apply simp
         apply (rule cendpoint_relation_ntfn_queue)
             apply fastforce
            apply assumption+
         apply simp
         apply (erule (1) map_to_ko_atI')
         \<comment> \<open>ntfn relation\<close>
        apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
         apply (simp add: cnotification_relation_def Let_def isWaitingNtfn_def
                   split: ntfn.splits split del: if_split)
         apply (erule iffD1 [OF tcb_queue_relation'_cong [OF refl _ _ refl], rotated -1])
          apply (clarsimp simp add: h_t_valid_clift_Some_iff)
          apply (subst tcb_queue_relation'_next_sign; assumption?)
           apply fastforce
          apply (simp add: notification_lift_def sign_extend_sign_extend_eq)
         apply (clarsimp simp: h_t_valid_clift_Some_iff notification_lift_def sign_extend_sign_extend_eq)
         apply (subst tcb_queue_relation'_prev_sign; assumption?)
          apply fastforce
         apply simp
        apply simp
       subgoal by (clarsimp simp: carch_state_relation_def carch_globals_def
                                  fpu_null_state_heap_update_tag_disj_simps
                                  global_ioport_bitmap_heap_update_tag_disj_simps
                           elim!: fpu_null_state_typ_heap_preservation)
      subgoal by (simp add: cmachine_state_relation_def)
     subgoal by (simp add: h_t_valid_clift_Some_iff)
    subgoal by (simp add: objBits_simps')
   subgoal by (simp add: objBits_simps)
  by assumption

lemmas rf_sr_tcb_update_no_queue_gen
    = rf_sr_tcb_update_no_queue[where t="t''\<lparr> globals := gs \<lparr> t_hrs_' := th \<rparr>\<rparr>" for th, simplified]

lemma threadSet_tcbState_simple_corres:
  "ccorres dc xfdc (tcb_at' thread)
        {s. (\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := v64_' s && mask 4\<rparr>, fl)) \<and>
           thread_state_ptr_' s = Ptr &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C''])} []
        (threadSet (tcbState_update (\<lambda>_. st)) thread)  (Call thread_state_ptr_set_tsType_'proc)"
  apply (rule threadSet_corres_lemma)
  apply (rule thread_state_ptr_set_tsType_spec)
  apply (rule thread_state_ptr_set_tsType_modifies)
   apply clarsimp
   apply (frule (1) obj_at_cslift_tcb)
   apply (clarsimp simp: typ_heap_simps')
   apply (rule rf_sr_tcb_update_no_queue_gen, assumption+, simp, simp_all)
    apply (rule ball_tcb_cte_casesI, simp_all)
    apply (frule cmap_relation_tcb)
    apply (frule (1) cmap_relation_ko_atD)
    apply clarsimp
    apply (simp add: ctcb_relation_def cthread_state_relation_def)
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps)
  done

lemma ko_at_obj_congD':
  "\<lbrakk>ko_at' k p s; ko_at' k' p s\<rbrakk> \<Longrightarrow> k = k'"
  apply (erule obj_atE')+
  apply simp
  done

lemma threadGet_vcg_corres_P:
  assumes c: "\<And>x. \<forall>\<sigma>. \<Gamma>\<turnstile> {s. (\<sigma>, s) \<in> rf_sr
                       \<and> tcb_at' thread \<sigma> \<and> P \<sigma>
                       \<and> (\<forall>tcb. ko_at' tcb thread \<sigma> \<longrightarrow> (\<exists>tcb'.
                       x = f tcb \<and> cslift s (tcb_ptr_to_ctcb_ptr thread) = Some tcb'
                       \<and> ctcb_relation tcb tcb'))} c {s. (\<sigma>, s) \<in> rf_sr \<and> r x (xf s)}"
  shows "ccorres r xf P UNIV hs (threadGet f thread) c"
  apply (rule ccorres_add_return2)
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_pre_threadGet)
  apply (rule_tac P = "\<lambda>\<sigma>. \<exists>tcb. ko_at' tcb thread \<sigma> \<and> x = f tcb \<and> P \<sigma>"
    and P' = UNIV in ccorres_from_vcg)
   apply (simp add: return_def)
   apply (rule allI, rule conseqPre)
   apply (rule spec [OF c])
   apply clarsimp
   apply (frule cmap_relation_tcb)
   apply (frule (1) cmap_relation_ko_atD)
   apply clarsimp
   apply (rule conjI)
    apply (erule obj_at'_weakenE)
    apply simp
   apply clarsimp
   apply (drule (1) ko_at_obj_congD')
   apply simp
  apply fastforce
  done

lemmas threadGet_vcg_corres = threadGet_vcg_corres_P[where P=\<top>]

lemma threadGet_specs_corres:
  assumes spec: "\<forall>s. \<Gamma> \<turnstile> {s} Call g {t. xf t = f' s}"
  and      mod: "modifies_spec g"
  and       xf: "\<And>f s. xf (globals_update f s) = xf s"
  shows "ccorres r xf (ko_at' ko thread) {s'. r (f ko) (f' s')} hs (threadGet f thread) (Call g)"
  apply (rule ccorres_Call_call_for_vcg)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return2)
   apply (rule ccorres_pre_threadGet)
   apply (rule_tac P = "\<lambda>s. ko_at' ko thread s \<and> x = f ko" in ccorres_from_vcg [where P' = "{s'. r (f ko) (f' s')}"])
   apply (rule allI)
    apply (rule HoarePartial.ProcModifyReturnNoAbr [where return' = "\<lambda>s t. t\<lparr> globals := globals s \<rparr>"])
      apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ spec])
      defer
      apply vcg
     prefer 2
     apply (rule mod)
    apply (clarsimp simp: mex_def meq_def)
    apply (frule obj_at'_weakenE [OF _ TrueI])
   apply clarsimp
   apply (drule (1) ko_at_obj_congD')
   apply simp
  apply (clarsimp simp: return_def)
  apply (rule conjI)
   apply (erule iffD1 [OF rf_sr_upd, rotated -1], simp_all)[1]
  apply (simp add: xf)
  done

lemma ccorres_exI1:
  assumes rl: "\<And>x. ccorres r xf (Q x) (P' x) hs a c"
  shows   "ccorres r xf (\<lambda>s. (\<exists>x. P x s) \<and> (\<forall>x. P x s \<longrightarrow> Q x s))
                        {s'. \<forall>x s. (s, s') \<in> rf_sr \<and> P x s \<longrightarrow> s' \<in> P' x} hs a c"
  apply (rule ccorresI')
  apply clarsimp
  apply (drule spec, drule (1) mp)
  apply (rule ccorresE [OF rl], assumption+)
    apply fastforce
   apply assumption
   apply assumption
  apply fastforce
  done

lemma isStopped_ccorres [corres]:
  "ccorres (\<lambda>r r'. r = to_bool r') ret__unsigned_long_'
  (tcb_at' thread) (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread})  []
  (isStopped thread) (Call isStopped_'proc)"
  apply (cinit lift: thread_' simp: getThreadState_def)
  apply (rule ccorres_pre_threadGet)
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_cond_weak)
      apply (rule ccorres_return_C)
        apply simp
       apply simp
      apply simp
     apply (simp add: ccorres_cond_iffs)
     apply (rule ccorres_return_C)
       apply simp
      apply simp
     apply simp
    apply vcg
   apply (rule conseqPre)
   apply vcg
   apply clarsimp
  apply clarsimp
  apply (clarsimp simp: typ_heap_simps ctcb_relation_thread_state_to_tsType
                 split: thread_state.splits)
    apply (simp add: ThreadState_defs)+
  done

lemma isRunnable_ccorres [corres]:
  "ccorres (\<lambda>r r'. r = to_bool r') ret__unsigned_long_'
  (tcb_at' thread) (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread})  []
  (isRunnable thread) (Call isRunnable_'proc)"
  apply (cinit lift: thread_' simp: getThreadState_def)
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule ccorres_pre_threadGet)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_cond_weak)
     apply (rule ccorres_return_C)
        apply (simp)
       apply (simp)
      apply (simp)
     apply (simp add: ccorres_cond_iffs)
     apply (rule ccorres_return_C)
       apply (simp)
      apply (simp)
     apply (simp)
    apply (vcg)
   apply (rule conseqPre)
    apply (vcg)
   apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp simp: typ_heap_simps ctcb_relation_thread_state_to_tsType
                 split: thread_state.splits)
       apply (simp add: ThreadState_defs)+
  done

lemma tcb_ptr_to_ctcb_ptr_imageD:
  "x \<in> tcb_ptr_to_ctcb_ptr ` S \<Longrightarrow> ctcb_ptr_to_tcb_ptr x \<in> S"
  apply (erule imageE)
  apply simp
  done

lemma ctcb_ptr_to_tcb_ptr_imageI:
  "ctcb_ptr_to_tcb_ptr x \<in> S \<Longrightarrow> x \<in> tcb_ptr_to_ctcb_ptr ` S"
  apply (drule imageI [where f = tcb_ptr_to_ctcb_ptr])
  apply simp
  done

lemma ctcb_relation_unat_prio_eq:
  "ctcb_relation tcb tcb' \<Longrightarrow> unat (tcbPriority tcb) = unat (tcbPriority_C tcb')"
  apply (clarsimp simp: ctcb_relation_def)
  apply (erule_tac t = "tcbPriority_C tcb'" in subst)
  apply simp
  done

lemma ctcb_relation_unat_dom_eq:
  "ctcb_relation tcb tcb' \<Longrightarrow> unat (tcbDomain tcb) = unat (tcbDomain_C tcb')"
  apply (clarsimp simp: ctcb_relation_def)
  apply (erule_tac t = "tcbDomain_C tcb'" in subst)
  apply simp
  done

lemma threadSet_queued_ccorres [corres]:
  shows "ccorres dc xfdc (tcb_at' thread)
        {s. v64_' s = from_bool v \<and> thread_state_ptr_' s = Ptr &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C''])} []
        (threadSet (tcbQueued_update (\<lambda>_. v)) thread)
        (Call thread_state_ptr_set_tcbQueued_'proc)"
  apply (rule threadSet_corres_lemma)
     apply (rule thread_state_ptr_set_tcbQueued_spec)
    apply (rule thread_state_ptr_set_tcbQueued_modifies)
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

(* FIXME: move *)
lemma cmap_relation_no_upd:
  "\<lbrakk> cmap_relation a c f rel; a p = Some ko; rel ko v; inj f \<rbrakk> \<Longrightarrow> cmap_relation a (c(f p \<mapsto> v)) f rel"
  apply (clarsimp simp: cmap_relation_def)
  apply (subgoal_tac "f p \<in> dom c")
   prefer 2
   apply (drule_tac t="dom c" in sym)
   apply fastforce
  apply clarsimp
  apply (drule (1) injD)
  apply simp
  done

(* FIXME: move *)
lemma cmap_relation_rel_upd:
  "\<lbrakk> cmap_relation a c f rel; \<And>v v'. rel v v' \<Longrightarrow> rel' v v' \<rbrakk> \<Longrightarrow> cmap_relation a c f rel'"
  by (simp add: cmap_relation_def)

declare fun_upd_restrict_conv[simp del]

lemmas queue_in_range = of_nat_mono_maybe[OF _ cready_queues_index_to_C_in_range,
        where 'a=32, unfolded cready_queues_index_to_C_def numPriorities_def,
        simplified, unfolded ucast_nat_def]
    of_nat_mono_maybe[OF _ cready_queues_index_to_C_in_range,
        where 'a="32 signed", unfolded cready_queues_index_to_C_def numPriorities_def,
        simplified, unfolded ucast_nat_def]
    of_nat_mono_maybe[OF _ cready_queues_index_to_C_in_range,
        where 'a=64, unfolded cready_queues_index_to_C_def numPriorities_def,
        simplified, unfolded ucast_nat_def]

lemma cready_queues_index_to_C_def2:
  "\<lbrakk> qdom \<le> maxDomain; prio \<le> maxPriority \<rbrakk>
   \<Longrightarrow> cready_queues_index_to_C qdom prio
             = unat (ucast qdom * of_nat numPriorities + ucast prio :: machine_word)"
  using numPriorities_machine_word_safe
  apply -
  apply (frule (1) cready_queues_index_to_C_in_range[simplified maxDom_to_H maxPrio_to_H])
  apply (subst unat_add_lem[THEN iffD1])
   apply (auto simp: unat_mult_simple cready_queues_index_to_C_def)
  done

lemma ready_queues_index_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s'. s' = s \<and> (Kernel_Config.numDomains \<le> 1 \<longrightarrow> dom_' s' = 0)}
       Call ready_queues_index_'proc
       \<lbrace>\<acute>ret__unsigned_long = (dom_' s) * word_of_nat numPriorities + (prio_' s)\<rbrace>"
  by vcg (simp add: numDomains_sge_1_simp numPriorities_def)

lemma prio_to_l1index_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call prio_to_l1index_'proc
       \<lbrace>\<acute>ret__unsigned_long = prio_' s >> wordRadix \<rbrace>"
  by vcg (simp add: word_sle_def wordRadix_def')

lemma invert_l1index_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call invert_l1index_'proc
       \<lbrace>\<acute>ret__unsigned_long = of_nat l2BitmapSize - 1 - l1index_' s \<rbrace>"
  unfolding l2BitmapSize_def'
  by vcg
     (simp add: word_sle_def sdiv_int_def sdiv_word_def smod_word_def smod_int_def)

lemma cbitmap_L1_relation_update:
  "\<lbrakk> (\<sigma>, s) \<in> rf_sr ; cbitmap_L1_relation cupd aupd \<rbrakk>
   \<Longrightarrow> (\<sigma>\<lparr>ksReadyQueuesL1Bitmap := aupd \<rparr>,
       globals_update (ksReadyQueuesL1Bitmap_'_update (\<lambda>_. cupd)) s)
      \<in> rf_sr"
  by (simp add: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                cmachine_state_relation_def)

lemma cbitmap_L2_relation_update:
  "\<lbrakk> (\<sigma>, s) \<in> rf_sr ; cbitmap_L2_relation cupd aupd \<rbrakk>
   \<Longrightarrow> (\<sigma>\<lparr>ksReadyQueuesL2Bitmap := aupd \<rparr>,
       globals_update (ksReadyQueuesL2Bitmap_'_update (\<lambda>_. cupd)) s)
      \<in> rf_sr"
  by (simp add: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                cmachine_state_relation_def)

lemma cready_queues_index_to_C_ucast_helper:
  fixes p :: priority
  fixes d :: domain
  shows "unat (ucast d * 0x100 + ucast p :: machine_word) = unat d * 256 + unat p"
  unfolding tcb_queue_relation'_def maxPriority_def numPriorities_def
  using unat_lt2p[where x=p] unat_lt2p[where x=d]
  by (clarsimp simp: cready_queues_index_to_C_def word_le_nat_alt unat_word_ariths)

lemmas prio_and_dom_limit_helpers =
  prio_ucast_shiftr_wordRadix_helper
  prio_ucast_shiftr_wordRadix_helper'
  prio_ucast_shiftr_wordRadix_helper2
  prio_ucast_shiftr_wordRadix_helper3
  prio_unat_shiftr_wordRadix_helper'
  cready_queues_index_to_C_ucast_helper
  unat_ucast_prio_L1_cmask_simp
  machine_word_and_3F_less_40

(* FIXME MOVE *)
lemma rf_sr_cbitmap_L1_relation[intro]:
  "(\<sigma>, x) \<in> rf_sr \<Longrightarrow> cbitmap_L1_relation (ksReadyQueuesL1Bitmap_' (globals x)) (ksReadyQueuesL1Bitmap \<sigma>)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

(* FIXME MOVE *)
lemma rf_sr_cbitmap_L2_relation[intro]:
  "(\<sigma>, x) \<in> rf_sr \<Longrightarrow> cbitmap_L2_relation (ksReadyQueuesL2Bitmap_' (globals x)) (ksReadyQueuesL2Bitmap \<sigma>)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma cbitmap_L1_relation_bit_set:
  fixes p :: priority
  shows
  "\<lbrakk> cbitmap_L1_relation (ksReadyQueuesL1Bitmap_' (globals x)) (ksReadyQueuesL1Bitmap \<sigma>) ;
     d \<le> maxDomain \<rbrakk> \<Longrightarrow>
   cbitmap_L1_relation
           (Arrays.update (ksReadyQueuesL1Bitmap_' (globals x)) (unat d)
             (ksReadyQueuesL1Bitmap_' (globals x).[unat d] || 2 ^ unat (p >> wordRadix)))
           ((ksReadyQueuesL1Bitmap \<sigma>)(d := ksReadyQueuesL1Bitmap \<sigma> d || 2 ^ prioToL1Index p))"
  apply (unfold cbitmap_L1_relation_def)
  apply (clarsimp simp: le_maxDomain_eq_less_numDomains word_le_nat_alt prioToL1Index_def
                        num_domains_index_updates)
  done

lemma cbitmap_L2_relation_bit_set:
  fixes p :: priority
  fixes d :: domain
  shows "\<lbrakk> cbitmap_L2_relation (ksReadyQueuesL2Bitmap_' (globals \<sigma>')) (ksReadyQueuesL2Bitmap \<sigma>) ;
           d \<le> maxDomain ; b = b' \<rbrakk>
         \<Longrightarrow>
         cbitmap_L2_relation
          (Arrays.update (ksReadyQueuesL2Bitmap_' (globals \<sigma>')) (unat d)
            (Arrays.update (ksReadyQueuesL2Bitmap_' (globals \<sigma>').[unat d])
              (invertL1Index (prioToL1Index p))
              (ksReadyQueuesL2Bitmap_' (globals \<sigma>').[unat d].[invertL1Index (prioToL1Index p)] ||
               2 ^ unat (p && b))))
          ((ksReadyQueuesL2Bitmap \<sigma>)
           ((d, invertL1Index (prioToL1Index p)) :=
              ksReadyQueuesL2Bitmap \<sigma> (d, invertL1Index (prioToL1Index p)) ||
               2 ^ unat (p && b')))"
  unfolding cbitmap_L2_relation_def numPriorities_def wordBits_def word_size l2BitmapSize_def'
  apply (clarsimp simp: word_size prioToL1Index_def wordRadix_def mask_def
                        invertL1Index_def l2BitmapSize_def'
                        le_maxDomain_eq_less_numDomains word_le_nat_alt)
  apply (case_tac "da = d" ; clarsimp simp: num_domains_index_updates)
  done

lemma invert_prioToL1Index_c_simp:
  "p \<le> maxPriority
   \<Longrightarrow>
   unat ((of_nat l2BitmapSize :: machine_word) - 1 - (ucast p >> wordRadix))
   = invertL1Index (prioToL1Index p)"
   unfolding maxPriority_def l2BitmapSize_def' invertL1Index_def prioToL1Index_def
     numPriorities_def
   by (simp add: unat_sub prio_and_dom_limit_helpers)

lemma c_invert_assist: "3 - (ucast (p :: priority) >> 6 :: machine_word) < 4"
  using prio_ucast_shiftr_wordRadix_helper'[simplified wordRadix_def]
  by - (rule word_less_imp_diff_less, simp_all)

lemma addToBitmap_ccorres:
  "ccorres dc xfdc
     (K (tdom \<le> maxDomain \<and> prio \<le> maxPriority)) (\<lbrace>\<acute>dom = ucast tdom\<rbrace> \<inter> \<lbrace>\<acute>prio = ucast prio\<rbrace>) hs
     (addToBitmap tdom prio) (Call addToBitmap_'proc)"
  supply prio_and_dom_limit_helpers[simp] invert_prioToL1Index_c_simp[simp]
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply clarsimp
  apply (frule maxDomain_le_unat_ucast_explicit)
  apply (clarsimp simp: getQueue_def gets_def get_def setQueue_def modify_def
                        put_def bind_def return_def bitmap_fun_defs)
  apply (intro conjI impI allI)
   apply (fastforce simp: c_invert_assist l2BitmapSize_def' wordRadix_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        carch_state_relation_def cmachine_state_relation_def)
  apply (rule conjI)
   apply (clarsimp intro!: cbitmap_L1_relation_bit_set)
  apply (fastforce dest!: cbitmap_L2_relation_bit_set simp: wordRadix_def mask_def)
  done

lemma rf_sr_tcb_update_twice:
  "h_t_valid (hrs_htd (hrs2 (globals s') (t_hrs_' (gs2 (globals s'))))) c_guard
      (ptr (t_hrs_' (gs2 (globals s'))) (globals s'))
    \<Longrightarrow> ((s, globals_update (\<lambda>gs. t_hrs_'_update (\<lambda>ths.
        hrs_mem_update (heap_update (ptr ths gs :: tcb_C ptr) (v ths gs))
            (hrs_mem_update (heap_update (ptr ths gs) (v' ths gs)) (hrs2 gs ths))) (gs2 gs)) s') \<in> rf_sr)
    = ((s, globals_update (\<lambda>gs. t_hrs_'_update (\<lambda>ths.
        hrs_mem_update (heap_update (ptr ths gs) (v ths gs)) (hrs2 gs ths)) (gs2 gs)) s') \<in> rf_sr)"
  by (simp add: rf_sr_def cstate_relation_def Let_def
                cpspace_relation_def typ_heap_simps'
                carch_state_relation_def cmachine_state_relation_def
                packed_heap_update_collapse_hrs)

lemmas rf_sr_tcb_update_no_queue_gen2 =
  rf_sr_obj_update_helper[OF rf_sr_tcb_update_no_queue_gen, simplified]

lemma tcb_queue_prepend_ccorres:
  "ccorres ctcb_queue_relation ret__struct_tcb_queue_C_'
     (\<lambda>s. tcb_at' tcbPtr s
          \<and> (tcbQueueHead queue \<noteq> None \<longleftrightarrow> tcbQueueEnd queue \<noteq> None)
          \<and> (\<forall>head. tcbQueueHead queue = Some head \<longrightarrow> tcb_at' head s))
     (\<lbrace>ctcb_queue_relation queue \<acute>queue\<rbrace> \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace>) hs
     (tcbQueuePrepend queue tcbPtr) (Call tcb_queue_prepend_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply if_split[split del]
  apply (cinit lift: tcb_')
   \<comment> \<open>cinit is not able to lift queue_' because queue_' is later modified in the C program\<close>
   apply (rule_tac xf'=queue_' in ccorres_abstract, ceqv, rename_tac cqueue)
   apply (rule_tac P="ctcb_queue_relation queue cqueue" in ccorres_gen_asm2)
   apply (rule_tac xf'=ret__unsigned_long_'
               and val="from_bool (tcbQueueEmpty queue)"
               and R="?abs"
               and R'="\<lbrace>\<acute>queue = cqueue\<rbrace>"
                in ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg)
      apply (fastforce dest: tcb_at_not_NULL
                       simp: ctcb_queue_relation_def option_to_ctcb_ptr_def tcbQueueEmpty_def)
     apply ceqv
    apply (rule_tac r'=ctcb_queue_relation and xf'=queue_' in ccorres_split_nothrow)
        apply (rule_tac Q="?abs"
                    and Q'="\<lambda>s'. queue_' s' = cqueue"
                     in ccorres_cond_both')
          apply fastforce
         apply clarsimp
         apply (rule ccorres_return[where R=\<top>])
         apply (rule conseqPre, vcg)
         apply (fastforce simp: ctcb_queue_relation_def option_to_ctcb_ptr_def)
        apply (rule ccorres_seq_skip'[THEN iffD1])
        apply (rule ccorres_rhs_assoc)+
        apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
            apply (rule ccorres_Guard)
            apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s
                                            \<and> head_C cqueue = option_to_ctcb_ptr (tcbQueueHead queue)}"
                        and R="\<lbrace>head_C cqueue = option_to_ctcb_ptr (tcbQueueHead queue)\<rbrace>"
                         in threadSet_ccorres_lemma4[where P=\<top> and P'=\<top>])
             apply (rule conseqPre, vcg)
             apply clarsimp
             apply (frule (1) obj_at_cslift_tcb)
             apply (fastforce intro!: rf_sr_tcb_update_no_queue_gen2
                                simp: typ_heap_simps' tcb_cte_cases_def cteSizeBits_def
                                      ctcb_relation_def option_to_ctcb_ptr_def)
            apply (clarsimp simp: ctcb_relation_def option_to_ctcb_ptr_def split: if_splits)
           apply ceqv
          apply simp
          apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
              apply (rule ccorres_Guard)
              apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr
                                              \<and> ko_at' tcb (the (tcbQueueHead queue)) s
                                              \<and> head_C cqueue = option_to_ctcb_ptr (tcbQueueHead queue)}"
                          and R="\<lbrace>head_C cqueue = option_to_ctcb_ptr (tcbQueueHead queue)\<rbrace>"
                           in threadSet_ccorres_lemma4[where P=\<top> and P'=\<top>])
               apply (rule conseqPre, vcg)
               apply clarsimp
               apply (frule (1) obj_at_cslift_tcb)
               apply (fastforce intro!: rf_sr_tcb_update_no_queue_gen2
                                  simp: typ_heap_simps' tcb_cte_cases_def cteSizeBits_def
                                        ctcb_relation_def option_to_ctcb_ptr_def tcbQueueEmpty_def)
              apply fastforce
             apply ceqv
            apply (rule ccorres_return_Skip')
           apply wpsimp
          apply vcg
         apply wpsimp
        apply vcg
       apply ceqv
      apply csymbr
      apply (fastforce intro: ccorres_return_C')
     apply wpsimp
    apply vcg
   apply clarsimp
   apply (vcg exspec=tcb_queue_empty_modifies)
  apply clarsimp
  apply (frule (1) tcb_at_h_t_valid)
  by (force dest: tcb_at_h_t_valid
            simp: ctcb_queue_relation_def option_to_ctcb_ptr_def tcbQueueEmpty_def)

lemma tcb_queue_append_ccorres:
  "ccorres ctcb_queue_relation ret__struct_tcb_queue_C_'
     (\<lambda>s. tcb_at' tcbPtr s
          \<and> (tcbQueueHead queue \<noteq> None \<longleftrightarrow> tcbQueueEnd queue \<noteq> None)
          \<and> (\<forall>head. tcbQueueHead queue = Some head \<longrightarrow> tcb_at' head s)
          \<and> (\<forall>end. tcbQueueEnd queue = Some end \<longrightarrow> tcb_at' end s))
     (\<lbrace>ctcb_queue_relation queue \<acute>queue\<rbrace> \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace>) hs
     (tcbQueueAppend queue tcbPtr) (Call tcb_queue_append_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply if_split[split del]
  apply (cinit lift: tcb_')
   \<comment> \<open>cinit is not able to lift queue_' because queue_' is later modified in the C program\<close>
   apply (rule_tac xf'=queue_' in ccorres_abstract, ceqv, rename_tac cqueue)
   apply (rule_tac P="ctcb_queue_relation queue cqueue
                      \<and> (tcbQueueHead queue \<noteq> None \<longleftrightarrow> tcbQueueEnd queue \<noteq> None)"
                in ccorres_gen_asm2)
   apply (rule_tac xf'=ret__unsigned_long_'
               and val="from_bool (tcbQueueEmpty queue)"
               and R="?abs"
               and R'="\<lbrace>\<acute>queue = cqueue\<rbrace>"
                in ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg)
      apply (fastforce dest: tcb_at_not_NULL
                       simp: ctcb_queue_relation_def option_to_ctcb_ptr_def tcbQueueEmpty_def)
     apply ceqv
    apply (rule_tac r'=ctcb_queue_relation and xf'=queue_' in ccorres_split_nothrow)
        apply (rule_tac Q="?abs"
                    and Q'="\<lambda>s'. queue_' s' = cqueue"
                     in ccorres_cond_both')
          apply (fastforce dest: tcb_at_not_NULL
                           simp: ctcb_queue_relation_def option_to_ctcb_ptr_def)
         apply clarsimp
         apply (rule ccorres_return[where R=\<top>])
         apply (rule conseqPre, vcg)
         apply (fastforce simp: ctcb_queue_relation_def option_to_ctcb_ptr_def)
        apply (rule ccorres_seq_skip'[THEN iffD1])
        apply (rule ccorres_rhs_assoc)+
        apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
            apply (rule ccorres_Guard)
            apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s
                                            \<and> end_C cqueue = option_to_ctcb_ptr (tcbQueueEnd queue)}"
                        and R="\<lbrace>end_C cqueue = option_to_ctcb_ptr (tcbQueueEnd queue)\<rbrace>"
                         in threadSet_ccorres_lemma4[where P=\<top> and P'=\<top>])
             apply (rule conseqPre, vcg)
             apply clarsimp
             apply (frule (1) obj_at_cslift_tcb)
             apply (fastforce intro!: rf_sr_tcb_update_no_queue_gen2
                                simp: typ_heap_simps' tcb_cte_cases_def cteSizeBits_def
                                      ctcb_relation_def option_to_ctcb_ptr_def)
            apply (clarsimp simp: ctcb_relation_def option_to_ctcb_ptr_def split: if_splits)
           apply ceqv
          apply simp
          apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
              apply (rule ccorres_Guard)
              apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr
                                              \<and> ko_at' tcb (the (tcbQueueEnd queue)) s
                                              \<and> end_C cqueue = option_to_ctcb_ptr (tcbQueueEnd queue)}"
                          and R="\<lbrace>end_C cqueue = option_to_ctcb_ptr (tcbQueueEnd queue)\<rbrace>"
                           in threadSet_ccorres_lemma4[where P=\<top> and P'=\<top>])
               apply (rule conseqPre, vcg)
               apply clarsimp
               apply (frule (1) obj_at_cslift_tcb)
               apply (fastforce intro!: rf_sr_tcb_update_no_queue_gen2
                                  simp: typ_heap_simps' tcb_cte_cases_def cteSizeBits_def
                                        ctcb_relation_def option_to_ctcb_ptr_def tcbQueueEmpty_def)
              apply fastforce
             apply ceqv
            apply (rule ccorres_return_Skip')
           apply wpsimp
          apply vcg
         apply wpsimp
        apply vcg
       apply ceqv
      apply csymbr
      apply (fastforce intro: ccorres_return_C')
     apply wpsimp
    apply vcg
   apply (vcg exspec=tcb_queue_empty_modifies)
  apply clarsimp
  apply (frule (1) tcb_at_h_t_valid)
  by (force dest: tcb_at_h_t_valid
            simp: ctcb_queue_relation_def option_to_ctcb_ptr_def tcbQueueEmpty_def)

lemma getQueue_ccorres:
  "ccorres ctcb_queue_relation queue_'
     (K (tdom \<le> maxDomain \<and> prio \<le> maxPriority))
     \<lbrace>\<acute>idx = word_of_nat (cready_queues_index_to_C tdom prio)\<rbrace> hs
     (getQueue tdom prio) (\<acute>queue :== \<acute>ksReadyQueues.[unat \<acute>idx])"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: getQueue_def gets_def get_def bind_def return_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (frule (1) cready_queues_index_to_C_in_range)
  apply (clarsimp simp: unat_of_nat_eq cready_queues_relation_def)
  done

lemma setQueue_ccorres:
  "ctcb_queue_relation queue cqueue \<Longrightarrow>
   ccorres dc xfdc
     (K (tdom \<le> maxDomain \<and> prio \<le> maxPriority))
     \<lbrace>\<acute>idx = word_of_nat (cready_queues_index_to_C tdom prio)\<rbrace> hs
     (setQueue tdom prio queue)
     (Basic (\<lambda>s. globals_update
                  (ksReadyQueues_'_update
                   (\<lambda>_. Arrays.update (ksReadyQueues_' (globals s)) (unat (idx_' s)) cqueue)) s))"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: setQueue_def get_def modify_def put_def bind_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        carch_state_relation_def cmachine_state_relation_def)
  apply (frule (1) cready_queues_index_to_C_in_range)
  apply (clarsimp simp: unat_of_nat_eq cready_queues_relation_def)
  apply (frule cready_queues_index_to_C_distinct, assumption+)
  apply (frule_tac qdom=d and prio=p in cready_queues_index_to_C_in_range)
   apply fastforce
  apply clarsimp
  done

crunch isRunnable
  for (empty_fail) empty_fail[wp]

lemma tcbSchedEnqueue_ccorres:
  "ccorres dc xfdc
     (tcb_at' t and valid_objs' and pspace_aligned' and pspace_distinct')
     \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace> hs
     (tcbSchedEnqueue t) (Call tcbSchedEnqueue_'proc)"
proof -
  note prio_and_dom_limit_helpers[simp] word_sle_def[simp] maxDom_to_H[simp] maxPrio_to_H[simp]
  note invert_prioToL1Index_c_simp[simp]

  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  note word_less_1[simp del]

  show ?thesis
    apply (cinit lift: tcb_')
     apply (rule ccorres_stateAssert)+
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_assert)
        apply (thin_tac runnable)
        apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'" and xf'="ret__unsigned_longlong_'"
                     in ccorres_split_nothrow)
            apply (rule threadGet_vcg_corres)
            apply (rule allI, rule conseqPre, vcg)
            apply clarsimp
            apply (drule obj_at_ko_at', clarsimp)
            apply (drule spec, drule(1) mp, clarsimp)
            apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
           apply ceqv
          apply (simp add: when_def unless_def del: Collect_const split del: if_split)
          apply (rule ccorres_cond[where R=\<top>])
            apply (simp add: to_bool_def)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'="dom_'" in ccorres_split_nothrow)
               apply (rule threadGet_vcg_corres)
               apply (rule allI, rule conseqPre, vcg)
               apply clarsimp
               apply (drule obj_at_ko_at', clarsimp)
               apply (drule spec, drule(1) mp, clarsimp)
               apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
              apply ceqv
             apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'="prio_'" in ccorres_split_nothrow)
                 apply (rule threadGet_vcg_corres)
                 apply (rule allI, rule conseqPre, vcg)
                 apply clarsimp
                 apply (drule obj_at_ko_at', clarsimp)
                 apply (drule spec, drule(1) mp, clarsimp)
                 apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
                apply ceqv
               apply (rule ccorres_rhs_assoc2)+
               apply (simp only: bind_assoc[symmetric])
               apply (rule ccorres_split_nothrow_novcg_dc)
                  prefer 2
                  apply (rule ccorres_move_c_guard_tcb)
                  apply (simp only: dc_def[symmetric])
                  apply ctac
                 apply (rule ccorres_rhs_assoc)+
                 apply (rule ccorres_symb_exec_r)
                   apply (rule ccorres_Guard_Seq)
                   apply (simp add: bind_assoc)
                   apply (ctac add: getQueue_ccorres)
                     apply (rename_tac queue cqueue)
                     apply (rule_tac xf'=ret__unsigned_long_'
                                 and val="from_bool (tcbQueueEmpty queue)"
                                 and R="\<lambda>s. \<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueHead queue)) s
                                            \<and> (tcbQueueHead queue \<noteq> None \<longleftrightarrow> tcbQueueEnd queue \<noteq> None)"
                                 and R'="{s'. queue_' s' = cqueue}"
                                  in ccorres_symb_exec_r_known_rv)
                        apply (rule conseqPre, vcg)
                        apply (fastforce dest: tcb_at_not_NULL
                                         simp: ctcb_queue_relation_def option_to_ctcb_ptr_def
                                               tcbQueueEmpty_def)
                       apply ceqv
                      apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                          apply (rule ccorres_cond[where R=\<top>])
                            apply fastforce
                           apply (ctac add: addToBitmap_ccorres)
                          apply (rule ccorres_return_Skip)
                         apply ceqv
                        apply (ctac add: tcb_queue_prepend_ccorres)
                          apply (rule ccorres_Guard)
                          apply (rule setQueue_ccorres)
                          apply fastforce
                         apply wpsimp
                        apply (vcg exspec=tcb_queue_prepend_modifies)
                       apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
                      apply (vcg exspec=addToBitmap_modifies)
                     apply vcg
                    apply wpsimp
                   apply vcg
                  apply clarsimp
                  apply vcg
                 apply (rule conseqPre, vcg)
                 apply clarsimp
                apply wpsimp
               apply (clarsimp simp: guard_is_UNIV_def)
              apply (wpsimp wp: threadGet_wp)
             apply vcg
            apply clarsimp
            apply (wpsimp wp: threadGet_wp)
           apply vcg
          apply (rule ccorres_return_Skip)
         apply (wpsimp wp: threadGet_wp)
        apply (vcg expsec=thread_state_get_tcbQueued_modifies)
       apply wpsimp
      apply (wpsimp wp: isRunnable_wp)
     apply wpsimp
    apply normalise_obj_at'
    apply (rename_tac tcb)
    apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
    apply (clarsimp simp: valid_tcb'_def)
    apply (frule (1) obj_at_cslift_tcb)
    apply (rule conjI)
     apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
     apply (drule_tac x="tcbDomain tcb" in spec)
     apply (drule_tac x="tcbPriority tcb" in spec)
     apply clarsimp
     apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
     apply (force dest!: tcbQueueHead_iff_tcbQueueEnd simp: tcbQueueEmpty_def obj_at'_def)
    apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
    apply (rule conjI)
     apply (clarsimp simp: maxDomain_def)
    apply (cut_tac qdom="tcbDomain tcb" and prio="tcbPriority tcb"
                in cready_queues_index_to_C_in_range)
      apply fastforce
     apply fastforce
    apply (clarsimp simp: word_less_nat_alt cready_queues_index_to_C_def2)
    done
qed

lemma tcbSchedAppend_ccorres:
  "ccorres dc xfdc
     (tcb_at' t and valid_objs' and pspace_aligned' and pspace_distinct')
     \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace> hs
     (tcbSchedAppend t) (Call tcbSchedAppend_'proc)"
proof -
  note prio_and_dom_limit_helpers[simp] word_sle_def[simp] maxDom_to_H[simp] maxPrio_to_H[simp]
  note invert_prioToL1Index_c_simp[simp]
  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  note word_less_1[simp del]
  show ?thesis
    apply (cinit lift: tcb_')
     apply (rule ccorres_stateAssert)+
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_assert)
        apply (thin_tac "runnable")
        apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'" and xf'="ret__unsigned_longlong_'"
                     in ccorres_split_nothrow)
            apply (rule threadGet_vcg_corres)
            apply (rule allI, rule conseqPre, vcg)
            apply clarsimp
            apply (drule obj_at_ko_at', clarsimp)
            apply (drule spec, drule(1) mp, clarsimp)
            apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
           apply ceqv
          apply (simp add: when_def unless_def del: Collect_const split del: if_split)
          apply (rule ccorres_cond[where R=\<top>])
            apply (simp add: to_bool_def)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'="dom_'" in ccorres_split_nothrow)
               apply (rule threadGet_vcg_corres)
               apply (rule allI, rule conseqPre, vcg)
               apply clarsimp
               apply (drule obj_at_ko_at', clarsimp)
               apply (drule spec, drule(1) mp, clarsimp)
               apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
              apply ceqv
             apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'="prio_'" in ccorres_split_nothrow)
                 apply (rule threadGet_vcg_corres)
                 apply (rule allI, rule conseqPre, vcg)
                 apply clarsimp
                 apply (drule obj_at_ko_at', clarsimp)
                 apply (drule spec, drule(1) mp, clarsimp)
                 apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
                apply ceqv
               apply (rule ccorres_rhs_assoc2)+
               apply (simp only: bind_assoc[symmetric])
               apply (rule ccorres_split_nothrow_novcg_dc)
                  prefer 2
                  apply (rule ccorres_move_c_guard_tcb)
                  apply (simp only: dc_def[symmetric])
                  apply ctac
                 apply (rule ccorres_rhs_assoc)+
                 apply (rule ccorres_symb_exec_r)
                   apply (rule ccorres_Guard_Seq)
                   apply (simp add: bind_assoc)
                   apply (ctac add: getQueue_ccorres)
                     apply (rename_tac queue cqueue)
                     apply (rule_tac xf'=ret__unsigned_long_'
                                 and val="from_bool (tcbQueueEmpty queue)"
                                 and R="\<lambda>s. \<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueHead queue)) s
                                            \<and> (tcbQueueHead queue \<noteq> None \<longleftrightarrow> tcbQueueEnd queue \<noteq> None)"
                                 and R'="{s'. queue_' s' = cqueue}"
                                  in ccorres_symb_exec_r_known_rv)
                        apply (rule conseqPre, vcg)
                        apply (fastforce dest: tcb_at_not_NULL
                                         simp: ctcb_queue_relation_def option_to_ctcb_ptr_def
                                               tcbQueueEmpty_def)
                       apply ceqv
                      apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                          apply (rule ccorres_cond[where R=\<top>])
                            apply (fastforce dest!: tcb_at_not_NULL
                                              simp: ctcb_queue_relation_def option_to_ctcb_ptr_def)
                           apply (ctac add: addToBitmap_ccorres)
                          apply (rule ccorres_return_Skip)
                         apply ceqv
                        apply (ctac add: tcb_queue_append_ccorres)
                          apply (rule ccorres_Guard)
                          apply (rule setQueue_ccorres)
                          apply fastforce
                         apply wpsimp
                        apply (vcg exspec=tcb_queue_prepend_modifies)
                       apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
                      apply (vcg exspec=addToBitmap_modifies)
                     apply vcg
                    apply wpsimp
                   apply vcg
                  apply clarsimp
                  apply vcg
                 apply (rule conseqPre, vcg)
                 apply clarsimp
                apply wpsimp
               apply (clarsimp simp: guard_is_UNIV_def)
              apply (wpsimp wp: threadGet_wp)
             apply vcg
            apply clarsimp
            apply (wpsimp wp: threadGet_wp)
           apply clarsimp
           apply vcg
          apply (rule ccorres_return_Skip)
         apply (wpsimp wp: threadGet_wp)
        apply (vcg expsec=thread_state_get_tcbQueued_modifies)
       apply wpsimp
      apply (wpsimp wp: isRunnable_wp)
     apply wpsimp
    apply normalise_obj_at'
    apply (rename_tac tcb)
    apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
    apply (clarsimp simp: valid_tcb'_def)
    apply (frule (1) obj_at_cslift_tcb)
    apply (rule conjI)
     apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
     apply (drule_tac x="tcbDomain tcb" in spec)
     apply (drule_tac x="tcbPriority tcb" in spec)
     apply clarsimp
     apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
     apply (frule (3) obj_at'_tcbQueueEnd_ksReadyQueues)
     apply (force dest!: tcbQueueHead_iff_tcbQueueEnd simp: tcbQueueEmpty_def obj_at'_def)
    apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
    apply (rule conjI)
     apply (clarsimp simp: maxDomain_def)
    apply (cut_tac qdom="tcbDomain tcb" and prio="tcbPriority tcb"
                in cready_queues_index_to_C_in_range)
      apply fastforce
     apply fastforce
    apply (clarsimp simp: word_less_nat_alt cready_queues_index_to_C_def2 tcbQueueEmpty_def)
    done
qed

(* FIXME same proofs as bit_set, maybe can generalise? *)
lemma cbitmap_L1_relation_bit_clear:
  fixes p :: priority
  shows
  "\<lbrakk> cbitmap_L1_relation (ksReadyQueuesL1Bitmap_' (globals x)) (ksReadyQueuesL1Bitmap \<sigma>) ;
     d \<le> maxDomain \<rbrakk> \<Longrightarrow>
   cbitmap_L1_relation
           (Arrays.update (ksReadyQueuesL1Bitmap_' (globals x)) (unat d)
             (ksReadyQueuesL1Bitmap_' (globals x).[unat d] && ~~ 2 ^ unat (p >> wordRadix)))
           ((ksReadyQueuesL1Bitmap \<sigma>)(d := ksReadyQueuesL1Bitmap \<sigma> d && ~~ 2 ^ prioToL1Index p))"
  unfolding cbitmap_L1_relation_def numPriorities_def wordBits_def word_size l2BitmapSize_def'
  by (clarsimp simp: word_size prioToL1Index_def wordRadix_def mask_def
                     invertL1Index_def l2BitmapSize_def'
                     le_maxDomain_eq_less_numDomains word_le_nat_alt num_domains_index_updates)

lemma cbitmap_L2_relationD:
  "\<lbrakk> cbitmap_L2_relation cbitmap2 abitmap2 ; d \<le> maxDomain ; i < l2BitmapSize \<rbrakk> \<Longrightarrow>
    cbitmap2.[unat d].[i] = abitmap2 (d, i)"
  unfolding cbitmap_L2_relation_def l2BitmapSize_def'
  by clarsimp

lemma cbitmap_L2_relation_bit_clear:
  fixes p :: priority
  fixes d :: domain
  shows "\<lbrakk> cbitmap_L2_relation (ksReadyQueuesL2Bitmap_' (globals \<sigma>')) (ksReadyQueuesL2Bitmap \<sigma>) ;
           d \<le> maxDomain \<rbrakk>
         \<Longrightarrow>
         cbitmap_L2_relation
          (Arrays.update (ksReadyQueuesL2Bitmap_' (globals \<sigma>')) (unat d)
            (Arrays.update (ksReadyQueuesL2Bitmap_' (globals \<sigma>').[unat d])
              (invertL1Index (prioToL1Index p))
              (ksReadyQueuesL2Bitmap_' (globals \<sigma>').[unat d].[invertL1Index (prioToL1Index p)] &&
                ~~ 2 ^ unat (p && 0x3F))))
          ((ksReadyQueuesL2Bitmap \<sigma>)
           ((d, invertL1Index (prioToL1Index p)) :=
              ksReadyQueuesL2Bitmap \<sigma> (d, invertL1Index (prioToL1Index p)) &&
                ~~ 2 ^ unat (p && mask wordRadix)))"
  unfolding cbitmap_L2_relation_def numPriorities_def wordBits_def word_size l2BitmapSize_def'
  apply (clarsimp simp: word_size prioToL1Index_def wordRadix_def mask_def
                        invertL1Index_def l2BitmapSize_def'
                        le_maxDomain_eq_less_numDomains word_le_nat_alt)
  apply (case_tac "da = d" ; clarsimp simp: num_domains_index_updates)
  done

lemma removeFromBitmap_ccorres:
  "ccorres dc xfdc
     (K (tdom \<le> maxDomain \<and> prio \<le> maxPriority)) (\<lbrace>\<acute>dom = ucast tdom\<rbrace> \<inter> \<lbrace>\<acute>prio = ucast prio\<rbrace>) hs
     (removeFromBitmap tdom prio) (Call removeFromBitmap_'proc)"
proof -

  note prio_and_dom_limit_helpers[simp] word_sle_def[simp]

  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  include no_less_1_simps

  have invert_l1_index_limit: "\<And>p. invertL1Index (prioToL1Index p) < l2BitmapSize"
    unfolding invertL1Index_def l2BitmapSize_def' prioToL1Index_def
    by simp

  show ?thesis
    supply if_split[split del]
    (* pull out static assms *)
    apply simp
    apply (rule ccorres_grab_asm[where P=\<top>, simplified])
    apply (cinit lift: dom_' prio_')
     apply clarsimp
     apply csymbr
     apply csymbr
     (* we can clear up all C guards now *)
     apply (clarsimp simp: maxDomain_le_unat_ucast_explicit word_and_less')
     apply (simp add: invert_prioToL1Index_c_simp word_less_nat_alt)
     apply (simp add: invert_l1_index_limit[simplified l2BitmapSize_def'])
     apply ccorres_rewrite
     (* handle L2 update *)
     apply (rule_tac ccorres_split_nothrow_novcg_dc)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: simpler_gets_def get_def modify_def
                              put_def bind_def return_def bitmap_fun_defs)
        apply (frule rf_sr_cbitmap_L2_relation)
        apply (erule cbitmap_L2_relation_update)
        apply (erule (1) cbitmap_L2_relation_bit_clear)
       (* the check on the C side is identical to checking the L2 entry, rewrite the condition *)
       apply (simp add: getReadyQueuesL2Bitmap_def)
       apply (rule ccorres_symb_exec_l3, rename_tac l2)
          apply (rule_tac C'="{s. l2 = 0}"
                      and Q="\<lambda>s. l2 = ksReadyQueuesL2Bitmap s (tdom, invertL1Index (prioToL1Index prio))"
                   in ccorres_rewrite_cond_sr[where Q'=UNIV])
           apply clarsimp
           apply (frule rf_sr_cbitmap_L2_relation)
           apply (clarsimp simp: cbitmap_L2_relationD invert_l1_index_limit split: if_split)
          (* unset L1 bit when L2 entry is empty *)
          apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: simpler_gets_def get_def modify_def
                                put_def bind_def return_def bitmap_fun_defs)
          apply (frule rf_sr_cbitmap_L1_relation)
          apply (erule cbitmap_L1_relation_update)
          apply (erule (1) cbitmap_L1_relation_bit_clear)
         apply wpsimp+
     apply (fastforce simp: guard_is_UNIV_def)
    apply clarsimp
    done
qed

lemma ctcb_ptr_to_tcb_ptr_option_to_ctcb_ptr[simp]:
  "ctcb_ptr_to_tcb_ptr (option_to_ctcb_ptr (Some ptr)) = ptr"
  by (clarsimp simp: option_to_ctcb_ptr_def)

lemma tcb_queue_remove_ccorres:
  "ccorres ctcb_queue_relation ret__struct_tcb_queue_C_'
     (\<lambda>s. tcb_at' tcbPtr s \<and> valid_objs' s
          \<and> (tcbQueueHead queue \<noteq> None \<longleftrightarrow> tcbQueueEnd queue \<noteq> None))
     (\<lbrace>ctcb_queue_relation queue \<acute>queue\<rbrace> \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace>) hs
     (tcbQueueRemove queue tcbPtr) (Call tcb_queue_remove_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply if_split[split del]
  apply (cinit' lift: tcb_')
   apply (rename_tac tcb')
   apply (simp only: tcbQueueRemove_def)
    \<comment> \<open>cinit is not able to lift queue_' because queue_' is later modified in the C program\<close>
   apply (rule_tac xf'=queue_' in ccorres_abstract, ceqv, rename_tac cqueue)
   apply (rule_tac P="ctcb_queue_relation queue cqueue" in ccorres_gen_asm2)
   apply (rule ccorres_pre_getObject_tcb, rename_tac tcb)
   apply (rule ccorres_symb_exec_l, rename_tac beforePtrOpt)
      apply (rule ccorres_symb_exec_l, rename_tac afterPtrOpt)
         apply (rule ccorres_move_c_guard_tcb)
         apply (rule_tac xf'="before___ptr_to_struct_tcb_C_'"
                     and val="option_to_ctcb_ptr beforePtrOpt"
                     and R="ko_at' tcb tcbPtr and K (tcbSchedPrev tcb = beforePtrOpt)"
                     and R'=UNIV
                      in ccorres_symb_exec_r_known_rv)
            apply (rule conseqPre, vcg)
            apply (fastforce dest: obj_at_cslift_tcb simp: typ_heap_simps ctcb_relation_def)
           apply ceqv
          apply (rule ccorres_move_c_guard_tcb)
          apply (rule_tac xf'="after___ptr_to_struct_tcb_C_'"
                      and val="option_to_ctcb_ptr afterPtrOpt"
                      and R="ko_at' tcb tcbPtr and K (tcbSchedNext tcb = afterPtrOpt)"
                       in ccorres_symb_exec_r_known_rv[where R'=UNIV])
             apply (rule conseqPre, vcg)
             apply (fastforce dest: obj_at_cslift_tcb simp: typ_heap_simps ctcb_relation_def)
            apply ceqv
           apply (rule ccorres_cond_seq)
           apply (rule ccorres_cond[where R="?abs"])
             apply (fastforce dest: tcb_at_not_NULL
                              simp: ctcb_queue_relation_def option_to_ctcb_ptr_def)
            apply (rule ccorres_rhs_assoc)+
            apply csymbr
            apply csymbr
            apply (fastforce intro: ccorres_return_C')
           apply (rule ccorres_cond_seq)
           apply (rule_tac Q="?abs" and Q'=\<top> in ccorres_cond_both')
             apply (fastforce dest: tcb_at_not_NULL
                              simp: ctcb_queue_relation_def option_to_ctcb_ptr_def split: if_splits)
            apply clarsimp
            apply (rule ccorres_assert2)
            apply (rule ccorres_rhs_assoc)+
            apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                apply (rule ccorres_move_c_guard_tcb)+
                apply (rule_tac P=\<top> and P'="tcb_at' tcbPtr"
                            and Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb (the afterPtrOpt) s}"
                             in threadSet_ccorres_lemma3)
                 apply (rule conseqPre, vcg)
                 apply clarsimp
                 apply (frule (1) obj_at_cslift_tcb)
                 apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                   simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                         tcb_cte_cases_def cteSizeBits_def)
                apply fastforce
               apply ceqv
              apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                  apply (rule ccorres_move_c_guard_tcb)
                  apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s}"
                               in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
                   apply (rule conseqPre, vcg)
                   apply clarsimp
                   apply (frule (1) obj_at_cslift_tcb[where thread=tcbPtr])
                   apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                     simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                           tcb_cte_cases_def cteSizeBits_def)
                  apply clarsimp
                 apply ceqv
                apply (rule ccorres_symb_exec_r)
                  apply (fastforce intro: ccorres_return_C')
                 apply vcg
                apply (rule conseqPre, vcg)
                apply clarsimp
               apply wpsimp
              apply vcg
             apply wpsimp
            apply vcg
           apply (rule ccorres_cond_seq)
           apply (rule_tac Q="?abs" and Q'=\<top> in ccorres_cond_both')
             apply (fastforce dest: tcb_at_not_NULL
                              simp: ctcb_queue_relation_def option_to_ctcb_ptr_def split: if_splits)
            apply clarsimp
            apply (rule ccorres_assert2)
            apply (rule ccorres_rhs_assoc)+
            apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                apply (rule ccorres_move_c_guard_tcb)+
                apply (rule_tac P=\<top> and P'="tcb_at' tcbPtr"
                            and Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb (the beforePtrOpt) s}"
                             in threadSet_ccorres_lemma3)
                 apply (rule conseqPre, vcg)
                 apply clarsimp
                 apply (frule (1) obj_at_cslift_tcb)
                 apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                   simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                         tcb_cte_cases_def cteSizeBits_def)
                apply fastforce
               apply ceqv
              apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                  apply (rule ccorres_move_c_guard_tcb)
                  apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s}"
                               in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
                   apply (rule conseqPre, vcg)
                   apply clarsimp
                   apply (frule (1) obj_at_cslift_tcb[where thread=tcbPtr])
                   apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                     simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                           tcb_cte_cases_def cteSizeBits_def)
                  apply clarsimp
                 apply ceqv
                apply (rule ccorres_symb_exec_r)
                  apply (fastforce intro: ccorres_return_C')
                 apply vcg
                apply (rule conseqPre, vcg)
                apply clarsimp
               apply wpsimp
              apply vcg
             apply wpsimp
            apply vcg
           apply clarsimp
           apply (rule ccorres_assert2)+
           apply (rule ccorres_rhs_assoc)+
           apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
               apply (rule ccorres_move_c_guard_tcb)+
               apply (rule_tac Q="\<lambda>s tcb'. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb' (the beforePtrOpt) s}"
                            in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
                apply (rule conseqPre, vcg)
                apply clarsimp
                apply (frule (1) obj_at_cslift_tcb)
                apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                  simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                        tcb_cte_cases_def cteSizeBits_def)
               apply clarsimp
              apply ceqv
             apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                 apply (rule ccorres_move_c_guard_tcb)+
                 apply (rule_tac P=\<top> and P'="tcb_at' tcbPtr"
                             and Q="\<lambda>s tcb'. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb' (the afterPtrOpt) s}"
                              in threadSet_ccorres_lemma3)
                  apply (rule conseqPre, vcg)
                  apply clarsimp
                  apply (frule (1) obj_at_cslift_tcb)
                  apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                    simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                          tcb_cte_cases_def cteSizeBits_def)
                 apply clarsimp
                apply ceqv
               apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                   apply (rule ccorres_move_c_guard_tcb)
                   apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s}"
                                in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
                    apply (rule conseqPre, vcg)
                    apply clarsimp
                    apply (frule (1) obj_at_cslift_tcb[where thread=tcbPtr])
                    apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                      simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                            tcb_cte_cases_def cteSizeBits_def)
                   apply clarsimp
                  apply ceqv
                 apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                     apply (rule ccorres_move_c_guard_tcb)
                     apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s}"
                                  in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
                      apply (rule conseqPre, vcg)
                      apply clarsimp
                      apply (frule (1) obj_at_cslift_tcb[where thread=tcbPtr])
                      apply (fastforce elim!: rf_sr_tcb_update_no_queue_gen2
                                        simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                              tcb_cte_cases_def cteSizeBits_def)
                     apply fastforce
                    apply ceqv
                   apply (fastforce intro: ccorres_return_C')
                  apply (wpsimp | vcg)+
  apply (clarsimp split: if_splits)
  apply normalise_obj_at'
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  by (intro conjI impI;
      clarsimp simp: ctcb_queue_relation_def typ_heap_simps option_to_ctcb_ptr_def
                     valid_tcb'_def valid_bound_tcb'_def)

lemma tcbQueueRemove_tcb_at'_head:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> (\<forall>head. tcbQueueHead queue = Some head \<longrightarrow> tcb_at' head s)\<rbrace>
   tcbQueueRemove queue t
   \<lbrace>\<lambda>rv s. \<not> tcbQueueEmpty rv \<longrightarrow> tcb_at' (the (tcbQueueHead rv)) s\<rbrace>"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: getTCB_wp haskell_assert_wp hoare_vcg_imp_lift')
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (fastforce simp: valid_tcb'_def valid_bound_tcb'_def tcbQueueEmpty_def obj_at'_def)
  done

lemma tcbSchedDequeue_ccorres:
  "ccorres dc xfdc
     (tcb_at' t and valid_objs' and pspace_aligned' and pspace_distinct')
     \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace> hs
     (tcbSchedDequeue t) (Call tcbSchedDequeue_'proc)"
proof -
  note prio_and_dom_limit_helpers[simp] word_sle_def[simp] maxDom_to_H[simp] maxPrio_to_H[simp]
  note invert_prioToL1Index_c_simp[simp]

  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  include no_less_1_simps

  show ?thesis
    apply (cinit lift: tcb_')
     apply (rule ccorres_stateAssert)+
     apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'" and xf'="ret__unsigned_longlong_'"
                  in ccorres_split_nothrow)
         apply (rule threadGet_vcg_corres)
         apply (rule allI, rule conseqPre, vcg)
         apply clarsimp
         apply (drule obj_at_ko_at', clarsimp)
         apply (drule spec, drule(1) mp, clarsimp)
         apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
        apply ceqv
       apply (simp add: when_def del: Collect_const split del: if_split)
       apply (rule ccorres_cond[where R=\<top>])
         apply (simp add: to_bool_def)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'="dom_'" in ccorres_split_nothrow)
            apply (rule threadGet_vcg_corres)
            apply (rule allI, rule conseqPre, vcg)
            apply clarsimp
            apply (drule obj_at_ko_at', clarsimp)
            apply (drule spec, drule(1) mp, clarsimp)
            apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
           apply ceqv
          apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'="prio_'" in ccorres_split_nothrow)
              apply (rule threadGet_vcg_corres)
              apply (rule allI, rule conseqPre, vcg)
              apply clarsimp
              apply (drule obj_at_ko_at', clarsimp)
              apply (drule spec, drule(1) mp, clarsimp)
              apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
             apply ceqv
            apply (rule ccorres_symb_exec_r)
              apply (rule ccorres_Guard_Seq)
              apply (simp add: bind_assoc)
              apply (ctac add: getQueue_ccorres)
                apply (rule_tac r'=ctcb_queue_relation and xf'=new_queue_' in ccorres_split_nothrow)
                    apply (ctac add: tcb_queue_remove_ccorres)
                   apply ceqv
                  apply (rename_tac queue' newqueue)
                  apply (rule ccorres_Guard_Seq)
                  apply (ctac add: setQueue_ccorres)
                    apply (rule ccorres_split_nothrow_novcg_dc)
                       apply ctac
                      apply (rule_tac xf'=ret__unsigned_long_'
                                  and val="from_bool (tcbQueueEmpty queue')"
                                  and R="\<lambda>s. \<not> tcbQueueEmpty queue' \<longrightarrow> tcb_at' (the (tcbQueueHead queue')) s"
                                  in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                         apply (rule conseqPre, vcg)
                         apply (fastforce dest: tcb_at_not_NULL
                                          simp: ctcb_queue_relation_def option_to_ctcb_ptr_def
                                                tcbQueueEmpty_def split: option.splits)
                        apply ceqv
                       apply (rule ccorres_cond[where R=\<top>])
                         apply fastforce
                        apply (ctac add: removeFromBitmap_ccorres)
                       apply (rule ccorres_return_Skip)
                      apply vcg
                     apply (wpsimp wp: hoare_vcg_imp_lift')
                    apply (clarsimp simp: guard_is_UNIV_def)
                   apply (wpsimp wp: hoare_vcg_imp_lift')
                  apply vcg
                 apply ((wpsimp wp: tcbQueueRemove_tcb_at'_head | wp (once) hoare_drop_imps)+)[1]
                apply (vcg exspec=tcb_queue_remove_modifies)
               apply wpsimp
              apply vcg
             apply vcg
            apply (rule conseqPre, vcg)
            apply clarsimp
           apply (wpsimp wp: threadGet_wp)
          apply vcg
         apply clarsimp
         apply (wpsimp wp: threadGet_wp)
        apply vcg
       apply (rule ccorres_return_Skip)
      apply (wpsimp wp: threadGet_wp)
     apply (vcg expsec=thread_state_get_tcbQueued_modifies)
    apply normalise_obj_at'
    apply (rename_tac tcb)
    apply (frule (1) obj_at_cslift_tcb)
    apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
    apply (clarsimp simp: valid_tcb'_def)
    apply (cut_tac qdom="tcbDomain tcb" and prio="tcbPriority tcb"
                in cready_queues_index_to_C_in_range)
      apply fastforce
     apply fastforce
    apply (rule conjI)
     apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
     apply (drule_tac x="tcbDomain tcb" in spec)
     apply (drule_tac x="tcbPriority tcb" in spec)
     apply clarsimp
     apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
     apply (force dest!: tcbQueueHead_iff_tcbQueueEnd simp: tcbQueueEmpty_def obj_at'_def)
    by (fastforce simp: word_less_nat_alt
                        cready_queues_index_to_C_def2 ctcb_relation_def
                        typ_heap_simps le_maxDomain_eq_less_numDomains(2) unat_trans_ucast_helper)
qed

lemma isStopped_spec:
  "\<forall>s. \<Gamma> \<turnstile> ({s} \<inter> {s. cslift s (thread_' s) \<noteq> None}) Call isStopped_'proc
       {s'. ret__unsigned_long_' s' = from_bool (tsType_CL (thread_state_lift (tcbState_C (the (cslift s (thread_' s))))) \<in>
                            {scast ThreadState_BlockedOnReply,
                             scast ThreadState_BlockedOnNotification, scast ThreadState_BlockedOnSend,
                             scast ThreadState_BlockedOnReceive, scast ThreadState_Inactive}) }"
  apply vcg
  apply (clarsimp simp: typ_heap_simps)
done

lemma isRunnable_spec:
  "\<forall>s. \<Gamma> \<turnstile> ({s} \<inter> {s. cslift s (thread_' s) \<noteq> None}) Call isRunnable_'proc
       {s'. ret__unsigned_long_' s' = from_bool (tsType_CL (thread_state_lift (tcbState_C (the (cslift s (thread_' s))))) \<in>
                            { scast ThreadState_Running, scast ThreadState_Restart })}"
  apply vcg
  apply (clarsimp simp: typ_heap_simps)
done

(* FIXME: move *)
lemma ccorres_setSchedulerAction:
  "cscheduler_action_relation a p \<Longrightarrow>
  ccorres dc xfdc \<top> UNIV hs
      (setSchedulerAction a)
      (Basic (\<lambda>s. globals_update (ksSchedulerAction_'_update (\<lambda>_. p)) s))"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: setSchedulerAction_def modify_def get_def put_def bind_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def cmachine_state_relation_def)
  done

declare ge_0_from_bool [simp]

lemma scheduler_action_case_switch_to_if:
  "(case act of SwitchToThread t \<Rightarrow> f t | _ \<Rightarrow> g)
      = (if \<exists>t. act = SwitchToThread t
            then f (case act of SwitchToThread t \<Rightarrow> t) else g)"
  by (simp split: scheduler_action.split)

lemma tcb_at_1:
  "tcb_at' t s \<Longrightarrow> tcb_ptr_to_ctcb_ptr t \<noteq> tcb_Ptr 1"
  apply (drule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (clarsimp simp add: is_aligned_def ctcb_size_bits_def)
  done

lemma rescheduleRequired_ccorres:
  "ccorres dc xfdc
     ((\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs'
      and pspace_aligned' and pspace_distinct')
     UNIV []
     rescheduleRequired (Call rescheduleRequired_'proc)"
  apply cinit
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
          apply (simp add: scheduler_action_case_switch_to_if
                      cong: if_weak_cong split del: if_split)
          apply (rule_tac R="\<lambda>s. action = ksSchedulerAction s \<and> weak_sch_act_wf action s"
                     in ccorres_cond)
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def)
            subgoal by (clarsimp simp: weak_sch_act_wf_def tcb_at_1 tcb_at_not_NULL
                           split: scheduler_action.split_asm dest!: pred_tcb_at')
           apply (ctac add: tcbSchedEnqueue_ccorres)
          apply (rule ccorres_return_Skip)
         apply ceqv
        apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: setSchedulerAction_def simpler_modify_def)
        subgoal by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                              cscheduler_action_relation_def
                              carch_state_relation_def cmachine_state_relation_def)
       apply wp
      apply (simp add: guard_is_UNIV_def)
     apply wp+
   apply (simp add: getSchedulerAction_def)
  apply (clarsimp simp: weak_sch_act_wf_def rf_sr_def cstate_relation_def
                        Let_def cscheduler_action_relation_def)
  by (auto simp: tcb_at_not_NULL tcb_at_1
                    tcb_at_not_NULL[THEN not_sym] tcb_at_1[THEN not_sym]
                 split: scheduler_action.split_asm)

lemma getReadyQueuesL1Bitmap_sp:
  "\<lbrace>\<lambda>s. P s \<and> d \<le> maxDomain \<rbrace>
   getReadyQueuesL1Bitmap d
   \<lbrace>\<lambda>rv s. ksReadyQueuesL1Bitmap s d = rv \<and> d \<le> maxDomain \<and> P s\<rbrace>"
  unfolding bitmap_fun_defs
  by wp simp

(* this doesn't actually carry over d \<le> maxDomain to the rest of the ccorres,
   use ccorres_cross_over_guard to do that *)
lemma ccorres_pre_getReadyQueuesL1Bitmap:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. d \<le> maxDomain \<and> (\<forall>rv. ksReadyQueuesL1Bitmap s d = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. (ksReadyQueuesL1Bitmap_' (globals s)).[unat d] = ucast rv
                                 \<longrightarrow> s \<in> P' rv }
                          hs (getReadyQueuesL1Bitmap d >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
  apply (rule ccorres_symb_exec_l2)
      defer
      defer
      apply (rule getReadyQueuesL1Bitmap_sp)
     apply blast
    apply clarsimp
    prefer 3
    apply (clarsimp simp: bitmap_fun_defs gets_exs_valid)
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply blast
   apply assumption
  apply (drule rf_sr_cbitmap_L1_relation)
  apply (clarsimp simp: cbitmap_L1_relation_def)
  done

lemma getReadyQueuesL2Bitmap_sp:
  "\<lbrace>\<lambda>s. P s \<and> d \<le> maxDomain \<and> i < l2BitmapSize \<rbrace>
   getReadyQueuesL2Bitmap d i
   \<lbrace>\<lambda>rv s. ksReadyQueuesL2Bitmap s (d, i) = rv \<and> d \<le> maxDomain \<and> i < l2BitmapSize \<and> P s\<rbrace>"
  unfolding bitmap_fun_defs
  by wp simp

lemma ccorres_pre_getReadyQueuesL2Bitmap:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. d \<le> maxDomain \<and> i < l2BitmapSize
                       \<and> (\<forall>rv. ksReadyQueuesL2Bitmap s (d,i) = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. (ksReadyQueuesL2Bitmap_' (globals s)).[unat d].[i] = ucast rv
                                 \<longrightarrow> s \<in> P' rv }
                          hs (getReadyQueuesL2Bitmap d i >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
  apply (rule ccorres_symb_exec_l2)
      defer
      defer
      apply (rule getReadyQueuesL2Bitmap_sp)
     apply blast
    apply clarsimp
    prefer 3
    apply (clarsimp simp: bitmap_fun_defs gets_exs_valid)
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply blast
   apply assumption
  apply (drule rf_sr_cbitmap_L2_relation)
  apply (clarsimp simp: cbitmap_L2_relation_def)
  done

lemma rf_sr_ksReadyQueuesL1Bitmap_simp:
  "\<lbrakk> (\<sigma>, s') \<in> rf_sr ; d \<le> maxDomain \<rbrakk>
  \<Longrightarrow> ksReadyQueuesL1Bitmap_' (globals s').[unat d] = ksReadyQueuesL1Bitmap \<sigma> d"
  apply (drule rf_sr_cbitmap_L1_relation)
  apply (simp add: cbitmap_L1_relation_def)
  done

lemma cguard_UNIV:
  "P s \<Longrightarrow> s \<in> (if P s then UNIV else {})"
  by fastforce

lemma lookupBitmapPriority_le_maxPriority:
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ;
     \<forall>d p. d > maxDomain \<or> p > maxPriority \<longrightarrow> tcbQueueEmpty (ksReadyQueues s (d, p));
     valid_bitmaps s \<rbrakk>
   \<Longrightarrow> lookupBitmapPriority d s \<le> maxPriority"
  apply (clarsimp simp: valid_bitmaps_def)
  by (fastforce dest!: bitmapQ_from_bitmap_lookup bitmapQ_ksReadyQueuesI intro: ccontr)

lemma rf_sr_ksReadyQueuesL1Bitmap_not_zero:
  "\<lbrakk> (\<sigma>, s') \<in> rf_sr ; d \<le> maxDomain ; ksReadyQueuesL1Bitmap_' (globals s').[unat d] \<noteq> 0 \<rbrakk>
  \<Longrightarrow> ksReadyQueuesL1Bitmap \<sigma> d \<noteq> 0"
  apply (drule rf_sr_cbitmap_L1_relation)
  apply (simp add: cbitmap_L1_relation_def)
  done

lemma ksReadyQueuesL1Bitmap_word_log2_max:
  "\<lbrakk>valid_bitmaps s; ksReadyQueuesL1Bitmap s d \<noteq> 0\<rbrakk>
   \<Longrightarrow> word_log2 (ksReadyQueuesL1Bitmap s d) < l2BitmapSize"
  unfolding valid_bitmaps_def
  by (fastforce dest: word_log2_nth_same bitmapQ_no_L1_orphansD)

lemma word_log2_max_word64[simp]:
  "word_log2 (w :: 64 word) < 64"
  using word_log2_max[where w=w]
  by (simp add: word_size)

lemma rf_sr_ksReadyQueuesL2Bitmap_simp:
  "\<lbrakk> (\<sigma>, s') \<in> rf_sr ; d \<le> maxDomain ; valid_bitmaps \<sigma> ; ksReadyQueuesL1Bitmap \<sigma> d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> ksReadyQueuesL2Bitmap_' (globals s').[unat d].[word_log2 (ksReadyQueuesL1Bitmap \<sigma> d)] =
      ksReadyQueuesL2Bitmap \<sigma> (d, word_log2 (ksReadyQueuesL1Bitmap \<sigma> d))"
  apply (frule rf_sr_cbitmap_L2_relation)
  apply (frule (1) ksReadyQueuesL1Bitmap_word_log2_max)
  apply (drule (3) cbitmap_L2_relationD)
  done

lemma ksReadyQueuesL2Bitmap_nonzeroI:
  "\<lbrakk> d \<le> maxDomain ; valid_bitmaps s ; ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d))) \<noteq> 0"
   unfolding valid_bitmaps_def
   apply clarsimp
   apply (frule bitmapQ_no_L1_orphansD)
    apply (erule word_log2_nth_same)
   apply clarsimp
   done

lemma clzl_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0} Call clzl_'proc
       \<lbrace>\<acute>ret__long = of_nat (word_clz (x___unsigned_long_' s))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply clarsimp
  apply (rule_tac x="ret__long_'_update f x" for f in exI)
  apply (simp add: mex_def meq_def)
  done

lemma l1index_to_prio_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call l1index_to_prio_'proc
       \<lbrace>\<acute>ret__unsigned_long = l1index_' s << wordRadix \<rbrace>"
  by vcg (simp add: word_sle_def wordRadix_def')

lemma getHighestPrio_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = ucast rv) ret__unsigned_long_'
    (\<lambda>s. d \<le> maxDomain \<and> ksReadyQueuesL1Bitmap s d \<noteq> 0 \<and> bitmapQ_no_L1_orphans s)
    (UNIV \<inter> {s. dom_' s = ucast d}) hs
    (getHighestPrio d) (Call getHighestPrio_'proc)"
proof -

  note prio_and_dom_limit_helpers [simp]
  note Collect_const_mem [simp]

  have signed_word_log2:
  "\<And>w. w \<noteq> 0 \<Longrightarrow> (0x3F::64 signed word) - of_nat (word_clz (w::machine_word)) = (of_nat (word_log2 w))"
  unfolding word_log2_def
  by (clarsimp dest!: word_clz_nonzero_max simp: word_size)

  have word_log2_def64:
    "\<And>w. word_log2 (w::machine_word) = 63 - word_clz w"
    unfolding word_log2_def by (simp add: word_size)

  (* FIXME generalise *)
  have word_clz_sint_upper[simp]:
    "\<And>(w::machine_word). sint (of_nat (word_clz w) :: 64 signed word) \<le> 0x800000000000003F"
    apply (subst sint_eq_uint)
     apply (rule not_msb_from_less)
     apply simp
     apply (rule word_of_nat_less)
     apply simp
     apply (rule order_le_less_trans[OF word_clz_max])
     apply (simp add: word_size)
    apply (subst uint_nat)
    apply (simp add: unat_of_nat)
    apply (subst Divides.mod_less, simp)
     apply (rule order_le_less_trans[OF word_clz_max])
     apply (simp add: word_size)
    apply (rule iffD2 [OF le_nat_iff[symmetric]])
    apply simp
    apply (rule order_trans[OF word_clz_max])
    apply (simp add: word_size)
    done

  have word_clz_sint_lower[simp]:
    "\<And>(w::machine_word). - sint (of_nat (word_clz w) :: 64 signed word) \<le> 0x7FFFFFFFFFFFFFC0"
    apply (subst sint_eq_uint)
     apply (rule not_msb_from_less)
     apply simp
     apply (rule word_of_nat_less)
     apply simp
     apply (rule order_le_less_trans[OF word_clz_max])
     apply (simp add: word_size)
    apply (subst uint_nat)
    apply (simp add: unat_of_nat)
    done

  have invertL1Index_unat_fold:
    "\<And>(w::machine_word). \<lbrakk> w \<noteq> 0 ; word_log2 w < l2BitmapSize \<rbrakk> \<Longrightarrow>
       unat (of_nat l2BitmapSize - (1::machine_word) - of_nat (word_log2 w))
     = invertL1Index (word_log2 w)"
    apply (subst unat_sub)
     apply (clarsimp simp: l2BitmapSize_def')
     apply (rule word_of_nat_le)
     apply (drule word_log2_nth_same)
     apply (clarsimp simp: l2BitmapSize_def')
    apply (clarsimp simp: invertL1Index_def l2BitmapSize_def')
    apply (simp add: unat_of_nat_eq)
    done

  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  include no_less_1_simps

  show ?thesis
  apply (cinit lift: dom_')
   apply (clarsimp split del: if_split)
   apply (rule ccorres_pre_getReadyQueuesL1Bitmap)
   apply (rule ccorres_pre_getReadyQueuesL2Bitmap)
   apply (rename_tac l2)
   apply (rule ccorres_Guard_Seq|csymbr)+
   apply (rule ccorres_abstract_cleanup)
   apply (rule ccorres_Guard_Seq|csymbr)+
   apply (rule ccorres_abstract_cleanup)
   apply (rule ccorres_Guard_Seq|csymbr)+
   apply (clarsimp simp: word_log2_def word_size)
   apply (rename_tac clz_l1index clz_l2index)
   apply (rule_tac P="\<lambda>s. l1 \<noteq> 0 \<and> l2 \<noteq> 0 \<and> word_log2 l1 < l2BitmapSize"
            and P'="{s. clz_l1index = of_nat (word_clz l1) \<and>
                        clz_l2index = of_nat (word_clz l2) }"
            in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
    subgoal for l1 l2 _ _ _
    apply (clarsimp simp: return_def l1IndexToPrio_def)
    apply (simp add: signed_word_log2 word_log2_def64[symmetric] ucast_or_distrib)
    apply (rule_tac f="(||)" in arg_cong2)
     apply (subst of_nat_shiftl)+
     apply (subst ucast_of_nat_small, simp add: wordRadix_def l2BitmapSize_def')
     apply (rule refl)
    apply (subst ucast_of_nat_small, simp add: wordRadix_def)
     apply (rule word_log2_max_word64[THEN order_less_le_trans], simp)
    apply (rule refl)
    done
   apply (clarsimp simp: word_sle_def)

   apply (frule rf_sr_cbitmap_L1_relation)
   apply (subgoal_tac "ksReadyQueuesL1Bitmap_' (globals s').[unat d] \<noteq> 0")
    prefer 2
    subgoal by (fastforce simp: cbitmap_L1_relation_def)

   apply (clarsimp simp: signed_word_log2 cbitmap_L1_relation_def maxDomain_le_unat_ucast_explicit)
   apply (frule bitmapQ_no_L1_orphansD, erule word_log2_nth_same)
   apply simp
   apply (rule conjI, fastforce simp: invertL1Index_def l2BitmapSize_def')
   apply (rule conjI, fastforce simp: invertL1Index_unat_fold)
   apply (rule conjI)
    apply (subst invertL1Index_unat_fold, assumption, fastforce)
    apply (frule rf_sr_cbitmap_L2_relation)
    apply (fastforce simp: cbitmap_L2_relation_def)
   apply (clarsimp simp: l2BitmapSize_def')
   apply (fastforce simp: word_less_nat_alt word_le_nat_alt unat_sub unat_of_nat)
   done
qed

lemma ccorres_abstract_ksCurThread:
  assumes ceqv: "\<And>rv' t t'. ceqv \<Gamma> (\<lambda>s. ksCurThread_' (globals s)) rv' t t' d (d' rv')"
  and       cc: "\<And>ct. ccorres_underlying rf_sr \<Gamma> r xf arrel axf (G ct) (G' ct) hs a (d' (tcb_ptr_to_ctcb_ptr ct))"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf (\<lambda>s. G (ksCurThread s) s)
            {s. s \<in> G' (ctcb_ptr_to_tcb_ptr (ksCurThread_' (globals s)))} hs a d"
  apply (rule ccorres_guard_imp)
    prefer 2
    apply assumption
   apply (rule ccorres_abstract[OF ceqv, where G'="\<lambda>ct. \<lbrace>ct = \<acute>ksCurThread\<rbrace> \<inter> G' (ctcb_ptr_to_tcb_ptr ct)"])
   apply (subgoal_tac "\<exists>t. rv' = tcb_ptr_to_ctcb_ptr t")
    apply clarsimp
    apply (rule ccorres_guard_imp2)
     apply (rule cc)
    apply (clarsimp simp: rf_sr_ksCurThread)
   apply (metis tcb_ptr_to_tcb_ptr)
  apply simp
  done

lemma ctcb_relation_unat_tcbPriority_C:
  "ctcb_relation tcb tcb' \<Longrightarrow> unat (tcbPriority_C tcb') = unat (tcbPriority tcb)"
  apply (clarsimp simp: ctcb_relation_def)
  apply (rule trans, rule arg_cong[where f=unat], erule sym)
  apply (simp(no_asm))
  done

lemma ctcb_relation_unat_tcbDomain_C:
  "ctcb_relation tcb tcb' \<Longrightarrow> unat (tcbDomain_C tcb') = unat (tcbDomain tcb)"
  apply (clarsimp simp: ctcb_relation_def)
  apply (rule trans, rule arg_cong[where f=unat], erule sym)
  apply (simp(no_asm))
  done

lemma getCurDomain_ccorres_dom_':
  "ccorres (\<lambda>rv rv'. rv' = ucast rv) dom_'
       \<top> UNIV hs curDomain (\<acute>dom :== \<acute>ksCurDomain)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: curDomain_def simpler_gets_def
                        rf_sr_ksCurDomain)
  done

lemma getCurDomain_maxDom_ccorres_dom_':
  "ccorres (\<lambda>rv rv'. rv' = ucast rv) dom_'
     (\<lambda>s. ksCurDomain s \<le> maxDomain) UNIV hs
     curDomain (\<acute>dom :== (if maxDom \<noteq> 0 then \<acute>ksCurDomain else 0))"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  using maxDom_to_H
  apply (clarsimp simp: curDomain_def simpler_gets_def
                        rf_sr_ksCurDomain)
  done

lemma threadGet_get_obj_at'_has_domain:
  "\<lbrace> tcb_at' t \<rbrace> threadGet tcbDomain t \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. rv = tcbDomain tcb) t\<rbrace>"
  by (wp threadGet_obj_at') (simp add: obj_at'_def)

lemma possibleSwitchTo_ccorres:
  shows
  "ccorres dc xfdc
         ((\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
            and st_tcb_at' runnable' t and (\<lambda>s. ksCurDomain s \<le> maxDomain)
            and valid_objs' and pspace_aligned' and pspace_distinct')
         ({s. target_' s = tcb_ptr_to_ctcb_ptr t}
          \<inter> UNIV) []
     (possibleSwitchTo t )
     (Call possibleSwitchTo_'proc)"
  supply if_split [split del]
  supply Collect_const [simp del]
  supply prio_and_dom_limit_helpers[simp]
  (* FIXME: these should likely be in simpset for CRefine, or even in general *)
  supply from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp]
         ccorres_IF_True[simp] if_cong[cong]
  apply (cinit lift: target_')
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule ccorres_pre_curDomain, rename_tac curDom)
   apply (rule ccorres_symb_exec_l3[OF _ threadGet_inv _ empty_fail_threadGet], rename_tac targetDom)
    apply (rule ccorres_symb_exec_l3[OF _ gsa_wp _ empty_fail_getSchedulerAction], rename_tac sact)
     apply (rule_tac C'="{s. targetDom \<noteq> curDom}"
              and Q="\<lambda>s. curDom = ksCurDomain s \<and> obj_at' (\<lambda>tcb. targetDom = tcbDomain tcb) t s"
              and Q'=UNIV in ccorres_rewrite_cond_sr)
      subgoal
        apply clarsimp
        apply (drule obj_at_ko_at', clarsimp  simp: rf_sr_ksCurDomain)
        apply (frule (1) obj_at_cslift_tcb, clarsimp simp: typ_heap_simps')
        apply (drule ctcb_relation_unat_tcbDomain_C)
        apply unat_arith
        apply fastforce
        done
     apply (rule ccorres_cond2[where R=\<top>], simp)
      apply (ctac add: tcbSchedEnqueue_ccorres)
     apply (rule_tac R="\<lambda>s. sact = ksSchedulerAction s \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                     in ccorres_cond)
       apply (fastforce dest!: rf_sr_sched_action_relation pred_tcb_at' tcb_at_not_NULL
                        simp: cscheduler_action_relation_def weak_sch_act_wf_def
                        split: scheduler_action.splits)
      apply (ctac add: rescheduleRequired_ccorres)
        apply (ctac add: tcbSchedEnqueue_ccorres)
       apply wp
      apply (vcg exspec=rescheduleRequired_modifies)
     apply (rule ccorres_setSchedulerAction, simp add: cscheduler_action_relation_def)
    apply clarsimp
    apply wp
   apply clarsimp
   apply (wp hoare_drop_imps threadGet_get_obj_at'_has_domain)
  apply (clarsimp simp: pred_tcb_at')
  done

lemma scheduleTCB_ccorres':
  "ccorres dc xfdc
           (tcb_at' thread and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                           and valid_objs' and pspace_aligned' and pspace_distinct')
           (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread})
           []
  (do (runnable, curThread, action) \<leftarrow> do
      runnable \<leftarrow> isRunnable thread;
      curThread \<leftarrow> getCurThread;
      action \<leftarrow> getSchedulerAction;
      return (runnable, curThread, action) od;
      when (\<not> runnable \<and>
              curThread = thread \<and> action = ResumeCurrentThread)
       rescheduleRequired
  od)
  (Call scheduleTCB_'proc)"
  supply empty_fail_cond[simp]
  apply (cinit' lift: tptr_')
   apply (rule ccorres_rhs_assoc2)+
   apply (rule_tac xf'="ret__int_'" in ccorres_split_nothrow_novcg)
       defer
       apply ceqv
      apply (unfold split_def)[1]
      apply (rule ccorres_when[where R=\<top>])
       apply (intro allI impI)
       apply (unfold mem_simps)[1]
       apply assumption
      apply (ctac add: rescheduleRequired_ccorres)
     prefer 4
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_pre_getCurThread)
        apply (rule ccorres_symb_exec_l)
           apply (rule_tac P="\<lambda>s. st_tcb_at' (\<lambda>st. runnable' st = runnable) thread s
                                 \<and> curThread = ksCurThread s
                                 \<and> action = ksSchedulerAction s
                                 \<and> (\<forall>t. ksSchedulerAction s = SwitchToThread t \<longrightarrow> tcb_at' t s)"
                           and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
           apply (clarsimp simp: from_bool_0 rf_sr_ksCurThread)
           apply (rule conjI)
            apply (clarsimp simp: st_tcb_at'_def)
            apply (drule (1) obj_at_cslift_tcb)
            apply (clarsimp simp: typ_heap_simps)
            apply (subgoal_tac "ksSchedulerAction \<sigma> = ResumeCurrentThread")
             apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def)
             apply (case_tac "tcbState ko", simp_all add: ThreadState_defs)[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def                                  tcb_at_not_NULL
                           split: scheduler_action.split_asm)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 cscheduler_action_relation_def)
          apply wp+
   apply (simp add: isRunnable_def isStopped_def)
   apply (simp add: guard_is_UNIV_def)
  apply clarsimp
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def weak_sch_act_wf_def)
  done

lemma scheduleTCB_ccorres_valid_queues'_pre:
  "ccorresG rf_sr \<Gamma> dc xfdc
     (tcb_at' thread and st_tcb_at' (not runnable') thread
      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and valid_objs' and pspace_aligned' and pspace_distinct')
     \<lbrace>\<acute>tptr = tcb_ptr_to_ctcb_ptr thread\<rbrace> []
     (do (runnable, curThread, action) \<leftarrow> do runnable \<leftarrow> isRunnable thread;
                                             curThread \<leftarrow> getCurThread;
                                             action \<leftarrow> getSchedulerAction;
                                             return (runnable, curThread, action)
                                          od;
         when (\<not> runnable \<and> curThread = thread \<and> action = ResumeCurrentThread) rescheduleRequired
      od)
     (Call scheduleTCB_'proc)"
  supply empty_fail_cond[simp]
  apply (cinit' lift: tptr_')
   apply (rule ccorres_rhs_assoc2)+
   apply (rule_tac xf'="ret__int_'" in ccorres_split_nothrow_novcg)
       defer
       apply ceqv
      apply (unfold split_def)[1]
      apply (rule ccorres_when[where R=\<top>])
       apply (intro allI impI)
       apply (unfold mem_simps)[1]
       apply assumption
      apply (ctac add: rescheduleRequired_ccorres)
     prefer 4
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_pre_getCurThread)
        apply (rule ccorres_symb_exec_l)
           apply (rule_tac P="\<lambda>s. st_tcb_at' (\<lambda>st. runnable' st = runnable) thread s
                                 \<and> curThread = ksCurThread s
                                 \<and> action = ksSchedulerAction s
                                 \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                           and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def if_1_0_0 split del: if_split)
           apply (clarsimp simp: from_bool_0 rf_sr_ksCurThread)
           apply (rule conjI)
            apply (clarsimp simp: st_tcb_at'_def)
            apply (drule (1) obj_at_cslift_tcb)
            apply (clarsimp simp: typ_heap_simps)
            apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def weak_sch_act_wf_def)
             apply (case_tac "tcbState ko", simp_all add: ThreadState_defs)[1]
                 apply (fold_subgoals (prefix))[6]
                 subgoal premises prems using prems
                         by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                       cscheduler_action_relation_def
                                       tcb_at_not_NULL[OF obj_tcb_at'] st_tcb_at'_def
                                split: scheduler_action.split_asm)+
           apply (clarsimp simp: rf_sr_def cstate_relation_def cscheduler_action_relation_def
                           split: scheduler_action.split_asm)
          apply wp+
     apply (simp add: isRunnable_def isStopped_def)
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
  done

lemmas scheduleTCB_ccorres_valid_queues'
    = scheduleTCB_ccorres_valid_queues'_pre[unfolded bind_assoc return_bind split_conv]

lemma rescheduleRequired_ccorres_valid_queues'_simple:
  "ccorresG rf_sr \<Gamma> dc xfdc
     sch_act_simple UNIV []
     rescheduleRequired (Call rescheduleRequired_'proc)"
  apply cinit
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
          apply (simp add: scheduler_action_case_switch_to_if
                      cong: if_weak_cong split del: if_split)
          apply (rule_tac R="\<lambda>s. action = ksSchedulerAction s \<and> sch_act_simple s"
                     in ccorres_cond)
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def)
            apply (clarsimp simp: weak_sch_act_wf_def tcb_at_1 tcb_at_not_NULL
                           split: scheduler_action.split_asm dest!: st_tcb_strg'[rule_format])
           apply (ctac add: tcbSchedEnqueue_ccorres)
          apply (rule ccorres_return_Skip)
         apply ceqv
        apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: setSchedulerAction_def simpler_modify_def)
        apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                              cscheduler_action_relation_def
                              carch_state_relation_def cmachine_state_relation_def
                              )
       apply wp
      apply (simp add: guard_is_UNIV_def)
     apply wp+
   apply (simp add: getSchedulerAction_def)
  apply (clarsimp simp: weak_sch_act_wf_def rf_sr_def cstate_relation_def
                        Let_def cscheduler_action_relation_def)
  by (auto simp: tcb_at_not_NULL tcb_at_1
                    tcb_at_not_NULL[THEN not_sym] tcb_at_1[THEN not_sym]
                 split: scheduler_action.split_asm)

lemma scheduleTCB_ccorres_valid_queues'_pre_simple:
  "ccorresG rf_sr \<Gamma> dc xfdc
     (tcb_at' thread and st_tcb_at' (not runnable') thread and valid_queues' and sch_act_simple)
     \<lbrace>\<acute>tptr = tcb_ptr_to_ctcb_ptr thread\<rbrace> []
     (do (runnable, curThread, action) \<leftarrow> do runnable \<leftarrow> isRunnable thread;
                                             curThread \<leftarrow> getCurThread;
                                             action \<leftarrow> getSchedulerAction;
                                             return (runnable, curThread, action)
                                          od;
         when (\<not> runnable \<and> curThread = thread \<and> action = ResumeCurrentThread) rescheduleRequired
      od)
     (Call scheduleTCB_'proc)"
  supply empty_fail_cond[simp]
  apply (cinit' lift: tptr_' simp del: word_neq_0_conv)
   apply (rule ccorres_rhs_assoc2)+
   apply (rule_tac xf'="ret__int_'" in ccorres_split_nothrow_novcg)
       defer
       apply ceqv
      apply (unfold split_def)[1]
      apply (rule ccorres_when[where R=\<top>])
       apply (intro allI impI)
       apply (unfold mem_simps)[1]
       apply assumption
      apply (ctac add: rescheduleRequired_ccorres_valid_queues'_simple)
     prefer 4
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_pre_getCurThread)
        apply (rule ccorres_symb_exec_l)
           apply (rule_tac P="\<lambda>s. st_tcb_at' (\<lambda>st. runnable' st = runnable) thread s
                                 \<and> curThread = ksCurThread s
                                 \<and> action = ksSchedulerAction s
                                 \<and> sch_act_simple s"
                           and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def if_1_0_0 split del: if_split)
           apply (clarsimp simp: from_bool_0 rf_sr_ksCurThread)
           apply (rule conjI)
            apply (clarsimp simp: st_tcb_at'_def)
            apply (drule (1) obj_at_cslift_tcb)
            apply (clarsimp simp: typ_heap_simps)
            apply (subgoal_tac "ksSchedulerAction \<sigma> = ResumeCurrentThread")
             apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def)
             apply (case_tac "tcbState ko", simp_all add: ThreadState_defs)[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def
                                  tcb_at_not_NULL
                           split: scheduler_action.split_asm)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 cscheduler_action_relation_def)
          apply wp+
   apply (simp add: isRunnable_def isStopped_def)
   apply (simp add: guard_is_UNIV_def)
  apply clarsimp
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
  done

lemmas scheduleTCB_ccorres_valid_queues'_simple
    = scheduleTCB_ccorres_valid_queues'_pre_simple[unfolded bind_assoc return_bind split_conv]

lemmas scheduleTCB_ccorres[corres]
    = scheduleTCB_ccorres'[unfolded bind_assoc return_bind split_conv]

lemma threadSet_weak_sch_act_wf_runnable':
            "\<lbrace> \<lambda>s. (ksSchedulerAction s = SwitchToThread thread \<longrightarrow> runnable' st) \<and> weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>
               threadSet (tcbState_update (\<lambda>_. st)) thread
             \<lbrace> \<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  apply (simp add: weak_sch_act_wf_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift threadSet_pred_tcb_at_state
            threadSet_tcbDomain_triv)
   apply simp
  apply (clarsimp)
done

lemma setThreadState_ccorres[corres]:
   "ccorres dc xfdc
      (\<lambda>s. tcb_at' thread s \<and> valid_objs' s \<and> valid_tcb_state' st s \<and>
           pspace_aligned' s \<and> pspace_distinct' s \<and>
           (ksSchedulerAction s = SwitchToThread thread \<longrightarrow> runnable' st) \<and>
           sch_act_wf (ksSchedulerAction s) s)
      ({s'. (\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := ts_' s' && mask 4\<rparr>, fl))}
       \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) hs
         (setThreadState st thread) (Call setThreadState_'proc)"
  apply (cinit lift: tptr_' cong add: call_ignore_cong)
   apply (ctac (no_vcg) add: threadSet_tcbState_simple_corres)
    apply (ctac add: scheduleTCB_ccorres)
   apply (wp threadSet_weak_sch_act_wf_runnable' threadSet_valid_objs')
  by (clarsimp simp: weak_sch_act_wf_def valid_queues_def valid_tcb'_tcbState_update)

lemma setThreadState_ccorres_valid_queues':
  "ccorres dc xfdc
     (\<lambda>s. tcb_at' thread s \<and> \<not> runnable' st \<and> weak_sch_act_wf (ksSchedulerAction s) s
          \<and> sch_act_not thread s \<and> valid_objs' s \<and> valid_tcb_state' st s
          \<and> pspace_aligned' s \<and> pspace_distinct' s)
     ({s'. (\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := ts_' s' && mask 4\<rparr>, fl))}
      \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) []
     (setThreadState st thread) (Call setThreadState_'proc)"
  apply (cinit lift: tptr_' cong add: call_ignore_cong)
   apply (ctac (no_vcg) add: threadSet_tcbState_simple_corres)
    apply (ctac add: scheduleTCB_ccorres_valid_queues')
   apply (wp threadSet_weak_sch_act_wf_runnable' threadSet_valid_objs'
             threadSet_tcbState_st_tcb_at')
  by (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)

lemma simp_list_case_return:
  "(case x of [] \<Rightarrow> return e | y # ys \<Rightarrow> return f) = return (if x = [] then e else f)"
  by (clarsimp split: list.splits)

lemma cancelSignal_ccorres [corres]:
     "ccorres dc xfdc
      (invs' and st_tcb_at' ((=) (Structures_H.thread_state.BlockedOnNotification ntfn)) thread)
      (UNIV \<inter> {s. threadPtr_' s = tcb_ptr_to_ctcb_ptr thread} \<inter> {s. ntfnPtr_' s = Ptr ntfn})
      [] (cancelSignal thread ntfn) (Call cancelSignal_'proc)"
  apply (cinit lift: threadPtr_' ntfnPtr_' simp add: Let_def list_case_return cong add: call_ignore_cong)
   apply (unfold fun_app_def)
   apply (simp only: simp_list_case_return return_bind ccorres_seq_skip)
   apply (rule ccorres_pre_getNotification)
   apply (rule ccorres_assert)
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_rhs_assoc2)
   apply (ctac (no_vcg) add: cancelSignal_ccorres_helper)
     apply (ctac add: setThreadState_ccorres_valid_queues')
    apply ((wp setNotification_nosch hoare_vcg_all_lift set_ntfn_valid_objs' | simp add: valid_tcb_state'_def split del: if_split)+)[1]
   apply (simp add: ThreadState_defs)
  apply (rule conjI, clarsimp, rule conjI, clarsimp)
    apply (frule (1) ko_at_valid_ntfn'[OF _ invs_valid_objs'])
   subgoal by ((auto simp: obj_at'_def projectKOs st_tcb_at'_def invs'_def valid_state'_def
                     isTS_defs cte_wp_at_ctes_of
                     cthread_state_relation_def sch_act_wf_weak valid_ntfn'_def
               | clarsimp simp: eq_commute)+)
   apply (clarsimp)
   apply (frule (1) ko_at_valid_ntfn'[OF _ invs_valid_objs'])
   apply (frule (2) ntfn_blocked_in_queueD)
   by (auto simp: obj_at'_def projectKOs st_tcb_at'_def invs'_def valid_state'_def
                     isTS_defs cte_wp_at_ctes_of valid_ntfn'_def
                     cthread_state_relation_def sch_act_wf_weak isWaitingNtfn_def
             split: ntfn.splits option.splits
         |  clarsimp simp: eq_commute
         | drule_tac x=thread in bspec)+

(* FIXME: MOVE *)
lemma ccorres_pre_getEndpoint [ccorres_pre]:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
           (ep_at' p and (\<lambda>s. \<forall>ep. ko_at' ep p s \<longrightarrow> P ep s))
           ({s'. \<forall>ep. cendpoint_relation (cslift s') ep (the (cslift s' (Ptr p))) \<longrightarrow> s' \<in> P' ep})
           hs (getEndpoint p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
  apply (rule ccorres_symb_exec_l2)
      defer
      defer
      apply (rule get_ep_sp')
     apply assumption
    apply clarsimp
    prefer 3
    apply (clarsimp simp add: getEndpoint_def exs_getObject objBits_simps')
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply simp
   apply assumption
  apply (drule spec, erule mp)
  apply (drule cmap_relation_ep)
  apply (drule (1) cmap_relation_ko_atD)
  apply clarsimp
  done

lemma ep_blocked_in_queueD:
  "\<lbrakk> st_tcb_at' (\<lambda>st. (isBlockedOnSend st \<or> isBlockedOnReceive st)
                      \<and> blockingObject st = ep) thread \<sigma>;
               ko_at' ep' ep \<sigma>; invs' \<sigma> \<rbrakk>
   \<Longrightarrow> thread \<in> set (epQueue ep') \<and> (isSendEP ep' \<or> isRecvEP ep')"
  apply (drule sym_refs_st_tcb_atD')
   apply clarsimp
  apply (clarsimp simp: refs_of_rev' obj_at'_def ko_wp_at'_def projectKOs)
  apply (clarsimp simp: isTS_defs split: Structures_H.thread_state.split_asm)
   apply (cases ep', simp_all add: isSendEP_def isRecvEP_def)[1]
  apply (cases ep', simp_all add: isSendEP_def isRecvEP_def)[1]
  done

lemma ep_ptr_get_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. s \<Turnstile>\<^sub>c \<acute>epptr\<rbrace> \<acute>ret__struct_tcb_queue_C :== PROC ep_ptr_get_queue(\<acute>epptr)
       \<lbrace>head_C \<acute>ret__struct_tcb_queue_C = Ptr (epQueue_head_CL (endpoint_lift (the (cslift s \<^bsup>s\<^esup>epptr)))) \<and>
        end_C \<acute>ret__struct_tcb_queue_C = Ptr (epQueue_tail_CL (endpoint_lift (the (cslift s \<^bsup>s\<^esup>epptr))))\<rbrace>"
  apply vcg
  apply clarsimp
  done

(* FIXME x64: bitfield shenanigans *)
lemma ep_ptr_set_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. s \<Turnstile>\<^sub>c \<acute>epptr\<rbrace> Call ep_ptr_set_queue_'proc
           {t. (\<exists>ep'. endpoint_lift ep' =
  (endpoint_lift (the (cslift s (\<^bsup>s\<^esup>epptr))))\<lparr> epQueue_head_CL := ptr_val (head_C \<^bsup>s\<^esup>queue) && ~~ mask 4,
                                                      epQueue_tail_CL := ptr_val (end_C \<^bsup>s\<^esup>queue) && ~~ mask 4 \<rparr>
             \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (\<^bsup>s\<^esup>epptr) ep')
                 (t_hrs_' (globals s)))}"
  apply vcg
  apply (auto simp: split_def h_t_valid_clift_Some_iff
                    typ_heap_simps packed_heap_update_collapse_hrs)
  oops

lemma valid_ep_blockedD:
  "\<lbrakk> valid_ep' ep s; (isSendEP ep \<or> isRecvEP ep) \<rbrakk> \<Longrightarrow> (epQueue ep) \<noteq> [] \<and> (\<forall>t\<in>set (epQueue ep). tcb_at' t s) \<and> distinct (epQueue ep)"
  unfolding valid_ep'_def isSendEP_def isRecvEP_def
  by (clarsimp split: endpoint.splits)


lemma ep_to_ep_queue:
  assumes ko: "ko_at' ep' ep s"
  and     waiting: "(isSendEP ep' \<or> isRecvEP ep')"
  and     rf: "(s, s') \<in> rf_sr"
  shows "ep_queue_relation' (cslift s') (epQueue ep')
              (Ptr (epQueue_head_CL
                     (endpoint_lift (the (cslift s' (Ptr ep))))))
              (Ptr (epQueue_tail_CL
                     (endpoint_lift (the (cslift s' (Ptr ep))))))"
proof -
  from rf have
    "cmap_relation (map_to_eps (ksPSpace s)) (cslift s') Ptr (cendpoint_relation (cslift s'))"
    by (rule cmap_relation_ep)

  thus ?thesis using ko waiting
    apply -
    apply (erule (1) cmap_relation_ko_atE)
    apply (clarsimp simp: cendpoint_relation_def Let_def isSendEP_def isRecvEP_def split: endpoint.splits)
    done
qed

lemma ep_ep_disjoint:
  assumes srs: "sym_refs (state_refs_of' s)"
  and    epat: "ko_at' ep epptr s"
  and   epat': "ko_at' ep' epptr' s"
  and     epq: "(isSendEP ep \<or> isRecvEP ep)"
  and    epq': "(isSendEP ep' \<or> isRecvEP ep')"
  and      neq: "epptr' \<noteq> epptr"
  shows  "set (epQueue ep) \<inter> set (epQueue ep') = {}"
  using srs epat epat' epq epq' neq
  apply -
  apply (subst disjoint_iff_not_equal, intro ballI, rule notI)
  apply (drule sym_refs_ko_atD', clarsimp)+
  apply clarsimp
  apply (clarsimp simp: isSendEP_def isRecvEP_def split: endpoint.splits)
  apply (simp_all add: st_tcb_at_refs_of_rev')
  apply (fastforce simp: st_tcb_at'_def obj_at'_def)+
  done

lemma cendpoint_relation_ep_queue:
  fixes ep :: "endpoint"
  assumes   ep: "cendpoint_relation mp ep' b"
  and     mpeq: "(mp' |` (- S)) = (mp |` (- S))"
  and      epq: "ep' \<noteq> IdleEP \<Longrightarrow>
                     set (epQueue ep') \<inter> (ctcb_ptr_to_tcb_ptr ` S) = {}"
  shows  "cendpoint_relation mp' ep' b"
proof -

  have rl: "\<And>p list. \<lbrakk> ctcb_ptr_to_tcb_ptr p \<in> set list;
                          ep' = RecvEP list \<or> ep' = SendEP list \<rbrakk>
                         \<Longrightarrow> mp' p = mp p"
    using epq
    apply (cut_tac x=p in fun_cong[OF mpeq])
    apply (cases ep', auto simp: restrict_map_def split: if_split_asm)
    done

  have rl': "\<And>p list. \<lbrakk> p \<in> tcb_ptr_to_ctcb_ptr ` set list;
                          ep' = RecvEP list \<or> ep' = SendEP list \<rbrakk>
                         \<Longrightarrow> mp' p = mp p"
    by (clarsimp elim!: rl[rotated])

  show ?thesis using ep rl' mpeq unfolding cendpoint_relation_def
    by (simp add: Let_def
            cong: Structures_H.endpoint.case_cong tcb_queue_relation'_cong)
qed

lemma cpspace_relation_ep_update_an_ep:
  fixes ep :: "endpoint"
  defines "qs \<equiv> if (isSendEP ep \<or> isRecvEP ep) then set (epQueue ep) else {}"
  assumes koat: "ko_at' ep epptr s"
  and      cp: "cmap_relation (map_to_eps (ksPSpace s)) (cslift t) Ptr (cendpoint_relation mp)"
  and     rel: "cendpoint_relation mp' ep' endpoint"
  and    mpeq: "(mp' |` (- S)) = (mp |` (- S))"
  and     pal: "pspace_aligned' s" "pspace_distinct' s"
  and  others: "\<And>epptr' ep'. \<lbrakk> ko_at' ep' epptr' s; epptr' \<noteq> epptr; ep' \<noteq> IdleEP \<rbrakk>
                                 \<Longrightarrow> set (epQueue ep') \<inter> (ctcb_ptr_to_tcb_ptr ` S) = {}"
  shows "cmap_relation (map_to_eps ((ksPSpace s)(epptr \<mapsto> KOEndpoint ep')))
           ((cslift t)(Ptr epptr \<mapsto> endpoint)) Ptr (cendpoint_relation mp')"
  using cp koat pal rel unfolding cmap_relation_def
  apply -
  apply (clarsimp elim!: obj_atE' simp: map_comp_update projectKO_opts_defs)
  apply (drule (1) bspec [OF _ domI])
  apply simp
  apply (erule cendpoint_relation_ep_queue[OF _ mpeq])
  apply (erule(4) others[OF map_to_ko_atI])
  done

lemma endpoint_not_idle_cases:
  "ep \<noteq> IdleEP \<Longrightarrow> isSendEP ep \<or> isRecvEP ep"
  by (clarsimp simp: isRecvEP_def isSendEP_def split: Structures_H.endpoint.split)

lemma cpspace_relation_ep_update_ep:
  fixes ep :: "endpoint"
  defines "qs \<equiv> if (isSendEP ep \<or> isRecvEP ep) then set (epQueue ep) else {}"
  assumes koat: "ko_at' ep epptr s"
  and     invs: "invs' s"
  and      cp: "cmap_relation (map_to_eps (ksPSpace s)) (cslift t) Ptr (cendpoint_relation mp)"
  and     rel: "cendpoint_relation mp' ep' endpoint"
  and    mpeq: "(mp' |` (- (tcb_ptr_to_ctcb_ptr ` qs))) = (mp |` (- (tcb_ptr_to_ctcb_ptr ` qs)))"
  shows "cmap_relation (map_to_eps ((ksPSpace s)(epptr \<mapsto> KOEndpoint ep')))
           ((cslift t)(Ptr epptr \<mapsto> endpoint)) Ptr (cendpoint_relation mp')"
  using invs
  apply (intro cpspace_relation_ep_update_an_ep[OF koat cp rel mpeq])
    apply clarsimp+
  apply (clarsimp simp add: qs_def image_image simp del: imp_disjL)
  apply (rule ep_ep_disjoint[OF _ _ koat endpoint_not_idle_cases], auto)
  done

lemma cpspace_relation_ep_update_ep':
  fixes ep :: "endpoint" and ep' :: "endpoint"
    and epptr :: "machine_word" and s :: "kernel_state"
  defines "qs \<equiv> if (isSendEP ep' \<or> isRecvEP ep') then set (epQueue ep') else {}"
  defines "s' \<equiv> s\<lparr>ksPSpace := (ksPSpace s)(epptr \<mapsto> KOEndpoint ep')\<rparr>"
  assumes koat: "ko_at' ep epptr s"
  and       vp: "valid_pspace' s"
  and      cp: "cmap_relation (map_to_eps (ksPSpace s)) (cslift t) Ptr (cendpoint_relation mp)"
  and      srs: "sym_refs (state_refs_of' s')"
  and     rel: "cendpoint_relation mp' ep' endpoint"
  and    mpeq: "(mp' |` (- (tcb_ptr_to_ctcb_ptr ` qs))) = (mp |` (- (tcb_ptr_to_ctcb_ptr ` qs)))"
  shows "cmap_relation (map_to_eps ((ksPSpace s)(epptr \<mapsto> KOEndpoint ep')))
           ((cslift t)(Ptr epptr \<mapsto> endpoint)) Ptr (cendpoint_relation mp')"
proof -
  from koat have koat': "ko_at' ep' epptr s'"
    by (clarsimp simp: obj_at'_def s'_def objBitsKO_def ps_clear_def projectKOs)

  from koat have koat'': "\<And>ep'' epptr'. \<lbrakk> ko_at' ep'' epptr' s; epptr' \<noteq> epptr \<rbrakk>
              \<Longrightarrow> ko_at' ep'' epptr' s'"
    by (clarsimp simp: obj_at'_def s'_def objBitsKO_def ps_clear_def projectKOs)

  show ?thesis using vp ep_ep_disjoint[OF srs koat'' koat' endpoint_not_idle_cases]
  apply (intro cpspace_relation_ep_update_an_ep[OF koat cp rel mpeq])
    apply clarsimp+
  apply (clarsimp simp add: qs_def image_image simp del: imp_disjL)
  done
qed

lemma cnotification_relation_ep_queue:
  assumes   srs: "sym_refs (state_refs_of' s)"
  and      koat: "ko_at' ep epptr s"
  and iswaiting: "(isSendEP ep \<or> isRecvEP ep)"
  and      mpeq: "(mp' |` (- (tcb_ptr_to_ctcb_ptr ` set (epQueue ep))))
  = (mp |` (- (tcb_ptr_to_ctcb_ptr ` set (epQueue ep))))"
  and      koat': "ko_at' a ntfnPtr s"
  shows "cnotification_relation mp a b = cnotification_relation mp' a b"
proof -
  have rl: "\<And>p. \<lbrakk> p \<in> tcb_ptr_to_ctcb_ptr ` set (ntfnQueue (ntfnObj a));
                  isWaitingNtfn (ntfnObj a) \<rbrakk>
    \<Longrightarrow> mp p = mp' p" using srs koat' koat iswaiting mpeq
    apply -
    apply (drule (4) ntfn_ep_disjoint)
    apply (erule restrict_map_eqI [symmetric])
    apply (erule imageE)
    apply (fastforce simp: disjoint_iff_not_equal inj_eq)
    done

  show ?thesis
    unfolding cnotification_relation_def using rl
    apply (simp add: Let_def)
    apply (cases "ntfnObj a")
       apply (simp add: isWaitingNtfn_def cong: tcb_queue_relation'_cong)+
    done
qed

(* FIXME: x64 can be removed? *)
lemma epQueue_head_mask_2 [simp]:
  "epQueue_head_CL (endpoint_lift ko') && ~~ mask 2 = epQueue_head_CL (endpoint_lift ko')"
  unfolding endpoint_lift_def
  oops (*by (clarsimp simp: mask_def word_bw_assocs) *)

lemma epQueue_tail_mask_2 [simp]:
  "epQueue_tail_CL (endpoint_lift ko') && ~~ mask 2 = epQueue_tail_CL (endpoint_lift ko')"
  unfolding endpoint_lift_def
  by (clarsimp simp: mask_def word_bw_assocs sign_extend_def) word_bitwise

lemma epQueue_tail_sign[simp]:
  "sign_extend 47 (epQueue_tail_CL (endpoint_lift ko)) = epQueue_tail_CL (endpoint_lift ko)"
  by (simp add: endpoint_lift_def sign_extend_sign_extend_eq)

(* Clag from cancelSignal_ccorres_helper *)

lemma cancelIPC_ccorres_helper:
  "ccorres dc xfdc (invs' and
         st_tcb_at' (\<lambda>st. (isBlockedOnSend st \<or> isBlockedOnReceive st)
                            \<and> blockingObject st = ep) thread
        and ko_at' ep' ep)
        {s. epptr_' s = Ptr ep}
        []
        (setEndpoint ep (if remove1 thread (epQueue ep') = [] then Structures_H.endpoint.IdleEP
                         else epQueue_update (\<lambda>_. remove1 thread (epQueue ep')) ep'))
        (\<acute>queue :== CALL ep_ptr_get_queue(\<acute>epptr);;
         \<acute>queue :== CALL tcbEPDequeue(tcb_ptr_to_ctcb_ptr thread,\<acute>queue);;
          CALL ep_ptr_set_queue(\<acute>epptr,\<acute>queue);;
          IF head_C \<acute>queue = NULL THEN
              CALL endpoint_ptr_set_state(\<acute>epptr,scast EPState_Idle)
          FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre)
   apply vcg
  apply (clarsimp split del: if_split)
  apply (frule (2) ep_blocked_in_queueD)
  apply (frule (1) ko_at_valid_ep' [OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) valid_ep_blockedD)
  apply (elim conjE)
  apply (frule cmap_relation_ep)
  apply (erule (1) cmap_relation_ko_atE)
  apply (intro conjI)
   apply (erule h_t_valid_clift)
  apply (rule impI)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x = \<sigma> in exI)
   apply (intro conjI)
       apply assumption+
   apply (drule (2) ep_to_ep_queue)
   apply (simp add: tcb_queue_relation'_def)
  apply (clarsimp simp: typ_heap_simps cong: imp_cong split del: if_split)
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (intro impI conjI allI)
   \<comment> \<open>empty case\<close>
   apply clarsimp
   apply (frule iffD1 [OF tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel]])
     apply (rule ballI, erule bspec)
     apply (erule subsetD [rotated])
     apply clarsimp
    subgoal by simp
   apply (simp add: setEndpoint_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: remove1_empty rf_sr_def cstate_relation_def Let_def
                        cpspace_relation_def update_ep_map_tos typ_heap_simps')
       apply (elim conjE)
       apply (intro conjI)
           \<comment> \<open>tcb relation\<close>
           apply (erule ctcb_relation_null_ep_ptrs)
           subgoal by (clarsimp simp: comp_def)
          \<comment> \<open>ep relation\<close>
          apply (rule cpspace_relation_ep_update_ep, assumption+)
           subgoal by (simp add: cendpoint_relation_def Let_def EPState_Idle_def)
          subgoal by simp
         \<comment> \<open>ntfn relation\<close>
         apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
         apply simp
         apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
          subgoal by simp
         apply (erule (1) map_to_ko_atI')
        apply (simp add: heap_to_user_data_def Let_def)
        subgoal by (clarsimp simp: carch_state_relation_def carch_globals_def
                                   fpu_null_state_heap_update_tag_disj_simps
                                   global_ioport_bitmap_heap_update_tag_disj_simps
                                   packed_heap_update_collapse_hrs
                             elim!: fpu_null_state_typ_heap_preservation)
       subgoal by (simp add: cmachine_state_relation_def)
      subgoal by (simp add: h_t_valid_clift_Some_iff)
     subgoal by (simp add: objBits_simps')
    subgoal by (simp add: objBits_simps)
   apply assumption
  \<comment> \<open>non empty case\<close>
  apply clarsimp
  apply (frule tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel])
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
   apply clarsimp
  apply (simp add: setEndpoint_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (frule (1) st_tcb_at_h_t_valid)
      apply (simp add: remove1_empty rf_sr_def cstate_relation_def Let_def
                       cpspace_relation_def update_ep_map_tos typ_heap_simps')
      apply (elim conjE)
      apply (intro conjI)
          \<comment> \<open>tcb relation\<close>
          apply (erule ctcb_relation_null_ep_ptrs)
          subgoal by (clarsimp simp: comp_def)
         \<comment> \<open>ep relation\<close>
         apply (rule cpspace_relation_ep_update_ep, assumption+)
          apply (simp add: cendpoint_relation_def Let_def isSendEP_def isRecvEP_def
                      split: endpoint.splits split del: if_split)
           \<comment> \<open>recv case\<close>
           apply (subgoal_tac "pspace_canonical' \<sigma>")
            prefer 2
            apply fastforce
           apply (clarsimp simp: h_t_valid_clift_Some_iff ctcb_offset_defs
                                 tcb_queue_relation'_next_mask tcb_queue_relation'_prev_mask
                                 tcb_queue_relation'_next_sign tcb_queue_relation'_prev_sign
                           cong: tcb_queue_relation'_cong)
           subgoal by (intro impI conjI; simp)
          \<comment> \<open>send case\<close>
          apply (subgoal_tac "pspace_canonical' \<sigma>")
           prefer 2
           apply fastforce
          apply (clarsimp simp: h_t_valid_clift_Some_iff ctcb_offset_defs
                                tcb_queue_relation'_next_mask tcb_queue_relation'_prev_mask
                                tcb_queue_relation'_next_sign tcb_queue_relation'_prev_sign
                         cong: tcb_queue_relation'_cong)
          subgoal by (intro impI conjI; simp)
         \<comment> \<open>send case\<close>
         apply (subgoal_tac "pspace_canonical' \<sigma>")
          prefer 2
          apply fastforce
         apply (clarsimp simp: h_t_valid_clift_Some_iff ctcb_offset_defs
                               tcb_queue_relation'_next_mask tcb_queue_relation'_prev_mask
                               tcb_queue_relation'_next_sign tcb_queue_relation'_prev_sign
                         cong: tcb_queue_relation'_cong)
        \<comment> \<open>ntfn relation\<close>
        apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
        apply simp
        apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
        apply simp
        apply (erule (1) map_to_ko_atI')
       subgoal by (clarsimp simp: carch_state_relation_def carch_globals_def
                                  fpu_null_state_heap_update_tag_disj_simps
                                  global_ioport_bitmap_heap_update_tag_disj_simps
                                  packed_heap_update_collapse_hrs
                            elim!: fpu_null_state_typ_heap_preservation)
      subgoal by (simp add: cmachine_state_relation_def)
     subgoal by (simp add: h_t_valid_clift_Some_iff)
    subgoal by (simp add: objBits_simps')
   subgoal by (simp add: objBits_simps)
  by assumption

lemma getThreadState_ccorres_foo:
  "(\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c) \<Longrightarrow>
    ccorres r xf (\<lambda>s. \<forall>ts. st_tcb_at' ((=) ts) t s \<longrightarrow> P ts s)
                 {s. \<forall>ts tcb'. cslift s (tcb_ptr_to_ctcb_ptr t) = Some tcb'
                              \<and> cthread_state_relation ts (tcbState_C tcb', tcbFault_C tcb')
                            \<longrightarrow> s \<in> P' ts} hs
        (getThreadState t >>= f) c"
  apply (rule ccorres_symb_exec_l' [OF _ gts_inv' gts_sp' empty_fail_getThreadState])
  apply (erule_tac x=rv in meta_allE)
  apply (erule ccorres_guard_imp2)
  apply (clarsimp simp: st_tcb_at'_def)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule cmap_relationE1 [OF cmap_relation_tcb])
   apply (erule ko_at_projectKO_opt)
  apply (clarsimp simp: ctcb_relation_def obj_at'_def)
  done

lemma ep_blocked_in_queueD_recv:
  "\<lbrakk>st_tcb_at' ((=) (Structures_H.thread_state.BlockedOnReceive x gr)) thread \<sigma>; ko_at' ep' x \<sigma>; invs' \<sigma>\<rbrakk> \<Longrightarrow> thread \<in> set (epQueue ep') \<and> isRecvEP ep'"
  apply (frule sym_refs_st_tcb_atD', clarsimp)
  apply (clarsimp simp: refs_of_rev' obj_at'_def ko_wp_at'_def projectKOs)
  apply (cases ep', simp_all add: isSendEP_def isRecvEP_def)[1]
  done

lemma ep_blocked_in_queueD_send:
  "\<lbrakk>st_tcb_at' ((=) (Structures_H.thread_state.BlockedOnSend x xa xb xc xd)) thread \<sigma>; ko_at' ep' x \<sigma>; invs' \<sigma>\<rbrakk> \<Longrightarrow> thread \<in> set (epQueue ep') \<and> isSendEP ep'"
  apply (frule sym_refs_st_tcb_atD', clarsimp)
  apply (clarsimp simp: refs_of_rev' obj_at'_def ko_wp_at'_def projectKOs)
  apply (cases ep', simp_all add: isSendEP_def isRecvEP_def)[1]
  done

lemma cancelIPC_ccorres1:
  assumes cteDeleteOne_ccorres:
  "\<And>w slot. ccorres dc xfdc
   (invs' and cte_wp_at' (\<lambda>ct. w = -1 \<or> cteCap ct = NullCap
        \<or> (\<forall>cap'. ccap_relation (cteCap ct) cap' \<longrightarrow> cap_get_tag cap' = w)) slot)
   ({s. gs_get_assn cteDeleteOne_'proc (ghost'state_' (globals s)) = w}
        \<inter> {s. slot_' s = Ptr slot}) []
   (cteDeleteOne slot) (Call cteDeleteOne_'proc)"
  shows
  "ccorres dc xfdc (tcb_at' thread and invs')
                   (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) []
          (cancelIPC thread) (Call cancelIPC_'proc)"
  apply (cinit lift: tptr_' simp: Let_def cong: call_ignore_cong)
   apply (rule ccorres_move_c_guard_tcb)
   apply csymbr
   apply (rule getThreadState_ccorres_foo)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=ret__unsigned_longlong_' in ccorres_abstract, ceqv)
     apply (rule_tac P="rv' = thread_state_to_tsType rv" in ccorres_gen_asm2)
     apply wpc
            \<comment> \<open>BlockedOnReceive\<close>
            apply (simp add: word_sle_def ccorres_cond_iffs cong: call_ignore_cong)
            apply (rule ccorres_rhs_assoc)+
            apply csymbr
            apply csymbr
            apply (rule ccorres_pre_getEndpoint)
            apply (rule ccorres_assert)
            apply (rule ccorres_symb_exec_r) \<comment> \<open>ptr_get lemmas don't work so well :(\<close>
              apply (rule ccorres_symb_exec_r)
                apply (simp only: fun_app_def simp_list_case_return
                                  return_bind ccorres_seq_skip)
                apply (rule ccorres_rhs_assoc2)
                apply (rule ccorres_rhs_assoc2)
                apply (rule ccorres_rhs_assoc2)
                apply (ctac (no_vcg) add: cancelIPC_ccorres_helper)
                  apply (ctac add: setThreadState_ccorres_valid_queues')
                 apply (wp hoare_vcg_all_lift set_ep_valid_objs' | simp add: valid_tcb_state'_def split del: if_split)+
                apply (simp add: ThreadState_defs)
               apply vcg
              apply (rule conseqPre, vcg)
              apply clarsimp
             apply clarsimp
             apply (rule conseqPre, vcg)
             apply (rule subset_refl)
            apply (rule conseqPre, vcg)
            apply clarsimp
          \<comment> \<open>BlockedOnReply case\<close>
           apply (simp add: ThreadState_defs ccorres_cond_iffs
                            Collect_False Collect_True word_sle_def
                      cong: call_ignore_cong del: Collect_const)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply (unfold comp_def)[1]
           apply csymbr
           apply (rule ccorres_move_c_guard_tcb)+
           apply (rule ccorres_split_nothrow_novcg)
               apply (rule_tac P=\<top> in threadSet_ccorres_lemma2)
                apply vcg
               apply (clarsimp simp: typ_heap_simps')
               apply (erule(1) rf_sr_tcb_update_no_queue2,
                 (simp add: typ_heap_simps')+)[1]
                apply (rule ball_tcb_cte_casesI, simp_all)[1]
               apply (clarsimp simp: ctcb_relation_def seL4_Fault_lift_NullFault
                                     cfault_rel_def cthread_state_relation_def)
               apply (case_tac "tcbState tcb", simp_all add: is_cap_fault_def)[1]
              apply ceqv
             apply ccorres_remove_UNIV_guard
             apply (rule ccorres_move_array_assertion_tcb_ctes)
             apply (rule_tac P="tcb_at' thread" in ccorres_cross_over_guard)
             apply (simp add: getThreadReplySlot_def)
             apply ctac
               apply (simp only: liftM_def bind_assoc return_bind del: Collect_const)
               apply (rule ccorres_pre_getCTE)
               apply (rename_tac slot slot' cte)
               apply (rule ccorres_move_c_guard_cte)
               apply (rule_tac xf'=ret__unsigned_longlong_' and val="mdbNext (cteMDBNode cte)"
                         and R="cte_wp_at' ((=) cte) slot and invs'"
                          in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
                  apply vcg
                  apply (clarsimp simp: cte_wp_at_ctes_of)
                  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
                  apply (clarsimp simp: typ_heap_simps)
                  apply (clarsimp simp: ccte_relation_def map_option_Some_eq2)
                 apply ceqv
                apply csymbr
                apply (rule ccorres_Cond_rhs)
                 apply (simp add: nullPointer_def when_def)
                 apply (rule ccorres_symb_exec_l[OF _ _ _ empty_fail_stateAssert])
                   apply (rule ccorres_symb_exec_r)
                     apply (ctac add: cteDeleteOne_ccorres[where w1="scast cap_reply_cap"])
                    apply vcg
                   apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
                       gs_set_assn_Delete_cstate_relation[unfolded o_def])
                  apply (wp | simp)+
                apply (rule ccorres_return_Skip)
               apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                                ghost_assertion_data_set_def cap_tag_defs)
              apply (simp add: locateSlot_conv, wp)
             apply vcg
            apply (rule_tac Q="\<lambda>rv. tcb_at' thread and invs'" in hoare_post_imp)
             apply (clarsimp simp: cte_wp_at_ctes_of capHasProperty_def
                                   cap_get_tag_isCap ucast_id)
            apply (wp threadSet_invs_trivial | simp)+
           apply (clarsimp simp add: guard_is_UNIV_def tcbReplySlot_def
                        Kernel_C.tcbReply_def tcbCNodeEntries_def)
          \<comment> \<open>BlockedOnNotification\<close>
          apply (simp add: word_sle_def ThreadState_defs ccorres_cond_iffs
                     cong: call_ignore_cong)
          apply (rule ccorres_symb_exec_r)
            apply (ctac (no_vcg))
           apply clarsimp
           apply (rule conseqPre, vcg)
           apply (rule subset_refl)
          apply (rule conseqPre, vcg)
          apply clarsimp
         \<comment> \<open>Running, Inactive, and Idle\<close>
         apply (simp add: word_sle_def ThreadState_defs ccorres_cond_iffs
                    cong: call_ignore_cong,
                rule ccorres_return_Skip)+
      \<comment> \<open>BlockedOnSend\<close>
      apply (simp add: word_sle_def ccorres_cond_iffs
                 cong: call_ignore_cong)
      \<comment> \<open>clag\<close>
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply (rule ccorres_pre_getEndpoint)
      apply (rule ccorres_assert)
      apply (rule ccorres_symb_exec_r) \<comment> \<open>ptr_get lemmas don't work so well :(\<close>
        apply (rule ccorres_symb_exec_r)
          apply (simp only: fun_app_def simp_list_case_return return_bind ccorres_seq_skip)
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_rhs_assoc2)
          apply (ctac (no_vcg) add: cancelIPC_ccorres_helper)
            apply (ctac add: setThreadState_ccorres_valid_queues')
           apply (wp hoare_vcg_all_lift set_ep_valid_objs' | simp add: valid_tcb_state'_def split del:if_split)+
       apply (simp add: ThreadState_defs)
         apply clarsimp
         apply (rule conseqPre, vcg, rule subset_refl)
        apply (rule conseqPre, vcg)
        apply clarsimp
       apply clarsimp
       apply (rule conseqPre, vcg, rule subset_refl)
      apply (rule conseqPre, vcg)
      apply clarsimp
  \<comment> \<open>Restart\<close>
     apply (simp add: word_sle_def ThreadState_defs ccorres_cond_iffs
                cong: call_ignore_cong,
            rule ccorres_return_Skip)
    \<comment> \<open>Post wp proofs\<close>
    apply vcg
   apply clarsimp
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply clarsimp
  apply (drule(1) obj_at_cslift_tcb)
  apply clarsimp
  apply (frule obj_at_valid_objs', clarsimp+)
  apply (clarsimp simp: projectKOs valid_obj'_def valid_tcb'_def
                        valid_tcb_state'_def typ_heap_simps
                        word_sle_def)
  apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp)
    apply (rule conjI)
     subgoal by (auto simp: projectKOs obj_at'_def pred_tcb_at'_def split: thread_state.splits)[1]
    apply (clarsimp)
    apply (rule conjI)
     subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                     isTS_defs cte_wp_at_ctes_of
                     cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                     split: thread_state.splits)
    apply clarsimp
    apply (frule (2) ep_blocked_in_queueD_recv)
    apply (frule (1) ko_at_valid_ep'[OF _ invs_valid_objs'])
    subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                         isTS_defs cte_wp_at_ctes_of isRecvEP_def
                         cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                    split: thread_state.splits endpoint.splits)
   apply (rule conjI)
    apply (clarsimp simp: inQ_def)
   apply clarsimp
   apply (rule conjI)
    subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                         isTS_defs cte_wp_at_ctes_of
                         cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                    split: thread_state.splits)
   apply clarsimp
   apply (rule conjI)
    subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                         isTS_defs cte_wp_at_ctes_of
                         cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                    split: thread_state.splits)
   apply clarsimp
   apply (frule (2) ep_blocked_in_queueD_send)
   apply (frule (1) ko_at_valid_ep'[OF _ invs_valid_objs'])
   subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                        isTS_defs cte_wp_at_ctes_of isSendEP_def
                        cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                   split: thread_state.splits endpoint.splits)[1]
  apply (auto simp: isTS_defs cthread_state_relation_def typ_heap_simps weak_sch_act_wf_def)
  apply (case_tac ts,
           auto simp: isTS_defs cthread_state_relation_def typ_heap_simps)
  done

end
end
