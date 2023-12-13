(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IpcCancel_C
imports SyscallArgs_C
begin

context kernel_m
begin

lemma cready_queues_index_to_C_in_range':
  assumes prems: "qdom \<le> ucast maxDom" "prio \<le> ucast maxPrio"
  shows "cready_queues_index_to_C qdom prio < num_tcb_queues"
proof -
  have P: "unat prio < numPriorities"
    using prems
    by (simp add: numPriorities_def seL4_MaxPrio_def Suc_le_lessD unat_le_helper)
  have Q: "unat qdom < numDomains"
    using prems
    by (simp add: maxDom_to_H le_maxDomain_eq_less_numDomains word_le_nat_alt)
  show ?thesis
    using mod_lemma[OF _ P, where q="unat qdom" and c=numDomains] Q
    by (clarsimp simp: num_tcb_queues_calculation cready_queues_index_to_C_def field_simps)
qed

lemmas cready_queues_index_to_C_in_range =
  cready_queues_index_to_C_in_range'[simplified num_tcb_queues_def]

lemma cready_queues_index_to_C_inj:
  "\<lbrakk> cready_queues_index_to_C qdom prio = cready_queues_index_to_C qdom' prio';
     prio \<le> ucast maxPrio; prio' \<le> ucast maxPrio \<rbrakk> \<Longrightarrow> prio = prio' \<and> qdom = qdom'"
  apply (rule context_conjI)
  apply (auto simp: cready_queues_index_to_C_def numPriorities_def
                    seL4_MaxPrio_def word_le_nat_alt dest: arg_cong[where f="\<lambda>x. x mod 256"])
  done

lemma cready_queues_index_to_C_distinct:
  "\<lbrakk> qdom = qdom' \<longrightarrow> prio \<noteq> prio'; prio \<le> ucast maxPrio; prio' \<le> ucast maxPrio \<rbrakk>
   \<Longrightarrow> cready_queues_index_to_C qdom prio \<noteq> cready_queues_index_to_C qdom' prio'"
  apply (auto simp: cready_queues_index_to_C_inj)
  done

lemma cstate_relation_ksReadyQueues_update:
  "\<lbrakk> cstate_relation hs cs; arr = ksReadyQueues_' cs;
     sched_queue_relation' (clift (t_hrs_' cs)) v (head_C v') (end_C v');
     qdom \<le> ucast maxDom; prio \<le> ucast maxPrio \<rbrakk>
    \<Longrightarrow> cstate_relation (ksReadyQueues_update (\<lambda>qs. qs ((qdom, prio) := v)) hs)
                        (ksReadyQueues_'_update (\<lambda>_. Arrays.update arr
                                                        (cready_queues_index_to_C qdom prio) v') cs)"
  apply (clarsimp simp: cstate_relation_def Let_def
                        cmachine_state_relation_def
                        carch_state_relation_def carch_globals_def
                        cready_queues_relation_def seL4_MinPrio_def minDom_def)
  apply (frule cready_queues_index_to_C_in_range, assumption)
  apply clarsimp
  apply (frule_tac qdom=qdoma and prio=prioa in cready_queues_index_to_C_in_range, assumption)
  apply (frule cready_queues_index_to_C_distinct, assumption+)
  apply clarsimp
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

lemma valid_queuesD':
  "\<lbrakk> obj_at' (inQ d p) t s; valid_queues' s \<rbrakk>
        \<Longrightarrow> t \<in> set (ksReadyQueues s (d, p))"
  by (simp add: valid_queues'_def)

lemma invs_valid_queues'[elim!]:
  "invs' s \<Longrightarrow> valid_queues' s"
  by (simp add: invs'_def valid_state'_def)


lemma ntfn_ptr_get_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> \<sigma> \<Turnstile>\<^sub>c \<^bsup>\<sigma>\<^esup>ntfnPtr} \<acute>ret__struct_tcb_queue_C :== PROC ntfn_ptr_get_queue(\<acute>ntfnPtr)
       \<lbrace>head_C \<acute>ret__struct_tcb_queue_C = Ptr (ntfnQueue_head_CL (notification_lift (the (cslift s \<^bsup>s\<^esup>ntfnPtr)))) \<and>
        end_C \<acute>ret__struct_tcb_queue_C = Ptr (ntfnQueue_tail_CL (notification_lift (the (cslift s \<^bsup>s\<^esup>ntfnPtr))))\<rbrace>"
  apply vcg
  apply clarsimp
  done

abbreviation
  "cslift_all_but_tcb_C s t \<equiv> (cslift s :: cte_C typ_heap) = cslift t
          \<and> (cslift s :: endpoint_C typ_heap) = cslift t
          \<and> (cslift s :: notification_C typ_heap) = cslift t
          \<and> (cslift s :: vcpu_C typ_heap) = cslift t
          \<and> (cslift s :: asid_pool_C typ_heap) = cslift t
          \<and> (cslift s :: pte_C typ_heap) = cslift t
          \<and> (cslift s :: user_data_C typ_heap) = cslift t
          \<and> (cslift s :: user_data_device_C typ_heap) = cslift t"

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
  apply (intro allI conjI impI) (* FIXME AARCH64 different number of goals, not sure why *)
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
        apply (rule ext)
        apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def
                        cong: if_weak_cong)
       apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff c_guard_clift)
      apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff
                      cong: if_weak_cong)
     apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def)
    apply (rule ext)
    apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def)
   apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff c_guard_clift)
  apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff c_guard_clift)
  done

lemma ntfn_ptr_set_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. s \<Turnstile>\<^sub>c \<acute>ntfnPtr\<rbrace> Call ntfn_ptr_set_queue_'proc
           {t. (\<exists>ntfn'. notification_lift ntfn' =
  (notification_lift (the (cslift s (\<^bsup>s\<^esup>ntfnPtr))))\<lparr>
    ntfnQueue_head_CL := make_canonical (ptr_val (head_C \<^bsup>s\<^esup>ntfn_queue)),
    ntfnQueue_tail_CL := make_canonical (ptr_val (end_C \<^bsup>s\<^esup>ntfn_queue)) \<rparr>
            \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (\<^bsup>s\<^esup>ntfnPtr) ntfn')
                (t_hrs_' (globals s)))}"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: packed_heap_update_collapse_hrs typ_heap_simps' make_canonical_def
                        canonical_bit_def)
  done

(* FIXME AARCH64: move up into TcbQueue_C *)
lemma tcb_queue_relation_next_canonical:
  assumes "tcb_queue_relation getNext getPrev mp queue NULL qhead"
  assumes valid_ep: "\<forall>t\<in>set queue. tcb_at' t s"
                    "distinct queue"
                    "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
                    "tcbp \<in> set queue"
  assumes canon: "pspace_canonical' s"
  shows "make_canonical (ptr_val (getNext tcb)) = ptr_val (getNext tcb)"
proof (cases "getNext tcb = NULL")
  case True
  thus ?thesis by simp
next
  case False
  hence "ctcb_ptr_to_tcb_ptr (getNext tcb) \<in> set queue" using assms
    by (fastforce dest: tcb_queueD split: if_split_asm)
  with valid_ep(1)
  have tcb: "tcb_at' (ctcb_ptr_to_tcb_ptr (getNext tcb)) s" ..
  with canon
  have "canonical_address (ctcb_ptr_to_tcb_ptr (getNext tcb))"
    by (simp add: obj_at'_is_canonical)
  moreover
  have "is_aligned (ctcb_ptr_to_tcb_ptr (getNext tcb)) tcbBlockSizeBits"
    using tcb by (rule tcb_aligned')
  ultimately
  have "canonical_address (ptr_val (getNext tcb))"
    by (rule canonical_address_ctcb_ptr)
  thus ?thesis
    by (simp add: canonical_make_canonical_idem)
qed

lemma tcb_queue_relation'_next_canonical:
  "\<lbrakk> tcb_queue_relation' getNext getPrev mp queue qhead qend; \<forall>t\<in>set queue. tcb_at' t s;
     distinct queue; mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb; tcbp \<in> set queue;
     pspace_canonical' s\<rbrakk>
   \<Longrightarrow> make_canonical (ptr_val (getNext tcb)) = ptr_val (getNext tcb)"
  by (rule tcb_queue_relation_next_canonical [OF tcb_queue_relation'_queue_rel])

(* FIXME AARCH64: move up into TcbQueue_C *)
lemma tcb_queue_relation_prev_canonical:
  assumes "tcb_queue_relation getNext getPrev mp queue NULL qhead"
  assumes valid_ep: "\<forall>t\<in>set queue. tcb_at' t s"
                    "distinct queue"
                    "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
                    "tcbp \<in> set queue"
  assumes canon: "pspace_canonical' s"
  shows "make_canonical (ptr_val (getPrev tcb)) = ptr_val (getPrev tcb)"
proof (cases "getPrev tcb = NULL")
  case True
  thus ?thesis by simp
next
  case False
  hence "ctcb_ptr_to_tcb_ptr (getPrev tcb) \<in> set queue" using assms
    by (fastforce dest: tcb_queueD split: if_split_asm)
  with valid_ep(1)
  have tcb: "tcb_at' (ctcb_ptr_to_tcb_ptr (getPrev tcb)) s" ..
  with canon
  have "canonical_address (ctcb_ptr_to_tcb_ptr (getPrev tcb))"
    by (simp add: obj_at'_is_canonical)
  moreover
  have "is_aligned (ctcb_ptr_to_tcb_ptr (getPrev tcb)) tcbBlockSizeBits"
    using tcb by (rule tcb_aligned')
  ultimately
  have "canonical_address (ptr_val (getPrev tcb))"
    by (rule canonical_address_ctcb_ptr)
  thus ?thesis
    by (simp add: canonical_make_canonical_idem)
qed

lemma tcb_queue_relation'_prev_canonical:
  "\<lbrakk> tcb_queue_relation' getNext getPrev mp queue qhead qend; \<forall>t\<in>set queue. tcb_at' t s;
     distinct queue; mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb; tcbp \<in> set queue;
     pspace_canonical' s\<rbrakk>
   \<Longrightarrow> make_canonical (ptr_val (getPrev tcb)) = ptr_val (getPrev tcb)"
  by (rule tcb_queue_relation_prev_canonical [OF tcb_queue_relation'_queue_rel])

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
            apply (erule ctcb_relation_null_queue_ptrs)
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
         \<comment> \<open>queue relation\<close>
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (clarsimp simp: carch_state_relation_def carch_globals_def
                              typ_heap_simps' packed_heap_update_collapse_hrs)
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
           apply (erule ctcb_relation_null_queue_ptrs)
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
           apply (subst tcb_queue_relation'_next_canonical; assumption?)
            apply fastforce
           apply (simp add: notification_lift_def make_canonical_def canonical_bit_def)
          apply (clarsimp simp: h_t_valid_clift_Some_iff notification_lift_def)
          apply (subst tcb_queue_relation'_prev_canonical; assumption?)
           apply fastforce
          apply (simp add: make_canonical_def canonical_bit_def)
         apply simp
        \<comment> \<open>queue relation\<close>
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        apply (clarsimp simp: comp_def)
       subgoal by (clarsimp simp: carch_state_relation_def carch_globals_def)
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
    apply (simp add: "StrictC'_thread_state_defs")+
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
       apply (simp add: "StrictC'_thread_state_defs")+
  done



lemma tcb_queue_relation_update_head:
  fixes getNext_update :: "(tcb_C ptr \<Rightarrow> tcb_C ptr) \<Rightarrow> tcb_C \<Rightarrow> tcb_C" and
  getPrev_update :: "(tcb_C ptr \<Rightarrow> tcb_C ptr) \<Rightarrow> tcb_C \<Rightarrow> tcb_C"
  assumes qr: "tcb_queue_relation getNext getPrev mp queue NULL qhead"
  and     qh': "qhead' \<notin> tcb_ptr_to_ctcb_ptr ` set queue"
  and  cs_tcb: "mp qhead' = Some tcb"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and     qhN: "qhead' \<noteq> NULL"
  and     fgN: "fg_cons getNext (getNext_update \<circ> (\<lambda>x _. x))"
  and     fgP: "fg_cons getPrev (getPrev_update \<circ> (\<lambda>x _. x))"
  and     npu: "\<And>f t. getNext (getPrev_update f t) = getNext t"
  and     pnu: "\<And>f t. getPrev (getNext_update f t) = getPrev t"
  shows   "tcb_queue_relation getNext getPrev
                 (upd_unless_null qhead (getPrev_update (\<lambda>_. qhead') (the (mp qhead)))
                       (mp(qhead' := Some (getPrev_update (\<lambda>_. NULL) (getNext_update (\<lambda>_. qhead)  tcb)))))
                 (ctcb_ptr_to_tcb_ptr qhead' # queue) NULL qhead'"
  using qr qh' cs_tcb valid_ep qhN
  apply (subgoal_tac "qhead \<noteq> qhead'")
  apply (clarsimp simp: pnu upd_unless_null_def fg_consD1 [OF fgN] fg_consD1 [OF fgP] npu)
  apply (cases queue)
    apply simp
   apply (frule (2) tcb_queue_relation_next_not_NULL)
    apply simp
   apply (clarsimp simp: fg_consD1 [OF fgN] fg_consD1 [OF fgP] pnu npu)
   apply (subst tcb_queue_relation_cong [OF refl refl refl, where mp' = mp])
    apply (clarsimp simp: inj_eq)
    apply (intro impI conjI)
     apply (frule_tac x = x in imageI [where f = tcb_ptr_to_ctcb_ptr])
     apply simp
    apply simp
   apply simp
  apply clarsimp
  apply (cases queue)
   apply simp
  apply simp
  done

lemma tcbSchedEnqueue_update:
  assumes sr: "sched_queue_relation' mp queue qhead qend"
  and     qh': "qhead' \<notin> tcb_ptr_to_ctcb_ptr ` set queue"
  and  cs_tcb: "mp qhead' = Some tcb"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and     qhN: "qhead' \<noteq> NULL"
  shows
  "sched_queue_relation'
                   (upd_unless_null qhead (tcbSchedPrev_C_update (\<lambda>_. qhead') (the (mp qhead)))
                (mp(qhead' \<mapsto> tcb\<lparr>tcbSchedNext_C := qhead, tcbSchedPrev_C := NULL\<rparr>)))
            (ctcb_ptr_to_tcb_ptr qhead' # queue) qhead' (if qend = NULL then qhead' else qend)"
  using sr qh' cs_tcb valid_ep qhN
  apply -
  apply (erule tcb_queue_relationE')
  apply (rule tcb_queue_relationI')
   apply (erule (5) tcb_queue_relation_update_head
        [where getNext_update = tcbSchedNext_C_update and getPrev_update = tcbSchedPrev_C_update], simp_all)[1]
  apply simp
  apply (intro impI)
  apply (erule (1) tcb_queue_relation_not_NULL')
  apply simp
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

lemma tcb_queue'_head_end_NULL:
  assumes qr: "tcb_queue_relation' getNext getPrev mp queue qhead qend"
  and   tat: "\<forall>t\<in>set queue. tcb_at' t s"
  shows "(qend = NULL) = (qhead = NULL)"
  using qr tat
  apply -
  apply (erule tcb_queue_relationE')
  apply (simp add: tcb_queue_head_empty_iff)
  apply (rule impI)
  apply (rule tcb_at_not_NULL)
  apply (erule bspec)
  apply simp
  done

lemma tcb_queue_relation_qhead_mem:
  "\<lbrakk> tcb_queue_relation getNext getPrev mp queue NULL qhead;
  (\<forall>tcb\<in>set queue. tcb_at' tcb t) \<rbrakk>
  \<Longrightarrow> qhead \<noteq> NULL \<longrightarrow> ctcb_ptr_to_tcb_ptr qhead \<in> set queue"
  by (clarsimp simp: tcb_queue_head_empty_iff tcb_queue_relation_head_hd)

lemma tcb_queue_relation_qhead_valid:
  "\<lbrakk> tcb_queue_relation getNext getPrev (cslift s') queue NULL qhead;
  (s, s') \<in> rf_sr; (\<forall>tcb\<in>set queue. tcb_at' tcb s) \<rbrakk>
  \<Longrightarrow> qhead \<noteq> NULL \<longrightarrow> s' \<Turnstile>\<^sub>c qhead"
  apply (frule (1) tcb_queue_relation_qhead_mem)
  apply clarsimp
  apply(drule (3) tcb_queue_memberD)
  apply (simp add: h_t_valid_clift_Some_iff)
  done

lemmas tcb_queue_relation_qhead_mem' = tcb_queue_relation_qhead_mem [OF tcb_queue_relation'_queue_rel]
lemmas tcb_queue_relation_qhead_valid' = tcb_queue_relation_qhead_valid [OF tcb_queue_relation'_queue_rel]


lemma valid_queues_valid_q:
  "valid_queues s \<Longrightarrow> (\<forall>tcb\<in>set (ksReadyQueues s (qdom, prio)). tcb_at' tcb s) \<and> distinct (ksReadyQueues s (qdom, prio))"
  apply (clarsimp simp: valid_queues_def valid_queues_no_bitmap_def)
  apply (drule spec [where x = qdom])
  apply (drule spec [where x = prio])
  apply clarsimp
  apply (drule (1) bspec, erule obj_at'_weakenE)
  apply simp
  done

lemma invs_valid_q:
  "invs' s \<Longrightarrow> (\<forall>tcb\<in>set (ksReadyQueues s (qdom, prio)). tcb_at' tcb s) \<and> distinct (ksReadyQueues s (qdom, prio))"
  apply (rule valid_queues_valid_q)
  apply (clarsimp simp: invs'_def valid_state'_def)
  done

lemma tcbQueued_not_in_queues:
  assumes vq: "valid_queues s"
  and    objat: "obj_at' (Not \<circ> tcbQueued) thread s"
  shows   "thread \<notin> set (ksReadyQueues s (d, p))"
  using vq objat
  apply -
  apply clarsimp
  apply (drule (1) valid_queues_obj_at'D)
  apply (erule obj_atE')+
  apply (clarsimp simp: inQ_def)
  done


lemma rf_sr_sched_queue_relation:
  "\<lbrakk> (s, s') \<in> rf_sr; d \<le> ucast maxDom; p \<le> ucast maxPrio \<rbrakk>
  \<Longrightarrow> sched_queue_relation' (cslift s') (ksReadyQueues s (d, p))
                                        (head_C (index (ksReadyQueues_' (globals s'))
                                                       (cready_queues_index_to_C d p)))
                                        (end_C (index (ksReadyQueues_' (globals s'))
                                                      (cready_queues_index_to_C d p)))"
  unfolding rf_sr_def cstate_relation_def cready_queues_relation_def
  apply (clarsimp simp: Let_def seL4_MinPrio_def minDom_def)
  done

lemma ready_queue_not_in:
  assumes  vq: "valid_queues s"
  and     inq: "t \<in> set (ksReadyQueues s (d, p))"
  and     neq: "d \<noteq> d' \<or> p \<noteq> p'"
  shows   "t \<notin> set (ksReadyQueues s (d', p'))"
proof
  assume "t \<in> set (ksReadyQueues s (d', p'))"
  hence "obj_at' (inQ d' p') t s" using vq by (rule valid_queues_obj_at'D)
  moreover have "obj_at' (inQ d p) t s" using inq vq by (rule valid_queues_obj_at'D)
  ultimately show False using neq
    by (clarsimp elim!: obj_atE' simp: inQ_def)
qed

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

lemma ccorres_pre_getQueue:
  assumes cc: "\<And>queue. ccorres r xf (P queue) (P' queue) hs (f queue) c"
  shows   "ccorres r xf (\<lambda>s. P (ksReadyQueues s (d, p)) s \<and> d \<le> maxDomain \<and> p \<le> maxPriority)
                        {s'. \<forall>queue. (let cqueue = index (ksReadyQueues_' (globals s'))
                                                         (cready_queues_index_to_C d p) in
                                      sched_queue_relation' (cslift s') queue (head_C cqueue) (end_C cqueue)) \<longrightarrow> s' \<in> P' queue}
           hs (getQueue d p >>= (\<lambda>queue. f queue)) c"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_symb_exec_l2)
     defer
     defer
     apply (rule gq_sp)
    defer
    apply (rule ccorres_guard_imp)
    apply (rule cc)
     apply clarsimp
     apply assumption
    apply assumption
   apply (clarsimp simp: getQueue_def gets_exs_valid)
  apply clarsimp
  apply (drule spec, erule mp)
  apply (simp add: Let_def)
  apply (erule rf_sr_sched_queue_relation)
   apply (simp add: maxDom_to_H maxPrio_to_H)+
  done

lemma state_relation_queue_update_helper':
  "\<lbrakk> (s, s') \<in> rf_sr;
     (\<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s)
                                       \<and> distinct (ksReadyQueues s (d, p)));
          globals t = ksReadyQueues_'_update
             (\<lambda>_. Arrays.update (ksReadyQueues_' (globals s')) prio' q')
             (t_hrs_'_update f (globals s'));
          sched_queue_relation' (cslift t) q (head_C q') (end_C q');
          cslift t |` ( - tcb_ptr_to_ctcb_ptr ` S )
             = cslift s' |` ( - tcb_ptr_to_ctcb_ptr ` S );
          option_map tcb_null_sched_ptrs \<circ> cslift t
            = option_map tcb_null_sched_ptrs \<circ> cslift s';
          cslift_all_but_tcb_C t s';
          zero_ranges_are_zero (gsUntypedZeroRanges s) (f (t_hrs_' (globals s')))
              = zero_ranges_are_zero (gsUntypedZeroRanges s) (t_hrs_' (globals s'));
          hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s'));
          prio' = cready_queues_index_to_C qdom prio;
          \<forall>x \<in> S. obj_at' (inQ qdom prio) x s
                   \<or> (obj_at' (\<lambda>tcb. tcbPriority tcb = prio) x s
                       \<and> obj_at' (\<lambda>tcb. tcbDomain tcb = qdom) x s)
                   \<or> (tcb_at' x s \<and> (\<forall>d' p'. (d' \<noteq> qdom \<or> p' \<noteq> prio)
                                         \<longrightarrow> x \<notin> set (ksReadyQueues s (d', p'))));
          S \<noteq> {}; qdom \<le> ucast maxDom; prio \<le> ucast maxPrio \<rbrakk>
      \<Longrightarrow> (s \<lparr>ksReadyQueues := (ksReadyQueues s)((qdom, prio) := q)\<rparr>, t) \<in> rf_sr"
  apply (subst(asm) disj_imp_rhs)
   apply (subst obj_at'_and[symmetric])
   apply (rule disjI1, erule obj_at'_weakenE, simp add: inQ_def)
  apply (subst(asm) disj_imp_rhs)
   apply (subst(asm) obj_at'_and[symmetric])
   apply (rule conjI, erule obj_at'_weakenE, simp)
   apply (rule allI, rule allI)
   apply (drule_tac x=d' in spec)
   apply (drule_tac x=p' in spec)
   apply clarsimp
   apply (drule(1) bspec)
   apply (clarsimp simp: inQ_def obj_at'_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (intro conjI)
      \<comment> \<open>cpspace_relation\<close>
     apply (erule nonemptyE, drule(1) bspec)
     apply (clarsimp simp: cpspace_relation_def)
     apply (drule obj_at_ko_at', clarsimp)
     apply (rule cmap_relationE1, assumption,
            erule ko_at_projectKO_opt)
     apply (frule null_sched_queue)
     apply (frule null_sched_epD)
     apply (intro conjI)
       \<comment> \<open>tcb relation\<close>
       apply (drule ctcb_relation_null_queue_ptrs,
              simp_all)[1]
      \<comment> \<open>endpoint relation\<close>
      apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
      apply simp
      apply (erule cendpoint_relation_upd_tcb_no_queues, simp+)
     \<comment> \<open>ntfn relation\<close>
     apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
     apply simp
     apply (erule cnotification_relation_upd_tcb_no_queues, simp+)
    \<comment> \<open>ready queues\<close>
    apply (simp add: cready_queues_relation_def Let_def cready_queues_index_to_C_in_range
                     seL4_MinPrio_def minDom_def)
    apply clarsimp
    apply (frule cready_queues_index_to_C_distinct, assumption+)
    apply (clarsimp simp: cready_queues_index_to_C_in_range all_conj_distrib)
    apply (rule iffD1 [OF tcb_queue_relation'_cong[OF refl], rotated -1],
           drule spec, drule spec, erule mp, simp+)
    apply clarsimp
    apply (drule_tac x="tcb_ptr_to_ctcb_ptr x" in fun_cong)+
    apply (clarsimp simp: restrict_map_def
                   split: if_split_asm)
   by (auto simp: carch_state_relation_def cmachine_state_relation_def)

lemma state_relation_queue_update_helper:
  "\<lbrakk> (s, s') \<in> rf_sr; valid_queues s;
          globals t = ksReadyQueues_'_update
             (\<lambda>_. Arrays.update (ksReadyQueues_' (globals s')) prio' q')
             (t_hrs_'_update f (globals s'));
          sched_queue_relation' (cslift t) q (head_C q') (end_C q');
          cslift t |` ( - tcb_ptr_to_ctcb_ptr ` S )
             = cslift s' |` ( - tcb_ptr_to_ctcb_ptr ` S );
          option_map tcb_null_sched_ptrs \<circ> cslift t
            = option_map tcb_null_sched_ptrs \<circ> cslift s';
          cslift_all_but_tcb_C t s';
          zero_ranges_are_zero (gsUntypedZeroRanges s) (f (t_hrs_' (globals s')))
              = zero_ranges_are_zero (gsUntypedZeroRanges s) (t_hrs_' (globals s'));
          hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s'));
          prio' = cready_queues_index_to_C qdom prio;
          \<forall>x \<in> S. obj_at' (inQ qdom prio) x s
                   \<or> (obj_at' (\<lambda>tcb. tcbPriority tcb = prio) x s
                       \<and> obj_at' (\<lambda>tcb. tcbDomain tcb = qdom) x s)
                   \<or> (tcb_at' x s \<and> (\<forall>d' p'. (d' \<noteq> qdom \<or> p' \<noteq> prio)
                                         \<longrightarrow> x \<notin> set (ksReadyQueues s (d', p'))));
          S \<noteq> {}; qdom \<le> ucast maxDom; prio \<le> ucast maxPrio \<rbrakk>
      \<Longrightarrow> (s \<lparr>ksReadyQueues := (ksReadyQueues s)((qdom, prio) := q)\<rparr>, t) \<in> rf_sr"
  apply (subgoal_tac "\<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s)
                           \<and> distinct(ksReadyQueues s (d, p))")
   apply (erule(5) state_relation_queue_update_helper', simp_all)
  apply (clarsimp simp: valid_queues_def valid_queues_no_bitmap_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply (clarsimp)
  apply (drule(1) bspec)
  apply (erule obj_at'_weakenE, clarsimp)
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
       \<lbrace>\<acute>ret__unsigned_long = (dom_' s) * 0x100 + (prio_' s)\<rbrace>"
  by vcg (simp add: numDomains_sge_1_simp)

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

lemma carch_state_relation_enqueue_simp:
  "carch_state_relation (ksArchState \<sigma>)
    (t_hrs_'_update f
      (globals \<sigma>' \<lparr>ksReadyQueuesL1Bitmap_' := l1upd, ksReadyQueuesL2Bitmap_' := l2upd \<rparr>)
      \<lparr>ksReadyQueues_' := rqupd \<rparr>) =
   carch_state_relation (ksArchState \<sigma>) (t_hrs_'_update f (globals \<sigma>'))"
  unfolding carch_state_relation_def
  by clarsimp

lemma t_hrs_ksReadyQueues_upd_absorb:
  "t_hrs_'_update f (g s) \<lparr>ksReadyQueues_' := rqupd \<rparr> =
   t_hrs_'_update f (g s \<lparr>ksReadyQueues_' := rqupd\<rparr>)"
  by simp

lemma rf_sr_drop_bitmaps_enqueue_helper:
  "\<lbrakk> (\<sigma>,\<sigma>') \<in> rf_sr ;
     cbitmap_L1_relation ksqL1upd' ksqL1upd ; cbitmap_L2_relation ksqL2upd' ksqL2upd \<rbrakk>
   \<Longrightarrow>
   ((\<sigma>\<lparr>ksReadyQueues := ksqupd, ksReadyQueuesL1Bitmap := ksqL1upd, ksReadyQueuesL2Bitmap := ksqL2upd\<rparr>,
     \<sigma>'\<lparr>idx___unsigned_long_' := i', queue_' := queue_upd',
        globals := t_hrs_'_update f
          (globals \<sigma>'
             \<lparr>ksReadyQueuesL1Bitmap_' := ksqL1upd',
              ksReadyQueuesL2Bitmap_' := ksqL2upd',
              ksReadyQueues_' := ksqupd'\<rparr>)\<rparr>) \<in> rf_sr) =
   ((\<sigma>\<lparr>ksReadyQueues := ksqupd\<rparr>,
     \<sigma>'\<lparr>idx_' := i', queue_' := queue_upd',
        globals := t_hrs_'_update f
          (globals \<sigma>' \<lparr>ksReadyQueues_' := ksqupd'\<rparr>)\<rparr>) \<in> rf_sr)"
  unfolding rf_sr_def cstate_relation_def Let_def
             carch_state_relation_def cmachine_state_relation_def
  by (clarsimp simp: rf_sr_cbitmap_L1_relation rf_sr_cbitmap_L2_relation)

lemma cmachine_state_relation_enqueue_simp:
  "cmachine_state_relation (ksMachineState \<sigma>)
    (t_hrs_'_update f
      (globals \<sigma>' \<lparr>ksReadyQueuesL1Bitmap_' := l1upd, ksReadyQueuesL2Bitmap_' := l2upd \<rparr>)
      \<lparr>ksReadyQueues_' := rqupd \<rparr>) =
   cmachine_state_relation (ksMachineState \<sigma>) (t_hrs_'_update f (globals \<sigma>'))"
  unfolding cmachine_state_relation_def
  by clarsimp

lemma tcb_queue_relation'_empty_ksReadyQueues:
  "\<lbrakk> sched_queue_relation' (cslift x) (q s) NULL NULL ; \<forall>t\<in> set (q s). tcb_at' t s  \<rbrakk> \<Longrightarrow> q s = []"
  apply (clarsimp simp add: tcb_queue_relation'_def)
  apply (subst (asm) eq_commute)
  apply (cases "q s" rule: rev_cases, simp)
  apply (clarsimp simp: tcb_at_not_NULL)
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

lemma tcbSchedEnqueue_ccorres:
  "ccorres dc xfdc
           (valid_queues and tcb_at' t and valid_objs')
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           hs
           (tcbSchedEnqueue t)
           (Call tcbSchedEnqueue_'proc)"
proof -
  note prio_and_dom_limit_helpers[simp] word_sle_def[simp] maxDom_to_H[simp] maxPrio_to_H[simp]
  note invert_prioToL1Index_c_simp[simp]

  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  note word_less_1[simp del]

  show ?thesis
    apply (cinit lift: tcb_')
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
               apply simp
               apply ctac
              prefer 2
              apply (wp, clarsimp, wp+)
             apply (rule_tac P="\<lambda>s. valid_queues s \<and> (\<forall>p. t \<notin> set (ksReadyQueues s p))
                                  \<and> (\<exists>tcb. ko_at' tcb t s \<and> tcbDomain tcb =rva
                                  \<and> tcbPriority tcb = rvb \<and> valid_tcb' tcb s)"
                         and P'=UNIV in ccorres_from_vcg)
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: getQueue_def gets_def get_def setQueue_def modify_def
                                   put_def bind_def return_def bitmap_fun_defs null_def)
             apply (clarsimp simp: queue_in_range valid_tcb'_def)
             apply (rule conjI; clarsimp simp: queue_in_range)
              (* queue is empty, set t to be new queue *)
              apply (drule (1) obj_at_cslift_tcb)
              apply clarsimp
              apply (frule_tac d="tcbDomain tcb" and p="tcbPriority tcb"
                       in rf_sr_sched_queue_relation)
                apply clarsimp
               apply clarsimp
              apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL)
               apply (simp add: valid_queues_valid_q)
              apply (subgoal_tac
                      "head_C (ksReadyQueues_' (globals x)
                         .[cready_queues_index_to_C (tcbDomain tcb) (tcbPriority tcb)]) = NULL")
               prefer 2
               apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL; simp add: valid_queues_valid_q)
              apply (subgoal_tac
                       "end_C (ksReadyQueues_' (globals x)
                          .[cready_queues_index_to_C (tcbDomain tcb) (tcbPriority tcb)]) = NULL")
               prefer 2
               apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL[symmetric]; simp add: valid_queues_valid_q)
              apply (rule conjI, solves \<open>clarsimp simp: le_maxDomain_eq_less_numDomains
                                                        unat_trans_ucast_helper\<close>)
              apply (frule maxDomain_le_unat_ucast_explicit)
              apply (clarsimp simp: cready_queues_index_to_C_def numPriorities_def)
              apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
              apply (simp add: t_hrs_ksReadyQueues_upd_absorb)

              apply (rule conjI)
               apply (clarsimp simp: l2BitmapSize_def' wordRadix_def c_invert_assist)

              apply (subst rf_sr_drop_bitmaps_enqueue_helper, assumption)
                apply (fastforce intro: cbitmap_L1_relation_bit_set)
               apply (fastforce intro: cbitmap_L2_relation_bit_set simp: wordRadix_def mask_def)
              apply (frule_tac d="tcbDomain tcb" and p="tcbPriority tcb" in rf_sr_sched_queue_relation)
                apply clarsimp
               apply clarsimp
              apply (drule_tac qhead'="tcb_ptr_to_ctcb_ptr t" and s=\<sigma> in tcbSchedEnqueue_update,
                     simp_all add: valid_queues_valid_q)[1]
               apply (rule tcb_at_not_NULL, erule obj_at'_weakenE, simp)
              apply (erule(1) state_relation_queue_update_helper[where S="{t}"],
                     (simp | rule globals.equality)+,
                     simp_all add: cready_queues_index_to_C_def2 numPriorities_def
                                   t_hrs_ksReadyQueues_upd_absorb upd_unless_null_def
                                   typ_heap_simps)[1]
               apply (fastforce simp: tcb_null_sched_ptrs_def typ_heap_simps c_guard_clift
                                elim: obj_at'_weaken)+
             apply (rule conjI, solves \<open>clarsimp simp: le_maxDomain_eq_less_numDomains
                                                       unat_trans_ucast_helper\<close>)
             apply clarsimp
             apply (rule conjI; clarsimp simp: queue_in_range)
              (* invalid, disagreement between C and Haskell on emptiness of queue *)
              apply (drule (1) obj_at_cslift_tcb)
              apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
              apply (frule_tac d="tcbDomain tcb" and p="tcbPriority tcb" in rf_sr_sched_queue_relation)
                apply clarsimp
               apply clarsimp
              apply (clarsimp simp: cready_queues_index_to_C_def numPriorities_def)
              apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL)
               apply (simp add: valid_queues_valid_q)
              apply clarsimp
              apply (drule tcb_queue_relation'_empty_ksReadyQueues; simp add: valid_queues_valid_q)
             (* queue was not empty, add t to queue and leave bitmaps alone *)
             apply (drule (1) obj_at_cslift_tcb)
             apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
             apply (frule_tac d="tcbDomain tcb" and p="tcbPriority tcb" in rf_sr_sched_queue_relation)
               apply clarsimp
              apply clarsimp
             apply (clarsimp simp: cready_queues_index_to_C_def numPriorities_def)
             apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL)
              apply (simp add: valid_queues_valid_q)
             apply clarsimp
             apply (frule_tac t=\<sigma> in tcb_queue_relation_qhead_mem')
              apply (simp add: valid_queues_valid_q)
             apply (frule(1) tcb_queue_relation_qhead_valid')
              apply (simp add: valid_queues_valid_q)
             apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff numPriorities_def
                                   cready_queues_index_to_C_def2)
             apply (drule_tac qhead'="tcb_ptr_to_ctcb_ptr t" and s=\<sigma> in tcbSchedEnqueue_update,
                    simp_all add: valid_queues_valid_q)[1]
               apply clarsimp

              apply (rule tcb_at_not_NULL, erule obj_at'_weakenE, simp)
             apply (frule(2) obj_at_cslift_tcb[OF valid_queues_obj_at'D])
             apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
             apply (erule_tac S="{t, v}" for v in state_relation_queue_update_helper,
                    (simp | rule globals.equality)+,
                    simp_all add: typ_heap_simps if_Some_helper numPriorities_def
                                  cready_queues_index_to_C_def2 upd_unless_null_def
                             del: fun_upd_restrict_conv
                             cong: if_cong
                             split del: if_split)[1]
                 apply simp
                 apply (rule conjI)
                  apply clarsimp
                  apply (drule_tac s="tcb_ptr_to_ctcb_ptr t" in sym, simp)
                 apply (clarsimp simp add: fun_upd_twist)
                prefer 4
                apply (simp add: obj_at'_weakenE[OF _ TrueI])
                apply (rule disjI1, erule (1) valid_queues_obj_at'D)
               apply clarsimp
              apply (fastforce simp: tcb_null_sched_ptrs_def)
             apply (simp add: typ_heap_simps c_guard_clift)
            apply (simp add: guard_is_UNIV_def)
           apply simp
           apply (wp threadGet_wp)
          apply vcg
         apply simp
         apply (wp threadGet_wp)
        apply vcg
       apply (rule ccorres_return_Skip)
      apply simp
      apply (wp threadGet_wp)
     apply vcg
    apply (fastforce simp: valid_objs'_def obj_at'_def ran_def projectKOs typ_at'_def
                           valid_obj'_def inQ_def
                    dest!: valid_queues_obj_at'D)
  done
qed

lemmas tcbSchedDequeue_update
    = tcbDequeue_update[where tn=tcbSchedNext_C and tn_update=tcbSchedNext_C_update
                          and tp'=tcbSchedPrev_C and tp_update=tcbSchedPrev_C_update,
                        simplified]

lemma tcb_queue_relation_prev_next:
  "\<lbrakk> tcb_queue_relation tn tp' mp queue qprev qhead;
     tcbp \<in> set queue; distinct (ctcb_ptr_to_tcb_ptr qprev # queue);
     \<forall>t \<in> set queue. tcb_at' t s; qprev \<noteq> tcb_Ptr 0 \<longrightarrow> mp qprev \<noteq> None;
     mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb \<rbrakk>
      \<Longrightarrow> (tn tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tn tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue
                       \<and> mp (tn tcb) \<noteq> None \<and> tn tcb \<noteq> tcb_ptr_to_ctcb_ptr tcbp)
        \<and> (tp' tcb \<noteq> tcb_Ptr 0 \<longrightarrow> (tp' tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue
                                         \<or> tp' tcb = qprev)
                       \<and> mp (tp' tcb) \<noteq> None \<and> tp' tcb \<noteq> tcb_ptr_to_ctcb_ptr tcbp)
        \<and> (tn tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tn tcb \<noteq> tp' tcb)"
  apply (induct queue arbitrary: qprev qhead)
   apply simp
  apply simp
  apply (erule disjE)
   apply clarsimp
   apply (case_tac "queue")
    apply clarsimp
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
   apply clarsimp
   apply (drule_tac f=ctcb_ptr_to_tcb_ptr in arg_cong[where y="tp' tcb"], simp)
  apply clarsimp
  apply fastforce
  done

lemma tcb_queue_relation_prev_next':
  "\<lbrakk> tcb_queue_relation' tn tp' mp queue qhead qend; tcbp \<in> set queue; distinct queue;
       \<forall>t \<in> set queue. tcb_at' t s; mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb \<rbrakk>
      \<Longrightarrow> (tn tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tn tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue
                       \<and> mp (tn tcb) \<noteq> None \<and> tn tcb \<noteq> tcb_ptr_to_ctcb_ptr tcbp)
        \<and> (tp' tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tp' tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue
                       \<and> mp (tp' tcb) \<noteq> None \<and> tp' tcb \<noteq> tcb_ptr_to_ctcb_ptr tcbp)
        \<and> (tn tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tn tcb \<noteq> tp' tcb)"
  apply (clarsimp simp: tcb_queue_relation'_def split: if_split_asm)
  apply (drule(1) tcb_queue_relation_prev_next, simp_all)
   apply (fastforce dest: tcb_at_not_NULL)
  apply clarsimp
  done

(* L1 bitmap only updated if L2 entry bits end up all zero *)
lemma rf_sr_drop_bitmaps_dequeue_helper_L2:
  "\<lbrakk> (\<sigma>,\<sigma>') \<in> rf_sr ;
     cbitmap_L2_relation ksqL2upd' ksqL2upd \<rbrakk>
   \<Longrightarrow>
((\<sigma>\<lparr>ksReadyQueues := ksqupd,
   ksReadyQueuesL2Bitmap := ksqL2upd\<rparr>,
 \<sigma>'\<lparr>idx___unsigned_long_' := i',
   queue_' := queue_upd',
   globals := globals \<sigma>'
     \<lparr>ksReadyQueuesL2Bitmap_' := ksqL2upd',
      ksReadyQueues_' := ksqupd'\<rparr>\<rparr>)
         \<in> rf_sr)
 =
((\<sigma>\<lparr>ksReadyQueues := ksqupd\<rparr>,
 \<sigma>'\<lparr>idx___unsigned_long_' := i',
   queue_' := queue_upd',
   globals := globals \<sigma>'
     \<lparr>ksReadyQueues_' := ksqupd'\<rparr>\<rparr>) \<in> rf_sr)
"
  unfolding rf_sr_def cstate_relation_def Let_def
             carch_state_relation_def cmachine_state_relation_def
  by (clarsimp simp: rf_sr_cbitmap_L1_relation rf_sr_cbitmap_L2_relation)

lemma rf_sr_drop_bitmaps_dequeue_helper:
  "\<lbrakk> (\<sigma>,\<sigma>') \<in> rf_sr ;
     cbitmap_L1_relation ksqL1upd' ksqL1upd ; cbitmap_L2_relation ksqL2upd' ksqL2upd \<rbrakk>
   \<Longrightarrow>
((\<sigma>\<lparr>ksReadyQueues := ksqupd,
   ksReadyQueuesL2Bitmap := ksqL2upd,
   ksReadyQueuesL1Bitmap := ksqL1upd\<rparr>,
 \<sigma>'\<lparr>idx___unsigned_long_' := i',
   queue_' := queue_upd',
   globals := globals \<sigma>'
     \<lparr>ksReadyQueuesL2Bitmap_' := ksqL2upd',
      ksReadyQueuesL1Bitmap_' := ksqL1upd',
      ksReadyQueues_' := ksqupd'\<rparr>\<rparr>)
         \<in> rf_sr)
 =
((\<sigma>\<lparr>ksReadyQueues := ksqupd\<rparr>,
 \<sigma>'\<lparr>idx___unsigned_long_' := i',
   queue_' := queue_upd',
   globals := globals \<sigma>'
     \<lparr>ksReadyQueues_' := ksqupd'\<rparr>\<rparr>) \<in> rf_sr)
"
  unfolding rf_sr_def cstate_relation_def Let_def
             carch_state_relation_def cmachine_state_relation_def
  by (clarsimp simp: rf_sr_cbitmap_L1_relation rf_sr_cbitmap_L2_relation)

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

lemma cready_queues_relation_empty_queue_helper:
  "\<lbrakk> tcbDomain ko \<le> maxDomain ; tcbPriority ko \<le> maxPriority ;
     cready_queues_relation (cslift \<sigma>') (ksReadyQueues_' (globals \<sigma>')) (ksReadyQueues \<sigma>)\<rbrakk>
   \<Longrightarrow>
   cready_queues_relation (cslift \<sigma>')
          (Arrays.update (ksReadyQueues_' (globals \<sigma>')) (unat (tcbDomain ko) * 256 + unat (tcbPriority ko))
            (tcb_queue_C.end_C_update (\<lambda>_. NULL)
              (head_C_update (\<lambda>_. NULL)
                (ksReadyQueues_' (globals \<sigma>').[unat (tcbDomain ko) * 256 + unat (tcbPriority ko)]))))
          ((ksReadyQueues \<sigma>)((tcbDomain ko, tcbPriority ko) := []))"
  unfolding cready_queues_relation_def Let_def
  using maxPrio_to_H[simp] maxDom_to_H[simp]
  apply clarsimp
  apply (frule (1) cready_queues_index_to_C_in_range[simplified maxDom_to_H maxPrio_to_H])
  apply (fold cready_queues_index_to_C_def[simplified numPriorities_def])
  apply (case_tac "qdom = tcbDomain ko",
          simp_all add: prio_and_dom_limit_helpers seL4_MinPrio_def
                        minDom_def)
   apply (fastforce simp: cready_queues_index_to_C_in_range simp: cready_queues_index_to_C_distinct)+
  done

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

lemma tcbSchedDequeue_ccorres':
  "ccorres dc xfdc
           ((\<lambda>s. \<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s)
                     \<and> distinct (ksReadyQueues s (d, p)))
             and valid_queues' and tcb_at' t and valid_objs')
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           []
           (tcbSchedDequeue t)
           (Call tcbSchedDequeue_'proc)"
proof -

  note prio_and_dom_limit_helpers[simp] word_sle_def[simp]

  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  include no_less_1_simps

  have ksQ_tcb_at': "\<And>s ko d p.
    \<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s)
                                          \<and> distinct (ksReadyQueues s (d, p)) \<Longrightarrow>
    \<forall>t\<in>set (ksReadyQueues s (d, p)). tcb_at' t s"
    by (fastforce dest: spec elim: obj_at'_weakenE)

  have invert_l1_index_limit: "\<And>p. invertL1Index (prioToL1Index p) < 4"
    unfolding invertL1Index_def l2BitmapSize_def' prioToL1Index_def
    by simp

  show ?thesis
  apply (cinit lift: tcb_')
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
             apply ctac
            prefer 2
            apply (wp, clarsimp, wp+)
           apply (rule_tac P="(\<lambda>s. \<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s)
                                         \<and> distinct(ksReadyQueues s (d, p)))
                                and valid_queues' and obj_at' (inQ rva rvb) t
                                and (\<lambda>s. rva \<le> maxDomain \<and> rvb \<le> maxPriority)"
                       and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: getQueue_def gets_def get_def setQueue_def modify_def
                                 put_def bind_def return_def bitmap_fun_defs when_def
                                 null_def)

           apply (rule conjI; clarsimp simp: queue_in_range[simplified maxDom_to_H maxPrio_to_H])
            apply (rule conjI; clarsimp simp: queue_in_range[simplified maxDom_to_H maxPrio_to_H])
             apply (frule(1) valid_queuesD')
             apply (drule (1) obj_at_cslift_tcb, clarsimp simp: inQ_def)
             apply (frule_tac d="tcbDomain ko" and p="tcbPriority ko" in rf_sr_sched_queue_relation)
               apply (fastforce simp: maxDom_to_H maxPrio_to_H)+
             apply (frule_tac s=\<sigma> in tcb_queue_relation_prev_next'; (fastforce simp: ksQ_tcb_at')?)
             apply (drule_tac s=\<sigma> in tcbSchedDequeue_update, assumption,
                    simp_all add: remove1_filter ksQ_tcb_at')[1]
             apply (rule conjI, solves \<open>clarsimp simp: le_maxDomain_eq_less_numDomains
                                                       unat_trans_ucast_helper\<close>)
             apply (clarsimp simp: maxDomain_le_unat_ucast_explicit)
             apply (intro conjI;
                    clarsimp simp: h_val_field_clift'
                                   h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift)+
               apply (drule(2) filter_empty_unfiltered_contr, simp)+
             apply (rule conjI; clarsimp)
              apply (rule conjI)
               apply (fastforce simp: c_invert_assist l2BitmapSize_def' wordRadix_def)
              apply (rule conjI; clarsimp)
               apply (subst rf_sr_drop_bitmaps_dequeue_helper, assumption)
                 apply (fastforce intro: cbitmap_L1_relation_bit_clear)
                apply (simp add: invert_prioToL1Index_c_simp)
                apply (frule rf_sr_cbitmap_L2_relation)
                apply (clarsimp simp: cbitmap_L2_relation_def
                                      word_size prioToL1Index_def wordRadix_def mask_def
                                      word_le_nat_alt
                                      numPriorities_def wordBits_def l2BitmapSize_def'
                                      invertL1Index_def numDomains_less_numeric_explicit)
                apply (case_tac "d = tcbDomain ko"
                       ; fastforce simp: le_maxDomain_eq_less_numDomains
                                         numDomains_less_numeric_explicit)
               apply (drule (1) obj_at_cslift_tcb, clarsimp simp: inQ_def)
               apply (frule_tac d="tcbDomain ko" and p="tcbPriority ko"
                        in rf_sr_sched_queue_relation)
                 apply (fold_subgoals (prefix))[2]
                subgoal premises prems using prems by (fastforce simp: maxDom_to_H maxPrio_to_H)+

               apply (frule_tac s=\<sigma> in tcb_queue_relation_prev_next', assumption)
                  prefer 3
                  apply fastforce
                 apply (fold_subgoals (prefix))[2]
                subgoal premises prems using prems by ((fastforce simp: ksQ_tcb_at')+)
               apply (drule_tac s=\<sigma> in tcbSchedDequeue_update, assumption,
                      simp_all add: remove1_filter ksQ_tcb_at')[1]
               (* trivial case, setting queue to empty *)
               apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                                     cmachine_state_relation_def)
               apply (erule (2) cready_queues_relation_empty_queue_helper)
              (* impossible case, C L2 update disagrees with Haskell update *)
              apply (simp add: invert_prioToL1Index_c_simp)
              apply (subst (asm) num_domains_index_updates)
               subgoal by (simp add: le_maxDomain_eq_less_numDomains word_le_nat_alt)
              apply (subst (asm) Arrays.index_update)
               apply (simp add: invert_l1_index_limit)

              apply (frule rf_sr_cbitmap_L2_relation)
              apply (drule_tac i="invertL1Index (prioToL1Index (tcbPriority ko))"
                       in cbitmap_L2_relationD, assumption)
               apply (fastforce simp: l2BitmapSize_def' invert_l1_index_limit)
              apply (fastforce simp: prioToL1Index_def invertL1Index_def mask_def wordRadix_def)
             (* impossible case *)
             apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
             apply (drule(2) filter_empty_unfiltered_contr, fastforce)

            apply (frule (1) valid_queuesD')
            apply (drule (1) obj_at_cslift_tcb, clarsimp simp: inQ_def)
            apply (frule_tac d="tcbDomain ko" and p="tcbPriority ko"
                     in rf_sr_sched_queue_relation)
              apply fold_subgoals[2]
              apply (fastforce simp: maxDom_to_H maxPrio_to_H)+
            apply (clarsimp simp: h_val_field_clift'
                                  h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift)
            apply (frule_tac s=\<sigma> in tcb_queue_relation_prev_next', assumption)
               prefer 3
               apply fastforce
              apply (fold_subgoals (prefix))[2]
             subgoal premises prems using prems by (fastforce simp: ksQ_tcb_at')+
            apply (drule_tac s=\<sigma> in tcbSchedDequeue_update, assumption,
                   simp_all add: remove1_filter ksQ_tcb_at')[1]
            apply (clarsimp simp:  filter_noteq_op upd_unless_null_def)
            apply (rule conjI, solves \<open>clarsimp simp: le_maxDomain_eq_less_numDomains
                                                      unat_trans_ucast_helper\<close>)
            apply (clarsimp simp: maxDomain_le_unat_ucast_explicit)
            apply (rule conjI, clarsimp)
             apply (clarsimp simp: h_val_field_clift'
                                   h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift)
             apply (rule conjI; clarsimp)
              apply (simp add: typ_heap_simps)
              apply (clarsimp simp: h_t_valid_c_guard [OF h_t_valid_field, OF h_t_valid_clift]
                                    h_t_valid_field[OF h_t_valid_clift] h_t_valid_clift)
              apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                       in state_relation_queue_update_helper',
                     (simp | rule globals.equality)+,
                     simp_all add: clift_field_update if_Some_helper numPriorities_def
                                   cready_queues_index_to_C_def2 typ_heap_simps
                                   maxDom_to_H maxPrio_to_H
                             cong: if_cong split del: if_split)[1]

               apply (fastforce simp: tcb_null_sched_ptrs_def typ_heap_simps c_guard_clift
                                elim: obj_at'_weaken)+
             apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                      in state_relation_queue_update_helper',
                    (simp | rule globals.equality)+,
                    simp_all add: clift_field_update if_Some_helper numPriorities_def
                                  cready_queues_index_to_C_def2
                                  maxDom_to_H maxPrio_to_H
                            cong: if_cong split del: if_split,
                    simp_all add: typ_heap_simps')[1]
              subgoal by (fastforce simp: tcb_null_sched_ptrs_def)
             subgoal by fastforce
            apply clarsimp
            apply (rule conjI; clarsimp)
             apply (rule conjI)
              apply (fastforce simp: c_invert_assist l2BitmapSize_def' wordRadix_def)
             apply (rule conjI; clarsimp)
              (* invalid, missing bitmap updates on haskell side *)
              apply (fold_subgoals (prefix))[2]
             subgoal premises prems using prems
               by (fastforce dest!: tcb_queue_relation'_empty_ksReadyQueues
                              elim: obj_at'_weaken)+
            apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
            apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                     in state_relation_queue_update_helper',
                   (simp | rule globals.equality)+,
                   simp_all add: clift_field_update if_Some_helper numPriorities_def
                                 cready_queues_index_to_C_def2
                                 maxDom_to_H maxPrio_to_H
                           cong: if_cong split del: if_split)[1]
               apply (fold_subgoals (prefix))[4]
            subgoal premises prems using prems
              by - (fastforce simp: typ_heap_simps c_guard_clift tcb_null_sched_ptrs_def
                                    clift_heap_update_same[OF h_t_valid_clift])+
           apply (rule conjI; clarsimp simp: queue_in_range[simplified maxDom_to_H maxPrio_to_H])
            apply (frule (1) valid_queuesD')
            apply (drule (1) obj_at_cslift_tcb, clarsimp simp: inQ_def)
            apply (frule_tac d="tcbDomain ko" and p="tcbPriority ko"
                     in rf_sr_sched_queue_relation)
              apply (fold_subgoals (prefix))[2]
             subgoal premises prems using prems by (fastforce simp: maxDom_to_H maxPrio_to_H)+
            apply (clarsimp simp: h_val_field_clift'
                                  h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift)
            apply (frule_tac s=\<sigma> in tcb_queue_relation_prev_next')
                apply fastforce
               prefer 3
               apply fastforce
              apply (fold_subgoals (prefix))[2]
             subgoal premises prems using prems by (fastforce simp: ksQ_tcb_at')+
            apply (drule_tac s=\<sigma> in tcbSchedDequeue_update, assumption,
                   simp_all add: remove1_filter ksQ_tcb_at')[1]
            apply (clarsimp simp:  filter_noteq_op upd_unless_null_def)
            apply (rule conjI, solves \<open>clarsimp simp: le_maxDomain_eq_less_numDomains
                                                      unat_trans_ucast_helper\<close>)
            apply (clarsimp simp: maxDomain_le_unat_ucast_explicit)
            apply (rule conjI; clarsimp)
             apply (clarsimp simp: h_val_field_clift'
                                   h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift)
             apply (clarsimp simp: typ_heap_simps)
             apply (rule conjI; clarsimp simp: typ_heap_simps)
             apply (drule(2) filter_empty_unfiltered_contr[simplified filter_noteq_op], simp)
            apply (rule conjI)
             apply (fastforce simp: c_invert_assist l2BitmapSize_def' wordRadix_def)
            apply (rule conjI; clarsimp)
             (* impossible case, C L2 update disagrees with Haskell update *)
             apply (subst (asm) num_domains_index_updates)
              apply (simp add: le_maxDomain_eq_less_numDomains word_le_nat_alt)
             apply (subst (asm) Arrays.index_update)
              subgoal using invert_l1_index_limit
                by (fastforce simp add: invert_prioToL1Index_c_simp intro: nat_Suc_less_le_imp)
             apply (frule rf_sr_cbitmap_L2_relation)
             apply (simp add: invert_prioToL1Index_c_simp)
             apply (drule_tac i="invertL1Index (prioToL1Index (tcbPriority ko))"
                      in cbitmap_L2_relationD, assumption)
              subgoal by (simp add: invert_l1_index_limit l2BitmapSize_def')
             apply (fastforce simp: prioToL1Index_def invertL1Index_def mask_def wordRadix_def)

            apply (simp add: invert_prioToL1Index_c_simp)
            apply (subst rf_sr_drop_bitmaps_dequeue_helper_L2, assumption)
             subgoal by (fastforce dest: rf_sr_cbitmap_L2_relation elim!: cbitmap_L2_relation_bit_clear)

            (* trivial case, setting queue to empty *)
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                                  cmachine_state_relation_def)
            apply (erule (2) cready_queues_relation_empty_queue_helper)

           apply (frule (1) valid_queuesD')
           apply (drule (1) obj_at_cslift_tcb, clarsimp simp: inQ_def)
           apply (frule_tac d="tcbDomain ko" and p="tcbPriority ko"
                    in rf_sr_sched_queue_relation)
             apply (fold_subgoals (prefix))[2]
            subgoal premises prems using prems by (fastforce simp: maxDom_to_H maxPrio_to_H)+
           apply (clarsimp simp: h_val_field_clift'
                                 h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift)
           apply (simp add: invert_prioToL1Index_c_simp)
           apply (frule_tac s=\<sigma> in tcb_queue_relation_prev_next')
               apply (fastforce simp add: ksQ_tcb_at')+
           apply (drule_tac s=\<sigma> in tcbSchedDequeue_update, assumption,
                  simp_all add: remove1_filter ksQ_tcb_at')[1]
           apply (clarsimp simp: filter_noteq_op upd_unless_null_def)
           apply (rule conjI, solves \<open>clarsimp simp: le_maxDomain_eq_less_numDomains
                                                     unat_trans_ucast_helper\<close>)
           apply (clarsimp simp: maxDomain_le_unat_ucast_explicit)
           apply (rule conjI, clarsimp)
            apply (clarsimp simp: h_val_field_clift'
                                  h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift)
            apply (clarsimp simp: typ_heap_simps)
            apply (rule conjI; clarsimp simp: typ_heap_simps)
             apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                      in state_relation_queue_update_helper',
                    (simp | rule globals.equality)+,
                    simp_all add: clift_field_update if_Some_helper numPriorities_def
                                  cready_queues_index_to_C_def2
                                  maxDom_to_H maxPrio_to_H
                            cong: if_cong split del: if_split)[1]
                apply (fastforce simp: tcb_null_sched_ptrs_def)
               apply (fastforce simp: typ_heap_simps c_guard_clift)
              apply (fastforce simp: typ_heap_simps)
             apply (fastforce simp: tcb_null_sched_ptrs_def)
            apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                     in state_relation_queue_update_helper',
                   (simp | rule globals.equality)+,
                   simp_all add: clift_field_update if_Some_helper numPriorities_def
                                 cready_queues_index_to_C_def2
                                 maxDom_to_H maxPrio_to_H
                           cong: if_cong split del: if_split)[1]
               apply (fold_subgoals (prefix))[4]
            subgoal premises prems using prems
              by - (fastforce simp: typ_heap_simps c_guard_clift tcb_null_sched_ptrs_def
                                    clift_heap_update_same[OF h_t_valid_clift])+
           apply (clarsimp)
           apply (rule conjI; clarsimp simp: typ_heap_simps)
            apply (rule conjI)
             apply (fastforce simp: c_invert_assist l2BitmapSize_def' wordRadix_def)
            apply (rule conjI; clarsimp)
             (* invalid, missing bitmap updates on haskell side *)
             apply (drule tcb_queue_relation'_empty_ksReadyQueues)
              apply (fold_subgoals (prefix))[2]
             subgoal premises prems using prems by (fastforce elim: obj_at'_weaken)+
            (* invalid, missing bitmap updates on haskell side *)
            apply (drule tcb_queue_relation'_empty_ksReadyQueues)
             apply (fold_subgoals (prefix))[2]
            subgoal premises prems using prems by (fastforce elim: obj_at'_weaken)+
           apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                    in state_relation_queue_update_helper',
                  (simp | rule globals.equality)+,
                  simp_all add: clift_field_update if_Some_helper numPriorities_def
                                cready_queues_index_to_C_def2 typ_heap_simps
                                maxDom_to_H maxPrio_to_H
                          cong: if_cong split del: if_split)[1]
            apply (fold_subgoals (prefix))[3]
           subgoal premises prems using prems
            by (fastforce simp: typ_heap_simps c_guard_clift tcb_null_sched_ptrs_def)+
          apply (simp add: guard_is_UNIV_def)
         apply simp
         apply (wp threadGet_wp)
        apply vcg
       apply simp
       apply (wp threadGet_wp)
      apply vcg
     apply (rule ccorres_return_Skip)
    apply simp
    apply (wp threadGet_wp)
   apply vcg
  by (fastforce simp: valid_objs'_def obj_at'_def ran_def projectKOs typ_at'_def
                      valid_obj'_def valid_tcb'_def inQ_def)
qed

lemma tcbSchedDequeue_ccorres:
  "ccorres dc xfdc
           (valid_queues and valid_queues' and tcb_at' t and valid_objs')
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           []
           (tcbSchedDequeue t)
           (Call tcbSchedDequeue_'proc)"
  apply (rule ccorres_guard_imp [OF tcbSchedDequeue_ccorres'])
   apply (clarsimp simp: valid_queues_def valid_queues_no_bitmap_def)
   apply (drule_tac x=d in spec)
   apply (drule_tac x=p in spec)
   apply (clarsimp)
   apply (drule(1) bspec)
   apply (erule obj_at'_weakenE)
   apply (clarsimp)+
  done

lemma tcb_queue_relation_append:
  "\<lbrakk> tcb_queue_relation tn tp' mp queue qprev qhead; queue \<noteq> [];
     qend' \<notin> tcb_ptr_to_ctcb_ptr ` set queue; mp qend' = Some tcb;
     queue = queue' @ [ctcb_ptr_to_tcb_ptr qend]; distinct queue;
     \<forall>x \<in> set queue. tcb_ptr_to_ctcb_ptr x \<noteq> NULL; qend' \<noteq> NULL;
     \<And>v f g. tn (tn_update f v) = f (tn v) \<and> tp' (tp_update g v) = g (tp' v)
                \<and> tn (tp_update f v) = tn v \<and> tp' (tn_update g v) = tp' v \<rbrakk>
    \<Longrightarrow> tcb_queue_relation tn tp'
          (mp (qend \<mapsto> tn_update (\<lambda>_. qend') (the (mp qend)),
               qend' \<mapsto> tn_update (\<lambda>_. NULL) (tp_update (\<lambda>_. qend) tcb)))
          (queue @ [ctcb_ptr_to_tcb_ptr qend']) qprev qhead"
  using [[hypsubst_thin = true]]
  apply clarsimp
  apply (induct queue' arbitrary: qprev qhead)
   apply clarsimp
  apply clarsimp
  done

lemma tcbSchedAppend_update:
  assumes sr: "sched_queue_relation' mp queue qhead qend"
  and     qh': "qend' \<notin> tcb_ptr_to_ctcb_ptr ` set queue"
  and  cs_tcb: "mp qend' = Some tcb"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and     qhN: "qend' \<noteq> NULL"
  shows
  "sched_queue_relation'
            (upd_unless_null qend (tcbSchedNext_C_update (\<lambda>_. qend') (the (mp qend)))
                (mp(qend' \<mapsto> tcb\<lparr>tcbSchedNext_C := NULL, tcbSchedPrev_C := qend\<rparr>)))
            (queue @ [ctcb_ptr_to_tcb_ptr qend']) (if queue = [] then qend' else qhead) qend'"
  using sr qh' valid_ep cs_tcb qhN
  apply -
  apply (rule rev_cases[where xs=queue])
   apply (simp add: tcb_queue_relation'_def upd_unless_null_def)
  apply (clarsimp simp: tcb_queue_relation'_def upd_unless_null_def tcb_at_not_NULL)
  apply (drule_tac qend'=qend' and tn_update=tcbSchedNext_C_update
             and tp_update=tcbSchedPrev_C_update and qend="tcb_ptr_to_ctcb_ptr y"
             in tcb_queue_relation_append, simp_all)
   apply (fastforce simp add: tcb_at_not_NULL)
  apply (simp add: fun_upd_twist)
  done

lemma tcb_queue_relation_qend_mems:
  "\<lbrakk> tcb_queue_relation' getNext getPrev mp queue qhead qend;
     \<forall>x \<in> set queue. tcb_at' x s \<rbrakk>
      \<Longrightarrow> (qend = NULL \<longrightarrow> queue = [])
       \<and> (qend \<noteq> NULL \<longrightarrow> ctcb_ptr_to_tcb_ptr qend \<in> set queue)"
  apply (clarsimp simp: tcb_queue_relation'_def)
  apply (drule bspec, erule last_in_set)
  apply (simp add: tcb_at_not_NULL)
  done

lemma tcbSchedAppend_ccorres:
  "ccorres dc xfdc
           (valid_queues and tcb_at' t and valid_objs')
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           []
           (tcbSchedAppend t)
           (Call tcbSchedAppend_'proc)"
proof -
  note prio_and_dom_limit_helpers[simp] word_sle_def[simp] maxDom_to_H[simp] maxPrio_to_H[simp]

  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  include no_less_1_simps

  show ?thesis
  apply (cinit lift: tcb_')
   apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'"
               and xf'="ret__unsigned_longlong_'" in ccorres_split_nothrow)
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
      apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv"
          and xf'="dom_'" in ccorres_split_nothrow)
          apply (rule threadGet_vcg_corres)
          apply (rule allI, rule conseqPre, vcg)
          apply clarsimp
          apply (drule obj_at_ko_at', clarsimp)
          apply (drule spec, drule(1) mp, clarsimp)
          apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
         apply ceqv
        apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv"
            and xf'="prio_'" in ccorres_split_nothrow)
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
             apply ctac
            prefer 2
            apply (wp, clarsimp, wp+)
           apply (rule_tac P="\<lambda>s. valid_queues s \<and> (\<forall>p. t \<notin> set (ksReadyQueues s p))
                                  \<and> (\<exists>tcb. ko_at' tcb t s \<and> tcbDomain tcb =rva
                                  \<and> tcbPriority tcb = rvb \<and> valid_tcb' tcb s)"
                       and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: getQueue_def gets_def get_def setQueue_def modify_def
                                 put_def bind_def return_def bitmap_fun_defs null_def)
           apply (clarsimp simp: queue_in_range valid_tcb'_def)
           apply (rule conjI; clarsimp simp: queue_in_range)
            apply (drule (1) obj_at_cslift_tcb)
            apply clarsimp
            apply (frule_tac d="tcbDomain tcb" and p="tcbPriority tcb"
                     in rf_sr_sched_queue_relation)
              apply clarsimp
             apply clarsimp
            apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL)
             apply (simp add: valid_queues_valid_q)
            apply (frule_tac s=\<sigma> in tcb_queue_relation_qend_mems,  simp add: valid_queues_valid_q)
            apply (drule_tac qend'="tcb_ptr_to_ctcb_ptr t" and s=\<sigma> in tcbSchedAppend_update,
                   simp_all add: valid_queues_valid_q)[1]
             apply (rule tcb_at_not_NULL, erule obj_at'_weakenE, simp)
            apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
            apply (simp add: invert_prioToL1Index_c_simp)
            apply (rule conjI, solves \<open>clarsimp simp: le_maxDomain_eq_less_numDomains
                                                      unat_trans_ucast_helper\<close>)
            apply (clarsimp simp: maxDomain_le_unat_ucast_explicit)
            apply (rule conjI; clarsimp)
             apply (rule conjI)
              apply (fastforce simp: c_invert_assist l2BitmapSize_def' wordRadix_def)
             apply (simp add: t_hrs_ksReadyQueues_upd_absorb)
             apply (subst rf_sr_drop_bitmaps_enqueue_helper, assumption)
               apply (fastforce intro: cbitmap_L1_relation_bit_set)
              subgoal by (fastforce intro: cbitmap_L2_relation_bit_set simp: wordRadix_def mask_def)
             apply (erule(1) state_relation_queue_update_helper[where S="{t}"],
                    (simp | rule globals.equality)+,
                    simp_all add: cready_queues_index_to_C_def2 numPriorities_def
                                  t_hrs_ksReadyQueues_upd_absorb upd_unless_null_def
                                  typ_heap_simps)[1]
               apply (fastforce simp: tcb_null_sched_ptrs_def elim: obj_at'_weaken)
              apply (fastforce simp: typ_heap_simps c_guard_clift)
             apply (fastforce simp: tcb_null_sched_ptrs_def elim: obj_at'_weaken)
            apply (clarsimp simp: upd_unless_null_def cready_queues_index_to_C_def numPriorities_def)
           apply (rule conjI, solves \<open>clarsimp simp: le_maxDomain_eq_less_numDomains
                                                     unat_trans_ucast_helper\<close>)
           apply (clarsimp simp: maxDomain_le_unat_ucast_explicit)
           apply (rule conjI; clarsimp simp: queue_in_range)
            apply (drule (1) obj_at_cslift_tcb)
            apply clarsimp
            apply (frule_tac d="tcbDomain tcb" and p="tcbPriority tcb"
                     in rf_sr_sched_queue_relation)
              apply clarsimp
             apply clarsimp
            apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL)
             apply (simp add: valid_queues_valid_q)
            apply (frule_tac s=\<sigma> in tcb_queue_relation_qend_mems,
                   simp add: valid_queues_valid_q)
            apply (drule_tac qend'="tcb_ptr_to_ctcb_ptr t" and s=\<sigma> in tcbSchedAppend_update,
                   simp_all add: valid_queues_valid_q)[1]
              apply clarsimp
             apply (rule tcb_at_not_NULL, erule obj_at'_weakenE, simp)
            apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
            apply (clarsimp simp: upd_unless_null_def cready_queues_index_to_C_def numPriorities_def)
           apply (drule (1) obj_at_cslift_tcb)
           apply clarsimp
           apply (frule_tac d="tcbDomain tcb" and p="tcbPriority tcb"
                    in rf_sr_sched_queue_relation)
             apply clarsimp
            apply clarsimp
           apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL)
            apply (simp add: valid_queues_valid_q)
           apply (frule_tac s=\<sigma> in tcb_queue_relation_qend_mems,
                  simp add: valid_queues_valid_q)
           apply (drule_tac qend'="tcb_ptr_to_ctcb_ptr t" and s=\<sigma> in tcbSchedAppend_update,
                  simp_all add: valid_queues_valid_q)[1]
             apply clarsimp
            apply (rule tcb_at_not_NULL, erule obj_at'_weakenE, simp)
           apply (clarsimp simp: cready_queues_index_to_C_def2 numPriorities_def)
           apply (frule(2) obj_at_cslift_tcb[OF valid_queues_obj_at'D])
           apply (clarsimp simp: h_val_field_clift' h_t_valid_clift)
           apply (erule_tac S="{t, v}" for v in state_relation_queue_update_helper,
                  (simp | rule globals.equality)+,
                  simp_all add: typ_heap_simps if_Some_helper numPriorities_def
                                cready_queues_index_to_C_def2 upd_unless_null_def
                           cong: if_cong split del: if_split
                           del: fun_upd_restrict_conv)[1]
               apply simp
               apply (rule conjI)
                apply clarsimp
                apply (drule_tac s="tcb_ptr_to_ctcb_ptr t" in sym, simp)
               apply (clarsimp simp add: fun_upd_twist)
              prefer 4
              apply (simp add: obj_at'_weakenE[OF _ TrueI])
              apply (rule disjI1, erule valid_queues_obj_at'D)
              subgoal by simp
             subgoal by simp
            subgoal by (fastforce simp: tcb_null_sched_ptrs_def)
           subgoal by (fastforce simp: typ_heap_simps c_guard_clift)
          apply (simp add: guard_is_UNIV_def)
         apply simp
         apply (wp threadGet_wp)
        apply vcg
       apply simp
       apply (wp threadGet_wp)
      apply vcg
     apply (rule ccorres_return_Skip)
    apply simp
    apply (wp threadGet_wp)
   apply vcg
  by (fastforce simp: valid_objs'_def obj_at'_def ran_def projectKOs typ_at'_def
                         valid_obj'_def inQ_def
                   dest!: valid_queues_obj_at'D)
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
  "ccorres dc xfdc (valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs')
           UNIV [] rescheduleRequired (Call rescheduleRequired_'proc)"
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
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ; valid_queues s \<rbrakk>
   \<Longrightarrow> lookupBitmapPriority d s \<le> maxPriority"
   unfolding valid_queues_def valid_queues_no_bitmap_def
   by (fastforce dest!: bitmapQ_from_bitmap_lookup bitmapQ_ksReadyQueuesI intro: ccontr)

lemma rf_sr_ksReadyQueuesL1Bitmap_not_zero:
  "\<lbrakk> (\<sigma>, s') \<in> rf_sr ; d \<le> maxDomain ; ksReadyQueuesL1Bitmap_' (globals s').[unat d] \<noteq> 0 \<rbrakk>
  \<Longrightarrow> ksReadyQueuesL1Bitmap \<sigma> d \<noteq> 0"
  apply (drule rf_sr_cbitmap_L1_relation)
  apply (simp add: cbitmap_L1_relation_def)
  done

lemma ksReadyQueuesL1Bitmap_word_log2_max:
    "\<lbrakk>valid_queues s; ksReadyQueuesL1Bitmap s d \<noteq> 0\<rbrakk>
    \<Longrightarrow> word_log2 (ksReadyQueuesL1Bitmap s d) < l2BitmapSize"
    unfolding valid_queues_def
    by (fastforce dest: word_log2_nth_same bitmapQ_no_L1_orphansD)

lemma word_log2_max_word64[simp]:
  "word_log2 (w :: 64 word) < 64"
  using word_log2_max[where w=w]
  by (simp add: word_size)

lemma rf_sr_ksReadyQueuesL2Bitmap_simp:
  "\<lbrakk> (\<sigma>, s') \<in> rf_sr ; d \<le> maxDomain ; valid_queues \<sigma> ; ksReadyQueuesL1Bitmap \<sigma> d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> ksReadyQueuesL2Bitmap_' (globals s').[unat d].[word_log2 (ksReadyQueuesL1Bitmap \<sigma> d)] =
      ksReadyQueuesL2Bitmap \<sigma> (d, word_log2 (ksReadyQueuesL1Bitmap \<sigma> d))"
  apply (frule rf_sr_cbitmap_L2_relation)
  apply (frule (1) ksReadyQueuesL1Bitmap_word_log2_max)
  apply (drule (3) cbitmap_L2_relationD)
  done

lemma ksReadyQueuesL2Bitmap_nonzeroI:
  "\<lbrakk> d \<le> maxDomain ; valid_queues s ; ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d))) \<noteq> 0"
   unfolding valid_queues_def
   apply clarsimp
   apply (frule bitmapQ_no_L1_orphansD)
    apply (erule word_log2_nth_same)
   apply clarsimp
   done

lemma l1index_to_prio_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call l1index_to_prio_'proc
       \<lbrace>\<acute>ret__unsigned_long = l1index_' s << wordRadix \<rbrace>"
  by vcg (simp add: word_sle_def wordRadix_def')

lemma getHighestPrio_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = ucast rv) ret__unsigned_long_'
    ((\<lambda>s. ksReadyQueuesL1Bitmap s d \<noteq> 0 \<and> bitmapQ_no_L1_orphans s) and K (d \<le> maxDomain))
    (UNIV \<inter> {s. dom_' s = ucast d}) hs
    (getHighestPrio d) (Call getHighestPrio_'proc)"
proof -

  note prio_and_dom_limit_helpers[simp]
  note Collect_const_mem[simp]

  have unsigned_word_log2:
  "\<And>w. w \<noteq> 0 \<Longrightarrow> (0x3F::64 signed word) - of_nat (word_clz (w::machine_word)) = (of_nat (word_log2 w))"
  unfolding word_log2_def
  by (clarsimp dest!: word_clz_nonzero_max simp: word_size)

  have word_log2_def64:
    "\<And>w. word_log2 (w::machine_word) = 63 - word_clz w"
    unfolding word_log2_def by (simp add: word_size)

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

  (* annoyingly, inside one of the csymbr commands, we get unwanted minus distribution *)
  have word_clz_word_log2_fixup:
    "\<And>w::machine_word.
       w \<noteq> 0 \<Longrightarrow> (0xFFFFFFFFFFFFFFC0::machine_word) + (of_nat l2BitmapSize + of_nat (word_clz w))
                = of_nat l2BitmapSize - 1 - of_nat (word_log2 w)"
  by (frule word_clz_nonzero_max)
     (simp add: word_log2_def64 word_size)

  (* when numDomains = 1, array bounds checks would become _ = 0 rather than _ < 1, changing the
     shape of the proof compared to when numDomains > 1 *)
  include no_less_1_simps

  show ?thesis
    apply (rule ccorres_grab_asm)
    apply (cinit lift: dom_')
     apply (clarsimp split del: if_split)
     apply (rule ccorres_pre_getReadyQueuesL1Bitmap)
     apply (rule ccorres_pre_getReadyQueuesL2Bitmap)
     apply (rename_tac l2)
     apply ccorres_rewrite (* UNIV guard *)
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
       apply (simp add: unsigned_word_log2 word_log2_def64[symmetric] ucast_or_distrib)
       apply (rule_tac f="(||)" in arg_cong2)
        apply (subst of_nat_shiftl)+
        apply (subst ucast_of_nat_small, simp add: wordRadix_def l2BitmapSize_def')
        apply (rule refl)
       apply (subst ucast_of_nat_small, simp add: wordRadix_def)
        apply (rule word_log2_max_word64[THEN order_less_le_trans], simp)
       apply (rule refl)
       done
    apply clarsimp
    apply (frule rf_sr_cbitmap_L1_relation)
    apply (prop_tac "ksReadyQueuesL1Bitmap_' (globals s').[unat d] \<noteq> 0")
     subgoal by (fastforce simp: cbitmap_L1_relation_def)
    apply (simp add: word_clz_word_log2_fixup)
    apply (clarsimp simp: unsigned_word_log2 cbitmap_L1_relation_def maxDomain_le_unat_ucast_explicit
                          order_trans[OF word_clz_sint_upper] order_trans[OF word_clz_sint_lower])
    apply (frule bitmapQ_no_L1_orphansD, erule word_log2_nth_same)
    apply (rule conjI, fastforce simp: invertL1Index_def l2BitmapSize_def')
    apply (rule conjI, fastforce)
    apply (rule conjI, fastforce)
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
         (valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
            and st_tcb_at' runnable' t and (\<lambda>s. ksCurDomain s \<le> maxDomain)
            and valid_objs')
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
           (tcb_at' thread and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_queues
                           and valid_objs')
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
           apply (clarsimp simp: return_def split del: if_split)
           apply (clarsimp simp: from_bool_0 rf_sr_ksCurThread)
           apply (rule conjI)
            apply (clarsimp simp: st_tcb_at'_def)
            apply (drule (1) obj_at_cslift_tcb)
            apply (clarsimp simp: typ_heap_simps)
            apply (subgoal_tac "ksSchedulerAction \<sigma> = ResumeCurrentThread")
             apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def)
             apply (case_tac "tcbState ko", simp_all add: "StrictC'_thread_state_defs")[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def                                  tcb_at_not_NULL
                           split: scheduler_action.split_asm)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 cscheduler_action_relation_def)
          apply wp+
     apply (simp add: isRunnable_def isStopped_def)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply clarsimp
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def weak_sch_act_wf_def)
  done

lemma scheduleTCB_ccorres_valid_queues'_pre:
        "ccorresG rf_sr \<Gamma> dc xfdc (tcb_at' thread and st_tcb_at' (not runnable') thread and valid_queues' and valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs')
         (UNIV \<inter> \<lbrace>\<acute>tptr = tcb_ptr_to_ctcb_ptr thread\<rbrace>) []
         (do (runnable, curThread, action) \<leftarrow> do
             runnable \<leftarrow> isRunnable thread;
             curThread \<leftarrow> getCurThread;
             action \<leftarrow> getSchedulerAction;
             return (runnable, curThread, action) od;
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
           apply (clarsimp simp: return_def)
           apply (clarsimp simp: from_bool_0 rf_sr_ksCurThread)
           apply (rule conjI)
            apply (clarsimp simp: st_tcb_at'_def)
            apply (drule (1) obj_at_cslift_tcb)
            apply (clarsimp simp: typ_heap_simps)
            apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def weak_sch_act_wf_def)
             apply (case_tac "tcbState ko", simp_all add: "StrictC'_thread_state_defs")[1]
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
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
  done


lemmas scheduleTCB_ccorres_valid_queues'
    = scheduleTCB_ccorres_valid_queues'_pre[unfolded bind_assoc return_bind split_conv]

lemma rescheduleRequired_ccorres_valid_queues'_simple:
  "ccorresG rf_sr \<Gamma> dc xfdc (valid_queues' and sch_act_simple) UNIV [] rescheduleRequired (Call rescheduleRequired_'proc)"
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
        "ccorresG rf_sr \<Gamma> dc xfdc (tcb_at' thread and st_tcb_at' (not runnable') thread and valid_queues' and sch_act_simple)
         (UNIV \<inter> \<lbrace>\<acute>tptr = tcb_ptr_to_ctcb_ptr thread\<rbrace>) []
         (do (runnable, curThread, action) \<leftarrow> do
             runnable \<leftarrow> isRunnable thread;
             curThread \<leftarrow> getCurThread;
             action \<leftarrow> getSchedulerAction;
             return (runnable, curThread, action) od;
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
             apply (case_tac "tcbState ko", simp_all add: "StrictC'_thread_state_defs")[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def
                                  tcb_at_not_NULL
                           split: scheduler_action.split_asm)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 cscheduler_action_relation_def)
          apply wp+
     apply (simp add: isRunnable_def isStopped_def)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply clarsimp
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def valid_queues'_def)
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

lemma threadSet_valid_queues_and_runnable': "\<lbrace>\<lambda>s. valid_queues s \<and> (\<forall>p. thread \<in> set (ksReadyQueues s p) \<longrightarrow> runnable' st)\<rbrace>
                 threadSet (tcbState_update (\<lambda>_. st)) thread
               \<lbrace>\<lambda>rv s. valid_queues s\<rbrace>"
  apply (wp threadSet_valid_queues)
  apply (clarsimp simp: inQ_def)
done

lemma setThreadState_ccorres[corres]:
   "ccorres dc xfdc
   (\<lambda>s. tcb_at' thread s \<and> valid_queues s \<and> valid_objs' s \<and> valid_tcb_state' st s \<and>
                 (ksSchedulerAction s = SwitchToThread thread \<longrightarrow> runnable' st) \<and>
                 (\<forall>p. thread \<in> set (ksReadyQueues s p) \<longrightarrow> runnable' st) \<and>
                 sch_act_wf (ksSchedulerAction s) s)
     ({s'. (\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := ts_' s' && mask 4\<rparr>, fl))}
    \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) hs
         (setThreadState st thread) (Call setThreadState_'proc)"
   apply (cinit lift: tptr_' cong add: call_ignore_cong)
   apply (ctac (no_vcg) add: threadSet_tcbState_simple_corres)
    apply (ctac add: scheduleTCB_ccorres)
  apply (wp threadSet_weak_sch_act_wf_runnable' threadSet_valid_queues_and_runnable'
            threadSet_valid_objs')
  by (clarsimp simp: weak_sch_act_wf_def valid_queues_def valid_tcb'_tcbState_update)

lemma threadSet_valid_queues'_and_not_runnable': "\<lbrace>tcb_at' thread and valid_queues' and (\<lambda>s. (\<not> runnable' st))\<rbrace>
                  threadSet (tcbState_update (\<lambda>_. st)) thread
               \<lbrace>\<lambda>rv. tcb_at' thread and st_tcb_at' (not runnable') thread and valid_queues' \<rbrace>"

  apply (wp threadSet_valid_queues' threadSet_tcbState_st_tcb_at')
  apply (clarsimp simp: pred_neg_def valid_queues'_def inQ_def)+
done

lemma setThreadState_ccorres_valid_queues':
   "ccorres dc xfdc
   (\<lambda>s. tcb_at' thread s \<and> valid_queues' s \<and> \<not> runnable' st \<and> weak_sch_act_wf (ksSchedulerAction s) s \<and> Invariants_H.valid_queues s \<and> (\<forall>p. thread \<notin> set (ksReadyQueues s p)) \<and> sch_act_not thread s \<and> valid_objs' s \<and> valid_tcb_state' st s)
     ({s'. (\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := ts_' s' && mask 4\<rparr>, fl))}
    \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) []
         (setThreadState st thread) (Call setThreadState_'proc)"
   apply (cinit lift: tptr_' cong add: call_ignore_cong)
   apply (ctac (no_vcg) add: threadSet_tcbState_simple_corres)
    apply (ctac add: scheduleTCB_ccorres_valid_queues')
   apply (wp threadSet_valid_queues'_and_not_runnable' threadSet_weak_sch_act_wf_runnable' threadSet_valid_queues_and_runnable' threadSet_valid_objs')
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
    apply ((wp setNotification_nosch setNotification_ksQ hoare_vcg_all_lift set_ntfn_valid_objs' | simp add: valid_tcb_state'_def split del: if_split)+)[1]
   apply (simp add: "StrictC'_thread_state_defs")
  apply (rule conjI, clarsimp, rule conjI, clarsimp)
    apply (frule (1) ko_at_valid_ntfn'[OF _ invs_valid_objs'])
   subgoal by ((auto simp: obj_at'_def projectKOs st_tcb_at'_def invs'_def valid_state'_def
                     isTS_defs cte_wp_at_ctes_of "StrictC'_thread_state_defs"
                     cthread_state_relation_def sch_act_wf_weak valid_ntfn'_def
             dest!: valid_queues_not_runnable'_not_ksQ[where t=thread] |
           clarsimp simp: eq_commute)+)
   apply (clarsimp)
   apply (frule (1) ko_at_valid_ntfn'[OF _ invs_valid_objs'])
   apply (frule (2) ntfn_blocked_in_queueD)
   by (auto simp: obj_at'_def projectKOs st_tcb_at'_def invs'_def valid_state'_def
                     isTS_defs cte_wp_at_ctes_of "StrictC'_thread_state_defs" valid_ntfn'_def
                     cthread_state_relation_def sch_act_wf_weak isWaitingNtfn_def
             dest!: valid_queues_not_runnable'_not_ksQ[where t=thread]
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

(* FIXME AARCH64: x64 can be removed? *)
lemma epQueue_head_mask_2 [simp]:
  "epQueue_head_CL (endpoint_lift ko') && ~~ mask 2 = epQueue_head_CL (endpoint_lift ko')"
  unfolding endpoint_lift_def
  oops (*by (clarsimp simp: mask_def word_bw_assocs) *)

lemma epQueue_tail_mask_2 [simp]:
  "epQueue_tail_CL (endpoint_lift ko') && ~~ mask 2 = epQueue_tail_CL (endpoint_lift ko')"
  unfolding endpoint_lift_def
  by (clarsimp simp: mask_def word_bw_assocs)

(* FIXME AARCH64 is this used? useful? depends on deployment of make_canonical *)
lemma epQueue_tail_make_canonical[simp]:
  "make_canonical (epQueue_tail_CL (endpoint_lift ko)) = epQueue_tail_CL (endpoint_lift ko)"
  by (simp add: endpoint_lift_def make_canonical_def canonical_bit_def mask_def
                word_bw_assocs)

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
            apply (erule ctcb_relation_null_queue_ptrs)
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
        \<comment> \<open>queue relation\<close>
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         subgoal by (clarsimp simp: comp_def)
        subgoal by (clarsimp simp: carch_state_relation_def carch_globals_def
                                   packed_heap_update_collapse_hrs)
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
           apply (erule ctcb_relation_null_queue_ptrs)
           subgoal by (clarsimp simp: comp_def)
       \<comment> \<open>ep relation\<close>
          apply (rule cpspace_relation_ep_update_ep, assumption+)
           apply (simp add: cendpoint_relation_def Let_def isSendEP_def isRecvEP_def split: endpoint.splits split del: if_split)
           \<comment> \<open>recv case\<close>
            apply (subgoal_tac "pspace_canonical' \<sigma>")
             prefer 2
             apply fastforce
            apply (clarsimp
                     simp: h_t_valid_clift_Some_iff ctcb_offset_defs mask_shiftl_decompose
                           tcb_queue_relation'_next_mask tcb_queue_relation'_prev_mask
                           tcb_queue_relation'_next_canonical tcb_queue_relation'_prev_canonical
                     simp flip: canonical_bit_def make_canonical_def
                     cong: tcb_queue_relation'_cong)
            subgoal by (intro impI conjI; simp)
           \<comment> \<open>send case\<close>
            apply (subgoal_tac "pspace_canonical' \<sigma>")
             prefer 2
             apply fastforce
           apply (clarsimp
                    simp: h_t_valid_clift_Some_iff ctcb_offset_defs mask_shiftl_decompose
                          tcb_queue_relation'_next_mask tcb_queue_relation'_prev_mask
                          tcb_queue_relation'_next_canonical tcb_queue_relation'_prev_canonical
                    simp flip: canonical_bit_def
                    cong: tcb_queue_relation'_cong)
           subgoal by (intro impI conjI; simp)
          subgoal by simp
                \<comment> \<open>ntfn relation\<close>
         apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
         apply simp
         apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
         apply simp
         apply (erule (1) map_to_ko_atI')
         \<comment> \<open>queue relation\<close>
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        subgoal by (clarsimp simp: comp_def)
       subgoal by (clarsimp simp: carch_state_relation_def carch_globals_def
                                  packed_heap_update_collapse_hrs)
      subgoal by (simp add: cmachine_state_relation_def)
     subgoal by (simp add: h_t_valid_clift_Some_iff)
    subgoal by (simp add: objBits_simps')
   subgoal by (simp add: objBits_simps)
  by assumption

declare empty_fail_get[iff]

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
            apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs cong: call_ignore_cong)
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
                apply (simp add: "StrictC'_thread_state_defs")
               apply vcg
              apply (rule conseqPre, vcg)
              apply clarsimp
             apply clarsimp
             apply (rule conseqPre, vcg)
             apply (rule subset_refl)
            apply (rule conseqPre, vcg)
            apply clarsimp
          \<comment> \<open>BlockedOnReply case\<close>
           apply (simp add: "StrictC'_thread_state_defs" ccorres_cond_iffs
                            Collect_False Collect_True word_sle_def
                      cong: call_ignore_cong del: Collect_const)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
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
          apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs
                     cong: call_ignore_cong)
          apply (rule ccorres_symb_exec_r)
            apply (ctac (no_vcg))
           apply clarsimp
           apply (rule conseqPre, vcg)
           apply (rule subset_refl)
          apply (rule conseqPre, vcg)
          apply clarsimp
         \<comment> \<open>Running, Inactive, and Idle\<close>
         apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs
                    cong: call_ignore_cong,
                rule ccorres_return_Skip)+
      \<comment> \<open>BlockedOnSend\<close>
      apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs
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
       apply (simp add: "StrictC'_thread_state_defs")
         apply clarsimp
         apply (rule conseqPre, vcg, rule subset_refl)
        apply (rule conseqPre, vcg)
        apply clarsimp
       apply clarsimp
       apply (rule conseqPre, vcg, rule subset_refl)
      apply (rule conseqPre, vcg)
      apply clarsimp
  \<comment> \<open>Restart\<close>
     apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs
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
             dest!: valid_queues_not_runnable'_not_ksQ[where t=thread] split: thread_state.splits)
    apply clarsimp
    apply (frule (2) ep_blocked_in_queueD_recv)
    apply (frule (1) ko_at_valid_ep'[OF _ invs_valid_objs'])
    subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                         isTS_defs cte_wp_at_ctes_of isRecvEP_def
                         cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                 dest!: valid_queues_not_runnable'_not_ksQ[where t=thread] split: thread_state.splits endpoint.splits)
   apply (rule conjI)
    apply (clarsimp simp: inQ_def)
   apply (rule conjI)
    apply clarsimp
   apply clarsimp
   apply (rule conjI)
    subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                         isTS_defs cte_wp_at_ctes_of
                         cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                 dest!: valid_queues_not_runnable'_not_ksQ[where t=thread] split: thread_state.splits)
   apply clarsimp
   apply (rule conjI)
    subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                         isTS_defs cte_wp_at_ctes_of
                         cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                 dest!: valid_queues_not_runnable'_not_ksQ[where t=thread] split: thread_state.splits)
   apply clarsimp
   apply (frule (2) ep_blocked_in_queueD_send)
   apply (frule (1) ko_at_valid_ep'[OF _ invs_valid_objs'])
   subgoal by (auto simp: obj_at'_def projectKOs pred_tcb_at'_def invs'_def valid_state'_def
                        isTS_defs cte_wp_at_ctes_of isSendEP_def
                        cthread_state_relation_def sch_act_wf_weak valid_ep'_def
                dest!: valid_queues_not_runnable'_not_ksQ[where t=thread] split: thread_state.splits endpoint.splits)[1]
  apply (auto simp: isTS_defs cthread_state_relation_def typ_heap_simps weak_sch_act_wf_def)
  apply (case_tac ts,
           auto simp: isTS_defs cthread_state_relation_def typ_heap_simps)
  done

end
end
