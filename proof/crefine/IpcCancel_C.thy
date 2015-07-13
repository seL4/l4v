(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory IpcCancel_C
imports SyscallArgs_C
begin

context kernel_m
begin

lemma cready_queues_index_to_C_in_range':
  assumes prems: "qdom \<le> ucast maxDom" "prio \<le> ucast maxPrio"
  shows "cready_queues_index_to_C qdom prio < numDomains * numPriorities"
proof -
  have P: "unat prio < numPriorities"
    using prems
    by (simp add: numPriorities_def seL4_MaxPrio_def Suc_le_lessD unat_le_helper)
  have Q: "unat qdom < numDomains"
    using prems
    by (simp add: numDomains_def maxDom_def Suc_le_lessD unat_le_helper)
  show ?thesis
    using mod_lemma[OF _ P, where q="unat qdom" and c=numDomains] mod_less[OF Q]
    by (clarsimp simp: cready_queues_index_to_C_def field_simps numDomains_def)
qed

lemmas cready_queues_index_to_C_in_range
            = cready_queues_index_to_C_in_range'[unfolded numPriorities_def numDomains_def, simplified]

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
  apply (auto split: split_if)
  done

lemma valid_queuesD':
  "\<lbrakk> obj_at' (inQ d p) t s; valid_queues' s \<rbrakk>
        \<Longrightarrow> t \<in> set (ksReadyQueues s (d, p))"
  by (simp add: valid_queues'_def)

lemma invs_valid_queues'[elim!]:
  "invs' s \<Longrightarrow> valid_queues' s"
  by (simp add: invs'_def valid_state'_def)


lemma aep_ptr_get_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> \<sigma> \<Turnstile>\<^sub>c \<^bsup>\<sigma>\<^esup>aepptr} \<acute>ret__struct_tcb_queue_C :== PROC aep_ptr_get_queue(\<acute>aepptr) 
       \<lbrace>head_C \<acute>ret__struct_tcb_queue_C = Ptr (aepQueue_head_CL (async_endpoint_lift (the (cslift s \<^bsup>s\<^esup>aepptr)))) \<and>
        end_C \<acute>ret__struct_tcb_queue_C = Ptr (aepQueue_tail_CL (async_endpoint_lift (the (cslift s \<^bsup>s\<^esup>aepptr))))\<rbrace>"
  apply vcg
  apply clarsimp
  done

declare td_names_word8[simp]

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
              \<and> (ep_queue_relation' (cslift t) (Lib.delete (ctcb_ptr_to_tcb_ptr \<^bsup>s\<^esup>tcb) queue) (head_C (ret__struct_tcb_queue_C_' t)) (end_C (ret__struct_tcb_queue_C_' t))
                \<and> (cslift t |` (- tcb_ptr_to_ctcb_ptr ` set queue)) = 
                  (cslift s |` (- tcb_ptr_to_ctcb_ptr ` set queue))
                \<and> option_map tcb_null_ep_ptrs \<circ> (cslift t) = 
                  option_map tcb_null_ep_ptrs \<circ> (cslift s))
                \<and> cslift_all_but_tcb_C t s \<and> (hrs_htd \<^bsup>t\<^esup>t_hrs) = (hrs_htd \<^bsup>s\<^esup>t_hrs)}"         
  apply (intro allI)
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp split del: split_if)
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
  apply (simp add: typ_heap_simps)
  apply (intro allI conjI impI)
            apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff)
           apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff
                           cong: if_weak_cong)
          apply (rule ext)
          apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def)
         apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff)
        apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff)
       apply (rule ext)
       apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def
                       cong: if_weak_cong)
      apply (rule ext)
      apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def)
     apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff)
    apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff
                    cong: if_weak_cong)
   apply (rule ext)
   apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff tcb_null_ep_ptrs_def)
  apply simp
  done

lemma aep_ptr_set_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. s \<Turnstile>\<^sub>c \<acute>aepptr\<rbrace> Call aep_ptr_set_queue_'proc 
           {t. (\<exists>aep'. async_endpoint_lift aep' = 
  (async_endpoint_lift (the (cslift s (\<^bsup>s\<^esup>aepptr))))\<lparr> aepQueue_head_CL := ptr_val (head_C \<^bsup>s\<^esup>aep_queue) && ~~ mask 4,
                                                      aepQueue_tail_CL := ptr_val (end_C \<^bsup>s\<^esup>aep_queue) && ~~ mask 4 \<rparr> \<and>
             (cslift t :: async_endpoint_C typ_heap) = (cslift s)(\<^bsup>s\<^esup>aepptr \<mapsto> aep'))
             \<and> cslift_all_but_async_endpoint_C t s \<and> (hrs_htd \<^bsup>t\<^esup>t_hrs) = (hrs_htd \<^bsup>s\<^esup>t_hrs)}"
  apply vcg
  apply (auto simp: split_def h_t_valid_clift_Some_iff)
  done

lemma asyncIPCCancel_ccorres_helper:
  "ccorres dc xfdc (invs' and st_tcb_at' (op = (BlockedOnAsyncEvent aep)) thread and ko_at' aep' aep)
        UNIV
        []
        (setAsyncEP aep
          (if remove1 thread (aepQueue aep') = []
           then async_endpoint.IdleAEP
           else aepQueue_update (\<lambda>_. remove1 thread (aepQueue aep')) aep'))
        (\<acute>aep_queue :== CALL aep_ptr_get_queue(Ptr aep);;
         \<acute>aep_queue :== CALL tcbEPDequeue(tcb_ptr_to_ctcb_ptr thread,\<acute>aep_queue);;
         CALL aep_ptr_set_queue(Ptr aep,\<acute>aep_queue);;
         IF head_C \<acute>aep_queue = NULL THEN
           CALL async_endpoint_ptr_set_state(Ptr aep,
           scast AEPState_Idle)
         FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp split del: split_if simp del: comp_def)
  apply (frule (2) aep_blocked_in_queueD)
  apply (frule (1) ko_at_valid_aep' [OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) valid_aep_isWaitingAEPD)
  apply (elim conjE)
  apply (frule cmap_relation_aep)
  apply (erule (1) cmap_relation_ko_atE)  
  apply (rule conjI)
   apply (erule h_t_valid_clift)
  apply (rule impI)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x = \<sigma> in exI)
   apply (intro conjI, assumption+)
   apply (drule (2) aep_to_ep_queue)
   apply (simp add: tcb_queue_relation'_def)
  apply (clarsimp simp: typ_heap_simps cong: imp_cong split del: split_if simp del: comp_def)  
  apply (frule null_ep_queue [simplified Fun.comp_def])
  apply (intro impI conjI allI)
   -- "empty case"
   apply clarsimp
   apply (frule iffD1 [OF tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel]])
     apply (rule ballI, erule bspec)
     apply (erule subsetD [rotated])
     apply clarsimp
    apply simp
   apply (simp add: setAsyncEP_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: remove1_empty  rf_sr_def cstate_relation_def Let_def cpspace_relation_def update_aep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
            -- "tcb relation"
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           -- "ep relation"
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule cendpoint_relation_aep_queue [OF invs_sym'], assumption+)
           apply simp
           apply (erule (1) map_to_ko_atI')
          -- "aep relation"
          apply (rule cpspace_relation_aep_update_aep, assumption+)
          apply (simp add: casync_endpoint_relation_def Let_def AEPState_Idle_def)
          apply (simp add: carch_state_relation_def carch_globals_def)
         -- "queue relation"
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def carch_globals_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)

     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
  -- "non empty case"
  apply clarsimp
  apply (frule tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel]) 
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
   apply clarsimp
  apply (simp add: setAsyncEP_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (frule (1) st_tcb_at_h_t_valid)
      apply (simp add: remove1_empty rf_sr_def cstate_relation_def Let_def cpspace_relation_def update_aep_map_tos)
      apply (elim conjE)
      apply (intro conjI)
           -- "tcb relation"
           apply (erule ctcb_relation_null_queue_ptrs)
           apply (clarsimp simp: comp_def)
          -- "ep relation"
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule cendpoint_relation_aep_queue)
              apply fastforce
             apply assumption+
          apply simp
          apply (erule (1) map_to_ko_atI')
         -- "aep relation"
         apply (rule cpspace_relation_aep_update_aep, assumption+)
          apply (simp add: casync_endpoint_relation_def Let_def isWaitingAEP_def split: async_endpoint.splits split del: split_if)
          apply (erule iffD1 [OF tcb_queue_relation'_cong [OF refl _ _ refl], rotated -1])  
           apply (clarsimp simp add: Ptr_ptr_val h_t_valid_clift_Some_iff)
           apply (simp add: tcb_queue_relation'_next_mask_4)
          apply (clarsimp simp add: Ptr_ptr_val h_t_valid_clift_Some_iff)
          apply (simp add: tcb_queue_relation'_prev_mask_4)
         apply simp
        -- "queue relation"
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        apply (clarsimp simp: comp_def)
       apply (simp add: carch_state_relation_def carch_globals_def)
      apply (simp add: cmachine_state_relation_def)
     apply (simp add: h_t_valid_clift_Some_iff)
    apply (simp add: objBits_simps)
   apply (simp add: objBits_simps)
  apply assumption
  done


lemma threadSet_tcbState_simple_corres:
  "ccorres dc xfdc (tcb_at' thread)
        {s. (\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := v_' s && mask 4\<rparr>, fl)) \<and>
           thread_state_ptr_' s = Ptr &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C''])} []  
        (threadSet (tcbState_update (\<lambda>_. st)) thread)  (Call thread_state_ptr_set_tsType_'proc)"
  apply (rule threadSet_corres_lemma)
  apply (rule thread_state_ptr_set_tsType_spec)
  apply (rule thread_state_ptr_set_tsType_modifies)
   apply clarsimp   
   apply (frule (1) obj_at_cslift_tcb)
   apply clarsimp
   apply (rule rf_sr_tcb_update_no_queue, assumption+, simp_all)       
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
      
lemma isBlocked_ccorres [corres]:
  "ccorres (\<lambda>r r'. r = to_bool r') ret__unsigned_long_' 
  (tcb_at' thread) (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread})  []
  (isBlocked thread) (Call isBlocked_'proc)"  
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
  apply (clarsimp simp: to_bool_def true_def false_def typ_heap_simps
    ctcb_relation_thread_state_to_tsType split: thread_state.splits)
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
  apply (clarsimp simp: to_bool_def true_def false_def typ_heap_simps
    ctcb_relation_thread_state_to_tsType split: thread_state.splits)
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
  apply (clarsimp simp: pnu upd_unless_null_def fg_consD1 [OF fgN] fg_consD1 [OF fgP] pnu npu) 
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
  apply (clarsimp simp: valid_queues_def)
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

declare unat_ucast_8_32[simp]

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
        {s. v_' s = from_bool v \<and> thread_state_ptr_' s = Ptr &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C''])} []  
        (threadSet (tcbQueued_update (\<lambda>_. v)) thread) 
        (Call thread_state_ptr_set_tcbQueued_'proc)"
  apply (rule threadSet_corres_lemma)
     apply (rule thread_state_ptr_set_tcbQueued_spec)
    apply (rule thread_state_ptr_set_tcbQueued_modifies)
   apply clarsimp
   apply (frule (1) obj_at_cslift_tcb)
   apply clarsimp 
   apply (rule rf_sr_tcb_update_no_queue, assumption+, simp_all)
   apply (rule ball_tcb_cte_casesI, simp_all)
   apply (simp add: ctcb_relation_def cthread_state_relation_def)
   apply (case_tac "tcbState ko", simp_all add: WordLemmaBucket.from_bool_mask_simp)[1]
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
  
(* FIXME: move *)
lemma threadGet_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at' tcb thread s \<longrightarrow> P (f tcb) s\<rbrace> threadGet f thread \<lbrace>P\<rbrace>"
  apply (rule hoare_post_imp [OF _ tg_sp'])  
  apply clarsimp
  apply (frule obj_at_ko_at')
  apply (clarsimp elim: obj_atE')
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
      -- "cpspace_relation"
     apply (erule nonemptyE, drule(1) bspec)
     apply (clarsimp simp: cpspace_relation_def)
     apply (drule obj_at_ko_at', clarsimp)
     apply (rule cmap_relationE1, assumption,
            erule ko_at_projectKO_opt)
     apply (frule null_sched_queue)
     apply (frule null_sched_epD)
     apply (intro conjI)
       -- "tcb relation"
       apply (drule ctcb_relation_null_queue_ptrs,
              simp_all)[1]
      -- "endpoint relation"
      apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
      apply simp
      apply (erule cendpoint_relation_upd_tcb_no_queues, simp+)
     -- "aep relation"
     apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
     apply simp
     apply (erule casync_endpoint_relation_upd_tcb_no_queues, simp+)
    -- "ready queues"
    apply (simp add: cready_queues_relation_def Let_def
                     cready_queues_index_to_C_in_range
                     seL4_MinPrio_def minDom_def)
    apply clarsimp
    apply (frule cready_queues_index_to_C_distinct, assumption+)
    apply (clarsimp simp: cready_queues_index_to_C_in_range all_conj_distrib)
    apply (rule iffD1 [OF tcb_queue_relation'_cong[OF refl], rotated -1],
           drule spec, drule spec, erule mp, simp+)
    apply clarsimp
    apply (drule_tac x="tcb_ptr_to_ctcb_ptr x" in fun_cong)+
    apply (clarsimp simp: restrict_map_def
                   split: split_if_asm)
   apply (simp_all add: carch_state_relation_def cmachine_state_relation_def 
                        h_t_valid_clift_Some_iff)
  done

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
   apply (erule(12) state_relation_queue_update_helper')
  apply (clarsimp simp: valid_queues_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply (clarsimp)
  apply (drule(1) bspec)
  apply (erule obj_at'_weakenE, clarsimp)
  done

(* FIXME: move *)
lemma from_bool_vals [simp]: 
  "from_bool True = scast true"
  "from_bool False = scast false"
  "scast true \<noteq> scast false"
  by (auto simp add: from_bool_def true_def false_def)

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

lemma cready_queues_index_to_C_def2':
  "\<lbrakk> qdom \<le> ucast maxDom; prio \<le> ucast maxPrio \<rbrakk>
   \<Longrightarrow> cready_queues_index_to_C qdom prio
             = unat (ucast qdom * of_nat numPriorities + ucast prio :: 32 word)"
  apply (simp add: cready_queues_index_to_C_def numPriorities_def)
  apply (subst unat_add_lem[THEN iffD1])
   apply (frule cready_queues_index_to_C_in_range, simp)
   apply (simp add: cready_queues_index_to_C_def numPriorities_def)
   apply (subst unat_mult_simple)
    apply (simp add: word_bits_def maxDom_def)
   apply simp
  apply (subst unat_mult_simple)
   apply (simp add: word_bits_def maxDom_def)
   apply (subst (asm) word_le_nat_alt)
   apply simp
  apply simp
  done

lemmas cready_queues_index_to_C_def2
           = cready_queues_index_to_C_def2'[simplified maxDom_to_H maxPrio_to_H]

lemma ready_queues_index_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call ready_queues_index_'proc
       \<lbrace>\<acute>ret__unsigned = (dom___unsigned_' s) * 0x100 + (prio___unsigned_' s)\<rbrace>"
  apply vcg
  apply clarsimp
  done

lemma tcbSchedEnqueue_ccorres:
  "ccorres dc xfdc 
           (valid_queues and tcb_at' t and valid_objs')
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           []
           (tcbSchedEnqueue t)
           (Call tcbSchedEnqueue_'proc)"
  apply (cinit lift: tcb_')
   apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'"
              and xf'="ret__unsigned_long_'" in ccorres_split_nothrow)
       apply (rule threadGet_vcg_corres)
       apply (rule allI, rule conseqPre, vcg)
       apply clarsimp
       apply (drule obj_at_ko_at', clarsimp)
       apply (drule spec, drule(1) mp, clarsimp)
       apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
      apply ceqv
     apply (simp add: unless_def when_def
                 del: Collect_const split del: split_if)
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
             apply (simp only: dc_def[symmetric])
             apply ctac
            prefer 2
            apply wp
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply (rule_tac P="\<lambda>s. valid_queues s \<and> (\<forall>d p. t \<notin> set (ksReadyQueues s (d, p)))
                                  \<and> (\<exists>tcb. ko_at' tcb t s \<and> tcbDomain tcb =rva
                                  \<and> tcbPriority tcb = rvb \<and> valid_tcb' tcb s)" 
                       and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: getQueue_def gets_def get_def setQueue_def modify_def 
                                 put_def bind_def return_def)
           apply (clarsimp simp: queue_in_range valid_tcb'_def maxDom_to_H maxPrio_to_H)
           apply (drule (1) obj_at_cslift_tcb)
           apply (clarsimp simp: ucast_less[THEN order_less_le_trans])
           apply (frule_tac d="tcbDomain tcba" and p="tcbPriority tcba"
                      in rf_sr_sched_queue_relation)
             apply (clarsimp simp: maxDom_to_H)
            apply (clarsimp simp: maxPrio_to_H)
           apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL)
            apply (simp add: valid_queues_valid_q)
           apply (frule_tac s=\<sigma> and qhead'="tcb_ptr_to_ctcb_ptr t"
                       in tcbSchedEnqueue_update,
                  simp_all add: valid_queues_valid_q)[1]
             apply (rule notI, drule tcb_ptr_to_ctcb_ptr_imageD)
             apply simp
            apply (rule tcb_at_not_NULL,
                   erule obj_at'_weakenE, simp)
           apply (rule conjI)
            apply (clarsimp simp: typ_heap_simps)
            apply (erule(1) state_relation_queue_update_helper
                                    [where S="{t}"],
                   simp_all add: cready_queues_index_to_C_def2 numPriorities_def
                                 typ_heap_simps maxDom_to_H maxPrio_to_H)[1]
              apply (simp add: upd_unless_null_def)
             apply (rule ext)
             apply (simp add: tcb_null_sched_ptrs_def)
            apply (simp add: obj_at'_weakenE[OF _ TrueI])
           apply (frule_tac t=\<sigma> in tcb_queue_relation_qhead_mem')
            apply (simp add: valid_queues_valid_q)
           apply (drule(1) tcb_queue_relation_qhead_valid')
            apply (simp add: valid_queues_valid_q)
           apply (clarsimp simp: typ_heap_simps h_t_valid_clift_Some_iff numPriorities_def
                                 cready_queues_index_to_C_def2)
           apply (erule_tac S="{t, v}" for v in state_relation_queue_update_helper,
                  simp_all add: cready_queues_index_to_C_def2 numPriorities_def
                                 typ_heap_simps maxDom_to_H maxPrio_to_H)[1]
              apply (simp add: upd_unless_null_def)
              apply (subst clift_field_update
                       | simp add: if_Some_helper
                             split del: split_if cong: if_cong)+
              apply (simp split: split_if, intro impI conjI)
               apply (drule ctcb_ptr_to_tcb_ptr_imageI)
               apply fastforce
              apply (simp add: fun_upd_twist)
             prefer 3
             apply (simp add: obj_at'_weakenE[OF _ TrueI])
             apply (rule disjI1, erule(1) valid_queues_obj_at'D)
            apply (subst clift_field_update | simp split del: split_if
                     | simp add: typ_heap_simps if_Some_helper cong: if_cong)+
           apply (intro conjI impI ext)
            apply (simp add: tcb_null_sched_ptrs_def)
           apply (simp add: tcb_null_sched_ptrs_def)
        apply (simp add: guard_is_UNIV_def true_def from_bool_def)
         apply simp
         apply (wp threadGet_wp)
        apply vcg
       apply simp
       apply (wp threadGet_wp)
      apply vcg
     apply (rule ccorres_return_Skip[unfolded dc_def])
    apply simp
    apply (wp threadGet_wp)
   apply vcg
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule(1) valid_queues_obj_at'D)
   apply (clarsimp simp: obj_at'_def projectKOs inQ_def)
  apply (fastforce simp: valid_objs'_def obj_at'_def ran_def projectKOs
                         typ_at'_def valid_obj'_def)
  done

lemmas tcbSchedDequeue_update
    = tcbDequeue_update[where tn=tcbSchedNext_C and tn_update=tcbSchedNext_C_update
                          and tp=tcbSchedPrev_C and tp_update=tcbSchedPrev_C_update,
                        simplified]

lemma tcb_queue_relation_prev_next:
  "\<lbrakk> tcb_queue_relation tn tp mp queue qprev qhead;
     tcbp \<in> set queue; distinct (ctcb_ptr_to_tcb_ptr qprev # queue);
     \<forall>t \<in> set queue. tcb_at' t s; qprev \<noteq> tcb_Ptr 0 \<longrightarrow> mp qprev \<noteq> None;
     mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb \<rbrakk>
      \<Longrightarrow> (tn tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tn tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue
                       \<and> mp (tn tcb) \<noteq> None \<and> tn tcb \<noteq> tcb_ptr_to_ctcb_ptr tcbp)
        \<and> (tp tcb \<noteq> tcb_Ptr 0 \<longrightarrow> (tp tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue
                                         \<or> tp tcb = qprev)
                       \<and> mp (tp tcb) \<noteq> None \<and> tp tcb \<noteq> tcb_ptr_to_ctcb_ptr tcbp)
        \<and> (tn tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tn tcb \<noteq> tp tcb)"
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
   apply (drule_tac f=ctcb_ptr_to_tcb_ptr in arg_cong[where y="tp tcb"], simp)
  apply clarsimp
  apply fastforce
  done

lemma tcb_queue_relation_prev_next':
  "\<lbrakk> tcb_queue_relation' tn tp mp queue qhead qend; tcbp \<in> set queue; distinct queue;
       \<forall>t \<in> set queue. tcb_at' t s; mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb \<rbrakk>
      \<Longrightarrow> (tn tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tn tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue
                       \<and> mp (tn tcb) \<noteq> None \<and> tn tcb \<noteq> tcb_ptr_to_ctcb_ptr tcbp)
        \<and> (tp tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tp tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue
                       \<and> mp (tp tcb) \<noteq> None \<and> tp tcb \<noteq> tcb_ptr_to_ctcb_ptr tcbp)
        \<and> (tn tcb \<noteq> tcb_Ptr 0 \<longrightarrow> tn tcb \<noteq> tp tcb)"
  apply (clarsimp simp: tcb_queue_relation'_def split: split_if_asm)
  apply (drule(1) tcb_queue_relation_prev_next, simp_all)
   apply (fastforce dest: tcb_at_not_NULL)
  apply clarsimp
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
  have ksQ_tcb_at': "\<And>s ko d p.
    \<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s)
                                          \<and> distinct (ksReadyQueues s (d, p)) \<Longrightarrow>
    \<forall>t\<in>set (ksReadyQueues s (d, p)). tcb_at' t s"
    by (fastforce dest: spec elim: obj_at'_weakenE)
  show ?thesis
  apply (cinit lift: tcb_')
   apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'"
              and xf'="ret__unsigned_long_'" in ccorres_split_nothrow)
       apply (rule threadGet_vcg_corres)
       apply (rule allI, rule conseqPre, vcg)
       apply clarsimp
       apply (drule obj_at_ko_at', clarsimp)
       apply (drule spec, drule(1) mp, clarsimp)
       apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
      apply ceqv
     apply (simp add: when_def
                 del: Collect_const split del: split_if)
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
             apply (simp only: dc_def[symmetric])
             apply ctac
            prefer 2
            apply wp
           apply (rule_tac P="(\<lambda>s. \<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s)
                                       \<and> distinct(ksReadyQueues s (d, p)))
                               and valid_queues' and obj_at' (inQ rva rvb) t
                               and (\<lambda>s. rva \<le> maxDomain \<and> rvb \<le> maxPriority)"
                       and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: getQueue_def gets_def get_def setQueue_def modify_def 
                                 put_def bind_def return_def)
           apply (clarsimp simp: queue_in_range[simplified maxDom_to_H maxPrio_to_H])
           apply (frule(1) valid_queuesD')
           apply (drule (1) obj_at_cslift_tcb, clarsimp simp: inQ_def)
           apply (frule_tac d="tcbDomain ko" and p="tcbPriority ko"
                      in rf_sr_sched_queue_relation)
             apply (clarsimp simp: maxDom_to_H)
            apply (clarsimp simp: maxPrio_to_H)
           apply (frule_tac s=\<sigma> in tcb_queue_relation_prev_next', assumption)
              apply simp
             apply (simp add: ksQ_tcb_at')
            apply assumption
           apply (drule_tac s=\<sigma> in tcbSchedDequeue_update, assumption,
                  simp_all add: remove1_filter ksQ_tcb_at')[1]
           apply (clarsimp simp: h_val_field_clift'
                                 h_t_valid_c_guard [OF h_t_valid_field, OF h_t_valid_clift]
                                 h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift
                                 ucast_less[THEN order_less_le_trans])
           apply (rule conjI)
            apply (clarsimp simp: h_val_field_clift' if_Some_helper clift_field_update
                                  h_t_valid_c_guard [OF h_t_valid_field, OF h_t_valid_clift]
                                  h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift
                       split del: split_if cong: if_cong)
            apply (rule conjI)
             apply (clarsimp simp: h_t_valid_c_guard [OF h_t_valid_field, OF h_t_valid_clift]
                                   h_t_valid_clift[THEN h_t_valid_field] h_t_valid_clift)
             apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                         in state_relation_queue_update_helper',
                    assumption, subst update_index_same,
                    simp_all add: clift_field_update if_Some_helper
                            cong: if_cong split del: split_if)[1]
                  apply (simp add: upd_unless_null_def eq_commute)
                 apply (rule ext, simp add: tcb_null_sched_ptrs_def)
                apply (simp add: typ_heap_simps)
               apply clarsimp
              apply (clarsimp simp: maxDom_to_H)
             apply (clarsimp simp: maxPrio_to_H)
            apply clarsimp
            apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                         in state_relation_queue_update_helper', assumption,
                   simp_all add: clift_field_update if_Some_helper numPriorities_def
                                 cready_queues_index_to_C_def2
                           cong: if_cong split del: split_if)[1]
                 apply (simp add: upd_unless_null_def eq_commute)
                apply (rule ext, simp add: tcb_null_sched_ptrs_def)
               apply (simp add: typ_heap_simps)
              apply clarsimp
             apply (clarsimp simp: maxDom_to_H)
            apply (clarsimp simp: maxPrio_to_H)
           apply clarsimp
           apply (rule conjI)
            apply (clarsimp simp: h_t_valid_c_guard [OF h_t_valid_field, OF h_t_valid_clift]
                                  h_t_valid_field[OF h_t_valid_clift] h_t_valid_clift)
            apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                         in state_relation_queue_update_helper', assumption,
                   simp_all add: clift_field_update if_Some_helper numPriorities_def
                                 cready_queues_index_to_C_def2
                           cong: if_cong split del: split_if)[1]
                 apply (simp add: upd_unless_null_def eq_commute)
                apply (rule ext, simp add: tcb_null_sched_ptrs_def)
               apply (simp add: typ_heap_simps)
              apply clarsimp
             apply (clarsimp simp: maxDom_to_H)
            apply (clarsimp simp: maxPrio_to_H)
           apply clarsimp
           apply (erule_tac S="set (ksReadyQueues \<sigma> (tcbDomain ko, tcbPriority ko))"
                       and f="\<lambda>_. t_hrs_' (globals x)"
                        in state_relation_queue_update_helper', assumption,
                  simp_all add: clift_field_update if_Some_helper numPriorities_def
                                cready_queues_index_to_C_def2
                          cong: if_cong split del: split_if)[1]
              apply (simp add: upd_unless_null_def eq_commute)
             apply clarsimp
            apply (clarsimp simp: maxDom_to_H)
           apply (clarsimp simp: maxPrio_to_H)
          apply (simp add: guard_is_UNIV_def)
         apply simp
         apply (wp threadGet_wp)
        apply vcg
       apply simp
       apply (wp threadGet_wp)
      apply vcg
     apply (rule ccorres_return_Skip[unfolded dc_def])
    apply simp
    apply (wp threadGet_wp)
   apply vcg
  apply (fastforce simp: valid_objs'_def obj_at'_def ran_def projectKOs typ_at'_def
                         valid_obj'_def valid_tcb'_def inQ_def)
  done
qed

lemma tcbSchedDequeue_ccorres:
  "ccorres dc xfdc 
           (valid_queues and valid_queues' and tcb_at' t and valid_objs')
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           []
           (tcbSchedDequeue t)
           (Call tcbSchedDequeue_'proc)"
  apply (rule ccorres_guard_imp [OF tcbSchedDequeue_ccorres'])
   apply (clarsimp simp: valid_queues_def)
   apply (drule_tac x=d in spec)
   apply (drule_tac x=p in spec)
   apply (clarsimp)
   apply (drule(1) bspec)
   apply (erule obj_at'_weakenE)
   apply (clarsimp)+
  done

lemma tcb_queue_relation_append:
  "\<lbrakk> tcb_queue_relation tn tp mp queue qprev qhead; queue \<noteq> [];
     qend' \<notin> tcb_ptr_to_ctcb_ptr ` set queue; mp qend' = Some tcb;
     queue = queue' @ [ctcb_ptr_to_tcb_ptr qend]; distinct queue;
     \<forall>x \<in> set queue. tcb_ptr_to_ctcb_ptr x \<noteq> NULL; qend' \<noteq> NULL;
     \<And>v f g. tn (tn_update f v) = f (tn v) \<and> tp (tp_update g v) = g (tp v)
                \<and> tn (tp_update f v) = tn v \<and> tp (tn_update g v) = tp v \<rbrakk>
    \<Longrightarrow> tcb_queue_relation tn tp
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
  apply (cinit lift: tcb_')
   apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'"
              and xf'="ret__unsigned_long_'" in ccorres_split_nothrow)
       apply (rule threadGet_vcg_corres)
       apply (rule allI, rule conseqPre, vcg)
       apply clarsimp
       apply (drule obj_at_ko_at', clarsimp)
       apply (drule spec, drule(1) mp, clarsimp)
       apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
      apply ceqv
     apply (simp add: when_def unless_def
                 del: Collect_const split del: split_if)
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
             apply (simp only: dc_def[symmetric])
             apply ctac
            prefer 2
            apply wp
           apply (rule_tac P="\<lambda>s. valid_queues s \<and> (\<forall>p. t \<notin> set (ksReadyQueues s p))
                                  \<and> (\<exists>tcb. ko_at' tcb t s \<and> tcbDomain tcb =rva
                                  \<and> tcbPriority tcb = rvb \<and> valid_tcb' tcb s)"
                       and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: getQueue_def gets_def get_def setQueue_def modify_def 
                                 put_def bind_def return_def)
           apply (clarsimp simp: queue_in_range valid_tcb'_def maxDom_to_H maxPrio_to_H)
           apply (drule (1) obj_at_cslift_tcb)
           apply clarsimp
           apply (frule_tac d="tcbDomain tcba" and p="tcbPriority tcba"
                      in rf_sr_sched_queue_relation)
             apply (clarsimp simp: maxDom_to_H)
            apply (clarsimp simp: maxPrio_to_H)
           apply (frule_tac s=\<sigma> in tcb_queue'_head_end_NULL)
            apply (simp add: valid_queues_valid_q)
           apply (frule_tac s=\<sigma> in tcb_queue_relation_qend_mems,
                  simp add: valid_queues_valid_q)
           apply (drule_tac qend'="tcb_ptr_to_ctcb_ptr t" and s=\<sigma> in tcbSchedAppend_update,
                  simp_all add: valid_queues_valid_q)[1]
             apply clarsimp
            apply (rule tcb_at_not_NULL, erule obj_at'_weakenE, simp)
           apply (clarsimp simp: h_val_field_clift' h_t_valid_clift
                                 h_t_valid_c_guard [OF h_t_valid_field, OF h_t_valid_clift]
                                 h_t_valid_field[OF h_t_valid_clift]
                                 ucast_less[THEN order_less_le_trans])
           apply (rule conjI)
            apply clarsimp
            apply (erule(1) state_relation_queue_update_helper
                                    [where S="{t}"],
                   simp_all add: cready_queues_index_to_C_def2 numPriorities_def
                                 typ_heap_simps maxDom_to_H maxPrio_to_H)[1]
              apply (simp add: upd_unless_null_def)
             apply (rule ext)
             apply (simp add: tcb_null_sched_ptrs_def)
            apply (simp add: obj_at'_weakenE[OF _ TrueI])
           apply (clarsimp simp: cready_queues_index_to_C_def2 numPriorities_def)
           apply (frule(2) obj_at_cslift_tcb[OF valid_queues_obj_at'D])
           apply (clarsimp simp: h_val_field_clift' h_t_valid_clift
                                 h_t_valid_c_guard [OF h_t_valid_field, OF h_t_valid_clift]
                                 h_t_valid_field[OF h_t_valid_clift])
           apply (erule_tac S="{t, v}" for v in state_relation_queue_update_helper,
                  simp_all add: typ_heap_simps if_Some_helper numPriorities_def
                                cready_queues_index_to_C_def2
                          cong: if_cong split del: split_if
                           del: fun_upd_restrict_conv)[1]
                apply (simp add: upd_unless_null_def split: split_if_asm)
                apply (rule conjI)
                 apply clarsimp
                 apply (drule_tac s="tcb_ptr_to_ctcb_ptr t" in sym, simp)
                apply clarsimp
                apply (simp add: fun_upd_twist)
               prefer 3
               apply (simp add: obj_at'_weakenE[OF _ TrueI])
               apply (rule disjI1, erule valid_queues_obj_at'D)
               apply simp
              apply simp
             apply (rule ext, simp add: tcb_null_sched_ptrs_def)
             apply clarsimp
            apply (clarsimp simp: maxDom_to_H)
           apply (clarsimp simp: maxPrio_to_H)
          apply (simp add: guard_is_UNIV_def)
         apply simp
         apply (wp threadGet_wp)
        apply vcg
       apply simp
       apply (wp threadGet_wp)
      apply vcg
     apply (rule ccorres_return_Skip[unfolded dc_def])
    apply simp
    apply (wp threadGet_wp)
   apply vcg
  apply (fastforce simp: valid_objs'_def obj_at'_def ran_def projectKOs typ_at'_def
                         valid_obj'_def inQ_def
                   dest!: valid_queues_obj_at'D)
  done

lemma true_eq_from_bool [simp]:
  "(scast true = from_bool P) = P"
  by (simp add: true_def from_bool_def split: bool.splits)

lemma isBlocked_spec:
  "\<forall>s. \<Gamma> \<turnstile> ({s} \<inter> {s. cslift s (thread_' s) \<noteq> None}) Call isBlocked_'proc 
       {s'. ret__unsigned_long_' s' = from_bool (tsType_CL (thread_state_lift (tcbState_C (the (cslift s (thread_' s))))) \<in> 
                            {scast ThreadState_BlockedOnReply, 
                             scast ThreadState_BlockedOnAsyncEvent, scast ThreadState_BlockedOnSend, 
                             scast ThreadState_BlockedOnReceive, scast ThreadState_Inactive}) }"
  apply vcg
  apply (clarsimp simp: typ_heap_simps)
done


declare scast_from_bool [simp]
declare from_bool_1 [simp]

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

lemma tcb_at_max_word:
  "tcb_at' t s \<Longrightarrow> tcb_ptr_to_ctcb_ptr t \<noteq> tcb_Ptr max_word"
  apply (drule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (clarsimp simp add: is_aligned_def max_word_def)
  done

lemma scast_max_word [simp]:
    "scast (max_word :: 32 signed word) = (max_word :: 32 word)"
  by (clarsimp simp: max_word_def)

lemma rescheduleRequired_ccorres:
  "ccorres dc xfdc (valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and valid_objs')
           UNIV [] rescheduleRequired (Call rescheduleRequired_'proc)"
  apply cinit
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
          apply (simp add: scheduler_action_case_switch_to_if
                      cong: if_weak_cong split del: split_if)
          apply (rule_tac R="\<lambda>s. action = ksSchedulerAction s \<and> weak_sch_act_wf action s"
                     in ccorres_cond)
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def)
            apply (clarsimp simp: weak_sch_act_wf_def tcb_at_max_word tcb_at_not_NULL
                           split: scheduler_action.split_asm dest!: st_tcb_at')
           apply (ctac add: tcbSchedEnqueue_ccorres)
          apply (rule ccorres_return_Skip)
         apply ceqv
        apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: setSchedulerAction_def simpler_modify_def)
        apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                              cscheduler_action_relation_def
                              carch_state_relation_def cmachine_state_relation_def
                              max_word_def)
       apply wp
      apply (simp add: guard_is_UNIV_def)
     apply wp
   apply (simp add: getSchedulerAction_def)
  apply (clarsimp simp: weak_sch_act_wf_def rf_sr_def cstate_relation_def
                        Let_def cscheduler_action_relation_def)
  apply (auto simp: tcb_at_not_NULL tcb_at_max_word
                    tcb_at_not_NULL[THEN not_sym] tcb_at_max_word[THEN not_sym]
                 split: scheduler_action.split_asm)[1]
  done

lemma rescheduleRequired_ccorres_valid_queues': 
  "ccorresG rf_sr \<Gamma> dc xfdc (valid_queues' and sch_act_simple) UNIV [] rescheduleRequired (Call rescheduleRequired_'proc)"
  apply cinit
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
          apply (simp add: scheduler_action_case_switch_to_if
                      cong: if_weak_cong split del: split_if)
          apply (rule_tac R="\<lambda>s. action = ksSchedulerAction s \<and> sch_act_simple s"
                     in ccorres_cond)
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def)
            apply (clarsimp simp: weak_sch_act_wf_def tcb_at_max_word tcb_at_not_NULL
                           split: scheduler_action.split_asm dest!: st_tcb_at')
           apply (ctac add: tcbSchedEnqueue_ccorres)
          apply (rule ccorres_return_Skip)
         apply ceqv
        apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: setSchedulerAction_def simpler_modify_def)
        apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                              cscheduler_action_relation_def
                              carch_state_relation_def cmachine_state_relation_def
                              max_word_def)
       apply wp
      apply (simp add: guard_is_UNIV_def)
     apply wp
   apply (simp add: getSchedulerAction_def)
  apply (clarsimp simp: weak_sch_act_wf_def rf_sr_def cstate_relation_def
                        Let_def cscheduler_action_relation_def)
  apply (auto simp: tcb_at_not_NULL tcb_at_max_word
                    tcb_at_not_NULL[THEN not_sym] tcb_at_max_word[THEN not_sym]
                 split: scheduler_action.split_asm)
  done

lemma getCurDomain_ccorres:
  "ccorres (op = \<circ> ucast) curDom_'
       \<top> UNIV hs curDomain (\<acute>curDom :== \<acute>ksCurDomain)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: curDomain_def simpler_gets_def
                        rf_sr_ksCurDomain)
  done

lemma possibleSwitchTo_ccorres:
  "ccorres dc xfdc
         (valid_queues and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and st_tcb_at' runnable' t
                       and valid_objs')
         ({s. target_' s = tcb_ptr_to_ctcb_ptr t}
             \<inter> {s. onSamePriority_' s = from_bool b} \<inter> UNIV) []
     (possibleSwitchTo t b)
     (Call possibleSwitchTo_'proc)"
  apply (cinit lift: target_' onSamePriority_')
   apply (rule ccorres_pre_getCurThread)
   apply (ctac(no_vcg) add: getCurDomain_ccorres)
     apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'=curPrio_'
                 in ccorres_split_nothrow_novcg)
         apply (rule_tac P="\<lambda>s. ksCurThread s = rv" in threadGet_vcg_corres_P)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: rf_sr_ksCurThread obj_at'_def projectKOs
                               typ_heap_simps' ctcb_relation_def)
        apply ceqv
       apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'=targetDom_'
                   in ccorres_split_nothrow_novcg)
           apply (rule threadGet_vcg_corres)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: rf_sr_ksCurThread obj_at'_def projectKOs
                                 typ_heap_simps' ctcb_relation_def)
          apply ceqv
         apply (rule_tac r'="\<lambda>rv rv'. rv' = ucast rv" and xf'=targetPrio_'
                      in ccorres_split_nothrow_novcg)
             apply (rule threadGet_vcg_corres)
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: rf_sr_ksCurThread obj_at'_def projectKOs
                                   typ_heap_simps' ctcb_relation_def)
            apply ceqv
           apply (rule_tac r'="cscheduler_action_relation"
                      and xf'="action___ptr_to_struct_tcb_C_'"
                       in ccorres_split_nothrow_novcg)
               apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: getSchedulerAction_def simpler_gets_def)
               apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
              apply ceqv
             apply (rule_tac R=\<top> in ccorres_cond)
               apply clarsimp
               apply (simp add: word_less_nat_alt unat_ucast_8_32 up_ucast_inj_eq)
              apply (ctac add: tcbSchedEnqueue_ccorres)
             apply (rule ccorres_split_nothrow_novcg_dc)
                apply (rule_tac R="weak_sch_act_wf rve" in ccorres_cond)
                  apply (clarsimp simp: from_bool_0)
                  apply (simp add: word_less_nat_alt unat_ucast_8_32 up_ucast_inj_eq)
                  apply (simp add: cscheduler_action_relation_def)
                  apply (clarsimp simp: max_word_def weak_sch_act_wf_def tcb_at_not_NULL
                                 split: scheduler_action.split_asm dest!: st_tcb_at')
                 apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
                 apply (rule allI, rule conseqPre, vcg)
                 apply (clarsimp simp: setSchedulerAction_def simpler_modify_def)
                 apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                       cscheduler_action_relation_def
                                       carch_state_relation_def cmachine_state_relation_def)
                apply (ctac add: tcbSchedEnqueue_ccorres)
               apply (simp only: scheduler_action_case_switch_to_if)
               apply (rule_tac R="weak_sch_act_wf rve" in ccorres_cond)
                 apply (clarsimp simp del: Collect_const)
                 apply (clarsimp simp: cscheduler_action_relation_def
                                       weak_sch_act_wf_def
                                       tcb_at_not_NULL tcb_at_max_word
                                split: scheduler_action.split_asm dest!: st_tcb_at' )
                apply (ctac add: rescheduleRequired_ccorres)
               apply (rule ccorres_return_Skip)
              apply (simp split del: split_if)
              apply wp
               apply (simp add: weak_sch_act_wf_def)
              apply (wp weak_sch_act_wf_lift_linear)
             apply (simp add: guard_is_UNIV_def)
            apply (wp static_imp_wp threadGet_wp | clarsimp simp: guard_is_UNIV_def)+
  apply (clarsimp simp: weak_sch_act_wf_def obj_at'_weakenE[OF _ TrueI]
                        valid_objs'_maxDomain valid_objs'_maxPriority)
  done

lemma attemptSwitchTo_ccorres [corres]:
  "ccorres dc xfdc (valid_queues and st_tcb_at' runnable' thread and valid_objs'
                       and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
                   (UNIV \<inter> \<lbrace>\<acute>target = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
           (attemptSwitchTo thread)
           (Call attemptSwitchTo_'proc)"
  apply (cinit lift: target_')
   apply (ctac add: possibleSwitchTo_ccorres)
  apply clarsimp
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
           apply (clarsimp simp: return_def if_1_0_0 split del: split_if)
           apply (clarsimp simp: from_bool_0 rf_sr_ksCurThread)
           apply (rule conjI)
            apply (clarsimp simp: st_tcb_at'_def)
            apply (drule (1) obj_at_cslift_tcb)
            apply (clarsimp simp: typ_heap_simps)
            apply (subgoal_tac "ksSchedulerAction \<sigma> = ResumeCurrentThread")
             apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def)
             apply (case_tac "tcbState ko", simp_all add: "StrictC'_thread_state_defs")[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def max_word_def
                                  tcb_at_not_NULL
                           split: scheduler_action.split_asm)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 cscheduler_action_relation_def)
          apply wp
        apply (simp add: getSchedulerAction_def)
       apply wp
     apply (simp add: isRunnable_def isBlocked_def)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply clarsimp
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def weak_sch_act_wf_def)
  done

lemma scheduleTCB_ccorres_valid_queues'_pre:
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
      apply (ctac add: rescheduleRequired_ccorres_valid_queues')
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
           apply (clarsimp simp: return_def if_1_0_0 split del: split_if)
           apply (clarsimp simp: from_bool_0 rf_sr_ksCurThread)
           apply (rule conjI)
            apply (clarsimp simp: st_tcb_at'_def)
            apply (drule (1) obj_at_cslift_tcb)
            apply (clarsimp simp: typ_heap_simps)
            apply (subgoal_tac "ksSchedulerAction \<sigma> = ResumeCurrentThread")
             apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def)
             apply (case_tac "tcbState ko", simp_all add: "StrictC'_thread_state_defs")[1]
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cscheduler_action_relation_def max_word_def
                                  tcb_at_not_NULL
                           split: scheduler_action.split_asm)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 cscheduler_action_relation_def)
          apply wp
        apply (simp add: getSchedulerAction_def)
       apply wp
     apply (simp add: isRunnable_def isBlocked_def)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply clarsimp
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def valid_queues'_def)
  done

lemmas scheduleTCB_ccorres_valid_queues'
    = scheduleTCB_ccorres_valid_queues'_pre[unfolded bind_assoc return_bind split_conv]

lemmas scheduleTCB_ccorres[corres]
    = scheduleTCB_ccorres'[unfolded bind_assoc return_bind split_conv]

lemma threadSet_weak_sch_act_wf_runnable': 
            "\<lbrace> \<lambda>s. (ksSchedulerAction s = SwitchToThread thread \<longrightarrow> runnable' st) \<and> weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>
               threadSet (tcbState_update (\<lambda>_. st)) thread
             \<lbrace> \<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  apply (simp add: weak_sch_act_wf_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift threadSet_st_tcb_at_state
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
    \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) []
         (setThreadState st thread) (Call setThreadState_'proc)"
   apply (cinit lift: tptr_' cong add: call_ignore_cong)
    apply (ctac (no_vcg) add: threadSet_tcbState_simple_corres)
   apply (ctac add: scheduleTCB_ccorres)
  apply (wp threadSet_weak_sch_act_wf_runnable' threadSet_valid_queues_and_runnable'
            threadSet_valid_objs')
  apply (clarsimp simp: weak_sch_act_wf_def valid_queues_def valid_tcb'_tcbState_update)
done

lemma threadSet_valid_queues'_and_not_runnable': "\<lbrace>tcb_at' thread and valid_queues' and (\<lambda>s. (\<not> runnable' st))\<rbrace>
                  threadSet (tcbState_update (\<lambda>_. st)) thread
               \<lbrace>\<lambda>rv. tcb_at' thread and st_tcb_at' (not runnable') thread and valid_queues' \<rbrace>"
  
  apply (wp threadSet_valid_queues' threadSet_tcbState_st_tcb_at')
  apply (clarsimp simp: pred_neg_def valid_queues'_def inQ_def)+
done

lemma setThreadState_ccorres_valid_queues':
   "ccorres dc xfdc 
   (\<lambda>s. tcb_at' thread s \<and> valid_queues' s \<and> \<not> runnable' st \<and> sch_act_simple s)
     ({s'. (\<forall>cl fl. cthread_state_relation_lifted st (cl\<lparr>tsType_CL := ts_' s' && mask 4\<rparr>, fl))}
    \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) []
         (setThreadState st thread) (Call setThreadState_'proc)"
   apply (cinit lift: tptr_' cong add: call_ignore_cong)
    apply (ctac (no_vcg) add: threadSet_tcbState_simple_corres)
   apply (ctac add: scheduleTCB_ccorres_valid_queues')
  apply (wp threadSet_valid_queues'_and_not_runnable')
  apply (clarsimp simp: weak_sch_act_wf_def valid_queues'_def)
done

lemma simp_list_case_return:
  "(case x of [] \<Rightarrow> return e | y # ys \<Rightarrow> return f) = return (if x = [] then e else f)"
  by (clarsimp split: list.splits)

lemma asyncIPCCancel_ccorres [corres]:
  "ccorres dc xfdc 
   (invs' and st_tcb_at' (op = (Structures_H.thread_state.BlockedOnAsyncEvent aep)) thread and sch_act_simple)
   (UNIV \<inter> {s. threadPtr_' s = tcb_ptr_to_ctcb_ptr thread} \<inter> {s. aepptr_' s = Ptr aep})
   [] (asyncIPCCancel thread aep) (Call asyncIPCCancel_'proc)"
  apply (cinit lift: threadPtr_' aepptr_' simp add: Let_def list_case_return cong add: call_ignore_cong)
   apply (unfold fun_app_def)   
   apply (simp only: simp_list_case_return return_bind ccorres_seq_skip) 
   apply (rule ccorres_pre_getAsyncEP)
   apply (rule ccorres_assert)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_rhs_assoc2)
     apply (ctac (no_vcg) add: asyncIPCCancel_ccorres_helper)
     apply (ctac add: setThreadState_ccorres_valid_queues')
    apply wp   
   apply (simp add: "StrictC'_thread_state_defs")
  apply (clarsimp simp: invs'_def valid_state'_def)
  done

lemma ko_at_valid_ep':
  "\<lbrakk>ko_at' ep p s; valid_objs' s\<rbrakk> \<Longrightarrow> valid_ep' ep s"
  apply (erule obj_atE')
  apply (erule (1) valid_objsE')
   apply (simp add: projectKOs valid_obj'_def)
   done
 
lemma cmap_relation_ep:
  "(s, s') \<in> rf_sr \<Longrightarrow> 
  cmap_relation (map_to_eps (ksPSpace s)) (cslift s') Ptr (cendpoint_relation (cslift s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

(* FIXME: MOVE *)
lemma ccorres_pre_getEndpoint [corres_pre]:
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
    apply (clarsimp simp add: getEndpoint_def exs_getObject objBits_simps)
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
                      \<and> blockingIPCEndpoint st = ep) thread \<sigma>;
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

lemma ep_ptr_set_queue_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. s \<Turnstile>\<^sub>c \<acute>epptr\<rbrace> Call ep_ptr_set_queue_'proc 
           {t. (\<exists>ep'. endpoint_lift ep' = 
  (endpoint_lift (the (cslift s (\<^bsup>s\<^esup>epptr))))\<lparr> epQueue_head_CL := ptr_val (head_C \<^bsup>s\<^esup>queue) && ~~ mask 4,
                                                      epQueue_tail_CL := ptr_val (end_C \<^bsup>s\<^esup>queue) && ~~ mask 4 \<rparr> \<and>
             (cslift t :: endpoint_C typ_heap) = (cslift s)(\<^bsup>s\<^esup>epptr \<mapsto> ep'))
             \<and> cslift_all_but_endpoint_C t s \<and> (hrs_htd \<^bsup>t\<^esup>t_hrs) = (hrs_htd \<^bsup>s\<^esup>t_hrs)}"
  apply vcg
  apply (auto simp: split_def h_t_valid_clift_Some_iff)
  done

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
    apply (cases ep', auto simp: restrict_map_def split: split_if_asm)
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
  shows "cmap_relation (map_to_eps (ksPSpace s(epptr \<mapsto> KOEndpoint ep')))
           (cslift t(Ptr epptr \<mapsto> endpoint)) Ptr (cendpoint_relation mp')"
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
  shows "cmap_relation (map_to_eps (ksPSpace s(epptr \<mapsto> KOEndpoint ep')))
           (cslift t(Ptr epptr \<mapsto> endpoint)) Ptr (cendpoint_relation mp')"
  using invs
  apply (intro cpspace_relation_ep_update_an_ep[OF koat cp rel mpeq])
    apply clarsimp+
  apply (clarsimp simp add: qs_def image_image simp del: imp_disjL)
  apply (rule ep_ep_disjoint[OF _ _ koat endpoint_not_idle_cases], auto)
  done

lemma cpspace_relation_ep_update_ep':
  fixes ep :: "endpoint" and ep' :: "endpoint"
    and epptr :: "word32" and s :: "kernel_state"
  defines "qs \<equiv> if (isSendEP ep' \<or> isRecvEP ep') then set (epQueue ep') else {}"
  defines "s' \<equiv> s\<lparr>ksPSpace := ksPSpace s(epptr \<mapsto> KOEndpoint ep')\<rparr>"
  assumes koat: "ko_at' ep epptr s"
  and       vp: "valid_pspace' s"
  and      cp: "cmap_relation (map_to_eps (ksPSpace s)) (cslift t) Ptr (cendpoint_relation mp)"
  and      srs: "sym_refs (state_refs_of' s')"
  and     rel: "cendpoint_relation mp' ep' endpoint"
  and    mpeq: "(mp' |` (- (tcb_ptr_to_ctcb_ptr ` qs))) = (mp |` (- (tcb_ptr_to_ctcb_ptr ` qs)))"
  shows "cmap_relation (map_to_eps (ksPSpace s(epptr \<mapsto> KOEndpoint ep')))
           (cslift t(Ptr epptr \<mapsto> endpoint)) Ptr (cendpoint_relation mp')"
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

lemma casync_endpoint_relation_ep_queue:
  assumes   srs: "sym_refs (state_refs_of' s)"
  and      koat: "ko_at' ep epptr s"
  and iswaiting: "(isSendEP ep \<or> isRecvEP ep)"
  and      mpeq: "(mp' |` (- (tcb_ptr_to_ctcb_ptr ` set (epQueue ep))))
  = (mp |` (- (tcb_ptr_to_ctcb_ptr ` set (epQueue ep))))"  
  and      koat': "ko_at' a aepptr s"
  shows "casync_endpoint_relation mp a b = casync_endpoint_relation mp' a b"
proof -  
  have rl: "\<And>p. \<lbrakk> p \<in> tcb_ptr_to_ctcb_ptr ` set (aepQueue a); isWaitingAEP a \<rbrakk>
    \<Longrightarrow> mp p = mp' p" using srs koat' koat iswaiting mpeq
    apply -
    apply (drule (4) aep_ep_disjoint)  
    apply (erule restrict_map_eqI [symmetric])
    apply (erule imageE)  
    apply (fastforce simp: disjoint_iff_not_equal inj_eq)
    done

  show ?thesis
    unfolding casync_endpoint_relation_def using rl
    apply (simp add: Let_def)
    apply (cases a)
       apply (simp add: isWaitingAEP_def cong: tcb_queue_relation'_cong)+
    done
qed

lemma epQueue_head_mask_4 [simp]:
  "epQueue_head_CL (endpoint_lift ko') && ~~ mask 4 = epQueue_head_CL (endpoint_lift ko')"
  unfolding endpoint_lift_def
  by (clarsimp simp: mask_def word_bw_assocs)

lemma epQueue_tail_mask_4 [simp]:
  "epQueue_tail_CL (endpoint_lift ko') && ~~ mask 4 = epQueue_tail_CL (endpoint_lift ko')"
  unfolding endpoint_lift_def
  by (clarsimp simp: mask_def word_bw_assocs)

(* Clag from asyncIPCCancel_ccorres_helper *)

lemma ipcCancel_ccorres_helper:
  "ccorres dc xfdc (invs' and 
         st_tcb_at' (\<lambda>st. (isBlockedOnSend st \<or> isBlockedOnReceive st)
                            \<and> blockingIPCEndpoint st = ep) thread
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
  apply (clarsimp split del: split_if simp del: comp_def)
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
  apply (clarsimp simp: typ_heap_simps cong: imp_cong split del: split_if simp del: comp_def)
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (intro impI conjI allI)
   -- "empty case"
  apply clarsimp
  apply (frule iffD1 [OF tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel]])
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
   apply clarsimp
    apply simp
  apply (simp add: setEndpoint_def split_def)
   apply (rule bexI [OF _ setObject_eq])
   apply (simp add: remove1_empty rf_sr_def cstate_relation_def Let_def cpspace_relation_def update_ep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
       -- "tcb relation"
       apply (erule ctcb_relation_null_queue_ptrs)
       apply (clarsimp simp: comp_def)
   -- "ep relation"
   apply (rule cpspace_relation_ep_update_ep, assumption+)
   apply (simp add: cendpoint_relation_def Let_def EPState_Idle_def)
  apply simp
  -- "aep relation"  
   apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
   apply simp
   apply (rule casync_endpoint_relation_ep_queue [OF invs_sym'], assumption+)
    apply simp
   apply (erule (1) map_to_ko_atI')
          apply (simp add: heap_to_page_data_def Let_def)
  -- "queue relation"
  apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def carch_globals_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
  -- "non empty case"
  apply clarsimp
  apply (frule tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel]) 
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
    apply clarsimp   
  apply (simp add: setEndpoint_def split_def)
   apply (rule bexI [OF _ setObject_eq])
      apply (frule (1) st_tcb_at_h_t_valid)
   apply (simp add: remove1_empty rf_sr_def cstate_relation_def Let_def cpspace_relation_def update_ep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
       -- "tcb relation"
       apply (erule ctcb_relation_null_queue_ptrs)
       apply (clarsimp simp: comp_def)
   -- "ep relation"       
   apply (rule cpspace_relation_ep_update_ep, assumption+)
   apply (simp add: cendpoint_relation_def Let_def isSendEP_def isRecvEP_def split: endpoint.splits split del: split_if)    
   -- "recv case"
   apply (clarsimp simp add: Ptr_ptr_val h_t_valid_clift_Some_iff  
     tcb_queue_relation'_next_mask_4 tcb_queue_relation'_prev_mask_4 cong: tcb_queue_relation'_cong)
    apply (intro impI conjI, simp_all)[1]
   -- "send case"   
   apply (clarsimp simp add: Ptr_ptr_val h_t_valid_clift_Some_iff  
     tcb_queue_relation'_next_mask_4 tcb_queue_relation'_prev_mask_4 cong: tcb_queue_relation'_cong)
   apply (intro impI conjI, simp_all)[1]
  apply simp
        -- "aep relation"       
  apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
  apply simp
  apply (rule casync_endpoint_relation_ep_queue [OF invs_sym'], assumption+)
  apply simp
  apply (erule (1) map_to_ko_atI')
  -- "queue relation"
  apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def carch_globals_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
   done

(* CLAG *)
lemma locateSlot_ccorres [corres]:
  assumes gl: "\<And>v s. globals (xfu v s) = globals s" -- "for state rel. preservation"
  and     fg: "\<And>v s. xf (xfu (\<lambda>_. v) s) = v"
  shows "ccorres (\<lambda>v v'. v' = Ptr v) xf \<top> {_. cnode = cnode' \<and> offset = offset'} hs (locateSlot cnode offset)
                              (Basic (\<lambda>s. xfu (\<lambda>_. Ptr (cnode' + offset' * of_nat (size_of TYPE(cte_C))) :: cte_C ptr) s))"
  unfolding locateSlot_def using gl fg  
  apply -
  apply (simp add: size_of_def split del: split_if)
  apply (rule ccorres_return)
  apply (rule conseqPre)
   apply vcg
  apply (clarsimp simp: fg objBits_simps)
  done

declare empty_fail_get[iff]

lemma getThreadState_ccorres_foo:
  "(\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c) \<Longrightarrow>
    ccorres r xf (\<lambda>s. \<forall>ts. st_tcb_at' (op = ts) t s \<longrightarrow> P ts s)
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

lemma ipcCancel_ccorres_reply_helper:
  assumes cteDeleteOne_ccorres:
  "\<And>w slot. ccorres dc xfdc
   (invs' and sch_act_simple and cte_wp_at' (\<lambda>ct. w = -1 \<or> cteCap ct = NullCap
        \<or> (\<forall>cap'. ccap_relation (cteCap ct) cap' \<longrightarrow> cap_get_tag cap' = w)) slot)
   ({s. gs_get_assn cteDeleteOne_'proc (ghost'state_' (globals s)) = w}
        \<inter> {s. slot_' s = Ptr slot}) []
   (cteDeleteOne slot) (Call cteDeleteOne_'proc)"
  shows

  "ccorres dc xfdc (invs' and st_tcb_at' (isBlockedOnReply or isBlockedOnFault) thread
                          and sch_act_simple) UNIV hs
     (do y \<leftarrow> threadSet (tcbFault_update Map.empty) thread;
         slot \<leftarrow> getThreadReplySlot thread;
         callerCap \<leftarrow> liftM (\<lambda>x. mdbNext (cteMDBNode x)) (getCTE slot);
         when (callerCap \<noteq> nullPointer)
          (do y \<leftarrow> stateAssert (capHasProperty callerCap isReplyCap) [];
              cteDeleteOne callerCap
           od)
      od)
     (CALL fault_null_fault_ptr_new(Ptr &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbFault_C'']));;
      (\<acute>slot :==
         cte_Ptr
          ((ptr_val (tcb_ptr_to_ctcb_ptr thread) && 0xFFFFFE00) +
           of_int (sint Kernel_C.tcbReply) * of_nat (size_of TYPE(cte_C)));;
       (Guard C_Guard {s. s \<Turnstile>\<^sub>c slot_' s}
         (\<acute>ret__unsigned_long :== CALL mdb_node_get_mdbNext(h_val (hrs_mem \<acute>t_hrs)
                  (mdb_Ptr &(\<acute>slot\<rightarrow>[''cteMDBNode_C'']))));;
        (\<acute>callerCap___ptr_to_struct_cte_C :== cte_Ptr \<acute>ret__unsigned_long;;
         IF \<acute>callerCap___ptr_to_struct_cte_C \<noteq> NULL THEN
           Basic (globals_update (ghost'state_'_update
              (ghost_assertion_data_set cteDeleteOne_'proc (ucast cap_reply_cap)
                (\<lambda>x. apsnd (apsnd x)))));;
           CALL cteDeleteOne(\<acute>callerCap___ptr_to_struct_cte_C)
         FI))))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_gen_asm, drule_tac thread=thread in ptr_val_tcb_ptr_mask2)
   apply (simp add: getThreadReplySlot_def del: Collect_const)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (rule_tac P=\<top> in threadSet_ccorres_lemma2)
       apply vcg
      apply (clarsimp simp: typ_heap_simps)
      apply (erule(2) rf_sr_tcb_update_no_queue, simp_all add: typ_heap_simps)[1]
       apply (rule ball_tcb_cte_casesI, simp_all)[1]
      apply (clarsimp simp: ctcb_relation_def fault_lift_null_fault
                            cfault_rel_def cthread_state_relation_def)
      apply (case_tac "tcbState tcb", simp_all add: is_cap_fault_def)[1]
     apply ctac
       apply (simp (no_asm) only: liftM_def bind_assoc return_bind del: Collect_const)
       apply (rule ccorres_pre_getCTE)
       apply (rule_tac xf'=ret__unsigned_long_' and val="mdbNext (cteMDBNode x)"
                      and R="cte_wp_at' (op = x) rv and invs'"
                       in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
          apply vcg
          apply (clarsimp simp: cte_wp_at_ctes_of)
          apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
          apply (clarsimp simp: typ_heap_simps)
          apply (clarsimp simp: ccte_relation_def option_map_Some_eq2)
         apply ceqv
        apply csymbr
        apply (rule ccorres_Cond_rhs)
         apply (simp add: nullPointer_def when_def)
         apply (rule ccorres_symb_exec_l[OF _ _ _ empty_fail_stateAssert])
           apply (simp only: dc_def[symmetric])
           apply (rule ccorres_symb_exec_r)
             apply (ctac add: cteDeleteOne_ccorres[where w1="scast cap_reply_cap"])
            apply vcg
           apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def
              gs_set_assn_Delete_cstate_relation[unfolded o_def])
          apply (wp | simp)+
        apply (simp add: when_def nullPointer_def dc_def[symmetric])
        apply (rule ccorres_return_Skip)
       apply (simp add: guard_is_UNIV_def ghost_assertion_data_get_def
                        ghost_assertion_data_set_def cap_tag_defs)
      apply (simp add: locateSlot_conv, wp)
     apply vcg
    apply (rule_tac Q="\<lambda>rv. invs' and sch_act_simple" in hoare_post_imp)
     apply (clarsimp simp: cte_wp_at_ctes_of capHasProperty_def cap_get_tag_isCap ucast_id)
    apply (wp hoare_vcg_all_lift threadSet_invs_trivial
               | wp_once hoare_drop_imps | simp)+
   apply (clarsimp simp: guard_is_UNIV_def tcbReplySlot_def
                         Kernel_C.tcbReply_def mask_def)
  apply (fastforce simp: st_tcb_at_tcb_at' inQ_def tcb_aligned'[OF st_tcb_at_tcb_at'])
  done

lemma ipcCancel_ccorres1:
  assumes cteDeleteOne_ccorres:
  "\<And>w slot. ccorres dc xfdc
   (invs' and sch_act_simple and cte_wp_at' (\<lambda>ct. w = -1 \<or> cteCap ct = NullCap
        \<or> (\<forall>cap'. ccap_relation (cteCap ct) cap' \<longrightarrow> cap_get_tag cap' = w)) slot)
   ({s. gs_get_assn cteDeleteOne_'proc (ghost'state_' (globals s)) = w}
        \<inter> {s. slot_' s = Ptr slot}) []
   (cteDeleteOne slot) (Call cteDeleteOne_'proc)"
  shows
  "ccorres dc xfdc (tcb_at' thread and invs' and sch_act_simple)
                   (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr thread}) []
          (ipcCancel thread) (Call ipcCancel_'proc)"
  apply (cinit lift: tptr_' simp: Let_def cong: call_ignore_cong)
   apply (rule ccorres_move_c_guard_tcb)
   apply csymbr
   apply (rule getThreadState_ccorres_foo)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=ret__unsigned_long_' in ccorres_abstract, ceqv)
     apply (rule_tac P="rv' = thread_state_to_tsType rv" in ccorres_gen_asm2)
     apply wpc
            -- "BlockedOnReceive"
            apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs cong: call_ignore_cong)
            apply (fold dc_def)
            apply (rule ccorres_rhs_assoc)+
            apply csymbr
            apply csymbr
            apply (rule ccorres_pre_getEndpoint)
            apply (rule ccorres_assert)
             apply (rule ccorres_symb_exec_r) -- "ptr_get lemmas don't work so well :("
               apply (rule ccorres_symb_exec_r)
                 apply (simp only: fun_app_def simp_list_case_return 
                                   return_bind ccorres_seq_skip)
                 apply (rule ccorres_rhs_assoc2)
                 apply (rule ccorres_rhs_assoc2)
                 apply (rule ccorres_rhs_assoc2)
                 apply (ctac (no_vcg) add: ipcCancel_ccorres_helper)
                   apply (ctac add: setThreadState_ccorres_valid_queues')
                  apply wp
                 apply (simp add: "StrictC'_thread_state_defs")
                apply vcg
               apply (rule conseqPre, vcg)
               apply clarsimp
              apply clarsimp
              apply (rule conseqPre, vcg)
              apply (rule subset_refl)
             apply (rule conseqPre, vcg)
             apply clarsimp
           -- "BlockedOnReply case"
           apply (simp add: "StrictC'_thread_state_defs" ccorres_cond_iffs
                            Collect_False Collect_True word_sle_def
                      cong: call_ignore_cong del: Collect_const)
           apply (fold dc_def)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply (unfold comp_def)[1]
           apply (rule ccorres_Guard ccorres_Guard_Seq)+
           apply (clarsimp simp del: dc_simp simp: of_int_sint)
           apply ccorres_remove_UNIV_guard
           apply (rule ipcCancel_ccorres_reply_helper [OF cteDeleteOne_ccorres, unfolded dc_def])
          -- "BlockedOnAsyncEvent"
          apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs dc_def [symmetric] cong: call_ignore_cong)
          apply (rule ccorres_symb_exec_r)
            apply (ctac (no_vcg))
           apply clarsimp
           apply (rule conseqPre, vcg)
           apply (rule subset_refl)
          apply (rule conseqPre, vcg)
          apply clarsimp
         -- "Running, Inactive, and Idle"
         apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs dc_def [symmetric] cong: call_ignore_cong, 
                rule ccorres_return_Skip)+
      -- "BlockedOnSend"
      apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs dc_def [symmetric] cong: call_ignore_cong)
      -- "clag"
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply (rule ccorres_pre_getEndpoint)
      apply (rule ccorres_assert)
      apply (rule ccorres_symb_exec_r) -- "ptr_get lemmas don't work so well :("
       apply (rule ccorres_symb_exec_r)
       apply (simp only: fun_app_def simp_list_case_return return_bind ccorres_seq_skip)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (ctac (no_vcg) add: ipcCancel_ccorres_helper)
       apply (ctac add: setThreadState_ccorres_valid_queues')
       apply wp
       apply (simp add: "StrictC'_thread_state_defs")
             apply clarsimp
             apply (rule conseqPre, vcg, rule subset_refl)
            apply (rule conseqPre, vcg)
            apply clarsimp
           apply clarsimp
           apply (rule conseqPre, vcg, rule subset_refl)
         apply (rule conseqPre, vcg)
         apply clarsimp
     -- "Restart"
     apply (simp add: word_sle_def "StrictC'_thread_state_defs" ccorres_cond_iffs dc_def [symmetric] cong: call_ignore_cong, 
            rule ccorres_return_Skip)
    -- "Post wp proofs"
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
  apply (rule conjI)
   apply (auto simp: obj_at'_def projectKOs st_tcb_at'_def
                     isTS_defs cte_wp_at_ctes_of
                     cthread_state_relation_def)[1]
  apply clarsimp
  apply (case_tac ts,
         auto simp: isTS_defs cthread_state_relation_def typ_heap_simps)
  done

end
end

