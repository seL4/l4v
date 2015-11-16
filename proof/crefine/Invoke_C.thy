(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Invoke_C
imports Recycle_C "../../lib/clib/MonadicRewrite_C"
begin

context kernel_m
begin

(************************************************************************)
(*                                                                      *)
(* decodeDomainInvocation  **********************************************)
(*                                                                      *)
(************************************************************************)

lemma slotcap_in_mem_ThreadCap:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); (s, s') \<in> rf_sr \<rbrakk>
       \<Longrightarrow> \<exists>v. cslift s' (cte_Ptr slot) = Some v
           \<and> (cap_get_tag (cte_C.cap_C v) = scast cap_thread_cap)
              = (isThreadCap cap)
           \<and> (isThreadCap cap
                  \<longrightarrow> ccap_relation cap (cte_C.cap_C v))"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
  apply (clarsimp dest!: ccte_relation_ccap_relation)
  apply (simp add: cap_get_tag_isCap)
  done

lemma cap_case_ThreadCap2:
  "(case cap of (ThreadCap ptr) \<Rightarrow> f ptr | _ \<Rightarrow> g)
   = (if isThreadCap cap
      then f (capTCBPtr cap)
      else g)"
  by (simp add: isCap_simps
         split: capability.split)

lemma setDomain_ccorres:
  "ccorres dc xfdc
      (invs' and tcb_at' t and sch_act_simple
             and (\<lambda>s. d \<le> maxDomain))
      (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr t} \<inter> {s. dom_' s = ucast d})
      [] (setDomain t d) (Call setDomain_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: tptr_' dom_')
   apply (rule ccorres_pre_getCurThread)
   apply (ctac(no_vcg) add: tcbSchedDequeue_ccorres)
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule ccorres_split_nothrow_novcg_dc)
       apply (rule threadSet_ccorres_lemma2[where P=\<top>])
        apply vcg
       apply clarsimp
       apply (erule(1) rf_sr_tcb_update_no_queue2,
              (simp add: typ_heap_simps)+, simp_all)[1]
         apply (subst heap_update_field_hrs | fastforce intro: typ_heap_simps)+
        apply (rule ball_tcb_cte_casesI, simp+)
       apply (simp add: ctcb_relation_def)
      apply (ctac(no_vcg) add: isRunnable_ccorres)
       apply (rule ccorres_split_nothrow_novcg_dc)
          apply (simp add: when_def to_bool_def del: Collect_const)
          apply (rule ccorres_cond2[where R=\<top>], simp add: Collect_const_mem)
           apply (ctac add: tcbSchedEnqueue_ccorres)
          apply (rule ccorres_return_Skip)
         apply (simp add: when_def to_bool_def)
         apply (rule_tac R="\<lambda>s. rv = ksCurThread s"
                    in ccorres_cond2)
           apply (clarsimp simp: rf_sr_ksCurThread)
          apply (ctac add: rescheduleRequired_ccorres[unfolded dc_def])
         apply (rule ccorres_return_Skip')
        apply simp
        apply (wp hoare_drop_imps weak_sch_act_wf_lift_linear)
       apply (simp add: guard_is_UNIV_def)
      apply simp
      apply wp
     apply (rule_tac Q="\<lambda>_. all_invs_but_sch_extra and tcb_at' t and sch_act_simple
                        and (\<lambda>s. rv = ksCurThread s)" in hoare_strengthen_post)
      apply (wp_trace threadSet_all_invs_but_sch_extra)
     apply (clarsimp simp:valid_pspace_valid_objs' st_tcb_at_def[symmetric]
       sch_act_simple_def st_tcb_at'_def o_def weak_sch_act_wf_def split:if_splits)
    apply (simp add: guard_is_UNIV_def)
   apply (rule_tac Q="\<lambda>_. invs' and tcb_at' t and sch_act_simple
      and (\<lambda>s. rv = ksCurThread s \<and> (\<forall>p. t \<notin> set (ksReadyQueues s p)))" in hoare_strengthen_post)
    apply (wp weak_sch_act_wf_lift_linear tcbSchedDequeue_not_queued
              tcbSchedDequeue_not_in_queue hoare_vcg_imp_lift hoare_vcg_all_lift)
   apply (clarsimp simp:invs'_def valid_pspace'_def valid_state'_def)
  apply (fastforce simp: valid_tcb'_def tcb_cte_cases_def
                         invs'_def valid_state'_def valid_pspace'_def)
  done

lemma active_runnable':
  "active' state \<Longrightarrow> runnable' state"
  by (fastforce simp: runnable'_def)

lemma decodeDomainInvocation_ccorres:
  notes Collect_const[simp del]
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread)
              and sch_act_simple and ct_active'
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v).
                              ex_nonz_cap_to' y s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v)
              and sysargs_rel args buffer)
       (UNIV
             \<inter> {s. unat (length_' s) = length args}
             \<inter> {s. extraCaps_' s = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. label_' s = lab}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeDomainInvocation lab args extraCaps
           >>= invocationCatch thread isBlocking isCall (uncurry InvokeDomain))
  (Call decodeDomainInvocation_'proc)"
  apply (cinit' lift: length_' extraCaps_' call_' label_' buffer_'
                simp: decodeDomainInvocation_def list_case_If2 whenE_def)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: invocation_eq_use_types)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind invocationCatch_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: unat_gt_0[symmetric] del:)
   apply (rule ccorres_add_return)
   apply (rule ccorres_rhs_assoc)+
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (simp add: numDomains_def hd_conv_nth word_le_nat_alt)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: throwError_bind invocationCatch_def numDomains_def
                       hd_conv_nth word_le_nat_alt
                 cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (simp add: null_def excaps_map_def)
     apply (rule ccorres_Guard_Seq)+
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: throwError_bind invocationCatch_def
                       interpret_excaps_test_null
                 cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (simp add: interpret_excaps_test_null hd_conv_nth cap_case_ThreadCap2)
     apply (rule ccorres_add_return)
     apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_thread_cap)
                                          = (isThreadCap rv))
                                  \<and> (cap_get_tag rv' = scast cap_thread_cap \<longrightarrow> ccap_relation rv rv'))
                                (fst (extraCaps ! 0))"
                and xf'=tcap_' in ccorres_split_nothrow)
         apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
         apply (drule(1) slotcap_in_mem_ThreadCap)
         apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
         apply (clarsimp simp: typ_heap_simps' mask_def word_sless_def word_sle_def)
        apply ceqv
       apply csymbr
       apply clarsimp
       apply (rule ccorres_Cond_rhs_Seq)
        apply (simp add: Collect_const)
        apply (simp add: throwError_bind invocationCatch_def
                   cong: StateSpace.state.fold_congs globals.fold_congs)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (simp add: Collect_const returnOk_def uncurry_def)
       apply (simp (no_asm) add: ccorres_invocationCatch_Inr split_def
                                 performInvocation_def liftE_bindE bind_assoc)
       apply (ctac add: setThreadState_ccorres)
         apply csymbr
         apply (ctac add: setDomain_ccorres)
           apply (rule ccorres_alternative2)
           apply (ctac add: ccorres_return_CE)
          apply wp
         apply (vcg exspec=setDomain_modifies)
        apply (wp sts_invs_minor')
       apply (vcg exspec=setThreadState_modifies)
      apply wp
      apply simp
     apply clarsimp
     apply vcg
    apply wp
    apply simp
   apply clarsimp
   apply (vcg exspec=getSyscallArg_modifies)

  apply (clarsimp simp: valid_tcb_state'_def invs_valid_queues' invs_valid_objs'
                        invs_queues invs_sch_act_wf' ct_in_state'_def pred_tcb_at'
                        rf_sr_ksCurThread word_sle_def word_sless_def sysargs_rel_to_n
                        mask_eq_iff_w2p mask_eq_iff_w2p word_size "StrictC'_thread_state_defs"
                        maxDomain_def numDomains_def)
  apply (rule conjI)
   apply (clarsimp simp: linorder_not_le isCap_simps)
   apply (rule conjI, clarsimp simp: unat32_eq_of_nat)
   apply clarsimp
   apply (drule_tac x="extraCaps ! 0" and P="\<lambda>v. valid_cap' (fst v) s" in bspec)
    apply (clarsimp simp: nth_mem interpret_excaps_test_null excaps_map_def)
   apply (clarsimp simp: valid_cap_simps' pred_tcb'_weakenE active_runnable')
   apply (rule conjI)
    apply (fastforce simp: tcb_st_refs_of'_def elim:pred_tcb'_weakenE)
   apply (simp add: word_le_nat_alt unat_ucast)
  apply (clarsimp simp: ucast_ucast_len word_less_nat_alt
                        ccap_relation_def cap_to_H_simps cap_thread_cap_lift)
  done

(************************************************************************)
(*                                                                      *)
(* invokeCNodeDelete_ccorres ********************************************)
(*                                                                      *)
(************************************************************************)

lemma invokeCNodeDelete_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (\<lambda>s. invs' s \<and> sch_act_simple s)
       (UNIV \<inter> {s. destSlot_' s = Ptr destSlot}) []
       (invokeCNode (Delete destSlot)) 
  (Call invokeCNodeDelete_'proc)"
  apply (cinit lift: destSlot_' simp del: return_bind cong:call_ignore_cong)
   apply (rule ccorres_trim_returnE, simp, simp)
   apply (rule ccorres_callE)
       apply (rule cteDelete_ccorres[simplified])
      apply (simp add: from_bool_def true_def)+
done



(************************************************************************)
(*                                                                      *)
(* invokeCNodeRevoke_ccorres ********************************************)
(*                                                                      *)
(************************************************************************)
lemma invokeCNodeRevoke_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
         (invs' and sch_act_simple)
         (UNIV \<inter> {s. destSlot_' s = cte_Ptr destSlot}) []
       (invokeCNode (Revoke destSlot)) 
  (Call invokeCNodeRevoke_'proc)"
  apply (cinit lift: destSlot_' simp del: return_bind cong:call_ignore_cong)
   apply (rule ccorres_trim_returnE, simp, simp)
   apply (rule ccorres_callE)
       apply (rule cteRevoke_ccorres[simplified])
      apply (simp add: from_bool_def true_def)+
done


(************************************************************************)
(*                                                                      *)
(* invokeCNodeRecycle_ccorres ********************************************)
(*                                                                      *)
(************************************************************************)

lemma invokeCNodeRecycle_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and sch_act_simple) (UNIV \<inter> {s. destSlot_' s = cte_Ptr destSlot}) []
     (invokeCNode (Recycle destSlot)) 
     (Call invokeCNodeRecycle_'proc)"
  apply (cinit lift: destSlot_' simp del: return_bind cong:call_ignore_cong)
   apply (rule ccorres_trim_returnE, simp, simp)
   apply (rule ccorres_callE)
       apply (rule cteRecycle_ccorres[simplified])
      apply (simp add: from_bool_def true_def)+
done



(************************************************************************)
(*                                                                      *)
(* invokeCNodeInsert_ccorres ********************************************)
(*                                                                      *)
(************************************************************************)

lemma invokeCNodeInsert_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (cte_wp_at' (\<lambda>scte. capMasterCap (cteCap scte) = capMasterCap cap) src
                     and valid_mdb' and pspace_aligned' and valid_objs' and valid_cap' cap)
       (UNIV \<inter> {s. destSlot_' s = Ptr dest} \<inter> 
               {s. srcSlot_' s = Ptr src} \<inter>
               {s. ccap_relation cap (cap_' s)}) [] 
       (invokeCNode (Insert cap src dest)) 
  (Call invokeCNodeInsert_'proc)"
  apply (cinit lift: destSlot_' srcSlot_' cap_' simp del: return_bind cong:call_ignore_cong)
  apply (simp add: liftE_def) 
  apply (ctac (no_vcg) add: cteInsert_ccorres) 
  apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
  apply (rule allI, rule conseqPre,vcg) apply clarsimp  apply (simp add: return_def)
  apply wp
  apply (clarsimp simp: cte_wp_at_ctes_of)
done




(************************************************************************)
(*                                                                      *)
(* invokeCNodeMove_ccorres  *********************************************)
(*                                                                      *)
(************************************************************************)

lemma invokeCNodeMove_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (valid_mdb' and pspace_aligned' ) 
       (UNIV \<inter> {s. destSlot_' s = Ptr dest} \<inter> 
               {s. srcSlot_' s = Ptr src} \<inter>
               {s. ccap_relation cap (cap_' s)}) [] 
       (invokeCNode (Move cap src dest)) 
  (Call invokeCNodeMove_'proc)"
  apply (cinit lift: destSlot_' srcSlot_' cap_' simp del: return_bind cong:call_ignore_cong)
  apply (simp add: liftE_def) 
  apply (ctac (no_vcg) add: cteMove_ccorres) 
  apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
  apply (rule allI, rule conseqPre,vcg) apply clarsimp  apply (simp add: return_def)
  apply wp
  apply clarsimp
done






(************************************************************************)
(*                                                                      *)
(* invokeCNodeRotate_ccorres  *******************************************)
(*                                                                      *)
(************************************************************************)



lemma invokeCNodeRotate_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (\<lambda>s. cte_at' slot1 s \<and> cte_at' slot2 s \<and> slot1 \<noteq> slot2
            \<and> valid_pspace' s \<and> valid_cap' cap2 s
            \<and> cte_wp_at' (\<lambda>c. weak_derived' cap2 (cteCap c)) slot2 s
            \<and> cte_wp_at' (\<lambda>c. isUntypedCap (cteCap c) \<longrightarrow> (cteCap c) = cap2) slot2 s
            \<and> cte_wp_at' (\<lambda>c. cteCap c \<noteq> NullCap) slot2 s
            \<and> (slot1 \<noteq> slot3 \<longrightarrow> cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot3 s))
       (UNIV \<inter> {s. slot1_' s = Ptr slot1} \<inter> 
               {s. slot2_' s = Ptr slot2} \<inter> 
               {s. slot3_' s = Ptr slot3} \<inter>
               {s. ccap_relation cap1 (cap1_' s)} \<inter>
               {s. ccap_relation cap2 (cap2_' s)}) [] 
       (invokeCNode (Rotate cap1 cap2 slot1 slot2 slot3)) 
  (Call invokeCNodeRotate_'proc)"
  apply (cinit lift: slot1_' slot2_' slot3_' cap1_' cap2_' simp del: return_bind cong:call_ignore_cong)
   apply (simp split del: split_if del: Collect_const)
   apply (simp only: liftE_def)
   apply (rule_tac r'="dc" and xf'="xfdc" in ccorres_split_nothrow_novcg)
       apply (rule ccorres_cond [where R = \<top>])
         apply (clarsimp simp: Collect_const_mem)
        apply (ctac (no_vcg) add: cteSwap_ccorres)
       apply (ctac (no_vcg) add: cteMove_ccorres)
        apply (simp only: K_bind_def)
        apply (ctac (no_vcg) add: cteMove_ccorres)
       apply (rule hoare_strengthen_post)
        apply (rule cteMove_valid_pspace')
       apply (simp add: valid_pspace'_def)
      apply ceqv
     apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre,vcg)
     apply clarsimp
     apply (simp add: return_def) 
    apply wp
   apply (simp add: guard_is_UNIV_def dc_def xfdc_def)
  apply (clarsimp simp: valid_pspace'_def)
  apply (rule conjI, clarsimp)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (clarsimp simp: weak_derived'_def isCap_simps)
  done



(************************************************************************)
(*                                                                      *)
(* invokeCNodeSaveCaller  ***********************************************)
(*                                                                      *)
(************************************************************************)

lemma invokeCNodeSaveCaller_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (valid_mdb' and pspace_aligned' and cur_tcb')
       (UNIV \<inter> {s. destSlot_' s = Ptr destSlot}) [] 
       (invokeCNode (SaveCaller destSlot)) 
  (Call invokeCNodeSaveCaller_'proc)" 
  apply (cinit lift: destSlot_'  simp del: return_bind cong:call_ignore_cong)
   apply (simp add: Collect_True split del: split_if  del: Collect_const cong:call_ignore_cong)
   apply (simp only: liftE_def)
   apply (rule ccorres_Guard_Seq)+
   apply (simp only: bind_assoc)
   apply (rule ccorres_pre_getCurThread)

   apply (simp only: getThreadCallerSlot_def locateSlot_conv)

   apply (rule_tac P="\<lambda>s. rv=ksCurThread s \<and> is_aligned rv 9" and r'="\<lambda> a c. c = Ptr a"
                   and xf'="srcSlot_'" and P'=UNIV in ccorres_split_nothrow)

       apply (rule ccorres_return)
       apply vcg
       apply clarsimp
       apply (simp add: cte_level_bits_def size_of_def of_nat_def)
       apply (simp add: rf_sr_def cstate_relation_def Kernel_C.tcbCaller_def tcbCallerSlot_def)
       apply (clarsimp simp: Let_def)
       apply (subst ptr_val_tcb_ptr_mask2 [simplified mask_def, simplified]) 
        apply assumption
       apply simp
      apply ceqv

     apply (simp del: Collect_const cong: call_ignore_cong)
     apply (rule ccorres_getSlotCap_cte_at)
     apply (rule ccorres_move_c_guard_cte)
     apply (ctac (no_vcg))
       apply csymbr
       apply (wpc, simp_all add: cap_get_tag_isCap isCap_simps
                                 Collect_False Collect_True
                            del: Collect_const)[1]
                 apply (rule ccorres_fail)+
                  -- "NullCap case"
                apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV]) 
                apply (rule allI, rule conseqPre, vcg) 
                apply clarsimp 
                apply (simp add: return_def)
               apply (rule ccorres_fail)+
          -- "ReplyCap case"
          apply (rule ccorres_rhs_assoc)
          apply csymbr
          apply (frule cap_get_tag_isCap_unfolded_H_cap)
          apply (simp add: cap_get_tag_ReplyCap)
          apply (case_tac " (capReplyMaster_CL (cap_reply_cap_lift cap))=0", simp_all add: to_bool_def)[1]
           apply (ctac (no_vcg) add: cteMove_ccorres)
            apply (rule ccorres_return_CE [unfolded returnOk_def,simplified], simp+)[1]
           apply wp
          apply (rule ccorres_fail')
         apply (rule ccorres_fail)+
      apply (wp getSlotCap_wp)
     apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
    apply wp
   apply vcg
  apply (clarsimp simp: word_sle_def cte_wp_at_ctes_of
                        tcb_aligned' cur_tcb'_def
                        tcb_cnode_index_defs ptr_add_assertion_positive)
  apply (frule(1) rf_sr_tcb_ctes_array_assertion2[rotated])
  apply (simp add: tcb_cnode_index_defs array_assertion_shrink_right
                   rf_sr_ksCurThread)
  done





(************************************************************************)
(*                                                                      *)
(* decodeCNodeInvocation  ***********************************************)
(*                                                                      *)
(************************************************************************)

lemma ccorres_basic_srnoop2:
  "\<lbrakk> \<And>s. globals (g s) = globals s;
     ccorres_underlying rf_sr Gamm r xf arrel axf G (g ` G') hs a c \<rbrakk>
    \<Longrightarrow> ccorres_underlying rf_sr Gamm r xf arrel axf G G'
           hs a (Basic g ;; c)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_r)
     apply assumption
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply simp
  done

lemma updateCapData_spec2:
  "\<forall>cap preserve newData. \<Gamma> \<turnstile> \<lbrace> ccap_relation cap \<acute>cap \<and> preserve = to_bool (\<acute>preserve) \<and> newData = \<acute>newData\<rbrace>
  Call updateCapData_'proc
  \<lbrace>  ccap_relation (updateCapData preserve newData cap) \<acute>ret__struct_cap_C \<rbrace>"
  by (simp add: updateCapData_spec)

lemma mdbRevocable_CL_cte_to_H:
  "(mdbRevocable_CL (cteMDBNode_CL clcte) = 0)
     = (\<not> mdbRevocable (cteMDBNode (cte_to_H clcte)))"
  by (simp add: cte_to_H_def mdb_node_to_H_def to_bool_def)

lemma ccorres_add_specific_return:
  "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs
        (do v \<leftarrow> return val; f v od) c
   \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs (f val) c"
  by simp

(* FIXME: also in Tcb_C *)
lemma ccorres_subgoal_tailE:
  "\<lbrakk> ccorres rvr xf Q Q' hs (b ()) d;
      ccorres rvr xf Q Q' hs (b ()) d \<Longrightarrow> ccorres rvr xf P P' hs (a >>=E b) (c ;; d) \<rbrakk>
        \<Longrightarrow> ccorres rvr xf P P' hs (a >>=E b) (c ;; d)"
  by simp

lemma label_in_CNodeInv_ranges:
  "(label < scast Kernel_C.CNodeRevoke \<or> scast Kernel_C.CNodeSaveCaller < label)
      = (invocation_type label \<notin> set [CNodeRevoke .e. CNodeSaveCaller])"
  "(scast Kernel_C.CNodeCopy \<le> label \<and> label \<le> scast Kernel_C.CNodeMutate)
      = (invocation_type label \<in> set [CNodeCopy .e. CNodeMutate])"
  apply (simp_all add: upto_enum_def fromEnum_def enum_invocation_label
                  del: upt.simps)
  apply (simp_all add: atLeastLessThanSuc)
  apply (simp_all add: toEnum_def enum_invocation_label)
  apply (simp_all add: invocation_eq_use_types[symmetric] invocation_label_defs)
  apply (simp_all add: unat_arith_simps)
  apply arith+
  done

lemma cnode_invok_case_cleanup2:
  "i \<in> set [CNodeCopy .e. CNodeMutate] \<Longrightarrow>
     (case i of CNodeRevoke \<Rightarrow> P | CNodeDelete \<Rightarrow> Q | CNodeRecycle \<Rightarrow> R
              | CNodeRotate \<Rightarrow> S | CNodeSaveCaller \<Rightarrow> T | _ \<Rightarrow> U) = U"
  apply (rule cnode_invok_case_cleanup)
  apply (simp add: upto_enum_def fromEnum_def toEnum_def
                   enum_invocation_label)
  apply auto
  done

lemma Arch_hasRecycleRights_spec:
  "\<forall>cap. \<Gamma> \<turnstile> \<lbrace> ccap_relation (ArchObjectCap cap) \<acute>cap \<rbrace> 
             Call Arch_hasRecycleRights_'proc 
             \<lbrace> \<acute>ret__unsigned_long = from_bool (ArchRetypeDecls_H.hasRecycleRights cap) \<rbrace>"
  apply vcg
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule cap_get_tag_PageCap_frame [THEN iffD1], assumption)
   apply clarsimp
   apply (drule ccap_relation_PageCap_generics)
   apply (auto simp: ArchRetype_H.hasRecycleRights_def 
                         vmrights_to_H_def true_def false_def 
                         vmrights_defs
                   dest: less_4_cases
                   split: if_splits)[1]
  apply (rule conjI)
   apply clarsimp
   apply (frule cap_get_tag_PageCap_small_frame [THEN iffD1], assumption)
   apply clarsimp
   apply (drule ccap_relation_PageCap_generics)
   apply (auto simp: ArchRetype_H.hasRecycleRights_def 
                         vmrights_to_H_def true_def false_def 
                         vmrights_defs
                   dest: less_4_cases
                   split: if_splits)[1]
  apply (case_tac cap,
         auto simp: ArchRetype_H.hasRecycleRights_def
              dest: ccap_relation_frame_tags)[1]
  done

lemma hasRecycleRights_spec:
  "\<forall>cap. \<Gamma> \<turnstile> \<lbrace> ccap_relation cap \<acute>cap \<rbrace> 
             Call hasRecycleRights_'proc 
             \<lbrace> \<acute>ret__unsigned_long = from_bool (hasRecycleRights cap) \<rbrace>"
  apply vcg
  apply (clarsimp simp: if_1_0_0)
  apply (rule conjI)
   -- "DomainCap"
   apply clarsimp
   apply (drule (1) cap_get_tag_to_H)
   apply (clarsimp simp: hasRecycleRights_def)
  apply (rule conjI)
   -- "NullCap"
   apply clarsimp
   apply (drule cap_get_tag_to_H, simp)
   apply (clarsimp simp: hasRecycleRights_def)
  apply (rule impI)
  apply (rule conjI)
   -- "EP"
   apply clarsimp 
   apply (drule sym, drule (1) cap_get_tag_to_H)
   apply (clarsimp simp: hasRecycleRights_def to_bool_def 
                         true_def false_def 
                   split: split_if bool.splits)
  apply (rule impI)
  apply (rule conjI)
   -- "NTFN"
   apply clarsimp 
   apply (drule sym, drule (1) cap_get_tag_to_H)
   apply (clarsimp simp: hasRecycleRights_def to_bool_def 
                         true_def false_def 
                   split: split_if bool.splits)
  apply (rule impI)
  apply (rule conjI)
   -- "Arch"
   apply (clarsimp simp: from_bool_neq_0)
   apply (frule (1) cap_get_tag_isCap_ArchObject2_worker [rotated])
    apply (rule refl)
   apply (clarsimp simp: isCap_simps hasRecycleRights_def)
   apply fastforce
  -- "rest"
  apply (case_tac cap,
         auto simp: cap_get_tag_isCap_unfolded_H_cap cap_tag_defs  
                     from_bool_def false_def true_def hasRecycleRights_def
              dest: cap_get_tag_isArchCap_unfolded_H_cap
              split: capability.splits bool.splits)[1]
  done

lemma updateCapData_Untyped:
  "isUntypedCap a
         \<Longrightarrow> updateCapData b c a = a"
 by (clarsimp simp:isCap_simps updateCapData_def)

lemma ctes_of_valid_strengthen:
  "(invs' s \<and> ctes_of s p = Some cte) \<longrightarrow> valid_cap' (cteCap cte) s"
  apply (case_tac cte)
  apply clarsimp
  apply (erule ctes_of_valid_cap')
  apply fastforce
  done

lemma decodeCNodeInvocation_ccorres:
  shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) 
              and sch_act_simple and ct_active'
              and valid_cap' cp
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v).
                              ex_nonz_cap_to' y s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v)
              and sysargs_rel args buffer)
       (UNIV 
             \<inter> {s. unat (length_' s) = length args}
             \<inter> {s. ccap_relation cp (cap_' s)} 
             \<inter> {s. extraCaps_' s = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. label_' s = lab} 
             \<inter> {s. buffer_' s = option_to_ptr buffer}) [] 
       (decodeCNodeInvocation lab args cp (map fst extraCaps)
           >>= invocationCatch thread isBlocking isCall InvokeCNode) 
  (Call decodeCNodeInvocation_'proc)"
  apply (cases "\<not>isCNodeCap cp")
   apply (simp add: decodeCNodeInvocation_def
              cong: conj_cong)
   apply (rule ccorres_fail')
  apply (cinit' (no_subst_asm) lift: length_' cap_' extraCaps_'
                                     call_' label_' buffer_')
   apply (clarsimp simp: word_less_nat_alt decodeCNodeInvocation_def
                         list_case_If2 invocation_eq_use_types
                         label_in_CNodeInv_ranges[unfolded word_less_nat_alt]
                         cnode_invok_case_cleanup2
               simp del: Collect_const
                   cong: call_ignore_cong globals.fold_congs
                         StateSpace.state.fold_congs bool.case_cong
               cong del: invocation_label.case_cong_weak)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: unlessE_def throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: length_ineq_not_Nil unlessE_whenE
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply (simp add: split_def Let_def invocationCatch_use_injection_handler
                        injection_bindE [OF refl refl] bindE_assoc
                   del: Collect_const)
       (* sigh \<dots> just going to blog this here. i can't use call_ignore_cong
          because we need to rewrite within at least one argument in order to
          match the rewrite that's happened in the argument to ?R13918 and we
          can't apply ctac below. but once we have simplified away
          newData = newData below there's no way to get it back. sigh *)
       apply (ctac add: ccorres_injection_handler_csum1
                           [OF lookupTargetSlot_ccorres,
                               unfolded lookupTargetSlot_def])
          apply (simp add: Collect_False del: Collect_const
                     cong: call_ignore_cong)
          apply csymbr
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp add: word_less_nat_alt
                       del: Collect_const cong: call_ignore_cong)
           apply (rule ccorres_split_throws)
            apply (rule ccorres_rhs_assoc | csymbr)+
            apply (simp add: invocationCatch_use_injection_handler
                                  [symmetric, unfolded o_def]
                             if_1_0_0 dc_def[symmetric]
                        del: Collect_const cong: call_ignore_cong)
            apply (rule ccorres_Cond_rhs_Seq)
             apply (simp add:if_P del: Collect_const)
             apply (rule ccorres_cond_true_seq)
             apply (simp add: throwError_bind invocationCatch_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (simp add: linorder_not_less del: Collect_const cong: call_ignore_cong)
            apply (rule ccorres_Guard_Seq)+
            apply csymbr
            apply (simp add: if_1_0_0 interpret_excaps_test_null
                             excaps_map_def
                        del: Collect_const)
            apply (rule ccorres_Cond_rhs_Seq)
             apply (simp add: throwError_bind invocationCatch_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (simp del: Collect_const cong: call_ignore_cong)
            apply (rule ccorres_add_return)
            apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
            apply (rule ccorres_add_return)
              apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=3 and buffer=buffer])
                apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
                apply (rule ccorres_move_c_guard_cte)
                apply ctac
                  apply (rule ccorres_assert2)
                  apply (simp add: split_def invocationCatch_use_injection_handler
                                   injection_bindE [OF refl refl] bindE_assoc
                                   injection_liftE [OF refl] if_not_P
                             cong: call_ignore_cong)
                  apply (ctac add: ccorres_injection_handler_csum1 [OF ensureEmptySlot_ccorres])
                     prefer 2
                     apply simp
                     apply (rule ccorres_split_throws)
                      apply simp
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                     apply vcg
                    apply simp
                    apply (ctac add: ccorres_injection_handler_csum1
                                         [OF lookupSourceSlot_ccorres,
                                             unfolded lookupSourceSlot_def])
                       prefer 2
                       apply simp
                       apply (rule ccorres_split_throws)
                        apply simp
                        apply (rule ccorres_return_C_errorE, simp+)[1]
                       apply vcg
                      apply (simp add: liftE_bindE cong: call_ignore_cong)
                      apply csymbr
                      apply (rule ccorres_move_c_guard_cte)
                      apply (rule ccorres_pre_getCTE)
                      apply (rule ccorres_add_return)
                      apply (rule_tac xf'=ret__unsigned_long_'
                                   and r'="\<lambda>_ rv'. (rv' = scast cap_null_cap)
                                              = (cteCap rvb = NullCap)"
                                    in ccorres_split_nothrow)
                          apply (rule_tac P'="{s. \<exists>v. cslift s (cte_Ptr rva) = Some v
                                                  \<and> ccte_relation rvb v}"
                                     in ccorres_from_vcg[where P=\<top>])
                          apply (rule allI, rule conseqPre, vcg)
                          apply (rule subsetI, clarsimp simp: Collect_const_mem return_def)
                          apply (clarsimp dest!: ccte_relation_ccap_relation
                                           simp: cap_get_tag_NullCap
                                                 typ_heap_simps)
                         apply ceqv
                        apply (simp del: Collect_const cong: call_ignore_cong)
                        apply (rule ccorres_Cond_rhs_Seq)
                         apply (simp add: whenE_def injection_handler_throwError)
                         apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
                          apply vcg
                         apply (rule conseqPre, vcg)
                         apply (clarsimp simp: throwError_def return_def hd_conv_nth
                                               syscall_error_rel_def exception_defs
                                               syscall_error_to_H_cases numeral_eqs)
                         apply (clarsimp simp: lookup_fault_missing_capability_lift
                                               mask_eq_iff_w2p word_size word_less_nat_alt
                                               word_bits_def hd_conv_nth)
                        apply (simp add: whenE_def[where P=False]
                                         injection_handler_returnOk Collect_const[symmetric]
                                   cong: call_ignore_cong del: Collect_const)
                        apply (rule ccorres_Cond_rhs_Seq)
                         -- "CNodeCopy case"
                         apply (simp add: Collect_const[symmetric] del: Collect_const)
                         apply (rule ccorres_rhs_assoc)+
                         apply (rule ccorres_Cond_rhs_Seq)
                          apply (simp add: injection_handler_throwError dc_def[symmetric]
                                           if_P)
                          apply (rule syscall_error_throwError_ccorres_n)
                          apply (simp add: syscall_error_to_H_cases)
                         apply (simp add: list_case_helper injection_handler_returnOk
                                          split_def hd_conv_nth numeral_eqs[symmetric]
                                          if_not_P
                                     del: Collect_const)
                         apply (rule ccorres_add_return)
                         apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=4 and buffer=buffer])
                           apply csymbr
                           apply (rule ccorres_move_c_guard_cte)
                           apply (simp add: split_def del: Collect_const)
                           apply (rule_tac val="maskCapRights (rightsFromWord (args ! 4)) (cteCap rvb)"
                                           in ccorres_add_specific_return)
                           apply (ctac add: maskCapRights_ccorres)
                             apply (ctac add: ccorres_injection_handler_csum1 [OF deriveCap_ccorres])
                                prefer 2
                                apply simp
                                apply (rule ccorres_split_throws)
                                 apply simp
                                 apply (rule ccorres_return_C_errorE, simp+)[1]
                                apply vcg
                               apply simp
                               apply csymbr
                               apply csymbr
                               apply csymbr
                               apply (simp add: cap_get_tag_NullCap del: Collect_const)
                               apply (rule ccorres_Cond_rhs_Seq)
                                apply (simp add: injection_handler_throwError whenE_def
                                                 dc_def[symmetric])
                                apply (rule syscall_error_throwError_ccorres_n)
                                apply (simp add: syscall_error_to_H_cases)
                               apply (simp add: whenE_def injection_handler_returnOk
                                                ccorres_invocationCatch_Inr performInvocation_def
                                                bindE_assoc false_def)
                               apply (ctac add: setThreadState_ccorres)
                                 apply (simp add: ccorres_cond_iffs)
                                 apply (ctac(no_vcg) add: invokeCNodeInsert_ccorres)
                                   apply (rule ccorres_alternative2)
                                   apply (rule ccorres_return_CE, simp+)[1]
                                  apply (rule ccorres_return_C_errorE, simp+)[1]
                                 apply wp
                                apply (wp sts_valid_pspace_hangers)
                               apply (simp add: Collect_const_mem)
                               apply (vcg exspec=setThreadState_modifies)
                              apply simp
                              apply (wp injection_wp_E[OF refl])
                              apply (rule hoare_post_imp_R)
                               apply (rule_tac Q'="\<lambda>rv. valid_pspace' and valid_queues
                                                    and valid_cap' rv and valid_objs'
                                                         and tcb_at' thread and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)"
                                           in hoare_vcg_R_conj)
                                apply (rule deriveCap_Null_helper[OF deriveCap_derived])
                               apply wp
                              apply (clarsimp simp: cte_wp_at_ctes_of)
                              apply (simp add: is_derived'_def badge_derived'_def
                                               valid_tcb_state'_def)
                             apply (simp add: Collect_const_mem all_ex_eq_helper)
                             apply (vcg exspec=deriveCap_modifies)
                            apply wp
                           apply (simp add: Collect_const_mem)
                           apply (vcg exspec=maskCapRights_modifies)
                          apply wp
                         apply (simp add: Collect_const_mem)
                         apply (vcg exspec=getSyscallArg_modifies)
                        apply (rule ccorres_Cond_rhs_Seq)
                         -- "CNodeMint case"
                         apply (simp add: Collect_const[symmetric]
                                     del: Collect_const)
                         apply (rule ccorres_rhs_assoc)+
                         apply (rule ccorres_Cond_rhs_Seq)
                          apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
                           apply vcg
                          apply (rule conseqPre, vcg)
                          apply (clarsimp split: split_if simp: injection_handler_throwError)
                          apply (auto simp: throwError_def return_def
                                            syscall_error_to_H_cases syscall_error_rel_def
                                            exception_defs)[1]
                         apply (simp add: list_case_helper injection_handler_returnOk
                                          split_def linorder_not_less numeral_eqs[symmetric]
                                          hd_conv_nth le_Suc_eq le_imp_diff_is_add if_not_P
                                     del: Collect_const)
                         apply (rule ccorres_add_return)
                           apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=4 and buffer=buffer])
                           apply csymbr
                           apply (rule ccorres_add_return)
                           apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=5 and buffer=buffer])
                             apply (rule ccorres_move_c_guard_cte)
                             apply (simp del: Collect_const)
                             apply (rule_tac val="maskCapRights (rightsFromWord (args ! 4)) (cteCap rvb)"
                                             in ccorres_add_specific_return)
                             apply (ctac add: maskCapRights_ccorres)
                               apply (rule ccorres_symb_exec_r)
                                 apply (ctac add: ccorres_injection_handler_csum1 [OF deriveCap_ccorres])
                                    prefer 2
                                    apply simp
                                    apply (rule ccorres_split_throws)
                                     apply simp
                                     apply (rule ccorres_return_C_errorE, simp+)[1]
                                    apply vcg
                                   apply simp
                                   apply csymbr
                                   apply csymbr
                                   apply csymbr
                                   apply (simp add: cap_get_tag_NullCap del: Collect_const)
                                   apply (rule ccorres_Cond_rhs_Seq)
                                    apply (simp add: whenE_def injection_handler_returnOk
                                                     invocationCatch_def injection_handler_throwError
                                                     dc_def[symmetric])
                                    apply (rule syscall_error_throwError_ccorres_n)
                                    apply (simp add: syscall_error_to_H_cases)
                                   apply (simp add: whenE_def injection_handler_returnOk
                                                    ccorres_invocationCatch_Inr false_def
                                                    performInvocation_def bindE_assoc)
                                   apply (ctac add: setThreadState_ccorres)
                                     apply (simp add: ccorres_cond_iffs)
                                     apply (ctac(no_vcg) add: invokeCNodeInsert_ccorres)
                                       apply (rule ccorres_alternative2)
                                       apply (rule ccorres_return_CE, simp+)[1]
                                      apply (rule ccorres_return_C_errorE, simp+)[1]
                                     apply wp
                                    apply (wp sts_valid_pspace_hangers)
                                   apply (simp add: Collect_const_mem)
                                   apply (vcg exspec=setThreadState_modifies)
                                  apply (simp add: conj_comms valid_tcb_state'_def)
                                  apply (wp injection_wp_E[OF refl])
                                  apply (rule hoare_post_imp_R)
                                   apply (rule_tac Q'="\<lambda>rv. valid_pspace' and valid_queues
                                                        and valid_cap' rv and valid_objs'
                                                             and tcb_at' thread and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)"
                                               in hoare_vcg_R_conj)
                                    apply (rule deriveCap_Null_helper [OF deriveCap_derived])
                                   apply wp
                                  apply (clarsimp simp: cte_wp_at_ctes_of)
                                  apply (simp add: is_derived'_def badge_derived'_def)
                                 apply (simp add: Collect_const_mem all_ex_eq_helper)
                                 apply (vcg exspec=deriveCap_modifies)
                                apply (simp add: Collect_const_mem)
                                apply (vcg exspec=updateCapData_spec2)
                               apply (rule conseqPre, vcg exspec=updateCapData_spec2, clarsimp)
                               apply fastforce
                              apply simp
                              apply wp
                             apply (simp add: Collect_const_mem hd_drop_conv_nth)
                             apply (vcg exspec=maskCapRights_modifies)
                            apply simp
                            apply wp
                           apply (simp add: Collect_const_mem)
                           apply (vcg exspec=getSyscallArg_modifies)
                          apply simp
                          apply wp
                         apply (simp add: Collect_const_mem)
                         apply (vcg exspec=getSyscallArg_modifies)
                        apply (rule ccorres_Cond_rhs_Seq)
                         -- "CNodeMove case"
                         apply (simp add: Collect_const[symmetric] split_def
                                          injection_handler_returnOk whenE_def
                                          ccorres_invocationCatch_Inr
                                          performInvocation_def bindE_assoc
                                     del: Collect_const)
                         apply (rule ccorres_rhs_assoc)+
                         apply (rule ccorres_move_c_guard_cte)
                         apply (rule ccorres_symb_exec_r)
                           apply (rule_tac xf'=newCap_' in ccorres_abstract, ceqv)
                           apply (rule_tac P="ccap_relation (cteCap rvb) rv'a"
                                       in ccorres_gen_asm2)
                           apply csymbr
                           apply csymbr
                           apply (simp add: cap_get_tag_NullCap true_def)
                           apply (ctac add: setThreadState_ccorres)
                             apply (simp add: ccorres_cond_iffs)
                             apply (ctac(no_vcg) add: invokeCNodeMove_ccorres)
                               apply (rule ccorres_alternative2)
                               apply (rule ccorres_return_CE, simp+)[1]
                              apply (rule ccorres_return_C_errorE, simp+)[1]
                             apply wp
                            apply (wp sts_valid_pspace_hangers)
                           apply (simp add: Collect_const_mem)
                           apply (vcg exspec=setThreadState_modifies)
                          apply vcg
                         apply (rule conseqPre, vcg, clarsimp)
                        apply (rule ccorres_Cond_rhs_Seq)
                         -- "CNodeMutate case"
                         apply (rule ccorres_rhs_assoc)+
                         apply (simp add: Collect_const[symmetric] del: Collect_const
                                    cong: call_ignore_cong)
                         apply (rule ccorres_Cond_rhs_Seq)
                          apply (simp add: injection_handler_throwError dc_def[symmetric] if_P)
                          apply (rule syscall_error_throwError_ccorres_n)
                          apply (simp add: syscall_error_to_H_cases)
                         apply (simp add: if_not_P del: Collect_const)
                         apply (rule ccorres_add_return)
                         apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=4 and buffer=buffer])
                           apply (simp add: list_case_helper split_def hd_conv_nth
                                            Collect_const[symmetric]
                                            injection_handler_returnOk
                                       del: Collect_const)
                           apply (rule ccorres_move_c_guard_cte)
                           apply (rule ccorres_symb_exec_r)
                             apply (rule_tac xf'="newCap_'" in ccorres_abstract, ceqv)
                             apply (rule_tac P="ccap_relation (updateCapData True (args ! 4) (cteCap rvb)) rv'a"
                                             in ccorres_gen_asm2)
                             apply csymbr
                             apply csymbr
                             apply (simp add: cap_get_tag_isCap del: Collect_const)
                             apply (rule ccorres_Cond_rhs_Seq)
                              apply (simp add: whenE_def injection_handler_throwError
                                               dc_def[symmetric] numeral_eqs)
                              apply (rule syscall_error_throwError_ccorres_n)
                              apply (simp add: syscall_error_to_H_cases)
                             apply (simp add: whenE_def injection_handler_returnOk
                                              ccorres_invocationCatch_Inr numeral_eqs
                                              performInvocation_def bindE_assoc)
                             apply (ctac add: setThreadState_ccorres)
                               apply (simp add: true_def ccorres_cond_iffs)
                               apply (ctac(no_vcg) add: invokeCNodeMove_ccorres)
                                 apply (rule ccorres_alternative2)
                                 apply (rule ccorres_return_CE, simp+)[1]
                                apply (rule ccorres_return_C_errorE, simp+)[1]
                               apply (wp sts_valid_pspace_hangers)
                             apply (simp add: Collect_const_mem)
                             apply (vcg exspec=setThreadState_modifies)
                            apply (simp add: Collect_const_mem exception_defs)
                            apply (vcg exspec=updateCapData_spec2)
                           apply (rule conseqPre, vcg exspec=updateCapData_spec2, clarsimp)
                           apply fastforce
                          apply wp
                         apply (simp add: Collect_const_mem)
                         apply (vcg exspec=getSyscallArg_modifies)
                        apply simp
                        apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
                        apply (simp add: upto_enum_def fromEnum_def toEnum_def
                                         enum_invocation_label)
                       apply (wp getCTE_wp')
                      apply (simp add: Collect_const_mem)
                      apply vcg
                     apply (simp add: cte_wp_at_ctes_of[where P="op = cte" for cte]
                                      cte_wp_at_ctes_of[where P="\<lambda>cte. Q cte \<and> R cte" for Q R]
                                      badge_derived_updateCapData)
                     apply (rule validE_R_validE)
                     apply (rule_tac Q'="\<lambda>a b. cte_wp_at' (\<lambda>x. True) a b \<and> invs' b \<and> 
                       tcb_at' thread b  \<and> sch_act_wf (ksSchedulerAction b) b \<and> valid_tcb_state' Restart b
                       \<and> Q2 b" for Q2 in  hoare_post_imp_R)
                       prefer 2
                       apply (clarsimp simp:cte_wp_at_ctes_of)
                       apply (drule ctes_of_valid')
                         apply (erule invs_valid_objs')
                        apply (clarsimp simp:valid_updateCapDataI invs_queues invs_valid_objs' invs_valid_pspace')
                       apply (assumption)
                     apply (wp hoare_vcg_all_lift_R injection_wp_E[OF refl]
                               lsfco_cte_at' hoare_vcg_const_imp_lift_R
                           )+
                    apply (simp add: Collect_const_mem word_sle_def word_sless_def
                                     all_ex_eq_helper)
                    apply (vcg exspec=lookupSourceSlot_modifies)
                   apply simp
                   apply (wp injection_wp_E[OF refl])
                  apply (simp add: Collect_const_mem)
                  apply (vcg exspec=ensureEmptySlot_modifies)
                 apply simp
                 apply (wp hoare_drop_imps)[1]
                apply (simp add: Collect_const_mem)
                apply vcg
               apply wp
              apply (vcg exspec=getSyscallArg_modifies)
             apply wp
            apply (simp add: Collect_const_mem)
            apply (vcg exspec=getSyscallArg_modifies)
           apply (vcg exspec=getSyscallArg_modifies
                      exspec=ensureEmptySlot_modifies exspec=lookupSourceSlot_modifies
                      exspec=maskCapRights_modifies exspec=updateCapData_modifies
                      exspec=setThreadState_modifies exspec=invokeCNodeMove_modifies
                      exspec=invokeCNodeInsert_modifies exspec=deriveCap_modifies)
          apply (simp del: Collect_const)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                            performInvocation_def bindE_assoc)
           apply (rule ccorres_split_throws)
            apply (rule ccorres_rhs_assoc)+
            apply (ctac add: setThreadState_ccorres)
              apply (ctac(no_vcg) add: invokeCNodeRevoke_ccorres)
                apply (rule ccorres_alternative2)
                apply (rule ccorres_return_CE, simp+)[1]
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply (wp sts_invs_minor')
            apply (simp add: Collect_const_mem)
            apply (vcg exspec=setThreadState_modifies)
           apply (vcg exspec=setThreadState_modifies exspec=invokeCNodeRevoke_modifies)
          apply (simp del: Collect_const)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                            performInvocation_def bindE_assoc)
           apply (rule ccorres_split_throws)
            apply (rule ccorres_rhs_assoc)+
            apply (ctac add: setThreadState_ccorres)
              apply (ctac(no_vcg) add: invokeCNodeDelete_ccorres)
                apply (rule ccorres_alternative2)
                apply (rule ccorres_return_CE, simp+)[1]
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply (wp sts_invs_minor')
            apply (simp add: Collect_const_mem)
            apply (vcg exspec=setThreadState_modifies)
           apply (vcg exspec=setThreadState_modifies exspec=invokeCNodeDelete_modifies)
          apply (simp del: Collect_const)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp add: injection_handler_returnOk bindE_assoc
                            injection_bindE[OF refl refl] split_def
                            dc_def[symmetric])
           apply (rule ccorres_split_throws)
            apply (rule ccorres_rhs_assoc)+
            apply (ctac add: ccorres_injection_handler_csum1 [OF ensureEmptySlot_ccorres])
               apply (simp add: ccorres_invocationCatch_Inr performInvocation_def
                                dc_def[symmetric] bindE_assoc)
               apply (ctac add: setThreadState_ccorres)
                 apply (ctac(no_vcg) add: invokeCNodeSaveCaller_ccorres)
                   apply (rule ccorres_alternative2)
                   apply (rule ccorres_return_CE, simp+)[1]
                  apply (rule ccorres_return_C_errorE, simp+)[1]
                 apply (wp sts_valid_pspace_hangers)
               apply (simp add: Collect_const_mem)
               apply (vcg exspec=setThreadState_modifies)
              apply (simp add: dc_def[symmetric])
              apply (rule ccorres_split_throws)
               apply simp
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply vcg
             apply (wp injection_wp_E[OF refl])
            apply (simp add: all_ex_eq_helper)
            apply (vcg exspec=ensureEmptySlot_modifies)
           apply (vcg exspec=invokeCNodeSaveCaller_modifies exspec=setThreadState_modifies
                      exspec=ensureEmptySlot_modifies)
          apply (simp del: Collect_const)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                            injection_bindE[OF refl refl] bindE_assoc
                            injection_liftE [OF refl] split_def
                       del: Collect_const)
           apply (rule ccorres_split_throws)
            apply (rule ccorres_rhs_assoc)+
            apply (simp only: liftE_bindE)
            apply (rule ccorres_pre_getCTE)
            apply (rule ccorres_move_c_guard_cte)
            apply (rule ccorres_symb_exec_r) 
              apply (rule_tac xf'=ret__unsigned_long_' in ccorres_abstract, ceqv)
              apply (rule_tac P="rv' = from_bool (hasRecycleRights (cteCap rva))"
                          in ccorres_gen_asm2)
              apply (simp del: Collect_const) 
              apply (rule ccorres_Cond_rhs_Seq)               
               apply (simp add: unlessE_def whenE_def injection_handler_throwError
                                dc_def[symmetric] from_bool_0) 
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply (simp add: unlessE_def whenE_def injection_handler_returnOk 
                               from_bool_neq_0
                          del: Collect_const)
              apply (simp add: unlessE_def injection_handler_returnOk
                               ccorres_invocationCatch_Inr
                               performInvocation_def bindE_assoc)
              apply (ctac add: setThreadState_ccorres)
                apply (ctac(no_vcg) add: invokeCNodeRecycle_ccorres)
                  apply (rule ccorres_alternative2)
                  apply (rule ccorres_return_CE, simp+)[1]
                 apply (rule ccorres_return_C_errorE, simp+)[1]
                apply (wp sts_invs_minor')
              apply (simp add: Collect_const_mem)
              apply (vcg exspec=setThreadState_modifies)
             apply (simp add: Collect_const_mem)
             apply vcg
            apply (rule conseqPre, vcg, clarsimp)
            apply fastforce
           apply (vcg exspec=setThreadState_modifies 
                      exspec=invokeCNodeRecycle_modifies 
                      exspec=hasRecycleRights_modifies)
          apply (simp del: Collect_const)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp del: Collect_const)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr+
           apply (simp add: if_1_0_0 del: Collect_const)
           apply (rule ccorres_Cond_rhs_Seq)
            apply (simp add: if_P | rule ccorres_cond_true_seq)+
            apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
             apply vcg
            apply (rule conseqPre, vcg)
            apply (clarsimp simp: injection_handler_throwError 
                           split: list.split)
            apply (simp add: throwError_def return_def exception_defs
                             syscall_error_rel_def syscall_error_to_H_cases)
            apply clarsimp
           apply (simp add: invocationCatch_use_injection_handler
                                  [symmetric, unfolded o_def]
                       del: Collect_const)
           apply (rule ccorres_Guard_Seq)+
           apply csymbr
           apply (simp add: interpret_excaps_test_null excaps_map_def
                            if_1_0_0 dc_def[symmetric]
                       del: Collect_const)
           apply (rule ccorres_Cond_rhs_Seq)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule ccorres_cond_true_seq)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           apply (rule ccorres_Guard_Seq)+
           apply csymbr
           apply (simp add: interpret_excaps_test_null Suc_length_not_empty'
                            if_1_0_0 del: Collect_const)
           apply (rule ccorres_Cond_rhs_Seq)
            apply (clarsimp simp: neq_Nil_conv)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           apply (simp add: split_def Collect_const[symmetric] del: Collect_const)
           apply (rule ccorres_add_return)
           apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
             apply (rule ccorres_add_return)
             apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=3 and buffer=buffer])
               apply (rule ccorres_add_return)
               apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=4 and buffer=buffer])
                 apply (rule ccorres_add_return)
                 apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=5 and buffer=buffer])
                   apply (rule ccorres_add_return)
                   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=6 and buffer=buffer])
                     apply (rule ccorres_add_return)
                     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=7 and buffer=buffer])
                       apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
                       apply (rule ccorres_move_c_guard_cte)
                       apply ctac
                         apply (rule ccorres_assert2)
                         apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=1])
                         apply (rule ccorres_move_c_guard_cte)
                         apply ctac
                           apply (rule ccorres_assert2)
                           apply (simp add: le_Suc_eq if_not_P length_ineq_not_Nil)
                           apply (simp add: invocationCatch_use_injection_handler
                                            injection_liftE [OF refl] injection_handler_returnOk
                                            injection_bindE [OF refl refl] bindE_assoc)
                           apply (ctac add: ccorres_injection_handler_csum1
                                               [OF lookupSourceSlot_ccorres, unfolded lookupSourceSlot_def])
                              prefer 2
                              apply simp
                              apply (rule ccorres_split_throws)
                               apply (rule ccorres_return_C_errorE, simp+)[1]
                              apply vcg
                             apply (simp add: Collect_False del: Collect_const)
                             apply csymbr
                             apply (ctac add: ccorres_injection_handler_csum1
                                                 [OF lookupPivotSlot_ccorres, unfolded lookupPivotSlot_def])
                                prefer 2
                                apply simp
                                apply (rule ccorres_split_throws)
                                 apply (rule ccorres_return_C_errorE, simp+)[1]
                                apply vcg
                               apply (simp add: Collect_False split_def
                                           del: Collect_const)
                               apply csymbr
                               apply (rule ccorres_Cond_rhs_Seq)
                                apply (simp add: whenE_def injection_handler_throwError
                                                 dc_def[symmetric])
                                apply (rule syscall_error_throwError_ccorres_n)
                                apply (simp add: syscall_error_to_H_cases)
                               apply (simp add: whenE_def[where P=False] injection_handler_returnOk
                                           del: Collect_const)
                               apply (rule ccorres_subgoal_tailE)
                                apply (rule ccorres_move_c_guard_cte)
                                apply (simp add: injection_handler_returnOk del: Collect_const)
                                apply (simp add: liftE_bindE liftM_def del: Collect_const)
                                apply (rule ccorres_pre_getCTE)
                                apply (rule ccorres_symb_exec_r)
                                  apply (rule_tac xf'=ret__unsigned_long_' in ccorres_abstract, ceqv)
                                  apply (rule_tac P="(rv' = scast cap_null_cap) = (cteCap rvc = NullCap)"
                                                in ccorres_gen_asm2)
                                  apply (simp del: Collect_const)
                                  apply (rule ccorres_Cond_rhs_Seq)
                                   apply (simp add: whenE_def injection_handler_throwError)
                                   apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
                                    apply vcg
                                   apply (rule conseqPre, vcg)
                                   apply (clarsimp simp: throwError_def return_def hd_conv_nth
                                                         syscall_error_rel_def exception_defs
                                                         syscall_error_to_H_cases numeral_eqs[symmetric])
                                   apply (clarsimp simp: lookup_fault_missing_capability_lift
                                                         mask_eq_iff_w2p word_size word_less_nat_alt
                                                         word_bits_def)
                                  apply (simp add: injection_handler_returnOk whenE_def[where P=False]
                                              del: Collect_const)
                                  apply (rule ccorres_pre_getCTE)
                                  apply (rule ccorres_move_c_guard_cte)
                                  apply (rule ccorres_symb_exec_r)
                                    apply (rule_tac xf'=ret__unsigned_long_' in ccorres_abstract, ceqv)
                                    apply (rule_tac P="(rv'a = scast cap_null_cap) = (cteCap x = NullCap)"
                                                  in ccorres_gen_asm2)
                                    apply (simp del: Collect_const)
                                    apply (rule ccorres_Cond_rhs_Seq)
                                     apply (simp add: whenE_def injection_handler_throwError)
                                     apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
                                      apply vcg
                                     apply (rule conseqPre, vcg)
                                     apply (clarsimp simp: throwError_def return_def hd_conv_nth
                                                           exception_defs syscall_error_rel_def
                                                           numeral_eqs)
                                     apply (simp add: syscall_error_to_H_cases
                                                      lookup_fault_missing_capability_lift)
                                     apply (simp add: mask_eq_iff_w2p word_less_nat_alt
                                                      word_size word_bits_def)
                                    apply (simp add: whenE_def[where P=False] injection_handler_returnOk
                                                     hd_conv_nth numeral_eqs[symmetric]
                                                del: Collect_const)
                                    apply (rule ccorres_move_c_guard_cte)
                                    apply (rule ccorres_symb_exec_r)
                                      apply (rule_tac xf'="newSrcCap_'" in ccorres_abstract, ceqv)
                                      apply (rule_tac P="ccap_relation (updateCapData True (args ! 5) (cteCap rvc)) rv'b"
                                                      in ccorres_gen_asm2)
                                      apply (rule ccorres_move_c_guard_cte)
                                      apply (rule ccorres_symb_exec_r)
                                        apply (rule_tac xf'="newPivotCap_'" in ccorres_abstract, ceqv)
                                        apply (rule_tac P="ccap_relation (updateCapData True (args ! 2) (cteCap x)) rv'c"
                                                        in ccorres_gen_asm2)
                                        apply csymbr
                                        apply (simp add: cap_get_tag_NullCap del: Collect_const)
                                        apply (rule ccorres_Cond_rhs_Seq)
                                         apply (simp add: whenE_def injection_handler_throwError
                                                          dc_def[symmetric])
                                         apply (rule syscall_error_throwError_ccorres_n)
                                         apply (simp add: syscall_error_to_H_cases)
                                        apply (simp add: whenE_def[where P=False] injection_handler_returnOk
                                                    del: Collect_const)
                                        apply csymbr
                                        apply (simp add: cap_get_tag_NullCap del: Collect_const)
                                        apply (rule ccorres_Cond_rhs_Seq)
                                         apply (simp add: whenE_def injection_handler_throwError
                                                          dc_def[symmetric])
                                         apply (rule syscall_error_throwError_ccorres_n)
                                         apply (simp add: syscall_error_to_H_cases)
                                        apply (simp add: whenE_def injection_handler_returnOk
                                                         ccorres_invocationCatch_Inr
                                                         performInvocation_def bindE_assoc)
                                        apply (ctac add: setThreadState_ccorres)
                                          apply (rule ccorres_rhs_assoc2, rule ccorres_split_throws)
                                           apply (ctac(no_vcg) add: invokeCNodeRotate_ccorres)
                                             apply (rule ccorres_alternative2)
                                             apply (rule ccorres_return_CE, simp+)[1]
                                            apply (rule ccorres_return_C_errorE, simp+)[1]
                                           apply wp
                                          apply (vcg exspec=invokeCNodeRotate_modifies)
                                         apply (wp static_imp_wp)
                                       apply (simp add: Collect_const_mem)
                                       apply (vcg exspec=setThreadState_modifies)
                                      apply (simp add: Collect_const_mem)
                                      apply (vcg exspec=updateCapData_spec2)
                                     apply (rule conseqPre, vcg exspec=updateCapData_spec2)
                                     apply clarsimp
                                     apply fastforce
                                    apply (simp add: Collect_const_mem)
                                    apply (vcg exspec=updateCapData_spec2)
                                   apply (rule conseqPre, vcg exspec=updateCapData_spec2)
                                   apply clarsimp
                                   apply fastforce
                                  apply (simp add: Collect_const_mem)
                                  apply vcg
                                 apply (rule conseqPre, vcg, clarsimp)
                                apply (simp add: Collect_const_mem)
                                apply vcg
                               apply (rule conseqPre, vcg, clarsimp)
                              apply (rule ccorres_Cond_rhs_Seq)
                               apply (simp add: unlessE_def)
                               apply (rule ccorres_rhs_assoc)+
                               apply (ctac add: ccorres_injection_handler_csum1
                                                      [OF ensureEmptySlot_ccorres])
                                  apply (simp add: Collect_False del: Collect_const)
                                 apply simp
                                 apply (rule ccorres_split_throws)
                                  apply (rule ccorres_return_C_errorE, simp+)[1]
                                 apply vcg
                                apply simp
                                apply (wp injection_wp_E[OF refl] ensureEmptySlot_stronger)
                               apply (simp add: Collect_const_mem all_ex_eq_helper)
                               apply (vcg exspec=ensureEmptySlot_modifies)
                              apply (simp add: unlessE_def injection_handler_returnOk
                                          del: Collect_const)
                              apply (wp injection_wp_E[OF refl])
                              apply (rule_tac Q'="\<lambda>rvb. invs' 
                                                   and cte_at' rv and cte_at' rva
                                                   and tcb_at' thread"
                                                        in hoare_post_imp_R)
                               apply (wp lsfco_cte_at')
                              apply (clarsimp simp: cte_wp_at_ctes_of weak_derived_updateCapData
                                                    capBadge_updateCapData_True)
                              apply (simp add: valid_tcb_state'_def)
                              apply (auto simp:updateCapData_Untyped 
                                elim!: valid_updateCapDataI[OF ctes_of_valid'])[1]
                             apply (simp add: Collect_const_mem all_ex_eq_helper)
                             apply (vcg exspec=lookupPivotSlot_modifies)
                            apply simp
                            apply (wp injection_wp_E[OF refl]
                                      lsfco_cte_at')
                           apply (simp add: Collect_const_mem all_ex_eq_helper)
                           apply (vcg exspec=lookupSourceSlot_modifies)
                          apply simp
                          apply (wp | wp_once hoare_drop_imps)+
                         apply simp
                         apply vcg
                        apply simp
                        apply (wp | wp_once hoare_drop_imps)+
                       apply simp
                       apply vcg
                      apply wp
                     apply simp
                     apply (vcg exspec=getSyscallArg_modifies)
                    apply (wp static_imp_wp)
                   apply simp
                   apply (vcg exspec=getSyscallArg_modifies)
                  apply wp
                 apply simp
                 apply (vcg exspec=getSyscallArg_modifies)
                apply (wp static_imp_wp)
               apply simp
               apply (vcg exspec=getSyscallArg_modifies)
              apply (wp static_imp_wp)
             apply simp
             apply (vcg exspec=getSyscallArg_modifies)
            apply wp
           apply simp
           apply (vcg exspec=getSyscallArg_modifies)
          apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
          apply (simp add: upto_enum_def fromEnum_def toEnum_def
                           enum_invocation_label)
         apply (rule ccorres_split_throws)
          apply (simp add: ccorres_cond_iffs)
          apply (rule ccorres_return_C_errorE, simp+)[1]
         apply vcg
        apply simp
        apply (wp injection_wp_E[OF refl] hoare_vcg_const_imp_lift_R
                  hoare_vcg_all_lift_R lsfco_cte_at' static_imp_wp | wp_once hoare_drop_imps)+
       apply (simp add: all_ex_eq_helper)
       apply (vcg exspec=lookupTargetSlot_modifies)
      apply simp
      apply wp
     apply simp
     apply (vcg exspec=getSyscallArg_modifies)
    apply simp
    apply wp
   apply simp
   apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: valid_tcb_state'_def invs_valid_objs' invs_valid_pspace'
                        ct_in_state'_def pred_tcb_at' invs_queues
                        cur_tcb'_def word_sle_def word_sless_def
                        unat_lt2p[where 'a=32, folded word_bits_def])
  apply (rule conjI)
   apply (clarsimp simp: sysargs_rel_n_def n_msgRegisters_def excaps_map_def
                         cte_wp_at_ctes_of excaps_in_mem_def slotcap_in_mem_def
                         sysargs_rel_def length_ineq_not_Nil
                  dest!: interpret_excaps_eq)
   (* why does auto with these rules take ten times as long? *)
    apply ((rule conjI | clarsimp simp:split_def neq_Nil_conv
                      | erule pred_tcb'_weakenE disjE
                      | drule st_tcb_at_idle_thread')+)[1]
  apply (frule interpret_excaps_eq)
  apply (clarsimp simp: excaps_map_def mask_def[where n=4]
                        ccap_rights_relation_def rightsFromWord_wordFromRights
                        "StrictC'_thread_state_defs" map_comp_Some_iff
                        rf_sr_ksCurThread hd_conv_nth hd_drop_conv_nth)
  apply ((rule conjI
            | clarsimp simp: rightsFromWord_wordFromRights
                             ccte_relation_def c_valid_cte_def
                             cl_valid_cte_def c_valid_cap_def
                             option_map_Some_eq2 neq_Nil_conv
                             ccap_relation_def numeral_eqs
                             ccap_relation_NullCap_iff[symmetric]
                             if_1_0_0 interpret_excaps_test_null
                             mdbRevocable_CL_cte_to_H false_def true_def
            | clarsimp simp: typ_heap_simps'
            | frule length_ineq_not_Nil)+)  
  done

end

crunch valid_queues[wp]: insertNewCap "valid_queues"
  (wp: crunch_wps)

lemmas setCTE_def3 = setCTE_def2[THEN eq_reflection]

lemma setCTE_sch_act_wf[wp]:
  "\<lbrace> \<lambda>s. sch_act_wf (ksSchedulerAction s) s \<rbrace>
   setCTE src cte 
   \<lbrace>\<lambda>x s. sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  by (wp sch_act_wf_lift setCTE_pred_tcb_at' setCTE_tcb_in_cur_domain')

crunch sch_act_wf[wp]: insertNewCap "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps ignore: setCTE)
  
crunch ksCurThread[wp]: deleteObjects "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps ignore:freeMemory simp : unless_def)

context kernel_m begin

lemma wordFromMessageInfo_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call wordFromMessageInfo_'proc 
           \<lbrace>\<acute>ret__unsigned_long = index (message_info_C.words_C (mi_' s)) (unat 0)\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply (simp add: word_sless_def word_sle_def)
  done

lemma message_info_lift_def2:
  "message_info_lift message_info \<equiv>
  \<lparr>msgLabel_CL = (index (message_info_C.words_C message_info) 0 >> 12) && mask 20,
   msgCapsUnwrapped_CL = (index (message_info_C.words_C message_info) 0 >> 9) && mask 3,
   msgExtraCaps_CL = (index (message_info_C.words_C message_info) 0 >> 7) && mask 2,
   msgLength_CL = (index (message_info_C.words_C message_info) 0 >> 0) && mask 7\<rparr>"
  apply (simp add: message_info_lift_def mask_def)
  done

lemma globals_update_id:
  "globals_update (t_hrs_'_update (hrs_htd_update id)) x = x"
   by (simp add:id_def hrs_htd_update_def)

lemma getObjectSize_spec:
  "\<forall>s. \<Gamma>\<turnstile>\<lbrace>s. \<acute>t \<le> of_nat (length (enum::ArchTypes_H.object_type list) - 1)\<rbrace> Call getObjectSize_'proc
           \<lbrace>\<acute>ret__unsigned_long = of_nat (getObjectSize (object_type_to_H (t_' s)) (unat (userObjSize_' s)))\<rbrace>"
  apply vcg
  apply (clarsimp simp:ARMSmallPageBits_def ARMLargePageBits_def objBits_simps
    object_type_to_H_def Kernel_C_defs APIType_capBits_def ARMSectionBits_def ARMSuperSectionBits_def)
  apply (simp add:nAPIObjects_def)
  apply (simp add:enum_object_type enum_apiobject_type)
  apply unat_arith
  done

lemma object_type_from_H_bound:
  "object_type_from_H newType \<le> of_nat (length (enum::ArchTypes_H.object_type list) - Suc 0)"
  apply (simp add:enum_object_type enum_apiobject_type object_type_from_H_def)
  apply (case_tac newType)
  apply (clarsimp simp:ARMSmallPageBits_def ARMLargePageBits_def objBits_simps
     Kernel_C_defs split:apiobject_type.splits)+
  done

lemma updateCap_ct_active'[wp]:
  "\<lbrace>ct_active'\<rbrace> updateCap srcSlot cap \<lbrace>\<lambda>rva. ct_active' \<rbrace>"
  apply (rule hoare_pre)
  apply (simp add:ct_in_state'_def)
  apply (wps|wp|simp add:ct_in_state'_def)+
  done

lemma APIType_capBits_low:
  "\<lbrakk> newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < us;
     newType = APIObjectType apiobject_type.Untyped \<longrightarrow> 4 \<le> us \<and> us \<le> 30\<rbrakk>
           \<Longrightarrow> 4 \<le> APIType_capBits newType us"
  apply (case_tac newType)
  apply (clarsimp simp:invokeUntyped_proofs_def APIType_capBits_def objBits_simps
    split: apiobject_type.splits)+
  done

lemma APIType_capBits_high:
  "\<lbrakk> newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow>  us < 28;
     newType = APIObjectType apiobject_type.Untyped \<longrightarrow> us \<le> 30\<rbrakk>
           \<Longrightarrow> APIType_capBits newType us < 32"
  apply (case_tac newType)
  apply (clarsimp simp:invokeUntyped_proofs_def APIType_capBits_def objBits_simps
    split: apiobject_type.splits)+
  done

lemma typ_clear_region_eq:
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  Int_atLeastAtMost atLeastatMost_empty_iff
shows 
 "\<lbrakk>ctes_of (s::kernel_state) (ptr_val p) = Some cte; is_aligned ptr bits; bits < word_bits;
  {ptr..ptr + 2 ^ bits - 1} \<inter> {ptr_val p..ptr_val p + 0xF} = {}; ((clift hp) :: (cte_C ptr \<rightharpoonup> cte_C)) p = Some to\<rbrakk> \<Longrightarrow> 
  (clift (hrs_htd_update (typ_clear_region ptr bits) hp) :: (cte_C ptr \<rightharpoonup> cte_C)) p = Some to"
   apply (clarsimp simp:lift_t_def lift_typ_heap_def Fun.comp_def restrict_map_def split:if_splits)
   apply (intro conjI impI)
   apply (case_tac hp)
    apply (clarsimp simp:typ_clear_region_def hrs_htd_update_def)
    apply (rule arg_cong[where f = from_bytes])
    apply (clarsimp simp:heap_list_s_def lift_state_def proj_h_def)
   apply (case_tac hp)
   apply (clarsimp simp:typ_clear_region_def hrs_htd_update_def)
   apply (clarsimp simp:heap_list_s_def lift_state_def proj_h_def)
   apply (clarsimp simp:s_valid_def h_t_valid_def)
    apply (clarsimp simp:valid_footprint_def Let_def)
    apply (drule spec)
    apply (erule(1) impE)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp add:map_le_def)
    apply (drule_tac x = aa in bspec)
     apply simp
    apply (clarsimp simp:proj_d_def)
    apply (clarsimp simp:hrs_htd_update_def typ_clear_region_def
     split:if_splits option.splits)
    apply (simp add:intvl_range_conv[where 'a=32, folded word_bits_def])
    apply (subgoal_tac "ptr_val p + of_nat y \<in> {ptr_val p..ptr_val p + 0xF}")
     apply blast
    apply (clarsimp simp:blah)
     apply (rule context_conjI)
      apply (rule is_aligned_no_wrap')
      apply (rule ctes_of_is_aligned[where cte = cte and s = s])
       apply simp
      apply (simp add:objBits_simps of_nat_power[where x = 4,simplified])
     apply (rule word_plus_mono_right)
      apply (simp add:word_of_nat_le)
     apply (rule is_aligned_no_wrap')
      apply (rule ctes_of_is_aligned[where cte = cte and s = s])
       apply simp
    apply (clarsimp simp:objBits_simps)
   apply (clarsimp simp:proj_d_def)
   done

lemma cte_size_inter_empty: 
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  Int_atLeastAtMost atLeastatMost_empty_iff
shows "\<lbrakk>invs' s;ctes_of s p = Some cte;isUntypedCap (cteCap cte);p\<notin> capRange (cteCap cte) \<rbrakk>
  \<Longrightarrow> {p .. p + 0xF} \<inter> capRange (cteCap cte) = {}"
  apply (frule ctes_of_valid')
   apply fastforce
  apply (clarsimp simp:isCap_simps valid_cap'_def valid_untyped'_def)
  apply (frule ctes_of_ko_at_strong)
   apply (erule is_aligned_weaken[OF ctes_of_is_aligned])
   apply (simp add:objBits_simps)
  apply clarsimp
  apply (drule_tac x = ptr in spec)
  apply (clarsimp simp:ko_wp_at'_def)
  apply (erule impE)
   apply (erule pspace_alignedD',fastforce)
  apply (frule pspace_distinctD')
   apply fastforce
  apply (clarsimp simp:capAligned_def)
  apply (drule_tac p = v0 and p' = ptr in aligned_ranges_subset_or_disjoint)
   apply (erule pspace_alignedD',fastforce)
  apply (subst (asm) intvl_range_conv[where bits = 4,simplified])
    apply (erule is_aligned_weaken[OF ctes_of_is_aligned])
    apply (simp add:objBits_simps)
   apply (simp add:word_bits_def)
  apply (erule disjE)
   apply (simp add:obj_range'_def field_simps)
   apply blast
  apply (subgoal_tac "p \<in> {p..p+0xF}")
   prefer 2
   apply (clarsimp simp:blah)
   apply (rule is_aligned_no_wrap'[where sz = 4])
    apply (erule is_aligned_weaken[OF ctes_of_is_aligned])
    apply (simp add:objBits_simps)
   apply simp
  apply (simp add:obj_range'_def field_simps)
  apply blast
  done

lemma region_is_typelessI:
  "\<lbrakk>hrs_htd (t_hrs_' (globals t)) = hrs_htd (hrs_htd_update (typ_clear_region ptr sz) h) \<rbrakk>
         \<Longrightarrow> region_is_typeless ptr (2^sz) t"
  apply (case_tac h)
  apply (clarsimp simp: typ_clear_region_def region_is_typeless_def
     hrs_htd_def hrs_htd_update_def split:if_splits)
  done

lemma rf_sr_cpspace_relation:
  "(s,s') \<in> rf_sr \<Longrightarrow> cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState s)) (t_hrs_' (globals s'))"
  by (clarsimp simp:rf_sr_def cstate_relation_def Let_def)

lemma rf_sr_htd_safe_kernel_data_refs:
  "(s, s') \<in> rf_sr \<Longrightarrow> htd_safe (- kernel_data_refs) (hrs_htd (t_hrs_' (globals s')))"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                     kernel_data_refs_domain_eq_rotate)

lemma invokeUntyped_Retype_ccorres_side_case:
(* start the lemma with the form after ccorres_name_pre *)
  "\<lbrakk>(invs' and ct_active' and
      valid_untyped_inv' (Retype cref ptr_base ptr newType us destSlots)) s;
    ptr \<noteq> ptr_base\<rbrakk>
   \<Longrightarrow> ccorresG rf_sr \<Gamma> (cintr \<currency> dc)
         (liftxf errstate id (K ()) ret__unsigned_long_') (\<lambda>s'. s' = s)
         (UNIV \<inter> \<lbrace>\<acute>freeRegionBase = Ptr ptr\<rbrace> \<inter> \<lbrace>\<acute>regionBase = Ptr ptr_base\<rbrace> \<inter>
          \<lbrace>\<acute>srcSlot = cte_Ptr cref\<rbrace> \<inter>
          \<lbrace>\<acute>newType = object_type_from_H newType\<rbrace> \<inter>
          \<lbrace>unat \<acute>userSize = us\<rbrace> \<inter>
          \<lbrace>\<acute>destSlots = slot_range_C (cte_Ptr cnodeptr) start
                                     (of_nat (length destSlots)) \<and>
           (\<forall>n<length destSlots.
               destSlots ! n = cnodeptr + (start + of_nat n) * 0x10)\<rbrace>)
         [] (do invokeUntyped (Retype cref ptr_base ptr newType us destSlots);
                returnOk ()
             od)
            (Call invokeUntyped_Retype_'proc)"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule ctes_of_valid',fastforce)
  apply (subgoal_tac
           "invokeUntyped_proofs s cref ptr newType us destSlots sz idx")
   prefer 2
   apply (clarsimp simp: invokeUntyped_proofs_def cte_wp_at_ctes_of)
 proof -
   fix sz idx cte
   assume cover:
     "range_cover ptr sz  (APIType_capBits newType us) (length destSlots)"
   and proofs: "invokeUntyped_proofs s cref ptr newType us destSlots sz idx"
   and us_misc:
     "newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < us"
     "newType = APIObjectType apiobject_type.Untyped \<longrightarrow> 4 \<le> us \<and> us \<le> 30"
   and misc: "destSlots \<noteq> []" "ptr \<noteq> ptr  && ~~ mask sz" "ct_active' s"
     "sch_act_simple s" "invs' s "
     "ctes_of s cref = Some cte"
     "cteCap cte = UntypedCap (ptr && ~~ mask sz) sz idx"

   note no_simps[simp del] =
     untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
     atLeastatMost_subset_iff atLeastLessThan_iff Int_atLeastAtMost
     atLeastatMost_empty_iff split_paired_Ex usableUntypedRange.simps

   have us_misc':
     "(newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> us < 28)"
     using cover
     apply -
     apply (drule range_cover_sz')
     apply (clarsimp simp:APIType_capBits_def objBits_simps word_bits_conv)
     done

   have unat_of_nat:
     "unat (of_nat (APIType_capBits newType us)::word32) =
      APIType_capBits newType us"
     using cover
     apply -
     apply (rule unat_of_nat32)
     apply (drule range_cover_sz')
     apply (simp add:word_bits_def)
     done

   (* FIXME: extract? *)
   have [simp]: "ghost'state_'_update id = id" by (rule ext) simp
   have [simp]: "t_hrs_'_update (hrs_htd_update id) = id"
     by (rule ext) (simp add: hrs_htd_update_def)

   show "ccorresG rf_sr \<Gamma> (cintr \<currency> dc)
           (liftxf errstate id (\<lambda>y. ()) ret__unsigned_long_') (\<lambda>s'. s' = s)
           (\<lbrace>\<acute>freeRegionBase = Ptr ptr\<rbrace> \<inter>
            \<lbrace>\<acute>regionBase = Ptr (ptr && ~~ mask sz)\<rbrace> \<inter>
            \<lbrace>\<acute>srcSlot = cte_Ptr cref\<rbrace> \<inter>
            \<lbrace>\<acute>newType = object_type_from_H newType\<rbrace> \<inter>
            \<lbrace>unat \<acute>userSize = us\<rbrace> \<inter>
            \<lbrace>\<acute>destSlots = slot_range_C (cte_Ptr cnodeptr) start
                                       (of_nat (length destSlots)) \<and>
             (\<forall>n<length destSlots.
                destSlots ! n = cnodeptr + (start * 0x10 + of_nat n * 0x10))\<rbrace>)
           [] (do x \<leftarrow> invokeUntyped (Retype cref (ptr && ~~ mask sz) ptr
                                             newType us destSlots);
                  returnOk x od)
              (Call invokeUntyped_Retype_'proc)"
   using misc proofs cover us_misc us_misc' unat_of_nat
   apply (cinit' lift: freeRegionBase_' regionBase_' srcSlot_' newType_'
                       userSize_' destSlots_'
          simp: invokeUntyped_def bind_assoc when_def)
    apply (rule ccorres_move_c_guard_cte)
    apply csymbr
    apply (rule ccorres_abstract_cleanup)
    apply (rule_tac P = "size_ign = of_nat sz" in ccorres_gen_asm2)
    apply simp
    apply (rule ccorres_symb_exec_r)
      apply (rule ccorres_symb_exec_r)
        apply (rule ccorres_symb_exec_r)
          apply (rule ccorres_Guard_Seq)+
          apply (rule ccorres_symb_exec_r)
            apply (rule_tac xf'="\<lambda>s. totalObjectSize_' s"
                         in ccorres_abstract, ceqv)
            apply (rule_tac P = "rv' = of_nat (shiftL (length destSlots)
                                                 (APIType_capBits newType us))"
                         in ccorres_gen_asm2)
            apply (rule ccorres_symb_exec_r)
              apply (rule ccorres_Guard_Seq)+
              apply (rule ccorres_symb_exec_l)
                 apply (rule_tac P="rv = UntypedCap (ptr && ~~ mask sz) sz idx"
                              in ccorres_gen_asm)
                 apply simp
                 apply (ctac add: update_freeIndex)
                   apply (ctac add: createNewObjects_ccorres[where sz = sz and 
                     idx="getFreeIndex (ptr && ~~ mask sz)
                           (ptr + of_nat (shiftL (length destSlots)
                                           (APIType_capBits newType us)))" and
                     start = start and cnodeptr=cnodeptr and
                     num = "of_nat (length destSlots)"])
                     apply (rule ccorres_return_CE, simp+)[1]
                    apply wp
                   apply (vcg exspec=createNewObjects_modifies)
                  apply simp
                  apply (wp updateFreeIndex_invs'[where cap = "UntypedCap (ptr && ~~ mask sz) sz idx" and src = cref,simplified]
                            updateFreeIndex_pspace_no_overlap'[where cap = "UntypedCap (ptr && ~~ mask sz) sz idx",simplified]
                            updateFreeIndex_caps_no_overlap''[where cap = "UntypedCap (ptr && ~~ mask sz) sz idx",simplified]
                            updateFreeIndex_caps_overlap_reserved'[where cap = "UntypedCap (ptr && ~~ mask sz) sz idx",simplified]
                            updateFreeIndex_descendants_range_in'[where cap = "UntypedCap (ptr && ~~ mask sz) sz idx",simplified]
                            updateCap_weak_cte_wp_at hoare_vcg_ball_lift
                            freeIndexUpdate_ex_cte[where pcap = "UntypedCap (ptr && ~~ mask sz) sz idx",simplified])
                 apply vcg
                apply wp_once
               apply (clarsimp simp: getFreeIndex_def)
               apply (wp getSlotCap_wp)
              apply simp
             apply vcg
            apply clarsimp
            apply (rule conseqPre, vcg, clarsimp)
           apply vcg
          apply clarsimp
          apply (rule conseqPre, vcg, clarsimp)
         apply vcg
        apply clarsimp
        apply (rule conseqPre, vcg, clarsimp)
       apply vcg
      apply clarsimp
      apply vcg
      apply clarsimp
     apply clarsimp
     apply vcg
    apply clarsimp
    apply (rule conseqPre, vcg, clarsimp)
    apply (clarsimp simp: hrs_htd_update rf_sr_def cstate_relation_def
                          Let_def kernel_data_refs_domain_eq_rotate)
   apply (clarsimp simp: cte_wp_at_ctes_of invs_valid_objs' invs_valid_pspace'
                         conj_comms)
   apply (frule invokeUntyped_proofs.usableRange_disjoint)
   apply (frule invokeUntyped_proofs.descendants_range)
   apply (frule invokeUntyped_proofs.descendants_range(2))
   apply (frule invokeUntyped_proofs.subset_stuff)
   apply (frule invokeUntyped_proofs.ps_no_overlap', simp)
   apply (frule invokeUntyped_proofs.cref_inv)
   apply (frule invokeUntyped_proofs.caps_no_overlap')
   apply (frule invokeUntyped_proofs.idx_compare')
   apply (frule invokeUntyped_proofs.not_0_ptr)
   apply (frule range_cover_unat)
   apply (clarsimp simp: add_minus_neg_mask word_sle_def
              range_cover.unat_of_nat_n shiftL_nat shiftl_t2n
              object_type_from_H_bound field_simps getFreeIndex_def
              hrs_htd_update rf_sr_domain_eq rf_sr_htd_safe_kernel_data_refs)
   apply (rule context_conjI)
    apply clarsimp
    apply (drule(1) invokeUntyped_proofs.slots_invD)
    apply clarsimp
   apply (frule(1) APIType_capBits_low)
   apply (rule context_conjI)
    apply (erule(1) is_aligned_weaken[OF range_cover.aligned])
   apply (rule context_conjI)
    apply (erule(1) rf_sr_ctes_of_cliftE)
    apply (simp add: typ_heap_simps)
   apply (rule context_conjI)
    apply clarsimp
    apply (drule(1) invokeUntyped_proofs.slots_invD,simp)
   apply (rule context_conjI)
    apply (rule cap_get_tag_isCap[THEN iffD2,OF ccte_relation_ccap_relation])
     apply (rule rf_sr_ctes_of_cliftE,assumption+)
     apply (erule(1) rf_sr_cte_relation)
     apply simp
    apply simp
   apply simp
   apply (rule context_conjI)
    apply (rule rf_sr_ctes_of_cliftE,assumption+)
    apply (frule(2) rf_sr_cte_relation)
    apply (drule ccte_relation_ccap_relation)
    apply (simp add:cap_get_tag_UntypedCap)
   apply (intro conjI)
        apply (clarsimp simp:invokeUntyped_proofs_def)
       apply (rule aligned_add_aligned[OF aligned_after_mask])
         apply (erule range_cover.aligned)
        apply (rule is_aligned_weaken)
         apply (rule is_aligned_shiftl_self
                        [unfolded shiftl_t2n field_simps, simplified])
        apply simp
       apply simp
      apply (rule disjoint_subset[rotated])
       apply (frule valid_global_refsD'[THEN conjunct1], fastforce)
       apply (simp add: Int_ac)
      apply (clarsimp simp: no_simps word_and_le2)
     apply clarsimp
     apply (frule(1) invokeUntyped_proofs.slots_invD)
     apply (clarsimp simp: invokeUntyped_proofs_def cte_wp_at_ctes_of) 
     apply (drule(1) bspec)+
     apply clarsimp
    apply (clarsimp simp: no_simps word_and_le2)
   apply clarsimp
   apply (rule of_nat_power[where x = 5,simplified])
    apply (rule APIType_capBits_high)
     apply simp+
   done
qed

lemma invokeUntyped_Retype_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and ct_active' and
      valid_untyped_inv' (Retype cref ptr_base ptr newType us destSlots))
     (UNIV \<inter>  {s. freeRegionBase_' s = Ptr ptr} 
           \<inter>  {s. regionBase_' s = Ptr ptr_base } 
           \<inter>  {s. srcSlot_' s = Ptr cref}
           \<inter>  {s. newType_' s = object_type_from_H newType }
           \<inter>  {s. unat (userSize_' s) = us }
           \<inter>  \<lbrace>\<acute>destSlots = slot_range_C (cte_Ptr cnodeptr) start
                                          (of_nat (length destSlots)) \<and>
                (\<forall>n<length destSlots.
                    destSlots ! n = cnodeptr + (start + of_nat n) * 0x10)\<rbrace>)
     []
     (do invokeUntyped (Retype cref ptr_base ptr newType us destSlots);
         returnOk () od)
     (Call invokeUntyped_Retype_'proc)"
  apply (rule ccorres_name_pre)
  apply (case_tac "ptr = ptr_base")
   prefer 2
   apply (rule invokeUntyped_Retype_ccorres_side_case)
    apply simp+
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (frule ctes_of_valid',fastforce)
  apply (subgoal_tac
           "invokeUntyped_proofs s cref ptr_base newType us destSlots sz idx")
   prefer 2
   apply (clarsimp simp:invokeUntyped_proofs_def cte_wp_at_ctes_of)
  (* This is the main case involving deleteObjects. *)
  (* FIXME: proof very similar to invokeUntyped_Retype_ccorres_side_case. *)
  proof -
    fix s sz idx cte
    assume cover:
      "range_cover ptr_base sz  (APIType_capBits newType us) (length destSlots)"
    and proofs:
      "invokeUntyped_proofs s cref ptr_base newType us destSlots sz idx"
    and us_misc:
      "newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < us"
      "newType = APIObjectType apiobject_type.Untyped \<longrightarrow> 4 \<le> us \<and> us \<le> 30"
    and misc:
      "destSlots \<noteq> []" "ptr_base && ~~ mask sz = ptr_base" "ct_active' s"
      "sch_act_simple s" "invs' s "
      "ctes_of s cref = Some cte" "cteCap cte = UntypedCap ptr_base sz idx"
    note no_simps[simp del] = untyped_range.simps usable_untyped_range.simps
         atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
         Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
         usableUntypedRange.simps

    have us_misc':
      "(newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> us < 28)"
      using cover
      apply -
      apply (drule range_cover_sz')
      apply (clarsimp simp:APIType_capBits_def objBits_simps word_bits_conv)
      done

    have cte_size_inter_empty:
      "{cref..cref + 0xF} \<inter> {ptr_base..ptr_base + 2 ^ sz - 1} = {}"
      using cover misc
      apply -
      apply (rule disjoint_subset2[rotated])
      apply (erule(1) cte_size_inter_empty)
        apply (clarsimp simp:isCap_simps)
       apply (cut_tac invokeUntyped_proofs.cref_inv[OF proofs])
       apply simp
      apply simp
      done

    show
      "ccorresG rf_sr \<Gamma> (cintr \<currency> dc) 
         (liftxf errstate id (\<lambda>y. ()) ret__unsigned_long_') (\<lambda>s'. s' = s)
         (\<lbrace>\<acute>freeRegionBase = Ptr ptr_base\<rbrace> \<inter> \<lbrace>\<acute>regionBase = Ptr ptr_base\<rbrace> \<inter>
          \<lbrace>\<acute>srcSlot = cte_Ptr cref\<rbrace> \<inter>
          \<lbrace>\<acute>newType = object_type_from_H newType\<rbrace> \<inter>
          \<lbrace>unat \<acute>userSize = us\<rbrace> \<inter>
          \<lbrace>\<acute>destSlots = slot_range_C (cte_Ptr cnodeptr) start
                                     (of_nat (length destSlots)) \<and>
           (\<forall>n<length destSlots.
              destSlots ! n = cnodeptr + (start * 0x10 + of_nat n * 0x10))\<rbrace>)
         [] (invokeUntyped (Retype cref ptr_base ptr_base newType us destSlots)
             >>= returnOk)
            (Call invokeUntyped_Retype_'proc)"
      apply (cinit' lift: freeRegionBase_' regionBase_' srcSlot_' newType_'
                          userSize_' destSlots_'
                    simp: invokeUntyped_def bind_assoc when_def)
       apply (rule ccorres_symb_exec_l)
          apply (rule ccorres_move_c_guard_cte)
          apply csymbr
          apply (rule ccorres_abstract_cleanup)
          apply (rule_tac P = "rv = UntypedCap ptr_base sz idx"
                       in ccorres_gen_asm)
          apply (rule_tac P = "size_ign = of_nat sz" in ccorres_gen_asm2)
          apply (cut_tac unat_of_nat32[of sz])
           prefer 2
           using range_cover.sz[OF cover]
           apply (clarsimp simp: word_bits_def)
          apply (simp add: hrs_htd_update)
          apply (rule ccorres_Guard_Seq[where S=UNIV])?
          apply (ctac (c_lines 2) add: deleteObjects_ccorres
                              pre del: ccorres_Guard_Seq)
            apply csymbr
            apply (rule ccorres_symb_exec_r)
              apply (rule_tac xf'="\<lambda>s. totalObjectSize_' s"
                           in ccorres_abstract, ceqv)
              apply (rule_tac P="rv' = of_nat (shiftL (length destSlots)
                                              (APIType_capBits newType us))"
                           in ccorres_gen_asm2)
              apply csymbr
              apply (rule ccorres_move_c_guard_cte)
              apply (rule ccorres_Guard_Seq)+
              apply simp
              apply (ctac add: update_freeIndex)
                apply (ctac add: createNewObjects_ccorres[where sz = sz and
                           start = start and cnodeptr=cnodeptr and
                           num = "of_nat (length destSlots)"])
                  apply (rule ccorres_return_CE)
                    apply simp
                   apply simp
                  apply simp
                 apply wp
                apply clarsimp
                apply (vcg exspec=createNewObjects_modifies)
               apply (wp updateFreeIndex_invs_simple'[where cap = "UntypedCap ptr_base sz idx" and src = cref,simplified]
                         updateFreeIndex_pspace_no_overlap'[where cap = "UntypedCap ptr_base sz idx",simplified]
                         updateFreeIndex_caps_no_overlap''[where cap = "UntypedCap ptr_base sz idx",simplified]
                         updateFreeIndex_caps_overlap_reserved'[where cap = "UntypedCap ptr_base sz idx",simplified]
                         updateFreeIndex_descendants_range_in'[where cap = "UntypedCap ptr_base sz idx",simplified]
                         updateCap_weak_cte_wp_at hoare_vcg_ball_lift
                         freeIndexUpdate_ex_cte[where pcap = "UntypedCap ptr_base sz idx",simplified])
              apply clarsimp
              apply (vcg exspec=cap_untyped_cap_ptr_set_capFreeIndex_modifies)
             apply clarsimp
             apply vcg
            apply (rule conseqPre, vcg, clarsimp)
           apply (cut_tac cover us_misc proofs misc us_misc')
           apply (clarsimp simp: getFreeIndex_def conj_comms)
           apply (rule_tac Q = "\<lambda>r. invs' and sch_act_simple and ct_active' and
                    cte_wp_at' (\<lambda>c. cteCap c = UntypedCap ptr_base sz idx) cref and 
                    (\<lambda>s. \<forall>slot\<in>set destSlots. cte_wp_at' (\<lambda>c. cteCap c = NullCap) slot s) and
                    (\<lambda>s. \<forall>x\<in>set destSlots. ex_cte_cap_wp_to' (\<lambda>_. True) x s) and
                    pspace_no_overlap' ptr_base sz and 
                    (\<lambda>s. descendants_range_in' {ptr_base..(ptr_base && ~~ mask sz) + 2 ^ sz - 1} cref (ctes_of s))" in  hoare_strengthen_post)
            prefer 2
            apply (clarsimp simp: invs_valid_objs' invs_valid_pspace')
            apply (frule invokeUntyped_proofs.not_0_ptr)
            apply (clarsimp simp: valid_cap'_def shiftL_nat cte_wp_at_ctes_of
                                  range_cover.unat_of_nat_n)
            apply (rename_tac us sa ctea)
            apply (intro conjI)
                      apply (erule descendants_range_caps_no_overlapI')
                       apply (fastforce simp:cte_wp_at_ctes_of)
                      apply simp
                     apply (clarsimp dest!:
                                invokeUntyped_proofs.slots_invD[OF proofs])
                    apply (erule is_aligned_weaken[OF range_cover.aligned])
                    apply (clarsimp simp: APIType_capBits_low)
                   apply (rule_tac us1="unat userSize" in is_aligned_weaken
                            [OF _ APIType_capBits_low[where newType = newType]])
                     apply (simp add: is_aligned_def)
                     apply (drule range_cover.unat_of_nat_n_shift
                                  [OF _ le_refl])
                     apply (clarsimp simp: shiftl_t2n)
                    apply simp
                   apply simp
                  apply (frule range_cover.unat_of_nat_n_shift[OF _ le_refl])
                  apply (clarsimp simp: shiftl_t2n)
                  apply (frule range_cover.range_cover_n_le(2))
                  apply (drule nat_le_power_trans)
                   apply (simp add: range_cover.sz)
                  apply (simp add: field_simps)
                 apply (clarsimp dest!:
                            invokeUntyped_proofs.slots_invD[OF proofs])
                apply (drule_tac s=sa
                              in valid_global_refsD'[OF _ invs_valid_global'])
                 apply simp
                apply (clarsimp simp: Int_ac)
                apply (erule disjoint_subset2
                             [OF invokeUntyped_proofs.subset_stuff])
                apply simp
               apply (erule descendants_range_in_subseteq')
               apply (frule_tac x="of_nat (length destSlots) - 1"
                             in range_cover_bound'')
                apply simp
                apply (erule range_cover_not_zero[rotated])
                apply simp
               apply (clarsimp simp: no_simps field_simps)
              apply (frule_tac x="of_nat (length destSlots) - 1"
                            in range_cover_bound'')
               apply simp
               apply (erule range_cover_not_zero[rotated])
               apply simp
              apply (clarsimp simp: no_simps field_simps)
             apply simp
            apply (drule invokeUntyped_proofs.usableRange_disjoint)
            apply (clarsimp simp: field_simps mask_out_sub_mask)
           apply (wp deleteObjects_invs'[where p = cref]
                     deleteObjects_descendants[where p = cref]
                     deleteObjects_nosch
                     deleteObjects_st_tcb_at'[where p = cref]
                     Detype_R.deleteObjects_cte_wp_at'
                     hoare_vcg_ball_lift deleteObjects_cap_to'[where p = cref]
                  | simp add: sch_act_simple_def ct_in_state'_def | wps)+
          apply clarsimp
          apply vcg
         apply wp
        apply (wp getSlotCap_wp)
       apply simp
      apply (cut_tac misc us_misc' proofs us_misc
                     invokeUntyped_proofs.cref_inv[OF proofs])
      apply (clarsimp simp: cte_wp_at_ctes_of invokeUntyped_proofs_def
                            descendants_range'_def2 sch_act_simple_def
                            invs_valid_pspace' range_cover.sz)
      apply (rename_tac us s')
      apply (frule ctes_of_valid', fastforce)
      apply (clarsimp simp: valid_cap'_def capAligned_def ct_in_state'_def)
      apply (intro conjI)
          apply fastforce
         apply simp
        apply (fastforce simp: st_tcb_at'_def obj_at'_def)
       apply (clarsimp dest!: invokeUntyped_proofs.slots_invD[OF proofs])
      apply (erule(1) rf_sr_ctes_of_cliftE)
      apply (simp add:typ_heap_simps)
      apply (frule rf_sr_cpspace_relation)
      apply (frule cap_CL_lift[symmetric])
      apply (frule(2) rf_sr_cte_relation)
      apply (subst (asm) cap_untyped_cap_lift[THEN iffD1])
       apply (subst cap_get_tag_isCap[OF ccte_relation_ccap_relation])
        apply simp
       apply simp
      apply (simp add: cap_to_H_simps)
      apply (frule typ_clear_region_eq[rotated -1], simp+)
       apply (simp add: Int_ac cte_size_inter_empty)
      apply (clarsimp simp: range_cover.unat_of_nat_n
                            region_is_typeless_def[symmetric])
      apply (intro conjI impI allI)
           apply (rule of_nat_power[where x = 5,simplified])
            apply (rule APIType_capBits_high)
             apply (clarsimp simp: unat_of_nat32[where x=us] word_bits_def)+
          apply (clarsimp simp:getFreeIndex_def)
         apply (simp add: word_sle_def)
         apply (simp add: shiftL_nat word_bits_conv shiftl_t2n)
         apply (clarsimp dest!: range_cover_sz'
                          simp: unat_of_nat32 word_bits_def)
        apply (rule object_type_from_H_bound)
       apply (subst cap_get_tag_isCap)
        apply (erule ccte_relation_ccap_relation)
       apply (simp add:isCap_simps cap_to_H_def)
       done
   qed

lemma ccorres_returnOk_Basic:
  "\<lbrakk> \<And>\<sigma> s. (\<sigma>, s) \<in> sr \<Longrightarrow> r (Inr v) (xf (f s))
                   \<and> (\<sigma>, f s) \<in> sr \<rbrakk> \<Longrightarrow>
   ccorres_underlying sr \<Gamma> r xf arrel axf \<top> UNIV hs
      (returnOk v) (Basic f)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: returnOk_def return_def)
  done

lemma injection_handler_whenE:
  "injection_handler injf (whenE P f)
    = whenE P (injection_handler injf f)"
  by (simp add: whenE_def injection_handler_returnOk split: split_if)

lemma fromEnum_object_type_to_H:
  "fromEnum x = unat (object_type_from_H x)"
  apply (cut_tac eqset_imp_iff[where x=x, OF enum_surj])
  apply (simp add: fromEnum_def enum_object_type
                   enum_apiobject_type
                   object_type_from_H_def
                   "StrictC'_object_defs" "api_object_defs"
            split: split_if)
  apply (auto simp: "api_object_defs")
  done

lemma injection_handler_sequenceE:
  "injection_handler injf (sequenceE xs)
    = sequenceE (map (injection_handler injf) xs)"
  apply (induct xs, simp_all add: sequenceE_def)
   apply (simp add: injection_handler_returnOk)
  apply (simp add: injection_bindE[OF refl refl]
                   injection_handler_returnOk
                   Let_def)
  done

lemma getSlotCap_capAligned[wp]:
  "\<lbrace>valid_objs'\<rbrace> getSlotCap ptr \<lbrace>\<lambda>rv s. capAligned rv\<rbrace>"
  apply (rule hoare_strengthen_post, rule getSlotCap_valid_cap)
  apply (clarsimp simp: valid_capAligned)
  done

lemma ccorres_throwError_inl_rrel:
  "ccorres_underlying sr Gamm (inl_rrel r) xf arrel axf hs P P'
            (throwError v) c
   \<Longrightarrow> ccorres_underlying sr Gamm r xf (inl_rrel arrel) axf hs P P'
            (throwError v) c"
  apply (rule ccorresI')
  apply (erule(3) ccorresE)
    apply (simp add: throwError_def return_def)
   apply assumption
  apply (simp add: throwError_def return_def
                   unif_rrel_def split: split_if_asm)
  done

lemmas ccorres_return_C_errorE_inl_rrel
    = ccorres_throwError_inl_rrel[OF ccorres_return_C_errorE]

lemma mapME_ensureEmptySlot':
  "\<lbrace>P\<rbrace> 
  mapME (\<lambda>x. injection_handler Inl (ensureEmptySlot (f x))) slots
  \<lbrace>\<lambda>rva s. P s \<and> (\<forall>slot \<in> set slots. (\<exists>cte. cteCap cte = capability.NullCap \<and> ctes_of s (f slot) = Some cte))\<rbrace>, -"
  apply (induct slots arbitrary: P)
   apply simp
   apply wp 
  apply (rename_tac a slots P)
  apply (simp add: mapME_def sequenceE_def Let_def)
  apply (rule_tac Q="\<lambda>rv. P and (\<lambda>s. \<exists>cte. cteCap cte = capability.NullCap \<and> ctes_of s (f a) = Some cte)" in validE_R_sp) 
   apply (simp add: ensureEmptySlot_def unlessE_def) 
   apply (wp injection_wp_E[OF refl] getCTE_wp')
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule meta_allE)
  apply wp
  apply (fold validE_R_def)
  apply (erule hoare_post_imp_R)
  apply clarsimp
  done 

lemma mapME_ensureEmptySlot:
  "\<lbrace>\<top>\<rbrace> 
  mapME (\<lambda>x. injection_handler Inl (ensureEmptySlot (f x))) [S .e. (E::word32)] 
  \<lbrace>\<lambda>rva s. \<forall>slot. S \<le> slot \<and> slot \<le> E \<longrightarrow>
           (\<exists>cte. cteCap cte = capability.NullCap \<and> ctes_of s (f slot) = Some cte)\<rbrace>, -"
  apply (rule hoare_post_imp_R)
   apply (rule mapME_ensureEmptySlot')
  apply clarsimp
  done

lemma capCNodeRadix_CL_less_32:
  "cap_get_tag ccap = scast cap_cnode_cap \<Longrightarrow> capCNodeRadix_CL (cap_cnode_cap_lift ccap) < 32"
  apply (simp add: cap_cnode_cap_lift_def cap_lift_cnode_cap)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply simp
  done

lemmas unat_capCNodeRadix_CL_less_32
    = capCNodeRadix_CL_less_32[unfolded word_less_nat_alt, simplified]

lemmas capCNodeRadix_CL_less_32s
    = capCNodeRadix_CL_less_32 unat_capCNodeRadix_CL_less_32
      linorder_not_le[THEN iffD2, OF capCNodeRadix_CL_less_32]
      linorder_not_le[THEN iffD2, OF unat_capCNodeRadix_CL_less_32]

lemma TripleSuc:
  "Suc (Suc (Suc 0)) = 3"
  by simp

lemma case_sum_distrib:
  "case_sum a b x >>= f = case_sum (\<lambda>x. a x >>= f) (\<lambda>x. b x >>= f) x"
  by (case_tac x,simp+)

lemma alignUp_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. alignment_' s < 0x20 \<rbrace> Call alignUp_'proc
         \<lbrace>\<acute>ret__unsigned_long = alignUp (baseValue_' s) (unat (alignment_' s))\<rbrace>"
  apply vcg
  apply (simp add:alignUp_def2 mask_def field_simps)
  done

lemma checkFreeIndex_ccorres:
  "ccap_relation cp cap \<Longrightarrow>
  ccorresG rf_sr \<Gamma> (intr_and_se_rel \<currency> (\<lambda>r r'. r = unat (r' << 4))) (liftxf errstate (K (scast EXCEPTION_NONE)) id freeIndex_') 
  (cte_wp_at' (\<lambda>cte. (cteCap cte = cp \<and> isUntypedCap cp)) slot and valid_objs' and valid_mdb') UNIV hs
  (liftE $ constOnFailure (capFreeIndex cp) (doE y \<leftarrow> ensureNoChildren slot;
  returnOk 0 odE))
  (\<acute>status :== CALL ensureNoChildren(cte_Ptr slot);;
  (Cond \<lbrace>\<acute>status \<noteq> scast EXCEPTION_NONE\<rbrace> (\<acute>freeIndex :== CALL cap_untyped_cap_get_capFreeIndex(cap))
  (\<acute>freeIndex :== 0)))"
  apply (simp add: constOnFailure_def catch_def liftE_def bindE_bind_linearise bind_assoc case_sum_distrib)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_split_nothrow_case_sum)
        apply (ctac add:ensureNoChildren_ccorres)
       apply (ceqv)
       apply (rule ccorres_from_vcg[where P' = UNIV])
       apply (clarsimp simp:returnOk_def return_def bind_def)
       apply (rule conseqPre)
        apply vcg
       apply clarsimp
      apply simp
      apply (rule ccorres_from_vcg[where P'= UNIV])
      apply (clarsimp simp:return_def)
      apply (rule conseqPre)
       apply vcg
      apply clarsimp
      apply (rule context_conjI)
       apply (clarsimp simp:cap_get_tag_isCap)
       apply assumption
      apply (clarsimp simp:ccap_relation_def isCap_simps cap_untyped_cap_lift_def
             cap_lift_def cap_to_H_def
             split:if_splits)
     apply (rule ensureNoChildren_wp[where P = dc]) 
    apply clarsimp
    apply vcg
   apply (clarsimp simp:cte_wp_at_ctes_of rf_sr_def cstate_relation_def cpspace_relation_def Let_def)
   apply (rule cmap_relationE1,assumption+)
   apply (rule exI)+
   apply (rule conjI,assumption)
   apply (rule conjI,simp add:typ_heap_simps')
   apply (clarsimp simp:typ_heap_simps')
   apply (subst (asm) mdbNext_not_zero_eq_simpler[symmetric])
    apply (erule ccte_relation_cmdbnode_relation)
   apply (frule(2) valid_mdbD1')
   apply (drule_tac s'= s' in valid_mdb_cslift_next)
      apply (simp add:rf_sr_def Let_def cstate_relation_def cpspace_relation_def)
     apply simp 
    apply simp
   apply clarsimp
   apply (erule_tac y = c in cmap_relationE1)
    apply assumption
   apply (clarsimp simp:cmdb_node_relation_mdbNext[OF ccte_relation_cmdbnode_relation])
   apply (intro conjI exI,assumption)
    apply (erule(1) valid_capAligned[OF ctes_of_valid'])
   apply (erule(1) ctes_of_valid')
   done

lemma ccap_relation_untyped_CL_simps:
  "\<lbrakk>ccap_relation cp cap;isUntypedCap cp\<rbrakk>
   \<Longrightarrow> unat (capBlockSize_CL (cap_untyped_cap_lift cap)) = (capBlockSize cp)
       \<and> (capPtr_CL (cap_untyped_cap_lift cap)) = (capPtr cp)"
  apply (frule cap_get_tag_UntypedCap)
  apply (simp add:cap_get_tag_isCap)
  done

lemma valid_untyped_capBlockSize_misc:
  "\<lbrakk>s \<turnstile>' cp; isUntypedCap cp; (z::nat) \<le> capFreeIndex cp
   \<rbrakk> \<Longrightarrow> 2 ^ capBlockSize cp - z < 2 ^ word_bits
    \<and> of_nat (2^capBlockSize cp - z) = (2::word32) ^ capBlockSize cp - of_nat z"
  apply (clarsimp simp:valid_cap'_def isCap_simps)
  apply (rule le_less_trans[OF diff_le_self])
  apply (rule power_strict_increasing)
   apply (simp add:word_bits_def)
  apply simp
  done

lemma alternative_distrib:
  "(do r\<leftarrow>c; (a \<sqinter> b) od) = ((do c; a od) \<sqinter> (do c ; b od))"
  apply (rule ext)+
  apply (clarsimp simp:alternative_def bind_def split_def)
  apply force
  done

lemma setThreadStateRestart_ct_active':
  "\<lbrace>ct_active'\<rbrace> setThreadState Restart thread
  \<lbrace>\<lambda>rva s. ct_active' s\<rbrace>"
  apply (simp add:ct_in_state'_def)
  apply (rule hoare_pre)
  apply (wps)
  apply (wp sts_st_tcb_at'_cases)
  apply clarsimp
  done

lemma toEnum_object_type_to_H:
  "unat v \<le> (fromEnum::ArchTypes_H.object_type \<Rightarrow> nat) maxBound
  \<Longrightarrow> toEnum (unat v) = (object_type_to_H (v::word32))"
  apply (simp add:enum_object_type enum_apiobject_type object_type_to_H_def toEnum_def
                  maxBound_less_length)
  apply (clarsimp simp: Kernel_C_defs split:if_splits)
  apply unat_arith
  done

lemma unat_of_nat_APIType_capBits:
  "b \<le> 30
  \<Longrightarrow> unat (of_nat (APIType_capBits z b) ::word32) = APIType_capBits z b"
  apply (rule unat_of_nat32)
  apply (case_tac z)
  apply (clarsimp simp:invokeUntyped_proofs_def word_bits_conv APIType_capBits_def objBits_simps
    split: apiobject_type.splits)+
  done

lemma valid_untyped_inv'_D:
  "valid_untyped_inv' (Retype slot ptr_base ptr ty us slots) s
   \<Longrightarrow> APIType_capBits ty us < 32"
  apply (clarsimp simp:valid_untyped_inv'.simps)
  apply (drule range_cover_sz')
  apply (simp add:word_bits_def)
  done
  
lemma  object_type_from_to_H:
  "unat v \<le> (fromEnum::ArchTypes_H.object_type \<Rightarrow> nat) maxBound
         \<Longrightarrow> v = object_type_from_H (object_type_to_H v)"
  apply (simp add:toEnum_object_type_to_H[symmetric])
  apply (rule iffD1[OF word_unat.Rep_inject])
  apply (subst fromEnum_object_type_to_H[symmetric])
  apply (simp add:from_to_enum)
  done

lemma shiftR_gt0_le32:
  "\<lbrakk>0 < unat (of_nat (shiftR a b ));a < 2 ^ word_bits\<rbrakk> \<Longrightarrow> b< 32"
  apply (rule ccontr)
  apply (clarsimp simp:not_less shiftR_nat)
  apply (subst (asm) div_less)
   apply (erule less_le_trans)
   apply (rule power_increasing)
    apply (simp add:word_bits_def)+
  done

lemma shiftr_overflow:
  "32\<le> a \<Longrightarrow> (b::word32) >> a = 0"
  apply (word_bitwise)
  apply simp
  done

lemma impI':
  "(\<not> B \<Longrightarrow> \<not> A) \<Longrightarrow> A \<longrightarrow> B"
  by auto

lemma decodeUntypedInvocation_ccorres_helper:
notes TripleSuc[simp]
notes valid_untyped_inv'.simps[simp del] tl_drop_1[simp]
shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) 
              and sch_act_simple and ct_active'
              and valid_cap' cp and K (isUntypedCap cp)
              and cte_wp_at' (\<lambda>cte. cteCap cte = cp) slot
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v).
                              ex_nonz_cap_to' y s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v)
              and sysargs_rel args buffer)
       (UNIV 
             \<inter> {s. label_' s = label}
             \<inter> {s. unat (length_' s) = length args}
             \<inter> {s. ccap_relation cp (cap_' s)}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. extraCaps_' s = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       []
       ((doE uinv \<leftarrow> decodeUntypedInvocation label args slot cp (map fst extraCaps);
           liftE (stateAssert (valid_untyped_inv' uinv) []); returnOk uinv odE)
           >>= invocationCatch thread isBlocking isCall InvokeUntyped) 
  (Call decodeUntypedInvocation_'proc)"
  apply (rule ccorres_name_pre)
  apply (cinit' lift: label_' length_' cap_' slot_' extraCaps_' call_' buffer_'
                simp: decodeUntypedInvocation_def list_case_If2
                      invocation_eq_use_types)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: unlessE_def throwError_bind invocationCatch_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp del: Collect_const cong: call_ignore_cong)
   apply csymbr
   apply (simp add: if_1_0_0 word_less_nat_alt
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_Cond_rhs_Seq)
    apply simp
    apply (rule ccorres_cond_true_seq)
    apply (simp add: throwError_bind invocationCatch_def
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_Guard_Seq)+
   apply csymbr
   apply (simp add: interpret_excaps_test_null
                    excaps_map_def if_1_0_0
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
     apply vcg
    apply (rule conseqPre, vcg)
    apply (clarsimp simp: throwError_bind invocationCatch_def
                   split: list.split,
           simp add: throwError_def return_def
                     syscall_error_rel_def exception_defs
                     syscall_error_to_H_cases)
   apply (simp add: list_case_helper[OF neq_Nil_lengthI]
                    list_case_helper
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_add_return)
   apply (simp only: )
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (simp only: )
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply (rule ccorres_add_return)
       apply (simp only: )
       apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
         apply (rule ccorres_add_return)
         apply (simp only: )
         apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=3 and buffer=buffer])
           apply (rule ccorres_add_return)
           apply (simp only: )
           apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=4 and buffer=buffer])
             apply (rule ccorres_add_return)
             apply (simp only: )  
             apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=5 and buffer=buffer])
               apply (rule ccorres_Guard_Seq)+
               apply csymbr
               apply (simp add: invocationCatch_use_injection_handler
                                injection_bindE[OF refl refl]
                                injection_handler_whenE
                                rangeCheck_def unlessE_whenE
                                injection_liftE [OF refl]
                                injection_handler_throwError
                                bindE_assoc length_ineq_not_Nil
                                injection_handler_If
                          cong: StateSpace.state.fold_congs globals.fold_congs
                           del: Collect_const)
               apply (rule ccorres_split_when_throwError_cond
                               [where Q=\<top> and Q'=\<top>, rotated -1])
                  apply vcg
                 apply (simp add: seL4_ObjectTypeCount_def maxBound_is_length)
                 apply (subst hd_conv_nth, clarsimp)
                 apply (clarsimp simp: enum_object_type enum_apiobject_type
                                       word_le_nat_alt)
                 apply arith
                apply (rule syscall_error_throwError_ccorres_n)
                apply (simp add: syscall_error_to_H_cases)
               apply (rule ccorres_Guard_Seq)+
               apply (rule ccorres_split_when_throwError_cond
                               [where Q=\<top> and Q'=\<top>, rotated -1])
                  apply vcg
                 apply (clarsimp simp: word_size Collect_const_mem
                                       fromIntegral_def integral_inv
                                       hd_drop_conv_nth2 word_le_nat_alt)
                 apply arith
                apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                apply (rule allI, rule conseqPre, vcg)
                apply (clarsimp simp: throwError_def return_def
                                      syscall_error_rel_def exception_defs
                                      syscall_error_to_H_cases)
                apply (simp add: word_size word_sle_def)
               apply (simp add: fromIntegral_def integral_inv
                                hd_drop_conv_nth2
                           del: Collect_const)
               apply (rule ccorres_split_when_throwError_cond
                               [where Q=\<top> and Q'=\<top>, rotated -1])
                  apply vcg
                 apply (clarsimp simp: Collect_const_mem unat_eq_0
                                       linorder_not_less
                                       hd_conv_nth length_ineq_not_Nil)
                 apply (simp add: toEnum_eq_to_fromEnum_eq
                                  fromEnum_object_type_to_H
                                  object_type_from_H_def
                                  fromAPIType_def ArchTypes_H.fromAPIType_def)
                apply (rule syscall_error_throwError_ccorres_n)
                apply (simp add: syscall_error_to_H_cases)
               apply (rule ccorres_split_when_throwError_cond
                               [where Q=\<top> and Q'=\<top>, rotated -1])
                  apply vcg
                 apply (clarsimp simp: Collect_const_mem unat_eq_0
                                       linorder_not_less
                                       hd_conv_nth length_ineq_not_Nil
                                       toEnum_eq_to_fromEnum_eq)
                 apply (simp add: fromEnum_object_type_to_H
                                  object_type_from_H_def
                                  fromAPIType_def ArchTypes_H.fromAPIType_def)
                apply (rule syscall_error_throwError_ccorres_n)
                apply (simp add: syscall_error_to_H_cases)
                apply (rule_tac xf'="nodeCap_'"
                             and r'="\<lambda>rv rv'. ccap_relation rv rv' \<and> unat (args ! 3) \<le> word_bits"
                          in ccorres_splitE)
                    apply (rule ccorres_cond2[where R=\<top>])
                      apply (clarsimp simp add: unat_eq_0 )
                     apply (rule_tac P="args ! 3 = 0" in ccorres_gen_asm)
                     apply (rule ccorres_move_c_guard_cte)
                     apply (simp add: injection_handler_returnOk)
                     apply (rule ccorres_nohs)
                     apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
                     apply (rule ccorres_seq_skip'[THEN iffD1])
                     apply ctac
                       apply (rule ccorres_assert2)
                       apply (rule_tac P'="{s. nodeCap_' s = nodeCap}" in ccorres_from_vcg[where P=\<top>])
                       apply (rule allI, rule conseqPre, vcg)
                       apply (clarsimp simp: returnOk_def return_def hd_conv_nth)
                      apply (wp hoare_drop_imps)
                     apply vcg
                    apply (simp add: split_def injection_bindE[OF refl refl]
                                del: Collect_const)
                    apply (rule ccorres_rhs_assoc)+
                    apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
                    apply (rule ccorres_move_c_guard_cte)
                    apply ctac
                      apply (rule ccorres_assert2)
                      apply (ctac add: ccorres_injection_handler_csum1
                                        [OF lookupTargetSlot_ccorres,
                                            unfolded lookupTargetSlot_def])
                         apply (simp add: injection_liftE[OF refl])
                         apply (simp add: liftE_liftM o_def split_def withoutFailure_def
                                          hd_drop_conv_nth2 numeral_eqs[symmetric])
                         apply (rule ccorres_nohs)
                         apply (rule ccorres_getSlotCap_cte_at)
                         apply (rule ccorres_move_c_guard_cte)
                         apply ctac
                        apply simp
                        apply (rule ccorres_split_throws, simp?,
                               rule ccorres_return_C_errorE_inl_rrel, simp+)
                        apply vcg
                       apply simp
                       apply wp
                      apply (simp add: all_ex_eq_helper)
                      apply (vcg exspec=lookupTargetSlot_modifies)
                     apply simp
                     apply (wp hoare_drop_imps)
                    apply (simp add: hd_conv_nth)
                    apply vcg
                   apply ceqv
                  apply (rule_tac P="\<lambda>_. capAligned rv" in ccorres_cross_over_guard)
                  apply csymbr
                  apply (elim conjE)
                  apply (simp add: if_1_0_0 cap_get_tag_isCap
                                    cap_case_CNodeCap_True_throw
                                    injection_handler_whenE
                                    injection_handler_throwError
                               del: Collect_const)
                  apply (rule ccorres_Cond_rhs_Seq)
                    apply simp
                    apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
                     apply vcg
                    apply (rule conseqPre, vcg)
                    apply (clarsimp simp: throwError_def return_def
                                          syscall_error_rel_def exception_defs
                                          syscall_error_to_H_cases)
                    apply (simp add: lookup_fault_missing_capability_lift
                                     hd_drop_conv_nth2 numeral_eqs[symmetric])
                    apply (rule le_32_mask_eq)
                    apply (simp add: word_bits_def word_le_nat_alt)
                   apply simp
                   apply csymbr
                   apply (rule ccorres_Guard_Seq)
                   apply csymbr
                   apply (rule ccorres_split_when_throwError_cond
                                   [where Q=\<top> and Q'=\<top>, rotated -1])
                      apply vcg
                     apply (clarsimp simp: Collect_const_mem cap_get_tag_isCap[symmetric])
                     apply (drule(1) cap_get_tag_to_H)
                     apply (clarsimp simp: linorder_not_le)
                    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                    apply (rule allI, rule conseqPre, vcg)
                    apply (clarsimp simp: throwError_def return_def
                                          syscall_error_rel_def exception_defs
                                          syscall_error_to_H_cases)
                    apply (simp add: cap_get_tag_isCap[symmetric])
                    apply (drule(1) cap_get_tag_to_H)
                    apply clarsimp
                   apply (rule ccorres_split_when_throwError_cond
                                   [where Q=\<top> and Q'=\<top>, rotated -1])
                      apply vcg
                     apply (clarsimp simp:)
                     apply (simp add: retypeFanOutLimit_def word_le_nat_alt
                                      linorder_not_le)
                     apply (auto simp: linorder_not_le unat_eq_0)[1]
                    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                    apply (rule allI, rule conseqPre, vcg)
                    apply (clarsimp simp: throwError_def return_def
                                          syscall_error_rel_def exception_defs
                                          syscall_error_to_H_cases)
                    apply (simp add: retypeFanOutLimit_def)
                   apply (rule ccorres_split_when_throwError_cond
                                   [where Q=\<top> and Q'=\<top>, rotated -1])
                      apply vcg
                     apply (clarsimp simp: numeral_eqs[symmetric]
                                           word_le_nat_alt linorder_not_le
                                           cap_get_tag_isCap[symmetric])
                     apply (drule(1) cap_get_tag_to_H)
                     apply clarsimp
                    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                    apply (rule allI, rule conseqPre, vcg)
                    apply (clarsimp simp: throwError_def return_def
                                          syscall_error_rel_def exception_defs
                                          syscall_error_to_H_cases)
                    apply (simp add: cap_get_tag_isCap[symmetric])
                    apply (drule(1) cap_get_tag_to_H)
                    apply (clarsimp)
                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply (simp add: locateSlot_conv mapM_return liftE_bindE
                                    injection_handler_sequenceE mapME_x_sequenceE
                                    whileAnno_def injection_bindE[OF refl refl]
                                    bindE_assoc injection_handler_returnOk)
                   apply csymbr
                   apply (simp add: liftE_bindE[symmetric])
                   apply (rule_tac P="capAligned rv" in ccorres_gen_asm)
                   apply (subgoal_tac "args ! 5 \<le> args ! 4 + args ! 5")
                    prefer 2
                    apply (clarsimp simp: numeral_eqs[symmetric])
                    apply (subst field_simps, erule plus_minus_no_overflow_ab)
                    apply (erule order_trans)
                    apply (rule order_less_imp_le, rule word_power_less_1)
                    apply (clarsimp simp: capAligned_def isCap_simps word_bits_def)
                   apply (rule ccorres_splitE)
                       apply (rule ccorres_sequenceE_while_gen'
                                     [where i="unat (args ! 4)" and xf'=xfdc
                                       and xf_update="i_'_update" and xf="i_'"
                                       and r'=dc and F="\<top>\<top>" and Q=UNIV])
                             apply simp
                             apply (rule ccorres_guard_imp2)
                              apply (rule ccorres_add_returnOk)
                              apply (ctac add: ccorres_injection_handler_csum1
                                                  [OF ensureEmptySlot_ccorres])
                                 apply (simp add: ccorres_cond_iffs returnOk_def)
                                 apply (rule ccorres_return_Skip')
                                apply (simp add: ccorres_cond_iffs inl_rrel_inl_rrel)
                                apply (rule ccorres_return_C_errorE_inl_rrel,
                                       simp+)[1]
                               apply wp
                              apply (simp add: all_ex_eq_helper)
                              apply (vcg exspec=ensureEmptySlot_modifies)
                             apply (clarsimp simp: upto_enum_word
                                            split: split_if_asm simp del: upt.simps)
                             apply (simp add: cte_level_bits_def field_simps size_of_def
                                              numeral_eqs[symmetric])
                             apply (simp add: cap_get_tag_isCap[symmetric])
                             apply (drule(1) cap_get_tag_to_H)
                             apply simp
                            apply (clarsimp simp add: upto_enum_word
                                            simp del: upt.simps)
                            apply (simp add: word_less_nat_alt[symmetric] numeral_eqs[symmetric])
                            apply (simp add: Suc_unat_diff_1)
                            apply (subst iffD1 [OF unat_plus_simple])
                             apply (erule iffD2 [OF olen_add_eqv])
                            apply simp
                           apply (rule conseqPre, vcg exspec=ensureEmptySlot_modifies)
                           apply clarsimp
                          apply wp
                         apply (simp only: word_bits_def[symmetric])
                         apply clarsimp
                         apply (simp add: upto_enum_word numeral_eqs[symmetric]
                                          Suc_unat_diff_1
                                     del: upt.simps)
                         apply (subst(asm) olen_add_eqv[symmetric])
                         apply (simp add: iffD1 [OF unat_plus_simple])
                         apply (simp add: iffD1 [OF unat_plus_simple, symmetric])
                         apply (simp only: word_bits_def)
                         apply (rule unat_lt2p)
                        apply simp
                       apply simp
                      apply (rule ceqv_refl)
                     apply (ctac (c_lines 2) add:checkFreeIndex_ccorres[unfolded fun_app_def])
                        apply (rule_tac P = "rvb \<le> (capFreeIndex cp)" in ccorres_gen_asm)
                        apply csymbr
                        apply (rule ccorres_Guard_Seq)+
                        apply csymbr+
                        apply (rule ccorres_Guard_Seq)+
                        apply csymbr
                        apply (rule ccorres_Guard_Seq)+
                        apply csymbr
                        apply (rule ccorres_symb_exec_r)
                         apply (rule_tac xf'=ret__int_' in ccorres_abstract, ceqv)
                         apply (rule_tac P = "rv'b = (if (unat (2 ^ capBlockSize cp - (xfdc << 4) 
                           >> (APIType_capBits (toEnum (unat (hd args))) (unat (args ! Suc 0))))
                           < unat (args ! 5)) then 1 else 0)" in ccorres_gen_asm2)
                         apply (rule_tac
                           ccorres_split_when_throwError_cond[where Q = \<top> and Q' = \<top>])
                            apply (clarsimp simp: ccap_relation_untyped_CL_simps shiftL_nat
                              valid_untyped_capBlockSize_misc
                              of_nat_shiftR)
                            apply (clarsimp simp:toEnum_object_type_to_H 
                              unat_of_nat_APIType_capBits word_size hd_conv_nth length_ineq_not_Nil
                              split:if_splits)
                          apply (rule syscall_error_throwError_ccorres_n)
                          apply (clarsimp simp: syscall_error_rel_def
                            ccap_relation_untyped_CL_simps shiftL_nat
                            syscall_error_to_H_cases valid_untyped_capBlockSize_misc)
                         apply csymbr
                         apply (simp (no_asm) add:liftE_bindE)
                         apply (rule ccorres_symb_exec_l)
                            apply (simp (no_asm) add: ccorres_invocationCatch_Inr split_def
                              performInvocation_def liftE_bindE bind_assoc)
                            apply (ctac add: setThreadState_ccorres)
                              apply csymbr
                              apply (rule ccorres_trim_returnE, (simp (no_asm))+)
                              apply (simp (no_asm) add: o_def dc_def[symmetric] 
                                 bindE_assoc id_def[symmetric] bind_bindE_assoc)
                              apply (simp (no_asm) only:alternative_distrib)
                              apply (rule ccorres_alternative2)
                              apply (rule ccorres_call)
                                 apply (rule_tac cnodeptr="capCNodePtr rv" in invokeUntyped_Retype_ccorres[where start = "args!4"])
                                apply simp
                               apply simp
                              apply simp
                             apply (wp sts_invs_minor' setThreadStateRestart_ct_active' sts_valid_untyped_inv')
                            apply (clarsimp simp: ccap_relation_untyped_CL_simps shiftL_nat
                             toEnum_object_type_to_H unat_of_nat_APIType_capBits word_size
                             valid_untyped_capBlockSize_misc getFreeRef_def hd_conv_nth length_ineq_not_Nil)
                            apply (rule_tac conseqPost[where A' = "{}" and Q' = UNIV])
                              apply (vcg exspec=setThreadState_modifies)
                             apply (clarsimp simp:object_type_from_to_H cap_get_tag_isCap)
                             apply (frule_tac cap = rv in cap_get_tag_to_H(5))
                              apply (simp add:cap_get_tag_isCap)
                             apply (case_tac slots,simp)
                             apply (simp add:field_simps Suc_unat_diff_1)
                             apply (frule iffD2[OF olen_add_eqv])
                             apply (clarsimp simp: unat_plus_simple[THEN iffD1])
                             apply (subst upto_enum_word)
                             apply (subst nth_map_upt)
                              apply (clarsimp simp:field_simps Suc_unat_diff_1 unat_plus_simple[THEN iffD1])
                             apply (clarsimp simp:cte_level_bits_def)
                            apply simp
                           apply wp
                           apply simp
                          apply (simp (no_asm))
                          apply (rule hoare_strengthen_post[OF stateAssert_sp])
                          apply clarsimp
                          apply assumption
                         apply simp
                        apply clarsimp
                        apply vcg
                       apply clarsimp
                       apply vcg
                      apply clarsimp
                      apply (rule conseqPre,vcg,clarsimp)
                     apply (rule ccorres_guard_imp
                         [where Q =\<top> and Q' = UNIV,rotated],assumption+)
                     apply (simp add: o_def)
                    apply (simp add: liftE_validE)
                    apply (rule checkFreeIndex_wp)
                   apply (clarsimp simp: ccap_relation_untyped_CL_simps shiftL_nat cap_get_tag_isCap
                        toEnum_object_type_to_H unat_of_nat_APIType_capBits word_size
                        valid_untyped_capBlockSize_misc getFreeRef_def hd_conv_nth length_ineq_not_Nil)
                   apply (rule_tac Q' ="{sa. 
                        ksCurThread_' (globals sa) = tcb_ptr_to_ctcb_ptr (ksCurThread s)}" in conseqPost[where 
                         A' = "{}"])
                     apply vcg
                     apply (clarsimp simp:toEnum_object_type_to_H not_le word_sle_def 
                        enum_apiobject_type enum_object_type maxBound_is_length
                       unat_of_nat_APIType_capBits word_size hd_conv_nth length_ineq_not_Nil
                       not_less word_le_nat_alt split:if_splits)
                    apply (intro conjI allI)
                     apply (clarsimp simp:shiftL_nat isCap_simps valid_cap_simps',simp add:word_bits_def)
                     apply (rule ccontr)
                     apply (clarsimp simp:not_less shiftr_overflow)
                    apply (clarsimp simp:shiftL_nat isCap_simps valid_cap_simps' word_bits_def)
                    apply (intro conjI impI)
                     apply (clarsimp simp:ThreadState_Restart_def not_less mask_def split:split_if_asm)
                    apply (rule of_nat_power[where x = 5,simplified])
                     apply (rule ccontr)
                     apply (simp add:not_less shiftr_overflow unat_eq_0)
                    apply simp
                   apply simp
                  apply (rule_tac Q'="\<lambda>r. cte_wp_at' (\<lambda>cte. cteCap cte = cp) slot
                      and invs' and  (\<lambda>s. ksCurThread s = thread) and 
                      sch_act_simple and ct_active'" in hoare_post_imp_R)
                   prefer 2
                   apply (clarsimp simp:invs_valid_objs' invs_mdb'
                      invs_queues ct_in_state'_def pred_tcb_at')
                   apply (subgoal_tac "ksCurThread s \<noteq> ksIdleThread sa")
                    prefer 2
                    apply clarsimp
                    apply (frule st_tcb_at_idle_thread',fastforce)
                    apply (clarsimp simp:valid_idle'_def)
                   apply (clarsimp simp:st_tcb_at'_def obj_at'_def
                       invs'_def valid_state'_def)
                   apply (subgoal_tac "tcbState obja \<noteq> Inactive \<and> \<not> idle' (tcbState obja)")
                    prefer 2
                    apply (rule conjI, clarsimp)
                    apply (clarsimp dest!:invs_valid_idle')
                   apply (subgoal_tac "tcb_st_refs_of' (tcbState obja) = {}")
                    prefer 2
                    apply fastforce (* slow fastforce *)
                   apply (clarsimp split:if_splits simp:not_less toEnum_object_type_to_H 
                             word_size hd_conv_nth length_ineq_not_Nil)
                   apply (case_tac "tcbState obja", (simp add: runnable'_def valid_tcb_state'_def)+)
                  apply (wp mapME_wp'[unfolded mapME_def])
                  apply (rule hoare_pre)
                   apply (rule validE_R_validE)
                   apply (wp injection_wp_E[OF refl])
                  apply clarsimp
                 apply (simp add: ccHoarePost_def xfdc_def)
                 apply (simp only: whileAnno_def[where I=UNIV and V=UNIV, symmetric])
                 apply (rule_tac V=UNIV
                                in HoarePartial.reannotateWhileNoGuard)
                 apply (vcg exspec=ensureEmptySlot_modifies)
                  prefer 2
                  apply clarsimp
                  apply (subst (asm) mem_Collect_eq, assumption)
                 apply clarsimp
                apply clarsimp
                apply (wp injection_wp_E[OF refl] 
                          getSlotCap_capAligned | wp_once hoare_drop_imps)+
               apply (simp del: Collect_const)
               apply (vcg exspec=lookupTargetSlot_modifies)
              apply simp
              apply wp
             apply (simp add: all_ex_eq_helper)
             apply (vcg exspec=getSyscallArg_modifies)
            apply simp
            apply wp
           apply simp
           apply (vcg exspec=getSyscallArg_modifies)
          apply simp
          apply wp
         apply simp
         apply (vcg exspec=getSyscallArg_modifies)
        apply simp
        apply wp
       apply simp
       apply (vcg exspec=getSyscallArg_modifies)
      apply simp
      apply wp
      apply simp
      apply (vcg exspec=getSyscallArg_modifies)
     apply simp
    apply wp
   apply simp
   apply (vcg exspec=getSyscallArg_modifies)
  apply clarsimp
  apply (clarsimp simp: hd_drop_conv_nth2 hd_conv_nth neq_Nil_lengthI
                        ct_in_state'_def pred_tcb_at'
                        rf_sr_ksCurThread mask_eq_iff_w2p
                        "StrictC'_thread_state_defs" numeral_eqs[symmetric]
                        cap_get_tag_isCap cte_wp_at_ctes_of
                        unat_eq_0 ccHoarePost_def)
  apply (rule conjI)
   apply (clarsimp simp: linorder_not_less isCap_simps)
   apply (clarsimp simp: sysargs_rel_to_n)
   apply (rule conjI, clarsimp)
   apply (clarsimp simp: ArchTypes_H.fromAPIType_def Types_H.fromAPIType_def)
   apply (subgoal_tac "unat (args ! Suc 0) < word_bits")
    prefer 2
    apply (erule le_less_trans)
    apply (simp add: word_size fromIntegral_def fromInteger_nat toInteger_nat word_bits_def)
   apply (clarsimp simp: excaps_map_def neq_Nil_conv excaps_in_mem_def
                         slotcap_in_mem_def cte_wp_at_ctes_of
                         valid_capAligned[OF ctes_of_valid'] invs_valid_objs'
                  dest!: interpret_excaps_eq)
   apply (simp only: word_bits_def unat_lt2p)
  apply (frule interpret_excaps_eq)
  apply (clarsimp simp: if_1_0_0 word_less_nat_alt neq_Nil_conv
                        mask_def[where n=4] excaps_map_def
                        ccap_rights_relation_def word_sle_def
                        rightsFromWord_wordFromRights
                        excaps_in_mem_def slotcap_in_mem_def
                        signed_shift_guard_simpler_32
                        extra_sle_sless_unfolds
                 elim!: inl_inrE
              simp del: rf_sr_upd_safe)
  apply (clarsimp simp:cap_get_tag_isCap[symmetric])
  apply (rule conjI)
   apply (clarsimp simp: cap_get_tag_isCap[symmetric]
     capCNodeRadix_CL_less_32s rf_sr_ksCurThread not_le
                  elim!: inl_inrE)
   apply (drule(1) cap_get_tag_to_H)+
   apply (clarsimp simp: isCap_simps capAligned_def[unfolded capUntypedPtr_def, split_simps capability.split]
                         objBits_simps word_bits_def)
   apply (rule rf_sr_ctes_of_cliftE,assumption+)
   apply (intro exI)+
   apply (rule conjI,assumption)
   apply (rule conjI,erule(2) rf_sr_cte_relation)
   apply (frule(1) h_t_valid_and_cslift_and_c_guard_field_mdbNext_CL[rotated -1])
     apply (clarsimp simp:cte_wp_at_ctes_of)
    apply fastforce
   apply (clarsimp simp:typ_heap_simps)
   apply (frule_tac p = slot in valid_mdb_ctes_of_next[rotated])
     apply simp
    apply fastforce
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (frule_tac src = "(mdbNext_CL (cteMDBNode_CL ctel'))" in  rf_sr_cte_relation)
     apply simp
    apply simp
   apply (intro exI conjI,assumption)
   apply (erule valid_capAligned[OF ctes_of_valid'])
    apply fastforce
   apply simp
 apply (clarsimp elim!:inl_inrE)
 apply (drule(1) cap_get_tag_to_H)+
  apply (rule conjI)
   apply (clarsimp simp: cap_get_tag_isCap[symmetric]
     capCNodeRadix_CL_less_32s rf_sr_ksCurThread not_le
                  elim!: inl_inrE)
   apply (rule rf_sr_ctes_of_cliftE,assumption+)
   apply (intro exI)+
   apply (rule conjI,assumption)
    apply (rule conjI,erule(2) rf_sr_cte_relation)
    apply (frule(1) h_t_valid_and_cslift_and_c_guard_field_mdbNext_CL[rotated -1])
      apply (clarsimp simp:cte_wp_at_ctes_of simp del: rf_sr_upd_safe)
     apply fastforce
    apply (clarsimp simp:typ_heap_simps simp del: rf_sr_upd_safe)
   apply (frule_tac p = slot in valid_mdb_ctes_of_next[rotated])
     apply (simp del: rf_sr_upd_safe)
    apply fastforce
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (frule_tac src = "(mdbNext_CL (cteMDBNode_CL ctel'))" in  rf_sr_cte_relation)
     apply simp
    apply simp
   apply (intro exI conjI,assumption)
   apply (erule valid_capAligned[OF ctes_of_valid'])
    apply fastforce
   apply simp
  apply (clarsimp simp: cap_get_tag_isCap[symmetric])
  apply (drule(1) cap_get_tag_to_H)+
  apply (clarsimp simp: capAligned_def objBits_simps word_bits_def)
  done

lemma decodeUntypedInvocation_ccorres:
notes TripleSuc[simp]
notes valid_untyped_inv'.simps[simp del]
shows
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) 
              and sch_act_simple and ct_active'
              and valid_cap' cp and K (isUntypedCap cp)
              and cte_wp_at' (\<lambda>cte. cteCap cte = cp) slot
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v).
                              ex_nonz_cap_to' y s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps.
                             s \<turnstile>' fst v)
              and sysargs_rel args buffer)
       (UNIV 
             \<inter> {s. label_' s = label}
             \<inter> {s. unat (length_' s) = length args}
             \<inter> {s. ccap_relation cp (cap_' s)}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. extraCaps_' s = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       []
       (decodeUntypedInvocation label args slot cp (map fst extraCaps)
           >>= invocationCatch thread isBlocking isCall InvokeUntyped) 
  (Call decodeUntypedInvocation_'proc)"
  apply (rule ccorres_name_pre)
  apply (clarsimp simp:isCap_simps)
  apply (rule ccorres_guard_imp2)
   apply (rule monadic_rewrite_ccorres_assemble)
    apply (rule_tac isBlocking=isBlocking and isCall=isCall and buffer=buffer
                in decodeUntypedInvocation_ccorres_helper[unfolded K_def])
    apply assumption
   apply (rule monadic_rewrite_transverse)
    apply (rule monadic_rewrite_bind_head)
    apply (rule monadic_rewrite_bindE[OF monadic_rewrite_refl])
     apply (simp add: liftE_bindE stateAssert_def2 bind_assoc)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule_tac P=x in monadic_rewrite_gen_asm)
      apply simp
      apply (rule monadic_rewrite_refl)
     apply (wp | simp)+
   apply (simp add: gets_bind_ign)
   apply (rule monadic_rewrite_refl)
  apply (clarsimp simp: ex_cte_cap_wp_to'_def excaps_in_mem_def)
  apply (drule(1) bspec)+
  apply (rule_tac x = b in exI)
  apply (clarsimp simp:slotcap_in_mem_def cte_wp_at_ctes_of)
  done

end
end
