(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Invoke_C
imports Recycle_C "CLib.MonadicRewrite_C"
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
              (simp add: typ_heap_simps')+, simp_all?)[1]
        apply (rule ball_tcb_cte_casesI, simp+)
       apply (simp add: ctcb_relation_def)
      apply (ctac(no_vcg) add: isRunnable_ccorres)
       apply (rule ccorres_split_nothrow_novcg_dc)
          apply (simp add: when_def to_bool_def del: Collect_const)
          apply (rule ccorres_cond2[where R=\<top>], simp add: Collect_const_mem)
           apply (ctac add: tcbSchedEnqueue_ccorres)
          apply (rule ccorres_return_Skip)
         apply (simp add: when_def)
         apply (rule_tac R="\<lambda>s. curThread = ksCurThread s"
                    in ccorres_cond2)
           apply (clarsimp simp: rf_sr_ksCurThread)
          apply (ctac add: rescheduleRequired_ccorres)
         apply (rule ccorres_return_Skip')
        apply simp
        apply (wp hoare_drop_imps weak_sch_act_wf_lift_linear)
       apply (simp add: guard_is_UNIV_def)
      apply simp
      apply wp
     apply (rule_tac Q'="\<lambda>_. all_invs_but_sch_extra and tcb_at' t and sch_act_simple
                            and (\<lambda>s. curThread = ksCurThread s)"
              in hoare_strengthen_post)
      apply (wp threadSet_all_invs_but_sch_extra)
     apply (fastforce simp: valid_pspace_valid_objs' st_tcb_at_def[symmetric]
                            sch_act_simple_def st_tcb_at'_def weak_sch_act_wf_def
                     split: if_splits)
    apply (simp add: guard_is_UNIV_def)
   apply (rule_tac Q'="\<lambda>_. invs' and tcb_at' t and sch_act_simple and (\<lambda>s. curThread = ksCurThread s)"
            in hoare_strengthen_post)
    apply (wp weak_sch_act_wf_lift_linear tcbSchedDequeue_not_queued
              hoare_vcg_imp_lift hoare_vcg_all_lift)
   apply (clarsimp simp: invs'_def valid_pspace'_def valid_state'_def)
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
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. invLabel_' s = lab}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeDomainInvocation lab args extraCaps
           >>= invocationCatch thread isBlocking isCall (uncurry InvokeDomain))
  (Call decodeDomainInvocation_'proc)"
  supply gen_invocation_type_eq[simp]
  apply (cinit' lift: length___unsigned_long_' current_extra_caps_' call_' invLabel_' buffer_'
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
     apply (simp add: hd_conv_nth word_le_nat_alt)
     apply (simp add: unat_scast_numDomains)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: throwError_bind invocationCatch_def
                       hd_conv_nth word_le_nat_alt unat_numDomains_to_H
                 cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (simp add: null_def excaps_map_def unat_numDomains_to_H)
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

  apply (clarsimp simp: valid_tcb_state'_def invs_valid_objs'
                        invs_sch_act_wf' ct_in_state'_def pred_tcb_at'
                        rf_sr_ksCurThread word_sle_def word_sless_def sysargs_rel_to_n
                        mask_eq_iff_w2p mask_eq_iff_w2p word_size ThreadState_defs)
  apply (rule conjI)
   apply (clarsimp simp: linorder_not_le isCap_simps)
   apply (rule conjI, clarsimp simp: unat64_eq_of_nat)
   apply clarsimp
   apply (drule_tac x="extraCaps ! 0" and P="\<lambda>v. valid_cap' (fst v) s" in bspec)
    apply (clarsimp simp: nth_mem interpret_excaps_test_null excaps_map_def)
   apply (clarsimp simp: valid_cap_simps' pred_tcb'_weakenE active_runnable')
   apply (intro conjI; fastforce?)
    apply (fastforce simp: tcb_st_refs_of'_def elim:pred_tcb'_weakenE)
   apply (simp add: word_le_nat_alt unat_ucast unat_numDomains_to_H le_maxDomain_eq_less_numDomains)
  apply (clarsimp simp: ccap_relation_def cap_to_H_simps cap_thread_cap_lift)
  subgoal (* args ! 0 can be contained in a domain-sized word *)
    by (clarsimp simp: not_le unat_numDomains_to_H ucast_ucast_len[simplified word_less_nat_alt]
                 dest!: less_numDomains_is_domain)
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
      apply simp+
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
      apply simp+
done


(************************************************************************)
(*                                                                      *)
(* invokeCNodeCancelBadgedSends_ccorres *********************************)
(*                                                                      *)
(************************************************************************)

lemma invokeCNodeCancelBadgedSends_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and sch_act_simple and valid_cap' cap and K (isEndpointCap cap)) (UNIV \<inter> {s. ccap_relation cap (cap_' s)}) []
     (invokeCNode (CancelBadgedSends cap))
     (Call invokeCNodeCancelBadgedSends_'proc)"
  apply (simp)
  apply (rule ccorres_gen_asm)
  apply (clarsimp simp: isCap_simps)
  apply (cinit lift: cap_' simp del: return_bind cong:call_ignore_cong)
   apply (frule cap_get_tag_isCap_unfolded_H_cap)
   apply (simp add: cap_get_tag_EndpointCap del: Collect_const)
   apply csymbr
   apply csymbr
   apply (simp add: unless_def liftE_def when_def Collect_True del: Collect_const)
   apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
       apply (rule_tac R=\<top> in ccorres_cond2)
         apply (clarsimp simp: cap_get_tag_isCap[symmetric] simp del: Collect_const dest!: cap_get_tag_to_H)
        apply (rule ccorres_rhs_assoc | csymbr)+
        apply (ctac add: cancelBadgedSends_ccorres)
       apply (rule ccorres_return_Skip)
      apply ceqv
     apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre,vcg)
     apply clarsimp
     apply (simp add: return_def)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (clarsimp simp: valid_cap_simps' cap_get_tag_EndpointCap)
  done



(************************************************************************)
(*                                                                      *)
(* invokeCNodeInsert_ccorres ********************************************)
(*                                                                      *)
(************************************************************************)

lemma invokeCNodeInsert_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (cte_wp_at' (\<lambda>scte. capMasterCap (cteCap scte) = capMasterCap cap) src
                     and valid_mdb' and pspace_aligned' and pspace_canonical'
                     and valid_objs' and valid_cap' cap)
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
       (valid_mdb' and pspace_aligned' and pspace_canonical')
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
   apply (simp split del: if_split del: Collect_const)
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
   apply (simp add: guard_is_UNIV_def)
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
       (valid_mdb' and pspace_aligned' and pspace_canonical' and cur_tcb')
       (UNIV \<inter> {s. destSlot_' s = Ptr destSlot}) []
       (invokeCNode (SaveCaller destSlot))
  (Call invokeCNodeSaveCaller_'proc)"
  apply (cinit lift: destSlot_'  simp del: return_bind cong:call_ignore_cong)
   apply (simp add: Collect_True split del: if_split  del: Collect_const cong:call_ignore_cong)
   apply (simp only: liftE_def)
   apply (rule ccorres_Guard_Seq)+
   apply (simp only: bind_assoc)
   apply (rule ccorres_pre_getCurThread)

   apply (simp only: getThreadCallerSlot_def locateSlot_conv)

   apply (rule_tac P="\<lambda>s. rv=ksCurThread s \<and> is_aligned rv tcbBlockSizeBits" and r'="\<lambda> a c. c = Ptr a"
                   and xf'="srcSlot_'" and P'=UNIV in ccorres_split_nothrow)

       apply (rule ccorres_return)
       apply vcg
       apply clarsimp
       apply (simp add: cte_level_bits_def size_of_def of_nat_def)
       apply (simp add: rf_sr_def cstate_relation_def Kernel_C.tcbCaller_def tcbCallerSlot_def)
       apply (clarsimp simp: Let_def objBits_defs)
       apply (subst ptr_val_tcb_ptr_mask2[simplified mask_def objBits_defs, simplified])
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
                  \<comment> \<open>NullCap case\<close>
                apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
                apply (rule allI, rule conseqPre, vcg)
                apply clarsimp
                apply (simp add: return_def)
               apply (rule ccorres_fail)+
          \<comment> \<open>ReplyCap case\<close>
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


lemmas invocation_eq_use_types_sym = invocation_eq_use_types[TRY [symmetric]]

lemma label_in_CNodeInv_ranges:
  "(label < scast Kernel_C.CNodeRevoke \<or> scast Kernel_C.CNodeSaveCaller < label)
      = (gen_invocation_type label \<notin> set [CNodeRevoke .e. CNodeSaveCaller])"
  "(scast Kernel_C.CNodeCopy \<le> label \<and> label \<le> scast Kernel_C.CNodeMutate)
      = (gen_invocation_type label \<in> set [CNodeCopy .e. CNodeMutate])"
  apply (simp_all add: upto_enum_def fromEnum_def enum_gen_invocation_labels
                  del: upt.simps)
  apply (simp_all add: atLeastLessThanSuc)
  apply (simp_all add: toEnum_def enum_invocation_label enum_gen_invocation_labels)
  apply (simp_all flip: gen_invocation_type_eq)
  apply (simp_all add: invocation_eq_use_types_sym invocation_label_defs)
  apply (simp_all add: unat_arith_simps)
  apply arith+
  done

lemma cnode_invok_case_cleanup2:
  "i \<in> set [CNodeCopy .e. CNodeMutate] \<Longrightarrow>
     (case i of CNodeRevoke \<Rightarrow> P | CNodeDelete \<Rightarrow> Q | CNodeCancelBadgedSends \<Rightarrow> R
              | CNodeRotate \<Rightarrow> S | CNodeSaveCaller \<Rightarrow> T | _ \<Rightarrow> U) = U"
  apply (rule cnode_invok_case_cleanup)
  apply (simp add: upto_enum_def fromEnum_def toEnum_def
                   enum_invocation_label enum_gen_invocation_labels)
  apply auto
  done

lemma hasCancelSendRights_spec:
  "\<forall>cap. \<Gamma> \<turnstile> \<lbrace> ccap_relation cap \<acute>cap \<rbrace>
             Call hasCancelSendRights_'proc
             \<lbrace> \<acute>ret__unsigned_long = from_bool (hasCancelSendRights cap) \<rbrace>"
  apply vcg
  apply (clarsimp simp: if_1_0_0)
  apply (rule conjI)
   apply clarsimp
   apply (drule sym, drule (1) cap_get_tag_to_H)
   apply (clarsimp simp: hasCancelSendRights_def to_bool_def
                   split: if_split bool.splits)
  apply (rule impI)
  apply (case_tac cap,
         auto simp: cap_get_tag_isCap_unfolded_H_cap cap_tag_defs hasCancelSendRights_def
              dest: cap_get_tag_isArchCap_unfolded_H_cap
              split: capability.splits bool.splits)[1]
  done

lemma decodeCNodeInvocation_ccorres:
  notes gen_invocation_type_eq[simp]
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
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. ccap_relation cp (cap_' s)}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. invLabel_' s = lab}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeCNodeInvocation lab args cp (map fst extraCaps)
           >>= invocationCatch thread isBlocking isCall InvokeCNode)
  (Call decodeCNodeInvocation_'proc)"
  supply if_cong[cong]
  apply (cases "\<not>isCNodeCap cp")
   apply (simp add: decodeCNodeInvocation_def
              cong: conj_cong)
   apply (rule ccorres_fail')
  apply (cinit' (no_subst_asm) lift: length___unsigned_long_' cap_' current_extra_caps_'
                                     call_' invLabel_' buffer_')
   apply (clarsimp simp: word_less_nat_alt decodeCNodeInvocation_def
                         list_case_If2 invocation_eq_use_types
                         label_in_CNodeInv_ranges[unfolded word_less_nat_alt]
                         cnode_invok_case_cleanup2
               simp del: Collect_const
                   cong: call_ignore_cong globals.fold_congs
                         StateSpace.state.fold_congs bool.case_cong
               cong del: invocation_label.case_cong_weak gen_invocation_labels.case_cong_weak)
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
            apply (simp add: invocationCatch_use_injection_handler[symmetric]
                        del: Collect_const cong: call_ignore_cong)
            apply (rule ccorres_Cond_rhs_Seq)
             apply (simp add:if_P del: Collect_const)
             apply (rule ccorres_cond_true_seq)
             apply (simp add: throwError_bind invocationCatch_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (simp add: linorder_not_less del: Collect_const cong: call_ignore_cong)
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
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                     apply vcg
                    apply simp
                    apply (ctac add: ccorres_injection_handler_csum1
                                         [OF lookupSourceSlot_ccorres,
                                             unfolded lookupSourceSlot_def])
                       prefer 2
                       apply simp
                       apply (rule ccorres_split_throws)
                        apply (rule ccorres_return_C_errorE, simp+)[1]
                       apply vcg
                      apply (simp add: liftE_bindE cong: call_ignore_cong)
                      apply csymbr
                      apply (rule ccorres_move_c_guard_cte)
                      apply (rule ccorres_pre_getCTE)
                      apply (rule ccorres_add_return)
                      apply (rule_tac xf'=ret__unsigned_longlong_'
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
                                               word_bits_def hd_conv_nth take_bit_Suc)
                        apply (simp add: whenE_def[where P=False]
                                         injection_handler_returnOk Collect_const[symmetric]
                                   cong: call_ignore_cong del: Collect_const)
                        apply (rule ccorres_Cond_rhs_Seq)
                         \<comment> \<open>CNodeCopy case\<close>
                         apply (simp add: Collect_const[symmetric] del: Collect_const)
                         apply (rule ccorres_rhs_assoc)+
                         apply (rule ccorres_Cond_rhs_Seq)
                          apply (simp add: injection_handler_throwError if_P)
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
                                 apply (rule ccorres_return_C_errorE, simp+)[1]
                                apply vcg
                               apply simp
                               apply csymbr
                               apply csymbr
                               apply csymbr
                               apply (simp add: cap_get_tag_NullCap del: Collect_const)
                               apply (rule ccorres_Cond_rhs_Seq)
                                apply (simp add: injection_handler_throwError whenE_def)
                                apply (rule syscall_error_throwError_ccorres_n)
                                apply (simp add: syscall_error_to_H_cases)
                               apply (simp add: whenE_def injection_handler_returnOk
                                                ccorres_invocationCatch_Inr performInvocation_def
                                                bindE_assoc)
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
                              apply (rule hoare_strengthen_postE_R)
                               apply (rule_tac Q'="\<lambda>rv. valid_pspace'
                                                    and valid_cap' rv and valid_objs'
                                                         and tcb_at' thread and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)"
                                           in hoare_vcg_conj_liftE_R)
                                apply (rule deriveCap_Null_helper[OF deriveCap_derived])
                               apply wp
                              apply (clarsimp simp: cte_wp_at_ctes_of)
                              apply (fastforce simp: is_derived'_def badge_derived'_def
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
                         \<comment> \<open>CNodeMint case\<close>
                         apply (simp flip: Collect_const)
                         apply (rule ccorres_rhs_assoc)+
                         apply (rule ccorres_Cond_rhs_Seq)
                          apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
                           apply vcg
                          apply (rule conseqPre, vcg)
                          apply (clarsimp split: if_split simp: injection_handler_throwError)
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
                                     apply (rule ccorres_return_C_errorE, simp+)[1]
                                    apply vcg
                                   apply simp
                                   apply csymbr
                                   apply csymbr
                                   apply csymbr
                                   apply (simp add: cap_get_tag_NullCap del: Collect_const)
                                   apply (rule ccorres_Cond_rhs_Seq)
                                    apply (simp add: whenE_def injection_handler_returnOk
                                                     invocationCatch_def injection_handler_throwError)
                                    apply (rule syscall_error_throwError_ccorres_n)
                                    apply (simp add: syscall_error_to_H_cases)
                                   apply (simp add: whenE_def injection_handler_returnOk
                                                    ccorres_invocationCatch_Inr
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
                                  apply (rule hoare_strengthen_postE_R)
                                   apply (rule_tac Q'="\<lambda>rv. valid_pspace'
                                                        and valid_cap' rv and valid_objs'
                                                             and tcb_at' thread and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)"
                                               in hoare_vcg_conj_liftE_R)
                                    apply (rule deriveCap_Null_helper [OF deriveCap_derived])
                                   apply wp
                                  apply (clarsimp simp: cte_wp_at_ctes_of)
                                  apply (fastforce simp: is_derived'_def badge_derived'_def)
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
                         \<comment> \<open>CNodeMove case\<close>
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
                           apply (simp add: cap_get_tag_NullCap)
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
                         \<comment> \<open>CNodeMutate case\<close>
                         apply (rule ccorres_rhs_assoc)+
                         apply (simp add: flip: Collect_const
                                    cong: call_ignore_cong)
                         apply (rule ccorres_Cond_rhs_Seq)
                          apply (simp add: injection_handler_throwError if_P)
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
                              apply (simp add: whenE_def injection_handler_throwError numeral_eqs)
                              apply (rule syscall_error_throwError_ccorres_n)
                              apply (simp add: syscall_error_to_H_cases)
                             apply (simp add: whenE_def injection_handler_returnOk
                                              ccorres_invocationCatch_Inr numeral_eqs
                                              performInvocation_def bindE_assoc)
                             apply (ctac add: setThreadState_ccorres)
                               apply (simp add: ccorres_cond_iffs)
                               apply (ctac(no_vcg) add: invokeCNodeMove_ccorres)
                                 apply (rule ccorres_alternative2)
                                 apply (rule ccorres_return_CE, simp+)[1]
                                apply (rule ccorres_return_C_errorE, simp+)[1]
                               apply (wp sts_valid_pspace_hangers)+
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
                                         enum_gen_invocation_labels)
                       apply (wp getCTE_wp')
                      apply (simp add: Collect_const_mem)
                      apply vcg
                     apply (simp add: cte_wp_at_ctes_of[where P="(=) cte" for cte]
                                      cte_wp_at_ctes_of[where P="\<lambda>cte. Q cte \<and> R cte" for Q R]
                                      badge_derived_updateCapData)
                     apply (rule validE_R_validE)
                     apply (rule_tac Q'="\<lambda>a b. cte_wp_at' (\<lambda>x. True) a b \<and> invs' b \<and>
                       tcb_at' thread b  \<and> sch_act_wf (ksSchedulerAction b) b \<and> valid_tcb_state' Restart b
                       \<and> Q2 b" for Q2 in  hoare_strengthen_postE_R)
                      prefer 2
                      apply (clarsimp simp:cte_wp_at_ctes_of)
                      apply (drule ctes_of_valid')
                       apply (erule invs_valid_objs')
                      apply (frule invs_pspace_aligned')
                      apply (frule invs_pspace_distinct')
                      apply (clarsimp simp:valid_updateCapDataI invs_valid_objs' invs_valid_pspace')
                      apply assumption
                     apply (wp hoare_vcg_all_liftE_R injection_wp_E[OF refl]
                               lsfco_cte_at' hoare_vcg_const_imp_liftE_R
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
              apply (wp sts_invs_minor')+
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
              apply (wp sts_invs_minor')+
            apply (simp add: Collect_const_mem)
            apply (vcg exspec=setThreadState_modifies)
           apply (vcg exspec=setThreadState_modifies exspec=invokeCNodeDelete_modifies)
          apply (simp del: Collect_const)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp add: injection_handler_returnOk bindE_assoc
                            injection_bindE[OF refl refl] split_def)
           apply (rule ccorres_split_throws)
            apply (rule ccorres_rhs_assoc)+
            apply (ctac add: ccorres_injection_handler_csum1 [OF ensureEmptySlot_ccorres])
               apply (simp add: ccorres_invocationCatch_Inr performInvocation_def bindE_assoc)
               apply (ctac add: setThreadState_ccorres)
                 apply (ctac(no_vcg) add: invokeCNodeSaveCaller_ccorres)
                   apply (rule ccorres_alternative2)
                   apply (rule ccorres_return_CE, simp+)[1]
                  apply (rule ccorres_return_C_errorE, simp+)[1]
                 apply (wp sts_valid_pspace_hangers)+
               apply (simp add: Collect_const_mem)
               apply (vcg exspec=setThreadState_modifies)
              apply simp
              apply (rule ccorres_split_throws)
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
            apply csymbr
            apply (rule ccorres_move_c_guard_cte)
            apply (rule ccorres_symb_exec_r)
              apply (rule_tac xf'=destCap_' in ccorres_abstract, ceqv)
              apply (rule_tac P="ccap_relation (cteCap rva) rv'" in ccorres_gen_asm2)
              apply (rule ccorres_symb_exec_r)
                apply (rule_tac xf'=ret__unsigned_long_' in ccorres_abstract, ceqv)
                apply (rule_tac P="rv'a = from_bool (hasCancelSendRights (cteCap rva))"
                               in ccorres_gen_asm2)
                apply (simp del: Collect_const)
                apply (rule ccorres_Cond_rhs_Seq)
                 apply (simp add: unlessE_def whenE_def injection_handler_throwError from_bool_0)
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (simp add: syscall_error_to_H_cases)
                apply (simp add: unlessE_def whenE_def injection_handler_returnOk
                                 from_bool_neq_0
                            del: Collect_const)
                apply (simp add: unlessE_def injection_handler_returnOk
                                 ccorres_invocationCatch_Inr
                                 performInvocation_def bindE_assoc)
                apply (ctac add: setThreadState_ccorres)
                  apply (ctac(no_vcg) add: invokeCNodeCancelBadgedSends_ccorres)
                    apply (rule ccorres_alternative2)
                    apply (rule ccorres_return_CE, simp+)[1]
                   apply (rule ccorres_return_C_errorE, simp+)[1]
                  apply (wp sts_invs_minor')+
                apply (simp add: Collect_const_mem)
                apply (vcg exspec=setThreadState_modifies)
               apply (simp add: Collect_const_mem)
               apply vcg
              apply (rule conseqPre, vcg, clarsimp)
              apply fastforce
             apply (vcg)
            apply (simp del: Collect_const)
            apply (rule conseqPre, vcg)
            apply (simp del: Collect_const)
           apply (vcg exspec=setThreadState_modifies
                      exspec=invokeCNodeCancelBadgedSends_modifies
                      exspec=hasCancelSendRights_modifies)
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
           apply (simp add: invocationCatch_use_injection_handler[symmetric]
                       del: Collect_const)
           apply csymbr
           apply (simp add: interpret_excaps_test_null excaps_map_def
                       del: Collect_const)
           apply (rule ccorres_Cond_rhs_Seq)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule ccorres_cond_true_seq)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
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
                                apply (simp add: whenE_def injection_handler_throwError)
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
                                  apply (rule_tac xf'=ret__unsigned_longlong_' in ccorres_abstract, ceqv)
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
                                    apply (rule_tac xf'=ret__unsigned_longlong_' in ccorres_abstract, ceqv)
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
                                                      word_size word_bits_def take_bit_Suc)
                                    apply (simp add: whenE_def[where P=False] injection_handler_returnOk
                                                     hd_conv_nth numeral_eqs[symmetric])
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
                                         apply (simp add: whenE_def injection_handler_throwError)
                                         apply (rule syscall_error_throwError_ccorres_n)
                                         apply (simp add: syscall_error_to_H_cases)
                                        apply (simp add: whenE_def[where P=False] injection_handler_returnOk
                                                    del: Collect_const)
                                        apply csymbr
                                        apply (simp add: cap_get_tag_NullCap del: Collect_const)
                                        apply (rule ccorres_Cond_rhs_Seq)
                                         apply (simp add: whenE_def injection_handler_throwError)
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
                                         apply (wp hoare_weak_lift_imp)+
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
                                                        in hoare_strengthen_postE_R)
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
                          apply (wp | wp (once) hoare_drop_imps)+
                         apply simp
                         apply vcg
                        apply simp
                        apply (wp | wp (once) hoare_drop_imps)+
                       apply simp
                       apply vcg
                      apply wp
                     apply simp
                     apply (vcg exspec=getSyscallArg_modifies)
                    apply (wp hoare_weak_lift_imp)
                   apply simp
                   apply (vcg exspec=getSyscallArg_modifies)
                  apply wp
                 apply simp
                 apply (vcg exspec=getSyscallArg_modifies)
                apply (wp hoare_weak_lift_imp)
               apply simp
               apply (vcg exspec=getSyscallArg_modifies)
              apply (wp hoare_weak_lift_imp)
             apply simp
             apply (vcg exspec=getSyscallArg_modifies)
            apply wp
           apply simp
           apply (vcg exspec=getSyscallArg_modifies)
          apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
          apply (simp add: upto_enum_def fromEnum_def toEnum_def
                           enum_gen_invocation_labels)
         apply (rule ccorres_split_throws)
          apply (simp add: ccorres_cond_iffs)
          apply (rule ccorres_return_C_errorE, simp+)[1]
         apply vcg
        apply simp
        apply (wp injection_wp_E[OF refl] hoare_vcg_const_imp_liftE_R
                  hoare_vcg_all_liftE_R lsfco_cte_at' hoare_weak_lift_imp
                | simp add: hasCancelSendRights_not_Null ctes_of_valid_strengthen
                      cong: conj_cong
                | wp (once) hoare_drop_imps)+
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
                        ct_in_state'_def pred_tcb_at'
                        cur_tcb'_def word_sle_def word_sless_def
                        unat_lt2p[where 'a=machine_word_len, folded word_bits_def])
  apply (rule conjI)
   apply (clarsimp simp: sysargs_rel_n_def n_msgRegisters_def excaps_map_def
                         cte_wp_at_ctes_of excaps_in_mem_def slotcap_in_mem_def
                         sysargs_rel_def length_ineq_not_Nil
                  dest!: interpret_excaps_eq)
    apply ((rule conjI | clarsimp simp:split_def neq_Nil_conv
                      | erule pred_tcb'_weakenE disjE
                      | drule st_tcb_at_idle_thread')+)[1]
  apply (frule interpret_excaps_eq)
  apply (clarsimp simp: excaps_map_def mask_def[where n=4]
                        ccap_rights_relation_def rightsFromWord_wordFromRights
                        ThreadState_defs map_comp_Some_iff
                        rf_sr_ksCurThread hd_conv_nth hd_drop_conv_nth)
  apply ((rule conjI
            | clarsimp simp: rightsFromWord_wordFromRights
                             ccte_relation_def c_valid_cte_def
                             cl_valid_cte_def c_valid_cap_def
                             map_option_Some_eq2 neq_Nil_conv ccap_relation_def
                             numeral_eqs hasCancelSendRights_not_Null
                             ccap_relation_NullCap_iff[symmetric]
                             interpret_excaps_test_null mdbRevocable_CL_cte_to_H
            | clarsimp simp: typ_heap_simps'
            | frule length_ineq_not_Nil)+)
  done

end

context begin interpretation Arch . (*FIXME: arch-split*)

lemmas setCTE_def3 = setCTE_def2[THEN eq_reflection]

lemma setCTE_sch_act_wf[wp]:
  "\<lbrace> \<lambda>s. sch_act_wf (ksSchedulerAction s) s \<rbrace>
   setCTE src cte
   \<lbrace>\<lambda>x s. sch_act_wf (ksSchedulerAction s) s \<rbrace>"
  by (wp sch_act_wf_lift setCTE_pred_tcb_at' setCTE_tcb_in_cur_domain')

crunch insertNewCap
  for sch_act_wf[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps ignore: setCTE)

crunch deleteObjects
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps simp: unless_def)

lemma deleteObjects_gsCNodes_at_pt:
  "\<lbrace>(\<lambda>s. P (gsCNodes s ptr))
      and K (ptr \<notin> {ptr_base .. ptr_base + 2 ^ sz - 1} \<and> is_aligned ptr_base sz)\<rbrace>
    deleteObjects ptr_base sz
       \<lbrace>\<lambda>rv s. P (gsCNodes s ptr)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: deleteObjects_def2 add_mask_fold)
  apply (wpsimp cong: conj_cong
         | wp (once) hoare_drop_imps)+
  done

crunch setThreadState, updateFreeIndex, preemptionPoint
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  (simp: unless_def whenE_def ignore_del: preemptionPoint)

lemma resetUntypedCap_gsCNodes_at_pt:
  "\<lbrace>(\<lambda>s. P (gsCNodes s ptr))
      and cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and> ptr \<notin> untypedRange (cteCap cte)) slot
      and valid_objs'\<rbrace>
    resetUntypedCap slot
   \<lbrace>\<lambda>rv s. P (gsCNodes s ptr)\<rbrace>, -"
  apply (simp add: resetUntypedCap_def unlessE_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_wp' | simp add: unless_def)+
    apply (wp hoare_vcg_const_imp_lift
              deleteObjects_gsCNodes_at_pt
              getSlotCap_wp)+
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  apply (frule(1) ctes_of_valid')
  apply (clarsimp simp: valid_cap_simps' capAligned_def)
  done

end

context kernel_m begin

lemma wordFromMessageInfo_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call wordFromMessageInfo_'proc
           \<lbrace>\<acute>ret__unsigned_long = index (seL4_MessageInfo_C.words_C (mi_' s)) (unat 0)\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply (simp add: word_sless_def word_sle_def)
  done

lemma seL4_MessageInfo_lift_def2:
  "seL4_MessageInfo_lift message_info \<equiv>
  \<lparr>label_CL = (index (seL4_MessageInfo_C.words_C message_info) 0 >> 12) && mask 52,
   capsUnwrapped_CL = (index (seL4_MessageInfo_C.words_C message_info) 0 >> 9) && mask 3,
   extraCaps_CL = (index (seL4_MessageInfo_C.words_C message_info) 0 >> 7) && mask 2,
   length_CL = (index (seL4_MessageInfo_C.words_C message_info) 0 >> 0) && mask 7\<rparr>"
  apply (simp add: seL4_MessageInfo_lift_def mask_def)
  done

lemma globals_update_id:
  "globals_update (t_hrs_'_update (hrs_htd_update id)) x = x"
   by (simp add: hrs_htd_update_def)

lemma getObjectSize_spec:
  "\<forall>s. \<Gamma>\<turnstile>\<lbrace>s. \<acute>t \<le> of_nat (length (enum::object_type list) - 1)\<rbrace> Call getObjectSize_'proc
           \<lbrace>\<acute>ret__unsigned_long = of_nat (getObjectSize (object_type_to_H (t_' s)) (unat (userObjSize_' s)))\<rbrace>"
  apply vcg
  apply (clarsimp simp: Kernel_C_defs
                         bit_simps objBits_simps' framesize_to_H_def pageBitsForSize_def
                        object_type_to_H_def Kernel_C_defs APIType_capBits_def)
  apply (simp add:nAPIObjects_def)
  apply (simp add:enum_object_type enum_apiobject_type)
  apply unat_arith
  done

lemma object_type_from_H_bound:
  "object_type_from_H newType \<le> of_nat (length (enum::object_type list) - Suc 0)"
  apply (simp add:enum_object_type enum_apiobject_type object_type_from_H_def)
  apply (case_tac newType)
  apply (clarsimp simp: Kernel_C_defs objBits_simps
                  split:apiobject_type.splits)+
  done

lemma updateCap_ct_active'[wp]:
  "\<lbrace>ct_active'\<rbrace> updateCap srcSlot cap \<lbrace>\<lambda>rva. ct_active' \<rbrace>"
  apply (rule hoare_pre)
  apply (simp add:ct_in_state'_def)
  apply (wps|wp|simp add:ct_in_state'_def)+
  done

lemma APIType_capBits_low:
  "\<lbrakk> newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < us;
     newType = APIObjectType apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits\<rbrakk>
           \<Longrightarrow> 4 \<le> APIType_capBits newType us"
  apply (case_tac newType)
  apply (clarsimp simp: invokeUntyped_proofs_def APIType_capBits_def objBits_simps' bit_simps
                        untypedBits_defs
                 split: apiobject_type.splits)+
  done

lemma APIType_capBits_high:
  "\<lbrakk> newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow>  us < 59;
     newType = APIObjectType apiobject_type.Untyped \<longrightarrow> us \<le> 61\<rbrakk>
           \<Longrightarrow> APIType_capBits newType us < 64"
  apply (case_tac newType)
  apply (clarsimp simp: invokeUntyped_proofs_def APIType_capBits_def objBits_simps' bit_simps
                 split: apiobject_type.splits)+
  done

lemma typ_clear_region_eq:
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  Int_atLeastAtMost atLeastatMost_empty_iff
shows
 "\<lbrakk>ctes_of (s::kernel_state) (ptr_val p) = Some cte; is_aligned ptr bits; bits < word_bits;
  {ptr..ptr + 2 ^ bits - 1} \<inter> {ptr_val p..ptr_val p + mask cteSizeBits} = {}; ((clift hp) :: (cte_C ptr \<rightharpoonup> cte_C)) p = Some to\<rbrakk> \<Longrightarrow>
  (clift (hrs_htd_update (typ_clear_region ptr bits) hp) :: (cte_C ptr \<rightharpoonup> cte_C)) p = Some to"
   apply (clarsimp simp:lift_t_def lift_typ_heap_def restrict_map_def split:if_splits)
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
    apply (simp add:intvl_range_conv[where 'a=machine_word_len, folded word_bits_def])
    apply (subgoal_tac "ptr_val p + of_nat y \<in> {ptr_val p..ptr_val p + mask cteSizeBits}")
     apply blast
    apply (clarsimp simp:blah)
     apply (rule context_conjI)
      apply (rule is_aligned_no_wrap')
      apply (rule ctes_of_is_aligned[where cte = cte and s = s])
       apply simp
      apply (rule of_nat_power; simp add: objBits_simps')
     apply (rule word_plus_mono_right)
      apply (simp add: word_of_nat_le objBits_defs mask_def)
     apply (rule is_aligned_no_wrap')
      apply (rule ctes_of_is_aligned[where cte = cte and s = s])
       apply simp
    apply (clarsimp simp: objBits_simps' mask_def)
   apply (clarsimp simp: proj_d_def)
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

lemma cNodeNoOverlap_retype_have_size:
  "\<not> cNodeOverlap cns (\<lambda>x. ptr \<le> x \<and> x \<le> ptr + of_nat num * 2 ^ bits - 1)
    \<Longrightarrow> cnodes_retype_have_size {ptr .. ptr + of_nat num * 2 ^ bits - 1} anysz cns"
  apply (clarsimp simp: cnodes_retype_have_size_def cNodeOverlap_def)
  apply (elim allE, drule(1) mp, clarsimp simp: upto_intvl_eq[symmetric])
  apply (erule disjoint_subset2[rotated])
  apply clarsimp
  done

lemma range_cover_compare_bound_word:
  "range_cover ptr sz sbit n
    \<Longrightarrow> (of_nat n * 2 ^ sbit) + (ptr && mask sz) \<le> 2 ^ sz"
  apply (simp add: word_le_nat_alt range_cover_unat
                   add.commute)
  apply (frule range_cover.range_cover_compare_bound)
  apply (simp add: range_cover.sz range_cover.unat_of_nat_shift)
  done

lemma isUntypedCap_ccap_relation_helper:
  "ccap_relation cap ccap
    \<Longrightarrow> isUntypedCap cap
    \<Longrightarrow> cap_get_tag ccap = scast cap_untyped_cap
      \<and> cap_lift ccap = Some (Cap_untyped_cap (cap_untyped_cap_lift ccap))
      \<and> cap_untyped_cap_lift ccap =
            \<lparr> capFreeIndex_CL = of_nat (capFreeIndex cap) >> 4,
                       capIsDevice_CL = from_bool (capIsDevice cap),
                       capBlockSize_CL = of_nat (capBlockSize cap),
                       capPtr_CL = capPtr cap\<rparr>"
  apply (simp add: cap_get_tag_isCap[symmetric])
  apply (frule(1) cap_get_tag_UntypedCap[THEN iffD1])
  apply (frule cap_lift_untyped_cap)
  apply (simp add: cap_untyped_cap_lift_def)
  apply (clarsimp simp: shiftl_shiftr1 word_size from_to_bool_last_bit)
  apply (simp add: mask_def word_bw_assocs )
  done

lemma pspace_no_overlap_underlying_zero_update:
  "pspace_no_overlap' ptr sz s
    \<Longrightarrow> invs' s
    \<Longrightarrow> S \<subseteq> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}
    \<Longrightarrow> s\<lparr>ksMachineState := underlying_memory_update
      (\<lambda>m x. if x \<in> S then 0 else m x) (ksMachineState s)\<rparr>
        = s"
  apply (subgoal_tac "\<forall>x \<in> S. underlying_memory (ksMachineState s) x = 0")
   apply (cases "ksMachineState s")
   apply (cases s, simp add: fun_eq_iff split: if_split)
  apply (clarsimp split: if_split_asm)
  apply (erule pspace_no_overlap_underlying_zero)
   apply (simp add: invs'_def valid_state'_def)
  apply blast
  done

lemma clearMemory_untyped_ccorres:
  "ccorres dc xfdc ((\<lambda>s. invs' s
              \<and> (\<exists>cap. cte_wp_at' (\<lambda>cte. cteCap cte = cap) ut_slot s
                  \<and> isUntypedCap cap
                  \<and> {ptr ..+ 2 ^ sz} \<subseteq> untypedRange cap
                  \<and> pspace_no_overlap' (capPtr cap) (capBlockSize cap) s)
              \<and> 2 ^ sz \<le> gsMaxObjectSize s)
          and (\<lambda>_. is_aligned ptr sz \<and> sz \<ge> 3 \<and> sz \<le> resetChunkBits))
      ({s. region_actually_is_bytes ptr (2 ^ sz) s}
            \<inter> {s. bits_' s = of_nat sz}
            \<inter> {s. ptr___ptr_to_void_' s = Ptr ptr})
      []
     (doMachineOp (clearMemory ptr (2 ^ sz))) (Call clearMemory_'proc)"
  (is "ccorres dc xfdc ?P ?P' [] ?m ?c")
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: bits_' ptr___ptr_to_void_')
   apply (rule_tac P="ptr \<noteq> 0 \<and> sz < word_bits" in ccorres_gen_asm)
   apply (simp add: clearMemory_def)
   apply (rule_tac P="?P" and P'="{s. region_actually_is_bytes ptr (2 ^ sz) s}" in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (rule conjI; clarsimp)
    apply (simp add: word_less_nat_alt unat_of_nat word_bits_def)
   apply (clarsimp simp: isCap_simps valid_cap'_def capAligned_def
                         is_aligned_no_wrap'[OF _ word64_power_less_1]
                         unat_of_nat_eq word_bits_def)
   apply (simp add: is_aligned_weaken is_aligned_triv[THEN is_aligned_weaken])
   apply (clarsimp simp: ghost_assertion_size_logic[unfolded o_def] region_actually_is_bytes_dom_s)
   apply (clarsimp simp: field_simps word_size_def mapM_x_storeWord_step
                         word_bits_def cte_wp_at_ctes_of)
   apply (frule ctes_of_valid', clarify+)
   apply (simp add: doMachineOp_def split_def exec_gets)
   apply (simp add: select_f_def simpler_modify_def bind_def valid_cap_simps' capAligned_def)
   apply (subst pspace_no_overlap_underlying_zero_update; simp?)
    apply (case_tac sz, simp_all)[1]
    apply (case_tac nat, simp_all)[1]
    apply (case_tac nata, simp_all)[1]
   apply (clarsimp dest!: region_actually_is_bytes)
   apply (drule(1) rf_sr_rep0)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         carch_state_relation_def cmachine_state_relation_def)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule ctes_of_valid'; clarify?)
  apply (clarsimp simp: isCap_simps valid_cap_simps' capAligned_def
                        word_of_nat_less Kernel_Config.resetChunkBits_def
                        word_bits_def unat_2p_sub_1)
  apply (cases "ptr = 0"; simp)
  apply (drule subsetD, rule intvl_self, simp)
  apply simp
  done

lemma t_hrs_update_use_t_hrs:
  "t_hrs_'_update f s
    = (t_hrs_'_update (\<lambda>_. f (t_hrs_' s)) $ s)"
  by simp

lemma reset_untyped_inner_offs_helper:
  "\<lbrakk> cteCap cte = capability.UntypedCap dev ptr sz idx;
      i \<le> unat ((of_nat idx - 1 :: addr) div 2 ^ sz2);
      sz2 \<le> sz; idx \<noteq> 0;
      valid_cap' (cteCap cte) s
    \<rbrakk>
    \<Longrightarrow> of_nat i * 2 ^ sz2 < (2 ^ sz :: addr)"
  apply (clarsimp simp: valid_cap_simps' untypedBits_defs)
  apply (rule word_less_power_trans2, simp_all)
  apply (rule word_of_nat_less)
  apply (erule order_le_less_trans)
  apply (simp only: word_less_nat_alt[symmetric])
  apply (simp add: shiftr_div_2n_w[symmetric] word_size)
  apply (rule shiftr_less_t2n)
  apply (simp add: word_of_nat_le)
  apply (rule of_nat_neq_0, simp)
  apply (erule order_le_less_trans)
  apply (rule power_strict_increasing, simp_all)
  done

lemma typ_region_bytes_dom_s:
  "S \<subseteq> {ptr ..+ 2 ^ bits}
    \<Longrightarrow> S \<times> {SIndexVal, SIndexTyp 0} \<subseteq> dom_s (typ_region_bytes ptr bits htd)"
  apply (clarsimp simp: typ_region_bytes_def dom_s_def)
  apply fastforce
  done

lemma aligned_intvl_offset_subset:
  assumes al: "is_aligned (ptr :: 'a :: len word) sz" and al': "is_aligned x sz'"
  and     szv: "sz' \<le> sz" and xsz: "x < 2 ^ sz"
  shows       "{ptr + x ..+ 2 ^ sz'} \<subseteq> {ptr ..+ 2 ^ sz}"
  apply (simp only: upto_intvl_eq al aligned_add_aligned[OF al al' szv])
  apply (rule aligned_range_offset_subset[OF al al' szv xsz])
  done

lemma aligned_intvl_offset_subset_ran:
  assumes al: "is_aligned (ptr :: 'a :: len word) sz" and al': "is_aligned x sz'"
  and     szv: "sz' \<le> sz" and xsz: "x < 2 ^ sz"
  shows       "{ptr + x ..+ 2 ^ sz'} \<subseteq> {ptr .. ptr + 2 ^ sz - 1}"
  apply (simp only: upto_intvl_eq al aligned_add_aligned[OF al al' szv])
  apply (rule aligned_range_offset_subset[OF al al' szv xsz])
  done

lemma ccorres_req_Ex:
  assumes v: "\<And>s s'. \<lbrakk> (s, s') \<in> sr; P s; s' \<in> P' \<rbrakk> \<Longrightarrow> \<exists>v. Q v s \<and> Q' v s' \<and> V v"
  and cc: "\<And>v. V v \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf r' xf' (P and Q v) (P' \<inter> {s. Q' v s}) hs H C"
  shows "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H C"
  apply (rule ccorres_name_pre)
  apply (rule ccorres_name_pre_C)
  apply (case_tac "(s, sa) \<in> sr")
   apply (drule(2) v, clarsimp)
   apply (rule ccorres_guard_imp2, erule cc)
   apply auto[1]
  apply (rule ccorresI', simp)
  done

lemma region_actually_is_bytes_subset_t_hrs:
  "region_actually_is_bytes ptr sz s'
    \<Longrightarrow> {ptr' ..+ sz'} \<subseteq> {ptr ..+ sz}
    \<Longrightarrow> t_hrs_' (globals s') = t_hrs_' (globals s)
    \<Longrightarrow> region_actually_is_bytes ptr' sz' s"
  by (auto simp: region_actually_is_bytes_def)

lemma eq_UntypedCap_helper:
  "isUntypedCap cap \<and> capIsDevice cap = dev
      \<and> capPtr cap = ptr \<and> capBlockSize cap = sz
      \<and> capFreeIndex cap = idx
    \<Longrightarrow> cap = UntypedCap dev ptr sz idx"
  by (clarsimp simp: isCap_simps)

lemma byte_regions_unmodified_actually_heap_list:
  "byte_regions_unmodified hrs hrs'
    \<Longrightarrow> region_actually_is_bytes' p' n' htd
    \<Longrightarrow> htd = (hrs_htd hrs)
    \<Longrightarrow> heap_list (hrs_mem hrs) n p = v
    \<Longrightarrow> {p ..+ n} \<subseteq> {p' ..+ n'}
    \<Longrightarrow> heap_list (hrs_mem hrs') n p = v"
  apply (erule trans[rotated], rule heap_list_h_eq2)
  apply (simp add: byte_regions_unmodified_def region_actually_is_bytes_def)
  apply (drule_tac x=x in spec)
  apply (drule_tac x=x in bspec)
   apply blast
  apply (clarsimp split: if_split_asm)
  done

lemma ucast_64_32[simp]:
  "UCAST(64 \<rightarrow> 32) (of_nat x) = of_nat x"
  by (simp add: ucast_of_nat is_down_def source_size_def target_size_def word_size)

text \<open>
@{term resetUntypedCap_'proc} retypes the @{term Untyped} region as bytes, and then enters
a loop which progressively zeros the memory, ultimately establishing @{term zero_ranges_are_zero}
for the full @{term Untyped} range. Since @{term zero_ranges_are_zero} also requires
@{term region_actually_is_bytes}, the loop must remember that we retyped the whole range before
entering the loop. It is sufficient to know that @{term hrs_htd} is preserved, and for most
contents of the loop, this is straightforward. On RISCV64, @{term preemptionPoint_'proc} contains
inline assembly, so we must appeal to the axiomatisation of inline assembly to show that
@{term hrs_htd} is preserved.
\<close>
lemma preemptionPoint_hrs_htd:
  "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call preemptionPoint_'proc \<lbrace>hrs_htd \<acute>t_hrs = hrs_htd \<^bsup>\<sigma>\<^esup>t_hrs\<rbrace>"
  by (rule allI, rule conseqPre, vcg, clarsimp simp: asm_spec_enabled elim!: asm_specE)

lemma resetUntypedCap_ccorres:
  notes upt.simps[simp del] Collect_const[simp del] replicate_numeral[simp del]
  shows
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and sch_act_simple and ct_active' and cte_wp_at' (isUntypedCap o cteCap) slot
         and (\<lambda>s. descendants_of' slot (ctes_of s) = {}))
     (UNIV \<inter>  {s. srcSlot_' s = Ptr slot})
     []
     (resetUntypedCap slot)
     (Call resetUntypedCap_'proc)"
  using [[ceqv_simpl_sequence = true]]
  supply if_cong[cong] option.case_cong[cong]
  apply (cinit lift: srcSlot_')
   apply (simp add: liftE_bindE getSlotCap_def
                    Collect_True extra_sle_sless_unfolds)
   apply (rule ccorres_getCTE, rename_tac cte)
   apply (rule ccorres_move_c_guard_cte)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'="prev_cap_'" in ccorres_abstract, ceqv)
     apply (rename_tac prev_cap)
     apply (rule_tac P="ccap_relation (cteCap cte) prev_cap"
       in ccorres_gen_asm2)
     apply (csymbr | rule ccorres_Guard_Seq[where S=UNIV])+
     apply (rule_tac P="isUntypedCap (cteCap cte)
             \<and> capFreeIndex (cteCap cte) < 2 ^ word_bits
             \<and> capFreeIndex (cteCap cte) < 2 ^ (word_bits - 1)
             \<and> is_aligned (of_nat (capFreeIndex (cteCap cte)) :: addr) 4
             \<and> capBlockSize (cteCap cte) < 2 ^ word_bits"
       in ccorres_gen_asm)
     apply clarsimp
     apply (frule(1) isUntypedCap_ccap_relation_helper)
     apply (clarsimp simp: shiftr_shiftl1)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (frule of_nat_0, simp add: word_bits_def)
      apply (simp add: unlessE_def)
      apply (rule ccorres_split_throws)
       apply (rule ccorres_return_CE, simp+)
      apply vcg
     apply clarsimp
     apply (clarsimp simp: unat_of_nat64)
     apply (frule of_nat_gt_0)
     apply (simp add: unlessE_def)
     apply (simp add: hrs_htd_update)
     apply (rule ccorres_Guard_Seq[where S=UNIV])?
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow)
         apply (rule_tac idx="capFreeIndex (cteCap cte)" in deleteObjects_ccorres[where p=slot])
        apply ceqv
       apply clarsimp
       apply (simp only: ccorres_seq_cond_raise)
       apply (rule ccorres_cond[where R="\<top>"])
         apply (clarsimp simp: Kernel_Config.resetChunkBits_def)
         apply (simp add: word_less_nat_alt unat_of_nat64 from_bool_0)
         apply blast
        apply (simp add: liftE_def bind_assoc shiftL_nat unless_def
                         when_def)
        apply (rule ccorres_rhs_assoc)+
        apply (rule ccorres_split_nothrow[where xf'=xfdc and r'=dc])
            apply (rule ccorres_cond2[where R=\<top>])
              apply (simp add: from_bool_0)
             apply (ctac add: clearMemory_untyped_ccorres[where ut_slot=slot])
            apply (rule ccorres_return_Skip)
           apply ceqv
          apply (rule ccorres_rhs_assoc2)+
          apply (rule ccorres_split_nothrow_novcg)
              apply (rule_tac cap'="cteCap cte" in updateFreeIndex_ccorres)
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: typ_heap_simps' cap_get_tag_isCap
                             dest!: ccte_relation_ccap_relation)
              apply (drule(1) isUntypedCap_ccap_relation_helper)+
              apply (rule exI, strengthen refl, simp)
              apply (simp only: t_hrs_update_use_t_hrs mex_def meq_def)
              apply blast
             apply ceqv
            apply (rule ccorres_return_CE'[unfolded returnOk_def o_apply], simp+)
           apply wp
          apply (simp add: guard_is_UNIV_def)
         apply wp
        apply simp
        apply (vcg)
       apply (rule_tac P="resetChunkBits \<le> capBlockSize (cteCap cte)
             \<and> of_nat (capFreeIndex (cteCap cte)) - 1
                 < (2 ^ capBlockSize (cteCap cte) :: addr)"
           in ccorres_gen_asm)
       apply (elim conjE)
       apply (simp add: whileAnno_def)
       apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+
       apply csymbr
       apply (simp add: reset_name_seq_bound_helper2 word_sle_def word_sless_def
                        msb_big linorder_not_le word_bits_def word_of_nat_less
                        reset_name_seq_bound_helper2[simplified simp_thms]
                        Collect_True)
       apply ((rule ccorres_Guard_Seq[where S=UNIV])+)?
       apply (rule ccorres_add_returnOk)
       apply (rule ccorres_splitE_novcg)
           apply (rule_tac P="capPtr (cteCap cte) \<le> getFreeRef (capPtr (cteCap cte))
                 (capFreeIndex (cteCap cte)) - 1"
               in ccorres_gen_asm)
           apply (rule_tac P="(\<exists>s. valid_cap' (cteCap cte) s)
                \<and> \<not> capIsDevice (cteCap cte)" in ccorres_gen_asm)
           apply (rule_tac yf="\<lambda>ptr. ptr - (capPtr (cteCap cte))"
                      and P="\<lambda>s. 2 ^ resetChunkBits \<le> gsMaxObjectSize s"
                      and F="\<lambda>n b idx. cte_wp_at' (\<lambda>cte'. \<exists>idx'. cteCap cte'
                                  = (cteCap cte)\<lparr> capFreeIndex := idx' \<rparr>
                              \<and> idx = (getFreeRef (capPtr (cteCap cte)) idx') - 1
                                  && ~~ mask resetChunkBits) slot
                          and invs'
                          and (\<lambda>s. descendants_of' slot (ctes_of s) = {})
                          and pspace_no_overlap' (capPtr (cteCap cte)) (capBlockSize (cteCap cte))"
                      and Q="{s. \<not> capIsDevice (cteCap cte)
                          \<longrightarrow> region_actually_is_bytes (capPtr (cteCap cte))
                              (2 ^ (capBlockSize (cteCap cte))) s}"
                 in mapME_x_simpl_sequence_fun_related)
              apply (rule nth_equalityI)
               apply (simp add: length_upto_enum_step)
               apply (simp add: getFreeRef_def shiftr_div_2n_w Kernel_Config.resetChunkBits_def
                                word_size)
              apply (simp add: length_upto_enum_step upto_enum_step_nth
                               less_Suc_eq_le nth_rev getFreeRef_def
                               Kernel_Config.resetChunkBits_def shiftr_div_2n_w word_size
                               and_not_mask shiftl_t2n)
             apply clarify
             apply (rule_tac Q="\<lambda>v. cte_wp_at' (\<lambda>cte. capFreeIndex (cteCap cte) = v) slot"
                   and Q'="\<top>\<top>" and V="\<lambda>v. x = (getFreeRef (capPtr (cteCap cte)) v) - 1
                           && ~~ mask resetChunkBits"
                   in ccorres_req_Ex)
              apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
             apply (clarsimp simp add: shiftL_nat)
             apply (rename_tac prior_idx)
             apply (rule ccorres_guard_imp2)
              apply (rule ccorres_rhs_assoc)+
              apply (ctac add: clearMemory_untyped_ccorres[where ut_slot=slot])
                apply csymbr
                apply (rule ccorres_move_c_guard_cte)
                apply (rule ccorres_split_nothrow_novcg)
                    apply (rule_tac cap'="(cteCap cte)\<lparr> capFreeIndex := prior_idx \<rparr>"
                          in updateFreeIndex_ccorres)
                    apply (rule allI, rule conseqPre, vcg)
                    apply (clarsimp simp: typ_heap_simps' cap_get_tag_isCap
                                   dest!: ccte_relation_ccap_relation)
                    apply (drule(1) isUntypedCap_ccap_relation_helper)+
                    apply (drule isUntypedCap_ccap_relation_helper, clarsimp simp: isCap_simps)
                    apply (rule exI, strengthen refl, simp)
                    apply (simp only: t_hrs_update_use_t_hrs mex_def meq_def,
                      simp only: fun_app_def, strengthen exI[mk_strg I], strengthen refl)
                    apply (clarsimp simp: isCap_simps)
                    apply (simp add: getFreeIndex_def)
                    apply (clarsimp simp: in_set_conv_nth
                                          length_upto_enum_step upto_enum_step_nth
                                          less_Suc_eq_le getFreeRef_def)
                    apply (frule(2) reset_untyped_inner_offs_helper, simp+)
                    apply (clarsimp simp: valid_cap_simps' capAligned_def
                                          is_aligned_mask_out_add_eq_sub[OF is_aligned_weaken])
                    apply (rule less_mask_eq, rule shiftr_less_t2n,
                      erule order_less_le_trans, rule two_power_increasing,
                      simp_all add: maxUntypedSizeBits_def)[1]
                   apply ceqv
                  apply (rule ccorres_add_returnOk)
                  apply (ctac add: preemptionPoint_ccorres)
                     apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
                     apply (rule allI, rule conseqPre, vcg)
                     apply (clarsimp simp: returnOk_def return_def)
                    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                    apply (rule allI, rule conseqPre, vcg)
                    apply (clarsimp simp: throwError_def return_def cintr_def)
                   apply wp
                  apply (simp, vcg exspec=preemptionPoint_modifies)
                 apply (wp updateFreeIndex_clear_invs')
                apply (simp add: guard_is_UNIV_def)
               apply (wp hoare_vcg_ex_lift doMachineOp_psp_no_overlap)
              apply clarsimp
              apply (vcg)
             apply clarify
             apply (rule conjI)
              apply (clarsimp simp: invs_valid_objs' cte_wp_at_ctes_of
                                    invs_urz
                                    getFreeIndex_def isCap_simps
                                    invs_pspace_aligned'
                                    invs_pspace_distinct'
                          simp del: )
              apply (frule valid_global_refsD_with_objSize, clarsimp)
              apply (clarsimp simp: conj_comms in_set_conv_nth
                                    length_upto_enum_step upto_enum_step_nth
                                    less_Suc_eq_le getFreeRef_def)
              apply (frule(2) reset_untyped_inner_offs_helper, simp+)
              apply (clarsimp simp: valid_cap_simps' capAligned_def
                                    aligned_offset_non_zero cteCaps_of_def
                                    is_aligned_mask_out_add_eq_sub[OF is_aligned_weaken]
                                    if_split[where P="\<lambda>z. a \<le> z" for a])
              apply (strengthen is_aligned_mult_triv2[THEN is_aligned_weaken]
                  aligned_sub_aligned
                  aligned_intvl_offset_subset_ran
                  unat_le_helper Aligned.is_aligned_neg_mask)
              apply (simp add: order_less_imp_le Kernel_Config.resetChunkBits_def untypedBits_defs)

             apply (clarsimp simp: in_set_conv_nth isCap_simps
                                   length_upto_enum_step upto_enum_step_nth
                                   less_Suc_eq_le getFreeRef_def
                                   cte_wp_at_ctes_of getFreeIndex_def
                                   hrs_mem_update)
             apply (frule valid_global_refsD_with_objSize, clarsimp)
             apply (frule(2) reset_untyped_inner_offs_helper, simp+)
             apply (frule ctes_of_valid', clarify+)
             apply (clarsimp simp: valid_cap_simps')
             apply (strengthen ghost_assertion_size_logic[unfolded o_def, rotated, mk_strg I E]
                               is_aligned_weaken[where y=2 and x=resetChunkBits]
                               is_aligned_weaken[where y=8 and x=resetChunkBits]
                               is_aligned_no_overflow'[where n=8, simplified]
                               power_increasing[where a=2 and n=8, simplified]
                               region_actually_is_bytes_dom_s[mk_strg I E]
                               aligned_intvl_offset_subset[where sz'=8, simplified]
                               is_aligned_mult_triv2[THEN is_aligned_weaken]
                               region_actually_is_bytes_subset_t_hrs[mk_strg I E]
                           | simp)+
             apply (clarsimp simp: capAligned_def imp_conjL
                                   aligned_offset_non_zero
                                   is_aligned_add_multI conj_comms
                                   is_aligned_mask_out_add_eq_sub[OF is_aligned_weaken])
             apply (strengthen region_actually_is_bytes_subset[mk_strg I E]
                    heap_list_is_zero_mono[OF heap_list_update_eq]
                    order_trans [OF intvl_start_le
                          aligned_intvl_offset_subset[where sz'=resetChunkBits]]
                    byte_regions_unmodified_actually_heap_list[mk_strg I E E]
                | simp add: is_aligned_mult_triv2 hrs_mem_update)+
             apply (simp add: unat_sub word_le_nat_alt unat_sub[OF word_and_le2]
                              mask_out_sub_mask word_and_le2
                              unat_of_nat64[OF order_le_less_trans, rotated,
                                OF power_strict_increasing])
             apply (case_tac idx')
              apply clarsimp
              apply (simp add: addr_card_def card_word Kernel_Config.resetChunkBits_def mask_def)
              apply (rule conjI)
               apply (rule is_aligned_add)
                apply (erule is_aligned_weaken, simp add: minUntypedSizeBits_def)
               apply (simp add: is_aligned_def)
              apply (simp add: is_aligned_def)
             apply clarsimp
             apply (simp add:  addr_card_def card_word is_aligned_def[of "0x100"]
                               Kernel_Config.resetChunkBits_def)
             apply (simp add: unat_of_nat64[OF order_le_less_trans, rotated,
                                OF power_strict_increasing])
             apply (simp add: word_mod_2p_is_mask[symmetric] Kernel_Config.resetChunkBits_def
                              unat_mod unat_of_nat mod_mod_cancel)
             apply (strengthen nat_le_Suc_less_imp[OF mod_less_divisor, THEN order_trans])
             apply simp
             apply (rule is_aligned_add)
              apply (erule is_aligned_weaken, simp add: minUntypedSizeBits_def)
             apply (drule sym[of "a * b" for a b], simp)
             apply (cut_tac is_aligned_mult_triv2[of _ 8, simplified])
             apply (erule is_aligned_weaken, simp)
            apply clarsimp
            apply (rule conseqPre, vcg exspec=preemptionPoint_hrs_htd)
            apply (clarsimp simp: in_set_conv_nth isCap_simps
                                  length_upto_enum_step upto_enum_step_nth
                                  less_Suc_eq_le getFreeRef_def
                                  cte_wp_at_ctes_of getFreeIndex_def
                                  hrs_mem_update)
            apply (frule(2) reset_untyped_inner_offs_helper, simp+)
            apply (clarsimp simp: valid_cap_simps')
            apply (strengthen is_aligned_weaken[where y=2 and x=resetChunkBits]
                              ghost_assertion_size_logic[unfolded o_def, rotated, mk_strg I E]
                              is_aligned_weaken[where y=8 and x=resetChunkBits]
                              is_aligned_no_overflow'[where n=8, simplified]
                              power_increasing[where a=2 and n=8, simplified]
                              region_actually_is_bytes_dom_s[mk_strg I E]
                              aligned_intvl_offset_subset[where sz'=8, simplified]
                              is_aligned_mult_triv2[THEN is_aligned_weaken]
                          | simp)+
            apply (clarsimp simp: capAligned_def
                                  aligned_offset_non_zero
                                  is_aligned_add_multI conj_comms
                                  region_actually_is_bytes_def)
            apply (simp add: Kernel_Config.resetChunkBits_def is_aligned_def[of "0x100"])
            apply (rule is_aligned_add)
             apply (erule is_aligned_weaken, simp add: minUntypedSizeBits_def)
            apply (cut_tac is_aligned_mult_triv2[of _ 8, simplified])
            apply (erule is_aligned_weaken, simp)
           apply (rule hoare_pre)
            apply (wp updateFreeIndex_cte_wp_at updateFreeIndex_clear_invs'
                      updateFreeIndex_pspace_no_overlap'
                      updateFreeIndex_descendants_of2
                      doMachineOp_psp_no_overlap
                      hoare_vcg_ex_lift
              | (wp (once) preemptionPoint_inv, simp, simp add: pspace_no_overlap'_def)
              | simp)+
           apply (simp add: cte_wp_at_ctes_of isCap_simps | clarify)+
           apply (clarsimp simp: length_upto_enum_step upto_enum_step_nth
                                 less_Suc_eq_le getFreeRef_def
                                 getFreeIndex_def nth_rev
                                 conj_comms invs_pspace_aligned' invs_pspace_distinct'
                                 invs_valid_pspace')
           apply (frule(1) reset_untyped_inner_offs_helper[OF _ order_refl], simp+)
           apply (frule ctes_of_valid', clarify+)
           apply (clarsimp simp: valid_cap_simps' capAligned_def
                                 is_aligned_mask_out_add_eq[OF is_aligned_weaken]
                                 aligned_bump_down Aligned.is_aligned_neg_mask
                                 is_aligned_mask_out_add_eq_sub[OF is_aligned_weaken])
           apply (simp add: field_simps)
           apply (strengthen Aligned.is_aligned_neg_mask unat_le_helper)
           apply (simp add: minUntypedSizeBits_def Kernel_Config.resetChunkBits_def[unfolded atomize_eq, THEN arg_cong[where f="\<lambda>x. n \<le> x" for n]])
           apply (rule order_less_imp_le, erule order_le_less_trans[rotated],
             rule olen_add_eqv[THEN iffD2])
           apply (rule order_trans, rule word_mult_le_mono1, rule word_of_nat_le,
             erule order_trans[rotated], simp, simp add: Kernel_Config.resetChunkBits_def)
            apply (simp only: unat_power_lower64 shiftr_div_2n_w[symmetric]
                              word_size word_bits_def[symmetric])
            apply (rule nat_less_power_trans2)
             apply (rule order_less_le_trans[OF word_shiftr_lt])
             apply (simp add: word_bits_def)
            apply (simp add: word_bits_def Kernel_Config.resetChunkBits_def)
           apply (simp add: field_simps)
          apply ceqv
         apply (rule ccorres_return_CE, simp+)[1]
        apply wp
       apply (simp add: ccHoarePost_def guard_is_UNIV_def)
      apply simp

      apply (strengthen invs_valid_objs' invs_urz)
      apply ((rule_tac d="capIsDevice (cteCap cte)" and idx="capFreeIndex (cteCap cte)" in
                deleteObject_no_overlap
        | rule_tac d="capIsDevice (cteCap cte)" and idx="capFreeIndex (cteCap cte)" in
                deleteObjects_cte_wp_at'
        | wp (once) hoare_vcg_const_imp_lift
                hoare_vcg_conj_lift
        | wp (once) deleteObjects_invs'[where p=slot]
                 deleteObjects_descendants[where p=slot]
        | strengthen exI[mk_strg I])+)[1]
     apply (simp add: word_sle_def)
     apply vcg
    apply simp
    apply vcg
   apply (rule conseqPre, vcg, clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (frule if_unsafe_then_capD', clarsimp+)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply ((strengthen refl eq_UntypedCap_helper
             eq_UntypedCap_helper[symmetric] | simp)+)?
   apply (frule ctes_of_valid', clarsimp+)
   apply (simp add: exI)?
   apply (clarsimp simp: isCap_simps valid_cap_simps' capAligned_def
                         conj_comms invs_valid_pspace'
                         descendants_range'_def2
                         empty_descendants_range_in'
                         getFreeRef_def upto_intvl_eq)
   apply (frule valid_global_refsD_with_objSize, clarsimp+)
   apply (strengthen order_le_less_trans[where z="2 ^ n" for n, mk_strg I E]
     order_trans[rotated, where z="gsMaxObjectSize s" for s, mk_strg I E])
   apply (strengthen power_strict_increasing
            | simp)+
   apply (clarsimp simp: word_bits_def maxUntypedSizeBits_def minUntypedSizeBits_def)
   apply (subgoal_tac "capPtr (cteCap cte) \<le> getFreeRef (capPtr (cteCap cte))
       (capFreeIndex (cteCap cte)) - 1")
    apply (case_tac "the (ctes_of s slot)", simp)
    apply (frule(3) ex_cte_not_in_untyped_range, clarsimp+)
    apply (strengthen is_aligned_no_wrap'[where off="a - b" for a b,
        simplified field_simps, mk_strg I E])
    apply (simp add: getFreeRef_def nth_rev length_upto_enum_step
                     upto_enum_step_nth word_of_nat_le
                     is_aligned_mask_out_add_eq_sub[OF is_aligned_weaken])
    apply (simp add: neg_mask_is_div' Kernel_Config.resetChunkBits_def word_size)
    apply (safe, simp_all)[1]
   apply (simp add: getFreeRef_def)
   apply (strengthen is_aligned_no_wrap'[where off="a - b" for a b,
       simplified field_simps, mk_strg I E])
   apply (simp add: word_of_nat_le)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule(1) rf_sr_ctes_of_clift, clarsimp)
  apply (frule(2) rf_sr_cte_relation)
  apply (clarsimp simp: typ_heap_simps'
                 dest!: ccte_relation_ccap_relation)
  apply (strengthen typ_region_bytes_actually_is_bytes)
  apply (simp add: hrs_htd_update hrs_mem_update exI)
  apply (frule(1) isUntypedCap_ccap_relation_helper)
  apply (frule ctes_of_valid', clarify+)
  apply (frule valid_global_refsD_with_objSize, clarsimp)
  apply (clarsimp simp: valid_cap_simps' isCap_simps capAligned_def
                        from_bool_0 cap_to_H_simps)
  apply (frule(1) ghost_assertion_size_logic_no_unat)
  apply (simp add: ghost_assertion_data_get_def gs_clear_region_def)
  apply (strengthen is_aligned_no_overflow'
                    typ_region_bytes_dom_s
                    aligned_intvl_offset_subset
                    region_is_bytes_typ_region_bytes
                    intvl_start_le is_aligned_power2
                    heap_list_is_zero_mono[OF heap_list_update_eq]
                    byte_regions_unmodified_actually_heap_list[OF _ _ refl, mk_strg I E]
                    typ_region_bytes_actually_is_bytes[OF refl]
                    region_actually_is_bytes_subset[OF typ_region_bytes_actually_is_bytes[OF refl]]
    | simp add: unat_of_nat imp_conjL hrs_mem_update hrs_htd_update)+
  apply (simp add: maxUntypedSizeBits_def minUntypedSizeBits_def)
  apply (rule conjI; clarsimp)
  apply (rule conjI, erule is_aligned_weaken, simp)
  by (clarsimp simp: order_trans[OF power_increasing[where a=2]]
                     addr_card_def card_word
                     is_aligned_weaken from_bool_0)

lemma ccorres_cross_retype_zero_bytes_over_guard:
  "range_cover ptr sz (APIType_capBits newType userSize) num_ret
    \<Longrightarrow> ccorres_underlying rf_sr Gamm rvr xf arrel axf P' Q hs af cf
    \<Longrightarrow> ccorres_underlying rf_sr Gamm rvr xf arrel axf
        ((\<lambda>s. invs' s
      \<and> cte_wp_at' (\<lambda>cte. \<exists>idx. cteCap cte = UntypedCap dev (ptr && ~~ mask sz) sz idx
          \<and> idx \<le> unat (ptr && mask sz)) p s) and P')
      {s'. (\<not> dev \<longrightarrow> region_actually_is_zero_bytes ptr
            (num_ret * 2 ^ APIType_capBits newType userSize) s')
         \<and> (\<exists>cte cte' idx. cslift s' (cte_Ptr p) = Some cte'
                 \<and> ccte_relation cte cte' \<and> cteCap cte = UntypedCap dev (ptr && ~~ mask sz) sz idx)
         \<longrightarrow> s' \<in> Q} hs af cf"
  apply (erule ccorres_guard_imp2)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule(1) rf_sr_ctes_of_clift, clarsimp)
  apply (frule(2) rf_sr_cte_relation)
  apply (case_tac dev)
   apply fastforce
  apply (frule(1) retype_offs_region_actually_is_zero_bytes, (simp | clarsimp)+)
  apply fastforce
  done

lemma zero_bytes_heap_update:
  "heap_list_is_zero (hrs_mem hrs) ptr n
    \<Longrightarrow> region_is_bytes' ptr n (hrs_htd hrs)
    \<Longrightarrow> h_t_valid (hrs_htd hrs) c_guard (cptr :: 'a ptr)
    \<Longrightarrow> typ_uinfo_t TYPE ('a :: mem_type) \<noteq> typ_uinfo_t TYPE(8 word)
    \<Longrightarrow> heap_list_is_zero (heap_update cptr v (hrs_mem hrs)) ptr n"
  apply (frule(2) region_is_bytes_disjoint)
  apply (clarsimp simp: heap_update_def)
  apply (subst heap_list_update_disjoint_same, simp_all)
  apply (simp add: Int_commute)
  done

lemma invokeUntyped_Retype_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and ct_active' and ex_cte_cap_to' cnodeptr
       and (\<lambda>s. case gsCNodes s cnodeptr of None \<Rightarrow> False
                  | Some n \<Rightarrow> length destSlots + unat start \<le> 2 ^ n)
       and valid_untyped_inv' (Retype cref reset ptr_base ptr newType us destSlots isdev)
       and K (isdev \<longrightarrow> (newType = APIObjectType ArchTypes_H.apiobject_type.Untyped \<or> isFrameType newType))
     )
     (UNIV \<inter>  {s. retypeBase_' s = Ptr ptr}
           \<inter>  {s. srcSlot_' s = Ptr cref}
           \<inter>  {s. reset_' s = from_bool reset}
           \<inter>  {s. newType_' s = object_type_from_H newType }
           \<inter>  {s. unat (userSize_' s) = us }
           \<inter>  {s. deviceMemory_' s = from_bool isdev}
           \<inter>  {s. destCNode_' s = cte_Ptr cnodeptr}
           \<inter>  {s. destOffset_' s = start \<and> (\<forall>n < length destSlots. destSlots ! n = cnodeptr + (start + of_nat n) * 2^cteSizeBits)}
           \<inter>  {s. destLength_' s = of_nat (length destSlots)})
     []
     (invokeUntyped (Retype cref reset ptr_base ptr newType us destSlots isdev))
     (Call invokeUntyped_Retype_'proc)"
  (is "ccorres _ _ _ ?P' [] _ _")
  apply (rule ccorres_name_pre)
  apply (clarsimp simp only: valid_untyped_inv_wcap')
  proof -
    fix s sz idx cte
    assume vui1: "valid_untyped_inv_wcap'
         (Invocations_H.untyped_invocation.Retype cref reset ptr_base ptr newType us destSlots isdev)
         (Some (case Invocations_H.untyped_invocation.Retype cref reset ptr_base ptr newType us destSlots
                      isdev of
                Invocations_H.untyped_invocation.Retype slot reset ptr_base ptr ty us slots d \<Rightarrow>
                  capability.UntypedCap d (ptr && ~~ mask sz) sz idx))
         s"
      and misc1[simplified]: "ct_active' s" "invs' s" "ex_cte_cap_to' cnodeptr s"
      "case gsCNodes s cnodeptr of None \<Rightarrow> False
        | Some n \<Rightarrow> length destSlots + unat start \<le> 2 ^ n"
     "K (isdev \<longrightarrow> (newType = APIObjectType ArchTypes_H.apiobject_type.Untyped \<or> isFrameType newType)) s"

    have vui: "valid_untyped_inv_wcap' (Retype cref reset ptr_base ptr newType us destSlots isdev)
        (Some (UntypedCap isdev (ptr && ~~ mask sz) sz idx)) s"
      using vui1
      by (clarsimp simp: cte_wp_at_ctes_of)

    have proofs: "invokeUntyped_proofs s cref reset ptr_base ptr newType us destSlots sz idx isdev"
      using vui misc1
      by (clarsimp simp: cte_wp_at_ctes_of invokeUntyped_proofs_def)

   note no_simps[simp del] = untyped_range.simps usable_untyped_range.simps
         atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
         Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
         usableUntypedRange.simps

    have cover:
      "range_cover ptr sz (APIType_capBits newType us) (length destSlots)"
      using vui
      by (clarsimp simp: cte_wp_at_ctes_of)

    have us_misc:
      "newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < us"
      "newType = APIObjectType apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits"
      using vui
      by (auto simp: cte_wp_at_ctes_of untypedBits_defs)

    note bits_low = APIType_capBits_low[OF us_misc]

    have misc2:
      "destSlots \<noteq> []" "ptr_base && ~~ mask sz = ptr_base"
      using vui
      by (clarsimp simp: cte_wp_at_ctes_of)+

    note misc = misc1 misc2

    have us_misc':
      "(newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> us < 59)"
      using cover
      apply -
      apply (drule range_cover_sz')
      apply (clarsimp simp:APIType_capBits_def objBits_simps' word_bits_conv)
      done

    have ptr_base_eq:
      "ptr_base = ptr && ~~ mask sz"
      using vui
      by (clarsimp simp: cte_wp_at_ctes_of)+

    have ptr_in_km:
      "(ptr && ~~ mask sz) \<in> kernel_mappings"
      using vui misc
      apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (frule Finalise_R.ctes_of_valid', clarsimp)
      apply (clarsimp simp: valid_cap_simps')
      done

    have sz_bound:
      "sz \<le> 38"
      using vui misc
      apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (frule Finalise_R.ctes_of_valid', clarsimp)
      apply (clarsimp simp: valid_cap_simps' untypedBits_defs)
      done

    have APIType_capBits_max:
      "APIType_capBits newType us \<le> maxUntypedSizeBits"
      using vui by clarsimp

    have some_range_cover_arithmetic:
      "(ptr + (of_nat (length destSlots) << unat (of_nat (APIType_capBits newType us) :: addr))
          - ptr_base >> 4) && mask 39
      = of_nat (getFreeIndex ptr_base
          (ptr + of_nat (shiftL (length destSlots)
              (APIType_capBits newType us)))) >> 4"
      using cover range_cover_sz'[OF cover]
      apply (simp add: getFreeIndex_def shiftl_t2n
                       unat_of_nat_eq shiftL_nat)
      apply (rule less_mask_eq)
      apply (rule shiftr_less_t2n)
      apply (rule order_le_less_trans[where y="2 ^ sz"])
       apply (rule order_trans[OF _ range_cover_compare_bound_word[OF cover]])
       apply (simp add: ptr_base_eq mask_out_sub_mask mult.commute)
      apply (simp add: word_less_nat_alt order_le_less_trans[OF sz_bound])
      apply (rule order_less_le_trans, rule power_strict_increasing,
        rule order_le_less_trans[OF sz_bound lessI], simp+)
      done

    show
      "ccorres (cintr \<currency> dc)
         (liftxf errstate id (K ()) ret__unsigned_long_') (\<lambda>s'. s' = s) ?P'
         [] (invokeUntyped (Retype cref reset ptr_base ptr newType us destSlots isdev))
            (Call invokeUntyped_Retype_'proc)"
      apply (cinit lift: retypeBase_' srcSlot_' reset_' newType_'
                         userSize_' deviceMemory_' destCNode_' destOffset_' destLength_'
                   simp: when_def archOverlap_def)
       apply (rule ccorres_move_c_guard_cte)
       apply csymbr
       apply (rule ccorres_abstract_cleanup)
       apply (rename_tac ptr_fetch,
         rule_tac P="ptr_fetch = ptr_base" in ccorres_gen_asm2)
       apply csymbr
       apply csymbr
       apply (simp add: from_bool_0 del: Collect_const)
       apply (rule_tac xf'=xfdc and r'=dc in ccorres_splitE)
           apply (rule ccorres_Cond_rhs)
            apply (simp add: whenE_def)
            apply (rule ccorres_add_returnOk)
            apply (ctac add: resetUntypedCap_ccorres)
               apply (simp add: ccorres_cond_empty_iff)
               apply (rule ccorres_returnOk_skip)
              apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: throwError_def return_def cintr_def)
             apply wp
            apply (vcg exspec=resetUntypedCap_modifies)
           apply (simp add: whenE_def)
           apply (rule ccorres_returnOk_skip)
          apply ceqv
         apply (simp add: liftE_def bind_assoc)
         apply csymbr
         apply (rule ccorres_Guard_Seq)
         apply csymbr
         apply csymbr
         apply (rule ccorres_move_c_guard_cte)
         apply (rule ccorres_stateAssert)
         apply (rule ccorres_assert)

         apply (rule ccorres_cross_retype_zero_bytes_over_guard[where
             dev=isdev and p=cref, OF cover])
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
             apply (rule_tac cap'="UntypedCap isdev ptr_base sz (if reset then 0 else idx)"
                  in updateFreeIndex_ccorres)
             apply (rule allI, rule conseqPre, vcg)
             apply (rule subsetI, clarsimp simp: typ_heap_simps' isCap_simps)
             apply (frule ccte_relation_ccap_relation)
             apply clarsimp
             apply (frule cap_get_tag_isCap_unfolded_H_cap)
             apply (cut_tac some_range_cover_arithmetic)
             apply (case_tac cte', clarsimp simp: modify_map_def fun_eq_iff split: if_split)
             apply (simp add: mex_def meq_def ptr_base_eq)
             apply (rule exI, strengthen refl, simp)
             apply (strengthen globals.fold_congs, simp add: field_simps)
            apply ceqv
           apply (ctac add: createNewObjects_ccorres[where sz = sz and
                            start = start and cnodeptr=cnodeptr and
                            num = "of_nat (length destSlots)"
                            and idx = "getFreeIndex ptr_base
                                 (ptr + of_nat (shiftL (length destSlots) (APIType_capBits newType us)))"])
             apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: return_def)
            apply wp
           apply (vcg exspec=createNewObjects_modifies)
          apply (simp add: canonicalAddressAssert_def)
          (* strengthen canonical_address (ptr && ~~ mask sz) now, while we have canonical ptr *)
          apply (drule canonical_address_neq_mask[where sz=sz])
           apply (rule sz_bound[folded maxUntypedSizeBits_def])
          apply clarsimp
          apply (wp updateFreeIndex_forward_invs' sch_act_simple_lift
                    updateFreeIndex_cte_wp_at hoare_vcg_const_Ball_lift
                    updateFreeIndex_pspace_no_overlap'
                    updateFreeIndex_caps_no_overlap''
                    updateFreeIndex_caps_overlap_reserved
                    updateFreeIndex_descendants_range_in'
                  | simp)+
         apply (clarsimp simp: misc unat_of_nat_eq[OF range_cover.weak, OF cover])
         apply (vcg exspec=cap_untyped_cap_ptr_set_capFreeIndex_modifies)
        apply simp
        apply (rule validE_validE_R, rule hoare_strengthen_postE,
               rule hoare_vcg_conj_liftE1[rotated, where Q="\<lambda>_ s.
                 case gsCNodes s cnodeptr of None \<Rightarrow> False
                   | Some n \<Rightarrow> length destSlots + unat start \<le> 2 ^ n"],
               rule whenE_reset_resetUntypedCap_invs_etc
                   [where ui="Retype cref reset ptr_base ptr newType us destSlots isdev"
                      and dev=isdev and ptr="ptr && ~~ mask sz" and ptr'=ptr and sz=sz and idx=idx])
          apply (simp add: whenE_def, wp resetUntypedCap_gsCNodes_at_pt)[1]
         prefer 2
         apply simp
        apply (clarsimp simp only: )
        apply (frule(2) invokeUntyped_proofs.intro)
        apply (cut_tac bits_low us_misc us_misc')
        apply (clarsimp simp: cte_wp_at_ctes_of
                              invokeUntyped_proofs.caps_no_overlap'
                              invokeUntyped_proofs.ps_no_overlap'
                              invokeUntyped_proofs.descendants_range
                              if_split[where P="\<lambda>v. v \<le> getFreeIndex x y" for x y]
                              empty_descendants_range_in'
                              invs_pspace_aligned' invs_pspace_distinct'
                              invs_ksCurDomain_maxDomain'
                              invokeUntyped_proofs.not_0_ptr
                              atLeastAtMost_iff[where i=0]
                        cong: if_cong)
        apply (frule invokeUntyped_proofs.idx_le_new_offs)
        apply (frule invokeUntyped_proofs.szw)
        apply (frule invokeUntyped_proofs.descendants_range(2), simp)
        apply (simp add: cNodeNoOverlap_retype_have_size shiftL_nat mult.commute)
        apply (clarsimp simp: getFreeIndex_def conj_comms shiftL_nat
                              is_aligned_weaken[OF range_cover.funky_aligned]
                              invs_valid_pspace' isCap_simps
                              arg_cong[OF mask_out_sub_mask, where f="\<lambda>y. x - y" for x]
                              field_simps unat_of_nat_eq[OF range_cover.weak, OF cover]
                              if_apply_def2 invs_valid_objs' ptr_base_eq sz_bound
                              ptr_in_km
                              invs_urz untypedBits_defs)

        apply (intro conjI; (solves\<open>clarsimp simp: mask_2pm1 field_simps\<close>)?)
                  (* pspace_no_overlap *)
                  apply (cases reset, simp_all)[1]
                 (* is_aligned 4 *)
                 apply (erule is_aligned_weaken[OF range_cover.aligned])
                 apply (clarsimp simp: APIType_capBits_low)
                (* new idx le *)
                apply (clarsimp split: if_split)
               (* cnodeptr not in area *)
               apply (rule contra_subsetD[rotated],
                      rule invokeUntyped_proofs.ex_cte_no_overlap'[OF proofs], rule misc)
               apply (simp add: shiftl_t2n mult.commute)
               apply (rule order_trans, erule range_cover_subset', simp_all)[1]
               apply (clarsimp simp: mask_2pm1 field_simps)
              (* descendants_range_in' *)
              using invokeUntyped_proofs.descendants_range
              apply (clarsimp simp: mask_2pm1 field_simps)
             (* gsCNodes *)
             apply (clarsimp simp: mask_2pm1 field_simps split: option.split_asm)
            (* kernel data refs *)
            apply (drule(1) valid_global_refsD'[OF _ invs_valid_global'])
            apply clarsimp
            apply (clarsimp simp: mask_2pm1 field_simps)
            apply (subst Int_commute, erule disjoint_subset2[rotated])
            apply (rule order_trans, erule invokeUntyped_proofs.subset_stuff)
            apply (simp add: atLeastatMost_subset_iff word_and_le2)
            apply (clarsimp simp: mask_2pm1 field_simps)
           (* offset bounds *)
           apply (frule range_cover.unat_of_nat_n_shift, rule order_refl)
           apply (rule order_trans[rotated], erule range_cover.range_cover_compare_bound)
           apply (subst unat_plus_simple[THEN iffD1])
            apply (rule order_trans, erule range_cover.range_cover_base_le,
              simp add: shiftl_t2n field_simps)
           apply (simp add: shiftl_t2n field_simps)
          (* subsets *)
          apply (rule order_trans, erule invokeUntyped_proofs.subset_stuff)
          apply (simp add: atLeastatMost_subset_iff word_and_le2)
          apply (clarsimp simp: mask_2pm1 field_simps)
         (* destSlots *)
         apply (clarsimp split: if_split)
         apply (frule invokeUntyped_proofs.slots_invD[OF proofs])
         apply (simp add: conj_comms)
        (* usableUntyped *)
        apply (drule invokeUntyped_proofs.usableRange_disjoint[where d=isdev])
        apply (clarsimp simp: field_simps mask_out_sub_mask)

       (* clean up the C postcondition before applying VCG *)
       apply (rule conseqPost[where Q'=UNIV and Q'=UNIV])
         apply (vcg exspec=resetUntypedCap_modifies)
        apply (cut_tac range_cover.sz[OF cover]
                       invokeUntyped_proofs.idx_le_new_offs[OF proofs])
        apply (clarsimp simp: ccHoarePost_def hrs_mem_update
                              object_type_from_H_bound
                              typ_heap_simps' word_sle_def
                              word_of_nat_less zero_bytes_heap_update
                              region_actually_is_bytes)
        apply (frule ccte_relation_ccap_relation)
        apply (cut_tac vui)
        apply (clarsimp simp: cap_get_tag_isCap getFreeIndex_def
                              cte_wp_at_ctes_of shiftL_nat
                       split: if_split)
        apply (simp add: mask_out_sub_mask field_simps region_is_bytes'_def objBits_defs)
        apply (clarsimp elim!: region_actually_is_bytes_subset)
       apply (rule order_refl)

      apply (cut_tac misc us_misc' proofs us_misc bits_low
                     invokeUntyped_proofs.cref_inv[OF proofs])
      apply (clarsimp simp: cte_wp_at_ctes_of invokeUntyped_proofs_def
                            descendants_range'_def2 sch_act_simple_def
                            invs_valid_pspace' range_cover.sz)
      apply (frule ctes_of_valid', fastforce)
      apply (clarsimp simp: valid_cap'_def capAligned_def ct_in_state'_def
                            invs_valid_objs' inr_rrel_def)
      apply (erule(1) rf_sr_ctes_of_cliftE)
      apply (frule(2) rf_sr_cte_relation)
      apply (clarsimp simp: cap_get_tag_isCap typ_heap_simps
                     dest!: ccte_relation_ccap_relation)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)

      apply (intro conjI)
       apply clarsimp
       apply (drule invokeUntyped_proofs.ex_cte_no_overlap'[OF proofs])
       apply simp
       apply (clarsimp simp: mask_2pm1 field_simps)
      apply (frule(1) cap_get_tag_to_H)
      apply (simp add: cap_lift_untyped_cap)
      apply clarsimp
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
                   unif_rrel_def split: if_split_asm)
  done

lemmas ccorres_return_C_errorE_inl_rrel
    = ccorres_throwError_inl_rrel[OF ccorres_return_C_errorE]

lemma mapME_ensureEmptySlot':
  "\<lbrace>P\<rbrace>
  mapME (\<lambda>x. injection_handler Inl (ensureEmptySlot (f x))) slots
  \<lbrace>\<lambda>rva s. P s \<and> (\<forall>slot \<in> set slots. (\<exists>cte. cteCap cte = capability.NullCap \<and> ctes_of s (f slot) = Some cte))\<rbrace>, -"
  including no_pre
  apply (induct slots arbitrary: P)
   apply wpsimp
  apply (rename_tac a slots P)
  apply (simp add: mapME_def sequenceE_def Let_def)
  apply (rule_tac Q="\<lambda>rv. P and (\<lambda>s. \<exists>cte. cteCap cte = capability.NullCap \<and> ctes_of s (f a) = Some cte)" in validE_R_sp)
   apply (simp add: ensureEmptySlot_def unlessE_def)
   apply (wp injection_wp_E[OF refl] getCTE_wp')
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule meta_allE)
  apply wp
  apply (fold validE_R_def)
  apply (erule hoare_strengthen_postE_R)
  apply clarsimp
  done

lemma mapME_ensureEmptySlot:
  "\<lbrace>\<top>\<rbrace>
  mapME (\<lambda>x. injection_handler Inl (ensureEmptySlot (f x))) [S .e. (E::machine_word)]
  \<lbrace>\<lambda>rva s. \<forall>slot. S \<le> slot \<and> slot \<le> E \<longrightarrow>
           (\<exists>cte. cteCap cte = capability.NullCap \<and> ctes_of s (f slot) = Some cte)\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R)
   apply (rule mapME_ensureEmptySlot')
  apply clarsimp
  done

lemma capCNodeRadix_CL_less_64:
  "cap_get_tag ccap = scast cap_cnode_cap \<Longrightarrow> capCNodeRadix_CL (cap_cnode_cap_lift ccap) < 64"
  apply (simp add: cap_cnode_cap_lift_def cap_lift_cnode_cap)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply (simp add: mask_def)
  done

lemmas unat_capCNodeRadix_CL_less_64
    = capCNodeRadix_CL_less_64[unfolded word_less_nat_alt, simplified]

lemmas capCNodeRadix_CL_less_64s
    = capCNodeRadix_CL_less_64 unat_capCNodeRadix_CL_less_64
      linorder_not_le[THEN iffD2, OF capCNodeRadix_CL_less_64]
      linorder_not_le[THEN iffD2, OF unat_capCNodeRadix_CL_less_64]

lemma TripleSuc:
  "Suc (Suc (Suc 0)) = 3"
  by simp

lemma case_sum_distrib:
  "case_sum a b x >>= f = case_sum (\<lambda>x. a x >>= f) (\<lambda>x. b x >>= f) x"
  by (case_tac x,simp+)

lemma alignUp_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. alignment_' s < 0x40 \<rbrace> Call alignUp_'proc
         \<lbrace>\<acute>ret__unsigned_long = alignUp (baseValue_' s) (unat (alignment_' s))\<rbrace>"
  apply vcg
  apply (simp add:alignUp_def2 mask_def field_simps)
  done

lemma checkFreeIndex_ccorres:
  "ccap_relation cp cap \<Longrightarrow>
  ccorresG rf_sr \<Gamma> (intr_and_se_rel \<currency> (\<lambda>r (fi, r'). r' = from_bool r
          \<and> (case r of True \<Rightarrow> fi = 0 | False \<Rightarrow> capFreeIndex cp = unat (fi << 4))))
      (liftxf errstate (K (scast EXCEPTION_NONE)) id (\<lambda>s. (freeIndex_' s, reset_' s)))
  (cte_wp_at' (\<lambda>cte. (cteCap cte = cp \<and> isUntypedCap cp)) slot and valid_objs' and valid_mdb') UNIV hs
  (liftE $ constOnFailure False (doE y \<leftarrow> ensureNoChildren slot; returnOk True odE))
  (\<acute>status :== CALL ensureNoChildren(cte_Ptr slot);;
  (Cond \<lbrace>\<acute>status \<noteq> scast EXCEPTION_NONE\<rbrace>
    ( \<acute>ret__unsigned_longlong :== CALL cap_untyped_cap_get_capFreeIndex(cap);;
      \<acute>freeIndex :== \<acute>ret__unsigned_longlong;;
      \<acute>reset :== scast false)
    (\<acute>freeIndex :== 0
        ;; \<acute>reset :== scast true)))"
  apply (simp add: constOnFailure_def catch_def liftE_def bindE_bind_linearise bind_assoc case_sum_distrib)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_split_nothrow_case_sum)
        apply (ctac add:ensureNoChildren_ccorres)
       apply (ceqv)
      apply (rule ccorres_from_vcg[where P' = UNIV])
      apply (clarsimp simp add: returnOk_def, simp add: return_def)
      apply (rule conseqPre)
       apply vcg
      apply clarsimp
     apply simp
     apply (rule ccorres_from_vcg[where P'= UNIV])
     apply (simp, clarsimp simp:return_def)
     apply (rule conseqPre)
      apply vcg
     apply clarsimp
     apply (rule context_conjI)
      apply (clarsimp simp:cap_get_tag_isCap)
      apply assumption
     apply (clarsimp simp: ccap_relation_def isCap_simps cap_untyped_cap_lift_def cap_lift_def
                           cap_to_H_def
                     split: if_splits
                     cong: if_cong)
    apply (rule ensureNoChildren_wp[where P = dc])
   apply clarsimp
   apply (vcg exspec=ensureNoChildren_modifies)
  apply (clarsimp simp: cte_wp_at_ctes_of)
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
    \<and> of_nat (2^capBlockSize cp - z) = (2::machine_word) ^ capBlockSize cp - of_nat z"
  apply (clarsimp simp:valid_cap'_def isCap_simps)
  apply (rule le_less_trans[OF diff_le_self])
  apply (rule power_strict_increasing)
   apply (simp add:word_bits_def)
   apply (simp add: untypedBits_defs)+
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
  "unat v \<le> (fromEnum::object_type \<Rightarrow> nat) maxBound
  \<Longrightarrow> toEnum (unat v) = (object_type_to_H (v::machine_word))"
  apply (simp add:enum_object_type enum_apiobject_type object_type_to_H_def toEnum_def
                  maxBound_less_length)
  apply (clarsimp simp: Kernel_C_defs split:if_splits)
  apply unat_arith
  done

lemma unat_of_nat_APIType_capBits:
  "b \<le> word_bits
  \<Longrightarrow> unat (of_nat (APIType_capBits z b) ::machine_word) = APIType_capBits z b"
  apply (rule unat_of_nat64)
  apply (case_tac z)
  apply (clarsimp simp: invokeUntyped_proofs_def word_bits_conv APIType_capBits_def objBits_simps'
                        bit_simps
                 split: apiobject_type.splits)+
  done

lemma valid_untyped_inv'_D:
  "valid_untyped_inv' (Retype cref reset ptr_base ptr ty us destSlots isdev) s
   \<Longrightarrow> APIType_capBits ty us < 64"
  apply clarsimp
  apply (drule range_cover_sz')
  apply (simp add:word_bits_def)
  done

lemma  object_type_from_to_H:
  "unat v \<le> (fromEnum::object_type \<Rightarrow> nat) maxBound
         \<Longrightarrow> v = object_type_from_H (object_type_to_H v)"
  apply (simp add:toEnum_object_type_to_H[symmetric])
  apply (rule iffD1[OF word_unat.Rep_inject])
  apply (subst fromEnum_object_type_to_H[symmetric])
  apply (simp add:from_to_enum)
  done

lemma shiftR_gt0_le64:
  "\<lbrakk>0 < unat (of_nat (shiftR a b ));a < 2 ^ word_bits\<rbrakk> \<Longrightarrow> b< 64"
  apply (rule ccontr)
  apply (clarsimp simp:not_less shiftR_nat)
  apply (subst (asm) div_less)
   apply (erule less_le_trans)
   apply (rule power_increasing)
    apply (simp add:word_bits_def)+
  done

lemma shiftr_overflow:
  "64\<le> a \<Longrightarrow> (b::machine_word) >> a = 0"
  apply (word_bitwise)
  apply simp
  done

lemma ctes_of_ex_cte_cap_to':
  "ctes_of s p = Some cte \<Longrightarrow> \<forall>r \<in> cte_refs' (cteCap cte) (irq_node' s). ex_cte_cap_to' r s"
  by (auto simp add: ex_cte_cap_wp_to'_def cte_wp_at_ctes_of)


lemma Arch_isFrameType_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. unat \<acute>type \<le> fromEnum (maxBound::object_type)\<rbrace>
             Call Arch_isFrameType_'proc
  \<lbrace> \<acute>ret__unsigned_long =
     from_bool (isFrameType ((toEnum (unat \<^bsup>s\<^esup> type))::object_type))\<rbrace>"
  apply vcg
  apply (simp add: toEnum_object_type_to_H)
  apply (frule object_type_from_to_H)
  apply (auto dest!: object_type_from_H_toAPIType_simps[THEN iffD1,OF eq_commute[THEN iffD1]])
  apply (auto simp: object_type_to_H_def isFrameType_def isFrameType_def
             split: if_splits object_type.splits)
  apply (auto simp: object_type_from_H_def )
  done

lemma decodeUntypedInvocation_ccorres_helper:
  notes TripleSuc[simp]
  notes valid_untyped_inv_wcap'.simps[simp del] tl_drop_1[simp]
  notes gen_invocation_type_eq[simp]
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
             \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. ccap_relation cp (cap_' s)}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       []
       ((doE uinv \<leftarrow> decodeUntypedInvocation label args slot cp (map fst extraCaps);
           liftE (stateAssert (valid_untyped_inv' uinv) []); returnOk uinv odE)
           >>= invocationCatch thread isBlocking isCall InvokeUntyped)
  (Call decodeUntypedInvocation_'proc)"
  supply if_cong[cong] option.case_cong[cong]
  apply (rule ccorres_name_pre)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cap_' slot_' current_extra_caps_' call_' buffer_'
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
               apply csymbr
               apply ((rule ccorres_Guard_Seq)+)?
               apply (subst whenE_whenE_body)
               apply (rule ccorres_split_when_throwError_cond
                               [where Q=\<top> and Q'=\<top>, rotated -1])
                  apply vcg
                 apply (clarsimp simp: word_size Collect_const_mem fromIntegral_def integral_inv
                                       hd_drop_conv_nth2 word_le_nat_alt maxUntypedSizeBits_def
                                       toEnum_object_type_to_H wordBits_def not_less[symmetric])
                 apply (subst hd_conv_nth, clarsimp)
                 apply (simp add: unat_of_nat_APIType_capBits word_bits_def)
                apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                apply (rule allI, rule conseqPre, vcg)
                apply (clarsimp simp: throwError_def return_def maxUntypedSizeBits_def
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
                                  fromAPIType_def RISCV64_H.fromAPIType_def)
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
                                  object_type_from_H_def untypedBits_defs
                                  fromAPIType_def RISCV64_H.fromAPIType_def)
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
                        apply (simp add: liftE_liftM split_def hd_drop_conv_nth2
                                   cong: ccorres_all_cong)
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
                  apply (rule le_64_mask_eq)
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
                   apply (simp add: Kernel_Config.retypeFanOutLimit_def word_le_nat_alt
                                    linorder_not_le)
                   apply (auto simp: linorder_not_le unat_eq_0)[1]
                  apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                  apply (rule allI, rule conseqPre, vcg)
                  apply (clarsimp simp: throwError_def return_def
                                        syscall_error_rel_def exception_defs
                                        syscall_error_to_H_cases)
                  apply (simp add: Kernel_Config.retypeFanOutLimit_def)
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
                 apply (simp add: mapM_locate_eq liftE_bindE
                                  injection_handler_sequenceE mapME_x_sequenceE
                                  whileAnno_def injection_bindE[OF refl refl]
                                  bindE_assoc injection_handler_returnOk)
                 (* gsCNodes assertion *)
                 apply (rule ccorres_stateAssert)
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
                     apply (rule_tac F="\<lambda>_ s. case gsCNodes s (RetypeDecls_H.capUntypedPtr rv) of
                           None \<Rightarrow> False | Some n \<Rightarrow> args ! 4 + args ! 5 - 1 < 2 ^ n"
                               in ccorres_sequenceE_while_gen'
                                     [where i="unat (args ! 4)" and xf'=xfdc
                                       and xf_update="i_'_update" and xf="i_'"
                                       and r'=dc and Q=UNIV])
                           apply simp
                           apply (rule ccorres_guard_imp2)
                            apply (rule ccorres_add_returnOk)
                            apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+
                            apply (ctac add: ccorres_injection_handler_csum1
                                                  [OF ensureEmptySlot_ccorres])
                               apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+
                               apply (simp add: ccorres_cond_iffs returnOk_def)
                               apply (rule ccorres_return_Skip')
                              apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+
                              apply (simp add: ccorres_cond_iffs inl_rrel_inl_rrel)
                              apply (rule ccorres_return_C_errorE_inl_rrel,
                                     simp+)[1]
                             apply wp
                            apply (simp add: all_ex_eq_helper)
                            apply (vcg exspec=ensureEmptySlot_modifies)
                           apply (clarsimp simp: upto_enum_word
                                          split: if_split_asm simp del: upt.simps)
                           apply (simp add: cte_level_bits_def field_simps size_of_def
                                            numeral_eqs[symmetric])
                           apply (simp add: cap_get_tag_isCap[symmetric]
                                     split: option.split_asm)
                           apply (drule(1) rf_sr_gsCNodes_array_assertion)
                           apply (drule(1) cap_get_tag_to_H)
                           apply clarsimp
                           apply (subgoal_tac P for P)
                            apply (subst array_assertion_shrink_right, assumption, assumption)
                            apply (simp add: array_assertion_shrink_right)
                           apply (rule unat_le_helper, simp)
                           apply (erule order_trans[rotated])
                           apply (subst add.commute, rule word_plus_mono_right)
                            apply (simp add: unat_plus_simple[THEN iffD1] olen_add_eqv[symmetric])
                            apply (simp add: word_le_nat_alt unat_of_nat)
                           apply (simp add: olen_add_eqv[symmetric])
                          apply (clarsimp simp add: upto_enum_word
                                          simp del: upt.simps)
                          apply (simp add: word_less_nat_alt[symmetric] numeral_eqs[symmetric])
                          apply (simp add: Suc_unat_diff_1)
                          apply (subst iffD1 [OF unat_plus_simple])
                           apply (erule iffD2 [OF olen_add_eqv])
                          apply simp
                         apply (rule conseqPre, vcg exspec=ensureEmptySlot_modifies)
                         apply clarsimp
                        apply simp
                        apply (wp injection_wp_E[OF refl])
                        apply (simp only: word_bits_def[symmetric])
                        apply clarsimp
                       apply (simp add: upto_enum_word numeral_eqs[symmetric]
                                   del: upt.simps)
                       apply (subst Suc_unat_diff_1)
                        apply clarsimp
                        apply unat_arith
                       apply (subst(asm) olen_add_eqv[symmetric])
                       apply (simp add: iffD1 [OF unat_plus_simple])
                       apply (simp add: iffD1 [OF unat_plus_simple, symmetric])
                       apply (simp only: word_bits_def)
                       apply (rule less_le_trans, rule unat_lt2p, simp)
                      apply simp
                     apply simp
                    apply (rule ceqv_refl)
                   apply (ctac (c_lines 2) add:checkFreeIndex_ccorres[unfolded fun_app_def])
                      apply (rename_tac reset reset_fi_tup)
                      apply (rule_tac xf'=reset_' in ccorres_abstract, ceqv)
                      apply (rule_tac xf'=freeIndex_' in ccorres_abstract, ceqv)
                      apply (rename_tac reset' fi', rule_tac P="reset_fi_tup = (fi', reset')"
                            in ccorres_gen_asm2)
                      apply csymbr
                      apply csymbr+
                      apply (rule ccorres_Guard_Seq)+
                      apply csymbr
                      apply (rule ccorres_Guard_Seq)
                      apply (rule_tac ccorres_split_when_throwError_cond[where Q = \<top> and Q' = \<top>])
                         apply (case_tac reset;
                                clarsimp simp: ccap_relation_untyped_CL_simps shiftL_nat
                                               valid_untyped_capBlockSize_misc
                                               valid_untyped_capBlockSize_misc[where z=0, simplified]
                                               of_nat_shiftR toEnum_object_type_to_H)
                          apply (subst hd_conv_nth, clarsimp)
                          apply (subst unat_of_nat_APIType_capBits,
                                 clarsimp simp: wordBits_def word_size word_bits_def)
                          apply simp
                         apply (subst hd_conv_nth, clarsimp)
                         apply (subst unat_of_nat_APIType_capBits,
                                clarsimp simp: wordBits_def word_size word_bits_def)
                         apply simp
                        apply (rule syscall_error_throwError_ccorres_n)
                        apply (case_tac reset; clarsimp simp: syscall_error_rel_def shiftL_nat
                                               ccap_relation_untyped_CL_simps syscall_error_to_H_cases
                                               valid_untyped_capBlockSize_misc)
                       apply csymbr
                       apply csymbr
                       apply csymbr
                       apply (rule ccorres_symb_exec_r)
                         apply (rule_tac xf'=ret__int_' in ccorres_abstract, ceqv)
                         apply (rule_tac P = "rv'b = from_bool (capIsDevice cp \<and>
                                              \<not> isFrameType (toEnum (unat (hd args))))"
                                         in ccorres_gen_asm2)
                         apply (rule_tac ccorres_split_when_throwError_cond[where Q = \<top> and Q' = \<top>])
                            apply (clarsimp simp: toEnum_eq_to_fromEnum_eq length_ineq_not_Nil
                                                  fromEnum_object_type_to_H from_bool_0
                                                  object_type_from_H_def hd_conv_nth
                                                  fromAPIType_def RISCV64_H.fromAPIType_def)
                           apply (rule syscall_error_throwError_ccorres_n)
                           apply (clarsimp simp: syscall_error_rel_def
                                                 ccap_relation_untyped_CL_simps shiftL_nat
                                                 syscall_error_to_H_cases )
                          apply csymbr
                          apply (simp add:liftE_bindE)
                          apply (rule ccorres_symb_exec_l)
                             apply (simp (no_asm) add: ccorres_invocationCatch_Inr split_def
                                                       performInvocation_def liftE_bindE bind_assoc)
                             apply (ctac add: setThreadState_ccorres)
                               apply (rule ccorres_trim_returnE, (simp (no_asm))+)
                               apply (simp (no_asm) add: bindE_assoc bind_bindE_assoc)
                               apply (rule ccorres_seq_skip'[THEN iffD1])
                               apply (ctac(no_vcg) add: invokeUntyped_Retype_ccorres[where start = "args!4"])
                                 apply (rule ccorres_alternative2)
                                 apply (rule ccorres_returnOk_skip)
                                apply (simp(no_asm) add: throwError_def, rule ccorres_return_Skip')
                               apply (rule hoare_vcg_conj_lift
                                      | rule_tac p="capCNodePtr rv" in setThreadState_cap_to'
                                      | wp (once) sts_invs_minor' setThreadStateRestart_ct_active'
                                                sts_valid_untyped_inv')+
                             apply (clarsimp simp: ccap_relation_untyped_CL_simps shiftL_nat
                                                   toEnum_object_type_to_H unat_of_nat_APIType_capBits
                                                   word_size valid_untyped_capBlockSize_misc
                                                   getFreeRef_def hd_conv_nth length_ineq_not_Nil)
                             apply (rule_tac conseqPost[where A' = "{}" and Q' = UNIV])
                               apply (vcg exspec=setThreadState_modifies)
                              apply (clarsimp simp: object_type_from_to_H cap_get_tag_isCap
                                                    ccap_relation_isDeviceCap)
                              apply (frule_tac cap = rv in cap_get_tag_to_H(5))
                               apply (simp add: cap_get_tag_isCap)
                              apply (simp add: field_simps Suc_unat_diff_1)
                              apply (rule conjI)
                               apply (clarsimp split: bool.split_asm
                                                simp: unat_of_nat_APIType_capBits wordBits_def
                                                      word_size word_bits_def)
                              apply (frule iffD2[OF olen_add_eqv])
                              apply (frule(1) isUntypedCap_ccap_relation_helper)
                              apply (clarsimp simp: unat_plus_simple[THEN iffD1])
                              apply (subst upto_enum_word)
                              apply (subst nth_map_upt)
                               apply (clarsimp simp: field_simps Suc_unat_diff_1 unat_plus_simple[THEN iffD1])
                              apply (clarsimp simp: cte_level_bits_def objBits_defs)
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
                      apply vcg
                     apply (rule ccorres_guard_imp
                         [where Q =\<top> and Q' = UNIV,rotated],assumption+)
                     apply simp
                    apply (simp add: liftE_validE)
                    apply (rule checkFreeIndex_wp)
                   apply (clarsimp simp: ccap_relation_untyped_CL_simps shiftL_nat cap_get_tag_isCap
                        toEnum_object_type_to_H unat_of_nat_APIType_capBits word_size
                        valid_untyped_capBlockSize_misc getFreeRef_def hd_conv_nth length_ineq_not_Nil)
                   apply (rule_tac Q' ="{sa.
                        ksCurThread_' (globals sa) = tcb_ptr_to_ctcb_ptr (ksCurThread s)}" in conseqPost[where
                         A' = "{}"])
                     apply (vcg exspec=ensureNoChildren_modifies
                                exspec=cap_untyped_cap_get_capFreeIndex_modifies)
                    apply (rule subsetI,
                       clarsimp simp:toEnum_object_type_to_H not_le word_sle_def
                                           enum_apiobject_type enum_object_type maxBound_is_length
                                           unat_of_nat_APIType_capBits word_size hd_conv_nth length_ineq_not_Nil
                       not_less word_le_nat_alt isCap_simps valid_cap_simps')
                    apply (strengthen word_of_nat_less)
                    apply (clarsimp simp: ThreadState_defs mask_def ccap_relation_isDeviceCap2
                                   split: if_split)
                    apply (clarsimp simp: not_less shiftr_overflow maxUntypedSizeBits_def
                                          unat_of_nat_APIType_capBits)
                    apply (intro conjI impI;
                           clarsimp simp: not_less shiftr_overflow unat_of_nat_APIType_capBits
                                          wordBits_def word_size word_bits_def)
                   apply simp
                  apply simp
                  apply (rule_tac Q'="\<lambda>r. cte_wp_at' (\<lambda>cte. cteCap cte = cp) slot
                      and invs' and  (\<lambda>s. ksCurThread s = thread)
                      and ex_cte_cap_to' (capCNodePtr rv)
                      and (\<lambda>s. case gsCNodes s (capCNodePtr rv) of None \<Rightarrow> False
                            | Some n \<Rightarrow> args ! 4 + args ! 5 - 1 < 2 ^ n)
                      and sch_act_simple and ct_active'" in hoare_strengthen_postE_R)
                   prefer 2
                   apply (clarsimp simp: invs_valid_objs' invs_mdb'
                                         ct_in_state'_def pred_tcb_at')
                   apply (subgoal_tac "ksCurThread s \<noteq> ksIdleThread sa")
                    prefer 2
                    apply clarsimp
                    apply (frule st_tcb_at_idle_thread',fastforce)
                    apply (clarsimp simp: valid_idle'_def)
                   apply (clarsimp simp: st_tcb_at'_def obj_at'_def
                                         invs'_def valid_state'_def)
                   apply (subgoal_tac "tcbState obja \<noteq> Inactive \<and> \<not> idle' (tcbState obja)")
                    prefer 2
                    apply (rule conjI, clarsimp)
                    apply (clarsimp dest!:invs_valid_idle')
                   apply (subgoal_tac "tcb_st_refs_of' (tcbState obja) = {}")
                    prefer 2
                    apply fastforce (* slow fastforce *)
                   apply (clarsimp split: if_splits simp: not_less toEnum_object_type_to_H
                                          word_size hd_conv_nth length_ineq_not_Nil)
                   apply (subgoal_tac "tcbQueued obja \<longrightarrow> runnable' (tcbState obja)")
                    apply (simp add: trans [OF olen_add_eqv[symmetric] unat_plus_simple]
                                     fromAPIType_def)
                    apply (clarsimp simp: word_le_nat_alt unat_2tp_if
                                          valid_tcb_state'_def
                                   split: option.split_asm if_split_asm)
                    apply blast
                   apply (case_tac "tcbState obja",
                          (simp add: runnable'_def valid_tcb_state'_def)+)[1]
                  apply simp
                  apply (rule validE_validE_R, rule mapME_wp'[unfolded mapME_def])
                  apply (rule hoare_pre)
                   apply (rule validE_R_validE)
                   apply (wp injection_wp_E[OF refl])
                  apply clarsimp
                 apply (simp add: ccHoarePost_def)
                 apply (simp only: whileAnno_def[where I=UNIV and V=UNIV, symmetric])
                 apply (rule_tac V=UNIV
                                in HoarePartial.reannotateWhileNoGuard)
                 apply (vcg exspec=ensureEmptySlot_modifies)
                  prefer 2
                  apply clarsimp
                  apply (subst (asm) mem_Collect_eq, assumption)
                 apply clarsimp
                apply (rule_tac Q'="\<lambda>r s. cte_wp_at' (\<lambda>cte. cteCap cte = cp) slot s
                      \<and> invs' s \<and> ksCurThread s = thread
                      \<and> valid_cap' r s
                      \<and> (\<forall>rf\<in>cte_refs' r (irq_node' s). ex_cte_cap_to' rf s)
                      \<and> sch_act_simple s \<and> ct_active' s" in hoare_strengthen_postE_R)
                 apply clarsimp
                 apply (wp injection_wp_E[OF refl] getSlotCap_cap_to'
                           getSlotCap_capAligned
                           | wp (once) hoare_drop_imps)+
                apply (clarsimp simp: valid_capAligned isCap_simps)
                apply (drule_tac x=0 in bspec, simp+)
                apply (frule(1) base_length_minus_one_inequality[where
                    wbase="args ! 4" and wlength="args ! 5"], simp_all)[1]
                 apply (simp add: valid_cap_simps' capAligned_def word_bits_def)
                apply (clarsimp simp: upto_enum_def word_le_nat_alt[symmetric]
                               split: option.split_asm if_split_asm)
                apply (drule spec, drule mp, erule conjI, rule order_refl)
                apply clarsimp
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
                        numeral_eqs[symmetric] cap_get_tag_isCap cte_wp_at_ctes_of
                        unat_eq_0 ccHoarePost_def)
  apply (rule conjI)
   apply (clarsimp simp: linorder_not_less isCap_simps)
   apply (clarsimp simp: sysargs_rel_to_n)
   apply (rule conjI, clarsimp)
   apply (clarsimp simp: fromAPIType_def)
   apply (subgoal_tac "unat (args ! Suc 0) < word_bits")
    prefer 2
    apply (simp add: word_size fromIntegral_def fromInteger_nat toInteger_nat word_bits_def
                     maxUntypedSizeBits_def wordBits_def)
   apply (clarsimp simp: excaps_map_def neq_Nil_conv excaps_in_mem_def
                         slotcap_in_mem_def cte_wp_at_ctes_of
                         valid_capAligned[OF ctes_of_valid'] invs_valid_objs'
                  dest!: interpret_excaps_eq)
   apply (clarsimp dest!: ctes_of_ex_cte_cap_to')
   apply (simp only: word_bits_def unat_lt2p)
  apply (frule interpret_excaps_eq)
  apply (clarsimp simp: if_1_0_0 word_less_nat_alt neq_Nil_conv
                        mask_def[where n=4] excaps_map_def
                        ccap_rights_relation_def word_sle_def
                        rightsFromWord_wordFromRights
                        excaps_in_mem_def slotcap_in_mem_def
                        signed_shift_guard_simpler_64
                        extra_sle_sless_unfolds
                 elim!: inl_inrE
              simp del: rf_sr_upd_safe imp_disjL)
   apply (rule conjI)
    apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_isCap_unfolded_H_cap
                          capCNodeRadix_CL_less_64s rf_sr_ksCurThread not_le
                   elim!: inl_inrE)
   apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_isCap_unfolded_H_cap
                         capCNodeRadix_CL_less_64s rf_sr_ksCurThread not_le
                  elim!: inl_inrE)
  apply (clarsimp simp: enum_object_type enum_apiobject_type word_le_nat_alt seL4_ObjectTypeCount_def)
  done

lemma decodeUntypedInvocation_ccorres:
notes TripleSuc[simp]
notes valid_untyped_inv_wcap'.simps[simp del]
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
             \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. ccap_relation cp (cap_' s)}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. call_' s = from_bool isCall}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       []
       (decodeUntypedInvocation label args slot cp (map fst extraCaps)
           >>= invocationCatch thread isBlocking isCall InvokeUntyped)
  (Call decodeUntypedInvocation_'proc)"
  apply (rule ccorres_name_pre)
  apply (clarsimp simp: isCap_simps)
  apply (rule ccorres_guard_imp2)
   apply (rule monadic_rewrite_ccorres_assemble)
    apply (rule_tac isBlocking=isBlocking and isCall=isCall and buffer=buffer
                in decodeUntypedInvocation_ccorres_helper)
    apply assumption
   apply (rule monadic_rewrite_trans[rotated])
    apply (rule monadic_rewrite_bind_head)
    apply (simp add: liftE_bindE stateAssert_def2 bind_assoc)
    apply (monadic_rewrite_r monadic_rewrite_if_r_True)
    apply (monadic_rewrite_r_method monadic_rewrite_symb_exec_r_drop wpsimp)
      apply (rule monadic_rewrite_refl)
     apply wpsimp
    apply (rule monadic_rewrite_refl)
   apply (rule monadic_rewrite_refl)
  apply (clarsimp simp: ex_cte_cap_wp_to'_def excaps_in_mem_def)
  apply (drule(1) bspec)+
  apply (rule_tac x = b in exI)
  apply (clarsimp simp: slotcap_in_mem_def cte_wp_at_ctes_of)
  done

end
end
