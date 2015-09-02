(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Schedule_C
imports Tcb_C
begin

(* FIXME: Move to an appropriate place in lib/ somewhere*)
lemma ucast_sub_ucast:
  fixes x :: "'a::len word"
  assumes "y \<le> x"
  assumes T: "len_of TYPE('a) \<le> len_of TYPE('b)"
  shows "ucast (x - y) = (ucast x - ucast y :: 'b::len word)"
proof -
  from T
  have P: "unat x < 2 ^ len_of TYPE('b)" "unat y < 2 ^ len_of TYPE('b)"
    by (fastforce intro!: less_le_trans[OF unat_lt2p])+
  thus ?thesis
    by (simp add: unat_arith_simps unat_ucast split assms[simplified unat_arith_simps])
qed

(* FIXME move *)
lemma setVMRoot_valid_queues':
  "\<lbrace> valid_queues' \<rbrace> setVMRoot a \<lbrace> \<lambda>_. valid_queues' \<rbrace>"
  apply (rule valid_queues_lift')
    apply wp
  done

(* FIXME move to REFINE *)
crunch valid_queues'[wp]: "ArchThreadDecls_H.switchToThread" valid_queues'
    (ignore: MachineOps.clearExMonitor)
crunch ksCurDomain[wp]: switchToIdleThread "\<lambda>s. P (ksCurDomain s)"
crunch valid_pspace'[wp]: switchToIdleThread, switchToThread valid_pspace'
(simp: whenE_def)
crunch valid_arch_state'[wp]: switchToThread valid_arch_state'

context kernel_m begin

(* FIXME: MOVE to CSpaceAcc_C *)
lemma ccorres_pre_gets_armKSGlobalsFrame_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. ArchStateData_H.armKSGlobalsFrame (ksArchState s) = rv  \<longrightarrow> P rv s))
                  {s. \<forall>rv. symbol_table ''armKSGlobalsFrame'' = rv \<longrightarrow> s \<in> P' rv }
                          hs (gets (ArchStateData_H.armKSGlobalsFrame \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def
                        carch_globals_def Let_def)
  done

(* FIXME: MOVE to CSpaceAcc_C *)
lemma rf_sr_ksDomainTime:
  "(s, s') \<in> rf_sr \<Longrightarrow> ksDomainTime_' (globals s') = ksDomainTime s"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

(* FIXME: MOVE to CSpaceAcc_C *)
lemma ccorres_pre_getDomainTime:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf 
                  (\<lambda>s. (\<forall>rv. ksDomainTime s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. ksDomainTime_' (globals s) = rv
                                 \<longrightarrow> s \<in> P' rv }
                          hs (getDomainTime >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (simp add: getDomainTime_def)
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def getDomainTime_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_ksDomainTime)
  done

lemma user_word_at_armKSGlobalsFrame:
  "\<lbrakk> valid_pspace' s; valid_arch_state' s \<rbrakk>
   \<Longrightarrow> \<exists>w. user_word_at w (ArchStateData_H.armKSGlobalsFrame (ksArchState s)) s"
  apply (simp add: user_word_at_def)
  apply (simp add: pointerInUserData_def)
  apply (clarsimp simp: valid_pspace'_def)
  apply (clarsimp simp: valid_arch_state'_def)
  apply (subgoal_tac "is_aligned (ArchStateData_H.armKSGlobalsFrame (ksArchState s)) pageBits")
   apply simp
   apply (erule is_aligned_weaken)
   apply (simp add: pageBits_def)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
  apply (drule (1) pspace_alignedD')+
  apply (case_tac ko, simp_all)[1]
  apply (simp add: objBitsKO_def)
  done

lemma h_t_valid_armKSGlobalsFrame:
  "\<lbrakk>valid_arch_state' s; (s, s') \<in> rf_sr \<rbrakk>
       \<Longrightarrow> s' \<Turnstile>\<^sub>c (Ptr :: (32 word \<Rightarrow> user_data_C ptr)) (symbol_table ''armKSGlobalsFrame'')"
  apply (clarsimp simp:valid_arch_state'_def)
  apply (clarsimp simp:rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
  apply (clarsimp simp:cmap_relation_def)
  apply (subgoal_tac "symbol_table ''armKSGlobalsFrame'' \<in> 
    dom (heap_to_page_data (ksPSpace s) (underlying_memory (ksMachineState s)))")
  prefer 2
    apply (clarsimp simp:obj_at'_def typ_at'_def ko_wp_at'_def
      carch_state_relation_def carch_globals_def)
   apply (simp add:heap_to_page_data_def map_comp_def)
   apply (case_tac ko,simp_all add:projectKO_opt_user_data)[1]
  apply (erule domE)
  apply (drule_tac x = " (Ptr :: (32 word \<Rightarrow> user_data_C ptr))
    (symbol_table ''armKSGlobalsFrame'')" in  eqset_imp_iff)
  apply (clarsimp simp add:image_def dom_def)
  apply (erule h_t_valid_clift)
  done

lemma c_guard_abs_word32_armKSGlobalsFrame:
  "\<lbrakk>valid_arch_state' s; (s, s') \<in> rf_sr\<rbrakk>
  \<Longrightarrow> s' \<Turnstile>\<^sub>c (Ptr :: word32 \<Rightarrow> (word32[1024]) ptr) (symbol_table ''armKSGlobalsFrame'')"
  apply (frule(1) h_t_valid_armKSGlobalsFrame)
  apply (drule h_t_valid_field[where f="[''words_C'']"])
  apply simp
  apply simp
  apply (simp add: field_lvalue_def field_lookup_offset_eq)
  apply (subst(asm) field_lookup_offset_eq)
  apply fastforce
  apply simp
  done

lemma Arch_switchToIdleThread_ccorres:
  "ccorres dc xfdc (valid_pspace' and valid_arch_state') UNIV []
           ArchThreadDecls_H.switchToIdleThread (Call Arch_switchToIdleThread_'proc)"
  apply (cinit simp: ArchThread_H.switchToIdleThread_def)
   apply (rule ccorres_pre_gets_armKSGlobalsFrame_ksArchState)
   apply (rule ccorres_Guard)
   apply (simp add: storeWordUser_def)
   apply (rule ccorres_symb_exec_l'[OF _ stateAssert_inv stateAssert_sp empty_fail_stateAssert])
   apply (rule ccorres_Guard)
   apply (rule storeWord_ccorres[unfolded fun_app_def])
  apply clarsimp
  apply (frule user_word_at_armKSGlobalsFrame, simp)
  apply (clarsimp simp: valid_pspace'_def is_aligned_globals_2)
  apply (drule (1) user_word_at_cross_over, rule refl)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        carch_state_relation_def carch_globals_def c_guard_abs_word32_armKSGlobalsFrame)
  done

(* FIXME: move *)
lemma empty_fail_getIdleThread [simp,intro!]:
  "empty_fail getIdleThread"
  by (simp add: getIdleThread_def)

lemma switchToIdleThread_ccorres:
  "ccorres dc xfdc (valid_pspace' and valid_arch_state') UNIV []
           switchToIdleThread (Call switchToIdleThread_'proc)"
  apply (cinit)
   apply (rule ccorres_symb_exec_l)
      apply (ctac (no_vcg) add: Arch_switchToIdleThread_ccorres)
       apply (simp add: setCurThread_def)
       apply (rule_tac P="\<lambda>s. thread = ksIdleThread s" and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: simpler_modify_def)
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                             carch_state_relation_def cmachine_state_relation_def)
      apply (simp add: ArchThread_H.switchToIdleThread_def)
      apply wp
   apply simp
  apply simp
  done

lemma Arch_switchToThread_ccorres:
  "ccorres dc xfdc
           (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' t)
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           [] 
           (ArchThreadDecls_H.switchToThread t) (Call Arch_switchToThread_'proc)"
  apply (cinit lift: tcb_')
   apply (unfold ArchThread_H.switchToThread_def)[1]
   apply (ctac (no_vcg) add: setVMRoot_ccorres)
    apply (simp (no_asm) del: Collect_const)
    apply (rule_tac Q="\<lambda>globals s. globals = ArchStateData_H.armKSGlobalsFrame (ksArchState s) \<and> 
                       all_invs_but_ct_idle_or_in_cur_domain' s" in ccorres_symb_exec_l) 
       apply (rule_tac Q="\<lambda>ib s. (\<exists>tcb. ko_at' tcb t s \<and> ib = tcbIPCBuffer tcb) \<and> 
                                 rva = ArchStateData_H.armKSGlobalsFrame (ksArchState s) \<and> 
                                 all_invs_but_ct_idle_or_in_cur_domain' s" in ccorres_symb_exec_l)
          apply (unfold storeWordUser_def)[1]
          apply (simp (no_asm) only: K_bind_def bind_assoc) 
          apply (rule_tac A'=UNIV in ccorres_guard_imp2)
           apply (rule ccorres_stateAssert)
           apply (rule ccorres_Guard_Seq)+
           apply (fold dc_def)[1]
           apply (ctac(no_vcg) add: storeWord_ccorres)
             apply (ctac add: clearExMonitor_ccorres)
            apply wp
           apply simp
          apply clarsimp
          apply (rule conjI)
           apply (clarsimp simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_pspace'_def)
           apply (clarsimp simp: valid_arch_state'_def typ_at'_def ko_wp_at'_def)
           apply (drule (1) pspace_alignedD')+
           apply (case_tac ko, simp_all)[1]
           apply (simp add: objBitsKO_def pageBits_def)
           apply (erule is_aligned_weaken)
           apply simp
          apply (clarsimp split: split_if)
          apply (drule (1) obj_at_cslift_tcb)
          apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
          apply (frule user_word_at_armKSGlobalsFrame)
           apply (simp add: invs_arch_state')
          apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
          apply (drule (1) user_word_at_cross_over, rule refl)
          apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                carch_state_relation_def carch_globals_def c_guard_abs_word32_armKSGlobalsFrame)
         apply wp
        apply (wp threadGet_wp)
        apply fastforce
       apply (simp|wp setVMRoot_invs_no_cicd')+
   done


(* FIXME: move *)
lemma switchToThread_ccorres:
  "ccorres dc xfdc 
           (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' t) 
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           []
           (switchToThread t)
           (Call switchToThread_'proc)"
  apply (cinit lift: thread_')
   apply (ctac (no_vcg) add: Arch_switchToThread_ccorres)
    apply (ctac (no_vcg) add: tcbSchedDequeue_ccorres)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply clarsimp
     apply (rule conseqPre, vcg)
     apply (clarsimp simp: setCurThread_def simpler_modify_def)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def 
                           carch_state_relation_def cmachine_state_relation_def)
    apply wp
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def)
  done

lemma get_tsType_ccorres2:
  "ccorres (\<lambda>r r'. r' = thread_state_to_tsType r) ret__unsigned_long_' (tcb_at' thread)
           (UNIV \<inter> {s. f s = tcb_ptr_to_ctcb_ptr thread} \<inter> 
            {s. cslift s (Ptr &(f s\<rightarrow>[''tcbState_C''])) = Some (thread_state_' s)}) []
  (getThreadState thread) (Call thread_state_get_tsType_'proc)"
  unfolding getThreadState_def
  apply (rule ccorres_from_spec_modifies [where P=\<top>, simplified]) 
     apply (rule thread_state_get_tsType_spec)
    apply (rule thread_state_get_tsType_modifies)
   apply simp    
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps)
  apply (rule bexI [rotated, OF threadGet_eq], assumption)
  apply simp
  apply (drule ctcb_relation_thread_state_to_tsType)
  apply simp
  done

lemma activateThread_ccorres:
  "ccorres dc xfdc 
           (ct_in_state' activatable' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
                   and valid_queues and valid_objs')
           UNIV []
           activateThread
           (Call activateThread_'proc)"
  apply (cinit)
   apply (rule ccorres_pre_getCurThread)
   apply (ctac add: get_tsType_ccorres2 [where f="\<lambda>s. ksCurThread_' (globals s)"])
     apply (rule_tac P="activatable' rv" in ccorres_gen_asm)
     apply (wpc)
            apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
          apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
         apply simp
         apply (rule ccorres_cond_true) 
         apply (rule ccorres_return_Skip)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
       apply (simp add: "StrictC'_thread_state_defs" del: Collect_const)
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_true)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: activateIdleThread_def return_def)
      apply (rule_tac P=\<top> and P'=UNIV in ccorres_inst, simp)
     apply (simp add: "StrictC'_thread_state_defs" del: Collect_const)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_true)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply (ctac)
       apply (ctac add: setNextPC_ccorres)
         apply ctac
        apply (wp | simp add: valid_tcb_state'_def)+
       apply vcg
      apply wp
     apply vcg
    apply (wp gts_wp') 
   apply vcg
  apply (clarsimp simp: ct_in_state'_def)
  apply (rule conjI, clarsimp)
  apply (clarsimp simp: st_tcb_at'_def)
  apply (rule conjI, clarsimp simp: obj_at'_def)
  apply clarsimp
  apply (drule (1) obj_at_cslift_tcb)
  apply (subgoal_tac "ksCurThread_' (globals s') = tcb_ptr_to_ctcb_ptr (ksCurThread s)")
   prefer 2
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: typ_heap_simps ThreadState_Running_def mask_def)
  done

lemmas ccorres_sequenceE_while_down_prio
    = ccorres_sequenceE_while_down
      [where xf="p_'" and xf_update="p_'_update",
         simplified]

lemma ceqv_Guard_UNIV_Skip:
  "ceqv Gamma xf v s s' (a ;; Guard F UNIV Skip) a"
  apply (rule ceqvI)
  apply (safe elim!: exec_Normal_elim_cases)
   apply (case_tac s'a, auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  apply (cases s', auto intro: exec.intros)
  done

lemma ceqv_tail_Guard_onto_Skip:
  "ceqv Gamma xf v s s'
      (a ;; Guard F G b) ((a ;; Guard F G Skip) ;; b)"
  apply (rule ceqvI)
  apply (safe elim!: exec_Normal_elim_cases)
   apply (case_tac s'a, auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  apply (case_tac s'aa, auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  done

lemma ceqv_remove_tail_Guard_Skip:
  "\<lbrakk> \<And>s. s \<in> G \<rbrakk> \<Longrightarrow> ceqv Gamma xf v s s' (a ;; Guard F G Skip) a"
  apply (rule ceqvI)
  apply (safe elim!: exec_Normal_elim_cases)
   apply (case_tac s'a, auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  apply (case_tac s', auto intro: exec.intros elim!: exec_Normal_elim_cases)[1]
  done

lemmas ccorres_remove_tail_Guard_Skip
    = ccorres_abstract[where xf'="\<lambda>_. ()", OF ceqv_remove_tail_Guard_Skip]

lemma queue_in_range_pre:
  "\<lbrakk> (qdom :: word32) \<le> ucast maxDom; prio \<le> ucast maxPrio \<rbrakk>
    \<Longrightarrow> qdom * of_nat numPriorities + prio < of_nat (numDomains * numPriorities)"
  by (clarsimp simp: cready_queues_index_to_C_def word_less_nat_alt
                     word_le_nat_alt unat_ucast maxDom_def seL4_MaxPrio_def
                     numPriorities_def unat_word_ariths numDomains_def)

lemmas queue_in_range' = queue_in_range_pre[unfolded numDomains_def numPriorities_def, simplified]

lemma chooseThread_ccorres:
  "ccorres dc xfdc all_invs_but_ct_idle_or_in_cur_domain' UNIV [] chooseThread (Call chooseThread_'proc)"
  apply (cinit)
   apply (rule ccorres_pre_curDomain)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_abstract[where xf'=p_'], ceqv)
     apply (rename_tac maxP_not_for_use) (* just name it something that doesn't clash *)
     apply (simp add: findM_is_mapME mapME_x_sequenceE bindE_assoc seL4_MaxPrio_def
                      whileAnno_def)
     apply (rule ccorres_splitE_novcg)
        apply (simp add: exec_eq_simps cong: ccorres_exec_congs)
        apply (rule ccorres_abstract [where xf'="\<lambda>_. ()"])
          apply (rule While_ceqv)
            apply (rule impI, rule refl)
           apply (rule ceqv_trans, rule ceqv_Guard_UNIV_Skip)
           apply (rule ceqv_tail_Guard_onto_Skip)
           apply simp
          apply (simp add: xpres_def)
         apply (rule_tac F="\<lambda>_. all_invs_but_ct_idle_or_in_cur_domain' and (\<lambda>s. curdom = ksCurDomain s)"
                     and Q=UNIV
                      in ccorres_sequenceE_while_down_prio[where r'=dc and xf'=xfdc])
             apply (clarsimp simp: bind_assoc)
             apply (rule ccorres_guard_imp2)
              apply (rule_tac xf'=p_' in ccorres_abstract, ceqv)
              apply (rename_tac p, rule_tac P="p = maxPrio - of_nat (length ys)"
                                         in ccorres_gen_asm2)
              apply (rule ccorres_rhs_assoc)
              apply (rule_tac xf'=thread_'
                          and r'="\<lambda>rv rv'. rv' = (case rv of [] \<Rightarrow> NULL
                                                           | (x # xs) \<Rightarrow> tcb_ptr_to_ctcb_ptr x)"
                           in ccorres_split_nothrow_novcg)
                  apply (rule_tac P="\<lambda>s. ksCurDomain s \<le> maxDomain \<and> curdom = ksCurDomain s"
                              and P'=UNIV
                               in ccorres_from_vcg)
                  apply (rule allI, rule conseqPre, vcg)
                  apply (clarsimp simp: getQueue_def simpler_gets_def upto_enum_word
                                        rev_map nth_map nth_rev
                              simp del: upt.simps)
                  apply (rule conjI)
                   apply (simp add: rf_sr_ksCurDomain maxDom_to_H[symmetric])
                   apply (rule queue_in_range')
                    apply (simp add: ucast_le_migrate word_size maxDom_def)
                   apply (simp add: scast_down_minus is_down_def target_size_def
                                    word_size source_size_def seL4_MaxPrio_def)
                   apply (rule word_sub_le)
                   apply (simp add: maxPrio_to_H[symmetric] unat_ucast seL4_MaxPrio_def
                                    WordLemmaBucket.of_nat_mono_maybe_le[where X=255, simplified, symmetric])
                  apply (frule_tac p="maxPriority - of_nat (length ys)"
                                in rf_sr_sched_queue_relation)
                    apply (simp add: maxDom_to_H[symmetric])
                   apply (simp add: maxPrio_to_H[symmetric])
                   apply (rule word_sub_le)
                   apply (simp add: maxPrio_to_H[symmetric] unat_ucast seL4_MaxPrio_def
                                    WordLemmaBucket.of_nat_mono_maybe_le[where X=255, simplified, symmetric])
                  apply (subst (asm) cready_queues_index_to_C_def2)
                    apply simp
                   apply (rule word_sub_le)
                   apply (simp add: maxPrio_to_H[symmetric] unat_ucast seL4_MaxPrio_def
                                    WordLemmaBucket.of_nat_mono_maybe_le[where X=255, simplified, symmetric])
                  apply (subst (asm) cready_queues_index_to_C_def2)
                    apply simp
                   apply (rule word_sub_le)
                   apply (simp add: maxPrio_to_H[symmetric] unat_ucast seL4_MaxPrio_def
                                    WordLemmaBucket.of_nat_mono_maybe_le[where X=255, simplified, symmetric])
                  apply (simp add: rf_sr_ksCurDomain numPriorities_def maxPrio_to_H[symmetric])
                  apply (subgoal_tac "ucast ((ucast maxPrio :: 8 word) - of_nat (length ys))
                                    = (scast (maxPrio - of_nat (length ys)) :: word32)")
                   apply simp
                   apply (auto simp: maxPrio_to_H tcb_queue_relation'_def
                              split: list.split)[1]
                  apply (simp add: seL4_MaxPrio_def WordLemmaBucket.of_nat_mono_maybe_le[where X=255, simplified, symmetric]
                                   ucast_sub_ucast scast_down_minus is_down_def target_size_def
                                   word_size source_size_def ucast_of_nat_small)
                 apply ceqv
                apply clarsimp
                apply (rule ccorres_remove_tail_Guard_Skip)
                 apply (simp add: maxPriority_def numPriorities_def seL4_MaxPrio_def Collect_const_mem
                                  word_sint_msb_eq minus_one_norm)
                 apply (simp add: not_msb_from_less unat_arith_simps unat_of_nat
                                  uint_nat)
                apply (rule_tac P="all_invs_but_ct_idle_or_in_cur_domain' and
                            (\<lambda>s. ksReadyQueues s (curdom, maxPriority - of_nat (length ys)) = rv)"
                           and P'="{s. thread_' s = (case rv of [] \<Rightarrow> NULL
                                                   | (x # xs) \<Rightarrow> tcb_ptr_to_ctcb_ptr x)}"
                             in ccorres_inst)
                apply (induct_tac rv)
                 apply simp
                 apply (rule ccorres_guard_imp2, rule ccorres_cond_false)
                  apply (rule ccorres_returnOk_skip)
                 apply clarsimp
                apply clarsimp
                apply (rule ccorres_guard_imp2)
                 apply (rule ccorres_cond_true)
                 apply (rule ccorres_rhs_assoc)+
                 apply (subst ccorres_seq_skip)
                 apply (ctac(no_vcg) add: switchToThread_ccorres)
                  apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                  apply (rule allI, rule conseqPre, vcg)
                  apply (clarsimp simp: throwError_def return_def)
                 apply wp
                apply (thin_tac "ccorres_underlying ?sr ?G ?r ?xf ?ar ?axf ?P ?P' ?hs ?a ?c")
                apply (clarsimp simp: invs_valid_queues')
                apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_queues_def)
                apply (drule_tac x="curdom" in spec)
                apply (drule_tac x="maxPriority - of_nat (length ys)" in spec)
                apply (clarsimp simp: obj_at'_weakenE[OF _ TrueI] filter_id_conv
                                      tcb_at_not_NULL[OF obj_at'_weakenE])
               apply wp
              apply (clarsimp simp: guard_is_UNIV_def)
             apply (clarsimp simp: upto_enum_word rev_map nth_map nth_rev
                                   field_simps all_invs_but_ct_idle_or_in_cur_domain'_def
                         simp del: upt.simps)
             apply (clarsimp simp: minBound_word maxBound_word seL4_MaxPrio_def
                                   Collect_const_mem minus_one_norm)
             apply simp
            apply (clarsimp simp: seL4_MinPrio_def maxPriority_def numPriorities_def word_sle_def
                                  field_simps)
            apply (drule word_unat.Abs_inverse'[rotated], simp add: unats_def)
            apply simp
           apply (rule HoarePartial.SeqSwap)
            apply vcg
           apply (rule HoarePartial.SeqSwap)
            apply (vcg exspec=switchToThread_modifies)
           apply (rule conseqPre, vcg)
           apply clarsimp
          apply (simp add: when_def cong: if_cong)
          apply (wp static_imp_wp | wpc)+
            apply (rule_tac Q="\<lambda>_. invs' and (\<lambda>s. curdom = ksCurDomain s)" in hoare_post_imp)
             apply (simp add: invs'_to_invs_no_cicd'_def)
            apply (wp switchToThread_invs_no_cicd')
           apply (rule_tac Q="\<lambda>_. invs' and (\<lambda>s. curdom = ksCurDomain s)" in hoare_post_imp)
            apply (simp add: invs'_to_invs_no_cicd'_def)
           apply (wp switchToThread_invs_no_cicd')
          apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def
                                hd_ksReadyQueues_runnable_2 invs_no_cicd_queues_tcb_in_cur_domain')
         apply simp
        apply ceqv
       apply (simp add: when_def liftE_liftM dc_def[symmetric])
       apply (ctac add: switchToIdleThread_ccorres)
      apply (fold mapME_def)
      apply (wp mapME_wp')
      apply (rule hoare_pre)
       apply (wp | wpc | clarsimp)+
     apply (clarsimp simp: guard_is_UNIV_def)
    apply (simp add: guard_is_UNIV_def seL4_MaxPrio_def)
    apply vcg
   apply clarsimp
   apply vcg_step
   apply simp
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def newKernelState_def)
  done

lemma ksDomSched_length_relation[simp]:
  "\<lbrakk>cstate_relation s s'\<rbrakk> \<Longrightarrow> length (kernel_state.ksDomSchedule s) = unat (ksDomScheduleLength)"
  apply (auto simp: cstate_relation_def cdom_schedule_relation_def Let_def ksDomScheduleLength_def)
  done

lemma ksDomSched_length_dom_relation[simp]:
  "\<lbrakk>cdom_schedule_relation (kernel_state.ksDomSchedule s) kernel_all_global_addresses.ksDomSchedule \<rbrakk> \<Longrightarrow> length (kernel_state.ksDomSchedule s) = unat (ksDomScheduleLength)"
  apply (auto simp: cstate_relation_def cdom_schedule_relation_def Let_def ksDomScheduleLength_def)
  done

lemma nextDomain_ccorres:
  "ccorres dc xfdc invs' UNIV [] nextDomain (Call nextDomain_'proc)"
  apply (cinit)
   apply (simp add: ksDomScheduleLength_def sdiv_word_def sdiv_int_def)
   apply (rule_tac P=invs' and P'=UNIV in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: simpler_modify_def Let_def
                         rf_sr_def cstate_relation_def
                         carch_state_relation_def cmachine_state_relation_def)
   apply (rule conjI)
    apply clarsimp
    apply (subgoal_tac "ksDomScheduleIdx \<sigma> = unat (ksDomScheduleLength - 1)")
     apply (fastforce simp add: cdom_schedule_relation_def dom_schedule_entry_relation_def dschDomain_def dschLength_def ksDomScheduleLength_def sdiv_word_def sdiv_int_def simp del: ksDomSched_length_dom_relation)
    apply (simp add: ksDomScheduleLength_def)
    apply (frule invs'_ksDomScheduleIdx)
    apply (simp add: invs'_ksDomSchedule newKernelState_def)
    apply (simp only: Abs_fnat_hom_1 Abs_fnat_hom_add)
    apply (drule unat_le_helper)
    apply (simp add: sdiv_int_def sdiv_word_def)
    apply (clarsimp simp: cdom_schedule_relation_def)
   apply (simp only: Abs_fnat_hom_1 Abs_fnat_hom_add word_not_le)
   apply clarsimp
   apply (subst (asm) of_nat_Suc[symmetric])
   apply (drule iffD1[OF of_nat_mono_maybe'[where X=3, simplified, symmetric], rotated 2])
     apply simp
    apply (frule invs'_ksDomScheduleIdx)
    apply (simp add: invs'_ksDomSchedule newKernelState_def)
    apply (clarsimp simp: cdom_schedule_relation_def)
   apply (clarsimp simp: ksDomScheduleLength_def)
   apply (subst of_nat_Suc[symmetric])+
   apply (subst unat_of_nat32)
    apply (simp add: word_bits_def)
   apply (subst unat_of_nat32)
    apply (simp add: word_bits_def)
   apply (fastforce simp add: cdom_schedule_relation_def dom_schedule_entry_relation_def dschDomain_def dschLength_def simp del: ksDomSched_length_dom_relation)
  apply simp
  done

lemma schedule_ccorres:
  "ccorres dc xfdc invs' UNIV [] schedule (Call schedule_'proc)"
  apply (cinit)
   apply (rule ccorres_pre_getCurThread)
   apply (rule_tac r'="\<lambda>rv rv'. cscheduler_action_relation rv (tcb_Ptr rv')"
              and xf'="action_'"
              and Q="\<lambda>action. \<lambda>s. invs' s \<and> ksSchedulerAction s = action \<and>
                                  tcb_at' curThread s"
              and Q'="\<lambda>rv rv'. \<lbrace>\<acute>action = rv' \<and> \<acute>ksSchedulerAction = tcb_Ptr rv' \<and>
                                \<acute>ksCurThread = tcb_ptr_to_ctcb_ptr curThread\<rbrace>"
              in ccorres_split_nothrow)
       apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: getSchedulerAction_def simpler_gets_def
                             rf_sr_cscheduler_relation)
      apply ceqv
     apply (case_tac rv, simp_all del: Collect_const)[1]
       apply (rule ccorres_guard_imp2)
        apply (rule ccorres_cond_false)+
        apply (rule ccorres_return_Skip)
       apply (clarsimp simp: cscheduler_action_relation_def max_word_def)
      apply (rule ccorres_guard_imp2)
       apply (rule ccorres_cond_true)
       apply (rule ccorres_rhs_assoc)+
       apply (ctac add: isRunnable_ccorres)
         apply (simp add: when_def)
         apply (rule_tac P="\<lambda>s. invs' s \<and> tcb_at' curThread s \<and>
                       (to_bool ret__unsigned_long \<longrightarrow> st_tcb_at' runnable' curThread s) \<and>
                        ksSchedulerAction s = ChooseNewThread"
                    and P'="{s. ksCurThread_' (globals s) = tcb_ptr_to_ctcb_ptr curThread}"
                      in ccorres_inst)
         apply (case_tac rva, simp_all del: dc_simp)
          apply (rule ccorres_guard_imp2)
           apply (clarsimp simp: to_bool_def ccorres_seq_cond_univ)
           apply (ctac add: tcbSchedEnqueue_ccorres)
             apply (rule_tac P'="\<lambda>rv. {s. ksDomainTime_' (globals s) = rv}"
                          in ccorres_pre_getDomainTime)
             apply (case_tac "rvb = 0")
              apply clarsimp
              apply (rule ccorres_guard_imp2)
               apply (rule ccorres_cond_true_seq)
               apply (ctac (no_vcg) add: nextDomain_ccorres)
                apply (ctac (no_vcg) add: chooseThread_ccorres)
                apply (rule ccorres_setSchedulerAction[unfolded dc_def])
              apply (simp add: cscheduler_action_relation_def)
             apply (wp nextDomain_invs_no_cicd')
             apply clarsimp
             apply assumption
(* FIXME else branch for rvb *)
              apply clarsimp
              apply (rule ccorres_guard_imp2)
               apply (rule ccorres_cond_false_seq)
               apply (simp only: ccorres_seq_skip)
                apply (ctac (no_vcg) add: chooseThread_ccorres)
                apply (rule ccorres_setSchedulerAction[unfolded dc_def])
              apply (simp add: cscheduler_action_relation_def)
             apply wp
             apply (auto simp: invs'_to_invs_no_cicd'_def)[1]
            apply (wp hoare_vcg_all_lift tcbSchedEnqueue_invs' | rule hoare_drop_imps)+
           apply clarsimp
           apply vcg
          apply auto[1]
(* FIXME else branch for rva *)
          apply (rule ccorres_guard_imp2)
           apply (clarsimp simp: to_bool_def ccorres_seq_cond_univ)
             apply (rule_tac P'="\<lambda>rv. {s. ksDomainTime_' (globals s) = rv}"
                          in ccorres_pre_getDomainTime)
             apply (case_tac "rv = 0")
              apply clarsimp
              apply (rule ccorres_guard_imp2)
               apply (rule ccorres_cond_true_seq)
               apply (ctac (no_vcg) add: nextDomain_ccorres)
                apply (ctac (no_vcg) add: chooseThread_ccorres)
                apply (rule ccorres_setSchedulerAction[unfolded dc_def])
              apply (simp add: cscheduler_action_relation_def)
             apply (wp nextDomain_invs_no_cicd')
             apply clarsimp
             apply assumption
(* FIXME else branch for rv *)
              apply clarsimp
              apply (rule ccorres_guard_imp2)
               apply (rule ccorres_cond_false_seq)
               apply (simp only: ccorres_seq_skip)
                apply (ctac (no_vcg) add: chooseThread_ccorres)
                apply (rule ccorres_setSchedulerAction[unfolded dc_def])
              apply (simp add: cscheduler_action_relation_def)
             apply wp
             apply (auto simp: invs'_to_invs_no_cicd'_def)[1]
           apply clarsimp
          apply wp
         apply vcg
          apply (auto simp: Collect_const_mem cscheduler_action_relation_def st_tcb_at'_def
                      elim: obj_at'_weakenE
                      dest: obj_at_cslift_tcb)[1]

     apply (rule ccorres_guard_imp2)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_cond_true)
      apply (rule ccorres_rhs_assoc)+
      apply (ctac add: isRunnable_ccorres)
        apply (rule_tac P="\<lambda>s. invs' s \<and> tcb_at' word s \<and> tcb_at' curThread s \<and>
                               ksSchedulerAction s \<noteq> ResumeCurrentThread \<and>
                               (rva \<longrightarrow> st_tcb_at' runnable' curThread s)"
                    and P'="{s. ksSchedulerAction_' (globals s) = tcb_ptr_to_ctcb_ptr word \<and>
                                ksCurThread_' (globals s) = tcb_ptr_to_ctcb_ptr curThread}"
                    in ccorres_inst)
        apply (case_tac rva, simp_all add: to_bool_def)
         apply (rule ccorres_guard_imp2)
          apply (ctac add: tcbSchedEnqueue_ccorres)
            apply (ctac (no_vcg) add: switchToThread_ccorres)
             apply (rule ccorres_setSchedulerAction)
             apply (simp add: cscheduler_action_relation_def)
            apply wp
            apply (rule_tac Q="\<lambda>_. invs' and tcb_at' word" in hoare_post_imp)
             apply (simp add: invs'_invs_no_cicd)
            apply wp
          apply (clarsimp simp: cscheduler_action_relation_def)
          apply (vcg exspec=tcbSchedEnqueue_modifies)
         apply fastforce
        apply (rule ccorres_guard_imp2)
         apply (ctac (no_vcg) add: switchToThread_ccorres)
          apply (rule ccorres_setSchedulerAction)
          apply (simp add: cscheduler_action_relation_def)
         apply wp
        apply (clarsimp simp: invs'_invs_no_cicd)
       apply wp
      apply vcg
     apply (clarsimp simp: Collect_const_mem cscheduler_action_relation_def)
     apply (drule_tac f=ptr_val in arg_cong, clarsimp)
     apply (case_tac "ksSchedulerAction s", simp_all)[1]
     apply (subgoal_tac "sch_act_wf (ksSchedulerAction s) s")
      prefer 2
      apply fastforce
     apply clarsimp
     apply (drule pred_tcb_at')
     apply (frule_tac t=word in tcb_at_not_NULL)
     apply (frule_tac p=word in is_aligned_tcb_ptr_to_ctcb_ptr)
     apply (drule obj_at_cslift_tcb[OF tcb_at_invs'], simp)
     apply (clarsimp simp: rf_sr_ksCurThread max_word_def is_aligned_def NULL_ptr_val bintr_Min)
    apply wp
   apply vcg
  apply (clarsimp simp: tcb_at_invs' st_tcb_at'_def o_def)
  done

(* FIXME: move *)
lemma map_to_tcbs_upd:
  "map_to_tcbs (ksPSpace s(t \<mapsto> KOTCB tcb')) = map_to_tcbs (ksPSpace s)(t \<mapsto> tcb')"
  apply (rule ext)
  apply (clarsimp simp: map_comp_def projectKOs split: option.splits if_splits)
  done

(* FIXME: move *)
lemma cep_relations_drop_fun_upd:
  "\<lbrakk> f x = Some v; tcbEPNext_C v' = tcbEPNext_C v; tcbEPPrev_C v' = tcbEPPrev_C v \<rbrakk>
      \<Longrightarrow> cendpoint_relation (f (x \<mapsto> v')) = cendpoint_relation f"
  "\<lbrakk> f x = Some v; tcbEPNext_C v' = tcbEPNext_C v; tcbEPPrev_C v' = tcbEPPrev_C v \<rbrakk>
      \<Longrightarrow> casync_endpoint_relation (f (x \<mapsto> v')) = casync_endpoint_relation f"
  by (intro ext cendpoint_relation_upd_tcb_no_queues[where thread=x]
                casync_endpoint_relation_upd_tcb_no_queues[where thread=x]
          | simp split: split_if)+

lemma threadSet_timeSlice_ccorres [corres]:
  "ccorres dc xfdc (tcb_at' thread) {s. thread' s = tcb_ptr_to_ctcb_ptr thread \<and> unat (v' s) = v} hs 
           (threadSet (tcbTimeSlice_update (\<lambda>_. v)) thread)
           (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update (heap_update (Ptr &(thread' s\<rightarrow>[''tcbTimeSlice_C''])::word32 ptr) (v' s)))) s))"
  apply (rule ccorres_guard_imp2)
   apply (rule threadSet_ccorres_lemma4 [where P=\<top> and P'=\<top>])   
    apply vcg
   prefer 2
   apply (rule conjI, simp)
   apply assumption
  apply clarsimp
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: cmachine_state_relation_def carch_state_relation_def cpspace_relation_def)
  apply (clarsimp simp: update_tcb_map_tos typ_heap_simps')
  apply (simp add: map_to_ctes_upd_tcb_no_ctes tcb_cte_cases_def)
  apply (simp add: cep_relations_drop_fun_upd)
  apply (rule conjI)
   defer
   apply (erule cready_queues_relation_not_queue_ptrs)
    apply (rule ext, simp split: split_if)
   apply (rule ext, simp split: split_if)
  apply (drule ko_at_projectKO_opt)
  apply (subst map_to_tcbs_upd)
  apply (erule (2) cmap_relation_upd_relI)
    apply (simp add: ctcb_relation_def)
   apply assumption
  apply simp
  done

lemma timerTick_ccorres:
  "ccorres dc xfdc invs' UNIV [] timerTick (Call timerTick_'proc)"
  apply (cinit)
   apply (rule ccorres_pre_getCurThread)
   apply (ctac add: get_tsType_ccorres2 [where f="\<lambda>s. ksCurThread_' (globals s)"])
     apply (rule ccorres_split_nothrow_novcg)
         apply wpc
                apply (simp add: "StrictC'_thread_state_defs", rule ccorres_cond_false, rule ccorres_return_Skip[unfolded dc_def])+
             (* thread_state.Running *)
             apply simp
             apply (rule ccorres_cond_true)
             apply (rule ccorres_pre_threadGet)
             apply (rule_tac P="cur_tcb'" and P'=\<top> in ccorres_move_c_guards(8))
              apply (clarsimp simp: cur_tcb'_def)
              apply (drule (1) tcb_at_h_t_valid)
              apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
             apply (rule_tac Q="\<lambda>s. obj_at' (\<lambda>tcb. tcbTimeSlice tcb = rva) (ksCurThread s) s" 
                         and Q'=\<top> in ccorres_cond_both')
               apply clarsimp
               apply (drule (1) obj_at_cslift_tcb)
               apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
               apply (clarsimp simp: typ_heap_simps)
               apply (clarsimp simp: ctcb_relation_def word_less_nat_alt)
              apply (rule_tac P="cur_tcb'" and P'=\<top> in ccorres_move_c_guards(8))
               apply (clarsimp simp: cur_tcb'_def)
               apply (fastforce simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps dest: tcb_at_h_t_valid)
              apply (rule_tac P="cur_tcb'" and P'=\<top> in ccorres_move_c_guards(8))
               apply (clarsimp simp: cur_tcb'_def)
               apply (fastforce simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps dest: tcb_at_h_t_valid)
              apply (ctac add: threadSet_timeSlice_ccorres[unfolded dc_def])
             apply (rule ccorres_rhs_assoc)+
             apply (ctac)
               apply simp
               apply (ctac (no_vcg) add: tcbSchedAppend_ccorres)
                apply (ctac add: rescheduleRequired_ccorres[unfolded dc_def])
               apply (wp weak_sch_act_wf_lift_linear threadSet_valid_queues
                         threadSet_pred_tcb_at_state tcbSchedAppend_valid_objs' threadSet_valid_objs' threadSet_tcbDomain_triv
                    | clarsimp simp: st_tcb_at'_def o_def split: if_splits)+
             apply (vcg exspec=tcbSchedDequeue_modifies)
        apply (simp add: "StrictC'_thread_state_defs", rule ccorres_cond_false, rule ccorres_return_Skip[unfolded dc_def])+
        apply ceqv
       apply (simp add: when_def numDomains_def decDomainTime_def)
       apply (rule ccorres_cond_true)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac rrel=dc and xf=xfdc and P=\<top> and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: simpler_modify_def)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 carch_state_relation_def cmachine_state_relation_def)
          apply ceqv
         apply (rule ccorres_pre_getDomainTime)
         apply (rule_tac P'="{s. ksDomainTime_' (globals s) = rvb}" in ccorres_inst, simp)
         apply (case_tac "rvb = 0")
          apply clarsimp
          apply (rule ccorres_guard_imp2)
           apply (rule ccorres_cond_true)
           apply (ctac add: rescheduleRequired_ccorres[unfolded dc_def])
          apply clarsimp
          apply assumption
         apply clarsimp
         apply (rule ccorres_guard_imp2)
          apply (rule ccorres_cond_false)
          apply (rule ccorres_return_Skip[unfolded dc_def])
         apply clarsimp
        apply wp
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (wpc
           | wp threadSet_weak_sch_act_wf threadSet_valid_objs' rescheduleRequired_weak_sch_act_wf
                tcbSchedAppend_valid_objs' weak_sch_act_wf_lift_linear threadSet_pred_tcb_no_state threadSet_tcbDomain_triv
                hoare_vcg_conj_lift hoare_vcg_all_lift
                threadGet_wp
           | simp split del: if_splits
           | rule hoare_drop_imps)+
     apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem word_sle_def word_sless_def)
    apply (wp gts_wp')
   apply vcg
  apply (clarsimp simp: invs_weak_sch_act_wf)
  apply (fold cur_tcb'_def)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp)
   apply (rule conjI)
    apply (clarsimp simp: invs'_def valid_state'_def)
    apply (auto simp: obj_at'_def inQ_def weak_sch_act_wf_def st_tcb_at'_def
                      valid_pspace'_def ct_idle_or_in_cur_domain'_def valid_tcb'_def valid_idle'_def projectKOs)[1]
   apply (rule conjI, clarsimp simp: invs'_def valid_state'_def valid_tcb'_def)+
     apply (clarsimp simp: tcb_cte_cases_def)
    apply (auto simp: obj_at'_def inQ_def weak_sch_act_wf_def st_tcb_at'_def
                      valid_pspace'_def ct_idle_or_in_cur_domain'_def valid_tcb'_def valid_idle'_def projectKOs)[1]
   apply (auto simp: invs'_def valid_state'_def)[1]

  apply (frule invs_cur')
  apply (clarsimp simp: cur_tcb'_def)
  apply (drule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def typ_heap_simps' timeSlice_def)
  apply (subst unat_sub)
   apply simp
  apply (clarsimp simp: ctcb_relation_def)
  done

end

end
