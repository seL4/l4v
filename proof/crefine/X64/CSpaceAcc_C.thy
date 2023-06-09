(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* collects lemmas common to the various CSpace branches *)

theory CSpaceAcc_C
imports "Refine.EmptyFail" Ctac_lemmas_C
begin

(* For resolving schematics *)
lemma lift_t_cslift:
  "cslift x p = Some y \<Longrightarrow>
  lift_t c_guard (hrs_mem (t_hrs_' (globals x)), hrs_htd (t_hrs_' (globals x))) p = Some y"
  by (simp add: hrs_htd_def hrs_mem_def)

context kernel begin

lemma ccorres_pre_getNotification:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
           (\<lambda>s. \<forall>ntfn. ko_at' ntfn p s \<longrightarrow> P ntfn s)
           ({s'. \<forall>ntfn s. (s, s') \<in> rf_sr \<and> ko_at' ntfn p s \<longrightarrow> s' \<in> P' ntfn})
           hs (getNotification p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule get_ntfn_sp')
     apply simp
    apply assumption
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply simp
   apply assumption
  apply fastforce
  done

lemma ccorres_pre_getCTE:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>cte. ctes_of s p = Some cte \<longrightarrow> P cte s))
                  {s. \<forall>cte'. (cte_lift \<circ>\<^sub>m cslift s) (Ptr p) = Some cte' \<and> cl_valid_cte cte' \<longrightarrow> s \<in> P' (cte_to_H cte') }
                          hs (getCTE p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule getCTE_sp)
     apply simp
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply (simp add: cte_wp_at_ctes_of)
   apply assumption
  apply (simp add: cte_wp_at_ctes_of)
  apply (drule (1) rf_sr_ctes_of_clift)
  apply clarsimp
  apply (simp add: c_valid_cte_eq)
  done

lemmas ccorres_getCTE = ccorres_pre_getCTE



lemma getCurThread_sp:
  "\<lbrace>P\<rbrace> getCurThread \<lbrace>\<lambda>rv s. ksCurThread s = rv \<and> P s\<rbrace>"
  by wpsimp

lemma rf_sr_ksCurThread:
  "(s, s') \<in> rf_sr \<Longrightarrow> ksCurThread_' (globals s')
                       = tcb_ptr_to_ctcb_ptr (ksCurThread s)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma ccorres_pre_getCurThread:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. ksCurThread s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. ksCurThread_' (globals s) = tcb_ptr_to_ctcb_ptr rv
                                 \<longrightarrow> s \<in> P' rv }
                          hs (getCurThread >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule getCurThread_sp)
     apply (clarsimp simp: empty_fail_def getCurThread_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_ksCurThread)
  done

lemma getSchedulerAction_sp:
  "\<lbrace>P\<rbrace> getSchedulerAction \<lbrace>\<lambda>rv s. ksSchedulerAction s = rv \<and> P s\<rbrace>"
  by wpsimp

lemma ccorres_pre_getSchedulerAction:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. ksSchedulerAction s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. cscheduler_action_relation rv (ksSchedulerAction_' (globals s))
                                 \<longrightarrow> s \<in> P' rv }
                          hs (getSchedulerAction >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule getSchedulerAction_sp)
     apply simp
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp dest!: rf_sr_sched_action_relation)
  done

lemma rf_sr_ksDomainTime:
  "(s, s') \<in> rf_sr \<Longrightarrow> ksDomainTime_' (globals s') = ksDomainTime s"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

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

lemma rf_sr_ksIdleThread:
  "(s, s') \<in> rf_sr \<Longrightarrow> ksIdleThread_' (globals s')
                       = tcb_ptr_to_ctcb_ptr (ksIdleThread s)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma getIdleThread_sp:
  "\<lbrace>P\<rbrace> getIdleThread \<lbrace>\<lambda>rv s. ksIdleThread s = rv \<and> P s\<rbrace>"
  by wpsimp

lemma ccorres_pre_getIdleThread:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. ksIdleThread s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. ksIdleThread_' (globals s) = tcb_ptr_to_ctcb_ptr rv
                                 \<longrightarrow> s \<in> P' rv }
                          hs (getIdleThread >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule getIdleThread_sp)
     apply (clarsimp simp: empty_fail_def getIdleThread_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_ksIdleThread)
  done

lemma curDomain_sp:
  "\<lbrace>P\<rbrace> curDomain \<lbrace>\<lambda>rv s. ksCurDomain s = rv \<and> P s\<rbrace>"
  apply wp
  apply simp
  done

lemma rf_sr_ksCurDomain:
  "(s, s') \<in> rf_sr \<Longrightarrow> ksCurDomain_' (globals s')
                       = ucast (ksCurDomain s)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma ccorres_pre_curDomain:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. ksCurDomain s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv. ksCurDomain_' (globals s) = ucast rv
                                 \<longrightarrow> s \<in> P' rv }
                          hs (curDomain >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule curDomain_sp)
     apply (clarsimp simp: empty_fail_def curDomain_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_ksCurDomain)
  done

lemma scast_EXCPT_NONE [simp]: "scast EXCEPTION_NONE = EXCEPTION_NONE"
  unfolding scast_def EXCEPTION_NONE_def
  by simp

(* FIXME x64: can we just say pagesize < 3? needs checking with
              enums that 2^n options *)
lemma pageBitsForSize_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>pagesize < 3\<rbrace> Call pageBitsForSize_'proc
   \<lbrace> \<acute>ret__unsigned_long = of_nat (pageBitsForSize (framesize_to_H \<^bsup>s\<^esup>pagesize)) \<rbrace>"
  apply vcg
  apply clarsimp
  apply (clarsimp simp: pageBitsForSize_def framesize_to_H_def
                        X86_SmallPage_def X86_LargePage_def
                        X64_HugePage_def bit_simps)
  apply (drule word_less_cases [where y=3])
  apply (erule disjE, simp, simp)
  apply (drule word_less_cases [where y=2])
  apply (erule disjE, simp, simp)
  done

lemma updateMDB_pre_cte_at:
  "\<lbrace>\<lambda>s. \<not> (p \<noteq> 0 \<longrightarrow> cte_at' p s) \<rbrace> updateMDB p f \<lbrace> \<lambda>_ _. False \<rbrace>"
  unfolding updateMDB_def Let_def
  apply simp
  apply (intro impI)
  apply (wp getCTE_wp)
  apply clarsimp
  done

lemma getSlotCap_pre_cte_at:
  "\<lbrace>\<lambda>s. \<not> cte_at' p s \<rbrace> getSlotCap p \<lbrace> \<lambda>_ _. False \<rbrace>"
  unfolding getSlotCap_def by (wpsimp wp: getCTE_wp)

lemma updateCap_pre_cte_at:
  "\<lbrace>\<lambda>s. \<not> cte_at' p s \<rbrace> updateCap p f \<lbrace> \<lambda>_ _. False \<rbrace>"
  unfolding updateCap_def by (wpsimp wp: getCTE_wp)

lemmas ccorres_updateMDB_cte_at = ccorres_guard_from_wp [OF updateMDB_pre_cte_at empty_fail_updateMDB]
  ccorres_guard_from_wp_bind [OF updateMDB_pre_cte_at empty_fail_updateMDB]

lemmas ccorres_getSlotCap_cte_at = ccorres_guard_from_wp [OF getSlotCap_pre_cte_at empty_fail_getSlotCap]
  ccorres_guard_from_wp_bind [OF getSlotCap_pre_cte_at empty_fail_getSlotCap]

lemmas ccorres_updateCap_cte_at = ccorres_guard_from_wp [OF updateCap_pre_cte_at empty_fail_updateCap]
  ccorres_guard_from_wp_bind [OF updateCap_pre_cte_at empty_fail_updateCap]

lemma array_assertion_abs_cnode_ctes:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (\<exists>n. gsCNodes s p = Some n \<and> n' \<le> 2 ^ n) \<and> True
    \<longrightarrow> (x s' = 0 \<or> array_assertion (cte_Ptr p) n' (hrs_htd (t_hrs_' (globals s'))))"
  apply (clarsimp, drule(1) rf_sr_gsCNodes_array_assertion)
  apply (metis array_assertion_shrink_right)
  done

lemmas ccorres_move_array_assertion_cnode_ctes [ccorres_pre]
    = ccorres_move_Guard_Seq [OF array_assertion_abs_cnode_ctes]
      ccorres_move_Guard [OF array_assertion_abs_cnode_ctes]

lemma locateSlotCNode_ccorres [corres]:
  assumes gl: "\<And>v s. globals (xfu v s) = globals s" \<comment> \<open>for state rel. preservation\<close>
  and     fg: "\<And>v s. xf (xfu (\<lambda>_. v) s) = v"
  shows "ccorres (\<lambda>v v'. v' = Ptr v) xf \<top> {_. cnode = cnode' \<and> offset = offset'} hs
    (locateSlotCNode cnode bits offset)
    (Guard MemorySafety
          {s. x s = 0 \<or> array_assertion (cte_Ptr cnode') (unat offset') (hrs_htd (t_hrs_' (globals s)))}
          (Basic (\<lambda>s. xfu (\<lambda>_. cte_Ptr (cnode' + offset'
              * of_nat (size_of TYPE(cte_C)))) s)))"
  apply (simp add: locateSlot_conv split del: if_split)
  apply (rule ccorres_guard_imp2)
   apply (rule_tac P="cnode = cnode' \<and> offset = offset'" in ccorres_gen_asm2)
   apply (rule ccorres_stateAssert)
   apply (rule ccorres_move_array_assertion_cnode_ctes)
   apply (rule ccorres_return[where R="\<top>" and R'=UNIV])
   apply (rule conseqPre, vcg)
   apply (clarsimp simp: fg rf_sr_def gl cte_level_bits_def field_simps)
  apply (clarsimp simp: Collect_const_mem split: option.split_asm)
  apply (rule unat_le_helper, simp)
  done

lemma locateSlotTCB_ccorres [corres]:
  assumes gl: "\<And>v s. globals (xfu v s) = globals s" \<comment> \<open>for state rel. preservation\<close>
  and     fg: "\<And>v s. xf (xfu (\<lambda>_. v) s) = v"
  shows "ccorres (\<lambda>v v'. v' = Ptr v) xf \<top> {_. cnode = cnode' \<and> offset = offset'} hs
    (locateSlotTCB cnode offset)
    (Basic (\<lambda>s. xfu (\<lambda>_. Ptr (cnode' + offset' * of_nat (size_of TYPE(cte_C))) :: cte_C ptr) s))"
  unfolding locateSlot_conv using gl fg
  apply -
  apply (simp add: size_of_def split del: if_split)
  apply (rule ccorres_return)
  apply (rule conseqPre)
   apply vcg
  apply (clarsimp simp: fg objBits_simps cte_level_bits_def)
  done

lemma getSlotCap_h_val_ccorres [corres]:
  fixes p :: "cstate \<Rightarrow> cte_C ptr"
  assumes gl: "\<And>v s. globals (xfu v s) = globals s" \<comment> \<open>for state rel. preservation\<close>
  and     fg: "\<And>v s. xf (xfu (\<lambda>_. v) s) = v"
  shows "ccorres ccap_relation xf \<top> {s. p s = Ptr a} hs
         (getSlotCap a) (Basic (\<lambda>s. xfu (\<lambda>_. h_val (hrs_mem (t_hrs_' (globals s))) (Ptr &(p s\<rightarrow>[''cap_C'']) :: cap_C ptr)) s))"
  unfolding getSlotCap_def
  apply (rule ccorres_add_UNIV_Int)
  apply (cinitlift p) \<comment> \<open>EVIL!\<close>
  apply simp
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_pre_getCTE)
   apply (rule_tac R = "\<lambda>s. ctes_of s a = Some cte" in ccorres_return  [where R' = UNIV])
   apply vcg
   apply (clarsimp simp: gl fg cte_wp_at_ctes_of)
   apply (erule (1) rf_sr_ctes_of_cliftE)
   apply (clarsimp simp add: typ_heap_simps ccap_relation_def cte_to_H_def cl_valid_cte_def c_valid_cap_def)
  apply simp
  done

lemma ccorres_pre_gets_x86KSASIDTable_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. x64KSASIDTable (ksArchState s) = rv  \<longrightarrow> P rv s))
                  {s. \<forall>rv. s \<in> P' rv } hs
                  (gets (x64KSASIDTable \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply clarsimp
  done

lemma ccorres_pre_gets_x86KSASIDTable_ksArchState':
  assumes cc: "\<And>rv. ccorres r xf (P and (\<lambda>s. rv = (x64KSASIDTable \<circ> ksArchState) s)) (P' rv) hs (f rv) c"
  shows   "ccorres r xf P {s. \<forall>rv. s \<in> P' rv } hs
                   (gets (x64KSASIDTable \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply clarsimp
  done

end
end
