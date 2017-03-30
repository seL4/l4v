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

context begin interpretation Arch . (*FIXME: arch_split*)

lemma nat_add_less_by_max:
  "\<lbrakk> (x::nat) \<le> xmax ; y < k - xmax \<rbrakk> \<Longrightarrow> x + y < k"
  by simp

lemma ucast_or_distrib:
fixes x :: "'a::len word"
fixes y :: "'a::len word"
shows
  "(ucast (x || y) :: ('b::len) word) = ucast x || ucast y"
  unfolding ucast_def Word.bitOR_word.abs_eq uint_or
  by blast

(* FIXME move *)
lemma of_nat_shiftl:
  "(of_nat x << n) = (of_nat (x * 2 ^ n) :: ('a::len) word)"
proof -
  have "(of_nat x::'a word) << n = of_nat (2 ^ n) * of_nat x"
    using shiftl_t2n by auto
  thus ?thesis by simp
qed

lemma unat_of_nat_shiftl_or_8_32: (* FIXME generalise *)
  "\<lbrakk> x * 2 ^ n < 256 ; y < 256 \<rbrakk>
   \<Longrightarrow> unat (((of_nat x << n) :: 8 word)  || of_nat y :: 8 word) = unat (((of_nat x << n):: machine_word) || of_nat y :: machine_word)"
  apply (subst unat_ucast_upcast[where 'b=8 and 'a=32,symmetric])
   apply (simp add: is_up)
  apply (subst ucast_or_distrib)
  apply (subst of_nat_shiftl)
  apply (subst ucast_of_nat_small, simp)
  apply (subst ucast_of_nat_small, simp)
  apply (simp add: of_nat_shiftl)
  done

(* FIXME move *)
lemma word_clz_max:
  "word_clz w \<le> size (w::'a::len word)"
  unfolding word_clz_def
  apply (simp add: word_size)
  apply (rule_tac y="length (to_bl w)" in order_trans)
   apply (rule List.length_takeWhile_le)
  apply simp
  done

(* FIXME move *)
lemma word_clz_nonzero_max:
  fixes w :: "'a::len word"
  assumes nz: "w \<noteq> 0"
  shows "word_clz w < size (w::'a::len word)"
proof -
  {
    assume a: "word_clz w = size (w::'a::len word)"
    hence "length (takeWhile Not (to_bl w)) = length (to_bl w)"
      by (simp add: word_clz_def word_size)
    hence allj: "\<forall>j\<in>set(to_bl w). \<not> j"
      using takeWhile_take_has_property[where n="length (to_bl w)" and xs="to_bl w" and P=Not]
      by simp
    have "to_bl w = replicate (length (to_bl w)) False"
      apply (rule list_of_false)
      using allj by auto
    hence "w = 0"
     apply simp
     apply (subst (asm) to_bl_0[symmetric])
     apply (drule Word.word_bl.Rep_eqD, assumption)
     done
    with nz have False by simp
  }
  thus ?thesis using word_clz_max
    by (fastforce intro: le_neq_trans)
qed

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
  by (rule valid_queues_lift'; wp)

(* FIXME move to REFINE *)
crunch valid_queues'[wp]: "Arch.switchToThread" valid_queues'
    (ignore: clearExMonitor)
crunch ksCurDomain[wp]: switchToIdleThread "\<lambda>s. P (ksCurDomain s)"
crunch valid_pspace'[wp]: switchToIdleThread, switchToThread valid_pspace'
(simp: whenE_def)
crunch valid_arch_state'[wp]: switchToThread valid_arch_state'

end

(*FIXME: arch_split: move up?*)
context Arch begin
context begin global_naming global
requalify_facts
  Thread_H.switchToIdleThread_def
  Thread_H.switchToThread_def
end
end

context kernel_m begin

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

lemma Arch_switchToIdleThread_ccorres:
  "ccorres dc xfdc (valid_pspace' and valid_arch_state') UNIV []
           Arch.switchToIdleThread (Call Arch_switchToIdleThread_'proc)"
  apply (cinit simp: ARM_H.switchToIdleThread_def)
  by (rule ccorres_return_Skip, clarsimp)

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
      apply (simp add: ARM_H.switchToIdleThread_def)
      apply wp+
   apply simp
  apply simp
  done

lemma Arch_switchToThread_ccorres:
  "ccorres dc xfdc
           (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' t)
           (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           [] 
           (Arch.switchToThread t) (Call Arch_switchToThread_'proc)"
  apply (cinit lift: tcb_')
   apply (unfold ARM_H.switchToThread_def)[1]
   apply (ctac (no_vcg) add: setVMRoot_ccorres)
    apply (simp (no_asm) del: Collect_const)
    apply (rule_tac A'=UNIV in ccorres_guard_imp2)
     apply (fold dc_def)[1]
     apply (ctac add: clearExMonitor_ccorres)
    apply clarsimp
   apply wp
  apply clarsimp
  apply (drule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
  done


(* FIXME: move *)
lemma switchToThread_ccorres:
  "ccorres dc xfdc 
           (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' t) 
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           hs
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
    apply wp+
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def)
  done

lemma get_tsType_ccorres2:
  "ccorres (\<lambda>r r'. r' = thread_state_to_tsType r) ret__unsigned_' (tcb_at' thread)
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

lemma clzl_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> x_' s \<noteq> 0} Call clzl_'proc
       \<lbrace>\<acute>ret__long = of_nat (word_clz (x_' s)) \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply clarsimp
  apply (rule_tac x="ret__long_'_update f x" for f in exI)
  apply (simp add: mex_def meq_def)
  done

lemma l1index_to_prio_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call l1index_to_prio_'proc
       \<lbrace>\<acute>ret__unsigned_long = l1index_' s << wordRadix \<rbrace>"
  by vcg (simp add: word_sle_def wordRadix_def')

lemma getCurDomain_ccorres_dom_':
  "ccorres (\<lambda>rv rv'. rv' = ucast rv) dom_'
       \<top> UNIV hs curDomain (\<acute>dom :== \<acute>ksCurDomain)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: curDomain_def simpler_gets_def
                        rf_sr_ksCurDomain)
  done

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
  "\<lbrace>\<lambda>s. P s \<and> d \<le> maxDomain \<and> i \<le> numPriorities div wordBits \<rbrace>
   getReadyQueuesL2Bitmap d i
   \<lbrace>\<lambda>rv s. ksReadyQueuesL2Bitmap s (d, i) = rv \<and> d \<le> maxDomain \<and> i \<le> numPriorities div wordBits \<and> P s\<rbrace>"
  unfolding bitmap_fun_defs
  by wp simp

lemma ccorres_pre_getReadyQueuesL2Bitmap:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. d \<le> maxDomain \<and> i \<le> numPriorities div wordBits
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

lemma switchToThread_ccorres':
  "ccorres (\<lambda>_ _. True) xfdc 
           (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' t) 
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t\<rbrace>)
           hs
           (switchToThread t)
           (Call switchToThread_'proc)"
  apply (rule ccorres_guard_imp2)
      apply (ctac (no_vcg) add: switchToThread_ccorres[simplified dc_def])
     apply auto
  done

lemma cguard_UNIV:
  "P s \<Longrightarrow> s \<in> (if P s then UNIV else {})"
  by fastforce

lemma lookupBitmapPriority_le_maxPriority:
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ; valid_queues s \<rbrakk>
   \<Longrightarrow> lookupBitmapPriority d s \<le> maxPriority"
   unfolding valid_queues_def valid_queues_no_bitmap_def
   by (fastforce dest!: bitmapQ_from_bitmap_lookup bitmapQ_ksReadyQueuesI intro: ccontr)

lemma unat_lookupBitmapPriority_32:
  "word_log2 (ksReadyQueuesL1Bitmap s d) < numPriorities div wordBits
   \<Longrightarrow> unat (lookupBitmapPriority d s) =
      unat (
       ((of_nat (word_log2 (ksReadyQueuesL1Bitmap s d)) << wordRadix) :: machine_word) ||
        of_nat (word_log2 (ksReadyQueuesL2Bitmap s (d, word_log2 (ksReadyQueuesL1Bitmap s d)))))"
  unfolding lookupBitmapPriority_def l1IndexToPrio_def numPriorities_def wordBits_def
  apply (simp add: word_size)
  apply (subst unat_of_nat_shiftl_or_8_32)
    apply (clarsimp simp: wordRadix_def)
   apply (rule order_less_le_trans[OF word_log2_max])
   apply (simp add: word_size)
  apply simp
  done

lemma rf_sr_ksReadyQueuesL1Bitmap_simp:
  "\<lbrakk> (\<sigma>, s') \<in> rf_sr ; d \<le> maxDomain \<rbrakk>
  \<Longrightarrow> ksReadyQueuesL1Bitmap_' (globals s').[unat d] = ksReadyQueuesL1Bitmap \<sigma> d"
  apply (drule rf_sr_cbitmap_L1_relation)
  apply (simp add: cbitmap_L1_relation_def)
  done

lemma rf_sr_ksReadyQueuesL1Bitmap_not_zero:
  "\<lbrakk> (\<sigma>, s') \<in> rf_sr ; d \<le> maxDomain ; ksReadyQueuesL1Bitmap_' (globals s').[unat d] \<noteq> 0 \<rbrakk>
  \<Longrightarrow> ksReadyQueuesL1Bitmap \<sigma> d \<noteq> 0"
  apply (drule rf_sr_cbitmap_L1_relation)
  apply (simp add: cbitmap_L1_relation_def)
  done

lemma ksReadyQueuesL1Bitmap_word_log2_max:
    "\<lbrakk>valid_queues s; ksReadyQueuesL1Bitmap s d \<noteq> 0\<rbrakk>
    \<Longrightarrow> word_log2 (ksReadyQueuesL1Bitmap s d) < numPriorities div wordBits"
    unfolding valid_queues_def
    by (fastforce dest: word_log2_nth_same bitmapQ_no_L1_orphansD)

lemma word_log2_max_word32[simp]:
  "word_log2 (w :: 32 word) < 32"
  using word_log2_max[where w=w]
  by (simp add: word_size)

lemma word_log2_max_word8[simp]:
  "word_log2 (w :: 8 word) < 8"
  using word_log2_max[where w=w]
  by (simp add: word_size)

lemma rf_sr_ksReadyQueuesL2Bitmap_simp:
  "\<lbrakk> (\<sigma>, s') \<in> rf_sr ; d \<le> maxDomain ; valid_queues \<sigma> ; ksReadyQueuesL1Bitmap \<sigma> d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> ksReadyQueuesL2Bitmap_' (globals s').[unat d].[word_log2 (ksReadyQueuesL1Bitmap \<sigma> d)] =
      ksReadyQueuesL2Bitmap \<sigma> (d, word_log2 (ksReadyQueuesL1Bitmap \<sigma> d))"
  apply (frule (1) ksReadyQueuesL1Bitmap_word_log2_max)
  apply (frule rf_sr_cbitmap_L2_relation)
  apply (drule (1) cbitmap_L2_relationD)
  apply (drule less_imp_le)
   apply assumption
  apply simp
  done

lemma ksReadyQueuesL2Bitmap_nonzeroI:
  "\<lbrakk> d \<le> maxDomain ; valid_queues s ; ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> ksReadyQueuesL2Bitmap s (d, word_log2 (ksReadyQueuesL1Bitmap s d)) \<noteq> 0"
   unfolding valid_queues_def
   apply clarsimp
   apply (frule bitmapQ_no_L1_orphansD)
    apply (erule word_log2_nth_same)
   apply clarsimp
   done

(* FIXME move *)
lemma unat_add_lem':
  "(unat x + unat y < 2 ^ len_of TYPE('a)) \<Longrightarrow>
    (unat (x + y :: 'a :: len word) = unat x + unat y)"
  by (subst unat_add_lem[symmetric], assumption)

lemma chooseThread_ccorres:
  "ccorres dc xfdc all_invs_but_ct_idle_or_in_cur_domain' UNIV [] chooseThread (Call chooseThread_'proc)"
proof -

  note prio_and_dom_limit_helpers [simp]
  note ksReadyQueuesL2Bitmap_nonzeroI [simp]
  note Collect_const_mem [simp]

  have signed_word_log2:
    "\<And>w. w \<noteq> 0 \<Longrightarrow> (0x1F::32 signed word) - of_nat (word_clz (w::machine_word)) = (of_nat (word_log2 w))"
    unfolding word_log2_def
    by (clarsimp dest!: word_clz_nonzero_max simp: word_size)

  have b[simp]:
    "\<And>w. unat (of_nat (word_log2 (w :: machine_word)) :: machine_word) = word_log2 w"
    by (fastforce simp add: unat_of_nat
                  intro: mod_less order_less_le_trans[OF word_log2_max_word32])

  have unat_ucast_d[simp]:
    "\<And>d. d \<le> maxDomain \<Longrightarrow> unat (ucast d * 0x100 :: machine_word) = unat d * 256"
    by (subst unat_mult_simple)
       (simp add: word_bits_def maxDomain_def numDomains_def word_le_nat_alt)+

  (* FIXME word automation anyone? *)
  have word_clz_sint_upper[simp]:
    "\<And>(w::machine_word). sint (of_nat (word_clz w) :: 32 signed word) \<le> 2147483679"
    apply (subst sint_eq_uint)
     apply (rule not_msb_from_less)
     apply simp
     apply (rule word_of_nat_less)
     apply simp
     apply (rule order_le_less_trans[OF word_clz_max])
     apply (simp add: word_size)
    apply (subst uint_nat)
    apply (simp add: unat_of_nat)
    apply (subst mod_less)
     apply (rule order_le_less_trans[OF word_clz_max])
     apply (simp add: word_size)
    apply (rule iffD2 [OF le_nat_iff[symmetric]])
    apply simp
    apply (rule order_trans[OF word_clz_max])
    apply (simp add: word_size)
    done

  have word_clz_sint_lower[simp]:
    "\<And>(w::machine_word). - sint (of_nat (word_clz w) :: 32 signed word) \<le> 2147483616"
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

  have invs_no_cicd'_max_CurDomain[intro]:
    "\<And>s. invs_no_cicd' s \<Longrightarrow> ksCurDomain s \<le> maxDomain"
    by (simp add: invs_no_cicd'_def)

  show ?thesis
  apply (cinit)
   apply (simp add: numDomains_def word_sless_alt word_sle_def)
   apply (ctac (no_vcg) add: getCurDomain_ccorres_dom_')
     apply clarsimp
     apply (rename_tac curdom)
     apply (rule_tac P="curdom \<le> maxDomain" in ccorres_cross_over_guard_no_st)
     apply (rule ccorres_Guard)
     apply (rule ccorres_pre_getReadyQueuesL1Bitmap)
     apply (rename_tac l1)
     apply (rule_tac R="\<lambda>s. l1 = ksReadyQueuesL1Bitmap s curdom \<and> curdom \<le> maxDomain"
              in ccorres_cond)
       apply (fastforce dest!: rf_sr_cbitmap_L1_relation simp: cbitmap_L1_relation_def)
      prefer 2
      apply (ctac(no_vcg) add: switchToIdleThread_ccorres)
     apply clarsimp
     apply (rule ccorres_rhs_assoc)+
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_pre_getReadyQueuesL2Bitmap)
     apply (rename_tac l2) 
     apply (rule ccorres_pre_getQueue)
     apply (rule_tac P="queue \<noteq> []" in ccorres_cross_over_guard_no_st)
     apply (rule ccorres_symb_exec_l)
        apply (rule ccorres_assert)
     apply csymbr
        apply (rule ccorres_abstract_cleanup)
        apply (rule ccorres_Guard_Seq)+
        apply csymbr
        apply (rule ccorres_Guard_Seq)+
        apply csymbr
        apply (rule ccorres_abstract_cleanup)
        apply (rule ccorres_Guard_Seq)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (rule ccorres_Guard_Seq)+
        apply (rule ccorres_symb_exec_r)
          apply (simp only: ccorres_seq_skip)
          apply (rule ccorres_call)
              apply (rule switchToThread_ccorres')
             apply simp
            apply simp
           apply simp
          apply vcg
         apply clarsimp
         apply vcg_step (* vcg creates a state that's not printable in a sane amount of time *)
         apply clarsimp
        apply wp+
      apply (simp add: isRunnable_def)
     apply wp
    apply (rename_tac s' d)
    apply (clarsimp simp: Let_def)
    apply (safe, simp_all add: invs_no_cicd'_max_CurDomain)
    (*10 subgoals *)
           apply (drule invs_no_cicd'_queues)
           apply (clarsimp simp: rf_sr_ksReadyQueuesL1Bitmap_simp signed_word_log2)
           apply (simp add: rf_sr_ksReadyQueuesL2Bitmap_simp signed_word_log2)
           apply (case_tac queue, simp)
           apply (clarsimp simp: tcb_queue_relation'_def cready_queues_index_to_C_def
                                  numPriorities_def l1IndexToPrio_def)
           apply (erule trans[rotated])
           apply (subst unat_of_nat_shiftl_or_8_32)
             apply (clarsimp simp: wordRadix_def)
             apply (fastforce dest: ksReadyQueuesL1Bitmap_word_log2_max
                              simp: numPriorities_def wordBits_def word_size)
            apply (drule_tac s=s in ksReadyQueuesL1Bitmap_word_log2_max, assumption)
            apply (rule order_less_le_trans[OF word_log2_max_word32] ; simp)

           apply (frule (1) ksReadyQueuesL1Bitmap_word_log2_max)
           apply (frule (1) lookupBitmapPriority_le_maxPriority)
           apply (simp add: word_less_nat_alt word_le_nat_alt)
           apply (simp add: unat_lookupBitmapPriority_32)
           apply (subst unat_add_lem')
            apply (simp add: word_less_nat_alt word_le_nat_alt)
            apply (rule_tac x="unat d * 256" and xmax="unat maxDomain * 256" in nat_add_less_by_max)
             apply (simp add: word_le_nat_alt)
            apply (clarsimp simp: maxDomain_def numDomains_def maxPriority_def numPriorities_def)
           apply (simp add: word_less_nat_alt word_le_nat_alt)

          apply (rename_tac \<sigma>)
          apply (drule invs_no_cicd'_queues)
          apply (clarsimp simp: rf_sr_ksReadyQueuesL1Bitmap_simp rf_sr_ksReadyQueuesL2Bitmap_simp signed_word_log2)
          apply (frule (1) ksReadyQueuesL1Bitmap_word_log2_max)
          apply (frule (1) lookupBitmapPriority_le_maxPriority)
          apply (simp add: word_less_nat_alt word_le_nat_alt unat_lookupBitmapPriority_32)
          apply (subst unat_add_lem')
           apply (simp add: word_less_nat_alt word_le_nat_alt)
           apply (rule_tac x="unat d * 256" and xmax="unat maxDomain * 256" in nat_add_less_by_max)
            apply (simp add: word_le_nat_alt)
           apply (clarsimp simp: maxDomain_def numDomains_def maxPriority_def numPriorities_def)
          apply (simp add: word_less_nat_alt word_le_nat_alt)

          apply (rule_tac x="unat d * 256" and xmax="unat maxDomain * 256" in nat_add_less_by_max)
           apply (simp add: word_le_nat_alt)
          apply (rule order_le_less_trans)
           apply (simp add: word_le_nat_alt)
          apply (clarsimp simp: maxDomain_def numDomains_def maxPriority_def numPriorities_def)

         apply (fastforce dest!: invs_no_cicd'_queues
                          simp: rf_sr_ksReadyQueuesL1Bitmap_simp rf_sr_ksReadyQueuesL2Bitmap_simp
                                signed_word_log2)

        apply (rename_tac \<sigma>)
        apply (drule invs_no_cicd'_queues)
        apply (clarsimp simp: rf_sr_ksReadyQueuesL1Bitmap_simp rf_sr_ksReadyQueuesL2Bitmap_simp signed_word_log2)
        apply (drule word_log2_nth_same)
        apply (drule bitmapQ_no_L1_orphansD[rotated])
         apply (simp add: valid_queues_def)
        apply (fastforce intro!: cguard_UNIV word_of_nat_less
                          simp: numPriorities_def wordBits_def word_size)
       apply (fastforce dest: word_log2_nth_same bitmapQ_no_L1_orphansD[rotated] invs_no_cicd'_queues
                        simp: valid_queues_def)
      apply (clarsimp dest!: invs_no_cicd'_queues simp add: valid_queues_def)
      apply (drule (2) bitmapQ_from_bitmap_lookup)
      apply (simp only: valid_bitmapQ_bitmapQ_simp lookupBitmapPriority_def)

     apply (frule invs_no_cicd'_queues)
     apply (clarsimp simp add: valid_queues_def)
     apply (drule (2) bitmapQ_from_bitmap_lookup)
     apply (simp only: valid_bitmapQ_bitmapQ_simp)
     apply (case_tac "ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)", simp)
     apply (rename_tac t ts)
     apply (frule_tac t=t in valid_queues_no_bitmap_objD)
      apply (blast intro: cons_set_intro)
     apply (simp add: lookupBitmapPriority_def)
     apply (clarsimp simp: obj_at'_def st_tcb_at'_def)

    apply (fold lookupBitmapPriority_def)
    apply (drule invs_no_cicd'_queues)
    apply (erule (1) lookupBitmapPriority_le_maxPriority)
   apply (simp add: invs_no_cicd'_def)+
  done
qed

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
   apply (drule iffD1[OF of_nat_mono_maybe'[where x=3, simplified, symmetric], rotated 2])
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
           apply (clarsimp simp: to_bool_def)
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
             apply (wp nextDomain_invs_no_cicd')+
             apply clarsimp
             apply assumption
(* else branch for rvb *)
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
(* else branch for rva *)
          apply (rule ccorres_guard_imp2)
           apply (clarsimp simp: to_bool_def)
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
             apply (wp nextDomain_invs_no_cicd')+
             apply clarsimp
             apply assumption
(* else branch for rv *)
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
     apply (rename_tac word)     
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
      \<Longrightarrow> cnotification_relation (f (x \<mapsto> v')) = cnotification_relation f"
  by (intro ext cendpoint_relation_upd_tcb_no_queues[where thread=x]
                cnotification_relation_upd_tcb_no_queues[where thread=x]
          | simp split: if_split)+

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
  apply (simp add: map_to_ctes_upd_tcb_no_ctes tcb_cte_cases_def
                   map_to_tcbs_upd)
  apply (simp add: cep_relations_drop_fun_upd cvariable_relation_upd_const
                   ko_at_projectKO_opt)
  apply (rule conjI)
   defer
   apply (erule cready_queues_relation_not_queue_ptrs)
    apply (rule ext, simp split: if_split)
   apply (rule ext, simp split: if_split)
  apply (drule ko_at_projectKO_opt)
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
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac rrel=dc and xf=xfdc and P=\<top> and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: simpler_modify_def)
           apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                 carch_state_relation_def cmachine_state_relation_def)
          apply ceqv
         apply (rule ccorres_pre_getDomainTime)
         apply (rename_tac rva rv'a rvb)
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
      apply (wp hoare_vcg_conj_lift hoare_vcg_all_lift hoare_drop_imps)
       apply (wpc | wp threadSet_weak_sch_act_wf threadSet_valid_objs' rescheduleRequired_weak_sch_act_wf
                       tcbSchedAppend_valid_objs' weak_sch_act_wf_lift_linear threadSet_st_tcb_at2 threadGet_wp
                  | simp split del: if_splits)+
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
    apply (auto simp: obj_at'_def inQ_def weak_sch_act_wf_def st_tcb_at'_def
                      valid_pspace'_def ct_idle_or_in_cur_domain'_def valid_tcb'_def valid_idle'_def projectKOs)[1]
   apply (auto simp: invs'_def valid_state'_def valid_tcb'_def tcb_cte_cases_def)[1]

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
