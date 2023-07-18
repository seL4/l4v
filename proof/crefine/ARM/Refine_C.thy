(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Toplevel Refinement Statement"

theory Refine_C
imports Init_C Fastpath_Equiv Fastpath_C CToCRefine
begin

context begin interpretation Arch . (*FIXME: arch_split*)
crunch ksQ[wp]: handleVMFault "\<lambda>s. P (ksReadyQueues s)"
  (ignore: getFAR getDFSR getIFSR)
end

context kernel_m
begin

text \<open>Assemble fastpaths\<close>

lemmas fastpath_call_ccorres_callKernel
    = monadic_rewrite_ccorres_assemble[OF fastpath_call_ccorres fastpath_callKernel_SysCall_corres]

lemmas fastpath_reply_recv_ccorres_callKernel
    = monadic_rewrite_ccorres_assemble[OF fastpath_reply_recv_ccorres fastpath_callKernel_SysReplyRecv_corres]

declare liftE_handle [simp]

lemma schedule_sch_act_wf:
  "\<lbrace>invs'\<rbrace> schedule \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (rule hoare_post_imp)
   apply (erule invs_sch_act_wf')
  apply (rule schedule_invs')
  done

lemma ucast_not_helper_cheating:
  fixes a:: "10 word"
  assumes a: "ucast a \<noteq> (0xFFFF :: word16)"
  shows "ucast a \<noteq> (0xFFFF::32 signed word)"
  by (word_bitwise,simp)

lemma ucast_helper_not_maxword:
  \<open>UCAST(10 \<rightarrow> 32) x \<noteq> 0xFFFF\<close>
  by transfer (simp add: take_bit_eq_mod)

lemmas ucast_helper_simps_32 =
  ucast_helper_not_maxword arg_cong[where f="UCAST(16 \<rightarrow> 32)", OF minus_one_norm]

lemma handleInterruptEntry_ccorres:
  "ccorres dc xfdc
           (invs' and sch_act_simple)
           UNIV []
           (callKernel Interrupt) (Call handleInterruptEntry_'proc)"
proof -
  show ?thesis
  apply (cinit')
   apply (simp add: callKernel_def handleEvent_def minus_one_norm)
   apply (simp add: liftE_bind bind_assoc)
    apply (ctac (no_vcg) add: getActiveIRQ_ccorres)
    apply (rule_tac P="rv \<noteq> Some 0xFFFF" in ccorres_gen_asm)
    apply wpc
     apply (simp add: irqInvalid_def ucast_helper_simps_32 mask_def)
     apply (rule ccorres_symb_exec_r)
       apply (ctac (no_vcg) add: schedule_ccorres)
        apply (rule ccorres_stateAssert_after)
        apply (rule ccorres_add_return2)
        apply (ctac (no_vcg) add: activateThread_ccorres)
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply (wp schedule_sch_act_wf schedule_invs'
             | strengthen invs_queues_imp invs_valid_objs_strengthen)+
      apply simp
      apply vcg
     apply vcg
    apply (clarsimp simp: irqInvalid_def ucast_ucast_b is_up ucast_helper_simps_32 mask_def)
    apply (ctac (no_vcg) add: handleInterrupt_ccorres)
     apply (ctac (no_vcg) add: schedule_ccorres)
      apply (rule ccorres_stateAssert_after)
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: activateThread_ccorres)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply (wp schedule_sch_act_wf schedule_invs'
             | strengthen invs_queues_imp invs_valid_objs_strengthen)+
   apply (rule_tac Q="\<lambda>rv s. invs' s \<and> (\<forall>x. rv = Some x \<longrightarrow> x \<le> ARM.maxIRQ) \<and> rv \<noteq> Some 0x3FF" in hoare_post_imp)
    apply (clarsimp simp: Kernel_C.maxIRQ_def ARM.maxIRQ_def)
   apply (wp getActiveIRQ_le_maxIRQ getActiveIRQ_neq_Some0xFF | simp)+
  apply (clarsimp simp: invs'_def valid_state'_def)
  done
qed

lemma handleUnknownSyscall_ccorres:
  "ccorres dc xfdc
           (invs' and ct_running' and
              (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
           (UNIV \<inter> {s. of_nat n = w_' s}) []
           (callKernel (UnknownSyscall n)) (Call handleUnknownSyscall_'proc)"
  apply (cinit' lift: w_')
   apply (simp add: callKernel_def handleEvent_def)
   apply (simp add: liftE_bind bind_assoc)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_pre_getCurThread)
     apply (ctac (no_vcg) add: handleFault_ccorres)
      apply (ctac (no_vcg) add: schedule_ccorres)
       apply (rule ccorres_stateAssert_after)
       apply (rule ccorres_add_return2)
       apply (ctac (no_vcg) add: activateThread_ccorres)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply (wp schedule_sch_act_wf schedule_invs'
              | strengthen invs_queues_imp invs_valid_objs_strengthen)+
    apply (clarsimp, vcg)
   apply (clarsimp, rule conseqPre, vcg, clarsimp)
  apply clarsimp
  apply (intro impI conjI allI)
      apply fastforce
     apply (clarsimp simp: ct_not_ksQ)
    apply (clarsimp simp add: sch_act_simple_def split: scheduler_action.split)
   apply (rule active_ex_cap')
    apply (erule active_from_running')
   apply (erule invs_iflive')
  apply (clarsimp simp: ct_in_state'_def)
  apply (frule st_tcb_idle'[rotated])
   apply (erule invs_valid_idle')
  apply (clarsimp simp: cfault_rel_def seL4_Fault_UnknownSyscall_lift is_cap_fault_def)
  done

lemma handleVMFaultEvent_ccorres:
  "ccorres dc xfdc
           (invs' and sch_act_simple and ct_running' and
               (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
           (UNIV \<inter> {s.  vm_faultType_' s = vm_fault_type_from_H vmfault_type}) []
           (callKernel (VMFaultEvent vmfault_type)) (Call handleVMFaultEvent_'proc)"
  apply (cinit' lift:vm_faultType_')
   apply (simp add: callKernel_def handleEvent_def)
   apply (simp add: liftE_bind bind_assoc)
   apply (rule ccorres_pre_getCurThread)
   apply (simp add: catch_def)
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_split_nothrow_novcg)
       apply (rule ccorres_split_nothrow_case_sum)
            apply (ctac (no_vcg) add: handleVMFault_ccorres)
           apply ceqv
          apply clarsimp
         apply clarsimp
         apply (rule ccorres_cond_univ)
         apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
         apply (rule_tac xf'=xfdc in ccorres_call)
            apply (ctac (no_vcg) add: handleFault_ccorres)
           apply simp
          apply simp
         apply simp
        apply (wp hv_inv_ex')
       apply (simp add: guard_is_UNIV_def)
       apply (vcg exspec=handleVMFault_modifies)
      apply ceqv
     apply clarsimp
     apply (ctac (no_vcg) add: schedule_ccorres)
      apply (rule ccorres_stateAssert_after)
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: activateThread_ccorres)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply (wp schedule_sch_act_wf schedule_invs'
             | strengthen invs_queues_imp invs_valid_objs_strengthen)+
     apply (case_tac x, clarsimp, wp)
     apply (clarsimp, wp, simp)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: simple_sane_strg[unfolded sch_act_sane_not])
  by (auto simp: ct_in_state'_def cfault_rel_def is_cap_fault_def ct_not_ksQ
              elim: pred_tcb'_weakenE st_tcb_ex_cap''
              dest: st_tcb_at_idle_thread' rf_sr_ksCurThread)


lemma handleUserLevelFault_ccorres:
  "ccorres dc xfdc
           (invs' and sch_act_simple and ct_running' and
               (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
           (UNIV \<inter> {s.  w_a_' s = word1} \<inter> {s. w_b_' s = word2 }) []
           (callKernel (UserLevelFault word1 word2)) (Call handleUserLevelFault_'proc)"
  apply (cinit' lift:w_a_' w_b_')
   apply (simp add: callKernel_def handleEvent_def)
   apply (simp add: liftE_bind bind_assoc)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_pre_getCurThread)
     apply (ctac (no_vcg) add: handleFault_ccorres)
      apply (ctac (no_vcg) add: schedule_ccorres)
       apply (rule ccorres_stateAssert_after)
       apply (rule ccorres_add_return2)
       apply (ctac (no_vcg) add: activateThread_ccorres)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply (wp schedule_sch_act_wf schedule_invs'
              | strengthen invs_queues_imp invs_valid_objs_strengthen)+
    apply (clarsimp, vcg)
   apply (clarsimp, rule conseqPre, vcg, clarsimp)
  apply clarsimp
  apply (intro impI conjI allI)
      apply (simp add: ct_in_state'_def)
      apply (erule pred_tcb'_weakenE)
      apply simp
     apply (clarsimp simp: ct_not_ksQ)
    apply (clarsimp simp add: sch_act_simple_def split: scheduler_action.split)
   apply (rule active_ex_cap')
    apply (erule active_from_running')
   apply (erule invs_iflive')
  apply (clarsimp simp: ct_in_state'_def)
  apply (frule st_tcb_idle'[rotated])
   apply (erule invs_valid_idle')
   apply simp
  apply (clarsimp simp: cfault_rel_def seL4_Fault_UserException_lift)
  apply (simp add: is_cap_fault_def)
  done

lemmas syscall_defs =
  Kernel_C.SysSend_def Kernel_C.SysNBSend_def
  Kernel_C.SysCall_def Kernel_C.SysRecv_def Kernel_C.SysNBRecv_def
  Kernel_C.SysReply_def Kernel_C.SysReplyRecv_def Kernel_C.SysYield_def

lemma ct_active_not_idle'_strengthen:
  "invs' s \<and> ct_active' s \<longrightarrow> ksCurThread s \<noteq> ksIdleThread s"
  by clarsimp


lemma handleSyscall_ccorres:
  "ccorres dc xfdc
           (invs' and
               (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
               sch_act_simple and ct_running' and
               (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
           (UNIV \<inter> {s. syscall_' s = syscall_from_H sysc }) []
           (callKernel (SyscallEvent sysc)) (Call handleSyscall_'proc)"
  apply (cinit' lift: syscall_')
   apply (simp add: callKernel_def handleEvent_def minus_one_norm)
   apply (simp add: handleE_def handleE'_def)
   apply (rule ccorres_split_nothrow_novcg)
       apply wpc
              prefer 3
              \<comment> \<open>SysSend\<close>
              apply (clarsimp simp: syscall_from_H_def syscall_defs)
              apply (rule ccorres_cond_empty |rule ccorres_cond_univ)+
              apply (simp add: handleSend_def)
              apply (rule ccorres_split_nothrow_case_sum)
                   apply (ctac (no_vcg) add: handleInvocation_ccorres)
                  apply ceqv
                 apply clarsimp
                 apply (rule ccorres_cond_empty)
                 apply (rule ccorres_returnOk_skip[unfolded returnOk_def,simplified])
                apply clarsimp
                apply (rule ccorres_cond_univ)
                apply (simp add: liftE_def bind_assoc)
                apply (ctac (no_vcg) add: getActiveIRQ_ccorres)
                 apply (rule ccorres_Guard)?
                 apply (simp only: irqInvalid_def)?
                 apply (rule_tac P="rv \<noteq> Some 0xFFFF" in ccorres_gen_asm)
                 apply (subst ccorres_seq_skip'[symmetric])
                 apply (rule ccorres_split_nothrow_novcg)
                     apply (rule_tac R=\<top> and xf=xfdc in ccorres_when)
                      apply (case_tac rv)
                      apply (clarsimp simp: ucast_def uint_minus_1_eq)
                     defer
                     apply (ctac (no_vcg) add: handleInterrupt_ccorres)
                    apply ceqv
                   apply (rule_tac r=dc and xf=xfdc in ccorres_returnOk_skip[unfolded returnOk_def,simplified])
                  apply wp
                 apply (simp add: guard_is_UNIV_def)
                apply clarsimp
                apply (rule_tac Q="\<lambda>rv s. invs' s \<and>
                 (\<forall>x. rv = Some x \<longrightarrow> x \<le> ARM.maxIRQ) \<and> rv \<noteq> Some 0x3FF"
                                             in hoare_post_imp)
                 apply (clarsimp simp: Kernel_C.maxIRQ_def ARM.maxIRQ_def)
                apply (wp getActiveIRQ_le_maxIRQ getActiveIRQ_neq_Some0xFF | simp)+
               apply (rule_tac Q=" invs' " in hoare_post_imp_dc2E, wp)
               apply (simp add: invs'_def valid_state'_def)
              apply clarsimp
              apply (vcg exspec=handleInvocation_modifies)
             prefer 3
             \<comment> \<open>SysNBSend\<close>
             apply (clarsimp simp: syscall_from_H_def syscall_defs)
             apply (rule ccorres_cond_empty |rule ccorres_cond_univ)+
             apply (simp add: handleSend_def)
             apply (rule ccorres_split_nothrow_case_sum)
                  apply (ctac (no_vcg) add: handleInvocation_ccorres)
                 apply ceqv
                apply clarsimp
                apply (rule ccorres_cond_empty)
                apply (rule ccorres_returnOk_skip[unfolded returnOk_def,simplified])
               apply clarsimp
               apply (rule ccorres_cond_univ)
               apply (simp add: liftE_def bind_assoc irqInvalid_def)
               apply (ctac (no_vcg) add: getActiveIRQ_ccorres)
                apply (rule_tac P="rv \<noteq> Some 0xFFFF" in ccorres_gen_asm)
                apply (subst ccorres_seq_skip'[symmetric])
                apply (rule ccorres_split_nothrow_novcg)
                    apply (rule_tac R=\<top> and xf=xfdc in ccorres_when)
                     apply (case_tac rv)
                      apply (clarsimp simp: ucast_helper_simps_32 mask_def)
                     apply (clarsimp simp only: ucast_helper_simps_32)
                     apply (intro iffI)
                      apply clarsimp
                      apply (cut_tac 'b=32 and x=a and n=10 and 'a=10 in
                               ucast_leq_mask; simp add: mask_def)
                     apply simp
                    apply (ctac (no_vcg) add: handleInterrupt_ccorres)
                   apply ceqv
                  apply (rule_tac ccorres_returnOk_skip[unfolded returnOk_def,simplified])
                 apply wp
                apply (simp add: guard_is_UNIV_def)
               apply clarsimp
               apply (rule_tac Q="\<lambda>rv s. invs' s \<and>
                (\<forall>x. rv = Some x \<longrightarrow> x \<le> ARM.maxIRQ) \<and> rv \<noteq> Some 0x3FF"
                                     in hoare_post_imp)
                apply (clarsimp simp: Kernel_C.maxIRQ_def ARM.maxIRQ_def)
               apply (wp getActiveIRQ_le_maxIRQ getActiveIRQ_neq_Some0xFF | simp)+
              apply (rule_tac Q=" invs' " in hoare_post_imp_dc2E, wp)
              apply (simp add: invs'_def valid_state'_def)
             apply clarsimp
             apply (vcg exspec=handleInvocation_modifies)
            \<comment> \<open>SysCall\<close>
            apply (clarsimp simp: syscall_from_H_def syscall_defs)
            apply (rule ccorres_cond_empty |rule ccorres_cond_univ)+
            apply (simp add: handleCall_def)
            apply (rule ccorres_split_nothrow_case_sum)
                 apply (ctac (no_vcg) add: handleInvocation_ccorres)
                apply ceqv
               apply clarsimp
               apply (rule ccorres_cond_empty)
               apply (rule ccorres_returnOk_skip[unfolded returnOk_def,simplified])
              apply clarsimp
              apply (rule ccorres_cond_univ)
              apply (simp add: liftE_def bind_assoc irqInvalid_def)
              apply (ctac (no_vcg) add: getActiveIRQ_ccorres)
               apply (rule_tac P="rv \<noteq> Some 0xFFFF" in ccorres_gen_asm)
               apply (subst ccorres_seq_skip'[symmetric])
               apply (rule ccorres_split_nothrow_novcg)
                   apply (rule ccorres_Guard)?
                   apply (rule_tac R=\<top> and xf=xfdc in ccorres_when)
                    apply (case_tac rv, clarsimp)
                    apply (clarsimp simp: ucast_ucast_b is_up ucast_helper_simps_32 mask_def)
                   apply (clarsimp simp: ucast_helper_simps_32)
                   apply (cut_tac 'b=32 and x=a and n=10 and 'a=10 in
                               ucast_leq_mask; simp add: mask_def)
                   apply (ctac (no_vcg) add: handleInterrupt_ccorres)
                  apply ceqv
                 apply (rule_tac ccorres_returnOk_skip[unfolded returnOk_def,simplified])
                apply wp
               apply (simp add: guard_is_UNIV_def)
              apply clarsimp
              apply (rule_tac Q="\<lambda>rv s. invs' s \<and>
               (\<forall>x. rv = Some x \<longrightarrow> x \<le> ARM.maxIRQ) \<and> rv \<noteq> Some 0x3FF"
                                        in hoare_post_imp)
               apply (clarsimp simp: Kernel_C.maxIRQ_def ARM.maxIRQ_def)
              apply (wp getActiveIRQ_le_maxIRQ getActiveIRQ_neq_Some0xFF | simp)+
             apply (rule_tac Q=" invs' " in hoare_post_imp_dc2E, wp)
             apply (simp add: invs'_def valid_state'_def)
            apply clarsimp
            apply (vcg exspec=handleInvocation_modifies)
           prefer 2
           \<comment> \<open>SysRecv\<close>
           apply (clarsimp simp: syscall_from_H_def syscall_defs)
           apply (rule ccorres_cond_empty |rule ccorres_cond_univ)+
           apply (simp add: liftE_bind)
           apply (subst ccorres_seq_skip'[symmetric])
           apply (ctac (no_vcg) add: handleRecv_ccorres)
            apply (rule ccorres_returnOk_skip[unfolded returnOk_def, simplified])
           apply wp
          prefer 2
          \<comment> \<open>SysReply\<close>
          apply (clarsimp simp: syscall_from_H_def syscall_defs)
          apply (rule ccorres_cond_empty |rule ccorres_cond_univ)+
          apply (simp add: liftE_bind)
          apply (subst ccorres_seq_skip'[symmetric])
          apply (ctac (no_vcg) add: handleReply_ccorres)
           apply (rule ccorres_returnOk_skip[unfolded returnOk_def, simplified])
          apply wp
         \<comment> \<open>SysReplyRecv\<close>
         apply (clarsimp simp: syscall_from_H_def syscall_defs)
         apply (rule ccorres_cond_empty |rule ccorres_cond_univ)+
         apply (simp add: liftE_bind bind_assoc)
         apply (ctac (no_vcg) add: handleReply_ccorres)
          apply (subst ccorres_seq_skip'[symmetric])
          apply (ctac (no_vcg) add: handleRecv_ccorres)
           apply (rule ccorres_returnOk_skip[unfolded returnOk_def, simplified])
          apply wp[1]
         apply clarsimp
         apply wp
         apply (rule_tac Q="\<lambda>rv s. ct_in_state' simple' s \<and> sch_act_sane s \<and>
                            (\<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))"
                              in hoare_post_imp)
          apply (simp add: ct_in_state'_def)
         apply (wp handleReply_sane handleReply_ct_not_ksQ)
        \<comment> \<open>SysYield\<close>
        apply (clarsimp simp: syscall_from_H_def syscall_defs)
        apply (rule ccorres_cond_empty |rule ccorres_cond_univ)+
        apply (simp add: liftE_bind)
        apply (subst ccorres_seq_skip'[symmetric])
        apply (ctac (no_vcg) add: handleYield_ccorres)
         apply (rule ccorres_returnOk_skip[unfolded returnOk_def, simplified])
        apply wp
       \<comment> \<open>SysNBRecv\<close>
       apply (clarsimp simp: syscall_from_H_def syscall_defs)
       apply (rule ccorres_cond_empty |rule ccorres_cond_univ)+
       apply (simp add: liftE_bind)
       apply (subst ccorres_seq_skip'[symmetric])
       apply (ctac (no_vcg) add: handleRecv_ccorres)
        apply (rule ccorres_returnOk_skip[unfolded returnOk_def, simplified])
       apply wp
      \<comment> \<open>rest of body\<close>
      apply ceqv
     apply (ctac (no_vcg) add: schedule_ccorres)
      apply (rule ccorres_stateAssert_after)
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: activateThread_ccorres)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply (wp schedule_invs' schedule_sch_act_wf | strengthen invs_queues_imp invs_valid_objs_strengthen)+
     apply (simp
          | wpc
          | wp hoare_drop_imp handleReply_sane handleReply_nonz_cap_to_ct schedule_invs'
               handleReply_ct_not_ksQ[simplified]
          | strengthen ct_active_not_idle'_strengthen invs_valid_objs_strengthen)+
      apply (rule_tac  Q="\<lambda>rv. invs' and ct_active'" in hoare_post_imp, simp)
      apply (wp hy_invs')
     apply (clarsimp simp add: liftE_def)
     apply wp
     apply (rule_tac  Q="\<lambda>rv. invs' and ct_active'" in hoare_post_imp, simp)
     apply (wp hy_invs')
    apply (clarsimp simp: liftE_def)
    apply (wp)
    apply (rule_tac Q="\<lambda>_. invs'" in hoare_post_imp, simp)
    apply (wp hw_invs')
   apply (simp add: guard_is_UNIV_def)
   apply clarsimp
   apply (drule active_from_running')
   apply (frule active_ex_cap')
    apply (clarsimp simp: invs'_def valid_state'_def)
   apply (clarsimp simp: simple_sane_strg ct_in_state'_def st_tcb_at'_def obj_at'_def
                        isReply_def ct_not_ksQ)
   apply (rule conjI, fastforce)
   prefer 2
   apply (cut_tac 'b=32 and x=a and n=10 and 'a=10 in ucast_leq_mask)
   by (auto simp: ucast_helper_simps_32 mask_def syscall_from_H_def Kernel_C.SysSend_def
            split: option.split_asm)

lemma ccorres_corres_u:
  "\<lbrakk> ccorres dc xfdc P (Collect P') [] H C; no_fail P H \<rbrakk> \<Longrightarrow>
  corres_underlying rf_sr nf nf' dc P P' H (exec_C \<Gamma> C)"
  apply (clarsimp simp: ccorres_underlying_def corres_underlying_def)
  apply (drule (1) bspec)
  apply (clarsimp simp: exec_C_def no_fail_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x=0 in allE)
   apply (erule_tac x="Normal y" in allE)
   apply simp
   apply (erule impE)
    apply (drule EHOther [where hs="[]"], simp)
    apply simp
   apply fastforce
  apply clarsimp
  apply (case_tac xs, simp_all)
    apply (fastforce intro: EHAbrupt EHEmpty)
   apply (fastforce intro: EHOther)+
  done

lemma ccorres_corres_u_xf:
  "\<lbrakk> ccorres rel xf P (Collect P') [] H C; no_fail P H \<rbrakk> \<Longrightarrow>
  corres_underlying rf_sr nf nf' rel P P' H ((exec_C \<Gamma> C) >>= (\<lambda>_. gets xf))"
  apply (clarsimp simp: ccorres_underlying_def corres_underlying_def)
  apply (drule (1) bspec)
  apply (clarsimp simp: exec_C_def no_fail_def)
  apply (drule_tac x = a in spec)
  apply (clarsimp simp:gets_def Nondet_Monad.bind_def get_def return_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x=0 in allE)
   apply (erule_tac x="Normal y" in allE)
   apply simp
   apply (erule impE)
    apply (drule EHOther [where hs="[]"], simp)
    apply simp
   apply (simp add: unif_rrel_def)
  apply (clarsimp simp:image_def)
  apply (case_tac xs, simp_all)
    apply (fastforce intro: EHAbrupt EHEmpty)
   apply (fastforce intro: EHOther)+
  done

definition
  "all_invs' e \<equiv> \<lambda>s'. \<exists>s :: det_state.
    (s,s') \<in> state_relation \<and>
    (einvs s \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s) \<and> (ct_running s \<or> ct_idle s) \<and>
      scheduler_action s = resume_cur_thread \<and> 0 < domain_time s \<and> valid_domain_list s) \<and>
    (invs' s' \<and> vs_valid_duplicates' (ksPSpace s') \<and>
      (e \<noteq> Interrupt \<longrightarrow> ct_running' s') \<and> (ct_running' s' \<or> ct_idle' s') \<and> ksDomainTime s' \<noteq> 0 \<and>
      ksSchedulerAction s' = ResumeCurrentThread)"

lemma no_fail_callKernel:
  "no_fail (all_invs' e) (callKernel e)"
  unfolding all_invs'_def
  apply (rule corres_nofail)
   apply (rule corres_guard_imp)
     apply (rule kernel_corres)
    apply force
   apply (simp add: sch_act_simple_def)
  apply metis
  done

lemma handleHypervisorEvent_ccorres:
  "ccorres dc xfdc
           (invs' and sch_act_simple)
           UNIV []
           (callKernel (HypervisorEvent t)) handleHypervisorEvent_C"
  apply (simp add: callKernel_def handleEvent_def handleHypervisorEvent_C_def)
  apply (simp add: liftE_def bind_assoc)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       apply (cases t; simp add: handleHypervisorFault_def)
       apply (ctac (no_vcg) add: schedule_ccorres)
        apply (rule ccorres_stateAssert_after)
        apply (rule ccorres_guard_imp[where A="A and P" and Q=A for A P])
          apply (ctac (no_vcg) add: activateThread_ccorres)
         apply simp
        apply assumption
       apply (wp schedule_sch_act_wf schedule_invs'
              | strengthen invs_queues_imp invs_valid_objs_strengthen)+
    apply clarsimp+
  done

lemma callKernel_corres_C:
  "corres_underlying rf_sr False True dc
           (all_invs' e)
           \<top>
           (callKernel e) (callKernel_C e)"
  using no_fail_callKernel [of e]
  apply (clarsimp simp: callKernel_C_def)
  apply (cases e, simp_all)
      prefer 4
      apply (rule ccorres_corres_u)
       apply simp
       apply (rule ccorres_guard_imp)
         apply (rule handleInterruptEntry_ccorres)
        apply (clarsimp simp: all_invs'_def sch_act_simple_def)
       apply simp
      apply assumption
     prefer 2
     apply (rule ccorres_corres_u [rotated], assumption)
     apply simp
     apply (rule ccorres_guard_imp)
       apply (rule ccorres_call)
          apply (rule handleUnknownSyscall_ccorres)
         apply (clarsimp simp: all_invs'_def sch_act_simple_def)+
    prefer 3
    apply (rule ccorres_corres_u [rotated], assumption)
     apply (rule ccorres_guard_imp)
       apply (rule ccorres_call)
          apply (rule handleVMFaultEvent_ccorres)
         apply (clarsimp simp: all_invs'_def sch_act_simple_def)+
   prefer 2
   apply (rule ccorres_corres_u [rotated], assumption)
    apply (rule ccorres_guard_imp)
      apply (rule ccorres_call)
         apply (rule handleUserLevelFault_ccorres)
        apply (clarsimp simp: all_invs'_def sch_act_simple_def)+
  apply (rule ccorres_corres_u [rotated], assumption)
   apply (rule ccorres_guard_imp)
     apply (rule ccorres_call)
        apply (rule handleSyscall_ccorres)
       apply (clarsimp simp: all_invs'_def sch_act_simple_def)+
   apply (rule ccorres_corres_u [rotated], assumption)
    apply (rule ccorres_guard_imp)
         apply (rule handleHypervisorEvent_ccorres)
        apply (clarsimp simp: all_invs'_def sch_act_simple_def)
       apply simp
  done

lemma ccorres_add_gets:
  "ccorresG rf_sr \<Gamma> rv xf P P' hs (do v \<leftarrow> gets f; m od) c
    \<Longrightarrow> ccorresG rf_sr \<Gamma> rv xf P P' hs m c"
  by (simp add: gets_bind_ign)

lemma ccorres_get_registers:
  "\<lbrakk> \<And>cptr msgInfo. ccorres dc xfdc
     ((\<lambda>s. P s \<and> Q s \<and>
           obj_at' (\<lambda>tcb. (atcbContextGet o tcbArch) tcb ARM_H.capRegister = cptr
                      \<and>   (atcbContextGet o tcbArch) tcb ARM_H.msgInfoRegister = msgInfo)
             (ksCurThread s) s) and R)
     (UNIV \<inter> \<lbrace>\<acute>cptr = cptr\<rbrace> \<inter> \<lbrace>\<acute>msgInfo = msgInfo\<rbrace>) [] m c \<rbrakk>
      \<Longrightarrow>
   ccorres dc xfdc
     (P and Q and ct_in_state' \<top> and R)
     {s. \<exists>v. cslift s (ksCurThread_' (globals s)) = Some v
              \<and> cptr_' s = index (registers_C (tcbContext_C (tcbArch_C v))) (unat Kernel_C.capRegister)
              \<and> msgInfo_' s = index (registers_C (tcbContext_C (tcbArch_C v))) (unat Kernel_C.msgInfoRegister)} []
     m c"
  apply (rule ccorres_assume_pre)
  apply (clarsimp simp: ct_in_state'_def st_tcb_at'_def)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule_tac x="(atcbContextGet o tcbArch) ko ARM_H.capRegister" in meta_allE)
  apply (erule_tac x="(atcbContextGet o tcbArch) ko ARM_H.msgInfoRegister" in meta_allE)
  apply (erule ccorres_guard_imp2)
  apply (clarsimp simp: rf_sr_ksCurThread)
  apply (drule(1) obj_at_cslift_tcb, clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: ctcb_relation_def ccontext_relation_def
                        ARM_H.msgInfoRegister_def ARM_H.capRegister_def
                        ARM.msgInfoRegister_def ARM.capRegister_def
                        carch_tcb_relation_def
                        "StrictC'_register_defs")
  done

lemma callKernel_withFastpath_corres_C:
  "corres_underlying rf_sr False True dc
           (all_invs' e)
           \<top>
           (callKernel e) (callKernel_withFastpath_C e)"
  using no_fail_callKernel [of e] callKernel_corres_C [of e]
  supply if_split[split del]
  apply (cases "e = SyscallEvent syscall.SysCall \<or>
            e = SyscallEvent syscall.SysReplyRecv")
  apply (simp_all add: callKernel_withFastpath_C_def
                  del: Collect_const cong: call_ignore_cong)
  apply (erule ccorres_corres_u[rotated])
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_rhs_assoc)+
   apply (rule ccorres_symb_exec_r)+
       apply (rule ccorres_Cond_rhs)
        apply simp
        apply (ctac add: ccorres_get_registers[OF fastpath_call_ccorres_callKernel])
       apply simp
       apply (ctac add: ccorres_get_registers[OF fastpath_reply_recv_ccorres_callKernel])
      apply vcg
     apply (rule conseqPre, vcg, clarsimp)
    apply vcg
   apply (rule conseqPre, vcg, clarsimp)
  apply (clarsimp simp: all_invs'_def rf_sr_ksCurThread)
  apply (frule(1) obj_at_cslift_tcb[OF tcb_at_invs'])
  apply (clarsimp simp: typ_heap_simps' ct_in_state'_def
                        "StrictC'_register_defs" word_sle_def word_sless_def
                        st_tcb_at'_opeq_simp)
  apply (rule conjI, fastforce simp: st_tcb_at'_def)
  apply (auto elim!: pred_tcb'_weakenE cnode_caps_gsCNodes_from_sr[rotated])
  done

lemma threadSet_all_invs_triv':
  "\<lbrace>all_invs' e and (\<lambda>s. t = ksCurThread s)\<rbrace>
  threadSet (\<lambda>tcb. tcbArch_update (\<lambda>_. atcbContextSet f (tcbArch tcb)) tcb) t \<lbrace>\<lambda>_. all_invs' e\<rbrace>"
  unfolding all_invs'_def
  apply (rule hoare_pre)
   apply (rule wp_from_corres_unit)
     apply (rule threadset_corresT [where f="tcb_arch_update (arch_tcb_context_set f)"])
        apply (simp add: tcb_relation_def arch_tcb_context_set_def
                         atcbContextSet_def arch_tcb_relation_def)
       apply (simp add: tcb_cap_cases_def)
      apply (simp add: tcb_cte_cases_def)
     apply (simp add: exst_same_def)
    apply (wp thread_set_invs_trivial thread_set_ct_running thread_set_not_state_valid_sched
              threadSet_invs_trivial threadSet_ct_running' static_imp_wp
              thread_set_ct_in_state
           | simp add: tcb_cap_cases_def tcb_arch_ref_def
           | rule threadSet_ct_in_state'
           | wp (once) hoare_vcg_disj_lift)+
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
  apply (clarsimp simp: invs_def invs'_def cur_tcb_def cur_tcb'_def)
  apply (simp add: state_relation_def)
  done

lemma getContext_corres:
  "t' = tcb_ptr_to_ctcb_ptr t \<Longrightarrow>
  corres_underlying rf_sr False True (=) (tcb_at' t) \<top>
                    (threadGet (atcbContextGet o tcbArch) t) (gets (getContext_C t'))"
  apply (clarsimp simp: corres_underlying_def simpler_gets_def)
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (frule threadGet_eq)
  apply (rule bexI)
   prefer 2
   apply assumption
  apply clarsimp
  apply (clarsimp simp: getContext_C_def)
  apply (drule cmap_relation_ko_atD [rotated])
   apply fastforce
  apply (clarsimp simp: typ_heap_simps ctcb_relation_def carch_tcb_relation_def from_user_context_C)
  done

lemma callKernel_cur:
  "\<lbrace>all_invs' e\<rbrace> callKernel e \<lbrace>\<lambda>rv s. tcb_at' (ksCurThread s) s\<rbrace>"
  apply (rule hoare_chain)
    apply (rule ckernel_invs)
   apply (clarsimp simp: all_invs'_def sch_act_simple_def)
  apply clarsimp
  done

lemma entry_corres_C:
  "corres_underlying rf_sr False True (=)
           (all_invs' e)
           \<top>
           (kernelEntry e uc) (kernelEntry_C fp e uc)"
  apply (simp add: kernelEntry_C_def kernelEntry_def getCurThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where P=\<top> and P'=\<top> and r'="\<lambda>t t'. t' = tcb_ptr_to_ctcb_ptr t"])
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
      apply (rule corres_split)
         apply (rule setTCBContext_C_corres, rule ccontext_rel_to_C, simp)
        apply simp
        apply (rule corres_split)
           apply (rule corres_cases[where R=fp]; simp)
            apply (rule callKernel_withFastpath_corres_C)
           apply (rule callKernel_corres_C)
          apply (rule corres_split[where P=\<top> and P'=\<top> and r'="\<lambda>t t'. t' = tcb_ptr_to_ctcb_ptr t"])
             apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
            apply (rule getContext_corres, simp)
           apply (wp threadSet_all_invs_triv' callKernel_cur)+
   apply (clarsimp simp: all_invs'_def invs'_def cur_tcb'_def valid_state'_def)
  apply simp
  done

lemma entry_refinement_C:
  "\<lbrakk>all_invs' e s; (s, t) \<in> rf_sr \<rbrakk>
     \<Longrightarrow> \<not> snd (kernelEntry_C fp e tc t)
        \<and> (\<forall>tc' t'. (tc',t') \<in> fst (kernelEntry_C fp e tc t)
            \<longrightarrow> (\<exists>s'. (tc', s') \<in> fst (kernelEntry e tc s) \<and> (s',t') \<in> rf_sr))"
  using entry_corres_C [of e]
  by (fastforce simp add: corres_underlying_def)

lemma ct_running'_C:
  "\<lbrakk> (s, t) \<in> rf_sr; invs' s \<rbrakk> \<Longrightarrow> ct_running' s = ct_running_C t"
  apply (simp add: ct_running_C_def Let_def ct_in_state'_def st_tcb_at'_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def cpspace_relation_def Let_def)
  apply (rule iffI)
   apply (drule obj_at_ko_at')
   apply clarsimp
   apply (erule (1) cmap_relation_ko_atE)
   apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def)
  apply clarsimp
  apply (drule (1) cmap_relation_cs_atD [where addr_fun=tcb_ptr_to_ctcb_ptr])
   apply simp
  apply clarsimp
  apply (frule (1) map_to_ko_atI')
  apply (erule obj_at'_weakenE)
  apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def)
  apply (case_tac "tcbState ko", simp_all add:
    ThreadState_Running_def
    ThreadState_BlockedOnReceive_def
    ThreadState_BlockedOnSend_def
    ThreadState_BlockedOnReply_def
    ThreadState_BlockedOnNotification_def
    ThreadState_Inactive_def
    ThreadState_IdleThreadState_def
    ThreadState_Restart_def)
  done

lemma full_invs_both:
  "ADT_H uop \<Turnstile>
  {s'. \<exists>s. (s,s') \<in> lift_state_relation state_relation \<and>
     s \<in> full_invs \<and> s' \<in> full_invs'}"
  apply (rule fw_inv_transport)
    apply (rule akernel_invariant)
   apply (rule ckernel_invariant)
  apply (rule fw_sim_A_H)
  done
end

context kernel_m
begin

lemma user_memory_update_corres_C_helper:
      "\<lbrakk>(a, b) \<in> rf_sr; pspace_aligned' a; pspace_distinct' a;
        dom um \<subseteq> dom (user_mem' a)\<rbrakk>
       \<Longrightarrow> (ksMachineState_update
            (underlying_memory_update
              (\<lambda>m. foldl (\<lambda>f p. f(p := the (um p))) m [p\<leftarrow>e. p \<in> dom um])) a,
            b\<lparr>globals := globals b
               \<lparr>t_hrs_' :=
                  (foldl (\<lambda>f p. f(p := the (um p))) (fst (t_hrs_' (globals b)))
                    [p\<leftarrow>e. p \<in> dom um],
                   snd (t_hrs_' (globals b)))\<rparr>\<rparr>)
           \<in> rf_sr"
  apply (induct e)
   apply simp
   apply (subgoal_tac
            "ksMachineState_update (underlying_memory_update (\<lambda>m. m)) a = a")
    apply (simp (no_asm_simp))
   apply simp
  apply (rename_tac x xs)
  apply (simp add: foldl_fun_upd_eq_foldr)
  apply (case_tac "x \<in> dom um", simp_all)
  apply (frule_tac ptr=x and b="the (um x)" in storeByteUser_rf_sr_upd)
     apply simp
    apply simp
   apply (thin_tac "(x,y) : rf_sr" for x y)+
   apply (fastforce simp add: pointerInUserData_def dom_user_mem')
  apply (simp add: o_def hrs_mem_update_def)
  done

lemma user_memory_update_corres_C:
  "corres_underlying rf_sr False nf (%_ _. True)
     (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> dom um \<subseteq> dom (user_mem' s))
     \<top>
     (doMachineOp (user_memory_update um)) (setUserMem_C um)"
  supply option.case_cong_weak[cong]
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp add: setUserMem_C_def simpler_modify_def)
  apply (subgoal_tac
       "doMachineOp (user_memory_update um) a =
        modify (ksMachineState_update (underlying_memory_update
                 (\<lambda>m. foldl (\<lambda>f p. f(p := the (um p))) m [p\<leftarrow>enum. p \<in> dom um])))
               a")
   prefer 2
   apply (clarsimp simp add: doMachineOp_def user_memory_update_def
                             simpler_modify_def simpler_gets_def select_f_def
                             Nondet_Monad.bind_def return_def)
   apply (thin_tac P for P)+
   apply (case_tac a, clarsimp)
   apply (case_tac ksMachineStatea, clarsimp)
   apply (rule ext)
   apply (simp add: foldl_fun_upd_value dom_def split: option.splits)
  apply clarsimp
  apply (cut_tac s'=a and s="globals b" in user_mem_C_relation[symmetric])
    apply (simp add: rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
   apply simp+
  apply (simp add: setUserMem_C_def_foldl)
  apply (clarsimp simp add: simpler_modify_def)
  apply (thin_tac "doMachineOp p s = x" for p s x)
  apply (drule sym, simp)
  apply (rule user_memory_update_corres_C_helper,auto)[1]
  done

lemma device_update_corres_C:
  "corres_underlying rf_sr False nf (=) (\<lambda>_. True) (\<lambda>_. True)
   (doMachineOp (device_memory_update ms))
   (setDeviceState_C ms)"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
    prefer 2
    apply (clarsimp simp add: setDeviceState_C_def simpler_modify_def)
  apply (rule ballI)
  apply (clarsimp simp: simpler_modify_def setDeviceState_C_def)
  apply (clarsimp simp: doMachineOp_def device_memory_update_def Nondet_Monad.bind_def in_monad
                        gets_def get_def return_def simpler_modify_def select_f_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                        cmachine_state_relation_def)
  done

lemma mem_dom_split:
 "(dom um \<subseteq> dom (user_mem' s) \<union> dom (device_mem' s))
 \<Longrightarrow> um = restrict_map um (dom (user_mem' s)) ++ restrict_map um (dom (device_mem' s))"
 apply (rule ext)
 apply (auto simp: map_add_def restrict_map_def split:if_splits option.splits)
 done

lemma dom_if_rewrite:
  "dom (\<lambda>x. if P x then Some (f x) else None) = dom (\<lambda>x. if P x then Some () else None)"
  by (auto split:if_splits)

crunch dmo_typ_at_pre_dom[wp]: doMachineOp "\<lambda>s. P (dom (\<lambda>x. if typ_at' T (x && ~~ mask pageBits) s then Some () else None))"
  (wp: crunch_wps simp: crunch_simps device_mem'_def)

lemma dmo_domain_device_mem'[wp]:
  "\<lbrace>\<lambda>s. P (dom (device_mem' s))\<rbrace> doMachineOp opfun \<lbrace>\<lambda>rv sa. P (dom (device_mem' sa))\<rbrace>"
  apply (simp add:device_mem'_def pointerInDeviceData_def)
  apply (rule hoare_pre)
  apply (subst dom_if_rewrite)
  apply (wp doMachineOp_typ_at')
  apply (erule arg_cong[where f = P,THEN iffD1,rotated])
  apply (auto split:if_splits)
  done

lemma dmo_domain_user_mem'[wp]:
  "\<lbrace>\<lambda>s. P (dom (user_mem' s))\<rbrace> doMachineOp opfun \<lbrace>\<lambda>rv sa. P (dom (user_mem' sa))\<rbrace>"
  apply (simp add:user_mem'_def pointerInUserData_def)
  apply (rule hoare_pre)
  apply (subst dom_if_rewrite)
  apply (wp doMachineOp_typ_at')
  apply (erule arg_cong[where f = P,THEN iffD1,rotated])
  apply (auto split:if_splits)
  done

lemma do_user_op_corres_C:
  "corres_underlying rf_sr False False (=) (invs' and ex_abs einvs) \<top>
                     (doUserOp f tc) (doUserOp_C f tc)"
  apply (simp only: doUserOp_C_def doUserOp_def split_def)
  apply (rule corres_guard_imp)
    apply (rule_tac P=\<top> and P'=\<top> and r'="(=)" in corres_split)
       apply (clarsimp simp: simpler_gets_def getCurThread_def
                corres_underlying_def rf_sr_def cstate_relation_def Let_def)
      apply (rule_tac P=valid_state' and P'=\<top> and r'="(=)" in corres_split)
         apply (clarsimp simp: cstate_to_A_def absKState_def
                               rf_sr_def cstate_to_H_correct ptable_lift_def)
        apply (rule_tac P=valid_state' and P'=\<top> and r'="(=)" in corres_split)
           apply (clarsimp simp: cstate_to_A_def absKState_def
                                 rf_sr_def cstate_to_H_correct ptable_rights_def)
          apply (rule_tac P=pspace_distinct' and P'=\<top> and r'="(=)"
                 in corres_split)
             apply clarsimp
             apply (rule fun_cong[where x=ptrFromPAddr])
             apply (rule_tac f=comp in arg_cong)
             apply (rule user_mem_C_relation[symmetric])
              apply (simp add: rf_sr_def cstate_relation_def Let_def
                               cpspace_relation_def)
             apply assumption
            apply (rule_tac P=pspace_distinct' and P'=\<top> and r'="(=)"
                 in corres_split)
               apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                               cpspace_relation_def)
               apply (drule(1) device_mem_C_relation[symmetric])
               apply simp
              apply (rule_tac P=valid_state' and P'=\<top> and r'="(=)" in corres_split)
                 apply (clarsimp simp: cstate_relation_def rf_sr_def
                   Let_def cmachine_state_relation_def)
                apply (rule_tac P=\<top> and P'=\<top> and r'="(=)" in corres_split)
                   apply (clarsimp simp add: corres_underlying_def fail_def
                        assert_def return_def
                        split:if_splits)
                  apply simp
                  apply (rule_tac P=\<top> and P'=\<top> and r'="(=)" in corres_split)
                    apply (clarsimp simp add: corres_underlying_def fail_def
                         assert_def return_def
                         split:if_splits)
                   apply simp
                   apply (rule_tac r'="(=)" in corres_split[OF corres_select])
                      apply clarsimp
                     apply simp
                     apply (rule corres_split[OF user_memory_update_corres_C])
                         apply (rule corres_split[OF device_update_corres_C,
                                         where R="\<top>\<top>" and R'="\<top>\<top>"])
                        apply (wp select_wp | simp)+
   apply (intro conjI allI ballI impI)
     apply ((clarsimp simp add: invs'_def valid_state'_def valid_pspace'_def)+)[5]
    apply (clarsimp simp:  ex_abs_def restrict_map_def
                  split: if_splits)
    apply (drule ptable_rights_imp_UserData[rotated -1])
     apply fastforce+
    apply (clarsimp simp: invs'_def valid_state'_def user_mem'_def device_mem'_def
                   split: if_splits)
    apply (drule_tac c = x in subsetD[where B = "dom S" for S])
     apply (simp add:dom_def)
    apply fastforce
   apply clarsimp
  done

lemma check_active_irq_corres_C:
  "corres_underlying rf_sr False True (=)
             (invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ex_abs valid_state) \<top>
             (checkActiveIRQ) (checkActiveIRQ_C)"
  apply (simp add: checkActiveIRQ_C_def checkActiveIRQ_def getActiveIRQ_C_def)
  apply (rule corres_guard_imp)
    apply (subst bind_assoc[symmetric])
    apply (rule corres_split)
       apply (rule ccorres_corres_u_xf)
        apply (rule ccorres_rel_imp, rule ccorres_guard_imp)
           apply (ctac add:getActiveIRQ_ccorres)
          apply (rule TrueI)
         apply simp
        apply assumption
       apply (rule no_fail_dmo')
       apply (rule no_fail_getActiveIRQ)
      apply (clarsimp simp: ucast_helper_simps_32 irqInvalid_def ucast_up_ucast_id
                            is_up_def source_size_def target_size_def word_size mask_def
                      split: option.splits)
     apply (rule hoare_TrueI)+
   apply (wp|simp)+
  done

lemma refinement2_both:
  "\<lparr> Init = Init_C, Fin = Fin_C,
     Step = (\<lambda>u. global_automaton check_active_irq_C (do_user_op_C uop) (kernel_call_C fp)) \<rparr>
   \<sqsubseteq> ADT_H uop"
  supply word_neq_0_conv[simp]
  apply (rule sim_imp_refines)
  apply (rule L_invariantI [where I\<^sub>c=UNIV and r="lift_state_relation rf_sr"])
    apply (rule full_invs_both)
   apply simp
  apply (unfold LI_def)
  apply (rule conjI)
   apply (simp add: ADT_H_def)
   apply (blast intro!: init_refinement_C)
  apply (rule conjI)
   prefer 2
   apply (simp add: ADT_H_def)
   apply (clarsimp simp: Fin_C_def)
   apply (drule lift_state_relationD)
   apply (clarsimp simp: cstate_to_A_def)
    apply (subst cstate_to_H_correct)
     apply (fastforce simp: full_invs'_def invs'_def)
    apply (clarsimp simp: rf_sr_def)
   apply (simp add:absKState_def observable_memory_def absExst_def)
   apply (rule MachineTypes.machine_state.equality,simp_all)[1]
   apply (rule ext)
   apply (clarsimp simp: user_mem'_def option_to_0_def split:if_splits)
  apply (simp add: ADT_H_def)
  supply subst_all [simp del]
  apply (clarsimp simp: rel_semi_def global_automaton_def relcomp_unfold
                        in_lift_state_relation_eq)

  apply (erule_tac P="a \<and> (\<exists>x. b x)" for a b in disjE)
  apply (clarsimp simp add: kernel_call_C_def kernel_call_H_def)
  apply (subgoal_tac "all_invs' x b")
   apply (drule_tac fp=fp and tc=af in entry_refinement_C, simp+)
   apply clarsimp
   apply (drule spec, drule spec, drule(1) mp)
   apply (clarsimp simp: full_invs'_def)
   apply (frule use_valid, rule kernelEntry_invs',
          simp add: sch_act_simple_def)
    apply (fastforce simp: ct_running'_C)
    apply (clarsimp simp: full_invs_def full_invs'_def all_invs'_def)
   apply fastforce

  apply (erule_tac P="a \<and> b \<and> c \<and> d \<and> e" for a b c d e in disjE)
   apply (clarsimp simp add: do_user_op_C_def do_user_op_H_def monad_to_transition_def)
   apply (rule rev_mp, rule_tac f="uop" and tc=af in do_user_op_corres_C)
   apply (clarsimp simp: corres_underlying_def invs_def ex_abs_def)
   apply (fastforce simp: full_invs'_def ex_abs_def)

  apply (erule_tac P="a \<and> b \<and> c \<and> (\<exists>x. e x)" for a b c d e in disjE)
   apply (clarsimp simp add: do_user_op_C_def do_user_op_H_def monad_to_transition_def)
   apply (rule rev_mp, rule_tac f="uop" and tc=af in do_user_op_corres_C)
   apply (clarsimp simp: corres_underlying_def invs_def ex_abs_def)
   apply (fastforce simp: full_invs'_def ex_abs_def)

  apply (clarsimp simp: check_active_irq_C_def check_active_irq_H_def)
  apply (rule rev_mp, rule check_active_irq_corres_C)
  apply (fastforce simp: corres_underlying_def full_invs'_def ex_abs_def)
  done

theorem refinement2:
  "ADT_C uop \<sqsubseteq> ADT_H uop"
  unfolding ADT_C_def
  by (rule refinement2_both)

theorem fp_refinement:
  "ADT_FP_C uop \<sqsubseteq> ADT_H uop"
  unfolding ADT_FP_C_def
  by (rule refinement2_both)

theorem seL4_refinement:
  "ADT_C uop \<sqsubseteq> ADT_A uop"
  by (blast intro: refinement refinement2 refinement_trans)

theorem seL4_fastpath_refinement:
  "ADT_FP_C uop \<sqsubseteq> ADT_A uop"
  by (blast intro: refinement fp_refinement refinement_trans)

lemma exec_C_Basic:
  "exec_C Gamma (Basic f) = (modify f)"
  apply (rule ext)
  apply (simp add: exec_C_def simpler_modify_def)
  apply (auto elim: exec.cases intro: exec.intros)
  done

lemma in_monad_imp_rewriteE:
  "\<lbrakk> (a, b) \<in> fst (f' s); monadic_rewrite F False \<top> f f'; F \<longrightarrow> \<not> snd (f s) \<rbrakk>
     \<Longrightarrow> (a, b) \<in> fst (f s)"
  by (auto simp add: monadic_rewrite_def)

lemma ccorres_underlying_Fault:
  "\<lbrakk> ccorres_underlying srel Gamma rrefl xf arrel axf G G' hs m c;
           \<exists>s. (s, s') \<in> srel \<and> G s \<and> s' \<in> G' \<and> \<not> snd (m s) \<rbrakk>
      \<Longrightarrow> \<not> Gamma \<turnstile> \<langle>c, Normal s'\<rangle> \<Rightarrow> Fault ft"
  apply clarsimp
  apply (erule(4) ccorresE)
   apply (erule exec_handlers.EHOther)
   apply simp
  apply simp
  done

lemma monadic_rewrite_\<Gamma>:
  "monadic_rewrite True False \<top>
    (exec_C \<Gamma> c)
    (exec_C (kernel_all_global_addresses.\<Gamma> symbol_table) c)"
  using spec_refine [of symbol_table domain]
  using spec_simulates_to_exec_simulates
  apply (clarsimp simp: spec_statefn_simulates_via_statefn
                        o_def map_option_case monadic_rewrite_def exec_C_def
                   split: option.splits
                   cong: option.case_cong)
  apply blast
  done

lemma no_fail_getActiveIRQ_C:
  "\<not>snd (getActiveIRQ_C s)"
  apply (clarsimp simp: getActiveIRQ_C_def exec_C_def)
  apply (drule getActiveIRQ_Normal)
  apply (clarsimp simp: isNormal_def)
  done

lemma kernel_all_subset_kernel:
  "global_automaton (kernel_global.check_active_irq_C symbol_table) (do_user_op_C uop)
       (kernel_global.kernel_call_C symbol_table fp)
       \<subseteq> global_automaton check_active_irq_C (do_user_op_C uop) (kernel_call_C fp)"
  apply (clarsimp simp: fw_sim_def rel_semi_def global_automaton_def
                        relcomp_unfold in_lift_state_relation_eq)
  apply (intro conjI)
   apply (simp_all add: kernel_global.kernel_call_C_def
                    kernel_call_C_def kernelEntry_C_def
                    setTCBContext_C_def
                    kernel_global.kernelEntry_C_def
                     exec_C_Basic
                    kernel_global.setTCBContext_C_def
                    kernel_call_H_def kernelEntry_def
                    getContext_C_def
                    check_active_irq_C_def checkActiveIRQ_C_def
                    kernel_global.check_active_irq_C_def kernel_global.checkActiveIRQ_C_def
                    check_active_irq_H_def checkActiveIRQ_def)
       apply clarsimp
       apply (erule in_monad_imp_rewriteE[where F=True])
        apply (rule monadic_rewrite_guard_imp)
         apply (rule monadic_rewrite_bind_tail)+
           apply (rule monadic_rewrite_bind_head[where P=\<top>])
           apply (simp add: callKernel_C_def callKernel_withFastpath_C_def
                            kernel_global.callKernel_C_def
                            kernel_global.callKernel_withFastpath_C_def
                            handleHypervisorEvent_C_def kernel_global.handleHypervisorEvent_C_def
                       split: event.split if_split)
           apply (intro allI impI conjI monadic_rewrite_\<Gamma>)[1]
          apply ((wp | simp)+)[3]
        apply (clarsimp simp: snd_bind snd_modify in_monad gets_def)
       apply clarsimp
      apply clarsimp
     apply clarsimp
    apply (clarsimp simp: in_monad)
    apply (erule (1) notE[OF _ in_monad_imp_rewriteE[where F=True]])
     apply (simp add: kernel_global.getActiveIRQ_C_def getActiveIRQ_C_def)
     apply (rule monadic_rewrite_\<Gamma>)
    apply (simp add: no_fail_getActiveIRQ_C)
   apply (clarsimp simp: in_monad)
   apply (erule (1) notE[OF _ in_monad_imp_rewriteE[where F=True]])
    apply (simp add: kernel_global.getActiveIRQ_C_def getActiveIRQ_C_def)
    apply (rule monadic_rewrite_\<Gamma>)
   apply (simp add: no_fail_getActiveIRQ_C)
  apply (clarsimp simp: in_monad)
  apply (erule (1) notE[OF _ in_monad_imp_rewriteE[where F=True]])
   apply (simp add: kernel_global.getActiveIRQ_C_def getActiveIRQ_C_def)
   apply (rule monadic_rewrite_\<Gamma>)
  apply (simp add: no_fail_getActiveIRQ_C)
  done

theorem true_refinement:
  "kernel_global.ADT_C symbol_table armKSKernelVSpace_C uop
   \<sqsubseteq> ADT_H uop"
  apply (rule refinement_trans[OF _ refinement2])
  apply (simp add: kernel_global.ADT_C_def ADT_C_def)
  apply (rule sim_imp_refines)
  apply (clarsimp simp: fw_simulates_def)
  apply (rule_tac x=Id in exI)
  using kernel_all_subset_kernel
  apply (simp add: fw_sim_def rel_semi_def)
  done

theorem true_fp_refinement:
  "kernel_global.ADT_FP_C symbol_table armKSKernelVSpace_C uop
   \<sqsubseteq> ADT_H uop"
  apply (rule refinement_trans[OF _ fp_refinement])
  apply (simp add: kernel_global.ADT_FP_C_def ADT_FP_C_def)
  apply (rule sim_imp_refines)
  apply (clarsimp simp: fw_simulates_def)
  apply (rule_tac x=Id in exI)
  using kernel_all_subset_kernel
  apply (simp add: fw_sim_def rel_semi_def)
  done

end

end
