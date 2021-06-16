(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ADT_IF_Refine_C
imports ADT_IF_Refine "CRefine.Refine_C"
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition handleInterruptEntry_C_body_if (*:: "(globals myvars, int, l4c_errortype) com"*) where
"handleInterruptEntry_C_body_if \<equiv> (
      (\<acute>irq :== CALL getActiveIRQ();;
       (Guard SignedArithmetic \<lbrace>True\<rbrace>
         (IF (ucast \<acute>irq :: word32) \<noteq> (ucast ((ucast (-1 :: 16 word)) :: word32)) THEN
            CALL handleInterrupt(\<acute>irq)
          FI)));;
       \<acute>ret__unsigned_long :== scast EXCEPTION_NONE)"



definition handleSyscall_C_body_if
  where
  "handleSyscall_C_body_if s \<equiv>
        (IF s = Kernel_C.SysSend THEN
           \<acute>ret__unsigned_long :== CALL handleInvocation(scast false,
           scast true)
         ELSE
           IF s = Kernel_C.SysNBSend THEN
             \<acute>ret__unsigned_long :== CALL handleInvocation(scast false,
             scast false)
           ELSE
             IF s = Kernel_C.SysCall THEN
               \<acute>ret__unsigned_long :== CALL handleInvocation(scast true,
               scast true)
             ELSE
               IF s = Kernel_C.SysRecv THEN
                 CALL handleRecv(scast true) ;;
                 \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
               ELSE
                 IF s = Kernel_C.SysReply THEN
                   CALL handleReply() ;;
                   \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
                 ELSE
                   IF s = Kernel_C.SysReplyRecv THEN
                     CALL handleReply();;
                     CALL handleRecv(scast true);;
                     \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
                   ELSE
                     IF s = Kernel_C.SysYield THEN
                       CALL handleYield();;
                       \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
                     ELSE
                       IF s = Kernel_C.SysNBRecv THEN
                         CALL handleRecv(scast false);;
                         \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
                       ELSE
                         IF True THEN
                           CALL halt()
                         FI
                       FI
                     FI
                   FI
                 FI
               FI
             FI
           FI
         FI)"

definition handleUnknownSyscall_C_body_if
  where
  "handleUnknownSyscall_C_body_if w \<equiv>
    (\<acute>current_fault :== CALL seL4_Fault_UnknownSyscall_new(w);;
      (CALL handleFault(\<acute>ksCurThread);;
         \<acute>ret__unsigned_long :== scast EXCEPTION_NONE))"

definition handleUserLevelFault_C_body_if
  where
  "handleUserLevelFault_C_body_if w1 w2 \<equiv>
    (\<acute>current_fault :== CALL seL4_Fault_UserException_new(w1,w2);;
      (CALL handleFault(\<acute>ksCurThread);;
         \<acute>ret__unsigned_long :== scast EXCEPTION_NONE))"

definition handleVMFaultEvent_C_body_if
  where
  "handleVMFaultEvent_C_body_if vm_faultType ==
     (\<acute>status :== CALL handleVMFault(\<acute>ksCurThread,scast vm_faultType);;
         (IF \<acute>status \<noteq> scast EXCEPTION_NONE THEN
            CALL handleFault(\<acute>ksCurThread)
          FI;;
            \<acute>ret__unsigned_long :== scast EXCEPTION_NONE))"

end

context kernel_m begin

definition
  "callKernel_C_body_if e \<equiv> case e of
    SyscallEvent n \<Rightarrow> (handleSyscall_C_body_if (ucast (syscall_from_H n)))
  | UnknownSyscall n \<Rightarrow>  (handleUnknownSyscall_C_body_if (of_nat n))
  | UserLevelFault w1 w2 \<Rightarrow> (handleUserLevelFault_C_body_if w1 w2)
  | Interrupt \<Rightarrow> (handleInterruptEntry_C_body_if)
  | VMFaultEvent t \<Rightarrow> (handleVMFaultEvent_C_body_if (vm_fault_type_from_H t))
  | HypervisorEvent t \<Rightarrow> (SKIP ;; \<acute>ret__unsigned_long :== scast EXCEPTION_NONE)"


definition
  kernelEntry_C_if (*::
    "bool \<Rightarrow> event \<Rightarrow> user_context \<Rightarrow> (cstate, (bool \<times> user_context)) nondet_monad"*)
  where
  "kernelEntry_C_if (fp :: bool) e tc \<equiv> do
    t \<leftarrow> gets (ksCurThread_' o globals);
    setArchTCB_C (arch_tcb_C (to_user_context_C tc)) t;
    exec_C \<Gamma> (callKernel_C_body_if e);
    ex \<leftarrow> gets ret__unsigned_long_';
    r \<leftarrow> return (if (ex = scast EXCEPTION_NONE) then Inr () else Inl ex);
  \<^cancel>\<open>
    stateAssert (\<lambda>s. (e \<noteq> Interrupt \<longrightarrow> 0 < ksDomainTime_' (globals s)) \<and>
                     (e = Interrupt \<longrightarrow> ksDomainTime_' (globals s) = 0 \<longrightarrow>
                         ksSchedulerAction_' (globals s) = Ptr 1) \<and>
                     valid_domain_listC) [];\<close>
    return (r,tc)
  od"

definition
  kernel_call_C_if
  where
  "kernel_call_C_if fp e \<equiv>
      {(s, b, (tc,s'))|s b tc s' r. ((r,tc),s') \<in> fst (split (kernelEntry_C_if fp e) s) \<and>
                   b = (case r of Inl x \<Rightarrow> True | Inr x \<Rightarrow> False)}"


lemma handleInterrupt_ccorres:
  "ccorres (K dc \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
           (invs')
           (UNIV)
           []
           (handleEvent Interrupt)
           (handleInterruptEntry_C_body_if)"
proof -
  have ucast_not_helper_cheating_unsigned:
    "\<And>a. ucast (a::10 word) \<noteq> (0xFFFF :: word16) \<Longrightarrow> ucast a \<noteq> (0xFFFF::32 word)"
    by (word_bitwise)
  show ?thesis
  apply (rule ccorres_guard_imp2)
   apply (simp add: handleEvent_def minus_one_norm handleInterruptEntry_C_body_if_def)
   apply (clarsimp simp: liftE_def bind_assoc)
   apply (rule ccorres_rhs_assoc)
   apply (ctac (no_vcg) add: getActiveIRQ_ccorres)
    apply (rule ccorres_Guard_Seq)
    apply (rule_tac P="rv \<noteq> Some 0xFFFF" in ccorres_gen_asm)
    apply wpc
     apply (simp add: ccorres_cond_empty_iff)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply (clarsimp simp: ucast_not_helper_cheating_unsigned ucast_helper_simps_32
      ucast_not_helper ccorres_cond_univ_iff ucast_ucast_a is_down)
    apply (ctac (no_vcg) add: handleInterrupt_ccorres)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wp
   apply (rule_tac Q="\<lambda>rv s. invs' s \<and> (\<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ)
                                     \<and> rv \<noteq> Some 0xFFFF" in hoare_post_imp)
    apply (clarsimp simp: Kernel_C.maxIRQ_def ARM.maxIRQ_def)
   apply (wp getActiveIRQ_le_maxIRQ getActiveIRQ_neq_Some0xFF | simp)+
  apply (clarsimp simp: invs'_def valid_state'_def)
  done
qed

lemma handleEvent_ccorres:
  notes K_def[simp del]
  shows
  "ccorres (\<lambda>rv rv'. (rv = Inr ()) = (rv' = scast EXCEPTION_NONE)) ret__unsigned_long_'
           (invs' and
               (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
                (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) and
               (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
           (UNIV) []
           (handleEvent e) (callKernel_C_body_if e)"
  supply option.case_cong[cong]
  apply (rule_tac r'="K dc \<currency> dc" and xf'="liftxf errstate id (K ()) ret__unsigned_long_'"
        in ccorres_rel_imp[rotated])
   apply (case_tac x, simp_all)[1]
  apply (rule ccorres_guard_imp2)
   apply (simp add: handleEvent_def callKernel_C_body_if_def)
   apply (wpc, simp_all)[1]
       apply (wpc, simp_all add: handleSyscall_C_body_if_def syscall_from_H_def liftE_def
                                 ccorres_cond_univ_iff syscall_defs ccorres_cond_empty_iff)[1]
              \<comment> \<open>SysCall\<close>
              apply (simp add: handleCall_def)
              apply (ctac (no_vcg) add: handleInvocation_ccorres)
             \<comment> \<open>SysReplyRecv\<close>
             apply (simp add: bind_assoc)
             apply (rule ccorres_rhs_assoc)+
             apply (ctac (no_vcg) add: handleReply_ccorres)
              apply (ctac (no_vcg) add: handleRecv_ccorres)
               apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: return_def)
              apply wp[1]
             apply clarsimp
             apply wp
             apply (rule_tac Q="\<lambda>rv s. ct_in_state' simple' s \<and> sch_act_sane s \<and>
                                (\<forall>p. ksCurThread s \<notin> set (ksReadyQueues s p))"
                   in hoare_post_imp)
              apply (simp add: ct_in_state'_def)
             apply (wp handleReply_sane handleReply_ct_not_ksQ)
             \<comment> \<open>SysSend\<close>
            apply (simp add: handleSend_def)
            apply (ctac (no_vcg) add: handleInvocation_ccorres)
           \<comment> \<open>SysNBSend\<close>
           apply (simp add: handleSend_def)
           apply (ctac (no_vcg) add: handleInvocation_ccorres)
          \<comment> \<open>SysRecv\<close>
          apply (ctac (no_vcg) add: handleRecv_ccorres)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
          apply wp
         \<comment> \<open>SysReply\<close>
         apply (ctac (no_vcg) add: handleReply_ccorres)
          apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: return_def)
         apply wp
       \<comment> \<open>SysYield\<close>
       apply (ctac (no_vcg) add: handleYield_ccorres)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply wp
      \<comment> \<open>SysNBRecv\<close>
          apply (ctac (no_vcg) add: handleRecv_ccorres)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
          apply wp
      \<comment> \<open>UnknownSyscall\<close>
      apply (simp add: liftE_def bind_assoc handleUnknownSyscall_C_body_if_def)
      apply (rule ccorres_pre_getCurThread)
      apply (rule ccorres_symb_exec_r)
        apply (ctac (no_vcg) add: handleFault_ccorres)
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply wp
       apply (clarsimp, vcg)
      apply (clarsimp, rule conseqPre, vcg, clarsimp)
     \<comment> \<open>UserLevelFault\<close>
     apply (simp add: liftE_def bind_assoc handleUserLevelFault_C_body_if_def)
     apply (rule ccorres_pre_getCurThread)
     apply (rule ccorres_symb_exec_r)
       apply (ctac (no_vcg) add: handleFault_ccorres)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply wp
      apply (clarsimp, vcg)
     apply (clarsimp, rule conseqPre, vcg, clarsimp)
    \<comment> \<open>Interrupt\<close>
    apply (ctac add: handleInterrupt_ccorres[unfolded handleEvent_def, simplified])
   \<comment> \<open>VMFaultEvent\<close>
   apply (simp add: liftE_def bind_assoc handleVMFaultEvent_C_body_if_def)
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
         apply (rule_tac P="\<lambda>s. thread = ksCurThread s" in ccorres_cross_over_guard)
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
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply (auto simp: ct_in_state'_def ct_not_ksQ isReply_def is_cap_fault_def
                    cfault_rel_def seL4_Fault_UnknownSyscall_lift seL4_Fault_UserException_lift
              elim: pred_tcb'_weakenE st_tcb_ex_cap''
              dest: st_tcb_at_idle_thread' rf_sr_ksCurThread)
  \<comment> \<open>HypervisorEvent\<close>
  apply (simp add: liftE_def bind_assoc)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (case_tac x6; simp add: handleHypervisorFault_def)
      apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def)
     apply wp+
  apply clarsimp
  done

lemma kernelEntry_corres_C:
  "corres_underlying rf_sr False False (prod_lift (\<lambda>r r'. (r = Inr ()) = (r' = Inr ()))) (
                     all_invs' e) \<top>
                     (kernelEntry_if e tc) (kernelEntry_C_if fp e tc)"
  using corres_nofail[OF kernel_entry_if_corres[of e tc], simplified]
  apply (simp add: kernelEntry_if_def kernelEntry_C_if_def)
  apply (simp only: bind_assoc[symmetric])
  apply (rule corres_stateAssert_no_fail)
   apply (erule no_fail_pre)
   apply (clarsimp simp: all_invs'_def)
   apply (rule exI, rule conjI, assumption)
   apply clarsimp
  apply (simp only: bind_assoc)
  apply (simp add: getCurThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated [where P=\<top> and P'=\<top> and r'="\<lambda>t t'. t' = tcb_ptr_to_ctcb_ptr t"])
       prefer 2
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
      apply (rule corres_split_deprecated)
         prefer 2
         apply (subst archTcbUpdate_aux2[symmetric])
         apply (rule setArchTCB_C_corres, simp, rule ccontext_rel_to_C)
         apply simp
        apply (rule corres_split_deprecated[OF _ ccorres_corres_u_xf, simplified bind_assoc])
            prefer 3
            apply (rule corres_nofail)
             apply (rule handleEvent_corres)
            apply simp
           prefer 2
           apply (rule_tac Q'="UNIV" in ccorres_guard_imp)
             apply (rule handleEvent_ccorres)
            apply (clarsimp simp: all_invs'_def)
           apply simp
          apply (rule_tac P="\<top>" and P'="\<top>" in corres_inst)
          apply (clarsimp simp: prod_lift_def split: if_split)
         apply simp
         apply wp+
       apply (rule hoare_strengthen_post)
        apply (subst archTcbUpdate_aux2[symmetric])
        apply (rule threadSet_all_invs_triv'[where e=e])
       apply (clarsimp simp: all_invs'_def)
       apply (rule exI, (rule conjI, assumption)+)
       subgoal by force
      apply simp
      apply (rule hoare_post_taut[where P=\<top>])
     apply wp+
   apply (clarsimp simp: all_invs'_def invs'_def cur_tcb'_def)
   apply fastforce
  done

end

context state_rel
begin

definition
  "ptable_rights_s'' s \<equiv> ptable_rights (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_lift_s'' s \<equiv> ptable_lift (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_attrs_s'' s \<equiv> ptable_attrs (cur_thread (cstate_to_A s)) (cstate_to_A s)"

definition
  "ptable_xn_s'' s \<equiv> \<lambda>addr. XNever \<in> ptable_attrs_s'' s addr"

definition
  doMachineOp_C :: "(machine_state, 'a) nondet_monad \<Rightarrow> (cstate, 'a) nondet_monad"
where
 "doMachineOp_C mop \<equiv>
  do
    ms \<leftarrow> gets (\<lambda>s. phantom_machine_state_' (globals s));
    (r, ms') \<leftarrow> select_f (mop ms);
    modify (\<lambda>s. s \<lparr>globals := globals s \<lparr> phantom_machine_state_' := ms' \<rparr>\<rparr>);
    return r
  od"

definition doUserOp_C_if
  :: "user_transition_if \<Rightarrow> user_context \<Rightarrow> (cstate, (event option \<times> user_context)) nondet_monad"
   where
  "doUserOp_C_if uop tc \<equiv>
   do
      pr \<leftarrow> gets ptable_rights_s'';
      pxn \<leftarrow> gets (\<lambda>s x. pr x \<noteq> {} \<and> ptable_xn_s'' s x);
      pl \<leftarrow> gets (\<lambda>s. restrict_map (ptable_lift_s'' s) {x. pr x \<noteq> {}});
      allow_read \<leftarrow> return {y. \<exists>x. pl x = Some y \<and> AllowRead \<in> pr x};
      allow_write \<leftarrow> return {y. \<exists>x. pl x = Some y \<and> AllowWrite \<in> pr x};
      t \<leftarrow> gets (\<lambda>s. cur_thread (cstate_to_A s));
      um \<leftarrow> gets (\<lambda>s. user_mem_C (globals s) \<circ> ptrFromPAddr);
      dm \<leftarrow> gets (\<lambda>s. device_mem_C (globals s) \<circ> ptrFromPAddr);
      ds \<leftarrow> gets (\<lambda>s. device_state (phantom_machine_state_' (globals s)));
      assert (dom (um \<circ> addrFromPPtr) \<subseteq> - dom ds);
      assert (dom (dm \<circ> addrFromPPtr) \<subseteq> dom ds);
      es \<leftarrow> doMachineOp_C getExMonitor;
      u \<leftarrow> return (uop t pl pr pxn (tc, um |` allow_read, (ds \<circ> ptrFromPAddr)|` allow_read ,es));
      assert (u \<noteq> {});
      (e,(tc',um',ds',es')) \<leftarrow> select u;
      setUserMem_C ((um' |` allow_write \<circ> addrFromPPtr) |` (- dom ds));
      setDeviceState_C ((ds' |` allow_write \<circ> addrFromPPtr) |` dom ds);
      doMachineOp_C (setExMonitor es');
      return (e,tc')
   od"


definition
  do_user_op_C_if
  where
  "do_user_op_C_if uop \<equiv> {(s,e,(tc,s'))| s e tc s'. ((e,tc),s') \<in> fst (split (doUserOp_C_if uop) s)}"

end

context kernel_m begin



lemma corres_underlying_split5:
    "(\<And>a b c d e. corres_underlying srel nf nf' rrel (Q a b c d e) (Q' a b c d e) (f a b c d e) (f' a b c d e)) \<Longrightarrow>
     corres_underlying srel nf nf' rrel (case x of (a,b,c,d,e) \<Rightarrow> Q a b c d e) (case x of (a,b,c,d,e) \<Rightarrow> Q' a b c d e) (case x of (a,b,c,d,e) \<Rightarrow> f a b c d e) (case x of (a,b,c,d,e) \<Rightarrow> f' a b c d e)"
  apply (case_tac x)
  apply simp
  done

lemma corres_select_f':
  "\<lbrakk> \<And>s s'. P s \<Longrightarrow> P' s' \<Longrightarrow> \<forall>s' \<in> fst S'. \<exists>s \<in> fst S. rvr s s'; nf' \<Longrightarrow> \<not> snd S' \<rbrakk>
      \<Longrightarrow> corres_underlying sr nf nf' rvr P P' (select_f S) (select_f S')"
  by (clarsimp simp: select_f_def corres_underlying_def)

lemma corres_dmo_getExMonitor_C:
  "corres_underlying rf_sr nf nf' (=) \<top> \<top> (doMachineOp getExMonitor) (doMachineOp_C getExMonitor)"
  apply (clarsimp simp: doMachineOp_def doMachineOp_C_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>ms ms'. exclusive_state ms = exclusive_state ms' \<and> machine_state_rest ms = machine_state_rest ms'
      \<and> irq_masks ms = irq_masks ms' \<and> equiv_irq_state ms ms' \<and> device_state ms = device_state ms'" and P="\<top>" and P'="\<top>" in corres_split_deprecated)
       apply (rule_tac r'="\<lambda>(r, ms) (r', ms'). r = r' \<and> ms = rv \<and> ms' = rv'" in corres_split_deprecated)
          apply (clarsimp simp: split_def)
          apply (rule_tac r'=dc and P="\<lambda>s. underlying_memory (snd ((aa, bb), ba)) = underlying_memory (ksMachineState s)"
                 and P'="\<lambda>s. underlying_memory (snd ((aa, bb), bc)) = underlying_memory (phantom_machine_state_' (globals s))" in corres_split_deprecated)
             apply clarsimp
            apply (rule corres_modify)
            apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def cmachine_state_relation_def Let_def)
           apply (wp hoare_TrueI)+
         apply (rule corres_select_f')
          apply (clarsimp simp: getExMonitor_def machine_rest_lift_def NonDetMonad.bind_def gets_def get_def return_def modify_def put_def select_f_def)
         apply (clarsimp simp: getExMonitor_no_fail[simplified no_fail_def])
        apply (wp hoare_TrueI)+
      apply (clarsimp simp: rf_sr_def cstate_relation_def cmachine_state_relation_def Let_def)
     apply (wp hoare_TrueI)+
  apply (rule TrueI conjI | clarsimp simp: getExMonitor_def machine_rest_lift_def NonDetMonad.bind_def gets_def get_def return_def modify_def put_def select_f_def)+
  done

lemma corres_dmo_setExMonitor_C:
  "corres_underlying rf_sr nf nf' dc \<top> \<top> (doMachineOp (setExMonitor es)) (doMachineOp_C (setExMonitor es))"
  apply (clarsimp simp: doMachineOp_def doMachineOp_C_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>ms ms'. exclusive_state ms = exclusive_state ms' \<and> machine_state_rest ms = machine_state_rest ms'
      \<and> irq_masks ms = irq_masks ms' \<and> equiv_irq_state ms ms' \<and> device_state ms = device_state ms'" and P="\<top>" and P'="\<top>" in corres_split_deprecated)
       apply (rule_tac r'="\<lambda>(r, ms) (r', ms'). ms = rv\<lparr>exclusive_state := es\<rparr> \<and> ms' = rv'\<lparr>exclusive_state := es\<rparr>" in corres_split_deprecated)
          apply (simp add: split_def)
          apply (rule_tac P="\<lambda>s. underlying_memory (snd rva) = underlying_memory (ksMachineState s)"
                 and P'="\<lambda>s. underlying_memory (snd rv'a) = underlying_memory (phantom_machine_state_' (globals s))" in corres_modify)
          apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def cmachine_state_relation_def Let_def)
         apply (rule corres_select_f')
          apply (clarsimp simp: setExMonitor_def machine_rest_lift_def NonDetMonad.bind_def gets_def get_def return_def modify_def put_def select_f_def)
         apply (clarsimp simp: setExMonitor_no_fail[simplified no_fail_def])
        apply (wp hoare_TrueI)+
      apply (clarsimp simp: rf_sr_def cstate_relation_def cmachine_state_relation_def Let_def)
     apply (wp hoare_TrueI)+
  apply (rule TrueI conjI | clarsimp simp: setExMonitor_def machine_rest_lift_def NonDetMonad.bind_def gets_def get_def return_def modify_def put_def select_f_def)+
  done

lemma dmo_getExMonitor_C_wp[wp]:
  "\<lbrace>\<lambda>s. P (exclusive_state (phantom_machine_state_' (globals s))) s\<rbrace>
   doMachineOp_C getExMonitor \<lbrace>P\<rbrace>"
  apply(simp add: doMachineOp_C_def)
  apply(wp modify_wp | wpc)+
  apply clarsimp
  apply(erule use_valid)
   apply wp
  apply simp
  done

lemma cur_thread_of_absKState[simp]:
   "cur_thread (absKState s) = (ksCurThread s)"
   by (clarsimp simp: cstate_relation_def Let_def absKState_def cstate_to_H_def)

lemma absKState_crelation:
  "\<lbrakk>cstate_relation s (globals s'); invs' s\<rbrakk>\<Longrightarrow>  cstate_to_A s' = absKState s"
  apply (clarsimp simp add: cstate_to_H_correct invs'_def cstate_to_A_def)
  apply (clarsimp simp: absKState_def absExst_def observable_memory_def)
  apply (case_tac s)
  apply clarsimp
  apply (case_tac ksMachineState)
  apply clarsimp
  apply (rule ext)
  by (clarsimp simp: option_to_0_def user_mem'_def pointerInUserData_def ko_wp_at'_def
                     obj_at'_def typ_at'_def ps_clear_def
              split: if_splits)

lemma do_user_op_if_C_corres:
   "corres_underlying rf_sr False False (=)
   (invs' and ex_abs einvs and (\<lambda>_. uop_nonempty f)) \<top>
   (doUserOp_if f tc) (doUserOp_C_if f tc)"
  apply (rule corres_gen_asm)
  apply (simp add: doUserOp_if_def doUserOp_C_if_def uop_nonempty_def del: split_paired_All)
  apply (rule corres_gets_same)
    apply (clarsimp simp: absKState_crelation ptable_rights_s'_def ptable_rights_s''_def
           rf_sr_def  cstate_relation_def Let_def cstate_to_H_correct)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: ptable_xn_s'_def ptable_xn_s''_def ptable_attrs_s_def
                          absKState_crelation ptable_attrs_s'_def ptable_attrs_s''_def  rf_sr_def)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: absKState_crelation curthread_relation ptable_lift_s'_def ptable_lift_s''_def
                         ptable_lift_s_def rf_sr_def)
   apply simp
  apply (simp add: getCurThread_def)
  apply (rule corres_gets_same)
    apply (simp add: absKState_crelation rf_sr_def)
   apply simp
  apply (rule corres_gets_same)
    apply (rule fun_cong[where x=ptrFromPAddr])
    apply (rule_tac f=comp in arg_cong)
    apply (rule user_mem_C_relation[symmetric])
    apply (simp add: rf_sr_def cstate_relation_def Let_def
                               cpspace_relation_def)
    apply fastforce
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                          cpspace_relation_def)
    apply (drule device_mem_C_relation[symmetric])
     apply fastforce
    apply (simp add: comp_def)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: cstate_relation_def rf_sr_def
                          Let_def cmachine_state_relation_def)
   apply simp
  apply (rule corres_guard_imp)
    apply (rule_tac P=\<top> and P'=\<top> and r'="(=)" in corres_split_deprecated)
       prefer 2
       apply (clarsimp simp add: corres_underlying_def fail_def
                                 assert_def return_def
                          split: if_splits)
      apply simp
      apply (rule_tac P=\<top> and P'=\<top> and r'="(=)" in corres_split_deprecated)
         prefer 2
         apply (clarsimp simp add: corres_underlying_def fail_def
                                   assert_def return_def
                            split: if_splits)
        apply simp
        apply (rule corres_split_deprecated[OF _ corres_dmo_getExMonitor_C])
          apply clarsimp
          apply (rule_tac r'="(=)" in corres_split_deprecated[OF _ corres_select])
              prefer 2
              apply clarsimp
             apply simp
             apply (rule corres_underlying_split5)
             apply (rule corres_split_deprecated[OF _ user_memory_update_corres_C])
               apply (rule corres_split_deprecated[OF _ device_update_corres_C])
                 apply (rule corres_split_deprecated[OF _ corres_dmo_setExMonitor_C,
                               where R="\<top>\<top>" and R'="\<top>\<top>"])
                        apply (wp select_wp | simp)+
    apply (clarsimp simp:  ex_abs_def restrict_map_def invs_pspace_aligned'
                           invs_pspace_distinct' ptable_lift_s'_def ptable_rights_s'_def
                   split: if_splits)
    apply (drule ptable_rights_imp_UserData[rotated -1])
     apply ((fastforce | intro conjI)+)[4]
    apply (clarsimp simp: user_mem'_def device_mem'_def dom_def split: if_splits)
    apply fastforce
   apply (clarsimp simp add: invs'_def valid_state'_def valid_pspace'_def ex_abs_def)
   done

definition
  checkActiveIRQ_C_if :: "user_context \<Rightarrow> (cstate, irq option \<times> user_context) nondet_monad"
  where
  "checkActiveIRQ_C_if tc \<equiv>
   do
      getActiveIRQ_C;
      irq \<leftarrow>  gets ret__unsigned_long_';
      return (if irq = 0xFFFF then None else Some (ucast irq), tc)
   od"

definition
  check_active_irq_C_if
  where
  "check_active_irq_C_if \<equiv> {((tc, s), irq, (tc', s')). ((irq, tc'), s') \<in> fst (checkActiveIRQ_C_if tc s)}"

lemma check_active_irq_corres_C:
  "corres_underlying rf_sr False False (=) \<top> \<top>
                     (checkActiveIRQ_if tc) (checkActiveIRQ_C_if tc)"
  apply (simp add: checkActiveIRQ_if_def checkActiveIRQ_C_if_def)
  apply (simp add: getActiveIRQ_C_def)
  apply (subst bind_assoc[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split_deprecated[where r'="\<lambda>a c. case a of None \<Rightarrow> c = 0xFFFF | Some x \<Rightarrow> c = ucast x \<and> c \<noteq> 0xFFFF", OF _ ccorres_corres_u_xf])
        apply (clarsimp split: if_split option.splits)
       apply (rule ccorres_guard_imp)
         apply (rule ccorres_rel_imp, rule ccorres_guard_imp)
            apply (rule getActiveIRQ_ccorres)
           apply simp+
         apply (case_tac x; simp add: ucast_helper_simps_32)
        apply simp+
      apply (rule no_fail_dmo')
      apply (rule getActiveIRQ_nf)
     apply (rule hoare_post_taut[where P=\<top>])+
   apply simp+
   apply fastforce
  done


definition
  handlePreemption_C_if :: "user_context \<Rightarrow> (cstate,user_context) nondet_monad" where
  "handlePreemption_C_if tc \<equiv>
       do (exec_C \<Gamma> handleInterruptEntry_C_body_if); return tc od"

lemma handlePreemption_if_def2:
  "handlePreemption_if tc = do
     r \<leftarrow> handleEvent Interrupt;
          stateAssert (\<lambda>s. (ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread) \<and>
                            valid_domain_list' s) [];
          return tc
   od"
  apply (clarsimp simp add: handlePreemption_if_def handleEvent_def liftE_def
                   bind_assoc)
  apply (rule bind_eqI)
  apply (rule ext)
  apply (clarsimp split: option.splits)
  done

lemma handleInterrupt_no_fail: "no_fail (ex_abs (einvs) and invs' and (\<lambda>s. intStateIRQTable (ksInterruptState s) a \<noteq> irqstate.IRQInactive)) (handleInterrupt a)"
  apply (rule no_fail_pre)
  apply (rule corres_nofail)
    apply (rule handleInterrupt_corres)
   apply (erule FalseE)
  apply (fastforce simp: ex_abs_def)
  done

lemma handleEvent_Interrupt_no_fail: "no_fail (invs' and ex_abs einvs) (handleEvent Interrupt)"
  apply (simp add: handleEvent_def)
  apply (rule no_fail_pre)
   apply wp
    apply (rule handleInterrupt_no_fail)
   apply (simp add: crunch_simps)
   apply (rule_tac Q="\<lambda>r s. ex_abs (einvs) s \<and>
                      invs' s \<and> (\<forall>irq. r = Some irq \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)" in hoare_strengthen_post)
    apply (rule hoare_vcg_conj_lift)
     apply (rule corres_ex_abs_lift)
      apply (rule dmo_getActiveIRQ_corres)
     apply wp
     apply simp
    apply wp
     apply simp
    apply (rule doMachineOp_getActiveIRQ_IRQ_active)
   apply clarsimp
  apply (clarsimp simp: invs'_def valid_state'_def)
  done

lemma handle_preemption_corres_C:
  "corres_underlying rf_sr False False (=)
                     (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
                      valid_domain_list' and (\<lambda>s. 0 < ksDomainTime s) and
                      ex_abs einvs) \<top>
                     (handlePreemption_if tc) (handlePreemption_C_if tc)"
  apply (simp add: handlePreemption_if_def2 handlePreemption_C_if_def)
  apply (rule corres_stateAssert_no_fail)
   using corres_nofail[OF handle_preemption_if_corres[of tc], simplified]
   apply (simp add: handlePreemption_if_def2)
   apply (erule no_fail_pre)
   apply (clarsimp simp: ex_abs_underlying_def)
   apply (rule exI, rule conjI, assumption)
   apply (clarsimp simp: domain_time_rel_eq domain_list_rel_eq)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="dc" in corres_split_deprecated)
       apply simp
      apply (rule ccorres_corres_u)
       apply (rule ccorres_guard_imp)
         apply (rule ccorres_rel_imp)
          apply (rule handleInterrupt_ccorres)
         apply simp
        prefer 3
        apply (rule handleEvent_Interrupt_no_fail)
       apply clarsimp
      apply simp
     apply (rule hoare_post_taut[where P=\<top>])+
   apply (fastforce simp: ex_abs_def schedaction_related)+
  done


definition
  handle_preemption_C_if
  where
  "handle_preemption_C_if \<equiv>
      {(s, u, s'). s' \<in> fst (split handlePreemption_C_if s)}"

definition
  schedule_C_if' :: "user_context \<Rightarrow> (cstate,user_context) nondet_monad" where
  "schedule_C_if' tc \<equiv>
    do exec_C \<Gamma> (Call schedule_'proc); exec_C \<Gamma> (Call activateThread_'proc); return tc od"


lemma ccorres_corres_u':
  "\<lbrakk>ccorres dc xfdc P' Q' [] H C; no_fail P'' H;
    (\<And>s. P s \<Longrightarrow> P' s \<and> P'' s);
    (Collect Q) \<subseteq> Q'\<rbrakk> \<Longrightarrow>
   corres_underlying rf_sr nf nf' dc P Q H (exec_C \<Gamma> C)"
  apply (rule ccorres_corres_u)
   apply (rule ccorres_guard_imp)
     apply assumption
    apply simp
   apply blast
  apply (rule no_fail_pre,simp+)
  done


lemma schedule_if_corres_C:
  "corres_underlying rf_sr False False (=)
                     (invs' and ex_abs einvs and valid_domain_list' and
                      (\<lambda>s. ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread)) \<top>
                     (schedule'_if tc) (schedule_C_if' tc)"
  apply (simp add: schedule'_if_def schedule_C_if'_def)
  apply (subst bind_assoc[symmetric], rule corres_stateAssert_no_fail)
   using corres_nofail[OF schedule_if_corres[of tc], simplified]
   apply (simp add: schedule'_if_def bind_assoc)
   apply (erule no_fail_pre)
   apply (clarsimp simp: ex_abs_def)
   apply (rule exI, rule conjI, assumption)
   apply (clarsimp simp: domain_time_rel_eq domain_list_rel_eq)
   apply (clarsimp simp: state_relation_def)
  apply (simp only: bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="dc" in corres_split_deprecated)
       apply simp
       apply (rule_tac r'="dc" in corres_split_deprecated)
          apply simp
         apply (rule ccorres_corres_u')
            apply (rule activateThread_ccorres)
           apply (rule corres_nofail)
            apply (rule activateThread_corres)
           apply (erule FalseE)
          apply simp
         apply simp
        apply (rule hoare_post_taut[where P=\<top>])+
      apply (rule ccorres_corres_u')
         apply (rule schedule_ccorres)
        apply (rule corres_nofail)
         apply (rule schedule_corres)
        apply (erule FalseE)
       apply simp
      apply simp
     apply (rule_tac Q="\<lambda>r. ct_in_state' activatable' and invs' and ex_abs(invs and ct_in_state activatable)" in hoare_strengthen_post)
      apply (wp schedule_invs' corres_ex_abs_lift)
       apply (rule schedule_corres)
      apply wp
     apply (clarsimp simp: ex_abs_def invs'_def valid_state'_def valid_pspace'_def)
     apply fastforce
    apply simp
    apply (rule hoare_post_taut[where P=\<top>])
   apply (auto simp: ex_abs_def)
  done

definition
  schedule_C_if
  where
  "schedule_C_if \<equiv>
      {(s, (e :: unit), s'). s' \<in> fst (split schedule_C_if' s)}"

definition
 kernelExit_C_if :: "user_context \<Rightarrow> (cstate,user_context) nondet_monad" where
  "kernelExit_C_if tc \<equiv>
   do t \<leftarrow> gets (ksCurThread_' \<circ> globals);
      gets $ getContext_C t
   od"

lemma corres_underlying_nf_imp2:
  "corres_underlying rf_sr nf True a b c d e \<Longrightarrow> corres_underlying rf_sr nf nf' a b c d e"
  by (auto simp: corres_underlying_def)

lemma kernel_exit_corres_C:
  "corres_underlying rf_sr False nf (=) (invs') \<top>
                     (kernelExit_if tc) (kernelExit_C_if tc)"
  apply (rule corres_underlying_nf_imp2)
  apply (simp add: kernelExit_if_def kernelExit_C_if_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>rv rv'. rv' = tcb_ptr_to_ctcb_ptr rv" in corres_split_deprecated)
       apply simp
       apply (rule getContext_corres)
       apply simp
      apply (rule_tac P="\<top>" and P'="\<top>" in corres_inst)
      apply (clarsimp simp: getCurThread_def rf_sr_def cstate_relation_def Let_def)
     apply wp+
   apply clarsimp+
  done


definition
  kernel_exit_C_if
  where
  "kernel_exit_C_if \<equiv>
      {(s, m, s'). s' \<in> fst (split kernelExit_C_if s) \<and>
                   m = (if ct_running_C (snd s') then InUserMode else InIdleMode)}"

end

lemma preserves_trivial: "preserves mode mode' UNIV f"
  apply (simp add: preserves_def)
  done

lemma preserves'_trivial: "preserves' mode UNIV f"
  apply (simp add: preserves'_def)
  done

context kernel_m begin


definition ADT_C_if where
"ADT_C_if fp uop \<equiv> \<lparr>Init = \<lambda>s. ({user_context_of s} \<times> {s'. cstate_to_A s' = (internal_state_if s)}) \<times> {sys_mode_of s} \<inter> {s''. \<exists>s'. ((internal_state_if s'),(internal_state_if s'')) \<in> rf_sr \<and> s' \<in> full_invs_if' \<and> sys_mode_of s = sys_mode_of s'},
                  Fin = \<lambda>((uc,s),m). ((uc, cstate_to_A s),m),
                  Step = (\<lambda>(u :: unit). global_automaton_if
                              check_active_irq_C_if (do_user_op_C_if uop)
                              (kernel_call_C_if fp) handle_preemption_C_if
                              schedule_C_if kernel_exit_C_if)\<rparr>"

lemma full_invs_all_invs[simp]:
  "((tc,s),KernelEntry e) \<in> full_invs_if' \<Longrightarrow> all_invs' e s"
  apply (clarsimp simp: full_invs_if'_def all_invs'_def ex_abs_def)
  apply (rule_tac x=sa in exI)
  by (auto simp: ct_running_related ct_idle_related schedaction_related
                 domain_time_rel_eq domain_list_rel_eq)

lemma obs_cpspace_user_data_relation:
  "\<lbrakk>pspace_aligned' bd;pspace_distinct' bd;
    cpspace_user_data_relation (ksPSpace bd) (underlying_memory (ksMachineState bd)) hgs\<rbrakk>
   \<Longrightarrow> cpspace_user_data_relation (ksPSpace bd) (underlying_memory (observable_memory (ksMachineState bd) (user_mem' bd))) hgs"
   apply (clarsimp simp: cmap_relation_def dom_heap_to_user_data)
   apply (drule bspec,fastforce)
   apply (clarsimp simp: cuser_user_data_relation_def observable_memory_def
                         heap_to_user_data_def map_comp_def Let_def
                  split: option.split_asm)
   apply (drule_tac x = off in spec)
   apply (subst option_to_0_user_mem')
   apply (subst map_option_byte_to_word_heap)
    apply (clarsimp simp: projectKO_opt_user_data pointerInUserData_def field_simps
                   split: kernel_object.split_asm option.split_asm)
    apply (frule(1) pspace_alignedD')
    apply (subst neg_mask_add_aligned)
      apply (simp add: objBits_simps)
     apply (simp add: word_less_nat_alt)
     apply (rule le_less_trans[OF unat_plus_gt])
     apply (subst add.commute)
     apply (subst unat_mult_simple)
      apply (simp add: word_bits_def)
      apply (rule less_le_trans[OF unat_lt2p])
      apply simp
     apply simp
    apply (rule nat_add_offset_less [where n = 2, simplified])
      apply simp
     apply (rule unat_lt2p)
    apply (simp add: pageBits_def objBits_simps)
   apply (frule(1) pspace_distinctD')
   apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def objBits_simps)
  apply simp
  done

lemma obs_cpspace_device_data_relation:
  "\<lbrakk>pspace_aligned' bd;pspace_distinct' bd;
    cpspace_device_data_relation (ksPSpace bd) (underlying_memory (ksMachineState bd)) hgs\<rbrakk>
   \<Longrightarrow> cpspace_device_data_relation (ksPSpace bd) (underlying_memory (observable_memory (ksMachineState bd) (user_mem' bd))) hgs"
   apply (clarsimp simp: cmap_relation_def dom_heap_to_device_data)
   apply (drule bspec,fastforce)
   apply (clarsimp simp: cuser_user_data_device_relation_def observable_memory_def
                         heap_to_user_data_def  map_comp_def Let_def
                  split: option.split_asm)
   done

lemma cstate_relation_observable_memory:
  "\<lbrakk>invs' bs;cstate_relation bs gs\<rbrakk>
  \<Longrightarrow> cstate_relation (bs\<lparr>ksMachineState := observable_memory (ksMachineState bs) (user_mem' bs)\<rparr>) gs"
  by (clarsimp simp: cstate_relation_def Let_def obs_cpspace_user_data_relation
                     obs_cpspace_device_data_relation cpspace_relation_def invs'_def
                     valid_state'_def valid_pspace'_def
                     cmachine_state_relation_def observable_memory_def)


lemma c_to_haskell:
  "uop_nonempty uop \<Longrightarrow>
   global_automata_refine checkActiveIRQ_H_if (doUserOp_H_if uop) kernelCall_H_if
     handlePreemption_H_if schedule'_H_if kernelExit_H_if full_invs_if' (ADT_H_if uop) UNIV
     check_active_irq_C_if (do_user_op_C_if uop) (kernel_call_C_if fp) handle_preemption_C_if schedule_C_if
     kernel_exit_C_if UNIV (ADT_C_if fp uop) (lift_snd_rel rf_sr) False"
  apply (simp add: global_automata_refine_def)
  apply (intro conjI)
    apply (rule haskell_invs)
   apply (unfold_locales)
                        apply (simp add: ADT_C_if_def)
                       apply (simp_all add: preserves_trivial preserves'_trivial)
          apply (clarsimp simp: lift_snd_rel_def ADT_C_if_def ADT_H_if_def absKState_crelation
                                rf_sr_def full_invs_if'_def)
          apply (clarsimp simp: rf_sr_def full_invs_if'_def ex_abs_def)
         apply (simp add: ADT_H_if_def ADT_C_if_def lift_fst_rel_def lift_snd_rel_def)
         apply safe
         apply (clarsimp simp: absKState_crelation  rf_sr_def full_invs_if'_def)
         apply (rule_tac x="((a,bd),ba)" in bexI)
          apply simp
         apply simp
         apply (frule cstate_to_H_correct[rotated],simp add: invs'_def)
         apply (case_tac ba,simp_all)
        apply (simp_all add: checkActiveIRQ_H_if_def check_active_irq_C_if_def
                             doUserOp_H_if_def do_user_op_C_if_def
                             kernelCall_H_if_def kernel_call_C_if_def
                             handlePreemption_H_if_def handle_preemption_C_if_def
                             schedule'_H_if_def schedule_C_if_def
                             kernelExit_H_if_def kernel_exit_C_if_def)
        apply (rule step_corres_lifts,rule corres_guard_imp[OF check_active_irq_corres_C]; fastforce simp: full_invs_if'_def)
       apply (rule step_corres_lifts,rule corres_guard_imp[OF check_active_irq_corres_C]; fastforce simp: full_invs_if'_def)
      apply (rule step_corres_lifts,rule corres_guard_imp[OF do_user_op_if_C_corres]; auto simp: full_invs_if'_def ex_abs_def)
     apply (rule step_corres_lifts)
      apply (rule corres_rel_imp)
       apply (rule corres_guard_imp[OF kernelEntry_corres_C],(clarsimp simp: prod_lift_def)+)
    apply (rule step_corres_lifts,rule corres_guard_imp[OF handle_preemption_corres_C]; auto simp add: full_invs_if'_def)
   apply (rule step_corres_lifts,rule corres_guard_imp[OF schedule_if_corres_C]; auto simp: full_invs_if'_def ex_abs_def)
  apply (rule_tac S="invs'" and S'="\<top>" in step_corres_lifts(5))
      apply (rule corres_guard_imp[OF kernel_exit_corres_C])
       apply (fastforce simp: full_invs_if'_def)
      apply simp+
    apply (simp add: ct_running'_C)
   apply wp+
  apply (clarsimp simp: full_invs_if'_def)
  apply (clarsimp)
  apply (drule use_valid[OF _ kernelEntry_if_no_preempt]; simp)
  done

(*fw_sim lemmas as theorems and refinement as corollaries with sim_imp_refines?*)
lemma infoflow_fw_sim_H: "uop_nonempty uop \<Longrightarrow> ADT_C_if fp uop \<sqsubseteq>\<^sub>F ADT_H_if uop"
  apply (erule global_automata_refine.fw_simulates[OF c_to_haskell])
  done

lemma infoflow_fw_sim_A: "uop_nonempty uop \<Longrightarrow> ADT_C_if fp uop \<sqsubseteq>\<^sub>F ADT_A_if uop"
  apply (rule fw_simulates_trans)
  apply (rule infoflow_fw_sim_H)
   apply simp+
  apply (erule global_automata_refine.fw_simulates[OF haskell_to_abs])
  done

theorem infoflow_refinement_H: "uop_nonempty uop \<Longrightarrow> ADT_C_if fp uop \<sqsubseteq> ADT_H_if uop"
  apply (erule sim_imp_refines[OF infoflow_fw_sim_H])
  done

theorem infoflow_refinement_A: "uop_nonempty uop \<Longrightarrow> ADT_C_if fp uop \<sqsubseteq> ADT_A_if uop"
  apply (erule sim_imp_refines[OF infoflow_fw_sim_A])
  done

end


end
