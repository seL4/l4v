(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory ADT_IF_Refine_C
imports    
    "ADT_IF_Refine" "../crefine/Refine_C"
begin


definition handleInterruptEntry_C_body_if (*:: "(globals myvars, int, l4c_errortype) com"*) where
"handleInterruptEntry_C_body_if \<equiv> (
      (\<acute>irq :== CALL getActiveIRQ();;
       (Guard SignedArithmetic \<lbrace>True\<rbrace>
         (IF (ucast \<acute>irq :: word32) \<noteq> (ucast ((ucast (-1 :: word8)) :: word32)) THEN
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
               IF s = Kernel_C.SysWait THEN
                 CALL handleWait(scast true) ;;
                 \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
               ELSE
                 IF s = Kernel_C.SysReply THEN
                   CALL handleReply() ;;
                   \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
                 ELSE
                   IF s = Kernel_C.SysReplyWait THEN
                     CALL handleReply();;
                     CALL handleWait(scast true);;
                     \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
                   ELSE
                     IF s = Kernel_C.SysYield THEN
                       CALL handleYield();;
                       \<acute>ret__unsigned_long :== scast EXCEPTION_NONE
                     ELSE
                       IF s = Kernel_C.SysPoll THEN
                         CALL handleWait(scast false);;
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
    (\<acute>current_fault :== CALL fault_unknown_syscall_new(w);;
      (CALL handleFault(\<acute>ksCurThread);;
         \<acute>ret__unsigned_long :== scast EXCEPTION_NONE))"

definition handleUserLevelFault_C_body_if
  where
  "handleUserLevelFault_C_body_if w1 w2 \<equiv>
    (\<acute>current_fault :== CALL fault_user_exception_new(w1,w2);;
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



context kernel_m begin

definition 
  "callKernel_C_body_if e \<equiv> case e of
    SyscallEvent n \<Rightarrow> (handleSyscall_C_body_if (ucast (syscall_from_H n)))
  | UnknownSyscall n \<Rightarrow>  (handleUnknownSyscall_C_body_if (of_nat n))
  | UserLevelFault w1 w2 \<Rightarrow> (handleUserLevelFault_C_body_if w1 w2)
  | Interrupt \<Rightarrow> (handleInterruptEntry_C_body_if)
  | VMFaultEvent t \<Rightarrow> (handleVMFaultEvent_C_body_if (vm_fault_type_from_H t))"


definition
  kernelEntry_C_if (*::
    "bool \<Rightarrow> event \<Rightarrow> user_context \<Rightarrow> (cstate, (bool \<times> user_context)) nondet_monad"*)
  where
  "kernelEntry_C_if (fp :: bool) e tc \<equiv> do
    t \<leftarrow> gets (ksCurThread_' o globals);
    setContext_C (to_user_context_C tc) t;
    exec_C \<Gamma> (callKernel_C_body_if e);
    ex \<leftarrow> gets ret__unsigned_long_';
    r \<leftarrow> return (if (ex = scast EXCEPTION_NONE) then Inr () else Inl ex);
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
  apply (rule ccorres_guard_imp2)
   apply (simp add: handleEvent_def minus_one_norm handleInterruptEntry_C_body_if_def)
   apply (clarsimp simp: liftE_def bind_assoc)
   apply (rule ccorres_rhs_assoc)
   apply (ctac (no_vcg) add: getActiveIRQ_ccorres)
    apply (rule ccorres_Guard_Seq)
    apply (rule_tac P="rv \<noteq> Some 0xFF" in ccorres_gen_asm)
    apply wpc
     apply (simp add: ccorres_cond_empty_iff)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply (simp add: ucast_not_helper ccorres_cond_univ_iff)
    apply (ctac (no_vcg) add: handleInterrupt_ccorres)
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wp
   apply (rule_tac Q="\<lambda>rv s. invs' s \<and> (\<forall>x. rv = Some x \<longrightarrow> x \<le> Platform.maxIRQ)
                                     \<and> rv \<noteq> Some 0xFF" in hoare_post_imp)
    apply (clarsimp simp: Kernel_C.maxIRQ_def Platform.maxIRQ_def)
   apply (wp getActiveIRQ_le_maxIRQ getActiveIRQ_neq_Some0xFF | simp)+
  apply (clarsimp simp: invs'_def valid_state'_def)
  done

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
  apply (rule_tac r'="K dc \<currency> dc" and xf'="liftxf errstate id (K ()) ret__unsigned_long_'"
        in ccorres_rel_imp[rotated])
   apply (case_tac x, simp_all)[1]
  apply (rule ccorres_guard_imp2)
   apply (simp add: handleEvent_def callKernel_C_body_if_def)
   apply (wpc, simp_all)[1]
       apply (wpc, simp_all add: handleSyscall_C_body_if_def syscall_from_H_def liftE_def
                                 ccorres_cond_univ_iff syscall_defs ccorres_cond_empty_iff)[1]
             -- "SysSend"
              apply (simp add: handleSend_def)
              apply (ctac (no_vcg) add: handleInvocation_ccorres)
            -- "SysNBSend"
            apply (simp add: handleSend_def)
            apply (ctac (no_vcg) add: handleInvocation_ccorres)
           -- "SysCall"
           apply (simp add: handleCall_def)
           apply (ctac (no_vcg) add: handleInvocation_ccorres)
          -- "SysWait"
          apply (ctac (no_vcg) add: handleWait_ccorres)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
          apply wp
         -- "SysReply"
         apply (ctac (no_vcg) add: handleReply_ccorres)
          apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: return_def)
         apply wp
        -- "SysReplyWait"
        apply (simp add: bind_assoc)
        apply (rule ccorres_rhs_assoc)+
        apply (ctac (no_vcg) add: handleReply_ccorres)
         apply (ctac (no_vcg) add: handleWait_ccorres)
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
       -- "SysYield"
       apply (ctac (no_vcg) add: handleYield_ccorres)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply wp
      -- "SysPoll"
          apply (ctac (no_vcg) add: handleWait_ccorres)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
          apply wp
      -- "UnknownSyscall"
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
     -- "UserLevelFault"
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
    -- "Interrupt"
    apply (ctac add: handleInterrupt_ccorres[unfolded handleEvent_def, simplified])
   -- "VMFaultEvent"
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
  apply (auto simp: ct_in_state'_def cfault_rel_def is_cap_fault_def ct_not_ksQ isReply_def
                    cfault_rel_def fault_unknown_syscall_lift fault_user_exception_lift
                    is_cap_fault_def
              elim: pred_tcb'_weakenE st_tcb_ex_cap''
              dest: st_tcb_at_idle_thread')
  done

lemma kernelEntry_corres_C:
  "corres_underlying rf_sr True (prod_lift (\<lambda>r r'. (r = Inr ()) = (r' = Inr ()))) (
               all_invs' e) \<top>
                     (kernelEntry_if e tc) (kernelEntry_C_if fp e tc)"
  apply (simp add: kernelEntry_if_def kernelEntry_C_if_def)
  apply (simp add: getCurThread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [where P=\<top> and P'=\<top> and r'="\<lambda>t t'. t' = tcb_ptr_to_ctcb_ptr t"])
       prefer 2
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)  
      apply (rule corres_split)
         prefer 2
         apply (rule setContext_C_corres, rule ccontext_rel_to_C)
         apply simp
        apply (rule corres_split[OF _ ccorres_corres_u_xf, simplified bind_assoc])
            prefer 3
            apply (rule corres_nofail)
            apply (rule he_corres)
           prefer 2
           apply (rule_tac Q'="UNIV" in ccorres_guard_imp)
             apply (rule handleEvent_ccorres)
            apply (clarsimp simp: all_invs'_def)
           apply simp
          apply (rule_tac P="\<top>" and P'="\<top>" in corres_inst)
          apply (clarsimp simp: prod_lift_def split: split_if)
         apply wp
       apply (rule hoare_strengthen_post)
        apply (rule threadSet_all_invs_triv'[where e=e])
       apply (clarsimp simp: all_invs'_def)
       apply force
      apply simp
      apply (rule hoare_post_taut[where P=\<top>])
     apply wp
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
      t \<leftarrow> gets (\<lambda>s. cur_thread (cstate_to_A s));
      um \<leftarrow> gets (\<lambda>s. restrict_map (user_mem_C (globals s) \<circ> ptrFromPAddr)
                             {y. EX x. pl x = Some y \<and> AllowRead \<in> pr x});
      es \<leftarrow> doMachineOp_C getExMonitor;
      u \<leftarrow> return (uop t pl pr pxn (tc, um, es));
      assert (u \<noteq> {});
      (e,(tc',um',es')) \<leftarrow> select u;
      setUserMem_C (
        (restrict_map um' {y. EX x. pl x = Some y \<and> AllowWrite : pr x} \<circ>
         addrFromPPtr));
      doMachineOp_C (setExMonitor es');
      return (e,tc')
   od"


definition
  do_user_op_C_if
  where
  "do_user_op_C_if uop \<equiv> {(s,e,(tc,s'))| s e tc s'. ((e,tc),s') \<in> fst (split (doUserOp_C_if uop) s)}"

end

context kernel_m begin



lemma corres_underlying_split4:
    "(\<And>a b c d. corres_underlying srel nf rrel (Q a b c d) (Q' a b c d) (f a b c d) (f' a b c d)) \<Longrightarrow>
     corres_underlying srel nf rrel (case x of (a,b,c,d) \<Rightarrow> Q a b c d) (case x of (a,b,c,d) \<Rightarrow> Q' a b c d) (case x of (a,b,c,d) \<Rightarrow> f a b c d) (case x of (a,b,c,d) \<Rightarrow> f' a b c d)"
  apply (case_tac x)
  apply simp
  done

lemma corres_select_f':
  "\<lbrakk> \<And>s s'. P s \<Longrightarrow> P' s' \<Longrightarrow> \<forall>s' \<in> fst S'. \<exists>s \<in> fst S. rvr s s'; nf \<Longrightarrow> \<not> snd S' \<rbrakk>
      \<Longrightarrow> corres_underlying sr nf rvr P P' (select_f S) (select_f S')"
  by (clarsimp simp: select_f_def corres_underlying_def)

lemma corres_dmo_getExMonitor_C:
  "corres_underlying rf_sr nf op = \<top> \<top> (doMachineOp getExMonitor) (doMachineOp_C getExMonitor)"
  apply (clarsimp simp: doMachineOp_def doMachineOp_C_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>ms ms'. exclusive_state ms = exclusive_state ms' \<and> machine_state_rest ms = machine_state_rest ms' \<and> irq_masks ms = irq_masks ms' \<and> equiv_irq_state ms ms'" and P="\<top>" and P'="\<top>" in corres_split)
       apply (rule_tac r'="\<lambda>(r, ms) (r', ms'). r = r' \<and> ms = rv \<and> ms' = rv'" in corres_split)
          apply (clarsimp simp: split_def)
          apply (rule_tac r'=dc and P="\<lambda>s. underlying_memory (snd ((aa, bb), ba)) = underlying_memory (ksMachineState s)"
                 and P'="\<lambda>s. underlying_memory (snd ((aa, bb), bc)) = underlying_memory (phantom_machine_state_' (globals s))" in corres_split)
             apply clarsimp
            apply (rule corres_modify)
            apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def cmachine_state_relation_def Let_def)
           apply (wp hoare_TrueI)
         apply (rule corres_select_f')
          apply (clarsimp simp: getExMonitor_def machine_rest_lift_def NonDetMonad.bind_def gets_def get_def return_def modify_def put_def select_f_def)
         apply (clarsimp simp: getExMonitor_no_fail[simplified no_fail_def])
        apply (wp hoare_TrueI)
      apply (clarsimp simp: corres_gets rf_sr_def cstate_relation_def cmachine_state_relation_def Let_def)
     apply (wp hoare_TrueI)
  apply (rule TrueI conjI | clarsimp simp: getExMonitor_def machine_rest_lift_def NonDetMonad.bind_def gets_def get_def return_def modify_def put_def select_f_def)+
  done

lemma corres_dmo_setExMonitor_C:
  "corres_underlying rf_sr nf dc \<top> \<top> (doMachineOp (setExMonitor es)) (doMachineOp_C (setExMonitor es))"
  apply (clarsimp simp: doMachineOp_def doMachineOp_C_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>ms ms'. exclusive_state ms = exclusive_state ms' \<and> machine_state_rest ms = machine_state_rest ms' \<and> irq_masks ms = irq_masks ms' \<and> equiv_irq_state ms ms'" and P="\<top>" and P'="\<top>" in corres_split)
       apply (rule_tac r'="\<lambda>(r, ms) (r', ms'). ms = rv\<lparr>exclusive_state := es\<rparr> \<and> ms' = rv'\<lparr>exclusive_state := es\<rparr>" in corres_split)
          apply (simp add: split_def)
          apply (rule_tac P="\<lambda>s. underlying_memory (snd rva) = underlying_memory (ksMachineState s)"
                 and P'="\<lambda>s. underlying_memory (snd rv'a) = underlying_memory (phantom_machine_state_' (globals s))" in corres_modify)
          apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def cmachine_state_relation_def Let_def)
         apply (rule corres_select_f')
          apply (clarsimp simp: setExMonitor_def machine_rest_lift_def NonDetMonad.bind_def gets_def get_def return_def modify_def put_def select_f_def)
         apply (clarsimp simp: setExMonitor_no_fail[simplified no_fail_def])
        apply (wp hoare_TrueI)
      apply (clarsimp simp: corres_gets rf_sr_def cstate_relation_def cmachine_state_relation_def Let_def)
     apply (wp hoare_TrueI)
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

lemma do_user_op_if_C_corres:
   "corres_underlying rf_sr True op = 
   (invs' and ex_abs einvs and (\<lambda>_. uop_nonempty f)) \<top>
   (doUserOp_if f tc) (doUserOp_C_if f tc)"
  apply (rule corres_gen_asm)
  apply (simp add: doUserOp_if_def doUserOp_C_if_def uop_nonempty_def del: split_paired_All)
  apply (thin_tac "P" for P)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="op=" and P'=\<top> and P="invs' and ex_abs (einvs)" in corres_split)
       prefer 2
       apply (clarsimp simp: ptable_rights_s'_def ptable_rights_s''_def cstate_to_A_def rf_sr_def)
       apply (subst cstate_to_H_correct, simp add: invs'_def,force+)+
       apply (simp only: ex_abs_def)
       apply (elim exE conjE)
       apply (clarsimp simp add: absKState_correct absArchState_correct)
       apply (clarsimp simp: absHeap_correct
                             invs_def valid_state_def valid_pspace_def state_relation_def)
      apply (rule_tac r'="op=" and P'=\<top> and P="invs' and ex_abs (einvs)" in corres_split)
         prefer 2
         apply (clarsimp simp: ptable_xn_s'_def ptable_xn_s''_def ptable_attrs_s_def
                               ptable_attrs_s'_def ptable_attrs_s''_def cstate_to_A_def rf_sr_def)
         apply (subst cstate_to_H_correct, simp add: invs'_def,force+)+
         apply (simp only: ex_abs_def)
         apply (elim exE conjE)
         apply (clarsimp simp add: absKState_correct absArchState_correct)
         apply (clarsimp simp: absHeap_correct
                               invs_def valid_state_def valid_pspace_def state_relation_def)
        apply (rule_tac r'="op=" and P'=\<top> and P="invs' and ex_abs (einvs)" in corres_split) 
           prefer 2
           apply (clarsimp simp: ptable_lift_s'_def ptable_lift_s''_def cstate_to_A_def rf_sr_def)
           apply (subst cstate_to_H_correct, simp add: invs'_def,force+)+
           apply (simp only: ex_abs_def)
           apply (elim exE conjE)
           apply (clarsimp simp add: absKState_correct absArchState_correct)
           apply (clarsimp simp: absHeap_correct
                                 invs_def valid_state_def valid_pspace_def state_relation_def)
          apply (rule_tac r'="op=" and P'=\<top> and P="invs' and ex_abs (einvs)" in corres_split) 
             prefer 2 
             apply (clarsimp simp add: getCurThread_def cstate_to_A_def cstate_to_H_def rf_sr_def
                    cstate_relation_def absKState_def Let_def)
       
            apply (rule_tac r'="op =" in corres_split)
               apply (rule corres_split[OF _ corres_dmo_getExMonitor_C])
                 apply clarsimp
                 apply (rule_tac r'="op =" in corres_split[OF _ corres_select])
                    apply simp
                    apply (rule corres_underlying_split4)
                    apply (rule_tac r'="\<top>\<top>" in corres_split)
                       apply (rule_tac r'=dc in corres_split)
                          apply simp
                         apply (rule corres_dmo_setExMonitor_C)
                        apply (rule hoare_post_taut[where P=\<top>])
                       apply (rule hoare_post_taut[where P=\<top>])
                      apply (rule user_memory_update_corres_C)
                     apply (wp hoare_post_taut[where P=\<top>])
                   apply clarsimp
                  apply (wp select_wp)[2]
                apply clarsimp
                apply (rule dmo_getExMonitor_wp')
               apply wp
              apply (rule_tac P="pspace_distinct'" and P'=\<top> in corres_inst)
              apply (clarsimp simp: rf_sr_def cstate_relation_def cpspace_relation_def 
                                    user_mem_C_relation Let_def)
             apply (wp | simp)+
  
   apply (clarsimp simp add: invs'_def valid_state'_def valid_pspace'_def ex_abs_def)
   apply (clarsimp simp: user_mem'_def ex_abs_def restrict_map_def invs_def
                         ptable_lift_s'_def
                  split: if_splits)
   apply (rule ptable_rights_imp_UserData [rotated])
      apply (clarsimp simp: valid_state'_def valid_pspace'_def invs'_def)
     apply assumption
    apply (fastforce simp: ptable_rights_s'_def)
   apply assumption
  apply (simp add: invs_def)
 apply simp
 done

definition 
  checkActiveIRQ_C_if :: "user_context \<Rightarrow> (cstate, irq option \<times> user_context) nondet_monad"
  where
  "checkActiveIRQ_C_if tc \<equiv>
   do 
      getActiveIRQ_C;
      irq \<leftarrow> gets ret__unsigned_long_';
      return (if irq = 255 then None else Some (ucast irq), tc)
   od"

definition 
  check_active_irq_C_if
  where
  "check_active_irq_C_if \<equiv> {((tc, s), irq, (tc', s')). ((irq, tc'), s') \<in> fst (checkActiveIRQ_C_if tc s)}"

lemma check_active_irq_corres_C:
  "corres_underlying rf_sr True (op =) \<top> \<top>
                     (checkActiveIRQ_if tc) (checkActiveIRQ_C_if tc)"
  apply (simp add: checkActiveIRQ_if_def checkActiveIRQ_C_if_def)
  apply (simp add: getActiveIRQ_C_def)
  apply (subst bind_assoc[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="\<lambda>a c. case a of None \<Rightarrow> c = 0xFF | Some x \<Rightarrow> c = ucast x \<and> c \<noteq> 0xFF", OF _ ccorres_corres_u_xf])
        apply (clarsimp split: split_if option.splits)
        apply (rule ucast_ucast_id[symmetric], simp)
       apply (rule ccorres_guard_imp)
         apply (rule getActiveIRQ_ccorres)
        apply simp+
      apply (rule no_fail_dmo')
      apply (rule getActiveIRQ_nf)
     apply (rule hoare_post_taut[where P=\<top>])+
   apply simp+
  done


definition
  handlePreemption_C_if :: "user_context \<Rightarrow> (cstate,user_context) nondet_monad" where
  "handlePreemption_C_if tc \<equiv> 
       do (exec_C \<Gamma> handleInterruptEntry_C_body_if); return tc od"

lemma handlePreemption_if_def2: "handlePreemption_if tc = do 
                                   r \<leftarrow> handleEvent Interrupt;
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
  apply (rule handle_interrupt_corres)
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
  "corres_underlying rf_sr True (op =) (invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and ex_abs einvs) \<top>
                     (handlePreemption_if tc) (handlePreemption_C_if tc)"
  apply (simp add: handlePreemption_if_def2 handlePreemption_C_if_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="dc" in corres_split)
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
   corres_underlying rf_sr nf dc P Q H (exec_C \<Gamma> C)"
  apply (rule ccorres_corres_u)
   apply (rule ccorres_guard_imp)
     apply assumption
    apply simp
   apply blast
  apply (rule no_fail_pre,simp+)
  done


lemma schedule_if_corres_C:
  "corres_underlying rf_sr True (op =) (invs' and ex_abs einvs) \<top>
                     (schedule'_if tc) (schedule_C_if' tc)"
  apply (simp add: schedule'_if_def schedule_C_if'_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="dc" in corres_split)
       apply simp
       apply (rule_tac r'="dc" in corres_split)
          apply simp
         apply (rule ccorres_corres_u')
            apply (rule activateThread_ccorres)
           apply (rule corres_nofail)
           apply (rule activate_corres)
          apply simp
         apply simp
        apply (rule hoare_post_taut[where P=\<top>])+
      apply (rule ccorres_corres_u')
         apply (rule schedule_ccorres)
        apply (rule corres_nofail)
        apply (rule schedule_corres)
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
   apply (fastforce simp: ex_abs_def)+
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

lemma kernel_exit_corres_C:
  "corres_underlying rf_sr True (op =) (invs') \<top>
                     (kernelExit_if tc) (kernelExit_C_if tc)"
  apply (simp add: kernelExit_if_def kernelExit_C_if_def)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="\<lambda>rv rv'. rv' = tcb_ptr_to_ctcb_ptr rv" in corres_split)
       apply simp
       apply (rule getContext_corres)
       apply simp
      apply (rule_tac P="\<top>" and P'="\<top>" in corres_inst)
      apply (clarsimp simp: getCurThread_def rf_sr_def cstate_relation_def Let_def)
     apply wp
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

lemma full_invs_all_invs[simp]: "((tc,s),KernelEntry e) \<in> full_invs_if' \<Longrightarrow> all_invs' e s"
  apply (clarsimp simp: full_invs_if'_def all_invs'_def ex_abs_def)
  apply (fastforce simp: ct_running_related schedaction_related)
  done

lemma c_to_haskell: "uop_nonempty uop \<Longrightarrow> global_automata_refine checkActiveIRQ_H_if (doUserOp_H_if uop) kernelCall_H_if
     handlePreemption_H_if schedule'_H_if kernelExit_H_if full_invs_if' (ADT_H_if uop) UNIV
     check_active_irq_C_if (do_user_op_C_if uop) (kernel_call_C_if fp) handle_preemption_C_if schedule_C_if
     kernel_exit_C_if UNIV (ADT_C_if fp uop) (lift_snd_rel rf_sr) False"
  apply (simp add: global_automata_refine_def)
  apply (intro conjI)
    apply (rule haskell_invs)
   apply (unfold_locales)
                        apply (simp add: ADT_C_if_def)
                        apply blast
                       apply (simp_all add: preserves_trivial preserves'_trivial)
          apply (clarsimp simp: lift_snd_rel_def ADT_C_if_def ADT_H_if_def cstate_to_A_def)
          apply (clarsimp simp: rf_sr_def full_invs_if'_def ex_abs_def)
          apply (frule(1) absKState_correct[rotated],simp)
          apply simp
          apply (frule cstate_to_H_correct[rotated],simp add: invs'_def)
          apply simp
         apply (simp add: ADT_H_if_def ADT_C_if_def lift_fst_rel_def lift_snd_rel_def)
         apply safe
         apply clarsimp
         apply (clarsimp simp: cstate_to_A_def)
         apply (rule_tac x="((a,cstate_to_H (globals bb)),ba)" in bexI)
          apply simp
          apply (clarsimp simp: rf_sr_def full_invs_if'_def)
          apply (frule cstate_to_H_correct[rotated],simp add: invs'_def)
          apply simp
         apply simp
         apply (clarsimp simp: rf_sr_def full_invs_if'_def)
         apply (frule cstate_to_H_correct[rotated],simp add: invs'_def)
         apply (case_tac ba,simp_all)
        apply (simp_all add: checkActiveIRQ_H_if_def check_active_irq_C_if_def
                             doUserOp_H_if_def do_user_op_C_if_def
                             kernelCall_H_if_def kernel_call_C_if_def
                             handlePreemption_H_if_def handle_preemption_C_if_def
                             schedule'_H_if_def schedule_C_if_def
                             kernelExit_H_if_def kernel_exit_C_if_def) 
        apply (rule step_corres_lifts,rule corres_guard_imp[OF check_active_irq_corres_C],(fastforce simp: full_invs_if'_def ex_abs_def)+)
       apply (rule step_corres_lifts,rule corres_guard_imp[OF check_active_irq_corres_C],(fastforce simp: full_invs_if'_def ex_abs_def)+)
      apply (rule step_corres_lifts,rule corres_guard_imp[OF do_user_op_if_C_corres],(fastforce simp: full_invs_if'_def ex_abs_def)+)
     apply (rule step_corres_lifts)
      apply (rule corres_rel_imp)
       apply (rule corres_guard_imp[OF kernelEntry_corres_C],(clarsimp simp: prod_lift_def)+)
    apply (rule step_corres_lifts,rule corres_guard_imp[OF handle_preemption_corres_C], (fastforce simp add: full_invs_if'_def)+)
   apply (rule step_corres_lifts,rule corres_guard_imp[OF schedule_if_corres_C],(fastforce simp: full_invs_if'_def ex_abs_def)+)
  apply (rule_tac S="invs'" and S'="\<top>" in step_corres_lifts(5))
      apply (rule corres_guard_imp[OF kernel_exit_corres_C])
       apply (fastforce simp: full_invs_if'_def ex_abs_def)
      apply simp+
    apply (simp add: ct_running'_C)
   apply wp
  apply (clarsimp simp: full_invs_if'_def)
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
