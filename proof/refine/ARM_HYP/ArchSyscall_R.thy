(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Refinement for handleEvent and syscalls - architecture-specific proofs *)

theory ArchSyscall_R
imports Syscall_R
begin

context Arch begin arch_global_naming

named_theorems Syscall_R_assms

lemma vcpuFlushIfCurrent_corres[corres]:
  "corres dc (pspace_aligned and pspace_distinct and valid_arch_state and tcb_at tptr)
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             (vcpu_flush_if_current tptr) (vcpuFlushIfCurrent tptr)"
  unfolding vcpu_flush_if_current_def vcpuFlushIfCurrent_def
  by (corres wp: arch_thread_get_wp archThreadGet_wp)

lemma prepareSetDomain_corres[Syscall_R_assms, corres]:
  "corres dc (pspace_aligned and pspace_distinct and valid_cur_fpu and valid_arch_state and tcb_at tptr)
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             (arch_prepare_set_domain tptr new_dom) (prepareSetDomain tptr new_dom)"
  unfolding prepareSetDomain_def arch_prepare_set_domain_def curDomain_def
  by corres

crunch prepareSetDomain
  for invs'[Syscall_R_assms, wp]: invs'
  and ksSchedulerAction[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and sch_act_simple[Syscall_R_assms, wp]: sch_act_simple
  and tcb_at'[Syscall_R_assms, wp]: "tcb_at' p"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  and ct_in_state'[Syscall_R_assms, wp]: "ct_in_state' P"
  (wp: sch_act_simple_lift ct_in_state_thread_state_lift' crunch_wps)

crunch postSetFlags, Arch.performIRQControl, Arch.invokeIRQHandler
  for typ_at'[Syscall_R_assms, wp]: "\<lambda>s. P (typ_at' T p s)"

lemma setThreadState_irq_control_inv_valid'[Syscall_R_assms, wp]:
  "setThreadState st t \<lbrace>irq_control_inv_valid' irqcontrol_invocation\<rbrace>"
  apply (case_tac irqcontrol_invocation; simp)
   apply (rename_tac archirq_inv)
   apply (case_tac archirq_inv; simp)
    apply (wpsimp simp: irq_issued'_def)+
  done

(* FIXME arch-split: consider moving to where other msgRegisters stuff goes... Tcb_R? Ipc_R? *)
lemma len_msg_registes_le_max_length[Syscall_R_assms]:
  "length msg_registers \<le> msg_max_length"
  by (simp add: msg_max_length_def msgRegisters_unfold)

lemma capRegister_cap_register[Syscall_R_assms]:
  "capRegister = cap_register"
  by (simp add: cap_register_def capRegister_def)

lemma dmo_addressTranslateS1_invs'[wp]:
  "doMachineOp (addressTranslateS1 addr) \<lbrace> invs' \<rbrace>"
  unfolding addressTranslateS1_def
  by (wpsimp wp: dmo_machine_op_lift_invs' dmo'_gets_wp simp: doMachineOp_bind)

lemma getHSR_invs'[wp]:
  "doMachineOp getHSR \<lbrace>invs'\<rbrace>"
  by (simp add: getHSR_def doMachineOp_def split_def select_f_returns | wp)+

lemma getFAR_invs'[wp]:
  "doMachineOp getFAR \<lbrace>invs'\<rbrace>"
  by (simp add: getFAR_def doMachineOp_def split_def select_f_returns | wp)+

lemma getHDFAR_invs'[wp]:
  "doMachineOp getHDFAR \<lbrace>invs'\<rbrace>"
  by (simp add: getHDFAR_def doMachineOp_def split_def select_f_returns | wp)+

lemma hv_invs'[Syscall_R_assms, wp]:
  "\<lbrace>invs' and tcb_at' t'\<rbrace> handleVMFault t' vptr \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (simp add: ARM_HYP_H.handleVMFault_def
             cong: vmfault_type.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpcw | simp)+
  done

crunch handleVMFault
  for nosch[Syscall_R_assms, wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma handleSpuriousIRQ_corres[Syscall_R_assms, corres]:
  "corres dc \<top> \<top> handle_spurious_irq handleSpuriousIRQ"
  unfolding handle_spurious_irq_def handleSpuriousIRQ_def
  by (corres corres: corres_machine_op)

lemma handleHypervisorFault_corres[Syscall_R_assms]:
  "corres dc (einvs and  st_tcb_at active thread and ex_nonz_cap_to thread)
             (invs' and sch_act_not thread
                    and st_tcb_at' simple' thread and ex_nonz_cap_to' thread)
          (handle_hypervisor_fault thread fault) (handleHypervisorFault thread fault)"
  apply (cases fault; clarsimp simp: handleHypervisorFault_def split del: if_split)
  apply (corres corres: handleFault_corres simp: valid_fault_def)
  done

lemma hvmf_invs_lift[Syscall_R_assms]:
  "(\<And>s m. P (s\<lparr>ksMachineState := ksMachineState s\<lparr>machine_state_rest := m\<rparr>\<rparr>) = P s) \<Longrightarrow>
   \<lbrace>P\<rbrace> handleVMFault t flt \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding handleVMFault_def
  by (wpsimp wp: dmo_machine_rest_lift asUser_inv dmo'_gets_wp
           simp: getHSR_def addressTranslateS1_def getFAR_def getHDFAR_def
                 doMachineOp_bind getRestartPC_def getRegister_def)

crunch handleVMFault
  for st_tcb_at'[Syscall_R_assms, wp]: "st_tcb_at' P t"
  and ex_nonz_cap_to'[Syscall_R_assms, wp]: "ex_nonz_cap_to' t"
  and norq[Syscall_R_assms, wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksit[Syscall_R_assms, wp]: "\<lambda>s. P (ksIdleThread s)"

crunch handleHypervisorFault
  for ksit[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: undefined_valid haskell_assert_inv)

lemma hh_invs'[Syscall_R_assms, wp]:
  "\<lbrace>invs' and sch_act_not p and st_tcb_at' simple' p and ex_nonz_cap_to' p and (\<lambda>s. p \<noteq> ksIdleThread s)\<rbrace>
   handleHypervisorFault p t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  supply if_split[split del]
  by (cases t; wpsimp simp: ARM_HYP_H.handleHypervisorFault_def)

crunch handleSpuriousIRQ
  for invs'[Syscall_R_assms, wp]: invs'
  (ignore: doMachineOp wp: dmo_invs'_simple)

lemma arch_performInvocation_inv[Syscall_R_assms]:
  "\<lbrace>\<top>\<rbrace> Arch.performInvocation invocation -, \<lbrace>P\<rbrace>"
  by (wpsimp simp: performARMMMUInvocation_def ARM_HYP_H.performInvocation_def)

lemma Arch_performIRQControl_inv_EE[Syscall_R_assms]:
  "\<lbrace>\<top>\<rbrace> Arch.performIRQControl irqc -, \<lbrace>P\<rbrace>"
  unfolding ARM_HYP_H.performIRQControl_def
  by wpsimp

(* FIXME arch-split: move to ArchInvariants_AI on this arch *)
lemmas pageBitsForSize_bounded = pbfs_less_wb'

end (* Arch *)

interpretation Syscall_R?: Syscall_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Syscall_R_assms)?)?)
qed

end
