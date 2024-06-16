(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSyscall_AC
imports
  Syscall_AC
begin

context Arch begin global_naming ARM_A

named_theorems Syscall_AC_assms

declare prepare_thread_delete_idle_thread[Syscall_AC_assms]
declare arch_finalise_cap_idle_thread[Syscall_AC_assms]
declare cap_move_idle_thread[Syscall_AC_assms]
declare cancel_badged_sends_idle_thread[Syscall_AC_assms]

lemma invs_irq_state_update[Syscall_AC_assms, simp]:
  "invs (s\<lparr>machine_state := irq_state_update f sa\<rparr>) = invs (s\<lparr>machine_state := sa\<rparr>)"
  apply (rule iffI)
   apply (subst invs_irq_state_independent[symmetric])
   apply (subst ARM.fold_congs(2); fastforce)
  apply (subst (asm) invs_irq_state_independent[symmetric])
  apply (subst ARM.fold_congs(2); fastforce)
  done

crunches prepare_thread_delete, arch_finalise_cap
  for cur_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)

crunches set_original
  for idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

lemma cap_move_cur_thread[Syscall_AC_assms, wp]:
  "cap_move new_cap src_slot dest_slot \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
  unfolding cap_move_def
  by (wpsimp wp: dxo_wp_weak)

lemma cancel_badged_sends_cur_thread[Syscall_AC_assms, wp]:
  "cancel_badged_sends epptr badge \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
  unfolding cancel_badged_sends_def
  by (wpsimp wp: dxo_wp_weak filterM_preserved crunch_wps)

lemma state_vrefs_cur_thread_update[Syscall_AC_assms, simp]:
  "state_vrefs (cur_thread_update f s) = state_vrefs s"
  by (simp add: state_vrefs_def)

crunches arch_mask_irq_signal, handle_reserved_irq
  for pas_refined[Syscall_AC_assms, wp]: "pas_refined aag"

crunches handle_hypervisor_fault
  for pas_refined[Syscall_AC_assms, wp]: "pas_refined aag"
  and cur_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (cur_thread s)"
  and integrity[Syscall_AC_assms, wp]: "integrity aag X st"

crunches handle_vm_fault
  for pas_refined[Syscall_AC_assms, wp]: "pas_refined aag"
  and cur_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (cur_thread s)"
  and state_refs_of[Syscall_AC_assms, wp]: "\<lambda>s. P (state_refs_of s)"
  (wp: as_user_getRestart_invs ignore: as_user)

lemma handle_vm_fault_integrity[Syscall_AC_assms]:
  "\<lbrace>integrity aag X st and K (is_subject aag thread)\<rbrace>
   handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (cases vmfault_type, simp_all)
  apply (rule hoare_pre)
  apply (wp as_user_integrity_autarch dmo_wp | simp add: getDFSR_def getFAR_def getIFSR_def)+
  done

crunches ackInterrupt, resetTimer
  for underlying_memory_inv[Syscall_AC_assms, wp]: "\<lambda>s. P (underlying_memory s)"
  (simp: maskInterrupt_def)

crunches arch_mask_irq_signal, handle_reserved_irq
  for integrity[Syscall_AC_assms, wp]: "integrity aag X st"
  (wp: dmo_no_mem_respects)

lemma set_thread_state_restart_to_running_respects[Syscall_AC_assms]:
  "\<lbrace>integrity aag X st and st_tcb_at ((=) Restart) thread and K (pasMayActivate aag)\<rbrace>
   do pc \<leftarrow> as_user thread getRestartPC;
            as_user thread $ setNextPC pc;
            set_thread_state thread Structures_A.thread_state.Running
   od
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def as_user_def split_def setNextPC_def
                   getRestartPC_def setRegister_def bind_assoc getRegister_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: in_monad fun_upd_def[symmetric] cong: if_cong)
  apply (cases "is_subject aag thread")
   apply (cut_tac aag=aag in integrity_update_autarch, simp+)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def obj_at_def st_tcb_at_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (rule_tac tro_tcb_activate[OF refl refl])
    apply (simp add: tcb_bound_notification_reset_integrity_def ctxt_IP_update_def)+
  done

lemma getActiveIRQ_inv[Syscall_AC_assms]:
  "\<forall>f s. P s \<longrightarrow> P (irq_state_update f s) \<Longrightarrow>
   \<lbrace>P\<rbrace> getActiveIRQ irq \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: irq_state_independent_def)

lemma getActiveIRQ_rv_None[Syscall_AC_assms]:
  "\<lbrace>\<top>\<rbrace> getActiveIRQ True \<lbrace>\<lambda>rv ms. (rv \<noteq> None \<longrightarrow> the rv \<notin> non_kernel_IRQs)\<rbrace>"
  by (wpsimp simp: getActiveIRQ_def)

lemma arch_activate_idle_thread_respects[Syscall_AC_assms, wp]:
  "arch_activate_idle_thread t \<lbrace>integrity aag X st\<rbrace>"
  unfolding arch_activate_idle_thread_def by wpsimp

lemma arch_activate_idle_thread_pas_refined[Syscall_AC_assms, wp]:
  "arch_activate_idle_thread t \<lbrace>pas_refined aag\<rbrace>"
  unfolding arch_activate_idle_thread_def by wpsimp

lemma integrity_exclusive_state_update[Syscall_AC_assms, simp]:
  "integrity aag X st (s\<lparr>machine_state := exclusive_state_update f (machine_state s)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

lemma dmo_clearExMonitor_respects_globals[Syscall_AC_assms, wp]:
  "do_machine_op clearExMonitor \<lbrace>integrity aag X st\<rbrace>"
  by (wpsimp wp: dmo_wp simp: clearExMonitor_def)

lemma arch_switch_to_thread_respects[Syscall_AC_assms, wp]:
  "arch_switch_to_thread t \<lbrace>integrity aag X st\<rbrace>"
  unfolding arch_switch_to_thread_def by wpsimp

lemma arch_switch_to_thread_pas_refined[Syscall_AC_assms, wp]:
  "arch_switch_to_thread t \<lbrace>pas_refined aag\<rbrace>"
  unfolding arch_switch_to_thread_def by wpsimp

lemma arch_switch_to_idle_thread_respects[Syscall_AC_assms, wp]:
  "arch_switch_to_idle_thread \<lbrace>integrity aag X st\<rbrace>"
  unfolding arch_switch_to_idle_thread_def by wpsimp

lemma arch_switch_to_idle_thread_pas_refined[Syscall_AC_assms, wp]:
  "arch_switch_to_idle_thread \<lbrace>pas_refined aag\<rbrace>"
  unfolding arch_switch_to_idle_thread_def by wpsimp

lemma arch_mask_irq_signal_arch_state[Syscall_AC_assms, wp]:
  "arch_mask_irq_signal irq \<lbrace>\<lambda>s :: det_ext state. P (arch_state s)\<rbrace>"
  by wpsimp

lemma handle_reserved_irq_arch_state[Syscall_AC_assms, wp]:
  "handle_reserved_irq irq \<lbrace>\<lambda>s :: det_ext state. P (arch_state s)\<rbrace>"
  unfolding handle_reserved_irq_def by wpsimp

crunches init_arch_objects
  for arch_state[Syscall_AC_assms, wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)

crunches arch_post_cap_deletion
  for ct_active[Syscall_AC_assms, wp]: "ct_active"
  (wp: crunch_wps filterM_preserved unless_wp
   simp: crunch_simps ignore: do_extended_op)

crunches
  arch_post_modify_registers, arch_invoke_irq_control,
  arch_invoke_irq_handler, arch_perform_invocation, arch_mask_irq_signal,
  handle_reserved_irq, handle_vm_fault, handle_hypervisor_fault, handle_arch_fault_reply
  for cur_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (cur_thread s)"
  and idle_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (idle_thread s)"
  and cur_domain[Syscall_AC_assms, wp]:  "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps)

\<comment> \<open>These aren't proved in the previous crunch, and hence need to be declared\<close>
declare handle_arch_fault_reply_cur_thread[Syscall_AC_assms]
declare handle_arch_fault_reply_it[Syscall_AC_assms]

end


global_interpretation Syscall_AC_1?: Syscall_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Syscall_AC_assms)?)
qed

end
