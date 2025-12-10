(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSyscall_AC
imports Syscall_AC
begin

context Arch begin arch_global_naming

named_theorems Syscall_AC_assms

crunch set_original
  for idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

declare prepare_thread_delete_idle_thread[Syscall_AC_assms]

lemma cap_move_idle_thread[Syscall_AC_assms, wp]:
  "cap_move new_cap src_slot dest_slot \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>"
  unfolding cap_move_def
  by (wpsimp wp: dxo_wp_weak)

lemma cancel_badged_sends_idle_thread[Syscall_AC_assms, wp]:
  "cancel_badged_sends epptr badge \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>"
  unfolding cancel_badged_sends_def
  by (wpsimp wp: dxo_wp_weak mapM_wp_inv get_simple_ko_wp simp: filterM_mapM)

declare arch_finalise_cap_idle_thread[Syscall_AC_assms]

lemma invs_irq_state_update[Syscall_AC_assms, simp]:
  "invs (s\<lparr>machine_state := irq_state_update f sa\<rparr>) = invs (s\<lparr>machine_state := sa\<rparr>)"
  apply (rule iffI)
   apply (subst invs_irq_state_independent[where f=f, symmetric])
   apply (erule back_subst[where P=invs])
   apply clarsimp
  apply (subst (asm) invs_irq_state_independent[where f=f, symmetric])
  apply clarsimp
  apply (erule back_subst[where P=invs])
  apply clarsimp
  done

declare prepare_thread_delete_cur_thread[Syscall_AC_assms]
        arch_finalise_cap_cur_thread[Syscall_AC_assms]

lemma cap_move_cur_thread[Syscall_AC_assms, wp]:
  "cap_move new_cap src_slot dest_slot \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
  unfolding cap_move_def
  by (wpsimp wp: dxo_wp_weak)

lemma cancel_badged_sends_cur_thread[Syscall_AC_assms, wp]:
  "cancel_badged_sends epptr badge \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
  unfolding cancel_badged_sends_def
  by (wpsimp wp: dxo_wp_weak filterM_preserved crunch_wps)

crunch arch_mask_irq_signal
  for pas_refined[Syscall_AC_assms, wp]: "pas_refined aag"
  (wp: crunch_wps simp: crunch_simps)

crunch handle_vm_fault
  for pas_refined[Syscall_AC_assms, wp]: "pas_refined aag"
  and cur_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (cur_thread s)"
  and state_refs_of[Syscall_AC_assms, wp]: "\<lambda>s. P (state_refs_of s)"

lemma handle_vm_fault_integrity[Syscall_AC_assms]:
  "\<lbrace>integrity aag X st and K (is_subject aag thread)\<rbrace>
   handle_vm_fault thread vmfault_type
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  unfolding handle_vm_fault_def addressTranslateS1_def
  by (cases vmfault_type; wpsimp wp: dmo_no_mem_respects as_user_integrity_autarch )

crunch ackInterrupt, resetTimer
  for underlying_memory_inv[Syscall_AC_assms, wp]: "\<lambda>s. P (underlying_memory s)"
  (simp: maskInterrupt_def)

crunch arch_mask_irq_signal
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
  apply (clarsimp simp: integrity_def integrity_arch_kh_upds dest!: get_tcb_SomeD)
  apply (intro conjI)
   apply (clarsimp simp: st_tcb_at_def obj_at_def opt_map_def)
   apply (rule_tac tro_tcb_activate[OF refl refl])
     apply (simp add: tcb_bound_notification_reset_integrity_def arch_tcb_set_registers_def
               split: user_context.splits)+
     apply (auto simp: integrity_fpu_def fpu_of_state_def arch_tcb_get_registers_def
                       arch_tcb_context_set_def arch_tcb_context_get_def)
  done

lemma getActiveIRQ_inv[Syscall_AC_assms]:
  "\<forall>f s. P s \<longrightarrow> P (irq_state_update f s)
   \<Longrightarrow> \<lbrace>P\<rbrace> getActiveIRQ irq \<lbrace>\<lambda>rv. P\<rbrace>"
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

lemma update_asid_pool_entry_valid_cur_vcpu[wp]:
  "update_asid_pool_entry f asid \<lbrace>valid_cur_vcpu\<rbrace>"
  by (wpsimp wp: valid_cur_vcpu_lift_weak in_cur_domain_lift_weak)

lemma valid_cur_vcpu_vmid_upd[simp]:
  "valid_cur_vcpu (s\<lparr>arch_state := arch_state s\<lparr>arm_next_vmid := v\<rparr>\<rparr>) = valid_cur_vcpu s"
  by (auto simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)

crunch set_vm_root, vcpu_switch, vcpu_flush
  for valid_cur_fpu[wp]: "valid_cur_fpu"
  (wp: mapM_x_wp_inv mapM_wp_inv)

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for integrity[Syscall_AC_assms, wp]: "integrity aag X st"
  and pas_refined[Syscall_AC_assms, wp]: "pas_refined aag"
  (wp: crunch_wps vcpu_switch_respects simp: crunch_simps)

lemma handle_reserved_irq_arch_state[Syscall_AC_assms, wp]:
  "handle_reserved_irq irq \<lbrace>\<lambda>s :: det_state. P (arch_state s)\<rbrace>"
  unfolding handle_reserved_irq_def by wpsimp

crunch arch_post_cap_deletion
  for ct_active[Syscall_AC_assms, wp]: "ct_active"
  (wp: crunch_wps filterM_preserved unless_wp simp: crunch_simps ignore: do_extended_op)

crunch
  arch_post_modify_registers, arch_invoke_irq_control,
  arch_invoke_irq_handler, arch_perform_invocation, arch_mask_irq_signal,
  handle_vm_fault, handle_arch_fault_reply
  for cur_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (cur_thread s)"
  and idle_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (idle_thread s)"
  and cur_domain[Syscall_AC_assms, wp]:  "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps simp: crunch_simps)

declare arch_invoke_irq_control_cur_domain[Syscall_AC_assms]
        arch_invoke_irq_handler_cur_domain[Syscall_AC_assms]
        arch_mask_irq_signal_idle_thread[Syscall_AC_assms]
        arch_mask_irq_signal_cur_domain[Syscall_AC_assms]
        handle_reserved_irq_idle_thread[Syscall_AC_assms]
        handle_reserved_irq_cur_domain[Syscall_AC_assms]
        handle_arch_fault_reply_cur_domain[Syscall_AC_assms]
        handle_hypervisor_fault_idle_thread[Syscall_AC_assms]
        handle_hypervisor_fault_cur_domain[Syscall_AC_assms]
        handle_vm_fault_idle_thread[Syscall_AC_assms]
        handle_vm_fault_cur_domain[Syscall_AC_assms]

crunch set_extra_badge
 for cur_domain[Syscall_AC_assms, wp]:  "\<lambda>s :: det_state. P (cur_domain s)"
  (wp: crunch_wps simp: crunch_simps)

lemma transfer_caps_loop_cur_domain[wp]:
  "transfer_caps_loop ep rcv_buffer n caps slots mi \<lbrace>\<lambda>s :: det_state. P (cur_domain s)\<rbrace>"
  supply if_split[split del]
  apply (induct caps arbitrary: slots n mi)
   apply (wpsimp | assumption)+
  done

crunch vgic_update_lr, vgic_update
  for integrity_autarch[wp]: "integrity aag X st"

lemma set_lrs_integrity_autarch:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> option_map (is_subject aag \<circ> fst) (arm_current_vcpu (arch_state s)) = Some True\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_lr n w)
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_gic_vcpu_ctrl_lr_def dmo_distr)
  apply wp
   apply (wp dmo_wp)
  apply (clarsimp simp: integrity_def)
  apply (erule allE, erule trhyp_trans)
  apply (clarsimp simp: integrity_hyp_def vcpu_integrity_def vcpu_of_state_def
                split: option.splits)
  done

lemma vgic_maintenance_integrity_autarch:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> pas_refined aag s \<and> is_subject aag (cur_thread s) \<and> invs s
        \<and> valid_cur_vcpu s \<and> (in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)\<rbrace>
   vgic_maintenance
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  (is "\<lbrace>?P\<rbrace> _ \<lbrace>_\<rbrace>")
  unfolding vgic_maintenance_def get_gic_vcpu_ctrl_misr_def
            get_gic_vcpu_ctrl_eisr0_def get_gic_vcpu_ctrl_eisr1_def
  apply (wpsimp wp: handle_fault_integrity_autarch gts_wp
                    set_lrs_integrity_autarch dmo_no_mem_respects
         split_del: if_split
         | wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)+
  apply (frule invs_cur)
  apply (clarsimp simp: valid_fault_def cur_tcb_def tcb_at_def)
  apply (fastforce simp: valid_cur_vcpu_def active_cur_vcpu_of_def
                         pred_tcb_at_def obj_at_def get_tcb_def
                  intro: associated_vcpu_is_subject)
  done

lemma vgic_maintenance_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> (ct_active s \<longrightarrow> is_subject aag (cur_thread s)) \<and> invs s\<rbrace>
   vgic_maintenance
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  unfolding vgic_maintenance_def get_gic_vcpu_ctrl_misr_def
            get_gic_vcpu_ctrl_eisr1_def get_gic_vcpu_ctrl_eisr0_def
  apply (wpsimp wp: handle_fault_pas_refined gts_wp)
               apply (rule hoare_lift_Pf2[where f="cur_thread", rotated])
                apply wpsimp
               apply (wpsimp wp:  vcpu_update_trivial_invs
                                 hoare_vcg_all_lift hoare_vcg_imp_lift)
              apply (rule_tac Q'="\<lambda>rv s. pas_refined aag s \<and> (ct_active s \<longrightarrow> is_subject aag (cur_thread s)) \<and> invs s"
                           in hoare_strengthen_post[rotated])
               apply (clarsimp simp: valid_fault_def ct_in_state_def pred_tcb_at_def obj_at_def runnable_eq)
              apply ((wpsimp wp: hoare_vcg_imp_lift)+)[4]
          apply (rule_tac Q'="\<lambda>rv s. pas_refined aag s \<and> (ct_active s \<longrightarrow> is_subject aag (cur_thread s)) \<and> invs s"
                       in hoare_strengthen_post[rotated])
           apply (auto simp: valid_fault_def ct_in_state_def pred_tcb_at_def obj_at_def runnable_eq)[1]
          apply wpsimp+
  done

lemma vcpu_vppi_masked_update_state_hyp_refs_of[wp]:
  "vcpu_update vcpu_ptr (\<lambda>vcpu. vcpu_vppi_masked_update (f vcpu) vcpu)
   \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding invoke_vcpu_ack_vppi_def vcpu_update_def readVCPUHardwareReg_def
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp dmo_wp)
  apply (erule back_subst[where P=P])
  apply (fastforce simp: state_hyp_refs_of_def opt_map_def split: option.splits if_splits)
  done

lemma vcpu_vppi_masked_update_pas_refined[wp]:
  "vcpu_update vcpu_ptr (\<lambda>vcpu. vcpu\<lparr>vcpu_vppi_masked := (vcpu_vppi_masked vcpu)(vppi := True)\<rparr>)
   \<lbrace>pas_refined aag\<rbrace>"
  unfolding pas_refined_def state_objs_to_policy_def by (wp | wps | simp)+

lemma vppi_event_integrity_autarch:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> pas_refined aag s \<and> invs s \<and> valid_cur_vcpu s \<and> is_subject aag (cur_thread s)
        \<and> (in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)\<rbrace>
   vppi_event irq
   \<lbrace>\<lambda>_ s. integrity aag X st s\<rbrace>"
  unfolding vppi_event_def
  apply (wpsimp wp: handle_fault_integrity_autarch maskInterrupt_invs dmo_no_mem_respects
                    vcpu_update_integrity_autarch  vcpu_update_trivial_invs
              simp: if_fun_split
         | wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)+
  apply (frule invs_cur)
  apply (clarsimp simp: valid_fault_def cur_tcb_def tcb_at_def)
  apply (fastforce intro: associated_vcpu_is_subject
                    simp: valid_cur_vcpu_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def get_tcb_def)
  done

lemma vppi_event_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> (ct_active s \<longrightarrow> is_subject aag (cur_thread s)) \<and> invs s\<rbrace>
   vppi_event irq
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  unfolding vppi_event_def
  apply (wpsimp wp: handle_fault_pas_refined gts_wp)
       apply (rule hoare_lift_Pf2[where f="cur_thread", rotated])
        apply wpsimp
       apply (wpsimp wp: vcpu_update_trivial_invs
                         hoare_vcg_all_lift hoare_vcg_imp_lift)
      apply (rule_tac Q'="\<lambda>rv s. pas_refined aag s \<and> (ct_active s \<longrightarrow> is_subject aag (cur_thread s)) \<and> invs s"
                   in hoare_strengthen_post[rotated])
       apply (clarsimp simp: valid_fault_def ct_in_state_def pred_tcb_at_def obj_at_def runnable_eq)
      apply (wpsimp wp: maskInterrupt_invs  hoare_vcg_imp_lift)+
  done

lemma handle_reserved_irq_integrity_autarch[Syscall_AC_assms]:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and valid_cur_vcpu
                       and is_subject aag \<circ> cur_thread
                       and (\<lambda>s. in_cur_domain (cur_thread s) s \<or> cur_thread s = idle_thread s)\<rbrace>
   handle_reserved_irq irq
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding handle_reserved_irq_def
  by (wpsimp wp: vppi_event_integrity_autarch vgic_maintenance_integrity_autarch)

lemma handle_reserved_irq_pas_refined[Syscall_AC_assms]:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> invs s \<and> (ct_active s \<longrightarrow> is_subject aag (cur_thread s))\<rbrace>
   handle_reserved_irq irq
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  unfolding handle_reserved_irq_def
  by (wpsimp wp: vppi_event_pas_refined vgic_maintenance_pas_refined)

lemma vgic_maintenance_idle:
  "\<lbrace>integrity aag X st and invs and valid_cur_vcpu and ct_idle\<rbrace>
   vgic_maintenance
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding vgic_maintenance_def
  apply (rule bind_wp)
   apply (rule_tac P'="\<lambda>s. integrity aag X st s \<and> (\<forall>v. rv \<noteq> Some (v,True))" in hoare_weaken_pre)
    apply (case_tac rv; clarsimp)
    apply (case_tac b; clarsimp)
   apply assumption
  apply (wpsimp)
  apply (prop_tac "only_idle s")
   apply (clarsimp simp: invs_def valid_state_def)
  apply (prop_tac "arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = None) (idle_thread s) s")
   apply (frule invs_valid_idle)
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def valid_arch_idle_def obj_at_def)
  apply (clarsimp simp: valid_cur_vcpu_def only_idle_def pred_tcb_at_def
                        ct_in_state_def obj_at_def active_cur_vcpu_of_def)
  done

lemma vppi_event_idle:
  "\<lbrace>integrity aag X st and invs and valid_cur_vcpu and ct_idle\<rbrace>
   vppi_event irq
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding vppi_event_def
  apply (rule bind_wp)
   apply (rule_tac P'="\<lambda>s. integrity aag X st s \<and> (\<forall>v. rv \<noteq> Some (v,True))" in hoare_weaken_pre)
    apply (case_tac rv; clarsimp)
    apply (case_tac b; clarsimp)
   apply assumption
  apply (wpsimp)
  apply (prop_tac "only_idle s")
   apply (clarsimp simp: invs_def valid_state_def)
  apply (prop_tac "arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = None) (idle_thread s) s")
   apply (frule invs_valid_idle)
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def valid_arch_idle_def obj_at_def)
  apply (clarsimp simp: valid_cur_vcpu_def only_idle_def pred_tcb_at_def
                        ct_in_state_def obj_at_def active_cur_vcpu_of_def)
  done

lemma handle_reserved_irq_idle[Syscall_AC_assms]:
  "\<lbrace>integrity aag X st and invs and valid_cur_vcpu and ct_idle\<rbrace>
   handle_reserved_irq irq
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding handle_reserved_irq_def
  by (wpsimp wp: vppi_event_idle vgic_maintenance_idle)

lemma handle_hypervisor_fault_pas_refined[Syscall_AC_assms, wp]:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> is_subject aag (cur_thread s) \<and> is_subject aag thread \<and> invs s\<rbrace>
   handle_hypervisor_fault thread fault
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  apply (case_tac fault)
  apply clarify
  apply (subst handle_hypervisor_fault.simps)
  apply (wpsimp wp: handle_fault_pas_refined simp: getESR_def isFpuEnable_def valid_fault_def)
  done

lemma handle_hypervisor_fault_integrity_autarch[Syscall_AC_assms, wp]:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> pas_refined aag s \<and> invs s \<and> is_subject aag thread
                             \<and> (ct_active s \<longrightarrow> is_subject aag (cur_thread s))\<rbrace>
   handle_hypervisor_fault thread fault
   \<lbrace>\<lambda>_ s. integrity aag X st s\<rbrace>"
  apply (case_tac fault)
  apply clarify
  apply (subst handle_hypervisor_fault.simps)
  apply (wpsimp wp: handle_fault_integrity_autarch simp: getESR_def isFpuEnable_def valid_fault_def)
  done

crunch ackInterrupt, resetTimer
  for vcpu_state[wp]: "\<lambda>s. P (vcpu_state s)"
  and fpu_state[wp]: "\<lambda>s. P (fpu_state s)"

lemma ackInterrupt_integrity[Syscall_AC_assms,wp]:
  "do_machine_op (ackInterrupt irq) \<lbrace>integrity aag X st\<rbrace>"
  by (wpsimp wp: dmo_no_mem_respects)

lemma maskInterrupt_integrity[Syscall_AC_assms,wp]:
  "do_machine_op (maskInterrupt m irq) \<lbrace>integrity aag X st\<rbrace>"
  by (wpsimp wp: dmo_no_mem_respects)

lemma resetTimer_integrity[Syscall_AC_assms,wp]:
  "do_machine_op resetTimer \<lbrace>integrity aag X st\<rbrace>"
  by (wpsimp wp: dmo_no_mem_respects)

lemma valid_cur_vcpu_machine_state[simp]:
  "valid_cur_vcpu (machine_state_update f s) = valid_cur_vcpu s"
  by (simp add: valid_cur_vcpu_def active_cur_vcpu_of_def)

declare valid_cur_vcpu_machine_state[Syscall_AC_assms]
        handle_event_valid_cur_vcpu[Syscall_AC_assms]
        valid_cur_vcpu_machine_state[Syscall_AC_assms]

\<comment> \<open>These aren't proved in the previous crunch, and hence need to be declared\<close>
declare handle_arch_fault_reply_it[Syscall_AC_assms]
declare handle_arch_fault_reply_cur_thread[Syscall_AC_assms]
declare arch_invoke_irq_control_cur_thread[Syscall_AC_assms]
declare arch_invoke_irq_handler_cur_thread[Syscall_AC_assms]
declare arch_mask_irq_signal_cur_thread[Syscall_AC_assms]
declare handle_reserved_irq_cur_thread[Syscall_AC_assms]
declare handle_hypervisor_fault_cur_thread[Syscall_AC_assms]
declare handle_vm_fault_cur_thread[Syscall_AC_assms]
declare ackInterrupt_underlying_memory_inv[Syscall_AC_assms]
declare resetTimer_underlying_memory_inv[Syscall_AC_assms]
declare arch_mask_irq_signal_arch_state[Syscall_AC_assms]
declare init_arch_objects_arch_state[Syscall_AC_assms]
declare arch_prepare_set_domain_idle_thread[Syscall_AC_assms]
declare arch_prepare_next_domain_valid_idle_etcb[Syscall_AC_assms]

lemma arch_thread_set_ct_in_cur_domain[wp]:
  "arch_thread_set f t \<lbrace>ct_in_cur_domain\<rbrace>"
  by (wpsimp wp: arch_thread_set_wp
           simp: ct_in_cur_domain_def in_cur_domain_def get_tcb_def etcbs_of'_def etcb_at'_def
          split: option.splits kernel_object.splits if_splits)

crunch vcpu_flush
  for ct_in_cur_domain[wp]: ct_in_cur_domain
  and weak_valid_sched_action[wp]: weak_valid_sched_action
  (ignore: vcpu_flush wp: weak_valid_sched_action_lift)

crunch arch_prepare_next_domain
  for integrity[Syscall_AC_assms, wp]: "integrity aag X st"
  and pas_refined[Syscall_AC_assms, wp]: "pas_refined aag"
  and ct_not_in_q[Syscall_AC_assms, wp]: "ct_not_in_q"
  and ct_in_cur_domain[Syscall_AC_assms, wp]: "ct_in_cur_domain"

lemma vcpu_flush_valid_sched_action[wp]:
  "vcpu_flush \<lbrace>valid_sched_action\<rbrace>"
  unfolding valid_sched_action_def is_activatable_def st_tcb_at_kh_simp
  by (rule hoare_lift_Pf[where f=cur_thread]; wpsimp wp: hoare_vcg_imp_lift switch_in_cur_domain_lift)

crunch arch_prepare_set_domain, arch_prepare_next_domain, arch_post_set_flags, handle_spurious_irq
  for valid_sched_action[Syscall_AC_assms, wp]: "valid_sched_action"
  and cur_domain[Syscall_AC_assms, wp]: "\<lambda>s. P (cur_domain s)"
  and cur_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (cur_thread s)"
  and idle_thread[Syscall_AC_assms, wp]: "\<lambda>s. P (idle_thread s)"

(* already proved elsewhere, so the attribute is not picked up in the crunch above *)
declare handle_spurious_irq_cur_domain[Syscall_AC_assms]
declare handle_spurious_irq_cur_thread[Syscall_AC_assms]
declare arch_prepare_next_domain_cur_domain[Syscall_AC_assms]
declare arch_prepare_set_domain_cur_domain[Syscall_AC_assms]
declare arch_prepare_set_domain_cur_thread[Syscall_AC_assms]

crunch handle_spurious_irq
  for pas_refined[Syscall_AC_assms, wp]: "pas_refined aag"
  and integrity[Syscall_AC_assms, wp]: "integrity aag X st"
  (ignore: do_machine_op)

crunch arch_post_cap_deletion, prepare_thread_delete
  for scheduler_action[Syscall_AC_assms, wp]: "\<lambda>s. P (scheduler_action s)"

lemma arch_invoke_irq_control_in_cur_domainE[Syscall_AC_assms, wp]:
  "\<lbrace>\<lambda>s::det_state. in_cur_domain t s\<rbrace>
   arch_invoke_irq_control ivk
   -,\<lbrace>\<lambda>_ s. in_cur_domain t s\<rbrace>"
  by (cases ivk; simp; (solves \<open>wpsimp\<close>)?)

lemma arch_perform_invocation_in_cur_domainE[Syscall_AC_assms, wp]:
  "\<lbrace>\<lambda>s::det_state. in_cur_domain t s\<rbrace>
   arch_perform_invocation ai
   -,\<lbrace>\<lambda>_ s. in_cur_domain t s\<rbrace>"
  by (wpsimp simp: arch_perform_invocation_def)

end


global_interpretation Syscall_AC_1?: Syscall_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Syscall_AC_assms[folded valid_cur_hyp_def])?)
qed

end
