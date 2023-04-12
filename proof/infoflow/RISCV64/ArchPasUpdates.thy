(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchPasUpdates
imports PasUpdates
begin

context Arch begin

named_theorems PasUpdates_assms

lemma arch_post_cap_deletion_domain_fields:
  "arch_post_cap_deletion c \<lbrace>domain_fields P\<rbrace>"
  sorry (* broken by timeprot -scottb *)

lemma arch_finalise_cap_domain_fields:
  "arch_finalise_cap c b \<lbrace>domain_fields P\<rbrace>"
  sorry (* broken by timeprot -scottb *)

lemma prepare_thread_delete_domain_fields:
  "prepare_thread_delete c \<lbrace>domain_fields P\<rbrace>"
  sorry (* broken by timeprot -scottb *)

crunches arch_post_cap_deletion, arch_finalise_cap, prepare_thread_delete
  for domain_fields[PasUpdates_assms, wp]: "domain_fields P"
  (    wp: syscall_valid select_wp crunch_wps rec_del_preservation cap_revoke_preservation modify_wp
           
     simp: crunch_simps check_cap_at_def filterM_mapM unless_def
   ignore: without_preemption filterM rec_del check_cap_at cap_revoke
   ignore_del: retype_region_ext create_cap_ext cap_insert_ext ethread_set cap_move_ext
               empty_slot_ext cap_swap_ext set_thread_state_ext tcb_sched_action reschedule_required)

end


global_interpretation PasUpdates_1?: PasUpdates_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    apply (unfold_locales; (fact PasUpdates_assms)?)
      using arch_post_cap_deletion_domain_fields apply blast
     using arch_finalise_cap_domain_fields apply presburger
    using prepare_thread_delete_domain_fields by blast
qed


context Arch begin

declare init_arch_objects_exst[PasUpdates_assms]

lemma arch_perform_invocation_domain_fields:
  "arch_perform_invocation i \<lbrace>domain_fields P\<rbrace>"
  sorry (* broken by timeprot - scottb *)

lemma handle_arch_fault_reply_domain_fields:
  "handle_arch_fault_reply a b c d \<lbrace>domain_fields P\<rbrace>"
  sorry (* broken by timeprot - scottb *)

crunches arch_perform_invocation, arch_post_modify_registers,
         arch_invoke_irq_control, arch_invoke_irq_handler, handle_arch_fault_reply
  for domain_fields[PasUpdates_assms, wp]: "domain_fields P"
  (wp: syscall_valid crunch_wps mapME_x_inv_wp
   simp: crunch_simps check_cap_at_def detype_def detype_ext_def mapM_x_defsym
   ignore: check_cap_at syscall
   ignore_del: set_domain set_priority possible_switch_to
   rule: transfer_caps_loop_pres)

lemma state_asids_to_policy_aux_pasSubject_update:
  "state_asids_to_policy_aux (aag\<lparr>pasSubject := x\<rparr>) caps asid vrefs =
   state_asids_to_policy_aux aag caps asid vrefs"
  apply (rule equalityI)
   apply clarify
   apply (erule state_asids_to_policy_aux.cases
          | simp
          | fastforce intro: state_asids_to_policy_aux.intros)+
  apply clarify
  apply (erule state_asids_to_policy_aux.cases)
    apply (simp, subst pasObjectAbs_pasSubject_update[symmetric]
               , subst pasASIDAbs_pasSubject_update[symmetric]
               , rule state_asids_to_policy_aux.intros
               , assumption+)+
  done

lemma state_asids_to_policy_pasSubject_update[PasUpdates_assms]:
  "state_asids_to_policy (aag\<lparr>pasSubject := x\<rparr>) s =
   state_asids_to_policy aag s"
  by (simp add: state_asids_to_policy_aux_pasSubject_update)

lemma state_asids_to_policy_aux_pasMayActivate_update:
  "state_asids_to_policy_aux (aag\<lparr>pasMayActivate := x\<rparr>) caps asid_tab vrefs =
   state_asids_to_policy_aux aag caps asid_tab vrefs"
  apply (rule equalityI)
   apply clarify
   apply (erule state_asids_to_policy_aux.cases
          | simp
          | fastforce intro: state_asids_to_policy_aux.intros)+
  apply clarify
  apply (erule state_asids_to_policy_aux.cases)
    apply (simp, subst pasObjectAbs_pasMayActivate_update[symmetric]
               , subst pasASIDAbs_pasMayActivate_update[symmetric]
               , rule state_asids_to_policy_aux.intros
               , assumption+)+
  done

lemma state_asids_to_policy_pasMayActivate_update[PasUpdates_assms]:
  "state_asids_to_policy (aag\<lparr>pasMayActivate := x\<rparr>) s =
   state_asids_to_policy aag s"
  by (simp add: state_asids_to_policy_aux_pasMayActivate_update)

lemma state_asids_to_policy_aux_pasMayEditReadyQueues_update:
  "state_asids_to_policy_aux (aag\<lparr>pasMayEditReadyQueues := x\<rparr>) caps asid_tab vrefs =
   state_asids_to_policy_aux aag caps asid_tab vrefs"
  apply (rule equalityI)
   apply (clarify)
   apply (erule state_asids_to_policy_aux.cases
          | simp
          | fastforce intro: state_asids_to_policy_aux.intros)+
  apply (clarify)
  apply (erule state_asids_to_policy_aux.cases)
    apply (simp, subst pasObjectAbs_pasMayEditReadyQueues_update[symmetric]
               , subst pasASIDAbs_pasMayEditReadyQueues_update[symmetric]
               , rule state_asids_to_policy_aux.intros
               , assumption+)+
  done

lemma state_asids_to_policy_pasMayEditReadyQueues_update[PasUpdates_assms]:
  "state_asids_to_policy (aag\<lparr>pasMayEditReadyQueues := x\<rparr>) s =
   state_asids_to_policy aag s"
  by (simp add: state_asids_to_policy_aux_pasMayEditReadyQueues_update)

end


global_interpretation PasUpdates_2?: PasUpdates_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    apply (unfold_locales; (fact PasUpdates_assms)?)
     using arch_perform_invocation_domain_fields apply presburger
    using handle_arch_fault_reply_inv apply blast
    done
qed

end
