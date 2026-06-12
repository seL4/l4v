(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAInvs
imports AInvs
begin

context Arch begin arch_global_naming

crunch handle_hypervisor_fault, handle_reserved_irq
  for schact_is_not_rct[wp]: "\<lambda>s. \<not> schact_is_rct s"
  (wp: crunch_wps)

crunch do_machine_op
  for schact_is_rct_ct_in_state_activatable[wp]: "\<lambda>s. schact_is_rct s \<longrightarrow> ct_in_state activatable s"
  (wp: hoare_vcg_imp_lift')

lemma handle_hypervisor_fault_schact_is_rct_ct_in_state_activatable[wp]:
  "handle_hypervisor_fault t fault \<lbrace>\<lambda>s. schact_is_rct s \<longrightarrow> ct_in_state activatable s\<rbrace>"
  supply if_split[split del]
  by (cases fault; wpsimp)

lemma set_vcpu_schact_is_rct_ct_in_state_activatable[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. schact_is_rct s \<longrightarrow> ct_in_state activatable s\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
  done

crunch vgic_update_lr
  for schact_is_rct_ct_in_state_activatable[wp]: "\<lambda>s. schact_is_rct s \<longrightarrow> ct_in_state activatable s"
  (simp: ct_in_state_def)

lemma vgic_maintenance_schact_is_rct_ct_in_state_activatable[wp]:
  "vgic_maintenance \<lbrace>\<lambda>s. schact_is_rct s \<longrightarrow> ct_in_state activatable s\<rbrace>"
  unfolding vgic_maintenance_def
  supply if_split[split del]
  apply (wpsimp wp: thread_get_wp' | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def split: if_splits)
  done

crunch handle_hypervisor_fault, handle_reserved_irq
  for schact_is_rct_ct_in_state_activatable[wp]: "\<lambda>s. schact_is_rct s \<longrightarrow> ct_in_state activatable s"
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and is_active_sc[wp]: "\<lambda>s. P (is_active_sc sc_ptr s)"

crunch handle_hypervisor_fault, handle_reserved_irq
  for ct_not_in_release_q[wp]: ct_not_in_release_q
  (wp: crunch_wps)

end

global_interpretation AInvs_AI?: AInvs_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (solves wpsimp)?)
qed

global_interpretation AInvs_AI_det_ext?: AInvs_AI_det_ext
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; wpsimp)
qed

end
