(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSchedule_AI
imports Schedule_AI
begin

context Arch begin arch_global_naming

named_theorems Schedule_AI_assms

lemma dmo_mapM_storeWord_0_invs[wp,Schedule_AI_assms]:
  "do_machine_op (mapM (\<lambda>p. storeWord p 0) S) \<lbrace>invs\<rbrace>"
  apply (simp add: dom_mapM)
  apply (rule mapM_UNIV_wp)
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def
                        valid_machine_state_def)
  apply (rule conjI)
   apply(erule use_valid[OF _ storeWord_valid_irq_states], simp)
  apply (erule use_valid)
   apply (simp add: storeWord_def word_rsplit_0)
   apply wp
  by (simp add: upto.simps word_bits_def)

lemma arch_stt_invs [wp,Schedule_AI_assms]:
  "arch_switch_to_thread t' \<lbrace>invs\<rbrace>"
  apply (wpsimp simp: arch_switch_to_thread_def)
  by (rule sym_refs_VCPU_hyp_live; fastforce)

lemma arch_stt_tcb [wp,Schedule_AI_assms]:
  "arch_switch_to_thread t' \<lbrace>tcb_at t'\<rbrace>"
  by (wpsimp simp: arch_switch_to_thread_def wp: tcb_at_typ_at)

lemma arch_stt_st_tcb_at[Schedule_AI_assms]:
  "arch_switch_to_thread t \<lbrace>st_tcb_at Q t\<rbrace>"
  by (wpsimp simp: arch_switch_to_thread_def)

lemma idle_strg:
  "thread = idle_thread s \<and> invs s \<Longrightarrow> invs (s\<lparr>cur_thread := thread\<rparr>)"
  by (clarsimp simp: invs_def valid_state_def valid_idle_def cur_tcb_def
                     pred_tcb_at_def valid_machine_state_def obj_at_def is_tcb_def)

crunch
  vcpu_update, vgic_update, vgic_update_lr, vcpu_restore_reg_range, vcpu_save_reg_range,
  vcpu_enable, vcpu_disable, vcpu_save, vcpu_restore, vcpu_switch, vcpu_save
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  and ct[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: mapM_x_wp mapM_wp subset_refl)

lemma arch_stit_invs[wp, Schedule_AI_assms]:
  "arch_switch_to_idle_thread \<lbrace>invs\<rbrace>"
  by (wpsimp simp: arch_switch_to_idle_thread_def)

lemma arch_stit_tcb_at[wp]:
  "arch_switch_to_idle_thread \<lbrace>tcb_at t\<rbrace>"
  by (wpsimp simp: arch_switch_to_idle_thread_def wp: tcb_at_typ_at)

crunch set_vm_root
  for ct[wp]: "\<lambda>s. P (cur_thread s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps wp: hoare_drop_imps)

lemma arch_stit_activatable[wp, Schedule_AI_assms]:
  "arch_switch_to_idle_thread \<lbrace>ct_in_state activatable\<rbrace>"
  apply (clarsimp simp: arch_switch_to_idle_thread_def)
  apply (wpsimp simp: ct_in_state_def wp: ct_in_state_thread_state_lift)
  done

lemma stit_invs [wp,Schedule_AI_assms]:
  "switch_to_idle_thread \<lbrace>invs\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wpsimp|strengthen idle_strg)+
  done

lemma stit_activatable[Schedule_AI_assms]:
  "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>_. ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wpsimp simp: ct_in_state_def)
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def valid_idle_def
                 elim!: pred_tcb_weaken_strongerE)
  done

crunch set_vm_root, vcpu_switch
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_stt_scheduler_action [wp, Schedule_AI_assms]:
  "\<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  by (wpsimp simp: arch_switch_to_thread_def)

lemma arch_stit_scheduler_action [wp, Schedule_AI_assms]:
  "\<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  by (wpsimp simp: arch_switch_to_idle_thread_def)

end

interpretation Schedule_AI?: Schedule_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (intro_locales; (unfold_locales; fact Schedule_AI_assms)?)
qed

end
