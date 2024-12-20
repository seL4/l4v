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

lemma invs_current_fpu_owner_update:
  "\<lbrakk>valid_arch_state s\<rbrakk> \<Longrightarrow> invs (s\<lparr>arch_state := arch_state s \<lparr>arm_current_fpu_owner := t\<rparr>\<rparr>) = invs s"
  by (auto simp: invs_def valid_state_def cur_tcb_def cur_vcpu_at_def obj_at_conj_distrib
                 valid_global_refs_def valid_asid_map_def valid_arch_state_def
                 valid_global_objs_def valid_global_vspace_mappings_def cur_vcpu_def
                 global_refs_def vmid_inv_def valid_global_arch_objs_def in_omonad obj_at_def
                 hyp_live_def arch_live_def
          split: option.splits)

lemma invs_current_fpu_owner_update':
  "\<lbrakk> invs s \<rbrakk> \<Longrightarrow> invs (s\<lparr>arch_state := arch_state s\<lparr>arm_current_fpu_owner := t\<rparr>\<rparr>)"
  apply (prop_tac "valid_arch_state s", simp add: invs_def valid_state_def)
  apply (simp add: invs_current_fpu_owner_update)
  done

crunch save_fpu_state, load_fpu_state
  for invs[wp]: invs
  (wp: dmo_invs_lift)

lemma switch_local_fpu_owner_invs:
  "switch_local_fpu_owner t \<lbrace>invs\<rbrace>"
  unfolding switch_local_fpu_owner_def
  by (wpsimp wp: dmo_invs_lift hoare_drop_imps | strengthen invs_current_fpu_owner_update')+

crunch lazy_fpu_restore
  for invs[wp]: invs
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and pred_tcb_at[wp]: "\<lambda>s. P (pred_tcb_at proj Q t s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: dmo_invs_lift)

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

crunch arch_prepare_next_domain
  for ct[wp, Schedule_AI_assms]: "\<lambda>s. P (cur_thread s)"
  and activatable[wp, Schedule_AI_assms]: "ct_in_state activatable"
  and pred_tcb_at[wp, Schedule_AI_assms]: "\<lambda>s. P (pred_tcb_at proj Q t s)"
  and valid_idle[wp, Schedule_AI_assms]: valid_idle
  and invs[wp, Schedule_AI_assms]: invs
  (wp: crunch_wps ct_in_state_thread_state_lift)

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
