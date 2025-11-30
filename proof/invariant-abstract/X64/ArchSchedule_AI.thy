(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSchedule_AI
imports Schedule_AI
begin

context Arch begin arch_global_naming

named_theorems Schedule_AI_assms

lemma dmo_mapM_storeWord_0_invs[wp,Schedule_AI_assms]:
  "valid invs (do_machine_op (mapM (\<lambda>p. storeWord p 0) S)) (\<lambda>_. invs)"
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
  apply (simp add: upto0_7_def word_bits_def split: if_splits)
  done

lemma set_x64_current_fpu_owner_valid_cur_fpu[wp]:
  "set_x64_current_fpu_owner new_owner \<lbrace>valid_cur_fpu\<rbrace>"
  unfolding set_x64_current_fpu_owner_def
  apply (wp arch_thread_set_wp)
  by (auto simp: valid_cur_fpu_defs valid_cur_fpu_is_tcb_cur_fpu_unique'[simplified valid_cur_fpu_defs])

lemma set_x64_current_fpu_owner_valid_pspace[wp]:
  "\<lbrace>valid_pspace and none_top ex_nonz_cap_to t\<rbrace>
   set_x64_current_fpu_owner t
   \<lbrace>\<lambda>_. valid_pspace\<rbrace>"
  unfolding set_x64_current_fpu_owner_def valid_pspace_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_disjI1)
  by fastforce

crunch set_x64_current_fpu_owner
  for valid_mdb[wp]: valid_mdb
  and valid_ioc[wp]: valid_ioc
  and valid_idle[wp]: valid_idle
  and only_idle[wp]: only_idle
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and valid_reply_caps[wp]: valid_reply_caps
  and valid_reply_masters[wp]: valid_reply_masters
  and valid_global_refs[wp]: valid_global_refs
  and valid_arch_state[wp]: valid_arch_state
  and valid_irq_node[wp]: valid_irq_node
  and valid_irq_handlers[wp]: valid_irq_handlers
  and valid_machine_state[wp]: valid_machine_state
  and valid_irq_states[wp]: valid_irq_states
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_arch_caps[wp]: valid_arch_caps
  and valid_global_objs[wp]: valid_global_objs
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and valid_asid_map[wp]: valid_asid_map
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and cur_tcb[wp]: cur_tcb
  (wp: crunch_wps)

lemma set_x64_current_fpu_owner_invs[wp]:
  "\<lbrace>invs and none_top tcb_at t and none_top ex_nonz_cap_to t\<rbrace>
   set_x64_current_fpu_owner t
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def)

crunch save_fpu_state, load_fpu_state
  for invs[wp]: invs
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  (wp: dmo_invs_lift)

lemmas save_fpu_state_typ_ats[wp] = abs_typ_at_lifts[OF save_fpu_state_typ_at]
lemmas load_fpu_state_typ_ats[wp] = abs_typ_at_lifts[OF load_fpu_state_typ_at]

lemma switch_local_fpu_owner_invs:
  "\<lbrace>invs and none_top tcb_at t and none_top ex_nonz_cap_to t\<rbrace> switch_local_fpu_owner t \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding switch_local_fpu_owner_def
  apply (wpsimp wp: dmo_invs_lift hoare_vcg_imp_lift' hoare_disjI1
         | wpsimp wp: hoare_vcg_all_lift)+
  by fastforce

crunch lazy_fpu_restore
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and st_tcb_at[wp]: "\<lambda>s. P (st_tcb_at Q t s)"
  (wp: dmo_invs_lift crunch_wps)

lemma lazy_fpu_restore_invs[wp]:
  "\<lbrace>invs and none_top ex_nonz_cap_to (Some t)\<rbrace>
   lazy_fpu_restore t
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding lazy_fpu_restore_def
  apply (wpsimp wp: dmo_invs_lift switch_local_fpu_owner_invs thread_get_wp')
  apply (clarsimp simp: obj_at_def is_tcb)
  done

crunch set_vm_root
  for ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_stt_invs [wp,Schedule_AI_assms]:
  "\<lbrace>invs and ex_nonz_cap_to t\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding arch_switch_to_thread_def
  by wpsimp

lemma arch_stt_tcb [wp,Schedule_AI_assms]:
  "arch_switch_to_thread t' \<lbrace>tcb_at t'\<rbrace>"
  by (wpsimp simp: arch_switch_to_thread_def wp: tcb_at_typ_at)

lemma arch_stt_st_tcb_at[Schedule_AI_assms]:
  "arch_switch_to_thread t \<lbrace>st_tcb_at Q t\<rbrace>"
  by (wpsimp simp: arch_switch_to_thread_def)

lemma arch_stit_invs[wp, Schedule_AI_assms]:
  "\<lbrace>invs\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>r. invs\<rbrace>"
  by (wpsimp wp: svr_invs simp: arch_switch_to_idle_thread_def)

lemma arch_stit_tcb_at[wp]:
  "\<lbrace>tcb_at t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>r. tcb_at t\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def )
  apply wp
  done

lemma idle_strg:
  "thread = idle_thread s \<and> invs s \<Longrightarrow> invs (s\<lparr>cur_thread := thread\<rparr>)"
  by (clarsimp simp: invs_def valid_state_def valid_idle_def cur_tcb_def
                     pred_tcb_at_def valid_machine_state_def obj_at_def is_tcb_def)

crunch set_vm_root
  for ct[wp]: "\<lambda>s. P (cur_thread s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_stit_activatable[wp, Schedule_AI_assms]:
  "\<lbrace>ct_in_state activatable\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (clarsimp simp: arch_switch_to_idle_thread_def)
  apply (wpsimp simp: ct_in_state_def wp: ct_in_state_thread_state_lift)
  done

lemma stit_invs [wp,Schedule_AI_assms]:
  "switch_to_idle_thread \<lbrace>invs\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wpsimp|strengthen idle_strg)+
  done

lemma stit_activatable[Schedule_AI_assms]:
  "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wp | simp add: ct_in_state_def)+
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def valid_idle_def
                 elim!: pred_tcb_weaken_strongerE)
  done

lemma arch_stt_scheduler_action [wp, Schedule_AI_assms]:
  "\<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  by (wpsimp simp: arch_switch_to_thread_def)

crunch arch_prepare_next_domain
  for ct[wp, Schedule_AI_assms]: "\<lambda>s. P (cur_thread s)"
  and activatable[wp, Schedule_AI_assms]: "ct_in_state activatable"
  and st_tcb_at[wp, Schedule_AI_assms]: "\<lambda>s. P (st_tcb_at Q t s)"
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
  by (intro_locales; unfold_locales; (fact Schedule_AI_assms)?)
  qed

end
