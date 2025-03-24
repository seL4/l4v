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
  apply (simp add: dom_mapM ef_storeWord)
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

lemma arch_stt_invs [wp,Schedule_AI_assms]:
  "\<lbrace>invs\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply wp
  done

lemma arch_stt_tcb [wp,Schedule_AI_assms]:
  "\<lbrace>tcb_at t'\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. tcb_at t'\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (wp)
  done

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

crunch set_vm_root
  for st_tcb_at[wp]: "st_tcb_at P t"
  (wp: crunch_wps simp: crunch_simps)

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
