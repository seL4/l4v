(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSchedule_AI
imports Schedule_AI
begin

context Arch begin global_naming RISCV64

declare opt_mapE[rule del]

named_theorems Schedule_AI_asms

lemma dmo_mapM_storeWord_0_invs[wp,Schedule_AI_asms]:
  "do_machine_op (mapM (\<lambda>p. storeWord p 0) S) \<lbrace>invs\<rbrace>"
  apply (simp add: dmo_mapM ef_storeWord)
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
  apply (simp add: upto.simps cur_sc_tcb_def word_bits_def)
  done

global_naming Arch

lemma arch_stt_invs [wp,Schedule_AI_asms]:
  "\<lbrace>invs\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply wp
  done

lemma arch_stt_tcb [wp,Schedule_AI_asms]:
  "\<lbrace>tcb_at t'\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. tcb_at t'\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (wp)
  done

lemma arch_stt_sc_at[wp,Schedule_AI_asms]:
  "arch_switch_to_thread t' \<lbrace>sc_at sc_ptr\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply wp
  done

lemma arch_stt_runnable[Schedule_AI_asms]:
  "\<lbrace>st_tcb_at Q t\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>r . st_tcb_at Q t\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply wp
  done

lemma arch_stit_invs[wp, Schedule_AI_asms]:
  "\<lbrace>invs\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>r. invs\<rbrace>"
  by (wpsimp simp: arch_switch_to_idle_thread_def)

lemma arch_stit_tcb_at[wp, Schedule_AI_asms]:
  "\<lbrace>tcb_at t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>r. tcb_at t\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def )
  apply (wp tcb_at_typ_at)
  done

lemma arch_stit_sc_at[wp, Schedule_AI_asms]:
  "arch_switch_to_idle_thread \<lbrace>sc_at sc_ptr\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply wp
  done

crunches set_vm_root
  for ct[wp]: "\<lambda>s. P (cur_thread s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps wp: hoare_drop_imps)

lemma arch_stit_activatable[wp, Schedule_AI_asms]:
  "\<lbrace>ct_in_state activatable\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (clarsimp simp: arch_switch_to_idle_thread_def)
  apply (wpsimp simp: ct_in_state_def wp: ct_in_state_thread_state_lift)
  done

lemma stit_activatable[Schedule_AI_asms]:
  "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wp | simp add: ct_in_state_def)+
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def valid_idle_def
                 elim!: pred_tcb_weaken_strongerE)
  done

crunches set_vm_root
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  (simp: crunch_simps)

lemma arch_stt_scheduler_action [wp, Schedule_AI_asms]:
  "\<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  by (wpsimp simp: arch_switch_to_thread_def)

lemma arch_stit_scheduler_action [wp, Schedule_AI_asms]:
  "\<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  by (wpsimp simp: arch_switch_to_idle_thread_def)

end

interpretation Schedule_AI?: Schedule_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Schedule_AI_asms)?)
  qed

end
