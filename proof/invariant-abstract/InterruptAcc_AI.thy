(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)


theory InterruptAcc_AI
imports ArchTcbAcc_AI
begin

lemma get_irq_slot_real_cte[wp]:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>real_cte_at\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_irq_node_def)
  done


lemma get_irq_slot_cte_at[wp]:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>cte_at\<rbrace>"
  apply (rule hoare_strengthen_post [OF get_irq_slot_real_cte])
  apply (clarsimp simp: real_cte_at_cte)
  done


crunch set_irq_state
  for valid_ioc[wp]: valid_ioc

definition valid_irq_masks_but where
  "valid_irq_masks_but irq table masked \<equiv> \<forall> irq'. irq' \<noteq> irq \<longrightarrow> table irq' = IRQInactive \<longrightarrow> masked irq'"

definition valid_irq_states_but where
  "valid_irq_states_but irq s \<equiv> valid_irq_masks_but irq (interrupt_states s) (irq_masks (machine_state s))"

definition all_invs_but_valid_irq_states_for where
  "all_invs_but_valid_irq_states_for irq \<equiv> valid_pspace and valid_mdb and
  valid_ioc and valid_idle and only_idle and
  if_unsafe_then_cap and
  valid_global_refs and
  valid_arch_state and
  valid_cur_fpu and
  valid_irq_node and
  valid_irq_handlers and
  valid_irq_states_but irq and
  valid_machine_state and
  valid_vspace_objs and \<comment> \<open> ARMHYP \<close>
  valid_arch_caps and
  valid_kernel_mappings and
  equal_kernel_mappings and
  valid_asid_map and
  valid_global_objs and
  valid_global_vspace_mappings and
  pspace_in_kernel_window and
  cap_refs_in_kernel_window and
  pspace_respects_device_region and
  cap_refs_respects_device_region and cur_tcb and cur_sc_tcb"


locale InterruptAcc_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes dmo_maskInterrupt_invs:
    "\<And>irq state.
      \<lbrace>all_invs_but_valid_irq_states_for irq and (\<lambda>s. state = interrupt_states s irq)\<rbrace>
        do_machine_op (maskInterrupt (state = IRQInactive) irq)
      \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"

context InterruptAcc_AI begin

lemma set_irq_state_invs[wp]:
  "\<And>state irq.
    \<lbrace>\<lambda>s::'state_ext state. invs s
          \<and> (state \<noteq> irq_state.IRQSignal \<longrightarrow> cap.IRQHandlerCap irq \<notin> ran (caps_of_state s))\<rbrace>
      set_irq_state state irq
    \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: set_irq_state_def)
  apply (wp dmo_maskInterrupt_invs)
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def cur_sc_tcb_def sc_tcb_sc_at_def
                        valid_mdb_def all_invs_but_valid_irq_states_for_def mdb_cte_at_def
                        valid_irq_node_def valid_irq_handlers_def irq_issued_def)
  apply (rule conjI)
   apply (clarsimp simp: cap_irqs_def cap_irq_opt_def split: cap.split_asm)
  apply (clarsimp simp: valid_machine_state_def valid_irq_states_but_def valid_irq_masks_but_def,
            blast elim: valid_irq_statesE)
  done

end

lemmas ucast_ucast_mask8 = ucast_ucast_mask[where 'a=8, simplified, symmetric]

end
