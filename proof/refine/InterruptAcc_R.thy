(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory InterruptAcc_R
imports TcbAcc_R
begin

lemma get_irq_slot_corres:
  "corres (\<lambda>sl sl'. sl' = cte_map sl) \<top> \<top> (get_irq_slot irq) (getIRQSlot irq)"
  apply (simp add: getIRQSlot_def get_irq_slot_def locateSlot_conv
                   liftM_def[symmetric])
  apply (simp add: getInterruptState_def)
  apply (clarsimp simp: state_relation_def interrupt_state_relation_def)
  apply (simp add: cte_map_def cte_level_bits_def
                   ucast_nat_def shiftl_t2n)
  done

crunch inv[wp]: get_irq_slot "P"
crunch inv[wp]: getIRQSlot "P"

lemma set_irq_state_corres:
  "irq_state_relation state state' \<Longrightarrow>
   corres dc \<top> \<top> (set_irq_state state irq) (setIRQState state' irq)"
  apply (simp add: set_irq_state_def setIRQState_def
                   bind_assoc[symmetric])
  apply (subgoal_tac "(state = irq_state.IRQInactive) = (state' = irqstate.IRQInactive)")
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor)
        apply (rule corres_machine_op)
        apply (rule corres_Id | simp)+
        apply (rule no_fail_maskInterrupt)
       apply (simp add: getInterruptState_def setInterruptState_def
                        simpler_gets_def simpler_modify_def bind_def)
       apply (simp add: simpler_modify_def[symmetric])
       apply (rule corres_trivial, rule corres_modify)
       apply (simp add: state_relation_def swp_def)
       apply (clarsimp simp: interrupt_state_relation_def)
      apply (wp | simp)+
  apply (clarsimp simp: irq_state_relation_def
                 split: irq_state.split_asm irqstate.split_asm)
  done

lemma setIRQState_invs[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (state \<noteq> IRQNotifyAEP \<longrightarrow> IRQHandlerCap irq \<notin> ran (cteCaps_of s)) \<and> (state \<noteq> IRQInactive \<longrightarrow> irq \<le> maxIRQ)\<rbrace>
      setIRQState state irq
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setIRQState_def setInterruptState_def getInterruptState_def)
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs'_def valid_state'_def cur_tcb'_def
                        Invariants_H.valid_queues_def valid_queues'_def
                        valid_idle'_def valid_irq_node'_def
                        valid_arch_state'_def valid_global_refs'_def
                        global_refs'_def valid_machine_state'_def
                        if_unsafe_then_cap'_def ex_cte_cap_to'_def
                        valid_irq_handlers'_def irq_issued'_def
                        cteCaps_of_def valid_irq_masks'_def
                        bitmapQ_defs valid_queues_no_bitmap_def)
  apply (rule conjI, clarsimp)
  apply (clarsimp simp: irqs_masked'_def ct_not_inQ_def)
  apply (rule conjI)
   apply fastforce
  apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma getIRQSlot_real_cte[wp]:
  "\<lbrace>invs'\<rbrace> getIRQSlot irq \<lbrace>real_cte_at'\<rbrace>"
  apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
  apply wp
  apply (clarsimp simp: invs'_def valid_state'_def valid_irq_node'_def
                        cte_level_bits_def ucast_nat_def)
  done

lemma getIRQSlot_cte_at[wp]:
  "\<lbrace>invs'\<rbrace> getIRQSlot irq \<lbrace>cte_at'\<rbrace>"
  apply (rule hoare_strengthen_post [OF getIRQSlot_real_cte])
  apply (clarsimp simp: real_cte_at')
  done

end
