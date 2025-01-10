(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory InterruptAcc_R
imports TcbAcc_R
begin

lemma getIRQSlot_corres:
  "corres (\<lambda>sl sl'. sl' = cte_map sl) \<top> \<top> (get_irq_slot irq) (getIRQSlot irq)"
  apply (simp add: getIRQSlot_def get_irq_slot_def locateSlot_conv
                   liftM_def[symmetric])
  apply (simp add: getInterruptState_def)
  apply (clarsimp simp: state_relation_def interrupt_state_relation_def)
  apply (simp add: cte_map_def cte_level_bits_def
                   ucast_nat_def shiftl_t2n)
  done

crunch get_irq_slot
  for inv[wp]: "P"
crunch getIRQSlot
  for inv[wp]: "P"

context begin interpretation Arch . (*FIXME: arch-split*)

lemma setIRQState_corres:
  "irq_state_relation state state' \<Longrightarrow>
   corres dc \<top> \<top> (set_irq_state state irq) (setIRQState state' irq)"
  apply (simp add: set_irq_state_def setIRQState_def
                   bind_assoc[symmetric])
  apply (subgoal_tac "(state = irq_state.IRQInactive) = (state' = irqstate.IRQInactive)")
   apply (rule corres_guard_imp)
     apply (rule corres_split_nor)
        apply (simp add: getInterruptState_def setInterruptState_def
                         simpler_gets_def simpler_modify_def bind_def)
        apply (simp add: simpler_modify_def[symmetric])
        apply (rule corres_trivial, rule corres_modify)
        apply (simp add: state_relation_def swp_def)
        apply (clarsimp simp: interrupt_state_relation_def)
       apply (rule corres_machine_op)
       apply (rule corres_Id | simp)+
       apply (rule no_fail_maskInterrupt)
      apply (wp | simp)+
  apply (clarsimp simp: irq_state_relation_def
                 split: irq_state.split_asm irqstate.split_asm)
  done

lemma setIRQState_invs[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> (state \<noteq> IRQSignal \<longrightarrow> IRQHandlerCap irq \<notin> ran (cteCaps_of s)) \<and> (state \<noteq> IRQInactive \<longrightarrow> irq \<le> maxIRQ)\<rbrace>
      setIRQState state irq
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setIRQState_def setInterruptState_def getInterruptState_def)
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs'_def valid_state'_def cur_tcb'_def
                        valid_idle'_def valid_irq_node'_def
                        valid_arch_state'_def valid_global_refs'_def
                        global_refs'_def valid_machine_state'_def
                        if_unsafe_then_cap'_def ex_cte_cap_to'_def
                        valid_irq_handlers'_def irq_issued'_def
                        cteCaps_of_def valid_irq_masks'_def
                        bitmapQ_defs valid_bitmaps_def
                  split: option.splits)
   apply (rule conjI, clarsimp)
   apply (clarsimp simp: irqs_masked'_def ct_not_inQ_def)
   apply (rule conjI)
    apply fastforce
   apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
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
                        cte_level_bits_def ucast_nat_def cteSizeBits_def shiftl_eq_mult mult.commute)
  done

lemma getIRQSlot_cte_at[wp]:
  "\<lbrace>invs'\<rbrace> getIRQSlot irq \<lbrace>cte_at'\<rbrace>"
  apply (rule hoare_strengthen_post [OF getIRQSlot_real_cte])
  apply (clarsimp simp: real_cte_at')
  done

lemma work_units_updated_state_relationI[intro!]:
  "(s,s') \<in> state_relation \<Longrightarrow>
   (work_units_completed_update (\<lambda>_. work_units_completed s + 1) s, s'\<lparr>ksWorkUnitsCompleted := ksWorkUnitsCompleted s' + 1\<rparr>) \<in> state_relation"
  apply (simp add: state_relation_def)
  done

lemma work_units_and_irq_state_state_relationI [intro!]:
  "(s, s') \<in> state_relation \<Longrightarrow>
   (s \<lparr> work_units_completed := n,  machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr>\<rparr>,
    s' \<lparr> ksWorkUnitsCompleted := n, ksMachineState := ksMachineState s' \<lparr> irq_state := f (irq_state (ksMachineState s')) \<rparr>\<rparr>)
   \<in> state_relation"
  by (simp add: state_relation_def swp_def)

lemma preemptionPoint_corres:
  "corres (dc \<oplus> dc) \<top> \<top> preemption_point preemptionPoint"
  apply (simp add: preemption_point_def preemptionPoint_def)
  by (auto simp: preemption_point_def preemptionPoint_def o_def gets_def liftE_def whenE_def getActiveIRQ_def
                 corres_underlying_def select_def bind_def get_def bindE_def select_f_def modify_def
                 alternative_def throwError_def returnOk_def return_def lift_def doMachineOp_def split_def
                 put_def getWorkUnits_def setWorkUnits_def modifyWorkUnits_def do_machine_op_def

                 update_work_units_def wrap_ext_bool_det_ext_ext_def work_units_limit_def workUnitsLimit_def
                 work_units_limit_reached_def OR_choiceE_def reset_work_units_def mk_ef_def
           elim: state_relationE)
  (* what? *)
  (* who says our proofs are not automatic.. *)

lemma preemptionPoint_inv:
  assumes "(\<And>f s. P (ksWorkUnitsCompleted_update f s) = P s)"
          "irq_state_independent_H P"
  shows "\<lbrace>P\<rbrace> preemptionPoint \<lbrace>\<lambda>_. P\<rbrace>" using assms
  apply (simp add: preemptionPoint_def setWorkUnits_def getWorkUnits_def modifyWorkUnits_def)
  apply (wpc
          | wp whenE_wp bind_wp [OF _ select_inv] hoare_drop_imps
          | simp)+
  done

lemma ct_running_irq_state_independent[intro!, simp]:
  "ct_running (s \<lparr>machine_state := machine_state s \<lparr>irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr>)
   = ct_running s"
  by (simp add: ct_in_state_def)

lemma ct_idle_irq_state_independent[intro!, simp]:
  "ct_idle (s \<lparr>machine_state := machine_state s \<lparr>irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr>)
   = ct_idle s"
  by (simp add: ct_in_state_def)

lemma typ_at'_irq_state_independent[simp, intro!]:
  "P (typ_at' T p (s \<lparr>ksMachineState := ksMachineState s \<lparr> irq_state := f (irq_state (ksMachineState s)) \<rparr>\<rparr>))
   = P (typ_at' T p s)"
  by (simp add: typ_at'_def)

lemma sch_act_simple_irq_state_independent[intro!, simp]:
  "sch_act_simple (s \<lparr> ksMachineState := ksMachineState s \<lparr> irq_state := f (irq_state (ksMachineState s)) \<rparr> \<rparr>) =
   sch_act_simple s"
  by (simp add: sch_act_simple_def)

lemma invs'_irq_state_independent [simp, intro!]:
  "invs' (s\<lparr>ksMachineState := ksMachineState s
                 \<lparr>irq_state := f (irq_state (ksMachineState s))\<rparr>\<rparr>) =
   invs' s"
  apply (clarsimp simp: irq_state_independent_H_def invs'_def valid_state'_def
          valid_pspace'_def sch_act_wf_def
          valid_queues_def sym_refs_def state_refs_of'_def
          if_live_then_nonz_cap'_def if_unsafe_then_cap'_def
          valid_idle'_def valid_global_refs'_def
          valid_arch_state'_def valid_irq_node'_def
          valid_irq_handlers'_def valid_irq_states'_def
          irqs_masked'_def bitmapQ_defs valid_bitmaps_def
          valid_pde_mappings'_def
          pspace_domain_valid_def cur_tcb'_def
          valid_machine_state'_def tcb_in_cur_domain'_def
          ct_not_inQ_def ct_idle_or_in_cur_domain'_def
          cong: if_cong option.case_cong)
  apply (rule iffI[rotated])
   apply (clarsimp)
   apply (case_tac "ksSchedulerAction s", simp_all)
  apply clarsimp
  apply (case_tac "ksSchedulerAction s", simp_all)
  done

lemma preemptionPoint_invs [wp]:
  "\<lbrace>invs'\<rbrace> preemptionPoint \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wp preemptionPoint_inv | clarsimp)+

end
end
