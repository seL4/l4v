(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
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

crunches modifyWorkUnits
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

context begin interpretation Arch . (*FIXME: arch_split*)

global_interpretation modifyWorkUnits: typ_at_all_props' "modifyWorkUnits f"
  by typ_at_props'

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
  "\<lbrace>\<lambda>s. invs' s \<and> (state \<noteq> IRQSignal \<longrightarrow> IRQHandlerCap irq \<notin> ran (cteCaps_of s)) \<and>
        (state \<noteq> IRQInactive \<longrightarrow> irq \<le> maxIRQ \<and> irq \<noteq> irqInvalid)\<rbrace>
      setIRQState state irq
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setIRQState_def setInterruptState_def getInterruptState_def)
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs'_def valid_dom_schedule'_def valid_irq_node'_def
                        valid_arch_state'_def valid_global_refs'_def
                        global_refs'_def valid_machine_state'_def
                        if_unsafe_then_cap'_def ex_cte_cap_to'_def
                        valid_irq_handlers'_def irq_issued'_def
                        cteCaps_of_def valid_irq_masks'_def
                        valid_bitmaps_def bitmapQ_defs irqs_masked'_def)
  apply fastforce
  done

lemma getIRQSlot_real_cte[wp]:
  "\<lbrace>invs'\<rbrace> getIRQSlot irq \<lbrace>real_cte_at'\<rbrace>"
  apply (simp add: getIRQSlot_def getInterruptState_def locateSlot_conv)
  apply wp
  apply (clarsimp simp: invs'_def valid_irq_node'_def
                        cte_level_bits_def ucast_nat_def cteSizeBits_def shiftl_t2n)
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

lemma update_work_units_corres[corres]:
  "corres (dc \<oplus> dc) \<top> \<top> (liftE update_work_units) (liftE (modifyWorkUnits (\<lambda>op. op + 1)))"
  apply (clarsimp simp: update_work_units_def modifyWorkUnits_def)
  apply (rule corres_modify)
  apply (clarsimp simp: state_relation_def)
  done

lemma getCurTime_corres[corres]:
  "corres (=) \<top> \<top> (gets cur_time) getCurTime"
  by (simp add: getCurTime_def state_relation_def)

lemma getDomainTime_corres[corres]:
  "corres (=) \<top> \<top> (gets domain_time) getDomainTime"
  by (simp add: getDomainTime_def state_relation_def)

lemma getCurTime_sp:
  "\<lbrace>P\<rbrace> getCurTime \<lbrace>\<lambda>rv s. rv = ksCurTime s \<and> P s\<rbrace>"
  by wpsimp

lemma updateTimeStamp_corres[corres]:
  "corres dc \<top> \<top> update_time_stamp updateTimeStamp"
  apply (clarsimp simp: update_time_stamp_def updateTimeStamp_def setConsumedTime_def)
  apply (prop_tac "minBudget = MIN_BUDGET")
   apply (clarsimp simp: minBudget_def MIN_BUDGET_def kernelWCETTicks_def)
  apply (rule corres_underlying_split[rotated 2, OF gets_sp getCurTime_sp])
   apply corresKsimp
  apply (rule corres_underlying_split[where r'="(=)"])
     apply (rule corres_guard_imp)
       apply (rule corres_machine_op)
       apply corresKsimp
        apply (wpsimp simp: getCurrentTime_def)
       apply simp
      apply simp
     apply simp
    apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
    apply (clarsimp simp: setCurTime_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF corres_modify])
         apply (clarsimp simp: state_relation_def cdt_relation_def)
        apply (clarsimp simp: setConsumedTime_def)
        apply (rule_tac Q'="\<lambda>rv s. rv = ksConsumedTime s" in corres_symb_exec_r)
           apply (rule corres_guard_imp)
             apply (rule corres_split[OF corres_modify])
                apply (simp add: state_relation_def cdt_relation_def)
               apply (rule corres_guard_imp)
                 apply (rule corres_rel_imp)
                  apply (rule corres_split[OF getDomainTime_corres])
                    apply (rule corres_when, rule refl)
                    apply (fastforce intro: setDomainTime_corres)
                   apply (wpsimp simp: getConsumedTime_def)+
  done

lemma no_ofail_readRefillHead[wp]:
  "no_ofail (sc_at' scPtr) (readRefillHead scPtr)"
  unfolding readRefillHead_def readSchedContext_def
  by (wpsimp wp_del: ovalid_readObject)

lemma no_ofail_readRefillCapacity[wp]:
  "no_ofail (sc_at' scPtr) (readRefillCapacity scPtr usage)"
  unfolding readRefillCapacity_def
  by wpsimp

lemma no_ofail_readRefillSufficient[wp]:
  "no_ofail (sc_at' scPtr) (readRefillSufficient scPtr usage)"
  unfolding readRefillSufficient_def
  by wpsimp

lemmas no_fail_getRefillSufficient[wp] =
  no_ofail_gets_the[OF no_ofail_readRefillSufficient, simplified getRefillSufficient_def[symmetric]]

lemma getRefillHead_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres (\<lambda>rv rv'. refill_map rv' = rv)
     (valid_objs and pspace_aligned and pspace_distinct
      and is_active_sc sc_ptr and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
     valid_objs'
     (get_refill_head sc_ptr) (getRefillHead scPtr)"
  apply (clarsimp simp: get_refill_head_def getRefillHead_def read_refill_head_def
                        readRefillHead_def getSchedContext_def[symmetric]
                        read_sched_context_get_sched_context
                        readSchedContext_def getObject_def[symmetric])
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF get_sc_corres])
      apply (rule corres_assert_assume_l)
      apply clarsimp
      apply (rule refill_hd_relation[symmetric])
       apply simp
      apply simp
     apply wpsimp
    apply wpsimp
   apply (clarsimp simp: sc_at_ppred_def obj_at_def is_sc_obj_def)
   apply (fastforce intro: valid_objs_valid_sched_context_size)
  apply clarsimp
  apply (frule (4) active_sc_at'_cross_valid_objs)
  by (fastforce dest: valid_objs'_valid_refills'
                simp: active_sc_at'_def obj_at'_def is_active_sc'_def in_omonad valid_refills'_def)

lemma getRefillCapacity_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres (=)
     (valid_objs and pspace_aligned and pspace_distinct
      and is_active_sc sc_ptr and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
     valid_objs'
     (get_sc_refill_capacity sc_ptr consumed) (getRefillCapacity scPtr consumed)"
  apply (clarsimp simp: get_sc_refill_capacity_def getRefillCapacity_def read_sc_refill_capacity_def
                        readRefillCapacity_def get_refill_head_def[symmetric]
                        getRefillHead_def[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getRefillHead_corres])
       apply simp
      apply (clarsimp simp: refillCapacity_def refill_capacity_def refill_map_def)
     apply wpsimp+
  done

lemma getRefillSufficient_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres (=)
     (valid_objs and pspace_aligned and pspace_distinct
      and is_active_sc sc_ptr and sc_refills_sc_at (\<lambda>refills. refills \<noteq> []) sc_ptr)
     valid_objs'
     (get_sc_refill_sufficient sc_ptr consumed) (getRefillSufficient scPtr consumed)"
  apply (clarsimp simp: get_sc_refill_sufficient_def getRefillSufficient_def
                        read_sc_refill_sufficient_def readRefillSufficient_def refill_sufficient_def
                        readRefillCapacity_def
                        get_refill_head_def[symmetric] getRefillHead_def[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getRefillHead_corres])
       apply simp
      apply (clarsimp simp: refillCapacity_def refill_capacity_def refill_map_def
                            minBudget_def MIN_BUDGET_def kernelWCETTicks_def)
     apply wpsimp+
  done

lemma modifyWorkUnits_valid_objs'[wp]:
  "modifyWorkUnits f \<lbrace>valid_objs'\<rbrace>"
  apply (clarsimp simp: modifyWorkUnits_def)
  apply wpsimp
  done

lemma setWorkUnits_corres[corres]:
  "corres dc \<top> \<top> reset_work_units (setWorkUnits 0)"
  apply (clarsimp simp: reset_work_units_def setWorkUnits_def)
  apply (rule corres_modify)
  apply (clarsimp simp: state_relation_def)
  done

crunches updateTimeStamp
  for valid_objs'[wp]: valid_objs'

lemma getCurSc_sp:
  "\<lbrace>P\<rbrace> getCurSc \<lbrace>\<lambda>rv s. rv = ksCurSc s \<and> P s\<rbrace>"
  by (wpsimp wp: getCurSc_def)

lemma getConsumedTime_sp:
  "\<lbrace>P\<rbrace> getConsumedTime \<lbrace>\<lambda>rv s. rv = ksConsumedTime s \<and> P s\<rbrace>"
  by wpsimp

lemma scActive_corres:
  "sc_ptr = scPtr \<Longrightarrow>
   corres (=) (sc_at scPtr and pspace_aligned and pspace_distinct) \<top>
     (get_sc_active sc_ptr) (scActive scPtr)"
  apply (rule corres_cross[where Q' = "sc_at' scPtr", OF sc_at'_cross_rel])
   apply (fastforce simp: obj_at_def is_sc_obj_def valid_obj_def valid_pspace_def sc_at_pred_n_def)
  apply (clarsimp simp: get_sc_active_def read_sc_active_def read_sched_context_get_sched_context
                        readScActive_def readSchedContext_def getObject_def[symmetric]
                        getSchedContext_def[symmetric] scActive_def)
  apply (corres corres: get_sc_corres simp: sc_relation_def scActive_def active_sc_def)
  done

lemma getConsumedTime_corres[corres]:
  "corres (=) \<top> \<top> (gets consumed_time) getConsumedTime"
  apply (simp add: getConsumedTime_def state_relation_def)
  done

lemma isCurDomainExpired_corres[corres]:
  "corres (=) \<top> \<top> (gets is_cur_domain_expired) isCurDomainExpired"
  apply (simp add: is_cur_domain_expired_def isCurDomainExpired_def getDomainTime_def
                   getConsumedTime_def)
  apply (clarsimp simp: corres_underlying_def gets_def bind_def get_def return_def
                        state_relation_def)
  done

lemma get_sc_active_sp:
  "\<lbrace>P\<rbrace>
   get_sc_active sc_ptr
   \<lbrace>\<lambda>rv s. P s
           \<and> (\<exists>sc n. ko_at (kernel_object.SchedContext sc n) sc_ptr s \<and> rv = (0 < sc_refill_max sc))\<rbrace>"
  apply wpsimp
  apply (clarsimp simp: obj_at_def active_sc_def)
  done

crunches updateTimeStamp, setWorkUnits, isCurDomainExpired
  for ksPSpace[wp]: "\<lambda>s. P (ksPSpace s)"
  and active_sc_at'[wp]: "active_sc_at' scPtr"
  and valid_objs'[wp]: valid_objs'
  and no_0_obj'[wp]: no_0_obj'
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  and scs_of'[wp]: "\<lambda>s. P (scs_of' s)"
  (simp: active_sc_at'_def crunch_simps getDomainTime_def setDomainTime_def setConsumedTime_def
         setCurTime_def)

crunches update_time_stamp
  for kheap[wp]: "\<lambda>s. P (kheap s)"
  (simp: crunch_simps)

crunch (no_fail) no_fail[wp]: getCurSc

lemma preemptionPoint_corres:
  "corres (dc \<oplus> dc)
     (valid_objs and cur_sc_tcb and pspace_aligned and pspace_distinct and active_scs_valid)
     valid_objs'
     preemption_point preemptionPoint"
  (is "corres _ ?abs ?conc _ _")
  supply if_split[split del]
  apply (simp add: preemption_point_def preemptionPoint_def)
  apply (rule corres_splitEE_skip;
         corresKsimp corres: update_work_units_corres
                       simp: update_work_units_def)
  apply (subst liftE_bindE[where a=getWorkUnits])
  apply (rule_tac Q'="\<lambda>rv s. rv = ksWorkUnitsCompleted s \<and> ?conc s"
               in corres_symb_exec_r[rotated])
     apply (wpsimp simp: getWorkUnits_def)+
  apply (rename_tac work_units)
  apply (clarsimp simp: OR_choiceE_def whenE_def work_units_limit_reached_def liftE_bindE)
  apply (rule_tac Q="\<lambda>rv s. rv = s \<and> ?abs s" in corres_symb_exec_l[rotated])
     apply wpsimp+
  apply (rename_tac ex)
  apply (rule_tac Q="\<lambda>s. ex = s \<and> work_units = work_units_completed s \<and> ?abs s"
              and Q'="\<lambda>s. work_units = ksWorkUnitsCompleted s \<and> valid_objs' s"
              in stronger_corres_guard_imp[rotated])
    apply (clarsimp simp: state_relation_def)
   apply simp
  apply (rule_tac Q="\<lambda>rv s. \<exists>rv'' t. rv = (rv'', s) \<and> rv'' = (workUnitsLimit \<le> work_units) \<and> ?abs s"
               in corres_symb_exec_l[rotated])
     apply (clarsimp simp: select_f_def mk_ef_def bind_def gets_def exs_valid_def get_def
                           return_def wrap_ext_bool_det_ext_ext_def)
    apply wpsimp
    apply (clarsimp simp: mk_ef_def bind_def gets_def get_def return_def work_units_limit_def
                          wrap_ext_bool_det_ext_ext_def Kernel_Config.workUnitsLimit_def)
   apply wpsimp
   apply (clarsimp simp: mk_ef_def bind_def gets_def get_def return_def
                         wrap_ext_bool_det_ext_ext_def)
  apply (case_tac rv; clarsimp)
  apply (rule corres_if_strong')
    apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF setWorkUnits_corres])
       apply (rule corres_split[OF updateTimeStamp_corres])
         apply (rule corres_split[OF corres_machine_op])
            apply corres
           apply (rule corres_split[OF isCurDomainExpired_corres])
             apply (rule corres_split[OF getCurSc_corres], clarsimp, rename_tac csc)
               apply (clarsimp simp: stateAssertE_def)
               apply (subst liftE_bindE)
               apply (rule_tac P'="\<lambda>s. csc = cur_sc s \<and> sc_at csc s" in corres_stateAssert_implied)
                apply (rule corres_split[OF getConsumedTime_corres])
                  apply (clarsimp simp: andM_def ifM_def bind_assoc)
                  apply (rule corres_split[OF scActive_corres], rule refl, rename_tac active)
                    apply clarsimp
                    apply (rule_tac R=active in corres_cases'; clarsimp)
                     apply (rule_tac R="\<top>\<top>" and R'="\<top>\<top>" in corres_split)
                        apply (rule corres_gets_the_gets)
                        apply (simp flip: get_sc_refill_sufficient_def)
                        apply (rule getRefillSufficient_corres, simp)
                       apply (fastforce intro: corres_returnOkTT split: if_splits)
                      apply wpsimp+
                    apply (rule_tac Q="\<top>\<top>" and P'=\<top> in corres_symb_exec_l)
                       apply fastforce
                      apply wpsimp+
               apply (fastforce intro!: sc_at_cross simp: sc_at'_asrt_def)
              apply wpsimp
             apply (rule_tac Q="\<lambda>_. valid_objs'" in hoare_post_imp)
              apply fastforce
             apply wpsimp+
        apply (rule_tac Q="\<lambda>_ s. sc_at (cur_sc s) s \<and> pspace_aligned s \<and> pspace_distinct s
                                 \<and> valid_objs s \<and> active_scs_valid s"
                     in hoare_post_imp)
         apply (fastforce intro!: valid_refills_nonempty_refills active_scs_validE
                            simp: vs_all_heap_simps)
        apply ((wpsimp | wps)+)[1]
       apply (wpsimp simp: reset_work_units_def)+
    apply (fastforce intro!: cur_sc_tcb_sc_at_cur_sc)
   apply clarsimp
  apply (corres corres: corres_returnOkTT)
  done

lemma updateTimeStamp_inv:
   "\<lbrakk>updateTimeStamp_independent P; time_state_independent_H P; getCurrentTime_independent_H P;
     domain_time_independent_H P\<rbrakk>
    \<Longrightarrow> updateTimeStamp \<lbrace>P\<rbrace>"
  apply (simp add: updateTimeStamp_def doMachineOp_def getCurrentTime_def)
  apply (rule bind_wp_fwd_skip, wpsimp)
  apply (rule bind_wp_fwd_skip, wpsimp)
   apply (fastforce simp: time_state_independent_H_def getCurrentTime_independent_H_def in_monad)
  apply (rule bind_wp_fwd_skip, wpsimp simp: setCurTime_def)
   apply (clarsimp simp: updateTimeStamp_independent_def)
   apply (drule_tac x="\<lambda>_. curTime'" in spec)
   apply (drule_tac x=id in spec)
   apply fastforce
  apply (wpsimp simp: setConsumedTime_def setDomainTime_def getDomainTime_def)
  apply (clarsimp simp: updateTimeStamp_independent_def)
  apply (drule_tac x=id in spec)
  apply (fastforce simp: update_time_stamp_independent_A_def domain_time_independent_H_def)
  done

lemma getDomainTime_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksDomainTime s) s \<rbrace> getDomainTime \<lbrace> P \<rbrace>"
  unfolding getDomainTime_def
  by wp

lemma preemptionPoint_inv:
  assumes "(\<And>f s. P (ksWorkUnitsCompleted_update f s) = P s)"
          "irq_state_independent_H P"
          "updateTimeStamp_independent P"
          "getCurrentTime_independent_H P"
          "time_state_independent_H P"
          "domain_time_independent_H P"
  shows "preemptionPoint \<lbrace>P\<rbrace>"
  using assms
  apply (simp add: preemptionPoint_def setWorkUnits_def getWorkUnits_def modifyWorkUnits_def)
  by (wpsimp simp: isCurDomainExpired_def stateAssertE_def
               wp: getDomainTime_wp updateTimeStamp_inv hoare_drop_imps)

lemma ct_in_state_machine_state_independent[intro!, simp]:
  "ct_in_state P (machine_state_update f s) = ct_in_state P s"
  by (simp add: ct_in_state_def)

lemma typ_at'_irq_state_independent[simp, intro!]:
  "P (typ_at' T p (s \<lparr>ksMachineState := ksMachineState s \<lparr> irq_state := f (irq_state (ksMachineState s)) \<rparr>\<rparr>))
   = P (typ_at' T p s)"
  by (simp add: typ_at'_def)

lemma sch_act_simple_irq_state_independent[intro!, simp]:
  "sch_act_simple (s \<lparr> ksMachineState := ksMachineState s \<lparr> irq_state := f (irq_state (ksMachineState s)) \<rparr> \<rparr>) =
   sch_act_simple s"
  by (simp add: sch_act_simple_def)

method invs'_independent_method
  = clarsimp simp: irq_state_independent_H_def invs'_def
                   valid_pspace'_def valid_replies'_def
                   if_live_then_nonz_cap'_def if_unsafe_then_cap'_def
                   valid_global_refs'_def
                   valid_arch_state'_def valid_irq_node'_def
                   valid_irq_handlers'_def valid_irq_states'_def
                   irqs_masked'_def valid_bitmaps_def bitmapQ_defs
                   pspace_domain_valid_def
                   valid_machine_state'_def ex_cte_cap_wp_to'_def
                   valid_mdb'_def
                   valid_dom_schedule'_def
             cong: if_cong option.case_cong

lemma
  shows invs'_irq_state_independent [simp, intro!]:
  "invs' (s\<lparr>ksMachineState := ksMachineState s
                 \<lparr>irq_state := f (irq_state (ksMachineState s))\<rparr>\<rparr>)
   = invs' s"
  and invs'_updateTimeStamp_independent [simp, intro!]:
  "invs' (s\<lparr>ksCurTime := f' (ksCurTime s), ksConsumedTime := g (ksConsumedTime s)\<rparr>)
   = invs' s"
  and invs'_getCurrentTime_independent [simp, intro!]:
  "invs' (s\<lparr>ksMachineState
            := ksMachineState s \<lparr>last_machine_time
                                 := f'' (last_machine_time (ksMachineState s)) (time_state (ksMachineState s))\<rparr>\<rparr>)
   = invs' s"
  and invs'_time_state_independent [simp, intro!]:
  "invs' (s\<lparr>ksMachineState := ksMachineState s \<lparr>time_state := f''' (time_state (ksMachineState s))\<rparr>\<rparr>)
   = invs' s"
  by invs'_independent_method+

lemma preemptionPoint_invs [wp]:
  "\<lbrace>invs'\<rbrace> preemptionPoint \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wp preemptionPoint_inv | clarsimp)+

end
end
