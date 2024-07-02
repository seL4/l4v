(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchADT_IF_Refine
imports ADT_IF_Refine
begin

context Arch begin global_naming RISCV64

named_theorems ADT_IF_Refine_assms

defs arch_extras_def:
  "arch_extras \<equiv> \<lambda>s. True"

declare arch_extras_def[simp]

lemma kernelEntry_invs'[ADT_IF_Refine_assms, wp]:
  "\<lbrace>invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)
          and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
          and arch_extras\<rbrace>
   kernelEntry_if e tc
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: kernelEntry_if_def)
  apply (wp threadSet_invs_trivial threadSet_ct_running' hoare_weak_lift_imp
         | wp (once) hoare_drop_imps
         | clarsimp)+
  done

lemma kernelEntry_arch_extras[ADT_IF_Refine_assms, wp]:
  "\<lbrace>invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)
          and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
          and arch_extras\<rbrace>
   kernelEntry_if e tc
   \<lbrace>\<lambda>_. arch_extras\<rbrace>"
  apply (simp add: kernelEntry_if_def)
  apply (wp threadSet_invs_trivial threadSet_ct_running' hoare_weak_lift_imp
         | wp (once) hoare_drop_imps
         | clarsimp)+
  done

crunch threadSet
  for arch_extras[ADT_IF_Refine_assms, wp]: "arch_extras"

lemma arch_tcb_context_set_tcb_relation[ADT_IF_Refine_assms]:
  "tcb_relation tcb tcb'
   \<Longrightarrow> tcb_relation (tcb\<lparr>tcb_arch := arch_tcb_context_set tc (tcb_arch tcb)\<rparr>)
                    (tcbArch_update (atcbContextSet tc) tcb')"
  by (simp add: tcb_relation_def arch_tcb_relation_def arch_tcb_context_set_def atcbContextSet_def)

lemma arch_tcb_context_get_atcbContextGet[ADT_IF_Refine_assms]:
  "tcb_relation tcb tcb'
   \<Longrightarrow> (arch_tcb_context_get \<circ> tcb_arch) tcb = (atcbContextGet \<circ> tcbArch) tcb'"
  by (simp add: tcb_relation_def arch_tcb_relation_def arch_tcb_context_get_def atcbContextGet_def)

definition
  "ptable_attrs_s' s \<equiv> ptable_attrs (ksCurThread s) (absKState s)"

definition
  "ptable_xn_s' s \<equiv>  \<lambda>addr. Execute \<notin> ptable_attrs_s' s addr"

definition doUserOp_if ::
  "user_transition_if \<Rightarrow> user_context \<Rightarrow> (event option \<times> user_context) kernel" where
  "doUserOp_if uop tc \<equiv>
  do pr \<leftarrow> gets ptable_rights_s';
     pxn \<leftarrow> gets (\<lambda>s x. pr x \<noteq> {} \<and> ptable_xn_s' s x);
     pl \<leftarrow> gets (\<lambda>s. ptable_lift_s' s |` {x. pr x \<noteq> {}});
     allow_read \<leftarrow> return {y. \<exists>x. pl x = Some y \<and> AllowRead \<in> pr x};
     allow_write \<leftarrow> return {y. \<exists>x. pl x = Some y \<and> AllowWrite \<in> pr x};
     t \<leftarrow> getCurThread;
     um \<leftarrow> gets (\<lambda>s. (user_mem' s \<circ> ptrFromPAddr));
     dm \<leftarrow> gets (\<lambda>s. (device_mem' s \<circ> ptrFromPAddr));
     ds \<leftarrow> gets (device_state \<circ> ksMachineState);
     assert (dom (um \<circ> addrFromPPtr) \<subseteq> - dom ds);
     assert (dom (dm \<circ> addrFromPPtr) \<subseteq> dom ds);
     u \<leftarrow>
       return
        (uop t pl pr pxn
          (tc, um |` allow_read,
           (ds \<circ> ptrFromPAddr) |` allow_read));
     assert (u \<noteq> {});
     (e, tc', um',ds') \<leftarrow> select u;
     doMachineOp
      (user_memory_update
        ((um' |` allow_write \<circ> addrFromPPtr) |` (- (dom ds))));
     doMachineOp
      (device_memory_update
          ((ds' |` allow_write \<circ> addrFromPPtr) |` dom ds));
     return (e, tc')
  od"

lemma ptable_attrs_abs_state[simp]:
  "ptable_attrs thread (abs_state s) = ptable_attrs thread s"
  by (simp add: ptable_attrs_def abs_state_def)

lemma doUserOp_if_empty_fail[ADT_IF_Refine_assms]:
  "empty_fail (doUserOp_if uop tc)"
  apply (simp add: doUserOp_if_def)
  apply (wp (once))
   apply wp
  apply (wp (once))
   apply wp
  apply (wp (once))
   apply wp
  apply (wp (once))
   apply wp
  apply (wp (once))
   apply wp
  apply (wp (once))
   apply wp
  apply (wp (once))
   apply wp
  apply (wp (once))
   apply wp
  apply (wp (once))
   apply wp
  apply (subst bind_assoc[symmetric])
  apply (rule empty_fail_bind)
   apply (rule empty_fail_select_bind)
  apply (wp | wpc)+
  done

lemma do_user_op_if_corres[ADT_IF_Refine_assms]:
  "corres (=) (einvs and ct_running and (\<lambda>_. \<forall>t pl pr pxn tcu. f t pl pr pxn tcu \<noteq> {}))
              (invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running')
              (do_user_op_if f tc) (doUserOp_if f tc)"
  apply (rule corres_gen_asm)
  apply (simp add: do_user_op_if_def doUserOp_if_def)
  apply (rule corres_gets_same)
    apply (clarsimp simp: ptable_rights_s_def ptable_rights_s'_def)
    apply (subst absKState_correct, fastforce, assumption+)
    apply (clarsimp elim!: state_relationE)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: ptable_attrs_s'_def ptable_attrs_s_def ptable_xn_s'_def ptable_xn_s_def)
    apply (subst absKState_correct, fastforce, assumption+)
    apply (clarsimp elim!: state_relationE)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: absArchState_correct curthread_relation ptable_lift_s'_def
                         ptable_lift_s_def)
    apply (subst absKState_correct, fastforce, assumption+)
    apply (clarsimp elim!: state_relationE)
   apply simp
  apply (simp add: getCurThread_def)
  apply (rule corres_gets_same)
    apply (simp add: curthread_relation)
   apply simp
  apply (rule corres_gets_same[where R ="\<lambda>r s. dom (r \<circ> addrFromPPtr) \<subseteq> - device_region s"])
    apply (clarsimp simp add: user_mem_relation dest!: invs_valid_stateI invs_valid_stateI')
   apply (clarsimp simp: invs_def valid_state_def pspace_respects_device_region_def)
   apply fastforce
  apply (rule corres_gets_same[where R ="\<lambda>r s. dom (r \<circ> addrFromPPtr) \<subseteq> device_region s"])
    apply (clarsimp simp add: device_mem_relation dest!: invs_valid_stateI invs_valid_stateI')
   apply (clarsimp simp: invs_def valid_state_def pspace_respects_device_region_def)
   apply fastforce
  apply (rule corres_gets_same[where R ="\<lambda>r s. dom r = device_region s"])
    apply (clarsimp simp: state_relation_def)
   apply simp
  apply (rule corres_assert_imp_r)
   apply fastforce
  apply (rule corres_assert_imp_r)
   apply fastforce
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=)"])
       apply (clarsimp simp: select_def corres_underlying_def)
      apply clarsimp
      apply (rule corres_split[OF corres_machine_op,where r'="(=)"])
         apply (rule corres_underlying_trivial)
         apply (clarsimp simp: user_memory_update_def)
         apply (rule no_fail_modify)
        apply (rule corres_split[OF corres_machine_op,where r'="(=)"])
           apply (rule corres_underlying_trivial)
           apply wp
          apply (rule corres_trivial, clarsimp)
          apply (wp hoare_TrueI[where P = \<top>] | simp)+
  done

lemma doUserOp_if_invs'[ADT_IF_Refine_assms, wp]:
  "\<lbrace>invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running' and ex_abs (einvs)\<rbrace>
   doUserOp_if f tc
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: doUserOp_if_def split_def ex_abs_def)
  apply (wp device_update_invs' dmo_invs' | simp)+
         apply (clarsimp simp add: no_irq_modify user_memory_update_def)
         apply wpsimp
        apply wp+
  apply (clarsimp simp: user_memory_update_def simpler_modify_def
                        restrict_map_def
                 split: option.splits)
  apply (auto dest: ptable_rights_imp_UserData[rotated 2]
              simp: ptable_rights_s'_def ptable_lift_s'_def)
  done

lemma doUserOp_valid_duplicates[ADT_IF_Refine_assms, wp]:
  "doUserOp_if f tc \<lbrace>arch_extras\<rbrace>"
  apply (simp add: doUserOp_if_def split_def)
  apply (wp dmo_invs' | simp)+
  done

lemma doUserOp_if_schedact[ADT_IF_Refine_assms, wp]:
  "doUserOp_if f tc \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: doUserOp_if_def)
  apply (wp | wpc | simp)+
  done

lemma doUserOp_if_st_tcb_at[ADT_IF_Refine_assms, wp]:
   "doUserOp_if f tc \<lbrace>st_tcb_at' st t\<rbrace>"
  apply (simp add: doUserOp_if_def)
  apply (wp | wpc | simp)+
  done

lemma doUserOp_if_cur_thread[ADT_IF_Refine_assms, wp]:
  "doUserOp_if f tc \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>"
  apply (simp add: doUserOp_if_def)
  apply (wp | wpc | simp)+
  done

lemma do_user_op_if_corres'[ADT_IF_Refine_assms]:
  "corres_underlying state_relation nf False (=) (einvs and ct_running)
     (invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running')
     (do_user_op_if f tc) (doUserOp_if f tc)"
  apply (simp add: do_user_op_if_def doUserOp_if_def)
  apply (rule corres_gets_same)
    apply (clarsimp simp: ptable_rights_s_def ptable_rights_s'_def)
    apply (subst absKState_correct, fastforce, assumption+)
    apply (clarsimp elim!: state_relationE)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: ptable_attrs_s'_def ptable_attrs_s_def ptable_xn_s'_def ptable_xn_s_def)
    apply (subst absKState_correct, fastforce, assumption+)
    apply (clarsimp elim!: state_relationE)
   apply simp
  apply (rule corres_gets_same)
    apply (clarsimp simp: absArchState_correct curthread_relation ptable_lift_s'_def
                         ptable_lift_s_def)
    apply (subst absKState_correct, fastforce, assumption+)
    apply (clarsimp elim!: state_relationE)
   apply simp
  apply (simp add: getCurThread_def)
  apply (rule corres_gets_same)
    apply (simp add: curthread_relation)
   apply simp
  apply (rule corres_gets_same[where R ="\<lambda>r s. dom (r \<circ> addrFromPPtr) \<subseteq> - device_region s"])
    apply (clarsimp simp add: user_mem_relation dest!: invs_valid_stateI invs_valid_stateI')
   apply (clarsimp simp: invs_def valid_state_def pspace_respects_device_region_def)
   apply fastforce
  apply (rule corres_gets_same[where R ="\<lambda>r s. dom (r \<circ> addrFromPPtr) \<subseteq> device_region s"])
    apply (clarsimp simp add: device_mem_relation dest!: invs_valid_stateI invs_valid_stateI')
   apply (clarsimp simp: invs_def valid_state_def pspace_respects_device_region_def dom_def)
  apply (rule corres_gets_same[where R ="\<lambda>r s. dom r = device_region s"])
    apply (clarsimp simp: state_relation_def)
   apply simp
  apply (rule corres_assert_imp_r)
   apply fastforce
  apply (rule corres_assert_imp_r)
   apply fastforce
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="dc"])
       apply (rule corres_assert')
      apply simp
      apply (rule corres_split[where r'="(=)"])
         apply (clarsimp simp: select_def corres_underlying_def)
        apply clarsimp
        apply (rule corres_split[OF corres_machine_op',where r'="(=)"])
           apply (rule corres_underlying_trivial, clarsimp)
          apply (rule corres_split[OF corres_machine_op', where r'="(=)"])
             apply (rule corres_underlying_trivial, clarsimp)
            apply (rule corres_trivial, clarsimp)
           apply (wp hoare_TrueI[where P = \<top>] | simp)+
   apply force
  apply force
  done

lemma getActiveIRQ_nf:
  "no_fail (\<lambda>_. True) (getActiveIRQ in_kernel)"
  apply (simp add: getActiveIRQ_def)
  apply (rule no_fail_pre)
   apply (rule no_fail_gets no_fail_modify
               no_fail_return | rule no_fail_bind | simp
          | intro impI conjI)+
     apply (wp del: no_irq | simp)+
  done

lemma dmo_getActiveIRQ_corres[ADT_IF_Refine_assms]:
  "corres (=) \<top> \<top> (do_machine_op (getActiveIRQ in_kernel)) (doMachineOp (getActiveIRQ in_kernel'))"
  apply (rule SubMonad_R.corres_machine_op)
  apply (rule corres_Id)
    apply (simp add: getActiveIRQ_def non_kernel_IRQs_def)
   apply simp
  apply (rule getActiveIRQ_nf)
  done

lemma dmo'_getActiveIRQ_wp[ADT_IF_Refine_assms]:
  "\<lbrace>\<lambda>s. P (irq_at (irq_state (ksMachineState s) + 1) (irq_masks (ksMachineState s)))
          (s\<lparr>ksMachineState := (ksMachineState s\<lparr>irq_state := irq_state (ksMachineState s) + 1\<rparr>)\<rparr>)\<rbrace>
   doMachineOp (getActiveIRQ in_kernel)
   \<lbrace>P\<rbrace>"
  apply(simp add: doMachineOp_def getActiveIRQ_def non_kernel_IRQs_def)
  apply(wp modify_wp | wpc)+
  apply clarsimp
  apply(erule use_valid)
   apply (wp modify_wp)
  apply(auto simp: irq_at_def)
  done

lemma scheduler_if'_arch_extras[ADT_IF_Refine_assms, wp]:
  "\<lbrace>invs' and arch_extras\<rbrace>
   schedule'_if tc
   \<lbrace>\<lambda>_. arch_extras\<rbrace>"
  apply (simp add: schedule'_if_def)
  apply (wp hoare_drop_imps | simp)+
  done

lemma handlePreemption_if_arch_extras[ADT_IF_Refine_assms, wp]:
  "handlePreemption_if tc \<lbrace>arch_extras\<rbrace>"
  apply (simp add: handlePreemption_if_def)
  apply (wp dmo'_getActiveIRQ_wp hoare_drop_imps)
  done

lemma handle_preemption_if_corres[ADT_IF_Refine_assms]:
  "corres (=) (einvs and valid_domain_list and (\<lambda>s. 0 < domain_time s))
              (invs') (handle_preemption_if tc) (handlePreemption_if tc)"
  apply (simp add: handlePreemption_if_def handle_preemption_if_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=)"])
       apply (rule dmo_getActiveIRQ_corres)
      apply (rule corres_split[where r'="dc"])
         apply (rule corres_when)
          apply simp
         apply simp
         apply (rule handleInterrupt_corres)
        apply (rule corres_stateAssert_assume_stronger[where Q=\<top> and
                      P="\<lambda>s. valid_domain_list s \<and>
                             (domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread)"])
         apply simp
        apply (clarsimp simp: state_relation_def)
       apply (wp handle_interrupt_valid_domain_time)+
     apply (rule dmo_getActiveIRQ_wp)
    apply (rule dmo'_getActiveIRQ_wp)
   apply clarsimp+
  apply (clarsimp simp: invs'_def valid_state'_def irq_at_def invs_def
                        Let_def valid_irq_states'_def)
  done

crunch doUserOp_if
  for ksDomainTime_inv[ADT_IF_Refine_assms, wp]: "\<lambda>s. P (ksDomainTime s)"
  and ksDomSchedule_inv[ADT_IF_Refine_assms, wp]: "\<lambda>s. P (ksDomSchedule s)"

crunch checkActiveIRQ_if
  for arch_extras[ADT_IF_Refine_assms, wp]: arch_extras

lemma valid_device_abs_state_eq[ADT_IF_Refine_assms]:
  "valid_machine_state s \<Longrightarrow> abs_state s = s"
  apply (simp add: abs_state_def observable_memory_def)
  apply (case_tac s)
  apply clarsimp
  apply (case_tac machine_state)
  apply clarsimp
  apply (rule ext)
  apply (fastforce simp: user_mem_def option_to_0_def valid_machine_state_def)
  done

lemma doUserOp_if_no_interrupt[ADT_IF_Refine_assms]:
  "\<lbrace>K (uop_sane uop)\<rbrace>
   doUserOp_if uop tc
   \<lbrace>\<lambda>r s. (fst r) \<noteq> Some Interrupt\<rbrace>"
  apply (simp add: doUserOp_if_def del: split_paired_All)
  apply (wp | wpc)+
  apply (clarsimp simp: uop_sane_def simp del: split_paired_All)
  done

lemma handleEvent_corres_arch_extras[ADT_IF_Refine_assms]:
    "corres (dc \<oplus> dc)
       (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and schact_is_rct)
       (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s)
              and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
              and arch_extras)
       (handle_event event) (handleEvent event)"
  by (fastforce intro: corres_guard2_imp[OF handleEvent_corres])

end

requalify_consts
  RISCV64.doUserOp_if


global_interpretation ADT_IF_Refine_1?: ADT_IF_Refine_1 doUserOp_if
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact ADT_IF_Refine_assms)?)
qed


sublocale valid_initial_state_noenabled \<subseteq> valid_initial_state_noenabled?:
  ADT_valid_initial_state_noenabled doUserOp_if ..

sublocale valid_initial_state_noenabled \<subseteq> valid_initial_state ..

end
