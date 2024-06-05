(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ADT_IF_Refine
imports "InfoFlow.ArchADT_IF" "Refine.EmptyFail_H"
begin

definition kernelEntry_if where
  "kernelEntry_if e tc \<equiv> do
     t \<leftarrow> getCurThread;
     threadSet (tcbArch_update (atcbContextSet tc)) t;
     r \<leftarrow> handleEvent e;
     stateAssert
       (\<lambda>s. valid_domain_list' s \<and> (e \<noteq> Interrupt \<longrightarrow> 0 < ksDomainTime s) \<and>
            (e = Interrupt \<longrightarrow> ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread)) [];
     return (r,tc)
   od"

crunch kernelEntry_if
  for (empty_fail) empty_fail

definition kernelExit_if where
  "kernelExit_if tc \<equiv> do
     t' \<leftarrow> getCurThread;
     threadGet (atcbContextGet o tcbArch) t'
   od"

definition kernelExit_H_if where
  "kernelExit_H_if \<equiv>
     {(s, m, s'). s' \<in> fst (split kernelExit_if s) \<and>
                  m = (if ct_running' (snd s') then InUserMode else InIdleMode)}"

definition has_srel_state where
  "has_srel_state srel P \<equiv> {s. \<exists>s'. (s,s') \<in> srel \<and> s' \<in> P}"

definition lift_fst_rel where
  "lift_fst_rel srel \<equiv> {(r,r'). snd r = snd r' \<and> (fst r, fst r') \<in> srel}"

(* Includes serializability *)
definition step_corres where
  "step_corres nf sr mode G G' \<equiv> \<lambda>ma mc.
     \<forall>(s,s')\<in>sr. (s',mode) \<in> G' \<and> (s,mode) \<in> G
                  \<longrightarrow> ((nf \<longrightarrow> (\<exists>e' t'. (s',e',t') \<in> mc)) \<and>
                       (\<forall>e' t'. (s',e',t') \<in> mc \<longrightarrow> (\<exists>e t. (s,e,t) \<in> ma \<and> (t,t') \<in> sr \<and> e = e')))"

definition lift_snd_rel where
  "lift_snd_rel srel \<equiv> {(r,r'). fst r = fst r' \<and> (snd r, snd r') \<in> srel}"

definition preserves where
  "preserves mode mode' P f \<equiv> \<forall>(s,e,s') \<in> f. (s,mode) \<in> P \<longrightarrow> (s',mode') \<in> P"

(* Special case for KernelExit *)
definition preserves' where
  "preserves' mode P f \<equiv> \<forall>(s,e,s') \<in> f. (s,mode) \<in> P \<longrightarrow> (s',e) \<in> P"

crunch kernelExit_if
  for (empty_fail) empty_fail

definition prod_lift where
  "prod_lift R r r' \<equiv> R (fst r) (fst r') \<and> (snd r) = (snd r')"

definition handlePreemption_if :: "user_context \<Rightarrow> user_context kernel" where
  "handlePreemption_if tc \<equiv> do
     irq \<leftarrow> doMachineOp (getActiveIRQ False);
     when (irq \<noteq> None) $ handleInterrupt (the irq);
     stateAssert
       (\<lambda>s. (ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread) \<and> valid_domain_list' s) [];
     return tc
   od"

crunch handlePreemption_if
  for (empty_fail) empty_fail

definition handlePreemption_H_if where
  "handlePreemption_H_if \<equiv> {(s, u, s'). s' \<in> fst (split handlePreemption_if s)}"

definition schedule'_if :: "user_context \<Rightarrow> user_context kernel" where
  "schedule'_if tc \<equiv> do
     schedule;
     activateThread;
     stateAssert (\<lambda>s. 0 < ksDomainTime s \<and> valid_domain_list' s) [];
     return tc
   od"

crunch schedule'_if
  for (empty_fail) empty_fail

definition schedule'_H_if where
  "schedule'_H_if \<equiv> {(s, e, s'). s' \<in> fst (split schedule'_if s)}"

definition checkActiveIRQ_if :: "user_context \<Rightarrow> (irq option \<times> user_context) kernel" where
  "checkActiveIRQ_if tc \<equiv> do
     irq \<leftarrow> doMachineOp (getActiveIRQ False);
     return (irq, tc)
   od"

crunch checkActiveIRQ_if
  for (empty_fail) empty_fail

definition checkActiveIRQ_H_if where
  "checkActiveIRQ_H_if \<equiv>
     {((tc, s), irq, (tc', s')). ((irq, tc'), s') \<in> fst (checkActiveIRQ_if tc s)}"

definition kernelCall_H_if where
  "kernelCall_H_if e \<equiv>
     {(s, b, (tc,s')) | s b tc s' r. ((r,tc),s') \<in> fst (split (kernelEntry_if e) s) \<and>
                                     b = (case r of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False)}"

definition
  "ptable_rights_s' s \<equiv> ptable_rights (ksCurThread s) (absKState s)"

definition
  "ptable_lift_s' s \<equiv> ptable_lift (ksCurThread s) (absKState s)"


lemma kernel_entry_if_domain_time_inv:
  "\<lbrace>K (e \<noteq> Interrupt) and (\<lambda>s. P (domain_time s))\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_ s. P (domain_time s) \<rbrace>"
   unfolding kernel_entry_if_def
   by (wp handle_event_domain_time_inv) simp

lemma kernel_entry_if_valid_domain_time:
  "\<lbrace>\<lambda>s. 0 < domain_time s\<rbrace>
   kernel_entry_if Interrupt tc
   \<lbrace>\<lambda>_ s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding kernel_entry_if_def
  apply (rule hoare_pre)
   apply (wp handle_interrupt_valid_domain_time
          | clarsimp | wpc)+
     \<comment> \<open>strengthen post of do_machine_op; we know interrupt occurred\<close>
     apply (rule_tac Q'="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
     apply (wp+, simp)
  done

lemma kernel_entry_if_no_preempt:
  "\<lbrace>\<top>\<rbrace> kernel_entry_if Interrupt ctx \<lbrace>\<lambda>(interrupt,_) _. interrupt = Inr ()\<rbrace>"
  unfolding kernel_entry_if_def
  by (wp | clarsimp intro!: validE_cases_valid)+

lemma kernelExit_inv[wp]:
  "kernelExit_if tc \<lbrace>P\<rbrace>"
  by (wpsimp simp: kernelExit_if_def)

lemma corres_ex_abs_lift:
  "\<lbrakk> corres r S P' f f'; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>ex_abs (P and S) and P'\<rbrace> f' \<lbrace>\<lambda>_. ex_abs Q\<rbrace>"
  by (fastforce simp: corres_underlying_def valid_def ex_abs_def)

lemmas schedaction_related = sched_act_rct_related

lemma empty_fail_select_bind: "empty_fail (assert (S \<noteq> {}) >>= (\<lambda>_. select S))"
  by (clarsimp simp: empty_fail_def select_def assert_def)

crunch user_memory_update
  for (empty_fail) empty_fail[wp]
crunch device_memory_update
  for (empty_fail) empty_fail[wp]

lemma corres_gets_same:
  assumes equiv: "\<And>s s'. \<lbrakk>P s; Q s'; (s, s') \<in> sr\<rbrakk>\<Longrightarrow> f s = g s'"
  and rimp : "\<And>s. P s \<Longrightarrow> R (f s) s"
  and corres: "\<And>r.  corres_underlying sr b c rr (P and (R r) and (\<lambda>s. r = f s)) Q (n r) (m r)"
  shows "corres_underlying sr b c rr P Q (do r \<leftarrow> gets f; n r od) (do r \<leftarrow> gets g; m r od)"
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r' = "(=)"])
       apply clarsimp
       apply (rule equiv)
         apply simp+
      apply (rule corres)
     apply wp+
   apply (simp add: rimp)
  apply simp
  done

lemma corres_assert_imp_r:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> Q'; corres_underlying state_relation a b rr P Q f (g ()) \<rbrakk>
     \<Longrightarrow> corres_underlying state_relation a b rr P Q f (assert Q' >>= g)"
  by (force simp: corres_underlying_def assert_def return_def bind_def fail_def)

lemma corres_return_same_trivial:
  "corres_underlying sr b c (=) \<top> \<top> (return a) (return a)"
  by simp

crunch device_memory_update
  for (no_fail) no_fail[wp]

lemma corres_ex_abs_lift':
  "\<lbrakk> corres_underlying state_relation False False r S P' f f'; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>ex_abs (P and S) and P'\<rbrace> f' \<lbrace>\<lambda>_. ex_abs Q\<rbrace>"
  by (fastforce simp: corres_underlying_def valid_def ex_abs_def)

lemma getCurThread_corres':
  "corres_underlying state_relation nf nf' (=) \<top> \<top> (gets cur_thread) getCurThread"
  by (simp add: getCurThread_def curthread_relation)

lemma user_mem_corres':
  "corres_underlying state_relation nf nf' (=) invs invs'
                     (gets (\<lambda>x. g (user_mem x))) (gets (\<lambda>x. g (user_mem' x)))"
  by (clarsimp simp: gets_def get_def return_def bind_def invs_def invs'_def
                     corres_underlying_def user_mem_relation)

lemma corres_machine_op':
  assumes P: "corres_underlying Id nf nf' r P Q x x'"
  shows "corres_underlying state_relation nf nf' r (P \<circ> machine_state) (Q \<circ> ksMachineState)
                           (do_machine_op x) (doMachineOp x')"
  apply (rule corres_submonad3[OF submonad_do_machine_op submonad_doMachineOp _ _ _ _ P])
  by (auto simp: state_relation_def swp_def)

lemma corres_assert':
  "corres_underlying sr nf False dc \<top> \<top> (assert P) (assert P)"
  by (clarsimp simp: corres_underlying_def assert_def return_def fail_def)


consts arch_extras :: "kernel_state \<Rightarrow> bool"

locale ADT_IF_Refine_1 =
  fixes doUserOp_if :: "user_transition_if \<Rightarrow> user_context \<Rightarrow> (event option \<times> user_context) kernel"
  assumes arch_tcb_context_set_tcb_relation:
    "tcb_relation tcb tcb'
     \<Longrightarrow> tcb_relation (tcb\<lparr>tcb_arch := arch_tcb_context_set tc (tcb_arch tcb)\<rparr>)
                      (tcbArch_update (atcbContextSet tc) tcb')"
  and arch_tcb_context_get_atcbContextGet:
    "tcb_relation tcb tcb'
     \<Longrightarrow> (arch_tcb_context_get \<circ> tcb_arch) tcb = (atcbContextGet \<circ> tcbArch) tcb'"
  and doUserOp_if_empty_fail:
    "empty_fail (doUserOp_if uop tc)"
  and do_user_op_if_corres:
    "corres (=) (einvs and ct_running and (\<lambda>_. \<forall>t pl pr pxn tcu. f t pl pr pxn tcu \<noteq> {}))
                (invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running')
                (do_user_op_if f tc) (doUserOp_if f tc)"
  and doUserOp_if_invs'[wp]:
    "\<lbrace>invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running' and ex_abs (einvs)\<rbrace>
     doUserOp_if f tc
     \<lbrace>\<lambda>_. invs'\<rbrace>"
  and doUserOp_arch_extras[wp]:
    "doUserOp_if f tc \<lbrace>arch_extras\<rbrace>"
  and doUserOp_if_schedact[wp]:
    "\<And>P. doUserOp_if f tc \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
  and doUserOp_if_st_tcb_at[wp]:
    "doUserOp_if f tc \<lbrace>st_tcb_at' st t\<rbrace>"
  and doUserOp_if_cur_thread[wp]:
    "\<And>P. doUserOp_if f tc \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>"
  and do_user_op_if_corres':
    "corres_underlying state_relation nf False (=) (einvs and ct_running)
       (invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running')
       (do_user_op_if f tc) (doUserOp_if f tc)"
  and dmo_getActiveIRQ_corres:
    "corres (=) \<top> \<top> (do_machine_op (getActiveIRQ in_kernel)) (doMachineOp (getActiveIRQ in_kernel'))"
  and dmo'_getActiveIRQ_wp:
    "\<lbrace>\<lambda>s. P (irq_at (irq_state (ksMachineState s) + 1) (irq_masks (ksMachineState s)))
            (s\<lparr>ksMachineState := (ksMachineState s\<lparr>irq_state := irq_state (ksMachineState s) + 1\<rparr>)\<rparr>)\<rbrace>
     doMachineOp (getActiveIRQ in_kernel)
     \<lbrace>P\<rbrace>"
  and handlePreemption_arch_extras[wp]:
    "handlePreemption_if tc \<lbrace>arch_extras\<rbrace>"
  and scheduler_if'_arch_extras[wp]:
    "\<lbrace>invs' and arch_extras\<rbrace>
     schedule'_if tc
     \<lbrace>\<lambda>_. arch_extras\<rbrace>"
  and checkActiveIRQ_ksPSpace[wp]:
    "checkActiveIRQ_if tc \<lbrace>arch_extras\<rbrace>"
  and kernelEntry_invs'[wp]:
    "\<lbrace>invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)
            and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
            and arch_extras\<rbrace>
     kernelEntry_if e tc
     \<lbrace>\<lambda>_. invs'\<rbrace>"
  and kernelEntry_arch_extras[wp]:
    "\<lbrace>invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)
            and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
            and arch_extras\<rbrace>
     kernelEntry_if e tc
     \<lbrace>\<lambda>_. arch_extras\<rbrace>"
  and threadSet_arch_extras[wp]:
    "threadSet a b \<lbrace>arch_extras\<rbrace>"
  and handle_preemption_if_corres:
    "corres (=) (einvs and valid_domain_list and (\<lambda>s. 0 < domain_time s)) (invs')
                (handle_preemption_if tc) (handlePreemption_if tc)"
  and doUserOp_if_ksDomainTime_inv[wp]:
    "\<And>P. doUserOp_if uop tc \<lbrace>\<lambda>s. P (ksDomainTime s)\<rbrace>"
  and doUserOp_if_ksDomSchedule_inv[wp]:
    "\<And>P. doUserOp_if uop tc \<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>"
  and valid_device_abs_state_eq:
    "valid_machine_state (s :: det_state) \<Longrightarrow> abs_state s = s"
  and doUserOp_if_no_interrupt:
    "\<lbrace>K (uop_sane uop)\<rbrace> doUserOp_if uop tc \<lbrace>\<lambda>r s. (fst r) \<noteq> Some Interrupt\<rbrace>"
  and handleEvent_corres_arch_extras:
    "corres (dc \<oplus> dc)
       (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and schact_is_rct)
       (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s)
              and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
              and arch_extras)
       (handle_event event) (handleEvent event)"
begin

lemma kernel_entry_if_corres:
  "corres (prod_lift (dc \<oplus> dc))
     (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s)
            and schact_is_rct
            and (\<lambda>s. 0 < domain_time s) and valid_domain_list)
     (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s)
            and arch_extras
            and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
     (kernel_entry_if event tc) (kernelEntry_if event tc)"
  apply (simp add: kernel_entry_if_def kernelEntry_if_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule corres_split)
         apply simp
         apply (rule threadset_corresT)
               apply (erule arch_tcb_context_set_tcb_relation)
              apply (clarsimp simp: tcb_cap_cases_def)
             apply (rule allI[OF ball_tcb_cte_casesI]; clarsimp)
            apply fastforce
           apply fastforce
          apply fastforce
         apply (simp add: exst_same_def)
        apply (rule corres_split[OF handleEvent_corres_arch_extras])
          apply (rule corres_stateAssert_assume_stronger[where Q=\<top> and
                        P="\<lambda>s. valid_domain_list s \<and>
                               (event \<noteq> Interrupt \<longrightarrow> 0 < domain_time s) \<and>
                               (event = Interrupt \<longrightarrow> domain_time s = 0 \<longrightarrow>
                                 scheduler_action s = choose_new_thread)"])
           apply (clarsimp simp: prod_lift_def)
          apply (clarsimp simp: state_relation_def)
         apply (wp hoare_TrueI threadSet_invs_trivial thread_set_invs_trivial thread_set_ct_running
                   threadSet_ct_running' thread_set_not_state_valid_sched hoare_vcg_const_imp_lift
                   handle_event_domain_time_inv handle_interrupt_valid_domain_time
                | simp add: tcb_cap_cases_def schact_is_rct_def | wpc | wp (once) hoare_drop_imps)+
   apply (fastforce simp: invs_def cur_tcb_def)
  apply force
  done

lemma kernelEntry_ex_abs[wp]:
  "\<lbrace>invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle')
          and arch_extras
          and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
          and (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list'
          and ex_abs (einvs)\<rbrace>
   kernelEntry_if e tc
   \<lbrace>\<lambda>_. ex_abs (einvs)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule corres_ex_abs_lift[OF kernel_entry_if_corres])
   apply (wp kernel_entry_if_invs kernel_entry_if_valid_sched)
  apply (clarsimp simp: ex_abs_def)
  apply (rule_tac x=sa in exI)
  apply (clarsimp simp: domain_time_rel_eq domain_list_rel_eq)
  by (fastforce simp: ct_running_related ct_idle_related schedaction_related
                      active_from_running' active_from_running schact_is_rct_def)

lemma doUserOp_if_ct_in_state[wp]:
  "doUserOp_if f tc \<lbrace>ct_in_state' st\<rbrace>"
   by (wpsimp wp: ct_in_state_thread_state_lift')

lemma doUserOp_if_ex_abs[wp]:
  "\<lbrace>invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running' and ex_abs (einvs)\<rbrace>
   doUserOp_if f tc
   \<lbrace>\<lambda>_. ex_abs (einvs)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule corres_ex_abs_lift'[OF do_user_op_if_corres'])
   apply (rule_tac Q'="\<lambda>a. invs and ct_running and valid_list and valid_sched" in hoare_strengthen_post)
    apply (wp do_user_op_if_invs)
   apply clarsimp
  apply (clarsimp simp: ex_abs_def)
  apply (rule_tac x=sa in exI)
  apply (clarsimp simp: active_from_running ct_running_related schedaction_related)+
  done

lemma check_active_irq_if_corres:
  "corres (=) \<top> \<top> (check_active_irq_if tc) (checkActiveIRQ_if tc)"
  apply (simp add: checkActiveIRQ_if_def check_active_irq_if_def)
  apply (rule corres_split_forwards'[where r'="(=)"])
     apply (rule dmo_getActiveIRQ_corres)
    apply wp+
  apply clarsimp
  done

lemma checkActiveIRQ_if_wp:
  "\<lbrace>\<lambda>s. P ((irq_at (irq_state (ksMachineState s) + 1) (irq_masks (ksMachineState s))), tc)
          (s\<lparr>ksMachineState := (ksMachineState s\<lparr>irq_state := irq_state (ksMachineState s) + 1\<rparr>)\<rparr>)\<rbrace>
   checkActiveIRQ_if tc
   \<lbrace>P\<rbrace>"
  by (simp add: checkActiveIRQ_if_def | wp dmo'_getActiveIRQ_wp)+

lemma checkActiveIRQ_invs'[wp]:
  "checkActiveIRQ_if tc \<lbrace>invs'\<rbrace>"
  by (wpsimp wp: checkActiveIRQ_if_wp)

lemma checkActiveIRQ_ct_in_state[wp]:
  "checkActiveIRQ_if tc \<lbrace>ct_in_state' st\<rbrace>"
  by (wpsimp wp: checkActiveIRQ_if_wp)

lemma checkActiveIRQ_schedact[wp]:
  "checkActiveIRQ_if tc \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
  by (wpsimp wp: checkActiveIRQ_if_wp)

lemma checkActiveIRQ_ex_abs[wp]:
  "checkActiveIRQ_if tc \<lbrace>ex_abs (einvs)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule corres_ex_abs_lift[OF check_active_irq_if_corres])
   apply (rule check_active_irq_if_wp)
  apply (clarsimp simp: ex_abs_def)
  done

lemma handlePreemption_invs'[wp]:
  "handlePreemption_if tc \<lbrace>invs'\<rbrace>"
  apply (simp add: handlePreemption_if_def)
  apply (wp dmo'_getActiveIRQ_wp hoare_drop_imps)
  apply clarsimp
  done

lemma handlePreemption_ex_abs[wp]:
  "\<lbrace>invs' and ex_abs (einvs) and valid_domain_list' and (\<lambda>s. 0 < ksDomainTime s)\<rbrace>
   handlePreemption_if tc
   \<lbrace>\<lambda>_. ex_abs (einvs)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule corres_ex_abs_lift[OF handle_preemption_if_corres])
   apply (wp handle_preemption_if_invs)
  apply (auto simp: ex_abs_def domain_list_rel_eq domain_time_rel_eq)
  done

end


lemma handle_preemption_if_valid_domain_time:
  "\<lbrace>\<lambda>s. 0 < domain_time s \<rbrace>
   handle_preemption_if tc
   \<lbrace>\<lambda>r s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread\<rbrace>"
  unfolding handle_preemption_if_def
  apply (rule hoare_pre)
   apply (wp handle_interrupt_valid_domain_time)
   apply (rule_tac Q'="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
   apply (wp, simp)
  done

lemma schedule_if_corres:
 "corres (=) (invs and valid_sched and valid_list and valid_domain_list
                   and (\<lambda>s. domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread))
             (invs') (schedule_if tc) (schedule'_if tc)"
  apply (simp add: schedule_if_def schedule'_if_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="dc"])
       apply (rule schedule_corres)
      apply (rule corres_split[where r'="dc"])
         apply (rule activateThread_corres)
        apply (rule corres_stateAssert_assume_stronger
                      [where Q=\<top> and P="\<lambda>s. valid_domain_list s \<and> 0 < domain_time s"])
         apply simp
        apply (clarsimp simp: state_relation_def)
       apply wp+
     apply (wp schedule_invs' schedule_domain_time_left)+
   apply clarsimp+
  done

lemma schedule_if'_invs'_post:
  "\<lbrace>invs'\<rbrace> schedule'_if tc \<lbrace>\<lambda>_. invs' and (ct_running' or ct_idle')\<rbrace>"
  apply (simp add: schedule'_if_def)
  apply (wp activate_invs' schedule_invs' schedule_sch_act_simple hoare_drop_imps | simp)+
  done

lemma schedule_if'_invs'[wp]:
  "schedule'_if tc \<lbrace>invs'\<rbrace>"
  apply (rule hoare_post_imp[OF _ schedule_if'_invs'_post])
  apply simp
  done

lemma schedule_if'_ct_running_or_idle[wp]:
  "\<lbrace>invs'\<rbrace> schedule'_if tc \<lbrace>\<lambda>r s. ct_running' s \<or> ct_idle' s\<rbrace>"
  apply (rule hoare_post_imp[OF _ schedule_if'_invs'_post])
  apply simp
  done

lemma schedule_if'_rct[wp]:
  "\<lbrace>invs'\<rbrace> schedule'_if tc \<lbrace>\<lambda>r s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  apply (simp add: schedule'_if_def)
  apply (wp activate_sch_act schedule_sch hoare_drop_imps)
  done

lemma nonzero_gt_zero:
  "x \<noteq> (0 :: obj_ref) \<Longrightarrow> x > 0"
  by (simp add: word_gt_0)

lemma gt_zero_nonzero:
  "(0 :: obj_ref) < x \<Longrightarrow> x \<noteq> 0"
  by (simp add: word_gt_0)

lemma schedule_if_domain_time_left:
  "\<lbrace>\<lambda>s. valid_domain_list s \<and> (domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread)\<rbrace>
   schedule_if tc
   \<lbrace>\<lambda>rv s. 0 < domain_time s\<rbrace>"
  unfolding schedule_if_def schedule_det_ext_ext_def schedule_switch_thread_fastfail_def
  supply ethread_get_wp[wp del]
  supply if_split[split del]
  supply nonzero_gt_zero[simp] gt_zero_nonzero[simp]
  apply (rule hoare_pre)
   apply (wpsimp simp: ethread_get_when_def wp: gts_wp
          | wp hoare_drop_imp[where f="ethread_get a b" for a b]
               hoare_drop_imp[where f="tcb_sched_action a b" for a b])+
  apply (auto split: if_split)
  done

lemma sched_act_relation_ChooseNewThread[simp]:
  "sched_act_relation sca ChooseNewThread = (sca = choose_new_thread)"
  by (cases sca; simp)

lemma scheduler'_if_ex_abs[wp]:
  "\<lbrace>invs' and ex_abs (einvs) and valid_domain_list'
          and (\<lambda>s. ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread)\<rbrace>
   schedule'_if tc
   \<lbrace>\<lambda>_. ex_abs (einvs)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule corres_ex_abs_lift[OF schedule_if_corres])
   apply wp
  apply (clarsimp simp: ex_abs_def)
  apply (rule exI, rule conjI, assumption)
  apply (frule state_relation_sched_act_relation)
  apply (auto simp: domain_list_rel_eq domain_time_rel_eq)
  done

lemma preservesE:
  assumes preserves: "preserves mode mode' P f"
  assumes inf: "(s,e,s') \<in> f"
  assumes P: "(s,mode) \<in> P"
  assumes a: "(s',mode') \<in> P \<Longrightarrow> Q"
  shows "Q"
  apply (rule a)
  apply (insert preserves inf P)
  apply (clarsimp simp: preserves_def)
  apply fastforce
  done

lemma preserves'E:
  assumes preserves: "preserves' mode P f"
  assumes inf: "(s,e,s') \<in> f"
  assumes P: "(s,mode) \<in> P"
  assumes a: "(s',e) \<in> P \<Longrightarrow> Q"
  shows "Q"
  apply (rule a)
  apply (insert preserves inf P)
  apply (clarsimp simp: preserves'_def)
  apply fastforce
  done

lemma step_corres_bothE:
  assumes corres: "step_corres nf srel mode invs_abs invs_conc f_abs f_conc"
  assumes preserves: "preserves mode mode' invs_conc f_conc"
  assumes a: "(s, s') \<in> srel"
  assumes e: "(s, mode) \<in> invs_abs"
  assumes b: "(s', mode) \<in> invs_conc"
  assumes c: "(s', e, t') \<in> f_conc"
  assumes d: "\<And>t. (s, e, t) \<in> f_abs
                   \<Longrightarrow> (t, mode') \<in> has_srel_state (lift_fst_rel srel) invs_conc
                   \<Longrightarrow> (t, t') \<in> srel
                   \<Longrightarrow> P"
  shows "P"
  apply (insert corres a b c e)
  apply (clarsimp simp: step_corres_def)
  apply (drule_tac x="(s,s')" in bspec,clarsimp+)
  apply (drule_tac x=e in spec)
  apply (drule_tac x="t'" in spec)
  apply simp
  apply clarsimp
  apply (rule_tac t=t in d,simp+)
   apply (clarsimp simp: has_srel_state_def lift_fst_rel_def)
   apply (rule preservesE[OF preserves],assumption+)
   apply fastforce+
  done

lemma step_corres_both'E:
  assumes corres: "step_corres nf srel mode invs_abs invs_conc f_abs f_conc"
  assumes preserves: "preserves' mode invs_conc f_conc"
  assumes a: "(s, s') \<in> srel"
  assumes e: "(s, mode) \<in> invs_abs"
  assumes b: "(s', mode) \<in> invs_conc"
  assumes c: "(s', e, t') \<in> f_conc"
  assumes d: "\<And>t. (s, e, t) \<in> f_abs
                   \<Longrightarrow> (t,e) \<in> has_srel_state (lift_fst_rel srel) invs_conc
                   \<Longrightarrow> (t, t') \<in> srel
                   \<Longrightarrow> P"
  shows "P"
  apply (insert corres a b c e)
  apply (clarsimp simp: step_corres_def)
  apply (drule_tac x="(s,s')" in bspec,clarsimp+)
  apply (drule_tac x=e in spec)
  apply (drule_tac x="t'" in spec)
  apply simp
  apply clarsimp
  apply (rule_tac t=t in d,simp+)
   apply (clarsimp simp: has_srel_state_def lift_fst_rel_def)
   apply (rule preserves'E[OF preserves],assumption+)
   apply fastforce+
  done

lemma step_corresE:
  assumes corres: "step_corres nf srel mode invs_abs invs_conc f_abs f_conc"
  assumes a: "(s, s') \<in> srel"
  assumes e: "(s, mode) \<in> invs_abs"
  assumes b: "(s', mode) \<in> invs_conc"
  assumes c: "(s', e, t') \<in> f_conc"
  assumes d: "\<And>t. \<lbrakk> (s, e, t) \<in> f_abs; (t, t') \<in> srel \<rbrakk> \<Longrightarrow> P"
  shows "P"
  apply (insert corres a b c e)
  apply (clarsimp simp: step_corres_def)
  apply (drule_tac x="(s,s')" in bspec,clarsimp+)
  apply (drule_tac x=e in spec)
  apply (drule_tac x=t' in spec)
  apply clarsimp
  apply (rule d)
   apply simp+
  done


locale global_automaton_invs =
  fixes check_active_irq
  fixes do_user_op
  fixes kernel_call
  fixes handle_preemption
  fixes schedule
  fixes kernel_exit
  fixes invs :: "('a global_sys_state) set"
  fixes ADT :: "(('a global_sys_state),'o, unit) data_type"
  fixes extras :: "'a global_sys_state set"
  assumes step_adt: "Step ADT =
    (\<lambda>u. (global_automaton_if check_active_irq do_user_op kernel_call
                              handle_preemption schedule kernel_exit) \<inter> {(s,s'). s' \<in> extras})"
  assumes check_active_irq_invs:
    "preserves InUserMode InUserMode invs check_active_irq"
  assumes check_active_irq_idle_invs:
    "preserves InIdleMode InIdleMode invs check_active_irq"
  assumes check_active_irq_invs_entry:
    "preserves InUserMode (KernelEntry Interrupt) invs check_active_irq"
  assumes check_active_irq_idle_invs_entry:
    "preserves InIdleMode (KernelEntry Interrupt) invs check_active_irq"
  assumes do_user_op_invs:
    "preserves InUserMode InUserMode invs do_user_op"
  assumes do_user_op_invs_entry:
    "preserves InUserMode (KernelEntry e) invs do_user_op"
  assumes kernel_call_invs:
    "e \<noteq> Interrupt
     \<Longrightarrow> preserves (KernelEntry e) KernelPreempted invs (kernel_call e)"
  assumes kernel_call_invs_sched:
    "preserves (KernelEntry e) (KernelSchedule (e = Interrupt)) invs (kernel_call e)"
  assumes handle_preemption_invs:
    "preserves KernelPreempted (KernelSchedule True) invs handle_preemption"
  assumes schedule_invs:
    "preserves (KernelSchedule b) KernelExit invs schedule"
  assumes kernel_exit_invs:
    "preserves' KernelExit invs kernel_exit"
  assumes init_invs:
    "(Init ADT) s \<subseteq> invs"
  assumes init_extras:
    "(Init ADT) s \<subseteq> extras"
  begin

lemma ADT_extras: "ADT \<Turnstile> extras"
  apply (rule invariantI)
   apply (clarsimp simp: init_extras)
  apply (clarsimp simp: step_adt)
  done

lemma ADT_invs: "ADT \<Turnstile> invs"
  apply (rule invariantI)
   apply (intro allI)
   apply (rule init_invs)
  apply (clarsimp simp: step_adt global_automaton_if_def)
  apply (elim disjE exE conjE,simp_all)
           apply (rule preservesE[OF kernel_call_invs])
              apply (rule preservesE[OF kernel_call_invs],assumption+)
          apply (rule preservesE[OF kernel_call_invs_sched],assumption+)
         apply (rule preservesE[OF handle_preemption_invs],assumption+)
        apply (rule preservesE[OF schedule_invs],assumption+)
       apply (rule preserves'E[OF kernel_exit_invs],assumption+)
      apply (rule preservesE[OF check_active_irq_invs],assumption+)
      apply (rule preservesE[OF do_user_op_invs_entry],assumption+)
     apply (rule preservesE[OF check_active_irq_invs],assumption+)
     apply (rule preservesE[OF do_user_op_invs],assumption+)
    apply (rule preservesE[OF check_active_irq_invs_entry],assumption+)
   apply (rule preservesE[OF check_active_irq_idle_invs_entry],assumption+)
  apply (rule preservesE[OF check_active_irq_idle_invs],assumption+)
  done

end


lemma invariant_holds_inter:
  "A \<Turnstile> I \<Longrightarrow> A \<Turnstile> S \<Longrightarrow> A \<Turnstile> (I \<inter> S)"
  apply (clarsimp simp: invariant_holds_def)
  apply blast
  done

lemma preserves_lift_ret:
  "(\<And>tc. \<lbrace>\<lambda>s. ((tc,s),mode) \<in> P\<rbrace> f tc \<lbrace>\<lambda>tc' s'. ((snd tc',s'),mode') \<in> P\<rbrace>)
   \<Longrightarrow> preserves mode mode' P {((tc, s), irq, tc', s'). ((irq, tc'), s') \<in> fst (f tc s)}"
  by (fastforce simp: preserves_def valid_def)

lemma preserves_lift:
  "(\<And>tc. \<lbrace>\<lambda>s. ((tc,s),mode) \<in> P\<rbrace> f tc \<lbrace>\<lambda>tc' s'. ((tc',s'),mode') \<in> P\<rbrace>)
   \<Longrightarrow> preserves mode mode' P {((tc, s), irq, tc', s'). (tc', s') \<in> fst (f tc s)}"
  by (clarsimp simp: preserves_def valid_def)

lemma preserves_lift':
  "(\<And>tc. \<lbrace>\<lambda>s. ((tc,s),mode) \<in> P\<rbrace> f uop tc \<lbrace>\<lambda>tc' s'. ((snd tc',s'),mode') \<in> P\<rbrace>)
   \<Longrightarrow> preserves mode mode' P {((a, b), e, tc, s') | a b e tc s'. ((e, tc), s') \<in> fst (f uop a b)}"
  by (fastforce simp: preserves_def valid_def)

lemma preserves_lift'':
   "(\<And>tc. \<lbrace>\<lambda>s. ((tc,s),mode) \<in> P\<rbrace> f e tc \<lbrace>\<lambda>tc' s'. ((snd tc',s'),mode') \<in> P\<rbrace>)
    \<Longrightarrow> preserves mode mode' P
         {((a, b), ba, tc, s') | a b ba tc s'.
                                 \<exists>r. ((r, tc), s') \<in> fst (f e a b) \<and> ba = (r \<noteq> Inr ())}"
  by (fastforce simp: preserves_def valid_def)

lemma preserves_lift''':
  "(\<And>tc. \<lbrace>\<lambda>s. ((tc,s),mode) \<in> P\<rbrace> f tc \<lbrace>\<lambda>tc' s'. ((tc',s'),mode') \<in> P\<rbrace>)
   \<Longrightarrow> preserves mode mode' P {(s, u, s'). s' \<in> fst (case s of (x, xa) \<Rightarrow> f x xa)}"
  by (clarsimp simp: preserves_def valid_def)

lemma preserves'_lift:
  "(\<And>tc. \<lbrace>\<lambda>s. ((tc,s),mode) \<in> P\<rbrace> f tc \<lbrace>\<lambda>tc' s'. ((tc',s'),y s') \<in> P\<rbrace>)
   \<Longrightarrow> preserves' mode P {(s, m, s'). s' \<in> fst (case s of (x, xa) \<Rightarrow> f x xa) \<and>
                                      m = (y (snd s'))}"
  by (fastforce simp: preserves'_def valid_def)

lemmas preserves_lifts = preserves_lift_ret preserves_lift preserves_lift'
                         preserves_lift'' preserves_lift''' preserves'_lift


definition full_invs_if' where
  "full_invs_if' \<equiv>
     {s. invs' (internal_state_if s)
       \<and> ex_abs (einvs) (internal_state_if s)
       \<and> arch_extras (internal_state_if s)
       \<and> (snd s \<noteq> KernelSchedule True \<longrightarrow> ksDomainTime (internal_state_if s) > 0)
       \<and> (ksDomainTime (internal_state_if s) = 0
          \<longrightarrow> ksSchedulerAction (internal_state_if s) = ChooseNewThread)
       \<and> valid_domain_list' (internal_state_if s)
       \<and> (case (snd s) of
            KernelEntry e \<Rightarrow> (e \<noteq> Interrupt
                              \<longrightarrow> ct_running' (internal_state_if s) \<and>
                                  ksDomainTime (internal_state_if s) \<noteq> 0) \<and>
                             (ct_running' (internal_state_if s) \<or> ct_idle' (internal_state_if s)) \<and>
                             ksSchedulerAction (internal_state_if s) = ResumeCurrentThread
          | KernelExit \<Rightarrow> (ct_running' (internal_state_if s) \<or> ct_idle' (internal_state_if s)) \<and>
                          ksSchedulerAction (internal_state_if s) = ResumeCurrentThread \<and>
                          ksDomainTime (internal_state_if s) \<noteq> 0
          | InUserMode \<Rightarrow> ct_running' (internal_state_if s) \<and>
                          ksSchedulerAction (internal_state_if s) = ResumeCurrentThread
          | InIdleMode \<Rightarrow> ct_idle' (internal_state_if s) \<and>
                          ksSchedulerAction (internal_state_if s) = ResumeCurrentThread
          | _ \<Rightarrow> True)}"

defs step_restrict_def:
  "step_restrict \<equiv> \<lambda>s. s \<in> has_srel_state (lift_fst_rel (lift_snd_rel state_relation)) full_invs_if'"

lemma abstract_invs:
  "global_automaton_invs check_active_irq_A_if (do_user_op_A_if uop)
                         kernel_call_A_if kernel_handle_preemption_if
                         kernel_schedule_if kernel_exit_A_if
                         (full_invs_if) (ADT_A_if uop) {s. step_restrict s}"
  supply nonzero_gt_zero[simp] gt_zero_nonzero[simp]
  supply conj_cong[cong]
  apply (unfold_locales)
               apply (simp add: ADT_A_if_def)
              apply (simp_all add: check_active_irq_A_if_def do_user_op_A_if_def
                                   kernel_call_A_if_def kernel_handle_preemption_if_def
                                   kernel_schedule_if_def kernel_exit_A_if_def
                              del: unit_Inl_or_Inr(2) split del: if_split)[12]
              apply (rule preserves_lifts |
                     wp check_active_irq_if_wp do_user_op_if_invs
                    | clarsimp simp add: full_invs_if_def)+
          apply (rule_tac Q'="\<lambda>r s'. (invs and ct_running) s' \<and>
                   valid_list s' \<and>
                   valid_sched s' \<and> scheduler_action s' = resume_cur_thread \<and>
                   valid_domain_list s' \<and>
                   (domain_time s' = 0 \<longrightarrow> scheduler_action s' = choose_new_thread)" in hoare_post_imp)
           apply (clarsimp)
          apply (wp do_user_op_if_invs hoare_vcg_imp_lift)
             apply clarsimp+
         apply (rule preserves_lifts)
         apply (simp add: full_invs_if_def)
         apply (rule_tac Q'="\<lambda>r s'. (invs and ct_running) s' \<and>
                  valid_list s' \<and>
                   valid_domain_list s' \<and>
                  domain_time s' \<noteq> 0 \<and>
                  valid_sched s' \<and> scheduler_action s' = resume_cur_thread" in hoare_post_imp)
          apply (clarsimp simp: active_from_running)
         apply (wp do_user_op_if_invs kernel_entry_if_invs kernel_entry_if_valid_sched ; clarsimp)
        (* KernelEntry \<rightarrow> KernelPreempted *)
        apply (rule preserves_lifts, simp add: full_invs_if_def)
        subgoal by (wp kernel_entry_if_invs kernel_entry_if_valid_sched
                        kernel_entry_if_domain_time_inv
                     ; clarsimp simp: active_from_running)

       (* KernelEntry \<rightarrow> KernelSchedule (e = Interrupt) *)
       apply (rule preserves_lifts, simp add: full_invs_if_def)
       apply (case_tac "e = Interrupt")
        subgoal by (wp kernel_entry_if_invs kernel_entry_if_valid_sched kernel_entry_if_valid_domain_time
                     | clarsimp simp: active_from_running)+
       apply (clarsimp simp: conj_left_commute)
       subgoal by (wp kernel_entry_if_invs kernel_entry_if_valid_sched kernel_entry_if_domain_time_inv
                    ; clarsimp simp: active_from_running)
      (* KernelPreempted \<rightarrow> KernelSchedule True *)
      apply (rule preserves_lifts, simp add: full_invs_if_def)
      subgoal for tc
        apply (rule hoare_pre)
         apply (wp handle_preemption_if_invs)
         apply (wp handle_preemption_if_valid_domain_time)
        apply clarsimp
        done
     (* KernelSchedule \<rightarrow> KernelExit *)
     apply (rule preserves_lifts, simp add: full_invs_if_def)
     subgoal by (rule hoare_pre, wp schedule_if_domain_time_left, fastforce)
    (* KernelExit \<rightarrow> InUserMode \<or> InIdleMode *)
    apply (rule preserves_lifts, simp add: full_invs_if_def)
    subgoal by (clarsimp cong: conj_cong | wp)+
   apply (fastforce simp: full_invs_if_def ADT_A_if_def step_restrict_def)+
  done

crunch checkActiveIRQ_if
  for ksDomainTime_inv[wp]: "\<lambda>s. P (ksDomainTime s)"
  and ksDomSchedule_inv[wp]: "\<lambda>s. P (ksDomSchedule s)"

lemma kernelEntry_if_valid_domain_time:
  "e \<noteq> Interrupt \<Longrightarrow> \<lbrace>\<top>\<rbrace> kernelEntry_if e tc \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<and> valid_domain_list' s\<rbrace>"
  "\<lbrace>\<top>\<rbrace>
   kernelEntry_if Interrupt tc
   \<lbrace>\<lambda>_ s. (ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread) \<and> valid_domain_list' s\<rbrace>"
  unfolding kernelEntry_if_def by wpsimp+

lemma handlePreemption_if_valid_domain_time:
  "\<lbrace>\<top>\<rbrace>
   handlePreemption_if tc
   \<lbrace>\<lambda>_ s. (ksDomainTime s = 0 \<longrightarrow> ksSchedulerAction s = ChooseNewThread) \<and> valid_domain_list' s\<rbrace>"
  unfolding handlePreemption_if_def by (wpsimp cong: if_cong)

lemma schedule'_if_valid_domain_time:
  "\<lbrace>\<top>\<rbrace> schedule'_if tc \<lbrace>\<lambda>_ s. 0 < ksDomainTime s\<rbrace>"
  "\<lbrace>\<top>\<rbrace> schedule'_if tc \<lbrace>\<lambda>_. valid_domain_list'\<rbrace>"
  unfolding schedule'_if_def by wpsimp+

lemma kernelEntry_if_no_preempt:
  "\<lbrace>\<top>\<rbrace> kernelEntry_if Interrupt ctx \<lbrace>\<lambda>(interrupt,_) _. interrupt = Inr () \<rbrace>"
  unfolding kernelEntry_if_def handleEvent_def
  by (wp | clarsimp intro!: validE_cases_valid)+


context ADT_IF_Refine_1 begin

definition doUserOp_H_if where
  "doUserOp_H_if uop \<equiv> {(s,e,(tc,s'))| s e tc s'. ((e,tc),s') \<in> fst (split (doUserOp_if uop) s)}"

definition ADT_H_if where
  "ADT_H_if uop \<equiv>
     \<lparr>Init = \<lambda>s. ({user_context_of s} \<times> {s'. absKState s' = (internal_state_if s)})
                                      \<times> {sys_mode_of s} \<inter> full_invs_if',
      Fin = \<lambda>((uc,s),m). ((uc, absKState s),m),
      Step = (\<lambda>u. global_automaton_if checkActiveIRQ_H_if (doUserOp_H_if uop)
                                      kernelCall_H_if handlePreemption_H_if
                                      schedule'_H_if kernelExit_H_if)\<rparr>"

lemma haskell_invs:
  "global_automaton_invs checkActiveIRQ_H_if (doUserOp_H_if uop)
                         kernelCall_H_if handlePreemption_H_if
                         schedule'_H_if kernelExit_H_if full_invs_if' (ADT_H_if uop) UNIV"
  supply nonzero_gt_zero[simp] gt_zero_nonzero[simp]
  supply conj_cong[cong]
  apply (unfold_locales)
               apply (simp add: ADT_H_if_def)
              apply (simp_all add: checkActiveIRQ_H_if_def doUserOp_H_if_def
                                    kernelCall_H_if_def handlePreemption_H_if_def
                                    schedule'_H_if_def kernelExit_H_if_def split del: if_split)[12]
              apply (rule preserves_lifts | wp | simp add: full_invs_if'_def
                  | wp (once) hoare_vcg_disj_lift)+
          apply (wp | wp (once) hoare_vcg_disj_lift hoare_drop_imps)+
         apply simp
        apply (rule preserves_lifts)
        apply (simp add: full_invs_if'_def)
        apply (wp kernelEntry_if_valid_domain_time; simp)
     subgoal for e
       apply (rule preserves_lifts, simp add: full_invs_if'_def)
       apply wp
          apply (case_tac "e = Interrupt"; wpsimp wp: kernelEntry_if_valid_domain_time)
        apply fastforce+
       done
      subgoal
        apply (rule preserves_lifts, simp add: full_invs_if'_def)
        apply (wp handlePreemption_if_valid_domain_time)
        apply fastforce
        done
     subgoal
       apply (rule preserves_lifts, simp add: full_invs_if'_def)
       apply (wp schedule'_if_valid_domain_time)
       apply fastforce
       done
    subgoal by (rule preserves_lifts, simp add: full_invs_if'_def)
                (wp, fastforce)
   apply (clarsimp simp: ADT_H_if_def)+
  done

(*Unused*)
lemma Init_Fin_ADT_H:
  "s' \<in> full_invs_if'
   \<Longrightarrow> s' \<in> Init (ADT_H_if uop) (Fin (ADT_H_if uop) s')"
  apply (clarsimp simp: ADT_H_if_def)
  apply (case_tac s')
  apply simp
  apply (case_tac a)
  apply simp
  done

(*Unused*)
lemma Fin_Init_ADT_H:
  "s' \<in> (Init (ADT_H_if uop) s)
   \<Longrightarrow> s' \<in> full_invs_if' \<Longrightarrow> s \<in> Fin (ADT_H_if uop) ` Init (ADT_H_if uop) s"
  apply (clarsimp simp: ADT_H_if_def)
  apply (case_tac s)
  apply simp
  apply clarsimp
  apply (simp add: image_def)
  apply (rule_tac x="((a,b),baa)" in bexI)
   apply clarsimp
  apply clarsimp
  done

end


lemma step_corres_exE:
  assumes step: "step_corres nf srel mode invs_abs invs_conc f f'"
  assumes nf: "nf"
  assumes invsC: "(s',mode) \<in> invs_conc"
  assumes invsA: "(s,mode) \<in> invs_abs"
  assumes srel: "(s,s') \<in> srel"
  assumes ex: "\<And>e t' t. (s',e,t') \<in> f' \<Longrightarrow> (s,e,t) \<in> f \<Longrightarrow> (t,t') \<in> srel \<Longrightarrow> P"
  shows P
  apply (insert step invsC invsA srel nf)
  apply (clarsimp simp: step_corres_def)
  apply (drule_tac x="(s,s')" in bspec,clarsimp+)
  apply (drule_tac x=e' in spec)
  apply (drule_tac x=t' in spec)
  apply clarsimp
  apply (rule ex)
    apply assumption+
  done


locale global_automata_refine =
  abs: global_automaton_invs check_active_irq_abs do_user_op_abs kernel_call_abs
                             handle_preemption_abs schedule_abs kernel_exit_abs
                             invs_abs ADT_abs extras_abs +
  conc: global_automaton_invs check_active_irq_conc do_user_op_conc kernel_call_conc
                              handle_preemption_conc schedule_conc kernel_exit_conc
                              invs_conc ADT_conc UNIV
  for check_active_irq_abs and do_user_op_abs and kernel_call_abs and handle_preemption_abs and
      schedule_abs and kernel_exit_abs and invs_abs and
      ADT_abs :: "(('a global_sys_state),'o, unit) data_type" and extras_abs and
      check_active_irq_conc and do_user_op_conc and kernel_call_conc and handle_preemption_conc and
      schedule_conc and kernel_exit_conc and invs_conc and
      ADT_conc :: "(('c global_sys_state),'o, unit) data_type" +
  fixes srel :: "((user_context \<times> 'a) \<times> (user_context \<times> 'c)) set"
  fixes nf :: "bool"
  assumes extras_abs_intro:
    "has_srel_state (lift_fst_rel srel) invs_conc \<subseteq> extras_abs"
  assumes srel_Fin:
    "\<lbrakk> (s,s') \<in> srel; (s,mode) \<in> invs_abs; (s',mode) \<in> invs_conc \<rbrakk>
       \<Longrightarrow> (Fin (ADT_conc)) (s',mode) = (Fin (ADT_abs)) (s,mode)"
  assumes init_refinement:
    "((Init (ADT_conc)) a) \<subseteq> lift_fst_rel srel `` ((Init (ADT_abs)) a)"
  assumes corres_check_active_irq:
    "step_corres nf srel InUserMode (invs_abs) invs_conc check_active_irq_abs check_active_irq_conc"
  assumes corres_check_active_irq_idle:
    "step_corres nf srel InIdleMode (invs_abs) invs_conc check_active_irq_abs check_active_irq_conc"
  assumes corres_do_user_op:
    "step_corres nf srel InUserMode (invs_abs) invs_conc (do_user_op_abs) (do_user_op_conc)"
  assumes corres_kernel_call:
    "step_corres nf srel (KernelEntry e) (invs_abs) invs_conc (kernel_call_abs e) (kernel_call_conc e)"
  assumes corres_handle_preemption:
    "step_corres nf srel KernelPreempted (invs_abs) invs_conc handle_preemption_abs handle_preemption_conc"
  assumes corres_schedule:
    "step_corres nf srel (KernelSchedule b) (invs_abs) invs_conc schedule_abs schedule_conc"
  assumes corres_kernel_exit:
    "step_corres nf srel KernelExit (invs_abs) invs_conc kernel_exit_abs kernel_exit_conc"
  assumes kernel_call_no_preempt:
    "\<And>s s' b. (s, b, s') \<in> kernel_call_abs Interrupt \<Longrightarrow> b = False"
begin

lemma extras_inter'[dest!]:
   "(t,mode) \<in> has_srel_state (lift_fst_rel srel) invs_conc \<Longrightarrow> (t,mode) \<in> extras_abs"
  apply (rule set_mp)
   apply (rule extras_abs_intro)
  apply simp
  done

lemma fw_sim_abs_conc:
  "LI (ADT_abs) (ADT_conc) (lift_fst_rel srel) (invs_abs \<times> invs_conc)"
  apply (unfold LI_def )
  apply (intro conjI allI)
    apply (rule init_refinement)
   apply (clarsimp simp: rel_semi_def relcomp_unfold lift_fst_rel_def
                         abs.step_adt conc.step_adt)
   apply (clarsimp simp: global_automaton_if_def)
   apply (elim disjE exE conjE,simp_all)
            apply (rule step_corres_bothE[OF corres_kernel_call conc.kernel_call_invs],assumption+,auto)[1]
           apply (rule step_corres_bothE[OF corres_kernel_call conc.kernel_call_invs_sched],assumption+,auto)[1]
          apply (rule step_corres_bothE[OF corres_handle_preemption conc.handle_preemption_invs],assumption+,auto)[1]
         apply (rule step_corres_bothE[OF corres_schedule conc.schedule_invs],assumption+,auto)[1]
        apply (rule step_corres_both'E[OF corres_kernel_exit conc.kernel_exit_invs],assumption+,auto)[1]
       apply (rule preservesE[OF conc.check_active_irq_invs],assumption+)
       apply (rule step_corres_bothE[OF corres_check_active_irq conc.check_active_irq_invs],assumption+,clarsimp)
       apply (rule preservesE[OF abs.check_active_irq_invs],assumption+)
       apply (rule_tac s'="(ac,be)" in step_corres_bothE[OF corres_do_user_op conc.do_user_op_invs_entry],assumption+,auto)[1]
      apply (rule preservesE[OF conc.check_active_irq_invs],assumption+)
      apply (rule step_corres_bothE[OF corres_check_active_irq conc.check_active_irq_invs],assumption+,clarsimp)
      apply (rule preservesE[OF abs.check_active_irq_invs],assumption+)
      apply (rule_tac s'="(ac,be)" in step_corres_bothE[OF corres_do_user_op conc.do_user_op_invs],assumption+,auto)[1]
     apply (rule step_corres_bothE[OF corres_check_active_irq conc.check_active_irq_invs_entry],assumption+,auto)[1]
    apply (rule step_corres_bothE[OF corres_check_active_irq_idle conc.check_active_irq_idle_invs_entry],assumption+,auto)[1]
   apply (rule preservesE[OF conc.check_active_irq_idle_invs],assumption+)
   apply (rule step_corres_bothE[OF corres_check_active_irq_idle conc.check_active_irq_idle_invs],assumption+,auto)[1]
  apply (fastforce intro!: srel_Fin simp: lift_fst_rel_def)
  done

lemma fw_simulates: "ADT_conc \<sqsubseteq>\<^sub>F ADT_abs"
  apply (rule L_invariantI)
    apply (rule abs.ADT_invs)
   apply (rule conc.ADT_invs)
  apply (rule fw_sim_abs_conc)
  done

lemma refinement: "ADT_conc \<sqsubseteq> ADT_abs"
  by (rule sim_imp_refines[OF fw_simulates])

lemma conc_serial:
  assumes uop_sane: "\<And>s e t. (s,e,t) \<in> do_user_op_conc \<Longrightarrow>
                       e \<noteq> Some Interrupt"
  assumes no_fail: "nf"
  shows
    "serial_system (ADT_conc) {s'. \<exists>s. (s,s') \<in> (lift_fst_rel srel) \<and> s \<in> invs_abs \<and> s' \<in> invs_conc}"
  apply (insert no_fail)
  apply (unfold_locales)
   apply (rule fw_inv_transport)
     apply (rule abs.ADT_invs)
    apply (rule conc.ADT_invs)
   apply (rule fw_sim_abs_conc)
  apply (clarsimp simp: conc.step_adt global_automaton_if_def lift_fst_rel_def)
  apply (case_tac ba,simp_all)
       apply (rule step_corres_exE[OF corres_check_active_irq],assumption+)
       apply (rule preservesE[OF conc.check_active_irq_invs],assumption+)
       apply (rule preservesE[OF abs.check_active_irq_invs],assumption+)
       apply (rule_tac s=t and s'=t' in step_corres_exE[OF corres_do_user_op],assumption+)
       apply (rule_tac s=t and s'=t' in step_corresE[OF corres_do_user_op],assumption+)
       apply clarsimp
       apply (case_tac e)
        apply (case_tac ea)
         apply fastforce
        apply simp
        apply (frule uop_sane)
        apply fastforce
       apply (case_tac ea)
        apply fastforce
       apply fastforce
      apply (rule step_corres_exE[OF corres_check_active_irq_idle],assumption+)
      apply (case_tac e)
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (rule step_corres_exE[OF corres_kernel_call],assumption+)
     apply (case_tac e ; fastforce dest: kernel_call_no_preempt)
    apply (rule step_corres_exE[OF corres_handle_preemption],assumption+)
    apply fastforce
   apply (rule step_corres_exE[OF corres_schedule],assumption+)
   apply fastforce
  apply (rule step_corres_exE[OF corres_kernel_exit],assumption+)
  apply fastforce
  done

lemma abs_serial:
  assumes constrained_B:
    "\<And>s. s \<in> invs_abs \<inter> extras_abs \<Longrightarrow> \<exists>s'. s' \<in> invs_conc \<and> (s, s') \<in> lift_fst_rel srel"
  assumes uop_sane:
    "\<And>s e t. (s,e,t) \<in> do_user_op_conc \<Longrightarrow> e \<noteq> Some Interrupt"
  assumes no_fail: "nf"
  shows "serial_system (ADT_abs) (invs_abs \<inter> extras_abs)"
  apply (rule serial_system.fw_sim_serial)
       apply (rule conc_serial)
        apply (rule uop_sane,simp)
       apply (rule no_fail)
      apply (rule fw_sim_abs_conc)
     apply (rule invariant_holds_inter)
      apply (rule abs.ADT_invs)
     apply (rule abs.ADT_extras)
    apply clarsimp
   apply simp
  apply (frule constrained_B)
  apply (clarsimp simp: lift_fst_rel_def)
  apply auto
  done

end


lemma step_corres_lift:
  "\<lbrakk> \<And>tc. corres_underlying srel False nf (=) (\<lambda>s. ((tc,s),mode) \<in> P) (\<lambda>s'. ((tc,s'),mode) \<in> P')
                            (f tc) (f' tc);
     \<And>tc. nf \<Longrightarrow> empty_fail (f' tc) \<rbrakk>
     \<Longrightarrow> step_corres nf (lift_snd_rel srel) mode P P'
           {((tc, s), irq, tc', s'). ((irq, tc'), s') \<in> fst (f tc s)}
           {((tc, s), irq, tc', s'). ((irq, tc'), s') \<in> fst (f' tc s)}"
  by (fastforce simp: corres_underlying_def step_corres_def lift_snd_rel_def empty_fail_def)

lemma step_corres_lift':
  "(\<And>tc. corres_underlying srel False nf (=)
            (\<lambda>s. ((tc,s),mode) \<in> P) (\<lambda>s'. ((tc,s'),mode) \<in> P') (f u tc) (f' u tc)) \<Longrightarrow>
   (\<And>tc. nf \<Longrightarrow> empty_fail (f' u tc)) \<Longrightarrow>
   step_corres nf (lift_snd_rel srel) mode
         P P'
         {((a, b), e, tc, s') |a b e tc s'.
          ((e, tc), s') \<in> fst (f u a b)}
         {((a, b), e, tc, s') |a b e tc s'.
          ((e, tc), s') \<in> fst (f' u a b)}"
  by (fastforce simp: corres_underlying_def step_corres_def lift_snd_rel_def empty_fail_def)

lemma step_corres_lift'':
  "\<lbrakk> \<And>tc. corres_underlying srel False nf
            (\<lambda>r r'. ((fst r) = Inr ()) = ((fst r') = Inr ()) \<and> (snd r) = (snd r'))
            (\<lambda>s. ((tc,s),mode) \<in> P) (\<lambda>s'. ((tc,s'),mode) \<in> P') (f e tc) (f' e tc);
     \<And>tc. nf \<Longrightarrow> empty_fail (f' e tc) \<rbrakk>
     \<Longrightarrow> step_corres nf (lift_snd_rel srel) mode P P'
           {((a, b), ba, tc, s') |a b ba tc s'. \<exists>r. ((r, tc), s') \<in> fst (f e a b) \<and>
                                                    ba = (r \<noteq> Inr ())}
           {((a, b), ba, tc, s') |a b ba tc s'. \<exists>r. ((r, tc), s') \<in> fst (f' e a b) \<and>
                                                    ba = (r \<noteq> Inr ())}"
  by (fastforce simp: corres_underlying_def step_corres_def lift_snd_rel_def empty_fail_def)

lemma step_corres_lift''':
  "\<lbrakk> \<And>tc. corres_underlying srel False nf (=) (\<lambda>s. ((tc,s),mode) \<in> P)
                            (\<lambda>s'. ((tc,s'),mode) \<in> P') (f tc) (f' tc);
     \<And>tc. nf \<Longrightarrow> empty_fail (f' tc) \<rbrakk>
     \<Longrightarrow> step_corres nf (lift_snd_rel srel) mode P P'
           {(s, u, s'). s' \<in> fst (case s of (x, xa) \<Rightarrow> f x xa)}
           {(s, u, s'). s' \<in> fst (case s of (x, xa) \<Rightarrow> f' x xa)}"
  by (fastforce simp: corres_underlying_def step_corres_def lift_snd_rel_def empty_fail_def)

lemma step_corres_lift'''':
  "\<lbrakk> \<And>tc. corres_underlying srel False nf (=) (\<lambda>s. ((tc,s),mode) \<in> P)
                             (\<lambda>s'. ((tc,s'),mode) \<in> P') (f tc) (f' tc);
     \<And>tc. nf \<Longrightarrow> empty_fail (f' tc);
     \<And>tc s s'. (s,s') \<in> srel \<Longrightarrow> S' s' \<Longrightarrow> S s \<Longrightarrow> y s = y' s';
     \<And>tc. \<lbrace>\<lambda>s'. ((tc,s'),mode) \<in> P'\<rbrace> (f' tc) \<lbrace>\<lambda>_. S'\<rbrace>;
     \<And>tc. \<lbrace>\<lambda>s'. ((tc,s'),mode) \<in> P\<rbrace> (f tc) \<lbrace>\<lambda>_. S\<rbrace> \<rbrakk>
     \<Longrightarrow> step_corres nf (lift_snd_rel srel) mode P P'
           {(s, m, s'). s' \<in> fst (case s of (x, xa) \<Rightarrow> f x xa) \<and> m = (y (snd s'))}
           {(s, m, s'). s' \<in> fst (case s of (x, xa) \<Rightarrow> f' x xa) \<and> m = (y' (snd s'))}"
  apply (clarsimp simp: corres_underlying_def step_corres_def lift_snd_rel_def empty_fail_def)
  apply (clarsimp simp: valid_def)
  apply (drule_tac x=a in meta_spec)+
  apply fastforce
  done

lemmas step_corres_lifts =
  step_corres_lift step_corres_lift' step_corres_lift'' step_corres_lift''' step_corres_lift''''

lemma st_tcb_at_coerce_haskell:
  "\<lbrakk> st_tcb_at P t a; (a, c) \<in> state_relation; tcb_at' t c \<rbrakk>
     \<Longrightarrow> st_tcb_at' (\<lambda>st'. \<exists>st. thread_state_relation st st' \<and> P st) t c"
  apply (clarsimp simp: state_relation_def pspace_relation_def
                        obj_at_def st_tcb_at'_def st_tcb_at_def)
  apply (drule_tac x=t in bspec)
   apply fastforce
  apply clarsimp
  apply (simp add: tcb_relation_cut_def)
  apply clarsimp
  apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_tcb split: kernel_object.splits)
  apply (rule_tac x="tcb_state tcb" in exI)
  apply simp
  apply (simp add: tcb_relation_def)
  done

lemma ct_running'_related:
  "\<lbrakk> (a, c) \<in> state_relation; invs' c; ct_running a \<rbrakk>
     \<Longrightarrow> ct_running' c"
  apply (clarsimp simp: ct_in_state_def ct_in_state'_def
                        curthread_relation)
  apply (frule(1) st_tcb_at_coerce_haskell)
  apply (simp add: invs'_def cur_tcb'_def curthread_relation)
  apply (erule pred_tcb'_weakenE)
  apply (case_tac st, simp_all)[1]
  done

lemma ct_idle'_related:
  "\<lbrakk> (a, c) \<in> state_relation; invs' c; ct_idle a \<rbrakk>
     \<Longrightarrow> ct_idle' c"
  apply (clarsimp simp: ct_in_state_def ct_in_state'_def curthread_relation)
  apply (frule(1) st_tcb_at_coerce_haskell)
   apply (simp add: invs'_def cur_tcb'_def curthread_relation)
  apply (erule pred_tcb'_weakenE)
  apply (case_tac st, simp_all)[1]
  done

lemma invs_machine_state:
  "invs s \<Longrightarrow> valid_machine_state s"
  by (clarsimp simp: invs_def valid_state_def)

(* FIXME MOVE to where sched_act_rct_related *)
lemma sched_act_cnt_related:
  "\<lbrakk> (a, c) \<in> state_relation; ksSchedulerAction c = ChooseNewThread \<rbrakk>
     \<Longrightarrow> scheduler_action a = choose_new_thread"
  by (case_tac "scheduler_action a", simp_all add: state_relation_def)


context ADT_IF_Refine_1 begin

lemma kernel_exit_if_corres:
  "corres (=) (invs) (invs') (kernel_exit_if tc) (kernelExit_if tc)"
  apply (simp add: kernel_exit_if_def kernelExit_if_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=)"])
       apply (rule getCurThread_corres)
      apply simp
      apply (rule threadGet_corres)
      apply (erule arch_tcb_context_get_atcbContextGet)
     apply wp+
   apply fastforce+
  done

lemma haskell_to_abs:
  "uop_nonempty uop
   \<Longrightarrow> global_automata_refine check_active_irq_A_if (do_user_op_A_if uop) kernel_call_A_if
                              kernel_handle_preemption_if kernel_schedule_if kernel_exit_A_if
                              full_invs_if (ADT_A_if uop) {s. step_restrict s} checkActiveIRQ_H_if
                              (doUserOp_H_if uop) kernelCall_H_if handlePreemption_H_if
                              schedule'_H_if kernelExit_H_if full_invs_if' (ADT_H_if uop)
                              (lift_snd_rel state_relation) True"
  apply (simp add: global_automata_refine_def)
  apply (intro conjI)
    apply (rule abstract_invs)
   apply (rule haskell_invs)
  apply (unfold_locales)
            apply (simp add: step_restrict_def)
           apply (simp add: ADT_H_if_def ADT_A_if_def)
           apply (clarsimp simp add: lift_snd_rel_def full_invs_if_def full_invs_if'_def)
           apply (frule valid_device_abs_state_eq[OF invs_machine_state])
           apply (frule absKState_correct[rotated])
             apply simp+
          apply (simp add: ADT_H_if_def ADT_A_if_def lift_fst_rel_def)
          apply (clarsimp simp: lift_snd_rel_def)
          apply (subgoal_tac "((a, absKState bb), ba) \<in> full_invs_if \<and> (absKState bb, bb) \<in> state_relation")
           apply (fastforce simp: step_restrict_def has_srel_state_def lift_fst_rel_def lift_snd_rel_def)
          apply (simp add: full_invs_if'_def)
          apply (clarsimp simp: ex_abs_def)
          apply (frule(1) absKState_correct[rotated],simp+)
          apply (simp add: full_invs_if_def)
          apply (frule valid_device_abs_state_eq[OF invs_machine_state])
          apply (case_tac ba; clarsimp simp: domain_time_rel_eq domain_list_rel_eq)
              apply (fastforce simp: active_from_running ct_running_related ct_idle_related schedaction_related)+
           apply (simp add: sched_act_cnt_related)
          apply (fastforce simp: active_from_running ct_running_related ct_idle_related schedaction_related)+
         apply (simp add: check_active_irq_A_if_def checkActiveIRQ_H_if_def)
         apply (rule step_corres_lifts)
          apply (rule corres_guard_imp)
            apply (rule check_active_irq_if_corres,simp+)
         apply (rule checkActiveIRQ_if_empty_fail)
        apply (simp add: check_active_irq_A_if_def checkActiveIRQ_H_if_def)
        apply (rule step_corres_lifts)
         apply (rule corres_guard_imp)
           apply (rule check_active_irq_if_corres,simp+)
        apply (rule checkActiveIRQ_if_empty_fail)
       apply (simp add: do_user_op_A_if_def doUserOp_H_if_def)
       apply (rule step_corres_lifts)
        apply (rule corres_guard_imp)
          apply (rule do_user_op_if_corres)
         apply (fastforce simp: full_invs_if_def uop_nonempty_def)
        apply (simp add: full_invs_if'_def uop_nonempty_def)
       apply (rule doUserOp_if_empty_fail)
      apply (simp add: kernelCall_H_if_def kernel_call_A_if_def del: unit_Inl_or_Inr(2))
      apply (rule step_corres_lifts)
       apply (rule corres_rel_imp)
        apply (rule corres_guard_imp)
          apply (rule kernel_entry_if_corres)
         apply clarsimp
         apply ((clarsimp simp: full_invs_if_def full_invs_if'_def schact_is_rct_def)+)[2]
       apply (fastforce simp: prod_lift_def)
      apply (rule kernelEntry_if_empty_fail)
     apply (simp add: kernel_handle_preemption_if_def handlePreemption_H_if_def)
     apply (rule step_corres_lifts)
      apply (rule corres_guard_imp)
        apply (rule handle_preemption_if_corres)
       apply (simp add: full_invs_if_def)
      apply (simp add: full_invs_if'_def)
     apply (rule handlePreemption_if_empty_fail)
    apply (simp add: kernel_schedule_if_def schedule'_H_if_def)
    apply (rule step_corres_lifts)
     apply (rule corres_guard_imp)
       apply (rule schedule_if_corres)
      apply (simp add: full_invs_if_def)
     apply (simp add: full_invs_if'_def)
    apply (rule schedule'_if_empty_fail)
   apply (simp add: kernel_exit_A_if_def kernelExit_H_if_def split del: if_split)
   apply (rule_tac S="\<top>" and S'="invs'" in step_corres_lifts(5))
       apply (rule corres_guard_imp)
         apply (rule kernel_exit_if_corres)
        apply ((simp add: full_invs_if_def full_invs_if'_def)+)[2]
      apply (rule kernelExit_if_empty_fail)
     apply clarsimp
     apply (clarsimp simp: ct_running'_related ct_running_related)
    apply wp
    apply (clarsimp simp: full_invs_if'_def)
   apply wp
  apply (clarsimp simp: kernel_call_A_if_def)
  apply (drule use_valid[OF _ kernel_entry_if_no_preempt]; simp)
  done

lemma ADT_A_if_Init_Fin_serial:
  "uop_sane uop \<Longrightarrow> Init_Fin_serial (ADT_A_if uop) s0 (full_invs_if \<inter> {s. step_restrict s})"
  apply (simp add: Init_Fin_serial_def)
  apply (rule conjI)
   apply (rule global_automata_refine.abs_serial[OF haskell_to_abs])
      apply (simp add: uop_sane_def uop_nonempty_def)
     apply (fastforce simp: step_restrict_def has_srel_state_def)
    apply (clarsimp simp add: doUserOp_H_if_def)
    apply (frule use_valid[OF _ doUserOp_if_no_interrupt])
     apply simp+
  apply (unfold_locales)
   apply (clarsimp simp: ADT_A_if_def)+
  done

lemma ADT_A_if_enabled:
  "uop_sane uop \<Longrightarrow> enabled_system (ADT_A_if uop) s0"
  apply (rule Init_Fin_serial.enabled)
  apply (rule ADT_A_if_Init_Fin_serial)
  apply simp
  done

end


lemma (in valid_initial_state_noenabled) uop_nonempty:
  "uop_nonempty utf"
  by (simp add: uop_nonempty_def utf_non_empty)

lemma (in valid_initial_state_noenabled) uop_sane:
  "uop_sane utf"
  apply (simp add: uop_sane_def utf_non_empty)
  apply (cut_tac utf_non_interrupt)
  apply blast
  done

locale ADT_valid_initial_state_noenabled = ADT_IF_Refine_1 + valid_initial_state_noenabled

sublocale ADT_valid_initial_state_noenabled \<subseteq> valid_initial_state
  using ADT_A_if_enabled[of utf s0, OF uop_sane] ADT_A_if_Init_Fin_serial[OF uop_sane, of s0]
  by unfold_locales (fastforce simp: enabled_system_def s0_def Init_Fin_serial_def
                                     serial_system_def Init_Fin_serial_axioms_def)+

end
