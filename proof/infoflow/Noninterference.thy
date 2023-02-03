(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Noninterference
imports
  Noninterference_Base
  Noninterference_Base_Alternatives
  ArchScheduler_IF
  ArchADT_IF
  Access.ArchADT_AC
begin

text \<open>

The top-level information flow theorems. (There are also theories for
example systems, which go on top of this one.)

We will instantiate the various unwinding systems, defined in
Noninterference_Base(_Alternative), with the actual kernel automaton
from ADT_IF. Then we consider the @{term noninterference_system.Nonleakage}
and @{term noninterference_system.Noninterference} properties over
our kernel big steps.

At the end of this file, we show the top-level Nonleakage theorem.
The Noninterference property does not hold on the kernel and is not
proven despite the name of the file, but a partial integrity result
holds in integrity_part.

\<close>

section \<open>sameFor : unwinding relation\<close>

datatype 'a partition = Partition 'a | PSched

fun scheduler_modes where
  "scheduler_modes KernelPreempted = True"
| "scheduler_modes (KernelEntry Interrupt) = True"
| "scheduler_modes (KernelSchedule b) = b"
| "scheduler_modes _ = False"

(*Modes where thread context is valid*)
fun user_modes where
  "user_modes KernelExit = False"
| "user_modes _ = True"

definition sameFor_subject ::
  "'a subject_label auth_graph \<Rightarrow> 'a subject_label agent_map \<Rightarrow>
   'a subject_label agent_irq_map \<Rightarrow> 'a subject_label agent_asid_map  \<Rightarrow>
   'a subject_label agent_domain_map \<Rightarrow> 'a \<Rightarrow> (observable_if \<times> observable_if) set" where
  "sameFor_subject g ab irqab asidab domainab l \<equiv>
     {(os,os') | os os' s s'.
        s = internal_state_if os \<and> s' = internal_state_if os' \<and>
        states_equiv_for (\<lambda>x. ab x \<in> subjectReads g (OrdinaryLabel l))
                         (\<lambda>x. irqab x \<in> subjectReads g (OrdinaryLabel l))
                         (\<lambda>x. asidab x \<in> subjectReads g (OrdinaryLabel l))
                         (\<lambda>x. domainab x \<inter> subjectReads g (OrdinaryLabel l) \<noteq> {}) s s' \<and>
        ((domainab (cur_domain s) \<inter> subjectReads g (OrdinaryLabel l) \<noteq> {} \<or>
          domainab (cur_domain s') \<inter> subjectReads g (OrdinaryLabel l) \<noteq> {})
          \<longrightarrow> (cur_domain s = cur_domain s' \<and> globals_equiv s s' \<and>
               scheduler_action s = scheduler_action s' \<and>
               work_units_completed s = work_units_completed s' \<and>
               irq_state (machine_state s) = irq_state (machine_state s') \<and>
               (user_modes (sys_mode_of os) \<longrightarrow> user_context_of os = user_context_of os') \<and>
               sys_mode_of os = sys_mode_of os' \<and> equiv_for (\<lambda>x. ab x = SilcLabel) kheap s s'))}"

definition sameFor_scheduler ::
   "'a subject_label auth_graph \<Rightarrow> 'a subject_label agent_map \<Rightarrow>
    'a subject_label agent_irq_map \<Rightarrow> 'a subject_label agent_asid_map \<Rightarrow>
    'a subject_label agent_domain_map \<Rightarrow> (observable_if \<times> observable_if) set" where
  "sameFor_scheduler g ab irqab asidab domainab \<equiv>
   {(os,os') | os os' s s'.
      s = internal_state_if os \<and> s' = internal_state_if os' \<and> domain_fields_equiv s s' \<and>
      idle_thread s = idle_thread s' \<and> globals_equiv_scheduler s s' \<and>
      equiv_for (\<lambda>x. ab x = SilcLabel) kheap s s' \<and> irq_state_of_state s = irq_state_of_state s' \<and>
      scheduler_modes (sys_mode_of os) = scheduler_modes (sys_mode_of os') \<and>
      interrupted_modes (sys_mode_of os) = interrupted_modes (sys_mode_of os')}"

text \<open>
  From the graph we define an equivalence relation on states for each partition.

  This is the unwinding relation of domain d with the right parameters (cf uwr later in this file)
\<close>
definition sameFor ::
  "'a subject_label auth_graph \<Rightarrow> 'a subject_label agent_map \<Rightarrow>
   'a subject_label agent_irq_map \<Rightarrow> 'a subject_label agent_asid_map \<Rightarrow>
   'a subject_label agent_domain_map \<Rightarrow> 'a partition \<Rightarrow> (observable_if \<times> observable_if) set" where
  "sameFor g ab irqab asidab domainab d \<equiv>
     case d of Partition l \<Rightarrow> sameFor_subject g ab irqab asidab domainab l
             | PSched \<Rightarrow> sameFor_scheduler g ab irqab asidab domainab"

abbreviation same_for where
  "same_for aag d \<equiv> sameFor (pasPolicy aag) (pasObjectAbs aag) (pasIRQAbs aag)
                             (pasASIDAbs aag) (pasDomainAbs aag) d"

text \<open>
  We want @{term sameFor} to be an equivalence relation always.
\<close>
lemma sameFor_refl: "refl (sameFor g ab irqab asidab domainab d)"
  by (auto intro!: refl_onI equiv_for_refl
             simp: sameFor_def sameFor_subject_def sameFor_scheduler_def domain_fields_equiv_def
            split: partition.splits
            intro: states_equiv_for_refl globals_equiv_refl globals_equiv_scheduler_refl)

lemma domain_fields_equiv_sym:
  "domain_fields_equiv s t \<Longrightarrow> domain_fields_equiv t s"
  by (clarsimp simp: domain_fields_equiv_def)

lemma sameFor_sym:
  "sym (sameFor g ab irqab asidab domainab d)"
  by (fastforce intro: symI
                 simp: sameFor_def sameFor_subject_def sameFor_scheduler_def
                split: partition.splits
                intro: states_equiv_for_sym globals_equiv_sym equiv_for_sym domain_fields_equiv_sym)

lemma domain_fields_equiv_trans:
  "\<lbrakk> domain_fields_equiv s t; domain_fields_equiv t u \<rbrakk>
     \<Longrightarrow> domain_fields_equiv s u"
  by (clarsimp simp: domain_fields_equiv_def)

lemma sameFor_trans:
  "trans (sameFor g ab irqab asidab domainab d)"
  apply (rule transI)
  apply (auto simp: sameFor_def sameFor_subject_def sameFor_scheduler_def
             split: partition.splits
             intro: states_equiv_for_trans globals_equiv_trans
                    equiv_for_trans domain_fields_equiv_trans)
  done

fun label_of where
  "label_of (OrdinaryLabel l) = l"

lemma is_label[simp]:
  "x \<noteq> SilcLabel \<Longrightarrow> OrdinaryLabel (label_of x) = x"
  by (case_tac x, auto)

lemma pasSubject_not_SilcLabel:
  "silc_inv aag s s' \<Longrightarrow> pasSubject aag \<noteq> SilcLabel"
  by (auto simp: silc_inv_def)

(* needs silc_inv to ensure pasSubject is not SilcLabel *)
lemma sameFor_reads_equiv_f_g:
  "\<lbrakk> reads_equiv_f_g aag s s'; silc_inv aag st' st'';
     pasSubject aag \<in> pasDomainAbs aag (cur_domain s) \<union> pasDomainAbs aag (cur_domain s') \<rbrakk>
     \<Longrightarrow> (((uc,s),mode),((uc,s'),mode)) \<in> same_for aag (Partition (label_of (pasSubject aag)))"
  apply (clarsimp simp: reads_equiv_f_g_def reads_equiv_def2 sameFor_def silc_dom_equiv_def)
  apply (simp add: sameFor_subject_def)
  apply (frule pasSubject_not_SilcLabel)
  apply (clarsimp)
  done

lemma sameFor_reads_equiv_f_g':
  "\<lbrakk> pas_cur_domain aag s \<or> pas_cur_domain aag s'; silc_inv aag st s;
     (((uc,s),mode),((uc',s'),mode')) \<in> same_for aag (Partition (label_of (pasSubject aag))) \<rbrakk>
     \<Longrightarrow> reads_equiv_f_g aag s s'"
  apply (frule pasSubject_not_SilcLabel)
  apply (auto simp: reads_equiv_f_g_def reads_equiv_def2 sameFor_def
                    sameFor_subject_def silc_dom_equiv_def globals_equiv_def)
  done

lemma sameFor_scheduler_equiv:
  "(s,s') \<in> same_for aag PSched
   \<Longrightarrow> scheduler_equiv aag (internal_state_if s) (internal_state_if s')"
  by (clarsimp simp: scheduler_equiv_def sameFor_def sameFor_scheduler_def silc_dom_equiv_def)


definition label_can_affect_partition where
  "label_can_affect_partition g k l \<equiv> \<exists>d. d \<in> subjectAffects g k \<and> d \<in> subjectReads g l"

definition partsSubjectAffects where
  "partsSubjectAffects g l \<equiv>
     Partition ` {x. label_can_affect_partition g (OrdinaryLabel l) (OrdinaryLabel x)}"


lemma reads_g_affects_equiv_sameFor:
  "\<lbrakk> reads_equiv_f_g aag s s' \<and> affects_equiv aag (OrdinaryLabel l) s s';
     pas_cur_domain aag s; silc_inv aag st' st'';
     Partition l \<in> partsSubjectAffects (pasPolicy aag) (label_of (pasSubject aag)) \<rbrakk>
     \<Longrightarrow> (((uc,s),mode),((uc,s'),mode)) \<in> same_for aag (Partition l)"
  apply (clarsimp simp: partsSubjectAffects_def)
  apply (simp add: affects_equiv_def2 sameFor_def sameFor_subject_def)
  apply (frule pasSubject_not_SilcLabel)
  apply (simp add: reads_equiv_f_g_def reads_equiv_def2 silc_dom_equiv_def)
  apply (erule states_equiv_for_guard_imp)
     apply (simp add: aag_can_affect_label_def label_can_affect_partition_def)+
  done

lemma schedule_reads_affects_equiv_sameFor_PSched:
  "\<lbrakk> scheduler_equiv aag s s'; scheduler_modes mode = scheduler_modes mode';
     interrupted_modes mode = interrupted_modes mode' \<rbrakk>
     \<Longrightarrow> (((uc,s),mode),((uc',s'),mode')) \<in> same_for aag PSched"
  by (simp add: sameFor_def sameFor_scheduler_def scheduler_equiv_def silc_dom_equiv_def)

lemma schedule_reads_affects_equiv_sameFor_PSched':
  "\<lbrakk> scheduler_equiv aag (internal_state_if s) (internal_state_if s');
     scheduler_modes (sys_mode_of s) = scheduler_modes (sys_mode_of s');
     interrupted_modes (sys_mode_of s) = interrupted_modes (sys_mode_of s') \<rbrakk>
     \<Longrightarrow> (s,s') \<in> same_for aag PSched"
  apply (case_tac s)
  apply (case_tac a)
  apply (case_tac s')
  apply (case_tac ab)
  apply clarsimp
  apply (rule schedule_reads_affects_equiv_sameFor_PSched; simp)
  done

lemma observable_if_cases:
  "P (s::observable_if) \<Longrightarrow> P (((user_context_of s),(internal_state_if s)),sys_mode_of s)"
  by (case_tac s, case_tac "fst s", simp)

lemma sameFor_reads_f_g_affects_equiv:
  "\<lbrakk> pas_cur_domain aag (internal_state_if s); silc_inv aag st (internal_state_if s);
     (s,s') \<in> same_for aag (Partition (label_of (pasSubject aag)));
     Partition l \<in> partsSubjectAffects (pasPolicy aag) (label_of (pasSubject aag));
     (s,s') \<in> same_for aag (Partition l) \<rbrakk>
     \<Longrightarrow> reads_equiv_f_g aag (internal_state_if s) (internal_state_if s') \<and>
         affects_equiv aag (OrdinaryLabel l) (internal_state_if s) (internal_state_if s')"
  apply (rule conjI)
   apply (rule sameFor_reads_equiv_f_g')
     apply blast
    apply blast
   apply (rule_tac s=s in observable_if_cases)
   apply (erule_tac s=s' in observable_if_cases)
  apply (simp add: partsSubjectAffects_def)
  apply (frule pasSubject_not_SilcLabel)
  apply clarsimp
  apply (clarsimp simp: affects_equiv_def2 sameFor_def)
  apply (clarsimp simp: sameFor_subject_def[where l=l])
  apply (blast intro: states_equiv_for_guard_imp)
  done

lemma schedule_reads_affects_equiv_sameFor:
  "\<lbrakk> scheduler_equiv aag s s'; scheduler_affects_equiv aag (OrdinaryLabel l) s s';
     user_modes mode \<longrightarrow> uc = uc' \<rbrakk>
     \<Longrightarrow> (((uc,s),mode),((uc',s'),mode)) \<in> same_for aag (Partition l)"
  by (auto simp: scheduler_equiv_def scheduler_affects_equiv_def sameFor_def sameFor_subject_def
                 silc_dom_equiv_def reads_scheduler_def domain_fields_equiv_def
                 disjoint_iff_not_equal Bex_def
          intro: globals_equiv_from_scheduler)

lemma globals_equiv_to_scheduler_globals_frame_equiv:
  "\<lbrakk> globals_equiv s t; invs s; invs t \<rbrakk>
     \<Longrightarrow> scheduler_globals_frame_equiv s t"
  by (simp add: globals_equiv_def scheduler_globals_frame_equiv_def)

lemma globals_equiv_to_cur_thread_eq:
  "globals_equiv s t \<Longrightarrow> cur_thread s = cur_thread t"
  by (simp add: globals_equiv_def)

lemma no_subject_affects_PSched:
  "PSched \<notin> partsSubjectAffects g l"
  by (auto simp: partsSubjectAffects_def elim: subjectAffects.cases)


section \<open>InfoFlow policy and partition integrity\<close>

text \<open>
  We derive a noninterference policy from the authority graph
  We exclude the silc label from the noninterference policy
  since it exists in the authority graph solely to ensure that no actual subject's
  label covers the inter label caps.
\<close>

inductive_set policyFlows :: "'a subject_label auth_graph \<Rightarrow> ('a partition \<times> 'a partition) set"
  for g :: "'a subject_label auth_graph" where
  policy_affects: "d \<in> partsSubjectAffects g l \<Longrightarrow> (Partition l, d) \<in> policyFlows g"
| policy_scheduler: "(PSched,d) \<in> policyFlows g"

lemma no_partition_flows_to_PSched:
  "(Partition l, PSched) \<notin> policyFlows g"
  apply (rule notI)
  apply (erule policyFlows.cases)
   apply (simp_all add: no_subject_affects_PSched)
  done

lemma partsSubjectAffects_bounds_those_subject_not_allowed_to_affect:
  "(Partition l,d) \<notin> policyFlows g \<Longrightarrow> d \<notin> partsSubjectAffects g l"
  apply (clarify)
  apply (drule policy_affects)
  apply (blast)
  done

lemma PSched_flows_to_all:
  "(PSched,d) \<in> policyFlows g"
  by (rule policyFlows.intros)

lemma policyFlows_refl:
  "refl (policyFlows g)"
  apply (rule refl_onI)
   apply simp
  apply (case_tac x)
   apply simp
   apply (rule policy_affects)
   apply (simp add: partsSubjectAffects_def image_def)
   apply (simp add: label_can_affect_partition_def)
   apply (blast intro: affects_lrefl)
  apply (blast intro: PSched_flows_to_all)
  done


(* a more constrained integrity property for non-PSched transitions
   TODO: can we constrain this further? *)
definition partitionIntegrity :: "'a subject_label PAS \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "partitionIntegrity aag s s' \<equiv>
     integrity (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
               (scheduler_affects_globals_frame s) s s' \<and>
     domain_fields_equiv s s' \<and> idle_thread s = idle_thread s' \<and>
     globals_equiv_scheduler s s' \<and> silc_dom_equiv aag s s'"


lemma thread_set_tcb_context_update_ct_active[wp]:
  "thread_set (tcb_arch_update (arch_tcb_context_set f)) t \<lbrace>\<lambda>s. P (ct_active s)\<rbrace>"
  apply (simp add: thread_set_def ct_in_state_def | wp set_object_wp touch_object_wp')+
  apply (clarsimp simp: st_tcb_at_def obj_at_def get_tcb_def ta_filter_def
                 split: option.splits kernel_object.splits)
  done

lemma prop_of_two_valid:
  assumes f: "\<And>P. m \<lbrace>\<lambda>s. P (f s)\<rbrace>"
  assumes g: "\<And>P. m \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "m \<lbrace>\<lambda>s. P (f s) (g s)\<rbrace>"
  by (rule hoare_pre, wps f g, wp, simp)

lemma thread_set_tcb_context_update_wp:
  "\<lbrace>\<lambda>s. P (s\<lparr>kheap := kheap s(t \<mapsto> TCB (tcb_arch_update f (the (get_tcb False t s))))\<rparr>)\<rbrace>
   thread_set (tcb_arch_update f) t
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_wp)
  apply simp
  done


lemma dmo_device_update_respects_Write:
  "\<lbrace>integrity aag X st and K (\<forall>p \<in> dom um'. aag_has_auth_to aag Write p)\<rbrace>
   do_machine_op (device_memory_update um')
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: device_memory_update_def)
  apply (rule hoare_pre)
   apply (wp dmo_wp)
  apply clarsimp
  apply (simp cong: abstract_state.fold_congs)
  apply (rule integrity_device_state_update)
    apply simp
   apply clarify
   apply (drule (1) bspec)
   apply simp
  apply fastforce
  done

lemma check_active_irq_if_integrity:
  "check_active_irq_if tc \<lbrace>integrity aag X st\<rbrace>"
  by (wpsimp wp: check_active_irq_if_wp simp: integrity_subjects_def)

lemma silc_dom_equiv_from_silc_inv_valid':
  assumes "\<And>st. \<lbrace>P and silc_inv aag st\<rbrace> f \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  shows "\<lbrace>P and silc_inv aag st and silc_dom_equiv aag sta\<rbrace> f \<lbrace>\<lambda>_. silc_dom_equiv aag sta\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule assms)
   apply (fastforce simp: silc_inv_def)
    (* we can't use clarsimp below because it splits pairs unconditionally *)
  apply (simp add: silc_inv_def silc_dom_equiv_def del: split_paired_All)
  apply (elim conjE)
  apply (intro allI impI notI)
  apply (drule(1) equiv_forD)+
  apply (frule(1) cte_wp_at_pspace'[THEN iffD1])
  apply (drule spec, drule(1) mp, erule notE, erule(1) cte_wp_at_pspace'[THEN iffD2])
  done

lemma ct_running_not_idle:
  "\<lbrakk> ct_running s; valid_idle s \<rbrakk> \<Longrightarrow> cur_thread s \<noteq> idle_thread s"
  by (clarsimp simp add: ct_in_state_def pred_tcb_at_def obj_at_def valid_idle_def)

lemma kernel_entry_if_globals_equiv_scheduler:
  "\<lbrace>globals_equiv_scheduler st and valid_arch_state and invs
                               and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
                               and (\<lambda>s. ct_idle s \<longrightarrow> tc = idle_context s)\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  apply (wp globals_equiv_scheduler_inv' kernel_entry_if_globals_equiv)
   apply (clarsimp)
   apply assumption
  apply clarsimp
  done

lemma domain_fields_equiv_lift:
  assumes a: "\<And>P. \<lbrace>domain_fields P and Q\<rbrace> f \<lbrace>\<lambda>_. domain_fields P\<rbrace>"
  assumes b: "\<And>P. \<lbrace>(\<lambda>s. P (cur_domain s)) and R\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
  shows "\<lbrace>domain_fields_equiv st and Q and R\<rbrace> f \<lbrace>\<lambda>_. domain_fields_equiv st\<rbrace>"
  apply (clarsimp simp: valid_def domain_fields_equiv_def)
  apply (erule use_valid, wp a b)
  apply simp
  done

lemma check_active_irq_if_partitionIntegrity:
  "check_active_irq_if tc \<lbrace>partitionIntegrity aag st\<rbrace>"
  apply (simp add: check_active_irq_if_def)
  apply (wp dmo_getActiveIRQ_wp)
  apply (simp add: partitionIntegrity_def integrity_subjects_def)
  apply (simp add: silc_dom_equiv_def equiv_for_def globals_equiv_scheduler_def)
  apply (fastforce simp: domain_fields_equiv_def)
  done

lemma do_machine_op_globals_equiv_scheduler:
   "(\<And>s sa. \<lbrakk> P sa; globals_equiv_scheduler s sa \<rbrakk>
              \<Longrightarrow> \<forall>x \<in> fst (f (machine_state sa)).
                    globals_equiv_scheduler s (sa\<lparr>machine_state := snd x\<rparr>))
    \<Longrightarrow> \<lbrace>globals_equiv_scheduler s and P\<rbrace>
        do_machine_op f
        \<lbrace>\<lambda>_. globals_equiv_scheduler s\<rbrace>"
  unfolding do_machine_op_def by (wp | simp add: split_def)+

lemma dmo_user_memory_update_globals_equiv_scheduler:
  "\<lbrace>globals_equiv_scheduler st and
    (invs and (\<lambda>s. pl = ptable_lift t s |` {x. pr x \<noteq> {}} \<and> pr = ptable_rights t s))\<rbrace>
   do_machine_op
     (user_memory_update ((ba |` {y. \<exists>x. pl x = Some y \<and> AllowWrite \<in> pr x} \<circ> addrFromPPtr) |` S))
   \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  apply (rule do_machine_op_globals_equiv_scheduler)
  apply clarsimp
  apply (erule use_valid)
   apply (simp add: user_memory_update_def)
   apply (wp modify_wp)
  apply (clarsimp simp: globals_equiv_scheduler_def split: option.splits)
  done

lemma dmo_device_memory_update_globals_equiv_scheduler:
  "\<lbrace>globals_equiv_scheduler st and (\<lambda>s. device_region s = S)\<rbrace>
   do_machine_op
     (device_memory_update ((ba |` {y. \<exists>x. pl x = Some y \<and> AllowWrite \<in> pr x} \<circ> addrFromPPtr) |` S))
   \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  apply (rule do_machine_op_globals_equiv_scheduler)
  apply clarsimp
  apply (simp add: device_memory_update_def simpler_modify_def)
  apply (clarsimp simp: globals_equiv_scheduler_def split: option.splits)
  done

lemma pas_refined_pasMayActivate_update[simp]:
  "pas_refined (aag\<lparr>pasMayActivate := x, pasMayEditReadyQueues := x\<rparr>) s =
   pas_refined (aag :: 'a subject_label PAS) s"
  apply (simp add: pas_refined_def irq_map_wellformed_aux_def tcb_domain_map_wellformed_aux_def)
  apply (simp add: state_asids_to_policy_pasMayActivate_update[simplified]
                  state_irqs_to_policy_pasMayActivate_update
                  state_asids_to_policy_pasMayEditReadyQueues_update[simplified]
                  state_irqs_to_policy_pasMayEditReadyQueues_update)
  done

lemma activate_thread_globals_equiv_scheduler:
  "\<lbrace>globals_equiv_scheduler st and valid_arch_state and valid_idle\<rbrace>
   activate_thread
   \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  by (wp globals_equiv_scheduler_inv' activate_thread_globals_equiv | force | fastforce)+

lemma schedule_cur_domain:
  "\<lbrace>\<lambda>s. P (cur_domain s) \<and> domain_time s \<noteq> 0\<rbrace>
   schedule
   \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
   (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  supply hoare_pre_cont[where a=next_domain, wp add]
         ethread_get_wp[wp del] if_split[split del] if_cong[cong]
  apply (simp add: schedule_def schedule_choose_new_thread_def | wp | wpc)+
               apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_strengthen_post)
                apply (simp | wp gts_wp | wp (once) hoare_drop_imps)+
               apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_strengthen_post)
                apply (simp | wp gts_wp | wp (once) hoare_drop_imps)+
      apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_strengthen_post)
       apply (simp | wp gts_wp | wp (once) hoare_drop_imps)+
  apply (clarsimp split: if_split)
  done

lemma schedule_domain_fields:
  "\<lbrace>domain_fields P and (\<lambda>s. domain_time s \<noteq> 0)\<rbrace>
   schedule
   \<lbrace>\<lambda>_. domain_fields P\<rbrace>"
   (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  supply hoare_pre_cont[where a=next_domain, wp add]
         ethread_get_wp[wp del] if_split[split del] if_cong[cong]
  apply (simp add: schedule_def schedule_choose_new_thread_def | wp | wpc)+
               apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_strengthen_post)
                apply (simp | wp gts_wp | wp (once) hoare_drop_imps)+
               apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_strengthen_post)
                apply (simp | wp gts_wp | wp (once) hoare_drop_imps)+
      apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_strengthen_post)
       apply (simp | wp gts_wp | wp (once) hoare_drop_imps)+
  apply (clarsimp split: if_split)
  sorry (* FIXME: Broken by experimental-tpspec -robs.
  done
*)

lemma schedule_if_partitionIntegrity:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "\<lbrace>partitionIntegrity aag st and guarded_pas_domain aag and pas_cur_domain aag and
          (\<lambda>s. domain_time s \<noteq> 0) and silc_inv aag st and einvs and pas_refined aag\<rbrace>
         schedule_if tc
         \<lbrace>\<lambda>_. partitionIntegrity aag st\<rbrace>"
  apply (simp add: schedule_if_def)
  apply (rule_tac Q="\<lambda>rv s. integrity (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                                      (scheduler_affects_globals_frame st) st s \<and>
                            domain_fields_equiv st s \<and> idle_thread s = idle_thread st \<and>
                            globals_equiv_scheduler st s \<and> silc_dom_equiv aag st s"
               in hoare_strengthen_post)
   apply (wpsimp wp: activate_thread_integrity activate_thread_globals_equiv_scheduler
                     silc_dom_equiv_from_silc_inv_valid'[where P="\<top>"] schedule_integrity
                     hoare_vcg_all_lift domain_fields_equiv_lift[where Q="\<top>" and R="\<top>"])
    apply (rule_tac Q="\<lambda>r s. guarded_pas_domain aag s \<and> pas_cur_domain aag s \<and>
                             domain_fields_equiv st s \<and> idle_thread s = idle_thread st \<and>
                             globals_equiv_scheduler st s \<and> silc_inv aag st s \<and>
                             silc_dom_equiv aag st s \<and> invs s" in hoare_strengthen_post)
     apply (wp schedule_guarded_pas_domain schedule_cur_domain
               silc_dom_equiv_from_silc_inv_valid'[where P="\<top>" and st=st]
               domain_fields_equiv_lift schedule_cur_domain schedule_domain_fields
            | simp add: silc_inv_def partitionIntegrity_def guarded_pas_domain_def
                        invs_valid_idle silc_dom_equiv_def)+
    apply (fastforce simp: equiv_for_refl dest: domains_distinct[THEN pas_domains_distinct_inj])
   apply (fastforce simp: partitionIntegrity_def globals_equiv_scheduler_def)+
  done

lemma partitionIntegrity_integrity:
  "partitionIntegrity aag s s'
   \<Longrightarrow> integrity (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                 (scheduler_affects_globals_frame s) s s'"
  by (clarsimp simp: partitionIntegrity_def)

lemma receive_blocked_on_eq:
  "\<lbrakk> receive_blocked_on ep ts; receive_blocked_on ep' ts \<rbrakk>
     \<Longrightarrow> ep = ep'"
  by (case_tac ts; simp)

lemma receive_blocked_on_eq':
  "\<lbrakk> receive_blocked_on ep ts; blocked_on ep' ts \<rbrakk>
     \<Longrightarrow> ep = ep'"
  by (case_tac ts; simp)

lemma receive_blocked_on_contradiction:
  "\<lbrakk> receive_blocked_on ep ts; send_blocked_on ep' ts \<rbrakk>
     \<Longrightarrow> False"
  by (case_tac ts; simp)

lemma pas_refined_tcb_st_to_auth:
  "\<lbrakk> pas_refined aag s; (ep, auth) \<in> tcb_st_to_auth (tcb_state tcb); kheap s p = Some (TCB tcb) \<rbrakk>
     \<Longrightarrow> (pasObjectAbs aag p, auth, pasObjectAbs aag ep) \<in> pasPolicy aag"
  apply (rule pas_refined_mem)
   apply (rule_tac s=s in sta_ts)
   apply (simp add: thread_st_auth_def tcb_states_of_state_def get_tcb_def)
  apply assumption
  done

(* FIXME DO _state abreviation for all elements and use them to write rule explicitely *)

lemmas integrity_subjects_obj =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct1]

lemmas integrity_subjects_eobj =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct1]

lemmas integrity_subjects_cdt =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct1]

lemmas integrity_subjects_cdt_list =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]

lemmas integrity_subjects_interrupts =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]

lemmas integrity_subjects_ready_queues =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]

lemmas integrity_subjects_mem =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]

lemmas integrity_subjects_device =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]

lemmas integrity_subjects_asids =
  integrity_subjects_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]

lemma pas_wellformed_pasSubject_update_Control:
  "\<lbrakk> pas_wellformed (aag\<lparr>pasSubject := pasObjectAbs aag p\<rparr>);
     (pasObjectAbs aag p, Control, pasObjectAbs aag p') \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag p = pasObjectAbs aag p'"
  by (fastforce simp: policy_wellformed_def)

lemma pas_wellformed_noninterference_policy_refl:
  "\<lbrakk> pas_wellformed_noninterference aag; pasObjectAbs aag x \<noteq> SilcLabel \<rbrakk>
     \<Longrightarrow> (pasObjectAbs aag x, auth, pasObjectAbs aag x) \<in> pasPolicy aag"
  unfolding pas_wellformed_noninterference_def
  by (fastforce intro!:aag_wellformed_refl)

lemma pas_wellformed_noninterference_control_to_eq:
  "\<lbrakk> pas_wellformed_noninterference aag;
     (pasObjectAbs aag x, Control, l) \<in> pasPolicy aag; pasObjectAbs aag x \<noteq> SilcLabel \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag x = l"
  unfolding pas_wellformed_noninterference_def
  by (erule aag_wellformed_Control; fastforce)

(* FIXME: MOVE *)
lemma fun_noteqD:
  "f \<noteq> g \<Longrightarrow> \<exists>a. f a \<noteq> g a"
  by blast


locale Noninterference_1 =
  fixes current_aag :: "det_state \<Rightarrow> 'a subject_label PAS"
  and arch_globals_equiv_strengthener :: "machine_state \<Rightarrow> machine_state \<Rightarrow> bool"
  assumes do_user_op_if_integrity:
    "\<lbrace>invs and integrity aag X st and is_subject aag \<circ> cur_thread and pas_refined aag\<rbrace>
     do_user_op_if uop tc
     \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  and do_user_op_if_globals_equiv_scheduler:
    "\<lbrace>globals_equiv_scheduler st and invs\<rbrace>
     do_user_op_if uop tc
     \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  and do_user_op_if_silc_dom_equiv[wp]:
    "do_user_op_if uop tc \<lbrace>silc_dom_equiv (aag :: 'a subject_label PAS) st\<rbrace>"
  and sameFor_scheduler_affects_equiv:
    "\<And>s s'. \<lbrakk> (s,s') \<in> same_for aag PSched; (s,s') \<in> same_for aag (Partition l');
              invs (internal_state_if s); invs (internal_state_if s') \<rbrakk>
              \<Longrightarrow> scheduler_equiv aag (internal_state_if s) (internal_state_if s') \<and>
                  scheduler_affects_equiv aag (OrdinaryLabel l')
                                          (internal_state_if s) (internal_state_if s')"
  and do_user_op_if_partitionIntegrity:
    "\<And>aag :: 'a subject_label PAS.
     \<lbrace>partitionIntegrity aag st and pas_refined aag and invs and is_subject aag \<circ> cur_thread\<rbrace>
     do_user_op_if uop tc
     \<lbrace>\<lambda>_. partitionIntegrity aag st\<rbrace>"
  and arch_activate_idle_thread_reads_respects_g[wp]:
    "reads_respects_g aag l \<top> (arch_activate_idle_thread t)"
  and dmo_storeWord_reads_respects_g[wp]:
    "reads_respects_g aag l \<top> (do_machine_op (storeWord ptr w))"
  and integrity_asids_update_reference_state:
   "is_subject aag t
    \<Longrightarrow> integrity_asids aag {pasSubject aag} x asid s (s\<lparr>kheap := kheap s(t \<mapsto> blah)\<rparr>)"
  and partitionIntegrity_subjectAffects_aobj:
    "\<lbrakk> partitionIntegrity aag s s'; kheap s x = Some (ArchObj ao); kheap s x \<noteq> kheap s' x;
       silc_inv aag st s; pas_refined aag s; pas_wellformed_noninterference aag \<rbrakk>
       \<Longrightarrow> subject_can_affect_label_directly aag (pasObjectAbs aag x)"
  and partitionIntegrity_subjectAffects_asid:
    "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s; valid_objs s; valid_arch_state s;
       valid_arch_state s'; pas_wellformed_noninterference aag; silc_inv aag st s'; invs s';
       \<not> equiv_asids (\<lambda>x. pasASIDAbs aag x = a) s s'\<rbrakk>
       \<Longrightarrow> a \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  and arch_switch_to_thread_reads_respects_g':
    "equiv_valid (reads_equiv_g aag) (affects_equiv aag l)
                 (\<lambda>s s'. affects_equiv aag l s s' \<and>
                         arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
                 (\<lambda>s. is_subject aag t) (arch_switch_to_thread t)"
  and arch_globals_equiv_strengthener_thread_independent:
    "arch_globals_equiv_strengthener (machine_state s) (machine_state s')
     \<Longrightarrow> \<forall>ct ct' it it'. arch_globals_equiv ct it (kheap s) (kheap s')
                           (arch_state s) (arch_state s') (machine_state s) (machine_state s') =
                         arch_globals_equiv ct' it' (kheap s) (kheap s')
                           (arch_state s) (arch_state s') (machine_state s) (machine_state s')"
  and ev2_invisible':
    "\<lbrakk> pas_domains_distinct aag; labels_are_invisible aag l L; labels_are_invisible aag l L';
       modifies_at_most aag L Q f; modifies_at_most aag L' Q' g;
       doesnt_touch_globals Q f; doesnt_touch_globals Q' g;
       \<And>st :: det_state. f \<lbrace>\<lambda>s. arch_globals_equiv_strengthener (machine_state st) (machine_state s)\<rbrace>;
       \<And>st :: det_state. g \<lbrace>\<lambda>s. arch_globals_equiv_strengthener (machine_state st) (machine_state s)\<rbrace>;
       \<forall>s t. P s \<and> P' t \<longrightarrow> (\<forall>(rva,s') \<in> fst (f s). \<forall>(rvb,t') \<in> fst (g t). W rva rvb) \<rbrakk>
       \<Longrightarrow> equiv_valid_2 (reads_equiv_g aag)
                         (\<lambda>s s'. affects_equiv aag l s s' \<and>
                                 arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
                         (\<lambda>s s'. affects_equiv aag l s s' \<and>
                                 arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
                         (W :: unit \<Rightarrow> unit \<Rightarrow> bool) (P and Q) (P' and Q') f g"
  and arch_switch_to_idle_thread_reads_respects_g[wp]:
    "reads_respects_g aag l \<top> (arch_switch_to_idle_thread)"
  and arch_globals_equiv_threads_eq:
    "arch_globals_equiv t' t'' kh kh' as as' ms ms'
     \<Longrightarrow> arch_globals_equiv t t kh kh' as as' ms ms'"
  and arch_globals_equiv_globals_equiv_scheduler[elim]:
    "arch_globals_equiv (cur_thread s') (idle_thread s) (kheap s) (kheap s')
                        (arch_state s) (arch_state s') (machine_state s) (machine_state s')
     \<Longrightarrow> arch_globals_equiv_scheduler (kheap s) (kheap s') (arch_state s) (arch_state s')"
  and getActiveIRQ_ret_no_dmo[wp]:
    "\<lbrace>\<top>\<rbrace> getActiveIRQ in_kernel \<lbrace>\<lambda>rv s. \<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ\<rbrace>"
  and dmo_getActive_IRQ_reads_respect_scheduler:
    "reads_respects_scheduler aag l (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
                             (do_machine_op (getActiveIRQ in_kernel))"
  (* FIXME IF: precludes ARM_HYP *)
  and getActiveIRQ_no_non_kernel_IRQs:
    "getActiveIRQ True = getActiveIRQ False"
begin

lemma integrity_update_reference_state:
  "\<lbrakk> is_subject aag t; integrity aag X st s; st = st'\<lparr>kheap := kheap st'(t \<mapsto> blah)\<rparr> \<rbrakk>
     \<Longrightarrow> integrity (aag :: 'a subject_label PAS) X st' s"
  apply (erule integrity_trans[rotated])
  apply (clarsimp simp: integrity_def opt_map_def integrity_asids_update_reference_state)
  done

(* lots of ugly hackery because handle_event_integrity wants the reference state to
   be identical to the initial one, but it isn't because we first update the
   context of cur_thread *)
lemma kernel_entry_if_integrity:
  "\<lbrace>einvs and schact_is_rct and pas_refined aag and is_subject aag \<circ> cur_thread
          and domain_sep_inv (pasMaySendIrqs aag) st' and guarded_pas_domain aag
          and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s) and (=) st\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_. integrity (aag :: 'a subject_label PAS) X st\<rbrace>"
  unfolding kernel_entry_if_def
  apply wp
     apply (rule valid_validE)
     apply (rule_tac Q="\<lambda>_ s. integrity aag X (st\<lparr>kheap :=
                         (kheap st)(cur_thread st \<mapsto> TCB (tcb_arch_update (arch_tcb_context_set tc)
                                                            (the (get_tcb (cur_thread st) st))))\<rparr>) s
                       \<and> is_subject aag (cur_thread s)
                       \<and> cur_thread s = cur_thread st" in hoare_strengthen_post)
      apply (wp handle_event_integrity handle_event_cur_thread | simp)+
     apply (fastforce intro: integrity_update_reference_state)
    apply (wp thread_set_integrity_autarch thread_set_pas_refined guarded_pas_domain_lift
              thread_set_invs_trivial thread_set_not_state_valid_sched
           | simp add: tcb_cap_cases_def schact_is_rct_def arch_tcb_update_aux2)+
    apply (wp (once) prop_of_two_valid[where f="ct_active" and g="cur_thread"])
      apply (wp | simp)+
    apply (wp thread_set_tcb_context_update_wp)+
  apply (clarsimp simp: schact_is_rct_def)
  apply (rule conjI)
   apply (erule integrity_update_reference_state[where blah="the (kheap st (cur_thread st))",
                                                 OF _ integrity_refl])
   apply simp
   apply (subgoal_tac "kheap st (cur_thread st) \<noteq> None")
    apply clarsimp
   apply (drule tcb_at_invs, clarsimp simp: tcb_at_def get_tcb_def
                                     split: kernel_object.splits option.splits)
  apply (clarsimp simp: invs_psp_aligned invs_vspace_objs invs_arch_state)
  apply (rule conjI)
   apply assumption
  apply (rule state.equality, simp_all)
  apply (rule ext, simp_all)
  done

lemma kernel_entry_if_partitionIntegrity:
  "\<lbrace>silc_inv aag st and pas_refined aag and einvs and schact_is_rct
                    and is_subject aag \<circ> cur_thread and domain_sep_inv (pasMaySendIrqs aag) st'
                    and guarded_pas_domain aag and (\<lambda>s. ev \<noteq> Interrupt \<and> ct_active s) and (=) st\<rbrace>
   kernel_entry_if ev tc
   \<lbrace>\<lambda>_. partitionIntegrity (aag :: 'a subject_label PAS) st\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. (\<forall>X. integrity (aag\<lparr>pasMayActivate := False,
                                                pasMayEditReadyQueues := False\<rparr>) X st s) \<and>
                            domain_fields_equiv st s \<and> globals_equiv_scheduler st s \<and>
                            idle_thread s = idle_thread st \<and> silc_dom_equiv aag st s"
               in hoare_strengthen_post)
   apply (wp hoare_vcg_conj_lift)
     apply (rule hoare_vcg_all_lift[OF kernel_entry_if_integrity[where st'=st']])
    sorry (* XXX: broken by touched_addresses. -robs
    apply (wp kernel_entry_if_cur_thread kernel_entry_if_globals_equiv_scheduler
              kernel_entry_if_cur_domain domain_fields_equiv_lift[where R="\<top>"]
              kernel_entry_if_domain_fields | simp)+
    apply (rule_tac P="pas_refined aag and einvs and schact_is_rct and
                       is_subject aag \<circ> cur_thread and domain_sep_inv (pasMaySendIrqs aag) st' and
                       (\<lambda> s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)"
                 in silc_dom_equiv_from_silc_inv_valid')
    apply (wp kernel_entry_silc_inv[where st'=st'], simp add: schact_is_rct_simple)
   apply (fastforce simp: pas_refined_pasMayActivate_update pas_refined_pasMayEditReadyQueues_update
                          globals_equiv_scheduler_refl silc_dom_equiv_def equiv_for_refl
                          domain_fields_equiv_def ct_active_not_idle')
  apply (fastforce simp: partitionIntegrity_def)
  done
*)

text \<open>
  This a very important theorem that ensures that @{const subjectAffects} is
  coherent with @{const integrity_obj}
\<close>
lemma partitionIntegrity_subjectAffects_obj:
  assumes par_inte: "partitionIntegrity (aag :: 'a subject_label PAS) s s'"
  assumes pas_ref: "pas_refined aag s"
  assumes invs: "invs s"
  assumes pwni: "pas_wellformed_noninterference aag"
  assumes silc_inv: "silc_inv aag st s"
  assumes kh_diff: "kheap s x \<noteq> kheap s' x"
  notes inte_obj = par_inte[THEN partitionIntegrity_integrity, THEN integrity_subjects_obj,
                            THEN spec[where x=x], simplified integrity_obj_def, simplified]
  shows "pasObjectAbs aag x \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"

proof -
  show ?thesis
    using inte_obj
  proof (induct "kheap s x" rule: converse_rtranclp_induct)
    case base
    thus ?case using kh_diff by force
  next
    case (step z)
    note troa = step.hyps(1)
    show ?case
    proof (cases "z = kheap s x")
      case True
      thus ?thesis using step.hyps by blast
    next
      case False
      note hyps = this pwni pas_ref invs silc_inv kh_diff
      hence sym_helper: "\<And>auth tcb. kheap s x = Some (TCB tcb) \<Longrightarrow>
                                    (pasObjectAbs aag x, auth, pasObjectAbs aag x) \<in> pasPolicy aag"
        by (fastforce elim!: pas_wellformed_noninterference_policy_refl
                             silc_inv_cnode_onlyE obj_atE
                       simp: is_cap_table_def)
      show ?thesis
        using troa
      proof (cases rule: integrity_obj_atomic.cases)
        case troa_lrefl
        thus ?thesis by (fastforce intro: subjectAffects.intros)
      next
        case (troa_ntfn ntfn ntfn' auth s)
        thus ?thesis by (fastforce intro: affects_ep)
      next
        case (troa_ep ep ep' auth s)
        thus ?thesis by (fastforce intro: affects_ep)
      next
        case (troa_ep_unblock ep ep' tcb ntfn)
        thus ?thesis by (fastforce intro: affects_ep_bound_trans)
      next
        case (troa_tcb_send tcb tcb' ctxt' ep)
        thus ?thesis using hyps
          apply (clarsimp simp: direct_send_def indirect_send_def)
          apply (erule disjE)
           apply (clarsimp simp: receive_blocked_on_def2)
           apply (frule (2) pas_refined_tcb_st_to_auth)
           apply (fastforce intro!: affects_send sym_helper)
          apply (fastforce intro!: affects_send bound_tcb_at_implies_receive
                                   pred_tcb_atI sym_helper)
          done
      next
        case (troa_tcb_call tcb tcb' caller R ctxt' ep)
        thus ?thesis using hyps
          apply (clarsimp simp add: direct_call_def ep_recv_blocked_def)
          apply (rule affects_send[rotated 2])
             apply (erule (1) pas_refined_tcb_st_to_auth[rotated 2]; force)
            apply (fastforce intro: sym_helper)
           apply assumption
          apply blast
          done
      next
        case (troa_tcb_reply tcb tcb' new_st ctxt')
        thus ?thesis using hyps
          apply clarsimp
          apply (erule affects_reply)
          by (rule sym_helper)
      next
        case (troa_tcb_receive tcb tcb' new_st ep)
        thus ?thesis using hyps
          by (auto intro: affects_recv pas_refined_tcb_st_to_auth simp: send_blocked_on_def2)
      next
        case (troa_tcb_restart tcb tcb' ep)
        thus ?thesis using hyps
          by (fastforce intro: affects_reset[where auth=Receive] affects_reset[where auth=SyncSend]
                         elim: blocked_on.elims pas_refined_tcb_st_to_auth[rotated 2]
                       intro!: sym_helper)
      next
        case (troa_tcb_unbind tcb tcb')
        thus ?thesis using hyps
          apply -
          by (cases "tcb_bound_notification tcb" ;
              fastforce intro: affects_reset[where auth=Receive] bound_tcb_at_implies_receive
                               pred_tcb_atI sym_helper)
      next
        case (troa_tcb_empty_ctable tcb tcb' cap')
        thus ?thesis using hyps
          apply (clarsimp simp:reply_cap_deletion_integrity_def; elim disjE; clarsimp)
          apply (rule affects_delete_derived)
          apply (rule aag_wellformed_delete_derived[rotated -1, OF pas_refined_wellformed],
                 assumption)
          apply (frule cap_auth_caps_of_state[rotated,where p ="(x,tcb_cnode_index 0)"],
                 force simp: caps_of_state_def')
          by (fastforce simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
                       split: if_splits)
      next
        case (troa_tcb_empty_caller tcb tcb' cap')
        thus ?thesis using hyps
          apply (clarsimp simp:reply_cap_deletion_integrity_def)
          apply (elim disjE; clarsimp)
          apply (rule affects_delete_derived)
          apply (rule aag_wellformed_delete_derived[rotated -1, OF pas_refined_wellformed],
                 assumption)
          apply (frule cap_auth_caps_of_state[rotated,where p ="(x,tcb_cnode_index 3)"],
                 force simp: caps_of_state_def')
          by (fastforce simp: aag_cap_auth_def cap_auth_conferred_def
                              reply_cap_rights_to_auth_def
                       split: if_splits)
      next
        case (troa_tcb_activate tcb tcb')
        thus ?thesis by blast
      next
        case (troa_arch ao ao')
        thus ?thesis
          using assms by (fastforce dest: partitionIntegrity_subjectAffects_aobj)
      next
        case (troa_cnode n content content')
        thus ?thesis
          using hyps unfolding cnode_integrity_def
          apply clarsimp
          apply (drule fun_noteqD)
          apply (erule exE, rename_tac l)
          apply (drule_tac x=l in spec)
          apply (clarsimp dest!:not_sym[where t=None])
          apply (clarsimp simp:reply_cap_deletion_integrity_def)
          apply (rule affects_delete_derived)
          apply (rule aag_wellformed_delete_derived[rotated -1, OF pas_refined_wellformed],
                 assumption)
          apply (frule_tac p="(x,l)" in cap_auth_caps_of_state[rotated])
           apply (force simp: caps_of_state_def' intro:well_formed_cnode_invsI)
          by (fastforce simp: aag_cap_auth_def cap_auth_conferred_def
                              reply_cap_rights_to_auth_def
                       split: if_splits)
      qed
    qed
  qed
qed

end


lemma kheap_ep_tcb_states_of_state_eq:
  "kheap s x = kheap s' x \<Longrightarrow> tcb_states_of_state s x = tcb_states_of_state s' x"
  unfolding tcb_states_of_state_def get_tcb_def by simp

lemma partitionIntegrity_subjectAffects_mem:
  assumes par_inte: "partitionIntegrity aag s s'"
  assumes pas_ref: "pas_refined aag s"
  assumes invs: "invs s"
  assumes um_diff:
    "underlying_memory (machine_state s) x \<noteq> underlying_memory (machine_state s') x"
  notes inte_mem =
    par_inte[THEN partitionIntegrity_integrity, THEN integrity_subjects_mem, THEN spec[where x=x]]
  shows
  "pasObjectAbs aag x \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  using inte_mem
  proof (cases rule: integrity_mem.cases)
    case trm_lrefl
    thus ?thesis by (fastforce intro: affects_lrefl)
  next
    case trm_orefl
    thus ?thesis using um_diff by blast
  next
    case trm_write
    thus ?thesis by (fastforce intro: affects_write)
  next
    case trm_globals
    thus ?thesis by blast
  next
    case (trm_ipc p) note trm_ipc_hyps = this
    then obtain tcbst where "tcb_states_of_state s p = Some tcbst" "can_receive_ipc tcbst"
      by (force split:option.splits)
    note hyps = this trm_ipc_hyps(2-)[simplified] pas_ref invs um_diff
    from par_inte[THEN partitionIntegrity_integrity, THEN integrity_subjects_obj,
                  THEN spec[where x=p], THEN tro_tro_alt]
    show ?thesis
    proof (cases rule: integrity_obj_alt.cases)
      case (tro_alt_tcb_send tcb tcb' ccap' cap' ntfn' ep)
      thus ?thesis using hyps
        apply (clarsimp simp: direct_send_def indirect_send_def)
        apply (erule disjE)
         apply (clarsimp simp: receive_blocked_on_def2)
         apply (frule (2) pas_refined_tcb_st_to_auth)
         apply (fastforce intro!: affects_send auth_ipc_buffers_mem_Write')
        apply clarsimp
        apply (rule affects_send[rotated 2])
           apply (fastforce intro!: affects_send bound_tcb_at_implies_receive pred_tcb_atI
                              dest: sym)
          apply (fastforce intro!: auth_ipc_buffers_mem_Write')
         apply assumption
        apply blast
        done
    next
      case (tro_alt_tcb_call tcb tcb' ccap' cap' ntfn' caller R ep)
      thus ?thesis using hyps
        apply (clarsimp simp add: direct_call_def ep_recv_blocked_def)
        apply (rule affects_send[rotated 2])
           apply (erule (1) pas_refined_tcb_st_to_auth[rotated 2]; force)
          apply (fastforce intro!: auth_ipc_buffers_mem_Write')
         apply assumption
        apply blast
        done
    next
      case (tro_alt_tcb_reply tcb tcb' ccap' cap' ntfn' new_st)
      thus ?thesis using hyps
        apply (clarsimp simp: direct_reply_def)
        apply (erule affects_reply)
        by (force intro: auth_ipc_buffers_mem_Write')
    next
      case (tro_alt_tcb_receive tcb tcb' ccap' cap' ntfn' new_st ep)
      thus ?thesis using hyps
        apply (clarsimp elim!: tcb_states_of_state_kheapE send_blocked_on.elims
                               can_receive_ipc.elims)
        apply (frule (1) pas_refined_tcb_st_to_auth[rotated 2,where auth=Call and ep =ep])
         apply force
        apply (rule affects_reply)
         apply (erule (1) aag_wellformed_reply, force)
        apply (fastforce intro!: auth_ipc_buffers_mem_Write')
        done
    next
      case (tro_alt_tcb_restart tcb tcb' ccap' cap' ntfn' ep)
      thus ?thesis using hyps
        by (fastforce intro: affects_reset[where auth=Receive] affects_reset[where auth=SyncSend]
                       elim: blocked_on.elims pas_refined_tcb_st_to_auth[rotated 2]
                     intro!: auth_ipc_buffers_mem_Write')
    qed (insert hyps, force elim: tcb_states_of_state_kheapE)+
  qed

lemma partitionIntegrity_subjectAffects_cdt:
  "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s;
     valid_mdb s; valid_objs s; cdt s (x,y) \<noteq> cdt s' (x,y) \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag x \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (drule partitionIntegrity_integrity)
  apply (drule integrity_subjects_cdt)
  apply (drule_tac x="(x,y)" in spec)
  apply (clarsimp simp: integrity_cdt_def)
  apply (rule affects_delete_derived)
  apply (frule (3) cdt_change_allowed_delete_derived)
  by simp

lemma partitionIntegrity_subjectAffects_cdt_list:
  "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s; pas_refined aag s';
     valid_list s; valid_list s'; silc_inv aag st s; silc_inv aag st' s';
     pas_wellformed_noninterference aag; invs s; invs s'; cdt_list s (x,y) \<noteq> cdt_list s' (x,y) \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag x \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (drule partitionIntegrity_integrity)
  apply (drule integrity_subjects_cdt_list)
  apply (simp add: integrity_cdt_list_def)
  apply (drule_tac x="x" in spec)
  apply (drule_tac x="y" in spec)
  apply (elim disjE)
   apply (drule(1) neq_filtered_ex)
   apply (elim bexE)
   apply (case_tac "pasObjectAbs aag x = SilcLabel")
    apply (subgoal_tac "pasObjectAbs aag (fst xa) = SilcLabel")
     apply simp
     apply (rule affects_delete_derived)
     apply (frule (3) cdt_change_allowed_delete_derived[OF invs_valid_objs invs_mdb])
     apply force
    subgoal by (fastforce simp add: silc_inv_def valid_list_2_def all_children_def
                          simp del: split_paired_All)
   apply (rule affects_delete_derived2)
    apply (frule (3) cdt_change_allowed_delete_derived[OF invs_valid_objs invs_mdb])
    apply assumption
   subgoal by (fastforce dest!: aag_cdt_link_DeleteDerived
                         simp add: valid_list_2_def
                         simp del: split_paired_All)
  apply (rule affects_delete_derived)
  apply (frule(3) cdt_change_allowed_delete_derived[OF invs_valid_objs invs_mdb])
  by simp

lemma partitionIntegrity_subjectAffects_is_original_cap:
  "\<lbrakk>partitionIntegrity aag s s'; pas_refined aag s; valid_mdb s; valid_objs s;
    is_original_cap s (x,y) \<noteq> is_original_cap s' (x,y)\<rbrakk> \<Longrightarrow>
   pasObjectAbs aag x
     \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (drule partitionIntegrity_integrity)
  apply (drule integrity_subjects_cdt)
  apply (drule_tac x="(x,y)" in spec)
  apply (clarsimp simp: integrity_cdt_def)
  apply (rule affects_delete_derived)
  apply (frule (3) cdt_change_allowed_delete_derived)
  by simp

lemma partitionIntegrity_subjectAffects_interrupt_states:
  "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s;
     valid_objs s; interrupt_states s x \<noteq> interrupt_states s' x \<rbrakk>
     \<Longrightarrow> pasIRQAbs aag x \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (drule partitionIntegrity_integrity)
  apply (drule integrity_subjects_interrupts)
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: integrity_interrupts_def)
  apply (rule affects_lrefl)
  done

lemma partitionIntegrity_subjectAffects_interrupt_irq_node:
  "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s; valid_objs s;
     interrupt_irq_node s x \<noteq> interrupt_irq_node s' x \<rbrakk>
     \<Longrightarrow> pasIRQAbs aag x \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (drule partitionIntegrity_integrity)
  apply (drule integrity_subjects_interrupts)
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: integrity_interrupts_def)
  apply (rule affects_lrefl)
  done

lemma pas_wellformed_pasSubject_update:
  "\<lbrakk> pas_wellformed_noninterference aag; silc_inv aag st s; invs s;
     kheap s x = Some (TCB t) \<or> kheap s x = Some (ArchObj a) \<rbrakk>
     \<Longrightarrow> pas_wellformed (aag\<lparr>pasSubject := pasObjectAbs aag x\<rparr>)"
  apply (simp add: pas_wellformed_noninterference_def)
  apply (elim conjE)
  apply (erule bspec)
  apply (clarsimp simp:  silc_inv_def obj_at_def split: kernel_object.splits)
  apply (drule spec, erule (1) impE)
  apply (fastforce simp: is_cap_table_def)
  done

lemma partitionIntegrity_subjectAffects_eobj:
  "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s;
     valid_objs s; einvs s; einvs s'; pas_wellformed_noninterference aag;
     silc_inv aag st s; silc_inv aag st' s'; ekheap s x \<noteq> ekheap s' x \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag x \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (drule partitionIntegrity_integrity)
  apply (drule integrity_subjects_eobj)
  apply (drule_tac x=x in spec)
  apply (erule integrity_eobj.cases)
   apply simp
   apply (rule subjectAffects.affects_lrefl)
  apply simp
  done

(*FIXME: Move*)
lemma prefix_helper:
  "\<lbrakk> a @ l = l'; distinct l; distinct l' \<rbrakk> \<Longrightarrow> set a \<inter> set l = {} \<and> set a \<subseteq> set l'"
  apply (induct l)
   apply simp+
  by (metis append_Cons disjoint_iff_not_equal distinct.simps(2) distinct_append
            distinct_length_2_or_more subset_code(1))

(*FIXME: Move*)
lemma valid_queuesE:
  assumes "valid_queues s"
  assumes "t \<in> set (ready_queues s d p)"
  assumes "\<lbrakk> is_etcb_at t s; etcb_at (\<lambda>t. tcb_priority t = p \<and> tcb_domain t = d) t s;
             st_tcb_at runnable t s; distinct (ready_queues s d p) \<rbrakk>
             \<Longrightarrow> R "
  shows R
  using assms by (clarsimp simp: valid_queues_def)

lemma valid_blocked_imp:
  "\<lbrakk> valid_blocked s; tcb_at t s; not_queued t s;
     t \<noteq> cur_thread s; scheduler_action s \<noteq> switch_thread t \<rbrakk>
     \<Longrightarrow> st_tcb_at (\<lambda>s. \<not> runnable s) t s"
  by (fastforce simp: valid_blocked_def st_tcb_at_def
                      tcb_at_st_tcb_at runnable_eq_active obj_at_def)

lemma valid_queues_not_in_place:
  "\<lbrakk> valid_queues s; t \<notin> set (ready_queues s d a);
     etcb_at (\<lambda>t. tcb_priority t = a \<and> tcb_domain t = d) t s; is_etcb_at t s\<rbrakk>
     \<Longrightarrow> not_queued t s"
  by (clarsimp simp: valid_queues_def not_queued_def etcb_at_def is_etcb_at_def
              split: option.splits)

lemma ready_queues_alters_kheap:
  assumes a: "valid_queues s"
  assumes b: "valid_blocked s"
  assumes c: "valid_idle s'"
  shows "\<lbrakk> ready_queues s d a \<noteq> ready_queues s' d a;
           threads @ ready_queues s d a = ready_queues s' d a; valid_queues s';
           valid_etcbs s; valid_etcbs s'; t \<in> set threads; ekheap s t = ekheap s' t;
           t \<noteq> idle_thread s \<longrightarrow> (t \<noteq> cur_thread s \<and> t \<noteq> cur_thread s');
           scheduler_action s \<noteq> switch_thread t; idle_thread s = idle_thread s' \<rbrakk>
           \<Longrightarrow> kheap s t \<noteq> kheap s' t"
  apply (frule prefix_helper)
    using a apply ((simp add: valid_queues_def)+)[2]
  apply clarsimp
  apply (drule(1) set_mp)
  apply (drule(1) orthD1)
  apply (erule(1) valid_queuesE)
  apply (subgoal_tac "tcb_at t s")
   apply (frule valid_blocked_imp[OF b])
      apply (rule valid_queues_not_in_place[OF a],assumption)
       apply (simp add: etcb_at_def)
      apply (simp add: is_etcb_at_def)
     using c apply (auto simp: pred_tcb_at_def tcb_at_st_tcb_at obj_at_def valid_idle_def)
   done

lemma valid_sched_valid_blocked: "valid_sched s \<Longrightarrow> valid_blocked s"
  by (simp add: valid_sched_def)


context Noninterference_1 begin

lemma partitionIntegrity_subjectAffects_ready_queues:
  assumes domains_distinct: "pas_domains_distinct (aag :: 'a subject_label PAS)"
  shows "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s; valid_objs s; einvs s; einvs s';
           pas_refined aag s'; pas_cur_domain aag s; pas_wellformed_noninterference aag;
           silc_inv aag st s; silc_inv aag st' s'; ready_queues s d \<noteq> ready_queues s' d;
           cur_thread s \<noteq> idle_thread s \<longrightarrow> is_subject aag (cur_thread s);
           cur_thread s' \<noteq> idle_thread s' \<longrightarrow> is_subject aag (cur_thread s') \<rbrakk>
           \<Longrightarrow> pasDomainAbs aag d \<inter> subjectAffects (pasPolicy aag) (pasSubject aag) \<noteq> {}"
  apply (clarsimp simp: disjoint_iff_not_equal)
  apply (frule valid_sched_valid_blocked[where s=s])
  apply (case_tac "pasSubject aag \<in> pasDomainAbs aag d")
   apply (metis affects_lrefl)
  apply (drule fun_noteqD,clarsimp)
  apply (clarsimp simp add: partitionIntegrity_def)
  apply (frule_tac d=d and p=a in integrity_subjects_ready_queues[rule_format])
  apply (clarsimp simp: integrity_ready_queues_def)
  apply (case_tac "threads = []")
   apply simp
  apply (erule not_NilE)
  apply (frule_tac x=x and d=d and p=a and s=s' in tcb_with_domain_at[OF valid_sched_valid_queues])
   apply (drule_tac t="ready_queues s' d a" in sym)
   apply simp
  apply clarsimp
  apply (frule(1) tcb_domain_wellformed)
  apply (rename_tac tcb_ptr tcbs tcb)
  apply (rule_tac x = "pasObjectAbs aag tcb_ptr" in bexI)
   apply (case_tac "scheduler_action s = switch_thread tcb_ptr")
    apply (drule switch_to_cur_domain[rotated])
      apply simp
     apply simp
    apply (fastforce dest: domains_distinct[THEN pas_domains_distinct_inj])
   apply (case_tac "ekheap s tcb_ptr \<noteq> ekheap s' tcb_ptr")
    apply (rule_tac s=s and s'=s' in partitionIntegrity_subjectAffects_eobj)
            apply (simp add: partitionIntegrity_def)+
   apply (subgoal_tac "kheap s tcb_ptr \<noteq> kheap s' tcb_ptr")
    apply (rule partitionIntegrity_subjectAffects_obj)
         apply (fastforce simp add: partitionIntegrity_def valid_sched_def)+
   apply (rule_tac threads="tcb_ptr # tcbs" in ready_queues_alters_kheap)
               apply (fastforce simp add: partitionIntegrity_def valid_sched_def)+
  done

end


lemma pas_refined_asid_mem:
  "\<lbrakk> v \<in> state_asids_to_policy aag s; pas_refined aag s \<rbrakk>
     \<Longrightarrow> v \<in> pasPolicy aag"
  by (auto simp add: pas_refined_def)

lemma sameFor_subject_def2:
  "sameFor_subject g ab irqab asidab domainab l =
     {(os,os') | os os' s s'. s = internal_state_if os \<and> s' = internal_state_if os' \<and>
                 (\<forall>d \<in> subjectReads g (OrdinaryLabel l).
                    states_equiv_for (\<lambda>x. ab x = d) (\<lambda>x. irqab x  = d)
                                     (\<lambda>x. asidab x = d) (\<lambda>x. d \<in> domainab x) s s') \<and>
                 ((domainab (cur_domain s) \<inter> subjectReads g (OrdinaryLabel l) \<noteq> {} \<or>
                   domainab (cur_domain s') \<inter> subjectReads g (OrdinaryLabel l) \<noteq> {})
                  \<longrightarrow> cur_domain s = cur_domain s' \<and> globals_equiv s s' \<and>
                      scheduler_action s = scheduler_action s' \<and>
                      work_units_completed s = work_units_completed s' \<and>
                      irq_state (machine_state s) = irq_state (machine_state s') \<and>
                      (user_modes (sys_mode_of os) \<longrightarrow> user_context_of os = user_context_of os') \<and>
                      sys_mode_of os = sys_mode_of os' \<and>
                      equiv_for (\<lambda>x. ab x = SilcLabel) kheap s s')}"
  apply (clarsimp simp: sameFor_subject_def)
  apply (rule equalityI)
   apply (rule subsetI)
   apply (drule CollectD)
   apply (rule CollectI)
   apply (clarify)
   apply (rule exI)+
   apply (rule conjI, rule refl)
   apply (rule conjI)
    apply (rule ballI)
    apply (erule states_equiv_for_guard_imp)
       apply (blast+)[4]
   apply (fastforce simp: globals_equiv_def)
  apply (rule subsetI)
  apply (drule CollectD)
  apply (rule CollectI)
  apply (clarify)
  apply (rule exI)+
  apply (rule conjI, rule refl)
  apply (rule conjI)
   apply (rule states_equiv_forI)
            apply ((fastforce intro: equiv_forI elim: states_equiv_forE equiv_forD)+)[5]
       apply (fastforce intro: equiv_forI elim: states_equiv_forE_is_original_cap)
      apply ((fastforce intro: equiv_forI elim: states_equiv_forE equiv_forD)+)[2]
    apply (solves \<open>clarsimp simp: equiv_asids_def states_equiv_for_def\<close>)
   apply (fastforce intro: equiv_forI elim: states_equiv_forE_ready_queues)
  apply fastforce
  done

text \<open>
  This lemma says that everything the current subject can affect, according to the
  integrity property, is included in @{term partsSubjectAffects}.
\<close>

lemma subject_can_affect_its_own_partition:
  "d \<notin> partsSubjectAffects (pasPolicy aag) (label_of (pasSubject aag))
   \<Longrightarrow> d \<noteq> Partition (label_of (pasSubject aag))"
  apply (erule contrapos_nn)
  apply (simp add: partsSubjectAffects_def image_def label_can_affect_partition_def)
  apply (blast intro: affects_lrefl)
  done

(* FIXME: cleanup this wonderful proof *)
lemma partitionIntegrity_subjectAffects_device:
  "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s; invs s; invs s';
     device_state (machine_state s) x \<noteq> device_state (machine_state s') x \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag x \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (drule partitionIntegrity_integrity)
  apply (frule integrity_subjects_device)
  apply (drule_tac x=x in spec)
  apply (erule integrity_device.cases)
    apply (fastforce intro: affects_lrefl)
   apply blast
  apply (fastforce intro: affects_write)
  done


(* a hack to prevent safe etc. below from taking apart the implication *)
definition guarded_is_subject_cur_thread
where
  "guarded_is_subject_cur_thread aag s \<equiv>
        cur_thread s \<noteq> idle_thread s \<longrightarrow> is_subject aag (cur_thread s)"


context Noninterference_1 begin

lemma partsSubjectAffects_bounds_subjects_affects:
  assumes domains_distinct: "pas_domains_distinct (aag :: 'a subject_label PAS)"
  shows "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s; pas_refined aag s'; valid_objs s;
           valid_arch_state s'; einvs s; einvs s'; silc_inv aag st s; silc_inv aag st' s';
           pas_wellformed_noninterference aag; pas_cur_domain aag s;
           guarded_is_subject_cur_thread aag s; guarded_is_subject_cur_thread aag s';
           d \<notin> partsSubjectAffects (pasPolicy aag) (label_of (pasSubject aag)); d \<noteq> PSched \<rbrakk>
           \<Longrightarrow> (((uc,s),mode),((uc',s'),mode')) \<in> same_for aag d"
  apply (frule pasSubject_not_SilcLabel)
  apply (erule contrapos_np)
  apply (cases d)
   prefer 2
   apply simp
  apply (clarsimp simp: sameFor_def sameFor_subject_def2 states_equiv_for_def equiv_for_def
                       partsSubjectAffects_def image_def label_can_affect_partition_def)
  apply (safe del: iffI notI)
                             apply (fastforce dest: partitionIntegrity_subjectAffects_obj)
                            apply ((auto dest: partitionIntegrity_subjectAffects_obj
                                               partitionIntegrity_subjectAffects_eobj
                                               partitionIntegrity_subjectAffects_mem
                                               partitionIntegrity_subjectAffects_device
                                               partitionIntegrity_subjectAffects_cdt
                                               partitionIntegrity_subjectAffects_cdt_list
                                               partitionIntegrity_subjectAffects_is_original_cap
                                               partitionIntegrity_subjectAffects_interrupt_states
                                               partitionIntegrity_subjectAffects_interrupt_irq_node
                                               partitionIntegrity_subjectAffects_asid
                                               partitionIntegrity_subjectAffects_ready_queues
                                                 [folded guarded_is_subject_cur_thread_def,
                                                  OF domains_distinct]
                                               domains_distinct[THEN pas_domains_distinct_inj]
                                    | fastforce simp: partitionIntegrity_def
                                                      silc_dom_equiv_def equiv_for_def)+)[11]
                 apply ((fastforce intro: affects_lrefl
                                   simp: partitionIntegrity_def domain_fields_equiv_def
                                   dest: domains_distinct[THEN pas_domains_distinct_inj])+)[16]
  done

end


lemma cur_thread_not_SilcLabel:
  "\<lbrakk> silc_inv aag st s; invs s \<rbrakk> \<Longrightarrow> pasObjectAbs aag (cur_thread s) \<noteq> SilcLabel"
  apply (rule notI)
  apply (simp add: silc_inv_def)
  apply (drule tcb_at_invs)
  apply clarify
  apply (drule_tac x="cur_thread s" in spec, erule (1) impE)
  apply (auto simp: obj_at_def is_tcb_def is_cap_table_def)
  apply (case_tac ko, simp_all)
  done

lemma ev_add_pre:
  "equiv_valid_inv I A P f \<Longrightarrow> equiv_valid_inv I A (P and Q) f"
  apply (rule equiv_valid_guard_imp)
   apply assumption
  apply simp
  done

crunch invs[wp]: check_active_irq_if "einvs"
  (wp: dmo_getActiveIRQ_wp ignore: do_machine_op)

crunch schact_is_rct[wp]: thread_set "schact_is_rct"
  (wp: get_object_wp simp: schact_is_rct_def)

definition partition :: "'a subject_label agent_domain_map \<Rightarrow> det_state \<Rightarrow> 'a" where
  "partition ab s \<equiv> label_of (the_elem (ab (cur_domain s)))"

lemma silc_inv_refl:
  "silc_inv aag st s \<Longrightarrow> silc_inv aag s s"
  by (fastforce simp: silc_inv_def silc_dom_equiv_def equiv_for_refl
              intro!: silc_inv_no_transferableD')


section \<open>Valid initial state is complete unwinding system\<close>

context valid_initial_state begin

text \<open>current running partition\<close>
definition part where
  "part s \<equiv> if scheduler_modes (sys_mode_of s) then PSched
             else Partition (partition (pasDomainAbs initial_aag) (internal_state_if s))"

text \<open>unwinding relation\<close>
definition uwr where
  "uwr \<equiv> same_for initial_aag"

end


text \<open>
  Here we are basically that the big step ADT of the kernel is a
  valid complete unwinding system on the policyFlow policy

  For those unfamiliar with the local subtleties, we are importing the all the facts
  of the complete_unwinding_system locale in the valid_initial_state locale under namespace ni.
\<close>
sublocale valid_initial_state \<subseteq> ni?:
   complete_unwinding_system "big_step_ADT_A_if utf" (* the ADT that we prove infoflow for *)
                             s0                      (* initial state *)
                             "\<lambda>e s. part s"          (* dom function *)
                             uwr                     (* uwr *)
                             "policyFlows (pasPolicy initial_aag)" (* policy *)
                             undefined               (* out -- unused *)
                             PSched                  (* scheduler partition name *)
  apply (simp add: complete_unwinding_system_def big_step_ADT_A_if_enabled_Step_system
                   unwinding_system_def complete_unwinding_system_axioms_def)
  apply (rule conjI)
   apply (unfold_locales)
      apply (clarsimp simp: equiv_def uwr_def, safe)[1]
        apply (simp add: sameFor_refl)
       apply (simp add: sameFor_sym)
      apply (simp add: sameFor_trans)
     apply (clarsimp simp: uwr_def sameFor_def sameFor_scheduler_def part_def
                          domain_fields_equiv_def partition_def)
    apply (rule PSched_flows_to_all)
   apply (case_tac x)
    apply (fastforce simp: no_partition_flows_to_PSched)
   apply simp
  apply (simp add: refl_onD[OF policyFlows_refl])
  done

lemma Fin_big_step_adt:
  "Fin (big_step_adt A R evmap) = Fin A"
  by (simp add: big_step_adt_def)


context valid_initial_state begin

lemma small_step_reachable:
  "ni.reachable s \<Longrightarrow> system.reachable (ADT_A_if utf) s0 s"
  apply (rule reachable_big_step_adt)
  apply (simp add: big_step_ADT_A_if_def)
  done

lemma reachable_invs_if:
  "ni.reachable s \<Longrightarrow> invs_if s"
  apply (rule ADT_A_if_reachable_invs_if)
  apply (erule small_step_reachable)
  done

abbreviation pas_refined_if where
  "pas_refined_if s \<equiv> pas_refined (current_aag (internal_state_if s)) (internal_state_if s)"

abbreviation guarded_pas_domain_if where
  "guarded_pas_domain_if s \<equiv>
     guarded_pas_domain (current_aag (internal_state_if s)) (internal_state_if s)"

lemma pas_refined_if:
  "ni.reachable  s \<Longrightarrow> pas_refined_if s"
  apply (drule reachable_invs_if)
  apply (simp add: invs_if_def Invs_def)
  done

lemma guarded_pas_domain_if:
  "ni.reachable  s \<Longrightarrow> guarded_pas_domain_if s"
  apply (drule reachable_invs_if)
  apply (simp add: invs_if_def Invs_def)
  done

lemma current_aag_eqI:
  "cur_domain s = cur_domain t \<Longrightarrow> current_aag s = current_aag t"
  by (simp add: current_aag_def)

lemma pas_refined_current_aag':
  "\<lbrakk> reachable t; current_aag (internal_state_if s) = current_aag (internal_state_if t) \<rbrakk>
     \<Longrightarrow> pas_refined (current_aag (internal_state_if s)) (internal_state_if t)"
  by (fastforce intro: pas_refined_if)

lemma guarded_pas_domain_current_aag':
  "\<lbrakk> reachable t; current_aag (internal_state_if s) = current_aag (internal_state_if t) \<rbrakk>
     \<Longrightarrow> guarded_pas_domain (current_aag (internal_state_if s)) (internal_state_if t)"
  by (fastforce intro: guarded_pas_domain_if)

abbreviation partition_if where
  "partition_if s \<equiv> partition (pasDomainAbs initial_aag) (internal_state_if s)"

lemma pasDomainAbs_not_SilcLabel[simp]:
  "SilcLabel \<notin> pasDomainAbs initial_aag x"
  apply (rule pas_wellformed_noninterference_silc)
  apply (rule policy_wellformed)
  done

lemma domain_in_ordinary_label[simp]:
  "OrdinaryLabel (label_of (the_elem (pasDomainAbs initial_aag (cur_domain s)))) =
   the_elem (pasDomainAbs initial_aag (cur_domain s))"
  apply (case_tac "the_elem (pasDomainAbs initial_aag (cur_domain s))")
   apply simp
  apply (metis the_label_of_domain_exists pasDomainAbs_not_SilcLabel)
  done

lemma uwr_partition_if:
  "\<lbrakk> (os,os') \<in> uwr (Partition (partition_if os));
     s = internal_state_if os; s' = internal_state_if os' \<rbrakk>
     \<Longrightarrow> states_equiv_for
           (\<lambda>x. pasObjectAbs initial_aag x \<in>
                  subjectReads (pasPolicy initial_aag)
                               (OrdinaryLabel (partition (pasDomainAbs initial_aag) s)))
           (\<lambda>x. pasIRQAbs initial_aag x \<in>
                  subjectReads (pasPolicy initial_aag)
                               (OrdinaryLabel (partition (pasDomainAbs initial_aag) s)))
           (\<lambda>x. pasASIDAbs initial_aag x \<in>
                  subjectReads (pasPolicy initial_aag)
                               (OrdinaryLabel (partition (pasDomainAbs initial_aag) s)))
           (\<lambda>x. pasDomainAbs initial_aag x \<inter>
                subjectReads (pasPolicy initial_aag)
                             (OrdinaryLabel (partition (pasDomainAbs initial_aag) s)) \<noteq> {}) s s' \<and>
         cur_thread s = cur_thread s' \<and> cur_domain s = cur_domain s' \<and>
         globals_equiv s s' \<and> scheduler_action s = scheduler_action s' \<and>
         work_units_completed s = work_units_completed s' \<and>
         irq_state (machine_state s) = irq_state (machine_state s') \<and>
         (user_modes (sys_mode_of os) \<longrightarrow> user_context_of os = user_context_of os') \<and>
         sys_mode_of os = sys_mode_of os' \<and>
         equiv_for (\<lambda>x. pasObjectAbs initial_aag x = SilcLabel) kheap s s'"
  apply (simp add: uwr_def sameFor_def sameFor_subject_def)
  apply (clarify | simp (no_asm_use) add: partition_def)+
  apply (subst (asm) the_subject_of_aag_domain, rule subject_current_aag)+
  apply (simp add: current_aag_def)
  apply (erule impE)
   using reads_lrefl subject_current_aag apply fastforce
  apply (fastforce simp: globals_equiv_def)
  done

lemma schact_is_rct_eqI:
  "(s,t) \<in> uwr(Partition (partition_if s))
   \<Longrightarrow> schact_is_rct (internal_state_if s) = schact_is_rct (internal_state_if t)"
  apply (drule uwr_partition_if[OF _ refl refl])
  apply (simp add: schact_is_rct_def)
  done

(*FIXME move*)
lemma handle_ev[wp]:
  assumes ok: "equiv_valid I AA AA P f"
  assumes err: "\<And>e. equiv_valid I AA AA (E e) (handler e)"
  assumes hoare: "\<lbrace>P\<rbrace> f -, \<lbrace>E\<rbrace>"
  shows "equiv_valid I AA AA P (f <handle> handler)"
  apply (simp add: handleE_def handleE'_def)
  apply (wp err ok | wpc | simp)+
   apply (insert hoare[simplified validE_E_def validE_def])[1]
   apply (simp split: sum.splits)
  by simp

lemma pas_refined_initial_aag_reachable:
  "system.reachable (big_step_ADT_A_if utf) s0 s
   \<Longrightarrow> pas_refined initial_aag (internal_state_if s)"
  apply (simp add: initial_aag_bak[where s="internal_state_if s"])
  apply (rule pas_refined_pasSubject_update[OF pas_refined_if pas_wellformed_cur])
   apply assumption
  apply (clarsimp simp: current_aag_def)
  apply blast
  done

lemma silc_inv_initial_aag_reachable:
  "system.reachable (big_step_ADT_A_if utf) s0 s
   \<Longrightarrow> silc_inv initial_aag s0_internal (internal_state_if s)"
  apply (simp add: silc_inv_cur[symmetric])
  apply (fastforce dest: reachable_invs_if simp: invs_if_def Invs_def)
  done

lemma uwr_def_cur:
  "uwr \<equiv> same_for (current_aag (internal_state_if s))"
  by (simp add: uwr_def current_aag_def)

lemma Step_big_step_ADT_A_if:
  "data_type.Step (big_step_ADT_A_if utf) = big_steps (ADT_A_if utf) big_step_R big_step_evmap"
  by (simp add: big_step_ADT_A_if_def big_step_adt_def)

lemma partitionIntegrity_refl:
  "partitionIntegrity aag s s"
  by (fastforce simp: partitionIntegrity_def silc_dom_equiv_def domain_fields_equiv_def
               intro: integrity_refl globals_equiv_scheduler_refl equiv_for_refl)

lemma partitionIntegrity_trans:
  "\<lbrakk> partitionIntegrity aag s t; partitionIntegrity aag t u \<rbrakk>
     \<Longrightarrow> partitionIntegrity aag s u"
  apply (clarsimp simp: partitionIntegrity_def)
  apply (rule conjI)
   apply (blast intro: integrity_trans)
  apply (fastforce intro: domain_fields_equiv_trans simp: silc_dom_equiv_def)
  done

lemma check_active_irq_A_if_partitionIntegrity:
  "((a, b), x, aa, ba) \<in> check_active_irq_A_if
   \<Longrightarrow> partitionIntegrity (current_aag b) b ba"
  apply (simp add: check_active_irq_A_if_def)
  apply (erule use_valid)
   apply (wp check_active_irq_if_partitionIntegrity)
  apply (rule partitionIntegrity_refl)
  done

lemma check_active_irq_A_if_result_state:
  "((a, b), x, aa, ba) \<in> check_active_irq_A_if
   \<Longrightarrow> ba = (b\<lparr>machine_state := (machine_state b)\<lparr>irq_state := irq_state_of_state b + 1\<rparr>\<rparr>)"
  apply (simp add: check_active_irq_A_if_def check_active_irq_if_def)
  apply (erule use_valid)
   apply (wp dmo_getActiveIRQ_wp)
  apply simp
  done

lemma ct_running_not_ct_idle:
  "\<lbrakk> valid_idle s; ct_running s \<rbrakk> \<Longrightarrow> \<not> ct_idle s"
  by (auto simp: ct_in_state_def valid_idle_def st_tcb_at_def obj_at_def)

lemma not_schedule_modes_KernelEntry:
  "(\<not> scheduler_modes (KernelEntry event)) = (event \<noteq> Interrupt)"
  by (case_tac event, simp_all)

lemma Step_ADT_A_if'':
  "\<lbrakk> (s, t) \<in> data_type.Step (ADT_A_if utf) (); system.reachable (ADT_A_if utf) s0 s \<rbrakk>
     \<Longrightarrow> (s, t) \<in> system.Step (ADT_A_if utf) ()"
  apply (simp add: system.reachable_def)
  apply (clarsimp)
  apply (frule execution_invs)
  apply (frule invs_if_full_invs_if)
  apply (frule execution_restrict)
  apply (simp add: system.Step_def execution_def steps_def ADT_A_if_def)
  done

end


locale Noninterference_valid_initial_state =
  Noninterference_1 current_aag + valid_initial_state _ _ _ _ _ current_aag for current_aag
begin

lemma kernel_call_A_if_partitionIntegrity:
  "\<lbrakk> ((a, b), x, aa, ba) \<in> kernel_call_A_if e; e \<noteq> Interrupt;
     ct_active b; Invs b; scheduler_action b = resume_cur_thread \<rbrakk>
     \<Longrightarrow> partitionIntegrity (current_aag b) b ba"
  apply (clarsimp simp: kernel_call_A_if_def)
  apply (erule use_valid)
   apply (wp kernel_entry_if_partitionIntegrity)
  apply (clarsimp simp: partitionIntegrity_refl Invs_def silc_inv_refl)
  apply (simp add: guarded_pas_domain_def current_aag_def active_from_running schact_is_rct_def)
  apply (erule impE)
   apply (rule ct_active_cur_thread_not_idle_thread, simp add: invs_valid_idle)
   apply simp
  apply (simp add: the_subject_of_aag_domain)
  done

lemma do_user_op_A_if_partitionIntegrity:
  "((a, b), x, aa, ba) \<in> do_user_op_A_if uop \<Longrightarrow> ct_running b \<Longrightarrow> Invs b
   \<Longrightarrow> partitionIntegrity (current_aag b) b ba"
  apply (simp add: do_user_op_A_if_def)
  apply (erule use_valid)
   apply (wp do_user_op_if_partitionIntegrity)
  apply (simp add: partitionIntegrity_refl)
  apply (simp add: Invs_def)
  apply (clarsimp simp: guarded_pas_domain_def current_aag_def)
  apply (erule impE)
   apply (erule ct_running_not_idle)
   apply (simp add: invs_valid_idle)
  apply (simp add: the_subject_of_aag_domain)
  done

lemma partitionIntegrity_current_aag_eq:
  "partitionIntegrity (current_aag s) s s' \<Longrightarrow> current_aag s' = current_aag s"
  by (simp add: current_aag_def partitionIntegrity_def domain_fields_equiv_def)

lemma partitionIntegrity_trans':
  "\<lbrakk> partitionIntegrity (current_aag s) s s';
     partitionIntegrity (current_aag s') s' t \<rbrakk>
     \<Longrightarrow> partitionIntegrity (current_aag s) s t"
  apply (rule partitionIntegrity_trans, assumption)
  apply (simp add: partitionIntegrity_current_aag_eq)
  done

lemma user_small_Step_partitionIntegrity:
  "\<lbrakk> ((a, b), x, aa, ba) \<in> check_active_irq_A_if;
     ct_running b; Invs b; ((aa, ba), y, ab, bb) \<in> do_user_op_A_if utf \<rbrakk>
     \<Longrightarrow> partitionIntegrity (current_aag b) b bb"
  apply (rule partitionIntegrity_trans'[rotated])
   apply (rule do_user_op_A_if_partitionIntegrity)
     apply assumption
    apply (drule check_active_irq_A_if_result_state)
    apply simp
   apply (drule check_active_irq_A_if_result_state)
   apply (simp add: Invs_def current_aag_def)
  apply (rule check_active_irq_A_if_partitionIntegrity)
  apply assumption
  done

lemma small_Step_partitionIntegrity:
  notes active_from_running[simp]
  assumes step: "(s, t) \<in> data_type.Step (ADT_A_if utf) ()"
    and reachable: "system.reachable (ADT_A_if utf) s0 s"
    and sched: "part s \<noteq> PSched"
  shows "partitionIntegrity (current_aag (internal_state_if s))
                            (internal_state_if s) (internal_state_if t)"
proof (cases "sys_mode_of s")
  case InUserMode
  with assms show ?thesis
    by (fastforce dest: ADT_A_if_reachable_invs_if
                  simp: invs_if_def part_def global_automaton_if_def
                        Step_ADT_A_if_def_global_automaton_if
                 intro: user_small_Step_partitionIntegrity check_active_irq_A_if_partitionIntegrity)
next case InIdleMode
  with assms show ?thesis
    by (fastforce simp: Step_ADT_A_if_def_global_automaton_if global_automaton_if_def
                 intro: check_active_irq_A_if_partitionIntegrity)
next case KernelEntry
  with assms show ?thesis
    by (fastforce dest: ADT_A_if_reachable_invs_if
                 simp: invs_if_def part_def Step_ADT_A_if_def_global_automaton_if
                       global_automaton_if_def not_schedule_modes_KernelEntry
                intro: kernel_call_A_if_partitionIntegrity)
next case KernelExit
  with assms show ?thesis
    apply (clarsimp simp: Step_ADT_A_if_def_global_automaton_if
                          global_automaton_if_def kernel_exit_A_if_def)
    apply (safe; simp)
    apply (erule use_valid)
     apply wp
    apply (rule partitionIntegrity_refl)
    done
next case KernelPreempted
  with assms show ?thesis
    by (simp add: part_def)
next case KernelSchedule
  with assms show ?thesis
    apply (clarsimp simp: part_def Step_ADT_A_if_def_global_automaton_if
                          global_automaton_if_def kernel_schedule_if_def)
    apply (safe; simp)
    apply (erule use_valid)
     apply (wp schedule_if_partitionIntegrity[OF current_domains_distinct])
    apply (clarsimp simp: partitionIntegrity_refl)
    apply (drule ADT_A_if_reachable_invs_if)
    apply (clarsimp simp: invs_if_def Invs_def silc_inv_refl current_aag_def)
    done
qed

end


context valid_initial_state begin

lemma sub_big_steps_reachable:
  "\<lbrakk> (s', evlist') \<in> sub_big_steps (ADT_A_if utf) big_step_R s;
     system.reachable (ADT_A_if utf) s0 s \<rbrakk>
     \<Longrightarrow> system.reachable (ADT_A_if utf) s0 s'"
  apply (rule_tac s=s and js=evlist' in Step_system.reachable_execution[OF ADT_A_if_Step_system])
   apply assumption
  apply (drule sub_big_steps_Run)
  apply (clarsimp simp: execution_def image_def)
  apply (subst Bex_def)
  apply (simp only: steps_eq_Run)
  apply (rule_tac x="s'" in exI)
  apply (rule conjI)
   apply (rule_tac x=s in exI)
   apply (clarsimp simp: system.reachable_def)
   apply (frule execution_invs)
   apply (frule invs_if_full_invs_if)
   apply (frule execution_restrict)
   apply (simp add: ADT_A_if_def)
  apply (simp add: ADT_A_if_def)
  done

lemma sub_big_steps_not_PSched:
  "\<lbrakk> (s', blah) \<in> sub_big_steps (ADT_A_if utf) big_step_R s; big_step_R\<^sup>*\<^sup>* s0 s; part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> part s' \<noteq> PSched"
  apply (drule tranclp_s0)
  apply (induct s' blah rule: sub_big_steps.induct)
   apply simp
  apply simp
  apply (simp add: part_def split: if_splits)
  apply (case_tac "sys_mode_of s", simp_all add: sys_mode_of_def)
  apply (case_tac "sys_mode_of s'", simp_all add: sys_mode_of_def)
      apply (case_tac "sys_mode_of t", simp_all add: sys_mode_of_def big_step_R_def split: if_splits)
       apply (rename_tac event)
       apply (case_tac event, simp_all)
      apply ((fastforce simp: ADT_A_if_def global_automaton_if_def)+)[2]
    apply (case_tac "sys_mode_of t", simp_all add: sys_mode_of_def big_step_R_def split: if_splits)
     apply (fastforce simp: ADT_A_if_def global_automaton_if_def)+
  apply (case_tac "sys_mode_of t", simp_all add: sys_mode_of_def)
   apply (clarsimp simp: ADT_A_if_def global_automaton_if_def kernel_exit_A_if_def split: if_splits)+
  done

lemma reachable_Step':
  "\<lbrakk> system.reachable (big_step_ADT_A_if utf) s0 s;
     (s, s') \<in> data_type.Step (big_step_ADT_A_if utf) a \<rbrakk>
     \<Longrightarrow> system.reachable (big_step_ADT_A_if utf) s0 s'"
  apply (rule reachable_Step, assumption)
  apply (drule small_step_reachable)
  apply (frule ADT_A_if_reachable_full_invs_if)
  apply (drule ADT_A_if_reachable_step_restrict)
  apply (clarsimp simp: system.Step_def execution_def big_step_ADT_A_if_def
                        Fin_big_step_adt Fin_ADT_if steps_eq_Run)
  apply (simp add: big_step_ADT_A_if_def big_step_adt_def Init_ADT_if)
  apply (cases s)
  apply (case_tac a)
  apply blast
  done

end


context Noninterference_valid_initial_state begin

lemma sub_big_steps_partitionIntegrity:
  "\<lbrakk> (t, as) \<in> sub_big_steps (ADT_A_if utf) big_step_R s;
     big_step_R\<^sup>*\<^sup>* s0 s; system.reachable (ADT_A_if utf) s0 s; part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> partitionIntegrity (current_aag (internal_state_if s))
                            (internal_state_if s) (internal_state_if t)"
  apply (induct t as rule: sub_big_steps.induct)
   apply (simp add: partitionIntegrity_def globals_equiv_scheduler_refl
                    silc_dom_equiv_def equiv_for_refl domain_fields_equiv_def)
  apply simp
  apply (erule partitionIntegrity_trans')
  apply (erule small_Step_partitionIntegrity)
   apply (blast intro: sub_big_steps_reachable)
  apply (rule sub_big_steps_not_PSched, simp+)
  done

lemma Step_partitionIntegrity':
  "\<lbrakk> (s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) ()\<rbrakk>
     \<Longrightarrow> system.reachable (big_step_ADT_A_if utf) s0 s \<and> part s \<noteq> PSched
         \<longrightarrow> partitionIntegrity (current_aag (internal_state_if s))
                                (internal_state_if s) (internal_state_if s')"
  apply (simp add: Step_big_step_ADT_A_if)
  apply (erule big_steps.induct)
  apply (simp add: big_step_evmap_def)
  apply (intro impI | elim conjE)+
  apply (rule partitionIntegrity_trans')
   apply (erule sub_big_steps_partitionIntegrity)
     apply (simp add: reachable_def execution_def)
     apply (clarsimp simp: big_step_ADT_A_if_def Fin_big_step_adt Fin_ADT_if steps_eq_Run)
     apply (rule Run_big_steps_tranclp)
     apply (simp add: big_step_ADT_A_if_def big_step_adt_def Init_ADT_if)
    apply (blast intro: small_step_reachable)
   apply assumption
  apply (erule small_Step_partitionIntegrity)
   apply (erule(1) sub_big_steps_reachable[OF _ small_step_reachable])
  apply (rule sub_big_steps_not_PSched, simp+)
   apply (simp add: reachable_def execution_def)
   apply (clarsimp simp: big_step_ADT_A_if_def Fin_big_step_adt Fin_ADT_if steps_eq_Run)
   apply (rule Run_big_steps_tranclp)
   apply (simp add: big_step_ADT_A_if_def big_step_adt_def Init_ADT_if)
  by simp

lemma Step_partitionIntegrity:
  "\<lbrakk> system.reachable (big_step_ADT_A_if utf) s0 s;
     (s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) (); part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> partitionIntegrity (current_aag (internal_state_if s))
                            (internal_state_if s) (internal_state_if s')"
  by (blast dest: Step_partitionIntegrity')

lemma Step_cur_domain_unchanged:
  "\<lbrakk> system.reachable (big_step_ADT_A_if utf) s0 s;
     (s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) (); part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> cur_domain (internal_state_if s') = cur_domain (internal_state_if s)"
  by (fastforce dest: Step_partitionIntegrity
                simp: partitionIntegrity_def domain_fields_equiv_def)

lemma Step_current_aag_unchanged:
  "\<lbrakk> system.reachable (big_step_ADT_A_if utf) s0 s;
     (s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) (); part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> current_aag (internal_state_if s') = current_aag (internal_state_if s)"
  apply (simp add: current_aag_def)
  apply (metis Step_cur_domain_unchanged)
  done

(* TOPLEVEL *)
lemma integrity_part:
  "\<lbrakk> system.reachable (big_step_ADT_A_if utf) s0 s;
     (s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) ();
     (part s, u) \<notin> policyFlows (pasPolicy initial_aag); u \<noteq> PSched; part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> (s,s') \<in> uwr u"
  supply [[simp_depth_limit=0]] \<comment> \<open>speedup\<close>
  apply (simp add: uwr_def_cur[where s=s])
  apply (case_tac s, case_tac s', simp)
  apply (case_tac a, case_tac aa, simp)
  apply (rule partsSubjectAffects_bounds_subjects_affects)
                 apply (rule current_domains_distinct)
                apply (fastforce dest: Step_partitionIntegrity)
               apply (fastforce dest: pas_refined_initial_aag_reachable simp: pas_refined_cur)
              apply (frule (2) pas_refined_current_aag'[OF _ Step_current_aag_unchanged[symmetric],
                                                        OF reachable_Step']; force)
             apply (fastforce dest!: reachable_invs_if simp: invs_if_def Invs_def)
            apply (fastforce dest!: reachable_invs_if[OF reachable_Step'] simp: invs_if_def Invs_def)
           apply (fastforce dest!: reachable_invs_if simp: invs_if_def Invs_def)
          apply (fastforce dest!: reachable_invs_if[OF reachable_Step'] simp: invs_if_def Invs_def)
         apply (fastforce dest: silc_inv_initial_aag_reachable simp: silc_inv_cur)
        apply (frule Step_current_aag_unchanged[symmetric];simp)
        apply (fastforce dest: silc_inv_initial_aag_reachable[OF reachable_Step'] simp: silc_inv_cur)
       apply (rule pas_wellformed_cur)
      apply (simp add: current_aag_def)
     apply (fastforce dest!: reachable_invs_if domains_distinct[THEN pas_domains_distinct_inj]
                       simp: invs_if_def Invs_def guarded_pas_domain_def
                             guarded_is_subject_cur_thread_def current_aag_def)
    apply (frule Step_current_aag_unchanged[symmetric];simp)
    apply (fastforce dest!: reachable_invs_if[OF reachable_Step']
                            domains_distinct[THEN pas_domains_distinct_inj]
                      simp: invs_if_def Invs_def guarded_pas_domain_def
                            guarded_is_subject_cur_thread_def current_aag_def)
   apply (rule partsSubjectAffects_bounds_those_subject_not_allowed_to_affect)
   apply (simp add: part_def partition_def current_aag_def split: if_split_asm)
  apply assumption
  done

end


context valid_initial_state begin

lemma not_PSched:
  "\<lbrakk> (x, u) \<notin> policyFlows (pasPolicy initial_aag); u \<noteq> PSched \<rbrakk>
     \<Longrightarrow> x \<noteq> PSched"
  apply (erule contrapos_nn)
  apply simp
  apply (rule schedFlowsToAll)
  done

lemma not_PSched_big_step_R:
  "\<lbrakk> part s \<noteq> PSched; big_step_R s t \<rbrakk>
     \<Longrightarrow> sys_mode_of s = KernelExit \<and> interrupted_modes (sys_mode_of t)"
  apply (clarsimp simp: part_def big_step_R_def sys_mode_of_def split: if_split_asm)
  apply (cases s, simp, case_tac b; simp)
  done

lemma sub_big_steps_Nil:
  "(s',[]) \<in> sub_big_steps A R s \<Longrightarrow> s' = s \<and> \<not> R s s"
  by (erule sub_big_steps.cases; simp)

lemma sub_big_steps_App:
  "(s',as @ [a]) \<in> sub_big_steps A R s
   \<Longrightarrow> \<exists>s'a. (s'a, as) \<in> sub_big_steps A R s \<and> (s'a, s') \<in> data_type.Step A a \<and> \<not> R s s'"
  by (erule sub_big_steps.cases; fastforce)

(* FIXME: move to ADT_IF.thy *)
lemma relation_preserved_across_sub_big_steps:
  "\<lbrakk> (s', as) \<in> sub_big_steps A R s; (t', as') \<in> sub_big_steps A R t; X s t; as' = as;
     \<forall>sa ta sa' ta'. X sa ta \<and>
       (\<exists>bs. (sa,bs) \<in> sub_big_steps A R s \<and> (sa',bs @ [()]) \<in> sub_big_steps A R s) \<and>
       (\<exists>cs. (ta,cs) \<in> sub_big_steps A R t \<and> (sa',cs @ [()]) \<in> sub_big_steps A R s) \<and>
       (sa,sa') \<in> data_type.Step A () \<and> (ta,ta') \<in> data_type.Step A ()
       \<longrightarrow> X sa' ta' \<rbrakk>
     \<Longrightarrow> X s' t'"
  apply hypsubst_thin
  apply (induct as arbitrary: s t s' t' rule: rev_induct)
   apply (drule sub_big_steps_Nil)+
   apply simp
  apply (frule_tac s=s in sub_big_steps_App)
  apply (frule_tac s=t in sub_big_steps_App)
  apply clarify
  apply (drule_tac x=s in meta_spec)
  apply (drule_tac x=t in meta_spec)
  apply (drule_tac x=s'a in meta_spec)
  apply (drule_tac x=s'aa in meta_spec)
  apply simp
  apply blast
  done

end


(* FIXME: move these next lemmas culminating in reads_respects_g
   for activate_thread and schedule into Schedule_IF or similar *)
lemma set_thread_state_runnable_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects_g aag (l :: 'a subject_label)
                          (valid_arch_state and K (runnable ts)) (set_thread_state t ts)"
  apply (rule gen_asm_ev)
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g[OF set_thread_state_runnable_reads_respects[OF domains_distinct]])
    apply assumption
   apply (rule doesnt_touch_globalsI)
   apply (wp set_thread_state_globals_equiv | simp)+
  done

lemma globals_equiv_idle_thread_ptr:
  "globals_equiv s t \<Longrightarrow> idle_thread s= idle_thread t"
  by (simp add: globals_equiv_def idle_equiv_def)

lemma get_thread_state_reads_respects_g:
  "reads_respects_g aag l (valid_idle and (\<lambda>s. is_subject aag t \<or> t = idle_thread s))
                    (get_thread_state t)"
  apply (rule use_spec_ev)
  apply (case_tac "t = idle_thread st")
   apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
   apply (drule_tac Q="\<lambda>rv s. s = st \<and> idle rv" in use_valid[OF _ gts_wp])
    apply (simp add: valid_idle_def)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (drule_tac Q="\<lambda>rv s. s = ta \<and> idle rv" in use_valid[OF _ gts_wp])
    apply (simp add: valid_idle_def)
    apply (fastforce simp: pred_tcb_at_def obj_at_def reads_equiv_g_def globals_equiv_idle_thread_ptr)
   apply (simp add: pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
  apply (frule aag_can_read_self)
  apply (frule get_thread_state_reads_respects_g[simplified equiv_valid_def2 equiv_valid_2_def,
                                                 rule_format, OF conjI, simplified]; fastforce)
  done

lemmas set_scheduler_action_reads_respects_g =
  reads_respects_g[OF set_scheduler_action_reads_respects,
                   OF doesnt_touch_globalsI[where P="\<top>"],
                   simplified,
                   OF set_scheduler_action_globals_equiv]

lemmas thread_get_reads_respects_g =
    reads_respects_g[OF thread_get_rev,
                     OF doesnt_touch_globalsI[where P="\<top>"],
                     simplified,
                     OF thread_get_inv]

lemmas tcb_sched_action_reads_respects_g =
    reads_respects_g[OF tcb_sched_action_reads_respects,
                     OF _ doesnt_touch_globalsI[where P="\<top>"],
                     simplified,
                     OF _ tcb_sched_action_extended.globals_equiv]

lemma set_tcb_queue_reads_respects_g':
  "equiv_valid (reads_equiv_g aag)
               (\<lambda>s s'. affects_equiv aag l s s' \<and>
                       arch_globals_equiv_strengthener  (machine_state s) (machine_state s'))
               (\<lambda>s s'. affects_equiv aag l s s' \<and>
                       arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
               \<top> (set_tcb_queue d prio queue)"
  unfolding equiv_valid_def2 equiv_valid_2_def
  supply if_cong[cong]
  apply (clarsimp simp: set_tcb_queue_def bind_def modify_def put_def get_def)
  by ((rule conjI
       | rule affects_equiv_ready_queues_update reads_equiv_ready_queues_update, assumption
       | clarsimp simp: reads_equiv_g_def
       | fastforce elim!: affects_equivE reads_equivE
                    simp: equiv_for_def globals_equiv_def idle_equiv_def)+)

lemma set_tcb_queue_globals_equiv[wp]:
  "set_tcb_queue d prio queue \<lbrace>globals_equiv st\<rbrace>"
  by (simp add: set_tcb_queue_def modify_def | wp)+


context Noninterference_1 begin

lemma activate_thread_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct pas"
  shows "reads_respects_g pas (l :: 'a subject_label)
           ((\<lambda>s. cur_thread s \<noteq> idle_thread s \<longrightarrow> is_subject pas (cur_thread s)) and invs)
           activate_thread"
  apply (simp add: activate_thread_def)
  apply (wp set_thread_state_runnable_reads_respects_g as_user_reads_respects_g
            get_thread_state_reads_respects_g gts_wp
         | wpc | simp add: det_setNextPC)+
  apply (clarsimp cong: conj_cong)
  apply (rule conjI)
   apply (blast intro: requiv_g_cur_thread_eq)
  apply (frule invs_valid_idle)
  apply simp
  apply (rule conjI)
   apply blast
  apply (rule impI)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_idle_def)
  apply (fastforce simp: det_getRestartPC)
  done

lemma cur_thread_update_reads_respects_g':
  "equiv_valid (reads_equiv_g aag)
               (\<lambda>s s'. affects_equiv aag l s s' \<and>
                       arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
               (affects_equiv aag l) \<top> (modify (cur_thread_update (\<lambda>_. t)))"
  apply (simp add: equiv_valid_def2)
  apply (rule modify_ev2)
  apply (clarsimp simp: reads_equiv_g_def reads_equiv_def2
                        affects_equiv_def2 globals_equiv_def idle_equiv_def)
  apply (fastforce intro: states_equiv_for_sym
                    dest: arch_globals_equiv_strengthener_thread_independent)
  done

lemma tcb_sched_action_reads_respects_g':
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "equiv_valid (reads_equiv_g aag)
               (\<lambda>s s'. affects_equiv aag (l :: 'a subject_label) s s' \<and>
                       arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
               (\<lambda>s s'. affects_equiv aag l s s' \<and>
                       arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
               (pas_refined aag) (tcb_sched_action action thread)"
  apply (simp add: tcb_sched_action_def get_tcb_queue_def)
  apply (subst gets_apply)
  apply (case_tac "aag_can_read aag thread \<or> aag_can_affect aag l thread")
   apply (simp add: ethread_get_def)
   apply (wp set_tcb_queue_reads_respects_g')
         apply (rule_tac Q="\<lambda>s. pasObjectAbs aag thread \<in> pasDomainAbs aag (tcb_domain rv)"
                      in equiv_valid_guard_imp)
          apply (wp gets_apply_ev')
          apply (clarsimp simp: reads_equiv_g_def)
          apply (elim reads_equivE affects_equivE equiv_forE)
          apply (clarsimp simp: disjoint_iff_not_equal)
          apply metis (* only one that works *)
         apply (wp | simp)+
   apply (intro conjI impI allI
          | fastforce simp: get_etcb_def reads_equiv_g_def
                      elim: reads_equivE affects_equivE equiv_forE)+
   apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def split: option.splits)
   apply (erule_tac x="(thread, tcb_domain y)" in ballE, force)
   apply (force intro: domtcbs simp: get_etcb_def)
  apply (simp add: equiv_valid_def2 ethread_get_def)
  apply (rule equiv_valid_rv_bind)
    apply (wp equiv_valid_rv_trivial', simp)
   apply (rule equiv_valid_2_bind)
      prefer 2
      apply (wp equiv_valid_rv_trivial, simp)
     apply (rule equiv_valid_2_bind)
        apply (rule_tac P="\<top>" and P'="\<top>" and L="{pasObjectAbs aag thread}" and
                                              L'="{pasObjectAbs aag thread}" in ev2_invisible')
                 apply (blast | simp add: labels_are_invisible_def)+
              apply (rule set_tcb_queue_modifies_at_most)
             apply (rule set_tcb_queue_modifies_at_most)
            apply (rule doesnt_touch_globalsI | simp | wp)+
       apply (clarsimp simp: equiv_valid_2_def gets_apply_def get_def bind_def return_def
                             labels_are_invisible_def)
       apply wp+
  apply clarsimp
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (erule_tac x="(thread, tcb_domain y)" in ballE)
   apply force
  apply (force intro: domtcbs simp: get_etcb_def)
  done

lemma switch_to_thread_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_g aag (l :: 'a subject_label)
                          (pas_refined aag and (\<lambda>s. is_subject aag t)) (switch_to_thread t)"
  apply (simp add: switch_to_thread_def)
  apply (subst bind_assoc[symmetric])
  apply (rule equiv_valid_guard_imp)
   apply (rule bind_ev)
     apply (wp bind_ev_general cur_thread_update_reads_respects_g'
               tcb_sched_action_reads_respects_g' arch_switch_to_thread_reads_respects_g')
    apply (simp add: equiv_valid_def2)
    apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
       apply (rule assert_ev2 | simp)+
      apply (rule equiv_valid_rv_trivial, wp+)
  apply fastforce
  done

lemma guarded_switch_to_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_g aag (l :: 'a subject_label)
                          (pas_refined aag and valid_idle and (\<lambda>s. is_subject aag t))
                          (guarded_switch_to t)"
  apply (simp add: guarded_switch_to_def)
  apply (wp switch_to_thread_reads_respects_g get_thread_state_reads_respects_g gts_wp)
  apply fastforce
  done

lemma cur_thread_update_idle_reads_respects_g':
  "reads_respects_g aag (l :: 'a subject_label) (\<lambda>s. t = idle_thread s) (modify (cur_thread_update (\<lambda>_. t)))"
  apply (simp add: equiv_valid_def2)
  apply (rule modify_ev2)
  apply (clarsimp simp: reads_equiv_g_def reads_equiv_def2
                        affects_equiv_def2 globals_equiv_def idle_equiv_def)
  apply (fastforce intro: states_equiv_for_sym arch_globals_equiv_threads_eq)
  done

lemma switch_to_idle_thread_reads_respects_g[wp]:
  "reads_respects_g aag (l :: 'a subject_label) \<top> (switch_to_idle_thread)"
  apply (simp add: switch_to_idle_thread_def)
  apply (wp cur_thread_update_idle_reads_respects_g')
  apply (fastforce simp: reads_equiv_g_def globals_equiv_idle_thread_ptr)
  done

lemma choose_thread_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_g aag (l :: 'a subject_label)
           ((\<lambda>s. cur_thread s \<noteq> idle_thread s \<longrightarrow> is_subject aag (cur_thread s)) and
                 einvs and valid_queues and pas_cur_domain aag and pas_refined aag)
           choose_thread"
  apply (simp add: choose_thread_def)
  apply (wp guarded_switch_to_reads_respects_g)
  apply (rule conjI)
   apply (fastforce simp: reads_equiv_g_def reads_equiv_def)
  apply (rule conjI)
   apply (clarsimp simp: reads_equiv_g_def reads_equiv_def2
                         states_equiv_for_def equiv_for_def disjoint_iff_not_equal)
   apply (metis reads_lrefl)
  apply (simp add: invs_valid_idle)
  (* everything from here clagged from Syscall_AC.choose_thread_respects *)
  apply (clarsimp simp: pas_refined_def)
  apply (clarsimp simp: tcb_domain_map_wellformed_aux_def)
  apply (erule_tac x="(hd (max_non_empty_queue (ready_queues s (cur_domain s))), cur_domain s)"
                in ballE)
   apply (fastforce dest: domains_distinct[THEN pas_domains_distinct_inj])
  apply (clarsimp simp: valid_queues_def is_etcb_at_def)
  apply (erule_tac x="cur_domain s" in allE)
  apply (erule_tac x="Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}" in allE)
  apply clarsimp
  apply (erule_tac x="hd (max_non_empty_queue (ready_queues s (cur_domain s)))" in ballE)
   apply (clarsimp)
   apply (erule notE, rule domtcbs)
    apply force
   apply (simp add: etcb_at_def)
  apply (simp add: max_non_empty_queue_def)
  apply (erule_tac P="hd A \<in> B" for A B in notE)
  apply (rule Max_prop)
   apply force+
  done

end


lemma scheduler_action_switch_thread_is_subject:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "\<lbrakk> valid_sched s; pas_cur_domain aag s; pas_refined aag s \<rbrakk>
           \<Longrightarrow> \<forall>x. scheduler_action s = switch_thread x \<longrightarrow> is_subject aag x"
  apply (clarsimp simp: valid_sched_def valid_sched_action_2_def
                        switch_in_cur_domain_2_def in_cur_domain_def)
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (drule_tac x="(x,cur_domain s)" in bspec)
   apply (clarsimp simp: etcb_at_def)
   apply (clarsimp simp: weak_valid_sched_action_2_def)
   apply (clarsimp simp: valid_etcbs_def)
   apply (drule_tac x=x in spec)
   apply (simp add: st_tcb_weakenE)
   apply (simp add: is_etcb_at_def split: option.splits)
   apply (fastforce elim: domains_of_state_aux.intros)
  apply (fastforce dest: domains_distinct[THEN pas_domains_distinct_inj])
  done

lemma gets_app_rewrite:
  "(gets y >>= (\<lambda>x. g (f x))) = (gets (\<lambda>s. f (y s)) >>= g)"
  apply (rule ext)
  apply (simp add: gets_def bind_def get_def return_def)
  done

lemma gets_domain_time_zero_ev:
  "equiv_valid_inv I A (\<lambda>s. domain_time s > 0) (gets (\<lambda>s. domain_time s = 0))"
  apply (rule gets_ev'')
  apply fastforce
  done

lemma reads_equiv_valid_g_inv_schedule_switch_thread_fastfail:
  "reads_equiv_valid_g_inv (affects_equiv aag l) aag
     ((\<lambda>s. ct \<noteq> it \<longrightarrow> is_subject aag (ct)))
     (schedule_switch_thread_fastfail ct it ct_prio target_prio)"
  unfolding schedule_switch_thread_fastfail_def
  by (wpsimp wp: reads_respects_g_from_inv[OF reads_respects_ethread_get])

lemma reads_respects_gets_ready_queues:
  "reads_respects aag l (\<lambda>s. pasSubject aag \<in> pasDomainAbs aag d)
     (gets (\<lambda>s. f (ready_queues s d)))"
  apply (wp gets_ev'')
  apply (force elim: reads_equivE simp: equiv_for_def)
  done

lemma reads_respects_is_highest_prio:
  "reads_respects aag l (\<lambda>s. pasSubject aag \<in> pasDomainAbs aag d)
                  (gets (\<lambda>s. is_highest_prio d p s))"
  by (fastforce simp: is_highest_prio_def intro: reads_respects_gets_ready_queues)

lemma reads_respects_ethread_get_when:
  "reads_respects aag l (\<lambda>_. b \<longrightarrow> is_subject aag thread) (ethread_get_when b f thread)"
  apply (simp add: ethread_get_when_def)
  apply (rule conjI; clarsimp)
   apply (rule reads_respects_ethread_get)
  apply wp
  done

text \<open>strengthening of @{thm ArchSyscall_AC.valid_sched_action_switch_subject_thread}\<close>
lemma valid_sched_action_switch_is_subject:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "\<lbrakk> scheduler_action s = switch_thread t ; valid_sched_action s ;
           valid_etcbs s ; pas_refined aag s ; pas_cur_domain aag s \<rbrakk>
           \<Longrightarrow> is_subject aag t"
  by (fastforce dest: valid_sched_action_switch_subject_thread
                      domains_distinct[THEN pas_domains_distinct_inj])


context Noninterference_1 begin

lemma schedule_choose_new_thread_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_g aag (l :: 'a subject_label)
           ((\<lambda>s. domain_time s \<noteq> 0) and einvs and pas_cur_domain aag and pas_refined aag and
            (\<lambda>s. (cur_thread s \<noteq> idle_thread s \<longrightarrow> is_subject aag (cur_thread s))))
           schedule_choose_new_thread"
  apply (simp add: schedule_choose_new_thread_def )
  apply (subst gets_app_rewrite[where y=domain_time and f="\<lambda>x. x = 0"])+
  apply (wp gets_domain_time_zero_ev set_scheduler_action_reads_respects_g
            choose_thread_reads_respects_g ev_pre_cont[where f=next_domain]
            hoare_pre_cont[where a=next_domain] when_ev)
  apply (clarsimp simp: valid_sched_def word_neq_0_conv)
  sorry (* FIXME: Broken by experimental-tpspec -robs.
  done
*)

lemma schedule_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_g aag (l :: 'a subject_label)
           ((\<lambda>s. cur_thread s \<noteq> idle_thread s \<longrightarrow> is_subject aag (cur_thread s)) and einvs and
            pas_cur_domain aag and (\<lambda>s. domain_time s \<noteq> 0) and pas_refined aag)
           schedule"
  supply ethread_get_wp[wp del]
  supply set_scheduler_action_wp[wp del]
  supply conj_cong[cong del] (* knowing the scheduler action messes with valid_sched_2 *)
  apply (simp add: schedule_def)
  apply wp
         apply wpc
           (* resume current thread *)
           apply wp[1]
          prefer 2
          (* choose new thread *)
          apply ((wp set_scheduler_action_reads_respects_g tcb_sched_action_reads_respects_g
                     schedule_choose_new_thread_reads_respects_g when_ev
                  | wpc | simp)+)[1]
         (* now switch_thread case *)
         apply (wpsimp wp: schedule_choose_new_thread_reads_respects_g enqueue_thread_queued
                           set_scheduler_action_reads_respects_g tcb_sched_action_reads_respects_g
                           set_scheduler_action_cnt_valid_sched)+
                        (* tcb_sched_action tcb_sched_append *)
                        apply (wp append_thread_queued set_scheduler_action_reads_respects_g
                                  guarded_switch_to_reads_respects_g
                                  reads_respects_g_from_inv[OF reads_respects_is_highest_prio]
                                  reads_equiv_valid_g_inv_schedule_switch_thread_fastfail)+
                 (* fastfail calculation *)
                 apply (wpsimp wp: reads_respects_g_from_inv[OF reads_respects_ethread_get]
                                   reads_respects_g_from_inv[OF reads_respects_ethread_get_when]
                                   when_ev gts_wp tcb_sched_action_reads_respects_g
                                   tcb_sched_action_enqueue_valid_blocked_except
                                   get_thread_state_reads_respects_g
                        | wp (once) hoare_drop_imp)+
  apply (clarsimp simp: invs_valid_idle)
  apply (intro allI conjI impI; (elim conjE)?;
         ((fastforce simp: valid_sched_def valid_sched_action_switch_is_subject[OF domains_distinct]
                    dest!: reads_equiv_gD intro!: globals_equiv_idle_thread_ptr))?)
               apply (tactic \<open>distinct_subgoals_tac\<close>)
         apply (all \<open>(erule requiv_g_cur_thread_eq)?\<close>)
         apply (simp_all add: requiv_sched_act_eq[OF reads_equiv_gD[THEN conjunct1]])
         apply (all \<open>(solves \<open>clarsimp elim!: st_tcb_weakenE\<close>)?\<close>)
       apply (all \<open>(solves \<open>clarsimp simp: not_cur_thread_def\<close>)?\<close>)
   apply (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def)+
  done

lemma schedule_if_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct pas"
  shows "reads_respects_g pas (l :: 'a subject_label)
           (einvs and pas_cur_domain pas and guarded_pas_domain pas
                  and (\<lambda>s. domain_time s > 0) and pas_refined pas) (schedule_if tc)"
  apply (simp add: schedule_if_def)
  apply (wp schedule_reads_respects_g activate_thread_reads_respects_g)
   apply (rule_tac Q="\<lambda>rv s. guarded_pas_domain pas s \<and> invs s \<and> pas_cur_domain pas s"
                in hoare_strengthen_post)
    apply (wp schedule_guarded_pas_domain schedule_cur_domain
           | simp add: guarded_pas_domain_def
           | fastforce dest: domains_distinct[THEN pas_domains_distinct_inj])+
  done

lemma globals_equiv_globals_equiv_scheduler[elim]:
  "globals_equiv s t \<Longrightarrow> globals_equiv_scheduler s t"
  by (auto simp: globals_equiv_def globals_equiv_scheduler_def)

end


lemma sameFor_current_partition_sys_mode_of_eq:
  "\<lbrakk> (s, t) \<in> sameFor_subject (pasPolicy initial_aag) (pasObjectAbs initial_aag)
                              (pasIRQAbs initial_aag) (pasASIDAbs initial_aag)
                              (pasDomainAbs initial_aag) a;
     label_of (the_elem (pasDomainAbs initial_aag (cur_domain (internal_state_if t)))) = a;
     OrdinaryLabel a \<in> pasDomainAbs initial_aag (cur_domain (internal_state_if s)) \<rbrakk>
     \<Longrightarrow> sys_mode_of s = sys_mode_of t"
  apply (simp add: sameFor_subject_def2)
  apply clarify
  apply (erule impE)
   apply fastforce
  apply simp
  done

lemma flow_then_affect:
  "(Partition x, Partition l) \<in> policyFlows (pasPolicy initial_aag)
   \<Longrightarrow> Partition l \<in> partsSubjectAffects (pasPolicy initial_aag) x"
  by (erule policyFlows.cases, simp_all add: partsSubjectAffects_def)


context valid_initial_state begin

lemma do_user_op_if_reads_respects_g:
  "reads_respects_g aag l (pas_refined aag and valid_vspace_objs_if and einvs and
                           is_subject aag \<circ> cur_thread and det_inv InUserMode tc and ct_running)
                    (do_user_op_if utf tc)"
  apply (rule equiv_valid_guard_imp)
   apply (rule do_user_op_reads_respects_g[where P="\<lambda>tc. einvs and
               det_inv InUserMode tc and ct_running"])
   using utf_det apply fastforce
  apply simp
  apply (rule ct_running_not_idle)
   apply simp
  apply (simp add: invs_valid_idle)
  done

lemma uwr_part_sys_mode_of_eq:
  "\<lbrakk> (s,t) \<in> uwr (part s); part t = part s; part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> sys_mode_of s = sys_mode_of t"
  apply (simp add: part_def split: if_split_asm)
  apply (simp add: partition_def)
  apply (cut_tac pas_wellformed_noninterference_silc
                   [OF policy_wellformed, where d="cur_domain (internal_state_if s)"])
  apply (case_tac "the_elem (pasDomainAbs initial_aag (cur_domain (internal_state_if s)))")
   apply (simp add: uwr_def sameFor_def)
   apply (erule (1) sameFor_current_partition_sys_mode_of_eq)
   apply (metis the_subject_of_aag_domain subject_current_aag)
  apply (metis the_label_of_domain_exists)
  done

lemma uwr_reads_equiv_f_g_affects_equiv:
  "\<lbrakk> (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr (Partition l); invs_if s; invs_if t;
     (part s, Partition l) \<in> policyFlows (pasPolicy initial_aag); part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> reads_equiv_f_g (current_aag (internal_state_if s))
                         (internal_state_if s) (internal_state_if t) \<and>
         affects_equiv (current_aag (internal_state_if s)) (OrdinaryLabel l)
                       (internal_state_if s) (internal_state_if t)"
  apply (rule sameFor_reads_f_g_affects_equiv)
      apply (simp add: current_aag_def)
     apply (simp add: invs_if_def Invs_def)
     apply blast
    apply (clarsimp simp: uwr_def part_def current_aag_def partition_def split: if_splits)
   apply (simp add: part_def split: if_splits add: partition_def current_aag_def flow_then_affect)
  apply (clarsimp simp: uwr_def part_def current_aag_def partition_def split: if_splits)
  done

end


lemma check_active_irq_if_reads_respects_g:
  "reads_respects_g aag (l :: 'a subject_label)
     (invs and only_timer_irq_inv irq st) (check_active_irq_if tc)"
  apply (simp add: check_active_irq_if_def)
  apply (wp dmo_getActiveIRQ_reads_respects_g| blast)+
  done

lemma check_active_irq_if_reads_respects_f_g:
  "reads_respects_f_g aag (l :: 'a subject_label)
     (silc_inv aag st and invs and only_timer_irq_inv irq st') (check_active_irq_if tc)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_f_g'[where Q="\<top>", OF check_active_irq_if_reads_respects_g])
   apply (wp check_active_irq_if_wp)
   apply fastforce+
  done

lemma partitionIntegrity_cur_domain:
  "partitionIntegrity aag s s' \<Longrightarrow> cur_domain s = cur_domain s'"
  by (clarsimp simp: partitionIntegrity_def domain_fields_equiv_def)

lemma use_ev:
  "\<lbrakk> equiv_valid I A B P f; (rv,s') \<in> fst (f s); (rv',t') \<in> fst (f t); P s; P t; I s t; A s t \<rbrakk>
    \<Longrightarrow> rv' = rv \<and> I s' t' \<and> B s' t'"
  by (fastforce simp: equiv_valid_def2 equiv_valid_2_def)


context valid_initial_state begin

lemma uwr_part_sys_mode_of_user_context_of_eq:
  "\<lbrakk> (s,t) \<in> uwr (part s); part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> sys_mode_of s = sys_mode_of t \<and>
         (user_modes (sys_mode_of s) \<longrightarrow> user_context_of s = user_context_of t)"
  by (clarsimp simp: part_def uwr_partition_if split: if_splits)

lemma uwr_PSched_cur_domain:
  "(s,t) \<in> uwr PSched \<Longrightarrow> cur_domain (internal_state_if s) = cur_domain (internal_state_if t)"
  by (fastforce simp: uwr_def sameFor_def sameFor_scheduler_def domain_fields_equiv_def)

lemma uwr_PSched_cur_domain':
  "(((sx, s), sm), ((tx, t), tm)) \<in> uwr PSched \<Longrightarrow> cur_domain s = cur_domain t"
  by (fastforce dest: uwr_PSched_cur_domain)

lemma part_not_PSched_sys_mode_of_not_KernelSchedule_True:
  "part s \<noteq> PSched \<Longrightarrow> sys_mode_of s \<noteq> KernelSchedule True"
  apply (erule contrapos_nn)
  apply (simp add: part_def)
  done

end


context Noninterference_valid_initial_state begin

lemma reads_equiv_f_g_affects_equiv_uwr:
  "\<lbrakk> reads_equiv_f_g (current_aag (internal_state_if s))
                     (internal_state_if s') (internal_state_if t');
     affects_equiv (current_aag (internal_state_if s)) (OrdinaryLabel a)
                   (internal_state_if s') (internal_state_if t');
     (part s, Partition a) \<in> policyFlows (pasPolicy initial_aag); part s \<noteq> PSched;
     silc_inv (current_aag (internal_state_if s')) s0_internal (internal_state_if s');
     (s,t) \<in> uwr PSched;
     partitionIntegrity (current_aag (internal_state_if s))
                        (internal_state_if s) (internal_state_if s');
     partitionIntegrity (current_aag (internal_state_if t))
                        (internal_state_if t) (internal_state_if t');
     sys_mode_of s' = sys_mode_of t'; user_context_of s' = user_context_of t' \<rbrakk>
     \<Longrightarrow> (s', t') \<in> uwr (Partition a) \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  apply (frule_tac s="internal_state_if s" in partitionIntegrity_cur_domain)
  apply (subgoal_tac "current_aag (internal_state_if s) = current_aag (internal_state_if s')")
   apply (case_tac s', case_tac t')
   apply (case_tac aa, case_tac aaa)
   apply (rule conjI)
    apply simp
    apply (drule (1) reads_g_affects_equiv_sameFor[OF conjI])
       apply (simp add: current_aag_def)
      apply (fastforce)
     apply (simp add: current_aag_def)
     apply (rule flow_then_affect)
     apply (simp add: part_def partition_def split: if_splits)
    apply (clarsimp simp: uwr_def current_aag_def)
    apply assumption
   apply (rule conjI)
    apply (clarsimp simp: uwr_def sameFor_def sameFor_scheduler_def)
    apply (clarsimp simp: reads_equiv_f_g_def reads_equiv_def silc_dom_equiv_def current_aag_def
                          globals_equiv_idle_thread_ptr globals_equiv_globals_equiv_scheduler)
    apply (fastforce simp: domain_fields_equiv_def partitionIntegrity_def)
   apply (drule sameFor_reads_equiv_f_g)
     apply (fastforce simp: invs_if_def Invs_def)
    apply (fastforce simp: current_aag_def)
   apply (simp add: uwr_def part_def partition_def current_aag_def split: if_splits)
  apply (simp add: current_aag_def)
  done

lemma check_active_irq_A_if_confidentiality_helper:
  notes reads_respects_irq = use_ev[OF check_active_irq_if_reads_respects_f_g[where st=s0_internal
                                                                                and st'=s0_internal
                                                                                and irq=timer_irq]]
  shows
    "\<lbrakk> (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u; invs_if s; invs_if t;
       silc_inv (current_aag (internal_state_if s')) s0_internal (internal_state_if s');
       (part s, u) \<in> policyFlows (pasPolicy initial_aag);
       part s \<noteq> PSched; u \<noteq> PSched; user_modes (sys_mode_of s);
       ((fst s),x,(fst s')) \<in> check_active_irq_A_if; ((fst t),y,(fst t')) \<in> check_active_irq_A_if \<rbrakk>
       \<Longrightarrow> x = y \<and> (snd s' = f x \<and> snd t' = f y
                    \<longrightarrow> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s))"
  apply (frule (1) uwr_part_sys_mode_of_user_context_of_eq)
  apply (clarsimp simp: check_active_irq_A_if_def)
  apply (case_tac s, case_tac t, simp_all)
  apply (case_tac u, simp_all)
  apply (frule (6) uwr_reads_equiv_f_g_affects_equiv)
  apply (match premises in "s = ((_, p), _)" and "t = ((_, q), _)"
                    and H: "(_, _) \<in> fst (check_active_irq_if _ p)"
                    for p q \<Rightarrow> \<open>rule revcut_rl[OF reads_respects_irq[where s=p and t=q, OF H]]\<close>)
       apply assumption
      apply (simp add: invs_if_def Invs_def)
      apply (elim conjE)
      apply assumption
     apply (simp add: invs_if_def Invs_def)
     apply (simp only: current_aag_eqI[OF uwr_PSched_cur_domain'])
    apply simp
   apply fastforce
  apply simp
  apply (rule impI)
  apply (rule reads_equiv_f_g_affects_equiv_uwr)
           apply simp+
     apply (erule use_valid[OF _ check_active_irq_if_partitionIntegrity])
     apply (rule partitionIntegrity_refl)
    apply simp
    apply (erule use_valid[OF _ check_active_irq_if_partitionIntegrity])
    apply (rule partitionIntegrity_refl)
   apply (simp add: sys_mode_of_def)
  apply (simp add: user_context_of_def)
  done

lemma check_active_irq_A_if_confidentiality:
  "\<lbrakk> (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u; invs_if s; invs_if t;
     (part s, u) \<in> policyFlows (pasPolicy initial_aag);
     part s \<noteq> PSched; u \<noteq> PSched; user_modes (sys_mode_of s);
     ((fst s),x,(fst s')) \<in> check_active_irq_A_if; ((fst t),y,(fst t')) \<in> check_active_irq_A_if \<rbrakk>
     \<Longrightarrow> x = y \<and> (snd s' = f x \<and> snd t' = f y
                  \<longrightarrow> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s))"
  apply (subgoal_tac "silc_inv (current_aag (internal_state_if s')) s0_internal (internal_state_if s')")
   apply (blast dest!: check_active_irq_A_if_confidentiality_helper)
  apply (case_tac s', simp)
  apply (case_tac a, simp)
  apply (clarsimp simp: check_active_irq_A_if_def)
  apply (erule use_valid)
   apply (wp check_active_irq_if_wp)
  apply (fastforce simp: invs_if_def Invs_def current_aag_def)
  done

lemma check_active_irq_A_if_confidentiality':
  "\<lbrakk> (XX, YY) \<in> uwr PSched; XX = s; YY = t; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
     invs_if s; invs_if t; (part s, u) \<in> policyFlows (pasPolicy initial_aag);
     part s \<noteq> PSched; u \<noteq> PSched; user_modes (sys_mode_of s);
     ((fst s),x,(fst s')) \<in> check_active_irq_A_if; ((fst t),y,(fst t')) \<in> check_active_irq_A_if;
     snd s' = (case x of None \<Rightarrow> InUserMode | Some xx \<Rightarrow> KernelEntry Interrupt);
     snd t' = (case y of None \<Rightarrow> InUserMode | Some yy \<Rightarrow> KernelEntry Interrupt) \<rbrakk>
     \<Longrightarrow> x = y \<and> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  by (blast dest: check_active_irq_A_if_confidentiality)

lemma check_active_irq_A_if_confidentiality'':
  "\<lbrakk> (XX, YY) \<in> uwr PSched; XX = s; YY = t; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
    invs_if s; invs_if t; (part s, u) \<in> policyFlows (pasPolicy initial_aag);
    part s \<noteq> PSched; u \<noteq> PSched; user_modes (sys_mode_of s);
    ((fst s),x,(fst s')) \<in> check_active_irq_A_if; ((fst t),y,(fst t')) \<in> check_active_irq_A_if;
    snd s' = (case x of None \<Rightarrow> InIdleMode | Some xx \<Rightarrow> KernelEntry Interrupt);
    snd t' = (case y of None \<Rightarrow> InIdleMode | Some yy \<Rightarrow> KernelEntry Interrupt) \<rbrakk>
    \<Longrightarrow> x = y \<and> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  by (blast dest: check_active_irq_A_if_confidentiality)

lemma check_active_irq_A_if_retval_eq:
  "\<lbrakk> (XX, YY) \<in> uwr PSched; XX = s; YY = t; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
     invs_if s; invs_if t; (part s, u) \<in> policyFlows (pasPolicy initial_aag);
     part s \<noteq> PSched; u \<noteq> PSched; user_modes (sys_mode_of s);
     ((fst s),x,s') \<in> check_active_irq_A_if; ((fst t),y,t') \<in> check_active_irq_A_if \<rbrakk>
     \<Longrightarrow> x = y"
  apply simp
  apply (drule_tac s'="(s',undefined)" and t'="(t',undefined)" and u=u
                in check_active_irq_A_if_confidentiality, simp+)
  apply (elim conjE, assumption)
  done

lemmas do_user_op_if_reads_respects_f_g =
  reads_respects_f_g'[where Q="\<top>", simplified,
                      OF do_user_op_if_reads_respects_g,
                      OF do_user_op_silc_inv]

lemma partitionIntegrity_irq_state_update[simp]:
  "partitionIntegrity aag y (y\<lparr>machine_state := (machine_state y)\<lparr>irq_state := X\<rparr>\<rparr>)"
  apply (cut_tac s=y and aag=aag in partitionIntegrity_refl)
  apply (clarsimp simp: partitionIntegrity_def integrity_subjects_def domain_fields_equiv_def
                        globals_equiv_scheduler_def silc_dom_equiv_def equiv_for_def)
  done

lemma invs_if_Invs:
  "invs_if s
   \<Longrightarrow> Invs (internal_state_if s) \<and>
       det_inv (sys_mode_of s) (cur_thread_context_of s) (internal_state_if s)"
  by (simp add: invs_if_def)

lemma do_user_op_A_if_confidentiality:
  notes read_respects_irq =
    use_ev[OF check_active_irq_if_reads_respects_f_g[where st=s0_internal
                                                       and st'=s0_internal
                                                       and irq=timer_irq
                                                       and aag="current_aag (internal_state_if s)"]]
  and read_respects_user_op =
    use_ev[OF do_user_op_if_reads_respects_f_g[where aag="current_aag (internal_state_if s)"
                                                 and st="s0_internal"]]
  shows
    "\<lbrakk> (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u; invs_if s; invs_if t;
       invs_if s'; invs_if t'; (part s, u) \<in> policyFlows (pasPolicy initial_aag);
       part s \<noteq> PSched; u \<noteq> PSched; sys_mode_of s = InUserMode; sys_mode_of t = InUserMode;
       (fst s, None, s_aux) \<in> check_active_irq_A_if; (fst t, None, t_aux) \<in> check_active_irq_A_if;
       (s_aux, xx, fst s') \<in> do_user_op_A_if utf; (t_aux, yy, fst t') \<in> do_user_op_A_if utf;
       snd s' = f xx; snd t' = f yy \<rbrakk>
       \<Longrightarrow> xx = yy \<and> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  including no_pre
  supply [[simp_depth_limit=2]] \<comment> \<open>speedup\<close>
  apply (frule (1) uwr_part_sys_mode_of_user_context_of_eq)
  apply (clarsimp simp: check_active_irq_A_if_def)
  apply (case_tac s, case_tac t, simp_all)
  apply (case_tac u, simp_all)
  apply (frule (6) uwr_reads_equiv_f_g_affects_equiv)
  apply (match premises in "s = ((_,p),_)" and "t = ((_,q),_)"
                    and H: "(_,_) \<in> fst (check_active_irq_if _ p)"
                    for p q \<Rightarrow> \<open>rule revcut_rl[OF read_respects_irq[where t=q, OF H]]\<close>)
       apply assumption
      apply (clarsimp dest!: invs_if_Invs simp: Invs_def)
     apply (drule uwr_PSched_cur_domain)
     apply (clarsimp dest!: invs_if_Invs simp: Invs_def)
     subgoal by (clarsimp simp: current_aag_def)
    apply simp
   apply fastforce
  apply (simp add: do_user_op_A_if_def | elim exE conjE)+
  apply (match premises in "s_aux = (_,p)" and "t_aux = (_,q)"
                    and H: "(_,_) \<in> fst (do_user_op_if _ _ p)"
                    for p q \<Rightarrow> \<open>rule revcut_rl[OF read_respects_user_op[where t=q, OF H]]\<close>)
       apply assumption
      apply (match premises in "s = ((_,p),_)" and H: "(_,_) \<in> fst (check_active_irq_if _ p)"
                   for p \<Rightarrow> \<open>rule revcut_rl[OF use_valid[OF H check_active_irq_if_User_det_inv]]\<close>)
       apply (simp (no_asm_use) add: invs_if_def Invs_def cur_thread_context_of_def)
       apply metis
      apply simp
      apply (erule use_valid)
       apply (wp check_active_irq_if_wp)
      apply (clarsimp simp: invs_if_def Invs_def)
      apply (blast intro!: guarded_pas_is_subject_current_aag[rule_format] active_from_running)
     apply (match premises in "t_aux = (_,q)" and H: "(_,q) \<in> fst (check_active_irq_if _ _)"
                  for q \<Rightarrow> \<open>rule revcut_rl[OF use_valid[OF H check_active_irq_if_User_det_inv]]\<close>)
      apply (simp (no_asm_use) add: invs_if_def Invs_def cur_thread_context_of_def)
      apply metis
     apply simp
     apply (erule_tac s'=yc in use_valid)
      apply (wp check_active_irq_if_wp)
     apply (clarsimp simp: invs_if_def Invs_def current_aag_eqI[OF uwr_PSched_cur_domain'])
     apply (match premises in "t = ((_,q),_)" and H: "invs q" for q \<Rightarrow>
              \<open>rule revcut_rl[OF ct_running_not_idle[OF _ invs_valid_idle[OF H]]]\<close>)
      apply assumption
     apply (match premises in "t = ((_,q),_)" for q \<Rightarrow>
              \<open>rule revcut_rl[OF current_aag_def[where t=q]]\<close>)
     apply (blast intro!: guarded_pas_is_subject_current_aag[rule_format] active_from_running)
    apply simp
   apply simp
  apply simp
  apply (rule reads_equiv_f_g_affects_equiv_uwr)
           apply ((clarsimp simp: Invs_def dest!: invs_if_Invs; rule TrueI)+)
      apply (simp add: invs_if_def Invs_def)
     apply (simp add: invs_if_def Invs_def)
     apply (erule use_valid[OF _ do_user_op_if_partitionIntegrity])
     apply (erule use_valid[OF _ check_active_irq_if_wp])
     apply clarsimp
     apply (frule (1) ct_running_not_idle[OF _ invs_valid_idle])
     apply (blast intro!: guarded_pas_is_subject_current_aag[rule_format] active_from_running)
    apply simp
    apply (erule_tac s'=s'aa in use_valid[OF _ do_user_op_if_partitionIntegrity])
    apply (erule_tac s'=yc in use_valid[OF _ check_active_irq_if_wp])
    apply (clarsimp simp: invs_if_def Invs_def)
    apply (match premises in "t = ((_,q),_)" and H: "invs q" for q \<Rightarrow>
             \<open>rule revcut_rl[OF ct_running_not_idle[OF _ invs_valid_idle[OF H]]]\<close>)
     apply assumption
    apply (blast intro!: guarded_pas_is_subject_current_aag[rule_format] active_from_running)
   apply (simp add: sys_mode_of_def)
  apply (simp add: user_context_of_def)
  done

lemma do_user_op_A_if_confidentiality':
  "\<lbrakk> (XX, YY) \<in> uwr PSched; XX = s; YY = t; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u; invs_if s;
     invs_if t; invs_if s'; invs_if t'; (part s, u) \<in> policyFlows (pasPolicy initial_aag);
     part s \<noteq> PSched; u \<noteq> PSched; sys_mode_of s = InUserMode; sys_mode_of t = InUserMode;
     ((fst s),None,s_aux) \<in> check_active_irq_A_if; ((fst t),None,t_aux) \<in> check_active_irq_A_if;
     (s_aux,xx,fst s') \<in> do_user_op_A_if utf; (t_aux,yy,fst t') \<in> do_user_op_A_if utf;
     snd s' = (case xx of None \<Rightarrow> InUserMode | Some xxx \<Rightarrow> KernelEntry xxx);
     snd t' = (case yy of None \<Rightarrow> InUserMode | Some yyy \<Rightarrow> KernelEntry yyy) \<rbrakk>
     \<Longrightarrow> xx = yy \<and> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  by (rule do_user_op_A_if_confidentiality, simp+)

end


context Noninterference_valid_initial_state begin

lemmas schedule_if_reads_respects_f_g =
         reads_respects_f_g'[where Q="\<top>", simplified, OF schedule_if_reads_respects_g,
                             OF _ schedule_if_silc_inv]

lemma kernel_schedule_if_confidentiality:
  "\<lbrakk> (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u; invs_if s; invs_if t;
     invs_if s'; invs_if t'; (part s, u) \<in> policyFlows (pasPolicy initial_aag);
     part s \<noteq> PSched; u \<noteq> PSched; user_modes (sys_mode_of s);
     ((fst s),(),(fst s')) \<in> kernel_schedule_if;
     ((fst t),(),(fst t')) \<in> kernel_schedule_if; snd s' = snd t' \<rbrakk>
     \<Longrightarrow> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  supply [[simp_depth_limit=1]] \<comment> \<open>speedup\<close>
  apply (frule (1) uwr_part_sys_mode_of_user_context_of_eq)
  apply (frule part_not_PSched_sys_mode_of_not_KernelSchedule_True)
  apply (clarsimp simp: kernel_schedule_if_def)
  apply (case_tac s, case_tac t, simp_all)
  apply (case_tac u, simp_all)
  apply (frule (6) uwr_reads_equiv_f_g_affects_equiv)
  apply (simp split: prod.splits)
  apply (case_tac s', case_tac t')
  apply (simp add: split_paired_all)
  apply (frule_tac s=x2 and t=bb and s2=x2
                in use_ev[OF schedule_if_reads_respects_f_g
                               [where st=s0_internal, OF current_domains_distinct]])
       apply assumption
      apply (clarsimp simp: invs_if_def Invs_def current_aag_def)
     apply (clarsimp simp: invs_if_def Invs_def)
     apply (drule uwr_PSched_cur_domain)
     apply (clarsimp simp: current_aag_def)
    apply simp
   apply fastforce
  apply simp
  apply (rule reads_equiv_f_g_affects_equiv_uwr)
           apply simp+
       apply (fastforce simp: invs_if_def Invs_def)
      apply simp
     apply simp
     apply (erule use_valid[OF _ schedule_if_partitionIntegrity[OF current_domains_distinct]])
     apply (clarsimp simp: partitionIntegrity_refl invs_if_def Invs_def current_aag_def silc_inv_refl)
    apply simp
    apply (erule use_valid[OF _ schedule_if_partitionIntegrity[OF current_domains_distinct]])
    apply (clarsimp simp: partitionIntegrity_refl invs_if_def Invs_def current_aag_def silc_inv_refl)
   apply (simp add: sys_mode_of_def)
  apply (simp add: user_context_of_def)
  done

lemma kernel_schedule_if_confidentiality':
  "\<lbrakk> (XX, YY) \<in> uwr PSched; XX = s; YY = t; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u; invs_if s;
     invs_if t; invs_if s'; invs_if t'; (part s, u) \<in> policyFlows (pasPolicy initial_aag);
     part s \<noteq> PSched; u \<noteq> PSched; user_modes (sys_mode_of s);
     ((fst s),(),(fst s')) \<in> kernel_schedule_if;
     ((fst t),(),(fst t')) \<in> kernel_schedule_if; snd s' = snd t' \<rbrakk>
     \<Longrightarrow> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  by (blast dest: kernel_schedule_if_confidentiality)

end


lemma thread_set_tcb_context_update_runnable_globals_equiv:
  "\<lbrace>globals_equiv st and st_tcb_at runnable t and invs\<rbrace>
   thread_set (tcb_arch_update (arch_tcb_context_set uc)) t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule hoare_pre)
  apply (rule thread_set_context_globals_equiv)
  apply clarsimp
  apply (frule invs_valid_idle)
  apply (fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma thread_set_tcb_context_update_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_g aag (l :: 'a subject_label) (st_tcb_at runnable t and invs)
                          (thread_set (tcb_arch_update (arch_tcb_context_set uc)) t)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g)
    apply (rule thread_set_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp thread_set_tcb_context_update_runnable_globals_equiv)
   apply simp+
  done

lemma thread_set_tcb_context_update_silc_inv:
  "thread_set (tcb_arch_update (arch_tcb_context_set f)) t \<lbrace>silc_inv aag st\<rbrace>"
  apply (rule thread_set_silc_inv)
  apply (simp add: tcb_cap_cases_def)
  done

lemmas thread_set_tcb_context_update_reads_respects_f_g =
  reads_respects_f_g'[where Q="\<top>", simplified,
                      OF thread_set_tcb_context_update_reads_respects_g,
                      OF _ thread_set_tcb_context_update_silc_inv]

lemma kernel_entry_if_reads_respects_f_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_f_g aag l (ct_active and silc_inv aag st and einvs
                                             and only_timer_irq_inv irq st'
                                             and schact_is_rct and pas_refined aag
                                             and pas_cur_domain aag and guarded_pas_domain aag
                                             and K (ev \<noteq> Interrupt \<and> \<not> pasMaySendIrqs aag))
                            (kernel_entry_if ev tc)"
  apply (simp add: kernel_entry_if_def)
  apply (wp handle_event_reads_respects_f_g thread_set_tcb_context_update_reads_respects_f_g
            thread_set_tcb_context_update_silc_inv only_timer_irq_inv_pres[where P="\<top>" and Q="\<top>"]
            thread_set_invs_trivial thread_set_not_state_valid_sched thread_set_pas_refined
         | simp add: tcb_cap_cases_def arch_tcb_update_aux2)+
  apply (elim conjE)
  apply (frule (1) ct_active_cur_thread_not_idle_thread[OF invs_valid_idle])
  apply (clarsimp simp: ct_in_state_def runnable_eq_active)
  apply (rule conjI)
   apply (fastforce dest: requiv_g_cur_thread_eq simp: reads_equiv_f_g_def)
  apply (clarsimp simp: guarded_pas_domain_def)
  apply (fastforce simp: only_timer_irq_inv_def invs_valid_idle
                   dest: domains_distinct[THEN pas_domains_distinct_inj])
  done

lemma reads_respects_f_g_2':
  "\<lbrakk> equiv_valid_2 (reads_equiv_g aag) (affects_equiv aag l) (affects_equiv aag l) (=) P P' f f';
     \<lbrace>silc_inv aag st and Q\<rbrace> f \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>;
     \<lbrace>silc_inv aag st and Q'\<rbrace> f' \<lbrace>\<lambda>_. silc_inv aag st\<rbrace> \<rbrakk>
     \<Longrightarrow> equiv_valid_2 (reads_equiv_f_g aag) (affects_equiv aag l) (affects_equiv aag l) (=)
                       (silc_inv aag st and P and Q) (silc_inv aag st and P' and Q') f f'"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def reads_equiv_f_g_def reads_equiv_g_def)
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply (subst conj_commute, rule conjI, fastforce)
  apply (rule silc_dom_equiv_trans)
   apply (rule silc_dom_equiv_sym)
   apply (rule silc_inv_silc_dom_equiv)
   apply (erule (1) use_valid, fastforce)
  apply (rule silc_inv_silc_dom_equiv)
  apply (erule (1) use_valid, fastforce)
  done


context Noninterference_valid_initial_state begin

lemma kernel_call_A_if_confidentiality:
  notes active_from_running[simp]
  shows "\<lbrakk> (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u; invs_if s; invs_if t;
           invs_if s'; invs_if t'; (part s, u) \<in> policyFlows (pasPolicy initial_aag);
           part s \<noteq> PSched; u \<noteq> PSched; ((fst s),x,(fst s')) \<in> kernel_call_A_if e;
           ((fst t),y,(fst t')) \<in> kernel_call_A_if e; e \<noteq> Interrupt;
           sys_mode_of s = KernelEntry e; sys_mode_of t = KernelEntry e; snd s' = f x; snd t' = f y \<rbrakk>
           \<Longrightarrow> x = y \<and> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  supply [[simp_depth_limit=3]] \<comment> \<open>speedup\<close>
  apply (frule (1) uwr_part_sys_mode_of_user_context_of_eq)
  apply (frule part_not_PSched_sys_mode_of_not_KernelSchedule_True)
  apply (clarsimp simp: kernel_call_A_if_def)
  apply (case_tac s, case_tac t, simp_all)
  apply (case_tac u, simp_all)
  apply (frule (6) uwr_reads_equiv_f_g_affects_equiv)
  apply (frule_tac s=b and t=ba and s2=b
                in use_ev[OF kernel_entry_if_reads_respects_f_g
                               [where st=s0_internal, OF current_domains_distinct]])
       apply assumption
      apply (clarsimp simp: invs_if_def Invs_def schact_is_rct_def current_aag_def)
      apply assumption
     apply (clarsimp simp: invs_if_def Invs_def schact_is_rct_def
                           current_aag_eqI[OF uwr_PSched_cur_domain'])
     apply (simp add: current_aag_def)
    apply simp
   apply fastforce
  apply simp
  apply (rule reads_equiv_f_g_affects_equiv_uwr)
           apply simp+
       apply (fastforce simp: invs_if_def Invs_def)
      apply simp
     apply simp
     apply (erule use_valid[OF _ kernel_entry_if_partitionIntegrity])
     apply (clarsimp simp: partitionIntegrity_refl invs_if_def Invs_def current_aag_def
                           silc_inv_refl schact_is_rct_def guarded_pas_domain_def
                           ct_active_cur_thread_not_idle_thread[OF invs_valid_idle])
     (* XXX: the conjI is needed here -- metis won't instantiate a schematic var *)
     apply (rule conjI)
      apply (metis the_subject_of_aag_domain)
     apply assumption
    apply simp
    apply (erule use_valid[OF _ kernel_entry_if_partitionIntegrity])
    apply (clarsimp simp: partitionIntegrity_refl invs_if_def Invs_def current_aag_def
                          silc_inv_refl schact_is_rct_def guarded_pas_domain_def
                          ct_active_cur_thread_not_idle_thread[OF invs_valid_idle])
    (* XXX: and here *)
    apply (rule conjI)
     apply (metis the_subject_of_aag_domain)
    apply assumption
   apply (simp add: sys_mode_of_def)
  apply (simp add: user_context_of_def)
  done

lemma kernel_call_A_if_confidentiality':
  "\<lbrakk> (XX, YY) \<in> uwr PSched; XX = s; YY = t; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
     invs_if s; invs_if t; invs_if s'; invs_if t';
     (part s, u) \<in> policyFlows (pasPolicy initial_aag); part s \<noteq> PSched; u \<noteq> PSched;
     ((fst s),x,(fst s')) \<in> kernel_call_A_if e; ((fst t),y,(fst t')) \<in> kernel_call_A_if e;
     e \<noteq> Interrupt; sys_mode_of s = KernelEntry e; sys_mode_of t = KernelEntry e;
     snd s' = (case x of True \<Rightarrow> KernelPreempted | _ \<Rightarrow> KernelSchedule False);
     snd t' = (case y of True \<Rightarrow> KernelPreempted | _ \<Rightarrow> KernelSchedule False) \<rbrakk>
     \<Longrightarrow> x = y \<and> (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  by (blast dest: kernel_call_A_if_confidentiality)

lemma thread_get_tcb_context_reads_respects_g_helper:
  "equiv_valid_rv_inv (reads_equiv_g aag) (affects_equiv aag l)
     (\<lambda>rv rv'. arch_tcb_context_get (tcb_arch rv) = arch_tcb_context_get (tcb_arch rv'))
     (\<lambda>s. t = idle_thread s \<or> is_subject aag t)
     (gets (get_tcb False t) >>= assert_opt)"
  apply (clarsimp simp: equiv_valid_2_def in_monad reads_equiv_g_def)
  apply (erule disjE)
   apply (frule globals_equiv_idle_thread_ptr)
   apply (simp add: get_tcb_def split: kernel_object.splits option.splits)
   apply (fastforce simp: globals_equiv_def idle_equiv_def)
  apply (fastforce dest: requiv_get_tcb_eq)
  done

lemma thread_get_tcb_context_reads_respects_g:
  "reads_respects_g aag l
     (\<lambda>s. t = idle_thread s \<or> is_subject aag t) (thread_get (arch_tcb_context_get o tcb_arch) t)"
  apply (simp add: thread_get_def gets_the_def equiv_valid_def2)
  apply (rule_tac W="\<lambda> rv rv'. arch_tcb_context_get (tcb_arch rv) = arch_tcb_context_get (tcb_arch rv')"
              and Q="\<top>\<top>" in equiv_valid_rv_bind)
    apply (rule thread_get_tcb_context_reads_respects_g_helper)
   apply (rule return_ev2, simp)
  apply (rule hoare_post_taut)
  done

(* this is a little more complicated because the context isn't
   guaranteed to be equal when called, so we need an equiv_valid_2
*)
lemma kernel_exit_if_reads_respects_g_2:
  "equiv_valid_2 (reads_equiv_g aag) (affects_equiv aag l) (affects_equiv aag l) (=)
                 (\<lambda>s. cur_thread s = idle_thread s \<or> is_subject aag (cur_thread s))
                 (\<lambda>s. cur_thread s = idle_thread s \<or> is_subject aag (cur_thread s))
                 (kernel_exit_if tc) (kernel_exit_if tc')"
  apply (simp add: kernel_exit_if_def)
  apply (fold equiv_valid_def2)
  apply (wp thread_get_tcb_context_reads_respects_g)
  apply (fastforce dest: requiv_g_cur_thread_eq)
  done

lemma kernel_exit_if_reads_respects_f_g_2:
  "equiv_valid_2 (reads_equiv_f_g aag) (affects_equiv aag l) (affects_equiv aag l) (=)
     (silc_inv aag st and (\<lambda>s. cur_thread s = idle_thread s \<or> is_subject aag (cur_thread s)))
     (silc_inv aag st and (\<lambda>s. cur_thread s = idle_thread s \<or> is_subject aag (cur_thread s)))
     (kernel_exit_if tc) (kernel_exit_if tc')"
  apply (rule equiv_valid_2_guard_imp)
    apply (rule reads_respects_f_g_2'[where Q="\<top>" and Q'="\<top>", OF kernel_exit_if_reads_respects_g_2])
     apply (wp | simp | blast)+
  done

end


lemma use_ev2:
  "\<lbrakk> equiv_valid_2 I A B R P P' f f'; (rv,s') \<in> fst (f s);
     (rv',t') \<in> fst (f' t); P s; P' t; I s t; A s t \<rbrakk>
     \<Longrightarrow> R rv rv' \<and> I s' t' \<and> B s' t'"
  by (fastforce simp: equiv_valid_2_def)

lemma reads_equiv_f_g_reads_equiv_g:
  "reads_equiv_f_g aag s t \<Longrightarrow> reads_equiv_g aag s t"
  by (fastforce simp: reads_equiv_f_g_def reads_equiv_g_def)


context valid_initial_state begin

lemma reads_equiv_g_ct_running_eq:
  "\<lbrakk> reads_equiv_g (current_aag bb) bd be; Invs bd; Invs be; current_aag bb = current_aag bd \<rbrakk>
     \<Longrightarrow> ct_running bd = ct_running be"
  apply (clarsimp simp: reads_equiv_f_g_def)
  apply (clarsimp simp: reads_equiv_g_def)
  apply (frule globals_equiv_idle_thread_ptr)
  apply (frule requiv_cur_thread_eq)
  apply (case_tac "cur_thread bd = idle_thread bd")
   apply (simp add: Invs_def)
   apply (elim conjE)
   apply (drule invs_valid_idle)+
   apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def valid_idle_def)
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  apply (fastforce simp: Invs_def guarded_pas_domain_def simp: current_aag_def
                   dest: is_subject_kheap_eq domains_distinct[THEN pas_domains_distinct_inj])
  done

lemma partitionIntegrity_part_unchanged:
  "\<lbrakk>partitionIntegrity aag (internal_state_if s) (internal_state_if s'); part s \<noteq> PSched;
    part s' \<noteq> PSched\<rbrakk> \<Longrightarrow> part s' = part s"
  apply (simp add: part_def split: if_splits
             add: partition_def partitionIntegrity_def domain_fields_equiv_def)
  done

lemma big_step_R_rtranclp:
  "system.reachable (big_step_ADT_A_if utf) s0 s
       \<Longrightarrow> big_step_R\<^sup>*\<^sup>* s0 s"
  apply (simp add: reachable_def execution_def)
  apply (clarsimp simp: big_step_ADT_A_if_def Fin_big_step_adt Fin_ADT_if steps_eq_Run)
  apply (rule Run_big_steps_tranclp)
  apply (simp add: big_step_ADT_A_if_def big_step_adt_def Init_ADT_if)
  done

lemma sub_big_steps_strict_prefix:
  "(s', as @ bs) \<in> sub_big_steps A R s \<Longrightarrow>
   \<exists>t. (t, as) \<in> sub_big_steps A R s"
  apply (induct bs arbitrary: s s' rule: rev_induct)
   apply fastforce
  apply (subst (asm) append_assoc[symmetric])
  apply (drule sub_big_steps_App)
  apply blast
  done

lemma uwr_part_sys_mode_of_eq':
  "\<lbrakk>(s,t) \<in> uwr (part x); part s = part x; part t = part x; part x \<noteq> PSched\<rbrakk>
    \<Longrightarrow> sys_mode_of s = sys_mode_of t"
  apply (fastforce intro: uwr_part_sys_mode_of_eq)
  done

end


lemma app_Cons:
  "xs @ (a # b) = (xs @ [a]) @ b"
  by simp

lemma sys_mode_of_eq_big_step_R_contradiction:
  "\<lbrakk> sys_mode_of s = sys_mode_of t; sys_mode_of s' = sys_mode_of t';
     big_step_R s s'; \<not> big_step_R t t' \<rbrakk>
     \<Longrightarrow> False"
  apply (simp add: big_step_R_def)
  apply (case_tac s, case_tac t, simp_all)
  apply (case_tac s', case_tac t', simp_all)
  apply auto
  done

lemma unit_list_as_replicate:
  "(as::unit list) = replicate (length as) ()"
  apply (induct as, auto)
  done

lemma unit_lists_unequal:
  "(as::unit list) \<noteq> (as'::unit list) \<Longrightarrow> as < as' \<or> as' < as"
  apply (simp add: less_list_def' strict_prefix_def)
  apply (case_tac "length as \<ge> length as'")
  apply (rule disjI2)
   apply (subst unit_list_as_replicate[where as=as])
   apply (subst unit_list_as_replicate[where as=as'])
   apply (clarsimp simp: prefix_def)
   apply (rule_tac x="replicate (length as - length as') ()" in exI)
   apply (subst replicate_add[symmetric])
   apply simp
  apply (rule disjI1)
  apply (subst unit_list_as_replicate[where as=as])
  apply (subst unit_list_as_replicate[where as=as'])
  apply (clarsimp simp: prefix_def)
  apply (rule_tac x="replicate (length as' - length as) ()" in exI)
  apply (subst replicate_add[symmetric])
  apply simp
  done


context Noninterference_valid_initial_state begin

lemma kernel_exit_A_if_confidentiality:
  "\<lbrakk>(s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
    invs_if s;     invs_if t;   invs_if s'; invs_if t';
    (part s, u) \<in> policyFlows (pasPolicy initial_aag);
    part s \<noteq> PSched; u \<noteq> PSched;
    ((fst s),x,(fst s')) \<in> kernel_exit_A_if;
    ((fst t),y,(fst t')) \<in> kernel_exit_A_if;
    sys_mode_of s = KernelExit; sys_mode_of t = KernelExit;
    snd s' = f x; snd t' = f y\<rbrakk> \<Longrightarrow>
   x = y \<and>
   (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  supply [[simp_depth_limit=2]] \<comment> \<open>speedup\<close>
  apply (clarsimp simp: kernel_exit_A_if_def)
  apply (case_tac s, case_tac t, simp_all)
  apply (case_tac u, simp_all)
  apply (frule (6) uwr_reads_equiv_f_g_affects_equiv)
  apply (simp split: prod.splits)
  apply (case_tac "fst s'", simp)
  apply (case_tac "fst t'", simp)
  apply (frule_tac s=x2 and t=x2a and aag1="current_aag x2"
                in use_ev2[OF kernel_exit_if_reads_respects_f_g_2[where st=s0_internal]])
       apply assumption
      apply (clarsimp simp: invs_if_def Invs_def current_aag_def guarded_pas_domain_def)
      apply (metis the_subject_of_aag_domain)
     apply (clarsimp simp: invs_if_def Invs_def)
     apply (drule uwr_PSched_cur_domain)
     apply (clarsimp simp: current_aag_def guarded_pas_domain_def)
     apply (metis the_subject_of_aag_domain)
    apply simp
   apply fastforce
  apply simp
  apply (elim conjE)
  apply (drule state_unchanged[OF kernel_exit_if_inv])+
  apply (subgoal_tac "ct_running bb = ct_running bc")
   apply simp
   apply (rule reads_equiv_f_g_affects_equiv_uwr)
            apply simp+
        apply (fastforce simp: invs_if_def Invs_def)
       apply simp
      apply simp
      apply (rule partitionIntegrity_refl)
     apply simp
     apply (rule partitionIntegrity_refl)
    apply (simp add: sys_mode_of_def)
   apply (simp add: user_context_of_def)
  apply (frule_tac bd=bb in reads_equiv_g_ct_running_eq[OF reads_equiv_f_g_reads_equiv_g])
     apply (fastforce simp: invs_if_def)
    apply (fastforce simp: invs_if_def)
   apply (fastforce simp: reads_equiv_f_g_def reads_equiv_def current_aag_def)
  apply simp
  done

lemma kernel_exit_A_if_confidentiality':
  "\<lbrakk>(XX, YY) \<in> uwr PSched; XX = s; YY = t; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
    invs_if s;     invs_if t;   invs_if s'; invs_if t';
    (part s, u) \<in> policyFlows (pasPolicy initial_aag);
    part s \<noteq> PSched; u \<noteq> PSched;
    ((fst s),x,(fst s')) \<in> kernel_exit_A_if;
    ((fst t),y,(fst t')) \<in> kernel_exit_A_if;
    sys_mode_of s = KernelExit; sys_mode_of t = KernelExit;
    snd s' = f x; snd t' = f y\<rbrakk> \<Longrightarrow>
   x = y \<and>
   (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  apply (blast dest: kernel_exit_A_if_confidentiality)
  done

lemma small_Step_confidentiality_part_not_PSched:
  shows
  "\<lbrakk>(s, s') \<in> Simulation.Step (ADT_A_if utf) ();
    (t, t') \<in> Simulation.Step (ADT_A_if utf) ();
    (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
    system.reachable (ADT_A_if utf) s0 s;
    system.reachable (ADT_A_if utf) s0 t;
    (part s, u) \<in> policyFlows (pasPolicy initial_aag);
    part s \<noteq> PSched; u \<noteq> PSched\<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s)"
  apply (frule schedIncludesCurrentDom)
  apply (frule uwr_part_sys_mode_of_eq, simp+)
  apply (frule_tac s=s in ADT_A_if_reachable_invs_if)
  apply (frule_tac s=t in ADT_A_if_reachable_invs_if)
  apply (frule(2) Step_system.reachable_Step[where s=s, OF ADT_A_if_Step_system _ Step_ADT_A_if''])
  apply (frule(2) Step_system.reachable_Step[where s=t, OF ADT_A_if_Step_system _ Step_ADT_A_if''])
  apply (frule_tac s=s' in ADT_A_if_reachable_invs_if)
  apply (frule_tac s=t' in ADT_A_if_reachable_invs_if)
  apply (case_tac "sys_mode_of s")
       (* InUserMode *)
       apply ((simp add: Step_ADT_A_if_def_global_automaton_if global_automaton_if_def
                 split: if_splits
              | intro impI allI
              | elim exE conjE disjE
              | simp_all add: not_schedule_modes_KernelEntry)+)[1]
               apply (drule do_user_op_A_if_confidentiality'[
                                     where s=s and t=t and s'=s' and t'=t' and u=u],simp+)
              apply (drule do_user_op_A_if_confidentiality'[
                                  where s=s and t=t and s'=s' and t'=t' and u=u], simp+)
             apply (drule_tac s=s and t=t and u=u and s'="(aa,ba)"
                          in check_active_irq_A_if_retval_eq, simp+)
            apply (drule do_user_op_A_if_confidentiality'[
                                where s=s and t=t and s'=s' and t'=t' and u=u], simp+)
           apply (drule_tac s=s and t=t and u=u and s'="(ad,bd)"
                        in check_active_irq_A_if_retval_eq, simp+)
          apply (drule do_user_op_A_if_confidentiality'[
                                where s=s and t=t and s'=s' and t'=t' and u=u], simp+)
         apply (drule_tac s=s and t=t and u=u and s'="(aa,ba)"
                      in check_active_irq_A_if_retval_eq, simp+)
        apply (drule_tac s=s and t=t and u=u and s'="(ad,bd)"
                    in check_active_irq_A_if_retval_eq, simp+)
       apply (drule check_active_irq_A_if_confidentiality'[
                            where s=s and t=t and s'=s' and t'=t' and u=u], simp+)
      (* InIdleMode *)
      apply ((simp add: Step_ADT_A_if_def_global_automaton_if global_automaton_if_def
                  split: if_splits
             | intro impI allI
             | elim exE conjE disjE
             | simp_all add: not_schedule_modes_KernelEntry)+)[1]
         apply (drule check_active_irq_A_if_confidentiality'[
                                      where s=s and t=t and s'=s' and t'=t' and u=u], simp+)
        apply (drule_tac s=s and t=t and u=u and s'="(aa,ba)" in check_active_irq_A_if_retval_eq,
              simp+)
       apply (drule_tac s=s and t=t and u=u and s'="(aa,ba)" in check_active_irq_A_if_retval_eq,
             simp+)
      apply (drule check_active_irq_A_if_confidentiality''[
                          where s=s and t=t and s'=s' and t'=t' and u=u],simp+)
     (* KernelEntry event -- where event \<noteq> Interrupt *)
     apply (rename_tac event)
     apply (subgoal_tac "event \<noteq> Interrupt")
      prefer 2
      apply (case_tac t, simp)
      apply (case_tac event, (fastforce simp: part_def split: if_splits)+)[1]
     apply ((simp add: Step_ADT_A_if_def_global_automaton_if global_automaton_if_def
                 split: if_splits
            | intro impI allI
            | elim exE conjE disjE
            | simp_all add: not_schedule_modes_KernelEntry)+)[1]
        apply (drule kernel_call_A_if_confidentiality'[where s=s and t=t and s'=s' and t'=t' and u=u],
              simp+)
       apply (drule kernel_call_A_if_confidentiality'[where s=s and t=t and s'=s' and t'=t' and u=u],
             simp+)
      apply (drule kernel_call_A_if_confidentiality'[where s=s and t=t and s'=s' and t'=t' and u=u],
            simp+)
     apply (drule kernel_call_A_if_confidentiality'[where s=s and t=t and s'=s' and t'=t' and u=u],
           simp+)
    (* KernelPreempted *)
    apply (simp add: part_def)
    (* KernelSchedule bool -- where \<not> bool *)
   apply ((simp add: Step_ADT_A_if_def_global_automaton_if global_automaton_if_def
               split: if_splits
         | intro impI allI
         | elim exE conjE disjE
         | simp_all add: not_schedule_modes_KernelEntry)+)[1]
   apply (drule kernel_schedule_if_confidentiality'[where s=s and t=t and s'=s' and t'=t' and u=u],
         simp+)
  (* KernelExit *)
  apply ((simp add: Step_ADT_A_if_def_global_automaton_if global_automaton_if_def
              split: if_splits
        | intro impI allI
        | elim exE conjE disjE
        | simp_all add: not_schedule_modes_KernelEntry)+)[1]
  apply (drule kernel_exit_A_if_confidentiality'[where s=s and t=t and s'=s' and t'=t' and u=u],
        simp+)
  done

lemma sub_big_steps_not_PSched_confidentiality_part:
  "\<lbrakk>(s', as) \<in> sub_big_steps (ADT_A_if utf) big_step_R s;
    (t', as) \<in> sub_big_steps (ADT_A_if utf) big_step_R t;
     (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
     u \<noteq> PSched;     (part s, u) \<in> policyFlows (pasPolicy initial_aag);
     system.reachable (big_step_ADT_A_if utf) s0 s;
     system.reachable (big_step_ADT_A_if utf) s0 t; part s \<noteq> PSched\<rbrakk> \<Longrightarrow>
  (s', t') \<in> uwr u \<and> (s', t') \<in> uwr PSched \<and> (s', t') \<in> uwr (part s) \<and>
   part s' = part s"
  apply (frule_tac s=s and t=t and X="\<lambda>s t. part s \<noteq> PSched \<and> ((s, t) \<in> uwr PSched \<and>
                                          (s, t) \<in> uwr (part s) \<and> (s, t) \<in> uwr u \<and>
                                          system.reachable (ADT_A_if utf) s0 s \<and>
                                          system.reachable (ADT_A_if utf) s0 t)"
               in relation_preserved_across_sub_big_steps)
      apply (simp add: small_step_reachable del: split_paired_All)+
   apply (intro impI allI | elim conjE)+
   apply (rename_tac sx tx sx' tx')
   apply (subgoal_tac "part sx = part s \<and> part sx' = part s")
    apply (frule_tac u=u and s=sx and t=tx in small_Step_confidentiality_part_not_PSched)
              apply (simp add: small_step_reachable)+
    apply (fastforce intro: Step_system.reachable_Step[OF ADT_A_if_Step_system _ Step_ADT_A_if'',
                                                      rotated])
   apply (elim exE conjE)
   apply (frule schedIncludesCurrentDom)
   apply (frule_tac s'=sx in partitionIntegrity_part_unchanged[OF sub_big_steps_partitionIntegrity])
        apply (blast intro: big_step_R_rtranclp)
       apply (erule small_step_reachable)
      apply assumption
     apply assumption
    apply assumption
   apply (rule conjI, assumption)
   apply (rule partitionIntegrity_part_unchanged[OF sub_big_steps_partitionIntegrity])
        apply assumption
       apply (blast intro: big_step_R_rtranclp)
      apply (erule small_step_reachable)
     apply assumption
    apply assumption
   apply (rule sub_big_steps_not_PSched)
     apply assumption
    apply (blast intro: big_step_R_rtranclp)
   apply assumption
  apply (frule_tac s'=s' in partitionIntegrity_part_unchanged[OF sub_big_steps_partitionIntegrity])
       apply (blast intro: big_step_R_rtranclp)
      apply (erule small_step_reachable)
     apply assumption
    apply assumption
   apply blast
  apply simp
  done

lemma non_PSched_steps_run_in_lock_step':
  "\<lbrakk>(s', as) \<in> sub_big_steps (ADT_A_if utf) big_step_R s;
     (s', t) \<in> data_type.Step (ADT_A_if utf) (); big_step_R s t;
     (s'a, asa) \<in> sub_big_steps (ADT_A_if utf) big_step_R sa;
     (s'a, ta) \<in> data_type.Step (ADT_A_if utf) (); big_step_R sa ta;
     (s, sa) \<in> uwr PSched; (s, sa) \<in> uwr (part s);
     system.reachable (big_step_ADT_A_if utf) s0 s;
     system.reachable (big_step_ADT_A_if utf) s0 sa; part s \<noteq> PSched;
     asa < as\<rbrakk> \<Longrightarrow> False"
  apply (erule strict_prefixE')
  apply (simp, subst (asm) app_Cons)
  apply (drule sub_big_steps_strict_prefix)
  apply (erule exE, rename_tac s'ab)
  apply (frule sub_big_steps_App)
  apply (erule exE, rename_tac s'aa)
  (* s'ab and ta need to be equivalent with respect to part s, which means their
     modes must be equal. The modes between sa and s are equal too,
      which means that big_step_R sa ta and \<not> big_step_R s s'ab is a contradiction *)
  apply (elim conjE)
  apply (frule_tac s=sa in sub_big_steps_reachable, simp add: small_step_reachable)
  apply (frule_tac s=s and s'=s'aa in sub_big_steps_reachable, simp add: small_step_reachable)
  apply (frule_tac s=sa and t=s and u="part s" in sub_big_steps_not_PSched_confidentiality_part)
          apply ((fastforce simp: uwr_sym dest: schedIncludesCurrentDom
                           simp: refl_onD[OF policyFlows_refl, simplified])+)[9]
  apply (elim conjE)
  (*apply (simp del: split_paired_All)*)
  apply (frule_tac s=s'aa and t=s'a and u="part sa" in small_Step_confidentiality_part_not_PSched)
          apply ((fastforce simp: uwr_sym dest: schedIncludesCurrentDom
                           simp: refl_onD[OF policyFlows_refl, simplified])+)[9] (* slowish *)
  apply (elim conjE)
  apply (subgoal_tac "part ta = part s")
   apply (drule schedIncludesCurrentDom)+
   apply (rule_tac s=sa and t=s in  sys_mode_of_eq_big_step_R_contradiction)
      apply (fastforce intro: uwr_part_sys_mode_of_eq'[symmetric])
     prefer 2
     apply assumption
    prefer 2
    apply assumption
   apply (fastforce intro: uwr_part_sys_mode_of_eq'[symmetric])
  apply (rule sym)
  apply (rule trans[rotated])
   apply (erule schedIncludesCurrentDom)
  apply (rule sym, rule partitionIntegrity_part_unchanged[OF sub_big_steps_partitionIntegrity])
       apply assumption
      apply (erule big_step_R_rtranclp)
     apply (erule small_step_reachable)
    apply simp+
  apply (rule sub_big_steps_not_PSched, assumption)
   apply (erule big_step_R_rtranclp)
  apply simp
  done

lemma non_PSched_steps_run_in_lock_step:
  "\<lbrakk>(s', as) \<in> sub_big_steps (ADT_A_if utf) big_step_R s;
    (s', t) \<in> data_type.Step (ADT_A_if utf) (); big_step_R s t;
    (s'a, asa) \<in> sub_big_steps (ADT_A_if utf) big_step_R sa;
    (s'a, ta) \<in> data_type.Step (ADT_A_if utf) (); big_step_R sa ta;
    (s, sa) \<in> uwr PSched; (s, sa) \<in> uwr (part s);
    system.reachable (big_step_ADT_A_if utf) s0 s;
    system.reachable (big_step_ADT_A_if utf) s0 sa;
    part s \<noteq> PSched\<rbrakk>
   \<Longrightarrow> asa = as"
  apply (case_tac "asa = as", assumption)
  apply (drule unit_lists_unequal)
  apply (erule disjE)
   apply (drule non_PSched_steps_run_in_lock_step', simp+)
  apply (frule schedIncludesCurrentDom[symmetric])
  apply (drule_tac as=asa and asa=as in non_PSched_steps_run_in_lock_step', (simp add: uwr_sym)+)
  done

lemma confidentiality_part_not_PSched:
  "\<lbrakk>(s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) ();
    (t, t') \<in> Simulation.Step (big_step_ADT_A_if utf) ()\<rbrakk> \<Longrightarrow>
    (s, t) \<in> uwr PSched \<and> (s, t) \<in> uwr (part s) \<and> (s, t) \<in> uwr u \<and>
    system.reachable (big_step_ADT_A_if utf) s0 s \<and>
    system.reachable (big_step_ADT_A_if utf) s0 t \<and>
    (part s, u) \<in> policyFlows (pasPolicy initial_aag) \<and>
    part s \<noteq> PSched \<and> u \<noteq> PSched \<longrightarrow>
   (s', t') \<in> uwr u"
  apply (simp add: Step_big_step_ADT_A_if)
  apply (erule big_steps.induct)+
  apply (intro impI | elim conjE)+
  apply (subgoal_tac "asa = as")
   apply (drule_tac X="\<lambda>s t. (s, t) \<in> uwr PSched \<and> (s, t) \<in> uwr (part s) \<and>
    (s, t) \<in> uwr u \<and>
    system.reachable (ADT_A_if utf) s0 s \<and>
    system.reachable (ADT_A_if utf) s0 t \<and>
    (part s, u) \<in> policyFlows (pasPolicy initial_aag) \<and>
    part s \<noteq> PSched" in relation_preserved_across_sub_big_steps)
      apply assumption
     apply (fastforce simp: small_step_reachable)
    apply assumption
   apply (simp del: split_paired_All)
   apply (thin_tac "(x,y) \<in> data_type.Step A b" for x y A b
         | thin_tac "big_step_R a b" for a b)+
   apply (intro allI impI | elim conjE)+
   apply (rename_tac x_s x_t x_s' x_t')
   apply (subgoal_tac "part x_s' = part x_s")
    apply (simp del: split_paired_All)
    apply (frule_tac u=u and s=x_s and t=x_t in small_Step_confidentiality_part_not_PSched)
              apply (simp add: small_step_reachable)+
     apply (fastforce intro: Step_system.reachable_Step[OF ADT_A_if_Step_system _ Step_ADT_A_if'',
                                                       rotated])
    apply (elim exE)
    apply (rule trans)
     apply (rule partitionIntegrity_part_unchanged[OF sub_big_steps_partitionIntegrity])
          apply blast
         apply (erule big_step_R_rtranclp)
        apply (erule small_step_reachable)
       apply simp+
     apply (rule sub_big_steps_not_PSched)
       apply blast
      apply (erule big_step_R_rtranclp)
     apply simp
    apply (rule sym)
    apply (rule partitionIntegrity_part_unchanged[OF sub_big_steps_partitionIntegrity])
         apply blast
        apply (erule big_step_R_rtranclp)
       apply (erule small_step_reachable)
      apply (simp+)[3]
   apply (elim conjE)
   apply simp
   apply (drule_tac s=s' and t=s'a and u=u in small_Step_confidentiality_part_not_PSched)
             apply (simp+)[10]
  apply (fastforce dest: non_PSched_steps_run_in_lock_step)
  done

end


lemma try_some_magic:
  "(\<forall>x. y = Some x \<longrightarrow> P x) = ((\<exists>x. y = Some x) \<longrightarrow> P (the y))"
  by auto

lemma thread_set_as_user2:
  "thread_set (tcb_arch_update (arch_tcb_context_set uc)) t = as_user t (modify (\<lambda>_. uc))"
proof -
  have P: "\<And>f. det (modify f)"
    by (simp add: modify_def)
  thus ?thesis
    apply (simp add: as_user_def P thread_set_def)
    apply (clarsimp simp: select_f_def simpler_modify_def bind_def
                          image_def fun_cong[OF arch_tcb_update_aux2])
    done
qed

lemma handle_preemption_agnostic_tc:
  "\<forall>P Q uc uc'. \<lbrace>P\<rbrace> handle_preemption_if uc \<lbrace>\<lambda>_. Q\<rbrace> \<longrightarrow> \<lbrace>P\<rbrace> handle_preemption_if uc' \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (clarsimp simp add: handle_preemption_if_def bind_assoc[symmetric])
  apply (erule bind_return_ign)
  done


context Noninterference_1 begin

lemma preemption_interrupt_scheduler_invisible:
  assumes domains_distinct[wp]: "pas_domains_distinct (aag :: 'a subject_label PAS)"
  shows "equiv_valid_2 (scheduler_equiv aag) (scheduler_affects_equiv aag l)
                       (scheduler_affects_equiv aag l) (\<lambda>r r'. r = uc \<and> snd r' = uc')
                       (einvs and pas_refined aag and guarded_pas_domain aag
                              and domain_sep_inv False st and silc_inv aag st'
                              and (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
                              and (\<lambda>s. ct_idle s \<longrightarrow> uc = idle_context s)
                              and (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s))
                       (einvs and pas_refined aag and guarded_pas_domain aag
                              and domain_sep_inv False st and silc_inv aag st'
                              and (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
                              and (\<lambda>s. ct_idle s \<longrightarrow> uc' = idle_context s)
                              and (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s))
                       (handle_preemption_if uc) (kernel_entry_if Interrupt uc')"
  apply (simp add: kernel_entry_if_def handle_preemption_if_def getActiveIRQ_no_non_kernel_IRQs)
  apply (rule equiv_valid_2_bind_right)
       apply (rule equiv_valid_2_bind_right)
            apply (simp add: liftE_def bind_assoc)
            apply (simp only: option.case_eq_if)
            apply (rule equiv_valid_2_bind_pre[where R'="(=)"])
                 apply (simp add: when_def split del: if_split)
                 apply (subst if_swap)
                 apply (simp split del: if_split)
                 apply (rule equiv_valid_2_bind_pre[where R'="(=)" and Q="\<top>\<top>" and Q'="\<top>\<top>"])
                      apply (rule return_ev2)
                      apply simp
                     apply (rule equiv_valid_2)
                     apply (wp handle_interrupt_reads_respects_scheduler[where st=st] | simp)+
                apply (rule equiv_valid_2)
                apply (rule dmo_getActive_IRQ_reads_respect_scheduler)
               apply (wp dmo_getActiveIRQ_return_axiom[simplified try_some_magic]
                      | simp  add: imp_conjR arch_tcb_update_aux2
                      | elim conjE
                      | intro conjI
                      | wp (once) hoare_drop_imps)+
           apply (subst thread_set_as_user2)
           apply (wp guarded_pas_domain_lift)
          apply ((simp add:  arch_tcb_update_aux2 | wp | force)+)[7]
   apply (fastforce simp: silc_inv_not_cur_thread cur_thread_idle guarded_pas_domain_def)+
  done

lemma handle_preemption_reads_respects_scheduler:
  assumes domains_distinct[wp]: "pas_domains_distinct (aag :: 'a subject_label PAS)"
  shows
    "reads_respects_scheduler aag l (einvs and pas_refined aag and guarded_pas_domain aag
                                           and domain_sep_inv False st and silc_inv aag st'
                                           and (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s))
                              (handle_preemption_if uc)"
  apply (simp add: handle_preemption_if_def)
  apply (wp when_ev handle_interrupt_reads_respects_scheduler
            dmo_getActiveIRQ_return_axiom[simplified try_some_magic]
            dmo_getActive_IRQ_reads_respect_scheduler
         | simp add: imp_conjR| wp (once) hoare_drop_imps)+
  apply force
  done

lemmas handle_preemption_reads_respects_scheduler_2 =
  agnostic_to_ev2[OF handle_preemption_agnostic_tc handle_preemption_context
                     handle_preemption_reads_respects_scheduler]

lemma kernel_entry_scheduler_equiv_2:
  assumes domains_distinct[wp]: "pas_domains_distinct (aag :: 'a subject_label PAS)"
  shows "equiv_valid_2 (scheduler_equiv aag) (scheduler_affects_equiv aag l)
                       (scheduler_affects_equiv aag l) (\<lambda>r r'. snd r = uc \<and> snd r' = uc')
                       (einvs and pas_refined aag and guarded_pas_domain aag
                              and domain_sep_inv False st and silc_inv aag st'
                              and (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
                              and (\<lambda>s. ct_idle s \<longrightarrow> uc = idle_context s)
                              and (\<lambda>s. reads_scheduler_cur_domain aag l s \<longrightarrow> uc = uc'))
                       (einvs and pas_refined aag and guarded_pas_domain aag
                              and domain_sep_inv False st and silc_inv aag st'
                              and (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
                              and (\<lambda>s. ct_idle s \<longrightarrow> uc' = idle_context s)
                              and (\<lambda>s. reads_scheduler_cur_domain aag l s \<longrightarrow> uc = uc'))
                       (kernel_entry_if Interrupt uc) (kernel_entry_if Interrupt uc')"
  apply (simp add: kernel_entry_if_def)
  apply (simp add: bind_assoc[symmetric])
  apply (rule equiv_valid_2_bind_pre[where R'="(=)"])
       apply (rule_tac P="\<top>" and P'="\<top>" in return_ev2)
       apply simp
      apply (rule equiv_valid_2_bind_pre[where R'="(=)"])
           apply (rule equiv_valid_2)
           apply simp
           apply (wp del: no_irq add: handle_interrupt_reads_respects_scheduler[where st=st]
                                      dmo_getActive_IRQ_reads_respect_scheduler
                  | wpc
                  | simp add: imp_conjR all_conj_distrib  arch_tcb_update_aux2
                  | wp (once) hoare_drop_imps)+
          apply (rule context_update_cur_thread_snippit)
         apply (wp thread_set_invs_trivial guarded_pas_domain_lift
                   thread_set_pas_refined thread_set_not_state_valid_sched
                | simp add: tcb_cap_cases_def arch_tcb_update_aux2)+
   apply (fastforce simp: silc_inv_not_cur_thread cur_thread_idle)+
  done

end


context valid_initial_state begin

lemma interrupt_step:
  assumes interrupt:
    "\<And>r. (r,internal_state_if s')
            \<in> fst (kernel_entry_if Interrupt (user_context_of s) (internal_state_if s))
          \<Longrightarrow> sys_mode_of s = KernelEntry Interrupt \<Longrightarrow> (sys_mode_of s' = KernelSchedule True)
          \<Longrightarrow> snd r = user_context_of s \<Longrightarrow> snd r = user_context_of s'
          \<Longrightarrow> cur_domain (internal_state_if s') = cur_domain (internal_state_if s)
          \<Longrightarrow> P"
  assumes preemption:
    "\<And>r. (r,internal_state_if s')
            \<in> fst (handle_preemption_if (user_context_of s) (internal_state_if s))
          \<Longrightarrow> sys_mode_of s = KernelPreempted \<Longrightarrow> sys_mode_of s' = KernelSchedule True
          \<Longrightarrow> r = user_context_of s \<Longrightarrow> r = user_context_of s'
          \<Longrightarrow> cur_domain (internal_state_if s') = cur_domain (internal_state_if s)
          \<Longrightarrow> P"
  shows "\<lbrakk> interrupted_modes (sys_mode_of s); (s,s') \<in> data_type.Step (ADT_A_if utf) () \<rbrakk> \<Longrightarrow> P"
  apply (insert interrupt preemption)
  apply atomize
  apply (case_tac s, clarsimp)
  apply (rename_tac uc i_s mode)
  apply (case_tac mode ; clarsimp)
   sorry (* XXX: broken by touched_addresses. -robs
   subgoal for uc i_s
     apply (clarsimp simp: system.Step_def execution_def steps_def ADT_A_if_def
                            global_automaton_if_def kernel_call_A_if_def
                            kernel_handle_preemption_if_def del: notI)
     apply (frule use_valid[OF _ kernel_entry_context] ; clarsimp)
     apply (frule_tac P1="\<lambda>x. x = cur_domain i_s" in use_valid[OF _ kernel_entry_if_cur_domain])
      apply auto
     done
  subgoal for uc i_s
    apply (clarsimp simp: system.Step_def execution_def steps_def ADT_A_if_def
                           global_automaton_if_def kernel_call_A_if_def
                           kernel_handle_preemption_if_def del: notI)
    apply (frule use_valid[OF _ handle_preemption_context] ; clarsimp)
    apply (frule_tac P1="\<lambda>x. x = cur_domain i_s" in use_valid[OF _ handle_preemption_if_cur_domain])
     apply auto
    done
  done
*)

lemma irq_masks_constant':
  "\<lbrakk> system.reachable (ADT_A_if utf) s0 s1; i_s1 = internal_state_if s1 \<rbrakk>
     \<Longrightarrow> irq_masks_of_state i_s1 = irq_masks_of_state (internal_state_if s0)"
  apply simp
  apply (rule Step_system.reachable_induct[OF ADT_A_if_Step_system,rotated,rotated], rule refl)
   apply (rule trans)
    prefer 2
    apply assumption
   apply (rule ADT_A_if_Step_irq_masks, simp add: Step_ADT_A_if')
   apply (rule ADT_A_if_reachable_invs_if,assumption)
  apply simp
  done

lemmas irq_masks_constant = irq_masks_constant'[OF small_step_reachable]

lemma internal_state_s0: "internal_state_if s0 = s0_internal"
  by (simp add: s0_def)

end


(* FIXME: clarify the following comment *)
(*Lets pretend PSched is labeled with SilcLabel*)
fun label_for_partition where
   "label_for_partition (Partition a) = (OrdinaryLabel a)"
 | "label_for_partition PSched = SilcLabel"


context Noninterference_valid_initial_state begin

lemma uwr_scheduler_affects_equiv:
  "\<lbrakk> (s,s') \<in> uwr PSched; (s,s') \<in> uwr u; invs_if s; invs_if s' \<rbrakk>
     \<Longrightarrow> scheduler_equiv initial_aag (internal_state_if s) (internal_state_if s') \<and>
         scheduler_affects_equiv initial_aag (label_for_partition u)
                                 (internal_state_if s) (internal_state_if s')"
  apply (simp add: uwr_def)
  apply (case_tac u)
   apply simp
   apply (rule sameFor_scheduler_affects_equiv)
      apply (simp add: invs_if_def Invs_def)+
  apply (rule context_conjI)
   apply (rule sameFor_scheduler_equiv,simp+)
  apply (rule SilcLabel_affects_scheduler_equiv)
  apply (rule sameFor_scheduler_equiv,simp)
  done

lemma scheduler_affects_equiv_uwr:
  assumes schedeq:
    "scheduler_equiv initial_aag (internal_state_if s) (internal_state_if s') \<and>
     scheduler_affects_equiv initial_aag (label_for_partition u)
                             (internal_state_if s) (internal_state_if s')"
  assumes imodes: "interrupted_modes (sys_mode_of s) = interrupted_modes (sys_mode_of s')"
  assumes smodes: "scheduler_modes (sys_mode_of s) = scheduler_modes (sys_mode_of s')"
  assumes dom_context:
    "reads_scheduler_cur_domain initial_aag (label_for_partition u) (internal_state_if s)
     \<longrightarrow> (user_modes (sys_mode_of s) \<longrightarrow> user_context_of s = user_context_of s') \<and>
         sys_mode_of s = sys_mode_of s'"
  shows "(s,s') \<in> uwr u"
  apply (case_tac u)
   prefer 2
   apply simp
   apply (simp add: uwr_def)
   apply (rule schedule_reads_affects_equiv_sameFor_PSched')
     apply (simp add: schedeq imodes smodes)+
  apply (insert schedeq dom_context)
  apply (case_tac "reads_scheduler_cur_domain initial_aag (label_for_partition u) (internal_state_if s)")
   apply clarsimp
   apply (frule_tac s="internal_state_if s" and mode="sys_mode_of s" and uc="user_context_of s"
                and uc'="user_context_of s'" and aag="initial_aag"
                 in schedule_reads_affects_equiv_sameFor, simp, simp)
   apply (simp add: uwr_def user_context_of_def sys_mode_of_def)
   apply (case_tac s)
   apply fastforce
  apply simp
  apply (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def sameFor_def
                        sameFor_subject_def uwr_def silc_dom_equiv_def reads_scheduler_def
                        domain_fields_equiv_def
                 intro: globals_equiv_from_scheduler
                 split: if_split_asm)
  apply (case_tac s)
  apply clarsimp
  apply (case_tac s')
  apply (clarsimp simp: disjoint_iff_not_equal)
  apply metis
  done

lemma cur_domain_reads:
  "(s,s') \<in> uwr u
   \<Longrightarrow> reads_scheduler_cur_domain initial_aag (label_for_partition u) (internal_state_if s)
   \<Longrightarrow> (user_modes (sys_mode_of s) \<longrightarrow> user_context_of s = user_context_of s') \<and>
       sys_mode_of s = sys_mode_of s'"
  by (cases u) (auto simp: reads_scheduler_def uwr_def sameFor_def sameFor_subject_def)

lemmas domain_can_read_context = cur_domain_reads[THEN conjunct1]
lemmas domain_can_read_context' = cur_domain_reads[OF uwr_sym, THEN conjunct1]
lemmas domain_can_read_sys_mode = cur_domain_reads[THEN conjunct2]
lemmas domain_can_read_sys_mode' = cur_domain_reads[OF uwr_sym, THEN conjunct2]

lemma equiv_valid_2E:
  assumes ev: "equiv_valid_2 I A B R P P' f g"
  assumes f: "(a,s') \<in> fst (f s)"
  assumes g: "(b,t') \<in> fst (g t)"
  assumes I: "I s t \<and> A s t"
  assumes P: "P s"
  assumes P': "P' t"
  assumes Q: "I s' t' \<Longrightarrow> B s' t' \<Longrightarrow> R a b \<Longrightarrow> S"
  shows S
  apply (insert ev)
  apply (clarsimp simp: equiv_valid_2_def)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply (simp add: I P P')
  apply (drule bspec[OF _ f],simp)
  apply (drule bspec[OF _ g],simp)
  apply (rule Q,simp+)
  done

lemma ev2_sym:
  assumes symI: "\<And>x y. I x y \<Longrightarrow> I y x"
  assumes symA: "\<And>x y. A x y \<Longrightarrow> A y x"
  assumes symB: "\<And>x y. B x y \<Longrightarrow> B y x"
  assumes symR: "\<And>x y. R x y \<Longrightarrow> R' y x"
  shows "equiv_valid_2 I A B R P' P f' f \<Longrightarrow> equiv_valid_2 I A B R' P P' f f'"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (blast intro: symA symB symI symR)
  done

lemma scheduler_step_1_confidentiality:
  notes blob = invs_if_def Invs_def sys_mode_of_def
               silc_inv_cur pas_refined_cur guarded_pas_domain_cur internal_state_s0
               domain_can_read_context domain_can_read_context'
               domain_can_read_sys_mode'[simplified sys_mode_of_def]
               domain_can_read_sys_mode[simplified sys_mode_of_def]
  assumes uwr: "(s,t) \<in> uwr PSched"  "(s,t) \<in> uwr u"
  assumes step_s: "(s,s') \<in> data_type.Step (ADT_A_if utf) ()"
  assumes step_t: "(t,t') \<in> data_type.Step (ADT_A_if utf) ()"
  assumes reach_s: "system.reachable (ADT_A_if utf) s0 s"
  assumes reach_t: "system.reachable (ADT_A_if utf) s0 t"
  shows "interrupted_modes (sys_mode_of s) \<Longrightarrow> (s',t') \<in> uwr u"
  supply [[simp_depth_limit=2]] \<comment> \<open>speedup\<close>
  apply (insert uwr step_s step_t)
  apply (cut_tac ADT_A_if_reachable_invs_if[OF reach_s])
  apply (cut_tac ADT_A_if_reachable_invs_if[OF reach_t])
  apply (cut_tac irq_masks_constant'[OF reach_s, OF refl])
  apply (cut_tac irq_masks_constant'[OF reach_t, OF refl])
  apply (subgoal_tac "interrupted_modes (sys_mode_of t)")
   apply (rule_tac s=s and s'=s' in interrupt_step,simp_all)
    apply (rule_tac s=t and s'=t' in interrupt_step,simp_all)
     apply (rule equiv_valid_2E[where s="internal_state_if s" and t="internal_state_if t",
                                OF kernel_entry_scheduler_equiv_2
                                     [where aag="initial_aag" and st="s0_internal"
                                        and st'="s0_internal" and l="label_for_partition u",
                                      OF domains_distinct]], assumption, assumption)
        apply (rule uwr_scheduler_affects_equiv,assumption+)
       apply ((clarsimp simp: blob)+)[2]
     apply (rule scheduler_affects_equiv_uwr,simp+)
     apply (clarsimp simp: blob)
    apply (rule equiv_valid_2E
                  [where s="internal_state_if s" and t="internal_state_if t",
                   OF ev2_sym[where R'="\<lambda>r r'. r' = user_context_of t \<and> snd r = user_context_of s",
                              OF _ _ _ _ preemption_interrupt_scheduler_invisible
                                           [where aag="initial_aag" and st="s0_internal"
                                              and st'="s0_internal" and l="label_for_partition u"
                                              and uc="user_context_of t" and uc'="user_context_of s",
                                           OF domains_distinct],
                              OF scheduler_equiv_sym scheduler_affects_equiv_sym
                                 scheduler_affects_equiv_sym, simplified]])
         apply (fastforce+)[2]
       apply (rule uwr_scheduler_affects_equiv,assumption+)
      (* FIXME: manual frule *)
      apply (clarsimp simp: blob)
      (* this restores normal form for reads_scheduler_cur_domain *)
      apply (rule ccontr[where P = "_ \<inter> _ = {}"])
      apply (frule (1) domain_can_read_context[where u = u])
      apply (frule domain_can_read_context'[where u = u])
       apply (metis uwr_PSched_cur_domain)
      apply (frule (1) domain_can_read_sys_mode[where u = u, simplified sys_mode_of_def])
      apply force
     apply (clarsimp simp: blob)
     apply (rule ccontr[where P = "_ \<inter> _ = {}"])
     apply (frule (1) domain_can_read_context'[where u = u])
     apply (frule domain_can_read_context[where u = u])
      apply (metis uwr_PSched_cur_domain)
     apply (frule (1) domain_can_read_sys_mode'[where u = u, simplified sys_mode_of_def])
     apply force
    apply (rule scheduler_affects_equiv_uwr,simp+)
    apply (clarsimp simp: blob)
   apply (rule_tac s=t and s'=t' in interrupt_step,simp_all)
    apply (rule equiv_valid_2E[where s="internal_state_if s" and t="internal_state_if t",
                               OF preemption_interrupt_scheduler_invisible
                                    [where aag="initial_aag" and st="s0_internal"
                                       and st'="s0_internal" and uc="user_context_of s"
                                       and l="label_for_partition u", OF domains_distinct]],
           assumption, assumption)
       apply (rule uwr_scheduler_affects_equiv,assumption+)
      (* FIXME: also clean up here *)
      apply (clarsimp simp: blob)
      apply (rule ccontr[where P = "_ \<inter> _ = {}"])
      apply (frule (1) domain_can_read_context[where u = u])
      apply (frule domain_can_read_context'[where u = u])
       apply (metis uwr_PSched_cur_domain)
      apply (frule (1) domain_can_read_sys_mode[where u = u, simplified sys_mode_of_def])
      apply force
     (* FIXME: and here *)
     apply (clarsimp simp: blob)
     apply (rule ccontr[where P = "_ \<inter> _ = {}"])
     apply (frule (1) domain_can_read_context'[where u = u])
     apply (frule domain_can_read_context[where u = u])
      apply (metis uwr_PSched_cur_domain)
     apply (frule (1) domain_can_read_sys_mode'[where u = u, simplified sys_mode_of_def])
     apply force
    apply (rule scheduler_affects_equiv_uwr,simp+)
    apply (clarsimp simp: blob)
   apply (rule equiv_valid_2E[where s="internal_state_if s" and t="internal_state_if t",
                              OF handle_preemption_reads_respects_scheduler_2
                                   [where aag="initial_aag" and st="s0_internal"
                                      and st'="s0_internal" and l="label_for_partition u",
                                    OF domains_distinct]], assumption, assumption)
      apply (rule uwr_scheduler_affects_equiv,assumption+)
     apply ((clarsimp simp: blob)+)[2]
   apply (rule scheduler_affects_equiv_uwr,simp+)
   apply (clarsimp simp: blob)
  apply (clarsimp simp add: sameFor_def sameFor_scheduler_def uwr_def)
  done

end


lemma schedule_if_context:
  "\<lbrace>\<top>\<rbrace> schedule_if tc \<lbrace>\<lambda>r s. r = tc\<rbrace>"
  apply (simp add: schedule_if_def)
  apply (wp | simp)+
  done

lemma schedule_step:
  assumes schedule:
    "\<And>r. \<lbrakk> (r,internal_state_if s') \<in> fst (schedule_if (user_context_of s) (internal_state_if s));
            sys_mode_of s' = KernelExit; r = user_context_of s; r = user_context_of s' \<rbrakk>
            \<Longrightarrow> P"
  shows
    "\<lbrakk> (sys_mode_of s) = KernelSchedule b; (s,s') \<in> data_type.Step (ADT_A_if utf) () \<rbrakk>
       \<Longrightarrow> P"
  apply (insert schedule)
  apply atomize
  apply (case_tac s, clarsimp)
  apply (rename_tac uc i_s)
  apply (simp_all add: system.Step_def execution_def steps_def ADT_A_if_def
                       global_automaton_if_def kernel_schedule_if_def
         | safe | clarsimp)+
   apply (frule use_valid[OF _ schedule_if_context], simp+)+
  done

lemma schedule_if_reads_respects_scheduler:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_scheduler aag l
           (einvs and pas_refined aag and silc_inv aag st and guarded_pas_domain aag and tick_done)
           (schedule_if uc)"
  apply (simp add: schedule_if_def)
  apply (wp schedule_reads_respects_scheduler schedule_guarded_pas_domain)
  apply fastforce
  done

lemma schedule_if_agnostic_tc:
  "\<forall>P Q uc uc'. \<lbrace>P\<rbrace> schedule_if uc \<lbrace>\<lambda>_. Q\<rbrace> \<longrightarrow> \<lbrace>P\<rbrace> schedule_if uc' \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (clarsimp simp add: schedule_if_def bind_assoc[symmetric])
  apply (erule bind_return_ign)
  done


context valid_initial_state begin

lemma step_from_interrupt_to_schedule:
  "\<lbrakk> (s', evs) \<in> sub_big_steps (ADT_A_if utf) big_step_R s;
     evs \<noteq> []; interrupted_modes (sys_mode_of s) \<rbrakk>
     \<Longrightarrow> (s,s') \<in> data_type.Step (ADT_A_if utf) () \<and> (sys_mode_of s') = KernelSchedule True"
  apply (induct rule: sub_big_steps.induct)
   apply simp
  apply (case_tac "evlist'")
   apply simp
   apply (erule sub_big_steps.cases)
    apply simp
    apply (erule interrupt_step[rotated,rotated],assumption)
     apply ((simp add: big_step_R_def sys_mode_of_def)+)[2]
   apply simp
  apply simp
  apply (elim conjE)
  apply (erule schedule_step[rotated],assumption)
  apply (simp add: big_step_R_def sys_mode_of_def)
  done

lemma scheduler_steps:
  assumes big_step: "(s,s'') \<in> data_type.Step (big_step_ADT_A_if utf) ()"
  assumes interrupted: "part s = PSched"
  obtains s' where "(s,s') \<in> data_type.Step (ADT_A_if utf) ()"
                   "sys_mode_of s' = KernelSchedule True"
                   "(s',s'') \<in> data_type.Step (ADT_A_if utf) ()"
  apply (insert big_step interrupted)
  apply (simp add: Step_big_step_ADT_A_if)
  apply (simp add: big_steps.simps)
  apply clarsimp
  apply (subgoal_tac "interrupted_modes (sys_mode_of s)")
   prefer 2
   apply (clarsimp simp add: big_step_R_def part_def sys_mode_of_def split: if_split_asm)
   apply (case_tac "snd s",simp_all)
  apply (case_tac "as = []")

   apply (erule sub_big_steps.cases)
    apply simp
    apply (erule interrupt_step[rotated,rotated],assumption)
     apply ((simp add: big_step_R_def sys_mode_of_def)+)[3]
  apply (frule step_from_interrupt_to_schedule)
  by clarsimp+

lemma PSched_reachable_interrupted:
  "\<lbrakk> part s = PSched; system.reachable (big_step_ADT_A_if utf) s0 s \<rbrakk>
     \<Longrightarrow> interrupted_modes (sys_mode_of s)"
  apply (drule big_step_R_rtranclp)
  apply (drule tranclp_s0)
  apply (clarsimp simp add: part_def sys_mode_of_def split: if_split_asm)
  done

(*If we're starting a non_schedule partition then we must have just exited*)
lemma reachable_nonsched_exit:
  "\<lbrakk> system.reachable (big_step_ADT_A_if utf) s0 s; part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> (snd s) = KernelExit"
  apply (drule big_step_R_rtranclp)
  apply (drule tranclp_s0)
  apply (clarsimp simp add: part_def split: if_split_asm)
  apply (case_tac s)
  apply simp
  apply (simp add: sys_mode_of_def)
  apply (case_tac b; simp)
  done

lemma silc_dom_equiv_current_aag:
  "silc_dom_equiv (current_aag s) st s' = silc_dom_equiv initial_aag st s'"
  by (simp add: silc_dom_equiv_def pasObjectAbs_current_aag)

end


lemmas schedule_if_reads_respects_scheduler_2 =
  agnostic_to_ev2[OF schedule_if_agnostic_tc schedule_if_context
                     schedule_if_reads_respects_scheduler]

lemma big_Step2:
  "(s,s') \<in> system.Step (big_step_ADT_A_if utf) u \<Longrightarrow>
   (s,s') \<in> Simulation.Step (big_step_ADT_A_if utf) u"
  apply (simp add: system.Step_def execution_def big_step_ADT_A_if_def
                   big_step_adt_def ADT_A_if_def steps_def)
  apply blast
  done


context Noninterference_valid_initial_state begin

lemma scheduler_step_2_confidentiality:
  notes blob = invs_if_def Invs_def sys_mode_of_def silc_inv_cur pas_refined_cur
               guarded_pas_domain_cur internal_state_s0 tick_done_def
  assumes uwr: "(s,t) \<in> uwr PSched" "(s,t) \<in> uwr u"
  assumes step_s: "(s,s') \<in> data_type.Step (ADT_A_if utf) ()"
  assumes step_t: "(t,t') \<in> data_type.Step (ADT_A_if utf) ()"
  assumes reach_s: "system.reachable (ADT_A_if utf) s0 s"
  assumes reach_t: "system.reachable (ADT_A_if utf) s0 t"
  shows "\<lbrakk> (sys_mode_of s) = KernelSchedule True; (sys_mode_of t) = KernelSchedule True \<rbrakk>
           \<Longrightarrow> (s',t') \<in> uwr u"
  apply (insert uwr step_s step_t)
  apply (rule_tac s=s and s'=s' in schedule_step,simp_all)
  apply (rule_tac s=t and s'=t' in schedule_step,simp_all)
  apply (cut_tac ADT_A_if_reachable_invs_if[OF reach_s])
  apply (cut_tac ADT_A_if_reachable_invs_if[OF reach_t])
  apply (rule equiv_valid_2E[where s="internal_state_if s" and t="internal_state_if t",
                             OF schedule_if_reads_respects_scheduler_2
                                  [where aag="initial_aag" and st="s0_internal"
                                     and l="label_for_partition u", OF domains_distinct]],
         assumption,assumption)
     apply (rule uwr_scheduler_affects_equiv,simp+)
    apply ((clarsimp simp: blob)+)[2]
  apply (rule scheduler_affects_equiv_uwr,simp+)
  done

lemma confidentiality_part_sched_transition:
  "\<lbrakk> (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
     system.reachable (big_step_ADT_A_if utf) s0 s; system.reachable (big_step_ADT_A_if utf) s0 t;
     (s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) ();
     (t, t') \<in> Simulation.Step (big_step_ADT_A_if utf) ();
     (part s, u) \<in> policyFlows (pasPolicy initial_aag); part s = PSched \<rbrakk>
     \<Longrightarrow> (s', t') \<in> uwr u"
  apply (frule schedIncludesCurrentDom)
  apply (case_tac "part s = PSched")
   apply simp
   apply (erule scheduler_steps, assumption+)
   apply (erule scheduler_steps, simp)
   apply (frule (3) scheduler_step_1_confidentiality[where u=PSched])
      apply (erule small_step_reachable)+
    apply (rule PSched_reachable_interrupted,simp+)
   apply (frule (3) scheduler_step_1_confidentiality[where u=u])
      apply (erule small_step_reachable)+
    apply (rule PSched_reachable_interrupted,simp+)
   apply (frule_tac s="s'a" and t="s'aa" and u=u in scheduler_step_2_confidentiality,
          assumption, assumption, assumption)
       apply (rule Step_system.reachable_Step[OF ADT_A_if_Step_system _ Step_ADT_A_if''])
         apply (erule small_step_reachable, simp)
       apply (erule small_step_reachable)
      apply (rule Step_system.reachable_Step[OF ADT_A_if_Step_system _ Step_ADT_A_if''])
        apply (erule small_step_reachable, simp)
      apply (erule small_step_reachable)
     apply simp+
  done

lemma confidentiality_for_sched:
  "\<lbrakk> (s, t) \<in> uwr PSched;
     system.reachable (big_step_ADT_A_if utf) s0 s; system.reachable (big_step_ADT_A_if utf) s0 t;
     (s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) ();
     (t, t') \<in> Simulation.Step (big_step_ADT_A_if utf) (); part s \<noteq> PSched \<rbrakk>
     \<Longrightarrow> (s', t') \<in> uwr PSched"
  apply (frule schedIncludesCurrentDom)
  apply (frule_tac s=s in reachable_nonsched_exit,assumption)
  apply (frule_tac s=t in reachable_nonsched_exit,simp)
  apply (frule_tac s=s and s'=s' in Step_partitionIntegrity,simp+)
  apply (frule_tac s=t and s'=t' in Step_partitionIntegrity,simp+)
  apply (simp add: uwr_def sameFor_def)
  apply (simp add: sameFor_scheduler_def)
  apply clarsimp
  apply (case_tac s')
  apply clarsimp
  apply (case_tac t')
  apply clarsimp
  apply (clarsimp simp add: partitionIntegrity_def)
  apply (rule conjI)
   apply (metis domain_fields_equiv_sym domain_fields_equiv_trans)
  apply (rule conjI)
   apply (metis globals_equiv_scheduler_sym globals_equiv_scheduler_trans)
  apply (rule conjI)
   apply (fold silc_dom_equiv_def)
   apply (simp add: silc_dom_equiv_current_aag)
   apply (metis silc_dom_equiv_sym silc_dom_equiv_trans)
  apply (rule conjI)
   apply (rule trans)
    apply (rule sym)
    apply (rule_tac ?s1.0="((a, b), KernelExit)" in big_step_irq_state_next_irq)
         apply (simp add: reachable_invs_if)
        apply (simp add: big_step_R_rtranclp)
       apply simp+
   apply (subgoal_tac "irq_masks_of_state b = irq_masks_of_state bb")
    apply simp
    apply (rule_tac ?s1.0="((aa, bb), KernelExit)" in big_step_irq_state_next_irq)
         apply (simp add: reachable_invs_if)
        apply (simp add: big_step_R_rtranclp)
       apply simp+
   apply (rule trans)
    apply (rule irq_masks_constant,assumption,fastforce)
   apply (rule sym)
   apply (rule irq_masks_constant,assumption,fastforce)
  apply (simp add: Step_big_step_ADT_A_if)
  apply (erule big_stepsE)
  apply (erule big_stepsE)
  apply (simp add: big_step_R_def)
  apply (case_tac baa, simp_all)
   apply (case_tac bca, simp_all)
  apply (case_tac bca, simp_all)
  done

lemma confidentiality_part:
  "\<lbrakk> (s, t) \<in> uwr PSched; (s, t) \<in> uwr (part s); (s, t) \<in> uwr u;
     system.reachable (big_step_ADT_A_if utf) s0 s; system.reachable (big_step_ADT_A_if utf) s0 t;
     (s, s') \<in> Simulation.Step (big_step_ADT_A_if utf) ();
     (t, t') \<in> Simulation.Step (big_step_ADT_A_if utf) ();
     (part s, u) \<in> policyFlows (pasPolicy initial_aag); u = PSched \<longrightarrow> part s = PSched \<rbrakk>
     \<Longrightarrow> (s', t') \<in> uwr u"
  apply (frule schedIncludesCurrentDom)
  apply (case_tac "part s = PSched")
   apply (fastforce intro: confidentiality_part_sched_transition)
  apply (fastforce intro: confidentiality_part_not_PSched[rule_format])
  done

lemma confidentiality_u:
  notes split_paired_All[simp del]
  shows "ni.confidentiality_u"
  apply (simp add: ni.confidentiality_u_def | intro allI impI | elim conjE)+
  apply (case_tac "(part s, u) \<in> policyFlows (pasPolicy initial_aag)")
   apply (simp)
   apply (fastforce intro: confidentiality_part schedNotGlobalChannel simp: big_Step2)
  apply (case_tac "u = PSched")
   apply (subgoal_tac "part s \<noteq> PSched")
    apply (blast intro: confidentiality_for_sched big_Step2)
   apply (fastforce intro: policyFlows_refl[THEN refl_onD])
  apply (metis integrity_part uwr_sym uwr_trans schedIncludesCurrentDom not_PSched big_Step2)
  done

(* TOPLEVEL *)
lemma nonleakage:
  "ni.Nonleakage_gen"
  apply (rule Nonleakage_gen[OF confidentiality_u])
  done

(* TOPLEVEL *)
lemma xnonleakage:
  "ni.xNonleakage_gen"
  apply (rule xNonleakage_gen[OF confidentiality_u])
  done

end

end
