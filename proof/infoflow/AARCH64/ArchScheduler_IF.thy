(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchScheduler_IF
imports Scheduler_IF

begin

context Arch begin arch_global_naming

named_theorems Scheduler_IF_assms

definition arch_globals_equiv_scheduler :: "kheap \<Rightarrow> kheap \<Rightarrow> arch_state \<Rightarrow> arch_state \<Rightarrow> bool" where
  "arch_globals_equiv_scheduler kh kh' as as' \<equiv>
     arm_us_global_vspace as = arm_us_global_vspace as' \<and> kh (arm_us_global_vspace as) = kh' (arm_us_global_vspace as)"

definition
  "arch_scheduler_affects_equiv s s' \<equiv> True"

lemma arch_globals_equiv_from_scheduler[Scheduler_IF_assms]:
  "\<lbrakk> arch_globals_equiv_scheduler (kheap s) (kheap s') (arch_state s) (arch_state s');
     cur_thread s' \<noteq> idle_thread s \<longrightarrow> arch_scheduler_affects_equiv s s' \<rbrakk>
     \<Longrightarrow> arch_globals_equiv (cur_thread s') (idle_thread s) (kheap s) (kheap s')
                            (arch_state s) (arch_state s') (machine_state s) (machine_state s')"
  by (clarsimp simp: arch_globals_equiv_scheduler_def arch_scheduler_affects_equiv_def)

lemma arch_globals_equiv_scheduler_refl[Scheduler_IF_assms]:
  "arch_globals_equiv_scheduler (kheap s) (kheap s) (arch_state s) (arch_state s)"
  by (simp add: idle_equiv_refl arch_globals_equiv_scheduler_def)

lemma arch_globals_equiv_scheduler_sym[Scheduler_IF_assms]:
  "arch_globals_equiv_scheduler (kheap s) (kheap s') (arch_state s) (arch_state s')
   \<Longrightarrow> arch_globals_equiv_scheduler (kheap s') (kheap s) (arch_state s') (arch_state s)"
  by (auto simp: arch_globals_equiv_scheduler_def)

lemma arch_globals_equiv_scheduler_trans[Scheduler_IF_assms]:
  "\<lbrakk> arch_globals_equiv_scheduler (kheap s) (kheap s') (arch_state s) (arch_state s');
     arch_globals_equiv_scheduler (kheap s') (kheap s'') (arch_state s') (arch_state s'') \<rbrakk>
     \<Longrightarrow> arch_globals_equiv_scheduler (kheap s) (kheap s'') (arch_state s) (arch_state s'')"
  by (clarsimp simp: arch_globals_equiv_scheduler_def)

lemma arch_scheduler_affects_equiv_trans[Scheduler_IF_assms, elim]:
  "\<lbrakk> arch_scheduler_affects_equiv s s'; arch_scheduler_affects_equiv s' s'' \<rbrakk>
     \<Longrightarrow> arch_scheduler_affects_equiv s s''"
  by (simp add: arch_scheduler_affects_equiv_def)

lemma arch_scheduler_affects_equiv_sym[Scheduler_IF_assms, elim]:
  "arch_scheduler_affects_equiv s s' \<Longrightarrow> arch_scheduler_affects_equiv s' s"
  by (simp add: arch_scheduler_affects_equiv_def)

lemma arch_scheduler_affects_equiv_sa_update[Scheduler_IF_assms, simp]:
  "arch_scheduler_affects_equiv (scheduler_action_update f s) s' =
   arch_scheduler_affects_equiv s s'"
  "arch_scheduler_affects_equiv s (scheduler_action_update f s') =
   arch_scheduler_affects_equiv s s'"
  by (auto simp: arch_scheduler_affects_equiv_def)

lemma equiv_asid_cur_thread_update[Scheduler_IF_assms, simp]:
  "equiv_asid asid (cur_thread_update f s) s' = equiv_asid asid s s'"
  "equiv_asid asid s (cur_thread_update f s') = equiv_asid asid s s'"
  by (auto simp: equiv_asid_def)

lemma arch_scheduler_affects_equiv_ready_queues_update[Scheduler_IF_assms, simp]:
  "arch_scheduler_affects_equiv (ready_queues_update f s) s' = arch_scheduler_affects_equiv s s'"
  "arch_scheduler_affects_equiv s (ready_queues_update f s') = arch_scheduler_affects_equiv s s'"
  by (auto simp: arch_scheduler_affects_equiv_def)

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for idle_thread[Scheduler_IF_assms, wp]: "\<lambda>s :: det_state. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

declare arch_prepare_next_domain_idle_thread[Scheduler_IF_assms]

crunch arch_switch_to_thread, arch_switch_to_idle_thread
  for cur_domain[Scheduler_IF_assms, wp]: "\<lambda>s. P (cur_domain s)"
  and domain_fields[Scheduler_IF_assms, wp]: "domain_fields P"

lemma arch_switch_to_idle_thread_globals_equiv[Scheduler_IF_assms,wp]:
  "\<lbrace>valid_arch_state and globals_equiv st\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding arch_switch_to_idle_thread_def
  by wpsimp

lemma arch_switch_to_idle_thread_work_units_completed[Scheduler_IF_assms,wp]:
  "arch_switch_to_idle_thread \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace>"
  by wp

crunch arch_activate_idle_thread
  for cur_domain[Scheduler_IF_assms, wp]: "\<lambda>s. P (cur_domain s)"
  and idle_thread[Scheduler_IF_assms, wp]: "\<lambda>s. P (idle_thread s)"
  and irq_state_of_state[Scheduler_IF_assms, wp]: "\<lambda>s. P (irq_state_of_state s)"
  and domain_fields[Scheduler_IF_assms, wp]: "domain_fields P"

lemma arch_scheduler_affects_equiv_cur_thread_update[Scheduler_IF_assms, simp]:
  "arch_scheduler_affects_equiv (cur_thread_update f s) s' = arch_scheduler_affects_equiv s s'"
  "arch_scheduler_affects_equiv s (cur_thread_update f s') = arch_scheduler_affects_equiv s s'"
  by (auto simp: arch_scheduler_affects_equiv_def)

lemma equiv_asid_domain_time_update[Scheduler_IF_assms, simp]:
  "equiv_asid asid (domain_time_update f s) s' = equiv_asid asid s s'"
  "equiv_asid asid s (domain_time_update f s') = equiv_asid asid s s'"
  by (auto simp: equiv_asid_def)

lemma arch_scheduler_affects_equiv_domain_time_update[Scheduler_IF_assms, simp]:
  "arch_scheduler_affects_equiv (domain_time_update f s) s' = arch_scheduler_affects_equiv s s'"
  "arch_scheduler_affects_equiv s (domain_time_update f s') = arch_scheduler_affects_equiv s s'"
  by (auto simp: arch_scheduler_affects_equiv_def)

crunch ackInterrupt
  for irq_state[Scheduler_IF_assms, wp]: "\<lambda>s. P (irq_state s)"

lemma thread_set_context_globals_equiv[Scheduler_IF_assms]:
  "\<lbrace>(\<lambda>s. t = idle_thread s \<longrightarrow> tc = idle_context s) and invs and globals_equiv st\<rbrace>
   thread_set (tcb_arch_update (arch_tcb_context_set tc)) t
   \<lbrace>\<lambda>rv. globals_equiv st\<rbrace>"
  apply (clarsimp simp: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (subgoal_tac "t \<noteq> arm_us_global_vspace (arch_state s)")
   apply (clarsimp simp: idle_equiv_def globals_equiv_def tcb_at_def2 get_tcb_def idle_context_def)
   apply (clarsimp split: option.splits kernel_object.splits)
  apply (fastforce simp: get_tcb_def obj_at_def valid_arch_state_def
                   dest: valid_global_arch_objs_pt_at invs_arch_state)
  done

lemma arch_scheduler_affects_equiv_update[Scheduler_IF_assms]:
  "arch_scheduler_affects_equiv st s
   \<Longrightarrow> arch_scheduler_affects_equiv st (s\<lparr>kheap := (kheap s)(x \<mapsto> TCB y')\<rparr>)"
  by (clarsimp simp: arch_scheduler_affects_equiv_def)

lemma equiv_asid_equiv_update[Scheduler_IF_assms]:
  "\<lbrakk> get_tcb x s = Some y; equiv_asid asid st s \<rbrakk>
     \<Longrightarrow> equiv_asid asid st (s\<lparr>kheap := (kheap s)(x \<mapsto> TCB y')\<rparr>)"
  by (clarsimp simp: equiv_asid_def obj_at_def get_tcb_def)

declare arch_activate_idle_thread_domain_fields_invs[Scheduler_IF_assms]

end


arch_requalify_consts
  arch_globals_equiv_scheduler
  arch_scheduler_affects_equiv

global_interpretation Scheduler_IF_1?:
  Scheduler_IF_1 arch_globals_equiv_scheduler arch_scheduler_affects_equiv
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Scheduler_IF_assms)?)
qed


context Arch begin arch_global_naming

(* scheduler_affects_equiv - states_equiv_for_labels *)
definition scheduler_affects_inv where
  "scheduler_affects_inv aag l st s \<equiv>
     (reads_scheduler_cur_domain aag l st \<or> reads_scheduler_cur_domain aag l s \<longrightarrow>
      cur_thread st = cur_thread s \<and>
      scheduler_action st = scheduler_action s \<and>
      work_units_completed st = work_units_completed s \<and>
      scheduler_globals_frame_equiv st s \<and>
      idle_thread st = idle_thread s \<and>
      (cur_thread st \<noteq> idle_thread s \<longrightarrow> arch_scheduler_affects_equiv st s))"

definition scheduler_inv where
  "scheduler_inv aag l s s' \<equiv>
     scheduler_equiv aag s s' \<and> scheduler_affects_inv aag l s s'"

abbreviation (input) scheduler_can_read where
  "scheduler_can_read aag l \<equiv> \<lambda>l'. l' \<in> reads_scheduler aag l"

lemma domains_distinct_states_equiv_for_labels:
  "pas_domains_distinct aag
   \<Longrightarrow> states_equiv_for_labels aag L s s' = states_equiv_but_for_labels aag (not L) s s'"
  apply (rule iffI; erule states_equiv_for_guard_imp; clarsimp)
   apply (fastforce simp: pas_domains_distinct_def)
  apply (clarsimp simp: pas_domains_distinct_def)
  apply (erule_tac x=x in allE, clarsimp)
  done

lemma scheduler_affects_equiv_def2:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "scheduler_affects_equiv aag l s s' \<equiv>
   states_equiv_but_for_labels aag (not scheduler_can_read aag l) s s' \<and> scheduler_affects_inv aag l s s'"
  apply (rule eq_reflection)
  apply (simp only: domains_distinct_states_equiv_for_labels[OF domains_distinct,symmetric])
  apply (auto simp: scheduler_affects_equiv_def scheduler_affects_inv_def)
  done

lemma scheduler_inv_def2:
  "scheduler_inv aag l s s' \<equiv>
     domain_fields_equiv s s' \<and> idle_thread s = idle_thread s' \<and>
     globals_equiv_scheduler s s' \<and> silc_dom_equiv aag s s' \<and>
     irq_state_of_state s = irq_state_of_state s' \<and>
     (reads_scheduler_cur_domain aag l s \<or> reads_scheduler_cur_domain aag l s'
      \<longrightarrow> (cur_thread s = cur_thread s' \<and> scheduler_action s = scheduler_action s' \<and>
           work_units_completed s = work_units_completed s' \<and>
           scheduler_globals_frame_equiv s s' \<and>
           (cur_thread s \<noteq> idle_thread s' \<longrightarrow> arch_scheduler_affects_equiv s s')))"
  apply (rule eq_reflection)
  apply (auto simp: scheduler_inv_def scheduler_equiv_def scheduler_affects_inv_def)
  done

lemma reads_respects_scheduler_def2:
  "reads_respects_scheduler aag l P f \<equiv>
   equiv_valid_inv (scheduler_inv aag l) (states_equiv_for_labels aag (scheduler_can_read aag l)) P f"
  apply (rule eq_reflection)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (rule iff_allI)+
  apply (rule iffI; clarsimp)
   apply (drule mp)
    apply (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def scheduler_inv_def2)
   apply (drule (1) bspec, clarsimp)+
   apply (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def scheduler_inv_def2)
  apply (drule mp)
   apply (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def scheduler_inv_def2)
  apply (drule (1) bspec, clarsimp)+
  apply (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def scheduler_inv_def2)
  done

lemma domain_fields_equiv_sym:
  "domain_fields_equiv st s = domain_fields_equiv s st"
  by (auto simp: domain_fields_equiv_def)

lemma reads_respects_scheduler_from_labels:
  assumes ev: "\<And>L. states_equiv_valid aag L P f"
    and inv: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (work_units_completed s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (irq_state_of_state s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
             "\<And>P st. \<lbrace>\<lambda>s. P (domain_fields_equiv st s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (domain_fields_equiv st s)\<rbrace>"
             "\<And>P st. \<lbrace>\<lambda>s. P (globals_equiv_scheduler st s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (globals_equiv_scheduler st s)\<rbrace>"
             "\<And>P st. \<lbrace>\<lambda>s. P (scheduler_globals_frame_equiv st s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (scheduler_globals_frame_equiv st s)\<rbrace>"
             "\<And>P st. \<lbrace>\<lambda>s. P (silc_dom_equiv aag st s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (silc_dom_equiv aag st s)\<rbrace>"
  shows "reads_respects_scheduler aag l (P and Q) f"
  apply (simp add: reads_respects_scheduler_def2)
  apply (rule equiv_valid_inv_split_lr)
   apply (rule equiv_valid_rv_inv_lift)
  unfolding scheduler_inv_def2
     apply (rule hoare_weaken_pre)
      apply clarsimp
      apply (rule hoare_lift_Pf2_pre_conj[where f=cur_domain, rotated], wp inv)
      apply (rule hoare_lift_Pf2_pre_conj[where f=cur_thread, rotated], wp inv)
      apply (rule hoare_lift_Pf2_pre_conj[where f=idle_thread, rotated], wp inv)
      apply (rule hoare_lift_Pf2_pre_conj[where f=idle_thread, rotated], wp inv)
      apply (rule hoare_lift_Pf2_pre_conj[where f=scheduler_action, rotated], wp inv)
      apply (rule hoare_lift_Pf2_pre_conj[where f=work_units_completed, rotated], wp inv)
      apply (rule hoare_lift_Pf2_pre_conj[where f=irq_state_of_state, rotated], wp inv)
      apply (rule hoare_lift_Pf2_pre_conj[where f=idle_thread, rotated], wp inv)
      apply (rule_tac f="domain_fields_equiv st" in hoare_lift_Pf2_pre_conj[rotated], wp inv)
      apply (rule_tac f="globals_equiv_scheduler st" in hoare_lift_Pf2_pre_conj[rotated], wp inv)
      apply (rule_tac f="scheduler_globals_frame_equiv st" in hoare_lift_Pf2_pre_conj[rotated], wp inv)
      apply (rule_tac f="silc_dom_equiv aag st" in hoare_lift_Pf2_pre_conj[rotated], wp inv)
      apply (clarsimp simp: arch_scheduler_affects_equiv_def)
      apply wp
     apply (clarsimp simp: arch_scheduler_affects_equiv_def)
    apply (auto simp: domain_fields_equiv_sym globals_equiv_scheduler_sym silc_dom_equiv_sym
                      scheduler_globals_frame_equiv_sym arch_scheduler_affects_equiv_sym)[2]
  apply (insert ev)
  apply (fastforce elim: wp_pre)
  done

definition swap_things where
  "swap_things s t \<equiv>
     t\<lparr>machine_state := underlying_memory_update
                          (\<lambda>m a. if a \<in> scheduler_affects_globals_frame t
                                 then underlying_memory (machine_state s) a
                                 else m a)
                          (machine_state t)\<rparr>
      \<lparr>cur_thread := cur_thread s\<rparr>"

lemma globals_equiv_scheduler_inv'[Scheduler_IF_assms]:
  "(\<And>st. \<lbrace>P and globals_equiv st\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>)
   \<Longrightarrow> \<lbrace>P and globals_equiv_scheduler s\<rbrace> f \<lbrace>\<lambda>_. globals_equiv_scheduler s\<rbrace>"
  apply atomize
  apply (rule use_spec)
  apply (simp add: spec_valid_def)
  apply (erule_tac x="(swap_things sa s)" in allE)
  apply (rule_tac Q'="\<lambda>r st. globals_equiv (swap_things sa s) st" in hoare_strengthen_post)
   apply (rule hoare_pre)
    apply assumption
   apply (clarsimp simp: globals_equiv_def swap_things_def globals_equiv_scheduler_def
                         arch_globals_equiv_scheduler_def arch_scheduler_affects_equiv_def)+
  done

crunch vcpu_switch
  for global_pt[wp]: "\<lambda>s. P (global_pt s)"
  (wp: valid_global_arch_objs_lift)

crunch vcpu_switch
  for valid_global_arch_objs[wp]: "valid_global_arch_objs"
  (wp: valid_global_arch_objs_lift)

lemma arch_switch_to_thread_globals_equiv_scheduler[Scheduler_IF_assms]:
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace>
   arch_switch_to_thread thread
   \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  unfolding arch_switch_to_thread_def storeWord_def
  apply (wpsimp wp: dmo_wp modify_wp thread_get_wp' lazy_fpu_restore_globals_equiv
                    globals_equiv_scheduler_inv'[where P="invs"])
   apply (auto intro: sym_refs_VCPU_hyp_live)
  done

crunch arch_activate_idle_thread
  for silc_dom_equiv[Scheduler_IF_assms, wp]: "silc_dom_equiv aag st"
  and scheduler_affects_equiv[Scheduler_IF_assms, wp]: "scheduler_affects_equiv aag l st"

lemma set_vm_root_arch_scheduler_affects_equiv[wp]:
  "set_vm_root tcb \<lbrace>arch_scheduler_affects_equiv st\<rbrace>"
  unfolding arch_scheduler_affects_equiv_def by wpsimp

lemmas set_vm_root_scheduler_affects_equiv[wp] =
  scheduler_affects_equiv_unobservable[OF set_vm_root_states_equiv_for
                                          set_vm_root_cur_domain _ _ _ set_vm_root_it
                                          set_vm_root_arch_scheduler_affects_equiv]

lemma set_vm_root_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l valid_global_arch_objs (set_vm_root thread)"
  apply (rule reads_respects_scheduler_unobservable'[OF scheduler_equiv_lift'
                                                          [OF globals_equiv_scheduler_inv']])
  apply (wp silc_dom_equiv_states_equiv_lift set_vm_root_states_equiv_for | simp)+
  done

lemma store_cur_thread_fragment_midstrength_reads_respects:
  "equiv_valid (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
               (scheduler_affects_equiv aag l) \<top>
               (do x \<leftarrow> modify (cur_thread_update (\<lambda>_. t));
                   set_scheduler_action resume_cur_thread
                od)"
  apply (rule equiv_valid_guard_imp)
   apply (rule equiv_valid_weaken_pre)
    apply (rule ev_asahi_ex_to_full_fragement)
   apply  (auto simp: midstrength_scheduler_affects_equiv_def asahi_scheduler_affects_equiv_def
                           asahi_ex_scheduler_affects_equiv_def states_equiv_for_def equiv_for_def
                           arch_scheduler_affects_equiv_def equiv_asids_def equiv_asid_def
                           scheduler_globals_frame_equiv_def
                 simp del: split_paired_All)
  done

lemma set_vm_root_globals_equiv_scheduler:
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace>
   set_vm_root t
   \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  by (rule globals_equiv_scheduler_inv', wpsimp)

lemma equiv_valid_inv_A_conjI:
  "\<lbrakk> equiv_valid_inv I A P f; equiv_valid_rv_inv I A' \<top>\<top> P f \<rbrakk>
     \<Longrightarrow> equiv_valid_inv I (\<lambda>s s'. A s s' \<and> A' s s') P f"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (erule_tac x=s in allE, erule_tac x=s in allE)
  apply (erule_tac x=t in allE, erule_tac x=t in allE)
  apply fastforce
  done

lemma scheduler_globals_frame_equiv_triv[simp]:
  "scheduler_globals_frame_equiv st s"
  by (clarsimp simp: scheduler_globals_frame_equiv_def)

lemma midstrength_reads_respects_scheduler_from_labels:
  assumes ev: "\<And>L. states_equiv_valid aag L P f"
  assumes inv: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
               "\<And>P. \<lbrace>\<lambda>s. P (irq_state_of_state s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
               "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (work_units_completed s)\<rbrace>"
               "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
               "\<And>st. \<lbrace>\<lambda>s. domain_fields_equiv st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. domain_fields_equiv st s\<rbrace>"
               "\<And>st. \<lbrace>\<lambda>s. globals_equiv_scheduler st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. globals_equiv_scheduler st s\<rbrace>"
               "\<And>st. \<lbrace>\<lambda>s. silc_dom_equiv aag st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. silc_dom_equiv aag st s\<rbrace>"
  shows "equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l) (P and Q) f"
  apply (rule equiv_valid_inv_split_lr)
   apply (rule equiv_valid_rv_inv_lift)
  unfolding scheduler_equiv_def
     apply (wpsimp wp: inv)
    apply (auto simp: domain_fields_equiv_sym globals_equiv_scheduler_sym silc_dom_equiv_sym)[2]
  unfolding midstrength_scheduler_affects_equiv_def
  apply (rule equiv_valid_inv_A_conjI)
   apply (rule_tac Q=P in equiv_valid_guard_imp)
    apply (insert ev)[1]
    apply fastforce
   apply simp
  apply (rule_tac Q=Q and Q'=Q in equiv_valid_2_guard_imp)
    apply (rule equiv_valid_rv_inv_lift)
      apply (wpsimp wp: inv hoare_vcg_imp_lift)+
    apply auto
  done

lemma weak_reads_respects_scheduler_from_labels:
  assumes ev: "\<And>L. states_equiv_valid aag L P f"
    and inv: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (irq_state_of_state s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
             "\<And>st. \<lbrace>\<lambda>s. domain_fields_equiv st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. domain_fields_equiv st s\<rbrace>"
             "\<And>st. \<lbrace>\<lambda>s. globals_equiv_scheduler st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. globals_equiv_scheduler st s\<rbrace>"
             "\<And>st. \<lbrace>\<lambda>s. silc_dom_equiv aag st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. silc_dom_equiv aag st s\<rbrace>"
  shows "equiv_valid_inv (scheduler_equiv aag) (weak_scheduler_affects_equiv aag l) (P and Q) f"
  apply (rule equiv_valid_inv_split_lr)
   apply (rule equiv_valid_rv_inv_lift)
  unfolding scheduler_equiv_def
     apply (wpsimp wp: inv)
    apply (auto simp: domain_fields_equiv_sym globals_equiv_scheduler_sym silc_dom_equiv_sym)[2]
  unfolding weak_scheduler_affects_equiv_def
  apply (rule_tac Q=P in equiv_valid_guard_imp)
   apply (insert ev)[1]
   apply fastforce
  apply simp
  done

lemmas globals_equiv_scheduler_inv = globals_equiv_scheduler_inv'[where P="\<top>",simplified]

lemmas set_global_user_vspace_globals_equiv_scheduler[wp] =
  globals_equiv_scheduler_inv[OF set_global_user_vspace_globals_equiv]

lemma set_vcpu_silc_dom_equiv:
  "\<lbrace>silc_dom_equiv aag st and valid_silc_label aag\<rbrace> set_vcpu ptr vcpu \<lbrace>\<lambda>_. silc_dom_equiv aag st\<rbrace>"
  unfolding set_vcpu_def
  by (wpsimp wp: set_object_silc_dom_equiv simp: is_cap_table_def)

crunch vcpu_save_reg
  for silc_dom_equiv[wp]: "silc_dom_equiv aag st"
  (wp: crunch_wps valid_silc_label_lift simp: crunch_simps)

lemma vcpu_save_reg_range_silc_dom_equiv[wp]:
  "\<lbrace>silc_dom_equiv aag st and valid_silc_label aag\<rbrace>
   vcpu_save_reg_range vr from to
   \<lbrace>\<lambda>_. silc_dom_equiv aag st\<rbrace>"
  unfolding vcpu_save_reg_range_def
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp_inv)
   apply (wpsimp wp: valid_silc_label_lift)+
  done

crunch vcpu_save, vcpu_restore
  for silc_dom_equiv: "silc_dom_equiv aag st"
  (wp: crunch_wps valid_silc_label_lift simp: crunch_simps)

crunch vcpu_switch
  for silc_dom_equiv[wp]: "silc_dom_equiv aag st"
  (wp: crunch_wps valid_silc_label_lift simp: crunch_simps)

crunch arch_switch_to_idle_thread
   for silc_dom_equiv[wp]: "silc_dom_equiv aag st"
  (wp: crunch_wps valid_silc_label_lift simp: crunch_simps)

crunch arch_switch_to_thread
   for silc_dom_equiv[wp]: "silc_dom_equiv aag st"
  (wp: crunch_wps valid_silc_label_lift simp: crunch_simps)

crunch arch_prepare_next_domain
  for silc_dom_equiv[wp]: "silc_dom_equiv aag st"
  and typ_at[wp]: "\<lambda>s. P (typ_at T ptr s)"
  (wp: crunch_wps valid_silc_label_lift simp: crunch_simps)

lemma next_domain_snippet_cur_vcpu_in_cur_domain:
  "\<lbrace>\<top>\<rbrace> do y <- arch_prepare_next_domain;
          next_domain
       od
   \<lbrace>\<lambda>_. cur_vcpu_in_cur_domain\<rbrace>"
  unfolding arch_prepare_next_domain_def
  by wpsimp

lemma next_domain_snippet_cur_fpu_in_cur_domain:
  "\<lbrace>\<top>\<rbrace> do y <- arch_prepare_next_domain;
          next_domain
       od
   \<lbrace>\<lambda>_. cur_fpu_in_cur_domain\<rbrace>"
  unfolding arch_prepare_next_domain_def
  by wpsimp

lemmas [Scheduler_IF_assms] =
  arch_switch_to_thread_silc_dom_equiv
  arch_switch_to_idle_thread_silc_dom_equiv
  set_scheduler_action_cur_vcpu_in_cur_domain
  set_scheduler_action_cur_fpu_in_cur_domain
  tcb_sched_action_cur_vcpu_in_cur_domain
  tcb_sched_action_cur_fpu_in_cur_domain
  next_domain_snippet_cur_vcpu_in_cur_domain
  next_domain_snippet_cur_fpu_in_cur_domain
  arch_prepare_next_domain_silc_dom_equiv
  arch_prepare_next_domain_typ_at

lemma vcpu_switch_globals_equiv_scheduler[wp]:
  "\<lbrace>valid_arch_state and globals_equiv_scheduler s\<rbrace> vcpu_switch vr \<lbrace>\<lambda>_. globals_equiv_scheduler s\<rbrace>"
  by (wp globals_equiv_scheduler_inv' vcpu_switch_globals_equiv | fastforce)+

lemma vcpu_switch_midstrength_reads_respects_scheduler:
  "equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
     (valid_arch_state and valid_silc_label aag) (vcpu_switch vopt)"
  apply (rule equiv_valid_guard_imp)
   apply (rule midstrength_reads_respects_scheduler_from_labels)
          apply (rule vcpu_switch_states_equiv_valid)
         apply (wpsimp wp: domain_fields_equiv_lift | erule conjunct1)+
  done

lemma set_global_user_vspace_states_equiv_for[wp]:
  "set_global_user_vspace \<lbrace>states_equiv_for P Q R S st\<rbrace>"
  unfolding set_global_user_vspace_def setVSpaceRoot_def
  by (wpsimp wp: do_machine_op_mol_states_equiv_for)

lemma set_global_user_vspace_midstrength_reads_respects:
  "equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
                   \<top> set_global_user_vspace"
  apply (rule equiv_valid_inv_unobservable)
      apply (rule hoare_pre)
       apply (rule scheduler_equiv_lift')
            apply wpsimp+
     apply (wp midstrength_scheduler_affects_equiv_unobservable
                    | simp | wps)+
     apply (auto simp: scheduler_equiv_sym midstrength_scheduler_affects_equiv_sym)
  done

lemma arch_switch_to_idle_thread_midstrength_reads_respects[Scheduler_IF_assms]:
  "equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
                   (valid_arch_state and valid_silc_label aag) arch_switch_to_idle_thread"
  unfolding arch_switch_to_idle_thread_def
  by (wp set_global_user_vspace_midstrength_reads_respects vcpu_switch_midstrength_reads_respects_scheduler)

lemma arch_switch_to_idle_thread_globals_equiv_scheduler[Scheduler_IF_assms, wp]:
  "\<lbrace>valid_arch_state and globals_equiv_scheduler sta\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  unfolding arch_switch_to_idle_thread_def storeWord_def
  by (wp dmo_wp modify_wp thread_get_wp' set_vm_root_globals_equiv_scheduler)

lemma states_equiv_but_for_labels_equiv_for_lift:
  assumes "\<And>st. \<lbrace>\<lambda>s. equiv_but_for_labels aag {l. L l} st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_. equiv_but_for_labels aag {l. L l} st\<rbrace>"
  shows "\<lbrace>\<lambda>s. states_equiv_but_for_labels aag L st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_. states_equiv_but_for_labels aag L st\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (prop_tac "equiv_but_for_labels aag {l. L l} s s")
   apply (clarsimp simp: equiv_but_for_labels_def states_equiv_for_refl)
  apply (insert assms)
  apply (erule_tac x=s in meta_allE)
  apply (drule use_valid)
    apply assumption
   apply simp
  apply (clarsimp simp: equiv_but_for_labels_def)
  apply (erule (1) states_equiv_for_trans)
  done

lemma vcpu_switch_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and>
        (\<forall>vr. vopt = Some vr \<longrightarrow> pasObjectAbs aag vr \<in> L) \<and>
        (\<forall>vr b. current_vcpu s = Some (vr,b) \<longrightarrow> pasObjectAbs aag vr \<in> L)\<rbrace>
   vcpu_switch vopt
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpc | wp modify_current_vcpu_equiv_but_for_labels)+
  apply clarsimp
  apply (rule conjI)
   apply (auto simp: cur_vcpu_of_def cur_vcpu_for_def)[1]
  apply clarsimp
  apply (rule conjI)
   apply (auto simp: cur_vcpu_of_def cur_vcpu_for_def)[1]
  apply clarsimp
  apply (case_tac b)
   apply (auto simp: cur_vcpu_of_def cur_vcpu_for_def)[1]
  apply clarsimp
  apply (case_tac "a = x")
   apply (auto simp: cur_vcpu_of_def cur_vcpu_for_def)[1]
  apply clarsimp
  apply (clarsimp simp: cur_vcpu_for_Some)
  done

lemma vcpu_switch_None_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and>
        (\<forall>vr b. current_vcpu s = Some (vr,True) \<longrightarrow> pasObjectAbs aag vr \<in> L)\<rbrace>
   vcpu_switch None
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpc | wp modify_current_vcpu_equiv_but_for_labels)+
  apply (auto simp: cur_vcpu_of_def cur_vcpu_for_def)[1]
  done

lemma tcb_invisible:
  "\<lbrakk> \<not> reads_scheduler_cur_domain aag l s; pas_refined aag s; in_cur_domain t s; tcb_at t s \<rbrakk>
    \<Longrightarrow> pasObjectAbs aag t \<notin> reads_scheduler aag l"
  apply (drule tcb_at_ko_at, clarsimp)
  apply (drule ko_at_etcbD)
  apply (frule (1) tcb_domain_wellformed)
  apply (prop_tac "etcb_domain (etcb_of tcb) = cur_domain s")
   apply (clarsimp simp: in_cur_domain_def)
   apply (clarsimp simp: etcbs_of'_def etcb_at'_def split: option.splits kernel_object.splits)
  apply simp
  by blast

lemma vcpu_controls_associated_tcb:
  "\<lbrakk> pas_refined aag s; vcpus_of s v = Some vcpu; vcpu_tcb vcpu = Some t \<rbrakk>
     \<Longrightarrow> (v, Control, t) \<in> state_objs_to_policy s"
  by (fastforce simp: sbta_href state_objs_to_policy_def state_hyp_refs_of_def opt_map_def
                dest: pas_refined_mem is_subject_trans split: option.splits)+

(* FIXME AARCH64 IF: move *)
lemma invs_cur_vcpu:
  "invs s \<Longrightarrow> cur_vcpu s"
  by (auto simp: invs_def valid_state_def valid_arch_state_def)

lemma vcpu_invisible:
  assumes nrs: "\<not> reads_scheduler_cur_domain aag l s"
  and pwn: "pas_wellformed_noninterference aag"
  shows
  "\<lbrakk> pas_refined aag s; valid_silc_label aag s;
     invs s; current_vcpu s = Some (vr,b); cur_vcpu_in_cur_domain s \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag vr \<notin> reads_scheduler aag l"
  apply (prop_tac "cur_vcpu s")
   apply (erule invs_cur_vcpu)
  apply (clarsimp simp: cur_vcpu_def opt_pred_def split: option.splits)
  apply (clarsimp simp: cur_vcpu_in_cur_domain_def cur_vcpu_tcb_def)
  apply (clarsimp simp: opt_map_def split: option.splits)
  apply (rename_tac t vcpu)
  apply (prop_tac "tcb_at t s")
   apply (drule invs_valid_objs)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_vcpu_def obj_at_def)
  apply (frule (2) tcb_invisible[OF nrs])
  apply (frule_tac vcpu=vcpu in vcpu_controls_associated_tcb)
    apply (fastforce simp: opt_map_def split: option.splits)
   apply simp
  apply (prop_tac "pasObjectAbs aag vr \<noteq> SilcLabel")
   apply (fastforce simp: valid_silc_label_def obj_at_def is_cap_table_def)
  apply (drule (1) pas_refined_mem)
  apply (drule aag_wellformed_Control)
  using pwn apply (fastforce simp: pas_wellformed_noninterference_def)
  apply simp
  done

lemma arch_switch_to_idle_thread_unobservable[Scheduler_IF_assms]:
  assumes wellformed: "pas_wellformed_noninterference aag"
  notes domains_distinct = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
    "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
      scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and
      invs and cur_vcpu_in_cur_domain and valid_silc_label aag and pas_refined aag\<rbrace>
     arch_switch_to_idle_thread
     \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply wp
    apply (rule scheduler_affects_equiv_unobservable)
          apply wpsimp+
    apply (unfold arch_scheduler_affects_equiv_def)[1]
    apply wpsimp
   apply (unfold scheduler_affects_equiv_def2[OF domains_distinct])
   apply (wp states_equiv_but_for_labels_equiv_for_lift)
    apply (wp vcpu_switch_None_equiv_but_for_labels)
   apply (simp add: scheduler_affects_inv_def arch_scheduler_affects_equiv_def)
   apply wps
   apply wpsimp
  using wellformed apply (clarsimp simp: vcpu_invisible)
  done

lemma lazy_fpu_restore_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> (\<forall>t. cur_fpu_of s t \<longrightarrow> pasObjectAbs aag t \<in> L) \<and>
        pasObjectAbs aag t \<in> L \<and> valid_cur_fpu s\<rbrace>
   lazy_fpu_restore t
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding lazy_fpu_restore_def
  apply wpsimp
     apply (wp switch_local_fpu_owner_equiv_but_for_labels)
    apply wpsimp+
   apply (wp thread_get_wp')
  apply clarsimp
  done

lemma cur_fpu_invisible:
  "\<lbrakk> pas_refined aag s; \<not> reads_scheduler_cur_domain aag l s; cur_fpu_in_cur_domain s;
     valid_cur_fpu s; current_fpu s = Some t \<rbrakk>
    \<Longrightarrow> pasObjectAbs aag t \<notin> reads_scheduler aag l"
  apply (clarsimp simp: cur_fpu_in_cur_domain_def)
  apply (frule current_fpu_owner_Some_tcb_at, fastforce)
  apply (drule tcb_at_ko_at, clarsimp)
  apply (drule ko_at_etcbD)
  apply (frule (1) tcb_domain_wellformed)
  apply (prop_tac "etcb_domain (etcb_of tcb) = cur_domain s")
   apply (clarsimp simp: in_cur_domain_def)
   apply (clarsimp simp: etcbs_of'_def etcb_at'_def split: option.splits kernel_object.splits)
  apply simp
  by blast

lemma states_equiv_for_helper:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "states_equiv_for (\<lambda>x. pasObjectAbs aag x \<in> reads_scheduler aag l)
                      (\<lambda>x. pasIRQAbs aag x \<in> reads_scheduler aag l)
                      (\<lambda>x. pasASIDAbs aag x \<in> reads_scheduler aag l)
                      (\<lambda>x. \<exists>la\<in>pasDomainAbs aag x. la \<in> reads_scheduler aag l)
                      st s =
     states_equiv_but_for_labels aag (\<lambda>l'. l' \<notin> reads_scheduler aag l) st s"
  apply clarsimp
  apply (rule iffI; erule rsubst[where P="\<lambda>x. states_equiv_for _ _ _ x _ _"]; rule ext)
   using domains_distinct
   apply (clarsimp simp: pas_domains_distinct_def)
   apply (erule_tac x=x in allE)
   apply clarsimp
  using domains_distinct
  apply (clarsimp simp: pas_domains_distinct_def)
  apply (erule_tac x=x in allE)
  apply clarsimp
  done

lemma lazy_fpu_restore_scheduler_affects_equiv:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "\<lbrace>\<lambda>s. scheduler_affects_equiv aag l st s \<and> pas_refined aag s \<and>
        \<not> reads_scheduler_cur_domain aag l s \<and> pasObjectAbs aag t \<notin> reads_scheduler aag l \<and>
        cur_fpu_in_cur_domain s \<and> valid_cur_fpu s\<rbrace>
   lazy_fpu_restore t
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (rule wp_pre)
  unfolding scheduler_affects_equiv_def
   apply (rule hoare_vcg_conj_lift)
    defer
    apply (clarsimp simp: arch_scheduler_affects_equiv_def)
    apply (wpsimp wp: hoare_vcg_imp_lift' simp: scheduler_globals_frame_equiv_def)
   apply (rule conjI)
    prefer 2
    apply clarsimp
   defer
   apply (rule_tac Q'="\<lambda>_. states_equiv_but_for_labels aag (\<lambda>l'. l' \<notin> reads_scheduler aag l) st"
                in hoare_strengthen_post[rotated])
    apply (clarsimp simp:)
    apply (subst states_equiv_for_helper[OF domains_distinct])
    apply (clarsimp simp: equiv_but_for_labels_def)
   apply (wp states_equiv_but_for_labels_equiv_for_lift)
   apply (wp lazy_fpu_restore_equiv_but_for_labels)
  apply (subst (asm) states_equiv_for_helper[OF domains_distinct])
  apply (clarsimp simp: equiv_but_for_labels_def)
  apply (clarsimp simp: cur_fpu_invisible)
  done

lemma vcpu_switch_scheduler_affects_equiv:
  assumes wellformed: "pas_wellformed_noninterference aag"
  notes domains_distinct = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
    "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
      K (\<forall>vr. vopt = Some vr \<longrightarrow> pasObjectAbs aag vr \<notin> reads_scheduler aag l) and
      scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and
      invs and cur_vcpu_in_cur_domain and valid_silc_label aag and pas_refined aag\<rbrace>
     vcpu_switch vopt
     \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (unfold scheduler_affects_equiv_def2[OF domains_distinct])
  apply (wp states_equiv_but_for_labels_equiv_for_lift)
    apply (wp vcpu_switch_equiv_but_for_labels)
   apply (unfold scheduler_affects_inv_def arch_scheduler_affects_equiv_def)
   apply simp
   apply wps
   apply wpsimp
  apply simp
  using wellformed apply (clarsimp simp: vcpu_invisible)
  done

lemma tcb_controls_associated_vcpu:
  "\<lbrakk> pas_refined aag s; get_tcb t s = Some tcb; tcb_vcpu (tcb_arch tcb) = Some v \<rbrakk>
     \<Longrightarrow> (t, Control, v) \<in> state_objs_to_policy s"
  by (fastforce simp: sbta_href state_objs_to_policy_def state_hyp_refs_of_def get_tcb_def
                dest: pas_refined_mem is_subject_trans split: option.splits kernel_object.splits)+

lemma associated_vcpu_invisible:
  "\<lbrakk> pas_wellformed_noninterference aag; pasObjectAbs aag t \<notin> reads_scheduler aag l;
     pas_refined aag s; valid_silc_label aag s; invs s;
     get_tcb t s = Some tcb; tcb_vcpu (tcb_arch tcb) = Some vr \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag vr \<notin> reads_scheduler aag l"
  apply (frule (2) tcb_controls_associated_vcpu)
  apply (prop_tac "pasObjectAbs aag t \<noteq> SilcLabel")
   apply (fastforce simp: valid_silc_label_def obj_at_def is_cap_table_def get_tcb_Some)
  apply (drule (1) pas_refined_mem)
  apply (drule aag_wellformed_Control)
   apply (fastforce simp: pas_wellformed_noninterference_def)
  apply simp
  done

lemma arch_switch_to_thread_unobservable[Scheduler_IF_assms]:
  assumes wellformed[wp]: "pas_wellformed_noninterference aag"
  notes domains_distinct[wp] = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
  "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
    (\<lambda>s. pasObjectAbs aag t \<notin> reads_scheduler aag l) and
    scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and
    invs and cur_vcpu_in_cur_domain and cur_fpu_in_cur_domain and
    valid_silc_label aag and pas_refined aag\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (wp set_vm_root_scheduler_affects_equiv lazy_fpu_restore_scheduler_affects_equiv
            vcpu_switch_scheduler_affects_equiv | simp)+
  apply clarsimp
  apply (rule conjI)
   prefer 2
   apply fastforce
  using wellformed by (clarsimp simp: associated_vcpu_invisible)

(* Can split, but probably more effort to generalise *)
lemma next_domain_midstrength_equiv_scheduler[Scheduler_IF_assms]:
  "equiv_valid (scheduler_equiv aag) (weak_scheduler_affects_equiv aag l)
               (midstrength_scheduler_affects_equiv aag l) \<top> next_domain"
  apply (simp add: next_domain_def)
  apply (subst is_extended.dxo_eq)
   apply (clarsimp simp: is_extended_def is_extended'_def is_extended_axioms_def)
   apply wpsimp
  apply (clarsimp simp: modify_modify)
  apply (rule ev_modify)
  apply (clarsimp simp: equiv_for_def equiv_asid_def equiv_asids_def Let_def scheduler_equiv_def
                        globals_equiv_scheduler_def silc_dom_equiv_def domain_fields_equiv_def
                        weak_scheduler_affects_equiv_def midstrength_scheduler_affects_equiv_def
                        states_equiv_for_def idle_equiv_def equiv_hyp_def equiv_fpu_def cur_fpu_for_def get_tcb_def)
  done

lemma resetTimer_irq_state[wp]:
  "resetTimer \<lbrace>\<lambda>s. P (irq_state s)\<rbrace>"
  apply (simp add: resetTimer_def machine_op_lift_def machine_rest_lift_def)
  apply (wp | wpc| simp)+
  done

lemma dmo_resetTimer_underlying_memory[wp]:
  "do_machine_op resetTimer \<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma dmo_resetTimer_device_state[wp]:
  "do_machine_op resetTimer \<lbrace>\<lambda>s. P (device_state (machine_state s))\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma dmo_resetTimer_vcpu_state[wp]:
  "do_machine_op resetTimer \<lbrace>\<lambda>s. P (vcpu_state (machine_state s))\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma dmo_resetTimer_fpu_state[wp]:
  "do_machine_op resetTimer \<lbrace>\<lambda>s. P (fpu_state (machine_state s))\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma dmo_resetTimer_tcb_cur_fpu_of[wp]:
  "do_machine_op resetTimer \<lbrace>\<lambda>s. P (tcb_cur_fpu_of s)\<rbrace>"
  by (wpsimp wp: dmo_wp simp: comp_def)

lemma dmo_resetTimer_reads_respects_scheduler[Scheduler_IF_assms]:
  "reads_respects_scheduler aag l \<top> (do_machine_op resetTimer)"
  apply (rule reads_respects_scheduler_unobservable)
   apply (rule scheduler_equiv_lift)
        apply (simp add: globals_equiv_scheduler_def[abs_def]  idle_equiv_def)
        apply (wpsimp wp: dmo_wp)
       apply ((wp silc_dom_lift dmo_wp | simp)+)[5]
  apply (rule scheduler_affects_equiv_unobservable)
  unfolding states_equiv_for_def[abs_def]
        apply (wp equiv_for_lift equiv_machine_state_lift equiv_asids_lift equiv_hyp_lift equiv_fpu_lift)+
  apply (wpsimp wp: dmo_wp simp: arch_scheduler_affects_equiv_def)
  done

lemma ackInterrupt_reads_respects_scheduler[Scheduler_IF_assms]:
  "reads_respects_scheduler aag l \<top> (do_machine_op (ackInterrupt irq))"
  apply (rule reads_respects_scheduler_unobservable)
   apply (rule scheduler_equiv_lift)
        apply (simp add:  globals_equiv_scheduler_def[abs_def] idle_equiv_def)
        apply (rule hoare_pre)
         apply wps
         apply (wp dmo_wp ackInterrupt_irq_masks | simp add:no_irq_def)+
        apply clarsimp
       apply ((wp silc_dom_lift dmo_wp | simp)+)[5]
  apply (rule scheduler_affects_equiv_unobservable)
        apply (simp add: states_equiv_for_def[abs_def] equiv_for_def equiv_asids_def equiv_asid_def)
        apply (rule hoare_pre)
         apply wps
         apply (wp dmo_wp | simp add: arch_scheduler_affects_equiv_def ackInterrupt_def)+
  done

lemma thread_set_scheduler_affects_equiv[Scheduler_IF_assms, wp]:
  "\<lbrace>(\<lambda>s. x \<noteq> idle_thread s \<longrightarrow> pasObjectAbs aag x \<notin> reads_scheduler aag l) and
    (\<lambda>s. x = idle_thread s \<longrightarrow> tc = idle_context s) and scheduler_affects_equiv aag l st\<rbrace>
   thread_set (tcb_arch_update (arch_tcb_context_set tc)) x
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_wp)
  apply (intro impI conjI)
  apply (case_tac "x \<noteq> idle_thread s",simp_all)
   apply (clarsimp simp: scheduler_affects_equiv_def get_tcb_def scheduler_globals_frame_equiv_def
                  split: option.splits kernel_object.splits)
   apply (clarsimp simp: arch_scheduler_affects_equiv_def)
   apply (elim states_equiv_forE equiv_forE)
   apply (rule states_equiv_forI,simp_all add: equiv_for_def equiv_asids_def equiv_asid_def)
    apply (clarsimp simp: obj_at_def)
   apply (clarsimp simp: equiv_fpu_def equiv_for_def cur_fpu_for_def get_tcb_def)
  apply (clarsimp simp: idle_context_def get_tcb_def
                  split: option.splits kernel_object.splits)
  apply (subst arch_tcb_update_aux)
  apply simp
  apply (subgoal_tac "s = (s\<lparr>kheap := (kheap s)(idle_thread s \<mapsto> TCB y)\<rparr>)", simp)
  apply (rule state.equality)
                  apply (rule ext)
                  apply simp+
  done


lemma thread_set_reads_respects_scheduler[Scheduler_IF_assms]:
  "reads_respects_scheduler aag l (valid_arch_state and K (valid_tcb_context_update f))
                                  (thread_set f t)"
  apply (rule gen_asm_ev)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  unfolding thread_set_def gets_the_def gets_def get_def put_def return_def fail_def
            set_object_def get_object_def assert_def assert_opt_def
  apply (clarsimp simp: bind_def split: option.splits if_splits)
  apply (clarsimp simp: get_tcb_ko_at obj_at_def)
  unfolding valid_tcb_context_update_def
  apply (rename_tac s' tcb tcb')
  apply (erule_tac x=tcb in allE)
  apply (erule_tac x=tcb' in allE)
  apply (rule conjI)
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def)
   apply (intro conjI)
     apply (clarsimp simp: valid_global_arch_objs_def arch_globals_equiv_scheduler_def)
    apply (clarsimp simp: idle_equiv_def tcb_at_def get_tcb_def arch_tcb_context_get_def)
   apply (clarsimp simp: silc_dom_equiv_def equiv_for_def)
  apply (clarsimp simp: scheduler_affects_equiv_def)
  apply (intro conjI)
  apply (clarsimp simp: states_equiv_for_def equiv_for_def)
  apply (intro conjI; clarsimp?)
    apply (clarsimp simp: equiv_asids_def equiv_asid_def obj_at_def)
   apply (clarsimp simp: equiv_fpu_def equiv_for_def cur_fpu_for_def get_tcb_def arch_tcb_context_set_def arch_tcb_context_get_def)
  apply (clarsimp simp: scheduler_globals_frame_equiv_def arch_scheduler_affects_equiv_def)
  done

lemma arch_activate_idle_thread_reads_respects_scheduler[Scheduler_IF_assms, wp]:
  "reads_respects_scheduler aag l \<top> (arch_activate_idle_thread rv)"
  unfolding arch_activate_idle_thread_def by wpsimp

lemma tcb_visible:
  "\<lbrakk> reads_scheduler_cur_domain aag l s; pas_refined aag s;
     pas_domains_distinct aag; in_cur_domain t s; tcb_at t s \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag t \<in> reads_scheduler aag l"
  apply (drule tcb_at_ko_at, clarsimp)
  apply (drule ko_at_etcbD)
  apply (frule (1) tcb_domain_wellformed)
  apply (prop_tac "etcb_domain (etcb_of tcb) = cur_domain s")
   apply (clarsimp simp: in_cur_domain_def)
   apply (clarsimp simp: etcbs_of'_def etcb_at'_def split: option.splits kernel_object.splits)
  apply (clarsimp simp: pas_domains_distinct_def)
  apply (erule_tac x="cur_domain s" in allE)
  apply clarsimp
  done

lemma associated_vcpu_visible:
  assumes nrs: "reads_scheduler_cur_domain aag l s"
  and pwn: "pas_wellformed_noninterference aag"
  shows
  "\<lbrakk> pasObjectAbs aag t \<in> reads_scheduler aag l;
     pas_refined aag s; valid_silc_label aag s; invs s;
     get_tcb t s = Some tcb; tcb_vcpu (tcb_arch tcb) = Some vr \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag vr \<in> reads_scheduler aag l"
  apply (frule (2) tcb_controls_associated_vcpu)
  apply (prop_tac "pasObjectAbs aag t \<noteq> SilcLabel")
   apply (fastforce simp: valid_silc_label_def obj_at_def is_cap_table_def get_tcb_Some)
  apply (drule (1) pas_refined_mem)
  apply (drule aag_wellformed_Control)
  using pwn apply (fastforce simp: pas_wellformed_noninterference_def)
  apply simp
  done

lemma vcpu_visible:
  assumes rs: "reads_scheduler_cur_domain aag l s"
  and wellformed: "pas_wellformed_noninterference aag"
  notes domains_distinct[wp] = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
  "\<lbrakk> pas_refined aag s; valid_silc_label aag s;
     invs s; current_vcpu s = Some (vr,b); cur_vcpu_in_cur_domain s \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag vr \<in> reads_scheduler aag l"
  apply (prop_tac "cur_vcpu s")
   apply (erule invs_cur_vcpu)
  apply (clarsimp simp: cur_vcpu_def opt_pred_def split: option.splits)
  apply (clarsimp simp: cur_vcpu_in_cur_domain_def cur_vcpu_tcb_def)
  apply (clarsimp simp: opt_map_def split: option.splits)
  apply (rename_tac t vcpu)
  apply (prop_tac "tcb_at t s")
   apply (drule invs_valid_objs)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_vcpu_def obj_at_def)
  apply (frule (2) tcb_visible[OF rs _ domains_distinct])
  apply (frule_tac vcpu=vcpu in vcpu_controls_associated_tcb)
    apply (fastforce simp: opt_map_def split: option.splits)
   apply simp
  apply (prop_tac "pasObjectAbs aag vr \<noteq> SilcLabel")
   apply (fastforce simp: valid_silc_label_def obj_at_def is_cap_table_def)
  apply (drule (1) pas_refined_mem)
  apply (drule aag_wellformed_Control)
  using wellformed apply (fastforce simp: pas_wellformed_noninterference_def)
  apply simp
  done

lemma gets_current_vcpu_weak_reads_respects_scheduler:
  assumes wellformed[simp]: "pas_wellformed_noninterference aag"
  notes domains_distinct[wp] = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
  "weak_reads_respects_scheduler aag l
     (reads_scheduler_cur_domain aag l and pas_refined aag and valid_silc_label aag
                                       and invs and cur_vcpu_in_cur_domain)
     (gets (arm_current_vcpu \<circ> arch_state))"
  apply (wp gets_ev'')
   prefer 2
   apply assumption
  apply clarsimp
  apply (prop_tac "equiv_for (\<lambda>vr. pasObjectAbs aag vr \<in> reads_scheduler aag l) cur_vcpu_of s t")
   apply (clarsimp simp: weak_scheduler_affects_equiv_def states_equiv_for_def equiv_hyp_def)
  apply (case_tac "\<exists>vr b. current_vcpu s = Some (vr,b)", clarsimp)
   apply (subgoal_tac "pasObjectAbs aag vr \<in> reads_scheduler aag l")
    apply (fastforce simp: equiv_for_def cur_vcpu_of_def split: if_splits option.splits)
   apply (erule vcpu_visible)
        apply simp+
  apply (case_tac "\<exists>vr b. current_vcpu t = Some (vr,b)", clarsimp)
   apply (subgoal_tac "pasObjectAbs aag vr \<in> reads_scheduler aag l")
    apply (fastforce simp: equiv_for_def cur_vcpu_of_def split: if_splits option.splits)
  apply (erule_tac s=t in vcpu_visible)
        apply simp+
  done

lemma vcpu_disable_None_states_equiv_valid:
  "states_equiv_valid aag L (\<lambda>s. \<exists>vr. current_vcpu s = Some (vr,True)) (vcpu_disable None)"
  apply (simp only: vcpu_disable_def fun_app_def bind_assoc[symmetric] vcpu_save_vgic_defs[symmetric])
  apply (clarsimp simp: dmo_distr)
  apply wpsimp
  done

lemma vcpu_disable_globals_equiv_scheduler[wp]:
  "\<lbrace>valid_arch_state and globals_equiv_scheduler s\<rbrace> vcpu_disable vr \<lbrace>\<lambda>_. globals_equiv_scheduler s\<rbrace>"
  by (wp globals_equiv_scheduler_inv' | fastforce)+

lemma vcpu_disable_None_weak_reads_respects_scheduler:
  "weak_reads_respects_scheduler aag l
     (\<lambda>s. valid_arch_state s \<and> valid_silc_label aag s \<and> (\<exists>vr. current_vcpu s = Some (vr,True)))
     (vcpu_disable None)"
  apply (rule equiv_valid_guard_imp)
  apply (rule weak_reads_respects_scheduler_from_labels[where Q="valid_arch_state and valid_silc_label aag"])
         apply (rule vcpu_disable_None_states_equiv_valid)
        apply (wpsimp wp: domain_fields_equiv_lift)+
  done

lemma modify_current_vcpu_None_states_equiv_valid[wp]:
  "states_equiv_valid aag L \<top> (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := None\<rparr>\<rparr>))"
  apply (wpsimp wp: modify_ev)
  apply (clarsimp simp: states_equiv_for_def equiv_for_def)
  apply (intro conjI)
    apply (auto simp: equiv_asids_def equiv_asid_def)[1]
   apply (clarsimp simp: equiv_hyp_def equiv_for_def cur_vcpu_of_def split: option.split)
  apply (auto simp: equiv_fpu_def equiv_for_def cur_fpu_for_def get_tcb_def)
  done

lemma disable_current_vcpu_weak_reads_respects_scheduler:
  "weak_reads_respects_scheduler aag l \<top> (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := None\<rparr>\<rparr>))"
  apply (rule equiv_valid_guard_imp)
   apply (rule weak_reads_respects_scheduler_from_labels)
  by (wpsimp wp: domain_fields_equiv_lift simp: globals_equiv_scheduler_def arch_globals_equiv_scheduler_def)+

lemma vcpu_disable_None_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   vcpu_disable None \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_disable_def
  apply (clarsimp simp: dmo_distr)
  apply wpsimp
  done

lemma modify_current_vcpu_equiv_but_for_labels'':
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := None\<rparr>\<rparr>)
   \<lbrace>\<lambda>_ s. equiv_but_for_labels aag L st s\<rbrace>"
  apply wp
  apply (clarsimp simp: cur_vcpu_for_def equiv_but_for_labels_def states_equiv_for_def equiv_for_def)
  apply (intro conjI)
    apply (clarsimp simp: equiv_asids_def equiv_asid_def)
   defer
   apply (clarsimp simp: equiv_fpu_def equiv_for_def cur_fpu_for_def get_tcb_def)
  apply (clarsimp simp: equiv_hyp_def equiv_for_def)
  apply (intro context_conjI; clarsimp)
  apply (erule_tac x=x in allE)+
  apply clarsimp
  apply (case_tac "\<exists>b. current_vcpu s = Some (x, b)")
   apply clarsimp
  apply (fastforce simp: cur_vcpu_of_def split: option.splits if_splits)
  done

lemma vcpu_invalidate_active_unobservable:
  assumes wellformed: "pas_wellformed_noninterference aag"
  notes domains_distinct = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
    "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
      scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and
      invs and cur_vcpu_in_cur_domain and valid_silc_label aag and pas_refined aag\<rbrace>
     vcpu_invalidate_active
     \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (simp add: vcpu_invalidate_active_def)
  apply (unfold scheduler_affects_equiv_def2[OF domains_distinct])
  supply modify_wp[wp del]
  apply (wp states_equiv_but_for_labels_equiv_for_lift modify_current_vcpu_equiv_but_for_labels'' | wpc)+
    apply clarsimp
    apply (clarsimp simp: cur_vcpu_for_def del: notI)
    apply (prop_tac "cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<in> reads_scheduler aag l) s = None")
     apply assumption
    apply (clarsimp simp: cur_vcpu_for_def)
   prefer 2
   apply (rule conjI)
    defer 2
    apply clarsimp
    apply (case_tac "current_vcpu s")
     apply (clarsimp simp: cur_vcpu_for_def split: option.splits)
    apply (clarsimp simp: cur_vcpu_for_def del: notI)
    apply (rule vcpu_invisible[OF _ wellformed])
         apply simp+
   apply (simp add: scheduler_affects_inv_def arch_scheduler_affects_equiv_def)
   apply (wpsimp wp: modify_wp hoare_vcg_imp_lift)
  apply clarsimp
  done

lemma vcpu_invalidate_active_weak_scheduler_reads_respects:
  assumes wellformed[wp,simp]: "pas_wellformed_noninterference aag"
  notes domains_distinct = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
  "weak_reads_respects_scheduler aag l
     (invs and ct_in_cur_domain and valid_cur_vcpu and pas_refined aag
           and cur_vcpu_in_cur_domain and valid_silc_label aag)
     vcpu_invalidate_active"
  apply (rule equiv_valid_cases[where P="\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l \<noteq> {}"])
    prefer 3
    apply (simp add: scheduler_equiv_def domain_fields_equiv_def)
   prefer 2
   defer
   apply (unfold vcpu_invalidate_active_def)[1]
   apply (rule equiv_valid_guard_imp)
    apply (wpc | wp disable_current_vcpu_weak_reads_respects_scheduler
                    vcpu_disable_None_weak_reads_respects_scheduler
                    gets_current_vcpu_weak_reads_respects_scheduler)+
   apply clarsimp
  apply (rule equiv_valid_guard_imp)
   apply (rule_tac weak_cur_domain_unobservable)
   apply (rule reads_respects_scheduler_unobservable'')
     apply (rule wp_pre)
      apply (rule scheduler_equiv_lift' [OF globals_equiv_scheduler_inv'])
           apply (wpsimp | erule conjunct1)+
    apply (rule wp_pre)
     apply (wp vcpu_invalidate_active_unobservable)
    apply clarsimp
    apply (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def domain_fields_equiv_def)
    apply assumption
   apply clarsimp
   apply assumption
  apply clarsimp
  apply auto
  done

lemma gets_arm_current_vcpu_states_equiv_valid:
  "states_equiv_valid aag L (\<lambda>s. cur_vcpu_for (L o pasObjectAbs aag) s \<noteq> None)
                        (gets (arm_current_vcpu \<circ> arch_state))"
  apply (wp gets_ev'')
   prefer 2
   apply assumption
  apply clarsimp
  apply (clarsimp simp: states_equiv_for_def equiv_hyp_def equiv_for_def)
  apply (fastforce simp: equiv_hyp_def equiv_for_def cur_vcpu_of_def split: if_splits option.splits)
  done

lemma vcpu_save_weak_reads_respects_scheduler:
  "weak_reads_respects_scheduler aag l
     (\<lambda>s. current_vcpu s = cv \<and> valid_arch_state s \<and> valid_silc_label aag s) (vcpu_save cv)"
  apply (rule equiv_valid_guard_imp)
   apply (rule weak_reads_respects_scheduler_from_labels)
         apply (rule vcpu_save_states_equiv_valid)
        apply (wpsimp wp: domain_fields_equiv_lift globals_equiv_scheduler_inv' vcpu_save_silc_dom_equiv | erule conjunct1)+
  apply (clarsimp simp: valid_arch_state_def)
  done

crunch vcpu_save
  for pas_refined[wp]: "pas_refined aag"
  (simp: pas_refined_def state_objs_to_policy_def ignore: vcpu_save)

crunch vcpu_save
  for cur_vcpu_in_cur_domain[wp]: cur_vcpu_in_cur_domain
  (wp: cur_vcpu_in_cur_domain_lift)

lemma vcpu_invalidate_active_unobservable':
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "\<lbrace>\<lambda>s. \<not> reads_scheduler_cur_domain aag l s \<and>
           scheduler_affects_equiv aag l st s \<and>
           cur_domain st = cur_domain s \<and>
           cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<in> reads_scheduler aag l) s = None\<rbrace>
     vcpu_invalidate_active
     \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (simp add: vcpu_invalidate_active_def)
  apply (unfold scheduler_affects_equiv_def2[OF domains_distinct])
  supply modify_wp[wp del]
  apply (wp states_equiv_but_for_labels_equiv_for_lift modify_current_vcpu_equiv_but_for_labels'' | wpc)+
    apply clarsimp
    apply (clarsimp simp: cur_vcpu_for_def del: notI)
    apply (prop_tac "cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<in> reads_scheduler aag l) s = None")
     apply assumption
    apply (clarsimp simp: cur_vcpu_for_def)
   prefer 2
   apply (rule conjI)
    defer 2
    apply clarsimp
   apply (simp add: scheduler_affects_inv_def arch_scheduler_affects_equiv_def)
   apply (wpsimp wp: modify_wp hoare_vcg_imp_lift)
  apply clarsimp
  done

lemma vcpu_save_unobservable:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "\<lbrace>\<lambda>s. \<not> reads_scheduler_cur_domain aag l s \<and>
           scheduler_affects_equiv aag l st s \<and>
           cur_domain st = cur_domain s \<and>
          current_vcpu s = vopt \<and>
          (\<exists>vr b. vopt = Some (vr,b) \<and> pasObjectAbs aag vr \<notin> reads_scheduler aag l)
          \<rbrace>
     vcpu_save vopt
     \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (unfold scheduler_affects_equiv_def2[OF domains_distinct])
  supply modify_wp[wp del]
  apply (wp states_equiv_but_for_labels_equiv_for_lift modify_current_vcpu_equiv_but_for_labels'' | wpc)+
   apply (simp add: scheduler_affects_inv_def arch_scheduler_affects_equiv_def)
   apply (wpsimp wp: modify_wp hoare_vcg_imp_lift)
  apply clarsimp
  done

lemma vcpu_flush_unobservable:
  assumes wellformed: "pas_wellformed_noninterference aag"
  notes domains_distinct[wp] = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
    "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
      scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and
      invs and cur_vcpu_in_cur_domain and valid_silc_label aag and pas_refined aag\<rbrace>
      vcpu_flush
      \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  unfolding vcpu_flush_def
  apply (wpsimp wp: vcpu_invalidate_active_unobservable' vcpu_save_unobservable)
  apply (rule context_conjI)
   prefer 2
   apply (clarsimp simp: cur_vcpu_for_Some)
  using wellformed apply (clarsimp simp: vcpu_invisible)
  done

lemma vcpu_flush_weak_scheduler_reads_respects:
  assumes wellformed[wp,simp]: "pas_wellformed_noninterference aag"
  notes domains_distinct = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
    "weak_reads_respects_scheduler aag l
       (pas_refined aag and valid_silc_label aag and invs and ct_in_cur_domain
                        and valid_cur_vcpu and cur_vcpu_in_cur_domain)
       vcpu_flush"
  apply (rule equiv_valid_cases[where P="\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l \<noteq> {}"])
    prefer 3
    apply (simp add: scheduler_equiv_def domain_fields_equiv_def)
   apply (simp add: vcpu_flush_def)
   apply wp
      apply (wpsimp wp: ct_in_cur_domain_lift when_ev valid_silc_label_lift
                        vcpu_invalidate_active_weak_scheduler_reads_respects
                        vcpu_save_weak_reads_respects_scheduler
                        gets_current_vcpu_weak_reads_respects_scheduler)
     apply (wp gets_current_vcpu_weak_reads_respects_scheduler)
    apply wp
   apply clarsimp
  apply (rule equiv_valid_guard_imp)
   apply (rule_tac weak_cur_domain_unobservable)
   apply (rule reads_respects_scheduler_unobservable'')
     apply (rule wp_pre)
      apply (rule scheduler_equiv_lift' [OF globals_equiv_scheduler_inv'])
           apply (wpsimp | erule conjunct1)+
    apply (rule wp_pre)
     apply (wp vcpu_flush_unobservable)
    apply clarsimp
    apply (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def domain_fields_equiv_def)
    apply assumption
   apply clarsimp
   apply assumption
  apply clarsimp
  apply auto
  done

lemma switch_local_fpu_owner_globals_equiv_scheduler[wp]:
  "\<lbrace>invs and globals_equiv_scheduler s\<rbrace> switch_local_fpu_owner vr \<lbrace>\<lambda>_. globals_equiv_scheduler s\<rbrace>"
  by (wp globals_equiv_scheduler_inv' switch_local_fpu_owner_globals_equiv | fastforce)+

lemma vcpu_flush_globals_equiv_scheduler[wp]:
  "\<lbrace>valid_arch_state and globals_equiv_scheduler s\<rbrace> vcpu_flush \<lbrace>\<lambda>_. globals_equiv_scheduler s\<rbrace>"
  by (wp globals_equiv_scheduler_inv' vcpu_flush_globals_equiv | fastforce)+

lemma arch_prepare_next_domain_globals_equiv_scheduler[Scheduler_IF_assms]:
  "\<lbrace>invs and globals_equiv_scheduler st\<rbrace> arch_prepare_next_domain \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  unfolding arch_prepare_next_domain_def
  by wpsimp

lemma vcpu_invalidate_active_states_equiv_valid:
  "states_equiv_valid aag L (\<lambda>s. cur_vcpu_for (L o pasObjectAbs aag) s \<noteq> None) vcpu_invalidate_active"
  unfolding vcpu_invalidate_active_def
  by (wpsimp wp: vcpu_disable_None_states_equiv_valid gets_arm_current_vcpu_states_equiv_valid)

lemma vcpu_invalidate_active_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> (\<forall>vr b. current_vcpu s = Some (vr,b) \<longrightarrow> pasObjectAbs aag vr \<in> L)\<rbrace>
   vcpu_invalidate_active
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_invalidate_active_def
  by (wpsimp wp: modify_current_vcpu_equiv_but_for_labels'')
     (auto simp: cur_vcpu_for_def)

lemma vcpu_flush_states_equiv_valid[wp]:
  "states_equiv_valid aag L (valid_numlistregs) vcpu_flush"
  unfolding vcpu_flush_def
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (L o pasObjectAbs aag) s \<noteq> None" in equiv_valid_cases)
    prefer 3
    apply (prop_tac "equiv_for (L o pasObjectAbs aag) cur_vcpu_of s t")
     apply (clarsimp simp: states_equiv_for_def equiv_for_def equiv_hyp_def)
    apply (rule iffI; clarsimp simp: equiv_for_def)
     apply (erule_tac x=ptr in allE, clarsimp simp: cur_vcpu_of_def split: option.splits if_splits)
    apply (erule_tac x=ptr in allE, clarsimp simp: cur_vcpu_of_def split: option.splits if_splits)
   apply wp
      apply (wpsimp wp: when_ev vcpu_invalidate_active_states_equiv_valid)
     apply (rule gets_arm_current_vcpu_states_equiv_valid)
    apply wpsimp
   apply clarsimp
  apply (subst pred_conj_comm)
  apply (rule states_equiv_valid_invisible[OF modifies_at_mostI])
    apply wpsimp
   apply wpsimp
  apply clarsimp
  done

lemma invs_valid_numlistregs [elim!]:
  "invs s \<Longrightarrow> valid_numlistregs s"
  by (drule invs_arch_state)
     (simp add: valid_arch_state_def)

lemma arch_prepare_next_domain_states_equiv_valid:
  "states_equiv_valid aag L invs arch_prepare_next_domain"
  unfolding arch_prepare_next_domain_def
  by wpsimp fastforce

crunch arch_prepare_next_domain
  for domain_time[wp]: "\<lambda>s. P (domain_time s)"
  and domain_index[wp]: "\<lambda>s. P (domain_index s)"
  (simp : crunch_simps wp: crunch_wps)

crunch arch_prepare_next_domain
  for globals_equiv[wp]: "globals_equiv st"
  (wp: valid_silc_label_lift)

lemma arch_prepare_next_domain_weak_scheduler_reads_respects[Scheduler_IF_assms]:
  "weak_reads_respects_scheduler aag l (invs and valid_silc_label aag) arch_prepare_next_domain"
  apply (rule equiv_valid_guard_imp)
   apply (rule_tac Q="invs and valid_silc_label aag" in weak_reads_respects_scheduler_from_labels)
         apply (rule arch_prepare_next_domain_states_equiv_valid)
        apply (wpsimp wp: domain_fields_equiv_lift  globals_equiv_scheduler_inv'[where P="invs"])+
  done

lemma gets_cur_fpu_of_states_equiv_valid:
  "states_equiv_valid aag L (valid_cur_fpu and K (L (pasObjectAbs aag t))) (gets (\<lambda>s. cur_fpu_of s t))"
  apply (wpsimp wp: gets_ev'')
   prefer 2
   apply (rule conjI)
    apply assumption+
  apply (prop_tac "equiv_fpu (\<lambda>x. L (pasObjectAbs aag x)) x xa")
   apply (clarsimp simp: states_equiv_for_def)
  apply (clarsimp simp: equiv_fpu_def2)
  done

lemma thread_get_states_equiv_valid:
  "states_equiv_valid aag L (K (L (pasObjectAbs aag thread))) (thread_get f thread)"
  unfolding thread_get_def fun_app_def
  apply (wp gets_the_ev)
  apply (auto simp: states_equiv_for_def equiv_for_def get_tcb_def)
  done

lemma lazy_fpu_restore_states_equiv_valid[wp]:
  "states_equiv_valid aag L (valid_cur_fpu and K (L (pasObjectAbs aag t))) (lazy_fpu_restore t)"
  unfolding lazy_fpu_restore_def
  apply (subst gets_comp)
  apply (unfold comp_def)
  apply (wpsimp wp: gets_cur_fpu_of_states_equiv_valid thread_get_states_equiv_valid thread_get_wp')
  done

lemma set_vm_root_states_equiv_valid[wp]:
  "states_equiv_valid aag L \<top> (set_vm_root t)"
  apply (rule states_equiv_valid_unobservable_unit_return)
  apply (wp set_vm_root_states_equiv_for)
  done

lemma arch_switch_to_thread_states_equiv_valid:
  "states_equiv_valid aag L (invs and  K (L (pasObjectAbs aag t))) (arch_switch_to_thread t)"
  unfolding arch_switch_to_thread_def
  apply (wpsimp wp: vcpu_switch_states_equiv_valid)
  apply (auto simp: states_equiv_for_def get_tcb_def equiv_for_def)
  done

lemma midstrength_reads_respects_scheduler_from_labels':
  assumes ev: "\<And>L. states_equiv_valid aag L (P (L o pasObjectAbs aag)) f"
    and inv: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (irq_state_of_state s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (work_units_completed s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
             "\<And>st. \<lbrace>\<lambda>s. domain_fields_equiv st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. domain_fields_equiv st s\<rbrace>"
             "\<And>st. \<lbrace>\<lambda>s. globals_equiv_scheduler st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. globals_equiv_scheduler st s\<rbrace>"
             "\<And>st. \<lbrace>\<lambda>s. silc_dom_equiv aag st s \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. silc_dom_equiv aag st s\<rbrace>"
  shows "equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
                         (P (\<lambda>x. pasObjectAbs aag x \<in> reads_scheduler aag l) and Q) f"
  apply (rule equiv_valid_inv_split_lr)
   apply (rule equiv_valid_rv_inv_lift)
  unfolding scheduler_equiv_def
     apply (wpsimp wp: inv)
    apply (auto simp: domain_fields_equiv_sym globals_equiv_scheduler_sym silc_dom_equiv_sym)[2]
  unfolding midstrength_scheduler_affects_equiv_def
  apply (rule equiv_valid_inv_A_conjI)
   apply (rule_tac equiv_valid_guard_imp)
    apply (insert ev)[1]
    apply fastforce
   apply (clarsimp simp: comp_def)
  apply (rule_tac Q=Q and Q'=Q in equiv_valid_2_guard_imp)
    apply (rule equiv_valid_rv_inv_lift)
      apply (wpsimp wp: inv hoare_vcg_imp_lift)+
    apply auto
  done

lemma lazy_fpu_restore_unobservable:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
    (\<lambda>s. pasObjectAbs aag t \<notin> reads_scheduler aag l) and
    scheduler_equiv aag st and scheduler_affects_equiv aag l st and
    invs and cur_fpu_in_cur_domain and valid_silc_label aag and pas_refined aag\<rbrace>
   lazy_fpu_restore t
   \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  by (wpsimp wp: set_vm_root_scheduler_affects_equiv
                 lazy_fpu_restore_scheduler_affects_equiv
                 vcpu_switch_scheduler_affects_equiv)

lemma midstrength_cur_domain_unobservable':
  "reads_respects_scheduler aag l (P and (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s)) f
   \<Longrightarrow> equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
         ((\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and P) f"
  apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def scheduler_affects_equiv_def
                        equiv_valid_def2 equiv_valid_2_def  midstrength_scheduler_affects_equiv_def)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply clarsimp
  apply (drule_tac x="(a,b)" in bspec,clarsimp+)
  apply (drule_tac x="(aa,ba)" in bspec,clarsimp+)
  done

lemma lazy_fpu_restore_midstrength_scheduler_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
                   ((\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)) and invs and
                    pas_refined aag and valid_silc_label aag and cur_fpu_in_cur_domain)
                   (lazy_fpu_restore t)"
  apply (rule_tac P="reads_scheduler_cur_domain aag l" in equiv_valid_cases)
    apply (rule equiv_valid_guard_imp)
     apply (rule_tac Q="invs and valid_silc_label aag" in midstrength_reads_respects_scheduler_from_labels')
            apply (rule equiv_valid_guard_imp)
             apply (rule lazy_fpu_restore_states_equiv_valid)
            apply (clarsimp simp: comp_def)
            apply assumption
           apply (wpsimp wp: domain_fields_equiv_lift lazy_fpu_restore_globals_equiv globals_equiv_scheduler_inv' | erule conjunct1)+
    apply (rule conjI)
     apply clarsimp
    apply (insert domains_distinct)
    apply (clarsimp simp: pas_domains_distinct_def)
    apply (erule_tac x="cur_domain s" in allE, clarsimp)
   apply (rule midstrength_cur_domain_unobservable')
   apply (rule reads_respects_scheduler_unobservable'')
     apply (wp_pre)
      apply (rule_tac P="invs and valid_silc_label aag" in scheduler_equiv_lift')
           apply (wpsimp wp: arch_switch_to_thread_globals_equiv_scheduler
                             lazy_fpu_restore_globals_equiv globals_equiv_scheduler_inv'
                  | erule conjunct1)+
    apply (wp lazy_fpu_restore_unobservable)
    apply clarsimp
    apply assumption
   apply clarsimp
   apply (rule conjI)
    apply simp
   apply (clarsimp simp: pas_domains_distinct_def)
   apply (erule_tac x="cur_domain s" in allE, clarsimp)
  apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)
  done

lemma arch_switch_to_thread_midstrength_reads_respects_scheduler':
  assumes wellformed[wp]: "pas_wellformed_noninterference aag"
  notes domains_distinct[wp] = pas_wellformed_noninterference_domains_distinct[OF wellformed]
  shows
    "equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
       ((\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)) and invs and pas_refined aag and
        valid_silc_label aag and cur_vcpu_in_cur_domain and cur_fpu_in_cur_domain)
       (arch_switch_to_thread t)"
  apply (rule_tac P="reads_scheduler_cur_domain aag l" in equiv_valid_cases)
    apply (rule equiv_valid_guard_imp)
     apply (rule_tac Q="invs and valid_silc_label aag" in midstrength_reads_respects_scheduler_from_labels')
            apply (rule equiv_valid_guard_imp)
             apply (rule arch_switch_to_thread_states_equiv_valid)
            apply (clarsimp simp: comp_def)
            apply assumption
           apply (wpsimp wp: domain_fields_equiv_lift arch_switch_to_thread_globals_equiv_scheduler)+
    apply (insert domains_distinct)
    apply (clarsimp simp: pas_domains_distinct_def)
    apply (erule_tac x="cur_domain s" in allE, clarsimp)
   prefer 2
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)
  apply (rule midstrength_cur_domain_unobservable')
  apply (rule reads_respects_scheduler_unobservable'')
    apply (wp_pre)
     apply (rule_tac P="invs and valid_silc_label aag" in scheduler_equiv_lift')
          apply (wpsimp wp: arch_switch_to_thread_globals_equiv_scheduler globals_equiv_scheduler_inv'
                 | erule conjunct1)+
   apply (wp arch_switch_to_thread_unobservable)
   apply clarsimp
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)
   apply assumption
  apply clarsimp
  apply (rule conjI, simp)
  apply (clarsimp simp: pas_domains_distinct_def)
  apply (erule_tac x="cur_domain s" in allE, clarsimp)
  done

lemma arch_switch_to_thread_midstrength_reads_respects_scheduler[Scheduler_IF_assms, wp]:
  assumes wellformed[wp]: "pas_wellformed_noninterference aag"
  notes domains_distinct[wp] = pas_wellformed_noninterference_domains_distinct[OF wellformed]
    shows "midstrength_reads_respects_scheduler aag l
           (invs and pas_refined aag and valid_silc_label aag
                 and cur_vcpu_in_cur_domain and cur_fpu_in_cur_domain
                 and (\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)))
           (do _ <- arch_switch_to_thread t;
               _ <- modify (cur_thread_update (\<lambda>_. t));
               modify (scheduler_action_update (\<lambda>_. resume_cur_thread))
            od)"
  apply (rule equiv_valid_guard_imp)
   apply (rule bind_ev_general)
     apply (fold set_scheduler_action_def)
     apply (rule store_cur_thread_fragment_midstrength_reads_respects)
    apply (rule arch_switch_to_thread_midstrength_reads_respects_scheduler')
    apply wpsimp+
  done

definition cur_hyp_in_cur_domain where
  "cur_hyp_in_cur_domain \<equiv> cur_vcpu_in_cur_domain"

end

arch_requalify_consts cur_hyp_in_cur_domain cur_fpu_in_cur_domain


global_interpretation Scheduler_IF_2?:
  Scheduler_IF_2 arch_globals_equiv_scheduler arch_scheduler_affects_equiv _ cur_hyp_in_cur_domain cur_fpu_in_cur_domain
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Scheduler_IF_assms[folded cur_hyp_in_cur_domain_def])?)
qed


hide_fact Scheduler_IF_2.globals_equiv_scheduler_inv'
arch_requalify_facts globals_equiv_scheduler_inv'

end
