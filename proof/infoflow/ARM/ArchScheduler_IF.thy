(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchScheduler_IF
imports Scheduler_IF

begin

context Arch begin global_naming ARM

named_theorems Scheduler_IF_assms

definition arch_globals_equiv_scheduler :: "kheap \<Rightarrow> kheap \<Rightarrow> arch_state \<Rightarrow> arch_state \<Rightarrow> bool" where
  "arch_globals_equiv_scheduler kh kh' as as' \<equiv>
     arm_global_pd as = arm_global_pd as' \<and> kh (arm_global_pd as) = kh' (arm_global_pd as)"

definition
  "arch_scheduler_affects_equiv s s' \<equiv> exclusive_state_equiv s s'"

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

crunches arch_switch_to_thread, arch_switch_to_idle_thread
  for idle_thread[Scheduler_IF_assms, wp]: "\<lambda>s :: det_state. P (idle_thread s)"
  and kheap[Scheduler_IF_assms, wp]: "\<lambda>s :: det_state. P (kheap s)"
  (wp: crunch_wps simp: crunch_simps)

crunches arch_switch_to_idle_thread
  for cur_domain[Scheduler_IF_assms, wp]: "\<lambda>s. P (cur_domain s)"
  and domain_fields[Scheduler_IF_assms, wp]: "domain_fields P"

crunches arch_switch_to_idle_thread
  for globals_equiv[Scheduler_IF_assms, wp]: "globals_equiv st"
  and states_equiv_for[Scheduler_IF_assms, wp]: "states_equiv_for P Q R S st"
  and work_units_completed[Scheduler_IF_assms, wp]: "\<lambda>s. P (work_units_completed s)"

crunches arch_activate_idle_thread
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

lemma equiv_asid_ekheap_update[Scheduler_IF_assms, simp]:
  "equiv_asid asid (ekheap_update f s) s' = equiv_asid asid s s'"
  "equiv_asid asid s (ekheap_update f s') = equiv_asid asid s s'"
  by (auto simp: equiv_asid_def)

lemma arch_scheduler_affects_equiv_domain_time_update[Scheduler_IF_assms, simp]:
  "arch_scheduler_affects_equiv (domain_time_update f s) s' = arch_scheduler_affects_equiv s s'"
  "arch_scheduler_affects_equiv s (domain_time_update f s') = arch_scheduler_affects_equiv s s'"
  by (auto simp: arch_scheduler_affects_equiv_def)

lemma arch_scheduler_affects_equiv_ekheap_update[Scheduler_IF_assms, simp]:
  "arch_scheduler_affects_equiv (ekheap_update f s) s' = arch_scheduler_affects_equiv s s'"
  "arch_scheduler_affects_equiv s (ekheap_update f s') = arch_scheduler_affects_equiv s s'"
  by (auto simp: arch_scheduler_affects_equiv_def)

crunch irq_state[Scheduler_IF_assms, wp]: ackInterrupt "\<lambda>s. P (irq_state s)"

lemma thread_set_context_globals_equiv[Scheduler_IF_assms]:
  "\<lbrace>(\<lambda>s. t = idle_thread s \<longrightarrow> tc = idle_context s) and invs and globals_equiv st\<rbrace>
   thread_set (tcb_arch_update (arch_tcb_context_set tc)) t
   \<lbrace>\<lambda>rv. globals_equiv st\<rbrace>"
  apply (clarsimp simp: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (subgoal_tac "t \<noteq> arm_global_pd (arch_state s)")
   apply (clarsimp simp: idle_equiv_def globals_equiv_def tcb_at_def2 get_tcb_def idle_context_def)
   apply (clarsimp split: option.splits kernel_object.splits)
  apply (drule arm_global_pd_not_tcb[OF invs_arch_state])
  apply clarsimp
  done

lemma arch_scheduler_affects_equiv_update[Scheduler_IF_assms]:
  "arch_scheduler_affects_equiv st s
   \<Longrightarrow> arch_scheduler_affects_equiv st (s\<lparr>kheap := (kheap s)(x \<mapsto> TCB y')\<rparr>)"
  by (clarsimp simp: arch_scheduler_affects_equiv_def)

lemma equiv_asid_equiv_update[Scheduler_IF_assms]:
  "\<lbrakk> get_tcb x s = Some y; equiv_asid asid st s \<rbrakk>
     \<Longrightarrow> equiv_asid asid st (s\<lparr>kheap := (kheap s)(x \<mapsto> TCB y')\<rparr>)"
  by (clarsimp simp: equiv_asid_def obj_at_def get_tcb_def)

end

context begin interpretation Arch .

requalify_consts
  arch_globals_equiv_scheduler
  arch_scheduler_affects_equiv

end


global_interpretation Scheduler_IF_1?:
  Scheduler_IF_1 arch_globals_equiv_scheduler arch_scheduler_affects_equiv
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Scheduler_IF_assms)?)
qed


context Arch begin global_naming ARM

definition swap_things where
  "swap_things s t \<equiv>
     t\<lparr>machine_state := underlying_memory_update
                          (\<lambda>m a. if a \<in> scheduler_affects_globals_frame t
                                 then underlying_memory (machine_state s) a
                                 else m a)
                          (machine_state t)\<lparr>exclusive_state := exclusive_state (machine_state s)\<rparr>\<rparr>
      \<lparr>cur_thread := cur_thread s\<rparr>"

lemma globals_equiv_scheduler_inv'[Scheduler_IF_assms]:
  "(\<And>st. \<lbrace>P and globals_equiv st\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>)
   \<Longrightarrow> \<lbrace>P and globals_equiv_scheduler s\<rbrace> f \<lbrace>\<lambda>_. globals_equiv_scheduler s\<rbrace>"
  apply atomize
  apply (rule use_spec)
  apply (simp add: spec_valid_def)
  apply (erule_tac x="(swap_things sa s)" in allE)
  apply (rule_tac Q="\<lambda>r st. globals_equiv (swap_things sa s) st" in hoare_strengthen_post)
   apply (rule hoare_pre)
    apply assumption
   apply (clarsimp simp: globals_equiv_def swap_things_def globals_equiv_scheduler_def
                         arch_globals_equiv_scheduler_def arch_scheduler_affects_equiv_def)+
  done

lemma clearExMonitor_globals_equiv_scheduler[wp]:
  "do_machine_op clearExMonitor \<lbrace>globals_equiv_scheduler sta\<rbrace>"
  unfolding clearExMonitor_def including no_pre
  apply (wp dmo_no_mem_globals_equiv_scheduler)
   apply simp
  apply (simp add: simpler_modify_def valid_def)
  done

lemma arch_switch_to_thread_globals_equiv_scheduler[Scheduler_IF_assms]:
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace>
   arch_switch_to_thread thread
   \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  unfolding arch_switch_to_thread_def storeWord_def
  by (wpsimp wp: clearExMonitor_globals_equiv_scheduler dmo_wp modify_wp thread_get_wp'
      | wp (once) globals_equiv_scheduler_inv'[where P="\<top>"])+

crunches arch_activate_idle_thread
  for silc_dom_equiv[Scheduler_IF_assms, wp]: "silc_dom_equiv aag st"
  and scheduler_affects_equiv[Scheduler_IF_assms, wp]: "scheduler_affects_equiv aag l st"

lemma dmo_mol_exclusive_state[wp]:
  "do_machine_op (machine_op_lift mop) \<lbrace>\<lambda>s. P (exclusive_state (machine_state s))\<rbrace>"
  by (wp mol_exclusive_state dmo_wp
      | simp add: split_def dmo_bind_valid writeTTBR0_def isb_def dsb_def)+

crunch exclusive_state[wp]: set_vm_root "\<lambda>s. P (exclusive_state (machine_state s))"
  (ignore: do_machine_op
     simp: invalidateLocalTLB_ASID_def setHardwareASID_def set_current_pd_def dsb_def isb_def
           writeTTBR0_def dmo_bind_valid crunch_simps)

lemma set_vm_root_arch_scheduler_affects_equiv[wp]:
  "set_vm_root tcb \<lbrace>arch_scheduler_affects_equiv st\<rbrace>"
  unfolding arch_scheduler_affects_equiv_def by wpsimp

lemmas set_vm_root_scheduler_affects_equiv[wp] =
  scheduler_affects_equiv_unobservable[OF set_vm_root_states_equiv_for
                                          set_vm_root_exst _ _ _ set_vm_root_it
                                          set_vm_root_arch_scheduler_affects_equiv]

lemma set_vm_root_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l \<top> (set_vm_root thread)"
  apply (rule reads_respects_scheduler_unobservable'[OF scheduler_equiv_lift'
                                                          [OF globals_equiv_scheduler_inv']])
  apply (wp silc_dom_equiv_states_equiv_lift set_vm_root_states_equiv_for | simp)+
  done

lemma ev_asahi_to_asahi_ex_dmo_clearExMonitor:
  "equiv_valid (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
               (asahi_ex_scheduler_affects_equiv aag l) \<top> (do_machine_op clearExMonitor)"
  apply (simp add: clearExMonitor_def)
  apply (wp dmo_ev)
  apply (rule ev_modify)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def
                         silc_dom_equiv_def equiv_for_def)
  apply (clarsimp simp: midstrength_scheduler_affects_equiv_def asahi_scheduler_affects_equiv_def
                        asahi_ex_scheduler_affects_equiv_def states_equiv_for_def equiv_for_def
                        arch_scheduler_affects_equiv_def equiv_asids_def equiv_asid_def
                        scheduler_globals_frame_equiv_def
              simp del: split_paired_All)
  done

lemma store_cur_thread_fragment_midstrength_reads_respects:
  "equiv_valid (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
               (scheduler_affects_equiv aag l) invs
               (do y \<leftarrow> do_machine_op clearExMonitor;
                   x \<leftarrow> modify (cur_thread_update (\<lambda>_. t));
                   set_scheduler_action resume_cur_thread
                od)"
  apply (rule equiv_valid_guard_imp)
   apply (rule bind_ev_general[OF ev_asahi_ex_to_full_fragement])
    apply (rule ev_asahi_to_asahi_ex_dmo_clearExMonitor)
   apply wp
  apply simp
  done

lemma arch_switch_to_thread_globals_equiv_scheduler':
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace>
   set_vm_root t
   \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  by (rule globals_equiv_scheduler_inv', wpsimp)

lemma reads_respects_scheduler_clearExMonitor[wp]:
  "reads_respects_scheduler aag l \<top> (do_machine_op clearExMonitor)"
  apply (simp add: clearExMonitor_def)
  apply (wp dmo_ev)
  apply (rule ev_modify)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def
                         silc_dom_equiv_def equiv_for_def)
  apply (clarsimp simp: scheduler_affects_equiv_def arch_scheduler_affects_equiv_def
                        states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def
                        scheduler_globals_frame_equiv_def
              simp del: split_paired_All)
  done

lemma arch_switch_to_thread_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l
     ((\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)) and invs)
     (arch_switch_to_thread t)"
  apply (rule reads_respects_scheduler_cases)
     apply (simp add: arch_switch_to_thread_def)
     apply wp
    apply (clarsimp simp: scheduler_equiv_def globals_equiv_scheduler_def)
   apply (simp add: arch_switch_to_thread_def)
   apply wp
  apply simp
  done

lemmas globals_equiv_scheduler_inv = globals_equiv_scheduler_inv'[where P="\<top>",simplified]

lemma arch_switch_to_thread_midstrength_reads_respects_scheduler[Scheduler_IF_assms, wp]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "midstrength_reads_respects_scheduler aag l
           (invs and pas_refined aag and (\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)))
           (do _ <- arch_switch_to_thread t;
               _ <- modify (cur_thread_update (\<lambda>_. t));
               modify (scheduler_action_update (\<lambda>_. resume_cur_thread))
            od)"
  apply (rule equiv_valid_guard_imp)
   apply (rule midstrength_reads_respects_scheduler_cases[
                    where Q="(invs and pas_refined aag and
                                  (\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)))",
                    OF domains_distinct])
       apply (simp add: arch_switch_to_thread_def bind_assoc)
       apply (rule bind_ev_general)
         apply (fold set_scheduler_action_def)
         apply (rule store_cur_thread_fragment_midstrength_reads_respects)
        apply (rule_tac P="\<top>" and P'="\<top>" in equiv_valid_inv_unobservable)
            apply (rule hoare_pre)
             apply (rule scheduler_equiv_lift'[where P=\<top>])
                  apply (wp globals_equiv_scheduler_inv silc_dom_lift | simp)+
           apply (wp midstrength_scheduler_affects_equiv_unobservable set_vm_root_states_equiv_for
                  | simp)+
          apply (wp cur_thread_update_not_subject_reads_respects_scheduler | simp | fastforce)+
  done

lemma arch_switch_to_idle_thread_globals_equiv_scheduler[Scheduler_IF_assms, wp]:
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  unfolding arch_switch_to_idle_thread_def storeWord_def
  by (wp dmo_wp modify_wp thread_get_wp' arch_switch_to_thread_globals_equiv_scheduler')

lemma arch_switch_to_idle_thread_unobservable[Scheduler_IF_assms]:
  "\<lbrace>(\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l = {}) and
    scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and invs\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply wp
  apply (clarsimp simp add: scheduler_equiv_def domain_fields_equiv_def invs_def valid_state_def)
  done

lemma clearExMonitor_unobservable:
  "\<lbrace>(\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l = {}) and
    scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain s = cur_domain st)\<rbrace>
   do_machine_op clearExMonitor
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: clearExMonitor_def)
  apply (rule hoare_pre)
   apply (wp dmo_wp modify_wp)
  apply (auto simp: states_equiv_for_def scheduler_affects_equiv_def equiv_for_def equiv_asids_def
                    equiv_asid_def scheduler_globals_frame_equiv_def silc_dom_equiv_def)
  done

lemma arch_switch_to_thread_unobservable[Scheduler_IF_assms]:
  "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
    scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and invs\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_ s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (wp set_vm_root_scheduler_affects_equiv clearExMonitor_unobservable | simp)+
  done

(* Can split, but probably more effort to generalise *)
lemma next_domain_midstrength_equiv_scheduler[Scheduler_IF_assms]:
  "equiv_valid (scheduler_equiv aag) (weak_scheduler_affects_equiv aag l)
               (midstrength_scheduler_affects_equiv aag l) \<top> next_domain"
  apply (simp add: next_domain_def)
  apply (rule ev_modify)
  apply (clarsimp simp: equiv_for_def equiv_asid_def equiv_asids_def Let_def scheduler_equiv_def
                        globals_equiv_scheduler_def silc_dom_equiv_def domain_fields_equiv_def
                        weak_scheduler_affects_equiv_def midstrength_scheduler_affects_equiv_def
                        states_equiv_for_def idle_equiv_def)
  done

lemma resetTimer_exclusive_state[wp]:
  "resetTimer \<lbrace>\<lambda>s. P (exclusive_state s)\<rbrace>"
  by (wpsimp simp: resetTimer_def wp: mol_exclusive_state)

lemma resetTimer_irq_state[wp]:
  "resetTimer \<lbrace>\<lambda>s. P (irq_state s)\<rbrace>"
  apply (simp add: resetTimer_def machine_op_lift_def machine_rest_lift_def)
  apply (wp | wpc| simp)+
  done

lemma dmo_resetTimer_reads_respects_scheduler[Scheduler_IF_assms]:
  "reads_respects_scheduler aag l \<top> (do_machine_op resetTimer)"
  apply (rule reads_respects_scheduler_unobservable)
   apply (rule scheduler_equiv_lift)
        apply (simp add: globals_equiv_scheduler_def[abs_def]  idle_equiv_def)
        apply (wpsimp wp: dmo_wp)
       apply ((wp silc_dom_lift dmo_wp | simp)+)[5]
  apply (rule scheduler_affects_equiv_unobservable)
        apply (simp add: states_equiv_for_def[abs_def] equiv_for_def equiv_asids_def equiv_asid_def)
        apply (rule hoare_pre)
         apply (wp  | simp add: arch_scheduler_affects_equiv_def | wp dmo_wp)+
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
   apply (wp mol_exclusive_state)
  apply (simp add: arch_scheduler_affects_equiv_def)
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
  apply (clarsimp simp: idle_context_def get_tcb_def
                  split: option.splits kernel_object.splits)
  apply (subst arch_tcb_update_aux)
  apply simp
  apply (subgoal_tac "s = (s\<lparr>kheap := (kheap s)(idle_thread s \<mapsto> TCB y)\<rparr>)", simp)
  apply (rule state.equality)
            apply (rule ext)
            apply simp+
  done

lemma set_object_reads_respects_scheduler[Scheduler_IF_assms, wp]:
  "reads_respects_scheduler aag l \<top> (set_object ptr obj)"
  unfolding equiv_valid_def2 equiv_valid_2_def
  by (auto simp: set_object_def bind_def get_def put_def return_def get_object_def assert_def
                 fail_def gets_def scheduler_equiv_def domain_fields_equiv_def equiv_for_def
                 globals_equiv_scheduler_def arch_globals_equiv_scheduler_def silc_dom_equiv_def
                 scheduler_affects_equiv_def arch_scheduler_affects_equiv_def
                 scheduler_globals_frame_equiv_def identical_kheap_updates_def
          intro: states_equiv_for_identical_kheap_updates idle_equiv_identical_kheap_updates)

lemma arch_activate_idle_thread_reads_respects_scheduler[Scheduler_IF_assms, wp]:
  "reads_respects_scheduler aag l \<top> (arch_activate_idle_thread rv)"
  unfolding arch_activate_idle_thread_def by wpsimp

end


global_interpretation Scheduler_IF_2?:
  Scheduler_IF_2 arch_globals_equiv_scheduler arch_scheduler_affects_equiv
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Scheduler_IF_assms)?)
qed


hide_fact Scheduler_IF_2.globals_equiv_scheduler_inv'
requalify_facts ARM.globals_equiv_scheduler_inv'

end
