(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Scheduler_IF
imports    "Syscall_IF" "PasUpdates"

begin

context begin interpretation Arch . (*FIXME: arch_splits*)

crunch cur_thread: activate_thread "\<lambda>s. P (cur_thread s)"
crunch cur_thread: arch_switch_to_thread "\<lambda>s. P( cur_thread s)"

(* After SELFOUR-553 scheduler no longer writes to shared memory *)
abbreviation scheduler_affects_globals_frame where
 "scheduler_affects_globals_frame s \<equiv>  {}"

definition globals_equiv_scheduler :: "'z::state_ext state \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
"globals_equiv_scheduler s s' \<equiv> arm_global_pd (arch_state s) = arm_global_pd (arch_state s') \<and>
     kheap s (arm_global_pd (arch_state s)) = kheap s' (arm_global_pd (arch_state s))
     \<and> idle_equiv s s' \<and> device_region s = device_region s'"

definition scheduler_globals_frame_equiv :: "'z::state_ext state \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
"scheduler_globals_frame_equiv s s' \<equiv> (\<forall>x\<in>scheduler_affects_globals_frame s. underlying_memory (machine_state s) x = underlying_memory (machine_state s') x
  \<and> device_state (machine_state s) x = device_state (machine_state s') x)"

definition domain_fields_equiv :: "det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
where
"domain_fields_equiv s s' \<equiv> cur_domain s = cur_domain s' \<and>
                            domain_time s = domain_time s' \<and>
                            domain_index s = domain_index s' \<and>
                            domain_list s = domain_list s'"


definition scheduler_equiv :: "'a subject_label PAS  \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
where
"scheduler_equiv aag s s'  \<equiv>
    domain_fields_equiv s s' \<and> idle_thread s = idle_thread s' \<and> globals_equiv_scheduler s s' \<and> silc_dom_equiv aag s s' \<and> irq_state_of_state s = irq_state_of_state s'"

(* The equivalence relation for what the scheduler can affect.
   Since information can flow from the scheduler to any domain,
   we assert that the result states are equivalent with respect
   to any domain.

*)



definition reads_scheduler where
"reads_scheduler aag l \<equiv> if (l = SilcLabel) then {} else
                         subjectReads (pasPolicy aag) l"

abbreviation reads_scheduler_cur_domain where
  "reads_scheduler_cur_domain aag l s \<equiv>
     pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l \<noteq> {}"

definition scheduler_affects_equiv :: "'a subject_label PAS  \<Rightarrow> ('a subject_label) \<Rightarrow>
                                       det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
"scheduler_affects_equiv aag l s s' \<equiv>
  (states_equiv_for_labels aag (\<lambda>l'. l' \<in> reads_scheduler aag l) s s' \<and>
  (reads_scheduler_cur_domain aag l s \<or> reads_scheduler_cur_domain aag l s' \<longrightarrow>
     (cur_thread s = cur_thread s' \<and> scheduler_action s = scheduler_action s' \<and>
      work_units_completed s = work_units_completed s' \<and>
      scheduler_globals_frame_equiv s s' \<and>
      idle_thread s = idle_thread s' \<and>
      (cur_thread s \<noteq> idle_thread s' \<longrightarrow> exclusive_state_equiv s s'))))"

lemma ev_modify:
  "(\<And> s t. \<lbrakk>P s; P t; A s t; I s t\<rbrakk> \<Longrightarrow> (I (f s) (f t)) \<and> (B (f s) (f t)))
   \<Longrightarrow> equiv_valid I A B P (modify f)"
  apply (clarsimp simp add: equiv_valid_def2 equiv_valid_2_def simpler_modify_def)
  done

abbreviation reads_respects_scheduler
where
"reads_respects_scheduler aag l P f  \<equiv>
   equiv_valid_inv (scheduler_equiv aag) (scheduler_affects_equiv aag l) P f"

lemma globals_equiv_from_scheduler:
  "\<lbrakk> globals_equiv_scheduler s s'; scheduler_globals_frame_equiv s s'; cur_thread s = cur_thread s';
    cur_thread s \<noteq> idle_thread s \<longrightarrow> exclusive_state_equiv s s'\<rbrakk> \<Longrightarrow>
  globals_equiv s s'"
  by (clarsimp simp: globals_equiv_scheduler_def scheduler_globals_frame_equiv_def
                     globals_equiv_def)

lemma globals_equiv_scheduler_refl:
  "globals_equiv_scheduler s s"
  by (simp add: globals_equiv_scheduler_def idle_equiv_refl)

lemma globals_equiv_scheduler_sym:
  "globals_equiv_scheduler s s' \<Longrightarrow> globals_equiv_scheduler s' s"
  by (auto simp add: globals_equiv_scheduler_def idle_equiv_sym)

lemma globals_equiv_scheduler_trans:
  "globals_equiv_scheduler s s' \<Longrightarrow> globals_equiv_scheduler s' s'' \<Longrightarrow> globals_equiv_scheduler s s''"
  apply (clarsimp simp add: globals_equiv_scheduler_def)
  apply (rule idle_equiv_trans,assumption,assumption)
  done


lemma scheduler_globals_frame_equiv_refl:
  "scheduler_globals_frame_equiv s s"
  by (simp add: scheduler_globals_frame_equiv_def)

lemma scheduler_globals_frame_equiv_sym[elim]:
  "scheduler_globals_frame_equiv s s' \<Longrightarrow> scheduler_globals_frame_equiv s' s"
  by (simp add: scheduler_globals_frame_equiv_def)

lemma scheduler_globals_frame_equiv_trans[elim]:
  "scheduler_globals_frame_equiv s s' \<Longrightarrow> scheduler_globals_frame_equiv s' s''
   \<Longrightarrow> scheduler_globals_frame_equiv s s''"
  by (simp add: scheduler_globals_frame_equiv_def)

lemma preserves_equivalence_2_weak:
assumes A: "(u,b) \<in> fst (f s)"
assumes B: "(u',ba) \<in> fst (g t)"
assumes R_preserved: "\<And>st. \<lbrace>P and (R st)\<rbrace> f \<lbrace>\<lambda>_.(R st)\<rbrace>"
assumes R_preserved': "\<And>st. \<lbrace>S and (R st)\<rbrace> g \<lbrace>\<lambda>_.(R st)\<rbrace>"
assumes R_sym: "\<forall>s s'. R s s' \<longrightarrow> R s' s"
assumes R_trans: "\<forall>s s' s''. R s s' \<longrightarrow> R s' s'' \<longrightarrow> R s s''"
shows "\<lbrakk> R s t;P s; S t\<rbrakk> \<Longrightarrow> R b ba"
  apply (insert A B)
  apply (drule use_valid[OF _ R_preserved])
  apply simp
   apply (rule R_sym[rule_format])
   apply assumption
  apply (drule use_valid[OF _ R_preserved'])
   apply simp
  apply (metis R_trans R_sym)
  done

lemma preserves_equivalence_weak:
assumes A: "(u,b) \<in> fst (f s)"
assumes B: "(u',ba) \<in> fst (f t)"
assumes R_preserved: "\<And>st. \<lbrace>P and (R st)\<rbrace> f \<lbrace>\<lambda>_.(R st)\<rbrace>"
assumes R_sym: "\<forall>s s'. R s s' \<longrightarrow> R s' s"
assumes R_trans: "\<forall>s s' s''. R s s' \<longrightarrow> R s' s'' \<longrightarrow> R s s''"
shows "\<lbrakk> R s t;P s; P t\<rbrakk> \<Longrightarrow> R b ba"
  using assms
  apply (blast intro: preserves_equivalence_2_weak)
  done



lemma scheduler_equiv_trans[elim]:
  "scheduler_equiv aag s s' \<Longrightarrow> scheduler_equiv aag s' s'' \<Longrightarrow> scheduler_equiv aag s s''"
  apply (simp add: scheduler_equiv_def domain_fields_equiv_def)
  apply clarify
  apply (rule conjI)
   apply (rule globals_equiv_scheduler_trans)
   apply simp+
  apply(blast intro: silc_dom_equiv_trans)
  done



lemma scheduler_equiv_sym[elim]:
  "scheduler_equiv aag s s' \<Longrightarrow> scheduler_equiv aag s' s"
  by (simp add: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_sym
                silc_dom_equiv_sym)

lemma scheduler_affects_equiv_trans[elim]:
  "\<lbrakk>scheduler_affects_equiv aag l s s'; scheduler_equiv aag s s';
    scheduler_affects_equiv aag l s' s''; scheduler_equiv aag s' s''\<rbrakk>
   \<Longrightarrow> scheduler_affects_equiv aag l s s''"
   apply (simp add: scheduler_affects_equiv_def scheduler_equiv_trans[where s'=s'])+
  apply clarify
  apply (rule conjI)
   apply (rule states_equiv_for_trans[where t=s'])
    apply simp+
  apply (force simp: scheduler_globals_frame_equiv_trans[where s'=s'] scheduler_equiv_def
                     domain_fields_equiv_def)
  done

lemma scheduler_affects_equiv_sym[elim]:
  "scheduler_affects_equiv aag l s s' \<Longrightarrow> scheduler_affects_equiv aag l s' s"
  apply (simp add: scheduler_affects_equiv_def)
  (* faster than the one-liner *)
  apply (clarsimp simp: scheduler_globals_frame_equiv_sym states_equiv_for_sym silc_dom_equiv_sym)
  apply force
  done

declare globals_equiv_scheduler_sym[elim]
declare globals_equiv_scheduler_trans[elim]
declare silc_dom_equiv_sym[elim]
declare silc_dom_equiv_trans[elim]

lemma scheduler_equiv_lift':
  assumes s: "\<And>st. \<lbrace>P and globals_equiv_scheduler st\<rbrace>  f \<lbrace>\<lambda>_.(globals_equiv_scheduler st)\<rbrace>"
  assumes d: "\<And>Q. \<lbrace>P and (\<lambda>s. Q (cur_domain s))\<rbrace> f \<lbrace>\<lambda>r s. Q (cur_domain s)\<rbrace>"
  assumes i: "\<And>P. invariant f (\<lambda>s. P (idle_thread s))"
  assumes e: "\<And>Q. \<lbrace>P and domain_fields Q\<rbrace> f \<lbrace>\<lambda>_. domain_fields Q\<rbrace>"
  assumes g: "\<And>P. invariant f (\<lambda>s. P (irq_state_of_state s))"
  assumes f: "\<And>st. \<lbrace>P and silc_dom_equiv aag st\<rbrace> f \<lbrace>\<lambda>_. silc_dom_equiv aag st\<rbrace>"
  shows "\<lbrace>P and scheduler_equiv aag st\<rbrace> f \<lbrace>\<lambda>_. scheduler_equiv aag st\<rbrace>"
  apply (simp add: scheduler_equiv_def[abs_def] domain_fields_equiv_def)
  apply (rule hoare_pre)
  apply (wp d e s i f g)
  apply simp
  done

lemmas scheduler_equiv_lift = scheduler_equiv_lift'[where P=\<top>,simplified]

lemma equiv_valid_inv_unobservable:
  assumes f: "\<And>st. \<lbrace>P and I st and A st\<rbrace> f \<lbrace>\<lambda>_. I st\<rbrace>"
  assumes g: "\<And>st. \<lbrace>P' and I st and A st\<rbrace> f \<lbrace>\<lambda>_. A st\<rbrace>"
  assumes sym: "\<forall>s s'. I s s' \<and> A s s' \<longrightarrow> I s' s \<and> A s' s"
  assumes trans: "\<forall>s s' s''. I s s' \<and> A s s' \<longrightarrow> I s' s'' \<and> A s' s'' \<longrightarrow> I s s'' \<and> A s s''"
  assumes s: "\<And>s. Q s \<Longrightarrow> P s \<and> P' s"
  shows "equiv_valid_inv I A  Q (f:: 'a \<Rightarrow> (unit \<times> 'a) set \<times> bool)"
  apply (clarsimp simp add: equiv_valid_def spec_equiv_valid_def equiv_valid_2_def)
  apply (erule preserves_equivalence_weak,assumption)
       apply (rule hoare_pre)
        apply (rule hoare_vcg_conj_lift)
         apply (rule f)
        apply (rule g)
       apply force
      apply (insert s)
      apply (fastforce intro!: sym trans)+
  done

lemma reads_respects_scheduler_unobservable'':
        "\<lbrakk>\<And>st. \<lbrace>P and scheduler_equiv aag st and scheduler_affects_equiv aag l st\<rbrace> f
              \<lbrace>\<lambda>_. scheduler_equiv aag st\<rbrace>;
         \<And>st. \<lbrace>P' and scheduler_equiv aag st and scheduler_affects_equiv aag l st\<rbrace> f
              \<lbrace>\<lambda>(_ :: unit). scheduler_affects_equiv aag l st\<rbrace>;
         \<And>s. Q s \<Longrightarrow> P s \<and> P' s\<rbrakk>
        \<Longrightarrow> reads_respects_scheduler aag l Q f"
  apply (rule equiv_valid_inv_unobservable,fastforce+)
  done

lemma reads_respects_scheduler_unobservable':
  assumes f: "\<And>st. \<lbrace>P and scheduler_equiv aag st\<rbrace> f \<lbrace>\<lambda>_. scheduler_equiv aag st\<rbrace>"
  assumes g:
    "\<And>st. \<lbrace>P and scheduler_affects_equiv aag l st\<rbrace> f \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  shows "reads_respects_scheduler aag l P (f:: (unit,det_ext) s_monad)"
  apply (rule reads_respects_scheduler_unobservable'')
   apply (wp f g | force)+
  done

definition swap_things where
  "swap_things s t \<equiv> t\<lparr> machine_state := underlying_memory_update
                                         (\<lambda>m a. if  a \<in> scheduler_affects_globals_frame t
                                                     then (underlying_memory (machine_state s) a)
                                                else m a) (machine_state t)
                        \<lparr>exclusive_state := exclusive_state (machine_state s)\<rparr>\<rparr>
                      \<lparr>cur_thread := cur_thread s\<rparr>"


lemma idle_equiv_machine_state_update[simp]:
  "idle_equiv st (s\<lparr>machine_state := x\<rparr>) = idle_equiv st s"
  by (simp add: idle_equiv_def)

lemma idle_equiv_machine_state_update'[simp]:
  "idle_equiv (st\<lparr>machine_state := x\<rparr>) s = idle_equiv st s"
  by (simp add: idle_equiv_def)

lemma idle_equiv_cur_thread_update'[simp]:
  "idle_equiv (st\<lparr>cur_thread := x\<rparr>) s = idle_equiv st s"
  by (simp add: idle_equiv_def)

lemma globals_equiv_scheduler_inv':
  "\<lbrakk>(\<And>st. \<lbrace> P and globals_equiv st\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>)\<rbrakk> \<Longrightarrow>
    \<lbrace> P and globals_equiv_scheduler s\<rbrace> f \<lbrace>\<lambda>_. globals_equiv_scheduler s\<rbrace>"
  apply atomize
  apply (rule use_spec)
  apply (simp add: spec_valid_def)
  apply (erule_tac x="(swap_things sa s)" in allE)
  apply (rule_tac Q="\<lambda>r st. globals_equiv (swap_things sa s) st" in hoare_strengthen_post )
   apply (rule hoare_pre)
    apply assumption
   apply (clarsimp simp add: globals_equiv_def swap_things_def globals_equiv_scheduler_def)+
  done

lemmas globals_equiv_scheduler_inv = globals_equiv_scheduler_inv'[where P="\<top>",simplified]

lemmas reads_respects_scheduler_unobservable =
             reads_respects_scheduler_unobservable'[where P="\<top>",simplified]

lemma silc_dom_equiv_scheduler_action_update[simp]:
  "silc_dom_equiv aag st (s\<lparr>scheduler_action := x\<rparr>) = silc_dom_equiv aag st s"
  by (simp add: silc_dom_equiv_def equiv_for_def)

crunch silc_dom_equiv[wp]: set_scheduler_action "silc_dom_equiv aag st"
  (ignore_del: set_scheduler_action)

lemma schedule_globals_frame_trans_state_upd[simp]:
  "scheduler_globals_frame_equiv st (trans_state f s) = scheduler_globals_frame_equiv st s"
  by (simp add: scheduler_globals_frame_equiv_def)

lemma idle_equiv_scheduler_action_update[simp]:
  "idle_equiv (scheduler_action_update f st) s = idle_equiv st s"
  by (simp add: idle_equiv_def)

lemma idle_equiv_scheduler_action_update'[simp]:
  "idle_equiv st (scheduler_action_update f s) = idle_equiv st s"
  by (simp add: idle_equiv_def)

lemma set_scheduler_action_rev_scheduler[wp]:
  "reads_respects_scheduler aag l \<top> (set_scheduler_action a)"
  apply (clarsimp simp add: set_scheduler_action_def)
  apply (rule ev_modify)
  apply (clarsimp simp add: scheduler_affects_equiv_def
                            scheduler_equiv_def states_equiv_for_def
                            equiv_asids_def equiv_asid_def
                            domain_fields_equiv_def
                            globals_equiv_scheduler_def
                            silc_dom_equiv_def
                            scheduler_globals_frame_equiv_def
                            equiv_for_def)
  done

lemma globals_equiv_scheduler_cur_thread_update[simp]:
  "globals_equiv_scheduler st (s\<lparr>cur_thread := x\<rparr>) = globals_equiv_scheduler st s"
  by (simp add: globals_equiv_scheduler_def idle_equiv_def)

lemma globals_equiv_scheduler_trans_state_update[simp]:
  "globals_equiv_scheduler st (trans_state f s) = globals_equiv_scheduler st s"
  by (simp add: globals_equiv_scheduler_def idle_equiv_def)

lemma states_equiv_for_cur_thread_update[simp]:
  "states_equiv_for P Q R S s (s'\<lparr>cur_thread := x\<rparr>) = states_equiv_for P Q R S s s'"
  by (simp add: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)

lemma scheduler_globals_frame_equiv_cur_thread_update[simp]:
  "scheduler_globals_frame_equiv st (s\<lparr>cur_thread := x\<rparr>) = scheduler_globals_frame_equiv st s"
  by (simp add: scheduler_globals_frame_equiv_def)

lemma scheduler_globals_frame_equiv_ready_queues_update[simp]:
  "scheduler_globals_frame_equiv st (s\<lparr>ready_queues := x\<rparr>) = scheduler_globals_frame_equiv st s"
  by (simp add: scheduler_globals_frame_equiv_def)

lemma scheduler_globals_frame_equiv_ready_queues_update'[simp]:
  "scheduler_globals_frame_equiv (st\<lparr>ready_queues := x\<rparr>) s = scheduler_globals_frame_equiv st s"
  by (simp add: scheduler_globals_frame_equiv_def)

lemma silc_dom_equiv_cur_thread_update[simp]:
  "silc_dom_equiv aag st (s\<lparr>cur_thread := x\<rparr>) = silc_dom_equiv aag st s"
  by (simp add: silc_dom_equiv_def equiv_for_def)

lemma silc_dom_equiv_ready_queues_update[simp]:
  "silc_dom_equiv aag st (s\<lparr>ready_queues := x\<rparr>) = silc_dom_equiv aag st s"
  by (simp add: silc_dom_equiv_def equiv_for_def)

lemma silc_dom_equiv_ready_queues_update'[simp]:
  "silc_dom_equiv aag (st\<lparr>ready_queues := x\<rparr>) s = silc_dom_equiv aag st s"
  by (simp add: silc_dom_equiv_def equiv_for_def)

lemma silc_dom_equiv_cur_thread_update'[simp]:
  "silc_dom_equiv aag (st\<lparr>cur_thread := x\<rparr>) s = silc_dom_equiv aag st s"
  by (simp add: silc_dom_equiv_def equiv_for_def)


lemma scheduler_equiv_ready_queues_update[simp]:
  "scheduler_equiv aag (st\<lparr>ready_queues := x\<rparr>) s = scheduler_equiv aag st s"
  by (simp add: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def
                   idle_equiv_def)

lemma scheduler_equiv_ready_queues_update'[simp]:
  "scheduler_equiv aag st (s\<lparr>ready_queues := x\<rparr>) = scheduler_equiv aag st s"
  by (simp add: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def
                   idle_equiv_def)


lemma get_tcb_queue_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l (K(pasDomainAbs aag rv \<inter> reads_scheduler aag l \<noteq> {}))
                            (get_tcb_queue rv rva)"
  apply (rule gen_asm_ev)
  apply (simp add: get_tcb_queue_def)
  apply (subst gets_apply)
  apply (wp gets_apply_ev)
  apply (force simp: scheduler_affects_equiv_def states_equiv_for_def
                     equiv_for_def disjoint_iff_not_equal)
  done

lemma ethread_get_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l (K(pasObjectAbs aag t \<in> reads_scheduler aag l)) (ethread_get f t)"
  apply (rule gen_asm_ev)
  apply (simp add: ethread_get_def)
  apply wp
  apply (clarsimp simp add: scheduler_affects_equiv_def states_equiv_for_def
                            equiv_for_def get_etcb_def)
  done

lemma ethread_get_when_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l (K(b \<longrightarrow> pasObjectAbs aag t \<in> reads_scheduler aag l))
    (ethread_get_when b f t)"
  apply (simp add: ethread_get_when_def)
  apply (rule conjI; clarsimp)
   using ethread_get_reads_respects_scheduler
   apply fastforce
  apply wp
  done

end

lemma (in is_extended') globals_equiv[wp]:
  "I (globals_equiv st)"
  by (rule lift_inv,simp)

lemma (in is_extended') globals_equiv_scheduler[wp]:
  "I (globals_equiv_scheduler st)"
  by (rule lift_inv,simp)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma tcb_domain_wellformed:
  "\<lbrakk>pas_refined aag s; ekheap s t = Some a\<rbrakk> \<Longrightarrow> pasObjectAbs aag t \<in> pasDomainAbs aag (tcb_domain a)"
  apply (clarsimp simp add: pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (drule_tac x="(t,tcb_domain a)" in bspec)
  apply (rule domtcbs)
  apply force+
  done

lemma reads_respects_scheduler_cases:
  assumes b:
    "pasObjectAbs aag t \<in> reads_scheduler aag l \<Longrightarrow> reads_respects_scheduler aag l P' (f t)"
  assumes b': "\<And>s. Q s \<Longrightarrow> pasObjectAbs aag t \<in> reads_scheduler aag l \<Longrightarrow> P' s"
  assumes c:
    "pasObjectAbs aag t \<notin> reads_scheduler aag l \<Longrightarrow> reads_respects_scheduler aag l P'' (f t)"
  assumes c': "\<And>s. Q s \<Longrightarrow> pasObjectAbs aag t \<notin> reads_scheduler aag l \<Longrightarrow> P'' s"
  shows "reads_respects_scheduler aag l Q (f t)"
  apply (insert b b' c c')
  apply (case_tac "pasObjectAbs aag t \<in> reads_scheduler aag l")
  apply (fastforce intro: equiv_valid_guard_imp)+
  done


lemma silc_dom_equiv_trans_state[simp]:
  "silc_dom_equiv aag st (trans_state f s) = silc_dom_equiv aag st s"
  by (simp add: silc_dom_equiv_def equiv_for_def)

end

lemma (in is_extended') silc_dom_equiv[wp]:
  "I (silc_dom_equiv aag st)"
  by (rule lift_inv,simp)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma tcb_action_reads_respects_scheduler[wp]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l (pas_refined aag) (tcb_sched_action f t)"
  apply (rule reads_respects_scheduler_cases)
     apply (simp add: tcb_sched_action_def set_tcb_queue_def)
     apply wp
           apply (rule ev_modify[where P=\<top>])
           apply (clarsimp simp add: scheduler_equiv_def domain_fields_equiv_def
                            globals_equiv_scheduler_def)
           apply (clarsimp simp: scheduler_affects_equiv_def states_equiv_for_def
                                 equiv_for_def equiv_asids_def equiv_asid_def idle_equiv_def
                                 )
           apply metis
          apply wp+
    apply (clarsimp simp add: etcb_at_def split: option.splits)
    apply (frule(1) tcb_domain_wellformed)
    apply blast
   apply (simp add: tcb_sched_action_def set_tcb_queue_def)
   apply (rule reads_respects_scheduler_unobservable'[where P="pas_refined aag"])
    apply wp
    apply (clarsimp simp add: etcb_at_def split: option.splits)
   apply wp
   apply (clarsimp simp: etcb_at_def split: option.splits)
   apply (clarsimp simp: scheduler_affects_equiv_def states_equiv_for_def
                         equiv_for_def equiv_asids_def equiv_asid_def)
   apply (frule(1) tcb_domain_wellformed)
   apply (rule ext)
   apply (solves \<open>auto dest: domains_distinct[THEN pas_domains_distinct_inj]\<close>)
  apply assumption
  done

lemma dmo_no_mem_globals_equiv_scheduler:
  assumes a: "(\<And>P. invariant f (\<lambda>ms. P (underlying_memory ms)))"
       and b: "(\<And>P. invariant f (\<lambda>ms. P (device_state ms)))"
  shows "invariant (do_machine_op f) (globals_equiv_scheduler s)"
  unfolding do_machine_op_def
  apply (rule hoare_pre)
  apply (wp | simp add: split_def)+
  apply clarsimp
  apply (frule_tac P1 = "\<lambda>um. um = underlying_memory (machine_state sa)" in use_valid[OF _ a])
   apply simp
  apply (frule_tac P1 = "\<lambda>um. um = device_state (machine_state sa)" in use_valid[OF _ b])
   apply simp
  apply (fastforce simp: valid_def globals_equiv_scheduler_def idle_equiv_def)
  done

lemma clearExMonitor_globals_equiv_scheduler[wp]:
  "\<lbrace> globals_equiv_scheduler sta \<rbrace> do_machine_op clearExMonitor \<lbrace> \<lambda>_. globals_equiv_scheduler sta \<rbrace>"
  unfolding clearExMonitor_def including no_pre
  apply (wp dmo_no_mem_globals_equiv_scheduler)
   apply simp
  apply (simp add: simpler_modify_def valid_def)
  done

lemma arch_switch_to_thread_globals_equiv_scheduler:
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace> arch_switch_to_thread thread
       \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  unfolding arch_switch_to_thread_def storeWord_def
  by (wpsimp wp: clearExMonitor_globals_equiv_scheduler dmo_wp modify_wp thread_get_wp'
           | wp (once) globals_equiv_scheduler_inv'[where P="\<top>"])+

lemma dmo_storeWord_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l \<top> (do_machine_op (storeWord rva rvb))"
  apply (clarsimp simp add: do_machine_op_def bind_def gets_def get_def
                    return_def select_f_def storeWord_def
                    assert_def simpler_modify_def fail_def)
  apply (fold simpler_modify_def)
  apply (intro impI conjI)
   apply (rule ev_modify)
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def
                         globals_equiv_scheduler_def)
   apply (clarsimp simp add: scheduler_affects_equiv_def states_equiv_for_def
                    equiv_for_def equiv_asids_def equiv_asid_def
                    scheduler_globals_frame_equiv_def silc_dom_equiv_def
                    )
  apply (simp add: equiv_valid_def2 equiv_valid_2_def)
  done

definition weak_scheduler_affects_equiv :: "'a subject_label PAS  \<Rightarrow> ('a subject_label) \<Rightarrow>
                                            det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
"weak_scheduler_affects_equiv aag l s s' \<equiv>
  (states_equiv_for_labels aag (\<lambda>l'. l' \<in> reads_scheduler aag l) s s')"

definition midstrength_scheduler_affects_equiv :: "'a subject_label PAS  \<Rightarrow> ('a subject_label) \<Rightarrow>
                                                   det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
"midstrength_scheduler_affects_equiv aag l s s' \<equiv>
  (states_equiv_for_labels aag (\<lambda>l'. l' \<in> reads_scheduler aag l) s s') \<and>
  (reads_scheduler_cur_domain aag l s \<or> reads_scheduler_cur_domain aag l s' \<longrightarrow>
     work_units_completed s = work_units_completed s')"

abbreviation strong_reads_respects_scheduler
where
"strong_reads_respects_scheduler aag l P f  \<equiv>
   equiv_valid (scheduler_equiv aag) (weak_scheduler_affects_equiv aag l)
               (scheduler_affects_equiv aag l) P f"

abbreviation midstrength_reads_respects_scheduler
where
"midstrength_reads_respects_scheduler aag l P f  \<equiv>
   equiv_valid (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
               (scheduler_affects_equiv aag l) P f"

abbreviation weak_reads_respects_scheduler
where
"weak_reads_respects_scheduler aag l P f  \<equiv>
   equiv_valid (scheduler_equiv aag) (weak_scheduler_affects_equiv aag l)
               (weak_scheduler_affects_equiv aag l) P f"

lemma store_cur_thread_midstrength_reads_respects:
  "equiv_valid (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
           (scheduler_affects_equiv aag l) (invs and (\<lambda>s. t = idle_thread s))
           (do x \<leftarrow> modify (cur_thread_update (\<lambda>_. t));
               set_scheduler_action resume_cur_thread
            od)"
  apply (clarsimp simp add: do_machine_op_def bind_def gets_def get_def
                    return_def select_f_def storeWord_def bind_def
                    set_scheduler_action_def
                    assert_def simpler_modify_def fail_def)
  apply (fold simpler_modify_def)
   apply (rule ev_modify)
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def
                         globals_equiv_scheduler_def)
   apply (clarsimp simp: scheduler_affects_equiv_def states_equiv_for_def
                         equiv_for_def equiv_asids_def equiv_asid_def
                         scheduler_globals_frame_equiv_def silc_dom_equiv_def
                         weak_scheduler_affects_equiv_def midstrength_scheduler_affects_equiv_def
                        idle_equiv_def)
   done

lemma globals_frame_equiv_as_states_equiv:
  "scheduler_globals_frame_equiv st s =
   states_equiv_for
     (\<lambda>x. x \<in> scheduler_affects_globals_frame s) \<bottom> \<bottom> \<bottom>
     (s\<lparr>machine_state := machine_state st, arch_state := arch_state st\<rparr>) s"
  by (clarsimp simp add: states_equiv_for_def equiv_for_def
                         scheduler_globals_frame_equiv_def
                         equiv_asids_def)

lemma silc_dom_equiv_as_states_equiv:
  "silc_dom_equiv aag st s =
   states_equiv_for
     (\<lambda>x. pasObjectAbs aag x = SilcLabel) \<bottom> \<bottom> \<bottom>
     (s\<lparr>kheap := kheap st\<rparr>) s"
  apply (clarsimp simp add: states_equiv_for_def equiv_for_def
                            silc_dom_equiv_def
                            equiv_asids_def)
  done

lemma silc_dom_equiv_states_equiv_lift:
  assumes a: "\<And>P Q R S st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  shows "\<lbrace>silc_dom_equiv aag st\<rbrace> f \<lbrace>\<lambda>_. silc_dom_equiv aag st\<rbrace>"
  apply (simp add: silc_dom_equiv_as_states_equiv[abs_def])
  apply (clarsimp simp add: valid_def)
  apply (frule use_valid[OF _ a])
   apply assumption
  apply (simp add: states_equiv_for_def equiv_for_def equiv_asids_def)
  done

lemma scheduler_affects_equiv_unobservable:
  assumes a: "\<And>P Q R S st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_domain s)\<rbrace>"
  assumes e: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_thread s)\<rbrace>"
  assumes s: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>r s. P (scheduler_action s)\<rbrace>"
  assumes w: "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace> f \<lbrace>\<lambda>r s. P (work_units_completed s)\<rbrace>"
  assumes i: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  assumes x:
    "\<And>P. \<lbrace>\<lambda>s. P (exclusive_state (machine_state s))\<rbrace>
            f
          \<lbrace>\<lambda>r s. P (exclusive_state (machine_state s))\<rbrace>"
  shows "\<lbrace>scheduler_affects_equiv aag l st\<rbrace>
           f
         \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  proof -
  have d: "\<lbrace>scheduler_globals_frame_equiv st\<rbrace> f \<lbrace>\<lambda>_. scheduler_globals_frame_equiv st\<rbrace>"
  apply (simp add: globals_frame_equiv_as_states_equiv[abs_def])
  apply (clarsimp simp add: valid_def)
  apply (frule use_valid[OF _ a])
   apply assumption
  apply (simp add: states_equiv_for_def equiv_for_def equiv_asids_def)
  done
  show ?thesis
    apply (simp add: scheduler_affects_equiv_def[abs_def])
    apply (rule hoare_pre)
     apply (wps c)
     apply (wp static_imp_wp a silc_dom_equiv_states_equiv_lift d e s w i x hoare_vcg_imp_lift)
    apply fastforce
  done
qed

lemma midstrength_scheduler_affects_equiv_unobservable:
  assumes a: "\<And>P Q R S st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes w:
    "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) (work_units_completed s)\<rbrace>
            f
         \<lbrace>\<lambda>r s. P (cur_domain s) (work_units_completed s)\<rbrace>"
  shows "\<lbrace>midstrength_scheduler_affects_equiv aag l st\<rbrace>
           f
         \<lbrace>\<lambda>_. midstrength_scheduler_affects_equiv aag l st\<rbrace>"
    apply (simp add: midstrength_scheduler_affects_equiv_def[abs_def])
    apply (rule hoare_pre)
     apply (wp a w silc_dom_equiv_states_equiv_lift)
    apply clarsimp
  done

lemma dmo_mol_exclusive_state[wp]:
  "invariant (do_machine_op (machine_op_lift mop)) (\<lambda>s. P (exclusive_state (machine_state s)))"
  by(wp mol_exclusive_state dmo_wp
    | simp add: split_def dmo_bind_valid writeTTBR0_def isb_def dsb_def )+

crunch exclusive_state[wp]: set_vm_root "\<lambda>s. P (exclusive_state (machine_state s))"
  (ignore: do_machine_op
     simp: invalidateLocalTLB_ASID_def setHardwareASID_def set_current_pd_def dsb_def isb_def
           writeTTBR0_def dmo_bind_valid crunch_simps)

lemmas set_vm_root_scheduler_affects_equiv[wp] =
        scheduler_affects_equiv_unobservable[OF set_vm_root_states_equiv_for
                                                set_vm_root_exst _ _ _ set_vm_root_it
                                                set_vm_root_exclusive_state]

lemma set_vm_root_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l \<top> (set_vm_root thread)"
  apply (rule reads_respects_scheduler_unobservable'[
                             OF scheduler_equiv_lift'[OF globals_equiv_scheduler_inv']])
  apply (wp silc_dom_equiv_states_equiv_lift set_vm_root_states_equiv_for | simp)+
  done

lemma thread_get_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l (K(pasObjectAbs aag t \<in> reads_scheduler aag l)) (thread_get f t)"
  apply (rule gen_asm_ev)
  apply (simp add: thread_get_def)
  apply wp
  apply (clarsimp simp add: scheduler_affects_equiv_def states_equiv_for_def
                            equiv_for_def get_tcb_def)
  done

crunch idle_thread[wp]: guarded_switch_to,schedule "\<lambda>(s :: det_state). P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma silc_dom_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (kheap s)\<rbrace> f \<lbrace>\<lambda>r s. P (kheap s)\<rbrace>"
         shows "\<lbrace>silc_dom_equiv aag st\<rbrace> f \<lbrace>\<lambda>_. silc_dom_equiv aag st\<rbrace>"
  apply (simp add: silc_dom_equiv_def equiv_for_def[abs_def])
  apply (wp a)
  done

lemma dmo_silc_dom[wp]:
  "\<lbrace>silc_dom_equiv aag st\<rbrace> do_machine_op mop \<lbrace>\<lambda>_. silc_dom_equiv aag st\<rbrace>"
  by (wp silc_dom_lift)

crunch kheap[wp]: guarded_switch_to, schedule "\<lambda>s :: det_state. P (kheap s)"
  (wp: dxo_wp_weak crunch_wps simp: crunch_simps)

lemma storeWord_irq_state_of_state[wp]:
  "\<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  apply (simp add: storeWord_def)
  apply (wp dmo_wp modify_wp)
  apply simp
  done

lemma clearExMonitor_irq_state_of_state[wp]:
  "\<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace> do_machine_op clearExMonitor \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  by (wpsimp wp: dmo_wp irq_state_clearExMonitor)

lemma clearExMonitor_scheduler_equiv[wp]:
  "\<lbrace> scheduler_equiv aag st \<rbrace> do_machine_op clearExMonitor \<lbrace> \<lambda>_. scheduler_equiv aag st \<rbrace>"
  by (rule scheduler_equiv_lift; wp)

lemma dmo_ev:
  "(\<And>s s'. equiv_valid (\<lambda>ms ms'. I (s\<lparr>machine_state := ms\<rparr>) (s'\<lparr>machine_state := ms'\<rparr>))
                   (\<lambda>ms ms'. A (s\<lparr>machine_state := ms\<rparr>) (s'\<lparr>machine_state := ms'\<rparr>))
                   (\<lambda>ms ms'. B (s\<lparr>machine_state := ms\<rparr>) (s'\<lparr>machine_state := ms'\<rparr>))
          (K (P s \<and> P s')) f)
    \<Longrightarrow> equiv_valid I A B P (do_machine_op f)"
  apply (clarsimp simp: do_machine_op_def bind_def equiv_valid_def2 equiv_valid_2_def gets_def
                        get_def select_f_def modify_def put_def return_def split_def)
  apply atomize
  apply (erule_tac x=s in allE)
  apply (erule_tac x=t in allE)
  apply simp
  apply (erule_tac x="machine_state s" in allE)
  apply (erule_tac x="machine_state t" in allE)
  apply fastforce
  done

lemma [wp]: "reads_respects_scheduler aag l (\<lambda>_. True) (do_machine_op clearExMonitor)"
  apply (simp add: clearExMonitor_def)
  apply (wp dmo_ev)
  apply (rule ev_modify)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def
                         silc_dom_equiv_def equiv_for_def)
  apply (clarsimp simp: scheduler_affects_equiv_def states_equiv_for_def equiv_for_def
                        equiv_asids_def equiv_asid_def scheduler_globals_frame_equiv_def
              simp del: split_paired_All)
  done

definition asahi_scheduler_affects_equiv ::
  "'a subject_label PAS \<Rightarrow> 'a subject_label \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
  where
    "asahi_scheduler_affects_equiv aag l s s' \<equiv>
       states_equiv_for_labels aag (\<lambda>x. x \<in> reads_scheduler aag l) s s' \<and>
       (reads_scheduler_cur_domain aag l s \<or> reads_scheduler_cur_domain aag l s' \<longrightarrow>
          work_units_completed s = work_units_completed s' \<and>
          scheduler_globals_frame_equiv s s')"

lemma asahi_scheduler_affects_equiv_unobservable:
  assumes a: "\<And>P Q R S X st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_domain s)\<rbrace>"
  assumes w: "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace> f \<lbrace>\<lambda>r s. P (work_units_completed s)\<rbrace>"
  shows "\<lbrace>asahi_scheduler_affects_equiv aag l st\<rbrace> f
         \<lbrace>\<lambda>_. asahi_scheduler_affects_equiv aag l st\<rbrace>"
  proof -
  have d: "\<lbrace>scheduler_globals_frame_equiv st\<rbrace> f \<lbrace>\<lambda>_. scheduler_globals_frame_equiv st\<rbrace>"
  apply (simp add: globals_frame_equiv_as_states_equiv[abs_def])
  apply (clarsimp simp add: valid_def)
  apply (frule use_valid[OF _ a])
   apply assumption
  apply (simp add: states_equiv_for_def equiv_for_def equiv_asids_def)
  done
  show ?thesis
    apply (simp add: asahi_scheduler_affects_equiv_def[abs_def])
    apply (rule hoare_pre)
     apply (wps c)
     apply (wp static_imp_wp a silc_dom_equiv_states_equiv_lift d w)
    apply clarsimp
  done
qed

lemma asahi_scheduler_affects_equiv_sym[elim]:
  "asahi_scheduler_affects_equiv aag l s s' \<Longrightarrow> asahi_scheduler_affects_equiv aag l s' s"
  apply (simp add: asahi_scheduler_affects_equiv_def)
  apply (auto simp: scheduler_globals_frame_equiv_sym states_equiv_for_sym silc_dom_equiv_sym)
  done

lemma asahi_scheduler_affects_equiv_trans[elim]:
  "\<lbrakk>asahi_scheduler_affects_equiv aag l s s'; scheduler_equiv aag s s';
    asahi_scheduler_affects_equiv aag l s' s''; scheduler_equiv aag s' s''\<rbrakk>
   \<Longrightarrow> asahi_scheduler_affects_equiv aag l s s''"
   apply (simp add: asahi_scheduler_affects_equiv_def scheduler_equiv_trans[where s'=s'])+
  apply clarify
  apply (rule conjI)
   apply (rule states_equiv_for_trans[where t=s'])
    apply simp+
  apply (force simp: scheduler_globals_frame_equiv_trans[where s'=s'] scheduler_equiv_def
                     domain_fields_equiv_def)
  done

definition asahi_ex_scheduler_affects_equiv ::
  "'a subject_label PAS \<Rightarrow> 'a subject_label \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
  where
    "asahi_ex_scheduler_affects_equiv aag l s s' \<equiv>
       states_equiv_for_labels aag (\<lambda>x. x \<in> reads_scheduler aag l) s s' \<and>
       (reads_scheduler_cur_domain aag l s \<or> reads_scheduler_cur_domain aag l s' \<longrightarrow>
          work_units_completed s = work_units_completed s' \<and>
          scheduler_globals_frame_equiv s s' \<and>
          exclusive_state_equiv s s')"

lemma asahi_ex_scheduler_affects_equiv_unobservable:
  assumes a: "\<And>P Q R S X st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>r s. P (cur_domain s)\<rbrace>"
  assumes w: "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace> f \<lbrace>\<lambda>r s. P (work_units_completed s)\<rbrace>"
  assumes x:
    "\<And>P. \<lbrace>\<lambda>s. P (exclusive_state (machine_state s))\<rbrace>
            f
         \<lbrace>\<lambda>r s. P (exclusive_state (machine_state s))\<rbrace>"
  shows "\<lbrace>asahi_ex_scheduler_affects_equiv aag l st\<rbrace>
           f
         \<lbrace>\<lambda>_. asahi_ex_scheduler_affects_equiv aag l st\<rbrace>"
  proof -
  have d: "\<lbrace>scheduler_globals_frame_equiv st\<rbrace> f \<lbrace>\<lambda>_. scheduler_globals_frame_equiv st\<rbrace>"
  apply (simp add: globals_frame_equiv_as_states_equiv[abs_def])
  apply (clarsimp simp add: valid_def)
  apply (frule use_valid[OF _ a])
   apply assumption
  apply (simp add: states_equiv_for_def equiv_for_def equiv_asids_def)
  done
  show ?thesis
    apply (simp add: asahi_ex_scheduler_affects_equiv_def[abs_def])
    apply (rule hoare_pre)
     apply (wps c)
     apply (wp static_imp_wp a silc_dom_equiv_states_equiv_lift d w x)
    apply clarsimp
  done
qed

lemma asahi_ex_scheduler_affects_equiv_sym[elim]:
  "asahi_ex_scheduler_affects_equiv aag l s s' \<Longrightarrow> asahi_ex_scheduler_affects_equiv aag l s' s"
  apply (simp add: asahi_ex_scheduler_affects_equiv_def)
  apply (auto simp: scheduler_globals_frame_equiv_sym states_equiv_for_sym silc_dom_equiv_sym)
  done

lemma asahi_ex_scheduler_affects_equiv_trans[elim]:
  "\<lbrakk>asahi_ex_scheduler_affects_equiv aag l s s'; scheduler_equiv aag s s';
    asahi_ex_scheduler_affects_equiv aag l s' s''; scheduler_equiv aag s' s''\<rbrakk>
    \<Longrightarrow> asahi_ex_scheduler_affects_equiv aag l s s''"
   apply (simp add: asahi_ex_scheduler_affects_equiv_def scheduler_equiv_trans[where s'=s'])+
  apply clarify
  apply (rule conjI)
   apply (rule states_equiv_for_trans[where t=s'])
    apply simp+
  apply (force simp: scheduler_globals_frame_equiv_trans[where s'=s'] scheduler_equiv_def
                     domain_fields_equiv_def)
  done

lemma ev_asahi_to_asahi_ex_dmo_clearExMonitor:
  "equiv_valid (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
               (asahi_ex_scheduler_affects_equiv aag l)
   \<top> (do_machine_op clearExMonitor)"
  apply (simp add: clearExMonitor_def)
  apply (wp dmo_ev)
  apply (rule ev_modify)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def
                         silc_dom_equiv_def equiv_for_def)
  apply (clarsimp simp: midstrength_scheduler_affects_equiv_def asahi_scheduler_affects_equiv_def
                        asahi_ex_scheduler_affects_equiv_def states_equiv_for_def equiv_for_def
                        equiv_asids_def equiv_asid_def scheduler_globals_frame_equiv_def
              simp del: split_paired_All)
  done

lemma ev_asahi_ex_to_full_fragement:
  "equiv_valid (scheduler_equiv aag) (asahi_ex_scheduler_affects_equiv aag l)
               (scheduler_affects_equiv aag l) \<top>
               (do x \<leftarrow> modify (cur_thread_update (\<lambda>_. t));
                   set_scheduler_action resume_cur_thread
                od)"
  apply (clarsimp simp: gets_def get_def return_def select_f_def  bind_def
                        set_scheduler_action_def assert_def simpler_modify_def fail_def)
  apply (fold simpler_modify_def)
  apply (rule ev_modify)
  apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def states_equiv_for_def
                        globals_equiv_scheduler_def scheduler_affects_equiv_def
                        equiv_for_def equiv_asids_def equiv_asid_def
                        scheduler_globals_frame_equiv_def silc_dom_equiv_def
                        weak_scheduler_affects_equiv_def
                        asahi_ex_scheduler_affects_equiv_def idle_equiv_def)
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
(*******************************)

lemma arch_switch_to_thread_globals_equiv_scheduler':
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace>
        set_vm_root t
       \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  by (rule globals_equiv_scheduler_inv', wpsimp)

lemma arch_switch_to_thread_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l ((\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)) and
                                    invs)
                            (arch_switch_to_thread t)"
  apply (rule reads_respects_scheduler_cases)
     apply (simp add: arch_switch_to_thread_def)
     apply wp
    apply (clarsimp simp: scheduler_equiv_def globals_equiv_scheduler_def)
   apply (simp add: arch_switch_to_thread_def)
   apply wp
  apply simp
  done

lemma arch_switch_to_thread_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace>
    arch_switch_to_thread t
  \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  unfolding arch_switch_to_thread_def
  by (wp do_machine_op_pas_refined | simp)+


lemma cur_thread_update_idle_reads_respects_scheduler:
  "reads_respects_scheduler aag l (\<lambda>s. t = idle_thread s)
        (modify (cur_thread_update (\<lambda>_. t)))"
  apply (rule ev_modify)
  apply (clarsimp simp add: scheduler_affects_equiv_def
                   scheduler_equiv_def domain_fields_equiv_def
                   globals_equiv_scheduler_def states_equiv_for_def
                   equiv_for_def equiv_asids_def equiv_asid_def
                   scheduler_globals_frame_equiv_def idle_equiv_def)
  done

lemma strong_cur_domain_unobservable:
  "reads_respects_scheduler aag l
             (P and (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s)) f
   \<Longrightarrow> strong_reads_respects_scheduler aag l
             (P and (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s)) f"
  apply (clarsimp simp add: equiv_valid_def2 equiv_valid_2_def
                            scheduler_equiv_def domain_fields_equiv_def
                            scheduler_affects_equiv_def weak_scheduler_affects_equiv_def)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply clarsimp
  apply (drule_tac x="(a,b)" in bspec,clarsimp+)
  apply (drule_tac x="(aa,ba)" in bspec,clarsimp+)
  done

lemma midstrength_cur_domain_unobservable:
  "reads_respects_scheduler aag l
         (P and (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s)) f
   \<Longrightarrow> midstrength_reads_respects_scheduler aag l
         (P and (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s)) f"
  apply (clarsimp simp add: equiv_valid_def2 equiv_valid_2_def
                            scheduler_equiv_def domain_fields_equiv_def
                            scheduler_affects_equiv_def midstrength_scheduler_affects_equiv_def)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply clarsimp
  apply (drule_tac x="(a,b)" in bspec,clarsimp+)
  apply (drule_tac x="(aa,ba)" in bspec,clarsimp+)
  done


lemma equiv_valid_get_assert:
  "equiv_valid I A B P f \<Longrightarrow>
   equiv_valid I A B P (get >>= (\<lambda> s. assert (g s) >>= (\<lambda> y. f)))"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def bind_def get_def
                        assert_def return_def fail_def)
  apply fastforce
  done



lemma midstrength_reads_respects_scheduler_cases:
  assumes domains_distinct: "pas_domains_distinct aag"
  assumes b:
    "pasObjectAbs aag t \<in> reads_scheduler aag l
     \<Longrightarrow> midstrength_reads_respects_scheduler aag l P' (f t)"
  assumes b': "\<And>s. Q s \<Longrightarrow> pasObjectAbs aag t \<in> reads_scheduler aag l \<Longrightarrow> P' s"
  assumes c:
    "pasObjectAbs aag t \<notin> reads_scheduler aag l
     \<Longrightarrow> reads_respects_scheduler aag l P'' (f t)"
  assumes c': "\<And>s. Q s \<Longrightarrow> pasObjectAbs aag t \<notin> reads_scheduler aag l \<Longrightarrow> P'' s"
  assumes d: "\<And>s. Q s \<Longrightarrow> pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)"
  shows "midstrength_reads_respects_scheduler aag l Q (f t)"
  apply (case_tac "pasObjectAbs aag t \<in> reads_scheduler aag l")
   apply (rule equiv_valid_guard_imp)
    apply (rule b)
     apply simp+
   apply (rule b')
     apply simp+
  apply (rule equiv_valid_guard_imp)
   apply (rule midstrength_cur_domain_unobservable)
   apply (rule equiv_valid_guard_imp)
    apply (rule c)
     apply simp+
   apply fastforce
  apply clarsimp
  apply (rule conjI)
   apply (rule c')
     apply simp+
  apply (fastforce dest: d domains_distinct[THEN pas_domains_distinct_inj])
  done

lemma thread_get_weak_reads_respects_scheduler[wp]:
  "weak_reads_respects_scheduler aag l
     (K (pasObjectAbs aag t \<in> reads_scheduler aag l))
     (thread_get f t)"
  apply (rule gen_asm_ev)
  apply (simp add: thread_get_def)
  apply wp
  apply (clarsimp simp add: weak_scheduler_affects_equiv_def states_equiv_for_def
                            equiv_for_def get_tcb_def)
  done

lemma midstrength_weak[intro]:
  "midstrength_scheduler_affects_equiv aag l s s' \<Longrightarrow> weak_scheduler_affects_equiv aag l s s'"
  apply(auto simp: midstrength_scheduler_affects_equiv_def weak_scheduler_affects_equiv_def)
  done

lemma weak_reads_respects_scheduler_to_midstrength:
  assumes w: "weak_reads_respects_scheduler aag l P f"
  assumes i: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "equiv_valid_inv (scheduler_equiv aag)
        (midstrength_scheduler_affects_equiv aag l) P f"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply(rule conjI)
   apply(insert w)[1]
   apply(fastforce simp: equiv_valid_def2 equiv_valid_2_def)
  apply(blast dest: state_unchanged[OF i])
  done

lemma weak_scheduler_affects_equiv_trans[elim]:
  "\<lbrakk>weak_scheduler_affects_equiv aag l s s'; weak_scheduler_affects_equiv aag l s' s''\<rbrakk>
    \<Longrightarrow> weak_scheduler_affects_equiv aag l s s''"
  apply (simp add: weak_scheduler_affects_equiv_def)
  apply (fastforce intro: states_equiv_for_trans)
  done

lemma midstrength_scheduler_affects_equiv_trans[elim]:
  "\<lbrakk>scheduler_equiv aag s s'; midstrength_scheduler_affects_equiv aag l s s';
    scheduler_equiv aag s' s''; midstrength_scheduler_affects_equiv aag l s' s''\<rbrakk>
    \<Longrightarrow> midstrength_scheduler_affects_equiv aag l s s''"
  apply (simp add: midstrength_scheduler_affects_equiv_def scheduler_equiv_def
                   domain_fields_equiv_def)
  apply (fastforce intro: states_equiv_for_trans)
  done


lemma weak_scheduler_affects_equiv_sym[elim]:
  "weak_scheduler_affects_equiv aag l s s' \<Longrightarrow> weak_scheduler_affects_equiv aag l s' s"
  apply (simp add: weak_scheduler_affects_equiv_def)
  apply (fastforce intro: states_equiv_for_sym)
  done

lemma midstrength_scheduler_affects_equiv_sym[elim]:
  "midstrength_scheduler_affects_equiv aag l s s'
   \<Longrightarrow> midstrength_scheduler_affects_equiv aag l s' s"
  apply (simp add: midstrength_scheduler_affects_equiv_def)
  apply (fastforce intro: states_equiv_for_sym)
  done

lemma ethread_get_oblivious_cur_thread:
  "oblivious (cur_thread_update f) (ethread_get a b)"
  apply (simp add: ethread_get_def gets_the_def)
  apply (wp oblivious_bind | simp add: oblivious_gets get_etcb_def)+
  done

lemma ethread_get_oblivious_schact:
  "oblivious (scheduler_action_update f) (ethread_get a b)"
  apply (simp add: ethread_get_def gets_the_def)
  apply (wp oblivious_bind | simp add: oblivious_gets get_etcb_def)+
  done

lemma tcb_action_oblivious_cur_thread:
  "oblivious (cur_thread_update a) (tcb_sched_action f t)"
   apply (simp add: tcb_sched_action_def)
   apply (wp oblivious_bind ethread_get_oblivious_cur_thread
         | clarsimp simp add: get_tcb_queue_def set_tcb_queue_def)+
   apply (fastforce intro: state.equality det_ext.equality)
   done

lemma tcb_action_oblivious_schact:
  "oblivious (scheduler_action_update a) (tcb_sched_action f t)"
   apply (simp add: tcb_sched_action_def)
   apply (wp oblivious_bind ethread_get_oblivious_schact
         | clarsimp simp add: get_tcb_queue_def set_tcb_queue_def)+
   apply (fastforce intro: state.equality det_ext.equality)
   done

lemma cur_thread_update_not_subject_reads_respects_scheduler:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l (\<lambda>s. pasObjectAbs aag t \<notin> reads_scheduler aag l \<and>
                                       pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s))
        (modify (cur_thread_update (\<lambda>_. t)))"
  apply (rule ev_modify)
  apply (clarsimp simp add: scheduler_affects_equiv_def
                   scheduler_equiv_def domain_fields_equiv_def
                   globals_equiv_scheduler_def states_equiv_for_def
                   equiv_for_def equiv_asids_def equiv_asid_def
                   scheduler_globals_frame_equiv_def idle_equiv_def)
  apply (blast dest: domains_distinct[THEN pas_domains_distinct_inj])
  done

lemma switch_to_thread_midstrength_reads_respects_scheduler[wp]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "midstrength_reads_respects_scheduler aag l
              (invs and pas_refined aag and
                 (\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)))
              (switch_to_thread t >>= (\<lambda>_. set_scheduler_action resume_cur_thread))"
  apply (simp add: switch_to_thread_def)
  apply (subst oblivious_modify_swap[symmetric, OF tcb_action_oblivious_cur_thread])
  apply (simp add: bind_assoc)
  apply (simp add: set_scheduler_action_def)
  apply (subst oblivious_modify_swap[symmetric, OF tcb_action_oblivious_schact])
  apply (rule equiv_valid_get_assert)
  apply (rule equiv_valid_guard_imp)
   apply (simp add: bind_assoc[symmetric])
   apply (rule bind_ev_general)
     apply (rule tcb_action_reads_respects_scheduler[OF domains_distinct])
    apply (simp add: bind_assoc)
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

lemma switch_to_thread_globals_equiv_scheduler[wp]:
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace> switch_to_thread thread
       \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp dxo_wp_weak arch_switch_to_thread_globals_equiv_scheduler | simp)+
  done


lemma ev_irrelevant_bind:
  assumes inv: "\<And> P. \<lbrace> P \<rbrace> f \<lbrace>\<lambda>_. P \<rbrace>"
  assumes ev: "equiv_valid I A B P g"
  shows "equiv_valid I A B P (do y \<leftarrow> f; g od)"
  proof -
    have a: "\<And>a b s. (a,b) \<in> fst (f s) \<Longrightarrow> b = s"
      apply (erule use_valid[OF _ inv])
      apply simp
    done
  show ?thesis
  apply (insert ev)
    apply (clarsimp simp add: equiv_valid_def2 equiv_valid_2_def
                              bind_def)
    apply (drule a)+
    apply clarsimp
    apply fastforce
  done
qed

lemma guarded_switch_to_thread_midstrength_reads_respects_scheduler[wp]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "midstrength_reads_respects_scheduler aag l
         (invs and pas_refined aag and
            (\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (cur_domain s)))
         (guarded_switch_to t >>= (\<lambda>_. set_scheduler_action resume_cur_thread))"
  apply (simp add: guarded_switch_to_def bind_assoc)
  apply (subst bind_assoc[symmetric])
  apply (rule ev_irrelevant_bind)
   apply (wp gts_wp | simp)+
  done

lemma arch_switch_to_idle_thread_globals_equiv_scheduler[wp]:
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace> arch_switch_to_idle_thread
       \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  unfolding arch_switch_to_idle_thread_def storeWord_def
  by (wp dmo_wp modify_wp thread_get_wp' arch_switch_to_thread_globals_equiv_scheduler')

lemma switch_to_idle_thread_globals_equiv_scheduler[wp]:
  "\<lbrace>invs and globals_equiv_scheduler sta\<rbrace> switch_to_idle_thread
       \<lbrace>\<lambda>_. globals_equiv_scheduler sta\<rbrace>"
  apply (simp add: switch_to_idle_thread_def)
  apply (wp | simp)+
  done

crunch cur_domain[wp]: guarded_switch_to,arch_switch_to_idle_thread,choose_thread
                       "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps simp: crunch_simps)

crunch domain_fields[wp]: guarded_switch_to,arch_switch_to_idle_thread, choose_thread
                          "domain_fields P"
  (wp: crunch_wps simp: crunch_simps)

lemma gets_evrv':
  "equiv_valid_rv I A B R (K (\<forall>s t. I s t \<and> A s t  \<longrightarrow> R (f s) (f t) \<and> B s t)) (gets f)"
  apply (auto simp: equiv_valid_2_def in_monad)
  done

lemma gets_ev_no_inv:
  shows "equiv_valid I A B (\<lambda> s. \<forall> s t. I s t \<and> A s t  \<longrightarrow> f s = f t \<and> B s t) (gets f)"
  apply (simp add: equiv_valid_def2)
  apply (auto intro: equiv_valid_rv_guard_imp[OF gets_evrv'])
  done

lemma switch_to_idle_thread_midstrength_reads_respects_scheduler[wp]:
  "midstrength_reads_respects_scheduler aag l (invs and pas_refined aag)
       (switch_to_idle_thread >>= (\<lambda>_. set_scheduler_action resume_cur_thread))"
  apply (simp add: switch_to_idle_thread_def)
  apply (rule equiv_valid_guard_imp)
   apply (simp add: arch_switch_to_idle_thread_def bind_assoc double_gets_drop_regets)
   apply (rule bind_ev_general)
   apply (rule bind_ev_general)
       apply (rule store_cur_thread_midstrength_reads_respects)
      apply (rule_tac P="\<top>" and P'="\<top>" in equiv_valid_inv_unobservable)
          apply (rule hoare_pre)
           apply (rule scheduler_equiv_lift'[where P=\<top>])
                apply (wp globals_equiv_scheduler_inv silc_dom_lift  | simp)+
         apply (wp midstrength_scheduler_affects_equiv_unobservable set_vm_root_states_equiv_for
               | simp)+
        apply (wp cur_thread_update_not_subject_reads_respects_scheduler
              | assumption | simp | fastforce)+
  apply (clarsimp simp: scheduler_equiv_def)
  done

lemma gets_read_queue_ev_from_weak_sae:
  "(\<forall>s t. B s t \<longrightarrow> weak_scheduler_affects_equiv aag l s t)
    \<Longrightarrow> equiv_valid_inv R B
        (\<lambda>s. pasDomainAbs aag d \<inter> reads_scheduler aag l \<noteq> {}) (gets (\<lambda>s. f (ready_queues s d)))"
  apply (rule equiv_valid_guard_imp)
  apply wp
  apply (force simp: weak_scheduler_affects_equiv_def states_equiv_for_def
                     equiv_for_def)
  done

lemma gets_read_queue_reads_respects_scheduler[wp]:
  "weak_reads_respects_scheduler aag l
    (\<lambda>s. pasDomainAbs aag d \<inter> reads_scheduler aag l \<noteq> {}) (gets (\<lambda>s. f (ready_queues s d)))"
  by (rule gets_read_queue_ev_from_weak_sae, simp)

lemma gets_ready_queue_midstrength_equiv_scheduler[wp]:
  "equiv_valid_inv (scheduler_equiv aag) (midstrength_scheduler_affects_equiv aag l)
     (\<lambda>s. pasDomainAbs aag d \<inter> reads_scheduler aag l \<noteq> {})
     (gets (\<lambda>s. f (ready_queues s d)))"
  by (rule gets_read_queue_ev_from_weak_sae, auto)

lemma gets_cur_domain_reads_respects_scheduler[wp]:
  "equiv_valid (scheduler_equiv aag) A A \<top> (gets cur_domain)"
  apply (rule equiv_valid_guard_imp)
  apply wp
  apply (clarsimp simp add: scheduler_equiv_def states_equiv_for_def
                            equiv_for_def domain_fields_equiv_def)
  done


lemma any_valid_thread:
  "queues p \<noteq> [] \<Longrightarrow> (\<And>x prio. x \<in> set (queues prio) \<Longrightarrow> P x)
   \<Longrightarrow> P (hd (max_non_empty_queue queues))"
  apply (simp add: max_non_empty_queue_def)
  apply (rule Max_prop)
   prefer 2
   apply simp
   apply blast
  apply (drule_tac x="hd (queues (Max {prio. queues prio \<noteq> []}))" in meta_spec)
  apply (drule_tac x="Max {prio. queues prio \<noteq> []}" in meta_spec)
  apply simp
  done

lemma tcb_with_domain_at:
  "valid_queues s \<Longrightarrow> x \<in> set (ready_queues s d p) \<Longrightarrow>
   \<exists>t. ekheap s x = Some t \<and> (tcb_domain t) = d"
   apply (fastforce simp add: valid_queues_def is_etcb_at_def etcb_at_def
                   split: option.splits)
   done

lemma if_ev_bind:
  "\<lbrakk>b \<Longrightarrow> equiv_valid I A B P (f >>= s); \<not> b \<Longrightarrow> equiv_valid I A B Q (g >>= s)\<rbrakk>
   \<Longrightarrow> equiv_valid I A B (\<lambda>s. (b \<longrightarrow> P s) \<and> (\<not> b \<longrightarrow> Q s)) ((if b then f else g) >>= s)"
  apply simp
  done

lemma choose_thread_reads_respects_scheduler_cur_domain:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "midstrength_reads_respects_scheduler aag l
           (invs and pas_refined aag and valid_queues and
                (\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l \<noteq> {}))
           (choose_thread >>= (\<lambda>_. set_scheduler_action resume_cur_thread))"
  apply (simp add: choose_thread_def bind_assoc)
  apply (rule equiv_valid_guard_imp)
   apply (rule bind_ev_general)
   apply (rule bind_ev_general)
       apply (rule if_ev_bind)
        apply (rule switch_to_idle_thread_midstrength_reads_respects_scheduler)
       apply (rule guarded_switch_to_thread_midstrength_reads_respects_scheduler)
      apply wp+
  apply clarsimp
  apply (erule any_valid_thread)
  apply (frule(1) tcb_with_domain_at)
  apply clarsimp
  apply (frule(1) tcb_domain_wellformed)
  apply simp
  done

lemma cur_thread_update_unobservable:
  "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
        scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain s = cur_domain st)\<rbrace>
     modify (cur_thread_update (\<lambda>_. thread))
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply wp
  apply (clarsimp simp  add: scheduler_affects_equiv_def scheduler_equiv_def
                   domain_fields_equiv_def)
  done


lemma arch_switch_to_idle_thread_unobservable:
  "\<lbrace>(\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l = {}) and
        scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and invs\<rbrace>
     arch_switch_to_idle_thread
   \<lbrace>\<lambda>rv s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply wp
  apply (clarsimp simp add: scheduler_equiv_def domain_fields_equiv_def
                   invs_def valid_state_def)
  done


lemma switch_to_idle_thread_unobservable:
  "\<lbrace>(\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l = {}) and
        scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain s = cur_domain st) and invs\<rbrace>
      switch_to_idle_thread
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: switch_to_idle_thread_def)
  apply (wp cur_thread_update_unobservable arch_switch_to_idle_thread_unobservable)
  apply (clarsimp simp add: scheduler_equiv_def domain_fields_equiv_def)
  done

lemma clearExMonitor_unobservable:
  "\<lbrace>(\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l = {}) and
         scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain s = cur_domain st)\<rbrace>
      do_machine_op clearExMonitor
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: clearExMonitor_def)
  apply (rule hoare_pre)
   apply (wp dmo_wp modify_wp)
  apply (clarsimp simp add: states_equiv_for_def
                            scheduler_affects_equiv_def equiv_for_def
                            equiv_asids_def equiv_asid_def
                            scheduler_globals_frame_equiv_def
                            silc_dom_equiv_def)
  done

lemma arch_switch_to_thread_unobservable:
  "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
         scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s) and invs\<rbrace>
      arch_switch_to_thread t
   \<lbrace>\<lambda>rv s. scheduler_affects_equiv aag l st s\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply (wp set_vm_root_scheduler_affects_equiv clearExMonitor_unobservable | simp)+
  done

lemma tcb_sched_action_unobservable:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "\<lbrace>pas_refined aag and scheduler_affects_equiv aag l st and
        (\<lambda>s. pasObjectAbs aag t \<notin> reads_scheduler aag l)\<rbrace>
      tcb_sched_action f t
   \<lbrace>\<lambda>rv. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (clarsimp simp add: etcb_at_def split: option.splits)
  apply (clarsimp simp: scheduler_affects_equiv_def states_equiv_for_def
                        equiv_for_def equiv_asids_def equiv_asid_def)
  apply (rule ext)
  apply clarsimp
  apply (frule(1) tcb_domain_wellformed)
  apply (metis domains_distinct[THEN pas_domains_distinct_inj])
  done


lemma switch_to_thread_unobservable:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
         (\<lambda>s. pasObjectAbs aag t \<notin> reads_scheduler aag l) and
         scheduler_affects_equiv aag l st and scheduler_equiv aag st and invs and pas_refined aag\<rbrace>
      switch_to_thread t
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp cur_thread_update_unobservable arch_switch_to_idle_thread_unobservable
            tcb_sched_action_unobservable arch_switch_to_thread_unobservable)
  apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)
  done

lemma choose_thread_reads_respects_scheduler_other_domain:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l ( invs and pas_refined aag and valid_queues and
              (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s))
              choose_thread"
  apply (rule reads_respects_scheduler_unobservable''[
                      where P'="\<lambda>s. \<not> reads_scheduler_cur_domain aag l s \<and>
                                    invs s \<and> pas_refined aag s \<and> valid_queues s"])
  apply (rule hoare_pre)
     apply (rule scheduler_equiv_lift'[where P="invs"])
          apply (simp add: choose_thread_def)
          apply (wp guarded_switch_to_lift silc_dom_lift | simp)+
    apply force

   apply (simp add: choose_thread_def)
   apply (wp guarded_switch_to_lift switch_to_idle_thread_unobservable
             switch_to_thread_unobservable | simp)+
   apply clarsimp
   apply (intro impI conjI)
    apply (simp add: scheduler_equiv_def domain_fields_equiv_def)
   apply (elim exE)
   apply (erule any_valid_thread)
   apply (frule(1) tcb_with_domain_at)
   apply clarsimp
   apply (frule(1) tcb_domain_wellformed)
   apply (force simp: disjoint_iff_not_equal)
  apply simp
  done

lemma equiv_valid_cases':
  "(\<And>s t. A s t \<Longrightarrow> I s t \<Longrightarrow> P s = P t) \<Longrightarrow> equiv_valid I A B (R and P) f
   \<Longrightarrow> equiv_valid I A B ((\<lambda>s. \<not>P s) and R) f
   \<Longrightarrow> equiv_valid I A B R f"
  apply (simp add: equiv_valid_def2 equiv_valid_2_def)
  apply fastforce
  done

lemmas equiv_valid_cases = equiv_valid_cases'[rotated]


lemma choose_thread_reads_respects_scheduler:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "midstrength_reads_respects_scheduler aag l (invs and pas_refined aag and valid_queues)
                       (choose_thread >>= (\<lambda>_. set_scheduler_action resume_cur_thread))"
  apply (rule equiv_valid_cases[
                      where P="\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l \<noteq> {}"])
    apply (rule equiv_valid_guard_imp)
     apply (rule choose_thread_reads_respects_scheduler_cur_domain[OF domains_distinct])
    apply simp
   apply (rule equiv_valid_guard_imp)
    apply (rule midstrength_cur_domain_unobservable)
    apply (rule equiv_valid_guard_imp)
     apply (wp choose_thread_reads_respects_scheduler_other_domain | simp)+
    apply force
   apply (clarsimp simp: reads_lrefl)
  apply (simp add: scheduler_equiv_def domain_fields_equiv_def)
  done


lemma next_domain_midstrength_equiv_scheduler:
  "equiv_valid (scheduler_equiv aag) (weak_scheduler_affects_equiv aag l)
               (midstrength_scheduler_affects_equiv aag l) \<top>
               next_domain"
  apply (simp add: next_domain_def)
  apply (rule ev_modify)
  apply (clarsimp simp add: scheduler_equiv_def Let_def
                            domain_fields_equiv_def globals_equiv_scheduler_def
                            silc_dom_equiv_def equiv_for_def
                            weak_scheduler_affects_equiv_def
                            midstrength_scheduler_affects_equiv_def
                            states_equiv_for_def equiv_asids_def
                            equiv_asid_def idle_equiv_def)
  done


lemma ev_weaken_pre_relation:
  "equiv_valid I A B P f \<Longrightarrow> (\<And>s t. A' s t \<Longrightarrow> A s t) \<Longrightarrow> equiv_valid I A' B P f"
  apply (clarsimp simp add: equiv_valid_def2 equiv_valid_2_def)
  apply fastforce
  done


lemma weak_scheduler_affects_equiv[intro]:
  "scheduler_affects_equiv aag l st s \<Longrightarrow> weak_scheduler_affects_equiv aag l st s"
  apply (simp add: scheduler_affects_equiv_def weak_scheduler_affects_equiv_def)
  done

lemma midstrength_scheduler_affects_equiv[intro]:
  "scheduler_affects_equiv aag l st s  \<Longrightarrow> midstrength_scheduler_affects_equiv aag l st s"
  apply (simp add: scheduler_affects_equiv_def midstrength_scheduler_affects_equiv_def)
  done

lemma next_domain_snippit:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l (invs and pas_refined aag and valid_queues)
      (do
        dom_time \<leftarrow> gets domain_time;
        y \<leftarrow> when (dom_time = 0) next_domain;
        y\<leftarrow> choose_thread;
        set_scheduler_action resume_cur_thread
       od)"
  apply (simp add: when_def)
  apply (rule bind_ev_pre)
     apply (rule bind_ev_general)
       apply (simp add: when_def)
       apply (rule choose_thread_reads_respects_scheduler[OF domains_distinct])
      apply (wp next_domain_midstrength_equiv_scheduler)
       apply (rule ev_weaken_pre_relation)
        apply (rule next_domain_midstrength_equiv_scheduler)
       apply fastforce
      apply (rule ev_weaken_pre_relation)
       apply wp
      apply fastforce
     apply (wp next_domain_valid_queues)+
  apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)
  done

lemma schedule_choose_new_thread_read_respects_scheduler:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l (invs and pas_refined aag and valid_queues)
     schedule_choose_new_thread"
  unfolding schedule_choose_new_thread_def
  by (simp add: next_domain_snippit[OF domains_distinct])

lemma get_thread_state_reads_respects_scheduler:
  "reads_respects_scheduler aag l
     ((\<lambda>s. st_tcb_at \<top> rv s \<longrightarrow>
             pasObjectAbs aag rv \<in> reads_scheduler aag l \<or> rv = idle_thread s)
      and valid_idle)
     (get_thread_state rv)"
  apply (clarsimp simp add: get_thread_state_def thread_get_def gets_the_def
                   gets_def get_def assert_opt_def get_tcb_def
                   bind_def return_def fail_def
                   valid_idle_def pred_tcb_at_def
                   obj_at_def
                   equiv_valid_def2 equiv_valid_2_def
                  split: option.splits kernel_object.splits
                   )
  apply (clarsimp simp add: scheduler_equiv_def)
  apply (elim disjE,simp_all)
  apply (clarsimp simp: scheduler_affects_equiv_def
                        states_equiv_for_def equiv_for_def)
  done

lemma get_cur_thread_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l
     (\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l \<noteq> {})
     (gets cur_thread)"
  by (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def
                     domain_fields_equiv_def gets_def get_def bind_def return_def
                     equiv_valid_def2 equiv_valid_2_def)

lemma get_scheduler_action_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l ( (\<lambda>s. pasDomainAbs aag (cur_domain s) \<inter> reads_scheduler aag l \<noteq> {}))
                            (gets scheduler_action)"
  by (clarsimp simp: scheduler_equiv_def scheduler_affects_equiv_def
                     domain_fields_equiv_def gets_def get_def bind_def return_def
                     equiv_valid_def2 equiv_valid_2_def)

lemma switch_to_cur_domain:
  "\<lbrakk>valid_sched s; scheduler_action s = switch_thread x; pas_refined aag s\<rbrakk>
    \<Longrightarrow> pasObjectAbs aag x \<in> pasDomainAbs aag (cur_domain s)"
    apply (clarsimp simp add: valid_sched_def
                              valid_sched_action_def
                              switch_in_cur_domain_def
                              in_cur_domain_def etcb_at_def
                              weak_valid_sched_action_def
                              is_etcb_at_def st_tcb_at_def
                              obj_at_def
                              valid_etcbs_def)
    apply (drule_tac x=x in spec)
    apply clarsimp
    apply (drule(1) tcb_domain_wellformed)
    apply simp
    done

lemma equiv_valid_dc:
  assumes a:"(\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>)"
  assumes b:"(\<And>P. \<lbrace>P\<rbrace> f' \<lbrace>\<lambda>_. P\<rbrace>)"
  shows "equiv_valid_2 I A A dc P P' f f'"
  apply (clarsimp simp add: equiv_valid_2_def)
  apply (erule use_valid[OF _ a])
  apply (erule use_valid[OF _ b])
  apply simp
  done



lemma equiv_valid_2_unobservable:
  assumes fI: "\<And>st. \<lbrace>P and I st and A st\<rbrace> f \<lbrace>\<lambda>_. I st\<rbrace>"
  assumes fA: "\<And>st. \<lbrace>P' and I st and A st\<rbrace> f \<lbrace>\<lambda>_. A st\<rbrace>"
  assumes gI: "\<And>st. \<lbrace>S and I st and A st\<rbrace> g \<lbrace>\<lambda>_. I st\<rbrace>"
  assumes gA: "\<And>st. \<lbrace>S' and I st and A st\<rbrace> g \<lbrace>\<lambda>_. A st\<rbrace>"
  assumes sym: "\<forall>s s'. I s s' \<and> A s s' \<longrightarrow> I s' s \<and> A s' s"
  assumes trans: "\<forall>s s' s''. I s s' \<and> A s s' \<longrightarrow> I s' s'' \<and> A s' s'' \<longrightarrow> I s s'' \<and> A s s''"
  shows "equiv_valid_2 I A A dc (P and P') (S and S') (f:: 'a \<Rightarrow> (unit \<times> 'a) set \<times> bool) g"
  apply (clarsimp simp add: equiv_valid_def spec_equiv_valid_def equiv_valid_2_def)
  apply (erule preserves_equivalence_2_weak,assumption)
       apply (rule hoare_pre)
        apply (rule hoare_vcg_conj_lift)
         apply (rule fI)
        apply (rule fA)
       apply force
       apply (rule hoare_pre)
       apply (rule hoare_vcg_conj_lift)
       apply (rule gI)
       apply (rule gA)
       apply force
      apply (fastforce intro!: sym trans)+
  done


lemma equiv_valid_2:
  "equiv_valid I A B P f \<Longrightarrow> equiv_valid_rv I A B (=) P f"
  apply (simp add: equiv_valid_def2)
  done

lemma ev_gets_const:
  "equiv_valid_inv I A (\<lambda>s. f s = x) (gets f)"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def
                        gets_def get_def bind_def return_def)
  done


lemma reads_respects_scheduler_invisible_domain_switch:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l
     (\<lambda>s. pas_refined aag s \<and> invs s \<and> valid_queues s \<and> guarded_pas_domain aag s
          \<and> domain_time s = 0 \<and> scheduler_action s = choose_new_thread
          \<and> \<not> reads_scheduler_cur_domain aag l s)
     schedule"
  apply (rule equiv_valid_guard_imp)
   apply (simp add: schedule_def)
   apply (simp add: equiv_valid_def2)
   apply (rule equiv_valid_rv_bind[where W=dc])
     apply (rule equiv_valid_dc)
      apply wp
     apply wp
    apply (rule equiv_valid_2_bind_pre[where R'=dc])
         apply (rule equiv_valid_2_bind_pre[where R'="(=)"])
              apply simp
              apply (rule_tac P="rv'b = choose_new_thread" in  EquivValid.gen_asm_ev2_l)
              apply simp
              apply (rule equiv_valid_2_bind_pre)
                   apply (rule equiv_valid_2)
                   apply (rule schedule_choose_new_thread_read_respects_scheduler[OF domains_distinct])
                  apply (rule_tac P="\<top>" and
                                  P'="pas_refined aag and
                                     (\<lambda>s. (runnable rva \<longrightarrow>
                                              (pasObjectAbs aag rv \<notin> reads_scheduler aag l)))" and
                                  S="\<top>" and
                                  S'="pas_refined aag and
                                     (\<lambda>s. (runnable rv'a \<longrightarrow>
                                               pasObjectAbs aag rv' \<notin> reads_scheduler aag l))"
                           in equiv_valid_2_unobservable)
                       apply wp
                        apply (rule scheduler_equiv_lift)
                             apply wp+
                       apply simp
                      apply clarsimp
                      apply wp
                       apply (wp tcb_sched_action_unobservable)
                      apply clarsimp
                     apply (wp scheduler_equiv_lift)+
                           apply (wp | simp)+
                     apply (wp tcb_sched_action_unobservable)+
                    apply simp
                   apply (fastforce+)[2]
                 apply wp+
               apply (force+)[2]
             apply (rule equiv_valid_2)
             apply (rule ev_gets_const)
            apply wp+
          apply (force+)[2]
        apply (rule equiv_valid_dc)
         apply wp
        apply wp
       apply (wp gts_wp)+
     apply (force+)[2]
   apply wp
  apply clarsimp
  apply (intro impI conjI allI; (rule TrueI refl)?)
   apply (simp add: guarded_pas_domain_def)
   apply (subgoal_tac "cur_thread s \<noteq> idle_thread s")
    apply (force simp: disjoint_iff_not_equal)
   apply (clarsimp simp add: pred_tcb_at_def obj_at_def valid_state_def
                              valid_idle_def invs_def)+
  done

crunch globals_equiv_scheduler[wp]: schedule "(\<lambda>s:: det_state. globals_equiv_scheduler st s)"
  (   wp: guarded_switch_to_lift crunch_wps hoare_drop_imps
  wp_del: ethread_get_wp
  ignore: guarded_switch_to
    simp: crunch_simps)

lemma schedule_no_domain_switch:
  "\<lbrace>(\<lambda>s. domain_time s \<noteq> 0) and (\<lambda>s. Q (cur_domain s))\<rbrace> schedule \<lbrace>\<lambda>r s. Q (cur_domain s)\<rbrace>"
  unfolding schedule_def
  supply ethread_get_wp[wp del]
  apply (wpsimp wp: hoare_drop_imps simp: if_apply_def2
         | simp add: schedule_choose_new_thread_def
         | wpc
         | rule hoare_pre_cont[where a=next_domain] )+
  done

lemma when_next_domain_domain_fields:
  "\<lbrace>\<lambda>s. \<not> B \<and>  domain_fields Q s \<rbrace> when B next_domain \<lbrace> \<lambda>_. domain_fields Q \<rbrace>"
  by (wpsimp | rule hoare_pre_cont[where a=next_domain])+

lemma schedule_no_domain_fields:
  "\<lbrace>(\<lambda>s. domain_time s \<noteq> 0) and domain_fields Q\<rbrace> schedule \<lbrace>\<lambda>_. domain_fields Q\<rbrace>"
  unfolding schedule_def
  supply ethread_get_wp[wp del]
  apply (wpsimp wp: hoare_drop_imps simp: if_apply_def2
         | simp add: schedule_choose_new_thread_def
         | wpc
         | rule hoare_pre_cont[where a=next_domain] )+
  done

lemma set_scheduler_action_unobservable:
  "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
          scheduler_affects_equiv aag l st and (\<lambda>s. cur_domain st = cur_domain s)\<rbrace>
      set_scheduler_action a
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: set_scheduler_action_def)
  apply wp
  apply (clarsimp simp add: scheduler_affects_equiv_def
                   scheduler_equiv_def domain_fields_equiv_def)
  done

lemma choose_thread_unobservable:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
         scheduler_affects_equiv aag l st and invs and valid_queues and pas_refined aag and
         scheduler_equiv aag st\<rbrace>
      choose_thread
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: choose_thread_def)
  apply (wp switch_to_idle_thread_unobservable guarded_switch_to_lift
            switch_to_thread_unobservable)
  apply (simp add: scheduler_affects_equiv_def
                   scheduler_equiv_def domain_fields_equiv_def)
  apply (intro impI conjI)
  apply (elim conjE exE)
  apply (erule any_valid_thread)
  apply (frule(1) tcb_with_domain_at)
  apply clarsimp
  apply (frule(1) tcb_domain_wellformed)
  apply (force simp: disjoint_iff_not_equal)
  done

lemma tcb_sched_action_scheduler_equiv[wp]:
  "\<lbrace>scheduler_equiv aag st\<rbrace> tcb_sched_action f a\<lbrace>\<lambda>_. scheduler_equiv aag st\<rbrace>"
  by (rule scheduler_equiv_lift; wp)

lemma cur_thread_cur_domain:
  "\<lbrakk>st_tcb_at ((=) st) (cur_thread s) s; \<not> idle st; invs s; guarded_pas_domain aag s\<rbrakk>
    \<Longrightarrow> pasObjectAbs aag (cur_thread s) \<in> pasDomainAbs aag (cur_domain s)"
  apply (clarsimp simp add: pred_tcb_at_def invs_def valid_idle_def
                            valid_state_def
                            obj_at_def guarded_pas_domain_def)
  done

lemma sched_equiv_cur_domain[intro]:
  "scheduler_equiv aag st s \<Longrightarrow> cur_domain st = cur_domain s"
  apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)
  done

lemma valid_sched_valid_queues[intro]:
  "valid_sched s \<Longrightarrow> valid_queues s"
  apply (simp add: valid_sched_def)
  done

lemma ethread_get_wp2:
  "\<lbrace>\<lambda>s. \<forall>etcb. etcb_at ((=) etcb) t s \<longrightarrow> Q (f etcb) s\<rbrace> ethread_get f t \<lbrace>Q\<rbrace>"
  apply wp
  apply (clarsimp simp: etcb_at_def split: option.split)
  done

lemma switch_thread_runnable:
  "\<lbrakk> valid_sched s ; scheduler_action s = switch_thread t \<rbrakk> \<Longrightarrow> st_tcb_at runnable t s"
  unfolding valid_sched_def valid_sched_action_def weak_valid_sched_action_def
  by clarsimp

lemma schedule_choose_new_thread_schedule_affects_no_switch:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>\<lambda>s. invs s \<and> pas_refined aag s \<and> valid_queues s \<and> domain_time s \<noteq> 0
        \<and> \<not> reads_scheduler_cur_domain aag l s
        \<and> scheduler_affects_equiv aag l st s \<and> scheduler_equiv aag st s
        \<and> cur_domain st = cur_domain s \<rbrace>
     schedule_choose_new_thread
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st \<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (wp set_scheduler_action_unobservable choose_thread_unobservable
            hoare_pre_cont[where a=next_domain])
  apply clarsimp
  done

lemma reads_respects_scheduler_invisible_no_domain_switch:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l
    (\<lambda>s. pas_refined aag s \<and> invs s \<and> valid_sched s \<and> guarded_pas_domain aag s
         \<and> domain_time s \<noteq> 0 \<and> \<not> reads_scheduler_cur_domain aag l s)
    schedule"
  supply ethread_get_wp[wp del]
  supply if_split[split del]
  apply (rule reads_respects_scheduler_unobservable''[where P=Q and P'=Q and Q=Q for Q])
  apply (rule hoare_pre)
     apply (rule scheduler_equiv_lift'[where P="invs and (\<lambda>s. domain_time s \<noteq> 0)"])
          apply (wp schedule_no_domain_switch schedule_no_domain_fields
                    silc_dom_lift | simp)+
   apply (simp add: schedule_def)
   apply (wp guarded_switch_to_lift
             scheduler_equiv_lift
             schedule_choose_new_thread_schedule_affects_no_switch
             set_scheduler_action_unobservable
             tcb_sched_action_unobservable
             switch_to_thread_unobservable silc_dom_lift
             gts_wp
             hoare_vcg_all_lift
             hoare_vcg_disj_lift
          | wpc | simp
          | rule hoare_pre_cont[where a=next_domain]
          | wp (once) hoare_drop_imp[where f="set_scheduler_action choose_new_thread"])+
            (* stop on fastfail calculation *)
            apply (clarsimp simp: conj_ac cong: imp_cong conj_cong)
            apply (wp hoare_drop_imps)[1]
           apply (wp tcb_sched_action_unobservable gts_wp
                     schedule_choose_new_thread_schedule_affects_no_switch)+
   apply (clarsimp simp: if_apply_def2)
   (* slow 15s *)
   by (safe
      ; (fastforce simp: switch_thread_runnable
        | fastforce dest!: switch_to_cur_domain cur_thread_cur_domain
        | fastforce simp: st_tcb_at_def obj_at_def))+

lemma read_respects_scheduler_switch_thread_case:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l
    (invs and valid_queues and (\<lambda>s. scheduler_action s = switch_thread t)
      and valid_sched_action and pas_refined aag)
    (do tcb_sched_action tcb_sched_enqueue t;
        set_scheduler_action choose_new_thread;
        schedule_choose_new_thread
    od)"
  unfolding schedule_choose_new_thread_def
  apply (rule equiv_valid_guard_imp)
   apply simp
   apply (rule bind_ev)
     apply (rule bind_ev)
       apply (rule next_domain_snippit[OF domains_distinct])
      apply wp[1]
     apply (simp add: pred_conj_def)
     apply (rule hoare_vcg_conj_lift)
      apply (rule set_scheduler_action_extended.invs)
     apply (wp tcb_action_reads_respects_scheduler)+
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def)
  done

lemma read_respects_scheduler_switch_thread_case_app:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l
    (invs and valid_queues and (\<lambda>s. scheduler_action s = switch_thread t)
      and valid_sched_action and pas_refined aag)
    (do tcb_sched_action tcb_sched_append t;
        set_scheduler_action choose_new_thread;
        schedule_choose_new_thread
    od)"
  unfolding schedule_choose_new_thread_def
  apply (rule equiv_valid_guard_imp)
   apply simp
   apply (rule bind_ev)
     apply (rule bind_ev)
       apply (rule next_domain_snippit[OF domains_distinct])
      apply wp[1]
     apply (simp add: pred_conj_def)
     apply (rule hoare_vcg_conj_lift)
      apply (rule set_scheduler_action_extended.invs)
     apply (wp tcb_action_reads_respects_scheduler)+
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def)
  done

lemma gets_highest_prio_ev_from_weak_sae:
  "(\<forall>s t. B s t \<longrightarrow> weak_scheduler_affects_equiv aag l s t)
    \<Longrightarrow> equiv_valid_inv R B
        (\<lambda>s. pasDomainAbs aag d \<inter> reads_scheduler aag l \<noteq> {}) (gets (\<lambda>s. is_highest_prio d p s))"
  apply (simp add: is_highest_prio_def)
  apply (erule gets_read_queue_ev_from_weak_sae)
  done

lemma etcb_in_domains_of_state:
  "\<lbrakk> is_etcb_at tcb_ptr s;
     etcb_at (\<lambda>t. tcb_domain t = tcb_dom) tcb_ptr s \<rbrakk>
   \<Longrightarrow> (tcb_ptr, tcb_dom) \<in> domains_of_state s"
  by (auto simp: domains_of_state_aux.simps is_etcb_at_def etcb_at_def)

lemma guarded_active_ct_cur_domain:
  "\<lbrakk>guarded_pas_domain aag s; ct_active s; invs s\<rbrakk> \<Longrightarrow>
  pasObjectAbs aag (cur_thread s) \<in> pasDomainAbs aag (cur_domain s)"
  apply (fastforce simp add: guarded_pas_domain_def invs_def valid_state_def valid_idle_def
                   ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma schedule_reads_respects_scheduler_cur_domain:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l
        (invs and pas_refined aag and valid_sched
         and guarded_pas_domain aag and
        (\<lambda>s. reads_scheduler_cur_domain aag l s)) schedule"
  supply ethread_get_wp[wp del]
  apply (simp add: schedule_def schedule_switch_thread_fastfail_def)
  apply (rule equiv_valid_guard_imp)
   apply (rule bind_ev)+
         apply wpc
           (* resume current thread *)
           apply wp[1]
          prefer 2
          (* choose new thread *)
          apply (rule bind_ev)
            apply (rule schedule_choose_new_thread_read_respects_scheduler[OF domains_distinct])
           apply ((wpsimp wp: when_ev gts_wp get_thread_state_reads_respects_scheduler)+)[2]
         (* switch thread *)
         apply (rule bind_ev)+
                       apply (rule if_ev)
                        apply (rule read_respects_scheduler_switch_thread_case[OF domains_distinct])
                       apply (rule if_ev)
                        apply (rule read_respects_scheduler_switch_thread_case_app[OF domains_distinct])
                       apply simp
                       apply (rule ev_weaken_pre_relation)
                        apply (rule guarded_switch_to_thread_midstrength_reads_respects_scheduler[OF domains_distinct])
                       apply fastforce
                      apply (rule gets_highest_prio_ev_from_weak_sae)
                      apply fastforce
                     apply ((wpsimp wp: when_ev gts_wp get_thread_state_reads_respects_scheduler
                                        ethread_get_when_reads_respects_scheduler
                                        hoare_vcg_all_lift
                            | wp (once) hoare_vcg_conj_lift hoare_drop_imps)+)+
  (* TODO: cleanup *)
  apply (intro impI conjI allI
         ; (fastforce simp: guarded_pas_domain_def valid_sched_def
                      dest: st_tcb_at_idle_thread switch_to_cur_domain)?
         ; (fastforce simp: guarded_pas_domain_def scheduler_equiv_def st_tcb_at_def obj_at_def
                            switch_to_cur_domain reads_lrefl)?
         ; (fastforce simp: guarded_pas_domain_def scheduler_equiv_def st_tcb_at_def obj_at_def
                            switch_to_cur_domain valid_sched_def reads_scheduler_def
                      split: if_splits
                      dest: domains_distinct[THEN pas_domains_distinct_inj])?)

   (* Last remaining goal is more fiddly (duplicated modulo "runnable st")
      We are switching to a new thread but still in the current domain.
      By the domains_distinct condition, we must remain in the current label as well
    *)
   (* slow 5s *)
   by (fastforce simp: guarded_pas_domain_def pas_refined_def reads_scheduler_def
                       tcb_domain_map_wellformed_aux_def
                       valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                       switch_in_cur_domain_def in_cur_domain_def
                 intro: etcb_in_domains_of_state tcb_at_is_etcb_at st_tcb_at_tcb_at
                 dest: domains_distinct[THEN pas_domains_distinct_inj]
                 split: if_splits prod.splits)+

definition tick_done where
"tick_done s \<equiv> domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread"

lemma schedule_reads_respects_scheduler:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l
          (invs and pas_refined aag and valid_sched and
           guarded_pas_domain aag and tick_done) schedule"
  apply (rule_tac P="\<lambda>s. reads_scheduler_cur_domain aag l s"
               in equiv_valid_cases)
    apply (rule equiv_valid_guard_imp)
     apply (rule schedule_reads_respects_scheduler_cur_domain[OF domains_distinct])
    apply simp
   apply (rule_tac P="\<lambda>s. domain_time s = 0" in equiv_valid_cases)
     apply (rule equiv_valid_guard_imp)
      apply (rule reads_respects_scheduler_invisible_domain_switch[OF domains_distinct])
     apply (clarsimp simp: tick_done_def valid_sched_def)
    apply (rule equiv_valid_guard_imp)
     apply (rule reads_respects_scheduler_invisible_no_domain_switch[OF domains_distinct])
    apply simp
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)+
  done

lemma reschedule_required_scheduler_equiv[wp]:
  "\<lbrace>scheduler_equiv aag st\<rbrace> reschedule_required \<lbrace>\<lambda>_. scheduler_equiv aag st\<rbrace>"
  apply (simp add: reschedule_required_def)
  apply (wp scheduler_equiv_lift | wpc | simp)+
  done

lemma switch_to_cur_domain':
  "\<lbrakk>valid_etcbs s; valid_sched_action s; scheduler_action s = switch_thread x; pas_refined aag s\<rbrakk>
    \<Longrightarrow> pasObjectAbs aag x \<in> pasDomainAbs aag (cur_domain s)"
  apply (clarsimp simp add: valid_sched_def
                            valid_sched_action_def
                            switch_in_cur_domain_def
                            in_cur_domain_def etcb_at_def
                            weak_valid_sched_action_def
                            is_etcb_at_def st_tcb_at_def
                            obj_at_def
                            valid_etcbs_def)
  apply (drule_tac x=x in spec)
  apply clarsimp
  apply (drule(1) tcb_domain_wellformed)
  apply simp
  done

lemma reschedule_required_scheduler_affects_equiv_unobservable[wp]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>pas_refined aag and
          (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
          valid_queues and
          valid_etcbs and
          valid_sched_action and
          scheduler_equiv aag st and
          scheduler_affects_equiv aag l st\<rbrace>
         reschedule_required \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: reschedule_required_def)
  apply (wp set_scheduler_action_unobservable
              tcb_sched_action_unobservable
          | wpc | simp)+
  apply ((fastforce intro!: valid_sched_valid_queues
                     dest!: switch_to_cur_domain' cur_thread_cur_domain)+)
  done

lemma reads_respects_scheduler_cases':
  assumes b: "reads_respects_scheduler aag l P' (f t)"
  assumes b': "\<And>s. Q s \<Longrightarrow> reads_scheduler_cur_domain aag l s \<Longrightarrow> P' s"
  assumes c: "reads_respects_scheduler aag l P'' (f t)"
  assumes c': "\<And>s. Q s \<Longrightarrow> \<not> reads_scheduler_cur_domain aag l s \<Longrightarrow> P'' s"
  shows "reads_respects_scheduler aag l Q (f t)"
  apply (rule_tac P="\<lambda>s. reads_scheduler_cur_domain aag l s"
               in equiv_valid_cases)
    apply (rule equiv_valid_guard_imp)
     apply (rule b)
    apply (simp add: b')
   apply (rule equiv_valid_guard_imp)
    apply (rule c)
   apply (simp add: c')
  apply (simp add: scheduler_equiv_def domain_fields_equiv_def)
  done

lemma reschedule_required_reads_respects_scheduler:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l (pas_refined aag and valid_queues and valid_etcbs and
                                   valid_sched_action)
                            reschedule_required"
  apply (rule reads_respects_scheduler_cases')
    apply (simp add: reschedule_required_def)
    apply (wp | wpc)+
    apply clarsimp
    apply (rule reads_respects_scheduler_unobservable'')
    apply (wp | simp | force)+
  done



lemma dec_domain_time_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l \<top> dec_domain_time"
  apply (simp add: dec_domain_time_def)
  apply (wp ev_modify)
  apply (fastforce simp add: scheduler_equiv_def
                            domain_fields_equiv_def
                            globals_equiv_scheduler_def
                            scheduler_globals_frame_equiv_def
                            silc_dom_equiv_def
                            equiv_for_def
                            scheduler_affects_equiv_def
                            states_equiv_for_def equiv_for_def
                            equiv_asids_def equiv_asid_def idle_equiv_def)
  done

lemma ethread_set_reads_respects_scheduler:
  "reads_respects_scheduler aag l (\<lambda>s. pasObjectAbs aag t \<in> reads_scheduler aag l)
           (ethread_set f t)"
  apply (clarsimp simp add: thread_set_time_slice_def
                   ethread_set_def gets_the_def
                   gets_def get_def bind_def put_def get_etcb_def
                   return_def assert_opt_def set_eobject_def
                   fail_def equiv_valid_def2 equiv_valid_2_def
                 split: option.splits)
  apply (clarsimp simp add: scheduler_equiv_def domain_fields_equiv_def
                   globals_equiv_scheduler_def idle_equiv_def
                   )
  apply (rule conjI)
   apply (clarsimp simp: silc_dom_equiv_def reads_scheduler_def
                         equiv_for_def
                   split: if_split_asm)
  apply (simp add: scheduler_affects_equiv_def)
  apply clarsimp
  apply (rule conjI)
   apply (rule states_equiv_for_identical_ekheap_updates,assumption)
   apply (elim states_equiv_forE equiv_forE)
   apply (clarsimp simp: identical_ekheap_updates_def)
  apply (clarsimp simp: scheduler_globals_frame_equiv_def)
  done

lemma ethread_set_time_slice_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> ethread_set (tcb_time_slice_update f) t \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def)
  apply (wp)
  apply (clarsimp simp: get_etcb_def valid_sched_def
                        valid_etcbs_def is_etcb_at_def
                        valid_queues_def etcb_at'_def
                        valid_sched_action_def
                        weak_valid_sched_action_def
                        switch_in_cur_domain_def
                        ct_in_cur_domain_def
                        in_cur_domain_def)
  apply (intro impI conjI allI ballI)
  apply fastforce+
  done

lemma ethread_set_time_slice_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> ethread_set (tcb_time_slice_update f) t \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def)
  apply (wp)
  apply (clarsimp simp: get_etcb_def valid_sched_def
                        valid_etcbs_def is_etcb_at_def
                        valid_queues_def etcb_at'_def
                        valid_sched_action_def
                        weak_valid_sched_action_def
                        switch_in_cur_domain_def
                        ct_in_cur_domain_def
                        in_cur_domain_def)
  done

lemma dec_domain_time_valid_queues[wp]:
  "\<lbrace>valid_queues\<rbrace> dec_domain_time \<lbrace>\<lambda>_. valid_queues\<rbrace>"
  apply (simp add: dec_domain_time_def)
  apply (wp | simp)+
  done

lemma dec_domain_time_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> dec_domain_time \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: dec_domain_time_def)
  apply (wp | simp)+
  done

lemma dec_domain_time_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> dec_domain_time \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  apply (simp add: dec_domain_time_def)
  apply (wp | simp)+
  done


lemma timer_tick_snippit:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_scheduler aag l (pas_refined aag and valid_queues and valid_etcbs
                                                         and valid_sched_action)
                                 (when (Suc 0 < numDomains)
                                    (do x \<leftarrow> dec_domain_time;
                                        dom_time \<leftarrow> gets domain_time;
                                        when (dom_time = 0) reschedule_required
                                     od))"
  apply (rule equiv_valid_guard_imp)
   apply (wp when_ev | wp (once) hoare_drop_imps)+
       apply (clarsimp simp: scheduler_equiv_def)
       apply (wp reschedule_required_reads_respects_scheduler | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)
  done



lemma timer_tick_reads_respects_scheduler_cur_domain:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l
     (reads_scheduler_cur_domain aag l and invs and guarded_pas_domain aag and
      pas_refined aag and valid_sched)
     timer_tick"
  apply (simp add: timer_tick_def)
  apply (subst Let_def)
  apply (subst thread_set_time_slice_def)+
  apply (wp when_ev reschedule_required_reads_respects_scheduler
            ethread_set_reads_respects_scheduler
            get_thread_state_reads_respects_scheduler gts_wp
         | wpc | wp (once) hoare_drop_imps)+
  apply (fastforce simp add: invs_def valid_state_def valid_idle_def
                            pred_tcb_at_def obj_at_def guarded_pas_domain_def
                            scheduler_equiv_def domain_fields_equiv_def
                            valid_sched_def valid_sched_action_def
                  split: option.splits
                  dest: domains_distinct[THEN pas_domains_distinct_inj])
  done

lemma ethread_set_unobservable[wp]:
   "\<lbrace>(\<lambda>s. pasObjectAbs aag t \<notin> reads_scheduler aag l) and scheduler_affects_equiv aag l st\<rbrace>
       ethread_set f t
    \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: ethread_set_def set_eobject_def)
  apply wp
  apply (clarsimp simp: get_etcb_def
                        scheduler_affects_equiv_def)
  apply (elim states_equiv_forE equiv_forE)
  apply (clarsimp simp: equiv_for_def states_equiv_for_def
                        equiv_asids_def equiv_asid_def)+
  done


lemma timer_tick_reads_respects_scheduler_unobservable:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l ((\<lambda>s. \<not>reads_scheduler_cur_domain aag l s) and invs and guarded_pas_domain aag and
                                   pas_refined aag and valid_sched)
                            timer_tick"
  apply (simp add: timer_tick_def)
  apply (subst Let_def)
  apply (subst thread_set_time_slice_def)+
  apply (simp add: bind_assoc[symmetric])
  apply (rule bind_ev_pre)
     apply (simp add: bind_assoc)
     apply (rule timer_tick_snippit[OF domains_distinct])
    apply (rule_tac P=\<top> and P'="(\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and invs and guarded_pas_domain aag and
                                 pas_refined aag and valid_sched"
                 in reads_respects_scheduler_unobservable'')
      apply (rule hoare_pre)
       apply (rule scheduler_equiv_lift)
            apply (wp gts_wp tcb_sched_action_unobservable
                      scheduler_equiv_lift| wpc | simp)+
     apply (clarsimp simp: etcb_at_def split: option.splits)
     apply (intro impI conjI allI)
          apply (fastforce dest!: cur_thread_cur_domain)+
        apply ((clarsimp simp add: st_tcb_at_def obj_at_def valid_sched_def)+)[3]
     apply (fastforce dest!: cur_thread_cur_domain)
    apply force
   apply (wp gts_wp| wpc)+
  apply (clarsimp simp: etcb_at_def valid_sched_def st_tcb_at_def
                        obj_at_def valid_sched_action_def split: option.splits)
  done

lemma timer_tick_reads_respects_scheduler:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l (invs and guarded_pas_domain aag and pas_refined aag and
                                   valid_sched)
                            timer_tick"
  apply (rule reads_respects_scheduler_cases')
     apply (rule timer_tick_reads_respects_scheduler_cur_domain[OF domains_distinct])
    apply simp
   apply (rule timer_tick_reads_respects_scheduler_unobservable[OF domains_distinct])
  apply simp
  done


lemma gets_ev':
  "equiv_valid_inv I A (P and K(\<forall>s t. P s \<longrightarrow> P t \<longrightarrow> I s t \<and> A s t \<longrightarrow> f s = f t)) (gets f)"
  by (clarsimp simp: equiv_valid_def2 equiv_valid_2_def
                     gets_def get_def bind_def
                     return_def)

lemma get_irq_state_reads_respects_scheduler_trivial:
  "reads_respects_scheduler aag l (domain_sep_inv False st) (get_irq_state irq)"
  apply (simp add: get_irq_state_def)
  apply (rule equiv_valid_guard_imp)
  apply (rule_tac P="domain_sep_inv False st" in  gets_ev')
  apply clarsimp
  apply (clarsimp simp: domain_sep_inv_def)
  done


lemma resetTimer_underlying_memory[wp]:
  "\<lbrace>\<lambda>s. P(underlying_memory s)\<rbrace> resetTimer \<lbrace>\<lambda>r s. P (underlying_memory s)\<rbrace>"
  apply (simp add: resetTimer_def machine_op_lift_def machine_rest_lift_def)
  apply (wp | wpc| simp)+
  done

lemma resetTimer_irq_state[wp]:
  "\<lbrace>\<lambda>s. P(irq_state s)\<rbrace> resetTimer \<lbrace>\<lambda>r s. P (irq_state s)\<rbrace>"
  apply (simp add: resetTimer_def machine_op_lift_def machine_rest_lift_def)
  apply (wp | wpc| simp)+
  done


lemma dmo_resetTimer_underlying_memory[wp]:
  "\<lbrace>\<lambda>s. P(underlying_memory (machine_state s))\<rbrace>
      do_machine_op resetTimer
   \<lbrace>\<lambda>r s. P (underlying_memory (machine_state s))\<rbrace>"
  apply (wp dmo_wp | simp)+
  done

lemma dmo_resetTimer_arch_state[wp]:
  "\<lbrace>\<lambda>s. P(arch_state s)\<rbrace> do_machine_op resetTimer \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  by (wp dmo_wp | simp)+

lemma dmo_resetTimer_device_state[wp]:
  "\<lbrace>\<lambda>s. P( device_state (machine_state s))\<rbrace>
      do_machine_op resetTimer
   \<lbrace>\<lambda>r s. P (device_state (machine_state s))\<rbrace>"
  by (wp dmo_wp | simp)+

lemma dmo_resetTimer_exclusive_state[wp]:
  "\<lbrace>\<lambda>s. P (exclusive_state (machine_state s))\<rbrace>
      do_machine_op resetTimer
   \<lbrace>\<lambda>r s. P (exclusive_state (machine_state s))\<rbrace>"
  by (wp dmo_mol_exclusive_state | simp add: resetTimer_def)+

lemma dmo_resetTimer_reads_respects_scheduler:
  "reads_respects_scheduler aag l \<top> (do_machine_op resetTimer)"
  apply (rule reads_respects_scheduler_unobservable)
   apply (rule scheduler_equiv_lift)
        apply (simp add: globals_equiv_scheduler_def[abs_def] idle_equiv_def)
        apply (rule hoare_pre)
         apply wps
         apply wp
        apply clarsimp
       apply ((wp silc_dom_lift dmo_wp | simp)+)[5]
  apply (rule scheduler_affects_equiv_unobservable)
     apply (simp add: states_equiv_for_def[abs_def] equiv_for_def equiv_asids_def
                      equiv_asid_def)
     apply (rule hoare_pre)
  apply (wp | simp | wp dmo_wp)+
  done

lemma irq_inactive_or_timer:
  "\<lbrace>domain_sep_inv False st and Q IRQTimer and Q IRQInactive\<rbrace> get_irq_state irq \<lbrace>Q\<rbrace>"
  apply (simp add:get_irq_state_def)
  apply wp
  apply (clarsimp simp add: domain_sep_inv_def)
  apply (drule_tac x=irq in spec)
  apply (drule_tac x=a in spec) (*makes yellow variables*)
  apply (drule_tac x=b in spec)
  apply (drule_tac x=aa in spec, drule_tac x=ba in spec)
  apply clarsimp
  apply (case_tac "interrupt_states st irq")
    apply clarsimp+
  done

lemma ackInterrupt_no_irq[wp]:
  "no_irq (ackInterrupt irq)"
  apply (clarsimp simp add:no_irq_def)
  apply (wp dmo_wp ackInterrupt_irq_masks | simp add:no_irq_def)+
  done

crunch irq_state[wp]: ackInterrupt "\<lambda>s. P (irq_state s)"

lemma ackInterrupt_reads_respects_scheduler:
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
         apply (wp dmo_wp | simp add:ackInterrupt_def)+
   apply (wp mol_exclusive_state)
  apply assumption
  done



lemma handle_interrupt_reads_respects_scheduler:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l (invs and guarded_pas_domain aag and pas_refined aag and
                                   valid_sched and domain_sep_inv False st and K (irq \<le> maxIRQ))
                            (handle_interrupt irq)"
  apply (simp add: handle_interrupt_def )
  apply (rule conjI; rule impI )
   apply (rule gen_asm_ev)
   apply simp
  apply (wp modify_wp | simp )+
  apply (rule ackInterrupt_reads_respects_scheduler)
     apply (rule_tac Q="rv = IRQTimer \<or> rv = IRQInactive" in gen_asm_ev(2))
     apply (elim disjE)
      apply (wp timer_tick_reads_respects_scheduler
        ackInterrupt_reads_respects_scheduler
        dmo_resetTimer_reads_respects_scheduler
        get_irq_state_reads_respects_scheduler_trivial
        fail_ev irq_inactive_or_timer | simp )+
   apply force
  done


(*FIXME: MOVE corres-like statement for out of step equiv_valid. Move to scheduler_IF?*)
lemma equiv_valid_2_bind_right:
  "\<lbrakk>\<And>rv. equiv_valid_2 D A A R T' (Q rv) g' (g rv);
    \<lbrace>S\<rbrace> f \<lbrace>Q\<rbrace>;
    \<And>st. \<lbrace>D st and A st and S'\<rbrace> f \<lbrace>\<lambda>r. D st\<rbrace>;
    \<And>st. \<lbrace>A st and D st and S''\<rbrace> f \<lbrace>\<lambda>r. A st\<rbrace>;
    \<And>s. T s \<Longrightarrow> P s \<and> S s \<and> S' s \<and> S'' s;
    \<And>s. T' s \<Longrightarrow> P s\<rbrakk>
   \<Longrightarrow> equiv_valid_2 D A A R T' T g' (f >>= g) "
  apply atomize
  apply (clarsimp simp: equiv_valid_2_def equiv_valid_def2 valid_def bind_def)
  apply fastforce
  done

(*FIXME: Move to scheduler_IF*)
lemma reads_respects_only_scheduler:
  "reads_respects_scheduler aag SilcLabel P f \<Longrightarrow> equiv_valid_inv (scheduler_equiv aag) \<top>\<top> P f"
  by (fastforce simp: equiv_valid_def2 equiv_valid_2_def scheduler_affects_equiv_def
                      reads_scheduler_def
                      states_equiv_for_def equiv_for_def scheduler_equiv_def equiv_asids_def
                      equiv_asid_def globals_equiv_scheduler_def)

(*FIXME: MOVE do_machine_op distributing over binds/basic operations*)
lemma dmo_distr:
  "do_machine_op (f >>= g) = (do_machine_op f >>= (\<lambda>x. do_machine_op (g x)))"
  apply (clarsimp simp: do_machine_op_def bind_assoc)
  apply (clarsimp simp: gets_def simpler_modify_def select_f_def
                  bind_def get_def return_def)
  apply (rule ext)
  apply safe
      apply ((clarsimp, force)+)[5]
  apply (simp add: image_def)
  done

lemma dmo_if_distr:
  "do_machine_op (if A then f else g) = (if A then (do_machine_op f) else (do_machine_op g))"
  apply simp
  done

lemma dmo_gets_distr:
  "do_machine_op (gets f) = (gets (\<lambda>s. f (machine_state s)))"
  apply (clarsimp simp: do_machine_op_def bind_assoc)
  apply (clarsimp simp: gets_def simpler_modify_def select_f_def
                  bind_def get_def return_def)
  done

lemma dmo_modify_distr:
  "do_machine_op (modify f) = modify (machine_state_update f)"
  apply (clarsimp simp: do_machine_op_def bind_assoc)
  apply (clarsimp simp: gets_def simpler_modify_def select_f_def
                  bind_def get_def return_def)
  apply (rule ext)
  apply clarsimp
  done

lemma dmo_return_distr:
  "do_machine_op (return x) = return x"
  apply (clarsimp simp: do_machine_op_def bind_assoc)
  apply (clarsimp simp: gets_def simpler_modify_def select_f_def
                  bind_def get_def return_def)
  done

(*FIXME: Move to scheduler_if*)
lemma dmo_getActive_IRQ_reads_respect_scheduler:
  "reads_respects_scheduler aag l (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
          (do_machine_op (getActiveIRQ in_kernel))"
  apply (simp add: getActiveIRQ_def)
  apply (simp add: dmo_distr dmo_if_distr dmo_gets_distr dmo_modify_distr dmo_return_distr
             cong: if_cong)
  apply wp
      apply (rule ev_modify[where P=\<top>])
      apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def
                             globals_equiv_scheduler_def)
      apply (clarsimp simp add: scheduler_affects_equiv_def states_equiv_for_def
                       equiv_for_def equiv_asids_def equiv_asid_def
                       scheduler_globals_frame_equiv_def silc_dom_equiv_def
                       idle_equiv_def)
     apply wp
    apply (rule_tac P="\<lambda>s. irq_masks_of_state st = irq_masks_of_state s" in gets_ev')
   apply wp
  apply clarsimp
  apply (simp add: scheduler_equiv_def)
  done

definition idle_context
where
  "idle_context s = arch_tcb_context_get (tcb_arch (the (get_tcb (idle_thread s) s)))"

lemma thread_set_context_globals_equiv:
  "\<lbrace>(\<lambda>s. t = idle_thread s \<longrightarrow> tc = idle_context s) and invs and globals_equiv st\<rbrace>
     thread_set (tcb_arch_update (arch_tcb_context_set tc)) t
   \<lbrace>\<lambda>rv. globals_equiv st\<rbrace>"
  apply (clarsimp simp: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (subgoal_tac "t \<noteq> arm_global_pd (arch_state s)")
   apply (clarsimp simp: idle_equiv_def globals_equiv_def tcb_at_def2 get_tcb_def idle_context_def)
   apply (clarsimp split: option.splits kernel_object.splits)
  apply (drule arm_global_pd_not_tcb[OF invs_valid_ko_at_arm])
  apply clarsimp
  done

lemma thread_set_scheduler_equiv[wp]:
  "\<lbrace>(invs and K(pasObjectAbs aag t \<noteq> SilcLabel) and
    (\<lambda>s. t = idle_thread s \<longrightarrow> tc = idle_context s)) and scheduler_equiv aag st\<rbrace>
     thread_set (tcb_arch_update (arch_tcb_context_set tc)) t
   \<lbrace>\<lambda>r. scheduler_equiv aag st\<rbrace>"
  apply (rule scheduler_equiv_lift')
       apply (rule globals_equiv_scheduler_inv')
       apply (wp thread_set_context_globals_equiv | clarsimp intro!: invs_valid_ko_at_arm)+
  apply (simp add: silc_dom_equiv_def thread_set_def)
  apply (wp set_object_wp)
  apply (clarsimp simp: get_tcb_def equiv_for_def split: kernel_object.splits option.splits)
  done

lemma arch_tcb_update_aux:
  "(tcb_arch_update f t) = tcb_arch_update (\<lambda>_. f (tcb_arch t)) t"
  by simp

lemma thread_set_scheduler_affects_equiv[wp]:
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
   apply (elim states_equiv_forE equiv_forE)
   apply (rule states_equiv_forI,simp_all add: equiv_for_def equiv_asids_def equiv_asid_def)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: idle_context_def get_tcb_def
                  split: option.splits kernel_object.splits)
  apply (subst arch_tcb_update_aux)
  apply simp
  apply (subgoal_tac "s = (s\<lparr>kheap := kheap s(idle_thread s \<mapsto> TCB y)\<rparr>)", simp)
  apply (rule state.equality)
            apply (rule ext)
            apply simp+
  done


lemma silc_inv_not_cur_thread:
  "silc_inv aag st s \<Longrightarrow> invs s \<Longrightarrow> pasObjectAbs aag (cur_thread s) \<noteq> SilcLabel"
  apply (clarsimp simp: silc_inv_def)
  apply (drule_tac x="(cur_thread s)" in spec)
  apply clarsimp
  apply (clarsimp simp add: obj_at_def invs_def cur_tcb_def
                  is_cap_table_def is_tcb_def)
  apply (case_tac ko,simp_all)
  done

lemma get_tcb_scheduler_equiv:
  "\<lbrakk>pasObjectAbs aag rv \<in> reads_scheduler aag l;
    scheduler_affects_equiv aag l s t\<rbrakk> \<Longrightarrow>
   get_tcb rv s = get_tcb rv t"
  apply (clarsimp simp: get_tcb_def scheduler_affects_equiv_def
                  states_equiv_for_def equiv_for_def
                  split: option.splits kernel_object.splits)
  done


lemma idle_equiv_identical_kheap_updates:
  "\<lbrakk>identical_kheap_updates s t kh kh'; idle_equiv s t\<rbrakk>
   \<Longrightarrow> idle_equiv (s\<lparr>kheap := kh\<rparr>) (t\<lparr>kheap := kh'\<rparr>)"
  apply (clarsimp simp add: identical_kheap_updates_def idle_equiv_def
                  tcb_at_def2)
  apply (drule_tac x="idle_thread t" in spec)
  apply fastforce
  done

lemma set_object_reads_respects_scheduler[wp]:
  "reads_respects_scheduler aag l \<top> (set_object ptr obj)"
  unfolding equiv_valid_def2 equiv_valid_2_def
  apply(clarsimp simp: set_object_def bind_def get_def put_def return_def
                       get_object_def assert_def fail_def gets_def
                       scheduler_equiv_def domain_fields_equiv_def
                       globals_equiv_scheduler_def silc_dom_equiv_def)
  apply (clarsimp simp: equiv_for_def scheduler_affects_equiv_def
                        scheduler_globals_frame_equiv_def identical_kheap_updates_def
                intro!: states_equiv_for_identical_kheap_updates
                        idle_equiv_identical_kheap_updates)
  apply (intro conjI impI)
      apply (clarsimp simp: equiv_for_def scheduler_affects_equiv_def
                            scheduler_globals_frame_equiv_def identical_kheap_updates_def
            | rule states_equiv_for_identical_kheap_updates idle_equiv_identical_kheap_updates)+
  done

lemma sts_reads_respects_scheduler:
  "reads_respects_scheduler aag l
     (K(pasObjectAbs aag rv \<in> reads_scheduler aag l) and
      reads_scheduler_cur_domain aag l and
      valid_idle and (\<lambda>s. rv \<noteq> idle_thread s))
     (set_thread_state rv st)"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def)
  apply (wp when_ev get_thread_state_reads_respects_scheduler
            gts_wp set_object_wp)
  apply (clarsimp simp: get_tcb_scheduler_equiv)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def
                        obj_at_def)
  done


lemma as_user_reads_respects_scheduler:
  "reads_respects_scheduler aag l (K(pasObjectAbs aag rv \<in> reads_scheduler aag l) and
                                   (\<lambda>s. rv \<noteq> idle_thread s) and K(det f))
        (as_user rv f)"
  apply (rule gen_asm_ev)
  apply (simp add: as_user_def)
  apply (wp select_f_ev | wpc | simp)+
  apply (clarsimp simp: get_tcb_scheduler_equiv)
  done

lemma restart_not_idle:
  "valid_idle s \<Longrightarrow> st_tcb_at ((=) Restart) t s \<Longrightarrow> t \<noteq> idle_thread s"
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)

lemma sts_silc_dom_equiv[wp]:
  "\<lbrace>K(pasObjectAbs aag x \<noteq> SilcLabel) and silc_dom_equiv aag st\<rbrace>
      set_thread_state x f
   \<lbrace>\<lambda>_. silc_dom_equiv aag st\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp dxo_wp_weak set_object_wp | simp)+
  apply (clarsimp simp: silc_dom_equiv_def equiv_for_def)
  done

lemma as_user_silc_dom_equiv[wp]:
  "\<lbrace>K(pasObjectAbs aag x \<noteq> SilcLabel) and silc_dom_equiv aag st\<rbrace>
      as_user x f
   \<lbrace>\<lambda>_. silc_dom_equiv aag st\<rbrace>"
  apply (simp add: as_user_def)
  apply (wp dxo_wp_weak set_object_wp | wpc | simp)+
  apply (clarsimp simp: silc_dom_equiv_def equiv_for_def)
  done

lemma scheduler_affects_equiv_update:
  "\<lbrakk>get_tcb x s = Some y;
    pasObjectAbs aag x \<notin> reads_scheduler aag l;
    scheduler_affects_equiv aag l st s\<rbrakk>
   \<Longrightarrow> scheduler_affects_equiv aag l st (s\<lparr>kheap := kheap s(x \<mapsto> TCB y')\<rparr>)"
  apply (clarsimp simp: scheduler_affects_equiv_def
                        states_equiv_for_def equiv_for_def
                        equiv_asids_def equiv_asid_def)
  apply (clarsimp simp: scheduler_globals_frame_equiv_def)
  apply (clarsimp simp: obj_at_def st_tcb_at_def get_tcb_def)
  done

lemma set_scheduler_action_wp[wp]:
  "\<lbrace>\<lambda>s. P () (s\<lparr>scheduler_action := a\<rparr>)\<rbrace> set_scheduler_action a \<lbrace>P\<rbrace>"
  apply(simp add: set_scheduler_action_def | wp)+
  done

lemma sts_scheduler_affects_equiv[wp]:
  "\<lbrace>K(pasObjectAbs aag x \<notin> reads_scheduler aag l) and scheduler_affects_equiv aag l st\<rbrace>
       set_thread_state x Running
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (simp add: set_thread_state_ext_def)

  apply (wp gts_wp set_object_wp)
  apply (intro impI conjI allI)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (fastforce intro!: scheduler_affects_equiv_update)
  done


lemma as_user_scheduler_affects_equiv[wp]:
  "\<lbrace>K(pasObjectAbs aag x \<notin> reads_scheduler aag l) and scheduler_affects_equiv aag l st\<rbrace>
      as_user x f
   \<lbrace>\<lambda>_. scheduler_affects_equiv aag l st\<rbrace>"
  apply (simp add: as_user_def)

  apply (wp gts_wp set_object_wp | wpc)+
  apply (intro impI conjI allI)
  apply (fastforce intro!: scheduler_affects_equiv_update)
  done

(* FIXME: MOVE *)
lemma st_tcb_at_not_idle_thread:
  "\<lbrakk> invs s; st_tcb_at ((=) t_st) t s; t_st \<noteq> IdleThreadState \<rbrakk> \<Longrightarrow> t \<noteq> idle_thread s"
  apply (frule st_tcb_at_tcb_at)
  apply (fastforce dest: st_tcb_at_idle_thread)
  done

lemma activate_thread_reads_respects_scheduler[wp]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_scheduler aag l (invs and silc_inv aag st and guarded_pas_domain aag)
                  activate_thread"
  apply (simp add: activate_thread_def)
  apply (rule reads_respects_scheduler_cases')
     apply ((wp sts_reads_respects_scheduler get_thread_state_reads_respects_scheduler gts_wp
               as_user_reads_respects_scheduler | wpc
              | simp add: setNextPC_det arch_activate_idle_thread_def)+)[1]
    apply (intro impI conjI allI
          ; fastforce simp: getRestartPC_det guarded_pas_domain_def reads_scheduler_def
                             restart_not_idle invs_valid_idle
                       dest: st_tcb_at_not_idle_thread
                             domains_distinct[THEN pas_domains_distinct_inj])
   apply (rule reads_respects_scheduler_unobservable''
                 [where P'="\<lambda>s. \<not> reads_scheduler_cur_domain aag l s \<and> guarded_pas_domain aag s \<and> invs s"])
     apply ((wp scheduler_equiv_lift'[where P="invs and silc_inv aag st"]
                globals_equiv_scheduler_inv'[where P="valid_ko_at_arm and valid_idle"]
                set_thread_state_globals_equiv gts_wp
            | wpc
            | clarsimp simp: arch_activate_idle_thread_def restart_not_idle invs_valid_ko_at_arm
                             silc_inv_not_cur_thread
            | force)+)[1]
    apply (wp gts_wp| wpc | simp add: arch_activate_idle_thread_def)+
    apply (clarsimp simp add: guarded_pas_domain_def restart_not_idle
                    invs_valid_idle)
   apply force+
  done


(*A function that is agnostic of its parameter with respect
  to the state space (as is the case with thread context updates)
  can be lifted to equiv_valid_2 over that parameter*)
lemma agnostic_to_ev2:
  assumes param_agnostic: "\<forall>P Q u u'. \<lbrace>P\<rbrace> (f u) \<lbrace>\<lambda>_. Q\<rbrace> \<longrightarrow> \<lbrace>P\<rbrace> (f u') \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes ret_agnostic: "\<And>u. \<lbrace>\<top>\<rbrace> (f u) \<lbrace>\<lambda>r s. r = g u\<rbrace>"
  assumes ev: "\<And>u. equiv_valid I A B P (f u)"
  shows "equiv_valid_2 I A B (\<lambda>r r'. r = (g u) \<and> r' = (g u')) P P (f u) (f u')"
  proof -
    have b: "\<And>a b s u. (a,b) \<in> fst (f u s) \<Longrightarrow> a = g u"

      apply (erule use_valid[OF _ ret_agnostic])
      apply simp
      done
    have a: "\<And>a b u u' s. (a,b) \<in> fst (f u s) \<Longrightarrow> \<exists>a'. (a',b) \<in> fst (f u' s)"
      apply (cut_tac P="\<lambda>sa. sa = s" and Q="\<lambda>s'. \<exists>a'. (a',s') \<in> fst (f u' s)"
                 and u=u' and u'=u in param_agnostic[rule_format])
      apply (clarsimp simp: valid_def)
      apply force
      apply (clarsimp simp: valid_def)
      apply (drule_tac x="(a,b)" in bspec)
       apply simp
      apply clarsimp
      done
  show ?thesis
  apply (cut_tac u=u in ev)
  apply (cut_tac u=u' in ev)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (frule a[where u=u and u'=u'])
  apply clarsimp
  apply (frule b[where u=u])
  apply (frule b[where u=u'])
  apply fastforce
  done
qed

lemma bind_return_ign:
  "\<lbrace>P\<rbrace> (f >>= (\<lambda>_. return x)) \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> (f >>= (\<lambda>_. return y)) \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (fastforce simp: valid_def bind_def return_def)
  done


lemma thread_set_reads_respect_scheduler[wp]:
  "reads_respects_scheduler aag l (invs and K(pasObjectAbs aag t \<noteq> SilcLabel)
                                        and (\<lambda>s. t = idle_thread s \<longrightarrow> tc = idle_context s)
                                        and guarded_pas_domain aag)
                                  (thread_set (tcb_arch_update (arch_tcb_context_set tc)) t)"
  apply (rule reads_respects_scheduler_cases[where P'=\<top>])
  prefer 3
  apply (rule reads_respects_scheduler_unobservable'')
  apply (wp | simp | elim conjE)+
  apply (simp add: thread_set_def)
  apply (wp)
  apply (fastforce simp: scheduler_affects_equiv_def get_tcb_def
                  states_equiv_for_def equiv_for_def scheduler_equiv_def
                  domain_fields_equiv_def
                  equiv_asids_def equiv_asid_def split: option.splits
                  kernel_object.splits)+
  done

lemma op_eq_unit_dc:
  "((=) :: unit \<Rightarrow> unit \<Rightarrow> bool) = (dc)"
  apply (rule ext)+
  apply simp
  done

lemma cur_thread_idle':
  "valid_idle s \<Longrightarrow> only_idle s \<Longrightarrow> ct_idle s = (cur_thread s = idle_thread s)"
  apply (rule iffI)
  apply (clarsimp simp: only_idle_def ct_in_state_def )
  apply (clarsimp simp: valid_idle_def ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma cur_thread_idle:
  "invs s \<Longrightarrow> ct_idle s = (cur_thread s = idle_thread s)"
  apply (rule cur_thread_idle')
  apply (simp add: invs_def valid_state_def)+
  done

lemma context_update_cur_thread_snippit_unobservable:
  "equiv_valid_2 (scheduler_equiv aag) (scheduler_affects_equiv aag l)
     (scheduler_affects_equiv aag l) (=)
     (invs and silc_inv aag st and guarded_pas_domain aag and
          (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
          (\<lambda>s. ct_idle s \<longrightarrow> uc = idle_context s))
     (invs and silc_inv aag st and guarded_pas_domain aag and
          (\<lambda>s. \<not> reads_scheduler_cur_domain aag l s) and
          (\<lambda>s. ct_idle s \<longrightarrow> uc' = idle_context s))
     (gets cur_thread >>= thread_set (tcb_arch_update (arch_tcb_context_set uc)))
     (gets cur_thread >>= thread_set (tcb_arch_update (arch_tcb_context_set uc')))"
  apply (rule equiv_valid_2_guard_imp)
    apply (simp add: op_eq_unit_dc)
    apply (rule equiv_valid_2_unobservable)
         apply (wp | elim conjE | simp add: dc_def)+
     apply fastforce
    apply fastforce
   apply (clarsimp simp: guarded_pas_domain_def
                         silc_inv_not_cur_thread cur_thread_idle
                         disjoint_iff_not_equal)+
  done

lemma context_update_cur_thread_snippit_cur_domain:
  "reads_respects_scheduler aag l (\<lambda>s. reads_scheduler_cur_domain aag l s \<and> invs s \<and>
        silc_inv aag st s \<and>
        (ct_idle s \<longrightarrow> uc = idle_context s) \<and>
        guarded_pas_domain aag s)
     (gets cur_thread >>= thread_set (tcb_arch_update (arch_tcb_context_set uc)))"
  apply wp
  apply (clarsimp simp: cur_thread_idle silc_inv_not_cur_thread del: notI)
  done

(*If we have to do this again we might consider an equiv_valid_2
  case splitting rule*)
lemma context_update_cur_thread_snippit:
  "equiv_valid_2 (scheduler_equiv aag) (scheduler_affects_equiv aag l)
     (scheduler_affects_equiv aag l) (=)
     (invs and silc_inv aag st and guarded_pas_domain aag and
         (\<lambda>s. reads_scheduler_cur_domain aag l s \<longrightarrow> uc = uc') and
         (\<lambda>s. ct_idle s \<longrightarrow> uc = idle_context s))
     (invs and silc_inv aag st and guarded_pas_domain aag and
         (\<lambda>s. reads_scheduler_cur_domain aag l s \<longrightarrow> uc = uc') and
         (\<lambda>s. ct_idle s \<longrightarrow> uc' = idle_context s))
     (gets cur_thread >>= thread_set (tcb_arch_update (arch_tcb_context_set uc)))
     (gets cur_thread >>= thread_set (tcb_arch_update (arch_tcb_context_set uc')))"
  apply (insert context_update_cur_thread_snippit_cur_domain[
                             where aag=aag and l=l and uc=uc and st=st])
  apply (insert context_update_cur_thread_snippit_unobservable[
                             where aag=aag and l=l and uc=uc and uc'=uc' and st=st])
  apply (clarsimp simp: equiv_valid_2_def equiv_valid_def2)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=t in spec)
  apply clarsimp
  apply (subgoal_tac "reads_scheduler_cur_domain aag l t = reads_scheduler_cur_domain aag l s")
   apply clarsimp
   apply (case_tac "reads_scheduler_cur_domain aag l s")
    apply ((fastforce)+)[2]
  apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def)
  done


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
  assumes
   symI: "\<And> x y. I x y \<Longrightarrow> I y x"
  assumes
   symA: "\<And> x y. A x y \<Longrightarrow> A y x"
  assumes
   symB: "\<And> x y. B x y \<Longrightarrow> B y x"
  assumes
   symR: "\<And> x y. R x y \<Longrightarrow> R' y x"
  shows
  "equiv_valid_2 I A B R P' P f' f \<Longrightarrow>
   equiv_valid_2 I A B R' P P' f f'"
  apply(clarsimp simp: equiv_valid_2_def)
  apply(blast intro: symA symB symI symR)
  done

lemma SilcLabel_affects_scheduler_equiv:
  "scheduler_equiv aag s t \<Longrightarrow> scheduler_affects_equiv aag SilcLabel s t"
  apply (simp add:  scheduler_affects_equiv_def reads_scheduler_def
                   states_equiv_for_def equiv_for_def scheduler_equiv_def equiv_asids_def
                   equiv_asid_def globals_equiv_scheduler_def)
  done

end

end
