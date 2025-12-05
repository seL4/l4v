(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchNoninterference
imports Noninterference
begin

context Arch begin global_naming RISCV64

named_theorems Noninterference_assms

(* clagged straight from ADT_AC.do_user_op_respects *)
lemma do_user_op_if_integrity[Noninterference_assms]:
  "\<lbrace>invs and integrity aag X st and is_subject aag \<circ> cur_thread and pas_refined aag\<rbrace>
   do_user_op_if uop tc
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: do_user_op_if_def)
  apply (wpsimp wp: dmo_user_memory_update_respects_Write dmo_device_update_respects_Write
                    hoare_vcg_all_lift hoare_vcg_imp_lift
            wp_del: select_wp)
             apply (rule hoare_pre_cont)
            apply (wp | wpc | clarsimp)+
  apply (rule conjI)
   apply clarsimp
   apply (simp add: restrict_map_def ptable_lift_s_def ptable_rights_s_def split: if_splits)
   apply (drule_tac auth=Write in user_op_access')
       apply (simp add: vspace_cap_rights_to_auth_def)+
  apply clarsimp
  apply (simp add: restrict_map_def ptable_lift_s_def ptable_rights_s_def split: if_splits)
  apply (drule_tac auth=Write in user_op_access')
      apply (simp add: vspace_cap_rights_to_auth_def)+
  done

lemma do_user_op_if_globals_equiv_scheduler[Noninterference_assms]:
  "\<lbrace>globals_equiv_scheduler st and invs\<rbrace>
   do_user_op_if tc uop
   \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  apply (simp add: do_user_op_if_def)
  apply (wpsimp wp: dmo_user_memory_update_globals_equiv_scheduler
                    dmo_device_memory_update_globals_equiv_scheduler)+
  apply (auto simp: ptable_lift_s_def ptable_rights_s_def)
  done

crunch do_user_op_if
  for silc_dom_equiv[Noninterference_assms, wp]: "silc_dom_equiv aag st"
  (ignore: do_machine_op user_memory_update wp: crunch_wps)

lemma sameFor_scheduler_affects_equiv[Noninterference_assms]:
  "\<lbrakk> (s,s') \<in> same_for aag PSched; (s,s') \<in> same_for aag (Partition l);
     invs (internal_state_if s); invs (internal_state_if s') \<rbrakk>
     \<Longrightarrow> scheduler_equiv aag (internal_state_if s) (internal_state_if s') \<and>
         scheduler_affects_equiv aag (OrdinaryLabel l) (internal_state_if s) (internal_state_if s')"
  apply (rule conjI)
   apply (blast intro: sameFor_scheduler_equiv)
  apply (clarsimp simp: scheduler_affects_equiv_def arch_scheduler_affects_equiv_def
                        sameFor_def silc_dom_equiv_def reads_scheduler_def sameFor_scheduler_def)
  (* simplifying using sameFor_subject_def in assumptions causes simp to loop *)
  apply (simp (no_asm_use) add: sameFor_subject_def disjoint_iff_not_equal Bex_def)
  apply (blast intro: globals_equiv_to_scheduler_globals_frame_equiv globals_equiv_to_cur_thread_eq)
  done

lemma do_user_op_if_partitionIntegrity[Noninterference_assms]:
  "\<lbrace>partitionIntegrity aag st and pas_refined aag and invs and is_subject aag \<circ> cur_thread\<rbrace>
   do_user_op_if tc uop
   \<lbrace>\<lambda>_. partitionIntegrity aag st\<rbrace>"
 apply (rule_tac Q'="\<lambda>rv s. integrity (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                                     (scheduler_affects_globals_frame st) st s \<and>
                           domain_fields_equiv st s \<and> idle_thread s = idle_thread st \<and>
                           globals_equiv_scheduler st s \<and> silc_dom_equiv aag st s"
              in hoare_strengthen_post)
   apply (wp hoare_vcg_conj_lift do_user_op_if_integrity do_user_op_if_globals_equiv_scheduler
             hoare_vcg_all_lift domain_fields_equiv_lift[where Q="\<top>" and R="\<top>"] | simp)+
  apply (clarsimp simp: partitionIntegrity_def)+
  done

lemma arch_activate_idle_thread_reads_respects_g[Noninterference_assms, wp]:
  "reads_respects_g aag l \<top> (arch_activate_idle_thread t)"
  unfolding arch_activate_idle_thread_def by wpsimp

definition arch_globals_equiv_strengthener :: "machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "arch_globals_equiv_strengthener ms ms' \<equiv> True"

declare arch_globals_equiv_strengthener_def[simp]

lemma arch_globals_equiv_strengthener_thread_independent[Noninterference_assms]:
  "arch_globals_equiv_strengthener (machine_state s) (machine_state s')
   \<Longrightarrow> \<forall>ct ct' it it'. arch_globals_equiv ct it (kheap s) (kheap s')
                         (arch_state s) (arch_state s') (machine_state s) (machine_state s') =
                       arch_globals_equiv ct' it' (kheap s) (kheap s')
                         (arch_state s) (arch_state s') (machine_state s) (machine_state s')"
  by auto

lemma integrity_asids_update_reference_state[Noninterference_assms]:
   "is_subject aag t
    \<Longrightarrow> integrity_asids aag {pasSubject aag} x a s (s\<lparr>kheap := (kheap s)(t \<mapsto> blah)\<rparr>)"
  by (clarsimp simp: integrity_asids_def opt_map_def)

lemma inte_obj_arch:
  assumes inte_obj: "(integrity_obj_atomic aag activate subjects l)\<^sup>*\<^sup>* ko ko'"
  assumes "ko = Some (ArchObj ao)"
  assumes "ko \<noteq> ko'"
  shows "integrity_obj_atomic aag activate subjects l ko ko'"
proof (cases "l \<in> subjects")
  case True
  then show ?thesis by (fastforce intro: integrity_obj_atomic.intros)
next
  case False
  note l = this
  have "\<forall>ao'. ko = Some (ArchObj ao) \<longrightarrow>
              ko \<noteq> ko' \<longrightarrow>
              integrity_obj_atomic aag activate subjects l ko ko'"
    using inte_obj
  proof (induct rule: rtranclp_induct)
    case base
    then show ?case by clarsimp
  next
    case (step y z)
    have "\<exists>ao'. ko' = Some (ArchObj ao')"
      using False inte_obj assms
      by (auto elim!: rtranclp_induct integrity_obj_atomic.cases)
    then show ?case using step.hyps
      by (fastforce intro: troa_arch arch_troa_asidpool_clear integrity_obj_atomic.intros
                    elim!: integrity_obj_atomic.cases arch_integrity_obj_atomic.cases)
  qed
  then show ?thesis
    using assms by fastforce
qed

lemma asid_pool_into_aag:
  "\<lbrakk> pool_for_asid asid s = Some p; kheap s p = Some (ArchObj (ASIDPool pool));
     pool r = Some p'; pas_refined aag s \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag Control p p'"
  apply (rule pas_refined_mem [rotated], assumption)
  apply (rule sta_vref)
  apply (rule state_vrefsD)
     apply (erule pool_for_asid_vs_lookupD)
    apply (fastforce simp: aobjs_of_Some)
   apply fastforce
  apply (fastforce simp: vs_refs_aux_def graph_of_def image_iff)
  done

lemma owns_mapping_owns_asidpool:
  "\<lbrakk> pool_for_asid asid s = Some p; kheap s p = Some (ArchObj (ASIDPool pool));
     pool r = Some p'; pas_refined aag s; is_subject aag p';
     pas_wellformed (aag\<lparr>pasSubject := (pasObjectAbs aag p)\<rparr>) \<rbrakk>
     \<Longrightarrow> is_subject aag p"
  apply (frule asid_pool_into_aag)
     apply assumption+
  apply (drule pas_wellformed_pasSubject_update_Control)
   apply assumption
  apply simp
  done

lemma partitionIntegrity_subjectAffects_aobj':
  "\<lbrakk> pool_for_asid asid s = Some x; kheap s x = Some (ArchObj ao); ao \<noteq> ao';
     pas_refined aag s; silc_inv aag st s; pas_wellformed_noninterference aag;
     arch_integrity_obj_atomic (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                               {pasSubject aag} (pasObjectAbs aag x) ao ao' \<rbrakk>
     \<Longrightarrow> subject_can_affect_label_directly aag (pasObjectAbs aag x)"
  unfolding arch_integrity_obj_atomic.simps asid_pool_integrity_def
  apply clarsimp
  apply (rule ccontr)
  apply (drule fun_noteqD)
  apply (erule exE, rename_tac r)
  apply (drule_tac x=r in spec)
  apply (clarsimp dest!: not_sym[where t=None])
  apply (subgoal_tac "is_subject aag x", force intro: affects_lrefl)
  apply (frule (1) aag_Control_into_owns)
  apply (frule (3) asid_pool_into_aag)
  apply simp
  apply (frule (1) pas_wellformed_noninterference_control_to_eq)
   apply (fastforce elim!: silc_inv_cnode_onlyE obj_atE simp: is_cap_table_def)
  apply clarsimp
  done

lemma partitionIntegrity_subjectAffects_aobj[Noninterference_assms]:
  assumes par_inte: "partitionIntegrity aag s s'"
  and "kheap s x = Some (ArchObj ao)"
      "kheap s x \<noteq> kheap s' x"
      "silc_inv aag st s"
      "pas_refined aag s"
      "pas_wellformed_noninterference aag"
  notes inte_obj = par_inte[THEN partitionIntegrity_integrity, THEN integrity_subjects_obj,
                            THEN spec[where x=x], simplified integrity_obj_def, simplified]
  shows "subject_can_affect_label_directly aag (pasObjectAbs aag x)"
proof (cases "pasObjectAbs aag x = pasSubject aag")
  case True
  then show ?thesis by (simp add: subjectAffects.intros(1))
next
  case False
  obtain ao' where ao': "kheap s' x = Some (ArchObj ao')"
    using assms False inte_obj_arch[OF inte_obj]
    by (auto elim: integrity_obj_atomic.cases)
  have arch_tro:
    "arch_integrity_obj_atomic (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                               {pasSubject aag} (pasObjectAbs aag x) ao ao'"
    using assms False ao' inte_obj_arch[OF inte_obj]
    by (auto elim: integrity_obj_atomic.cases)
  obtain asid where asid: "pool_for_asid asid s = Some x"
    using assms False inte_obj_arch[OF inte_obj]
          integrity_subjects_asids[OF partitionIntegrity_integrity[OF par_inte]]
    by (fastforce elim!: integrity_obj_atomic.cases arch_integrity_obj_atomic.cases
                   simp: integrity_asids_def aobjs_of_Some opt_map_def pool_for_asid_def)+
  show ?thesis
    using assms ao' asid arch_tro
    by (fastforce dest: partitionIntegrity_subjectAffects_aobj')
qed

lemma partitionIntegrity_subjectAffects_asid[Noninterference_assms]:
  "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s; valid_objs s;
     valid_arch_state s; valid_arch_state s'; pas_wellformed_noninterference aag;
     silc_inv aag st s'; invs s'; \<not> equiv_asids (\<lambda>x. pasASIDAbs aag x = a) s s' \<rbrakk>
     \<Longrightarrow> a \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)
  apply (case_tac "riscv_asid_table (arch_state s) (asid_high_bits_of asid) =
                   riscv_asid_table (arch_state s') (asid_high_bits_of asid)")
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
   apply (erule disjE)
    apply (case_tac "kheap s' pool_ptr = None"; clarsimp)
     apply (prop_tac "pool_ptr \<notin> dom (asid_pools_of s')")
      apply (fastforce simp: not_in_domIff asid_pools_of_ko_at obj_at_def)
     apply blast
    apply (case_tac "\<exists>asid_pool. y = ArchObj (ASIDPool asid_pool)"; clarsimp)
     apply (prop_tac "pool_ptr \<notin> dom (asid_pools_of s)")
      apply (fastforce simp: not_in_domIff asid_pools_of_ko_at obj_at_def)
     apply blast
    apply (prop_tac "pool_ptr \<notin> dom (asid_pools_of s')")
     apply (fastforce simp: not_in_domIff asid_pools_of_ko_at obj_at_def)
    apply blast
   apply clarsimp
   apply (rule affects_asidpool_map)
   apply (rule pas_refined_asid_mem)
    apply (drule partitionIntegrity_integrity)
    apply (drule integrity_subjects_obj)
    apply (drule_tac x="pool_ptr" in spec)+
    apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)
    apply (drule tro_tro_alt, erule integrity_obj_alt.cases; simp)
     apply (drule_tac t="pasSubject aag" in sym)
     apply simp
     apply (rule sata_asidpool)
      apply assumption
     apply assumption
    apply (clarsimp simp: arch_integrity_obj_alt.simps asid_pool_integrity_def)
    apply (drule_tac x="asid_low_bits_of asid" in spec)+
    apply clarsimp
    apply (drule owns_mapping_owns_asidpool[rotated])
         apply ((simp | blast intro: pas_refined_Control[THEN sym]
                      | fastforce simp: pool_for_asid_def
                                 intro: pas_wellformed_pasSubject_update[simplified])+)[5]
    apply (drule_tac t="pasSubject aag" in sym)+
    apply simp
    apply (rule sata_asidpool)
     apply assumption
    apply assumption
   apply assumption
  apply clarsimp
  apply (drule partitionIntegrity_integrity)
  apply (clarsimp simp: integrity_def integrity_asids_def)
  apply (drule_tac x=asid in spec)+
  apply (fastforce intro: affects_lrefl)
  done

(* clagged mostly from Scheduler_IF.dmo_storeWord_reads_respects_scheduler *)
lemma dmo_storeWord_reads_respects_g[Noninterference_assms, wp]:
  "reads_respects_g aag l \<top> (do_machine_op (storeWord ptr w))"
  apply (clarsimp simp: do_machine_op_def bind_def gets_def get_def return_def fail_def
                        select_f_def storeWord_def assert_def simpler_modify_def)
  apply (fold simpler_modify_def)
  apply (intro impI conjI)
   apply (rule ev_modify)
   apply (rule conjI)
    apply (fastforce simp: reads_equiv_g_def globals_equiv_def reads_equiv_def2 states_equiv_for_def
                           equiv_for_def equiv_asids_def equiv_asid_def silc_dom_equiv_def upto.simps)
   apply (rule affects_equiv_machine_state_update, assumption)
   apply (fastforce simp: equiv_for_def affects_equiv_def states_equiv_for_def upto.simps)
  apply (simp add: equiv_valid_def2 equiv_valid_2_def)
  done

lemma set_vm_root_reads_respects:
  "reads_respects aag l \<top> (set_vm_root tcb)"
  by (rule reads_respects_unobservable_unit_return) wp+

lemmas set_vm_root_reads_respects_g[wp] =
  reads_respects_g[OF set_vm_root_reads_respects,
                   OF doesnt_touch_globalsI[where P="\<top>"],
                   simplified,
                   OF set_vm_root_globals_equiv]

lemma arch_switch_to_thread_reads_respects_g'[Noninterference_assms]:
  "equiv_valid (reads_equiv_g aag) (affects_equiv aag l)
               (\<lambda>s s'. affects_equiv aag l s s' \<and>
                       arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
               (\<lambda>s. is_subject aag t)
               (arch_switch_to_thread t)"
  apply (simp add: arch_switch_to_thread_def)
  apply (rule equiv_valid_guard_imp)
  by (wp bind_ev_general thread_get_reads_respects_g | simp)+

(* consider rewriting the return-value assumption using equiv_valid_rv_inv *)
lemma ev2_invisible'[Noninterference_assms]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "\<lbrakk> labels_are_invisible aag l L; labels_are_invisible aag l L';
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
                         W (P and Q) (P' and Q') f g"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (rule conjI)
   apply blast
  apply (drule_tac s=s in modifies_at_mostD, assumption+)
  apply (drule_tac s=t in modifies_at_mostD, assumption+)
  apply (drule_tac s=s in globals_equivI, assumption+)
  apply (drule_tac s=t in globals_equivI, assumption+)
  apply (frule (1) equiv_but_for_reads_equiv[OF domains_distinct])
  apply (frule_tac s=t in equiv_but_for_reads_equiv[OF domains_distinct], assumption)
  apply (drule (1) equiv_but_for_affects_equiv[OF domains_distinct])
  apply (drule_tac s=t in equiv_but_for_affects_equiv[OF domains_distinct], assumption)
  apply (clarsimp simp: reads_equiv_g_def)
  apply (blast intro: reads_equiv_trans reads_equiv_sym affects_equiv_trans
                      affects_equiv_sym globals_equiv_trans globals_equiv_sym)
  done

lemma arch_switch_to_idle_thread_reads_respects_g[Noninterference_assms, wp]:
  "reads_respects_g aag l \<top> (arch_switch_to_idle_thread)"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply wp
  apply (clarsimp simp: reads_equiv_g_def globals_equiv_idle_thread_ptr)
  done

lemma arch_globals_equiv_threads_eq[Noninterference_assms]:
  "arch_globals_equiv t' t'' kh kh' as as' ms ms'
   \<Longrightarrow> arch_globals_equiv t t kh kh' as as' ms ms'"
  by clarsimp

lemma arch_globals_equiv_globals_equiv_scheduler[Noninterference_assms, elim]:
  "arch_globals_equiv (cur_thread t) (idle_thread s) (kheap s) (kheap t)
                      (arch_state s) (arch_state t) (machine_state s) (machine_state t)
   \<Longrightarrow> arch_globals_equiv_scheduler (kheap s) (kheap t) (arch_state s) (arch_state t)"
  by (auto simp: arch_globals_equiv_scheduler_def)

lemma getActiveIRQ_ret_no_dmo[Noninterference_assms, wp]:
  "\<lbrace>\<top>\<rbrace> getActiveIRQ in_kernel \<lbrace>\<lambda>rv s. \<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply (rule hoare_pre)
   apply (insert irq_oracle_max_irq)
   apply (wp dmo_getActiveIRQ_irq_masks)
  apply clarsimp
  done

(*FIXME: Move to scheduler_if*)
lemma dmo_getActive_IRQ_reads_respect_scheduler[Noninterference_assms]:
  "reads_respects_scheduler aag l (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
                            (do_machine_op (getActiveIRQ in_kernel))"
  apply (simp add: getActiveIRQ_def)
  apply (simp add: dmo_distr dmo_if_distr dmo_gets_distr dmo_modify_distr cong: if_cong)
  apply wp
      apply (rule ev_modify[where P=\<top>])
      apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def
                            scheduler_affects_equiv_def arch_scheduler_affects_equiv_def
                            states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def
                            scheduler_globals_frame_equiv_def silc_dom_equiv_def idle_equiv_def)
     apply wp
    apply (rule_tac P="\<lambda>s. irq_masks_of_state st = irq_masks_of_state s" in gets_ev')
   apply wp
  apply clarsimp
  apply (simp add: scheduler_equiv_def)
  done

lemma getActiveIRQ_no_non_kernel_IRQs[Noninterference_assms]:
  "getActiveIRQ True = getActiveIRQ False"
  by (clarsimp simp: getActiveIRQ_def non_kernel_IRQs_def)

lemma valid_cur_hyp_triv[Noninterference_assms]:
  "valid_cur_hyp s"
  by (simp add: valid_cur_hyp_def)

lemma arch_tcb_get_registers_equality[Noninterference_assms]:
  "arch_tcb_get_registers (tcb_arch tcb) = arch_tcb_get_registers (tcb_arch tcb')
   \<Longrightarrow> tcb_arch tcb = tcb_arch tcb'"
  by (auto simp: arch_tcb_get_registers_def intro: arch_tcb.equality user_context.expand)

end


requalify_consts RISCV64.arch_globals_equiv_strengthener
requalify_facts RISCV64.arch_globals_equiv_strengthener_thread_independent


global_interpretation Noninterference_1?: Noninterference_1 _ arch_globals_equiv_strengthener
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Noninterference_assms | solves \<open>rule integrity_arch_triv\<close>)?)
qed


sublocale valid_initial_state \<subseteq> valid_initial_state?:
  Noninterference_valid_initial_state arch_globals_equiv_strengthener ..

end
