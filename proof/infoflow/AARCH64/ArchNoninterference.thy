(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchNoninterference
imports Noninterference
begin

context Arch begin arch_global_naming

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
   apply (wpsimp wp: do_user_op_if_globals_equiv_scheduler
                     do_user_op_if_integrity domain_fields_equiv_lift)
   apply (auto simp: partitionIntegrity_def)
  done

lemma arch_activate_idle_thread_reads_respects_g[Noninterference_assms, wp]:
  "reads_respects_g aag l \<top> (arch_activate_idle_thread t)"
  unfolding arch_activate_idle_thread_def by wpsimp

crunch handle_spurious_irq
  for domain[wp]: "\<lambda>s.  Q (domain_time s) (domain_index s) (domain_list s)"
  and irq_state_of_state[wp]: "\<lambda>s. P (irq_state_of_state s)"

lemma handle_spurious_irq_reads_respect_scheduler[Noninterference_assms]:
  "reads_respects_scheduler aag l \<top> handle_spurious_irq"
  unfolding handle_spurious_irq_def
  by wpsimp

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

lemma partitionIntegrity_cur_vcpu_None:
   "\<lbrakk> partitionIntegrity aag s s'; valid_objs s; valid_objs s';
      cur_vcpu_of s x = None; cur_vcpu_of s' x = None; vcpu_at x s \<rbrakk>
      \<Longrightarrow> is_subject aag x \<or> kheap s x = kheap s' x"
  apply (prop_tac "integrity_obj (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                                 False {pasSubject aag} (pasObjectAbs aag x) (kheap s x) (kheap s' x)")
   apply (clarsimp simp: partitionIntegrity_def integrity_subjects_def)
  apply (prop_tac "integrity_hyp (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                                 {pasSubject aag} x s s'")
   apply (clarsimp simp: partitionIntegrity_def integrity_subjects_def)
  apply (rule disjCI2)
  apply (drule tro_tro_alt)
  apply (clarsimp simp: obj_at_def)
  apply (erule integrity_obj_alt.cases; clarsimp)
  apply (erule arch_integrity_obj_alt.cases; clarsimp)
  apply (rename_tac vcpu vcpu')
  apply (prop_tac "valid_vcpu vcpu s")
   apply (erule valid_objsE, simp, fastforce simp: valid_obj_def)
  apply (prop_tac "valid_vcpu vcpu' s'")
   apply (erule valid_objsE, simp, fastforce simp: valid_obj_def)
  apply (prop_tac "vcpus_of s x = Some vcpu")
   apply (clarsimp simp: opt_map_def)
  apply (prop_tac "vcpus_of s' x = Some vcpu'")
   apply (clarsimp simp: opt_map_def)
  apply (prop_tac "integrity_obj (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>) False
                                 {pasSubject aag} (pasObjectAbs aag x) (kheap s x) (kheap s' x)")
   apply (thin_tac "kheap _ x = _")+
   apply (clarsimp simp: partitionIntegrity_def integrity_subjects_def)
  apply (erule integrity_objE; fastforce?)
  apply (erule arch_integrity_obj_alt.cases; fastforce?)
  apply clarsimp
  apply (clarsimp simp: integrity_hyp_def vcpu_integrity_def vcpu_extra_lrs_def vcpu_of_state_def)
  apply (case_tac vcpu; case_tac vcpu'; clarsimp)
  apply (case_tac vcpu_vgic; case_tac vcpu_vgica; clarsimp)
  apply (rule ext)
  apply (drule_tac x=xa in fun_cong)+
  apply (auto split: if_splits)
  done

lemma partitionIntegrity_cur_vcpu_Some:
  "\<lbrakk> invs s; pas_refined aag s; pas_cur_domain aag s; pas_domains_distinct aag;
     cur_vcpu_in_cur_domain s; current_vcpu s = Some (vr,b) \<rbrakk>
     \<Longrightarrow> is_subject aag vr"
  apply (clarsimp simp: cur_vcpu_in_cur_domain_def cur_vcpu_tcb_def split: option.splits)
   defer
   apply (rename_tac t)
   apply (prop_tac "is_subject aag vr")
    apply (prop_tac "\<exists>tcb. ko_at (TCB tcb) t s")
     apply (prop_tac "valid_objs s")
      apply fastforce
     apply (clarsimp simp: opt_map_def split: option.splits)
     apply (erule (1) valid_objsE)
     apply (clarsimp simp: valid_obj_def valid_vcpu_def obj_at_def)
    apply (prop_tac "is_subject aag t")
     apply clarsimp
     apply (drule ko_at_etcbD)
     apply (frule (1) tcb_domain_wellformed)
     apply (prop_tac "etcb_domain (etcb_of tcb) = cur_domain s")
      apply (clarsimp simp: in_cur_domain_def)
      apply (clarsimp simp: etcbs_of'_def etcb_at'_def split: option.splits kernel_object.splits)
     apply simp
     apply (prop_tac "pasDomainAbs aag (cur_domain s) = {pasSubject aag}")
      apply (clarsimp simp: pas_domains_distinct_def)
      apply (metis singletonD)
     apply blast
    apply clarsimp
    apply (clarsimp simp: opt_map_def split: option.splits)
    apply (prop_tac "sym_refs (state_hyp_refs_of s)")
     apply fastforce
    apply (drule_tac x=vr in sym_refsD[rotated])
     apply (simp add: state_hyp_refs_of_def)
    apply (clarsimp simp: state_hyp_refs_of_def hyp_refs_of_def obj_at_def tcb_vcpu_refs_def split: option.splits)
    apply (erule associated_vcpu_is_subject)
      apply (simp add: get_tcb_Some_ko_at obj_at_def)
     apply simp+
  apply (prop_tac "cur_vcpu s")
   apply (prop_tac "valid_arch_state s")
    apply fastforce
   apply (clarsimp simp: valid_arch_state_def)
  apply (clarsimp simp: cur_vcpu_def opt_map_def opt_pred_def)
  done

lemma cur_vcpu_of_Some:
  "cur_vcpu_of s vr = Some b \<longleftrightarrow> current_vcpu s = Some (vr,b)"
  by (auto simp: cur_vcpu_of_def split: option.splits)

lemma partitionIntegrity_subjectAffects_vcpu:
  assumes par_inte: "partitionIntegrity aag s s'"
  and "kheap s x = Some (ArchObj (VCPU vcpu))"
  and kh_neq: "kheap s x \<noteq> kheap s' x"
  and "silc_inv aag st s"
      "pas_wellformed_noninterference aag"
      "pas_refined aag s" "pas_refined aag s'"
      "pas_cur_domain aag s" "pas_cur_domain aag s'"
      "cur_vcpu_in_cur_domain s" "cur_vcpu_in_cur_domain s'"
      "invs s" "invs s'"
  notes inte_obj = par_inte[THEN partitionIntegrity_integrity, THEN integrity_subjects_obj,
                            THEN spec[where x=x], simplified integrity_obj_def, simplified]
  shows "subject_can_affect_label_directly aag (pasObjectAbs aag x)"
  apply (rule ssubst[where s="pasSubject aag", OF _ affects_lrefl])
  apply (case_tac "cur_vcpu_of s x = None \<and> cur_vcpu_of s' x = None"; clarsimp)
   apply (drule (1) partitionIntegrity_cur_vcpu_None[OF par_inte, rotated 2])
      apply (simp_all add: assms obj_at_def invs_valid_objs)[3]
   apply (fastforce simp: kh_neq)
  apply (elim disjE; clarsimp; rule partitionIntegrity_cur_vcpu_Some
                   ; simp add: assms cur_vcpu_of_Some pas_wellformed_noninterference_domains_distinct)
  done

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
      by (fastforce intro: arch_integrity_obj_atomic.intros integrity_obj_atomic.intros
                    elim!: integrity_obj_atomic.cases arch_integrity_obj_atomic.cases)
  qed
  then show ?thesis
    using assms by fastforce
qed

lemma asid_pool_into_aag:
  "\<lbrakk> pool_for_asid asid s = Some p; kheap s p = Some (ArchObj (ASIDPool pool));
     pool r = Some entry; ap_vspace entry = p'; pas_refined aag s \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag Control p p'"
  apply (rule pas_refined_mem [rotated], assumption)
  apply (rule sta_vref)
  apply (rule state_vrefsD)
     apply (erule pool_for_asid_vs_lookupD)
    apply (fastforce simp: opt_map_def)
   apply fastforce
  apply (fastforce simp: vs_refs_aux_def graph_of_def image_iff)
  done

lemma owns_mapping_owns_asidpool:
  "\<lbrakk> pool_for_asid asid s = Some p; kheap s p = Some (ArchObj (ASIDPool pool));
     pool r = Some entry; ap_vspace entry = p'; pas_refined aag s; is_subject aag p';
     pas_wellformed (aag\<lparr>pasSubject := (pasObjectAbs aag p)\<rparr>) \<rbrakk>
     \<Longrightarrow> is_subject aag p"
  apply (frule asid_pool_into_aag)
     apply assumption+
  apply (drule pas_wellformed_pasSubject_update_Control)
   apply assumption
  apply simp
  done

lemma partitionIntegrity_subjectAffects_asid_pool':
  "\<lbrakk> pool_for_asid asid s = Some x; kheap s x = Some (ArchObj ao); ao \<noteq> ao';
     pas_refined aag s; silc_inv aag st s; pas_wellformed_noninterference aag; valid_arch_state s;
     arch_integrity_obj_atomic (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                              {pasSubject aag} (pasObjectAbs aag x) ao ao' \<rbrakk>
     \<Longrightarrow> subject_can_affect_label_directly aag (pasObjectAbs aag x)"
  unfolding arch_integrity_obj_atomic.simps asid_pool_integrity_def
  apply (elim disjE)
   apply clarsimp
   apply (rule ccontr)
   apply (drule fun_noteqD)
   apply (erule exE, rename_tac r)
   apply (drule_tac x=r in spec)
   apply (clarsimp dest!: not_sym[where t=None])
   apply (subgoal_tac "is_subject aag x", force intro: affects_lrefl)
   apply (frule (1) aag_Control_into_owns)
   apply (frule (2) asid_pool_into_aag)
     apply simp
    apply simp
   apply (frule (1) pas_wellformed_noninterference_control_to_eq)
    apply (fastforce elim!: silc_inv_cnode_onlyE obj_atE simp: is_cap_table_def)
   apply clarsimp
  apply clarsimp
  apply (drule (1) pool_for_asid_ap_at)
  apply (clarsimp simp: obj_at_def)
  done

lemma partitionIntegrity_subjectAffects_asid_pool:
  assumes par_inte: "partitionIntegrity aag s s'"
  and "kheap s x = Some (ArchObj (ASIDPool pool))"
      "kheap s x \<noteq> kheap s' x"
      "silc_inv aag st s"
      "pas_refined aag s"
      "valid_arch_state s"
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
                               {pasSubject aag} (pasObjectAbs aag x) (ASIDPool pool) ao'"
    using assms False ao' inte_obj_arch[OF inte_obj]
    by (auto elim: integrity_obj_atomic.cases)
  obtain asid where asid: "pool_for_asid asid s = Some x"
    using assms False inte_obj_arch[OF inte_obj]
          integrity_subjects_asids[OF partitionIntegrity_integrity[OF par_inte]]
    by (fastforce elim!: integrity_obj_atomic.cases arch_integrity_obj_atomic.cases
                   simp: integrity_asids_def aobjs_of_Some opt_map_def pool_for_asid_def)+
  show ?thesis
    using assms ao' asid arch_tro
    by (fastforce dest: partitionIntegrity_subjectAffects_asid_pool')
qed

lemma partitionIntegrity_subjectAffects_aobj:
  assumes par_inte: "partitionIntegrity aag s s'"
  and "kheap s x = Some (ArchObj ao)"
      "kheap s x \<noteq> kheap s' x"
      "silc_inv aag st s"
      "pas_wellformed_noninterference aag"
      "pas_refined aag s" "pas_refined aag s'"
      "pas_cur_domain aag s" "pas_cur_domain aag s'"
      "cur_vcpu_in_cur_domain s" "cur_vcpu_in_cur_domain s'"
      "invs s" "invs s'"
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
  show ?thesis
    apply (case_tac ao)
       apply (insert partitionIntegrity_subjectAffects_asid_pool[of aag s s' x _ st])
    using assms apply (simp add: invs_arch_state)
    using arch_tro apply (fastforce elim: arch_integrity_obj_atomic.cases)
    using arch_tro apply (fastforce elim: arch_integrity_obj_atomic.cases)
    apply (insert partitionIntegrity_subjectAffects_vcpu[of aag s s' x _ st])
    using assms apply (simp add: invs_arch_state)
    done
qed

declare cur_vcpu_for_None[simp]

lemma cur_vcpu_of_None[simp]:
  "cur_vcpu_of_2 None vst = None"
  by (clarsimp simp: cur_vcpu_of_def)

lemma partitionIntegrity_subjectAffects_numlistregs:
  "partitionIntegrity aag s s' \<Longrightarrow> equiv_for (\<lambda>x. pasObjectAbs aag x = da) (K \<circ> numlistregs) s s'"
  by (clarsimp simp: partitionIntegrity_def integrity_subjects_def integrity_hyp_def equiv_for_def)

lemma partitionIntegrity_subjectAffects_cur_vcpu_of:
   "\<lbrakk> invs s; invs s';
      cur_vcpu_in_cur_domain s; cur_vcpu_in_cur_domain s';
      pas_refined aag s; pas_refined aag s';
      pas_cur_domain aag s; pas_cur_domain aag s';
      pas_domains_distinct aag;
      \<not> equiv_for (\<lambda>x. pasObjectAbs aag x = a) cur_vcpu_of s s' \<rbrakk>
      \<Longrightarrow> a \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (case_tac "\<exists>b. cur_vcpu_for (\<lambda>x. pasObjectAbs aag x = a) s = Some b")
   apply (clarsimp simp: affects_lrefl partitionIntegrity_cur_vcpu_Some cur_vcpu_for_def split: option.splits if_splits)
  apply (case_tac "\<exists>b. cur_vcpu_for (\<lambda>x. pasObjectAbs aag x = a) s' = Some b")
   apply (clarsimp simp: affects_lrefl partitionIntegrity_cur_vcpu_Some cur_vcpu_for_def split: option.splits if_splits)
  apply clarsimp
  apply (erule swap)
  apply (clarsimp simp: equiv_for_def cur_vcpu_of_def split: option.splits)
  done

lemma partitionIntegrity_subjectAffects_hw_vcpu:
   "\<lbrakk> invs s; invs s';
      cur_vcpu_in_cur_domain s; cur_vcpu_in_cur_domain s';
      pas_refined aag s; pas_refined aag s';
      pas_cur_domain aag s; pas_cur_domain aag s';
      pas_domains_distinct aag;
      \<not> equiv_for (\<lambda>x. pasObjectAbs aag x = a) hw_vcpu_of s s' \<rbrakk>
      \<Longrightarrow> a \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (case_tac "\<exists>b. cur_vcpu_for (\<lambda>x. pasObjectAbs aag x = a) s = Some b")
   apply (clarsimp simp: affects_lrefl partitionIntegrity_cur_vcpu_Some cur_vcpu_for_def split: option.splits if_splits)
  apply (case_tac "\<exists>b. cur_vcpu_for (\<lambda>x. pasObjectAbs aag x = a) s' = Some b")
   apply (clarsimp simp: affects_lrefl partitionIntegrity_cur_vcpu_Some cur_vcpu_for_def split: option.splits if_splits)
  apply clarsimp
  apply (clarsimp simp: equiv_for_def)
  apply (clarsimp simp: cur_vcpu_of_def cur_vcpu_for_def split: option.splits if_splits)
  done

lemma partitionIntegrity_subjectAffects_hyp:
   "\<lbrakk> partitionIntegrity aag s s';
      invs s; invs s';
      cur_vcpu_in_cur_domain s; cur_vcpu_in_cur_domain s';
      pas_refined aag s; pas_refined aag s';
      pas_cur_domain aag s; pas_cur_domain aag s';
      pas_domains_distinct aag;
      \<not> equiv_hyp (\<lambda>x. pasObjectAbs aag x = a) s s' \<rbrakk>
      \<Longrightarrow> a \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  unfolding equiv_hyp_def
  using partitionIntegrity_subjectAffects_numlistregs
        partitionIntegrity_subjectAffects_cur_vcpu_of
        partitionIntegrity_subjectAffects_hw_vcpu
  by (metis (mono_tags))

lemma cur_fpu_is_subject:
  "\<lbrakk> invs s; pas_refined aag s; pas_cur_domain aag s; pas_domains_distinct aag;
     cur_fpu_in_cur_domain s; current_fpu s = Some t \<rbrakk>
     \<Longrightarrow> is_subject aag t"
  apply (clarsimp simp: cur_fpu_in_cur_domain_def split: option.splits)
  apply (frule current_fpu_owner_Some_tcb_at, fastforce)
  apply (drule tcb_at_ko_at, clarsimp)
  apply (drule ko_at_etcbD)
  apply (frule (1) tcb_domain_wellformed)
  apply (prop_tac "etcb_domain (etcb_of tcb) = cur_domain s")
   apply (clarsimp simp: in_cur_domain_def)
   apply (clarsimp simp: etcbs_of'_def etcb_at'_def split: option.splits kernel_object.splits)
  apply simp
  apply (prop_tac "pasDomainAbs aag (cur_domain s) = {pasSubject aag}")
   apply (clarsimp simp: pas_domains_distinct_def)
   apply (metis singletonD)
  apply blast
  done

lemma partitionIntegrity_subjectAffects_fpu:
   "\<lbrakk> partitionIntegrity aag s s';
      invs s; invs s';
      cur_fpu_in_cur_domain s; cur_fpu_in_cur_domain s';
      pas_refined aag s; pas_refined aag s';
      pas_cur_domain aag s; pas_cur_domain aag s';
      pas_domains_distinct aag;
      \<not> equiv_fpu (\<lambda>x. pasObjectAbs aag x = a) s s' \<rbrakk>
      \<Longrightarrow> a \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  unfolding equiv_fpu_def
  apply (clarsimp simp: equiv_for_def)
  apply (case_tac "is_arch_cur_fpu x s")
   apply (frule (4) cur_fpu_is_subject[of s])
    apply (simp add: is_arch_cur_fpu_def)
   apply (clarsimp simp: affects_lrefl)
  apply (case_tac "is_arch_cur_fpu x s'")
   apply (frule (4) cur_fpu_is_subject[of s'])
    apply (simp add: is_arch_cur_fpu_def)
   apply (clarsimp simp: affects_lrefl)
  apply (clarsimp simp: hw_fpu_def)
  done

lemma partitionIntegrity_subjectAffects_tcb_fpu':
   "\<lbrakk> partitionIntegrity aag s s'; valid_cur_fpu s; valid_cur_fpu s';
      kheap s x = Some (TCB tcb); kheap s' x = Some (TCB tcb');
      tcb' = tcb\<lparr>tcb_arch := new_arch\<rparr>;
      arch_tcb_get_registers new_arch = arch_tcb_get_registers (tcb_arch tcb);
      tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb);
      current_fpu s \<noteq> Some x; current_fpu s' \<noteq> Some x \<rbrakk>
      \<Longrightarrow> is_subject aag x \<or> kheap s x = kheap s' x"
  apply clarsimp
  apply (erule_tac P="tcb = tcb\<lparr>tcb_arch := new_arch\<rparr>" in swap)
  apply (prop_tac "integrity_fpu (aag\<lparr>pasMayActivate := False, pasMayEditReadyQueues := False\<rparr>)
                                 {pasSubject aag} x s s'")
   apply (clarsimp simp: partitionIntegrity_def integrity_subjects_def)
  apply (clarsimp simp: integrity_fpu_def)
  apply (clarsimp simp: fpu_of_state_def)
  apply (clarsimp simp: valid_cur_fpu_def)
  apply (erule_tac x=x in allE)+
  apply (clarsimp simp: is_tcb_cur_fpu_def obj_at_def)
  apply (subgoal_tac "tcb_arch tcb = new_arch")
   apply (case_tac tcb; clarsimp)
  apply (subgoal_tac "tcb_context (tcb_arch tcb) = tcb_context new_arch")
   apply (case_tac "tcb_arch tcb"; case_tac new_arch; clarsimp simp: tcb_vcpu_refs_def split: option.splits)
  apply (case_tac "tcb_context (tcb_arch tcb)"; case_tac "tcb_context new_arch"; clarsimp simp: arch_tcb_get_registers_def)
  done

lemma partitionIntegrity_subjectAffects_tcb_fpu:
  assumes par_inte: "partitionIntegrity aag s s'"
  and "kheap s x = Some (TCB tcb)"
      "kheap s' x = Some (TCB tcb')"
      "tcb' = tcb\<lparr>tcb_arch := new_arch\<rparr>"
      "arch_tcb_get_registers new_arch = arch_tcb_get_registers (tcb_arch tcb)"
      "tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb)"
      "kheap s x \<noteq> kheap s' x"
      "silc_inv aag st s"
      "pas_wellformed_noninterference aag"
      "pas_refined aag s" "pas_refined aag s'"
      "pas_cur_domain aag s" "pas_cur_domain aag s'"
      "cur_fpu_in_cur_domain s" "cur_fpu_in_cur_domain s'"
      "invs s" "invs s'"
  notes inte_obj = par_inte[THEN partitionIntegrity_integrity, THEN integrity_subjects_obj,
                            THEN spec[where x=x], simplified integrity_obj_def, simplified]
  shows "subject_can_affect_label_directly aag (pasObjectAbs aag x)"
  apply (rule ssubst[where s="pasSubject aag", OF _ affects_lrefl])
  apply (case_tac "current_fpu s \<noteq> Some x \<and> current_fpu s' \<noteq> Some x"; clarsimp)
   using assms apply (fastforce dest!: partitionIntegrity_subjectAffects_tcb_fpu'[OF par_inte, rotated 7])
  apply (elim disjE; rule cur_fpu_is_subject; simp add: assms pas_wellformed_noninterference_domains_distinct)
  done

lemma partitionIntegrity_subjectAffects_asid[Noninterference_assms]:
  "\<lbrakk> partitionIntegrity aag s s'; pas_refined aag s; valid_objs s;
     valid_arch_state s; valid_arch_state s'; pas_wellformed_noninterference aag;
     silc_inv aag st s'; invs s'; \<not> equiv_asids (\<lambda>x. pasASIDAbs aag x = a) s s' \<rbrakk>
     \<Longrightarrow> a \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"
  apply (clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)
  apply (case_tac "arm_asid_table (arch_state s) (asid_high_bits_of asid) =
                   arm_asid_table (arch_state s') (asid_high_bits_of asid)")
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
                                 intro: pas_wellformed_pasSubject_update[simplified])+)[6]
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
                           equiv_for_def equiv_asids_def equiv_asid_def silc_dom_equiv_def
                           upto.simps equiv_hyp_def equiv_fpu_def cur_fpu_for_def)
   apply (rule affects_equiv_machine_state_update, assumption)
   apply (fastforce simp: equiv_for_def affects_equiv_def states_equiv_for_def upto.simps)
    apply (clarsimp simp: identical_hyp_state_updates_def identical_updates_rv_def)
   apply (clarsimp simp: identical_fpu_state_updates_def identical_updates_rv_def cur_fpu_for_def)
  apply (simp add: equiv_valid_def2 equiv_valid_2_def)
  done

declare set_vm_root_states_equiv_for[wp]

lemma set_vm_root_reads_respects:
  "reads_respects aag l \<top> (set_vm_root tcb)"
  by (rule reads_respects_unobservable_unit_return) wp+

lemmas set_vm_root_reads_respects_g[wp] =
  reads_respects_g[OF set_vm_root_reads_respects,
                   OF doesnt_touch_globalsI[where P="valid_global_arch_objs"],
                   simplified, OF set_vm_root_globals_equiv]

lemmas lazy_fpu_restore_reads_respects_g[wp] =
   reads_respects_g[OF lazy_fpu_restore_reads_respects,
                    OF doesnt_touch_globalsI[where P=invs],
                    simplified, OF lazy_fpu_restore_globals_equiv]

lemmas vcpu_switch_reads_respects_g[wp] =
   reads_respects_g[OF vcpu_switch_reads_respects,
                    OF doesnt_touch_globalsI[where P=valid_arch_state],
                    simplified, OF vcpu_switch_globals_equiv]

crunch vcpu_switch
  for global_pt[wp]: "\<lambda>s. P (global_pt s)"
  (wp: valid_global_arch_objs_lift)

crunch vcpu_switch
  for valid_global_arch_objs[wp]: "valid_global_arch_objs"
  (wp: valid_global_arch_objs_lift)

lemma arch_switch_to_thread_reads_respects_g'[Noninterference_assms]:
  "equiv_valid (reads_equiv_g aag) (affects_equiv aag l)
               (\<lambda>s s'. affects_equiv aag l s s' \<and>
                       arch_globals_equiv_strengthener (machine_state s) (machine_state s'))
               (\<lambda>s. invs s \<and> is_subject aag t)
               (arch_switch_to_thread t)"
  apply (simp add: arch_switch_to_thread_def)
  apply (wp bind_ev_general thread_get_reads_respects_g)
  apply (auto intro: sym_refs_VCPU_hyp_live simp: reads_equiv_g_def)
  done

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

lemmas dmo_mol_reads_respects_g[wp] =
  reads_respects_g[OF dmo_mol_reads_respects,
                   OF doesnt_touch_globalsI[where P="\<top>"],
                   simplified,
                   OF dmo_mol_globals_equiv]

lemma set_global_user_vspace_reads_respects_g[Noninterference_assms, wp]:
  "reads_respects_g aag l \<top> (set_global_user_vspace)"
  unfolding set_global_user_vspace_def setVSpaceRoot_def
  apply wpsimp
  apply (clarsimp simp: reads_equiv_g_def globals_equiv_def)
  done

lemma arch_switch_to_idle_thread_reads_respects_g[Noninterference_assms, wp]:
  "reads_respects_g aag l valid_arch_state (arch_switch_to_idle_thread)"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply wp
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
  apply (clarsimp simp: maxIRQ_def)
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
                            scheduler_globals_frame_equiv_def silc_dom_equiv_def idle_equiv_def equiv_hyp_def equiv_fpu_def cur_fpu_for_def)
     apply wp
    apply (rule_tac P="\<lambda>s. irq_masks_of_state st = irq_masks_of_state s" in gets_ev')
   apply wp
  apply clarsimp
  apply (simp add: scheduler_equiv_def)
  done

lemma integrity_hyp_update_reference_state[Noninterference_assms]:
   "is_subject aag t
    \<Longrightarrow> integrity_hyp aag {pasSubject aag} x s (s\<lparr>kheap := (kheap s)(t \<mapsto> blah)\<rparr>)"
  by (auto simp: integrity_hyp_def vcpu_integrity_def vcpu_of_state_def opt_map_def)

lemma integrity_fpu_update_reference_state[Noninterference_assms]:
  "is_subject aag t
   \<Longrightarrow> integrity_fpu aag {pasSubject aag} x s (s\<lparr>kheap := (kheap s)(t \<mapsto> blah)\<rparr>)"
  by (auto simp: integrity_fpu_def fpu_of_state_def)

definition irq_at' :: "bool \<Rightarrow> nat \<Rightarrow> (irq \<Rightarrow> bool) \<Rightarrow> irq option" where
  "irq_at' in_kernel pos masks \<equiv>
   let i = irq_oracle pos in (if masks i \<or> in_kernel \<and> i \<in> non_kernel_IRQs then None else Some i)"

lemma dmo_getActiveIRQ_wp':
  "\<lbrace>\<lambda>s. P (irq_at' in_kernel (irq_state (machine_state s) + 1) (irq_masks (machine_state s)))
          (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>)\<rbrace>
   do_machine_op (getActiveIRQ in_kernel)
   \<lbrace>P\<rbrace>"
  apply (simp add: do_machine_op_def getActiveIRQ_def non_kernel_IRQs_def)
  apply (wp modify_wp | wpc)+
  apply clarsimp
  apply (erule use_valid)
   apply (wp modify_wp)
  apply (auto simp: Let_def non_kernel_IRQs_def irq_at'_def split: if_splits)
  done

lemma getActiveIRQ_ev2[Noninterference_assms]:
  "equiv_valid_2 (scheduler_equiv aag)
                 (scheduler_affects_equiv aag l) (scheduler_affects_equiv aag l)
                 (\<lambda>irq irq'. irq = irq' \<or> irq = None \<and> irq' \<in> Some ` non_kernel_IRQs)
                 (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
                 (\<lambda>s. irq_masks_of_state st = irq_masks_of_state s)
   (do_machine_op (getActiveIRQ True)) (do_machine_op (getActiveIRQ False))"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (erule use_valid, rule dmo_getActiveIRQ_wp')+
  apply (intro conjI)
   apply (clarsimp simp: scheduler_equiv_def irq_at'_def Let_def)
   apply clarsimp
   apply (clarsimp simp: scheduler_equiv_def domain_fields_equiv_def globals_equiv_scheduler_def
                         silc_dom_equiv_def equiv_for_def)
  apply (clarsimp simp: scheduler_affects_equiv_def)
  apply (intro conjI impI)
    apply (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_hyp_def equiv_fpu_def cur_fpu_for_def)
   apply (clarsimp simp: scheduler_globals_frame_equiv_def)
  apply (clarsimp simp: arch_scheduler_affects_equiv_def)
  done

crunch arch_prepare_next_domain
  for work_units_completed[wp]: "\<lambda>s. P (work_units_completed s)"

lemma arch_prepare_next_domain_reads_respects:
  "reads_respects aag l invs arch_prepare_next_domain"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_from_labels)
        apply (rule arch_prepare_next_domain_states_equiv_valid)
       apply wpsimp+
  done

lemma arch_prepare_next_domain_reads_respects_g:
  "reads_respects_g aag l invs arch_prepare_next_domain"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g[OF arch_prepare_next_domain_reads_respects doesnt_touch_globalsI])
   apply wpsimp
   apply assumption
  apply clarsimp
  done

lemmas [Noninterference_assms] =
  arch_prepare_next_domain_reads_respects_g
  partitionIntegrity_subjectAffects_aobj
  partitionIntegrity_subjectAffects_hyp
  partitionIntegrity_subjectAffects_fpu
  partitionIntegrity_subjectAffects_tcb_fpu

end


arch_requalify_consts arch_globals_equiv_strengthener
arch_requalify_facts arch_globals_equiv_strengthener_thread_independent


global_interpretation Noninterference_1?: Noninterference_1 _ arch_globals_equiv_strengthener
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Noninterference_assms[folded cur_hyp_in_cur_domain_def])
qed


sublocale valid_initial_state \<subseteq> valid_initial_state?:
  Noninterference_valid_initial_state arch_globals_equiv_strengthener ..

end
