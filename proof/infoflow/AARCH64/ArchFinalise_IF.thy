(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_IF
imports Finalise_IF
begin

(* FIXME AARCH64 IF: clean and refactor theory *)

context Arch begin global_naming AARCH64

named_theorems Finalise_IF_assms

crunch arch_post_cap_deletion
  for globals_equiv[Finalise_IF_assms, wp]: "globals_equiv st"
  and valid_arch_state[Finalise_IF_assms,wp]: valid_arch_state

lemma dmo_maskInterrupt_reads_respects[Finalise_IF_assms]:
  "reads_respects aag l \<top> (do_machine_op (maskInterrupt m irq))"
  by wpsimp

lemma arch_post_cap_deletion_read_respects[Finalise_IF_assms, wp]:
  "reads_respects aag l \<top> (arch_post_cap_deletion acap)"
  by wpsimp

lemma equiv_asid_sa_update[Finalise_IF_assms, simp]:
  "equiv_asid asid (scheduler_action_update f s) s' = equiv_asid asid s s'"
  "equiv_asid asid s (scheduler_action_update f s') = equiv_asid asid s s'"
  by (auto simp: equiv_asid_def)

lemma equiv_asid_ready_queues_update[Finalise_IF_assms, simp]:
  "equiv_asid asid (ready_queues_update f s) s' = equiv_asid asid s s'"
  "equiv_asid asid s (ready_queues_update f s') = equiv_asid asid s s'"
  by (auto simp: equiv_asid_def)

lemma arch_finalise_cap_makes_halted[Finalise_IF_assms]:
  "\<lbrace>invs and valid_cap (ArchObjectCap arch_cap)
        and (\<lambda>s. ex = is_final_cap' (ArchObjectCap arch_cap) s)
        and cte_wp_at ((=) (ArchObjectCap arch_cap)) slot\<rbrace>
   arch_finalise_cap arch_cap ex
   \<lbrace>\<lambda>rv s. \<forall>t \<in> obj_refs_ac (fst rv). halted_if_tcb t s\<rbrace>"
  by (wpsimp simp: arch_finalise_cap_def)

(* FIXME: move *)
lemma set_object_modifies_at_most:
  "modifies_at_most aag {pasObjectAbs aag ptr}
                    (\<lambda>s. \<not> asid_pool_at ptr s \<and> (\<forall>asid_pool. obj \<noteq> ArchObj (ASIDPool asid_pool)))
                    (set_object ptr obj)"
  apply (rule modifies_at_mostI)
  apply (wp set_object_equiv_but_for_labels)
  apply clarsimp
  done

lemma set_thread_state_reads_respects[Finalise_IF_assms]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag l (\<lambda>s. is_subject aag (cur_thread s)) (set_thread_state ref ts)"
  unfolding set_thread_state_def fun_app_def
  apply (simp add: bind_assoc[symmetric])
  apply (rule pre_ev)
   apply (rule_tac P'=\<top> in bind_ev)
     apply (rule set_thread_state_act_reads_respects)
    apply (case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
     apply (wp set_object_reads_respects gets_the_ev)
     apply fastforce
    apply (clarsimp simp: equiv_for_def get_tcb_def)
    apply (simp add: equiv_valid_def2)
    apply (rule equiv_valid_rv_bind)
      apply (rule equiv_valid_rv_trivial)
      apply (wp | simp)+
     apply (rule_tac P=\<top> and P'=\<top> and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}"
                  in ev2_invisible[OF domains_distinct])
         apply (blast | simp add: labels_are_invisible_def)+
       apply (rule set_object_modifies_at_most)
      apply (rule set_object_modifies_at_most)
     apply (simp | wp)+
    apply (blast dest: get_tcb_not_asid_pool_at)
   apply (subst thread_set_def[symmetric, simplified fun_app_def])
   apply (wp | simp)+
  done

lemma set_thread_state_runnable_reads_respects[Finalise_IF_assms]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "runnable ts \<Longrightarrow> reads_respects aag l \<top> (set_thread_state ref ts)"
  unfolding set_thread_state_def fun_app_def
  apply (simp add: bind_assoc[symmetric])
  apply (rule pre_ev)
   apply (rule_tac P'=\<top> in bind_ev)
     apply (rule set_thread_state_act_runnable_reads_respects)
    apply (case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
     apply (wp set_object_reads_respects gets_the_ev)
     apply fastforce
    apply (clarsimp simp: equiv_for_def get_tcb_def)
    apply (simp add: equiv_valid_def2)
    apply (rule equiv_valid_rv_bind)
      apply (rule equiv_valid_rv_trivial)
      apply (wp | simp)+
     apply (rule_tac P=\<top> and P'=\<top> and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}"
                  in ev2_invisible[OF domains_distinct])
         apply (blast | simp add: labels_are_invisible_def)+
       apply (rule set_object_modifies_at_most)
      apply (rule set_object_modifies_at_most)
     apply (simp | wp)+
    apply (blast dest: get_tcb_not_asid_pool_at)
   apply (subst thread_set_def[symmetric, simplified fun_app_def])
   apply (wp thread_set_st_tcb_at | simp)+
  done

lemma set_bound_notification_none_reads_respects[Finalise_IF_assms]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag l \<top> (set_bound_notification ref None)"
  unfolding set_bound_notification_def fun_app_def
  apply (rule pre_ev(5)[where Q=\<top>])
   apply (case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
    apply (wp set_object_reads_respects gets_the_ev)[1]
    apply fastforce
   apply (clarsimp simp: equiv_for_def get_tcb_def)
   apply (simp add: equiv_valid_def2)
   apply (rule equiv_valid_rv_bind)
     apply (rule equiv_valid_rv_trivial)
     apply (wp | simp)+
    apply (rule_tac P=\<top> and P'=\<top> and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}"
                 in ev2_invisible[OF domains_distinct])
        apply (blast | simp add: labels_are_invisible_def)+
      apply (rule set_object_modifies_at_most)
     apply (rule set_object_modifies_at_most)
    apply (simp | wp)+
   apply (blast dest: get_tcb_not_asid_pool_at)
  apply simp
  done

lemma set_tcb_queue_reads_respects[Finalise_IF_assms, wp]:
  "reads_respects aag l \<top> (set_tcb_queue d prio queue)"
  unfolding equiv_valid_def2 equiv_valid_2_def
  apply (clarsimp simp: set_tcb_queue_def bind_def modify_def put_def get_def)
  apply (rule conjI)
   apply (rule reads_equiv_ready_queues_update, assumption)
   apply (fastforce simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def)
  apply (rule affects_equiv_ready_queues_update, assumption)
  apply (clarsimp simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def
                        equiv_asids_def equiv_asid_def)
  apply (rule ext)
  apply force
  done

lemma set_tcb_queue_modifies_at_most:
  "modifies_at_most aag L (\<lambda>s. pasDomainAbs aag d \<inter> L \<noteq> {}) (set_tcb_queue d prio queue)"
  apply (rule modifies_at_mostI)
  apply (simp add: set_tcb_queue_def modify_def, wp)
  apply (force simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def equiv_asids_def
                     equiv_hyp_def equiv_fpu_def cur_fpu_for_def get_tcb_def)
  done

lemma set_notification_equiv_but_for_labels[Finalise_IF_assms]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag ntfnptr \<in> L)\<rbrace>
   set_notification ntfnptr ntfn
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_simple_ko_def
  apply (wp set_object_equiv_but_for_labels get_object_wp)
  apply (clarsimp simp: asid_pool_at_kheap partial_inv_def obj_at_def split: kernel_object.splits)
  done

lemma thread_set_reads_respects[Finalise_IF_assms]:
  "reads_respects aag l \<top> (thread_set f thread)"
  apply (rule equiv_valid_guard_imp)
   apply (rule_tac ptr=thread in reads_respects_unit_cases)
  unfolding thread_set_def
     apply (rule gen_asm_ev)
     apply (wpsimp wp: set_object_reads_respects)
    apply (wpsimp wp: set_object_equiv_but_for_labels)
    apply (clarsimp simp: get_tcb_def obj_at_def)
   apply wpsimp+
  apply auto
  done

lemma aag_cap_auth_ASIDPoolCap:
  "pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap r asid)) \<Longrightarrow>
   pas_refined aag s \<Longrightarrow> is_subject aag r"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                cli_no_irqs pas_refined_all_auth_is_owns)

lemma aag_cap_auth_PageDirectory:
  "pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word pt_t (Some a))) \<Longrightarrow>
    pas_refined aag s \<Longrightarrow> is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                cli_no_irqs pas_refined_all_auth_is_owns)

lemma aag_cap_auth_ASIDPoolCap_asid:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap r asid)); asid' \<noteq> 0;
     asid_high_bits_of asid' = asid_high_bits_of asid; pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject_asid aag asid'"
  apply (frule (1) aag_cap_auth_ASIDPoolCap)
  apply (unfold aag_cap_auth_def)
  apply (rule is_subject_into_is_subject_asid)
  apply auto
  done

lemma aag_cap_auth_PageCap_asid:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (FrameCap dev ref r sz (Some (a, b)))); pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject_asid aag a"
  by (auto simp: aag_cap_auth_def cap_links_asid_slot_def label_owns_asid_slot_def
          intro: pas_refined_Control_into_is_subject_asid)

lemma aag_cap_auth_PageTableCap:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word pt_t option)); pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                cli_no_irqs pas_refined_all_auth_is_owns)

lemma aag_cap_auth_PageTableCap_asid:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word pt_t (Some (a, b)))); pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject_asid aag a"
  by (auto simp: aag_cap_auth_def cap_links_asid_slot_def label_owns_asid_slot_def
          intro: pas_refined_Control_into_is_subject_asid)

lemma aag_cap_auth_PageDirectoryCap:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word pt_t option));  pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject aag word"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                cli_no_irqs pas_refined_all_auth_is_owns)

lemma aag_cap_auth_PageDirectoryCap_asid:
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word pt_t (Some (a,vref)))); pas_refined aag s \<rbrakk>
     \<Longrightarrow> is_subject_asid aag a"
  unfolding aag_cap_auth_def
  by (auto simp: cap_links_asid_slot_def label_owns_asid_slot_def
          intro: pas_refined_Control_into_is_subject_asid)

lemmas aag_cap_auth_subject = aag_cap_auth_ASIDPoolCap_asid
                              aag_cap_auth_PageCap_asid
                              aag_cap_auth_PageTableCap_asid

(* Helpful groupings *)

definition fpu_save where
  "fpu_save \<equiv> do
     cur_fpu_owner \<leftarrow> gets (arm_current_fpu_owner \<circ> arch_state);
     do_machine_op enableFpu;
     maybeM save_fpu_state cur_fpu_owner
  od"

definition fpu_restore where
  "fpu_restore new_owner \<equiv> do
     case new_owner of None \<Rightarrow> do_machine_op disableFpu
        | Some tcb_ptr \<Rightarrow> load_fpu_state tcb_ptr;
     set_arm_current_fpu_owner new_owner
   od"

lemma dmo_enableFpu_reads_respects[wp]:
  "reads_respects_l aag l \<top> (do_machine_op enableFpu)"
  unfolding enableFpu_def dmo_distr
  apply wpsimp
     apply (wpsimp wp: do_machine_op_reads_respects_l modify_ev)
       apply (clarsimp simp: equiv_for_def)
      apply (wpsimp wp: dmo_mol_reads_respects_l)+
  done

lemma dmo_disableFpu_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (do_machine_op disableFpu)"
  unfolding disableFpu_def dmo_distr
  apply wpsimp
     apply (wpsimp wp: do_machine_op_reads_respects_l modify_ev)
       apply (clarsimp simp: equiv_for_def)
      apply (wpsimp wp: dmo_mol_reads_respects_l)+
  done

lemma switch_local_fpu_owner_def2:
  "switch_local_fpu_owner new_owner = do fpu_save; fpu_restore new_owner od"
  unfolding switch_local_fpu_owner_def fpu_save_def fpu_restore_def
  by (clarsimp simp: bind_assoc)

lemma valid_cur_fpu_cur_fpu_for:
  "valid_cur_fpu s \<Longrightarrow> cur_fpu_for P s = (\<exists>p. P p \<and> is_tcb_cur_fpu p s)"
  apply (clarsimp simp: cur_fpu_for_def valid_cur_fpu_def)
  apply (rule iffI; erule ex_forward)
   apply (clarsimp simp: valid_cur_fpu_def is_tcb_cur_fpu_def obj_at_def get_tcb_def is_arch_cur_fpu_def
                  split: option.splits kernel_object.splits)+
  done

lemma equiv_kheap_equiv_current_fpu:
  "\<lbrakk> equiv_for P kheap s t; valid_cur_fpu s; valid_cur_fpu t; cur_fpu_for P s; cur_fpu_for P t\<rbrakk>
     \<Longrightarrow> current_fpu s = current_fpu t"
  apply (clarsimp simp: valid_cur_fpu_cur_fpu_for valid_cur_fpu_def
                        equiv_for_def is_tcb_cur_fpu_def obj_at_def)
  apply (drule_tac x=p in spec)+
  apply auto
  done

lemma maybeM_when:
  "maybeM f opt = when (opt \<noteq> None) (f (the opt))"
  by (clarsimp simp: maybeM_def when_def)

lemma maybeM_ev:
  "\<lbrakk> \<And>v. opt = Some v \<Longrightarrow> equiv_valid_inv I A (P v) (f v) \<rbrakk>
     \<Longrightarrow> equiv_valid_inv I A (\<lambda>s. \<forall>v. opt = Some v \<longrightarrow> P v s) (maybeM f opt)"
  apply (subst maybeM_when)
  apply (rule equiv_valid_guard_imp)
   apply (rule_tac P="P (the opt)" in when_ev)
   apply auto
  done

lemma as_user_reads_respects_l_roa:
  "reads_respects_l aag l (K (det f \<and> (l (pasObjectAbs aag thread)))) (as_user thread f)"
  apply (simp add: as_user_def split_def)
  apply (rule gen_asm_ev)
  apply (wp set_object_reads_respects_l select_f_ev gets_the_ev)
  apply (auto simp: equiv_for_def get_tcb_def arch_tcb_context_set_def states_equiv_for_def)
  done

lemma reads_respects_l_unobservable_unit_return:
  assumes f:
    "\<And>P Q R S st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  shows
    "reads_respects_l aag l \<top> (f::(unit,det_ext) s_monad)"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (erule use_valid[OF _ f])
  apply (rule states_equiv_for_sym)
  apply (erule use_valid[OF _ f])
  apply (rule states_equiv_for_sym)
  apply simp
  done

lemma dmo_readFpuState_reads_respects_l:
  "reads_respects_l aag l (cur_fpu_for (l o pasObjectAbs aag)) (do_machine_op readFpuState)"
  (is "reads_respects_l _ _ ?P _")
  unfolding readFpuState_def dmo_distr
  apply (rule_tac Q="\<lambda>_. ?P" in bind_ev_pre)
     apply wpsimp
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: gets_ev')
     apply (clarsimp simp: pred_disj_def equiv_fpu_state_def hw_fpu_def)
    apply (rule reads_respects_l_unobservable_unit_return)
    apply (wpsimp wp: dmo_wp)+
  done

lemma det_setFPUStat[simp]:
  "det (setFPUState fpu)"
  by (wpsimp simp: setFPUState_def)

lemma thread_set_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag ptr \<in> L)\<rbrace>
   thread_set f ptr
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding thread_set_def
  apply (wpsimp wp: set_object_equiv_but_for_labels)
  apply (clarsimp simp: get_tcb_def obj_at_def split: option.splits kernel_object.splits)
  done

lemma as_user_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag ptr \<in> L)\<rbrace>
   as_user ptr f
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (rule as_user_wp_thread_set_helper)
  apply wpsimp
  done

lemma dmo_readFpuState_inv[wp]:
  "do_machine_op readFpuState \<lbrace>P\<rbrace>"
  by (wpsimp simp: readFpuState_def wp: dmo_wp)

lemma save_fpu_state_reads_respects_l:
  "reads_respects_l aag l (\<lambda>s. current_fpu s = Some ptr) (save_fpu_state ptr)"
  (is "reads_respects_l _ _ ?P _")
  unfolding save_fpu_state_def
  apply (rule equiv_valid_guard_imp)
   apply (rule_tac P="?P" and ptr=ptr in reads_respects_l_unit_cases)
     apply (wpsimp wp: as_user_reads_respects_l_roa dmo_readFpuState_reads_respects_l)
     apply (clarsimp simp: cur_fpu_for_def is_arch_cur_fpu_def)
    apply wpsimp+
  done

(* FIXME AARCH64 IF: move *)
locale_abbrev "cur_fpu_of s \<equiv> \<lambda>x. arm_current_fpu_owner (arch_state s) = Some x"

lemma equiv_fpu_def2:
  "equiv_fpu P s s' \<equiv> (\<forall>x. P x \<longrightarrow>
     (current_fpu s = Some x \<longleftrightarrow> current_fpu s' = Some x) \<and>
     (current_fpu s = Some x \<longrightarrow> machine_fpu s = machine_fpu s'))"
  apply (rule eq_reflection)
  apply (clarsimp simp: equiv_fpu_def equiv_for_def valid_cur_fpu_cur_fpu_for)
  apply (clarsimp simp: hw_fpu_def is_arch_cur_fpu_def)
  apply auto
  done

lemma dmo_disableFpu_machine_fpu[wp]:
  "do_machine_op disableFpu \<lbrace>\<lambda>s. P (machine_fpu s)\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma dmo_enableFpu_machine_fpu[wp]:
  "do_machine_op enableFpu \<lbrace>\<lambda>s. P (machine_fpu s)\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma tcb_at_typ_at':
  "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)
    \<Longrightarrow> \<lbrace>\<lambda>s. P (tcb_at c s)\<rbrace> f \<lbrace>\<lambda>rv s. P (tcb_at c s)\<rbrace>"
  by (simp add: tcb_at_typ)

lemma as_user_not_tcb_at[wp]:
  "as_user t m \<lbrace>\<lambda>s. \<not>tcb_at t' s\<rbrace>"
  by (wpsimp wp: tcb_at_typ_at'[OF as_user_typ_at])

crunch save_fpu_state
  for not_tcb_at[wp]: "\<lambda>s. \<not>tcb_at t s"

lemma fpu_of_Some_True[simp]:
  "fpu_of (Some True) fopt fpu = Some fpu"
  by (clarsimp simp: fpu_of_def)

lemma fpu_of_Some_False[simp]:
  "fpu_of (Some False) fopt fpu = fopt"
  by (clarsimp simp: fpu_of_def)

lemma fpu_of_None[simp]:
  "fpu_of None fopt fpu = None"
  by (clarsimp simp: fpu_of_def)

lemma valid_cur_fpu_current_fpu_Some:
  "\<lbrakk> valid_cur_fpu s; current_fpu s = Some t \<rbrakk>
     \<Longrightarrow> tcb_cur_fpu_of s t = Some True"
  apply (clarsimp simp: valid_cur_fpu_def)
  apply (erule_tac x=t in allE)
  apply (clarsimp simp: get_tcb_def is_tcb_cur_fpu_def obj_at_def)
  done

lemma save_fpu_state_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> pasObjectAbs aag ptr \<in> L\<rbrace>
   save_fpu_state ptr
  \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding save_fpu_state_def
  by wpsimp

lemma dmo_enableFpu_equiv_but_for_labels[wp]:
  "do_machine_op enableFpu \<lbrace>equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_lift)

lemma dmo_disableFpu_equiv_but_for_labels[wp]:
  "do_machine_op disableFpu \<lbrace>equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_lift)

lemma fpu_save_reads_respects_l:
  "reads_respects_l aag l valid_cur_fpu fpu_save"
  unfolding fpu_save_def
  apply (rule_tac P="cur_fpu_for (l o pasObjectAbs aag)" in equiv_valid_cases'')
    apply (fastforce simp: states_equiv_for_def comp_def equiv_fpu_cur_fpu_for)
   apply (wpsimp wp: maybeM_ev gets_ev'' save_fpu_state_reads_respects_l
                     hoare_vcg_imp_lift' hoare_vcg_all_lift)
     apply (rename_tac s t)
     apply (prop_tac "valid_cur_fpu s \<and> cur_fpu_for (l o pasObjectAbs aag) s")
      apply assumption
     apply (prop_tac "valid_cur_fpu t \<and> cur_fpu_for (l o pasObjectAbs aag) t")
      apply assumption
     apply clarsimp
     apply (prop_tac "equiv_for (l o pasObjectAbs aag) kheap s t")
      apply (fastforce simp: states_equiv_for_def comp_def)
     apply (clarsimp simp: equiv_kheap_equiv_current_fpu)
    apply wpsimp
   apply clarsimp
  apply (rule wp_pre)
   apply (simp add: equiv_valid_def2)
   apply (rule_tac R'="\<top>\<top>"
               and Q="\<lambda>rv. (\<lambda>s. current_fpu s = rv \<and> valid_cur_fpu s)
                       and K (\<forall>vr. rv = Some vr \<longrightarrow> \<not> l (pasObjectAbs aag vr))"
               and Q'="\<lambda>rv. (\<lambda>s. current_fpu s = rv \<and> valid_cur_fpu s)
                        and K (\<forall>vr. rv = Some vr \<longrightarrow> \<not> l (pasObjectAbs aag vr))"
                in equiv_valid_2_bind)
      apply (rule EquivValid.gen_asm_ev2_l)
      apply (rule EquivValid.gen_asm_ev2_r)
      prefer 2
      apply (rule gets_any_evrv)
     apply (rule equiv_valid_2_guard_imp)
       apply (rule reads_respects_l_2_invisible)
           apply (rule modifies_at_mostI)
           apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift)
          apply (rule modifies_at_mostI)
          apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift)
         apply wpsimp
        apply wpsimp
       apply clarsimp
      apply simp
     apply simp
    apply wpsimp+
  apply (clarsimp simp: cur_fpu_for_def is_arch_cur_fpu_def)
  done

lemma equiv_valid_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (i s)\<rbrace>"
  shows "equiv_valid (equiv_for P i) \<top>\<top> \<top>\<top> \<top> (f :: ('s state, unit) nondet_monad)"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
   apply (erule use_valid)
    apply (wpsimp wp: assms equiv_for_lift)
   apply (erule use_valid)
    apply (wpsimp wp: assms equiv_for_lift)
   apply clarsimp
  done

crunch getFPUState
  for inv[wp]: P

crunch load_fpu_state
  for kheap[wp]: "\<lambda>s. P (kheap s)"
  (wp: as_user_inv)

lemma set_object_equiv_kheap:
  "equiv_valid_inv (equiv_for P kheap) \<top>\<top> \<top> (set_object ptr obj)"
  by (clarsimp simp: equiv_valid_def2 equiv_valid_2_def set_object_def get_object_def
                     bind_def' get_def gets_def put_def return_def fail_def assert_def equiv_for_def)

lemma thread_set_kheap_equiv:
  "equiv_valid_inv (equiv_for P kheap) \<top>\<top> \<top> (thread_set f thread)"
  unfolding thread_set_def
  apply (case_tac "P thread")
   apply (wpsimp wp: set_object_equiv_kheap)
   apply (clarsimp simp: get_tcb_def equiv_for_def)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def set_object_def get_object_def
                        gets_the_def assert_opt_def get_tcb_def bind_def' get_def gets_def
                        put_def return_def fail_def assert_def equiv_for_def
                 split: option.splits kernel_object.splits)
  done

lemma arch_thread_set_kheap_equiv:
  "equiv_valid_inv (equiv_for P kheap) \<top>\<top> \<top> (arch_thread_set f thread)"
  by (wpsimp simp: arch_thread_set_is_thread_set wp: thread_set_kheap_equiv)

lemma gets_current_fpu_owner_equiv_kheap:
  "equiv_valid (equiv_for P kheap) (equiv_for P cur_fpu_of) (\<lambda>_ _. True)
               (valid_cur_fpu and cur_fpu_for P)
               (gets (arm_current_fpu_owner \<circ> arch_state))"
  (is "equiv_valid_inv _ _ ?P _")
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def gets_def get_def return_def bind_def)
  apply (clarsimp simp: equiv_for_def cur_fpu_for_def is_arch_cur_fpu_def)
  done

lemma equiv_valid_make_inv:
  assumes "equiv_valid_inv I A P f"
  shows "equiv_valid I A \<top>\<top> P f"
  using assms
  by (fastforce simp: equiv_valid_def2 equiv_valid_2_def)

lemma arch_thread_set_equiv_for_kheap:
  "\<lbrace>equiv_for P kheap st and K (\<not>P thread)\<rbrace>
   arch_thread_set f thread
   \<lbrace>\<lambda>_. equiv_for P kheap st\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  apply (clarsimp simp: equiv_for_def)
  done

lemma set_arm_current_fpu_owner_ev:
  "equiv_valid (equiv_for P kheap) (equiv_for P cur_fpu_of) \<top>\<top> (valid_cur_fpu)
    (do cur_fpu_owner <- gets (arm_current_fpu_owner \<circ> arch_state);
        maybeM (arch_thread_set (tcb_cur_fpu_update (\<lambda>_. False))) cur_fpu_owner
     od)"
  apply (rule_tac P="cur_fpu_for P" in equiv_valid_cases'')
    apply (fastforce simp: equiv_for_def cur_fpu_for_def is_arch_cur_fpu_def)
   apply (rule wp_pre)
    apply (rule bind_ev_general)
      apply (wp maybeM_ev)
      apply (wpsimp wp: maybeM_ev arch_thread_set_kheap_equiv)
     apply (wp gets_current_fpu_owner_equiv_kheap)
    apply wpsimp
   apply clarsimp
  apply (rule equiv_valid_make_inv)
  apply (rule equiv_valid_inv_lift)
    apply (wpsimp wp: arch_thread_set_equiv_for_kheap equiv_for_lift)
    apply (clarsimp simp: equiv_for_def cur_fpu_for_def is_arch_cur_fpu_def)
   apply (auto simp: equiv_for_sym)
  done

crunch load_fpu_state
  for valid_cur_fpu[wp]: valid_cur_fpu

lemma fpu_restore_equiv_kheap':
  "equiv_valid (equiv_for P kheap) (equiv_for P cur_fpu_of) \<top>\<top> valid_cur_fpu (fpu_restore new_owner)"
  unfolding fpu_restore_def set_arm_current_fpu_owner_def
  apply (rule equiv_valid_guard_imp)
   apply (rule_tac A=B and B=B for B in bind_ev_general)
     prefer 2
     apply (rule equiv_valid_inv_lift)
       apply (wpsimp wp: equiv_for_lift)+
      apply (fastforce simp: equiv_for_def)+
    apply simp
    apply (subst bind_assoc[symmetric])
    apply (rule bind_ev_general)
      prefer 2
      apply (rule set_arm_current_fpu_owner_ev)
     apply clarsimp
     apply (rule bind_ev_general)
       prefer 2
       apply (rule equiv_valid_lift)
       apply wpsimp
      apply (rule maybeM_ev)
      apply (rule arch_thread_set_kheap_equiv)
     apply wpsimp+
  done

lemma fpu_restore_equiv_kheap:
  "equiv_valid (equiv_for P kheap) (equiv_fpu P) \<top>\<top> valid_cur_fpu (fpu_restore new_owner)"
  apply (rule equiv_valid_conseq)
    apply (rule_tac P=P in fpu_restore_equiv_kheap')
   apply (clarsimp simp: equiv_fpu_def2 equiv_for_def)
  apply clarsimp
  done

crunch fpu_save
  for valid_cur_fpu[wp]: "valid_cur_fpu"
  (wp: crunch_wps)

lemma switch_local_fpu_owner_equiv_kheap:
  "equiv_valid \<top>\<top> (states_equiv_for_labels aag l) (equiv_for (l o pasObjectAbs aag) kheap)
               valid_cur_fpu (switch_local_fpu_owner new_owner :: (det_state,unit) nondet_monad)"
  unfolding switch_local_fpu_owner_def2
  apply (rule equiv_valid_guard_imp)
   apply (rule bind_ev_general)
     apply clarsimp
     apply (rule equiv_valid_conseq)
       apply (rule_tac P="l o pasObjectAbs aag" in fpu_restore_equiv_kheap)
      apply clarsimp
      apply (subst conj_assoc[symmetric])
      apply (rule conjI)
       apply assumption
      apply clarsimp
      apply (rule conjI)
       apply assumption
      apply assumption
     apply clarsimp
    apply (rule equiv_valid_conseq)
      apply (rule_tac aag=aag and l=l in fpu_save_reads_respects_l)
     apply clarsimp
     apply (rule conjI)
      apply assumption+
    apply clarsimp
    apply (clarsimp simp: comp_def states_equiv_for_def equiv_for_disj equiv_fpu_def)
   apply wpsimp
  apply simp
  done

definition states_equiv_for_non_fpu ::
  "(obj_ref \<Rightarrow> bool) \<Rightarrow> (irq \<Rightarrow> bool) \<Rightarrow> (asid \<Rightarrow> bool) \<Rightarrow>
   (domain \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equiv_for_non_fpu P Q R S s s' \<equiv>
     equiv_machine_state P (machine_state s) (machine_state s') \<and>
     equiv_for (P \<circ> fst) cdt s s' \<and>
     equiv_for (P \<circ> fst) cdt_list s s' \<and>
     equiv_for (P \<circ> fst) is_original_cap s s' \<and>
     equiv_for Q interrupt_states s s' \<and>
     equiv_for Q interrupt_irq_node s s' \<and>
     equiv_for S ready_queues s s' \<and>
     equiv_asids R s s' \<and>
     equiv_hyp P s s'"

lemma states_equiv_for_non_fpu_refl:
  "states_equiv_for_non_fpu P Q R S s s"
  by (auto simp: states_equiv_for_non_fpu_def intro: equiv_for_refl equiv_asids_refl equiv_hyp_refl)

lemma states_equiv_for_non_fpu_sym:
  "states_equiv_for_non_fpu P Q R S s t \<Longrightarrow> states_equiv_for_non_fpu P Q R S t s"
  by (auto simp: states_equiv_for_non_fpu_def intro: equiv_for_sym equiv_asids_sym equiv_fpu_sym equiv_hyp_sym)

lemma states_equiv_for_non_fpu_trans:
  "\<lbrakk> states_equiv_for_non_fpu P Q R S s t; states_equiv_for_non_fpu P Q R S t u \<rbrakk>
     \<Longrightarrow> states_equiv_for_non_fpu P Q R S s u"
  by (auto simp: states_equiv_for_non_fpu_def
          intro: equiv_for_trans equiv_asids_trans equiv_fpu_trans equiv_hyp_trans equiv_forI
           elim: equiv_forE)

abbreviation states_equiv_for_labels_non_fpu ::
  "'a PAS \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equiv_for_labels_non_fpu aag P \<equiv>
      states_equiv_for_non_fpu (\<lambda>x. P (pasObjectAbs aag x)) (\<lambda>x. P (pasIRQAbs aag x))
                               (\<lambda>x. P (pasASIDAbs aag x)) (\<lambda>x. \<exists>l\<in>pasDomainAbs aag x. P l)"

abbreviation reads_respects_l_non_fpu where
  "reads_respects_l_non_fpu aag L P f \<equiv> equiv_valid_inv \<top>\<top> (states_equiv_for_labels_non_fpu aag L) P f"

lemma states_equiv_for_non_fpu_symmetric:
  "states_equiv_for_non_fpu P Q R S s t \<Longrightarrow> states_equiv_for_non_fpu P Q R S t s"
  by (auto simp: states_equiv_for_non_fpu_sym)

lemma reads_respects_l_non_fpu_unobservable:
  assumes f:
    "\<And>P Q R S st. \<lbrace>states_equiv_for_non_fpu P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for_non_fpu P Q R S st\<rbrace>"
  assumes g:
    "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes h:
    "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes j:
    "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes k:
    "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace> f \<lbrace>\<lambda>rv s. P (work_units_completed s)\<rbrace>"
  assumes l:
    "\<And>P. \<lbrace>\<lambda>s. P (irq_state (machine_state s))\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_state (machine_state s))\<rbrace>"
  shows
    "reads_respects_l_non_fpu aag l \<top> (f :: (det_state,unit) nondet_monad)"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (rule states_equiv_for_non_fpu_symmetric)
  apply (erule use_valid)
   apply (wp assms)
  apply (rule states_equiv_for_non_fpu_symmetric)
  apply (erule use_valid)
   apply (wp assms)
  apply simp
  done

lemma equiv_hyp_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_state (machine_state s))\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (current_vcpu s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (numlistregs s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. equiv_hyp P st s\<rbrace>"
  unfolding equiv_hyp_def
  apply (wpsimp wp: equiv_for_lift assms)
  apply (rule hoare_weaken_pre)
   apply (wps assms)
    apply wpsimp+
  done

lemma switch_local_fpu_owner_states_equiv_for_non_hyp[wp]:
  "switch_local_fpu_owner vopt \<lbrace>states_equiv_for_non_fpu P Q R S st\<rbrace>"
  unfolding states_equiv_for_non_fpu_def
  by (wpsimp wp: equiv_machine_state_lift equiv_asids_lift equiv_hyp_lift equiv_for_lift dmo_wp)

lemma valid_cur_fpu_hw_fpu_of:
  "valid_cur_fpu s \<Longrightarrow>
   hw_fpu_of s t = (if current_fpu s = Some t
                    then fpu_of (tcb_cur_fpu_of s t) (tcb_fpu_of s t) (machine_fpu s)
                    else None)"
  supply if_split[split del]
  apply (subst fpu_of_def)
  apply (clarsimp simp: is_arch_cur_fpu_def hw_fpu_def)
  apply (case_tac "current_fpu s = Some t"; clarsimp)
  apply (frule (1) current_fpu_owner_Some_tcb_at)
  apply (clarsimp simp: tcb_at_def get_tcb_def split: option.splits kernel_object.splits)
  apply (clarsimp simp: valid_cur_fpu_def)
  apply (erule_tac x=t in allE)
  apply (clarsimp simp: is_tcb_cur_fpu_def obj_at_def)
  done

lemma set_arm_current_fpu_owner_current_fpu[wp]:
  "\<lbrace>\<lambda>s. P (new_owner)\<rbrace>
   set_arm_current_fpu_owner new_owner
   \<lbrace>\<lambda>_ s. P (current_fpu s)\<rbrace>"
  unfolding set_arm_current_fpu_owner_def
  apply wpsimp
  apply auto
  done

crunch switch_local_fpu_owner
  for valid_cur_fpu[wp]: valid_cur_fpu
  (wp: hoare_drop_imps)

lemma switch_local_fpu_owner_current_fpu[wp]:
  "\<lbrace>\<lambda>s. P (new_owner)\<rbrace>
   switch_local_fpu_owner new_owner
   \<lbrace>\<lambda>_ s. P (current_fpu s)\<rbrace>"
  unfolding switch_local_fpu_owner_def
  by wpsimp

lemma switch_local_fpu_owner_hw_fpu_of:
  "\<lbrace>\<lambda>s. valid_cur_fpu s \<and> fopt = (if new_owner \<noteq> Some ptr then None
                                  else if hw_fpu_of s ptr = None then tcb_fpu_of s ptr
                                  else hw_fpu_of s ptr)\<rbrace>
   switch_local_fpu_owner new_owner
   \<lbrace>\<lambda>_ s. fopt = hw_fpu_of s ptr\<rbrace>"
  apply (rule_tac Q'="\<lambda>_ s. valid_cur_fpu s \<and>
                            (current_fpu s = Some ptr \<longrightarrow> fopt = fpu_of (tcb_cur_fpu_of s ptr)
                                                                        (tcb_fpu_of s ptr) (machine_fpu s)) \<and>
                            (current_fpu s \<noteq> Some ptr \<longrightarrow> fopt = None)"
               in hoare_strengthen_post[rotated])
   apply (clarsimp simp: valid_cur_fpu_hw_fpu_of)
  apply (rule wp_pre)
   apply (rule hoare_vcg_conj_lift)
    apply wpsimp
   apply (rule hoare_vcg_conj_lift)
    apply (rule hoare_vcg_imp_lift')
     apply wp
    apply (wp switch_local_fpu_owner_fpu_of)
   apply wp
  apply (clarsimp simp: valid_cur_fpu_hw_fpu_of split: if_splits)
   apply (simp add: valid_cur_fpu_current_fpu_Some)
  apply (clarsimp simp: fpu_of_def get_tcb_def split: option.splits bool.splits kernel_object.splits)
  by (simp add: valid_cur_fpu_defs(1,2,3))

lemma switch_local_fpu_owner_equiv_fpu:
  "equiv_valid (equiv_fpu P) (equiv_for P kheap) \<top>\<top> valid_cur_fpu (switch_local_fpu_owner new_owner)"
  apply (clarsimp simp: equiv_fpu_def equiv_valid_def2 equiv_valid_2_def)
  apply (rename_tac s' t')
  apply (clarsimp simp: equiv_for_def)
  apply (erule_tac x=x in allE)+
  apply clarsimp
  apply (rule sym)
  apply (erule use_valid)
   apply (rule switch_local_fpu_owner_hw_fpu_of)
  apply (rule conjI, simp)
  apply (rule sym)
  apply (erule use_valid)
   apply (rule switch_local_fpu_owner_hw_fpu_of)
  apply (rule conjI, simp)
  apply (case_tac "new_owner \<noteq> Some x")
   apply clarsimp
  apply (case_tac "hw_fpu_of s x = None")
   apply (clarsimp simp: get_tcb_def)
  apply clarsimp
  done

lemma switch_local_fpu_owner_reads_respects_l[wp]:
  "reads_respects_l aag l (valid_cur_fpu) (switch_local_fpu_owner new_owner)"
  apply (rule equiv_valid_conseq)
    apply (rule equiv_valid_split)
     apply (rule reads_respects_l_non_fpu_unobservable[of _ l aag])
          apply ((wpsimp simp: fpu_restore_def wp: dmo_wp)+)[6]
    apply (rule equiv_valid_split)
     apply (rule_tac aag=aag and l=l in switch_local_fpu_owner_equiv_kheap)
    apply (rule_tac P="l o pasObjectAbs aag" in switch_local_fpu_owner_equiv_fpu)
   apply (clarsimp simp: states_equiv_for_def states_equiv_for_non_fpu_def comp_def)+
  done

lemma switch_local_fpu_owner_reads_respects[wp]:
  "reads_respects aag l (valid_cur_fpu) (switch_local_fpu_owner new_owner)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_from_labels)
        apply (rule switch_local_fpu_owner_reads_respects_l)
       apply wpsimp+
  done

lemma arch_thread_set_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag t \<in> L)\<rbrace>
   arch_thread_set f t
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_equiv_but_for_labels)
  apply (clarsimp simp: get_tcb_def obj_at_def split: option.splits kernel_object.splits)
  done

lemma modify_current_fpu_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and>
        (\<forall>t. current_fpu s = Some t \<longrightarrow> pasObjectAbs aag t \<in> L) \<and>
        (\<forall>t. new_owner = Some t \<longrightarrow> pasObjectAbs aag t \<in> L)\<rbrace>
   modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_fpu_owner := new_owner\<rparr>\<rparr>)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply wp
  apply (subst equiv_but_for_labels_def)
  apply (subst states_equiv_for_def)
  apply (intro conjI; (clarsimp simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def; fail)?)
    apply (clarsimp simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def)
    apply (clarsimp simp: equiv_asids_def equiv_asid_def)
   apply (clarsimp simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def)
   apply (clarsimp simp: equiv_hyp_def equiv_for_def)
  apply (prop_tac "equiv_fpu (\<lambda>x. pasObjectAbs aag x \<notin> L) st s")
   apply (clarsimp simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def)
  apply (erule equiv_fpu_trans)
  apply (clarsimp simp: equiv_fpu_def)
  apply (clarsimp simp: equiv_for_def)
  apply (clarsimp simp: is_arch_cur_fpu_def)
  apply (clarsimp simp: hw_fpu_def)
  apply auto
  done

lemma set_arm_current_fpu_owner_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> (\<forall>t. new_owner = Some t \<longrightarrow> pasObjectAbs aag t \<in> L) \<and>
                                          (\<forall>t. current_fpu s = Some t \<longrightarrow> pasObjectAbs aag t \<in> L)\<rbrace>
   set_arm_current_fpu_owner new_owner
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_arm_current_fpu_owner_def
  by (wpsimp wp_del: modify_wp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift modify_current_fpu_equiv_but_for_labels)

lemma dmo_equiv_but_for_labels_fpu:
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (irq_state ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (vcpu_state ms)\<rbrace>"
  shows "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> \<not>cur_fpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s\<rbrace>
         do_machine_op f
         \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding equiv_but_for_labels_def states_equiv_for_def equiv_asids_def cur_fpu_for_def
  apply wp
   apply clarsimp
   apply (rule hoare_vcg_conj_lift, solves "wpsimp wp: equiv_for_lift equiv_hyp_lift assms dmo_wp")+
   apply (rule hoare_vcg_conj_lift)
    apply (clarsimp simp: equiv_fpu_def)
    apply (rule_tac Q'="\<lambda>_ s. (\<forall>x. pasObjectAbs aag x \<notin> L \<longrightarrow> hw_fpu_of st x = None) \<and>
                              \<not>cur_fpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s"
                 in hoare_strengthen_post)
     apply (wpsimp wp: equiv_for_lift2 assms dmo_wp simp: cur_fpu_for_def)
    apply (clarsimp simp: equiv_for_def hw_fpu_def)
    apply (erule_tac x=x in allE)
    apply (clarsimp split: if_splits)
    apply (fastforce simp: cur_fpu_for_def)
   apply (wpsimp wp: equiv_for_lift equiv_hyp_lift assms dmo_wp)
  apply clarsimp
  apply (clarsimp simp: equiv_fpu_def)
  apply (fastforce simp: equiv_for_def cur_fpu_for_def hw_fpu_def split: if_splits)
  done

lemma as_user_cur_fpu_for[wp]:
  "as_user t f \<lbrace>\<lambda>s. P (cur_fpu_for R s)\<rbrace>"
  apply (wpsimp wp: as_user_wp_thread_set_helper thread_set_wp)
  apply (auto elim!: rsubst[where P=P]
               simp: get_tcb_def cur_fpu_for_def arch_tcb_context_get_def arch_tcb_context_set_def)
  done

lemma dmo_cur_fpu_for[wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (cur_fpu_for R s)\<rbrace>"
  by (wpsimp wp: dmo_wp simp: cur_fpu_for_def)

crunch save_fpu_state
  for cur_fpu_for[wp]: "\<lambda>s. P (cur_fpu_for R s)"

lemma load_fpu_state_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> \<not>cur_fpu_for (\<lambda>a. pasObjectAbs aag a \<notin> L) s\<rbrace>
   load_fpu_state t
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding load_fpu_state_def
  by (wpsimp wp: dmo_equiv_but_for_labels_fpu as_user_inv)

lemma switch_local_fpu_owner_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> (\<forall>t. cur_fpu_of s t \<longrightarrow> pasObjectAbs aag t \<in> L) \<and>
                                          (\<forall>t. new_owner = Some t \<longrightarrow> pasObjectAbs aag t \<in> L)\<rbrace>
   switch_local_fpu_owner new_owner
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding switch_local_fpu_owner_def
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
  apply (prop_tac "equiv_fpu (\<lambda>a. pasObjectAbs aag a \<notin> L) st s")
   apply (clarsimp simp: equiv_but_for_labels_def states_equiv_for_def)
  apply (clarsimp simp: cur_fpu_for_def is_arch_cur_fpu_def)
  done

lemma fpu_release_reads_respects:
  "reads_respects aag l valid_cur_fpu (fpu_release t)"
  unfolding fpu_release_def
  apply (rule equiv_valid_guard_imp)
   apply (subst gets_comp)
   apply (rule_tac P=valid_cur_fpu and ptr=t in reads_respects_unit_cases)
     apply (rule equiv_valid_guard_imp)
      apply wp
        apply (wpsimp wp: when_ev)
       prefer 2
       apply wpsimp
      apply (wpsimp wp: gets_ev'')
      apply (prop_tac "valid_cur_fpu x \<and>  aag_can_read_or_affect aag l t")
       apply assumption
      apply (prop_tac "valid_cur_fpu xa \<and>  aag_can_read_or_affect aag l t")
       apply assumption
      apply (prop_tac "equiv_fpu (aag_can_read_or_affect aag l) x xa \<and>
                       equiv_for (aag_can_read_or_affect aag l) kheap x xa ")
       apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2
                             states_equiv_for_def equiv_for_disj equiv_fpu_def)
      apply clarsimp
      apply (clarsimp simp: valid_cur_fpu_def equiv_for_def is_tcb_cur_fpu_def obj_at_def)
      apply fastforce
     apply clarsimp
    apply wpsimp+
      apply (wp switch_local_fpu_owner_equiv_but_for_labels)
     apply (clarsimp split del: if_split cong: if_cong conj_cong)
     apply wp
    apply clarsimp
   apply wpsimp+
  done

lemma prepare_thread_delete_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag and valid_arch_state and valid_cur_fpu and K (is_subject aag thread))
                              (prepare_thread_delete thread)"
  unfolding prepare_thread_delete_def
  apply (wpsimp wp: fpu_release_reads_respects dissociate_vcpu_tcb_reads_respects hoare_vcg_imp_lift'
         | rule arch_thread_get_wp)+
  apply (subgoal_tac "is_subject aag x")
   apply fastforce
  apply (erule associated_vcpu_is_subject)
    apply (simp add: get_tcb_ko_at)
   apply simp
  apply simp
  done

lemma prepare_thread_delete_reads_respects_f[Finalise_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_f aag l (silc_inv aag st and pas_refined aag and valid_arch_state
                                                 and valid_cur_fpu and K (is_subject aag thread))
                                (prepare_thread_delete thread)"
  apply (rule equiv_valid_guard_imp)
   apply (wpsimp wp: reads_respects_f[OF prepare_thread_delete_reads_respects, where st=st])+
  done

lemma vcpu_finalise_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag and valid_arch_state and K (is_subject aag vr)) (vcpu_finalise vr)"
  unfolding vcpu_finalise_def
  apply (rule gen_asm_ev)
  apply (wpsimp wp: dissociate_vcpu_tcb_reads_respects get_vcpu_wp)
  apply (fastforce dest: associated_tcb_is_subject)
  done

lemma arch_finalise_cap_reads_respects[Finalise_IF_assms]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pas_refined aag and invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
                                         and K (pas_cap_cur_auth aag (ArchObjectCap cap)))
                        (arch_finalise_cap cap final)"
  unfolding arch_finalise_cap_def
  apply (rule gen_asm_ev)
  apply (case_tac cap)
     apply simp
     apply (simp split: bool.splits)
     apply (intro impI conjI)
         apply (wp delete_asid_pool_reads_respects unmap_page_reads_respects unmap_page_table_reads_respects
                   delete_asid_reads_respects find_vspace_for_asid_reads_respects vcpu_finalise_reads_respects
                | simp add: invs_psp_aligned invs_vspace_objs invs_valid_objs valid_cap_def
                            valid_arch_state_asid_table invs_arch_state wellformed_mapdata_def
                     split: option.splits bool.splits pt_type.splits
                | intro impI conjI allI
                | elim conjE
                | drule cte_wp_valid_cap
                | fastforce dest: aag_can_read_own_asids aag_cap_auth_subject)+
     apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
     apply (drule (1) pas_refined_Control, clarsimp)
    apply (wp delete_asid_pool_reads_respects unmap_page_reads_respects unmap_page_table_reads_respects
              delete_asid_reads_respects find_vspace_for_asid_reads_respects vcpu_finalise_reads_respects
           | simp add: invs_psp_aligned invs_vspace_objs invs_valid_objs valid_cap_def
                       valid_arch_state_asid_table invs_arch_state wellformed_mapdata_def
                split: option.splits bool.splits pt_type.splits
           | intro impI conjI allI
           | elim conjE
           | drule cte_wp_valid_cap
           | fastforce dest: aag_can_read_own_asids aag_cap_auth_subject)+
  done

(*NOTE: Required to dance around the issue of the base potentially
        being zero and thus we can't conclude it is in the current subject.*)
lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq':
  "\<lbrakk> pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap p b)); reads_equiv aag s t; pas_refined aag x \<rbrakk>
     \<Longrightarrow> asid_table s (asid_high_bits_of b) =
         asid_table t (asid_high_bits_of b)"
  apply (subgoal_tac "asid_high_bits_of 0 = asid_high_bits_of 1")
   apply (case_tac "b = 0")
    apply (subgoal_tac "is_subject_asid aag 1")
     apply ((fastforce intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq
                              aag_cap_auth_ASIDPoolCap_asid
                    simp del: asid_high_bits_of_0)+)[2]
   apply (auto intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq
                      aag_cap_auth_ASIDPoolCap_asid)[1]
  apply (simp add: asid_high_bits_of_def asid_low_bits_def)
  done

lemma pt_cap_aligned:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PageTableCap word pt_t x)); valid_caps (caps_of_state s) s \<rbrakk>
     \<Longrightarrow> is_aligned word (pt_bits pt_t)"
  by (auto simp: obj_ref_of_def pt_bits_def pageBits_def
          dest!: cap_aligned_valid[OF valid_capsD, unfolded cap_aligned_def, THEN conjunct1])

lemma maskInterrupt_no_mem:
  "maskInterrupt a b \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  by (wpsimp simp: maskInterrupt_def)

lemma set_irq_state_valid_global_objs:
  "set_irq_state state irq \<lbrace>valid_global_objs\<rbrace>"
  apply (simp add: set_irq_state_def)
  apply (wp modify_wp)
  apply (fastforce simp: valid_global_objs_def)
  done

lemma set_irq_state_globals_equiv[Finalise_IF_assms]:
  "set_irq_state state irq \<lbrace>globals_equiv st\<rbrace>"
  apply (simp add: set_irq_state_def)
  apply (wp dmo_no_mem_globals_equiv maskInterrupt_no_mem modify_wp)
  apply (simp add: globals_equiv_interrupt_states_update)
  done

lemma set_notification_globals_equiv[Finalise_IF_assms]:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   set_notification ptr ntfn
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding set_simple_ko_def
  apply (wp set_object_globals_equiv get_object_wp)
  apply (fastforce simp: obj_at_def valid_arch_state_def dest: valid_global_arch_objs_pt_at)
  done

lemma delete_asid_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   delete_asid asid pt
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding delete_asid_def
  by (wpsimp wp: set_vm_root_globals_equiv set_asid_pool_globals_equiv hoare_drop_imps)

lemma vcpu_finalise_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and invs\<rbrace>
   vcpu_finalise vr
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding vcpu_finalise_def
  apply (wpsimp wp: dissociate_vcpu_tcb_globals_equiv get_vcpu_wp)
  apply (rule conjI, fastforce)
    (* FIXME AARCH64 IF: boilerplate *)
  apply (rename_tac s' vcpu tcb)
  apply clarsimp
  apply (prop_tac "(idle_thread s', HypTCBRef) \<in> state_hyp_refs_of s' vr")
   apply (clarsimp simp: state_hyp_refs_of_def opt_map_def split: option.splits)
  apply (drule sym_refsD)
   apply (erule invs_hyp_sym_refs)
  apply (clarsimp simp: obj_at_vcpu_hyp_live_of_s[symmetric] is_vcpu_def
                     state_hyp_refs_of_def obj_at_def hyp_live_def hyp_refs_of_def
                     tcb_vcpu_refs_def refs_of_ao_def arch_live_def vcpu_tcb_refs_def
              split: option.splits kernel_object.splits arch_kernel_obj.splits)
  apply (frule invs_valid_idle)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def)
  apply (frule invs_iflive)
  apply (frule invs_valid_global_refs)
  apply (frule invs_valid_objs)
  apply (drule (1) idle_no_ex_cap)
  apply (erule swap, erule if_live_then_nonz_capD)
   apply simp
  apply clarsimp
  apply (clarsimp simp: live_def hyp_live_def)
  done

lemma arch_finalise_cap_globals_equiv[Finalise_IF_assms]:
  "\<lbrace>globals_equiv st and invs and valid_arch_cap cap\<rbrace>
   arch_finalise_cap cap b
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (induct cap; simp add: arch_finalise_cap_def)
  by (wp delete_asid_pool_globals_equiv case_option_wp unmap_page_globals_equiv
         unmap_page_table_globals_equiv delete_asid_globals_equiv
      | wpc | fastforce simp: valid_arch_cap_def wellformed_mapdata_def)+

lemma arch_thread_set_fpu_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   arch_thread_set (tcb_cur_fpu_update f) t
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding arch_thread_set_is_thread_set
  by (wpsimp wp: thread_set_globals_equiv simp: arch_tcb_context_get_def)

lemma globals_equiv_fpu_owner_update[simp]:
  "globals_equiv st (s\<lparr>arch_state := arch_state s\<lparr>arm_current_fpu_owner := cf\<rparr>\<rparr>) = globals_equiv st s"
  by (auto simp: globals_equiv_def)

lemma set_arm_current_fpu_owner_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   set_arm_current_fpu_owner new_owner
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding set_arm_current_fpu_owner_def
  by (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)+

lemma load_fpu_state_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   load_fpu_state t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding load_fpu_state_def
  by (wpsimp wp: dmo_globals_equiv)

lemma save_fpu_state_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   save_fpu_state t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding save_fpu_state_def
  by (wpsimp wp: dmo_globals_equiv)

crunch load_fpu_state, save_fpu_state
  for valid_arch_state[wp]: valid_arch_state

(* FIXME AARCH64 IF: move *)
lemma switch_local_fpu_owner_Some_globals_equiv:
  "\<lbrace>globals_equiv st and invs and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   switch_local_fpu_owner (Some t)
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding switch_local_fpu_owner_def
  apply (wpsimp wp: set_arm_current_fpu_owner_globals_equiv dmo_globals_equiv
                    load_fpu_state_globals_equiv save_fpu_state_globals_equiv
                    hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (fastforce simp: invs_def valid_state_def valid_pspace_def valid_cur_fpu_def
                         is_tcb_cur_fpu_def live_def arch_tcb_live_def
                   dest: idle_no_ex_cap if_live_then_nonz_capD)
  done

lemma switch_local_fpu_owner_None_globals_equiv:
  "\<lbrace>globals_equiv st and invs\<rbrace>
   switch_local_fpu_owner None
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding switch_local_fpu_owner_def
  apply (wpsimp wp: set_arm_current_fpu_owner_globals_equiv dmo_globals_equiv
                    load_fpu_state_globals_equiv save_fpu_state_globals_equiv
                    hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (fastforce simp: invs_def valid_state_def valid_pspace_def valid_cur_fpu_def
                          is_tcb_cur_fpu_def live_def arch_tcb_live_def
                    dest: idle_no_ex_cap if_live_then_nonz_capD)
  done

declare dissociate_vcpu_tcb_globals_equiv[wp del]

(* FIXME AARCH64 IF: consolidate *)
lemma dissociate_vcpu_tcb_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and invs\<rbrace>
   dissociate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  apply (wpsimp wp: as_user_globals_equiv simp: arch_tcb_context_get_def as_user_bind)
       apply (rule_tac Q'="\<lambda>_ s. arm_current_vcpu (arch_state s) = None" in hoare_post_add)
       apply (clarsimp cong: conj_cong)
       apply (wpsimp wp: get_vcpu_wp arch_thread_get_wp)+
  apply (subgoal_tac "(\<forall>tcb. ko_at (TCB tcb) t sa \<longrightarrow>
                        (\<forall>v. vcpus_of sa vr = Some v \<longrightarrow>
                             tcb_vcpu (tcb_arch tcb) = Some vr \<and> vcpu_tcb v = Some t \<longrightarrow>
                             t \<noteq> idle_thread sa))")
   apply fastforce
  apply clarsimp
    (* FIXME AARCH64 IF: boilerplate *)
  apply (rename_tac s' tcb vcpu)
  apply (prop_tac "(idle_thread s', HypTCBRef) \<in> state_hyp_refs_of s' vr")
   apply (clarsimp simp: state_hyp_refs_of_def opt_map_def split: option.splits)
  apply (drule sym_refsD)
   apply (erule invs_hyp_sym_refs)
  apply (clarsimp simp: obj_at_vcpu_hyp_live_of_s[symmetric] is_vcpu_def
                        state_hyp_refs_of_def obj_at_def hyp_live_def hyp_refs_of_def
                        tcb_vcpu_refs_def refs_of_ao_def arch_live_def vcpu_tcb_refs_def
                 split: option.splits kernel_object.splits arch_kernel_obj.splits)
  apply (frule invs_valid_idle)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def)
  apply (frule invs_iflive)
  apply (frule invs_valid_global_refs)
  apply (frule invs_valid_objs)
  apply (drule (1) idle_no_ex_cap)
  apply (erule swap, erule if_live_then_nonz_capD)
   apply simp
  apply clarsimp
  apply (clarsimp simp: live_def hyp_live_def)
  done

lemma fpu_release_globals_equiv:
  "\<lbrace>globals_equiv st and invs\<rbrace>
   fpu_release t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding fpu_release_def
  by (wpsimp wp: switch_local_fpu_owner_None_globals_equiv)

lemma prepare_thread_delete_globals_equiv[Finalise_IF_assms, wp]:
  "\<lbrace>globals_equiv s and invs\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding prepare_thread_delete_def
  by (wpsimp wp: fpu_release_globals_equiv hoare_drop_imps)

declare arch_get_sanitise_register_info_def[simp]

lemma set_bound_notification_globals_equiv[Finalise_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_bound_notification ref ts
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_bound_notification_def
  apply (wp set_object_globals_equiv dxo_wp_weak |simp)+
  apply (intro impI conjI allI)
  by (fastforce simp: valid_arch_state_def obj_at_def tcb_at_def2 get_tcb_def is_tcb_def
                dest: get_tcb_SomeD valid_global_arch_objs_pt_at
               split: option.splits kernel_object.splits)+

end


global_interpretation Finalise_IF_1?: Finalise_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Finalise_IF_assms)?)
qed

end
