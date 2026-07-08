(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchArch_IF
imports Arch_IF
begin

(* FIXME AARCH64 IF: clean and refactor theory *)

(* FIXME AARCH64 IF: consider modelling some of these *)
axiomatization dmo_reads_respects where
  dmo_getESR_reads_respects: "reads_respects aag l \<top> (do_machine_op AARCH64.getESR)" and
  dmo_getFAR_reads_respects: "reads_respects aag l \<top> (do_machine_op AARCH64.getFAR)" and
  dmo_doSMC_mop_reads_respects: "reads_respects aag l \<top> (do_machine_op (AARCH64.doSMC_mop args))" and
  dmo_addressTranslateS1_reads_respects: "reads_respects aag l \<top> (do_machine_op (AARCH64.addressTranslateS1 w))"


context Arch begin global_naming AARCH64

named_theorems Arch_IF_assms

(* we need to know we're not doing an asid pool update, or else this could affect
   what some other domain sees *)
lemma set_object_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and (\<lambda> s. \<not> asid_pool_at ptr s) and
    K ((\<forall>asid_pool. obj \<noteq> ArchObj (ASIDPool asid_pool)) \<and> pasObjectAbs aag ptr \<in> L)\<rbrace>
   set_object ptr obj
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: equiv_but_for_labels_def)
  apply (subst dummy_kheap_update[where st=st])
  apply (rule states_equiv_for_non_asid_pool_kheap_update)
     apply assumption
    apply (fastforce intro: equiv_forI elim: states_equiv_forE equiv_forE)
   apply (fastforce simp: non_asid_pool_kheap_update_def)
  apply (clarsimp simp: non_asid_pool_kheap_update_def asid_pool_at_kheap)
  done

lemma get_tcb_not_asid_pool_at:
  "get_tcb ref s = Some y \<Longrightarrow> \<not> asid_pool_at ref s"
  by (fastforce simp: get_tcb_def asid_pool_at_kheap)

lemma as_user_set_register_ev2:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "labels_are_invisible aag l (pasObjectAbs aag ` {thread,thread'})
         \<Longrightarrow> equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=) \<top> \<top>
                           (as_user thread (setRegister x y)) (as_user thread' (setRegister a b))"
  apply (simp add: as_user_def)
  apply (rule equiv_valid_2_guard_imp)
    apply (rule_tac L="{pasObjectAbs aag thread}" and L'="{pasObjectAbs aag thread'}"
                and Q="\<top>" and Q'="\<top>" in ev2_invisible[OF domains_distinct])
        apply (simp add: labels_are_invisible_def)+
      apply ((rule modifies_at_mostI
              | wp set_object_equiv_but_for_labels
              | simp add: split_def
              | fastforce dest: get_tcb_not_asid_pool_at)+)[2]
    apply auto
  done

crunch arch_post_cap_deletion
  for valid_global_refs[Arch_IF_assms, wp]: "valid_global_refs"

crunch store_word_offs
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: storeWord_def)

crunch set_irq_state, arch_post_cap_deletion, handle_arch_fault_reply
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps maskInterrupt_def)

crunch readVCPUHardwareReg, check_export_arch_timer, writeVCPUHardwareReg, maskInterrupt,
       enableFpuEL01, isb, dsb, setHCR, setSCTLR, sendSGI, set_gic_vcpu_ctrl_hcr,
       set_gic_vcpu_ctrl_lr, set_gic_vcpu_ctrl_apr, set_gic_vcpu_ctrl_vmcr, get_gic_vcpu_ctrl_hcr,
       get_gic_vcpu_ctrl_lr, get_gic_vcpu_ctrl_apr, get_gic_vcpu_ctrl_vmcr, do_flush,
       invalidateTranslationASID, writeFpuState, disableFpu, enableFpu, deactivateInterrupt
  for irq_state[wp]: "\<lambda>ms. P (irq_state ms)"

crunch arch_switch_to_idle_thread, arch_switch_to_thread
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s :: det_state. P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp crunch_wps whenE_wp
   simp: machine_op_lift_def setVSpaceRoot_def
         machine_rest_lift_def crunch_simps storeWord_def)

crunch arch_invoke_irq_handler
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp simp: maskInterrupt_def)

crunch arch_perform_invocation
  for irq_state_of_state[wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp simp: cache_machine_op_defs doSMC_mop_def
   wp: crunch_wps simp: crunch_simps ignore: ignore_failure)

crunch arch_finalise_cap, prepare_thread_delete
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s :: det_state. P (irq_state_of_state s)"
  (wp: modify_wp crunch_wps dmo_wp
   simp: crunch_simps)

lemma equiv_asid_machine_state_update[Arch_IF_assms, simp]:
  "equiv_asid asid (machine_state_update f s) s' = equiv_asid asid s s'"
  "equiv_asid asid s (machine_state_update f s') = equiv_asid asid s s'"
  by (auto simp: equiv_asid_def)

lemma as_user_set_register_reads_respects'[Arch_IF_assms]:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag l \<top> (as_user thread (setRegister x y))"
  apply (case_tac "aag_can_read aag thread \<or> aag_can_affect aag l thread")
   apply (simp add: as_user_def split_def)
   apply (rule gen_asm_ev)
   apply (wp set_object_reads_respects select_f_ev gets_the_ev)
   apply (auto intro: reads_affects_equiv_get_tcb_eq det_setRegister)[1]
  apply (simp add: equiv_valid_def2)
  apply (rule as_user_set_register_ev2[OF domains_distinct])
  apply (simp add: labels_are_invisible_def)
  done

lemma store_word_offs_reads_respects[Arch_IF_assms]:
  "reads_respects aag l \<top> (store_word_offs ptr offs v)"
  apply (simp add: store_word_offs_def storeWord_def do_machine_op_bind)
  apply (wpsimp wp: equiv_valid_get_assert do_machine_op_reads_respects assert_ev2 modify_ev
         | fastforce intro: equiv_forI elim: equiv_forE simp: upto.simps comp_def)+
  done

lemma set_simple_ko_globals_equiv[Arch_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_simple_ko f ptr ep
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_simple_ko_def
  apply (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre] get_object_wp
              simp: partial_inv_def)+
  apply (fastforce simp: obj_at_def valid_arch_state_def dest: valid_global_arch_objs_pt_at)
  done

crunch set_thread_state_act
  for globals_equiv[wp]: "globals_equiv s"

lemma set_thread_state_globals_equiv[Arch_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_thread_state_def
  apply (wp set_object_globals_equiv |simp)+
  apply (intro impI conjI allI)
    apply (fastforce simp: valid_arch_state_def obj_at_def tcb_at_def2 get_tcb_def is_tcb_def
                     dest: get_tcb_SomeD valid_global_arch_objs_pt_at
                    split: option.splits kernel_object.splits)+
  done

lemma set_cap_globals_equiv'[Arch_IF_assms]:
  "\<lbrace>globals_equiv s and valid_global_arch_objs\<rbrace>
   set_cap cap p
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_cap_def
  apply (simp only: split_def)
  apply (wp set_object_globals_equiv hoare_vcg_all_lift get_object_wp | wpc | simp)+
  apply (fastforce simp: valid_arch_state_def obj_at_def is_tcb_def
                   dest: valid_global_arch_objs_pt_at)+
  done

lemma as_user_globals_equiv[Arch_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
   as_user tptr f
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_globals_equiv simp: split_def)
  apply (fastforce simp: valid_arch_state_def get_tcb_def obj_at_def
                   dest: valid_global_arch_objs_pt_at)
  done

crunch arch_prepare_set_domain, arch_prepare_next_domain
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s. P (irq_state_of_state s)"

lemma equiv_hyp_machine_state_rest_update[Arch_IF_assms]:
  "equiv_hyp P st (s\<lparr>machine_state := ms\<lparr>machine_state_rest := r\<rparr>\<rparr>) = equiv_hyp P st (s\<lparr>machine_state := ms\<rparr>)"
  by (simp add: equiv_hyp_def equiv_for_def)

lemma equiv_fpu_machine_state_rest_update[Arch_IF_assms]:
  "equiv_fpu P st (s\<lparr>machine_state := ms\<lparr>machine_state_rest := r\<rparr>\<rparr>) = equiv_fpu P st (s\<lparr>machine_state := ms\<rparr>)"
  by (simp add: equiv_fpu_def equiv_for_def)

end


arch_requalify_facts
  set_simple_ko_globals_equiv
  retype_region_irq_state_of_state
  arch_perform_invocation_irq_state_of_state

declare
  retype_region_irq_state_of_state[wp]
  arch_perform_invocation_irq_state_of_state[wp]


global_interpretation Arch_IF_1?: Arch_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Arch_IF_assms)?)
qed


lemmas invs_imps =
  invs_sym_refs invs_psp_aligned invs_distinct invs_arch_state
  invs_valid_global_objs invs_arch_state invs_valid_objs invs_valid_global_refs tcb_at_invs
  invs_cur invs_kernel_mappings


context Arch begin global_naming AARCH64

lemma get_asid_pool_revrv':
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
     (\<lambda>rv rv'. aag_can_read aag ptr \<longrightarrow> rv = rv') \<top> (get_asid_pool ptr)"
  unfolding gets_map_def
  apply (subst gets_apply)
  apply (subst gets_apply)
  apply (rule_tac W="\<lambda>rv rv'. aag_can_read aag ptr \<longrightarrow> rv = rv'" in equiv_valid_rv_bind)
    apply (fastforce elim: reads_equivE equiv_forE
                     simp: equiv_valid_2_def opt_map_def gets_apply_def get_def bind_def return_def)
   apply (fastforce simp: equiv_valid_2_def return_def assert_opt_def fail_def split: option.splits)
  apply wp
  done

lemma get_asid_pool_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_asid_pool ptr)"
  unfolding gets_map_def
  apply (subst gets_apply)
  apply (wpsimp wp: gets_apply_ev)
  apply (fastforce elim: reads_equivE equiv_forE simp: opt_map_def)
  done

lemma get_asid_pool_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (\<lambda>rv rv'. rv (asid_low_bits_of asid) = rv' (asid_low_bits_of asid))
                            (\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                                 is_subject_asid aag asid \<and> asid \<noteq> 0)
                            (get_asid_pool a)"
  unfolding gets_map_def assert_opt_def2
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule_tac R'="\<lambda>rv rv'. \<forall>p p'. rv a = Some p \<and> rv' a = Some p'
                                       \<longrightarrow> p (asid_low_bits_of asid) = p' (asid_low_bits_of asid)"
               and P="\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                          is_subject_asid aag asid \<and> asid \<noteq> 0"
               and P'="\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                           is_subject_asid aag asid \<and> asid \<noteq> 0"
                in equiv_valid_2_bind)
      apply (clarsimp simp: equiv_valid_2_def assert_def bind_def return_def fail_def
                     split: if_split)
     apply (clarsimp simp: equiv_valid_2_def gets_def get_def bind_def return_def fail_def
                    split: if_split)
     apply (drule_tac s="Some a" in sym)
     apply (fastforce elim: reads_equivE simp: equiv_asids_def equiv_asid_def)
    apply (wp wp_post_taut | simp)+
  done

lemma asid_high_bits_0_eq_1:
  "asid_high_bits_of 0 = asid_high_bits_of 1"
  by (auto simp: asid_high_bits_of_def asid_low_bits_def)

lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq:
  "\<lbrakk> is_subject_asid aag asid; reads_equiv aag s t; asid \<noteq> 0 \<rbrakk>
     \<Longrightarrow> arm_asid_table (arch_state s) (asid_high_bits_of asid) =
         arm_asid_table (arch_state t) (asid_high_bits_of asid)"
  apply (erule reads_equivE)
  apply (fastforce simp: equiv_asids_def equiv_asid_def intro: aag_can_read_own_asids)
  done

lemma find_vspace_for_asid_reads_respects:
   "reads_respects aag l (K ( aag_can_read_asid aag asid)) (find_vspace_for_asid asid)"
  unfolding find_vspace_for_asid_def
  apply wpsimp
     apply (simp add: throw_opt_def)
     apply wpsimp
    apply wpsimp+
  apply (erule reads_equivE)
  apply (clarsimp simp: equiv_asids_def)
  apply (erule equiv_forE)
  apply (erule_tac x=asid in allE)
  apply clarsimp
  apply (fastforce simp: vspace_for_asid_def entry_for_asid_def entry_for_pool_def
                         pool_for_asid_def vspace_for_pool_def
                         opt_map_def obind_def obj_at_def equiv_asid_def
                  split: option.splits)
  done

crunch invalidate_tlb_by_asid
  for states_equiv_for[wp]: "states_equiv_for P Q R S st"
  and scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and work_units_completed[wp]: "\<lambda>s. P (work_units_completed s)"
  (wp: do_machine_op_mol_states_equiv_for ignore: do_machine_op simp: invalidateTranslationASID_def)

lemma invalidate_tlb_by_asid_reads_respects:
  "reads_respects aag l (\<lambda>_. True) (invalidate_tlb_by_asid asid)"
  by (wpsimp wp: reads_respects_unobservable_unit_return)

lemma invalidate_tlb_by_asid_va_reads_respects:
  "reads_respects aag l \<top> (invalidate_tlb_by_asid_va asid vaddr)"
  unfolding invalidate_tlb_by_asid_va_def invalidateTranslationSingle_def
  by (wpsimp wp: reads_respects_unobservable_unit_return do_machine_op_mol_states_equiv_for)

lemma ptes_of_reads_equiv:
  "\<lbrakk> is_subject aag (table_base pt_t ptr); reads_equiv aag s t \<rbrakk>
     \<Longrightarrow> ptes_of s pt_t ptr = ptes_of t pt_t ptr"
  by (fastforce elim: reads_equivE equiv_forE simp: ptes_of_def obind_def opt_map_def)

lemma pt_walk_reads_equiv:
  "\<lbrakk> reads_equiv aag s t; pas_refined aag s; pspace_aligned s; valid_asid_table s;
     valid_vspace_objs s; is_subject aag pt; vptr \<in> user_region;
     level \<le> max_pt_level; vs_lookup_table level asid vptr s = Some (level, pt) \<rbrakk>
     \<Longrightarrow> pt_walk level bot_level pt vptr (ptes_of s) =
         pt_walk level bot_level pt vptr (ptes_of t)"
  apply (induct level arbitrary: pt; clarsimp)
  apply (simp (no_asm) add: pt_walk.simps)
  apply (clarsimp simp: obind_def split: if_splits)
  apply (subgoal_tac "ptes_of s (level_type level) (pt_slot_offset level pt vptr) =
                      ptes_of t (level_type level) (pt_slot_offset level pt vptr)")
   apply (clarsimp split: option.splits)
   apply (frule_tac bot_level="level-1" in vs_lookup_table_extend)
     apply (fastforce simp: pt_walk.simps obind_def)
    apply clarsimp
   apply (erule_tac x="pptr_from_pte x2" in meta_allE)
   apply (drule meta_mp)
    apply (subst (asm) vs_lookup_split_Some[OF order_less_imp_le[OF bit0.pred]])
      apply fastforce+
    apply (erule_tac pt_ptr=pt in pt_walk_is_subject; fastforce)
   apply (erule (1) meta_mp)
  apply (rule ptes_of_reads_equiv)
   apply (subst table_base_pt_slot_offset)
    apply (erule vs_lookup_table_is_aligned)
  by fastforce+

lemma pt_lookup_from_level_reads_respects:
   "reads_respects aag l
      (\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
           is_subject aag pt \<and> level \<le> max_pt_level \<and> vref \<in> user_region \<and>
           (\<exists>asid. vs_lookup_table level asid vref s = Some (level, pt)))
      (pt_lookup_from_level level pt vref target_pt)"
  apply (induct level arbitrary: pt)
   apply (simp add: pt_lookup_from_level_simps)
   apply wp
  apply (simp (no_asm) add: pt_lookup_from_level_simps unlessE_def)
  apply clarsimp
  apply (rule equiv_valid_guard_imp)
   apply (wpsimp wp: get_pte_rev | assumption)+
  apply (frule vs_lookup_table_is_aligned; clarsimp)
  apply (prop_tac "pt_walk level (level - 1) pt vref (ptes_of s) =
                   Some (level - 1, pptr_from_pte rv)")
   apply (fastforce simp: vs_lookup_split_Some[OF order_less_imp_le[OF bit0.pred]]
                          pt_walk.simps obind_def)
  apply (rule conjI)
   apply (erule_tac level=level and bot_level="level-1" and pt_ptr=pt in pt_walk_is_subject; fastforce)
  apply (rule_tac x=asid in exI)
  apply (erule (2) vs_lookup_table_extend)
  done

lemma unmap_page_table_reads_respects:
  "reads_respects aag l
     (pas_refined aag and pspace_aligned and valid_vspace_objs and valid_asid_table
                      and K (asid \<noteq> 0 \<and> is_subject_asid aag asid \<and> vaddr \<in> user_region))
     (unmap_page_table asid vaddr pt)"
  unfolding unmap_page_table_def fun_app_def cleanByVA_PoU_def
  apply (rule gen_asm_ev)
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_mol_reads_respects store_pte_reads_respects invalidate_tlb_by_asid_reads_respects
             pt_lookup_from_level_reads_respects find_vspace_for_asid_reads_respects
          | wpc | simp | fastforce intro: hoare_strengthen_postE_R[OF pt_lookup_from_level_is_subject])+
  apply clarsimp
  apply (frule vspace_for_asid_is_subject)
     apply (fastforce dest: vspace_for_asid_vs_lookup vs_lookup_table_vref_independent)+
  done

lemma perform_page_table_invocation_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_objs and valid_vspace_objs
                                         and valid_asid_table and valid_pti pti
                                         and K (authorised_page_table_inv aag pti))
                  (perform_page_table_invocation pti)"
  unfolding perform_page_table_invocation_def perform_pt_inv_map_def perform_pt_inv_unmap_def
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_mol_reads_respects store_pte_reads_respects set_cap_reads_respects mapM_x_ev''
             unmap_page_table_reads_respects get_cap_rev
          | wpc | simp add: cleanByVA_PoU_def cleanCacheRange_PoU_def)+
  apply (case_tac pti; clarsimp simp: authorised_page_table_inv_def)
  apply (clarsimp simp: valid_pti_def)
  apply (frule cte_wp_valid_cap)
   apply fastforce
  apply (clarsimp simp: is_PageTableCap_def valid_cap_def wellformed_mapdata_def add_mask_fold)
  done

lemma unmap_page_reads_respects:
  "reads_respects aag l
     (pas_refined aag and pspace_aligned and valid_vspace_objs and valid_asid_table
                      and K (asid \<noteq> 0 \<and> is_subject_asid aag asid \<and> vptr \<in> user_region))
     (unmap_page pgsz asid vptr pptr)"
  unfolding unmap_page_def catch_def fun_app_def cleanByVA_PoU_def
  apply (simp add: unmap_page_def unlessE_def gets_the_def cong: vmpage_size.case_cong)
  apply (wp gets_ev' dmo_mol_reads_respects get_pte_rev throw_on_false_reads_respects
            find_vspace_for_asid_reads_respects store_pte_reads_respects[simplified]
            invalidate_tlb_by_asid_va_reads_respects
         | wpc | simp add: is_aligned_mask[symmetric])+
  apply (clarsimp simp: pt_lookup_slot_def)
  apply (frule (3) vspace_for_asid_is_subject)
  apply safe
    apply (frule vspace_for_asid_vs_lookup)
    apply (frule (6) pt_walk_reads_equiv[where bot_level=0])
      apply (rule order_refl)
     apply (erule vs_lookup_table_vref_independent[OF _ order_refl])
    apply (clarsimp simp: pt_lookup_slot_from_level_def obind_def split: option.splits)
   apply (fastforce elim!: pt_lookup_slot_from_level_is_subject
                     dest: vspace_for_asid_vs_lookup vs_lookup_table_vref_independent)+
  done

lemma perform_flush_reads_respects:
  "reads_respects aag l \<top> (perform_flush type vstart vend pstart space asid)"
  unfolding perform_flush_def do_flush_def isb_def dsb_def
            cleanCacheRange_PoU_def invalidateCacheRange_I_def
            cleanInvalidateCacheRange_RAM_def cleanCacheRange_RAM_def invalidateCacheRange_RAM_def
  by (cases type; wpsimp wp: dmo_mol_reads_respects when_ev simp: dmo_distr)

lemma perform_page_invocation_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects aag l (pas_refined aag and authorised_page_inv aag pgi and valid_page_inv pgi
                                           and valid_vspace_objs and valid_asid_table
                                           and pspace_aligned and is_subject aag \<circ> cur_thread)
                    (perform_page_invocation pgi)"
  unfolding perform_page_invocation_def fun_app_def when_def perform_pg_inv_map_def
            perform_pg_inv_unmap_def perform_pg_inv_get_addr_def cleanByVA_PoU_def
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_mol_reads_respects mapM_x_ev'' store_pte_reads_respects set_cap_reads_respects
             mapM_ev'' store_pte_reads_respects unmap_page_reads_respects
             get_cap_rev set_mrs_reads_respects set_message_info_reads_respects
             invalidate_tlb_by_asid_va_reads_respects get_pte_rev perform_flush_reads_respects
          | simp add: dmo_distr
          | wpc | wp (once) hoare_drop_imps[where Q'="\<lambda>r s. r"])+
  apply (case_tac pgi; clarsimp simp: authorised_page_inv_def valid_page_inv_def)
   apply (auto simp: cte_wp_at_caps_of_state authorised_slots_def cap_links_asid_slot_def
                     label_owns_asid_slot_def valid_arch_cap_def wellformed_mapdata_def
              dest!: clas_caps_of_state pas_refined_Control)
  done

lemma equiv_asids_arm_asid_table_update:
  "\<lbrakk> equiv_asids R s t; kheap s pool_ptr = kheap t pool_ptr \<rbrakk>
     \<Longrightarrow> equiv_asids R
           (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (asid_table s)
                                                             (asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)
           (t\<lparr>arch_state := arch_state t\<lparr>arm_asid_table := (asid_table t)
                                                             (asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)"
  by (clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap opt_map_def)

lemma arm_asid_table_update_reads_respects:
  "reads_respects aag l (K (is_subject aag pool_ptr))
     (do r \<leftarrow> gets asid_table;
         modify (\<lambda>s. s\<lparr>arch_state :=
                       arch_state s\<lparr>arm_asid_table := r(asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)
      od)"
  apply (simp add: equiv_valid_def2)
  apply (rule_tac W="\<top>\<top>"
              and Q="\<lambda>rv s. is_subject aag pool_ptr \<and> rv = arm_asid_table (arch_state s)"
               in equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
     apply wpsimp+
   apply (rule modify_ev2)
   apply clarsimp
   apply (drule (1) is_subject_kheap_eq[rotated])
   apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def
                         equiv_for_def equiv_hyp_def equiv_fpu_def)
   apply (fastforce intro!: equiv_asids_arm_asid_table_update)
  apply wpsimp
  done

lemma perform_asid_control_invocation_reads_respects:
  notes K_bind_ev[wp del]
  shows "reads_respects aag l (invs and ct_active and valid_aci aci and K (authorised_asid_control_inv aag aci))
                        (perform_asid_control_invocation aci)"
  unfolding perform_asid_control_invocation_def
  apply (rule gen_asm_ev)
  apply (rule equiv_valid_guard_imp)
   (* we do some hacky rewriting here to separate out the bit that does interesting stuff from the rest *)
   apply (subst (6) my_bind_rewrite_lemma)
   apply (subst (1) bind_assoc[symmetric])
   apply (subst another_hacky_rewrite)
   apply (subst another_hacky_rewrite)
   apply (wpc)
   apply (rule bind_ev)
     apply (rule K_bind_ev)
     apply (rule_tac bind_ev)
       apply (rule K_bind_ev)
       apply (rule bind_ev)
         apply (rule bind_ev)
           apply (rule return_ev)
          apply (rule K_bind_ev)
          apply simp
          apply (rule arm_asid_table_update_reads_respects)
         apply (wp cap_insert_reads_respects retype_region_reads_respects
                   set_cap_reads_respects delete_objects_reads_respects get_cap_rev
                | simp add: authorised_asid_control_inv_def)+
  apply (auto dest!: is_aligned_no_overflow)
  done

lemma set_asid_pool_reads_respects:
  "reads_respects aag l (K (is_subject aag ptr)) (set_asid_pool ptr pool)"
  unfolding set_asid_pool_def
  by (wpsimp wp: set_object_reads_respects get_asid_pool_rev)

lemma set_asid_pool_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_arch_objs\<rbrace>
   set_asid_pool ptr pool
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre] simp: a_type_def)
  apply (fastforce simp: obj_at_def dest: valid_global_arch_objs_pt_at)
  done

lemma perform_asid_pool_invocation_reads_respects_g:
  "reads_respects_g aag l (pas_refined aag and invs and K (authorised_asid_pool_inv aag api))
                  (perform_asid_pool_invocation api)"
  unfolding perform_asid_pool_invocation_def store_asid_pool_entry_def
  apply (rule equiv_valid_guard_imp)
   apply (wpsimp wp: reads_respects_g[OF set_asid_pool_reads_respects]
                     reads_respects_g[OF get_asid_pool_rev]
                     set_asid_pool_globals_equiv set_cap_reads_respects
                     doesnt_touch_globalsI get_cap_auth_wp[where aag=aag] get_cap_rev
                     set_cap_reads_respects_g get_cap_reads_respects_g
          | strengthen valid_arch_state_global_arch_objs
          | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: invs_arch_state invs_valid_global_objs invs_psp_aligned
                        invs_valid_global_vspace_mappings authorised_asid_pool_inv_def)
  done

lemma equiv_asids_arm_asid_table_delete:
  "equiv_asids R s t
   \<Longrightarrow> equiv_asids R
         (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := \<lambda>a. if a = asid_high_bits_of asid then None
                                                               else arm_asid_table (arch_state s) a\<rparr>\<rparr>)
         (t\<lparr>arch_state := arch_state t\<lparr>arm_asid_table := \<lambda>a. if a = asid_high_bits_of asid then None
                                                               else arm_asid_table (arch_state t) a\<rparr>\<rparr>)"
  by (clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)

lemma arm_asid_table_delete_ev2:
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) \<top>\<top>
     (\<lambda>s. rv = arm_asid_table (arch_state s)) (\<lambda>s. rv' = arm_asid_table (arch_state s))
     (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                     then None
                                                                     else rv a\<rparr>\<rparr>))
     (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                     then None
                                                                     else rv' a\<rparr>\<rparr>))"
  apply (rule modify_ev2)
  (* slow 15s *)
  by (auto simp: reads_equiv_def2 affects_equiv_def2 equiv_hyp_def
                 equiv_fpu_def equiv_for_def get_tcb_def cur_fpu_for_def
         intro!: states_equiv_forI equiv_forI equiv_asids_arm_asid_table_delete
          elim!: states_equiv_forE equiv_forE
           elim: is_subject_kheap_eq[simplified reads_equiv_def2 states_equiv_for_def, rotated])

lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq':
  "\<lbrakk> (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base
              \<longrightarrow> is_subject_asid aag asid'); reads_equiv aag s t \<rbrakk>
     \<Longrightarrow> arm_asid_table (arch_state s) (asid_high_bits_of base) =
         arm_asid_table (arch_state t) (asid_high_bits_of base)"
  apply (insert asid_high_bits_0_eq_1)
  apply (case_tac "base = 0")
   apply (subgoal_tac "is_subject_asid aag 1")
    apply (simp del: asid_high_bits_of_0)
    apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq[where aag=aag])
      apply (erule_tac x=1 in allE)
      apply simp+
  apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq[where aag=aag])
    apply (erule_tac x=base in allE)
    apply simp+
  done

lemma states_equiv_for_asid_map_update[simp]:
  "states_equiv_for P Q R S st (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map := asid_map'\<rparr>\<rparr>) =
   states_equiv_for P Q R S st s"
 by (auto simp: states_equiv_for_def equiv_for_def equiv_hyp_def equiv_fpu_def get_tcb_def cur_fpu_for_def
          intro: equiv_asids_triv' split: if_splits)

lemma states_equiv_for_vmid_table_update[simp]:
  "states_equiv_for P Q R S st (s\<lparr>arch_state := arch_state s\<lparr>arm_vmid_table := table\<rparr>\<rparr>) =
   states_equiv_for P Q R S st s"
 by (auto simp: states_equiv_for_def equiv_for_def equiv_hyp_def equiv_fpu_def get_tcb_def cur_fpu_for_def
          intro: equiv_asids_triv' split: if_splits)

lemma states_equiv_for_next_vmid_update[simp]:
  "states_equiv_for P Q R S st (s\<lparr>arch_state := arch_state s\<lparr>arm_next_vmid := vmid\<rparr>\<rparr>) =
   states_equiv_for P Q R S st s"
 by (auto simp: states_equiv_for_def equiv_for_def equiv_hyp_def equiv_fpu_def get_tcb_def cur_fpu_for_def
          intro: equiv_asids_triv' split: if_splits)

crunch get_vmid
  for states_equiv_for[wp]: "states_equiv_for P Q R S st"
  (wp: do_machine_op_mol_states_equiv_for ignore: do_machine_op simp: invalidateTranslationASID_def)

lemma set_vm_root_states_equiv_for:
  "set_vm_root thread \<lbrace>states_equiv_for P Q R S st\<rbrace>"
  unfolding set_vm_root_def catch_def fun_app_def set_global_user_vspace_def arm_context_switch_def
  by (wpsimp wp: do_machine_op_mol_states_equiv_for
                 hoare_vcg_all_lift whenE_wp hoare_drop_imps
           simp: setVSpaceRoot_def dmo_bind_valid if_apply_def2)+

crunch invalidate_asid_entry
  for states_equiv_for[wp]: "states_equiv_for P Q R S st"

crunch invalidate_asid_entry
  for sched_act[wp]: "\<lambda>s. P (scheduler_action s)"

crunch invalidate_asid_entry
  for wuc[wp]: "\<lambda>s. P (work_units_completed s)"

lemma delete_asid_pool_reads_respects:
  "reads_respects aag l (K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base
                                    \<longrightarrow> is_subject_asid aag asid'))
                  (delete_asid_pool base ptr)"
  unfolding delete_asid_pool_def
  apply (rule equiv_valid_guard_imp)
   apply (rule bind_ev)
     apply (simp)
     apply (subst equiv_valid_def2)
     apply (rule_tac W="\<top>\<top>"
                 and Q="\<lambda>rv s. rv = arm_asid_table (arch_state s) \<and>
                               (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base
                                        \<longrightarrow> is_subject_asid aag asid')"
                  in equiv_valid_rv_bind)
       apply (rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
        apply (wp, simp)
      apply (simp add: when_def)
      apply (clarsimp | rule conjI)+
        apply (rule equiv_valid_2_guard_imp)
          apply (rule equiv_valid_2_bind)
             apply (rule equiv_valid_2_bind)
                apply (rule equiv_valid_2_bind)
                   apply (rule equiv_valid_2_unobservable)
                              apply (wp set_vm_root_states_equiv_for)+
                  apply (rule arm_asid_table_delete_ev2)
                 apply (wp)+
               apply (rule equiv_valid_2_unobservable)
                          apply (wpsimp wp: mapM_wp_inv)+
            apply (rule equiv_valid_2_unobservable)
  by (wp mapM_wp' return_ev2
      | rule conjI | drule (1) requiv_arm_asid_table_asid_high_bits_of_asid_eq'
      | clarsimp | simp add: equiv_valid_2_def)+

lemma set_asid_pool_state_equal_except_kheap:
  "((), s') \<in> fst (set_asid_pool ptr pool s)
   \<Longrightarrow> states_equal_except_kheap_asid s s' \<and>
       (\<forall>p. p \<noteq> ptr \<longrightarrow> kheap s p = kheap s' p) \<and>
       asid_pools_of s' ptr = Some pool \<and>
       (\<forall>asid. asid \<noteq> 0
               \<longrightarrow> arm_asid_table (arch_state s) (asid_high_bits_of asid) =
                   arm_asid_table (arch_state s') (asid_high_bits_of asid) \<and>
                   (\<forall>pool_ptr. arm_asid_table (arch_state s) (asid_high_bits_of asid) =
                               Some pool_ptr
                               \<longrightarrow> asid_pool_at pool_ptr s = asid_pool_at pool_ptr s' \<and>
                                   (\<forall>asid_pool asid_pool'. pool_ptr \<noteq> ptr
                                                           \<longrightarrow> asid_pools_of s pool_ptr =
                                                               Some asid_pool \<and>
                                                               asid_pools_of s' pool_ptr =
                                                               Some asid_pool'
                                                               \<longrightarrow> asid_pool (asid_low_bits_of asid) =
                                                                   asid_pool' (asid_low_bits_of asid))))"
  by (clarsimp simp: set_asid_pool_def put_def bind_def set_object_def get_object_def gets_map_def
                     gets_def get_def return_def assert_def assert_opt_def fail_def
                     states_equal_except_kheap_asid_def equiv_for_def obj_at_def
              split: if_split_asm option.split_asm)

lemma set_asid_pool_delete_ev2:
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) \<top>\<top>
     (\<lambda>s. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some a \<and>
          asid_pools_of s a = Some pool \<and> asid \<noteq> 0 \<and> is_subject_asid aag asid)
     (\<lambda>s. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some a \<and>
          asid_pools_of s a = Some pool' \<and> asid \<noteq> 0 \<and> is_subject_asid aag asid)
     (set_asid_pool a (pool(asid_low_bits_of asid := None)))
     (set_asid_pool a (pool'(asid_low_bits_of asid := None)))"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (erule use_valid)
   apply (wpsimp simp: set_asid_pool_def wp: set_object_wp)
  apply clarsimp
  apply (erule use_valid)
   apply (wpsimp simp: set_asid_pool_def wp: set_object_wp)
  apply clarsimp
  apply (prop_tac "aag_can_read aag a \<or> aag_can_affect aag l a \<longrightarrow> pool = pool'")
   apply (erule reads_equivE)
   apply (erule equiv_forE)
   apply (erule_tac x=a in meta_allE)
   apply clarsimp
   apply (clarsimp simp: equiv_for_def)
   apply (erule affects_equivE)
   apply (erule equiv_forE)
   apply (erule_tac x=a in meta_allE)
   apply clarsimp
   apply (clarsimp simp: opt_map_def split: option.splits)
  apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_for_def)
  apply (clarsimp simp: equiv_asids_def equiv_asid_def obj_at_def opt_map_def | rule conjI)+
  done

lemma delete_asid_reads_respects:
  "reads_respects aag l (K (asid \<noteq> 0 \<and> is_subject_asid aag asid)) (delete_asid asid pt)"
  unfolding delete_asid_def
  supply fun_upd_apply[simp del]
  apply (subst equiv_valid_def2)
  apply (rule_tac W="\<top>\<top>" and Q="\<lambda>rv s. rv = asid_table s (asid_high_bits_of asid) \<and>
                                        is_subject_asid aag asid \<and> asid \<noteq> 0" in equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
     apply (wp, simp)
   apply (case_tac "rv = rv'")
    apply (simp)
    apply (case_tac "rv")
     apply (simp)
     apply (wp return_ev2, simp)
    apply (simp)
    apply (rule equiv_valid_2_guard_imp)
      apply (rule_tac R'="\<lambda>rv rv'. rv (asid_low_bits_of asid) = rv' (asid_low_bits_of asid)"
                   in equiv_valid_2_bind)
         apply (simp add: when_def)
         apply (clarsimp | rule conjI)+
          apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
             apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
                apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
                   apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
                      apply (subst equiv_valid_def2[symmetric])
                      apply (rule reads_respects_unobservable_unit_return)
                           apply (wp set_vm_root_states_equiv_for)+
                     apply (rule set_asid_pool_delete_ev2)
                    apply (wp)+
                  apply (rule equiv_valid_2_unobservable)
                             apply (wpsimp wp: do_machine_op_mol_states_equiv_for invalidate_tlb_by_asid_reads_respects)+
               apply (rule equiv_valid_2_unobservable)
                          apply wpsimp+
              apply (wpsimp wp: hoare_vcg_imp_lift')+
            apply (rule equiv_valid_2_unobservable)
                       apply (wpsimp wp: hoare_vcg_imp_lift')+
         apply (clarsimp | rule return_ev2)+
        apply (rule equiv_valid_2_guard_imp)
          apply (wp get_asid_pool_revrv)
         apply (simp)+
       apply (wp)+
     apply (clarsimp simp: obj_at_def)+
   apply (clarsimp simp: equiv_valid_2_def reads_equiv_def
                         equiv_asids_def equiv_asid_def states_equiv_for_def)
   apply (erule_tac x="pasASIDAbs aag asid" in ballE)
    apply (clarsimp)
   apply (drule aag_can_read_own_asids)
   apply wpsimp+
  apply (clarsimp simp: pool_for_asid_def)
  done

lemma globals_equiv_arm_asid_map_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>arm_asid_map := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma globals_equiv_arm_asid_table_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>arm_asid_table := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma globals_equiv_arm_vmid_table_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>arm_vmid_table := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma globals_equiv_arm_next_vmid_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>arm_next_vmid := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma valid_global_arch_objs_arm_asid_table_update[simp]:
  "valid_global_arch_objs (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := x\<rparr>\<rparr>) = valid_global_arch_objs s"
  by (simp add: valid_global_arch_objs_def)

lemma set_global_user_vspace_globals_equiv[wp]:
  "set_global_user_vspace \<lbrace>globals_equiv s\<rbrace>"
  unfolding set_global_user_vspace_def setVSpaceRoot_def
  by wpsimp

lemma update_asid_pool_entry_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_global_arch_objs\<rbrace>
   update_asid_pool_entry f asid
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding update_asid_pool_entry_def
  by (wpsimp wp: set_asid_pool_globals_equiv)

crunch invalidate_vmid_entry, invalidate_asid
  for globals_equiv[wp]: "globals_equiv st"
  (wp: crunch_wps dmo_mol_reads_respects simp: crunch_simps)

lemma find_free_vmid_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_global_arch_objs\<rbrace>
   find_free_vmid
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding find_free_vmid_def invalidateTranslationASID_def
  by wpsimp

crunch get_vmid
  for globals_equiv[wp]: "globals_equiv st"
  (wp: crunch_wps dmo_mol_reads_respects simp: crunch_simps)

lemma arm_context_switch_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_global_arch_objs\<rbrace>
   arm_context_switch vspace asid
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding arm_context_switch_def setVSpaceRoot_def
  by (wpsimp wp: dmo_mol_reads_respects)

lemma set_vm_root_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_global_arch_objs\<rbrace>
   set_vm_root tcb
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  by (wpsimp wp: dmo_mol_globals_equiv hoare_vcg_all_lift hoare_drop_imps
           simp: set_vm_root_def setVSpaceRoot_def)

crunch invalidate_asid_entry
  for globals_equiv[wp]: "globals_equiv st"
  (wp: crunch_wps dmo_mol_reads_respects simp: crunch_simps)

lemma invalidate_tlb_by_asid_globals_equiv[wp]:
  "invalidate_tlb_by_asid asid \<lbrace>globals_equiv s\<rbrace>"
  unfolding invalidate_tlb_by_asid_def invalidateTranslationASID_def
  by wpsimp

lemma invalidate_tlb_by_asid_va_globals_equiv[wp]:
  "invalidate_tlb_by_asid_va asid vaddr \<lbrace>globals_equiv s\<rbrace>"
  unfolding invalidate_tlb_by_asid_va_def invalidateTranslationSingle_def
  by wpsimp

lemma delete_asid_pool_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_global_arch_objs\<rbrace>
   delete_asid_pool base ptr
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding delete_asid_pool_def
  by (wpsimp wp: set_vm_root_globals_equiv mapM_wp[OF _ subset_refl] modify_wp)

lemma vs_lookup_slot_not_global:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, pte); level \<le> max_pt_level;
     pte_refs_of (level_type level) pte s = Some pt; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> pt \<notin> global_refs s"
  apply (prop_tac "vs_lookup_target level asid vref s = Some (level, pt)")
   apply (clarsimp simp: vs_lookup_target_def obind_def split: if_splits)
  apply (erule (2) vs_lookup_target_not_global)
  done

lemma unmap_page_table_globals_equiv:
  "\<lbrace>invs and globals_equiv st and K (vaddr \<in> user_region)\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. globals_equiv st\<rbrace>"
  unfolding unmap_page_table_def cleanByVA_PoU_def
  apply (wp store_pte_globals_equiv pt_lookup_from_level_wrp | wpc | simp)+
  apply clarsimp
  apply (rule_tac x=asid in exI)
  apply clarsimp
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some valid_arch_state_asid_table)
  apply (drule vs_lookup_slot_table_base; clarsimp)
  apply (drule reachable_page_table_not_global, clarsimp+)
  done

lemma mapM_x_swp_store_pte_globals_equiv:
  "\<lbrace>globals_equiv s and pspace_aligned and valid_arch_state and valid_global_vspace_mappings
                    and (\<lambda>s. \<forall>x \<in> set slots. table_base pt_t x \<notin> global_refs s)\<rbrace>
   mapM_x (swp (store_pte pt_t) pte) slots
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (rule_tac Q'="\<lambda>_. pspace_aligned and globals_equiv s and valid_arch_state
                                        and valid_global_vspace_mappings
                                        and (\<lambda>s. \<forall>x \<in> set slots. table_base pt_t x \<notin> global_refs s)"
               in hoare_strengthen_post)
   apply (wp mapM_x_wp' store_pte_valid_arch_state_unreachable
             store_pte_valid_global_vspace_mappings store_pte_globals_equiv | simp)+
    apply (auto simp: global_refs_def)
  done

lemma mapM_x_swp_store_pte_valid_ko_at_arch[wp]:
  "\<lbrace>pspace_aligned and valid_arch_state and valid_global_vspace_mappings
                   and (\<lambda>s. \<forall>x \<in> set slots. table_base pt_t x \<notin> global_refs s)\<rbrace>
   mapM_x (swp (store_pte pt_t) pte) slots
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (rule_tac Q'="\<lambda>_. pspace_aligned and valid_arch_state and valid_global_vspace_mappings
                                        and (\<lambda>s. \<forall>x \<in> set slots. table_base pt_t x \<notin> global_refs s)"
               in hoare_strengthen_post)
   apply (wp mapM_x_wp' store_pte_valid_arch_state_unreachable
             store_pte_valid_global_vspace_mappings store_pte_globals_equiv | simp)+
  done


definition authorised_for_globals_page_table_inv ::
  "page_table_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow> bool" where
  "authorised_for_globals_page_table_inv pti \<equiv> \<lambda>s.
     case pti of PageTableMap cap ptr pte p lvl \<Rightarrow> table_base (level_type lvl) p \<noteq> arm_us_global_vspace (arch_state s)
                                        | _ \<Rightarrow> True"

lemma perform_pt_inv_map_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. table_base (level_type lvl) p \<noteq> global_pt s)\<rbrace>
   perform_pt_inv_map cap sl pte p lvl
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pt_inv_map_def cleanByVA_PoU_def
  by (wpsimp wp: store_pte_globals_equiv set_cap_globals_equiv)

lemma perform_pt_inv_unmap_globals_equiv:
  "\<lbrace>invs and globals_equiv st and cte_wp_at ((=) (ArchObjectCap cap)) ct_slot\<rbrace>
   perform_pt_inv_unmap cap ct_slot
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pt_inv_unmap_def cleanCacheRange_PoU_def
  apply (wpsimp wp: set_cap_globals_equiv mapM_x_swp_store_pte_globals_equiv)
     apply (strengthen invs_imps invs_valid_global_vspace_mappings)
     apply (clarsimp cong: conj_cong)
     apply (wpsimp wp: unmap_page_table_globals_equiv unmap_page_table_invs)
    apply wpsimp+
  apply (intro conjI)
   apply (drule cte_wp_valid_cap, fastforce)
   apply (clarsimp simp: is_PageTableCap_def valid_cap_def valid_arch_cap_def wellformed_mapdata_def)
  apply (frule cte_wp_valid_cap, fastforce)
  apply (clarsimp simp: is_PageTableCap_def valid_cap_def valid_arch_cap_def wellformed_mapdata_def)
  apply (prop_tac "table_base x42 x = acap_obj cap")
   apply (prop_tac "is_aligned x41 (pt_bits x42)")
    apply (fastforce dest: is_aligned_pt simp: valid_arch_cap_def)
   apply (simp only: is_aligned_neg_mask_eq')
   apply (clarsimp simp: add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule_tac n="pt_bits x42" in neg_mask_mono_le)
   apply (drule_tac n="pt_bits x42" in neg_mask_mono_le)
   apply (fastforce dest: plus_mask_AND_NOT_mask_eq)
  apply clarsimp
  apply (frule invs_valid_global_refs)
  apply (drule (2) valid_global_refsD[OF invs_valid_global_refs])
  apply (clarsimp simp: cap_range_def)
  done

lemma perform_page_table_invocation_globals_equiv:
  "\<lbrace>invs and globals_equiv st and valid_pti pti and authorised_for_globals_page_table_inv pti\<rbrace>
   perform_page_table_invocation pti
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_page_table_invocation_def
  apply (wpsimp wp: store_pte_globals_equiv set_cap_globals_equiv
                    perform_pt_inv_map_globals_equiv
                    perform_pt_inv_unmap_globals_equiv)
  apply (case_tac pti; clarsimp simp: authorised_for_globals_page_table_inv_def valid_pti_def)
  done

lemma mapM_swp_store_pte_globals_equiv:
  "\<lbrace>globals_equiv s and (\<lambda>s. \<forall>x \<in> set slots. table_base pt_t x \<notin> global_refs s)\<rbrace>
   mapM (swp (store_pte pt_t) pte) slots
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (rule_tac Q'="\<lambda>_. globals_equiv s and (\<lambda>s. \<forall>x \<in> set slots. table_base pt_t x \<notin> global_refs s)"
               in hoare_strengthen_post)
   apply (wp mapM_wp' store_pte_valid_arch_state_unreachable
             store_pte_valid_global_vspace_mappings store_pte_globals_equiv | simp)+
    apply (auto simp: global_refs_def)
  done

lemma unmap_page_globals_equiv:
  "\<lbrace>globals_equiv st and invs and K (vptr \<in> user_region)\<rbrace>
   unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding unmap_page_def cleanByVA_PoU_def including no_pre
  apply (induct pgsz)
    apply (wpsimp wp: store_pte_globals_equiv | simp)+
    apply (rule hoare_weaken_preE[OF find_vspace_for_asid_wp])
    apply clarsimp
    apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
    apply (drule vs_lookup_slot_table_base; clarsimp?)
    apply (drule reachable_page_table_not_global; clarsimp?)
    apply fastforce
   apply (rule hoare_pre)
    apply (wpsimp wp: store_pte_globals_equiv mapM_swp_store_pte_globals_equiv hoare_drop_imps)+
   apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
   apply (drule vs_lookup_slot_level)
   apply (case_tac "x = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some valid_arch_state_asid_table)
   apply (drule vs_lookup_slot_table_base; clarsimp?)
   apply (drule reachable_page_table_not_global; clarsimp?)
   apply fastforce
  apply (wpsimp wp: store_pte_globals_equiv)+
  apply (rule hoare_weaken_preE[OF find_vspace_for_asid_wp])
  apply clarsimp
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
  apply (drule vs_lookup_slot_level)
  apply (case_tac "x = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some valid_arch_state_asid_table)
  apply (drule vs_lookup_slot_table_base; clarsimp?)
  apply (drule reachable_page_table_not_global; clarsimp?)
  apply fastforce
  done


definition authorised_for_globals_page_inv ::
  "page_invocation \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool"  where
  "authorised_for_globals_page_inv pgi \<equiv> \<lambda>s.
     case pgi of PageMap cap ptr m \<Rightarrow> (\<exists>slot. cte_wp_at (parent_for_refs m) slot s) | _ \<Rightarrow> True"

lemma length_msg_lt_msg_max:
  "length msg_registers < msg_max_length"
  by (simp add: msg_registers_def msgRegisters_def upto_enum_def
                fromEnum_def enum_register msg_max_length_def)

lemma set_mrs_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>sa. thread \<noteq> idle_thread sa)\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_mrs_def
  apply (wp | wpc)+
        apply (simp add: zipWithM_x_mapM_x)
        apply (rule conjI)
         apply (rule impI)
         apply (rule_tac Q'="\<lambda>_. globals_equiv s" in hoare_strengthen_post)
          apply (wp mapM_x_wp')
          apply (simp add: split_def)
          apply (wp store_word_offs_globals_equiv)
         apply (simp)
        apply (clarsimp)
        apply (insert length_msg_lt_msg_max)
        apply (simp)
       apply (wp set_object_globals_equiv hoare_weak_lift_imp)
      apply (wp hoare_vcg_all_lift set_object_globals_equiv hoare_weak_lift_imp)+
  apply (fastforce simp: valid_arch_state_def obj_at_def get_tcb_def
                   dest: valid_global_arch_objs_pt_at)
  done

lemma perform_pg_inv_get_addr_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. cur_thread s \<noteq> idle_thread s)\<rbrace>
   perform_pg_inv_get_addr ptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pg_inv_get_addr_def
  by (wpsimp wp: set_message_info_globals_equiv set_mrs_globals_equiv)

crunch unmap_page
  for valid_global_arch_objs[wp]: "valid_global_arch_objs"
  (wp: crunch_wps simp: crunch_simps)

lemma perform_pg_inv_unmap_globals_equiv:
  "\<lbrace>invs and globals_equiv st and cte_wp_at ((=) (ArchObjectCap cap)) ct_slot\<rbrace>
   perform_pg_inv_unmap cap ct_slot
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pg_inv_unmap_def
  apply (rule hoare_weaken_pre)
   apply (wp mapM_swp_store_pte_globals_equiv hoare_vcg_all_lift mapM_x_swp_store_pte_globals_equiv
             set_cap_globals_equiv' unmap_page_globals_equiv store_pte_globals_equiv
             store_pte_globals_equiv hoare_weak_lift_imp set_message_info_globals_equiv
             perform_pg_inv_get_addr_globals_equiv
          | wpc | simp add: do_machine_op_bind)+
  apply (clarsimp simp: acap_map_data_def)
  apply (intro conjI; clarsimp)
  apply (clarsimp split: arch_cap.splits)
  apply (drule cte_wp_valid_cap, fastforce)
  apply (clarsimp simp:  valid_cap_def valid_arch_cap_def wellformed_mapdata_def)
  done

lemma perform_pg_inv_map_globals_equiv:
  "\<lbrace>invs and globals_equiv st and (\<lambda>s. table_base (level_type lvl) slot \<noteq> global_pt s)\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot lvl
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pg_inv_map_def cleanByVA_PoU_def
  apply (wp mapM_swp_store_pte_globals_equiv hoare_vcg_all_lift mapM_x_swp_store_pte_globals_equiv
         set_cap_globals_equiv' unmap_page_globals_equiv store_pte_globals_equiv
         store_pte_globals_equiv hoare_weak_lift_imp set_message_info_globals_equiv
          perform_pg_inv_get_addr_globals_equiv
      | wpc | simp add: do_machine_op_bind | rule conjI; rule impI, wp hoare_drop_imps)+
  apply fastforce
  done

lemma perform_flush_globals_equiv[wp]:
  "perform_flush type vstart vend pstart space asid \<lbrace>globals_equiv st\<rbrace>"
  unfolding perform_flush_def do_flush_def cleanCacheRange_RAM_def invalidateCacheRange_RAM_def
            cleanInvalidateCacheRange_RAM_def cleanCacheRange_PoU_def invalidateCacheRange_I_def isb_def dsb_def
  by (cases type; wpsimp wp: dmo_mol_reads_respects when_ev simp: dmo_distr)

lemma perform_page_invocation_globals_equiv:
  "\<lbrace>invs and authorised_for_globals_page_inv pgi and valid_page_inv pgi
         and globals_equiv st and ct_active\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_page_invocation_def
  apply (wpsimp wp: perform_pg_inv_get_addr_globals_equiv
                    perform_pg_inv_unmap_globals_equiv perform_pg_inv_map_globals_equiv)
  apply (intro conjI)
    apply (clarsimp simp: valid_page_inv_def same_ref_def)
    apply (drule vs_lookup_slot_table_base; clarsimp)
    apply (drule reachable_page_table_not_global, clarsimp+)
   apply (clarsimp simp: valid_page_inv_def)
  apply clarsimp
  apply (fastforce dest: invs_valid_idle
                   simp: valid_idle_def pred_tcb_at_def obj_at_def ct_in_state_def)
  done

lemma retype_region_ASIDPoolObj_globals_equiv:
  "\<lbrace>globals_equiv s and (\<lambda>sa. ptr \<noteq> global_pt s) and (\<lambda>sa. ptr \<noteq> idle_thread sa)\<rbrace>
   retype_region ptr 1 0 (ArchObject ASIDPoolObj) dev
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding retype_region_def
  apply (wpsimp wp: modify_wp dxo_wp_weak
              simp: trans_state_update[symmetric] simp_del: trans_state_update)
  apply (fastforce simp: globals_equiv_def idle_equiv_def tcb_at_def2)
  done

lemma perform_asid_control_invocation_globals_equiv:
  notes delete_objects_invs[wp del]
  notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  shows "\<lbrace>globals_equiv s and invs and ct_active and valid_aci aci\<rbrace>
         perform_asid_control_invocation aci
         \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding perform_asid_control_invocation_def
  apply (rule hoare_pre)
   apply wpc
   apply (rename_tac word1 cslot_ptr1 cslot_ptr2 word2)
   apply (wp modify_wp cap_insert_globals_equiv
             retype_region_ASIDPoolObj_globals_equiv[simplified]
             retype_region_invs_extras(5)[where sz=pageBits]
             retype_region_invs_extras(6)[where sz=pageBits]
             set_cap_globals_equiv
             max_index_upd_invs_simple set_cap_no_overlap
             set_cap_caps_no_overlap max_index_upd_caps_overlap_reserved
             region_in_kernel_window_preserved
             hoare_vcg_all_lift  get_cap_wp hoare_weak_lift_imp
             set_cap_idx_up_aligned_area[where dev = False,simplified]
          | simp)+
   (* factor out the implication -- we know what the relevant components of the
      cap referred to in the cte_wp_at are anyway from valid_aci, so just use
      those directly to simplify the reasoning later on *)
   apply (rule_tac Q'="\<lambda>a b. globals_equiv s b \<and> invs b \<and>
                             word1 \<noteq> arm_us_global_vspace (arch_state b) \<and> word1 \<noteq> idle_thread b \<and>
                             (\<exists>idx. cte_wp_at ((=) (UntypedCap False word1 pageBits idx)) cslot_ptr2 b) \<and>
                             descendants_of cslot_ptr2 (cdt b) = {} \<and>
                             pspace_no_overlap_range_cover word1 pageBits b"
                in hoare_strengthen_post)
    prefer 2
    apply (clarsimp simp: globals_equiv_def invs_valid_global_objs)
    apply (drule cte_wp_at_eqD2, assumption)
    apply clarsimp
    apply (clarsimp simp: empty_descendants_range_in)
    apply (rule conjI, fastforce simp: cte_wp_at_def)
    apply (clarsimp simp: obj_bits_api_def default_arch_object_def)
    apply (frule untyped_cap_aligned, simp add: invs_valid_objs)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (strengthen refl caps_region_kernel_window_imp[mk_strg I E])
    apply (simp add: invs_valid_objs invs_cap_refs_in_kernel_window
                     atLeastatMost_subset_iff word_and_le2
               cong: conj_cong)
    apply (rule conjI, rule descendants_range_caps_no_overlapI)
       apply assumption
      apply (simp add: cte_wp_at_caps_of_state)
     apply (simp add: empty_descendants_range_in)
    apply (clarsimp simp: range_cover_def)
    apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
    apply (simp add: word_bw_assocs pageBits_def mask_zero)
   apply (wp add: delete_objects_invs_ex delete_objects_pspace_no_overlap[where dev=False]
                  delete_objects_globals_equiv hoare_vcg_ex_lift
             del: Untyped_AI.delete_objects_pspace_no_overlap | simp)+
  apply (clarsimp simp: conj_comms
                        invs_psp_aligned invs_valid_objs valid_aci_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule_tac cap="UntypedCap False a b c" for a b c in caps_of_state_valid, assumption)
  apply (clarsimp simp: valid_cap_def cap_aligned_def untyped_min_bits_def)
  apply (frule_tac slot="(aa,ba)"
                in untyped_caps_do_not_overlap_global_refs[rotated, OF invs_valid_global_refs])
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply ((rule conjI |rule refl | simp)+)[1]
  apply (rule conjI)
   apply (clarsimp simp: global_refs_def ptr_range_memI)
  apply (rule conjI)
   apply clarify
   apply (drule_tac p="global_pt sa" in ptr_range_memI)
   apply fastforce
  apply (rule conjI, fastforce simp: global_refs_def)
  apply (rule conjI)
   apply clarify
   apply fastforce
  apply (rule conjI)
   apply (drule untyped_slots_not_in_untyped_range)
        apply (blast intro!: empty_descendants_range_in)
       apply (simp add: cte_wp_at_caps_of_state)
      apply simp
     apply (rule refl)
    apply (rule subset_refl)
   apply (simp)
  apply (rule conjI)
   apply fastforce
  apply (auto intro: empty_descendants_range_in simp: descendants_range_def2 cap_range_def)
  done

lemma store_asid_pool_entry_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   store_asid_pool_entry pool_ptr asid ptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding store_asid_pool_entry_def
  by (wp modify_wp set_asid_pool_globals_equiv set_cap_globals_equiv get_cap_wp | wpc | fastforce)+

lemma perform_asid_pool_invocation_globals_equiv:
  "\<lbrace>globals_equiv s and invs and valid_apinv api\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding perform_asid_pool_invocation_def
  apply (rule hoare_weaken_pre)
   apply (wp modify_wp set_asid_pool_globals_equiv set_cap_globals_equiv
             store_asid_pool_entry_globals_equiv get_cap_wp
          | wpc | simp)+
  apply (clarsimp simp: valid_apinv_def cong: conj_cong)
  done

crunch perform_vspace_invocation
  for globals_equiv[wp]: "globals_equiv st"
  (simp: sendSGI_def wp: dmo_mol_globals_equiv)

lemma perform_sgi_invocation_globals_equiv[wp]:
  "perform_sgi_invocation iv \<lbrace>globals_equiv s\<rbrace>"
  unfolding perform_sgi_invocation_def sendSGI_def
  by wpsimp

lemma perform_vspace_invocation_reads_respects:
  "reads_respects aag l \<top> (perform_vspace_invocation iv)"
  unfolding perform_vspace_invocation_def
  by (cases iv; wpsimp wp: perform_flush_reads_respects)


(* Helpful groupings *)

definition vcpu_enable_2 where
  "vcpu_enable_2 vr \<equiv> do
     vcpu_enable vr;
     modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (vr, True)\<rparr>\<rparr>)
   od"

definition vcpu_restore_2 where
  "vcpu_restore_2 vr \<equiv> do
     vcpu_restore vr;
     modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (vr, True)\<rparr>\<rparr>)
   od"

definition vcpu_disable_2 where
  "vcpu_disable_2 vr \<equiv> do
     vcpu_disable (Some vr);
     modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (vr, False)\<rparr>\<rparr>)
   od"

definition vcpu_save_hcr where
  "vcpu_save_hcr vr \<equiv> do
     hcr <- do_machine_op get_gic_vcpu_ctrl_hcr;
     vgic_update vr (vgic_hcr_update (\<lambda>_. hcr))
   od"

definition vcpu_save_vmcr where
  "vcpu_save_vmcr vr \<equiv> do
     vmcr <- do_machine_op get_gic_vcpu_ctrl_vmcr;
     vgic_update vr (vgic_vmcr_update (\<lambda>_. vmcr))
   od"

definition vcpu_save_apr where
  "vcpu_save_apr vr \<equiv> do
     apr <- do_machine_op get_gic_vcpu_ctrl_apr;
     vgic_update vr (vgic_apr_update (\<lambda>_. apr))
   od"

definition vcpu_save_lr where
  "vcpu_save_lr vr reg \<equiv> do
     lr <- do_machine_op (get_gic_vcpu_ctrl_lr (word_of_nat reg));
     vgic_update_lr vr reg lr
   od"

definition vcpu_save_lrs where
  "vcpu_save_lrs vr \<equiv> do
     num_list_regs <- gets (arm_gicvcpu_numlistregs \<circ> arch_state);
     return [0..<num_list_regs] >>= mapM (vcpu_save_lr vr);
     return ()
   od"

lemmas vcpu_save_vgic_defs =
  vcpu_save_hcr_def
  vcpu_save_vmcr_def
  vcpu_save_apr_def
  vcpu_save_lr_def
  vcpu_save_lrs_def


(* FIXME AARCH64 IF: reads_respects and reads_respects_scheduler proofs are too specific to reuse.
   To allow reuse, we introduce a more generic equiv_valid relation over states_equiv_for_labels.
   Unfortunately, this means recreating much of the existing infrastructure. *)

locale_abbrev reads_respects_l_2 where
  "reads_respects_l_2 aag L \<equiv> equiv_valid_2 (\<lambda>_ _. True) (states_equiv_for_labels aag L) (states_equiv_for_labels aag L)"

locale_abbrev reads_respects_l where
  "reads_respects_l aag L \<equiv> equiv_valid_inv (\<lambda>_ _. True) (states_equiv_for_labels aag L)"

lemma reads_respects_l_2_invisible:
  "\<lbrakk> modifies_at_most aag {l. \<not>L l} Q f; modifies_at_most aag {l. \<not>L l} Q' g;
     \<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>; \<And>P. g \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>;
     \<forall>s t. P s \<and> P' t \<longrightarrow> (\<forall>(rva,s') \<in> fst (f s). \<forall>(rvb,t') \<in> fst (g t). R rva rvb) \<rbrakk>
     \<Longrightarrow> reads_respects_l_2 aag L R (P and Q) (P' and Q') f g"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def modifies_at_most_def)
  apply (rename_tac u s' v t')
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
  apply (prop_tac "states_equiv_for_labels aag L s s'")
   apply (subgoal_tac "equiv_for (\<lambda>x. \<exists>x\<in>pasDomainAbs aag x. L x) ready_queues s s'")
    apply (clarsimp simp: equiv_but_for_labels_def states_equiv_for_def)
   apply (clarsimp simp: equiv_for_def)
   apply (erule use_valid, erule meta_allE, assumption)
   apply simp
  apply (prop_tac "states_equiv_for_labels aag L t t'")
   apply (subgoal_tac "equiv_for (\<lambda>x. \<exists>x\<in>pasDomainAbs aag x. L x) ready_queues t t'")
    apply (clarsimp simp: equiv_but_for_labels_def states_equiv_for_def)
   apply (clarsimp simp: equiv_for_def)
   apply (erule use_valid, erule meta_allE, assumption)
   apply (erule use_valid, erule meta_allE, assumption)
   apply simp
  by (drule (1) states_equiv_for_trans,
      drule states_equiv_for_sym,
      drule (1) states_equiv_for_trans,
      drule states_equiv_for_sym,
      solves simp)

lemma reads_respects_l_invisible:
  "\<lbrakk> modifies_at_most aag {l. \<not>L l} Q f; \<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>;
     \<forall>s t. P s \<and> P t \<longrightarrow> (\<forall>(rva,s') \<in> fst (f s). \<forall>(rvb,t') \<in> fst (f t). rva = rvb) \<rbrakk>
     \<Longrightarrow> reads_respects_l aag L (P and Q) f"
  unfolding equiv_valid_def2 by (fastforce intro!: reads_respects_l_2_invisible)

lemma reads_respects_l_unit_cases':
  "\<lbrakk> reads_respects_l aag l (P and K (l (pasObjectAbs aag ptr))) f;
     modifies_at_most aag {pasObjectAbs aag ptr} Q f; \<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> \<rbrakk>
     \<Longrightarrow> reads_respects_l aag l (if l (pasObjectAbs aag ptr) then P else Q) (f :: (det_state,unit) nondet_monad)"
  apply (case_tac "l (pasObjectAbs aag ptr)")
   apply (erule equiv_valid_guard_imp, clarsimp)
  apply clarsimp
  apply (rule reads_respects_l_invisible[where P="\<top>", simplified])
    apply (fastforce simp: modifies_at_most_def equiv_but_for_labels_def elim: states_equiv_for_guard_imp)
   apply simp
  apply simp
  done

lemmas reads_respects_l_unit_cases = reads_respects_l_unit_cases'[OF _ modifies_at_mostI]

definition aag_can_affect_label_via where
  "aag_can_affect_label_via aag l d \<equiv> aag_can_affect_label aag l \<and> d \<in> subjectReads (pasPolicy aag) l"

locale_abbrev aag_can_read_or_affect_label where
  "aag_can_read_or_affect_label aag l \<equiv> \<lambda>d.
     aag_can_read_label aag d \<or> aag_can_affect_label_via aag l d"

(* The states_equiv_for parts of reads_respects *)
definition roa_equiv where
  "roa_equiv aag l s s' \<equiv> states_equiv_for_labels aag (aag_can_read_or_affect_label aag l) s s'"

(* The parts of reads_respects besides states_equiv_for *)
definition roa_inv where
  "roa_inv s s' \<equiv>
     cur_thread s = cur_thread s' \<and>
     cur_domain s = cur_domain s' \<and>
     scheduler_action s = scheduler_action s' \<and>
     work_units_completed s = work_units_completed s' \<and>
     equiv_irq_state (machine_state s) (machine_state s')"

lemma reads_equiv_for_labels:
  "reads_equiv aag s s' \<longleftrightarrow> states_equiv_for_labels aag (aag_can_read_label aag) s s' \<and> roa_inv s s'"
  by (auto simp: reads_equiv_def roa_inv_def states_equiv_for_def
                 equiv_for_def equiv_asids_def equiv_hyp_def equiv_fpu_def)

lemma affects_equiv_for_labels:
  "affects_equiv aag l s s' \<longleftrightarrow> states_equiv_for_labels aag (aag_can_affect_label_via aag l) s s'"
  by (auto intro: states_equiv_for_guard_imp[where P=\<bottom> and Q=\<bottom> and R=\<bottom> and S=\<bottom>]
            simp: affects_equiv_def aag_can_affect_label_via_def states_equiv_for_def
                  equiv_for_def equiv_asids_def equiv_hyp_False equiv_fpu_False)

lemma roa_equiv_def2:
  "roa_equiv aag l s s' \<longleftrightarrow> states_equiv_for_labels aag (aag_can_read_label aag) s s' \<and>
                            states_equiv_for_labels aag (aag_can_affect_label_via aag l) s s'"
  by (auto simp: roa_equiv_def states_equiv_for_def comp_def bex_disj_distrib
                 equiv_for_disj equiv_asids_def equiv_fpu_def equiv_hyp_def)

lemma reads_respects_def2:
  "reads_respects aag l P f \<longleftrightarrow> equiv_valid_inv roa_inv (roa_equiv aag l) P f"
  by (auto intro!: iff_allI
             simp: equiv_valid_def2 equiv_valid_2_def roa_equiv_def2
                   reads_equiv_for_labels affects_equiv_for_labels )

lemma reads_respects_from_labels:
  assumes ev: "\<And>L. reads_respects_l aag L P f"
    and inv: "\<And>P. f \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
    "\<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
    "\<And>P. f \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
    "\<And>P. f \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace>"
    "\<And>P. f \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  shows "reads_respects aag l P f"
  unfolding reads_respects_def2 roa_inv_def roa_equiv_def
  apply (rule equiv_valid_inv_split)
   apply (rule equiv_valid_rv_inv_lift)
     apply (rule hoare_weaken_pre)
      apply (wps inv)
      apply wp
     apply auto[3]
  apply (fastforce intro: ev)
  done

lemma equiv_valid_guard_necessary:
  assumes hoare: "\<lbrace>not P'\<rbrace> f \<lbrace>\<bottom>\<bottom>\<rbrace>"
  and ev: "equiv_valid I A B (P and P') f"
  shows "equiv_valid I A B P f"
  using ev
  apply (simp add: equiv_valid_def2 equiv_valid_2_def)
  apply (erule all_forward)+
  apply (fastforce dest: use_valid[OF _ hoare])
  done

lemma set_object_reads_respects_l:
  "reads_respects_l aag L \<top> (set_object ptr obj)"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def set_object_def get_object_def
                       bind_def' get_def gets_def put_def return_def fail_def assert_def)
  apply (erule states_equiv_for_identical_kheap_updates)
  apply (clarsimp simp: identical_kheap_updates_def)
  done

lemma set_vcpu_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (set_vcpu vr vcpu)"
  unfolding set_vcpu_def
  apply (rule_tac P'="vcpu_at vr" in equiv_valid_guard_necessary)
   apply (rule wp_pre)
    apply (rule hoare_set_object_weaken_pre)
    apply wp
   apply (clarsimp simp: obj_at_def)
  apply (wpsimp wp: set_object_reads_respects_l)
  done

lemma get_vcpu_reads_respects_l[wp]:
  "reads_respects_l aag l (K (l (pasObjectAbs aag vr))) (get_vcpu vr)"
  unfolding get_vcpu_def gets_map_def
  apply (subst gets_apply)
  apply (wpsimp wp: gets_apply_ev)
  apply (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_for_def opt_map_def)
  done

(* equiv_but_for_labels proofs *)

lemma set_vcpu_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag vr \<in> L)\<rbrace>
   set_vcpu vr vcpu
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_vcpu_def
  apply (rule wp_pre)
   apply (rule hoare_set_object_weaken_pre)
   apply (wp set_object_equiv_but_for_labels)
  apply (clarsimp simp: opt_map_def obj_at_def)
  done

lemma vcpu_update_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag vr \<in> L)\<rbrace>
   vcpu_update vr f
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_update_def by wpsimp

lemma vgic_update_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag vr \<in> L)\<rbrace>
   vgic_update vr f
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vgic_update_def by wpsimp

lemma vgic_update_lr_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag vr \<in> L)\<rbrace>
   vgic_update_lr vr reg irq
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vgic_update_lr_def by wpsimp

lemma dmo_mol_equiv_but_for_labels[wp]:
  "do_machine_op (machine_op_lift f) \<lbrace>equiv_but_for_labels aag L st\<rbrace>"
  unfolding equiv_but_for_labels_def
  by (wpsimp wp: do_machine_op_mol_states_equiv_for)

lemma dmo_equiv_but_for_labels_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (irq_state ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (vcpu_state ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (fpu_state ms)\<rbrace>"
  shows "do_machine_op f \<lbrace>equiv_but_for_labels aag L st\<rbrace>"
  unfolding equiv_but_for_labels_def states_equiv_for_def equiv_asids_def equiv_hyp_def equiv_fpu_def cur_fpu_for_def
  by (wpsimp wp: equiv_for_lift2 assms dmo_wp)

lemma dmo_equiv_but_for_labels_vcpu:
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (irq_state ms)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>ms. P (fpu_state ms)\<rbrace>"
  shows "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
         do_machine_op f
         \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding equiv_but_for_labels_def states_equiv_for_def equiv_asids_def equiv_hyp_def equiv_fpu_def cur_fpu_for_def
  apply wp
   apply clarsimp
   apply (rule hoare_vcg_conj_lift, solves "wpsimp wp: equiv_for_lift2 assms dmo_wp")+
   apply (rule hoare_vcg_conj_lift)
    apply (rule_tac Q'="\<lambda>_ s. equiv_for (\<lambda>x. pasObjectAbs aag x \<notin> L) cur_vcpu_of st s \<and>
                              cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None"
                 in hoare_strengthen_post)
     apply (wpsimp wp: equiv_for_lift2 assms dmo_wp)
    defer
    apply (wpsimp wp: equiv_for_lift2 assms dmo_wp)
   apply clarsimp
  apply (clarsimp simp: equiv_for_def cur_vcpu_for_def split: option.splits)
   apply (clarsimp simp: cur_vcpu_of_def split: option.splits)
  apply (clarsimp split: if_splits)
  apply (erule_tac x=x in allE)
  apply (clarsimp simp: cur_vcpu_of_def split: option.splits if_splits)
  done

lemma dmo_get_hcr_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s\<rbrace>
   do_machine_op get_gic_vcpu_ctrl_hcr
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_lift)

lemma dmo_set_hcr_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_hcr val)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_setSCTLR_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op (setSCTLR val)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_setHCR_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op (setHCR val)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_maskInterrupt_equiv_but_for_labels[wp]:
  "do_machine_op (maskInterrupt b irq) \<lbrace>equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_lift)

lemma dmo_check_export_arch_timer_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op check_export_arch_timer
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_writeVCPUHardwareReg_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op (writeVCPUHardwareReg reg val)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_readVCPUHardwareReg_inv[wp]:
  "do_machine_op (readVCPUHardwareReg reg) \<lbrace>P\<rbrace>"
  by (wpsimp simp: readVCPUHardwareReg_def)

lemma vcpu_save_reg_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag vr \<in> L)\<rbrace>
   vcpu_save_reg vr reg
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_save_reg_def
  by wpsimp

lemma save_virt_timer_equiv_but_for_labels[wp]:
   "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> pasObjectAbs aag vr \<in> L \<and> cur_vcpu_of s vr \<noteq> None\<rbrace>
   save_virt_timer vr
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding save_virt_timer_def
  apply wpsimp
  apply (clarsimp simp: cur_vcpu_for_def cur_vcpu_of_def split: option.splits if_splits)
  done

lemma dmo_enableFpuEL01_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op enableFpuEL01
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_isb_equiv_but_for_labels[wp]:
  "do_machine_op isb \<lbrace>equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_lift)

lemma dmo_dsb_equiv_but_for_labels[wp]:
  "do_machine_op dsb \<lbrace>equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_lift)

lemma vcpu_disable_Some_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_of s vr \<noteq> None \<and> pasObjectAbs aag vr \<in> L\<rbrace>
   vcpu_disable (Some vr) \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_disable_def
  apply (clarsimp simp: dmo_distr)
  apply wpsimp
  apply (clarsimp simp: cur_vcpu_for_def cur_vcpu_of_def split: option.splits if_splits)
  done

lemma vcpu_save_reg_range_equiv_but_for_labels[wp]:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag vr \<in> L)\<rbrace>
   vcpu_save_reg_range vr from to
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_save_reg_range_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: mapM_x_wp_inv)
  done

lemma dmo_get_lr_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op (get_gic_vcpu_ctrl_lr reg)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_set_lr_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_lr reg val)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_get_apr_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s\<rbrace>
   do_machine_op get_gic_vcpu_ctrl_apr
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_lift)

lemma dmo_set_apr_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_apr val)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma dmo_get_vmcr_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s\<rbrace>
   do_machine_op get_gic_vcpu_ctrl_vmcr
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_lift)

lemma dmo_set_vmcr_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_vmcr val)
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: dmo_equiv_but_for_labels_vcpu)

lemma vcpu_save_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> current_vcpu s = vopt \<and>
        (\<exists>vr b. vopt = Some (vr,b) \<and> pasObjectAbs aag vr \<in> L)\<rbrace>
   vcpu_save vopt \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_save_def
  apply (case_tac vopt; clarsimp)
  apply (wpsimp split_del: if_split simp: crunch_simps)
          apply (rule_tac Q'="\<lambda>_ s. equiv_but_for_labels aag L st s \<and> pasObjectAbs aag a \<in> L \<and>
                                    cur_vcpu_of s a \<noteq> None" in hoare_strengthen_post)
           apply (wpsimp wp: mapM_wp_inv)
           apply (clarsimp simp: cur_vcpu_for_def cur_vcpu_of_def split: option.splits if_splits)
          apply clarsimp
         apply (wpsimp simp: crunch_simps)+
  apply (clarsimp simp: cur_vcpu_for_def cur_vcpu_of_def split: option.splits if_splits)
  done

lemma vcpu_restore_reg_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
  vcpu_restore_reg vr reg
  \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_restore_reg_def
  by wp

lemma vcpu_restore_reg_range_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
  vcpu_restore_reg_range vr from to
  \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_restore_reg_range_def
  apply (rule hoare_strengthen_post, rule mapM_x_wp_inv)
   apply (wpsimp wp: mapM_x_wp_inv)+
  done

lemma restore_virt_timer_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
  restore_virt_timer vr
  \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding restore_virt_timer_def
  by wpsimp

lemma vcpu_enable_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
  vcpu_enable vr
  \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp simp: vcpu_enable_def dmo_distr)

crunch vcpu_restore_reg_range
  for current_vcpu[wp]: "\<lambda>s. P (current_vcpu s)"
  (wp: crunch_wps)

lemma vcpu_restore_equiv_but_for_labels[wp]:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> cur_vcpu_for (\<lambda>x. pasObjectAbs aag x \<notin> L) s = None\<rbrace>
  vcpu_restore vr
  \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  by (wpsimp wp: mapM_wp_inv simp: vcpu_restore_def dmo_distr dom_mapM)

lemma modify_current_vcpu_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> pasObjectAbs aag vr \<in> L \<and>
        (\<forall>ptr b. current_vcpu s = Some (ptr,b) \<longrightarrow> pasObjectAbs aag ptr \<in> L)\<rbrace>
   modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (vr,a)\<rparr>\<rparr>)
   \<lbrace>\<lambda>_ s. equiv_but_for_labels aag L st s\<rbrace>"
  apply wp
  apply simp
  apply (clarsimp simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def)
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

lemma vcpu_enable_2_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> pasObjectAbs aag vr \<in> L \<and>
        (\<forall>ptr b. current_vcpu s = Some (ptr,b) \<longrightarrow> pasObjectAbs aag ptr \<in> L)\<rbrace>
   vcpu_enable_2 vr
   \<lbrace>\<lambda>_ s. equiv_but_for_labels aag L st s\<rbrace>"
  unfolding vcpu_enable_2_def
  apply (wp modify_current_vcpu_equiv_but_for_labels)
  apply (fastforce simp: cur_vcpu_for_def split: option.splits)
  done

lemma vcpu_restore_2_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> pasObjectAbs aag vr \<in> L \<and>
        (\<forall>ptr b. current_vcpu s = Some (ptr,b) \<longrightarrow> pasObjectAbs aag ptr \<in> L)\<rbrace>
   vcpu_restore_2 vr
   \<lbrace>\<lambda>_ s. equiv_but_for_labels aag L st s\<rbrace>"
  unfolding vcpu_restore_2_def
  apply (wp modify_current_vcpu_equiv_but_for_labels)
  apply (fastforce simp: cur_vcpu_for_def split: option.splits)
  done

lemma vcpu_disable_2_equiv_but_for_labels:
  "\<lbrace>\<lambda>s. equiv_but_for_labels aag L st s \<and> current_vcpu s = Some (vr, True) \<and> pasObjectAbs aag vr \<in> L\<rbrace>
   vcpu_disable_2 vr
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding vcpu_disable_2_def
  apply (wp modify_current_vcpu_equiv_but_for_labels)
  apply (clarsimp simp: cur_vcpu_of_def)
  done


lemma vcpu_update_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (vcpu_update vr f)"
  unfolding vcpu_update_def
  apply (rule wp_pre)
   apply (rule_tac ptr=vr in reads_respects_l_unit_cases)
     apply wpsimp+
  done

lemma cur_vcpu_for_eq_Some[simp]:
  "(cur_vcpu_for_2 P cv = Some b) = (\<exists>ptr. cv = Some (ptr,b) \<and> P ptr)"
  by (clarsimp simp: cur_vcpu_for_def split: option.splits)

lemma cur_vcpu_for_equiv_l:
  "\<lbrakk> equiv_for P cur_vcpu_of st s \<rbrakk>
     \<Longrightarrow> cur_vcpu_for P st = cur_vcpu_for P s"
  apply (case_tac "current_vcpu st"; case_tac "current_vcpu s")
  by (auto simp: cur_vcpu_for_None cur_vcpu_for_Some equiv_for_def cur_vcpu_of_def split: if_splits)

lemma numlistregs_for_equiv_l:
  "\<lbrakk> equiv_for P (K \<circ> numlistregs) st s \<rbrakk>
     \<Longrightarrow> numlistregs_for P st = numlistregs_for P s"
  by (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def
                 equiv_hyp_def equiv_for_def numlistregs_for_def)

lemma do_machine_op_reads_respects_l':
  assumes equiv_dmo:
    "\<And>n cv cf. equiv_valid_inv (equiv_machine_state (l o pasObjectAbs aag)
                                             and equiv_hyp_state n cv
                                             and equiv_fpu_state cf)
                             (equiv_machine_state (l o pasObjectAbs aag)) (Q n cv cf) f"
  assumes guard:
    "\<And>s. P s \<Longrightarrow> Q (numlistregs_for (l o pasObjectAbs aag) s) (cur_vcpu_for (l o pasObjectAbs aag) s)
                    (cur_fpu_for (l o pasObjectAbs aag) s)
                    (machine_state s)"
  shows
    "reads_respects_l aag l P (do_machine_op f)"
  apply (rule use_spec_ev)
  apply (rule spec_equiv_valid_add_A[OF _ states_equiv_for_refl])
  apply (simp add: do_machine_op_def spec_equiv_valid_def)
  apply (rule equiv_valid_2_guard_imp)
    apply (rule_tac R'="\<lambda>rv rv'. equiv_machine_state (l o pasObjectAbs aag) rv rv' \<and>
                                 equiv_hyp_state (numlistregs_for (l o pasObjectAbs aag) st)
                                                 (cur_vcpu_for (l o pasObjectAbs aag) st) rv rv' \<and>
                                 equiv_fpu_state (cur_fpu_for (l o pasObjectAbs aag) st) rv rv'"
                and Q="\<lambda>r s. st = s \<and> Q (numlistregs_for (l o pasObjectAbs aag) st)
                                        (cur_vcpu_for (l o pasObjectAbs aag) st)
                                        (cur_fpu_for (l o pasObjectAbs aag) st) r"
                and Q'="\<lambda>r s. Q (numlistregs_for (l o pasObjectAbs aag) st)
                                (cur_vcpu_for (l o pasObjectAbs aag) st)
                                (cur_fpu_for (l o pasObjectAbs aag) st) r"
                and P="(=) st" and P'="\<top>" in equiv_valid_2_bind)
       apply (rule gen_asm_ev2_l[simplified K_def pred_conj_def])
       apply (rule gen_asm_ev2_r')
       apply (rule_tac R'="\<lambda>(r, ms') (r', ms''). r = r' \<and>
                             equiv_machine_state (l o pasObjectAbs aag) ms' ms'' \<and>
                             equiv_hyp_state (numlistregs_for (l o pasObjectAbs aag) st)
                                             (cur_vcpu_for (l o pasObjectAbs aag) st) ms' ms'' \<and>
                             equiv_fpu_state (cur_fpu_for (l o pasObjectAbs aag) st) ms' ms''"
                   and Q="\<lambda>r s. s = st" and Q'="\<top>\<top>" and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
            apply (clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
            apply (rule states_equiv_for_machine_state_update)
               apply clarsimp
              apply (clarsimp simp: equiv_for_def)
             apply (rule equiv_hyp_state_identical_hyp_state_updates)
              apply (clarsimp simp: equiv_hyp_state_def cur_vcpu_for_def numlistregs_for_def
                             split: option.splits if_splits)
             apply (clarsimp simp: states_equiv_for_def)
            apply (rule equiv_fpu_state_identical_fpu_state_updates)
             apply (fastforce simp: equiv_fpu_state_def cur_fpu_for_def hw_fpu_def
                             split: option.splits if_splits)
            apply (clarsimp simp: states_equiv_for_def)
           apply (insert equiv_dmo)[1]
           apply (clarsimp simp: select_f_def equiv_valid_2_def equiv_valid_def2 split_def equiv_for_def)
           apply (erule_tac x="numlistregs_for (l o pasObjectAbs aag) st" in meta_allE)
           apply (erule_tac x="cur_vcpu_for (l o pasObjectAbs aag) st" in meta_allE)
           apply (erule_tac x="cur_fpu_for (l o pasObjectAbs aag) st" in meta_allE)
           apply (drule_tac x=rv in spec, drule_tac x=rv' in spec, fastforce)
          apply wp
         apply wp
        apply clarsimp
       apply clarsimp
      apply (clarsimp simp: equiv_valid_2_def in_monad states_equiv_for_def equiv_hyp_def equiv_hyp_state_def comp_def)
      apply (rule conjI)
       apply (frule cur_vcpu_for_equiv_l)
       apply (case_tac "cur_vcpu_for (l o pasObjectAbs aag) t"; clarsimp)
        apply (clarsimp simp: cur_vcpu_for_def split: option.splits if_splits)
       apply (clarsimp simp: equiv_for_def)
       apply (erule_tac x=ptr in allE)+
       apply (fastforce simp: cur_vcpu_for_Some cur_vcpu_of_def hw_vcpu_def numlistregs_for_def
                       split: if_splits option.splits)
      apply (fastforce simp: equiv_fpu_def equiv_fpu_state_def equiv_for_def hw_fpu_def cur_fpu_for_def
                      split: if_splits)
     apply (wpsimp wp: guard)+
  apply (drule guard)
  apply (clarsimp simp: states_equiv_for_def equiv_fpu_cur_fpu_for equiv_hyp_def
                        cur_vcpu_for_equiv_l numlistregs_for_equiv_l comp_def)
  done

lemma do_machine_op_reads_respects_l:
  assumes equiv_dmo:
   "equiv_valid_inv (equiv_machine_state (l o pasObjectAbs aag)) (equiv_machine_state (l o pasObjectAbs aag)) \<top> f"
  assumes hyp_state_inv:
    "\<And>n cv ms. \<lbrace>equiv_hyp_state n cv ms\<rbrace> f \<lbrace>\<lambda>_. equiv_hyp_state n cv ms\<rbrace>"
   assumes fpu_state_inv:
    "\<And>cf ms. \<lbrace>equiv_fpu_state cf ms\<rbrace> f \<lbrace>\<lambda>_. equiv_fpu_state cf ms\<rbrace>"
  shows
    "reads_respects_l aag l \<top> (do_machine_op f)"
 apply (rule do_machine_op_reads_respects_l'[where Q="\<lambda>_ _ _. \<top>"])
   apply (insert equiv_dmo)
  apply (clarsimp simp: equiv_valid_2_def equiv_valid_def2 equiv_for_or
                  simp: split_def split: prod.splits simp: equiv_for_def)[1]
   apply (rename_tac rv st rv' st')
   apply (drule_tac x=s in spec, drule_tac x=t in spec)
   apply clarsimp
   apply (drule (1) bspec)+
   apply clarsimp
   apply (rule conjI)
    apply (erule use_valid[OF _ hyp_state_inv])
    apply (rule equiv_hyp_state_sym)
    apply (erule use_valid[OF _ hyp_state_inv])
    apply (erule equiv_hyp_state_sym)
   apply (erule use_valid[OF _ fpu_state_inv])
   apply (rule equiv_fpu_state_sym)
   apply (erule use_valid[OF _ fpu_state_inv])
   apply (erule equiv_fpu_state_sym)
  apply simp
  done

lemma readVCPUHardwareReg_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>b. cur_vcpu_for (l o pasObjectAbs aag) s = Some b \<and>
                                   (vcpuRegSavedWhenDisabled reg \<longrightarrow> b))
                          (do_machine_op (readVCPUHardwareReg reg))"
  unfolding readVCPUHardwareReg_def
  apply (wpsimp wp: do_machine_op_reads_respects_l')
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def cur_vcpu_for_Some)
  apply (case_tac b; clarsimp simp: hw_vcpu_def)
  apply (drule_tac x=reg in fun_cong, clarsimp)
  done

lemma dmo_mol_reads_respects_l:
  "reads_respects_l aag l \<top> (do_machine_op (machine_op_lift mop))"
  apply (rule do_machine_op_reads_respects_l)
    apply (rule equiv_valid_guard_imp[OF machine_op_lift_ev])
    apply simp
   apply wp+
  done

lemma writeVCPUHardwareReg_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (do_machine_op (writeVCPUHardwareReg reg val))"
  unfolding writeVCPUHardwareReg_def dmo_distr
  apply (wpsimp wp: dmo_mol_reads_respects_l)
    apply (wpsimp wp: do_machine_op_reads_respects_l' modify_ev)
   apply wpsimp
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def)
  apply (case_tac "cur_vcpu_for (l \<circ> pasObjectAbs aag) s"; clarsimp simp: cur_vcpu_for_Some)
  apply (clarsimp simp: hw_vcpu_def split: if_splits)
   apply (intro conjI ext; drule_tac x=r in fun_cong; clarsimp)+
  done

lemma vcpu_save_reg_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>b. current_vcpu s = Some (vr,b) \<and> (vcpuRegSavedWhenDisabled reg \<longrightarrow> b))
                          (vcpu_save_reg vr reg)"
  (is "reads_respects_l _ _ ?P _")
  unfolding vcpu_save_reg_def
  apply (rule wp_pre)
   apply (rule_tac P="?P" and ptr=vr in reads_respects_l_unit_cases)
     apply wpsimp+
  done

lemma vcpu_save_reg_range_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>b. current_vcpu s = Some (vr,b))
                          (vcpu_save_reg_range vr VCPURegTTBR0 VCPURegSPSR_EL1)"
  (is "reads_respects_l _ _ ?P _")
  unfolding vcpu_save_reg_range_def
  apply (wpsimp wp: mapM_x_ev[where I="\<lambda>s. \<exists>b. current_vcpu s = Some (vr,b)"])
    apply (auto simp: upto_enum_def fromEnum_def enum_vcpureg toEnum_def vcpuRegSavedWhenDisabled_def)[1]
   apply wpsimp+
  done

lemma get_gic_vcpu_ctrl_hcr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>b. cur_vcpu_for (l o pasObjectAbs aag) s = Some True)
                          (do_machine_op (get_gic_vcpu_ctrl_hcr))"
  unfolding get_gic_vcpu_ctrl_hcr_def dmo_distr
  apply (rule use_spec_ev)
  apply (wpsimp wp: do_machine_op_reads_respects_l')
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def cur_vcpu_for_Some hw_vcpu_def)
  done

lemma get_gic_vcpu_ctrl_vmcr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>b. cur_vcpu_for (l o pasObjectAbs aag) s = Some b)
                          (do_machine_op (get_gic_vcpu_ctrl_vmcr))"
  unfolding get_gic_vcpu_ctrl_vmcr_def dmo_distr
  apply (rule use_spec_ev)
  apply (wpsimp wp: do_machine_op_reads_respects_l')
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def cur_vcpu_for_Some hw_vcpu_def)
  done

lemma get_gic_vcpu_ctrl_apr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>b. cur_vcpu_for (l o pasObjectAbs aag) s = Some b)
                          (do_machine_op (get_gic_vcpu_ctrl_apr))"
  unfolding get_gic_vcpu_ctrl_apr_def dmo_distr
  apply (rule use_spec_ev)
  apply (wpsimp wp: do_machine_op_reads_respects_l')
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def cur_vcpu_for_Some hw_vcpu_def)
  done

lemma cur_fpu_for_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (cur_fpu_for Q s)\<rbrace>"
  unfolding cur_fpu_for_def
  by (wp assms)

lemma numlistregs_for_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (numlistregs s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (numlistregs_for Q s)\<rbrace>"
  unfolding numlistregs_for_def
  by (wp assms)

lemma get_gic_vcpu_ctrl_lr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. (\<exists>b. cur_vcpu_for (l o pasObjectAbs aag) s = Some b) \<and>
                               unat reg < numlistregs s)
                          (do_machine_op (get_gic_vcpu_ctrl_lr reg))"
  unfolding get_gic_vcpu_ctrl_lr_def dmo_distr
  apply wp
     apply (rule use_spec_ev)
     apply (wpsimp wp: do_machine_op_reads_respects_l')
    apply (wpsimp wp: dmo_mol_reads_respects_l)
   apply (rule hoare_lift_Pf[where f="numlistregs_for _"])
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift cur_fpu_for_lift)
   apply (wpsimp wp: numlistregs_for_lift)
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def cur_vcpu_for_Some hw_vcpu_def)
  apply (drule_tac x="unat reg" in fun_cong)+
  apply (clarsimp simp: numlistregs_for_def split: if_splits)
  done

lemma vgic_update_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (vgic_update vr f)"
  unfolding vgic_update_def by wp

lemma vgic_lr_update_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (vgic_update_lr vr reg irq)"
  unfolding vgic_update_lr_def by wp

lemma vcpu_save_hcr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. current_vcpu s = Some (vr,True))
                          (vcpu_save_hcr vr)"
  (is "reads_respects_l _ _ ?P _")
  unfolding vcpu_save_hcr_def
  apply (rule wp_pre)
   apply (rule_tac P="?P" and ptr=vr in reads_respects_l_unit_cases)
     apply (wpsimp simp: get_gic_vcpu_ctrl_hcr_def)+
  done

lemma vcpu_save_vmcr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>b. current_vcpu s = Some (vr,b))
                        (vcpu_save_vmcr vr)"
  (is "reads_respects_l _ _ ?P _")
  unfolding vcpu_save_vmcr_def
  apply (rule wp_pre)
   apply (rule_tac P="?P" and ptr=vr in reads_respects_l_unit_cases)
     apply (wpsimp simp: get_gic_vcpu_ctrl_vmcr_def)+
  done

lemma vcpu_save_apr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>b. current_vcpu s = Some (vr,b))
                        (vcpu_save_apr vr)"
  (is "reads_respects_l _ _ ?P _")
  unfolding vcpu_save_apr_def
  apply (rule wp_pre)
   apply (rule_tac P="?P" and ptr=vr in reads_respects_l_unit_cases)
     apply wpsimp+
  done

lemma vcpu_save_lr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. (\<exists>b. current_vcpu s = Some (vr,b)) \<and> valid_numlistregs s \<and> reg < numlistregs s)
                          (vcpu_save_lr vr reg)"
  (is "reads_respects_l _ _ ?P _")
  unfolding vcpu_save_lr_def
  apply (rule wp_pre)
   apply (rule_tac P="?P" and ptr=vr in reads_respects_l_unit_cases)
     apply wpsimp
     apply (clarsimp simp: valid_numlistregs_def)
     apply (simp add: unat_of_nat64)
    apply wpsimp
    apply assumption
   apply wpsimp
  apply (clarsimp simp: cur_vcpu_for_def)
  done

crunch vcpu_save_hcr, vcpu_save_vmcr, vcpu_save_apr, vcpu_save_lr, vcpu_save_lrs
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  (wp: mapM_wp_inv)

lemma vcpu_save_lrs_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. (\<exists>b. current_vcpu s = Some (vr,b)) \<and> valid_numlistregs s)
                          (vcpu_save_lrs vr)"
  (is "reads_respects_l _ _ ?P _")
  unfolding vcpu_save_lrs_def
  apply (rule wp_pre)
   apply (rule_tac P="?P" and ptr=vr in reads_respects_l_unit_cases)
     apply (wpsimp wp: mapM_ev)
            apply (rule wp_pre)
             apply wpsimp
            apply (prop_tac "\<forall>x \<in> set rva. x < numlistregs s")
             apply (erule conjunct1)
            apply clarsimp
            apply assumption
           apply wpsimp+
     apply (fastforce simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)
    apply (wpsimp wp: mapM_wp_inv simp: vcpu_save_lr_def get_gic_vcpu_ctrl_lr_def dmo_distr)+
  done

lemma equiv_valid_cases'':
  "\<lbrakk> \<And>s t. \<lbrakk> A s t; I s t; R s; R t \<rbrakk> \<Longrightarrow> P s = P t;
     equiv_valid I A B (R and P) f; equiv_valid I A B ((\<lambda>s. \<not>P s) and R) f \<rbrakk>
     \<Longrightarrow> equiv_valid I A B R f"
  by (fastforce simp: equiv_valid_def2 equiv_valid_2_def)

lemma hw_vcpu_Some_True[simp]:
  "hw_vcpu n (Some True) vst = Some (vcpu_mask n vst)"
  apply (clarsimp simp: hw_vcpu_def)
  apply (rule vcpu_state.equality; clarsimp)
  apply (rule gic_vcpu_interface.equality; clarsimp)
  apply (rule ext; clarsimp)
  done

lemma vcpu_mask_regs_update[simp]:
  "vcpu_mask n (vcpu_regs_update f vst) = vcpu_regs_update f (vcpu_mask n vst)"
  by (rule vcpu_state.equality; clarsimp)

lemma check_export_arch_timer_reads_respects_l'':
  "reads_respects_l aag l (\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None)
                          (do_machine_op check_export_arch_timer)"
  (is "reads_respects_l _ _ ?P _")
   unfolding check_export_arch_timer_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects_l)
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_def)
    apply wpsimp+
   done

lemma check_export_arch_timer_reads_respects_l':
  "reads_respects_l aag l (\<lambda>s. \<exists>vr. cur_vcpu_for (l o pasObjectAbs aag) s = Some True)
                          (do_machine_op check_export_arch_timer)"
  (is "reads_respects_l _ _ ?P _")
   unfolding check_export_arch_timer_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects_l)
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_Some)
    apply wpsimp+
   done

lemma cur_vcpu_for_None':
  "(cur_vcpu_for P s = None) = (\<forall>vr. P vr \<longrightarrow> cur_vcpu_of s vr = None)"
  by (auto simp: cur_vcpu_for_def cur_vcpu_of_def split: option.splits)

lemma check_export_arch_timer_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<exists>vr. current_vcpu s = Some (vr,True))
                          (do_machine_op check_export_arch_timer)"
  (is "reads_respects_l _ _ ?P _")
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None" in equiv_valid_cases'')
    apply (prop_tac "equiv_hyp (l o pasObjectAbs aag) s t")
     apply (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)[1]
    apply (auto simp: cur_vcpu_for_None' equiv_hyp_def equiv_for_def)[1]
   apply (wpsimp wp: check_export_arch_timer_reads_respects_l'')
  apply (wpsimp wp: check_export_arch_timer_reads_respects_l')
  done

lemma save_virt_timer_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. current_vcpu s = Some (vr,True))
                          (save_virt_timer vr)"
  (is "reads_respects_l _ _ ?P _")
  unfolding save_virt_timer_def
  apply (wpsimp wp: vcpu_save_reg_reads_respects_l)
  apply auto
  done

lemma dmo_dsb_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (do_machine_op dsb)"
  unfolding dsb_def
  by (wpsimp wp: dmo_mol_reads_respects_l)

lemma dmo_isb_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (do_machine_op isb)"
  unfolding isb_def
  by (wpsimp wp: dmo_mol_reads_respects_l)

lemma dmo_setHCR_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (do_machine_op (setHCR val))"
  unfolding setHCR_def
  by (wpsimp wp: dmo_mol_reads_respects_l)

lemma vcpu_save_lrs_helper:
  "do (do num_list_regs <- gets (arm_gicvcpu_numlistregs \<circ> arch_state);
                        return [0..<num_list_regs] >>= mapM (vcpu_save_lr vr)
       od);
      m
   od = do vcpu_save_lrs vr; m od"
  by (simp add: vcpu_save_lrs_def bind_assoc)

lemma bind_assoc_helper:
  "(do x <- f;
       y <- g x;
       (z y :: ('s,unit) nondet_monad)
    od) =
   (do y <- (f >>= g);
       z y od)"
  by (simp add: bind_assoc)

lemma vcpu_save_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. current_vcpu s = cv \<and> valid_numlistregs s) (vcpu_save cv)"
  apply (simp only: vcpu_save_def fun_app_def bind_assoc_helper vcpu_save_vgic_defs[symmetric] vcpu_save_lrs_helper)
  apply (wpsimp wp: when_ev mapM_ev mapM_wp_inv)+
  apply auto
  done

lemma dmo_maskInterrupt_reads_respects_l[wp]:
  "reads_respects_l aag l \<top> (do_machine_op (maskInterrupt m irq))"
  unfolding maskInterrupt_def
  apply (rule use_spec_ev)
  apply (wpsimp wp: do_machine_op_reads_respects_l' modify_ev)
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def)
  done

lemma enableFpuEL01_reads_respects_l'':
  "reads_respects_l aag l (\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None)
                          (do_machine_op enableFpuEL01)"
  (is "reads_respects_l _ _ ?P _")
   unfolding enableFpuEL01_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects_l)
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_def)
    apply wpsimp+
   done

lemma enableFpuEL01_reads_respects_l':
  "reads_respects_l aag l (\<lambda>s. \<exists>vr. cur_vcpu_for (l o pasObjectAbs aag) s = Some True)
                          (do_machine_op enableFpuEL01)"
  (is "reads_respects_l _ _ ?P _")
   unfolding enableFpuEL01_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects_l)
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_Some)
    apply wpsimp+
   done

lemma enableFpuEL01_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<forall>vr b. current_vcpu s = Some (vr,b) \<longrightarrow> b)
                          (do_machine_op enableFpuEL01)"
  (is "reads_respects_l _ _ ?P _")
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None" in equiv_valid_cases'')
    apply (prop_tac "equiv_hyp (l o pasObjectAbs aag) s t")
     apply (auto simp: states_equiv_for_def equiv_hyp_def equiv_for_def)[1]
    apply (auto simp: cur_vcpu_for_None' equiv_hyp_def equiv_for_def)[1]
   apply (wpsimp wp: enableFpuEL01_reads_respects_l'')
  apply (wpsimp wp: enableFpuEL01_reads_respects_l')
  done

lemma setSCTLR_reads_respects_l'':
  "reads_respects_l aag l (\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None)
                          (do_machine_op (setSCTLR val))"
  (is "reads_respects_l _ _ ?P _")
   unfolding setSCTLR_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects_l)
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_def)
    apply wpsimp+
   done

lemma setSCTLR_reads_respects_l':
  "reads_respects_l aag l (\<lambda>s. \<exists>vr. cur_vcpu_for (l o pasObjectAbs aag) s = Some True)
                          (do_machine_op (setSCTLR val))"
  (is "reads_respects_l _ _ ?P _")
   unfolding setSCTLR_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects_l)
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_Some)
    apply wpsimp+
   done

lemma setSCTLR_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<forall>vr b. current_vcpu s = Some (vr,b) \<longrightarrow> b)
                          (do_machine_op (setSCTLR val))"
  (is "reads_respects_l _ _ ?P _")
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None" in equiv_valid_cases'')
    apply (prop_tac "equiv_hyp (l o pasObjectAbs aag) s t")
     apply (auto simp: states_equiv_for_def equiv_hyp_def equiv_for_def)[1]
    apply (auto simp: cur_vcpu_for_None' equiv_hyp_def equiv_for_def)[1]
   apply (wpsimp wp: setSCTLR_reads_respects_l'')
  apply (wpsimp wp: setSCTLR_reads_respects_l')
  done

lemma set_gic_vcpu_ctrl_hcr_reads_respects_l'':
  "reads_respects_l aag l (\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None)
                          (do_machine_op (set_gic_vcpu_ctrl_hcr val))"
  (is "reads_respects_l _ _ ?P _")
   unfolding set_gic_vcpu_ctrl_hcr_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects_l)
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_def)
    apply wpsimp+
   done

lemma vcpu_mask_hcr_update[simp]:
  "vcpu_mask n (vcpu_vgic_update (vgic_hcr_update f) vst) = vcpu_vgic_update (vgic_hcr_update f) (vcpu_mask n vst)"
  by (rule vcpu_state.equality; clarsimp)

lemma set_gic_vcpu_ctrl_hcr_reads_respects_l':
  "reads_respects_l aag l (\<lambda>s. \<exists>vr. cur_vcpu_for (l o pasObjectAbs aag) s = Some True)
                          (do_machine_op (set_gic_vcpu_ctrl_hcr val))"
  (is "reads_respects_l _ _ ?P _")
   unfolding set_gic_vcpu_ctrl_hcr_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects_l)
     apply (rule do_machine_op_reads_respects_l')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_Some)
    apply wpsimp+
   done

lemma set_gic_vcpu_ctrl_hcr_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. \<forall>vr b. current_vcpu s = Some (vr,b) \<longrightarrow> b)
                          (do_machine_op (set_gic_vcpu_ctrl_hcr val))"
  (is "reads_respects_l _ _ ?P _")
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None" in equiv_valid_cases'')
    apply (prop_tac "equiv_hyp (l o pasObjectAbs aag) s t")
     apply (auto simp: states_equiv_for_def equiv_hyp_def equiv_for_def)[1]
    apply (auto simp: cur_vcpu_for_None' equiv_hyp_def equiv_for_def)[1]
   apply (wpsimp wp: set_gic_vcpu_ctrl_hcr_reads_respects_l'')
  apply (wpsimp wp: set_gic_vcpu_ctrl_hcr_reads_respects_l')
  done

lemma vcpu_disable_Some_reads_respects_l[wp]:
  "reads_respects_l aag l (\<lambda>s. current_vcpu s = Some (vr,True)) (vcpu_disable (Some vr))"
  apply (simp only: vcpu_disable_def fun_app_def bind_assoc_helper vcpu_save_vgic_defs[symmetric] vcpu_save_lrs_helper)
  apply (clarsimp simp: dmo_distr)
  apply (wpsimp wp: when_ev mapM_ev mapM_wp_inv)+
  apply auto
  done

definition states_equiv_for_non_hyp ::
  "(obj_ref \<Rightarrow> bool) \<Rightarrow> (irq \<Rightarrow> bool) \<Rightarrow> (asid \<Rightarrow> bool) \<Rightarrow>
   (domain \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equiv_for_non_hyp P Q R S s s' \<equiv>
     equiv_for P kheap s s' \<and>
     equiv_machine_state P (machine_state s) (machine_state s') \<and>
     equiv_for (P \<circ> fst) cdt s s' \<and>
     equiv_for (P \<circ> fst) cdt_list s s' \<and>
     equiv_for (P \<circ> fst) is_original_cap s s' \<and>
     equiv_for Q interrupt_states s s' \<and>
     equiv_for Q interrupt_irq_node s s' \<and>
     equiv_for S  ready_queues s s' \<and>
     equiv_asids R s s' \<and>
     equiv_fpu P s s'"

lemma states_equiv_for_non_hyp_refl:
  "states_equiv_for_non_hyp P Q R S s s"
  by (auto simp: states_equiv_for_non_hyp_def intro: equiv_for_refl equiv_asids_refl equiv_hyp_refl equiv_fpu_refl)

lemma states_equiv_for_non_hyp_sym:
  "states_equiv_for_non_hyp P Q R S s t \<Longrightarrow> states_equiv_for_non_hyp P Q R S t s"
  by (auto simp: states_equiv_for_non_hyp_def intro: equiv_for_sym equiv_asids_sym equiv_hyp_sym equiv_fpu_sym)

lemma states_equiv_for_non_hyp_trans:
  "\<lbrakk> states_equiv_for_non_hyp P Q R S s t; states_equiv_for_non_hyp P Q R S t u \<rbrakk>
     \<Longrightarrow> states_equiv_for_non_hyp P Q R S s u"
  by (auto simp: states_equiv_for_non_hyp_def
          intro: equiv_for_trans equiv_asids_trans equiv_hyp_trans equiv_fpu_trans equiv_forI
           elim: equiv_forE)

lemma states_equiv_for_non_hyp_lift:
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_for P kheap st s\<rbrace>"
  assumes "\<And>ms. f \<lbrace>\<lambda>s. equiv_machine_state P ms (machine_state s)\<rbrace>"
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_for (P \<circ> fst) cdt st s\<rbrace>"
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_for (P \<circ> fst) cdt_list st s\<rbrace>"
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_for (P \<circ> fst) is_original_cap st s\<rbrace>"
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_for Q interrupt_states st s\<rbrace>"
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_for Q interrupt_irq_node st s\<rbrace>"
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_for S  ready_queues st s\<rbrace>"
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_asids R st s\<rbrace>"
  assumes "\<And>st. f \<lbrace>\<lambda>s. equiv_fpu P st s\<rbrace>"
  shows "f \<lbrace>states_equiv_for_non_hyp P Q R S st\<rbrace>"
  unfolding states_equiv_for_non_hyp_def
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift, rule assms)+
   apply (rule assms)
  apply simp
  done

crunch vcpu_switch
  for is_original_cap[wp]: "\<lambda>s. P (is_original_cap s)"
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma equiv_asids_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. equiv_asids R st s\<rbrace>"
  unfolding equiv_asids_def equiv_asid_def asid_pools_at_eq
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift assms)
  apply auto
  done

crunch vcpu_switch
  for asid_pools[wp]: "\<lambda>s. P (asid_pools_of s)"
  (wp: crunch_wps)

lemma equiv_fpu_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (fpu_state (machine_state s))\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (current_fpu s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. equiv_fpu P st s\<rbrace>"
  apply (clarsimp simp: valid_def equiv_fpu_def equiv_for_def)
  apply (erule_tac x=x in allE, clarsimp)
  apply (frule_tac P="\<lambda>s'. fpu_state (machine_state s') = fpu_state (machine_state s)" in use_valid)
    apply (rule assms(1))
   apply simp
  apply (drule_tac P="\<lambda>s'. current_fpu s' = current_fpu s" in use_valid)
    apply (rule assms(2))
   apply simp
  apply (clarsimp simp: equiv_fpu_def opt_map_def fpu_of_state_def cur_fpu_for_def get_tcb_def
                 split: option.splits kernel_object.splits if_splits)
  done

crunch vcpu_restore
  for kheap[wp]: "\<lambda>s. P (kheap s)"
  and fpu_state[wp]: "\<lambda>s. P (fpu_state (machine_state s))"
  and underlying_memory[wp]: "\<lambda>s. P (underlying_memory (machine_state s))"
  and device_state[wp]: "\<lambda>s. P (device_state (machine_state s))"
  (wp: crunch_wps dmo_wp simp: crunch_simps)

lemma equiv_machine_state_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P  (device_state (machine_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. equiv_machine_state P ms (machine_state s)\<rbrace>"
  by (wpsimp wp: assms equiv_for_lift2)

lemma vcpu_restore_states_equiv_for_non_hyp[wp]:
  "vcpu_restore vopt \<lbrace>states_equiv_for_non_hyp P Q R S st\<rbrace>"
  apply (rule states_equiv_for_non_hyp_lift)
           defer
           defer
           apply (rule equiv_for_lift, (wpsimp; fail))+
     apply (rule equiv_asids_lift)
      apply wpsimp
     apply wpsimp
    apply (rule equiv_fpu_lift)
     apply (wpsimp simp: get_tcb_def wp: equiv_for_lift)+
  apply (wpsimp wp: equiv_machine_state_lift)
  done

lemma equiv_valid_split:
  assumes "equiv_valid I A B P f"
  assumes "equiv_valid I' A' B' P' f"
  shows "equiv_valid (\<lambda>s s'. I s s' \<and> I' s s') (\<lambda>s s'. A s s' \<and> A' s s')
                     (\<lambda>s s'. B s s' \<and> B' s s') (\<lambda>s. P s \<and> P' s) f"
  using assms by (fastforce simp: equiv_valid_def2 equiv_valid_2_def)

definition vmask where
  "vmask \<equiv> vcpu_mask"

lemma vcpus_of_vcpu_proj:
  "vcpus_of s vr = Some vcpu
   \<Longrightarrow> vcpu_proj UNIV UNIV True True True vr s = Some (vmask (numlistregs s) vcpu)"
  by (clarsimp simp: vcpu_proj_def vmask_def cong: if_cong)

lemma vmask_truncate_helper:
  "vmask (numlistregs s) (vcpu_state.truncate vcpu) =
   vcpu_state.truncate (vmask (numlistregs s) vcpu)"
  by (clarsimp simp: vmask_def vcpu_state.defs)

lemma vcpu_restore_vcpu_proj':
  "\<lbrace>\<lambda>s. vopt = vcpu_proj UNIV UNIV True True True vr s \<and> valid_arch_state s\<rbrace>
    vcpu_restore vr
    \<lbrace>\<lambda>_ s. vopt = vcpu_proj {} {} False False False vr s\<rbrace>"
  by (wpsimp wp: vcpu_restore_vcpu_proj)

lemma vcpu_restore_helper:
  "\<lbrace>\<lambda>s. vcpus_of s vr = Some vcpu \<and> valid_arch_state s\<rbrace>
   vcpu_restore vr
   \<lbrace>\<lambda>_ s. vmask (numlistregs s) (vcpu_state.truncate vcpu) = vmask (numlistregs s) (vcpu_state (machine_state s))\<rbrace>"
  apply (rule_tac Q'="\<lambda>_ s. vcpus_of s vr = Some vcpu \<and> Some (vmask (numlistregs s) vcpu) = vcpu_proj {} {} False False False vr s" in hoare_strengthen_post)
   apply (rule_tac P'="\<lambda>s. vcpus_of s vr = Some vcpu \<and> Some (vmask (numlistregs s) vcpu) = vcpu_proj UNIV UNIV True True True vr s \<and> valid_arch_state s" in hoare_weaken_pre)
    apply (rule hoare_weaken_pre)
     apply (rule hoare_vcg_conj_lift)
      apply wpsimp
     apply wps
     apply (wp vcpu_restore_vcpu_proj')
    apply clarsimp
   apply clarsimp
   apply (drule vcpus_of_vcpu_proj)
   apply simp
  apply clarsimp
  apply (clarsimp simp: vmask_truncate_helper)
  apply (clarsimp simp: vcpu_proj_def vcpu_state.defs vmask_def cong: if_cong)
  done


lemma vcpu_restore_2_helper:
  "\<lbrace>\<lambda>s. vcpus_of s vr = Some vcpu \<and> valid_arch_state s\<rbrace>
   vcpu_restore_2 vr
   \<lbrace>\<lambda>_ s. hw_vcpu_of s vr = Some (vcpu_mask (numlistregs s) (vcpu_state.truncate vcpu))\<rbrace>"
  unfolding vcpu_restore_2_def
apply (rule_tac Q'="\<lambda>_ s. vcpu_mask (numlistregs s) (vcpu_state.truncate vcpu) = vcpu_mask (numlistregs s) (vcpu_state (machine_state s)) \<and>
     current_vcpu s = Some (vr,True)" in hoare_strengthen_post)
   apply wp
    apply (rule hoare_vcg_conj_lift)
     apply simp
     apply (wp vcpu_restore_helper[simplified vmask_def])
    apply simp
    apply wpsimp+
  apply (clarsimp simp: cur_vcpu_of_def)
  done

lemma get_vcpu_vcpu_at:
  "\<lbrace>\<lambda>s. vcpu_at vr s \<longrightarrow> P s\<rbrace> get_vcpu vr \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding get_vcpu_def gets_map_def
  by (wpsimp simp: obj_at_def opt_map_def split: option.splits)

crunch vcpu_restore_2
  for kheap[wp]: "\<lambda>s. P (kheap s)"
  and numlistregs[wp]: "\<lambda>s. P (numlistregs s)"

(* This the main use of states_equiv_for : P is use to restrict the labels we want to consider *)
abbreviation states_equiv_for_labels_non_hyp ::
  "'a PAS \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equiv_for_labels_non_hyp aag P \<equiv>
      states_equiv_for_non_hyp (\<lambda>x. P (pasObjectAbs aag x)) (\<lambda>x. P (pasIRQAbs aag x))
                       (\<lambda>x. P (pasASIDAbs aag x)) (\<lambda>x. \<exists>l\<in>pasDomainAbs aag x. P l)"

abbreviation reads_respects_l_non_hyp where
  "reads_respects_l_non_hyp aag L P f \<equiv> equiv_valid_inv \<top>\<top> (states_equiv_for_labels_non_hyp aag L) P f"

lemma states_equiv_for_non_hyp_symmetric:
  "states_equiv_for_non_hyp P Q R S s t = states_equiv_for_non_hyp P Q R S t s"
  by (auto simp: states_equiv_for_non_hyp_sym)

(* for things that only modify parts of the state not in the state relations,
   we don't care what they read since these reads are unobservable anyway;
   however, we cannot assert anything about their return-values *)
lemma reads_respects_l_non_hyp_unobservable:
  assumes f:
    "\<And>P Q R S st. \<lbrace>states_equiv_for_non_hyp P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for_non_hyp P Q R S st\<rbrace>"
  shows
    "reads_respects_l_non_hyp aag l \<top> (f :: (det_state,unit) nondet_monad)"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
   apply (subst states_equiv_for_non_hyp_symmetric)
   apply (erule use_valid)
    apply (wp assms)
   apply (subst states_equiv_for_non_hyp_symmetric)
   apply (erule use_valid)
    apply (wp assms)
  apply simp
  done

lemma states_equiv_for_non_hyp_current_vcpu_update[simp]:
  " states_equiv_for_non_hyp P Q R S st
            (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := cv\<rparr>\<rparr>) = states_equiv_for_non_hyp P Q R S st s"
  by (clarsimp simp: states_equiv_for_non_hyp_def equiv_for_def equiv_asids_def equiv_asid_def equiv_fpu_def cur_fpu_for_def get_tcb_def)

lemma vcpu_restore_2_reads_respects_hyp_l:
  "equiv_valid (\<lambda>s s'. equiv_for P kheap s s' \<and>
                       equiv_for P (K \<circ> numlistregs) s s')
               \<top>\<top> (\<lambda>s s'. equiv_for P cur_vcpu_of s s' \<and>
                           equiv_for P hw_vcpu_of s s') (valid_arch_state)
               (vcpu_restore_2 vr)"
  apply (rule_tac P'="\<lambda>s. vcpus_of s vr \<noteq> None" in equiv_valid_guard_necessary)
   apply (unfold vcpu_restore_2_def vcpu_restore_def)[1]
   apply (clarsimp simp: bind_assoc)
   apply (wpsimp wp: get_vcpu_vcpu_at simp: obj_at_def opt_map_def)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (rule context_conjI)
   apply (erule use_valid, rule equiv_for_lift, wp)+
   apply simp
  apply (rename_tac s' t' vcpu vcpu')
  apply (rule context_conjI, clarsimp simp: comp_def)
   apply (erule use_valid, rule equiv_for_lift, wp)+
   apply simp
  apply (prop_tac "current_vcpu s' = Some (vr,True)")
   apply (erule use_valid, wpsimp simp: vcpu_restore_2_def, simp)
  apply (prop_tac "current_vcpu t' = Some (vr,True)")
   apply (erule use_valid, wpsimp simp: vcpu_restore_2_def, simp)
  apply (rule conjI)
   apply (clarsimp simp: equiv_for_def)
  apply (case_tac "P vr")
   apply (prop_tac "vcpu = vcpu'")
    apply (clarsimp simp: equiv_for_def opt_map_def)
   apply (drule use_valid[OF _ vcpu_restore_2_helper], simp)+
   apply (subgoal_tac " Some
            (vcpu_vgic_update
              (vgic_lr_update (\<lambda>f r. if numlistregs s' \<le> r then undefined else f r))
              (vcpu_state.truncate vcpu)) =
           Some
            (vcpu_vgic_update
              (vgic_lr_update (\<lambda>f r. if numlistregs t' \<le> r then undefined else f r))
              (vcpu_state.truncate vcpu'))")
    apply (clarsimp simp: equiv_for_def cur_vcpu_of_def)
   apply (clarsimp simp: equiv_for_def)
   apply (drule mp, fastforce)+
   apply clarsimp
  apply (clarsimp simp: equiv_for_def cur_vcpu_of_def)
  done

lemma vcpu_restore_2_reads_respects_l:
  "reads_respects_l aag l (valid_arch_state) (vcpu_restore_2 vr)"
  apply (rule equiv_valid_conseq)
    apply (rule equiv_valid_split)
     apply (subst vcpu_restore_2_def)[1]
     apply (rule reads_respects_l_non_hyp_unobservable[of _ l aag])
     apply (wpsimp)+
    apply (rule vcpu_restore_2_reads_respects_hyp_l[of "l o pasObjectAbs aag"])
   apply (auto simp: states_equiv_for_def comp_def
                     states_equiv_for_non_hyp_def equiv_hyp_def)
  done

lemma vcpu_enable_2_vcpu_proj:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj savedWhenDisabledRegs {} True False False vr s \<and> valid_arch_state s\<rbrace>
    vcpu_enable_2 vr
    \<lbrace>\<lambda>_ s. vopt = vcpu_proj {} {} False False False vr s\<rbrace>"
  by (wpsimp wp: vcpu_enable_vcpu_proj simp: vcpu_enable_2_def)

crunch vcpu_enable_2
  for kheap[wp]: "\<lambda>s. P (kheap s)"
  and numlistregs[wp]: "\<lambda>s. P (numlistregs s)"

lemma vcpu_enable_2_reads_respects_hyp_l:
  "equiv_valid (\<lambda>s s'. equiv_for P kheap s s' \<and>
                       equiv_for P (K \<circ> numlistregs) s s')
               (equiv_for P hw_vcpu_of)
               (\<lambda>s s'. equiv_for P cur_vcpu_of s s' \<and>
                           equiv_for P hw_vcpu_of s s') (\<lambda>s. current_vcpu s = Some (vr,False) \<and> valid_arch_state s)
               (vcpu_enable_2 vr)"
  apply (rule_tac P'="\<lambda>s. vcpus_of s vr \<noteq> None" in equiv_valid_guard_necessary)
   apply (unfold vcpu_enable_2_def vcpu_enable_def)[1]
   apply (clarsimp simp: bind_assoc)
   apply (wpsimp wp: get_vcpu_vcpu_at simp: obj_at_def opt_map_def)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (rule context_conjI)
   apply (erule use_valid, rule equiv_for_lift, wp)+
   apply simp
  apply (rename_tac s' t' vcpu vcpu')
  apply (rule context_conjI, clarsimp simp: comp_def)
   apply (erule use_valid, rule equiv_for_lift, wp)+
   apply simp
  apply (prop_tac "current_vcpu s' = Some (vr,True)")
   apply (erule use_valid, wpsimp simp: vcpu_enable_2_def, simp)
  apply (prop_tac "current_vcpu t' = Some (vr,True)")
   apply (erule use_valid, wpsimp simp: vcpu_enable_2_def, simp)
  apply (rule conjI)
   apply (clarsimp simp: equiv_for_def)
  apply (case_tac "P vr")
   apply (clarsimp simp: equiv_for_def)
   apply (erule_tac x=x in allE)+
   apply (drule mp, fastforce)+
   apply clarsimp
   apply (clarsimp simp: cur_vcpu_of_def)
   apply (prop_tac "vcpu' = vcpu")
    apply (clarsimp simp: opt_map_def)
   apply clarsimp
   apply (prop_tac "vcpu_proj savedWhenDisabledRegs {} True False False vr s =
                    vcpu_proj savedWhenDisabledRegs {} True False False vr t")
    apply (clarsimp simp: vcpu_proj_def hw_vcpu_def)
    apply (case_tac vcpu; clarsimp)
    apply (case_tac vcpu_vgic; clarsimp)
    apply (intro conjI ext)
     apply (drule_tac x=r in fun_cong, clarsimp)
    apply (drule_tac x=reg in fun_cong, clarsimp simp: vcpuRegSavedWhenDisabled_def split: if_splits vcpureg.splits)
   apply (prop_tac "vcpus_of s' vr = Some vcpu")
    apply (erule use_valid, wpsimp, simp)
   apply (prop_tac "vcpus_of t' vr = Some vcpu")
    apply (erule use_valid, wpsimp, clarsimp simp: opt_map_def)
   apply (drule use_valid, rule vcpu_enable_2_vcpu_proj, solves simp)
   apply simp
   apply (thin_tac "vcpu_proj _ _ _ _ _ _ _ = vcpu_proj _ _ _ _ _ _ _")
   apply (drule use_valid, rule vcpu_enable_2_vcpu_proj, solves simp)
   apply (thin_tac "vcpu_proj _ _ _ _ _ _ _ = vcpu_proj _ _ _ _ _ _ _")
   apply (clarsimp simp: vcpu_proj_def)
   apply (case_tac vcpu; clarsimp)
   apply (case_tac vcpu_vgic; clarsimp cong: if_cong)
  apply (clarsimp simp: equiv_for_def cur_vcpu_of_def)
  done

lemma vcpu_enable_states_equiv_for_non_hyp[wp]:
  "vcpu_enable vopt \<lbrace>states_equiv_for_non_hyp P Q R S st\<rbrace>"
  apply (rule states_equiv_for_non_hyp_lift)
           defer
           defer
           apply (rule equiv_for_lift, (wpsimp; fail))+
     apply (rule equiv_asids_lift)
      apply wpsimp
     apply wpsimp
    apply (rule equiv_fpu_lift)
     apply (wpsimp simp: get_tcb_def wp: equiv_for_lift)+
  apply (wpsimp wp: equiv_machine_state_lift)
  done

lemma vcpu_enable_2_reads_respects_l:
  "reads_respects_l aag l (\<lambda>s. current_vcpu s = Some (vr,False) \<and> valid_arch_state s) (vcpu_enable_2 vr)"
  apply (rule equiv_valid_conseq)
      apply (rule equiv_valid_split)
      apply (subst vcpu_enable_2_def)[1]
     apply (rule reads_respects_l_non_hyp_unobservable[of _ l aag])
            apply (wpsimp)+
    apply (rule vcpu_enable_2_reads_respects_hyp_l[of "l o pasObjectAbs aag"])
     apply (auto simp: states_equiv_for_def equiv_for_def
                       states_equiv_for_non_hyp_def  equiv_hyp_def)
  done

lemma reads_respects_l_modify_disable:
  "reads_respects_l aag l (\<lambda>s. current_vcpu s = Some (vr,True) \<and> l (pasObjectAbs aag vr))
                          (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (vr, False)\<rparr>\<rparr>))"
  apply (wpsimp wp: modify_ev')
  apply (clarsimp simp: states_equiv_for_def equiv_for_def)
  apply (intro conjI)
     apply (clarsimp simp: equiv_asids_def equiv_asid_def)
    apply (clarsimp simp: equiv_hyp_def equiv_for_def)
     apply (erule_tac x=vr in allE)+
     apply clarsimp
     apply (drule mp, fastforce)
     apply (clarsimp simp: cur_vcpu_of_def split: option.splits if_splits)
     apply (clarsimp simp: hw_vcpu_def)
     apply (case_tac "vcpu_state (machine_state s)"; case_tac "vcpu_state (machine_state t)"; clarsimp)
     apply (case_tac "vcpu_vgic"; case_tac "vcpu_vgica"; clarsimp)
     apply (intro conjI ext)
      apply (drule_tac x=r in fun_cong, clarsimp)
     apply (clarsimp split: if_splits)
   apply (clarsimp simp: equiv_fpu_def equiv_for_def cur_fpu_for_def get_tcb_def)
  done

lemma vcpu_disable_2_reads_respects_l:
  "reads_respects_l aag l (\<lambda>s. current_vcpu s = Some (vr,True) \<and> valid_arch_state s) (vcpu_disable_2 vr)"
  unfolding vcpu_disable_2_def
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_l_unit_cases)
     apply clarsimp
     apply (wp vcpu_disable_Some_reads_respects_l reads_respects_l_modify_disable)
     apply simp
    apply (wp modify_current_vcpu_equiv_but_for_labels)
    apply clarsimp
    apply assumption
   apply wpsimp
  apply (auto simp: cur_vcpu_of_def)
  done

crunch vcpu_disable_2, vcpu_enable_2, vcpu_restore_2
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"

lemma ev_evrv:
  "equiv_valid I A B P f \<Longrightarrow> equiv_valid_rv I A B (=) P f"
  by (unfold equiv_valid_def2)

lemma ev2_case_option:
  assumes "\<lbrakk>x = None; y = None\<rbrakk> \<Longrightarrow> equiv_valid_2 I A B R P1 Q1 f g"
  and "\<And>b. \<lbrakk>x = None; y = Some b\<rbrakk> \<Longrightarrow> equiv_valid_2 I A B R P2 (Q2 b) f (g' b)"
  and "\<And>a. \<lbrakk>x = Some a; y = None\<rbrakk> \<Longrightarrow> equiv_valid_2 I A B R (P3 a) Q3 (f' a) g"
  and "\<And>a b. \<lbrakk>x = Some a; y = Some b\<rbrakk> \<Longrightarrow> equiv_valid_2 I A B R (P4 a) (Q4 b) (f' a) (g' b)"
  shows "equiv_valid_2 I A B R (case_option (P1 and P2) (P3 and P4) x)
                               (case_option (Q1 and Q3) (Q2 and Q4) y)
                               (case_option f f' x) (case_option g g' y)"
  apply (case_tac x; case_tac y; clarsimp)
  by (rule equiv_valid_2_guard_imp, rule assms; fastforce)+

lemma vcpu_switch_reads_respects_l:
  notes ev2l_bind = equiv_valid_2_bind_pre[where P=\<top> and P'=\<top> and R'="\<top>\<top>", rotated, simplified]
  shows "reads_respects_l aag l (\<lambda>s. valid_arch_state s) (vcpu_switch vopt)"
  apply (unfold vcpu_switch_def)
  apply (fold vcpu_restore_2_def vcpu_enable_2_def vcpu_disable_2_def)
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (l o pasObjectAbs aag) s = None" in equiv_valid_cases'')
    apply (simp add: cur_vcpu_for_None')
    apply (clarsimp simp: states_equiv_for_def equiv_hyp_def equiv_for_def)
   prefer 2
   apply (wpsimp wp: when_ev vcpu_disable_2_reads_respects_l
                     vcpu_restore_2_reads_respects_l vcpu_enable_2_reads_respects_l gets_ev')
   apply (subgoal_tac "\<forall>t. states_equiv_for_labels aag l s t \<longrightarrow> current_vcpu s = current_vcpu t")
    apply (clarsimp simp: valid_arch_state_def)
   apply (clarsimp simp: states_equiv_for_def equiv_hyp_def equiv_for_def)
   apply (erule_tac x=ptr in allE)+
   apply (clarsimp simp: cur_vcpu_of_def split: option.splits if_splits)
  apply (rule_tac P="\<lambda>_. none_bot (l o pasObjectAbs aag) vopt" in equiv_valid_cases'')
    apply simp
   prefer 2
   apply (rule reads_respects_l_invisible[where P="\<top>", simplified])
     apply (rule modifies_at_mostI)
     apply (wpsimp wp: vcpu_enable_2_equiv_but_for_labels
                       vcpu_disable_2_equiv_but_for_labels
                       vcpu_restore_2_equiv_but_for_labels)
     apply (fastforce simp: cur_vcpu_for_def)
    apply wpsimp
   apply clarsimp
  apply (case_tac vopt; clarsimp simp: equiv_valid_def2)
   apply (clarsimp simp: equiv_valid_2_def)
  apply (rule equiv_valid_2_bind_pre[OF _ gets_any_evrv])
      apply (rule_tac P="\<forall>b. rv \<noteq> Some (a,b)" in gen_asm_ev2_l)
      apply (rule_tac P'="\<forall>b. rv' \<noteq> Some (a,b)" in gen_asm_ev2_r)
      apply (clarsimp simp: split_def)
      apply (rule ev2_case_option)
         apply (rule ev_evrv)
         apply (rule vcpu_restore_2_reads_respects_l)
        apply (subst if_P, clarsimp, blast)
        apply (subst return_bind[where f="\<lambda>_. vcpu_restore_2 _", symmetric],
               rule_tac R'=dc in equiv_valid_2_bind_pre)
             apply (simp only: K_bind_def)
             apply (rule ev_evrv)
             apply (rule vcpu_restore_2_reads_respects_l)
            apply (rule_tac P=\<top> and P'=\<top>
                         in reads_respects_l_2_invisible[OF modifies_at_mostI modifies_at_mostI])
                apply (assumption | wpsimp simp: split_def split_del: if_split)+
       apply (subst if_P, clarsimp, blast)
       apply (subst return_bind[where f="\<lambda>_. vcpu_restore_2 _", symmetric],
              rule_tac R'=dc in equiv_valid_2_bind_pre)
            apply (simp only: K_bind_def)
            apply (rule ev_evrv)
            apply (rule vcpu_restore_2_reads_respects_l)
           apply (rule_tac P=\<top> and P'=\<top>
                        in reads_respects_l_2_invisible[OF modifies_at_mostI modifies_at_mostI])
               apply (assumption | wpsimp simp: split_def split_del: if_split)+
      apply (subst if_P, clarsimp, blast)+
      apply (rule_tac R'=dc in equiv_valid_2_bind_pre)
           apply (simp only: K_bind_def)
           apply (rule ev_evrv)
           apply (rule vcpu_restore_2_reads_respects_l)
          apply (rule_tac P=\<top> and P'=\<top>
                       in reads_respects_l_2_invisible[OF modifies_at_mostI modifies_at_mostI])
              apply (assumption | wpsimp simp: split_def split_del: if_split)+
   apply (auto simp: cur_vcpu_for_def split: option.splits if_splits)
  done

lemma vcpu_switch_reads_respects:
  "reads_respects aag l valid_arch_state (vcpu_switch vopt)"
  apply (rule reads_respects_from_labels)
       apply (rule vcpu_switch_reads_respects_l)
      apply wpsimp+
  done

lemma set_vcpu_reads_respects[wp]:
  "reads_respects aag l \<top> (set_vcpu vr vcpu)"
  unfolding set_vcpu_def
  apply (rule_tac P'="vcpu_at vr" in equiv_valid_guard_necessary)
   apply (rule wp_pre)
    apply (rule hoare_set_object_weaken_pre)
    apply wp
   apply (clarsimp simp: obj_at_def)
  apply (wpsimp wp: set_object_reads_respects)
  done

lemma get_vcpu_reads_respects[wp]:
  "reads_respects aag l (K (aag_can_read aag vr \<or> aag_can_affect aag l vr)) (get_vcpu vr)"
  unfolding get_vcpu_def gets_map_def
  apply (subst gets_apply)
  apply (wpsimp wp: gets_apply_ev)
  apply (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_for_def opt_map_def)
  done

lemma vcpu_update_reads_respects[wp]:
  "reads_respects aag l \<top> (vcpu_update vr f)"
  unfolding vcpu_update_def
  apply (rule wp_pre)
   apply (rule_tac ptr=vr in reads_respects_unit_cases)
     apply wpsimp+
  done

lemma vcpu_read_reg_reads_respects[wp]:
  "reads_respects aag l (K (aag_can_read aag v)) (vcpu_read_reg v reg)"
  unfolding vcpu_read_reg_def
  by wpsimp

lemma vcpu_write_reg_reads_respects[wp]:
  "reads_respects aag l \<top> (vcpu_write_reg v reg val)"
  unfolding vcpu_write_reg_def
  by wpsimp

lemma gets_apply_evrv:
  "equiv_valid_rv_inv I A R (K (\<forall>s t. I s t \<and> A s t \<longrightarrow> R (f s x) (f t x))) (gets_apply f x)"
  apply (simp add: gets_apply_def get_def bind_def return_def)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  done

lemma gets_apply_evrv':
  "\<forall>s t. I s t \<and> A s t \<and> P s \<and> P t \<longrightarrow> R (f s x) (f t x)
   \<Longrightarrow> equiv_valid_rv_inv I A R P (gets_apply f x)"
  apply (simp add: gets_apply_def get_def bind_def return_def)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  done

lemma readVCPUHardwareReg_reads_respects[wp]:
  "reads_respects aag l (\<lambda>s. \<exists>b. cur_vcpu_for (aag_can_read_or_affect aag l) s = Some b \<and> (vcpuRegSavedWhenDisabled reg \<longrightarrow> b))
                        (do_machine_op (readVCPUHardwareReg reg))"
  unfolding readVCPUHardwareReg_def
  apply (rule do_machine_op_reads_respects'')
   apply wp
  apply clarsimp
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def cur_vcpu_for_Some)
  apply (case_tac b; clarsimp simp: hw_vcpu_def)
  apply (drule_tac x=reg in fun_cong, clarsimp)
  done

lemma writeVCPUHardwareReg_reads_respects[wp]:
  "reads_respects aag l \<top> (do_machine_op (writeVCPUHardwareReg reg val))"
  unfolding writeVCPUHardwareReg_def dmo_distr
  apply (wpsimp wp: dmo_mol_reads_respects)
    apply (rule use_spec_ev)
    apply (wpsimp wp: do_machine_op_reads_respects'' modify_ev)
   apply wpsimp
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def)
  apply (case_tac "cur_vcpu_for (aag_can_read aag or aag_can_affect aag l) s"; clarsimp simp: cur_vcpu_for_Some)
  apply (clarsimp simp: hw_vcpu_def split: if_splits)
   apply (intro conjI ext; drule_tac x=r in fun_cong; clarsimp)+
  done

lemma invoke_vcpu_read_register_reads_respects:
  "reads_respects aag l (K (aag_can_read aag v)) (invoke_vcpu_read_register v reg)"
  unfolding invoke_vcpu_read_register_def read_vcpu_register_def gets_def
  apply (subst bind_assoc)
  apply (subst return_bind)
  apply (subst bind_assoc[symmetric])
  apply (subst gets_apply_def[symmetric])
  apply simp
  apply (rule gen_asm_ev)
  apply (rule wp_pre)
   apply (unfold equiv_valid_def2)
   apply (clarsimp simp: bind_assoc)
   apply (rule_tac A=A and B=A and P=\<top> and W="\<lambda>x y. fst x = fst y \<and> (fst x \<longrightarrow> x = y)"
               and Q="\<lambda>rv s. (fst rv \<longrightarrow> Q rv s) \<and> (\<not>fst rv \<longrightarrow> Q' rv s)"
               for A Q Q' in equiv_valid_rv_bind_general)
     apply (wpsimp wp: gets_apply_evrv')
     apply (prop_tac "equiv_for (aag_can_read aag) cur_vcpu_of s t")
      apply (clarsimp simp: reads_equiv_def2 states_equiv_for_def equiv_hyp_def)
     apply (clarsimp simp: equiv_for_def)
     apply (erule_tac x=v in allE)
     apply (auto simp: equiv_for_def cur_vcpu_of_def split: option.splits if_splits)[1]
    apply (case_tac "fst rv"; clarsimp split del: if_split; wpfix)
     apply (subst equiv_valid_def2[symmetric])
     apply wpsimp
    apply (subst equiv_valid_def2[symmetric])
    apply wpsimp
     apply (rule equiv_valid_guard_imp)
      apply wpsimp
     apply clarsimp
    apply wpsimp
   apply wpsimp+
   apply (clarsimp split: option.splits)
  apply simp
  done

lemma invoke_vcpu_write_register_reads_respects:
  "reads_respects aag l (K (aag_can_read aag v)) (invoke_vcpu_write_register v reg val)"
  unfolding invoke_vcpu_write_register_def write_vcpu_register_def gets_def
  apply (subst bind_assoc)
  apply (subst return_bind)
  apply (subst bind_assoc[symmetric])
  apply (subst gets_apply_def[symmetric])
  apply simp
  apply (rule gen_asm_ev)
  apply (rule wp_pre)
   apply (unfold equiv_valid_def2)
   apply (clarsimp simp: bind_assoc)
   apply (rule_tac A=A and B=A and P=\<top> and W="\<lambda>x y. fst x = fst y \<and> (fst x \<longrightarrow> x = y)"
               and Q="\<lambda>rv s. (fst rv \<longrightarrow> Q rv s) \<and> (\<not>fst rv \<longrightarrow> Q' rv s)"
               for A Q Q' in equiv_valid_rv_bind_general)
     apply (wpsimp wp: gets_apply_evrv')
     apply (prop_tac "equiv_for (aag_can_read aag) cur_vcpu_of s t")
      apply (clarsimp simp: reads_equiv_def2 states_equiv_for_def equiv_hyp_def)
     apply (clarsimp simp: equiv_for_def)
     apply (erule_tac x=v in allE)
     apply (auto simp: equiv_for_def cur_vcpu_of_def split: option.splits if_splits)[1]
    apply (case_tac "fst rv"; clarsimp split del: if_split; wpfix)
     apply (subst equiv_valid_def2[symmetric])
     apply wpsimp
    apply (subst equiv_valid_def2[symmetric])
    apply wpsimp+
  done

lemma set_gic_vcpu_ctrl_lr_reads_respects'':
  "reads_respects aag l (\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s = None)
                        (do_machine_op (set_gic_vcpu_ctrl_lr reg val))"
  (is "reads_respects _ _ ?P _")
   unfolding set_gic_vcpu_ctrl_lr_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects)
     apply (rule do_machine_op_reads_respects'')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_def)
    apply wpsimp+
   done

lemma hw_vcpu_lr_update[simp]:
  "hw_vcpu n cv (vcpu_vgic_update (vgic_lr_update (\<lambda>f. f(reg := val))) vst) =
   (if reg < n then map_option (vcpu_vgic_update (vgic_lr_update (\<lambda>f. f(reg := val)))) (hw_vcpu n cv vst)
               else hw_vcpu n cv vst)"
  by (auto split: if_splits option.splits simp: hw_vcpu_def)

lemma set_gic_vcpu_ctrl_lr_reads_respects':
  "reads_respects aag l (\<lambda>s. \<exists>vr b. cur_vcpu_for (aag_can_read_or_affect aag l) s = Some b)
                        (do_machine_op (set_gic_vcpu_ctrl_lr reg val))"
  (is "reads_respects _ _ ?P _")
  unfolding set_gic_vcpu_ctrl_lr_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects)
     apply (rule do_machine_op_reads_respects'')
      apply (wpsimp wp: modify_ev')
    apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_Some)
    apply wpsimp+
   done

lemma set_gic_vcpu_ctrl_lr_reads_respects[wp]:
  "reads_respects aag l \<top>
                        (do_machine_op (set_gic_vcpu_ctrl_lr reg val))"
  (is "reads_respects _ _ ?P _")
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s = None" in equiv_valid_cases'')
    apply (prop_tac "equiv_hyp (aag_can_read_or_affect aag l) s t")
     apply (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)[1]
    apply (auto simp: cur_vcpu_for_None' equiv_hyp_def equiv_for_def)[1]
   apply (wpsimp wp: set_gic_vcpu_ctrl_lr_reads_respects'')
  apply (wpsimp wp: set_gic_vcpu_ctrl_lr_reads_respects')
  done

lemma vgic_update_reads_respects[wp]:
  "reads_respects aag l \<top> (vgic_update vr f)"
  unfolding vgic_update_def by wp

lemma vgic_lr_update_reads_respects[wp]:
  "reads_respects aag l \<top> (vgic_update_lr vr reg irq)"
  unfolding vgic_update_lr_def by wp

lemma invoke_vcpu_inject_irq_reads_respects:
  "reads_respects aag l (\<lambda>s. aag_can_read aag v) (invoke_vcpu_inject_irq v n irq)"
  unfolding invoke_vcpu_inject_irq_def
  apply (subst equiv_valid_def2)
  apply (rule_tac W="\<lambda>cv cv'. (cv \<noteq> None \<and> fst (the cv) = v) = (cv' \<noteq> None \<and> fst (the cv') = v)" in equiv_valid_rv_bind)
    apply (wpsimp wp: gets_evrv'')
    apply (prop_tac "equiv_for (aag_can_read aag) cur_vcpu_of s t")
     apply (clarsimp simp: reads_equiv_def2 states_equiv_for_def equiv_hyp_def)
    apply (clarsimp simp: equiv_for_def)
    apply (erule_tac x=v in allE)
    apply (auto simp: equiv_for_def cur_vcpu_of_def split: option.splits if_splits)[1]
   apply (clarsimp split del: if_split)
   apply (subst equiv_valid_def2[symmetric])
   apply wpsimp+
  done

lemma invoke_vcpu_ack_vppi_reads_respects:
  "reads_respects aag l (K (aag_can_read aag v)) (invoke_vcpu_ack_vppi v vppi)"
  unfolding invoke_vcpu_ack_vppi_def
  by wpsimp

lemma as_user_getRegister_reads_respects:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag l (K (aag_can_read aag thread \<or> aag_can_affect aag l thread)) (as_user thread (getRegister reg))"
   apply (simp add: as_user_def split_def)
   apply (rule gen_asm_ev)
   apply (wp set_object_reads_respects select_f_ev gets_the_ev)
   apply (auto intro: reads_affects_equiv_get_tcb_eq det_getRegister)[1]
  done

lemma arch_thread_set_vcpu_reads_respects[wp]:
  "reads_respects aag l (K (aag_can_read_or_affect aag l t))
                        (arch_thread_set (tcb_vcpu_update f) t)"
  unfolding arch_thread_set_def
  apply (wpsimp wp: set_object_reads_respects)
   apply fastforce
  done

lemma gets_arm_current_vcpu_reads_respects:
  "reads_respects aag l (\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s \<noteq> None)
                        (gets (arm_current_vcpu \<circ> arch_state))"
  apply (wpsimp wp: gets_ev')
  apply (erule disjE)
  apply (prop_tac "equiv_hyp (aag_can_read aag) s t")
   apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)
   apply (fastforce simp: equiv_hyp_def equiv_for_def cur_vcpu_of_def split: if_splits option.splits)
  apply (prop_tac "equiv_hyp (aag_can_affect aag l) s t")
   apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)
   apply (fastforce simp: equiv_hyp_def equiv_for_def cur_vcpu_of_def split: if_splits option.splits)
  done

lemma modify_current_vcpu_None_reads_respects[wp]:
  "reads_respects aag l \<top>
     (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := None\<rparr>\<rparr>))"
  apply (wpsimp wp: modify_ev)
  apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_for_def)
  apply (intro conjI)
  prefer 4
       apply (auto simp: equiv_asids_def equiv_asid_def)[2]
     prefer 2
     prefer 4
     apply (auto simp: equiv_fpu_def equiv_for_def cur_fpu_for_def get_tcb_def)[2]
   apply (clarsimp simp: equiv_hyp_def equiv_for_def cur_vcpu_of_def split: option.split)
   apply (clarsimp simp: equiv_hyp_def equiv_for_def cur_vcpu_of_def split: option.split)
  done

lemma dmo_dsb_reads_respects[wp]:
  "reads_respects aag l \<top> (do_machine_op dsb)"
  unfolding dsb_def
  by (wpsimp wp: dmo_mol_reads_respects)

lemma dmo_isb_reads_respects[wp]:
  "reads_respects aag l \<top> (do_machine_op isb)"
  unfolding isb_def
  by (wpsimp wp: dmo_mol_reads_respects)

lemma dmo_setHCR_reads_respects[wp]:
  "reads_respects aag l \<top> (do_machine_op (setHCR val))"
  unfolding setHCR_def
  by (wpsimp wp: dmo_mol_reads_respects)

lemma dmo_maskInterrupt_reads_respects[wp]:
  "reads_respects aag l \<top> (do_machine_op (maskInterrupt m irq))"
  unfolding maskInterrupt_def
  apply (rule use_spec_ev)
  apply (wpsimp wp: do_machine_op_reads_respects'' modify_ev)
  apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def)
  done

lemma enableFpuEL01_reads_respects'':
  "reads_respects aag l (\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s = None)
                        (do_machine_op enableFpuEL01)"
  (is "reads_respects _ _ ?P _")
   unfolding enableFpuEL01_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects)
     apply (rule do_machine_op_reads_respects'')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_def)
    apply wpsimp+
   done

lemma enableFpuEL01_reads_respects':
  "reads_respects aag l (\<lambda>s. \<exists>vr. cur_vcpu_for (aag_can_read_or_affect aag l) s = Some True)
                        (do_machine_op enableFpuEL01)"
  (is "reads_respects _ _ ?P _")
   unfolding enableFpuEL01_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects)
     apply (rule do_machine_op_reads_respects'')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_Some)
    apply wpsimp+
   done

lemma enableFpuEL01_reads_respects[wp]:
  "reads_respects aag l (\<lambda>s. \<forall>vr b. current_vcpu s = Some (vr,b) \<longrightarrow> b)
                        (do_machine_op enableFpuEL01)"
  (is "reads_respects _ _ ?P _")
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s = None" in equiv_valid_cases'')
    apply (prop_tac "equiv_hyp (aag_can_read_or_affect aag l) s t")
     apply (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)[1]
    apply (auto simp: cur_vcpu_for_None' equiv_hyp_def equiv_for_def)[1]
   apply (wpsimp wp: enableFpuEL01_reads_respects'')
  apply (wpsimp wp: enableFpuEL01_reads_respects')
  done

lemma setSCTLR_reads_respects'':
  "reads_respects aag l (\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s = None)
                        (do_machine_op (setSCTLR val))"
  (is "reads_respects _ _ ?P _")
   unfolding setSCTLR_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects)
     apply (rule do_machine_op_reads_respects'')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_def)
    apply wpsimp+
   done

lemma setSCTLR_reads_respects':
  "reads_respects aag l (\<lambda>s. \<exists>vr. cur_vcpu_for (aag_can_read_or_affect aag l) s = Some True)
                        (do_machine_op (setSCTLR val))"
  (is "reads_respects _ _ ?P _")
   unfolding setSCTLR_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects)
     apply (rule do_machine_op_reads_respects'')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_Some)
    apply wpsimp+
   done

lemma setSCTLR_reads_respects[wp]:
  "reads_respects aag l (\<lambda>s. \<forall>vr b. current_vcpu s = Some (vr,b) \<longrightarrow> b)
                        (do_machine_op (setSCTLR val))"
  (is "reads_respects _ _ ?P _")
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s = None" in equiv_valid_cases'')
    apply (prop_tac "equiv_hyp (aag_can_read_or_affect aag l) s t")
     apply (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)[1]
    apply (auto simp: cur_vcpu_for_None' equiv_hyp_def equiv_for_def)[1]
   apply (wpsimp wp: setSCTLR_reads_respects'')
  apply (wpsimp wp: setSCTLR_reads_respects')
  done

lemma set_gic_vcpu_ctrl_hcr_reads_respects'':
  "reads_respects aag l (\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s = None)
                        (do_machine_op (set_gic_vcpu_ctrl_hcr val))"
  (is "reads_respects _ _ ?P _")
   unfolding set_gic_vcpu_ctrl_hcr_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects)
     apply (rule do_machine_op_reads_respects'')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_def)
    apply wpsimp+
   done

lemma set_gic_vcpu_ctrl_hcr_reads_respects':
  "reads_respects aag l (\<lambda>s. \<exists>vr. cur_vcpu_for (aag_can_read_or_affect aag l) s = Some True)
                        (do_machine_op (set_gic_vcpu_ctrl_hcr val))"
  (is "reads_respects _ _ ?P _")
   unfolding set_gic_vcpu_ctrl_hcr_def dmo_distr
   apply (rule_tac P'="?P" in bind_ev_pre)
      apply (wpsimp wp: dmo_mol_reads_respects)
     apply (rule do_machine_op_reads_respects'')
      apply (wpsimp wp: modify_ev')
     apply (clarsimp simp: equiv_for_def equiv_hyp_state_def equiv_fpu_state_def cur_vcpu_for_Some)
    apply wpsimp+
   done

lemma set_gic_vcpu_ctrl_hcr_reads_respects[wp]:
  "reads_respects aag l (\<lambda>s. \<forall>vr b. current_vcpu s = Some (vr,b) \<longrightarrow> b)
                        (do_machine_op (set_gic_vcpu_ctrl_hcr val))"
  (is "reads_respects _ _ ?P _")
  apply (rule_tac P="\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s = None" in equiv_valid_cases'')
    apply (prop_tac "equiv_hyp (aag_can_read_or_affect aag l) s t")
     apply (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)[1]
    apply (auto simp: cur_vcpu_for_None' equiv_hyp_def equiv_for_def)[1]
   apply (wpsimp wp: set_gic_vcpu_ctrl_hcr_reads_respects'')
  apply (wpsimp wp: set_gic_vcpu_ctrl_hcr_reads_respects')
  done

lemma vcpu_disable_None_reads_respects[wp]:
  "reads_respects aag l (\<lambda>s. \<exists>vr. current_vcpu s = Some (vr,True)) (vcpu_disable None)"
  apply (simp only: vcpu_disable_def fun_app_def bind_assoc_helper vcpu_save_vgic_defs[symmetric] vcpu_save_lrs_helper)
  apply (clarsimp simp: dmo_distr)
  apply wpsimp
  done

lemma vcpu_invalidate_active_reads_respects:
  "reads_respects aag l (\<lambda>s. cur_vcpu_for (aag_can_read_or_affect aag l) s \<noteq> None) vcpu_invalidate_active"
  unfolding vcpu_invalidate_active_def
  apply wp
      apply wpsimp
     apply wpsimp
    apply (wp gets_arm_current_vcpu_reads_respects)
   apply wpsimp
  apply clarsimp
  done

lemma arch_thread_get_tcb_vcpu_reads_respects[wp]:
  "reads_respects aag l (K (aag_can_read aag t)) (arch_thread_get tcb_vcpu t)"
  unfolding arch_thread_get_def
  apply wpsimp
  apply fastforce
  done

lemma gets_comp:
  "do x <- gets f;
      m (g x)
   od =
   do x <- gets (g \<circ> f);
      m x
    od"
  by (simp add: gets_def)

lemma dissociate_vcpu_tcb_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (K (aag_can_read aag t \<and> aag_can_read aag vr))
                              (dissociate_vcpu_tcb vr t)"
  apply (clarsimp simp: dissociate_vcpu_tcb_def as_user_bind)
  apply (subst gets_comp)
  apply (wpsimp wp: as_user_set_register_reads_respects' as_user_getRegister_reads_respects when_ev
                    vcpu_invalidate_active_reads_respects get_vcpu_wp arch_thread_get_wp)
  apply (rule conjI; clarsimp)
  apply (prop_tac "equiv_hyp (aag_can_read aag) sa ta")
   apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def)
  apply (fastforce simp: equiv_hyp_def equiv_for_def cur_vcpu_of_def split: if_splits option.splits)
  done

lemma dissociate_vcpu_tcb_helper:
  "\<lbrace>\<lambda>s. \<exists>vcpu'. vcpus_of s vr = Some vcpu' \<and> P (Some (if v = vr then vcpu'\<lparr>vcpu_tcb := None\<rparr> else vcpu'))\<rbrace>
   dissociate_vcpu_tcb v t
   \<lbrace>\<lambda>_ s. P (vcpus_of s vr)\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  apply (wpsimp wp: get_vcpu_wp hoare_vcg_all_lift arch_thread_get_wp)
  apply (auto elim!: rsubst[where P=P] intro!: ext split: if_splits)
  done

lemma associate_vcpu_tcb_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag and valid_arch_state and K (is_subject aag vr \<and> is_subject aag t)) (associate_vcpu_tcb vr t)"
  unfolding associate_vcpu_tcb_def
  apply (rule_tac P'="\<lambda>s. vcpus_of s vr \<noteq> None" in equiv_valid_guard_necessary)
   apply (clarsimp simp: bind_assoc)
   apply (wpsimp wp: get_vcpu_vcpu_at simp: obj_at_def opt_map_def)
  apply (subst gets_comp)
  apply (wpsimp wp: when_ev vcpu_switch_reads_respects dissociate_vcpu_tcb_reads_respects
                    arch_thread_get_wp get_vcpu_wp dissociate_vcpu_tcb_helper
                    hoare_vcg_imp_lift' hoare_vcg_all_lift)
  apply (intro conjI impI allI; clarsimp?)
      apply (fastforce simp: get_tcb_ko_at dest: associated_vcpu_is_subject)
     apply (fastforce dest: associated_tcb_is_subject)
    apply (clarsimp simp: reads_equiv_def)
   apply (fastforce dest: associated_tcb_is_subject)
  apply (clarsimp simp: reads_equiv_def)
  done

lemma perform_vcpu_invocation_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pas_refined aag and valid_arch_state and valid_vcpu_invocation iv and K (authorised_vcpu_inv aag iv))
                        (perform_vcpu_invocation iv)"
  unfolding perform_vcpu_invocation_def authorised_vcpu_inv_def
  apply (rule gen_asm_ev)
  apply (cases iv; simp)
      apply (wpsimp wp: associate_vcpu_tcb_reads_respects)
     apply (wpsimp wp: invoke_vcpu_inject_irq_reads_respects)
    apply (wpsimp wp: invoke_vcpu_read_register_reads_respects)
   apply (wpsimp wp: invoke_vcpu_write_register_reads_respects)
  apply (wpsimp wp: invoke_vcpu_ack_vppi_reads_respects)
  done

lemma set_vcpu_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_vcpu ptr vcpu
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_vcpu_def
  apply (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre] get_object_wp
              simp: partial_inv_def)+
  apply (fastforce simp: obj_at_def valid_arch_state_def dest: valid_global_arch_objs_pt_at)
  done

lemma vcpu_update_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   vcpu_update vr f
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding vcpu_update_def
  by wpsimp

lemma thread_set_globals_equiv:
  "(\<And>tcb. arch_tcb_context_get (tcb_arch (f tcb)) = arch_tcb_context_get (tcb_arch tcb))
   \<Longrightarrow> \<lbrace>globals_equiv s and valid_arch_state\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding thread_set_def
  apply (wp set_object_globals_equiv)
  apply simp
  apply (intro impI conjI allI)
    apply (fastforce simp: valid_arch_state_def obj_at_def get_tcb_def dest: valid_global_arch_objs_pt_at)+
  done

lemma arch_thread_set_vcpu_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   arch_thread_set (tcb_vcpu_update f) t
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding arch_thread_set_is_thread_set
  by (wpsimp wp: thread_set_globals_equiv simp: arch_tcb_context_get_def)

crunch vcpu_save_reg
  for globals_equiv[wp]: "globals_equiv st"
  (simp: readVCPUHardwareReg_def)

crunch vgic_update_lr
  for globals_equiv[wp]: "globals_equiv st"

lemma vcpu_save_reg_range_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   vcpu_save_reg_range vr from to
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding vcpu_save_reg_range_def
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp_inv)
   apply wpsimp+
  done

lemma dmo_globals_equiv:
  "\<lbrakk> \<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> \<rbrakk>
     \<Longrightarrow> do_machine_op f \<lbrace>globals_equiv st\<rbrace>"
  apply (simp add: do_machine_op_def)
  apply (wp modify_wp | simp add: split_def)+
  apply (clarsimp simp: globals_equiv_def idle_equiv_def)
  apply (erule use_valid, fastforce+)
  done

crunch vcpu_save
  for globals_equiv[wp]: "globals_equiv st"
  (wp: mapM_wp_inv dmo_globals_equiv simp: crunch_simps )

crunch vcpu_restore
  for globals_equiv[wp]: "globals_equiv st"
  (wp: mapM_x_wp_inv mapM_wp_inv dmo_globals_equiv simp: crunch_simps )

crunch vcpu_disable
  for globals_equiv[wp]: "globals_equiv st"
  (wp: mapM_x_wp_inv mapM_wp_inv dmo_globals_equiv simp: crunch_simps )

lemma globals_equiv_arm_current_vcpu_update[simp]:
  "globals_equiv st (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := vcpu'\<rparr>\<rparr>) = globals_equiv st s"
  by (auto simp: globals_equiv_def idle_equiv_def)

crunch vcpu_switch
  for globals_equiv[wp]: "globals_equiv st"
  (wp: mapM_x_wp_inv mapM_wp_inv dmo_globals_equiv simp: crunch_simps )

lemma vcpu_invalidate_active_valid_arch_state[wp]:
  "vcpu_invalidate_active \<lbrace>valid_arch_state\<rbrace>"
  unfolding vcpu_invalidate_active_def
  apply wp
    apply (rule_tac Q'="\<lambda>_. valid_arch_state" in hoare_strengthen_post[rotated])
     apply (clarsimp simp: valid_arch_state_def cur_vcpu_def valid_global_arch_objs_def)
    apply wpsimp+
  done

crunch vcpu_invalidate_active
  for globals_equiv[wp]: "globals_equiv st"

lemma dissociate_vcpu_tcb_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   dissociate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  apply (wpsimp wp: as_user_globals_equiv simp: arch_tcb_context_get_def as_user_bind)
       apply (rule_tac Q'="\<lambda>_ s. arm_current_vcpu (arch_state s) = None" in hoare_post_add)
       apply (clarsimp cong: conj_cong)
       apply (wpsimp wp: get_vcpu_wp arch_thread_get_wp)+
  done

lemma associate_vcpu_tcb_globals_equiv[wp]:
  "\<lbrace>globals_equiv s and invs and ex_nonz_cap_to t\<rbrace>
   associate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding associate_vcpu_tcb_def
  apply (wpsimp)
  apply (wp hoare_drop_imps)
  apply clarsimp
       apply wpsimp
      apply clarsimp
      apply wpsimp
     apply (wp get_vcpu_wp)
       apply (rule_tac Q'="\<lambda>_. globals_equiv s and valid_arch_state" in hoare_post_add)
    apply (clarsimp cong: conj_cong)
    apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift dissociate_vcpu_tcb_vcpus_of)
   apply (wp arch_thread_get_wp)
  apply clarsimp
  apply (case_tac "t = idle_thread sa", clarsimp)
  using idle_no_ex_cap apply fastforce
  apply clarsimp
  apply (case_tac "vcpus_of sa vr"; clarsimp)
  apply (case_tac "vcpu_tcb a"; clarsimp)
  apply (case_tac "aa = idle_thread sa"; clarsimp)
  apply (subgoal_tac "False", clarsimp)
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

crunch invoke_vcpu_inject_irq, invoke_vcpu_read_register, invoke_vcpu_write_register, invoke_vcpu_ack_vppi, perform_smc_invocation
  for globals_equiv[wp]: "globals_equiv s"
  (wp: dmo_globals_equiv)

lemma perform_vcpu_invocation_globals_equiv:
  "\<lbrace>globals_equiv s and invs and valid_vcpu_invocation iv\<rbrace>
   perform_vcpu_invocation iv
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding perform_vcpu_invocation_def valid_vcpu_invocation_def
  by (cases iv; wpsimp)

lemma perform_sgi_invocation_reads_respects:
  "reads_respects aag l \<top>
                  (perform_sgi_invocation api)"
  unfolding perform_sgi_invocation_def sendSGI_def
  by (case_tac api; wpsimp wp: dmo_mol_reads_respects)

lemma perform_smc_invocation_reads_respects:
  "reads_respects aag l \<top> (perform_smc_invocation api)"
  unfolding perform_smc_invocation_def
  by (case_tac api; wpsimp wp: dmo_doSMC_mop_reads_respects)


definition authorised_for_globals_arch_inv ::
  "arch_invocation \<Rightarrow> ('z::state_ext) state \<Rightarrow> bool" where
  "authorised_for_globals_arch_inv ai \<equiv>
    case ai of InvokePageTable oper \<Rightarrow> authorised_for_globals_page_table_inv oper
             | InvokePage oper \<Rightarrow> authorised_for_globals_page_inv oper
             | _ \<Rightarrow> \<top>"

lemma arch_perform_invocation_reads_respects_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_g aag l (ct_active and authorised_arch_inv aag ai and valid_arch_inv ai
                                           and authorised_for_globals_arch_inv ai and invs
                                           and pas_refined aag and is_subject aag \<circ> cur_thread)
                          (arch_perform_invocation ai)"
  unfolding arch_perform_invocation_def fun_app_def
  apply (case_tac ai; clarsimp)
  by (wpsimp wp: doesnt_touch_globalsI
                 reads_respects_g[OF perform_page_table_invocation_reads_respects]
                 reads_respects_g[OF perform_page_invocation_reads_respects]
                 reads_respects_g[OF perform_asid_control_invocation_reads_respects]
                 reads_respects_g[OF perform_vspace_invocation_reads_respects]
                 reads_respects_g[OF perform_vcpu_invocation_reads_respects]
                 reads_respects_g[OF perform_sgi_invocation_reads_respects]
                 reads_respects_g[OF perform_smc_invocation_reads_respects]
                 perform_asid_pool_invocation_reads_respects_g
                 perform_page_table_invocation_globals_equiv
                 perform_page_invocation_globals_equiv
                 perform_asid_control_invocation_globals_equiv
                 perform_asid_pool_invocation_globals_equiv
                 perform_vcpu_invocation_globals_equiv
                 perform_sgi_invocation_globals_equiv
           simp: authorised_arch_inv_def valid_arch_inv_def authorised_for_globals_arch_inv_def
                 invs_psp_aligned invs_valid_objs invs_vspace_objs invs_valid_asid_table | simp)+

lemma arch_perform_invocation_globals_equiv:
  "\<lbrace>globals_equiv s and invs and ct_active and valid_arch_inv ai
                    and authorised_for_globals_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding arch_perform_invocation_def
  apply (wpsimp wp: perform_page_table_invocation_globals_equiv
                    perform_page_invocation_globals_equiv
                    perform_asid_control_invocation_globals_equiv
                    perform_asid_pool_invocation_globals_equiv
                    perform_vcpu_invocation_globals_equiv)+
  apply (auto simp: authorised_for_globals_arch_inv_def invs_def valid_state_def valid_arch_inv_def)
  done

crunch arch_post_cap_deletion
  for valid_global_objs[wp]: "valid_global_objs"

(* generalises auth_ipc_buffers_mem_Write *)
lemma auth_ipc_buffers_mem_Write':
  "\<lbrakk> x \<in> auth_ipc_buffers s thread; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> (pasObjectAbs aag thread, Write, pasObjectAbs aag x) \<in> pasPolicy aag"
  apply (clarsimp simp add: auth_ipc_buffers_member_def)
  apply (drule (1) cap_auth_caps_of_state)
  apply simp
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        vspace_cap_rights_to_auth_def vm_read_write_def
                 split: if_split_asm)
   apply (auto dest: ipcframe_subset_page)
  done

end

hide_fact as_user_globals_equiv

context begin interpretation Arch .

requalify_consts
  authorised_for_globals_arch_inv

requalify_facts
  arch_post_cap_deletion_valid_global_objs
  auth_ipc_buffers_mem_Write'
  thread_set_globals_equiv
  arch_post_modify_registers_cur_domain
  arch_post_modify_registers_cur_thread
  length_msg_lt_msg_max
  set_mrs_globals_equiv
  arch_perform_invocation_globals_equiv
  as_user_globals_equiv
  prepare_thread_delete_st_tcb_at_halted
  make_arch_fault_msg_inv
  check_valid_ipc_buffer_inv
  arch_tcb_update_aux2
  arch_perform_invocation_reads_respects_g

declare
  arch_post_cap_deletion_valid_global_objs[wp]
  arch_post_modify_registers_cur_domain[wp]
  arch_post_modify_registers_cur_thread[wp]
  prepare_thread_delete_st_tcb_at_halted[wp]

end

declare as_user_globals_equiv[wp]

end
