(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchArch_IF
imports Arch_IF
begin

context Arch begin global_naming RISCV64

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

crunch arch_switch_to_idle_thread, arch_switch_to_thread
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s :: det_state. P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp crunch_wps whenE_wp
   simp: machine_op_lift_def setVSpaceRoot_def
         machine_rest_lift_def crunch_simps storeWord_def)

crunch arch_invoke_irq_handler
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp simp: maskInterrupt_def plic_complete_claim_def)

crunch arch_perform_invocation
  for irq_state_of_state[wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp simp: cache_machine_op_defs
   wp: crunch_wps simp: crunch_simps ignore: ignore_failure)

crunch arch_finalise_cap, prepare_thread_delete
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s :: det_state. P (irq_state_of_state s)"
  (wp: modify_wp crunch_wps dmo_wp
   simp: crunch_simps hwASIDFlush_def)

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
  apply (simp add: store_word_offs_def)
  apply (rule equiv_valid_get_assert)
  apply (simp add: storeWord_def)
  apply (simp add: do_machine_op_bind)
  apply wp
     apply (rule use_spec_ev)
     apply (rule do_machine_op_spec_reads_respects)
      apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad)
      apply (fastforce intro: equiv_forI elim: equiv_forE simp: upto.simps comp_def)
     apply (rule use_spec_ev do_machine_op_spec_reads_respects assert_ev2
            | simp add: spec_equiv_valid_def | wp modify_wp)+
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

lemma set_cap_globals_equiv''[Arch_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
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

declare arch_prepare_set_domain_inv[Arch_IF_assms]
declare arch_prepare_next_domain_inv[Arch_IF_assms]

end


requalify_facts
  RISCV64.set_simple_ko_globals_equiv
  RISCV64.retype_region_irq_state_of_state
  RISCV64.arch_perform_invocation_irq_state_of_state

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


context Arch begin global_naming RISCV64

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
                            (\<lambda>s. Some a = riscv_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                                 is_subject_asid aag asid \<and> asid \<noteq> 0)
                            (get_asid_pool a)"
  unfolding gets_map_def assert_opt_def2
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule_tac R'="\<lambda>rv rv'. \<forall>p p'. rv a = Some p \<and> rv' a = Some p'
                                       \<longrightarrow> p (asid_low_bits_of asid) = p' (asid_low_bits_of asid)"
               and P="\<lambda>s. Some a = riscv_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                          is_subject_asid aag asid \<and> asid \<noteq> 0"
               and P'="\<lambda>s. Some a = riscv_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
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

lemma requiv_riscv_asid_table_asid_high_bits_of_asid_eq:
  "\<lbrakk> is_subject_asid aag asid; reads_equiv aag s t; asid \<noteq> 0 \<rbrakk>
     \<Longrightarrow> riscv_asid_table (arch_state s) (asid_high_bits_of asid) =
         riscv_asid_table (arch_state t) (asid_high_bits_of asid)"
  apply (erule reads_equivE)
  apply (fastforce simp: equiv_asids_def equiv_asid_def intro: aag_can_read_own_asids)
  done

lemma set_vm_root_states_equiv_for[wp]:
  "set_vm_root thread \<lbrace>states_equiv_for P Q R S st\<rbrace>"
  unfolding set_vm_root_def catch_def fun_app_def
  by (wpsimp wp: do_machine_op_mol_states_equiv_for
                 hoare_vcg_all_lift whenE_wp hoare_drop_imps
           simp: setVSpaceRoot_def dmo_bind_valid if_apply_def2)+

lemma find_vspace_for_asid_reads_respects:
   "reads_respects aag l (K (asid \<noteq> 0 \<and> aag_can_read_asid aag asid)) (find_vspace_for_asid asid)"
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
  apply (fastforce simp: vspace_for_asid_def pool_for_asid_def vspace_for_pool_def
                         opt_map_def obind_def obj_at_def equiv_asid_def
                  split: option.splits)
  done

lemma ptes_of_reads_equiv:
  "\<lbrakk> is_subject aag (table_base ptr); reads_equiv aag s t \<rbrakk>
     \<Longrightarrow> ptes_of s ptr = ptes_of t ptr"
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
  apply (subgoal_tac "ptes_of s (pt_slot_offset level pt vptr) =
                      ptes_of t (pt_slot_offset level pt vptr)")
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
  unfolding unmap_page_table_def fun_app_def
  apply (rule gen_asm_ev)
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_mol_reads_respects store_pte_reads_respects get_pte_rev
             pt_lookup_from_level_reads_respects pt_lookup_from_level_is_subject
             find_vspace_for_asid_wp find_vspace_for_asid_reads_respects hoare_vcg_all_liftE_R
          | wpc | simp add: sfence_def | wp (once) hoare_drop_imps)+
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
          | wpc | simp add: sfence_def)+
  apply (case_tac pti; clarsimp simp: authorised_page_table_inv_def)
  apply (clarsimp simp: valid_pti_def)
  apply (frule cte_wp_valid_cap)
   apply fastforce
  apply (clarsimp simp:  is_PageTableCap_def valid_cap_def wellformed_mapdata_def)
  done

lemma unmap_page_reads_respects:
  "reads_respects aag l
     (pas_refined aag and pspace_aligned and valid_vspace_objs and valid_asid_table
                      and K (asid \<noteq> 0 \<and> is_subject_asid aag asid \<and> vptr \<in> user_region))
     (unmap_page pgsz asid vptr pptr)"
  unfolding unmap_page_def catch_def fun_app_def
  supply gets_the_ev[wp del]
  apply (simp add: unmap_page_def swp_def cong: vmpage_size.case_cong)
  apply (simp add: unlessE_def gets_the_def)
  apply (wp gets_ev' dmo_mol_reads_respects get_pte_rev throw_on_false_reads_respects
            find_vspace_for_asid_reads_respects store_pte_reads_respects[simplified]
         | wpc | wp (once) hoare_drop_imps | simp add: sfence_def is_aligned_mask[symmetric])+
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

lemma perform_page_invocation_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects aag l (pas_refined aag and authorised_page_inv aag pgi and valid_page_inv pgi
                                           and valid_vspace_objs and valid_asid_table
                                           and pspace_aligned and is_subject aag \<circ> cur_thread)
                    (perform_page_invocation pgi)"
  unfolding perform_page_invocation_def fun_app_def when_def perform_pg_inv_map_def
            perform_pg_inv_unmap_def perform_pg_inv_get_addr_def
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_mol_reads_respects mapM_x_ev'' store_pte_reads_respects set_cap_reads_respects
             mapM_ev'' store_pte_reads_respects unmap_page_reads_respects  dmo_mol_2_reads_respects
             get_cap_rev set_mrs_reads_respects set_message_info_reads_respects
          | simp add: sfence_def
          | wpc | wp (once) hoare_drop_imps[where Q'="\<lambda>r s. r"])+
  apply (clarsimp simp: authorised_page_inv_def valid_page_inv_def)
  apply (auto simp: cte_wp_at_caps_of_state authorised_slots_def cap_links_asid_slot_def
                    label_owns_asid_slot_def valid_arch_cap_def wellformed_mapdata_def
             dest!: clas_caps_of_state pas_refined_Control)+
  done

lemma equiv_asids_riscv_asid_table_update:
  "\<lbrakk> equiv_asids R s t; kheap s pool_ptr = kheap t pool_ptr \<rbrakk>
     \<Longrightarrow> equiv_asids R
           (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (asid_table s)
                                                             (asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)
           (t\<lparr>arch_state := arch_state t\<lparr>riscv_asid_table := (asid_table t)
                                                             (asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)"
  by (clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap opt_map_def)

lemma riscv_asid_table_update_reads_respects:
  "reads_respects aag l (K (is_subject aag pool_ptr))
     (do r \<leftarrow> gets (riscv_asid_table \<circ> arch_state);
         modify (\<lambda>s. s\<lparr>arch_state :=
                       arch_state s\<lparr>riscv_asid_table := r(asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)
      od)"
  apply (simp add: equiv_valid_def2)
  apply (rule_tac W="\<top>\<top>"
              and Q="\<lambda>rv s. is_subject aag pool_ptr \<and> rv = riscv_asid_table (arch_state s)"
               in equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
     apply wpsimp+
   apply (rule modify_ev2)
   apply clarsimp
   apply (drule (1) is_subject_kheap_eq[rotated])
   apply (fastforce simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_for_def
                  intro!: equiv_asids_riscv_asid_table_update)
  apply wpsimp
  done

lemma perform_asid_control_invocation_reads_respects:
  notes K_bind_ev[wp del]
  shows "reads_respects aag l (K (authorised_asid_control_inv aag aci))
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
     apply (rule_tac P'=\<top> in bind_ev)
       apply (rule K_bind_ev)
       apply (rule bind_ev)
         apply (rule bind_ev)
           apply (rule return_ev)
          apply (rule K_bind_ev)
          apply simp
          apply (rule riscv_asid_table_update_reads_respects)
         apply (wp cap_insert_reads_respects retype_region_reads_respects
                   set_cap_reads_respects delete_objects_reads_respects get_cap_rev
                | simp add: authorised_asid_control_inv_def)+
  apply (auto dest!: is_aligned_no_overflow)
  done

lemma set_asid_pool_reads_respects:
  "reads_respects aag l (K (is_subject aag ptr)) (set_asid_pool ptr pool)"
  unfolding set_asid_pool_def
  by (wpsimp wp: set_object_reads_respects get_asid_pool_rev)

lemma copy_global_mappings_valid_arch_state:
  "\<lbrace>valid_arch_state and valid_global_vspace_mappings and pspace_aligned
                     and (\<lambda>s. x \<notin> global_refs s \<and> is_aligned x pt_bits)\<rbrace>
   copy_global_mappings x
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding copy_global_mappings_def including classic_wp_pre
  apply simp
  apply wp
   apply (rule_tac Q'="\<lambda>_. valid_arch_state and valid_global_vspace_mappings and pspace_aligned
                                           and (\<lambda>s. x \<notin> global_refs s \<and> is_aligned x pt_bits)"
                in hoare_strengthen_post)
    apply (wp mapM_x_wp[OF _ subset_refl]
              store_pte_valid_arch_state_unreachable
              store_pte_valid_global_vspace_mappings)
    apply (simp only: pt_index_def)
    apply (subst table_base_offset_id)
      apply clarsimp
     apply (clarsimp simp: pte_bits_def word_size_bits_def pt_bits_def
                           table_size_def ptTranslationBits_def mask_def)
     apply (word_bitwise, fastforce)
    apply clarsimp
    apply (simp_all)
  apply (clarsimp simp: valid_arch_state_def)
  apply (subst (asm) table_base_plus; simp add: mask_def)
  done

lemma set_asid_pool_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_asid_pool ptr pool
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre] simp: a_type_def)
  apply (fastforce simp: valid_arch_state_def obj_at_def dest: valid_global_arch_objs_pt_at)
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
                     copy_global_mappings_reads_respects_g copy_global_mappings_valid_arch_state
                     set_cap_reads_respects_g get_cap_reads_respects_g
          | strengthen valid_arch_state_global_arch_objs
          | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: invs_arch_state invs_valid_global_objs invs_psp_aligned
                        invs_valid_global_vspace_mappings authorised_asid_pool_inv_def
                  cong: conj_cong)
  apply (frule (1) caps_of_state_valid)
  apply (clarsimp simp: is_ArchObjectCap_def is_PageTableCap_def
                        valid_cap_def cap_aligned_def pt_bits_def aag_cap_auth_def
                        cap_auth_conferred_def arch_cap_auth_conferred_def)
  apply (frule riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
  apply (fastforce dest: pas_refined_Control cap_not_in_valid_global_refs)
  done

lemma equiv_asids_riscv_asid_table_delete:
  "equiv_asids R s t
   \<Longrightarrow> equiv_asids R
         (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of asid then None
                                                               else riscv_asid_table (arch_state s) a\<rparr>\<rparr>)
         (t\<lparr>arch_state := arch_state t\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of asid then None
                                                               else riscv_asid_table (arch_state t) a\<rparr>\<rparr>)"
  by (clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)

lemma riscv_asid_table_delete_ev2:
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) \<top>\<top>
     (\<lambda>s. rv = riscv_asid_table (arch_state s)) (\<lambda>s. rv' = riscv_asid_table (arch_state s))
     (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                     then None
                                                                     else rv a\<rparr>\<rparr>))
     (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                     then None
                                                                     else rv' a\<rparr>\<rparr>))"
  apply (rule modify_ev2)
  (* slow 15s *)
  by (auto simp: reads_equiv_def2 affects_equiv_def2
         intro!: states_equiv_forI equiv_forI equiv_asids_riscv_asid_table_delete
          elim!: states_equiv_forE equiv_forE
           elim: is_subject_kheap_eq[simplified reads_equiv_def2 states_equiv_for_def, rotated])


lemma requiv_riscv_asid_table_asid_high_bits_of_asid_eq':
  "\<lbrakk> (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base
              \<longrightarrow> is_subject_asid aag asid'); reads_equiv aag s t \<rbrakk>
     \<Longrightarrow> riscv_asid_table (arch_state s) (asid_high_bits_of base) =
         riscv_asid_table (arch_state t) (asid_high_bits_of base)"
  apply (insert asid_high_bits_0_eq_1)
  apply (case_tac "base = 0")
   apply (subgoal_tac "is_subject_asid aag 1")
    apply simp
    apply (rule requiv_riscv_asid_table_asid_high_bits_of_asid_eq[where aag=aag])
      apply (erule_tac x=1 in allE)
      apply simp+
  apply (rule requiv_riscv_asid_table_asid_high_bits_of_asid_eq[where aag=aag])
    apply (erule_tac x=base in allE)
    apply simp+
  done

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
                 and Q="\<lambda>rv s. rv = riscv_asid_table (arch_state s) \<and>
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
                apply (rule equiv_valid_2_unobservable)
                           apply (wp set_vm_root_states_equiv_for)+
               apply (rule riscv_asid_table_delete_ev2)
              apply (wp)+
            apply (rule equiv_valid_2_unobservable)
  by (wp mapM_wp' return_ev2
      | rule conjI | drule (1) requiv_riscv_asid_table_asid_high_bits_of_asid_eq'
      | clarsimp | simp add: equiv_valid_2_def)+

lemma set_asid_pool_state_equal_except_kheap:
  "((), s') \<in> fst (set_asid_pool ptr pool s)
   \<Longrightarrow> states_equal_except_kheap_asid s s' \<and>
       (\<forall>p. p \<noteq> ptr \<longrightarrow> kheap s p = kheap s' p) \<and>
       asid_pools_of s' ptr = Some pool \<and>
       (\<forall>asid. asid \<noteq> 0
               \<longrightarrow> riscv_asid_table (arch_state s) (asid_high_bits_of asid) =
                   riscv_asid_table (arch_state s') (asid_high_bits_of asid) \<and>
                   (\<forall>pool_ptr. riscv_asid_table (arch_state s) (asid_high_bits_of asid) =
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
     (\<lambda>s. riscv_asid_table (arch_state s) (asid_high_bits_of asid) = Some a \<and>
          asid_pools_of s a = Some pool \<and> asid \<noteq> 0 \<and> is_subject_asid aag asid)
     (\<lambda>s. riscv_asid_table (arch_state s) (asid_high_bits_of asid) = Some a \<and>
          asid_pools_of s a = Some pool' \<and> asid \<noteq> 0 \<and> is_subject_asid aag asid)
     (set_asid_pool a (pool(asid_low_bits_of asid := None)))
     (set_asid_pool a (pool'(asid_low_bits_of asid := None)))"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (frule_tac s'=b in set_asid_pool_state_equal_except_kheap)
  apply (frule_tac s'=ba in set_asid_pool_state_equal_except_kheap)
  apply (clarsimp simp: states_equal_except_kheap_asid_def)
  apply (rule conjI)
   apply (clarsimp simp: states_equiv_for_def reads_equiv_def equiv_for_def | rule conjI)+
    apply (case_tac "x=a")
     apply (clarsimp simp: opt_map_def split: option.splits)
    apply (fastforce)
   apply (clarsimp simp: equiv_asids_def equiv_asid_def | rule conjI)+
    apply (case_tac "pool_ptr = a")
     apply (clarsimp)
     apply (erule_tac x="pasASIDAbs aag asid" in ballE)
      apply (clarsimp)
      apply (erule_tac x=asid in allE)+
      apply (clarsimp)
     apply (drule aag_can_read_own_asids, simp)
    apply (erule_tac x="pasASIDAbs aag asida" in ballE)
     apply (clarsimp)
     apply (erule_tac x=asida in allE)+
     apply (clarsimp)
    apply (clarsimp)
   apply (clarsimp)
   apply (case_tac "pool_ptr=a")
    apply (erule_tac x="pasASIDAbs aag asida" in ballE; clarsimp)
   apply (clarsimp simp: opt_map_def split: option.splits)
  apply (clarsimp simp: affects_equiv_def equiv_for_def states_equiv_for_def | rule conjI)+
   apply (case_tac "x=a")
    apply (clarsimp simp: opt_map_def split: option.splits)
   apply (fastforce)
  apply (clarsimp simp: equiv_asids_def equiv_asid_def | rule conjI)+
   apply (case_tac "pool_ptr=a")
    apply (clarsimp simp: opt_map_def split: option.splits)
    apply (erule_tac x=asid in allE)+
    apply (clarsimp simp: asid_pool_at_kheap)
   apply (erule_tac x=asida in allE)+
   apply (clarsimp)
  apply (clarsimp)
  apply (case_tac "pool_ptr=a")
   apply (clarsimp simp: opt_map_def split: option.splits)
  apply (clarsimp simp: opt_map_def split: option.splits)
  done

lemma delete_asid_reads_respects:
  "reads_respects aag l (K (asid \<noteq> 0 \<and> is_subject_asid aag asid)) (delete_asid asid pt)"
  unfolding delete_asid_def
  apply (subst equiv_valid_def2)
  apply (rule_tac W="\<top>\<top>" and Q="\<lambda>rv s. rv = riscv_asid_table (arch_state s) \<and>
                                        is_subject_asid aag asid \<and> asid \<noteq> 0" in equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
     apply (wp, simp)
   apply (case_tac "rv (asid_high_bits_of asid) = rv' (asid_high_bits_of asid)")
    apply (simp)
    apply (case_tac "rv' (asid_high_bits_of asid)")
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
                apply (subst equiv_valid_def2[symmetric])
                apply (rule reads_respects_unobservable_unit_return)
                     apply (wp set_vm_root_states_equiv_for)+
               apply (rule set_asid_pool_delete_ev2)
              apply (wp)+
            apply (rule equiv_valid_2_unobservable)
                       apply (wpsimp wp: do_machine_op_mol_states_equiv_for simp: hwASIDFlush_def)+
         apply (clarsimp | rule return_ev2)+
        apply (rule equiv_valid_2_guard_imp)
          apply (wp get_asid_pool_revrv)
         apply (simp)+
       apply (wp)+
     apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)+
   apply (clarsimp simp: equiv_valid_2_def reads_equiv_def
                         equiv_asids_def equiv_asid_def states_equiv_for_def)
   apply (erule_tac x="pasASIDAbs aag asid" in ballE)
    apply (clarsimp)
   apply (drule aag_can_read_own_asids)
   apply wpsimp+
  done

lemma globals_equiv_arm_asid_table_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>riscv_asid_table := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma set_vm_root_globals_equiv[wp]:
  "set_vm_root tcb \<lbrace>globals_equiv s\<rbrace>"
  by (wpsimp wp: dmo_mol_globals_equiv hoare_vcg_all_lift hoare_drop_imps
           simp: set_vm_root_def setVSpaceRoot_def)

lemma delete_asid_pool_globals_equiv[wp]:
  "delete_asid_pool base ptr \<lbrace>globals_equiv s\<rbrace>"
  unfolding delete_asid_pool_def
  by (wpsimp wp: set_vm_root_globals_equiv mapM_wp[OF _ subset_refl] modify_wp)

lemma vs_lookup_slot_not_global:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, pte); level \<le> max_pt_level;
     pte_refs_of s pte = Some pt; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> pt \<notin> global_refs s"
  apply (prop_tac "vs_lookup_target level asid vref s = Some (level, pt)")
   apply (clarsimp simp: vs_lookup_target_def obind_def split: if_splits)
  apply (erule (2) vs_lookup_target_not_global)
  done

lemma unmap_page_table_globals_equiv:
  "\<lbrace>invs and globals_equiv st and K (vaddr \<in> user_region)\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. globals_equiv st\<rbrace>"
  unfolding unmap_page_table_def
  apply (wp store_pte_globals_equiv pt_lookup_from_level_wrp | wpc | simp add: sfence_def)+
  apply clarsimp
  apply (rule_tac x=asid in exI)
  apply clarsimp
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some valid_arch_state_asid_table)
  apply (drule vs_lookup_slot_table_base; clarsimp)
  apply (drule reachable_page_table_not_global, clarsimp+)
  apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
  done

lemma unmap_page_table_valid_arch_state:
  "\<lbrace>invs and valid_arch_state and K (vaddr \<in> user_region)\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding unmap_page_table_def
  apply (wpsimp wp: store_pte_valid_arch_state_unreachable pt_lookup_from_level_wrp simp: sfence_def)
  apply (rule_tac x=asid in exI)
  apply clarsimp
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some valid_arch_state_asid_table)
  apply (drule vs_lookup_slot_table_base; clarsimp)
  apply (drule reachable_page_table_not_global, clarsimp+)
  done

lemma mapM_x_swp_store_pte_globals_equiv:
  "\<lbrace>globals_equiv s and pspace_aligned and valid_arch_state and valid_global_vspace_mappings
                    and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s)\<rbrace>
   mapM_x (swp store_pte pte) slots
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (rule_tac Q'="\<lambda>_. pspace_aligned and globals_equiv s and valid_arch_state
                                        and valid_global_vspace_mappings
                                        and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s)"
               in hoare_strengthen_post)
   apply (wp mapM_x_wp' store_pte_valid_arch_state_unreachable
             store_pte_valid_global_vspace_mappings store_pte_globals_equiv | simp)+
    apply (clarsimp simp: valid_arch_state_def)
    apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
   apply auto
  done

lemma mapM_x_swp_store_pte_valid_ko_at_arch[wp]:
  "\<lbrace>pspace_aligned and valid_arch_state and valid_global_vspace_mappings
                   and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s)\<rbrace>
   mapM_x (swp store_pte A) slots
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (rule_tac Q'="\<lambda>_. pspace_aligned and valid_arch_state and valid_global_vspace_mappings
                                        and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s)"
               in hoare_strengthen_post)
   apply (wp mapM_x_wp' store_pte_valid_arch_state_unreachable
             store_pte_valid_global_vspace_mappings store_pte_globals_equiv | simp)+
    apply (clarsimp simp: valid_arch_state_def)
   apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
  apply auto
  done


definition authorised_for_globals_page_table_inv ::
  "page_table_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow> bool" where
  "authorised_for_globals_page_table_inv pti \<equiv> \<lambda>s.
     case pti of PageTableMap cap ptr pde p \<Rightarrow> p && ~~ mask pt_bits \<noteq> riscv_global_pt (arch_state s)
                                        | _ \<Rightarrow> True"


lemma perform_pt_inv_map_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and (\<lambda>s. table_base x14 \<noteq> global_pt s)\<rbrace>
   perform_pt_inv_map x11 x12 x13 x14
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pt_inv_map_def
  by (wpsimp wp: store_pte_globals_equiv set_cap_globals_equiv'' simp: sfence_def)

lemma perform_pt_inv_unmap_globals_equiv:
  "\<lbrace>invs and globals_equiv st and cte_wp_at ((=) (ArchObjectCap cap)) ct_slot\<rbrace>
   perform_pt_inv_unmap cap ct_slot
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pt_inv_unmap_def
  apply (wpsimp wp: set_cap_globals_equiv'' mapM_x_swp_store_pte_globals_equiv)
     apply (strengthen invs_imps invs_valid_global_vspace_mappings)
     apply (clarsimp cong: conj_cong)
     apply (wpsimp wp: unmap_page_table_globals_equiv unmap_page_table_invs)
    apply wpsimp+
  apply auto
   apply (drule cte_wp_valid_cap, fastforce)
   apply (clarsimp simp: is_PageTableCap_def valid_cap_def valid_arch_cap_def wellformed_mapdata_def)
  apply (frule cte_wp_valid_cap, fastforce)
  apply (clarsimp simp: is_PageTableCap_def valid_cap_def valid_arch_cap_def wellformed_mapdata_def)
  apply (prop_tac "table_base x = acap_obj cap")
   apply (prop_tac "is_aligned x41 pt_bits")
    apply (fastforce dest: is_aligned_pt simp: valid_arch_cap_def)
   apply (simp only: is_aligned_neg_mask_eq')
   apply (clarsimp simp: add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (drule neg_mask_mono_le[where n=pt_bits])
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
  apply (wpsimp wp: store_pte_globals_equiv set_cap_globals_equiv''
                    perform_pt_inv_map_globals_equiv
                    perform_pt_inv_unmap_globals_equiv)
  apply (case_tac pti; clarsimp simp: authorised_for_globals_page_table_inv_def valid_pti_def)
  done

lemma mapM_swp_store_pte_globals_equiv:
  "\<lbrace>globals_equiv s and pspace_aligned and valid_arch_state and valid_global_vspace_mappings
                    and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s)\<rbrace>
   mapM (swp store_pte pte) slots
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (rule_tac Q'="\<lambda>_. pspace_aligned and globals_equiv s and valid_arch_state
                                        and valid_global_vspace_mappings
                                        and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s)"
               in hoare_strengthen_post)
   apply (wp mapM_wp' store_pte_valid_arch_state_unreachable
             store_pte_valid_global_vspace_mappings store_pte_globals_equiv | simp)+
    apply (clarsimp simp: valid_arch_state_def)
    apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
   apply auto
  done

lemma mapM_swp_store_pte_valid_ko_at_arch[wp]:
  "\<lbrace>globals_equiv s and pspace_aligned and valid_arch_state and valid_global_vspace_mappings
                    and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s)\<rbrace>
   mapM (swp store_pte pte) slots
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (rule_tac Q'="\<lambda>_. pspace_aligned and globals_equiv s and valid_arch_state
                                        and valid_global_vspace_mappings
                                        and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s)"
               in hoare_strengthen_post)
   apply (wp mapM_wp' store_pte_valid_arch_state_unreachable
             store_pte_valid_global_vspace_mappings store_pte_globals_equiv | simp)+
    apply (clarsimp simp: valid_arch_state_def)
    apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
   apply auto
  done

lemma unmap_page_globals_equiv:
  "\<lbrace>globals_equiv st and invs and K (vptr \<in> user_region)\<rbrace>
   unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding unmap_page_def including no_pre
  apply (induct pgsz)
    apply (wpsimp wp: store_pte_globals_equiv | simp add: sfence_def)+
    apply (rule hoare_weaken_preE[OF find_vspace_for_asid_wp])
    apply clarsimp
    apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
    apply (drule vs_lookup_slot_table_base; clarsimp?)
    apply (drule reachable_page_table_not_global; clarsimp?)
    apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
   apply (rule hoare_pre)
    apply (wpsimp wp: store_pte_globals_equiv mapM_swp_store_pte_globals_equiv hoare_drop_imps
           | simp add: sfence_def)+
   apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
   apply (drule vs_lookup_slot_level)
   apply (case_tac "x = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some valid_arch_state_asid_table)
   apply (drule vs_lookup_slot_table_base; clarsimp?)
   apply (drule reachable_page_table_not_global; clarsimp?)
   apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
  apply (wpsimp wp: store_pte_globals_equiv | simp add: sfence_def)+
  apply (rule hoare_weaken_preE[OF find_vspace_for_asid_wp])
  apply clarsimp
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
  apply (drule vs_lookup_slot_level)
  apply (case_tac "x = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some valid_arch_state_asid_table)
  apply (drule vs_lookup_slot_table_base; clarsimp?)
  apply (drule reachable_page_table_not_global; clarsimp?)
  apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
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

lemma unmap_page_valid_arch_state:
  "\<lbrace>invs and K (vptr \<in> user_region)\<rbrace>
   unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding unmap_page_def
  apply (wpsimp wp: store_pte_valid_arch_state_unreachable)
  apply (frule invs_arch_state)
  apply (frule invs_valid_global_vspace_mappings)
  apply clarsimp
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
  apply (drule vs_lookup_slot_level)
  apply (case_tac "x = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some valid_arch_state_asid_table)
  apply (drule vs_lookup_slot_table_base; clarsimp?)
  apply (drule reachable_page_table_not_global; clarsimp?)
  done

lemma perform_pg_inv_unmap_globals_equiv:
  "\<lbrace>invs and globals_equiv st and cte_wp_at ((=) (ArchObjectCap cap)) ct_slot\<rbrace>
   perform_pg_inv_unmap cap ct_slot
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pg_inv_unmap_def
  apply (rule hoare_weaken_pre)
   apply (wp mapM_swp_store_pte_globals_equiv hoare_vcg_all_lift mapM_x_swp_store_pte_globals_equiv
             set_cap_globals_equiv'' unmap_page_globals_equiv store_pte_globals_equiv
             store_pte_globals_equiv hoare_weak_lift_imp set_message_info_globals_equiv
             unmap_page_valid_arch_state perform_pg_inv_get_addr_globals_equiv
          | wpc | simp add: do_machine_op_bind sfence_def)+
  apply (clarsimp simp: acap_map_data_def)
  apply (intro conjI; clarsimp)
  apply (clarsimp split: arch_cap.splits)
  apply (drule cte_wp_valid_cap, fastforce)
  apply (clarsimp simp:  valid_cap_def valid_arch_cap_def wellformed_mapdata_def)
  done

lemma perform_pg_inv_map_globals_equiv:
  "\<lbrace>invs and globals_equiv st and (\<lambda>s. table_base slot \<noteq> global_pt s)\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_pg_inv_map_def
  by (wp mapM_swp_store_pte_globals_equiv hoare_vcg_all_lift mapM_x_swp_store_pte_globals_equiv
         set_cap_globals_equiv'' unmap_page_globals_equiv store_pte_globals_equiv
         store_pte_globals_equiv hoare_weak_lift_imp set_message_info_globals_equiv
         unmap_page_valid_arch_state perform_pg_inv_get_addr_globals_equiv
      | wpc | simp add: do_machine_op_bind sfence_def | fastforce)+

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
    apply (fastforce dest: riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
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
   apply (wp modify_wp cap_insert_globals_equiv''
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
                             word1 \<noteq> riscv_global_pt (arch_state b) \<and> word1 \<noteq> idle_thread b \<and>
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
             del: Untyped_AI.delete_objects_pspace_no_overlap
          | simp add: page_bits_def)+
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
   apply (frule riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
   apply (drule_tac p="global_pt sa" in ptr_range_memI)
   apply fastforce
  apply (rule conjI, fastforce simp: global_refs_def)
  apply (rule conjI)
   apply clarify
   apply (frule riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
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
  by (wp modify_wp set_asid_pool_globals_equiv set_cap_globals_equiv'' get_cap_wp | wpc | simp)+

lemma perform_asid_pool_invocation_globals_equiv:
  "\<lbrace>globals_equiv s and invs and valid_apinv api\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding perform_asid_pool_invocation_def
  apply (rule hoare_weaken_pre)
   apply (wp modify_wp set_asid_pool_globals_equiv set_cap_globals_equiv''
             store_asid_pool_entry_globals_equiv copy_global_mappings_globals_equiv
             copy_global_mappings_valid_arch_state get_cap_wp
          | wpc | simp)+
  apply (clarsimp simp: valid_apinv_def cong: conj_cong)
  apply (intro conjI; fastforce?)
    apply (frule riscv_global_pt_in_global_refs[OF invs_valid_global_arch_objs])
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (frule (1) cap_not_in_valid_global_refs)
    apply (clarsimp simp: acap_obj_def is_pt_cap_def split: arch_cap.splits)
   apply (rule caps_of_state_aligned_page_table)
    apply (fastforce simp: cte_wp_at_caps_of_state is_pt_cap_def is_PageTableCap_def
                    split: option.splits)
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule (1) cap_not_in_valid_global_refs)
  apply (clarsimp simp: acap_obj_def is_pt_cap_def split: arch_cap.splits)
  done


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
  apply (case_tac ai; rule equiv_valid_guard_imp)
  by (wpsimp wp: doesnt_touch_globalsI
                 reads_respects_g[OF perform_page_table_invocation_reads_respects]
                 reads_respects_g[OF perform_page_invocation_reads_respects]
                 reads_respects_g[OF perform_asid_control_invocation_reads_respects]
                 perform_asid_pool_invocation_reads_respects_g
                 perform_page_table_invocation_globals_equiv
                 perform_page_invocation_globals_equiv
                 perform_asid_control_invocation_globals_equiv
                 perform_asid_pool_invocation_globals_equiv
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
                    perform_asid_pool_invocation_globals_equiv)+
  apply (auto simp: authorised_for_globals_arch_inv_def invs_def valid_state_def valid_arch_inv_def)
  done

crunch arch_post_cap_deletion
  for valid_global_objs[wp]: "valid_global_objs"

lemma get_thread_state_globals_equiv[wp]:
  "get_thread_state ref \<lbrace>globals_equiv s\<rbrace>"
  by wp

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

lemma thread_set_globals_equiv:
  "(\<And>tcb. arch_tcb_context_get (tcb_arch (f tcb)) = arch_tcb_context_get (tcb_arch tcb))
   \<Longrightarrow> \<lbrace>globals_equiv s and valid_arch_state\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding thread_set_def
  apply (wp set_object_globals_equiv)
  apply simp
  apply (intro impI conjI allI)
    apply (fastforce simp: valid_arch_state_def obj_at_def get_tcb_def dest: valid_global_arch_objs_pt_at)+
  apply (clarsimp simp: get_tcb_def tcb_at_def2 split: kernel_object.splits option.splits)
  done

end

hide_fact as_user_globals_equiv

context begin interpretation Arch .

requalify_consts
  authorised_for_globals_arch_inv

requalify_facts
  arch_post_cap_deletion_valid_global_objs
  get_thread_state_globals_equiv
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
  get_thread_state_globals_equiv[wp]
  arch_post_modify_registers_cur_domain[wp]
  arch_post_modify_registers_cur_thread[wp]
  prepare_thread_delete_st_tcb_at_halted[wp]

end

declare as_user_globals_equiv[wp]

axiomatization dmo_reads_respects where
  dmo_read_stval_reads_respects: "reads_respects aag l \<top> (do_machine_op read_stval)"

end
