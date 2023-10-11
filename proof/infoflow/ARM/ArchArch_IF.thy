(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchArch_IF
imports Arch_IF
begin

context Arch begin global_naming ARM

named_theorems Arch_IF_assms

lemma irq_state_clearExMonitor[wp]:
  "clearExMonitor \<lbrace>\<lambda>s. P (irq_state s)\<rbrace>"
  by (simp add: clearExMonitor_def | wp modify_wp)+

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
      apply ((rule modifies_at_mostI | wp set_object_equiv_but_for_labels | simp add: split_def | fastforce dest: get_tcb_not_asid_pool_at)+)[2]
    apply auto
  done

crunch valid_global_refs[Arch_IF_assms, wp]: arch_post_cap_deletion "valid_global_refs"

crunch irq_state_of_state[Arch_IF_assms, wp]: store_word_offs "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: storeWord_def)

crunches set_irq_state, arch_post_cap_deletion, handle_arch_fault_reply
  for irq_state_of_state[Arch_IF_assms, wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps maskInterrupt_def)

crunch irq_state_of_state[Arch_IF_assms, wp]: arch_switch_to_idle_thread, arch_switch_to_thread
  "\<lambda>s :: det_state. P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp crunch_wps whenE_wp
   simp: invalidateLocalTLB_ASID_def setHardwareASID_def set_current_pd_def machine_op_lift_def
         machine_rest_lift_def crunch_simps storeWord_def dsb_def isb_def writeTTBR0_def)

crunch irq_state_of_state[Arch_IF_assms, wp]: arch_invoke_irq_handler "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp simp: maskInterrupt_def)

crunch irq_state_of_state[wp]: arch_perform_invocation "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp simp: set_current_pd_def invalidateLocalTLB_ASID_def do_flush_defs
       invalidateLocalTLB_VAASID_def cleanByVA_PoU_def do_flush_def cache_machine_op_defs
   wp: crunch_wps simp: crunch_simps ignore: ignore_failure)

crunch irq_state_of_state[Arch_IF_assms, wp]: arch_finalise_cap, prepare_thread_delete
  "\<lambda>s :: det_state. P (irq_state_of_state s)"
  (wp: modify_wp crunch_wps dmo_wp
   simp: crunch_simps invalidateLocalTLB_ASID_def dsb_def
         cleanCaches_PoU_def invalidate_I_PoU_def clean_D_PoU_def)

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
      apply (fastforce intro: equiv_forI elim: equiv_forE)
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
  apply (fastforce simp: obj_at_def valid_arch_state_def)
  done

lemma set_thread_state_globals_equiv[Arch_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_thread_state ref ts
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_thread_state_def
  apply (wp set_object_globals_equiv dxo_wp_weak |simp)+
  apply (intro impI conjI allI)
    apply (clarsimp simp: valid_arch_state_def obj_at_def tcb_at_def2 get_tcb_def is_tcb_def
                    dest: get_tcb_SomeD
                   split: option.splits kernel_object.splits)+
  done

lemma set_cap_globals_equiv''[Arch_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_cap cap p
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_cap_def
  apply (simp only: split_def)
  apply (wp set_object_globals_equiv hoare_vcg_all_lift get_object_wp | wpc | simp)+
  apply (fastforce simp: valid_arch_state_def obj_at_def is_tcb_def)+
  done

lemma as_user_globals_equiv[Arch_IF_assms]:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
   as_user tptr f
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_globals_equiv simp: split_def)
  apply (clarsimp simp: valid_arch_state_def get_tcb_def obj_at_def)
  done

end

context begin interpretation Arch .

requalify_facts
  set_simple_ko_globals_equiv
  retype_region_irq_state_of_state
  arch_perform_invocation_irq_state_of_state

declare
  retype_region_irq_state_of_state[wp]
  arch_perform_invocation_irq_state_of_state[wp]

end


global_interpretation Arch_IF_1?: Arch_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Arch_IF_assms)?)
qed


lemmas invs_imps =
  invs_sym_refs invs_psp_aligned invs_distinct invs_arch_state invs_valid_global_objs
  invs_arch_state invs_valid_objs invs_valid_global_refs tcb_at_invs invs_cur invs_kernel_mappings


context Arch begin global_naming ARM

lemma cte_wp_at_page_directory_not_in_globals:
  "\<lbrakk> cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap word optiona))) slot s;
     x \<le> (kernel_base >> 20) - 1; valid_objs s; valid_global_refs s \<rbrakk>
     \<Longrightarrow> (x << 2) + word && ~~ mask pd_bits \<notin> global_refs s"
  apply (frule (1) cte_wp_at_valid_objs_valid_cap)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule (1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def)
  apply (subgoal_tac "is_aligned word pd_bits")
   apply (rule pd_shifting_global_refs)
     apply (simp add: pd_bits_def pageBits_def)+
  done

lemma not_in_global_not_arm:
  "A \<notin> global_refs s \<Longrightarrow> A \<noteq> arm_global_pd (arch_state s)"
  by (simp add: global_refs_def)

lemma cte_wp_at_page_cap_bits :
  "\<lbrakk> cte_wp_at ((=) (ArchObjectCap (PageTableCap word option))) slot s; valid_objs s \<rbrakk>
     \<Longrightarrow> cte_wp_at (\<lambda>c. (\<lambda>x. x && ~~ mask pt_bits) ` set [word, word + 4 .e. word + 2 ^ pt_bits - 1]
                        \<subseteq> obj_refs c \<and> is_pt_cap c) slot s"
  apply (frule (1) cte_wp_at_valid_objs_valid_cap)
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  apply (erule cte_wp_at_weakenE)
  apply (unfold is_pt_cap_def)
  apply (subgoal_tac "is_aligned word pt_bits")
   prefer 2
   apply (simp add: pt_bits_def pageBits_def)
  apply (auto simp: word_aligned_pt_slots)
  done

lemma mapM_x_swp_store_pte_invs' :
  "\<lbrace>invs and (\<lambda>s. cte_wp_at ((=) (ArchObjectCap (PageTableCap word option))) slot s)\<rbrace>
   mapM_x (swp store_pte InvalidPTE) [word , word + 4 .e. word + 2 ^ pt_bits - 1]
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_pre)
   apply (rule mapM_x_swp_store_pte_invs)
  apply clarsimp
  apply (case_tac slot)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (auto simp: cte_wp_at_page_cap_bits invs_def valid_state_def valid_pspace_def)
  done

lemma cte_wp_at_page_directory_not_in_kernel_mappings:
  "\<lbrakk> cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap word optiona))) slot s;
     x \<le> (kernel_base >> 20) - 1; valid_objs s; valid_global_refs s \<rbrakk>
     \<Longrightarrow> ucast ((x << 2) + word && mask pd_bits >> 2) \<notin> kernel_mapping_slots"
  apply (frule (1) cte_wp_at_valid_objs_valid_cap)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule (1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def)
  apply (subgoal_tac "is_aligned word pd_bits")
   apply (rule pd_shifting_kernel_mapping_slots)
    apply (simp add: pd_bits_def pageBits_def)+
  done

lemma get_asid_pool_revrv':
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
     (\<lambda>rv rv'. aag_can_read aag ptr \<longrightarrow> rv = rv') \<top> (get_asid_pool ptr)"
  unfolding get_asid_pool_def
  apply (rule_tac W="\<lambda>rv rv'. aag_can_read aag ptr \<longrightarrow> rv = rv'" in equiv_valid_rv_bind)
    apply (rule get_object_revrv')
   apply (case_tac "aag_can_read aag ptr")
    apply (simp)
    apply (case_tac rv)
        apply (simp | rule fail_ev2_l)+
    apply (rename_tac arch_kernel_obj)
    apply (case_tac arch_kernel_obj)
       apply (simp | rule return_ev2 | rule fail_ev2_l)+
   apply (clarsimp simp: equiv_valid_2_def)
   apply (case_tac rv)
       apply (clarsimp simp: fail_def)+
   apply (case_tac rv')
       apply (clarsimp simp: fail_def)+
   apply (rename_tac arch_kernel_obj arch_kernel_obj')
   apply (case_tac arch_kernel_obj)
      apply (case_tac arch_kernel_obj')
         apply (clarsimp simp: fail_def return_def)+
  apply (rule get_object_inv)
  done

lemma get_pt_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (get_pt ptr)"
  unfolding get_pt_def
  apply (rule equiv_valid_rv_bind)
    apply (rule get_object_revrv)
   apply (simp)
   apply (case_tac rv)
       apply (simp | rule fail_ev2_l)+
   apply (case_tac rv')
       apply (simp | rule fail_ev2_r)+
   apply (rename_tac arch_kernel_obj arch_kernel_obj')
   apply (case_tac arch_kernel_obj)
      apply (simp | rule fail_ev2_l)+
     apply (case_tac arch_kernel_obj')
        apply (simp | rule fail_ev2_r | rule return_ev2)+
    apply (case_tac arch_kernel_obj')
       apply (simp | rule fail_ev2_l)+
  apply (rule get_object_inv)
  done

lemma set_pt_reads_respects:
  "reads_respects aag l \<top> (set_pt ptr pt)"
  unfolding set_pt_def
  by (rule set_object_reads_respects)

lemma get_pt_reads_respects:
  "reads_respects aag l (K (is_subject aag ptr)) (get_pt ptr)"
  unfolding get_pt_def
  by (wpsimp wp: get_object_rev hoare_vcg_all_lift hoare_drop_imps)

lemma store_pte_reads_respects:
  "reads_respects aag l (K (is_subject aag (p && ~~ mask pt_bits)))
    (store_pte p pte)"
  unfolding store_pte_def fun_app_def
  by (wpsimp wp: set_pt_reads_respects get_pt_reads_respects)

lemma get_asid_pool_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_asid_pool ptr)"
  unfolding get_asid_pool_def
  by (wpsimp wp: get_object_rev)

lemma get_asid_pool_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag (\<lambda>rv rv'. rv (ucast asid) = rv' (ucast asid))
                            (\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                                 is_subject_asid aag asid \<and> asid \<noteq> 0)
                            (get_asid_pool a)"
  unfolding get_asid_pool_def
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule_tac R'="\<lambda>rv rv'. \<forall>p p'. rv = ArchObj (ASIDPool p) \<and> rv' = ArchObj (ASIDPool p')
                                       \<longrightarrow> p (ucast asid) = p' (ucast asid)"
               and P="\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                          is_subject_asid aag asid \<and> asid \<noteq> 0"
               and P'="\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                           is_subject_asid aag asid \<and> asid \<noteq> 0"
                in equiv_valid_2_bind)
      apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits
                       simp: fail_ev2_l fail_ev2_r return_ev2)
     apply (clarsimp simp: get_object_def gets_def assert_def bind_def put_def get_def
                           equiv_valid_2_def return_def fail_def
                    split: if_split)
     apply (erule reads_equivE)
     apply (clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)
     apply (drule aag_can_read_own_asids)
     apply (drule_tac s="Some a" in sym)
     apply force
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

lemma find_pd_for_asid_reads_respects:
  "reads_respects aag l (K (is_subject_asid aag asid)) (find_pd_for_asid asid)"
  apply (simp add: find_pd_for_asid_def)
  apply (subst gets_applyE)
  (* everything up to and including get_asid_pool, both executions are the same.
     it is only get_asid_pool that can return different values and for which we need
     to go equiv_valid_2. We rewrite using associativity to make the decomposition
     easier *)
  apply (subst bindE_assoc[symmetric])+
  apply (simp add: equiv_valid_def2)
  apply (subst rel_sum_comb_equals[symmetric])
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule_tac R'="\<lambda> rv rv'. rv (ucast asid) = rv' (ucast asid)" and Q="\<top>\<top>" and Q'="\<top>\<top>"
                in equiv_valid_2_bindE)
      apply (clarsimp split: option.splits simp: throwError_def returnOk_def)
      apply (intro conjI impI allI)
       apply (rule return_ev2, simp)
      apply (rule return_ev2, simp)
     apply wp+
   apply (rule_tac R'="(=)"
               and Q="\<lambda> rv s. rv = (arm_asid_table (arch_state s)) (asid_high_bits_of asid)
                            \<and> is_subject_asid aag asid \<and> asid \<noteq> 0"
               and Q'="\<lambda> rv s. rv = (arm_asid_table (arch_state s)) (asid_high_bits_of asid)
                             \<and> is_subject_asid aag asid \<and> asid \<noteq> 0"
                in equiv_valid_2_bindE)
      apply (simp add: equiv_valid_def2[symmetric])
      apply (split option.splits)
      apply (intro conjI impI allI)
       apply (simp add: throwError_def)
       apply (rule return_ev2, simp)
      apply (rule equiv_valid_2_liftE)
      apply (clarsimp)
      apply (rule get_asid_pool_revrv)
     apply (wp gets_apply_wp)+
   apply (subst rel_sum_comb_equals)
   apply (subst equiv_valid_def2[symmetric])
   apply (wp gets_apply_ev | simp)+
  apply (fastforce intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq)
  done

lemma find_pd_for_asid_assert_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs
                                         and K (is_subject_asid aag asid))
                  (find_pd_for_asid_assert asid)"
  unfolding find_pd_for_asid_assert_def
  apply (wpsimp wp: get_pde_rev find_pd_for_asid_reads_respects hoare_vcg_all_lift)
   apply (rule_tac Q'="\<lambda>rv s. is_subject aag (lookup_pd_slot rv 0 && ~~ mask pd_bits)"
                in hoare_post_imp_R)
    apply (rule find_pd_for_asid_pd_slot_authorised)
   apply (rename_tac rv s)
   apply (subgoal_tac "lookup_pd_slot rv 0 = rv")
    apply fastforce
   apply (simp add: lookup_pd_slot_def)
  apply fastforce
  done

lemma modify_arm_hwasid_table_reads_respects:
  "reads_respects aag l \<top> (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table := param\<rparr>\<rparr>))"
  apply (simp add: equiv_valid_def2)
  apply (rule modify_ev2)
  (* slow 5s *)
  by (auto simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def
          intro: equiv_asids_triv' split: if_splits)


lemma modify_arm_asid_map_reads_respects:
  "reads_respects aag l \<top> (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map := param\<rparr>\<rparr>))"
  apply (simp add: equiv_valid_def2)
  apply (rule modify_ev2)
  (* slow 5s *)
  by (auto simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def
          intro: equiv_asids_triv' split: if_splits)

lemma modify_arm_next_asid_reads_respects:
  "reads_respects aag l \<top> (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid := param\<rparr>\<rparr>))"
  apply (simp add: equiv_valid_def2)
  apply (rule modify_ev2)
  (* slow 5s *)
  by (auto simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def
          intro: equiv_asids_triv' split: if_splits)

lemmas modify_arch_state_reads_respects =
  modify_arm_asid_map_reads_respects
  modify_arm_hwasid_table_reads_respects
  modify_arm_next_asid_reads_respects

lemma states_equiv_for_arm_hwasid_table_update1:
  "states_equiv_for P Q R S (s\<lparr>arch_state := (arch_state s)\<lparr>arm_hwasid_table := Y\<rparr>\<rparr>) t =
   states_equiv_for P Q R S s t"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)

lemma states_equiv_for_arm_hwasid_table_update2:
  "states_equiv_for P Q R S t (s\<lparr>arch_state := (arch_state s)\<lparr>arm_hwasid_table := Y\<rparr>\<rparr>) =
   states_equiv_for P Q R S t s"
  apply (rule iffI)
   apply (drule states_equiv_for_sym)
   apply (rule states_equiv_for_sym)
   apply (simp add: states_equiv_for_arm_hwasid_table_update1)
  apply (drule states_equiv_for_sym)
  apply (rule states_equiv_for_sym)
  apply (simp add: states_equiv_for_arm_hwasid_table_update1)
  done

lemma states_equiv_for_arm_hwasid_table_update':
  "states_equiv_for P Q R S t (s\<lparr>arch_state := (arch_state s)\<lparr>arm_hwasid_table := Y\<rparr>\<rparr>) =
   states_equiv_for P Q R S t s"
  by (rule states_equiv_for_arm_hwasid_table_update2)

lemmas states_equiv_for_arm_hwasid_table_update =
  states_equiv_for_arm_hwasid_table_update1
  states_equiv_for_arm_hwasid_table_update2

lemma states_equiv_for_arm_next_asid_update1:
  "states_equiv_for P Q R S (s\<lparr>arch_state := (arch_state s)\<lparr>arm_next_asid := Y\<rparr>\<rparr>) t =
   states_equiv_for P Q R S s t"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)

lemma states_equiv_for_arm_next_asid_update2:
  "states_equiv_for P Q R S t (s\<lparr>arch_state := (arch_state s)\<lparr>arm_next_asid := X\<rparr>\<rparr>)
     = states_equiv_for P Q R S t s"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)

lemmas states_equiv_for_arm_next_asid_update =
  states_equiv_for_arm_next_asid_update1
  states_equiv_for_arm_next_asid_update2

lemma states_equiv_for_arm_asid_map_update1:
  "states_equiv_for P Q R S (s\<lparr>arch_state := (arch_state s)\<lparr>arm_asid_map := X\<rparr>\<rparr>) t
     = states_equiv_for P Q R S s t"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)

lemma states_equiv_for_arm_asid_map_update2:
  "states_equiv_for P Q R S t (s\<lparr>arch_state := (arch_state s)\<lparr>arm_asid_map := X\<rparr>\<rparr>)
     = states_equiv_for P Q R S t s"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)

lemmas states_equiv_for_arm_asid_map_update =
  states_equiv_for_arm_asid_map_update1
  states_equiv_for_arm_asid_map_update2

crunch states_equiv_for: invalidate_hw_asid_entry "states_equiv_for P Q R S st"
  (simp: states_equiv_for_arm_hwasid_table_update)

crunch states_equiv_for: invalidate_asid "states_equiv_for P Q R S st"
  (simp: states_equiv_for_arm_asid_map_update)

(* we don't care about the relationship between virtual and hardware asids at all --
   these should be unobservable, so rightly we don't expect this one to satisfy
   reads_respects but instead the weaker property where we assert no relation on
   the return values *)
lemma find_free_hw_asid_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (find_free_hw_asid)"
  unfolding find_free_hw_asid_def fun_app_def invalidateLocalTLB_ASID_def
  apply (rule equiv_valid_2_unobservable)
  by (wpsimp wp: invalidate_hw_asid_entry_states_equiv_for do_machine_op_mol_states_equiv_for
                 dmo_wp invalidate_asid_states_equiv_for
           simp: states_equiv_for_arm_asid_map_update states_equiv_for_arm_hwasid_table_update
                 states_equiv_for_arm_next_asid_update)+

lemma load_hw_asid_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (load_hw_asid asid)"
  by (rule equiv_valid_2_unobservable; wpsimp simp: load_hw_asid_def)

lemma states_equiv_for_arch_update1:
  "arm_asid_table A = arm_asid_table (arch_state s)
   \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>arch_state := A\<rparr>) t =
       states_equiv_for P Q R S s t"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)

lemma states_equiv_for_arch_update2:
  "arm_asid_table A = arm_asid_table (arch_state s)
   \<Longrightarrow> states_equiv_for P Q R S t (s\<lparr>arch_state := A\<rparr>) =
       states_equiv_for P Q R S t s"
  apply (rule iffI)
   apply (drule states_equiv_for_sym)
   apply (rule states_equiv_for_sym)
   apply (simp add: states_equiv_for_arch_update1)
  apply (drule states_equiv_for_sym)
  apply (rule states_equiv_for_sym)
  apply (simp add: states_equiv_for_arch_update1)
  done

lemmas states_equiv_for_arch_update = states_equiv_for_arch_update1 states_equiv_for_arch_update2

crunch states_equiv_for: store_hw_asid "states_equiv_for P Q R S st"
  (simp: states_equiv_for_arch_update)

lemma find_free_hw_asid_states_equiv_for:
  "find_free_hw_asid \<lbrace>states_equiv_for P Q R S st\<rbrace>"
  unfolding find_free_hw_asid_def
  by (wpsimp wp: invalidate_hw_asid_entry_states_equiv_for
                 do_machine_op_mol_states_equiv_for invalidate_asid_states_equiv_for
           simp: states_equiv_for_arm_next_asid_update invalidateLocalTLB_ASID_def)

crunch states_equiv_for: get_hw_asid "states_equiv_for P Q R S st"

lemma arm_context_switch_reads_respects:
  "reads_respects aag l \<top> (arm_context_switch pd asid)"
  unfolding arm_context_switch_def
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_unobservable_unit_return)
        apply (wp do_machine_op_mol_states_equiv_for get_hw_asid_states_equiv_for
               | simp add: set_current_pd_def setHardwareASID_def
                           writeTTBR0_def dsb_def isb_def dmo_bind_valid)+
  done

lemma arm_context_switch_states_equiv_for:
  "arm_context_switch pd asid \<lbrace>states_equiv_for P Q R S st\<rbrace>"
  unfolding arm_context_switch_def
  by (wp do_machine_op_mol_states_equiv_for get_hw_asid_states_equiv_for
      | simp add: set_current_pd_def setHardwareASID_def
                  dmo_bind_valid dsb_def isb_def writeTTBR0_def)+

lemma set_vm_root_states_equiv_for[wp]:
  "set_vm_root thread \<lbrace>states_equiv_for P Q R S st\<rbrace>"
  unfolding set_vm_root_def catch_def fun_app_def set_current_pd_def isb_def dsb_def writeTTBR0_def
  by (wpsimp wp: arm_context_switch_states_equiv_for do_machine_op_mol_states_equiv_for
                 hoare_vcg_all_lift whenE_wp hoare_drop_imps
           simp: dmo_bind_valid if_apply_def2)+

lemma set_vm_root_reads_respects:
  "reads_respects aag l \<top> (set_vm_root tcb)"
  by (rule reads_respects_unobservable_unit_return) wp+

lemma get_pte_reads_respects:
  "reads_respects aag l (K (is_subject aag (ptr && ~~ mask pt_bits))) (get_pte ptr)"
  unfolding get_pte_def fun_app_def
  by (wpsimp wp: get_pt_reads_respects)

crunch states_equiv_for: set_vm_root_for_flush "states_equiv_for P Q R S st"
  (wp: do_machine_op_mol_states_equiv_for ignore: do_machine_op simp: set_current_pd_def)

lemma set_vm_root_for_flush_reads_respects:
  "reads_respects aag l (is_subject aag \<circ> cur_thread) (set_vm_root_for_flush pd asid)"
  unfolding set_vm_root_for_flush_def fun_app_def set_current_pd_def
  apply (rule equiv_valid_guard_imp)
  by (wpsimp wp: arm_context_switch_reads_respects dmo_mol_reads_respects
                 hoare_vcg_all_lift hoare_drop_imps gets_cur_thread_ev get_cap_rev)+

crunch states_equiv_for: flush_table "states_equiv_for P Q R S st"
  (wp: crunch_wps do_machine_op_mol_states_equiv_for
   ignore: do_machine_op
   simp: invalidateLocalTLB_ASID_def crunch_simps)

crunch sched_act: flush_table "\<lambda> s. P (scheduler_action s)"
  (wp: crunch_wps simp: crunch_simps)

crunch wuc: flush_table "\<lambda> s. P (work_units_completed s)"
  (wp: crunch_wps simp: crunch_simps)

lemma flush_table_reads_respects:
  "reads_respects aag l \<top> (flush_table pd asid vptr pt)"
  apply (rule reads_respects_unobservable_unit_return)
       apply (rule flush_table_states_equiv_for)
      apply (rule flush_table_cur_thread)
     apply (rule flush_table_cur_domain)
    apply (rule flush_table_sched_act)
   apply (rule flush_table_wuc)
  apply wp
  done

lemma page_table_mapped_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs
                                         and K (is_subject_asid aag asid))
                  (page_table_mapped asid vaddr pt)"
  unfolding page_table_mapped_def catch_def fun_app_def
  by (wpsimp wp: get_pde_rev find_pd_for_asid_reads_respects)+

lemma unmap_page_table_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs
                                         and K (is_subject_asid aag asid))
                  (unmap_page_table asid vaddr pt)"
  unfolding unmap_page_table_def fun_app_def page_table_mapped_def
  by (wp dmo_mol_reads_respects store_pde_reads_respects get_pde_rev
         flush_table_reads_respects find_pd_for_asid_reads_respects hoare_vcg_all_lift_R
      | wpc | simp add: cleanByVA_PoU_def | wp (once) hoare_drop_imps)+

lemma perform_page_table_invocation_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs
                                         and K (authorised_page_table_inv aag pti))
                  (perform_page_table_invocation pti)"
  unfolding perform_page_table_invocation_def fun_app_def cleanCacheRange_PoU_def
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_cacheRangeOp_reads_respects dmo_mol_reads_respects store_pde_reads_respects
             set_cap_reads_respects mapM_x_ev'' store_pte_reads_respects
             unmap_page_table_reads_respects get_cap_rev
          | wpc | simp add: cleanByVA_PoU_def)+
  apply (case_tac pti; clarsimp simp: authorised_page_table_inv_def)
  done

lemma do_flush_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (do_flush typ start end pstart))"
  apply (cases "typ")
  by (wp dmo_mol_reads_respects dmo_cacheRangeOp_reads_respects
      | simp add: do_flush_def cache_machine_op_defs do_flush_defs dmo_bind_ev when_def
      | rule conjI | clarsimp)+

lemma perform_page_directory_invocation_reads_respects:
  "reads_respects aag l (is_subject aag \<circ> cur_thread) (perform_page_directory_invocation pdi)"
  unfolding perform_page_directory_invocation_def
  apply (cases pdi)
  by (wp do_flush_reads_respects set_vm_root_reads_respects set_vm_root_for_flush_reads_respects
      | simp add: when_def requiv_cur_thread_eq split del: if_split
      | wp (once) hoare_drop_imps | clarsimp)+

lemma check_mapping_pptr_reads_respects:
  "reads_respects aag l (K (\<forall>x. (tablePtr = Inl x \<longrightarrow> is_subject aag (x && ~~ mask pt_bits)) \<and>
                                (tablePtr = Inr x \<longrightarrow> is_subject aag (x && ~~ mask pd_bits))))
                  (check_mapping_pptr pptr pgsz tablePtr)"
  unfolding check_mapping_pptr_def fun_app_def
  apply (rule equiv_valid_guard_imp)
   apply (wpsimp wp: get_pte_reads_respects get_pde_rev)
  apply simp
  done

lemma lookup_pt_slot_reads_respects:
  "reads_respects aag l (K (is_subject aag (lookup_pd_slot pd vptr && ~~ mask pd_bits)))
                  (lookup_pt_slot pd vptr)"
  unfolding lookup_pt_slot_def fun_app_def
  by (wpsimp wp: get_pde_rev)

crunch sched_act: flush_page "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch wuc: flush_page "\<lambda>s. P (work_units_completed s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch states_equiv_for: flush_page "states_equiv_for P Q R S st"
  (wp: do_machine_op_mol_states_equiv_for crunch_wps
   ignore: do_machine_op
   simp: invalidateLocalTLB_VAASID_def if_apply_def2)

lemma flush_page_reads_respects:
  "reads_respects aag l \<top> (flush_page page_size pd asid vptr)"
  by (blast intro: reads_respects_unobservable_unit_return flush_page_states_equiv_for
                   flush_page_cur_thread flush_page_cur_domain flush_page_sched_act
                   flush_page_wuc flush_page_irq_state_of_state)

(* clagged some help from unmap_page_respects in Arch_AC *)
lemma unmap_page_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs
                                         and K (is_subject_asid aag asid \<and> vptr < kernel_base))
                  (unmap_page pgsz asid vptr pptr)"
  unfolding unmap_page_def catch_def fun_app_def cleanCacheRange_PoU_def
  apply (simp add: unmap_page_def swp_def cong: vmpage_size.case_cong)
  by (wp dmo_mol_reads_respects dmo_cacheRangeOp_reads_respects store_pte_reads_respects[simplified]
         check_mapping_pptr_reads_respects throw_on_false_reads_respects
         lookup_pt_slot_reads_respects lookup_pt_slot_authorised lookup_pt_slot_authorised2
         store_pde_reads_respects[simplified] flush_page_reads_respects
         find_pd_for_asid_reads_respects find_pd_for_asid_pd_slot_authorised
         mapM_ev''[where m="(\<lambda>a. store_pte a InvalidPTE)"
                     and P="\<lambda>x s. is_subject aag (x && ~~ mask pt_bits)"]
         mapM_ev''[where m="(\<lambda>a. store_pde a InvalidPDE)"
                     and P="\<lambda>x s. is_subject aag (x && ~~ mask pd_bits)"]
      | wpc | wp (once) hoare_drop_imps
      | simp add: is_aligned_6_masks is_aligned_mask[symmetric] cleanByVA_PoU_def)+

crunch states_equiv_for: invalidate_tlb_by_asid "states_equiv_for P Q R S st"
  (wp: do_machine_op_mol_states_equiv_for ignore: do_machine_op simp: invalidateLocalTLB_ASID_def)

crunch sched_act[wp]: invalidate_tlb_by_asid "\<lambda>s. P (scheduler_action s)"

crunch wuc[wp]: invalidate_tlb_by_asid "\<lambda>s. P (work_units_completed s)"

lemma invalidate_tlb_by_asid_reads_respects:
  "reads_respects aag l (\<lambda>_. True) (invalidate_tlb_by_asid asid)"
  apply (rule reads_respects_unobservable_unit_return)
       apply (rule invalidate_tlb_by_asid_states_equiv_for)
      apply wp+
  done

lemma get_master_pte_reads_respects:
  "reads_respects aag l (K (is_subject aag (p && ~~ mask pt_bits))) (get_master_pte p)"
  unfolding get_master_pte_def
  apply (wpsimp wp: get_pte_reads_respects hoare_drop_imps)
  apply (fastforce simp: pt_bits_def pageBits_def mask_lower_twice)
  done

lemma get_master_pde_reads_respects:
  "reads_respects aag l (K (is_subject aag (x && ~~ mask pd_bits))) (get_master_pde x)"
  unfolding get_master_pde_def
  apply (wpsimp wp: get_pde_rev hoare_drop_imps)
  apply (fastforce simp: pd_bits_def pageBits_def mask_lower_twice)
  done

lemma perform_page_invocation_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag and K (authorised_page_inv aag pgi)
                                               and valid_page_inv pgi and valid_vspace_objs
                                               and pspace_aligned and is_subject aag \<circ> cur_thread)
                        (perform_page_invocation pgi)"
  unfolding perform_page_invocation_def fun_app_def when_def cleanCacheRange_PoU_def
  apply (rule equiv_valid_guard_imp)
  apply wpc
      apply (simp add: mapM_discarded swp_def)
      apply (wp dmo_mol_reads_respects dmo_cacheRangeOp_reads_respects  mapM_x_ev''
                store_pte_reads_respects set_cap_reads_respects mapM_ev'' store_pde_reads_respects
                unmap_page_reads_respects set_vm_root_reads_respects dmo_mol_2_reads_respects
                set_vm_root_for_flush_reads_respects get_cap_rev  do_flush_reads_respects
                invalidate_tlb_by_asid_reads_respects get_master_pte_reads_respects
                get_master_pde_reads_respects set_mrs_reads_respects set_message_info_reads_respects
             | simp add: cleanByVA_PoU_def pte_check_if_mapped_def pde_check_if_mapped_def
             | wpc | wp (once) hoare_drop_imps[where R="\<lambda>r s. r"])+
  apply (clarsimp simp: authorised_page_inv_def valid_page_inv_def)
  apply (auto simp: cte_wp_at_caps_of_state valid_slots_def cap_auth_conferred_def
                    update_map_data_def is_page_cap_def authorised_slots_def valid_page_inv_def
                    valid_cap_simps cap_links_asid_slot_def label_owns_asid_slot_def
             dest!: bspec[OF _ rev_subsetD[OF _ tl_subseteq]] clas_caps_of_state pas_refined_Control
         | (frule aag_can_read_self, simp)+)+
  done

lemma equiv_asids_arm_asid_table_update:
  "\<lbrakk> equiv_asids R s t; kheap s pool_ptr = kheap t pool_ptr \<rbrakk>
     \<Longrightarrow> equiv_asids R
           (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (asid_table s)
                                                            (asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)
           (t\<lparr>arch_state := arch_state t\<lparr>arm_asid_table := (asid_table t)
                                                            (asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)"
  by (clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)

lemma arm_asid_table_update_reads_respects:
  "reads_respects aag l (K (is_subject aag pool_ptr))
     (do r \<leftarrow> gets (arm_asid_table \<circ> arch_state);
         modify (\<lambda>s. s\<lparr>arch_state := arch_state s
                                       \<lparr>arm_asid_table := r(asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)
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
   apply (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_for_def
             intro!: equiv_asids_arm_asid_table_update)
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
          apply (rule arm_asid_table_update_reads_respects)
         apply (wp cap_insert_reads_respects retype_region_reads_respects
                   set_cap_reads_respects delete_objects_reads_respects get_cap_rev
                | simp add: authorised_asid_control_inv_def)+
  apply (auto dest!: is_aligned_no_overflow)
  done

lemma set_asid_pool_reads_respects:
  "reads_respects aag l \<top> (set_asid_pool ptr pool)"
  unfolding set_asid_pool_def
  by (rule set_object_reads_respects)

lemma perform_asid_pool_invocation_reads_respects:
  "reads_respects aag l (pas_refined aag and K (authorised_asid_pool_inv aag api))
                  (perform_asid_pool_invocation api)"
  unfolding perform_asid_pool_invocation_def
  apply (rule equiv_valid_guard_imp)
   apply (wpsimp wp: set_asid_pool_reads_respects set_cap_reads_respects
                     get_asid_pool_rev get_cap_auth_wp[where aag=aag] get_cap_rev)
  apply (clarsimp simp: authorised_asid_pool_inv_def)
  done

lemma arch_perform_invocation_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs
                                               and authorised_arch_inv aag ai
                                               and valid_arch_inv ai and is_subject aag \<circ> cur_thread)
                        (arch_perform_invocation ai)"
  unfolding arch_perform_invocation_def fun_app_def
  apply (rule equiv_valid_guard_imp)
   apply (wpsimp wp: perform_page_table_invocation_reads_respects
                     perform_page_directory_invocation_reads_respects
                     perform_page_invocation_reads_respects
                     perform_asid_control_invocation_reads_respects
                     perform_asid_pool_invocation_reads_respects)
  by (auto simp: authorised_arch_inv_def valid_arch_inv_def)

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
  by (auto simp: reads_equiv_def2 affects_equiv_def2
         intro!: states_equiv_forI equiv_forI equiv_asids_arm_asid_table_delete
          elim!: states_equiv_forE equiv_forE
           elim: is_subject_kheap_eq[simplified reads_equiv_def2 states_equiv_for_def, rotated])

crunch states_equiv_for: invalidate_asid_entry "states_equiv_for P Q R S st"
crunch sched_act: invalidate_asid_entry "\<lambda>s. P (scheduler_action s)"
crunch wuc: invalidate_asid_entry "\<lambda>s. P (work_units_completed s)"
crunch sched_act: flush_space "\<lambda>s. P (scheduler_action s)"
crunch wuc: flush_space "\<lambda>s. P (work_units_completed s)"
crunch states_equiv_for: flush_space "states_equiv_for P Q R S st"
  (wp: mol_states_equiv_for dmo_wp
   ignore: do_machine_op
   simp: invalidateLocalTLB_ASID_def cleanCaches_PoU_def dsb_def invalidate_I_PoU_def clean_D_PoU_def)

lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq':
  "\<lbrakk> (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base
              \<longrightarrow> is_subject_asid aag asid'); reads_equiv aag s t \<rbrakk>
     \<Longrightarrow> arm_asid_table (arch_state s) (asid_high_bits_of base) =
         arm_asid_table (arch_state t) (asid_high_bits_of base)"
  apply (insert asid_high_bits_0_eq_1)
  apply (case_tac "base = 0")
   apply (subgoal_tac "is_subject_asid aag 1")
    apply simp
    apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq[where aag=aag])
      apply (erule_tac x=1 in allE)
      apply simp+
  apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq[where aag=aag])
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
                 and Q="\<lambda>rv s. rv = arm_asid_table (arch_state s) \<and>
                               (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base
                                        \<longrightarrow> is_subject_asid aag asid')"
                  in equiv_valid_rv_bind)
       apply (rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
        apply (wp, simp)
      apply (simp add: when_def)
      apply (clarsimp | rule conjI)+
        apply (subst bind_assoc[symmetric])
        apply (subst (3) bind_assoc[symmetric])
        apply (rule equiv_valid_2_guard_imp)
          apply (rule equiv_valid_2_bind)
             apply (rule equiv_valid_2_bind)
                apply (rule equiv_valid_2_unobservable)
                           apply (wp set_vm_root_states_equiv_for)+
               apply (rule arm_asid_table_delete_ev2)
              apply (wp)+
            apply (rule equiv_valid_2_unobservable)
  by (wp mapM_wp' invalidate_asid_entry_states_equiv_for flush_space_states_equiv_for
         invalidate_asid_entry_cur_thread invalidate_asid_entry_sched_act invalidate_asid_entry_wuc
         flush_space_cur_thread flush_space_sched_act flush_space_wuc return_ev2
      | rule conjI | drule (1) requiv_arm_asid_table_asid_high_bits_of_asid_eq'
      | clarsimp | simp add: equiv_valid_2_def)+

lemma set_asid_pool_state_equal_except_kheap:
  "((), s') \<in> fst (set_asid_pool ptr pool s)
   \<Longrightarrow> states_equal_except_kheap_asid s s' \<and>
       (\<forall>p. p \<noteq> ptr \<longrightarrow> kheap s p = kheap s' p) \<and>
       kheap s' ptr = Some (ArchObj (ASIDPool pool)) \<and>
       (\<forall>asid. asid \<noteq> 0
               \<longrightarrow> arm_asid_table (arch_state s) (asid_high_bits_of asid) =
                   arm_asid_table (arch_state s') (asid_high_bits_of asid) \<and>
                   (\<forall>pool_ptr. arm_asid_table (arch_state s) (asid_high_bits_of asid) =
                               Some pool_ptr
                               \<longrightarrow> asid_pool_at pool_ptr s = asid_pool_at pool_ptr s' \<and>
                                   (\<forall>asid_pool asid_pool'. pool_ptr \<noteq> ptr
                                                           \<longrightarrow> kheap s pool_ptr =
                                                               Some (ArchObj (ASIDPool asid_pool)) \<and>
                                                               kheap s' pool_ptr =
                                                               Some (ArchObj (ASIDPool asid_pool'))
                                                               \<longrightarrow> asid_pool (ucast asid) =
                                                                   asid_pool' (ucast asid))))"
  by (clarsimp simp: set_asid_pool_def put_def bind_def set_object_def get_object_def gets_def
                     get_def return_def assert_def fail_def states_equal_except_kheap_asid_def
                     equiv_for_def obj_at_def
              split: if_split_asm)

lemma set_asid_pool_delete_ev2:
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) \<top>\<top>
     (\<lambda>s. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some a \<and>
          kheap s a = Some (ArchObj (ASIDPool pool)) \<and> asid \<noteq> 0 \<and> is_subject_asid aag asid)
     (\<lambda>s. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some a \<and>
          kheap s a = Some (ArchObj (ASIDPool pool')) \<and> asid \<noteq> 0 \<and> is_subject_asid aag asid)
     (set_asid_pool a (pool(ucast asid := None))) (set_asid_pool a (pool'(ucast asid := None)))"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (frule_tac s'=b in set_asid_pool_state_equal_except_kheap)
  apply (frule_tac s'=ba in set_asid_pool_state_equal_except_kheap)
  apply (clarsimp simp: states_equal_except_kheap_asid_def)
  apply (rule conjI)
   apply (clarsimp simp: states_equiv_for_def reads_equiv_def equiv_for_def | rule conjI)+
    apply (case_tac "x=a")
     apply (clarsimp)
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
    apply (erule_tac x="pasASIDAbs aag asida" in ballE)
     apply (clarsimp)+
  apply (clarsimp simp: affects_equiv_def equiv_for_def states_equiv_for_def | rule conjI)+
   apply (case_tac "x=a")
    apply (clarsimp)
   apply (fastforce)
  apply (clarsimp simp: equiv_asids_def equiv_asid_def | rule conjI)+
   apply (case_tac "pool_ptr=a")
    apply (clarsimp)
    apply (erule_tac x=asid in allE)+
    apply (clarsimp simp: asid_pool_at_kheap)
   apply (erule_tac x=asida in allE)+
   apply (clarsimp)
  apply (clarsimp)
  apply (case_tac "pool_ptr=a")
   apply (clarsimp)+
  done

lemma delete_asid_reads_respects:
  "reads_respects aag l (K (asid \<noteq> 0 \<and> is_subject_asid aag asid)) (delete_asid asid pd)"
  unfolding delete_asid_def
  apply (subst equiv_valid_def2)
  apply (rule_tac W="\<top>\<top>" and Q="\<lambda>rv s. rv = arm_asid_table (arch_state s) \<and>
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
      apply (rule_tac R'="\<lambda>rv rv'. rv (ucast asid) = rv' (ucast asid)" in equiv_valid_2_bind)
         apply (simp add: when_def)
         apply (clarsimp | rule conjI)+
          apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
             apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
                apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
                   apply (subst equiv_valid_def2[symmetric])
                   apply (rule reads_respects_unobservable_unit_return)
                        apply (wp set_vm_root_states_equiv_for)+
                  apply (rule set_asid_pool_delete_ev2)
                 apply (wp)+
               apply (rule equiv_valid_2_unobservable)
                          apply (wp invalidate_asid_entry_states_equiv_for invalidate_asid_entry_cur_thread)+
                    apply (simp add: invalidate_asid_entry_def
                           | wp invalidate_asid_kheap invalidate_hw_asid_entry_kheap load_hw_asid_kheap)+
            apply (rule equiv_valid_2_unobservable)
                       apply (wp flush_space_states_equiv_for flush_space_cur_thread)+
                 apply (wp load_hw_asid_kheap | simp add: flush_space_def | wpc)+
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
  done

lemma set_asid_pool_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_asid_pool ptr pool
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  apply (fastforce simp: valid_arch_state_def obj_at_def)
  done

crunch globals_equiv[wp]: invalidate_hw_asid_entry "globals_equiv s"
  (simp: globals_equiv_def)

crunch globals_equiv[wp]: invalidate_asid "globals_equiv s"
  (simp: globals_equiv_def)

lemma globals_equiv_arm_next_asid_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>arm_next_asid := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma globals_equiv_arm_asid_map_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>arm_asid_map := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma globals_equiv_arm_hwasid_table_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>arm_hwasid_table := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma globals_equiv_arm_asid_table_update[simp]:
  "globals_equiv s (t\<lparr>arch_state := arch_state t\<lparr>arm_asid_table := x\<rparr>\<rparr>) = globals_equiv s t"
  by (simp add: globals_equiv_def)

lemma find_free_hw_asid_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> find_free_hw_asid \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding find_free_hw_asid_def
  by (wp modify_wp invalidate_hw_asid_entry_globals_equiv
         dmo_mol_globals_equiv invalidate_asid_globals_equiv
      | wpc | simp add: invalidateLocalTLB_ASID_def)+

lemma store_hw_asid_globals_equiv[wp]:
  "store_hw_asid asid hw_asid \<lbrace>globals_equiv s\<rbrace>"
  unfolding store_hw_asid_def
  apply (wp find_pd_for_asid_assert_wp | rule modify_wp, simp)+
  apply (fastforce simp: globals_equiv_def)
  done

lemma get_hw_asid_globals_equiv[wp]:
  "get_hw_asid asid \<lbrace>globals_equiv s\<rbrace>"
  unfolding get_hw_asid_def
  by (wp store_hw_asid_globals_equiv find_free_hw_asid_globals_equiv load_hw_asid_wp | wpc | simp)+

lemma arm_context_switch_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> arm_context_switch pd asid \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding arm_context_switch_def setHardwareASID_def
  by (wp dmo_mol_globals_equiv get_hw_asid_globals_equiv
      | simp add: dmo_bind_valid set_current_pd_def writeTTBR0_def isb_def dsb_def)+

lemma set_vm_root_globals_equiv[wp]:
  "set_vm_root tcb \<lbrace>globals_equiv s\<rbrace>"
  apply (clarsimp simp: set_vm_root_def set_current_pd_def dsb_def
                        isb_def writeTTBR0_def dmo_bind_valid)
  apply (wp dmo_mol_globals_equiv arm_context_switch_globals_equiv whenE_inv
         | wpc
         | clarsimp simp: dmo_bind_valid isb_def dsb_def writeTTBR0_def)+
   apply (wp hoare_vcg_all_lift | wp (once) hoare_drop_imps | clarsimp)+
  done

lemma invalidate_asid_entry_globals_equiv[wp]:
  "invalidate_asid_entry asid \<lbrace>globals_equiv s\<rbrace>"
  unfolding invalidate_asid_entry_def
  by (wpsimp wp: invalidate_hw_asid_entry_globals_equiv
                 invalidate_asid_globals_equiv load_hw_asid_wp)

lemma flush_space_globals_equiv[wp]:
  "flush_space asid \<lbrace>globals_equiv s\<rbrace>"
  unfolding flush_space_def
  by (wp dmo_mol_globals_equiv load_hw_asid_wp
      | wpc
      | simp add: invalidateLocalTLB_ASID_def cleanCaches_PoU_def dsb_def
                  invalidate_I_PoU_def clean_D_PoU_def dmo_bind_valid)+

lemma delete_asid_pool_globals_equiv[wp]:
  "delete_asid_pool base ptr \<lbrace>globals_equiv s\<rbrace>"
  unfolding delete_asid_pool_def
  by (wpsimp wp: set_vm_root_globals_equiv mapM_wp[OF _ subset_refl] modify_wp
                 invalidate_asid_entry_globals_equiv flush_space_globals_equiv)

crunch globals_equiv[wp]: invalidate_tlb_by_asid "globals_equiv s"
  (simp: invalidateLocalTLB_ASID_def wp: dmo_mol_globals_equiv ignore: machine_op_lift do_machine_op)

lemma set_pt_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   set_pt ptr pt
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_pt_def
  apply (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  apply (fastforce simp: valid_arch_state_def obj_at_def)
  done

crunch globals_equiv: store_pte "globals_equiv s"

lemma set_vm_root_for_flush_globals_equiv[wp]:
  "set_vm_root_for_flush pd asid \<lbrace>globals_equiv s\<rbrace>"
  unfolding set_vm_root_for_flush_def set_current_pd_def fun_app_def
  by (wpsimp wp: dmo_mol_globals_equiv hoare_drop_imps hoare_vcg_all_lift)

lemma flush_table_globals_equiv[wp]:
  "flush_table pd asid cptr pt \<lbrace>globals_equiv s\<rbrace>"
  unfolding flush_table_def invalidateLocalTLB_ASID_def fun_app_def
  by (wp mapM_wp' dmo_mol_globals_equiv
      | wpc | simp add: do_machine_op_bind split del: if_split cong: if_cong)+

lemma arm_global_pd_arm_asid_map_update[simp]:
  "arm_global_pd (arch_state s\<lparr>arm_asid_map := x\<rparr>) = arm_global_pd (arch_state s)"
  by (simp add: globals_equiv_def)

lemma arm_global_pd_arm_hwasid_table_update[simp]:
  "arm_global_pd (arch_state s\<lparr>arm_hwasid_table := x\<rparr>) = arm_global_pd (arch_state s)"
  by (simp add: globals_equiv_def)

crunch arm_global_pd[wp]: flush_table "\<lambda>s. P (arm_global_pd (arch_state s))"
  (wp: crunch_wps simp: crunch_simps)

crunch globals_equiv[wp]: page_table_mapped "globals_equiv st"

(*FIXME: duplicated, more reasonable version of not_in_global_refs_vs_lookup *)

lemma not_in_global_refs_vs_lookup2:
  "\<lbrakk> valid_vs_lookup s; valid_global_refs s; valid_arch_state s;
     valid_global_objs s; page_directory_at p s; (\<exists>\<rhd> p) s \<rbrakk>
     \<Longrightarrow> p \<notin> global_refs s"
  apply (insert not_in_global_refs_vs_lookup[where p=p and s=s])
  apply simp
  done

lemma find_pd_for_asid_not_arm_global_pd:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_global_objs
                   and valid_vs_lookup and valid_global_refs and valid_arch_state\<rbrace>
   find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. lookup_pd_slot rv vptr && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s)\<rbrace>, -"
  apply (wp find_pd_for_asid_lots)
  apply clarsimp
  apply (subst(asm) lookup_pd_slot_pd)
   apply (erule page_directory_at_aligned_pd_bits, simp+)
  apply (frule (4) not_in_global_refs_vs_lookup2)
   apply (auto simp: global_refs_def)
  done

lemma find_pd_for_asid_not_arm_global_pd_large_page:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_global_objs
                   and valid_vs_lookup and valid_global_refs and valid_arch_state\<rbrace>
   find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. lookup_pd_slot rv vptr && mask 6 = 0
           \<longrightarrow> (\<forall>x \<in> set [0 , 4 .e. 0x3C].
                  x + lookup_pd_slot rv vptr && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))\<rbrace>, -"
  apply (wp find_pd_for_asid_lots)
  apply clarsimp
  apply (subst (asm) is_aligned_mask[symmetric])
  apply (frule is_aligned_6_masks[where bits=pd_bits])
   apply simp+
  apply (subst(asm) lookup_pd_slot_eq)
   apply (erule page_directory_at_aligned_pd_bits, simp+)
  apply (frule (4) not_in_global_refs_vs_lookup2)
   apply (auto simp: global_refs_def)
  done

declare dmo_mol_globals_equiv[wp]

lemma unmap_page_table_globals_equiv:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_global_objs and valid_vs_lookup
                   and valid_global_refs and valid_arch_state and globals_equiv st\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. globals_equiv st\<rbrace>"
  unfolding unmap_page_table_def page_table_mapped_def
  apply (wp store_pde_globals_equiv | wpc | simp add: cleanByVA_PoU_def)+
     apply (rule_tac Q="\<lambda>_. globals_equiv st and (\<lambda>sa. lookup_pd_slot pd vaddr &&
                                                    ~~ mask pd_bits \<noteq> arm_global_pd (arch_state sa))"
                  in hoare_strengthen_post)
      apply (wp find_pd_for_asid_not_arm_global_pd hoare_post_imp_dc2E_actual | simp)+
  done

lemma mapM_x_swp_store_pte_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   mapM_x (swp store_pte A) slots
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (rule_tac Q="\<lambda>_. globals_equiv s and valid_arch_state" in hoare_strengthen_post)
   apply (wp mapM_x_wp' store_pte_globals_equiv | simp)+
  done

lemma mapM_x_swp_store_pte_valid_arch_state[wp]:
  "mapM_x (swp store_pte A) slots \<lbrace>valid_arch_state\<rbrace>"
  by (wp mapM_x_wp' | simp add: swp_def)+

crunch valid_arch_state[wp]: unmap_page_table "valid_arch_state"
  (wp: crunch_wps simp: crunch_simps a_type_simps)

definition authorised_for_globals_page_table_inv :: "page_table_invocation \<Rightarrow> 'z state \<Rightarrow> bool" where
  "authorised_for_globals_page_table_inv pti \<equiv>
     \<lambda>s. case pti of
           PageTableMap cap ptr pde p \<Rightarrow> p && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s)
         | _ \<Rightarrow> True"

lemma perform_page_table_invocation_globals_equiv:
  "\<lbrace>valid_global_refs and valid_global_objs and valid_arch_state and globals_equiv st
                      and pspace_aligned and valid_vspace_objs and valid_vs_lookup
                      and valid_kernel_mappings and authorised_for_globals_page_table_inv pti\<rbrace>
   perform_page_table_invocation pti
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_page_table_invocation_def cleanCacheRange_PoU_def
  apply (rule hoare_weaken_pre)
   apply (wp store_pde_globals_equiv set_cap_globals_equiv'' dmo_cacheRangeOp_lift
             mapM_x_swp_store_pte_globals_equiv unmap_page_table_globals_equiv
          | wpc | simp add: cleanByVA_PoU_def)+
  apply (fastforce simp: authorised_for_globals_page_table_inv_def
                         valid_arch_state_def obj_at_def
                   dest: a_type_pdD)
  done

lemma do_flush_globals_equiv:
  "do_machine_op (do_flush typ start end pstart) \<lbrace>globals_equiv st\<rbrace>"
  apply (cases "typ")
  by (wp dmo_cacheRangeOp_lift
      | simp add: do_flush_def cache_machine_op_defs do_flush_defs do_machine_op_bind when_def
                  empty_fail_cond
      | clarsimp | rule conjI)+

lemma perform_page_directory_invocation_globals_equiv:
  "perform_page_directory_invocation pdi \<lbrace>globals_equiv st\<rbrace>"
  unfolding perform_page_directory_invocation_def
  apply (cases pdi)
   apply (wp do_flush_globals_equiv | simp)+
  done

lemma flush_page_globals_equiv[wp]:
  "flush_page page_size pd asid vptr \<lbrace>globals_equiv st\<rbrace>"
  unfolding flush_page_def invalidateLocalTLB_VAASID_def
  by (wp | simp cong: if_cong split del: if_split)+

lemma flush_page_arm_global_pd[wp]:
  "flush_page pgsz pd asid vptr \<lbrace>\<lambda>s. P (arm_global_pd (arch_state s))\<rbrace>"
  unfolding flush_page_def
  by (wp | simp cong: if_cong split del: if_split)+

lemma mapM_swp_store_pte_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   mapM (swp store_pte A) slots
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule_tac Q="\<lambda> _. globals_equiv st and valid_arch_state"
               in hoare_strengthen_post)
   apply (wp mapM_wp' store_pte_globals_equiv | simp)+
  done

lemma mapM_swp_store_pde_globals_equiv:
  "\<lbrace>globals_equiv st and (\<lambda>s. \<forall>x \<in> set slots. x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))\<rbrace>
   mapM (swp store_pde A) slots
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule_tac Q="\<lambda>_. globals_equiv st and
                         (\<lambda>s. \<forall>x \<in> set slots. x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))"
               in hoare_strengthen_post)
   apply (wp mapM_wp' store_pde_globals_equiv | simp)+
  done

lemma mapM_swp_store_pte_valid_arch_state[wp]:
  "mapM (swp store_pte A) slots \<lbrace>valid_arch_state\<rbrace>"
  by (wp mapM_wp' | simp)+

lemma mapM_x_swp_store_pde_globals_equiv :
  "\<lbrace>globals_equiv st and (\<lambda>s. \<forall>x \<in> set slots. x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))\<rbrace>
   mapM_x (swp store_pde A) slots
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule_tac Q="\<lambda>_. globals_equiv st and
                         (\<lambda>s. \<forall>x \<in> set slots. x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))"
               in hoare_strengthen_post)
   apply (wp mapM_x_wp' store_pde_globals_equiv | simp)+
  done

lemma unmap_page_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and pspace_aligned and valid_vspace_objs
                     and valid_global_objs and valid_vs_lookup and valid_global_refs\<rbrace>
   unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding unmap_page_def cleanCacheRange_PoU_def including no_pre
  apply (induct pgsz)
     prefer 4
     apply (simp only: vmpage_size.simps)
     apply (wp mapM_swp_store_pde_globals_equiv dmo_cacheRangeOp_lift | simp add: cleanByVA_PoU_def)+
        apply (rule hoare_drop_imps)
        apply (wp)+
       apply (simp)
       apply (rule hoare_drop_imps)
       apply (wp)+
     apply (rule hoare_pre)
      apply (rule_tac Q="\<lambda>x. globals_equiv st and
                             (\<lambda>sa. lookup_pd_slot x vptr && mask 6 = 0
                                   \<longrightarrow> (\<forall>xa\<in>set [0 , 4 .e. 0x3C]. xa + lookup_pd_slot x vptr
                                                                     && ~~ mask pd_bits
                                                                   \<noteq> arm_global_pd (arch_state sa)))"
                  and E="\<lambda>_. globals_equiv st" in hoare_post_impErr)
        apply (wp find_pd_for_asid_not_arm_global_pd_large_page)
       apply simp
      apply simp
     apply simp
    apply (wp store_pte_globals_equiv | simp add: cleanByVA_PoU_def)+
      apply (wp hoare_drop_imps)+
     apply (wp (once) lookup_pt_slot_inv)
     apply (wp (once) lookup_pt_slot_inv)
     apply (wp (once) lookup_pt_slot_inv)
     apply (wp (once) lookup_pt_slot_inv)
    apply (simp)
    apply (rule hoare_pre)
     apply wp
    apply (simp)
   apply (simp)
   apply (rule hoare_pre)
    apply ((wp dmo_cacheRangeOp_lift mapM_swp_store_pde_globals_equiv store_pde_globals_equiv
               lookup_pt_slot_inv mapM_swp_store_pte_globals_equiv hoare_drop_imps
            | simp add: cleanByVA_PoU_def)+)[2]
  apply (rule hoare_pre)
   apply (wp store_pde_globals_equiv | simp add: cleanByVA_PoU_def)+
    apply (wp find_pd_for_asid_not_arm_global_pd hoare_drop_imps)+
  apply (clarsimp)
  done (* don't know what happened here. wp deleted globals_equiv from precon *)

lemma cte_wp_parent_not_global_pd:
  "\<lbrakk> valid_global_refs s; cte_wp_at (parent_for_refs (Inr (a,b))) k s \<rbrakk>
     \<Longrightarrow> \<forall>x \<in> set b. x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s)"
  apply (simp only: cte_wp_at_caps_of_state)
  apply (elim exE conjE)
  apply (drule valid_global_refsD2,simp)
  apply (unfold parent_for_refs_def)
  apply (simp add: image_def global_refs_def cap_range_def)
  apply clarsimp
  apply (subgoal_tac "arm_global_pd (arch_state s) \<in> set b")
   apply auto
  done

definition authorised_for_globals_page_inv ::
  "page_invocation \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool"  where
  "authorised_for_globals_page_inv pgi \<equiv> \<lambda>s.
     case pgi of PageMap asid cap ptr m \<Rightarrow> \<exists>slot. cte_wp_at (parent_for_refs m) slot s | _ \<Rightarrow> True"

crunch valid_arch_state[wp]: unmap_page "valid_arch_state"
  (wp: crunch_wps)

lemma arm_global_pd_not_tcb:
  "valid_arch_state s \<Longrightarrow> get_tcb (arm_global_pd (arch_state s)) s = None"
  unfolding valid_arch_state_def
  apply (case_tac "get_tcb (arm_global_pd (arch_state s)) s")
   apply (auto simp: get_tcb_ko_at obj_at_def)
  done

lemma length_msg_lt_msg_max:
  "length msg_registers < msg_max_length"
  by (simp add: msg_registers_def msgRegisters_def upto_enum_def fromEnum_def enum_register msg_max_length_def)

lemma set_mrs_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>sa. thread \<noteq> idle_thread sa)\<rbrace>
      set_mrs thread buf msgs
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_mrs_def
  apply (wp | wpc)+
       apply (simp add: zipWithM_x_mapM_x)
       apply (rule conjI)
        apply (rule impI)
        apply (rule_tac Q="\<lambda>_. globals_equiv s"
          in hoare_strengthen_post)
         apply (wp mapM_x_wp')
         apply (simp add: split_def)
         apply (wp store_word_offs_globals_equiv)
        apply (simp)
       apply (clarsimp)
       apply (insert length_msg_lt_msg_max)
       apply (simp)
      apply (wp set_object_globals_equiv hoare_weak_lift_imp)
     apply (wp hoare_vcg_all_lift set_object_globals_equiv hoare_weak_lift_imp)+
   apply (clarsimp simp:arm_global_pd_not_tcb)+
  done

lemma perform_page_invocation_globals_equiv:
  "\<lbrace>authorised_for_globals_page_inv pgi and valid_page_inv pgi and globals_equiv st and
    valid_arch_state and pspace_aligned and valid_vspace_objs and valid_global_objs and
    valid_vs_lookup and valid_global_refs and ct_active and valid_idle\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_page_invocation_def cleanCacheRange_PoU_def
  apply (rule hoare_weaken_pre)
  apply (wp mapM_swp_store_pte_globals_equiv hoare_vcg_all_lift dmo_cacheRangeOp_lift
            mapM_swp_store_pde_globals_equiv mapM_x_swp_store_pte_globals_equiv
            mapM_x_swp_store_pde_globals_equiv set_cap_globals_equiv''
            unmap_page_globals_equiv store_pte_globals_equiv store_pde_globals_equiv hoare_weak_lift_imp
            do_flush_globals_equiv set_mrs_globals_equiv set_message_info_globals_equiv
         | wpc | simp add: do_machine_op_bind cleanByVA_PoU_def)+
  by (auto simp: cte_wp_parent_not_global_pd authorised_for_globals_page_inv_def valid_page_inv_def
                 valid_slots_def valid_idle_def st_tcb_def2 ct_in_state_def pred_tcb_at_def obj_at_def
          dest!: rev_subsetD[OF _ tl_subseteq])

lemma retype_region_ASIDPoolObj_globals_equiv:
  "\<lbrace>globals_equiv s and (\<lambda>sa. ptr \<noteq> arm_global_pd (arch_state s)) and (\<lambda>sa. ptr \<noteq> idle_thread sa)\<rbrace>
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
   apply (rule_tac Q="\<lambda>a b. globals_equiv s b \<and> invs b \<and>
                             word1 \<noteq> arm_global_pd (arch_state b) \<and> word1 \<noteq> idle_thread b \<and>
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
   apply (clarsimp simp: global_refs_def ptr_range_memI)
  apply (rule conjI, fastforce simp: global_refs_def)
  apply (rule conjI, fastforce simp: global_refs_def)
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

lemma perform_asid_pool_invocation_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding perform_asid_pool_invocation_def
  apply (rule hoare_weaken_pre)
   apply (wp modify_wp set_asid_pool_globals_equiv set_cap_globals_equiv''
        get_cap_wp | wpc | simp)+
  done

definition authorised_for_globals_arch_inv ::
  "arch_invocation \<Rightarrow> ('z::state_ext) state \<Rightarrow> bool" where
  "authorised_for_globals_arch_inv ai \<equiv>
    case ai of InvokePageTable oper \<Rightarrow> authorised_for_globals_page_table_inv oper
             | InvokePage oper \<Rightarrow> authorised_for_globals_page_inv oper
             | _ \<Rightarrow> \<top>"

lemma arch_perform_invocation_globals_equiv:
  "\<lbrace>globals_equiv s and invs and ct_active and valid_arch_inv ai
                    and authorised_for_globals_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding arch_perform_invocation_def
 apply (wpsimp wp: perform_page_table_invocation_globals_equiv
                   perform_page_directory_invocation_globals_equiv
                   perform_page_invocation_globals_equiv
                   perform_asid_control_invocation_globals_equiv
                   perform_asid_pool_invocation_globals_equiv)+
  apply (auto simp: authorised_for_globals_arch_inv_def
              simp: invs_def valid_state_def valid_arch_inv_def invs_valid_vs_lookup)
  done

lemma arch_perform_invocation_reads_respects_g:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects_g aag l (ct_active and authorised_arch_inv aag ai and valid_arch_inv ai
                                           and authorised_for_globals_arch_inv ai and invs
                                           and pas_refined aag and is_subject aag \<circ> cur_thread)
                          (arch_perform_invocation ai)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g)
    apply (rule arch_perform_invocation_reads_respects[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp arch_perform_invocation_globals_equiv)
   apply (simp add: invs_valid_vs_lookup invs_def valid_state_def valid_pspace_def)+
  done

lemma find_pd_for_asid_authority3:
  "\<lbrace>\<lambda>s. \<forall>pd. (pspace_aligned s \<and> valid_vspace_objs s \<longrightarrow> is_aligned pd pd_bits) \<and> (\<exists>\<rhd> pd) s
             \<longrightarrow> Q pd s\<rbrace>
   find_pd_for_asid asid
   \<lbrace>Q\<rbrace>, -"
  apply (clarsimp simp: validE_R_def validE_def valid_def imp_conjL[symmetric])
  apply (frule in_inv_by_hoareD[OF find_pd_for_asid_inv], clarsimp)
  apply (drule spec, erule mp)
  apply (simp add: use_validE_R[OF _ find_pd_for_asid_authority1]
                   use_validE_R[OF _ find_pd_for_asid_aligned_pd_bits]
                   use_validE_R[OF _ find_pd_for_asid_lookup])
  done

lemma valid_arch_arm_asid_table_unmap:
  "valid_arch_state s \<and> tab = arm_asid_table (arch_state s)
   \<longrightarrow> valid_arch_state
         (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  by (clarsimp simp: valid_state_def valid_arch_state_unmap_strg)

lemma valid_arch_objs_arm_asid_table_unmap:
  "valid_vspace_objs s \<and> tab = arm_asid_table (arch_state s)
   \<longrightarrow> valid_vspace_objs
         (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  by (clarsimp simp: valid_state_def valid_vspace_objs_unmap_strg)

lemma valid_vspace_objs_arm_asid_table_unmap:
  "valid_vspace_objs s \<and> tab = arm_asid_table (arch_state s)
   \<longrightarrow> valid_vspace_objs
         (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  by (clarsimp simp: valid_state_def valid_vspace_objs_unmap_strg)

lemmas arm_context_switch_valid_vspace_objs_aux =
  hoare_drop_imp[of valid_vspace_objs "arm_context_switch _ _" "\<lambda>_ s. valid_vspace_objs s",
                 OF arm_context_switch_vspace_objs]

lemma delete_asid_pool_valid_vspace_objs[wp]:
  "delete_asid_pool base pptr \<lbrace>valid_vspace_objs\<rbrace>"
  unfolding delete_asid_pool_def
  apply (wp modify_wp)
      apply (strengthen valid_vspace_objs_arm_asid_table_unmap)
      apply (wpsimp wp: mapM_wp')+
  done

lemma set_asid_pool_arch_objs_unmap'':
  "\<lbrace>(valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p) and K(f = (ap |` S))\<rbrace>
   set_asid_pool p f
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply simp
  apply (rule set_asid_pool_vspace_objs_unmap)
  done

lemmas set_asid_pool_vspace_objs_unmap'' = set_asid_pool_arch_objs_unmap''

lemma delete_asid_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace>
   delete_asid a b
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding delete_asid_def
  apply (wpsimp wp: set_asid_pool_vspace_objs_unmap'')
  apply (fastforce simp: restrict_eq_asn_none)
  done

lemma cte_wp_at_pt_exists_cap:
  "\<lbrakk> valid_objs s; cte_wp_at ((=) (ArchObjectCap (PageTableCap word option))) slot s;
     x \<in> set [word , word + 4 .e. word + 2 ^ pt_bits - 1] \<rbrakk>
     \<Longrightarrow> \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and>
                   x && ~~ mask pt_bits \<in> obj_refs cap \<and> is_pt_cap cap"
  apply (case_tac slot)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (subgoal_tac "is_aligned word pt_bits")
   apply (frule (1) word_aligned_pt_slots)
   apply (simp add:pageBits_def cte_wp_at_caps_of_state is_pt_cap_def)
  apply (frule (1) cte_wp_valid_cap)
  apply (simp add: valid_cap_def cap_aligned_def pt_bits_def pageBits_def)
  done

lemma mapM_x_swp_store_pte_reads_respects':
  "reads_respects aag l (invs and cte_wp_at ((=) (ArchObjectCap (PageTableCap word option))) slot
                              and K (is_subject aag word))
                  (mapM_x (swp store_pte InvalidPTE) [word , word + 4 .e. word + 2 ^ pt_bits - 1])"
  apply (rule gen_asm_ev)
  apply (wp mapM_x_ev)
   apply simp
   apply (rule equiv_valid_guard_imp)
    apply (wp store_pte_reads_respects)
   apply simp
   apply (elim conjE)
   apply (subgoal_tac "is_aligned word pt_bits")
    apply (frule (1) word_aligned_pt_slots)
    apply simp
   apply (frule cte_wp_valid_cap)
    apply (rule invs_valid_objs)
    apply simp
   apply (simp add: valid_cap_def cap_aligned_def pt_bits_def pageBits_def)
  apply simp
  apply wp
  apply simp
  apply (fastforce simp: is_cap_simps dest!: cte_wp_at_pt_exists_cap[OF invs_valid_objs])
  done

lemma pd_bits_store_pde_helper:
  "\<lbrakk> xa \<le> (kernel_base >> 20) - 1; is_aligned word pd_bits \<rbrakk>
     \<Longrightarrow> ((xa << 2) + word && ~~ mask pd_bits) = word"
  apply (clarsimp simp: field_simps)
  apply (subst is_aligned_add_helper)
    apply simp
   apply (rule shiftl_less_t2n)
    apply (erule order_le_less_trans)
    apply (simp add: kernel_base_def  pd_bits_def pageBits_def)+
  done

lemma mapM_x_swp_store_pde_reads_respects':
  "reads_respects aag l
     (cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap w opt))) slot and valid_objs
                                                                    and K (is_subject aag w))
     (mapM_x (swp store_pde InvalidPDE)
             (map ((\<lambda>x. x + w) \<circ> swp (<<) 2) [0 .e. (kernel_base >> 20) - 1]))"
  apply (wp mapM_x_ev)
   apply simp
   apply (rule equiv_valid_guard_imp)
    apply (wp store_pde_reads_respects)
   apply clarsimp
   apply (subgoal_tac "is_aligned w pd_bits")
    apply (simp add: pd_bits_store_pde_helper)
   apply (frule (1) cte_wp_valid_cap)
   apply (simp add: valid_cap_def cap_aligned_def pd_bits_def pageBits_def)
  apply simp
  apply wp
  apply (clarsimp simp: wellformed_pde_def)+
  done

lemma mapM_x_swp_store_pte_pas_refined_simple:
  "mapM_x (swp store_pte InvalidPTE) A \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp wp: mapM_x_wp' store_pte_pas_refined_simple)

lemma mapM_x_swp_store_pde_pas_refined_simple:
  "mapM_x (swp store_pde InvalidPDE) A \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp wp: mapM_x_wp' store_pde_pas_refined_simple)

crunch valid_global_objs[wp]: arch_post_cap_deletion "valid_global_objs"

lemma get_thread_state_globals_equiv[wp]:
  "get_thread_state ref \<lbrace>globals_equiv s\<rbrace>"
  unfolding get_thread_state_def
  by (wpsimp wp: set_object_globals_equiv dxo_wp_weak)

(* generalises auth_ipc_buffers_mem_Write *)
lemma auth_ipc_buffers_mem_Write':
  "\<lbrakk> x \<in> auth_ipc_buffers s thread; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> (pasObjectAbs aag thread, Write, pasObjectAbs aag x) \<in> pasPolicy aag"
  apply (clarsimp simp add: auth_ipc_buffers_member_def)
  apply (drule (1) cap_auth_caps_of_state)
  apply simp
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        vspace_cap_rights_to_auth_def vm_read_write_def is_page_cap_def
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
    apply (fastforce simp: valid_arch_state_def obj_at_def get_tcb_def)+
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
  dmo_getDFSR_reads_respects: "reads_respects aag l \<top> (do_machine_op ARM.getDFSR)" and
  dmo_getFAR_reads_respects: "reads_respects aag l \<top> (do_machine_op ARM.getFAR)" and
  dmo_getIFSR_reads_respects: "reads_respects aag l \<top> (do_machine_op ARM.getIFSR)"

end
