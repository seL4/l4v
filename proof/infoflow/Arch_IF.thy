(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_IF
imports Retype_IF
begin

context begin interpretation Arch . (*FIXME: arch_split*)

abbreviation irq_state_of_state :: "det_state \<Rightarrow> nat" where
  "irq_state_of_state s \<equiv> irq_state (machine_state s)"

lemma do_extended_op_irq_state_of_state[wp]:
  "\<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace> do_extended_op f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  by (wpsimp wp: dxo_wp_weak)

lemma no_irq_underlying_memory_update[simp]:
  "no_irq (modify (underlying_memory_update f))"
  by (wpsimp simp: no_irq_def)

crunch irq_state_of_state[wp]: cap_insert "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps)

crunch irq_state_of_state[wp]: set_extra_badge "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: storeWord_def)


lemma transfer_caps_loop_irq_state[wp]:
  "\<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace> transfer_caps_loop a b c d e f \<lbrace>\<lambda>_ s. P (irq_state_of_state s)\<rbrace>"
  apply(wp transfer_caps_loop_pres)
  done

crunch irq_state_of_state[wp]: set_mrs "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps maskInterrupt_def store_word_offs_def storeWord_def ignore: const_on_failure)

crunch irq_state_of_state[wp]: handle_recv "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps maskInterrupt_def store_word_offs_def storeWord_def ignore: const_on_failure)

crunch irq_state_of_state[wp]: handle_reply "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps maskInterrupt_def unless_def store_word_offs_def storeWord_def ignore: const_on_failure)

crunch irq_state_of_state[wp]: handle_vm_fault, handle_hypervisor_fault "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps maskInterrupt_def unless_def store_word_offs_def storeWord_def ignore: const_on_failure getFAR getDFSR getIFSR simp: getDFSR_def no_irq_getFAR getFAR_def getIFSR_def)


lemma irq_state_clearExMonitor[wp]: "\<lbrace> \<lambda>s. P (irq_state s) \<rbrace> clearExMonitor \<lbrace> \<lambda>_ s. P (irq_state s) \<rbrace>"
  apply (simp add: clearExMonitor_def | wp modify_wp)+
  done

crunch irq_state_of_state[wp]: schedule "\<lambda>(s::det_state). P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp crunch_wps hoare_whenE_wp
       simp: invalidateLocalTLB_ASID_def setHardwareASID_def set_current_pd_def
             machine_op_lift_def machine_rest_lift_def crunch_simps storeWord_def
             dsb_def isb_def writeTTBR0_def)

crunch irq_state_of_state[wp]: reply_from_kernel "\<lambda>s. P (irq_state_of_state s)"


lemma detype_irq_state_of_state[simp]:
  "irq_state_of_state (detype S s) = irq_state_of_state s"
  apply(simp add: detype_def)
  done

text \<open>Not true of invoke_untyped any more.\<close>
crunch irq_state_of_state[wp]: retype_region,create_cap,delete_objects "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp crunch_wps
    simp: crunch_simps ignore: freeMemory
    simp: freeMemory_def storeWord_def clearMemory_def machine_op_lift_def machine_rest_lift_def mapM_x_defsym)

crunch irq_state_of_state[wp]: invoke_irq_control "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp crunch_wps
   simp: crunch_simps setIRQTrigger_def machine_op_lift_def machine_rest_lift_def)

crunch irq_state_of_state[wp]: invoke_irq_handler "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp simp: maskInterrupt_def)

crunch irq_state_of_state[wp]: arch_perform_invocation "\<lambda>(s::det_state). P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp simp: set_current_pd_def invalidateLocalTLB_ASID_def invalidateLocalTLB_VAASID_def cleanByVA_PoU_def do_flush_def cache_machine_op_defs do_flush_defs wp: crunch_wps simp: crunch_simps ignore: ignore_failure)

crunch irq_state_of_state[wp]: finalise_cap "\<lambda>(s::det_state). P (irq_state_of_state s)"
  (wp: select_wp modify_wp crunch_wps dmo_wp simp: crunch_simps invalidateLocalTLB_ASID_def cleanCaches_PoU_def dsb_def invalidate_I_PoU_def clean_D_PoU_def)

crunch irq_state_of_state[wp]: send_signal "\<lambda>s. P (irq_state_of_state s)"

crunch irq_state_of_state[wp]: cap_swap_for_delete "\<lambda>(s::det_state). P (irq_state_of_state s)"

crunch irq_state_of_state[wp]: cancel_badged_sends "\<lambda>(s::det_state). P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp hoare_unless_wp modify_wp simp: filterM_mapM crunch_simps no_irq_clearMemory simp: clearMemory_def storeWord_def invalidateLocalTLB_ASID_def
   ignore: filterM)

crunch irq_state_of_state[wp]: restart,invoke_domain "\<lambda>(s::det_state). P (irq_state_of_state s)"

subsection "reads_equiv"

(* this to go in InfloFlowBase? *)
lemma get_object_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (get_object ptr)"
  unfolding get_object_def
  apply(rule equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp)
     apply(rule gets_kheap_revrv')
    apply(simp, simp)
   apply(rule equiv_valid_2_bind)
      apply(rule return_ev2)
      apply(simp)
     apply(rule assert_ev2)
     apply(simp)
    apply(wpsimp)+
  done

lemma get_object_revrv':
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
   (\<lambda>rv rv'. aag_can_read aag ptr \<longrightarrow> rv = rv')
   \<top> (get_object ptr)"
  unfolding get_object_def
  apply(rule equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp)
     apply(rule gets_kheap_revrv)
    apply(simp, simp)
   apply(rule equiv_valid_2_bind)
      apply(rule return_ev2)
      apply(simp)
     apply(rule assert_ev2)
     apply(simp add: equiv_for_def)
    apply(wpsimp)+
  done

lemma get_asid_pool_revrv':
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
   (\<lambda>rv rv'. aag_can_read aag ptr \<longrightarrow> rv = rv')
   \<top> (get_asid_pool ptr)"
  unfolding get_asid_pool_def
  apply(rule_tac W="\<lambda>rv rv'. aag_can_read aag ptr \<longrightarrow>rv = rv'" in equiv_valid_rv_bind)
    apply(rule get_object_revrv')
   apply(case_tac "aag_can_read aag ptr")
    apply(simp)
    apply(case_tac rv')
        apply(simp | rule fail_ev2_l)+
    apply(rename_tac arch_kernel_obj)
    apply(case_tac arch_kernel_obj)
       apply(simp | rule return_ev2 | rule fail_ev2_l)+
   apply(clarsimp simp: equiv_valid_2_def)
   apply(case_tac rv)
       apply(clarsimp simp: fail_def)+
   apply(case_tac rv')
       apply(clarsimp simp: fail_def)+
   apply(rename_tac arch_kernel_obj arch_kernel_obj')
   apply(case_tac arch_kernel_obj)
      apply(case_tac arch_kernel_obj')
         apply(clarsimp simp: fail_def return_def)+
  apply(rule get_object_inv)
  done

lemma get_pt_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (get_pt ptr)"
  unfolding get_pt_def
  apply(rule equiv_valid_rv_bind)
    apply(rule get_object_revrv)
   apply(simp)
   apply(case_tac rv)
       apply(simp | rule fail_ev2_l)+
   apply(case_tac rv')
       apply(simp | rule fail_ev2_r)+
   apply(rename_tac arch_kernel_obj arch_kernel_obj')
   apply(case_tac arch_kernel_obj)
      apply(simp | rule fail_ev2_l)+
     apply(case_tac arch_kernel_obj')
        apply(simp | rule fail_ev2_r | rule return_ev2)+
    apply(case_tac arch_kernel_obj')
       apply(simp | rule fail_ev2_l)+
  apply(rule get_object_inv)
  done

lemma set_pt_reads_respects:
  "reads_respects aag l \<top> (set_pt ptr pt)"
  unfolding set_pt_def
  by (rule set_object_reads_respects)

lemma get_pt_reads_respects:
  "reads_respects aag l (K (is_subject aag ptr)) (get_pt ptr)"
  unfolding get_pt_def
  apply(wp get_object_rev hoare_vcg_all_lift
       | wp (once) hoare_drop_imps | simp | wpc)+
  done

lemma store_pte_reads_respects:
  "reads_respects aag l (K (is_subject aag (p && ~~ mask pt_bits)))
    (store_pte p pte)"
  unfolding store_pte_def fun_app_def
  apply(wp set_pt_reads_respects get_pt_reads_respects)
  apply(simp)
  done

lemma get_asid_pool_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_asid_pool ptr)"
  unfolding get_asid_pool_def
  apply(wp get_object_rev | wpc | simp)+
  done


lemma assertE_reads_respects:
  "reads_respects aag l \<top> (assertE P)"
  by (rule assertE_ev)

lemma gets_applyE:
  "liftE (gets f) >>=E (\<lambda> f. g (f x)) = liftE (gets_apply f x) >>=E g"
  apply(simp add: liftE_bindE)
  apply(rule gets_apply)
  done

lemma aag_can_read_own_asids:
  "is_subject_asid aag asid \<Longrightarrow> aag_can_read_asid aag asid"
  by simp

lemma get_asid_pool_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
         (\<lambda>rv rv'. rv (ucast asid) = rv' (ucast asid))
         (\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
          is_subject_asid aag asid \<and> asid \<noteq> 0)
         (get_asid_pool a)"
  unfolding get_asid_pool_def
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule_tac R'="\<lambda> rv rv'.
                         \<forall> asid_pool asid_pool'.
                            rv = ArchObj (ASIDPool asid_pool) \<and> rv' = ArchObj (ASIDPool asid_pool')
                            \<longrightarrow> asid_pool (ucast asid) = asid_pool' (ucast asid)"
              and P="\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                         is_subject_asid aag asid \<and> asid \<noteq> 0"
              and P'="\<lambda>s. Some a = arm_asid_table (arch_state s) (asid_high_bits_of asid) \<and>
                          is_subject_asid aag asid \<and> asid \<noteq> 0"
               in equiv_valid_2_bind)
      apply(clarsimp split: kernel_object.splits arch_kernel_obj.splits
                      simp: fail_ev2_l fail_ev2_r return_ev2)
     apply(clarsimp simp: get_object_def gets_def assert_def bind_def put_def get_def
                          equiv_valid_2_def return_def fail_def
                   split: if_split)
     apply(erule reads_equivE)
     apply(clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)
     apply(drule aag_can_read_own_asids)
     apply(drule_tac s="Some a" in sym)
     apply force
    apply (wp wp_post_taut | simp)+
  done

lemma asid_high_bits_0_eq_1:
  "asid_high_bits_of 0 = asid_high_bits_of 1"
  by (auto simp: asid_high_bits_of_def asid_low_bits_def)



lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq:
  "\<lbrakk>is_subject_asid aag asid; reads_equiv aag s t; asid \<noteq> 0\<rbrakk> \<Longrightarrow>
               arm_asid_table (arch_state s) (asid_high_bits_of asid) =
               arm_asid_table (arch_state t) (asid_high_bits_of asid)"
  apply(erule reads_equivE)
  apply(fastforce simp: equiv_asids_def equiv_asid_def intro: aag_can_read_own_asids)
  done

lemma find_pd_for_asid_reads_respects:
  "reads_respects aag l (K (is_subject_asid aag asid)) (find_pd_for_asid asid)"
  apply(simp add: find_pd_for_asid_def)
  apply(subst gets_applyE)
  (* everything up to and including get_asid_pool, both executions are the same.
     it is only get_asid_pool that can return different values and for which we need
     to go equiv_valid_2. We rewrite using associativity to make the decomposition
     easier *)
  apply(subst bindE_assoc[symmetric])+
  apply(simp add: equiv_valid_def2)
  apply(subst rel_sum_comb_equals[symmetric])
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule_tac R'="\<lambda> rv rv'. rv (ucast asid) = rv' (ucast asid)" and Q="\<top>\<top>" and Q'="\<top>\<top>"
               in equiv_valid_2_bindE)
      apply(clarsimp split: option.splits simp: throwError_def returnOk_def)
      apply(intro conjI impI allI)
       apply(rule return_ev2, simp)
      apply(rule return_ev2, simp)
     apply wp+
   apply(rule_tac R'="(=)"
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
      apply(rule equiv_valid_2_liftE)
      apply(clarsimp)
      apply(rule get_asid_pool_revrv)
     apply(wp gets_apply_wp)+
   apply(subst rel_sum_comb_equals)
   apply(subst equiv_valid_def2[symmetric])
   apply(wp gets_apply_ev | simp)+
  apply(fastforce intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq)
  done

lemma find_pd_for_asid_assert_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs and
    K (is_subject_asid aag asid))
  (find_pd_for_asid_assert asid)"
  unfolding find_pd_for_asid_assert_def
  apply(wp get_pde_rev find_pd_for_asid_reads_respects hoare_vcg_all_lift
       | wpc | simp)+
   apply(rule_tac Q'="\<lambda>rv s. is_subject aag (lookup_pd_slot rv 0 && ~~ mask pd_bits)"
               in hoare_post_imp_R)
   apply(rule find_pd_for_asid_pd_slot_authorised)
   apply(subgoal_tac "lookup_pd_slot r 0 = r")
    apply(fastforce)
   apply(simp add: lookup_pd_slot_def)
  apply(fastforce)
  done

lemma modify_arm_hwasid_table_reads_respects:
  "reads_respects aag l \<top> (modify
          (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table := param\<rparr>\<rparr>))"
  apply(simp add: equiv_valid_def2)
  apply(rule modify_ev2)
  (* FIXME: slow 5s *)
  by(auto simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def
          intro: equiv_asids_triv split: if_splits)


lemma modify_arm_asid_map_reads_respects:
  "reads_respects aag l \<top> (modify
          (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map := param\<rparr>\<rparr>))"
  apply(simp add: equiv_valid_def2)
  apply(rule modify_ev2)
  (* FIXME: slow 5s *)
  by(auto simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def
          intro: equiv_asids_triv split: if_splits)

lemma modify_arm_next_asid_reads_respects:
  "reads_respects aag l \<top> (modify
          (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid := param\<rparr>\<rparr>))"
  apply(simp add: equiv_valid_def2)
  apply(rule modify_ev2)
  (* FIXME: slow 5s *)
  by(auto simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def
          intro: equiv_asids_triv split: if_splits)


lemmas modify_arch_state_reads_respects =
  modify_arm_asid_map_reads_respects
  modify_arm_hwasid_table_reads_respects
  modify_arm_next_asid_reads_respects

lemma states_equiv_for_arm_hwasid_table_update1:
  "states_equiv_for P Q R S (s\<lparr> arch_state := (arch_state s)\<lparr> arm_hwasid_table := Y \<rparr>\<rparr>) t
     = states_equiv_for P Q R S s t"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def
                     asid_pool_at_kheap)

lemma states_equiv_for_arm_hwasid_table_update2:
  "states_equiv_for P Q R S t (s\<lparr> arch_state := (arch_state s)\<lparr> arm_hwasid_table := Y \<rparr>\<rparr>)
     = states_equiv_for P Q R S t s"
  apply(rule iffI)
   apply(drule states_equiv_for_sym)
   apply(rule states_equiv_for_sym)
   apply(simp add: states_equiv_for_arm_hwasid_table_update1)
  apply(drule states_equiv_for_sym)
  apply(rule states_equiv_for_sym)
  apply(simp add: states_equiv_for_arm_hwasid_table_update1)
  done

lemma states_equiv_for_arm_hwasid_table_update':
  "states_equiv_for P Q R S t (s\<lparr> arch_state := (arch_state s)\<lparr> arm_hwasid_table := Y \<rparr>\<rparr>)
     = states_equiv_for P Q R S t s"
  by (rule states_equiv_for_arm_hwasid_table_update2)

lemmas states_equiv_for_arm_hwasid_table_update =
  states_equiv_for_arm_hwasid_table_update1
  states_equiv_for_arm_hwasid_table_update2


lemma states_equiv_for_arm_next_asid_update1:
  "states_equiv_for P Q R S (s\<lparr> arch_state := (arch_state s)\<lparr> arm_next_asid := Y \<rparr>\<rparr>) t
     = states_equiv_for P Q R S s t"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def
                       asid_pool_at_kheap)

lemma states_equiv_for_arm_next_asid_update2:
  "states_equiv_for P Q R S t (s\<lparr> arch_state := (arch_state s)\<lparr> arm_next_asid := X \<rparr>\<rparr>)
     = states_equiv_for P Q R S t s"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def
                     asid_pool_at_kheap)

lemmas states_equiv_for_arm_next_asid_update =
  states_equiv_for_arm_next_asid_update1
  states_equiv_for_arm_next_asid_update2

lemma states_equiv_for_arm_asid_map_update1:
  "states_equiv_for P Q R S (s\<lparr> arch_state := (arch_state s)\<lparr> arm_asid_map := X \<rparr>\<rparr>) t
     = states_equiv_for P Q R S s t"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def
                     asid_pool_at_kheap)

lemma states_equiv_for_arm_asid_map_update2:
  "states_equiv_for P Q R S t (s\<lparr> arch_state := (arch_state s)\<lparr> arm_asid_map := X \<rparr>\<rparr>)
     = states_equiv_for P Q R S t s"
  by (clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def
                     asid_pool_at_kheap)

lemmas states_equiv_for_arm_asid_map_update =
  states_equiv_for_arm_asid_map_update1
  states_equiv_for_arm_asid_map_update2

(* for things that only modify parts of the state not in the state relations,
   we don't care what they read since these reads are unobservable anyway;
   however, we cannot assert anything about their return-values *)
lemma equiv_valid_2_unobservable:
  assumes f:
    "\<And> P Q R S X st. \<lbrace> states_equiv_for P Q R S st \<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes f':
    "\<And> P Q R S X st. \<lbrace> states_equiv_for P Q R S st \<rbrace> f' \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes g:
    "\<And> P. \<lbrace> \<lambda> s. P (cur_thread s) \<rbrace> f \<lbrace> \<lambda> rv s. P (cur_thread s) \<rbrace>"
  assumes g':
    "\<And> P. \<lbrace> \<lambda> s. P (cur_thread s) \<rbrace> f' \<lbrace> \<lambda> rv s. P (cur_thread s) \<rbrace>"
  assumes h:
    "\<And> P. \<lbrace> \<lambda> s. P (cur_domain s) \<rbrace> f \<lbrace> \<lambda> rv s. P (cur_domain s) \<rbrace>"
  assumes h':
    "\<And> P. \<lbrace> \<lambda> s. P (cur_domain s) \<rbrace> f' \<lbrace> \<lambda> rv s. P (cur_domain s) \<rbrace>"
  assumes j:
    "\<And> P. \<lbrace> \<lambda> s. P (scheduler_action s) \<rbrace> f \<lbrace> \<lambda> rv s. P (scheduler_action s) \<rbrace>"
  assumes j':
    "\<And> P. \<lbrace> \<lambda> s. P (scheduler_action s) \<rbrace> f' \<lbrace> \<lambda> rv s. P (scheduler_action s) \<rbrace>"
  assumes k:
    "\<And> P. \<lbrace> \<lambda> s. P (work_units_completed s) \<rbrace> f \<lbrace> \<lambda> rv s. P (work_units_completed s) \<rbrace>"
  assumes k':
    "\<And> P. \<lbrace> \<lambda> s. P (work_units_completed s) \<rbrace> f' \<lbrace> \<lambda> rv s. P (work_units_completed s) \<rbrace>"
  assumes l:
    "\<And> P. \<lbrace> \<lambda> s. P (irq_state (machine_state s)) \<rbrace> f \<lbrace> \<lambda> rv s. P (irq_state (machine_state s)) \<rbrace>"
  assumes l':
    "\<And> P. \<lbrace> \<lambda> s. P (irq_state (machine_state s)) \<rbrace> f' \<lbrace> \<lambda> rv s. P (irq_state (machine_state s)) \<rbrace>"

  shows
    "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) \<top>\<top> \<top> \<top> f f'"
  apply(clarsimp simp: equiv_valid_2_def)
  apply(frule use_valid[OF _ f])
   apply(rule states_equiv_for_refl)
  apply(frule use_valid[OF _ f'])
   apply(rule states_equiv_for_refl)
  apply(frule use_valid[OF _ f])
   apply(rule states_equiv_for_refl)
  apply(frule use_valid[OF _ f'])
   apply(rule states_equiv_for_refl)
  apply(frule use_valid)
    apply(rule_tac P="(=) (cur_thread s)" in g)
   apply(rule refl)
  apply(frule_tac f=f' in use_valid)
    apply(rule_tac P="(=) (cur_thread t)" in g')
   apply(rule refl)
  apply(frule use_valid)
    apply(rule_tac P="(=) (cur_domain s)" in h)
   apply(rule refl)
  apply(frule_tac f=f' in use_valid)
    apply(rule_tac P="(=) (cur_domain t)" in h')
   apply(rule refl)
  apply(frule use_valid)
    apply(rule_tac P="(=) (scheduler_action s)" in j)
   apply(rule refl)
  apply(frule_tac f=f' in use_valid)
    apply(rule_tac P="(=) (scheduler_action t)" in j')
   apply(rule refl)
  apply(frule use_valid)
    apply(rule_tac P="(=) (work_units_completed s)" in k)
   apply(rule refl)
  apply(frule_tac f=f' in use_valid)
    apply(rule_tac P="(=) (work_units_completed t)" in k')
   apply(rule refl)
  apply(frule use_valid)
    apply(rule_tac P="(=) (irq_state (machine_state s))" in l)
   apply(rule refl)
  apply(frule_tac f=f' in use_valid)
    apply(rule_tac P="(=) (irq_state (machine_state t))" in l')
   apply(rule refl)

  apply(clarsimp simp: reads_equiv_def2 affects_equiv_def2)
  apply(auto intro: states_equiv_for_sym states_equiv_for_trans)
  done


crunch states_equiv_for: invalidate_hw_asid_entry "states_equiv_for P Q R S st"
  (simp: states_equiv_for_arm_hwasid_table_update)

crunch states_equiv_for: invalidate_asid "states_equiv_for P Q R S st"
  (simp: states_equiv_for_arm_asid_map_update)

lemma mol_states_equiv_for:
  "\<lbrace>\<lambda>ms. states_equiv_for P Q R S st (s\<lparr>machine_state := ms\<rparr>)\<rbrace> machine_op_lift mop \<lbrace>\<lambda>a b. states_equiv_for P Q R S st (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  unfolding machine_op_lift_def
  apply (simp add: machine_rest_lift_def split_def)
  apply (wp modify_wp)
  apply (clarsimp simp: states_equiv_for_def)
  apply (clarsimp simp: equiv_asids_def equiv_asid_def)
  apply (fastforce elim!: equiv_forE intro!: equiv_forI)
  done

lemma do_machine_op_mol_states_equiv_for:
  "invariant (do_machine_op (machine_op_lift f)) (states_equiv_for P Q R S st)"
  apply(simp add: do_machine_op_def)
  apply(wp modify_wp | simp add: split_def)+
  apply(clarify)
  apply(erule use_valid)
   apply simp
   apply(rule mol_states_equiv_for)
  by simp


(* we don't care about the relationship between virtual and hardware asids at all --
   these should be unobservable, so rightly we don't expect this one to satisfy
   reads_respects but instead the weaker property where we assert no relation on
   the return values *)
lemma find_free_hw_asid_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (find_free_hw_asid)"
  unfolding find_free_hw_asid_def fun_app_def invalidateLocalTLB_ASID_def
  apply(rule equiv_valid_2_unobservable)
     apply (wp modify_wp invalidate_hw_asid_entry_states_equiv_for
               do_machine_op_mol_states_equiv_for
               invalidate_asid_states_equiv_for dmo_wp
           | wpc
           | simp add: states_equiv_for_arm_asid_map_update
                       states_equiv_for_arm_hwasid_table_update
                       states_equiv_for_arm_next_asid_update)+
  done

lemma load_hw_asid_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (load_hw_asid asid)"

  apply(rule equiv_valid_2_unobservable)
     apply(simp add: load_hw_asid_def | wp)+
  done

lemma states_equiv_for_arch_update1:
  "\<lbrakk>arm_globals_frame A = arm_globals_frame (arch_state s);
    arm_asid_table A = arm_asid_table (arch_state s)\<rbrakk> \<Longrightarrow>
    states_equiv_for P Q R S (s\<lparr> arch_state := A\<rparr>) t =
    states_equiv_for P Q R S s t"
  apply(clarsimp simp: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def asid_pool_at_kheap)
  done

lemma states_equiv_for_arch_update2:
  "\<lbrakk>arm_globals_frame A = arm_globals_frame (arch_state s);
    arm_asid_table A = arm_asid_table (arch_state s)\<rbrakk> \<Longrightarrow>
    states_equiv_for P Q R S t (s\<lparr> arch_state := A\<rparr>) =
    states_equiv_for P Q R S t s"
  apply(rule iffI)
   apply(drule states_equiv_for_sym)
   apply(rule states_equiv_for_sym)
   apply(simp add: states_equiv_for_arch_update1)
  apply(drule states_equiv_for_sym)
  apply(rule states_equiv_for_sym)
  apply(simp add: states_equiv_for_arch_update1)
  done

lemmas states_equiv_for_arch_update = states_equiv_for_arch_update1 states_equiv_for_arch_update2

crunch states_equiv_for: store_hw_asid "states_equiv_for P Q R S st"
  (simp: states_equiv_for_arch_update)

lemma find_free_hw_asid_states_equiv_for:
  "invariant (find_free_hw_asid) (states_equiv_for P Q R S st)"
  apply(simp add: find_free_hw_asid_def)
  apply(wp modify_wp invalidate_hw_asid_entry_states_equiv_for do_machine_op_mol_states_equiv_for invalidate_asid_states_equiv_for | wpc | simp add: states_equiv_for_arm_next_asid_update invalidateLocalTLB_ASID_def)+
  done

crunch states_equiv_for: get_hw_asid "states_equiv_for P Q R S st"

lemma reads_respects_unobservable_unit_return:
  assumes f:
    "\<And> P Q R S st. \<lbrace> states_equiv_for P Q R S st \<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes g:
    "\<And> P. \<lbrace> \<lambda> s. P (cur_thread s) \<rbrace> f \<lbrace> \<lambda> rv s. P (cur_thread s) \<rbrace>"
  assumes h:
    "\<And> P. \<lbrace> \<lambda> s. P (cur_domain s) \<rbrace> f \<lbrace> \<lambda> rv s. P (cur_domain s) \<rbrace>"
  assumes j:
    "\<And> P. \<lbrace> \<lambda> s. P (scheduler_action s) \<rbrace> f \<lbrace> \<lambda> rv s. P (scheduler_action s) \<rbrace>"
  assumes k:
    "\<And> P. \<lbrace> \<lambda> s. P (work_units_completed s) \<rbrace> f \<lbrace> \<lambda> rv s. P (work_units_completed s) \<rbrace>"
  assumes l:
    "\<And> P. \<lbrace> \<lambda> s. P (irq_state_of_state s) \<rbrace> f \<lbrace> \<lambda> rv s. P (irq_state_of_state s) \<rbrace>"

  shows
    "reads_respects aag l \<top> (f::(unit,det_ext) s_monad)"
  apply(subgoal_tac "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> f")
   apply(clarsimp simp: equiv_valid_2_def equiv_valid_def2)
  apply(rule equiv_valid_2_unobservable[OF f f g g h h j j k k l l])
  done

lemma dmo_mol_irq_state_of_state[wp]:
  "\<And>P. \<lbrace>\<lambda>s. P (irq_state_of_state s) \<rbrace> do_machine_op (machine_op_lift m)
       \<lbrace>\<lambda>_ s. P (irq_state_of_state s) \<rbrace>"
  apply(wp dmo_wp | simp)+
  done

lemma arm_context_switch_reads_respects:
  "reads_respects aag l \<top> (arm_context_switch pd asid)"
  unfolding arm_context_switch_def
  apply(rule equiv_valid_guard_imp)
  apply(rule reads_respects_unobservable_unit_return)
    apply (wp do_machine_op_mol_states_equiv_for get_hw_asid_states_equiv_for
     | simp add: set_current_pd_def dsb_def isb_def writeTTBR0_def dmo_bind_valid setHardwareASID_def)+
  done

lemma arm_context_switch_states_equiv_for:
  "invariant (arm_context_switch pd asid) (states_equiv_for P Q R S st)"
  unfolding arm_context_switch_def
  apply (wp do_machine_op_mol_states_equiv_for get_hw_asid_states_equiv_for | simp add: setHardwareASID_def dmo_bind_valid set_current_pd_def dsb_def isb_def writeTTBR0_def)+
  done

lemma set_vm_root_states_equiv_for[wp]:
  "invariant (set_vm_root thread) (states_equiv_for P Q R S st)"
  unfolding set_vm_root_def catch_def fun_app_def set_current_pd_def isb_def dsb_def writeTTBR0_def
  apply (wp (once) hoare_drop_imps
        |wp do_machine_op_mol_states_equiv_for hoare_vcg_all_lift arm_context_switch_states_equiv_for hoare_whenE_wp
        | wpc | simp add: dmo_bind_valid if_apply_def2)+
  done

lemma set_vm_root_reads_respects:
  "reads_respects aag l \<top> (set_vm_root tcb)"
  by (rule reads_respects_unobservable_unit_return) wp+

lemma get_pte_reads_respects:
  "reads_respects aag l (K (is_subject aag (ptr && ~~ mask pt_bits))) (get_pte ptr)"
  unfolding get_pte_def fun_app_def
  by (wpsimp wp: get_pt_reads_respects)

lemma gets_cur_thread_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag (=) \<top> (gets cur_thread)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE affects_equivE)
  done

crunch states_equiv_for: set_vm_root_for_flush "states_equiv_for P Q R S st"
  (wp: do_machine_op_mol_states_equiv_for ignore: do_machine_op simp: set_current_pd_def)

lemma set_vm_root_for_flush_reads_respects:
  "reads_respects aag l (is_subject aag \<circ> cur_thread)
    (set_vm_root_for_flush pd asid)"
  unfolding set_vm_root_for_flush_def fun_app_def set_current_pd_def
  apply(rule equiv_valid_guard_imp)
  apply (wp (once) hoare_drop_imps
        |wp arm_context_switch_reads_respects dmo_mol_reads_respects
            hoare_vcg_all_lift gets_cur_thread_ev get_cap_rev
        |wpc)+
  apply (clarsimp simp: reads_equiv_def)
  done

crunch states_equiv_for: flush_table "states_equiv_for P Q R S st"
  (wp: crunch_wps do_machine_op_mol_states_equiv_for ignore: do_machine_op simp: invalidateLocalTLB_ASID_def crunch_simps)

crunch sched_act: flush_table "\<lambda> s. P (scheduler_action s)"
  (wp: crunch_wps simp: crunch_simps)

crunch wuc: flush_table "\<lambda> s. P (work_units_completed s)"
  (wp: crunch_wps simp: crunch_simps)

lemma flush_table_reads_respects:
  "reads_respects aag l \<top> (flush_table pd asid vptr pt)"
  apply(rule reads_respects_unobservable_unit_return)
       apply(rule flush_table_states_equiv_for)
      apply(rule flush_table_cur_thread)
     apply(rule flush_table_cur_domain)
    apply(rule flush_table_sched_act)
   apply(rule flush_table_wuc)
  apply wp
  done

lemma page_table_mapped_reads_respects:
  "reads_respects aag l
    (pas_refined aag and pspace_aligned
     and valid_vspace_objs and K (is_subject_asid aag asid))
  (page_table_mapped asid vaddr pt)"
  unfolding page_table_mapped_def catch_def fun_app_def
  apply(wp get_pde_rev | wpc | simp)+
     apply(wp find_pd_for_asid_reads_respects | simp)+
  done


lemma unmap_page_table_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs and K (is_subject_asid aag asid))
   (unmap_page_table asid vaddr pt)"
  unfolding unmap_page_table_def fun_app_def page_table_mapped_def
  apply(wp find_pd_for_asid_pd_slot_authorised
           dmo_mol_reads_respects store_pde_reads_respects get_pde_rev get_pde_wp
           flush_table_reads_respects find_pd_for_asid_reads_respects hoare_vcg_all_lift_R catch_ev
       | wpc | simp add: cleanByVA_PoU_def | wp (once) hoare_drop_imps)+
  done


lemma perform_page_table_invocation_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs and K (authorised_page_table_inv aag pti))
    (perform_page_table_invocation pti)"
  unfolding perform_page_table_invocation_def fun_app_def cleanCacheRange_PoU_def
  apply(rule equiv_valid_guard_imp)
  apply(wp dmo_cacheRangeOp_reads_respects dmo_mol_reads_respects store_pde_reads_respects
           set_cap_reads_respects
           mapM_x_ev'' store_pte_reads_respects unmap_page_table_reads_respects get_cap_rev
       | wpc | simp add: cleanByVA_PoU_def)+
  apply(clarsimp simp: authorised_page_table_inv_def)
  apply(case_tac pti)
  apply auto
  done

lemma do_flush_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (do_flush typ start end pstart))"
  apply (rule equiv_valid_guard_imp)
   apply (cases "typ")
      apply (wp dmo_mol_reads_respects dmo_cacheRangeOp_reads_respects | simp add: do_flush_def cache_machine_op_defs do_flush_defs dmo_bind_ev when_def | rule conjI | clarsimp)+
      done

lemma perform_page_directory_invocation_reads_respects:
  "reads_respects aag l (is_subject aag \<circ> cur_thread) (perform_page_directory_invocation pdi)"
  unfolding perform_page_directory_invocation_def
  apply (cases pdi)
  apply (wp do_flush_reads_respects set_vm_root_reads_respects set_vm_root_for_flush_reads_respects | simp add: when_def requiv_cur_thread_eq split del: if_split | wp (once) hoare_drop_imps | clarsimp)+
  done

lemma throw_on_false_reads_respects:
  "reads_respects aag l P f \<Longrightarrow>
  reads_respects aag l P (throw_on_false ex f)"
  unfolding throw_on_false_def fun_app_def unlessE_def
  apply(wp | simp)+
  done

lemma check_mapping_pptr_reads_respects:
  "reads_respects aag l
    (K (\<forall>x.   (tablePtr = Inl x \<longrightarrow> is_subject aag (x && ~~ mask pt_bits))
            \<and> (tablePtr = Inr x \<longrightarrow> is_subject aag (x && ~~ mask pd_bits))))
  (check_mapping_pptr pptr pgsz tablePtr)"
  unfolding check_mapping_pptr_def fun_app_def
  apply(rule equiv_valid_guard_imp)
   apply(wp get_pte_reads_respects get_pde_rev | wpc)+
  apply(simp)
  done

lemma lookup_pt_slot_reads_respects:
  "reads_respects aag l (K (is_subject aag (lookup_pd_slot pd vptr && ~~ mask pd_bits))) (lookup_pt_slot pd vptr)"
  unfolding lookup_pt_slot_def fun_app_def
  apply(wp get_pde_rev | wpc | simp)+
  done

crunch sched_act: flush_page "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch wuc: flush_page "\<lambda>s. P (work_units_completed s)"
  (wp: crunch_wps simp: if_apply_def2)

crunch states_equiv_for: flush_page "states_equiv_for P Q R S st"
  (wp: do_machine_op_mol_states_equiv_for crunch_wps ignore: do_machine_op simp: invalidateLocalTLB_VAASID_def if_apply_def2)

lemma flush_page_reads_respects:
  "reads_respects aag l \<top> (flush_page page_size pd asid vptr)"
  apply (blast intro: reads_respects_unobservable_unit_return flush_page_states_equiv_for flush_page_cur_thread flush_page_cur_domain flush_page_sched_act flush_page_wuc flush_page_irq_state_of_state)
  done

(* clagged some help from unmap_page_respects in Arch_AC *)
lemma unmap_page_reads_respects:
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs and K (is_subject_asid aag asid \<and> vptr < kernel_base)) (unmap_page pgsz asid vptr pptr)"
  unfolding unmap_page_def catch_def fun_app_def cleanCacheRange_PoU_def
  apply (simp add: unmap_page_def swp_def cong: vmpage_size.case_cong)
  apply(wp dmo_mol_reads_respects dmo_cacheRangeOp_reads_respects
           store_pte_reads_respects[simplified]
           check_mapping_pptr_reads_respects
           throw_on_false_reads_respects  lookup_pt_slot_reads_respects
           lookup_pt_slot_authorised lookup_pt_slot_authorised2
           store_pde_reads_respects[simplified] flush_page_reads_respects
           find_pd_for_asid_reads_respects find_pd_for_asid_pd_slot_authorised
           mapM_ev''[
                     where m = "(\<lambda>a. store_pte a InvalidPTE)"
                       and P = "\<lambda>x s. is_subject aag (x && ~~ mask pt_bits)"]
           mapM_ev''[where m = "(\<lambda>a. store_pde a InvalidPDE)"
                       and P = "\<lambda>x s. is_subject aag (x && ~~ mask pd_bits)"]

       | wpc
       | simp add: is_aligned_6_masks is_aligned_mask[symmetric] cleanByVA_PoU_def
       | wp (once) hoare_drop_imps)+
  done

lemma dmo_mol_2_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (machine_op_lift mop >>= (\<lambda> y. machine_op_lift mop')))"
  apply(rule use_spec_ev)
  apply(rule do_machine_op_spec_reads_respects)
  apply wp
     apply(rule machine_op_lift_ev)
    apply(rule machine_op_lift_ev)
   apply(rule wp_post_taut)
  by (wp | simp)+

lemma tl_subseteq:
  "set (tl xs) \<subseteq> set xs"
  by (induct xs, auto)


crunch states_equiv_for: invalidate_tlb_by_asid "states_equiv_for P Q R S st"
  (wp: do_machine_op_mol_states_equiv_for ignore: do_machine_op simp: invalidateLocalTLB_ASID_def)


crunch sched_act[wp]: invalidate_tlb_by_asid "\<lambda>s. P (scheduler_action s)"
crunch wuc[wp]: invalidate_tlb_by_asid "\<lambda>s. P (work_units_completed s)"

lemma invalidate_tlb_by_asid_reads_respects:
  "reads_respects aag l (\<lambda>_. True) (invalidate_tlb_by_asid asid)"
  apply(rule reads_respects_unobservable_unit_return)
      apply (rule invalidate_tlb_by_asid_states_equiv_for)
     apply wp+
  done


lemma get_master_pte_reads_respects:
  "reads_respects aag l (K (is_subject aag (p && ~~ mask pt_bits))) (get_master_pte p)"
  unfolding get_master_pte_def
  apply(wp get_pte_reads_respects | wpc | simp
       | wp (once) hoare_drop_imps)+
  apply(fastforce simp: pt_bits_def pageBits_def mask_lower_twice)
  done


lemma get_master_pde_reads_respects:
  "reads_respects aag l (K (is_subject aag (x && ~~ mask pd_bits))) (get_master_pde x)"
  unfolding get_master_pde_def
  apply(wp get_pde_rev | wpc | simp
       | wp (once) hoare_drop_imps)+
  apply(fastforce simp: pd_bits_def pageBits_def mask_lower_twice)
  done


abbreviation(input) aag_can_read_label where
  "aag_can_read_label aag l \<equiv> l \<in> subjectReads (pasPolicy aag) (pasSubject aag)"

definition labels_are_invisible where
  "labels_are_invisible aag l L \<equiv>
         (\<forall> d \<in> L. \<not> aag_can_read_label aag d) \<and>
         (aag_can_affect_label aag l \<longrightarrow>
              (\<forall> d \<in> L. d \<notin> subjectReads (pasPolicy aag) l))"


lemma equiv_but_for_reads_equiv:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "\<lbrakk>labels_are_invisible aag l L; equiv_but_for_labels aag L s s'\<rbrakk> \<Longrightarrow>
   reads_equiv aag s s'"
  apply(simp add: reads_equiv_def2)
  apply(rule conjI)
   apply(clarsimp simp: labels_are_invisible_def equiv_but_for_labels_def)
   apply(rule states_equiv_forI)
             apply(fastforce intro: equiv_forI elim: states_equiv_forE equiv_forD)+
       apply((auto intro!: equiv_forI elim!: states_equiv_forE elim!: equiv_forD
             |clarsimp simp: o_def)+)[1]
      apply(fastforce intro: equiv_forI elim: states_equiv_forE equiv_forD)+
    apply(fastforce simp: equiv_asids_def elim: states_equiv_forE elim: equiv_forD)
   apply (clarsimp simp: equiv_for_def states_equiv_for_def disjoint_iff_not_equal)
   apply (metis domains_distinct[THEN pas_domains_distinct_inj])
  apply(fastforce simp: equiv_but_for_labels_def)
  done

lemma equiv_but_for_affects_equiv:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "\<lbrakk>labels_are_invisible aag l L; equiv_but_for_labels aag L s s'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l s s'"
  apply(subst affects_equiv_def2)
  apply(clarsimp simp: labels_are_invisible_def equiv_but_for_labels_def aag_can_affect_label_def)
  apply(rule states_equiv_forI)
         apply(fastforce intro!: equiv_forI elim!: states_equiv_forE equiv_forD)+
   apply(fastforce simp: equiv_asids_def elim!: states_equiv_forE elim!: equiv_forD)
  apply (clarsimp simp: equiv_for_def states_equiv_for_def disjoint_iff_not_equal)
  apply (metis domains_distinct[THEN pas_domains_distinct_inj])
  done

(* consider rewriting the return-value assumption using equiv_valid_rv_inv *)
lemma ev2_invisible:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "\<lbrakk>labels_are_invisible aag l L;
    labels_are_invisible aag l L';
    modifies_at_most aag L Q f;
    modifies_at_most aag L' Q' g;
    \<forall> s t. P s \<and> P' t \<longrightarrow> (\<forall>(rva,s') \<in> fst (f s). \<forall>(rvb,t') \<in> fst (g t). W rva rvb)\<rbrakk>
  \<Longrightarrow>
  equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
    W (P and Q) (P' and Q') f g"
  apply(clarsimp simp: equiv_valid_2_def)
  apply(rule conjI)
   apply blast
  apply(drule_tac s=s in modifies_at_mostD, assumption+)
  apply(drule_tac s=t in modifies_at_mostD, assumption+)
  apply(frule (1) equiv_but_for_reads_equiv[OF domains_distinct])
  apply(frule_tac s=t in equiv_but_for_reads_equiv[OF domains_distinct], assumption)
  apply(drule (1) equiv_but_for_affects_equiv[OF domains_distinct])
  apply(drule_tac s=t in equiv_but_for_affects_equiv[OF domains_distinct], assumption)
  apply(blast intro: reads_equiv_trans reads_equiv_sym affects_equiv_trans affects_equiv_sym)
  done

lemma modify_det:
  "det (modify f)"
  apply(clarsimp simp: det_def modify_def get_def put_def bind_def)
  done

lemma dummy_kheap_update:
  "st = st\<lparr> kheap := kheap st \<rparr>"
  by simp

(* we need to know we're not doing an asid pool update, or else this could affect
   what some other domain sees *)
lemma set_object_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and (\<lambda> s. \<not> asid_pool_at ptr s) and
    K ((\<forall> asid_pool. obj \<noteq> ArchObj (ASIDPool asid_pool)) \<and> pasObjectAbs aag ptr \<in> L)\<rbrace>
   set_object ptr obj
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply(clarsimp simp: equiv_but_for_labels_def)
  apply(subst dummy_kheap_update[where st=st])
  apply(rule states_equiv_for_non_asid_pool_kheap_update)
     apply assumption
    apply(fastforce intro: equiv_forI elim: states_equiv_forE equiv_forE)
   apply(fastforce simp: non_asid_pool_kheap_update_def)
  apply(clarsimp simp: non_asid_pool_kheap_update_def asid_pool_at_kheap)
  done


lemma get_tcb_not_asid_pool_at:
  "get_tcb ref s = Some y \<Longrightarrow> \<not> asid_pool_at ref s"
  by(fastforce simp: get_tcb_def asid_pool_at_kheap)

lemma as_user_set_register_ev2:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "labels_are_invisible aag l (pasObjectAbs aag ` {thread,thread'}) \<Longrightarrow>
   equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=) \<top> \<top> (as_user thread (setRegister x y)) (as_user thread' (setRegister a b))"
  apply(simp add: as_user_def)
  apply(rule equiv_valid_2_guard_imp)
   apply(rule_tac L="{pasObjectAbs aag thread}" and L'="{pasObjectAbs aag thread'}" and Q="\<top>" and Q'="\<top>" in ev2_invisible[OF domains_distinct])
        apply(simp add: labels_are_invisible_def)+
      apply((rule modifies_at_mostI | wp set_object_equiv_but_for_labels | simp add: split_def | fastforce dest: get_tcb_not_asid_pool_at)+)[2]
    apply auto
  done


lemma reads_affects_equiv_kheap_eq:
  "\<lbrakk>reads_equiv aag s s'; affects_equiv aag l s s';
    aag_can_affect aag l x \<or> aag_can_read aag x\<rbrakk> \<Longrightarrow>
   kheap s x = kheap s' x"
  apply(erule disjE)
   apply(fastforce elim: affects_equivE equiv_forE)
  apply(fastforce elim: reads_equivE equiv_forE)
  done

lemma reads_affects_equiv_get_tcb_eq:
  "\<lbrakk>aag_can_read aag thread \<or> aag_can_affect aag l thread;
    reads_equiv aag s t; affects_equiv aag l s t\<rbrakk> \<Longrightarrow>
   get_tcb thread s = get_tcb thread t"
  apply (fastforce simp: get_tcb_def split: kernel_object.splits option.splits simp: reads_affects_equiv_kheap_eq)
  done

lemma as_user_set_register_reads_respects':
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects aag l \<top> (as_user thread (setRegister x y))"
  apply (case_tac "aag_can_read aag thread \<or> aag_can_affect aag l thread")
   apply (simp add: as_user_def split_def)
   apply (rule gen_asm_ev)
   apply (wp set_object_reads_respects select_f_ev gets_the_ev)
   apply (auto intro: reads_affects_equiv_get_tcb_eq det_setRegister)[1]
  apply(simp add: equiv_valid_def2)
  apply(rule as_user_set_register_ev2[OF domains_distinct])
  apply(simp add: labels_are_invisible_def)
  done

lemma as_user_get_register_reads_respects:
  "reads_respects aag l (K (is_subject aag thread)) (as_user thread (getRegister reg))"
  apply (simp add: as_user_def split_def)
  apply (wp set_object_reads_respects select_f_ev gets_the_ev)
  apply (auto intro: reads_affects_equiv_get_tcb_eq det_getRegister)[1]
  done

lemma set_message_info_reads_respects:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "reads_respects aag l \<top>
    (set_message_info thread info)"
  unfolding set_message_info_def fun_app_def
  apply(rule as_user_set_register_reads_respects'[OF domains_distinct])
  done

lemma equiv_valid_get_assert:
  "equiv_valid_inv I A P f \<Longrightarrow>
   equiv_valid_inv I A P (get >>= (\<lambda> s. assert (g s) >>= (\<lambda> y. f)))"
  apply(subst equiv_valid_def2)
  apply(rule_tac W="\<top>\<top>" in equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp)
     apply(rule equiv_valid_rv_trivial)
     apply wpsimp+
   apply(rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
      apply(simp add: equiv_valid_def2)
     apply(rule assert_ev2)
     apply (wp | simp)+
  done

lemma store_word_offs_reads_respects:
  "reads_respects aag l \<top> (store_word_offs ptr offs v)"
  apply(simp add: store_word_offs_def)
  apply(rule equiv_valid_get_assert)
  apply(simp add: storeWord_def)
  apply(simp add: do_machine_op_bind)
  apply(wp)
     apply(rule use_spec_ev)
     apply(rule do_machine_op_spec_reads_respects)
     apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad)
     apply(fastforce intro: equiv_forI elim: equiv_forE)
    apply(rule use_spec_ev | rule do_machine_op_spec_reads_respects
         | simp add: spec_equiv_valid_def | rule assert_ev2 | wp modify_wp)+
  done


lemma set_mrs_reads_respects:
  "reads_respects aag l (K (aag_can_read aag thread \<or> aag_can_affect aag l thread)) (set_mrs thread buf msgs)"
  apply(simp add: set_mrs_def cong: option.case_cong_weak)
  apply(wp mapM_x_ev' store_word_offs_reads_respects set_object_reads_respects
       | wpc | simp add: split_def split del: if_split add: zipWithM_x_mapM_x)+
  apply(auto intro: reads_affects_equiv_get_tcb_eq)
  done

lemma perform_page_invocation_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pas_refined aag and K (authorised_page_inv aag pgi) and valid_page_inv pgi and valid_vspace_objs and pspace_aligned and is_subject aag \<circ> cur_thread) (perform_page_invocation pgi)"
  unfolding perform_page_invocation_def fun_app_def when_def cleanCacheRange_PoU_def
  apply(rule equiv_valid_guard_imp)
  apply wpc
      apply(simp add: mapM_discarded swp_def)
      apply (wp dmo_mol_reads_respects dmo_cacheRangeOp_reads_respects
                mapM_x_ev'' store_pte_reads_respects
                set_cap_reads_respects mapM_ev'' store_pde_reads_respects
                unmap_page_reads_respects set_vm_root_reads_respects
                dmo_mol_2_reads_respects set_vm_root_for_flush_reads_respects get_cap_rev
                do_flush_reads_respects invalidate_tlb_by_asid_reads_respects
                get_master_pte_reads_respects get_master_pde_reads_respects
                set_mrs_reads_respects set_message_info_reads_respects
            | simp add: cleanByVA_PoU_def pte_check_if_mapped_def pde_check_if_mapped_def  | wpc | wp (once) hoare_drop_imps[where R="\<lambda> r s. r"])+
  apply(clarsimp simp: authorised_page_inv_def valid_page_inv_def)
  apply (auto simp: cte_wp_at_caps_of_state valid_slots_def cap_auth_conferred_def
                    update_map_data_def is_page_cap_def authorised_slots_def
                    valid_page_inv_def valid_cap_simps
             dest!: bspec[OF _ rev_subsetD[OF _ tl_subseteq]]
       | auto dest!: clas_caps_of_state
               simp: cap_links_asid_slot_def label_owns_asid_slot_def
              dest!: pas_refined_Control
       | (frule aag_can_read_self, simp)+)+
  done

lemma equiv_asids_arm_asid_table_update:
  "\<lbrakk>equiv_asids R s t; kheap s pool_ptr = kheap t pool_ptr\<rbrakk> \<Longrightarrow>
   equiv_asids R (s\<lparr>arch_state := arch_state s
                   \<lparr>arm_asid_table := arm_asid_table (arch_state s)
                      (asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)
              (t\<lparr>arch_state := arch_state t
                   \<lparr>arm_asid_table := arm_asid_table (arch_state t)
                      (asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)"
  apply(clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)
  done


lemma arm_asid_table_update_reads_respects:
  "reads_respects aag l (K (is_subject aag pool_ptr))
        (do r \<leftarrow> gets (arm_asid_table \<circ> arch_state);
            modify
             (\<lambda>s. s\<lparr>arch_state := arch_state s
                      \<lparr>arm_asid_table := r(asid_high_bits_of asid \<mapsto> pool_ptr)\<rparr>\<rparr>)
         od)"
  apply(simp add: equiv_valid_def2)
  apply(rule_tac W="\<top>\<top>" and Q="\<lambda> rv s. is_subject aag pool_ptr \<and> rv = arm_asid_table (arch_state s)" in equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
     apply wpsimp+
   apply(rule modify_ev2)
   apply clarsimp
   apply (drule(1) is_subject_kheap_eq[rotated])
   apply (auto simp add: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_for_def intro!: equiv_asids_arm_asid_table_update)
   done


lemma my_bind_rewrite_lemma:
  "(f >>= g) =  (f >>= (\<lambda> r. (g r) >>= (\<lambda> x. return ())))"
  apply simp
  done

lemma delete_objects_reads_respects:
  "reads_respects aag l (\<lambda>_. True) (delete_objects p b)"
  apply (simp add: delete_objects_def)
  apply (wp detype_reads_respects dmo_freeMemory_reads_respects)
  done

lemma another_hacky_rewrite:
  "do a; (do x \<leftarrow> f; g x od); h; j od = do a; (f >>= g >>= (\<lambda>_. h)); j od"
  apply(simp add: bind_assoc[symmetric])
  done

lemma perform_asid_control_invocation_reads_respects:
  notes K_bind_ev[wp del]
  shows
  "reads_respects aag l (K (authorised_asid_control_inv aag aci))
  (perform_asid_control_invocation aci)"
  unfolding perform_asid_control_invocation_def
  apply(rule gen_asm_ev)
  apply(rule equiv_valid_guard_imp)
   (* we do some hacky rewriting here to separate out the bit that does interesting stuff from the rest *)
   apply(subst (6) my_bind_rewrite_lemma)
   apply(subst (1) bind_assoc[symmetric])
   apply(subst another_hacky_rewrite)
   apply(subst another_hacky_rewrite)
   apply(wpc)
   apply(rule bind_ev)
     apply(rule K_bind_ev)
     apply(rule_tac P'=\<top> in bind_ev)
       apply(rule K_bind_ev)
       apply(rule bind_ev)
         apply(rule bind_ev)
           apply(rule return_ev)
          apply(rule K_bind_ev)
          apply simp
          apply(rule arm_asid_table_update_reads_respects)
         apply (wp cap_insert_reads_respects retype_region_reads_respects
                   set_cap_reads_respects delete_objects_reads_respects get_cap_rev
               | simp add: authorised_asid_control_inv_def)+
  apply(auto dest!: is_aligned_no_overflow)
  done


lemma set_asid_pool_reads_respects:
  "reads_respects aag l \<top> (set_asid_pool ptr pool)"
  unfolding set_asid_pool_def
  by (rule set_object_reads_respects)

lemma perform_asid_pool_invocation_reads_respects:
  "reads_respects aag l (pas_refined aag and K (authorised_asid_pool_inv aag api))  (perform_asid_pool_invocation api)"
  unfolding perform_asid_pool_invocation_def
  apply(rule equiv_valid_guard_imp)
   apply(wp set_asid_pool_reads_respects set_cap_reads_respects
            get_asid_pool_rev get_cap_auth_wp[where aag=aag] get_cap_rev
        | wpc | simp)+
  apply(clarsimp simp: authorised_asid_pool_inv_def)
  done

lemma arch_perform_invocation_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs and
                         authorised_arch_inv aag ai and valid_arch_inv ai and is_subject aag \<circ> cur_thread)
    (arch_perform_invocation ai)"
  unfolding arch_perform_invocation_def fun_app_def
  apply(wp perform_page_table_invocation_reads_respects perform_page_directory_invocation_reads_respects perform_page_invocation_reads_respects perform_asid_control_invocation_reads_respects perform_asid_pool_invocation_reads_respects | wpc)+
  apply(case_tac ai)
  apply(auto simp: authorised_arch_inv_def valid_arch_inv_def)
  done

lemma equiv_asids_arm_asid_table_delete:
  "\<lbrakk>equiv_asids R s t\<rbrakk> \<Longrightarrow>
   equiv_asids R (s\<lparr>arch_state := arch_state s
                   \<lparr>arm_asid_table :=
                        \<lambda>a. if a = asid_high_bits_of asid then None
                             else arm_asid_table (arch_state s) a\<rparr>\<rparr>)
              (t\<lparr>arch_state := arch_state t
                   \<lparr>arm_asid_table :=
                        \<lambda>a. if a = asid_high_bits_of asid then None
                             else arm_asid_table (arch_state t) a\<rparr>\<rparr>)"
  apply(clarsimp simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)
  done

lemma arm_asid_table_delete_ev2:
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
     \<top>\<top> (\<lambda>s. rv = arm_asid_table (arch_state s))
        (\<lambda>s. rv' = arm_asid_table (arch_state s))
          (modify
             (\<lambda>s. s\<lparr>arch_state := arch_state s
                      \<lparr>arm_asid_table :=
                        \<lambda>a. if a = asid_high_bits_of base then None
                             else rv a\<rparr>\<rparr>))
          (modify
             (\<lambda>s. s\<lparr>arch_state := arch_state s
                      \<lparr>arm_asid_table :=
                        \<lambda>a. if a = asid_high_bits_of base then None
                             else rv' a\<rparr>\<rparr>))"
  apply(rule modify_ev2)
  (* slow 15s *)
  by(auto simp: reads_equiv_def2 affects_equiv_def2
          intro!: states_equiv_forI elim!: states_equiv_forE
          intro!: equiv_forI elim!: equiv_forE
          intro!: equiv_asids_arm_asid_table_delete
          elim: is_subject_kheap_eq[simplified reads_equiv_def2 states_equiv_for_def, rotated])

crunch states_equiv_for: invalidate_asid_entry "states_equiv_for P Q R S st"
crunch sched_act: invalidate_asid_entry "\<lambda>s. P (scheduler_action s)"
crunch wuc: invalidate_asid_entry "\<lambda>s. P (work_units_completed s)"
crunch states_equiv_for: flush_space "states_equiv_for P Q R S st"
  (wp: mol_states_equiv_for dmo_wp ignore: do_machine_op simp: invalidateLocalTLB_ASID_def cleanCaches_PoU_def dsb_def invalidate_I_PoU_def clean_D_PoU_def)
crunch sched_act: flush_space "\<lambda>s. P (scheduler_action s)"
crunch wuc: flush_space "\<lambda>s. P (work_units_completed s)"




lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq':
  "\<lbrakk>(\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base \<longrightarrow> is_subject_asid aag asid');reads_equiv aag s t\<rbrakk> \<Longrightarrow>
    arm_asid_table (arch_state s) (asid_high_bits_of base) =
    arm_asid_table (arch_state t) (asid_high_bits_of base)"
  apply (insert asid_high_bits_0_eq_1)
   apply(case_tac "base = 0")
    apply(subgoal_tac "is_subject_asid aag 1")
    apply simp
    apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq[where aag=aag])
    apply (erule_tac x=1 in allE)
    apply simp+
    apply (rule requiv_arm_asid_table_asid_high_bits_of_asid_eq[where aag=aag])
    apply (erule_tac x=base in allE)
    apply simp+
done


lemma delete_asid_pool_reads_respects:
  "reads_respects aag l (K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base \<longrightarrow> is_subject_asid aag asid')) (delete_asid_pool base ptr)"
  unfolding delete_asid_pool_def
  apply(rule equiv_valid_guard_imp)
   apply(rule bind_ev)
     apply(simp)
     apply(subst equiv_valid_def2)
     apply(rule_tac W="\<top>\<top>" and Q="\<lambda>rv s. rv = arm_asid_table (arch_state s)
        \<and> (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of base \<longrightarrow> is_subject_asid aag asid')"
                     in equiv_valid_rv_bind)
       apply(rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
        apply(wp, simp)
      apply(simp add: when_def)
      apply(clarsimp | rule conjI)+
        apply(subst bind_assoc[symmetric])
        apply(subst (3) bind_assoc[symmetric])
        apply(rule equiv_valid_2_guard_imp)
          apply(rule equiv_valid_2_bind)
             apply(rule equiv_valid_2_bind)
                apply(rule equiv_valid_2_unobservable)
                           apply(wp set_vm_root_states_equiv_for)+
               apply(rule arm_asid_table_delete_ev2)
              apply(wp)+
            apply(rule equiv_valid_2_unobservable)
                       apply(wp mapM_wp' invalidate_asid_entry_states_equiv_for flush_space_states_equiv_for invalidate_asid_entry_cur_thread invalidate_asid_entry_sched_act invalidate_asid_entry_wuc flush_space_cur_thread flush_space_sched_act flush_space_wuc | clarsimp)+
       apply( wp return_ev2 |
              drule (1) requiv_arm_asid_table_asid_high_bits_of_asid_eq' |
              clarsimp   | rule conjI |
              simp add: equiv_valid_2_def )+
done

definition states_equal_except_kheap_asid :: "det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equal_except_kheap_asid s s' \<equiv>
     equiv_machine_state \<top> (machine_state s) (machine_state s') \<and>
     equiv_for \<top> cdt s s' \<and>
     equiv_for \<top> cdt_list s s' \<and>
     equiv_for \<top> ekheap s s' \<and>
     equiv_for \<top> ready_queues s s' \<and>
     equiv_for \<top> is_original_cap s s' \<and>
     equiv_for \<top> interrupt_states s s' \<and>
     equiv_for \<top> interrupt_irq_node s s' \<and>
     cur_thread s = cur_thread s' \<and>
     cur_domain s = cur_domain s' \<and>
     scheduler_action s = scheduler_action s' \<and>
     work_units_completed s = work_units_completed s' \<and>
     irq_state_of_state s = irq_state_of_state s'"

lemma set_asid_pool_state_equal_except_kheap:
  "((), s') \<in> fst (set_asid_pool ptr pool s) \<Longrightarrow>
    states_equal_except_kheap_asid s s' \<and>
    (\<forall>p. p \<noteq> ptr \<longrightarrow> kheap s p = kheap s' p) \<and>
    kheap s' ptr = Some (ArchObj (ASIDPool pool)) \<and>
    (\<forall>asid. asid \<noteq> 0 \<longrightarrow>
      arm_asid_table (arch_state s) (asid_high_bits_of asid) =
      arm_asid_table (arch_state s') (asid_high_bits_of asid) \<and>
      (\<forall>pool_ptr. arm_asid_table (arch_state s) (asid_high_bits_of asid) =
        Some pool_ptr \<longrightarrow>
          asid_pool_at pool_ptr s = asid_pool_at pool_ptr s' \<and>
          (\<forall>asid_pool asid_pool'. pool_ptr \<noteq> ptr \<longrightarrow>
            kheap s pool_ptr = Some (ArchObj (ASIDPool asid_pool)) \<and>
            kheap s' pool_ptr = Some (ArchObj (ASIDPool asid_pool')) \<longrightarrow>
              asid_pool (ucast asid) = asid_pool' (ucast asid))))"
  by (clarsimp simp: set_asid_pool_def put_def bind_def set_object_def get_object_def gets_def
                     get_def return_def assert_def fail_def states_equal_except_kheap_asid_def
                     equiv_for_def obj_at_def
              split: if_split_asm)

lemma set_asid_pool_delete_ev2:
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
     \<top>\<top> (\<lambda>s. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some a \<and>
            kheap s a = Some (ArchObj (ASIDPool pool)) \<and>
            asid \<noteq> 0 \<and> is_subject_asid aag asid)
        (\<lambda>s. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some a \<and>
            kheap s a = Some (ArchObj (ASIDPool pool')) \<and>
            asid \<noteq> 0 \<and> is_subject_asid aag asid)
          (set_asid_pool a (pool(ucast asid := None)))
          (set_asid_pool a (pool'(ucast asid := None)))"
  apply(clarsimp simp: equiv_valid_2_def)
  apply(frule_tac s'=b in set_asid_pool_state_equal_except_kheap)
  apply(frule_tac s'=ba in set_asid_pool_state_equal_except_kheap)
  apply(clarsimp simp: states_equal_except_kheap_asid_def)
  apply(rule conjI)
   apply(clarsimp simp: states_equiv_for_def reads_equiv_def equiv_for_def | rule conjI)+
     apply(case_tac "x=a")
      apply(clarsimp)
     apply(fastforce)
    apply(clarsimp simp: equiv_asids_def equiv_asid_def | rule conjI)+
     apply(case_tac "pool_ptr = a")
      apply(clarsimp)
      apply(erule_tac x="pasASIDAbs aag asid" in ballE)
       apply(clarsimp)
       apply(erule_tac x=asid in allE)+
       apply(clarsimp)
      apply(drule aag_can_read_own_asids, simp)
     apply(erule_tac x="pasASIDAbs aag asida" in ballE)
      apply(clarsimp)
      apply(erule_tac x=asida in allE)+
      apply(clarsimp)
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac "pool_ptr=a")
     apply(erule_tac x="pasASIDAbs aag asida" in ballE)
      apply(clarsimp)+
  apply(clarsimp simp: affects_equiv_def equiv_for_def states_equiv_for_def | rule conjI)+
   apply(case_tac "x=a")
    apply(clarsimp)
   apply(fastforce)
  apply(clarsimp simp: equiv_asids_def equiv_asid_def | rule conjI)+
   apply(case_tac "pool_ptr=a")
    apply(clarsimp)
    apply(erule_tac x=asid in allE)+
    apply(clarsimp simp: asid_pool_at_kheap)
   apply(erule_tac x=asida in allE)+
   apply(clarsimp)
  apply(clarsimp)
  apply(case_tac "pool_ptr=a")
   apply(clarsimp)+
  done

lemma delete_asid_reads_respects:
  "reads_respects aag l (K (asid \<noteq> 0 \<and> is_subject_asid aag asid))
    (delete_asid asid pd)"
  unfolding delete_asid_def
  apply(subst equiv_valid_def2)
  apply(rule_tac W="\<top>\<top>" and Q="\<lambda>rv s. rv = arm_asid_table (arch_state s)
        \<and> is_subject_asid aag asid \<and> asid \<noteq> 0" in equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
     apply(wp, simp)
   apply(case_tac "rv (asid_high_bits_of asid) =
                   rv' (asid_high_bits_of asid)")
    apply(simp)
    apply(case_tac "rv' (asid_high_bits_of asid)")
     apply(simp)
     apply(wp return_ev2, simp)
    apply(simp)
    apply(rule equiv_valid_2_guard_imp)
    apply(rule_tac R'="\<lambda>rv rv'. rv (ucast asid) = rv' (ucast asid)"
                in equiv_valid_2_bind)
       apply(simp add: when_def)
       apply(clarsimp | rule conjI)+
        apply(rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
           apply(rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
              apply(rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
                 apply(subst equiv_valid_def2[symmetric])
                 apply(rule reads_respects_unobservable_unit_return)
                  apply(wp set_vm_root_states_equiv_for)+
                apply(rule set_asid_pool_delete_ev2)
               apply(wp)+
             apply(rule equiv_valid_2_unobservable)
                apply(wp invalidate_asid_entry_states_equiv_for
                         invalidate_asid_entry_cur_thread)+
            apply(simp add: invalidate_asid_entry_def
                | wp invalidate_asid_kheap invalidate_hw_asid_entry_kheap
                     load_hw_asid_kheap)+
          apply(rule equiv_valid_2_unobservable)
             apply(wp flush_space_states_equiv_for flush_space_cur_thread)+
         apply(wp load_hw_asid_kheap | simp add: flush_space_def | wpc)+
       apply(clarsimp | rule return_ev2)+
      apply(rule equiv_valid_2_guard_imp)
        apply(wp get_asid_pool_revrv)
       apply(simp)+
     apply(wp)+
   apply(clarsimp simp: obj_at_def)+
   apply(clarsimp simp: equiv_valid_2_def reads_equiv_def equiv_asids_def equiv_asid_def states_equiv_for_def)
   apply(erule_tac x="pasASIDAbs aag asid" in ballE)
    apply(clarsimp)
   apply(drule aag_can_read_own_asids)
   apply(clarsimp | wpsimp)+
   done


subsection "globals_equiv"


lemma set_simple_ko_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_simple_ko_def
  apply(wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre] get_object_wp
             simp: partial_inv_def)+
  apply(fastforce simp: obj_at_def valid_ko_at_arm_def)
  done

lemma set_endpoint_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding set_simple_ko_def set_object_def
  apply(wpsimp wp: get_object_wp
        simp: partial_inv_def a_type_def obj_at_def valid_ko_at_arm_def)+
  done

lemma set_thread_state_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_thread_state_def
  apply(wp set_object_globals_equiv dxo_wp_weak |simp)+
  apply (intro impI conjI allI)
  apply(clarsimp simp: valid_ko_at_arm_def obj_at_def tcb_at_def2 get_tcb_def is_tcb_def dest: get_tcb_SomeD
                 split: option.splits kernel_object.splits)+
  done

lemma set_bound_notification_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace> set_bound_notification ref ts \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_bound_notification_def
  apply(wp set_object_globals_equiv dxo_wp_weak |simp)+
  apply (intro impI conjI allI)
  apply(clarsimp simp: valid_ko_at_arm_def obj_at_def tcb_at_def2 get_tcb_def is_tcb_def
                 dest: get_tcb_SomeD
                split: option.splits kernel_object.splits)+
  done

lemma set_object_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm and (\<lambda>s. ptr = arm_global_pd (arch_state s) \<longrightarrow>
   a_type obj = AArch APageDirectory)\<rbrace>
     set_object ptr obj \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  by (wpsimp wp: set_object_wp
           simp: a_type_def valid_ko_at_arm_def obj_at_def
          split: kernel_object.splits arch_kernel_obj.splits if_splits)

lemma valid_ko_at_arm_exst_update[simp]: "valid_ko_at_arm (trans_state f s) = valid_ko_at_arm s"
  apply (simp add: valid_ko_at_arm_def)
  done

lemma set_thread_state_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding set_thread_state_def
  apply(wp set_object_valid_ko_at_arm dxo_wp_weak |simp)+
  apply(fastforce simp: valid_ko_at_arm_def get_tcb_ko_at obj_at_def)
  done

lemma set_bound_notification_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> set_bound_notification ref ts \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding set_bound_notification_def
  apply(wp set_object_valid_ko_at_arm dxo_wp_weak |simp)+
  apply(fastforce simp: valid_ko_at_arm_def get_tcb_ko_at obj_at_def)
  done

crunch globals_equiv: cancel_badged_sends "globals_equiv s"
 (wp: filterM_preserved dxo_wp_weak ignore: reschedule_required tcb_sched_action)

lemma thread_set_globals_equiv:
  "(\<And>tcb. arch_tcb_context_get (tcb_arch (f tcb)) = arch_tcb_context_get (tcb_arch tcb))
     \<Longrightarrow> \<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding thread_set_def
  apply(wp set_object_globals_equiv)
  apply simp
  apply (intro impI conjI allI)
  apply(fastforce simp: valid_ko_at_arm_def obj_at_def get_tcb_def)+
  apply (clarsimp simp: get_tcb_def tcb_at_def2 split: kernel_object.splits option.splits)
  done

lemma set_asid_pool_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  apply (fastforce simp: valid_ko_at_arm_def obj_at_def)
  done

lemma idle_equiv_arch_state_update[simp]: "idle_equiv st (s\<lparr>arch_state := x\<rparr>) = idle_equiv st s"
  apply (simp add: idle_equiv_def)
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
  apply(wp modify_wp invalidate_hw_asid_entry_globals_equiv
          dmo_mol_globals_equiv invalidate_asid_globals_equiv
       | wpc | simp add: invalidateLocalTLB_ASID_def)+
  done

lemma store_hw_asid_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> store_hw_asid asid hw_asid \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding store_hw_asid_def
  apply(wp find_pd_for_asid_assert_wp | rule modify_wp, simp)+
  apply(fastforce simp: globals_equiv_def)
  done

lemma get_hw_asid_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> get_hw_asid asid \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding get_hw_asid_def
  apply(wp store_hw_asid_globals_equiv find_free_hw_asid_globals_equiv load_hw_asid_wp | wpc | simp)+
  done

lemma arm_context_switch_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> arm_context_switch pd asid \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding arm_context_switch_def  setHardwareASID_def
  apply(wp dmo_mol_globals_equiv get_hw_asid_globals_equiv
       | simp add: dmo_bind_valid set_current_pd_def writeTTBR0_def isb_def dsb_def )+
  done

lemma set_vm_root_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> set_vm_root tcb \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (clarsimp simp:set_vm_root_def set_current_pd_def dsb_def
                       isb_def writeTTBR0_def dmo_bind_valid)
  apply(wp dmo_mol_globals_equiv arm_context_switch_globals_equiv whenE_inv
        | wpc
        | clarsimp simp: dmo_bind_valid isb_def dsb_def writeTTBR0_def)+
   apply(wp hoare_vcg_all_lift | wp (once) hoare_drop_imps | clarsimp)+
   done

lemma invalidate_asid_entry_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> invalidate_asid_entry asid \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding invalidate_asid_entry_def
  apply(wp invalidate_hw_asid_entry_globals_equiv invalidate_asid_globals_equiv load_hw_asid_wp)
  apply(clarsimp)
  done

lemma flush_space_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> flush_space asid \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
unfolding flush_space_def
apply(wp dmo_mol_globals_equiv load_hw_asid_wp
    | wpc
    | simp add: invalidateLocalTLB_ASID_def cleanCaches_PoU_def dsb_def invalidate_I_PoU_def clean_D_PoU_def dmo_bind_valid)+
done

lemma delete_asid_pool_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> delete_asid_pool base ptr \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding delete_asid_pool_def
  apply(wp set_vm_root_globals_equiv mapM_wp[OF _ subset_refl] modify_wp invalidate_asid_entry_globals_equiv flush_space_globals_equiv | simp)+
  done

crunch globals_equiv[wp]: invalidate_tlb_by_asid "globals_equiv s"
  (simp: invalidateLocalTLB_ASID_def wp: dmo_mol_globals_equiv ignore: machine_op_lift do_machine_op)

lemma set_pt_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace> set_pt ptr pt \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_pt_def
  apply (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  apply (fastforce simp: valid_ko_at_arm_def obj_at_def)
  done

crunch globals_equiv: store_pte "globals_equiv s"

lemma set_vm_root_for_flush_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> set_vm_root_for_flush pd asid \<lbrace>\<lambda>rv. globals_equiv s\<rbrace>"
  unfolding set_vm_root_for_flush_def set_current_pd_def fun_app_def
  apply(wp dmo_mol_globals_equiv | wpc | simp)+
    apply(rule_tac Q="\<lambda>rv. globals_equiv s" in hoare_strengthen_post)
     apply(wp | simp)+
     done

lemma flush_table_globals_equiv[wp]:
  "\<lbrace>globals_equiv s\<rbrace> flush_table pd asid cptr pt \<lbrace>\<lambda>rv. globals_equiv s\<rbrace>"
  unfolding flush_table_def invalidateLocalTLB_ASID_def fun_app_def
  apply (wp mapM_wp' dmo_mol_globals_equiv | wpc | simp add: do_machine_op_bind split del: if_split cong: if_cong)+
  done

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

lemma not_in_global_refs_vs_lookup2: "\<lbrakk>
  valid_vs_lookup s;
  valid_global_refs s;
  valid_arch_state s; valid_global_objs s; page_directory_at p s; (\<exists>\<rhd> p) s\<rbrakk> \<Longrightarrow>
  p \<notin> global_refs s"
  apply (insert not_in_global_refs_vs_lookup[where p=p and s=s])
  apply simp
done

(*FIXME: This should either be straightforward or moved somewhere else*)

lemma case_junk : "((case rv of Inl e \<Rightarrow> True | Inr r \<Rightarrow> P r) \<longrightarrow> (case rv of Inl e \<Rightarrow> True | Inr r \<Rightarrow> R r)) =
  (case rv of Inl e \<Rightarrow> True | Inr r \<Rightarrow> P r \<longrightarrow> R r)"
  apply (case_tac rv)
  apply simp+
done

(*FIXME: Same here*)
lemma hoare_add_postE : "\<lbrace>Q\<rbrace> f \<lbrace>\<lambda> r. P r\<rbrace>,- \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>\<lambda> r s. (P r s) \<longrightarrow> (R r s) \<rbrace>,- \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>\<lambda> r. R r\<rbrace>,-"
  unfolding validE_R_def validE_def
  apply (erule hoare_add_post)
   apply simp
  apply (erule hoare_post_imp[rotated])
  apply (simp add: case_junk)
done

lemma find_pd_for_asid_not_arm_global_pd:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_global_objs and valid_vs_lookup
  and valid_global_refs and valid_arch_state\<rbrace>
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
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_global_objs and valid_vs_lookup
  and valid_global_refs and valid_arch_state\<rbrace>
  find_pd_for_asid asid
  \<lbrace>\<lambda>rv s.
  (lookup_pd_slot rv vptr && mask 6 = 0) \<longrightarrow>
  (\<forall> x \<in> set [0 , 4 .e. 0x3C].
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
  and valid_global_refs and valid_arch_state and globals_equiv st\<rbrace> unmap_page_table asid vaddr pt \<lbrace>\<lambda>rv. globals_equiv st\<rbrace>"
  unfolding unmap_page_table_def page_table_mapped_def
  apply(wp store_pde_globals_equiv | wpc | simp add: cleanByVA_PoU_def)+
    apply(rule_tac Q="\<lambda>_. globals_equiv st and (\<lambda>sa. lookup_pd_slot pd vaddr && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state sa))" in hoare_strengthen_post)
     apply(wp find_pd_for_asid_not_arm_global_pd hoare_post_imp_dc2E_actual | simp)+
  done

lemma set_pt_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> set_pt ptr pt \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: set_object_wp_strong simp: valid_ko_at_arm_def obj_at_def a_type_def)

crunch valid_ko_at_arm[wp]: store_pte "valid_ko_at_arm"

lemma mapM_x_swp_store_pte_globals_equiv:
  " \<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace>
          mapM_x (swp store_pte A) slots
          \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply(rule_tac Q="\<lambda>_. globals_equiv s and valid_ko_at_arm" in hoare_strengthen_post)
   apply(wp mapM_x_wp' store_pte_globals_equiv store_pte_valid_ko_at_arm | simp)+
   done

lemma mapM_x_swp_store_pte_valid_ko_at_arm[wp]:
  " \<lbrace>valid_ko_at_arm\<rbrace>
          mapM_x (swp store_pte A) slots
          \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  apply(wp mapM_x_wp' | simp add: swp_def)+
  done

lemma set_cap_globals_equiv'':
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace>
  set_cap cap p \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_cap_def
  apply(simp only: split_def)
  apply(wp set_object_globals_equiv hoare_vcg_all_lift get_object_wp | wpc | simp)+
   apply(fastforce simp: valid_ko_at_arm_def valid_ao_at_def obj_at_def is_tcb_def)+
  done

lemma do_machine_op_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> do_machine_op mol \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding do_machine_op_def machine_op_lift_def split_def valid_ko_at_arm_def
  apply(wp modify_wp, simp)
  done

lemma valid_ko_at_arm_next_asid[simp]:
  "valid_ko_at_arm (s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid := x\<rparr>\<rparr>)
  = valid_ko_at_arm s"
  by (simp add: valid_ko_at_arm_def)

lemma valid_ko_at_arm_asid_map[simp]:
  "valid_ko_at_arm (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map := x\<rparr>\<rparr>)
  = valid_ko_at_arm s"
  by (simp add: valid_ko_at_arm_def)

lemma valid_ko_at_arm_hwasid_table[simp]:
  "valid_ko_at_arm (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table := x\<rparr>\<rparr>)
  = valid_ko_at_arm s"
  by (simp add: valid_ko_at_arm_def)

lemma valid_ko_at_arm_asid_table[simp]:
  "valid_ko_at_arm
                (s\<lparr>arch_state := arch_state s
                     \<lparr>arm_asid_table := A\<rparr>\<rparr>) =
   valid_ko_at_arm s" by (simp add: valid_ko_at_arm_def)

lemma valid_ko_at_arm_interrupt_states[simp]:
  "valid_ko_at_arm (s\<lparr>interrupt_states := f\<rparr>)
  = valid_ko_at_arm s"
  by (simp add: valid_ko_at_arm_def)

lemma valid_ko_at_arm_arch[simp]:
  "arm_global_pd A = arm_global_pd (arch_state s) \<Longrightarrow>
   valid_ko_at_arm (s\<lparr>arch_state := A\<rparr>) = valid_ko_at_arm s"
  by (simp add: valid_ko_at_arm_def)

crunch valid_ko_at_arm[wp]: arm_context_switch, set_vm_root, set_pd "valid_ko_at_arm"
  (wp: find_pd_for_asid_assert_wp crunch_wps simp: crunch_simps)

crunch valid_ko_at_arm[wp]: unmap_page_table "valid_ko_at_arm"
  (wp: crunch_wps simp: crunch_simps a_type_simps)

definition authorised_for_globals_page_table_inv ::
    "page_table_invocation \<Rightarrow> 'z state \<Rightarrow> bool" where
  "authorised_for_globals_page_table_inv pti \<equiv>
    \<lambda>s. case pti of PageTableMap cap ptr pde p
  \<Rightarrow> p && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s) | _ \<Rightarrow> True"

lemma perform_page_table_invocation_globals_equiv:
  "\<lbrace>valid_global_refs and valid_global_objs and valid_arch_state and
    globals_equiv st and pspace_aligned and valid_vspace_objs and
    valid_vs_lookup and valid_kernel_mappings and authorised_for_globals_page_table_inv pti\<rbrace>
  perform_page_table_invocation pti \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_page_table_invocation_def cleanCacheRange_PoU_def
  apply(rule hoare_weaken_pre)
   apply(wp store_pde_globals_equiv set_cap_globals_equiv'' dmo_cacheRangeOp_lift
            mapM_x_swp_store_pte_globals_equiv unmap_page_table_globals_equiv
           | wpc | simp add: cleanByVA_PoU_def)+
  apply(fastforce simp: authorised_for_globals_page_table_inv_def valid_arch_state_def valid_ko_at_arm_def obj_at_def dest: a_type_pdD)
  done

lemma do_flush_globals_equiv:
  "\<lbrace>globals_equiv st\<rbrace> do_machine_op (do_flush typ start end pstart)
    \<lbrace>\<lambda>rv. globals_equiv st\<rbrace>"
  apply (cases "typ")
     apply (wp dmo_cacheRangeOp_lift | simp add: do_flush_def cache_machine_op_defs do_flush_defs do_machine_op_bind when_def | clarsimp | rule conjI)+
     done

lemma perform_page_directory_invocation_globals_equiv:
  "\<lbrace>globals_equiv st\<rbrace>
  perform_page_directory_invocation pdi \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_page_directory_invocation_def
  apply (cases pdi)
   apply (wp do_flush_globals_equiv | simp)+
   done

lemma flush_page_globals_equiv[wp]:
  "\<lbrace>globals_equiv st\<rbrace> flush_page page_size pd asid vptr \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding flush_page_def invalidateLocalTLB_VAASID_def
  apply(wp | simp cong: if_cong split del: if_split)+
  done

lemma flush_page_arm_global_pd[wp]:
  "\<lbrace>\<lambda>s. P (arm_global_pd (arch_state s))\<rbrace>
     flush_page pgsz pd asid vptr
   \<lbrace>\<lambda>rv s. P (arm_global_pd (arch_state s))\<rbrace>"
  unfolding flush_page_def
  apply(wp | simp cong: if_cong split del: if_split)+
  done

lemma mapM_swp_store_pte_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm\<rbrace>
    mapM (swp store_pte A) slots \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply(rule_tac Q="\<lambda> _. globals_equiv st and valid_ko_at_arm"
        in hoare_strengthen_post)
   apply(wp mapM_wp' store_pte_globals_equiv | simp)+
   done

lemma mapM_swp_store_pde_globals_equiv:
  "\<lbrace>globals_equiv st and (\<lambda>s. \<forall>x \<in> set slots.
   x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))\<rbrace>
     mapM (swp store_pde A) slots \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule_tac Q="\<lambda> _. globals_equiv st and (\<lambda> s. \<forall>x \<in> set slots.
                      x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))"
         in hoare_strengthen_post)
   apply (wp mapM_wp' store_pde_globals_equiv | simp)+
   done

lemma mapM_swp_store_pte_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> mapM (swp store_pte A) slots \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  apply(wp mapM_wp' store_pte_valid_ko_at_arm | simp)+
  done

lemma mapM_x_swp_store_pde_globals_equiv :
  "\<lbrace>globals_equiv st and (\<lambda>s. \<forall>x \<in> set slots.
   x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))\<rbrace>
     mapM_x (swp store_pde A) slots \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule_tac Q="\<lambda>_. globals_equiv st and (\<lambda> s. \<forall>x \<in> set slots.
                     x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s))"
         in hoare_strengthen_post)
   apply (wp mapM_x_wp' store_pde_globals_equiv | simp)+
   done

crunch valid_ko_at_arm[wp]: flush_page "valid_ko_at_arm"
  (wp: crunch_wps simp: crunch_simps)

lemma unmap_page_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and pspace_aligned and valid_vspace_objs
  and valid_global_objs and valid_vs_lookup and valid_global_refs \<rbrace> unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding unmap_page_def cleanCacheRange_PoU_def including no_pre
  apply (induct pgsz)
     prefer 4
     apply (simp only: vmpage_size.simps)
     apply(wp mapM_swp_store_pde_globals_equiv dmo_cacheRangeOp_lift | simp add: cleanByVA_PoU_def)+
        apply(rule hoare_drop_imps)
        apply(wp)+
       apply(simp)
       apply(rule hoare_drop_imps)
       apply(wp)+
     apply (rule hoare_pre)
      apply (rule_tac Q="\<lambda>x. globals_equiv st and (\<lambda>sa. lookup_pd_slot x vptr && mask 6 = 0 \<longrightarrow> (\<forall>xa\<in>set [0 , 4 .e. 0x3C]. xa + lookup_pd_slot x vptr && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state sa)))" and E="\<lambda>_. globals_equiv st" in hoare_post_impErr)
        apply(wp find_pd_for_asid_not_arm_global_pd_large_page)
       apply simp
      apply simp
     apply simp
    apply(wp store_pte_globals_equiv | simp add: cleanByVA_PoU_def)+
      apply(wp hoare_drop_imps)+
     apply(wp (once) lookup_pt_slot_inv)
     apply(wp (once) lookup_pt_slot_inv)
     apply(wp (once) lookup_pt_slot_inv)
     apply(wp (once) lookup_pt_slot_inv)
    apply(simp)
    apply(rule hoare_pre)
     apply wp
    apply(simp add: valid_arch_state_ko_at_arm)
   apply(simp)
   apply(rule hoare_pre)
    apply(wp dmo_cacheRangeOp_lift mapM_swp_store_pde_globals_equiv store_pde_globals_equiv lookup_pt_slot_inv mapM_swp_store_pte_globals_equiv hoare_drop_imps | simp add: cleanByVA_PoU_def)+
   apply(simp add: valid_arch_state_ko_at_arm)
  apply(rule hoare_pre)
   apply(wp store_pde_globals_equiv | simp add: valid_arch_state_ko_at_arm cleanByVA_PoU_def)+
    apply(wp find_pd_for_asid_not_arm_global_pd hoare_drop_imps)+
  apply(clarsimp)
  done (* don't know what happened here. wp deleted globals_equiv from precon *)


lemma cte_wp_parent_not_global_pd: "valid_global_refs s \<Longrightarrow> cte_wp_at (parent_for_refs (Inr (a,b))) k s \<Longrightarrow> \<forall>x \<in> set b. x && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s)"
  apply (simp only: cte_wp_at_caps_of_state)
  apply (elim exE conjE)
  apply (drule valid_global_refsD2,simp)
  apply (unfold parent_for_refs_def)
  apply (simp add: image_def global_refs_def cap_range_def)
  apply clarsimp
  apply (subgoal_tac "arm_global_pd (arch_state s) \<in> set b")
   apply auto
  done

definition authorised_for_globals_page_inv :: "page_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  where "authorised_for_globals_page_inv pgi \<equiv>
    \<lambda>s. case pgi of PageMap asid cap ptr m \<Rightarrow> \<exists>slot. cte_wp_at (parent_for_refs m) slot s | _ \<Rightarrow> True"

lemma set_cap_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> set_cap cap p \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  apply(simp add: valid_ko_at_arm_def)
  apply(rule hoare_ex_wp)
  apply(rule hoare_pre)
   apply(simp add: set_cap_def split_def)
   apply(wp | wpc)+
     apply(simp add: set_object_def)
     apply(wp get_object_wp | wpc)+
  apply(fastforce simp: obj_at_def)
  done

crunch valid_ko_at_arm[wp]: unmap_page "valid_ko_at_arm"
  (wp: crunch_wps)

lemma as_user_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace> as_user tptr f
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding as_user_def
  apply(wp)
      apply(simp add: split_def)
      apply(wp set_object_globals_equiv)+
  apply(clarsimp simp: valid_ko_at_arm_def get_tcb_def obj_at_def)
  done


lemma set_message_info_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace> set_message_info thread info \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_message_info_def
  apply(wp as_user_globals_equiv)
  done

lemma store_word_offs_globals_equiv:
  "\<lbrace>globals_equiv s\<rbrace>
    store_word_offs ptr offs v
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding store_word_offs_def fun_app_def
  apply (wp do_machine_op_globals_equiv)
    apply clarsimp
    apply (erule use_valid[OF _ storeWord_globals_equiv])
    apply (wp | simp | force)+
  done


lemma length_msg_registers:
  "length msg_registers = 4"
  unfolding msg_registers_def
  by (simp add: msgRegisters_def upto_enum_def fromEnum_def enum_register)

lemma length_msg_lt_msg_max:
  "length msg_registers < msg_max_length"
  apply(simp add: length_msg_registers msg_max_length_def)
  done


lemma arm_global_pd_not_tcb:
  "valid_ko_at_arm s \<Longrightarrow> get_tcb (arm_global_pd (arch_state s)) s = None"
  unfolding valid_ko_at_arm_def
  apply (case_tac "get_tcb (arm_global_pd (arch_state s)) s")
  apply simp
  apply(clarsimp simp: valid_ko_at_arm_def get_tcb_ko_at obj_at_def)
  done


lemma set_mrs_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm and (\<lambda>sa. thread \<noteq> idle_thread sa)\<rbrace>
      set_mrs thread buf msgs
    \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_mrs_def
  apply(wp | wpc)+
       apply(simp add: zipWithM_x_mapM_x)
       apply(rule conjI)
        apply(rule impI)
        apply(rule_tac Q="\<lambda>_. globals_equiv s"
          in hoare_strengthen_post)
         apply(wp mapM_x_wp')
         apply(simp add: split_def)
         apply(wp store_word_offs_globals_equiv)
        apply(simp)
       apply(clarsimp)
       apply(insert length_msg_lt_msg_max)
       apply(simp)
      apply(wp set_object_globals_equiv static_imp_wp)
     apply(wp hoare_vcg_all_lift set_object_globals_equiv static_imp_wp)+
   apply(clarsimp simp:arm_global_pd_not_tcb)+
  done

crunch valid_ko_at_arm[wp]: set_mrs valid_ko_at_arm
  (wp: crunch_wps simp: crunch_simps arm_global_pd_not_tcb)

lemma perform_page_invocation_globals_equiv:
  "\<lbrace>authorised_for_globals_page_inv pgi and valid_page_inv pgi and globals_equiv st
    and valid_arch_state and pspace_aligned and valid_vspace_objs and valid_global_objs
    and valid_vs_lookup and valid_global_refs and ct_active and valid_idle\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding perform_page_invocation_def cleanCacheRange_PoU_def
  apply(rule hoare_weaken_pre)
  apply(wp mapM_swp_store_pte_globals_equiv hoare_vcg_all_lift dmo_cacheRangeOp_lift
        mapM_swp_store_pde_globals_equiv mapM_x_swp_store_pte_globals_equiv
        mapM_x_swp_store_pde_globals_equiv set_cap_globals_equiv''
        unmap_page_globals_equiv store_pte_globals_equiv store_pde_globals_equiv static_imp_wp
        do_flush_globals_equiv set_mrs_globals_equiv set_message_info_globals_equiv
       | wpc | simp add: do_machine_op_bind cleanByVA_PoU_def)+
  by (auto simp: cte_wp_parent_not_global_pd authorised_for_globals_page_inv_def
                   valid_page_inv_def valid_slots_def valid_idle_def st_tcb_def2 ct_in_state_def
                   pred_tcb_at_def obj_at_def
           dest: valid_arch_state_ko_at_arm
           dest!:rev_subsetD[OF _ tl_subseteq])

lemma retype_region_ASIDPoolObj_globals_equiv:
  "\<lbrace>globals_equiv s and (\<lambda>sa. ptr \<noteq> arm_global_pd (arch_state s)) and (\<lambda>sa. ptr \<noteq> idle_thread sa)\<rbrace>
  retype_region ptr 1 0 (ArchObject ASIDPoolObj) dev
  \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding retype_region_def
  apply(wp modify_wp dxo_wp_weak | simp | fastforce simp: globals_equiv_def default_arch_object_def obj_bits_api_def)+
      apply (simp add: trans_state_update[symmetric] del: trans_state_update)
     apply wp+
  apply (fastforce simp: globals_equiv_def idle_equiv_def tcb_at_def2)
  done

crunch valid_ko_at_arm[wp]: "set_untyped_cap_as_full" "valid_ko_at_arm"

lemma cap_insert_globals_equiv'':
  "\<lbrace>globals_equiv s and valid_global_objs and valid_ko_at_arm\<rbrace>
  cap_insert new_cap src_slot dest_slot \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding  cap_insert_def
  apply(wp set_original_globals_equiv update_cdt_globals_equiv set_cap_globals_equiv'' dxo_wp_weak
         | rule hoare_drop_imps | simp)+
  done



lemma retype_region_ASIDPoolObj_valid_ko_at_arm:
  "\<lbrace>valid_ko_at_arm and (\<lambda>s. ptr \<noteq> arm_global_pd (arch_state s))\<rbrace>
  retype_region ptr 1 0 (ArchObject ASIDPoolObj) dev
  \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  apply(simp add: retype_region_def)
  apply(wp modify_wp dxo_wp_weak |simp add: trans_state_update[symmetric] del: trans_state_update)+
  apply(clarsimp simp: valid_ko_at_arm_def)
  apply(rule_tac x=pd in exI)
  apply(fold fun_upd_def)
  apply(clarsimp simp: fun_upd_def obj_at_def)
  done

lemma detype_valid_ko_at_arm:
  "\<lbrace>valid_ko_at_arm and (\<lambda>s.
      arm_global_pd (arch_state s) \<notin> {ptr..ptr + 2 ^ bits - 1})\<rbrace>
   modify (detype {ptr..ptr + 2 ^ bits - 1}) \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  apply(wp modify_wp)
  apply(fastforce simp: valid_ko_at_arm_def detype_def obj_at_def)
  done

lemma detype_valid_arch_state:
  "\<lbrace>valid_arch_state and
    (\<lambda>s. arm_globals_frame (arch_state s) \<notin> {ptr..ptr + 2 ^ bits - 1} \<and>
         arm_global_pd (arch_state s) \<notin> {ptr..ptr + 2 ^ bits - 1} \<and>
    {ptr..ptr + 2 ^ bits - 1} \<inter> ran (arm_asid_table (arch_state s)) = {} \<and>
    {ptr..ptr + 2 ^ bits - 1} \<inter> set (arm_global_pts (arch_state s)) = {})\<rbrace>
   modify (detype {ptr..ptr + (1 << bits) - 1}) \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply(wp modify_wp)
  apply(simp add: valid_arch_state_def)
  apply(rule conjI)
   apply(clarsimp simp: valid_asid_table_def)
   apply(erule_tac x=p in in_empty_interE)
    apply(simp)+
  apply(clarsimp simp: valid_global_pts_def)
  apply(erule_tac x=p and B="set (arm_global_pts (arch_state s))" in in_empty_interE)
   apply(simp)+
   done


lemma delete_objects_valid_ko_at_arm:
   "\<lbrace>valid_ko_at_arm and
   (\<lambda>s. arm_global_pd (arch_state s) \<notin> ptr_range p b) and
    K (is_aligned p b \<and>
        2 \<le> b \<and>
        b < word_bits)\<rbrace>
  delete_objects p b \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  apply(rule hoare_gen_asm)
  unfolding delete_objects_def
  apply(wp detype_valid_ko_at_arm do_machine_op_valid_ko_at_arm | simp add: ptr_range_def)+
  done

lemma perform_asid_control_invocation_globals_equiv:
  notes delete_objects_invs[wp del]
  notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  shows
  "\<lbrace>globals_equiv s and invs and ct_active and valid_aci aci\<rbrace>
   perform_asid_control_invocation aci \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding perform_asid_control_invocation_def
  apply(rule hoare_pre)
   apply wpc
   apply (rename_tac word1 cslot_ptr1 cslot_ptr2 word2)
   apply (wp modify_wp cap_insert_globals_equiv''
             retype_region_ASIDPoolObj_globals_equiv[simplified]
             retype_region_invs_extras(5)[where sz=pageBits]
             retype_region_ASIDPoolObj_valid_ko_at_arm[simplified]
             set_cap_globals_equiv
             max_index_upd_invs_simple set_cap_no_overlap
             set_cap_caps_no_overlap max_index_upd_caps_overlap_reserved
             region_in_kernel_window_preserved
             hoare_vcg_all_lift  get_cap_wp static_imp_wp
             set_cap_idx_up_aligned_area[where dev = False,simplified]
         | simp)+
   (* factor out the implication -- we know what the relevant components of the
      cap referred to in the cte_wp_at are anyway from valid_aci, so just use
      those directly to simplify the reasoning later on *)
   apply(rule_tac Q="\<lambda> a b. globals_equiv s b \<and>
                            invs b \<and> valid_ko_at_arm b \<and> word1 \<noteq> arm_global_pd (arch_state b) \<and>
                            word1 \<noteq> idle_thread b \<and>
                            (\<exists> idx. cte_wp_at ((=) (UntypedCap False word1 pageBits idx)) cslot_ptr2 b) \<and>
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
                     atLeastatMost_subset_iff word_and_le2)
    apply(rule conjI, rule descendants_range_caps_no_overlapI)
       apply assumption
      apply(simp add: cte_wp_at_caps_of_state)
     apply(simp add: empty_descendants_range_in)
    apply(clarsimp simp: range_cover_def)
    apply(subst is_aligned_neg_mask_eq[THEN sym], assumption)
    apply(simp add: word_bw_assocs pageBits_def mask_zero)
   apply(wp add: delete_objects_invs_ex delete_objects_pspace_no_overlap[where dev=False]
            delete_objects_globals_equiv delete_objects_valid_ko_at_arm
            hoare_vcg_ex_lift
            del: Untyped_AI.delete_objects_pspace_no_overlap
        | simp add: page_bits_def)+
  apply (clarsimp simp: conj_comms invs_valid_ko_at_arm invs_psp_aligned invs_valid_objs valid_aci_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule_tac cap="UntypedCap False a b c" for a b c  in caps_of_state_valid, assumption)
  apply (clarsimp simp: valid_cap_def cap_aligned_def untyped_min_bits_def)
  apply (frule_tac slot="(aa,ba)" in untyped_caps_do_not_overlap_global_refs[rotated, OF invs_valid_global_refs])
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply ((rule conjI |rule refl | simp)+)[1]
  apply(rule conjI)
   apply(clarsimp simp: global_refs_def ptr_range_memI)
  apply(rule conjI)
   apply(clarsimp simp: global_refs_def ptr_range_memI)
  apply(rule conjI, fastforce simp: global_refs_def)
  apply(rule conjI, fastforce simp: global_refs_def)
  apply(rule conjI)
   apply(drule untyped_slots_not_in_untyped_range)
        apply(blast intro!: empty_descendants_range_in)
       apply(simp add: cte_wp_at_caps_of_state)
      apply simp
     apply(rule refl)
    apply(rule subset_refl)
   apply(simp)
  apply(rule conjI)
   apply fastforce
  apply (auto intro: empty_descendants_range_in simp: descendants_range_def2 cap_range_def)
  done


lemma perform_asid_pool_invocation_globals_equiv:
  "\<lbrace>globals_equiv s and valid_ko_at_arm\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding perform_asid_pool_invocation_def
  apply(rule hoare_weaken_pre)
   apply(wp modify_wp set_asid_pool_globals_equiv set_cap_globals_equiv''
        get_cap_wp | wpc | simp)+
  done

definition
  authorised_for_globals_arch_inv :: "arch_invocation \<Rightarrow> ('z::state_ext) state \<Rightarrow> bool" where
  "authorised_for_globals_arch_inv ai \<equiv> case ai of
  InvokePageTable oper \<Rightarrow> authorised_for_globals_page_table_inv oper |
  InvokePage oper \<Rightarrow> authorised_for_globals_page_inv oper |
  _ \<Rightarrow> \<top>"

lemma arch_perform_invocation_globals_equiv:
  "\<lbrace>globals_equiv s and invs and ct_active and valid_arch_inv ai and authorised_for_globals_arch_inv ai\<rbrace>
  arch_perform_invocation ai \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding arch_perform_invocation_def
  apply wp
   apply(wpc)
       apply(wp perform_page_table_invocation_globals_equiv perform_page_directory_invocation_globals_equiv
                perform_page_invocation_globals_equiv perform_asid_control_invocation_globals_equiv
                perform_asid_pool_invocation_globals_equiv)+
  apply(auto simp: authorised_for_globals_arch_inv_def
             dest: valid_arch_state_ko_at_arm
             simp: invs_def valid_state_def valid_arch_inv_def invs_valid_vs_lookup)
  done

lemma find_pd_for_asid_authority3:
  "\<lbrace>\<lambda>s. \<forall>pd. (pspace_aligned s \<and> valid_vspace_objs s \<longrightarrow> is_aligned pd pd_bits)
           \<and> (\<exists>\<rhd> pd) s
           \<longrightarrow> Q pd s\<rbrace> find_pd_for_asid asid \<lbrace>Q\<rbrace>, -"
  (is "\<lbrace>?P\<rbrace> ?f \<lbrace>Q\<rbrace>,-")
  apply (clarsimp simp: validE_R_def validE_def valid_def imp_conjL[symmetric])
  apply (frule in_inv_by_hoareD[OF find_pd_for_asid_inv], clarsimp)
  apply (drule spec, erule mp)
  apply (simp add: use_validE_R[OF _ find_pd_for_asid_authority1]
                   use_validE_R[OF _ find_pd_for_asid_aligned_pd_bits]
                   use_validE_R[OF _ find_pd_for_asid_lookup])
  done

lemma decode_arch_invocation_authorised_for_globals:
  "\<lbrace>invs and cte_wp_at ((=) (cap.ArchObjectCap cap)) slot
        and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)\<rbrace>
  arch_decode_invocation label msg x_slot slot cap excaps
  \<lbrace>\<lambda>rv. authorised_for_globals_arch_inv rv\<rbrace>, -"
  unfolding arch_decode_invocation_def authorised_for_globals_arch_inv_def
  apply (rule hoare_pre)
   apply (simp add: split_def Let_def
               cong: cap.case_cong arch_cap.case_cong if_cong option.case_cong
               split del: if_split)
   apply (wp select_wp select_ext_weak_wp whenE_throwError_wp check_vp_wpR unlessE_wp get_pde_wp get_master_pde_wp
             find_pd_for_asid_authority3 create_mapping_entries_parent_for_refs
           | wpc
           | simp add:  authorised_for_globals_page_inv_def
                  del: hoare_True_E_R
                  split del: if_split)+
     apply(simp cong: if_cong)
     apply(wp hoare_vcg_if_lift2)
     apply(rule hoare_conjI)
      apply(rule hoare_drop_imps)
      apply(simp add: authorised_for_globals_page_table_inv_def)
      apply(wp)
     apply(rule hoare_drop_imps)
     apply((wp hoare_TrueI hoare_vcg_all_lift hoare_drop_imps | wpc | simp)+)[3]
  apply (clarsimp simp: authorised_asid_pool_inv_def authorised_page_table_inv_def
                        neq_Nil_conv invs_psp_aligned invs_vspace_objs cli_no_irqs)
  apply (drule cte_wp_valid_cap, clarsimp+)
  apply (cases cap, simp_all)
    \<comment> \<open>PageCap\<close>
    apply (clarsimp simp: valid_cap_simps cli_no_irqs)
    apply (cases "invocation_type label";(rename_tac arch, case_tac arch; simp add: isPageFlushLabel_def isPDFlushLabel_def))
           \<comment> \<open>Map\<close>
           apply (rename_tac word cap_rights vmpage_size option arch)
           apply(clarsimp simp: isPageFlushLabel_def isPDFlushLabel_def | rule conjI)+
            apply(drule cte_wp_valid_cap)
             apply(clarsimp simp: invs_def valid_state_def)
            apply(simp add: valid_cap_def)
           apply(simp add: vmsz_aligned_def)
           apply(drule_tac ptr="msg ! 0" and off="2 ^ pageBitsForSize vmpage_size - 1" in is_aligned_no_wrap')
            apply(insert pbfs_less_wb')
            apply(clarsimp)
           apply(fastforce simp: x_power_minus_1)
          apply(clarsimp)
          apply(fastforce dest: cte_wp_valid_cap simp: invs_def valid_state_def valid_cap_def)
         \<comment> \<open>Unmap\<close>
         apply(simp add: authorised_for_globals_page_inv_def)+
   apply(clarsimp)
   \<comment> \<open>PageTableCap\<close>
   apply(simp add: authorised_for_globals_page_table_inv_def)
   apply(clarsimp)
   apply(frule_tac vptr="msg ! 0" in pd_shifting')
   apply(clarsimp)
   apply(clarsimp simp: invs_def valid_state_def valid_global_refs_def valid_refs_def global_refs_def)
   apply(erule_tac x=aa in allE)
   apply(erule_tac x=b in allE)
   apply(drule_tac P'="\<lambda>c. idle_thread s \<in> cap_range c \<or>
                 arm_global_pd (arch_state s) \<in> cap_range c \<or>
                 (range (interrupt_irq_node s) \<union>
                  set (arm_global_pts (arch_state s))) \<inter>
                 cap_range c \<noteq>
                 {}" in cte_wp_at_weakenE)
    apply(clarsimp simp: cap_range_def)
   apply(simp)
  by(fastforce)


lemma as_user_valid_ko_at_arm[wp]:
  "\<lbrace> valid_ko_at_arm \<rbrace>
  as_user thread f
  \<lbrace> \<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding as_user_def
  apply wp
     apply (case_tac x)
     apply (simp | wp select_wp)+
  apply(fastforce simp: valid_ko_at_arm_def get_tcb_ko_at obj_at_def)
  done

lemma valid_arch_arm_asid_table_unmap:
  "valid_arch_state s
       \<and> tab = arm_asid_table (arch_state s)
     \<longrightarrow> valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_state_def valid_arch_state_unmap_strg)
  done

lemma valid_arch_objs_arm_asid_table_unmap:
  "valid_vspace_objs s
       \<and> tab = arm_asid_table (arch_state s)
     \<longrightarrow> valid_vspace_objs (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_state_def valid_vspace_objs_unmap_strg)
  done

lemma valid_vspace_objs_arm_asid_table_unmap:
  "valid_vspace_objs s
       \<and> tab = arm_asid_table (arch_state s)
     \<longrightarrow> valid_vspace_objs (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_state_def valid_vspace_objs_unmap_strg)
  done

lemmas arm_context_switch_valid_vspace_objs_aux =
  hoare_drop_imp[of valid_vspace_objs "arm_context_switch _ _" "\<lambda>_ s. valid_vspace_objs s"
                , OF arm_context_switch_vspace_objs]

lemma delete_asid_pool_valid_arch_obsj[wp]:
  "\<lbrace>valid_vspace_objs\<rbrace>
    delete_asid_pool base pptr
  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding delete_asid_pool_def
  apply (wp modify_wp)
      apply (strengthen valid_vspace_objs_arm_asid_table_unmap)
      apply (wpsimp wp: mapM_wp')+
  done

lemma delete_asid_pool_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs\<rbrace>
    delete_asid_pool base pptr
  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding delete_asid_pool_def
  apply (wp modify_wp)
      apply (strengthen valid_vspace_objs_arm_asid_table_unmap)
      apply (wpsimp wp: mapM_wp')+
  done

crunch valid_vspace_objs[wp]: cap_swap_for_delete "valid_vspace_objs"

lemma set_asid_pool_arch_objs_unmap'':
 "\<lbrace>(valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p) and K(f = (ap |` S))\<rbrace> set_asid_pool p f \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply simp
  apply (rule set_asid_pool_vspace_objs_unmap)
  done

lemmas set_asid_pool_vspace_objs_unmap'' = set_asid_pool_arch_objs_unmap''


lemma restrict_eq_asn_none: "f(N := None) = f |` {s. s \<noteq> N}" by auto

lemma delete_asid_valid_arch_objs[wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace> delete_asid a b \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding delete_asid_def
  apply (wpsimp wp: set_asid_pool_arch_objs_unmap'')
  apply (fastforce simp: restrict_eq_asn_none)
  done

lemma delete_asid_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace> delete_asid a b \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding delete_asid_def
  apply (wpsimp wp: set_asid_pool_vspace_objs_unmap'')
  apply (fastforce simp: restrict_eq_asn_none)
  done

lemma store_pte_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs and valid_pte pte\<rbrace>
    store_pte p pte
  \<lbrace>\<lambda>_. (valid_vspace_objs)\<rbrace>"
  unfolding store_pte_def
  apply wp
  apply clarsimp
  apply (unfold valid_vspace_objs_def)
  apply (erule_tac x="p && ~~ mask pt_bits" in allE)
  apply auto
done

declare get_cap_global_refs[wp]

crunch valid_global_refs[wp]: cap_swap_for_delete "valid_global_refs"
  (wp: set_cap_globals dxo_wp_weak
   simp: crunch_simps
   ignore: set_object cap_swap_ext)

crunch valid_global_refs[wp]: empty_slot "valid_global_refs"
  (wp: hoare_drop_imps set_cap_globals dxo_wp_weak
   simp: cap_range_def
   ignore: set_object empty_slot_ext)

lemma thread_set_fault_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> thread_set (tcb_fault_update A) thread \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (wp thread_set_global_refs_triv thread_set_refs_trivial thread_set_obj_at_impossible | simp)+
  apply (rule ball_tcb_cap_casesI, simp+)
  done


lemma cap_swap_for_delete_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps\<rbrace> cap_swap_for_delete a b \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding cap_swap_for_delete_def
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_weakenE)
  done

lemma mapM_x_swp_store_pte_reads_respects':
  "reads_respects aag l (invs and (cte_wp_at ((=) (ArchObjectCap (PageTableCap word option))) slot) and K (is_subject aag word))
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

lemma mapM_x_swp_store_pde_reads_respects':
  "reads_respects aag l (cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap word option))) slot and valid_objs and K(is_subject aag word))
             (mapM_x (swp store_pde InvalidPDE)
               (map ((\<lambda>x. x + word) \<circ> swp (<<) 2) [0.e.(kernel_base >> 20) - 1]))"
  apply (wp mapM_x_ev)
   apply simp
   apply (rule equiv_valid_guard_imp)
    apply (wp store_pde_reads_respects)
   apply clarsimp
   apply (subgoal_tac "is_aligned word pd_bits")
    apply (simp add: pd_bits_store_pde_helper)
   apply (frule (1) cte_wp_valid_cap)
   apply (simp add: valid_cap_def cap_aligned_def pd_bits_def pageBits_def)
  apply simp
  apply wp
    apply (clarsimp simp: wellformed_pde_def)+
  done

lemma mapM_x_swp_store_pte_pas_refined_simple:
  "invariant  (mapM_x (swp store_pte InvalidPTE) A) (pas_refined aag)"
  by (wpsimp wp: mapM_x_wp' store_pte_pas_refined_simple)

lemma mapM_x_swp_store_pde_pas_refined_simple:
  "invariant (mapM_x (swp store_pde InvalidPDE) A) (pas_refined aag)"
  by (wpsimp wp: mapM_x_wp' store_pde_pas_refined_simple)

end

end
