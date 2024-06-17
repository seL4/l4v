(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Interrupt_IF
imports ArchFinalise_IF
begin

crunch cap_delete_one
  for valid_global_objs[wp]: "valid_global_objs"
  (wp: dxo_wp_weak simp: unless_def ignore: empty_slot_ext)


locale Interrupt_IF_1 =
  fixes aag :: "'a subject_label PAS"
  assumes arch_invoke_irq_handler_reads_respects[wp]:
    "reads_respects_f aag (l :: 'a subject_label) (silc_inv aag st) (arch_invoke_irq_handler hi)"
  and arch_invoke_irq_control_reads_respects:
    "reads_respects aag l (K (arch_authorised_irq_ctl_inv aag irq_ctl_inv))
                    (arch_invoke_irq_control irq_ctl_inv)"
  and arch_invoke_irq_control_globals_equiv:
    "\<lbrace>globals_equiv st and valid_arch_state and valid_global_objs\<rbrace>
     arch_invoke_irq_control ai
     \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  and arch_invoke_irq_handler_globals_equiv[wp]:
    "arch_invoke_irq_handler hi \<lbrace>globals_equiv st\<rbrace>"
begin

(* invs comes from cap_delete_one *)
lemma invoke_irq_handler_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs and pas_refined aag
                                           and irq_handler_inv_valid irq_inv
                                           and K (authorised_irq_hdl_inv aag irq_inv))
                    (invoke_irq_handler irq_inv)"
  apply (case_tac irq_inv)
    apply (simp)
    apply (rule equiv_valid_guard_imp)
     apply wpsimp
    apply fastforce
   apply (wp reads_respects_f[OF cap_insert_reads_respects]
             cap_delete_one_reads_respects_f[where st=st]
             reads_respects_f[OF get_irq_slot_reads_respects, where Q="\<top>"]
             cap_insert_silc_inv'' cap_delete_one_silc_inv_subject
             cap_delete_one_cte_wp_at_other hoare_weak_lift_imp
             hoare_vcg_ex_lift slots_holding_overlapping_caps_from_silc_inv[where aag=aag and st=st]
          | simp | simp add: get_irq_slot_def)+
   apply (clarsimp simp: pas_refined_def irq_map_wellformed_aux_def)
   apply ((rule conjI, assumption) | clarsimp simp: conj_comms authorised_irq_hdl_inv_def)+
   apply (drule_tac p="(a,b)" in cte_wp_at_norm)
   apply (elim exE conjE, rename_tac cap')
   apply (drule_tac cap=cap' in silc_invD)
     apply assumption
    apply (fastforce simp: intra_label_cap_def cap_points_to_label_def
                           interrupt_derived_ntfn_cap_identical_refs)
   apply (fastforce simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def
                          interrupt_derived_ntfn_cap_identical_refs)
  apply (clarsimp)
  apply (wpsimp wp: reads_respects_f[OF get_irq_slot_reads_respects, where Q=\<top>]
                    cap_delete_one_reads_respects_f)
  apply (auto simp: authorised_irq_hdl_inv_def)[1]
  done

lemma invoke_irq_control_reads_respects:
  "reads_respects aag l (K (authorised_irq_ctl_inv aag i)) (invoke_irq_control i)"
  apply (cases i)
   apply (wp cap_insert_reads_respects set_irq_state_reads_respects | simp)+
   apply (clarsimp simp: authorised_irq_ctl_inv_def)
  apply (simp add: authorised_irq_ctl_inv_def)
  apply (rule arch_invoke_irq_control_reads_respects[simplified])
  done

lemma invoke_irq_control_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and valid_global_objs\<rbrace>
   invoke_irq_control a
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (induct a)
   apply (wpsimp wp: set_irq_state_globals_equiv cap_insert_globals_equiv''
                     set_irq_state_valid_global_objs arch_invoke_irq_control_globals_equiv)+
  done

lemma invoke_irq_handler_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state and valid_global_objs\<rbrace>
   invoke_irq_handler a
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (induct a)
  by (wpsimp wp: modify_wp cap_insert_globals_equiv''
                 cap_delete_one_globals_equiv cap_delete_one_valid_global_objs)+

subsection "reads_respects_g"

lemma invoke_irq_handler_reads_respects_f_g:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_f_g aag l (silc_inv aag st and invs and pas_refined aag
                                             and irq_handler_inv_valid irq_inv
                                             and K (authorised_irq_hdl_inv aag irq_inv))
                      (invoke_irq_handler irq_inv)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_f_g])
    apply (rule invoke_irq_handler_reads_respects_f[OF domains_distinct])
   apply (rule doesnt_touch_globalsI)
   apply (wp invoke_irq_handler_globals_equiv | simp)+
  by auto

lemma invoke_irq_control_reads_respects_g:
  "reads_respects_g aag l (valid_global_objs and valid_arch_state
                                             and K (authorised_irq_ctl_inv aag i))
                    (invoke_irq_control i)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule invoke_irq_control_reads_respects)
   apply (rule doesnt_touch_globalsI)
   apply (wp invoke_irq_control_globals_equiv | simp)+
  done

end

end
