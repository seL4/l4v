(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchRetype_IF
imports Retype_IF
begin

context Arch begin global_naming RISCV64

named_theorems Retype_IF_assms

lemma modify_underlying_memory_update_0_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top>
                   (modify (underlying_memory_update (\<lambda>m. m(x := word_rsplit 0 ! 7,
                                                            x + 1 := word_rsplit 0 ! 6,
                                                            x + 2 := word_rsplit 0 ! 5,
                                                            x + 3 := word_rsplit 0 ! 4,
                                                            x + 4 := word_rsplit 0 ! 3,
                                                            x + 5 := word_rsplit 0 ! 2,
                                                            x + 6 := word_rsplit 0 ! Suc 0,
                                                            x + 7 := word_rsplit 0 ! 0))))"
  by (fastforce simp: equiv_valid_def2 equiv_valid_2_def in_monad
                elim: equiv_forE
               intro: equiv_forI)

lemma storeWord_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top> (storeWord x 0)"
  unfolding storeWord_def
  by (wp modify_underlying_memory_update_0_ev assert_inv | simp add: no_irq_def upto.simps comp_def)+

lemma clearMemory_ev[Retype_IF_assms]:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) (\<lambda>_. True) (clearMemory ptr bits)"
  unfolding clearMemory_def
  apply (rule equiv_valid_guard_imp)
   apply (rule mapM_x_ev[OF storeWord_ev])
   apply (rule wp_post_taut | simp)+
  done

lemma freeMemory_ev[Retype_IF_assms]:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) (\<lambda>_. True) (freeMemory ptr bits)"
  unfolding freeMemory_def
  apply (rule equiv_valid_guard_imp)
   apply (rule mapM_x_ev[OF storeWord_ev])
   apply (rule wp_post_taut | simp)+
  done

lemma set_pt_globals_equiv:
  "\<lbrace>globals_equiv st and (\<lambda>s. a \<noteq> global_pt s)\<rbrace>
   set_pt a b
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (unfold set_pt_def gets_map_def)
  apply (subst gets_apply)
  apply (wpsimp wp: gets_apply_ev set_object_globals_equiv)
  apply (fastforce elim: reads_equivE equiv_forE simp: opt_map_def)
  done

lemma set_pt_reads_respects:
  "reads_respects aag l (K (is_subject aag a)) (set_pt a b)"
  apply (unfold set_pt_def gets_map_def)
  apply (subst gets_apply)
  apply (wpsimp wp: gets_apply_ev set_object_reads_respects)
  apply (fastforce elim: reads_equivE equiv_forE simp: opt_map_def)
  done

lemma set_pt_reads_respects_g:
  "reads_respects_g aag l (\<lambda> s. is_subject aag ptr \<and> ptr \<noteq> global_pt s) (set_pt ptr pt)"
  by (fastforce intro: equiv_valid_guard_imp[OF reads_respects_g] doesnt_touch_globalsI
                       set_pt_reads_respects set_pt_globals_equiv)

crunch clearMemory
  for irq_state[Retype_IF_assms, wp]: "\<lambda>s. P (irq_state s)"
  (wp: crunch_wps simp: crunch_simps storeWord_def ignore_del: clearMemory)

crunch freeMemory
  for irq_state[Retype_IF_assms, wp]: "\<lambda>s. P (irq_state s)"
  (wp: crunch_wps simp: crunch_simps storeWord_def)

lemma get_pt_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_pt ptr)"
  apply (unfold gets_map_def)
  apply (subst gets_apply)
  apply (wpsimp wp: gets_apply_ev)
  apply (fastforce elim: reads_equivE equiv_forE simp: opt_map_def)
  done

lemma get_pt_revg:
  "reads_equiv_valid_g_inv A aag (\<lambda> s. ptr = riscv_global_pt (arch_state s)) (get_pt ptr)"
  apply (unfold gets_map_def)
  apply (subst gets_apply)
  apply (wp gets_apply_ev')
    defer
    apply (wp hoare_drop_imps)
   apply (rule conjI)
    apply assumption
   apply simp
  apply (auto simp: reads_equiv_g_def globals_equiv_def opt_map_def)
  done

lemma store_pte_reads_respects:
  "reads_respects aag l (K (is_subject aag (ptr && ~~ mask pt_bits))) (store_pte ptr pte)"
  unfolding store_pte_def fun_app_def
  apply (wp set_pt_reads_respects get_pt_rev)
  apply (clarsimp)
  done

lemma store_pte_globals_equiv:
  "\<lbrace>globals_equiv s and (\<lambda> s. ptr && ~~ mask pt_bits \<noteq> riscv_global_pt (arch_state s))\<rbrace>
   store_pte ptr pde
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding store_pte_def
  apply (wp set_pt_globals_equiv)
  apply simp
  done

lemma store_pte_reads_respects_g:
  "reads_respects_g aag l (\<lambda>s. is_subject aag (ptr && ~~ mask pt_bits) \<and>
                               ptr && ~~ mask pt_bits \<noteq> riscv_global_pt (arch_state s))
                    (store_pte ptr pte)"
  by (fastforce intro: equiv_valid_guard_imp[OF reads_respects_g] doesnt_touch_globalsI
                       store_pte_reads_respects store_pte_globals_equiv)

lemma get_pte_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag (ptr && ~~ mask pt_bits))) (get_pte ptr)"
  unfolding gets_map_def fun_app_def
  apply (subst gets_apply)
  apply (wpsimp wp: gets_apply_ev)
  apply (fastforce elim: reads_equivE equiv_forE simp: ptes_of_def obind_def opt_map_def)
  done

lemma get_pte_revg:
  "reads_equiv_valid_g_inv A aag (\<lambda>s. (ptr && ~~ mask pt_bits) = riscv_global_pt (arch_state s))
                                 (get_pte ptr)"
  apply (unfold gets_map_def)
  apply (subst gets_apply)
  apply (wp gets_apply_ev')
    defer
    apply (wp hoare_drop_imps)
   apply (rule conjI)
    apply assumption
   apply simp
  apply (auto simp: reads_equiv_g_def globals_equiv_def opt_map_def ptes_of_def obind_def)
  done

lemma copy_global_mappings_reads_respects_g:
  "reads_respects_g aag l
     ((\<lambda>s. x \<noteq> riscv_global_pt (arch_state s)) and pspace_aligned and valid_global_arch_objs
                                                and K (is_aligned x pt_bits \<and> is_subject aag x))
     (copy_global_mappings x)"
  unfolding copy_global_mappings_def
  apply (rule gen_asm_ev)
  apply clarsimp
  apply (rule bind_ev_pre)
     prefer 3
     apply (rule_tac P'="\<lambda>s. is_subject aag x \<and> x \<noteq> riscv_global_pt (arch_state s) \<and>
                            pspace_aligned s \<and> valid_global_arch_objs s" in hoare_weaken_pre)
      apply (rule gets_sp)
     apply (assumption)
    apply (wp mapM_x_ev store_pte_reads_respects_g get_pte_revg)
     apply (simp only: pt_index_def)
     apply (subst table_base_offset_id)
       apply clarsimp
      apply (clarsimp simp: pte_bits_def word_size_bits_def pt_bits_def
                            table_size_def ptTranslationBits_def mask_def)
      apply (word_bitwise, fastforce)
     apply (erule ssubst[OF table_base_offset_id])
      apply (clarsimp simp: pte_bits_def word_size_bits_def pt_bits_def
                            table_size_def ptTranslationBits_def mask_def)
      apply (word_bitwise, fastforce)
     apply clarsimp
    apply (wpsimp wp: get_pte_inv store_pte_aligned)+
  apply (fastforce dest: reads_equiv_gD simp: globals_equiv_def)
  done

lemma dmo_no_mem_globals_equiv:
  "\<lbrakk> \<And>P. f \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>;
     \<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>;
     \<And>P. f \<lbrace>\<lambda>ms. P (exclusive_state ms)\<rbrace> \<rbrakk>
     \<Longrightarrow> do_machine_op f \<lbrace>globals_equiv s\<rbrace>"
  unfolding do_machine_op_def
  apply (wp | simp add: split_def)+
  apply atomize
  apply (erule_tac x="(=) (underlying_memory (machine_state sa))" in allE)
  apply (erule_tac x="(=) (device_state (machine_state sa))" in allE)
  apply (erule_tac x="(=) (exclusive_state (machine_state sa))" in allE)
  apply (fastforce simp: valid_def globals_equiv_def idle_equiv_def)
  done

lemma dmo_mol_globals_equiv[wp]:
  "do_machine_op (machine_op_lift f) \<lbrace>globals_equiv s\<rbrace>"
  by (wpsimp wp: dmo_no_mem_globals_equiv simp: machine_op_lift_def machine_rest_lift_def)

lemma mol_globals_equiv:
  "machine_op_lift mop \<lbrace>\<lambda>ms. globals_equiv st (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  unfolding machine_op_lift_def
  apply (simp add: machine_rest_lift_def split_def)
  apply wp
  apply (clarsimp simp: globals_equiv_def idle_equiv_def)
  done

lemma storeWord_globals_equiv:
  "storeWord p v \<lbrace>\<lambda>ms. globals_equiv st (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  unfolding storeWord_def
  apply (simp add: is_aligned_mask[symmetric])
  apply wp
  apply (clarsimp simp: globals_equiv_def idle_equiv_def)
  done

lemma dmo_clearMemory_globals_equiv[Retype_IF_assms]:
  "do_machine_op (clearMemory ptr (2 ^ bits)) \<lbrace>globals_equiv s\<rbrace>"
  apply (simp add: do_machine_op_def clearMemory_def split_def)
  apply wpsimp
  apply (erule use_valid)
  by (wpsimp wp: mapM_x_wp' storeWord_globals_equiv mol_globals_equiv)+

lemma dmo_freeMemory_globals_equiv[Retype_IF_assms]:
  "do_machine_op (freeMemory ptr bits) \<lbrace>globals_equiv s\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: do_machine_op_def freeMemory_def split_def)
   apply (wp)
  apply clarsimp
  apply (erule use_valid)
   apply (wp mapM_x_wp' storeWord_globals_equiv mol_globals_equiv)
  apply (simp_all)
  done

lemma init_arch_objects_reads_respects_g:
  "reads_respects_g aag l \<top> (init_arch_objects new_type ptr num_objects obj_sz refs)"
  unfolding init_arch_objects_def by wp

lemma copy_global_mappings_globals_equiv:
  "\<lbrace>globals_equiv s and (\<lambda>s. x \<noteq> riscv_global_pt (arch_state s) \<and> is_aligned x pt_bits)\<rbrace>
   copy_global_mappings x
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding copy_global_mappings_def including classic_wp_pre
  apply simp
  apply wp
   apply (rule_tac Q'="\<lambda>_. globals_equiv s and (\<lambda>s. x \<noteq> riscv_global_pt (arch_state s) \<and>
                                                   is_aligned x pt_bits)" in hoare_strengthen_post)
    apply (wp mapM_x_wp[OF _ subset_refl] store_pte_globals_equiv)
    apply (simp only: pt_index_def)
    apply (subst table_base_offset_id)
      apply clarsimp
     apply (clarsimp simp: pte_bits_def word_size_bits_def pt_bits_def
                           table_size_def ptTranslationBits_def mask_def)
     apply (word_bitwise, fastforce)
  apply (simp_all)
  done

(* FIXME: cleanup this proof *)
lemma retype_region_globals_equiv[Retype_IF_assms]:
  notes blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                         Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  shows
    "\<lbrace>globals_equiv s and invs
                      and (\<lambda>s. \<exists>i. cte_wp_at (\<lambda>c. c = UntypedCap dev (p && ~~ mask sz) sz i) slot s \<and>
                                   (i \<le> unat (p && mask sz) \<or> pspace_no_overlap_range_cover p sz s))
                      and K (range_cover p sz (obj_bits_api type o_bits) num \<and> 0 < num)\<rbrace>
     retype_region p num o_bits type dev
     \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (simp only: retype_region_def foldr_upd_app_if fun_app_def K_bind_def)
  apply (wp dxo_wp_weak |simp)+
      apply (simp add: trans_state_update[symmetric] del: trans_state_update)
     apply (wp | simp)+
  apply clarsimp
  apply (simp only: globals_equiv_def)
  apply (clarsimp split del: if_split)
  apply (subgoal_tac "pspace_no_overlap_range_cover p sz sa")
   apply (rule conjI)
    apply (clarsimp simp: pspace_no_overlap_def)
    apply (drule_tac x="riscv_global_pt (arch_state sa)" in spec)
    apply (frule valid_global_arch_objs_pt_at[OF invs_valid_global_arch_objs])
    apply (clarsimp simp: invs_def valid_state_def valid_global_objs_def
                          valid_vso_at_def obj_at_def ptr_add_def)
    apply (frule_tac p=x in range_cover_subset)
      apply (simp add: blah)
     apply simp
    apply (frule range_cover_subset')
     apply simp
    apply (clarsimp simp: p_assoc_help)
    apply (drule disjoint_subset_neg1[OF _ subset_thing], rule is_aligned_no_wrap')
        apply (clarsimp simp: valid_pspace_def pspace_aligned_def)
        apply (drule_tac x="riscv_global_pt (arch_state sa)" and A="dom (kheap sa)"  in bspec)
         apply (simp add: domI)
        apply simp
       apply (rule word_power_less_1)
       apply (simp add: table_size_def ptTranslationBits_def pte_bits_def word_size_bits_def)
      apply simp
     apply simp
    apply simp
    apply (drule (1) subset_trans)
    apply (erule_tac P="a \<in> b" for a b in notE)
    apply (erule_tac A="{p + c..d}" for c d in subsetD)
    apply (simp add: blah)
    apply (rule is_aligned_no_wrap')
     apply (rule is_aligned_add[OF _ is_aligned_mult_triv2])
     apply (simp add: range_cover_def)
    apply (rule word_power_less_1)
    apply (simp add: range_cover_def)
   apply (erule updates_not_idle)
   apply (clarsimp simp: pspace_no_overlap_def)
   apply (drule_tac x="idle_thread sa" in spec)
   apply (clarsimp simp: invs_def valid_state_def valid_global_objs_def
                         obj_at_def ptr_add_def valid_idle_def pred_tcb_at_def)
   apply (frule_tac p=a in range_cover_subset)
     apply (simp add: blah)
    apply simp
   apply (frule range_cover_subset')
    apply simp
   apply (clarsimp simp: p_assoc_help)
   apply (drule disjoint_subset_neg1[OF _ subset_thing], rule is_aligned_no_wrap')
       apply (clarsimp simp: valid_pspace_def pspace_aligned_def)
       apply (drule_tac x="idle_thread sa" and A="dom (kheap sa)"  in bspec)
        apply (simp add: domI)
       apply simp
      apply uint_arith
     apply simp+
   apply (drule (1) subset_trans)
   apply (erule_tac P="a \<in> b" for a b in notE)
   apply (erule_tac A="{idle_thread_ptr..d}" for d in subsetD)
   apply (simp add: blah)
   apply (erule_tac t=idle_thread_ptr in subst)
   apply (rule is_aligned_no_wrap')
    apply (rule is_aligned_add[OF _ is_aligned_mult_triv2])
    apply (simp add: range_cover_def)+
  apply (auto intro!: cte_wp_at_pspace_no_overlapI simp: range_cover_def word_bits_def)[1]
  done

lemma no_irq_freeMemory[Retype_IF_assms]:
  "no_irq (freeMemory ptr sz)"
  apply (simp add: freeMemory_def)
  apply (wp no_irq_mapM_x no_irq_storeWord)
  done

lemma equiv_asid_detype[Retype_IF_assms]:
  "equiv_asid asid s s' \<Longrightarrow> equiv_asid asid (detype N s) (detype N s')"
  by (auto simp: equiv_asid_def)

end


global_interpretation Retype_IF_1?: Retype_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Retype_IF_assms)?)
qed


context Arch begin global_naming RISCV64

lemma detype_globals_equiv:
  "\<lbrace>globals_equiv st and ((\<lambda>s. riscv_global_pt (arch_state s) \<notin> S) and (\<lambda>s. idle_thread s \<notin> S))\<rbrace>
   modify (detype S)
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (wp)
  apply (clarsimp simp: globals_equiv_def detype_def idle_equiv_def tcb_at_def2)
  done

lemma detype_reads_respects_g:
  "reads_respects_g aag l ((\<lambda>s. riscv_global_pt (arch_state s) \<notin> S) and (\<lambda>s. idle_thread s \<notin> S))
                    (modify (detype S))"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g)
    apply (rule detype_reads_respects)
   apply (rule doesnt_touch_globalsI[OF detype_globals_equiv])
  apply simp
  done

lemma delete_objects_reads_respects_g:
 "reads_equiv_valid_g_inv (affects_equiv aag l) aag
    (\<lambda>s. riscv_global_pt (arch_state s) \<notin> ptr_range p b \<and>
         idle_thread s \<notin> ptr_range p b \<and>
         is_aligned p b \<and> 2 \<le> b \<and> b < word_bits)
    (delete_objects p b)"
  apply (simp add: delete_objects_def2)
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_freeMemory_reads_respects_g)
    apply (rule detype_reads_respects_g)
   apply wp
  apply (unfold ptr_range_def)
  apply simp
  done

lemma reset_untyped_cap_reads_respects_g:
 "reads_equiv_valid_g_inv (affects_equiv aag (l :: 'a subject_label)) aag
    (\<lambda>s. cte_wp_at is_untyped_cap slot s \<and> invs s \<and> ct_active s \<and> only_timer_irq_inv irq st s \<and>
         is_subject aag (fst slot) \<and> (descendants_of slot (cdt s) = {}))
    (reset_untyped_cap slot)"
  apply (simp add: reset_untyped_cap_def cong: if_cong)
  apply (rule equiv_valid_guard_imp)
   apply (wp set_cap_reads_respects_g dmo_clearMemory_reads_respects_g
          | simp add: unless_def when_def split del: if_split)+
       apply (rule_tac I="invs and cte_wp_at (\<lambda>cp. is_untyped_cap rv
                                                 \<and> (\<exists>idx. cp = free_index_update (\<lambda>_. idx) rv)
                                                 \<and> free_index_of rv \<le> 2 ^ (bits_of rv)
                                                 \<and> is_subject aag (fst slot)) slot
                               and pspace_no_overlap (untyped_range rv)
                               and only_timer_irq_inv irq st
                               and (\<lambda>s. descendants_of slot (cdt s) = {})" in mapME_x_ev)
        apply (rule equiv_valid_guard_imp)
         apply wp
             apply (rule reads_respects_g_from_inv)
              apply (rule preemption_point_reads_respects[where irq=irq and st=st])
             apply ((wp preemption_point_inv set_cap_reads_respects_g set_untyped_cap_invs_simple
                       only_timer_irq_inv_pres[where Q=\<top>, OF _ set_cap_domain_sep_inv]
                       dmo_clearMemory_reads_respects_g
                     | simp)+)
         apply (strengthen empty_descendants_range_in)
         apply (wp only_timer_irq_inv_pres[where P=\<top> and Q=\<top>] no_irq_clearMemory
                | simp | wp (once) dmo_wp)+
        apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
        apply (frule(1) caps_of_state_valid)
        apply (clarsimp simp: valid_cap_simps cap_aligned_def field_simps
                              free_index_of_def invs_valid_global_objs)
       apply (simp add: aligned_add_aligned is_aligned_shiftl)
       apply (clarsimp simp: Kernel_Config.resetChunkBits_def)
       apply (rule hoare_pre)
        apply (wp preemption_point_inv' set_untyped_cap_invs_simple set_cap_cte_wp_at
                  set_cap_no_overlap only_timer_irq_inv_pres[where Q=\<top>, OF _ set_cap_domain_sep_inv]
                  irq_state_independent_A_conjI
               | simp)+
        apply (strengthen empty_descendants_range_in)
        apply (wp only_timer_irq_inv_pres[where P=\<top> and Q=\<top>] no_irq_clearMemory
               | simp | wp (once) dmo_wp)+
       apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
       apply (frule(1) caps_of_state_valid)
       apply (clarsimp simp: valid_cap_simps cap_aligned_def field_simps free_index_of_def)
      apply (wp | simp)+
      apply (wp delete_objects_reads_respects_g)
     apply (simp add: if_apply_def2)
     apply (strengthen invs_valid_global_objs)
     apply (wp add: delete_objects_invs_ex hoare_vcg_const_imp_lift
                    delete_objects_pspace_no_overlap_again
                    only_timer_irq_inv_pres[where P=\<top> and Q=\<top>]
                    delete_objects_valid_arch_state
               del: Untyped_AI.delete_objects_pspace_no_overlap
            | simp)+
    apply (rule get_cap_reads_respects_g)
   apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
  apply (frule(1) caps_of_state_valid)
  apply (clarsimp simp: valid_cap_simps cap_aligned_def field_simps
                        free_index_of_def invs_valid_global_objs)
  apply (frule valid_global_refsD2, clarsimp+)
  apply (clarsimp simp: ptr_range_def[symmetric] global_refs_def descendants_range_def2)
  apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
  apply (strengthen refl[where t=True] refl ex_tupleI[where t=slot] empty_descendants_range_in
         | clarsimp)+
  apply (drule ex_cte_cap_protects[OF _ _ _ _ order_refl], erule caps_of_state_cteD)
     apply (clarsimp simp: descendants_range_def2 empty_descendants_range_in)
    apply clarsimp+
  apply (fastforce dest: invs_valid_global_arch_objs valid_global_arch_objs_global_ptD
                   simp: untyped_min_bits_def ptr_range_def)
  done

lemma retype_region_ret_pt_aligned:
  "\<lbrace>K (range_cover ptr sz (obj_bits_api tp us) num_objects)\<rbrace>
   retype_region ptr num_objects us tp dev
   \<lbrace>\<lambda>rv. K (\<forall>ref \<in> set rv. tp = ArchObject PageTableObj \<longrightarrow> is_aligned ref pt_bits)\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule hoare_weaken_pre)
    apply (rule retype_region_aligned_for_init)
   apply simp
  apply (clarsimp simp: obj_bits_api_def default_arch_object_def pt_bits_def pageBits_def)
  done

lemma post_retype_invs_valid_global_objsI:
  "post_retype_invs ty rv s \<Longrightarrow> valid_global_objs s"
  by (clarsimp simp: post_retype_invs_def invs_def valid_state_def split: if_split_asm)

lemma invoke_untyped_reads_respects_g_wcap[Retype_IF_assms]:
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
                         atLeastatMost_subset_iff atLeastLessThan_iff Int_atLeastAtMost
                         atLeastatMost_empty_iff split_paired_Ex
  shows "reads_respects_g aag (l :: 'a subject_label)
           (invs and valid_untyped_inv_wcap ui (Some (UntypedCap dev ptr sz idx))
                 and only_timer_irq_inv irq st and ct_active and pas_refined aag
                 and K (authorised_untyped_inv aag ui))
           (invoke_untyped ui)"
  apply (case_tac ui)
  apply (rename_tac cslot_ptr reset ptr_base ptr' apiobject_type nat list dev')
  apply (case_tac "\<not> (dev' = dev \<and> ptr = ptr' && ~~ mask sz)")
   (* contradictory *)
   apply (rule equiv_valid_guard_imp, rule_tac gen_asm_ev'[where P="\<top>" and Q=False], simp)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (simp add: invoke_untyped_def mapM_x_def[symmetric])
  apply (wpsimp wp: mapM_x_ev'' create_cap_reads_respects_g
                    hoare_vcg_ball_lift init_arch_objects_reads_respects_g)+
          apply (wp retype_region_reads_respects_g[where sz=sz and slot="slot_of_untyped_inv ui"])
         apply (rule_tac Q'="\<lambda>rvc s. (\<forall>x\<in>set rvc. is_subject aag x) \<and>
                                    (\<forall>x\<in>set rvc. is_aligned x (obj_bits_api apiobject_type nat)) \<and>
                                    ((0::obj_ref) < of_nat (length list)) \<and>
                                    post_retype_invs apiobject_type rvc s \<and>
                                    global_refs s \<inter> set rvc = {} \<and>
                                    (\<forall>x\<in>set list. is_subject aag (fst x))"
                     for sz in hoare_strengthen_post)
          apply (wp retype_region_ret_is_subject[where sz=sz, simplified]
                    retype_region_global_refs_disjoint[where sz=sz]
                    retype_region_ret_pt_aligned[where sz=sz]
                    retype_region_aligned_for_init[where sz=sz]
                    retype_region_post_retype_invs_spec[where sz=sz])
         apply clarsimp
         apply (fastforce simp: global_refs_def obj_bits_api_def
                                post_retype_invs_valid_arch_stateI
                                post_retype_invs_valid_global_objsI
                                pageBits_def default_arch_object_def
                         intro: post_retype_invs_pspace_alignedI
                                post_retype_invs_valid_arch_stateI
                          elim: in_set_zipE)
        apply (rule set_cap_reads_respects_g)
       apply simp
       apply (wp hoare_vcg_ex_lift set_cap_cte_wp_at_cases
                 hoare_vcg_disj_lift set_cap_no_overlap
                 set_free_index_invs_UntypedCap
                 set_untyped_cap_caps_overlap_reserved
                 set_cap_caps_no_overlap
                 region_in_kernel_window_preserved)
      apply (wp when_ev delete_objects_reads_respects_g hoare_vcg_disj_lift
                delete_objects_pspace_no_overlap
                delete_objects_descendants_range_in
                delete_objects_caps_no_overlap
                region_in_kernel_window_preserved
                get_cap_reads_respects_g get_cap_wp
             | simp split del: if_split)+
    apply (rule reset_untyped_cap_reads_respects_g[where irq=irq and st=st])
   apply (rule_tac P="authorised_untyped_inv aag ui \<and>
                      (\<forall>p \<in> ptr_range ptr sz. is_subject aag p)" in hoare_gen_asmE)
   apply (rule validE_validE_R,
          rule_tac E'="\<top>\<top>"
               and Q'="\<lambda>_. invs and valid_untyped_inv_wcap ui (Some (UntypedCap dev ptr sz (If reset 0 idx)))
                               and ct_active
                               and (\<lambda>s. reset \<longrightarrow> pspace_no_overlap {ptr .. ptr + 2 ^ sz - 1} s)"
                in hoare_strengthen_postE)
     apply (rule hoare_pre, wp whenE_wp)
      apply (rule validE_validE_R, rule hoare_strengthen_postE, rule reset_untyped_cap_invs_etc)
       apply (clarsimp simp only: if_True simp_thms, intro conjI, assumption+)
      apply simp
     apply assumption
    apply clarify
    apply (frule(2) invoke_untyped_proofs.intro)
    apply (clarsimp simp: cte_wp_at_caps_of_state bits_of_def
                          free_index_of_def untyped_range_def
                          if_split[where P="\<lambda>x. x \<le> unat v" for v]
               split del: if_split)
    apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
    apply (strengthen refl)
    apply (strengthen invs_valid_global_objs invs_arch_state)
    apply (clarsimp simp: authorised_untyped_inv_def conj_comms invoke_untyped_proofs.simps)
    apply (simp add: arg_cong[OF mask_out_sub_mask, where f="\<lambda>y. x - y" for x]
                     field_simps invoke_untyped_proofs.idx_le_new_offs
                     invoke_untyped_proofs.idx_compare' untyped_range_def)
    apply (strengthen caps_region_kernel_window_imp[mk_strg I E])
    apply (simp add: invoke_untyped_proofs.simps untyped_range_def invs_cap_refs_in_kernel_window
                     atLeastatMost_subset_iff[where b=x and d=x for x]
               cong: conj_cong split del: if_split)
    apply (intro conjI)
          (* mostly clagged from Untyped_AI *)
          apply (simp add: atLeastatMost_subset_iff word_and_le2)
         apply (case_tac reset)
          apply (clarsimp elim!: pspace_no_overlap_subset del: subsetI
                           simp: blah word_and_le2)
         apply (drule invoke_untyped_proofs.ps_no_overlap)
         apply (simp add: field_simps)
        apply (simp add: Int_commute, erule disjoint_subset2[rotated])
        apply (simp add: atLeastatMost_subset_iff word_and_le2)
       apply (clarsimp dest!: invoke_untyped_proofs.idx_le_new_offs)
      apply (simp add: ptr_range_def)
      apply (erule ball_subset, rule range_subsetI[OF _ order_refl])
      apply (simp add: word_and_le2)
     apply (erule order_trans[OF invoke_untyped_proofs.subset_stuff])
     apply (simp add: atLeastatMost_subset_iff word_and_le2)
    apply (drule invoke_untyped_proofs.usable_range_disjoint)
    apply (clarsimp simp: field_simps mask_out_sub_mask shiftl_t2n)
   apply blast
  apply (clarsimp simp: cte_wp_at_caps_of_state authorised_untyped_inv_def)
  apply (strengthen refl)
  apply (frule(1) cap_auth_caps_of_state)
  apply (simp add: aag_cap_auth_def untyped_range_def
                   aag_has_Control_iff_owns ptr_range_def[symmetric])
  apply (erule disjE, simp_all)[1]
  done

lemma delete_objects_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and (\<lambda>s. is_aligned p b \<and> 2 \<le> b \<and> b < word_bits \<and>
                              riscv_global_pt (arch_state s) \<notin> ptr_range p b \<and>
                              idle_thread s \<notin> ptr_range p b)\<rbrace>
   delete_objects p b
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wp detype_globals_equiv dmo_freeMemory_globals_equiv)
  apply (clarsimp simp: ptr_range_def)+
  done

lemma reset_untyped_cap_globals_equiv:
  "\<lbrace>globals_equiv st and invs and cte_wp_at is_untyped_cap slot
                     and ct_active and (\<lambda>s. descendants_of slot (cdt s) = {})\<rbrace>
   reset_untyped_cap slot
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (simp add: reset_untyped_cap_def cong: if_cong)
  apply (rule hoare_pre)
   apply (wp set_cap_globals_equiv dmo_clearMemory_globals_equiv
             preemption_point_inv | simp add: unless_def)+
     apply (rule valid_validE)
     apply (rule_tac P="cap_aligned cap \<and> is_untyped_cap cap" in hoare_gen_asm)
     apply (rule_tac Q'="\<lambda>_ s. valid_global_objs s \<and> valid_arch_state s \<and> globals_equiv st s"
                  in hoare_strengthen_post)
      apply (rule validE_valid, rule mapME_x_wp')
      apply (rule hoare_pre)
       apply (wp set_cap_globals_equiv dmo_clearMemory_globals_equiv
                 preemption_point_inv | simp add: if_apply_def2)+
    apply (clarsimp simp: is_cap_simps ptr_range_def[symmetric]
                          cap_aligned_def bits_of_def free_index_of_def)
    apply (clarsimp simp: Kernel_Config.resetChunkBits_def)
    apply (strengthen invs_valid_global_objs invs_arch_state)
    apply (wp delete_objects_invs_ex hoare_vcg_const_imp_lift get_cap_wp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state descendants_range_def2 is_cap_simps bits_of_def
             split del: if_split)
  apply (frule caps_of_state_valid_cap, clarsimp+)
  apply (clarsimp simp: valid_cap_simps cap_aligned_def untyped_min_bits_def)
  apply (frule valid_global_refsD2, clarsimp+)
  apply (clarsimp simp: ptr_range_def[symmetric] global_refs_def)
  apply (strengthen empty_descendants_range_in)
  apply (cases slot)
  apply (fastforce dest: valid_global_arch_objs_global_ptD[OF invs_valid_global_arch_objs])
  done

lemma invoke_untyped_globals_equiv:
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
                         atLeastatMost_subset_iff atLeastLessThan_iff Int_atLeastAtMost
                         atLeastatMost_empty_iff split_paired_Ex
  shows "\<lbrace>globals_equiv st and invs and valid_untyped_inv ui and ct_active\<rbrace>
         invoke_untyped ui
         \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre, rule invoke_untyped_Q)
       apply (wp create_cap_globals_equiv)
       apply auto[1]
      apply wpsimp
     apply (rule hoare_pre, wp retype_region_globals_equiv[where slot="slot_of_untyped_inv ui"])
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (strengthen refl)
     apply simp
    apply (wp set_cap_globals_equiv)
    apply auto[1]
   apply (wp reset_untyped_cap_globals_equiv)
  apply (cases ui, clarsimp simp: cte_wp_at_caps_of_state)
  done

end


global_interpretation Retype_IF_2?: Retype_IF_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Retype_IF_assms)?)
qed


requalify_facts
  RISCV64.reset_untyped_cap_reads_respects_g
  RISCV64.reset_untyped_cap_globals_equiv
  RISCV64.invoke_untyped_globals_equiv
  RISCV64.storeWord_globals_equiv

end
