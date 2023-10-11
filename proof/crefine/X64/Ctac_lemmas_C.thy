(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* seL4-specific lemmas for automation framework for C refinement *)

theory Ctac_lemmas_C
imports
  Ctac
begin

context kernel
begin

lemma c_guard_abs_cte:
  fixes p :: "cte_C ptr"
  shows "\<forall>s s'. (s, s') \<in> rf_sr \<and> cte_at' (ptr_val p) s \<and> True \<longrightarrow> s' \<Turnstile>\<^sub>c p"
  apply (cases p)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule (1) rf_sr_ctes_of_cliftE)
  apply (simp add: typ_heap_simps')
  done

lemmas ccorres_move_c_guard_cte [ccorres_pre] = ccorres_move_c_guards  [OF c_guard_abs_cte]

lemma c_guard_abs_tcb:
  fixes p :: "tcb_C ptr"
  shows "\<forall>s s'. (s, s') \<in> rf_sr \<and> tcb_at' (ctcb_ptr_to_tcb_ptr p) s \<and> True \<longrightarrow> s' \<Turnstile>\<^sub>c p"
  apply clarsimp
  apply (drule (1) tcb_at_h_t_valid)
  apply simp
  done

lemmas ccorres_move_c_guard_tcb [ccorres_pre] = ccorres_move_c_guards [OF c_guard_abs_tcb]

lemma cte_array_relation_array_assertion:
  "gsCNodes s p = Some n \<Longrightarrow> cte_array_relation s cstate
    \<Longrightarrow> array_assertion (cte_Ptr p) (2 ^ n) (hrs_htd (t_hrs_' cstate))"
  apply (rule h_t_array_valid_array_assertion)
   apply (clarsimp simp: cvariable_array_map_relation_def)
  apply simp
  done

lemma rf_sr_tcb_ctes_array_assertion':
  "\<lbrakk> (s, s') \<in> rf_sr; tcb_at' (ctcb_ptr_to_tcb_ptr tcb) s \<rbrakk>
    \<Longrightarrow> array_assertion (cte_Ptr (ptr_val tcb && ~~mask tcbBlockSizeBits))
        (unat tcbCNodeEntries) (hrs_htd (t_hrs_' (globals s')))"
  apply (rule h_t_array_valid_array_assertion, simp_all add: tcbCNodeEntries_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        cvariable_array_map_relation_def
                        cpspace_relation_def)
  apply (drule obj_at_ko_at', clarsimp)
  apply (drule spec, drule mp, rule exI, erule ko_at_projectKO_opt)
  apply (frule ptr_val_tcb_ptr_mask)
  apply (simp add: mask_def)
  done

lemmas rf_sr_tcb_ctes_array_assertion
  = rf_sr_tcb_ctes_array_assertion'[simplified objBits_defs mask_def, simplified]

lemma rf_sr_tcb_ctes_array_assertion2:
  "\<lbrakk> (s, s') \<in> rf_sr; tcb_at' tcb s \<rbrakk>
    \<Longrightarrow> array_assertion (cte_Ptr tcb)
        (unat tcbCNodeEntries) (hrs_htd (t_hrs_' (globals s')))"
  apply (frule(1) rf_sr_tcb_ctes_array_assertion[where
      tcb="tcb_ptr_to_ctcb_ptr t" for t, simplified])
  apply (simp add: ptr_val_tcb_ptr_mask)
  done

lemma array_assertion_abs_tcb_ctes':
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> tcb_at' (ctcb_ptr_to_tcb_ptr (tcb s')) s \<and> (n s' \<le> unat tcbCNodeEntries)
    \<longrightarrow> (x s' = 0 \<or> array_assertion (cte_Ptr (ptr_val (tcb s') && ~~mask tcbBlockSizeBits)) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> tcb_at' tcb' s \<and> (n s' \<le> unat tcbCNodeEntries)
    \<longrightarrow> (x s' = 0 \<or> array_assertion (cte_Ptr tcb') (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (safe intro!: disjCI2)
   apply (drule(1) rf_sr_tcb_ctes_array_assertion' rf_sr_tcb_ctes_array_assertion2
     | erule array_assertion_shrink_right | simp)+
  done

lemmas array_assertion_abs_tcb_ctes
  = array_assertion_abs_tcb_ctes'[simplified objBits_defs mask_def, simplified]

lemma array_assertion_abs_tcb_ctes_add':
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> tcb_at' (ctcb_ptr_to_tcb_ptr (tcb s')) s
        \<and> (n s' \<ge> 0 \<and> (case strong of True \<Rightarrow> n s' + 1 | False \<Rightarrow> n s') \<le> uint tcbCNodeEntries)
    \<longrightarrow> ptr_add_assertion (cte_Ptr (ptr_val (tcb s') && ~~mask tcbBlockSizeBits)) (n s')
                strong (hrs_htd (t_hrs_' (globals s')))"
  apply (clarsimp, drule(1) rf_sr_tcb_ctes_array_assertion')
  apply (simp add: ptr_add_assertion_positive, rule disjCI2)
  apply (erule array_assertion_shrink_right)
  apply (cases strong, simp_all add: unat_def del: nat_uint_eq)
  done

lemmas array_assertion_abs_tcb_ctes_add
  = array_assertion_abs_tcb_ctes_add'[simplified objBits_defs mask_def, simplified]

lemmas ccorres_move_array_assertion_tcb_ctes [ccorres_pre]
    = ccorres_move_array_assertions [OF array_assertion_abs_tcb_ctes(1)]
      ccorres_move_array_assertions [OF array_assertion_abs_tcb_ctes(2)]
      ccorres_move_Guard_Seq[OF array_assertion_abs_tcb_ctes_add]
      ccorres_move_Guard[OF array_assertion_abs_tcb_ctes_add]

lemma c_guard_abs_tcb_ctes':
  fixes p :: "cte_C ptr"
  shows "\<forall>s s'. (s, s') \<in> rf_sr \<and> tcb_at' (ctcb_ptr_to_tcb_ptr (tcb s')) s
    \<and> (n < ucast tcbCNodeEntries) \<longrightarrow> s' \<Turnstile>\<^sub>c cte_Ptr (((ptr_val (tcb s') && ~~mask tcbBlockSizeBits)
        + n * 2^cteSizeBits))"
  apply (clarsimp)
  apply (rule c_guard_abs_cte[rule_format], intro conjI, simp_all)
  apply (simp add: cte_at'_obj_at', rule disjI2)
  apply (frule ptr_val_tcb_ptr_mask)
  apply (rule_tac x="n * 2^cteSizeBits" in bexI)
   apply (simp add: mask_def)
  apply (simp add: word_less_nat_alt tcbCNodeEntries_def tcb_cte_cases_def objBits_defs)
  apply (case_tac "unat n", simp_all add: unat_eq_of_nat, rename_tac n_rem)
  apply (case_tac "n_rem", simp_all add: unat_eq_of_nat, (rename_tac n_rem)?)+
  done

lemmas c_guard_abs_tcb_ctes = c_guard_abs_tcb_ctes'[simplified objBits_defs mask_def, simplified]
lemmas ccorres_move_c_guard_tcb_ctes [ccorres_pre] = ccorres_move_c_guards  [OF c_guard_abs_tcb_ctes]

lemma c_guard_abs_pte:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> pte_at' (ptr_val p) s \<and> True
              \<longrightarrow> s' \<Turnstile>\<^sub>c (p :: pte_C ptr)"
  apply (clarsimp simp: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule cmap_relationE1[OF rf_sr_cpte_relation])
   apply (erule ko_at_projectKO_opt)
  apply (fastforce intro: typ_heap_simps)
  done

lemmas ccorres_move_c_guard_pte = ccorres_move_c_guards [OF c_guard_abs_pte]

lemma array_assertion_abs_pt:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_table_at' pd s)
        \<and> (n s' \<le> 2 ^ (ptBits - 3) \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (pte_Ptr pd) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (drule(1) page_table_at_rf_sr, clarsimp)
  apply (erule clift_array_assertion_imp,
         simp_all add: bit_simps)
  apply (rule_tac x=0 in exI, simp)
  done

lemmas ccorres_move_array_assertion_pt
    = ccorres_move_array_assertions[OF array_assertion_abs_pt]

lemma c_guard_abs_pde:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> pde_at' (ptr_val p) s \<and> True
              \<longrightarrow> s' \<Turnstile>\<^sub>c (p :: pde_C ptr)"
  apply (clarsimp simp: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule cmap_relationE1[OF rf_sr_cpde_relation])
   apply (erule ko_at_projectKO_opt)
  apply (fastforce intro: typ_heap_simps)
  done

lemmas ccorres_move_c_guard_pde = ccorres_move_c_guards [OF c_guard_abs_pde]

lemma array_assertion_abs_pd:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_directory_at' pd s)
        \<and> (n s' \<le> 2 ^ (pdBits - 3) \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (pde_Ptr pd) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (drule(1) page_directory_at_rf_sr, clarsimp)
  apply (erule clift_array_assertion_imp, simp_all add: bit_simps)
  apply (rule_tac x=0 in exI, simp)
  done

lemmas ccorres_move_array_assertion_pd
    = ccorres_move_array_assertions[OF array_assertion_abs_pd]

lemma c_guard_abs_pdpte:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> pdpte_at' (ptr_val p) s \<and> True
              \<longrightarrow> s' \<Turnstile>\<^sub>c (p :: pdpte_C ptr)"
  apply (clarsimp simp: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule cmap_relationE1[OF rf_sr_cpdpte_relation])
   apply (erule ko_at_projectKO_opt)
  apply (fastforce intro: typ_heap_simps)
  done

lemmas ccorres_move_c_guard_pdpte = ccorres_move_c_guards [OF c_guard_abs_pdpte]

lemma array_assertion_abs_pdpt:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (pd_pointer_table_at' pd s)
        \<and> (n s' \<le> 2 ^ (pdptBits - 3) \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (pdpte_Ptr pd) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (drule(1) pd_pointer_table_at_rf_sr, clarsimp)
  apply (erule clift_array_assertion_imp,
         simp_all add: bit_simps)
  apply (rule_tac x=0 in exI, simp)
  done

lemmas ccorres_move_array_assertion_pdpt
    = ccorres_move_array_assertions[OF array_assertion_abs_pdpt]

lemma c_guard_abs_pml4e:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> pml4e_at' (ptr_val p) s \<and> True
              \<longrightarrow> s' \<Turnstile>\<^sub>c (p :: pml4e_C ptr)"
  apply (clarsimp simp: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule cmap_relationE1[OF rf_sr_cpml4e_relation])
   apply (erule ko_at_projectKO_opt)
  apply (fastforce intro: typ_heap_simps)
  done

lemmas ccorres_move_c_guard_pml4e = ccorres_move_c_guards [OF c_guard_abs_pml4e]

lemma array_assertion_abs_pml4:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_map_l4_at' pd s)
        \<and> (n s' \<le> 2 ^ (pml4Bits - 3) \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (pml4e_Ptr pd) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (drule(1) page_map_l4_at_rf_sr, clarsimp)
  apply (erule clift_array_assertion_imp, simp_all add: bit_simps)
  apply (rule_tac x=0 in exI, simp)
  done

lemmas ccorres_move_array_assertion_pml4
    = ccorres_move_array_assertions[OF array_assertion_abs_pml4]

lemma move_c_guard_ap:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> asid_pool_at' (ptr_val p) s \<and> True
              \<longrightarrow> s' \<Turnstile>\<^sub>c (p :: asid_pool_C ptr)"
  apply (clarsimp simp: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule cmap_relationE1 [OF rf_sr_cpspace_asidpool_relation])
   apply (erule ko_at_projectKO_opt)
  apply (fastforce intro: typ_heap_simps)
  done

lemmas ccorres_move_c_guard_ap = ccorres_move_c_guards [OF move_c_guard_ap]

lemma array_assertion_abs_irq:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> True
        \<and> (n s' \<le> 256 \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion intStateIRQNode_Ptr (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (erule clift_array_assertion_imp, (simp add: exI[where x=0])+)
  done

lemmas ccorres_move_array_assertion_irq
    = ccorres_move_array_assertions [OF array_assertion_abs_irq]

lemma ccorres_Guard_intStateIRQNode_array_Ptr_Seq:
  assumes "ccorres_underlying rf_sr \<Gamma> r xf arrel axf A C hs a (c;; d)"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf A C hs a (Guard F {s. s \<Turnstile>\<^sub>c intStateIRQNode_array_Ptr} c;; d)"
  by (rule ccorres_guard_imp2[OF ccorres_move_Guard_Seq[where P=\<top> and P'=\<top>, OF _ assms]]
      ; simp add: rf_sr_def cstate_relation_def Let_def)

lemmas ccorres_Guard_intStateIRQNode_array_Ptr =
  ccorres_Guard_intStateIRQNode_array_Ptr_Seq[where d=SKIP, simplified ccorres_seq_skip']
  ccorres_Guard_intStateIRQNode_array_Ptr_Seq

lemma rf_sr_gsCNodes_array_assertion:
  "gsCNodes s p = Some n \<Longrightarrow> (s, s') \<in> rf_sr
    \<Longrightarrow>  array_assertion (cte_Ptr p) (2 ^ n) (hrs_htd (t_hrs_' (globals s')))"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                     cte_array_relation_array_assertion)

end

end

