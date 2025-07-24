(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch-specific lemmas on arch get/set object etc *)

theory ArchArchAcc_R
imports ArchAcc_R
begin

unbundle l4v_word_context

context begin interpretation Arch . (*FIXME: arch-split*)

declare if_cong[cong] (* FIXME: if_cong *)

lemma asid_pool_at_ko:
  "asid_pool_at p s \<Longrightarrow> \<exists>pool. ko_at (ArchObj (AARCH64_A.ASIDPool pool)) p s"
  by (clarsimp simp: asid_pools_at_eq obj_at_def elim!: opt_mapE)

lemma corres_gets_asid:
  "corres (\<lambda>a c. a = c o ucast) \<top> \<top> (gets asid_table) (gets (armKSASIDTable \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemma asid_low_bits [simp]:
  "asidLowBits = asid_low_bits"
  by (simp add: asid_low_bits_def asidLowBits_def)

lemma pteBits_pte_bits[simp]:
  "pteBits = pte_bits"
  by (simp add: bit_simps pteBits_def)

lemma cte_map_in_cnode1:
  "\<lbrakk> x \<le> x + 2 ^ (cte_level_bits + length y) - 1 \<rbrakk> \<Longrightarrow> x \<le> cte_map (x, y)"
  apply (simp add: cte_map_def)
  apply (rule word_plus_mono_right2[where b="mask (cte_level_bits + length y)"])
   apply (simp add: mask_def add_diff_eq)
  apply (rule leq_high_bits_shiftr_low_bits_leq_bits)
  apply (rule of_bl_max)
  done

lemma pspace_aligned_cross:
  "\<lbrakk> pspace_aligned s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow> pspace_aligned' s'"
  apply (clarsimp simp: pspace_aligned'_def pspace_aligned_def pspace_relation_def)
  apply (rename_tac p' ko')
  apply (prop_tac "p' \<in> pspace_dom (kheap s)", fastforce)
  apply (thin_tac "pspace_dom k = p" for k p)
  apply (clarsimp simp: pspace_dom_def)
  apply (drule bspec, fastforce)+
  apply clarsimp
  apply (rename_tac ko' a a' P ko)
  apply (erule (1) obj_relation_cutsE; clarsimp simp: objBits_simps)
       \<comment>\<open>CNode\<close>
       apply (clarsimp simp: cte_map_def)
       apply (simp only: cteSizeBits_def cte_level_bits_def)
       apply (rule is_aligned_add)
        apply (erule is_aligned_weaken, simp)
       apply (rule is_aligned_weaken)
        apply (rule is_aligned_shiftl_self, simp)
      \<comment>\<open>TCB\<close>
      apply (clarsimp simp: tcbBlockSizeBits_def elim!: is_aligned_weaken)
     \<comment>\<open>PageTable\<close>
     apply (rule is_aligned_add)
      apply (erule is_aligned_weaken)
      apply (simp add: bit_simps)
     apply (rule is_aligned_shift)
    \<comment>\<open>DataPage\<close>
    apply (rule is_aligned_add)
     apply (erule is_aligned_weaken)
     apply (rule pbfs_atleast_pageBits)
    apply (rule is_aligned_shift)
   \<comment>\<open>Other non-arch\<close>
   apply (simp add: other_obj_relation_def)
   apply (clarsimp simp: bit_simps' tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def
                   split: kernel_object.splits Structures_A.kernel_object.splits)
  \<comment>\<open>Other arch\<close>
  apply (clarsimp simp: bit_simps' archObjSize_def other_aobj_relation_def
                  split: kernel_object.splits arch_kernel_obj.splits;
         simp add: bit_simps' split: arch_kernel_object.splits)
  done

lemma of_bl_shift_cte_level_bits:
  "(of_bl z :: machine_word) << cte_level_bits \<le> mask (cte_level_bits + length z)"
  by word_bitwise
     (simp add: test_bit_of_bl bit_simps word_size cte_level_bits_def rev_bl_order_simps)

lemma obj_relation_cuts_range_limit:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk>
   \<Longrightarrow> \<exists>x n. p' = p + x \<and> is_aligned x n \<and> n \<le> obj_bits ko \<and> x \<le> mask (obj_bits ko)"
  apply (erule (1) obj_relation_cutsE; clarsimp)
       apply (drule (1) wf_cs_nD)
       apply (clarsimp simp: cte_map_def)
       apply (rule_tac x=cte_level_bits in exI)
       apply (simp add: is_aligned_shift of_bl_shift_cte_level_bits)
      apply (rule_tac x=tcbBlockSizeBits in exI)
      apply (simp add: tcbBlockSizeBits_def)
     apply (rule_tac x=pte_bits in exI)
     apply (simp add: is_aligned_shift mask_def)
     apply (rule shiftl_less_t2n)
      apply (simp add: table_size_def)
     apply (simp add: bit_simps)
    apply (rule_tac x=pageBits in exI)
    apply (simp add: is_aligned_shift pbfs_atleast_pageBits)
    apply (simp add: mask_def shiftl_t2n mult_ac)
    apply (erule word_less_power_trans2, rule pbfs_atleast_pageBits)
    apply (simp add: pbfs_less_wb'[unfolded word_bits_def, simplified])
   apply fastforce+
  done

lemma obj_relation_cuts_range_mask_range:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko'; is_aligned p (obj_bits ko) \<rbrakk>
   \<Longrightarrow> p' \<in> mask_range p (obj_bits ko)"
  apply (drule (1) obj_relation_cuts_range_limit, clarsimp)
  apply (rule conjI)
   apply (rule word_plus_mono_right2; assumption?)
   apply (simp add: is_aligned_no_overflow_mask)
  apply (erule word_plus_mono_right)
  apply (simp add: is_aligned_no_overflow_mask)
  done

lemma obj_relation_cuts_obj_bits:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk> \<Longrightarrow> objBitsKO ko' \<le> obj_bits ko"
  apply (erule (1) obj_relation_cutsE;
          clarsimp simp: objBits_simps objBits_defs bit_simps cte_level_bits_def
                         pbfs_atleast_pageBits[simplified bit_simps])
  apply (cases ko; simp add: other_obj_relation_def other_aobj_relation_def objBits_defs
                        split: kernel_object.splits)
  apply (case_tac ako; case_tac ko';
         clarsimp simp: archObjSize_def other_aobj_relation_def is_other_obj_relation_type_def
                  split: kernel_object.split arch_kernel_object.splits)
  done

lemmas is_aligned_add_step_le' = is_aligned_add_step_le[simplified mask_2pm1 add_diff_eq]

lemma pspace_distinct_cross:
  "\<lbrakk> pspace_distinct s; pspace_aligned s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow>
   pspace_distinct' s'"
  apply (frule (1) pspace_aligned_cross)
  apply (clarsimp simp: pspace_distinct'_def)
  apply (rename_tac p' ko')
  apply (rule pspace_dom_relatedE; assumption?)
  apply (rename_tac p ko P)
  apply (frule (1) pspace_alignedD')
  apply (frule (1) pspace_alignedD)
  apply (rule ps_clearI, assumption)
   apply (case_tac ko'; simp add: objBits_simps objBits_defs bit_simps')
   apply (simp split: arch_kernel_object.splits add: bit_simps')
  apply (rule ccontr, clarsimp)
  apply (rename_tac x' ko_x')
  apply (frule_tac x=x' in pspace_alignedD', assumption)
  apply (rule_tac x=x' in pspace_dom_relatedE; assumption?)
  apply (rename_tac x ko_x P')
  apply (frule_tac p=x in pspace_alignedD, assumption)
  apply (case_tac "p = x")
   apply clarsimp
   apply (erule (1) obj_relation_cutsE; clarsimp)
       apply (clarsimp simp: cte_relation_def cte_map_def objBits_simps)
       apply (rule_tac n=cte_level_bits in is_aligned_add_step_le'; assumption?)
         apply (rule is_aligned_add; (rule is_aligned_shift)?)
         apply (erule is_aligned_weaken, simp add: cte_level_bits_def)
        apply (rule is_aligned_add; (rule is_aligned_shift)?)
        apply (erule is_aligned_weaken, simp add: cte_level_bits_def)
       apply (simp add: cte_level_bits_def cteSizeBits_def)
      apply (clarsimp simp: pte_relation_def objBits_simps)
      apply (rule_tac n=pte_bits in is_aligned_add_step_le'; assumption?)
     apply (simp add: objBitsKO_Data)
     apply (rule_tac n=pageBits in is_aligned_add_step_le'; assumption?)
    apply (case_tac ko; simp split: if_split_asm)
    apply (rename_tac ako, case_tac ako; simp add: is_other_obj_relation_type_def split: if_split_asm)
   apply (case_tac ako; simp add: is_other_obj_relation_type_def split: if_split_asm)
  apply (frule (1) obj_relation_cuts_obj_bits)
  apply (drule (2) obj_relation_cuts_range_mask_range)+
  apply (prop_tac "x' \<in> mask_range p' (objBitsKO ko')", simp add: mask_def add_diff_eq)
  apply (frule_tac x=p and y=x in pspace_distinctD; assumption?)
  apply (drule (4) mask_range_subsetD)
  apply (erule (2) in_empty_interE)
  done

lemma asid_pool_at_cross:
  "\<lbrakk> asid_pool_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> asid_pool_at' p s'"
  apply (drule (2) pspace_distinct_cross)
  apply (clarsimp simp: obj_at_def typ_at'_def ko_wp_at'_def)
  apply (prop_tac "p \<in> pspace_dom (kheap s)")
   apply (clarsimp simp: pspace_dom_def)
   apply (rule bexI)
    prefer 2
    apply fastforce
   apply clarsimp
  apply (clarsimp simp: pspace_relation_def)
  apply (drule bspec, fastforce)
  apply (clarsimp simp: other_aobj_relation_def objBits_simps
                  split: kernel_object.splits arch_kernel_object.splits)
  apply (frule (1) pspace_alignedD)
  apply (rule conjI, simp add: bit_simps)
  apply (clarsimp simp: pspace_distinct'_def)
  apply (drule bspec, fastforce)
  apply (simp add: objBits_simps)
  done

lemma corres_cross_over_asid_pool_at:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> asid_pool_at p s \<and> pspace_distinct s \<and> pspace_aligned s;
     corres r P (Q and asid_pool_at' p) f g \<rbrakk> \<Longrightarrow>
   corres r P Q f g"
  apply (rule corres_cross_over_guard[where Q="Q and asid_pool_at' p"])
   apply (drule meta_spec, drule (1) meta_mp, clarsimp)
   apply (erule asid_pool_at_cross, clarsimp simp: state_relation_def; assumption)
  apply assumption
  done

lemma getObject_ASIDPool_corres:
  "p' = p \<Longrightarrow>
   corres asid_pool_relation
          (asid_pool_at p and pspace_aligned and pspace_distinct) \<top>
          (get_asid_pool p) (getObject p')"
  apply (rule corres_cross_over_asid_pool_at, fastforce)
  apply (simp add: getObject_def gets_map_def split_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all)[1]
   apply (clarsimp simp: lookupAround2_known1)
   apply (clarsimp simp: obj_at'_def objBits_simps)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
   apply simp
   apply (clarsimp simp add: objBits_simps
                      split: option.split)
  apply (clarsimp simp: in_monad loadObject_default_def)
  apply (simp add: bind_assoc exec_gets)
  apply (drule asid_pool_at_ko)
  apply (clarsimp simp: obj_at_def assert_opt_def fail_def return_def in_omonad
                  split: option.split)
  apply (simp add: in_magnitude_check objBits_simps pageBits_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_aobj_relation_def)
  done

lemma storePTE_cte_wp_at'[wp]:
  "storePTE ptr val \<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad projectKO_opts_defs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad projectKO_opts_defs)
  apply simp
  done

lemma storePTE_state_refs_of[wp]:
  "storePTE ptr val \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  unfolding storePTE_def
  apply (wp setObject_state_refs_of_eq;
         clarsimp simp: updateObject_default_def in_monad)
  done

lemma storePTE_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
     storePTE ptr val
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imps setObject_state_hyp_refs_of_eq
             simp: storePTE_def updateObject_default_def in_monad)

crunch setIRQState
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
crunch getIRQSlot
  for inv[wp]: "P"

lemma setObject_ASIDPool_corres[corres]:
  "\<lbrakk> p = p'; a = map_option abs_asid_entry o inv ASIDPool a' o ucast \<rbrakk> \<Longrightarrow>
  corres dc (asid_pool_at p and pspace_aligned and pspace_distinct) \<top>
            (set_asid_pool p a) (setObject p' a')"
  apply (simp add: set_asid_pool_def)
  apply (rule corres_underlying_symb_exec_l[where P=P and Q="\<lambda>_. P" for P])
    apply (rule corres_no_failI; clarsimp)
    apply (clarsimp simp: gets_map_def bind_def simpler_gets_def assert_opt_def fail_def return_def
                          obj_at_def in_omonad
                    split: option.splits)
   prefer 2
   apply wpsimp
  apply (rule corres_cross_over_asid_pool_at, fastforce)
  apply (rule corres_guard_imp)
    apply (rule setObject_other_arch_corres[where P="\<lambda>ko::asidpool. True"])
           apply simp
          apply (clarsimp simp: obj_at'_def)
          apply (erule map_to_ctes_upd_other, simp, simp)
         apply (simp add: a_type_def is_other_obj_relation_type_def)
        apply (simp add: objBits_simps)+
      apply (simp add: objBits_simps pageBits_def)+
    apply (simp add: other_aobj_relation_def asid_pool_relation_def)
   apply (simp add: typ_at'_def obj_at'_def ko_wp_at'_def)
   apply clarsimp
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp)
   apply (clarsimp simp: obj_at_def exs_valid_def assert_def a_type_def return_def fail_def)
   apply (auto split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm if_split_asm)[1]
  apply (simp add: typ_at_to_obj_at_arches)
  done

lemma p_le_table_base:
  "is_aligned p pte_bits \<Longrightarrow> p + mask pte_bits \<le> table_base pt_t p + mask (table_size pt_t)"
  apply (simp add: is_aligned_mask word_plus_and_or_coroll table_size_def pt_bits_def)
  apply (subst word_plus_and_or_coroll, word_eqI_solve)
  apply word_bitwise
  apply (simp add: word_size bit_simps)
  done

lemma table_index_in_table:
  "table_index pt_t p \<le> mask (ptTranslationBits pt_t)"
  by (simp add: pt_bits_def table_size_def word_bool_le_funs flip: shiftr_then_mask_commute)

lemma pte_at_cross:
  "\<lbrakk> pte_at pt_t p s; pspace_relation (kheap s) (ksPSpace s'); pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> pte_at' p s'"
  apply (drule (2) pspace_distinct_cross)
  apply (clarsimp simp: pte_at_def ptes_of_def in_omonad obj_at_def typ_at'_def ko_wp_at'_def)
  apply (simp split: if_split_asm)
  apply (prop_tac "p \<in> pspace_dom (kheap s)")
   apply (clarsimp simp: pspace_dom_def)
   apply (rule bexI)
    prefer 2
    apply fastforce
   apply (clarsimp simp: ran_def image_iff)
   apply (rule_tac x="table_index pt_t p" in bexI)
    apply (simp add: table_base_index_eq)
   apply (simp add: table_index_in_table)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule bspec, fastforce)
  apply clarsimp
  apply (drule_tac x="table_index pt_t p" in bspec)
   apply (simp add: table_index_in_table)
  apply (simp add: table_base_index_eq)
  apply (clarsimp simp: pte_relation_def)
  apply (clarsimp simp: objBits_simps)
  apply (clarsimp simp: pspace_distinct'_def)
  apply (drule bspec, fastforce)
  apply (simp add: objBits_simps)
  done

lemma corres_cross_over_pte_at:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> pte_at pt_t p s \<and> pspace_distinct s \<and> pspace_aligned s;
     corres r P (P' and pte_at' p) f g\<rbrakk> \<Longrightarrow>
   corres r P P' f g"
  apply (rule corres_cross_over_guard[where Q="P' and pte_at' p"])
   apply (drule meta_spec, drule (1) meta_mp, clarsimp)
   apply (erule pte_at_cross; assumption?)
   apply (simp add: state_relation_def)
  apply assumption
  done

lemma getObject_PTE_corres:
  "corres pte_relation' (pte_at pt_t p and pspace_aligned and pspace_distinct) \<top>
          (get_pte pt_t p) (getObject p)"
  apply (rule corres_cross_over_pte_at, fastforce)
  apply (simp add: getObject_def gets_map_def split_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: ko_wp_at'_def typ_at'_def lookupAround2_known1)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp)
   apply (clarsimp simp: objBits_def cong: option.case_cong)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
    apply (simp add: objBits_simps word_bits_def)
   apply simp
  apply (clarsimp simp: in_monad loadObject_default_def)
  apply (simp add: bind_assoc exec_gets fst_assert_opt)
  apply (clarsimp simp: pte_at_eq)
  apply (clarsimp simp: ptes_of_def)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def in_magnitude_check objBits_simps pte_bits_def word_size_bits_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def elim!: opt_mapE)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pte_relation_def)
  apply (drule_tac x="table_index pt_t p" in bspec)
   apply (simp add: table_index_in_table)
  apply (clarsimp simp: table_base_index_eq[simplified bit_simps] bit_simps)
  done

lemmas aligned_distinct_pte_atI'
    = aligned_distinct_obj_atI'[where 'a=pte,
                                simplified, OF _ _ _ refl]

lemma one_less_2p_pte_bits[simp]:
  "(1::machine_word) < 2 ^ pte_bits"
  by (simp add: bit_simps)

lemma pt_apply_upd_eq':
  "idx \<le> mask (ptTranslationBits (pt_type pt)) \<Longrightarrow>
   pt_apply (pt_upd pt (table_index (pt_type pt) p) pte) idx =
   (if table_index (pt_type pt) p = idx then pte else pt_apply pt idx)"
  unfolding pt_apply_def pt_upd_def
  using table_index_mask_eq[where pt_t=NormalPT_T] table_index_mask_eq[where pt_t=VSRootPT_T]
  by (cases pt; clarsimp simp: ucast_eq_mask vs_index_ptTranslationBits pt_index_ptTranslationBits
                               word_le_mask_eq)

\<comment> \<open>setObject_other_corres unfortunately doesn't work here\<close>
lemma setObject_PT_corres:
  "pte_relation' pte pte' \<Longrightarrow>
   corres dc ((\<lambda>s. pts_of s (table_base pt_t p) = Some pt) and K (is_aligned p pte_bits \<and> pt_type pt = pt_t) and
              pspace_aligned and pspace_distinct) \<top>
          (set_pt (table_base pt_t p) (pt_upd pt (table_index pt_t p) pte))
          (setObject p pte')"
  apply (rule corres_cross_over_pte_at[where p=p])
   apply (fastforce simp: pte_at_eq ptes_of_def in_omonad)
  apply (simp add: set_pt_def get_object_def bind_assoc set_object_def gets_map_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def lookupAround2_known1)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp)
   apply (simp add: objBits_simps word_bits_def)
  apply (clarsimp simp: setObject_def in_monad split_def updateObject_default_def)
  apply (simp add: in_magnitude_check objBits_simps a_type_simps)
  apply (clarsimp simp: obj_at_def exec_gets)
  apply (clarsimp simp: exec_get put_def elim!: opt_mapE)
  apply (clarsimp simp: state_relation_def)
  apply (rule conjI)
   apply (clarsimp simp: pspace_relation_def split del: if_split)
   apply (rule conjI)
    apply (subst pspace_dom_update, assumption)
     apply (simp add: a_type_def)
    apply (auto simp: dom_def)[1]
   apply (rule conjI)
    apply (drule bspec, blast)
    apply clarsimp
    apply (drule_tac x = x in bspec)
     apply simp
    apply (rule conjI; clarsimp)
     apply (clarsimp simp: pte_relation_def pt_apply_upd_eq')
     apply (metis more_pt_inner_beauty)
    apply (clarsimp simp: pte_relation_def table_base_index_eq pt_apply_upd_eq'
                   dest!: more_pt_inner_beauty)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: pte_relation_def pt_apply_upd_eq')
    apply (metis more_pt_inner_beauty table_base_index_eq)
   apply clarsimp
   apply (drule bspec, assumption)
   apply clarsimp
   apply (erule (1) obj_relation_cutsE)
        apply simp
       apply clarsimp
      apply clarsimp
      apply (smt (verit, best) pspace_aligned_pts_ofD pts_of_Some pts_of_type_unique aobjs_of_Some
                               table_base_plus)
     apply ((simp split: if_split_asm)+)[2]
    apply (simp add: other_obj_relation_def split: Structures_A.kernel_object.splits)
   apply (simp add: other_aobj_relation_def split: arch_kernel_obj.splits)
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask (pt_bits (pt_type pt))" in allE)+
   apply fastforce
  apply (extract_conjunct \<open>match conclusion in "ready_queues_relation_2 _ _ _ _ _" \<Rightarrow> -\<close>)
   apply (prop_tac "typ_at' (koTypeOf (injectKO pte')) p b")
    apply (simp add: typ_at'_def ko_wp_at'_def)
   subgoal by (fastforce dest: tcbs_of'_non_tcb_update)
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done

lemma storePTE_corres:
  "pte_relation' pte pte' \<Longrightarrow>
  corres dc (pte_at pt_t p and pspace_aligned and pspace_distinct) \<top> (store_pte pt_t p pte) (storePTE p pte')"
  apply (simp add: store_pte_def storePTE_def)
  apply (rule corres_assume_pre)
  apply (rule corres_symb_exec_l)
     apply (rule corres_symb_exec_l[where P="pte_at pt_t p and pspace_aligned and pspace_distinct"])
        apply (rule corres_symb_exec_l)
           apply (erule setObject_PT_corres)
          prefer 2
          apply (rule assert_inv)
         apply wpsimp
        apply wpsimp
       prefer 2
       apply (wpsimp simp: ptes_of_def in_omonad obj_at_def pte_at_def split: if_split_asm)
      apply (clarsimp simp: exs_valid_def gets_map_def fst_assert_opt in_omonad ptes_of_def
                            exec_gets pte_at_def)
     apply (wpsimp simp: pte_at_def ptes_of_def in_omonad)
    apply (wpsimp simp: pte_at_def2)
   apply wpsimp
  apply (wpsimp simp: pte_at_def2)
  done

lemmas tableBitSimps[simplified bit_simps pteBits_pte_bits, simplified] = ptBits_def
lemmas bitSimps = tableBitSimps

lemma bit_simps_corres[simp]:
  "ptBits pt_t = pt_bits pt_t"
  by (simp add: bit_simps bitSimps)

defs checkPTAt_def:
  "checkPTAt pt_t p \<equiv> stateAssert (\<lambda>s. page_table_at' pt_t p s \<and>
                                        gsPTTypes (ksArchState s) p = Some pt_t) []"

lemma pte_relation_must_pte:
  "pte_relation m (ArchObj (PageTable pt)) ko \<Longrightarrow> \<exists>pte. ko = (KOArch (KOPTE pte))"
  apply (case_tac ko)
   apply (simp_all add:pte_relation_def)
  apply clarsimp
  done

lemma page_table_at_cross:
  "\<lbrakk> pt_at pt_t p s; pspace_aligned s; pspace_distinct s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow>
   page_table_at' pt_t p s'"
  apply (clarsimp simp: page_table_at'_def)
  apply (rule context_conjI)
   apply (clarsimp simp: obj_at_def)
   apply (frule (1) pspace_alignedD)
   apply (clarsimp simp: bit_simps split: if_splits)
  apply clarsimp
  apply (rule pte_at_cross; assumption?)
  apply (erule (2) page_table_pte_atI_nicer)
  done

lemma getPTE_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::pte) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def in_magnitude_check
                     in_monad valid_def obj_at'_def objBits_simps)

lemma check_pt_at_lift:
  "corres_inst_eq ptr ptr' \<Longrightarrow> \<forall>s s'. (s, s') \<in> state_relation \<longrightarrow> True \<longrightarrow>
   (pspace_aligned s \<and> pspace_distinct s \<and> pt_at pt_t ptr s \<and> ptr = ptr') \<longrightarrow>
    \<top> s' \<longrightarrow> page_table_at' pt_t ptr' s' \<and> gsPTTypes (ksArchState s') ptr' = Some pt_t"
  apply clarsimp
  apply (rule conjI, fastforce intro!: page_table_at_cross)
  by (fastforce simp: ghost_relation_def obj_at_def elim!: state_relationE)

lemmas checkPTAt_corres[corresK] =
  corres_stateAssert_implied_frame[OF check_pt_at_lift, folded checkPTAt_def]

lemma lookupPTSlotFromLevel_inv:
  "lookupPTSlotFromLevel level pt_ptr vptr \<lbrace>P\<rbrace>"
  apply (induct level arbitrary: pt_ptr)
   apply (subst lookupPTSlotFromLevel.simps)
   apply (wpsimp simp: pteAtIndex_def wp: getPTE_wp)
  apply (subst lookupPTSlotFromLevel.simps)
  apply (wpsimp simp: pteAtIndex_def checkPTAt_def wp: getPTE_wp|assumption)+
  done

declare lookupPTSlotFromLevel_inv[wp]

lemma lookupPTFromLevel_inv[wp]:
  "lookupPTFromLevel level pt vptr target_pt \<lbrace>P\<rbrace>"
proof (induct level arbitrary: pt)
  case 0 show ?case
    by (subst lookupPTFromLevel.simps, simp add: checkPTAt_def, wpsimp)
next
  case (Suc level)
  show ?case
    by (subst lookupPTFromLevel.simps, simp add: checkPTAt_def)
       (wpsimp wp: Suc getPTE_wp simp: pteAtIndex_def)
qed

lemma size_maxPTLevel[simp]:
  "size max_pt_level = maxPTLevel"
  by (simp add: maxPTLevel_def level_defs)

lemma ptBitsLeft_0[simp]:
  "ptBitsLeft 0 = pageBits"
  by (simp add: ptBitsLeft_def)

lemma ptBitsLeft_eq[simp]:
  "ptBitsLeft (size level) = pt_bits_left level"
  unfolding ptBitsLeft_def pt_bits_left_def
  by (clarsimp simp flip: vm_level.size_less_eq
               simp: asid_pool_level_size ptTranslationBits_def maxPTLevel_def
               split: if_splits)

lemma ptIndex_eq[simp]:
  "ptIndex (size level) p = pt_index level p"
  by (clarsimp simp: ptIndex_def pt_index_def levelType_def
               simp flip: size_maxPTLevel level_type_eq(1))

lemma ptSlotIndex_eq[simp]:
  "ptSlotIndex (size level) = pt_slot_offset level"
  by (clarsimp intro!: ext simp: ptSlotIndex_def pt_slot_offset_def)

lemmas ptSlotIndex_0[simp] = ptSlotIndex_eq[where level=0, simplified]

lemma pteAtIndex_corres:
  "level' = size level \<Longrightarrow>
   corres pte_relation'
     (pte_at pt_t (pt_slot_offset level pt vptr) and pspace_aligned and pspace_distinct)
     \<top>
     (get_pte pt_t (pt_slot_offset level pt vptr))
     (pteAtIndex level' pt vptr)"
  by (simp add: pteAtIndex_def) (rule getObject_PTE_corres)

lemma user_region_or:
  "\<lbrakk> vref \<in> user_region; vref' \<in> user_region \<rbrakk> \<Longrightarrow> vref || vref' \<in> user_region"
  by (simp add: user_region_def canonical_user_def le_mask_high_bits word_size)

lemmas bit_pred = bit0.pred bit1.pred

lemma lookupPTSlotFromLevel_corres:
  "\<lbrakk> level' = size level; pt' = pt; level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   corres (\<lambda>(level, p) (bits, p'). bits = pt_bits_left level \<and> p' = p)
     (pspace_aligned and pspace_distinct and valid_vspace_objs and valid_asid_table and
     \<exists>\<rhd> (level, pt) and K (vptr \<in> user_region \<and> level \<le> max_pt_level))
     \<top>
     (gets_the (pt_lookup_slot_from_level level 0 pt vptr \<circ> ptes_of))
     (lookupPTSlotFromLevel level' pt' vptr)"
proof (induct level arbitrary: pt pt' level')
  case 0
  thus ?case by (simp add: lookupPTSlotFromLevel.simps pt_bits_left_def)
next
  case (minus level)
  from `0 < level`
  obtain nlevel where nlevel: "level = nlevel + 1" by (auto intro: that[of "level-1"])
  with `0 < level`
  have nlevel1: "nlevel < nlevel + 1" using bit_pred by fastforce
  with nlevel
  have level: "size level = Suc (size nlevel)" by simp

  from `0 < level` `level \<le> max_pt_level`
  have level_m1: "level - 1 \<le> max_pt_level"
    by blast

  from level
  have levelType[simp]:
    "levelType (Suc (size nlevel)) = level_type level"
    unfolding levelType_def using vm_level.size_inj
    by fastforce

  define vref_step where
    "vref_step vref \<equiv> vref_for_level vref (level+1) || (pt_index level vptr << pt_bits_left level)"
    for vref

  from `level \<le> max_pt_level`
  have vref_for_level_step[simp]:
    "vref_for_level (vref_step vref) (level + 1) = vref_for_level vref (level + 1)"
    for vref
    unfolding vref_step_def
    using vref_for_level_pt_index_idem[of level level level vref vptr] by simp

  from `level \<le> max_pt_level`
  have pt_walk_vref[simp]:
    "pt_walk max_pt_level level pt (vref_step vref) =
     pt_walk max_pt_level level pt vref" for pt vref
    by - (rule pt_walk_vref_for_level_eq; simp)

  from `level \<le> max_pt_level`
  have vref_step_user_region[simp]:
    "\<lbrakk> vref \<in> user_region; vptr \<in> user_region \<rbrakk> \<Longrightarrow> vref_step vref \<in> user_region"
    for vref
    unfolding vref_step_def
    using nlevel1 nlevel
    by (auto intro!: user_region_or vref_for_level_user_region
             simp: pt_bits_left_def bit_simps user_region_def
                   pt_index_def canonical_user_def word_eqI_simps
             dest!: max_pt_level_enum)

  have pt_slot_offset_step[simp]:
    "\<lbrakk> is_aligned pt (pt_bits level); vref \<in> user_region \<rbrakk> \<Longrightarrow>
     pt_slot_offset level pt (vref_step vref) = pt_slot_offset level pt vptr" for vref
    unfolding vref_step_def using nlevel1 nlevel
    apply simp
    apply (clarsimp simp: pt_slot_offset_or_def user_region_def canonical_user_def)
    apply (simp add: pt_index_def pt_bits_left_def)
    apply (rule conjI; clarsimp)
     apply (simp add: plus_one_eq_asid_pool vref_for_level_def pt_bits_left_def)
     apply (rule conjI, simp add: max_pt_level_def)
     apply (clarsimp simp: level_defs bit_simps maxPTLevel_def)
     apply (solves \<open>cases config_ARM_PA_SIZE_BITS_40; clarsimp?; word_eqI_solve\<close>)
    apply (clarsimp simp: vref_for_level_def pt_bits_left_def)
    apply (rule conjI; clarsimp)
     apply (subgoal_tac "nlevel = max_pt_level - 1")
      apply (clarsimp simp: level_defs bit_simps maxPTLevel_def split: if_split_asm)
      apply word_eqI_solve
     apply (subst (asm) add.commute[where a=2])
     apply (drule add_implies_diff)
     apply (simp add: max_pt_level_def)
    apply (simp add: pt_bits_def)
    apply (prop_tac "level_type (nlevel + 1) = NormalPT_T")
     apply (drule max_pt_level_enum)
     (* Unfolding config_ARM_PA_SIZE_BITS_40_def here, because the level_enum only produces a
        contradiction in one of the branches when PA_40 is set. *)
     apply (solves \<open>auto simp: level_defs Kernel_Config.config_ARM_PA_SIZE_BITS_40_def\<close>)[1]
    apply (simp add: bit_simps)
    apply word_eqI
    apply (drule max_pt_level_enum)
    by (cases config_ARM_PA_SIZE_BITS_40, auto simp: max_pt_level_def2)

  from `0 < level` `level' = size level` `pt' = pt` level `level \<le> max_pt_level` level_m1
  show ?case
    apply (subst pt_lookup_slot_from_level_rec)
    apply (simp add: lookupPTSlotFromLevel.simps Let_def obind_comp_dist if_comp_dist
                     gets_the_if_distrib checkPTAt_def gets_the_oapply2_comp)
    apply (rule corres_guard_imp, rule corres_split[where r'=pte_relation'])
         apply (rule pteAtIndex_corres, simp)
        apply (rule corres_if3)
          apply (rename_tac pte pte', case_tac pte; (simp add: isPageTablePTE_def))
         apply (rule corres_stateAssert_implied[where P'=\<top>])
          apply (rule minus(1))
            apply (simp add: nlevel)
           apply (clarsimp simp: AARCH64_A.is_PageTablePTE_def pptr_from_pte_def getPPtrFromPTE_def
                                 paddr_from_ppn_def isPagePTE_def)
          apply simp
         apply clarsimp
         apply (prop_tac "pt_at NormalPT_T (getPPtrFromPTE pte) s")
          apply (drule (2) valid_vspace_objs_strongD; assumption?)
           apply simp
          apply (simp add: state_relation_def)
          apply (clarsimp simp: pt_at_eq in_omonad AARCH64_A.is_PageTablePTE_def pptr_from_pte_def
                                getPPtrFromPTE_def isPagePTE_def paddr_from_ppn_def)
         apply (frule page_table_at_cross; assumption?)
          apply (fastforce simp: state_relation_def)
         apply (fastforce simp: ghost_relation_def obj_at_def elim!: state_relationE)
        apply (rule corres_inst[where P=\<top> and P'=\<top>])
        apply (clarsimp simp: ptSlotIndex_def pt_slot_offset_def pt_index_def pt_bits_left_def
                              ptIndex_def ptBitsLeft_def)
        apply (rule conjI; clarsimp)
        apply (metis vm_level.size_less_eq size_maxPTLevel)
       apply wpsimp+
     apply (frule (5) vs_lookup_table_is_aligned)
     apply (rule conjI)
      apply (drule (5) valid_vspace_objs_strongD)
      apply (clarsimp simp: pte_at_def obj_at_def ptes_of_def in_omonad)
      apply (simp add: pt_slot_offset_def)
      apply (rule conjI, fastforce)
      apply (rule is_aligned_add)
       apply (erule is_aligned_weaken)
       apply (simp add: bit_simps)
      apply (rule is_aligned_shiftl, simp)
     apply clarsimp
     apply (rule_tac x=asid in exI)
     apply (rule_tac x="vref_step vref" in exI)
     apply (clarsimp simp: vs_lookup_table_def in_omonad split: if_split_asm)
     apply (rule conjI)
      apply (clarsimp simp: level_defs)
     apply (subst pt_walk_split_Some[where level'=level]; simp?)
      apply (drule vm_level.pred)
      apply simp
     apply (subst pt_walk.simps)
     apply (simp add: in_omonad)
    apply simp
    done
qed

lemma lookupPTSlot_corres:
  "corres (\<lambda>(level, p) (bits, p'). bits = pt_bits_left level \<and> p' = p)
          (pspace_aligned and pspace_distinct and valid_vspace_objs
             and valid_asid_table and \<exists>\<rhd>(max_pt_level,pt)
             and K (vptr \<in> user_region))
          \<top>
          (gets_the (pt_lookup_slot pt vptr \<circ> ptes_of)) (lookupPTSlot pt vptr)"
  unfolding lookupPTSlot_def pt_lookup_slot_def
  apply (corresKsimp corres: lookupPTSlotFromLevel_corres)
  apply (fastforce simp: vspace_pt_at_eq pt_type_def
                   dest!: valid_vspace_objs_strongD
                   split: pt.splits)
  done

lemma lookupPTFromLevel_corres:
  "\<lbrakk> level' = size level; pt' = pt \<rbrakk> \<Longrightarrow>
   corres (lfr \<oplus> ((=) \<circ> fst))
          (pspace_aligned and pspace_distinct and valid_vspace_objs
             and valid_asid_table and \<exists>\<rhd>(level,pt)
             and K (vptr \<in> user_region \<and> level \<le> max_pt_level \<and> pt \<noteq> target))
          \<top>
          (pt_lookup_from_level level pt vptr target)
          (lookupPTFromLevel level' pt' vptr target)"
proof (induct level arbitrary: level' pt pt')
  case 0
  then show ?case
    apply (subst lookupPTFromLevel.simps, subst pt_lookup_from_level_simps)
    apply simp
    apply (rule corres_gen_asm)
    apply (simp add: lookup_failure_map_def)
    done
next
  case (minus level)

  (* FIXME: unfortunate duplication from lookupPTSlotFromLevel_corres *)
  from `0 < level`
  obtain nlevel where nlevel: "level = nlevel + 1" by (auto intro: that[of "level-1"])
  with `0 < level`
  have nlevel1: "nlevel < nlevel + 1" using vm_level.pred by fastforce
  with nlevel
  have level: "size level = Suc (size nlevel)" by simp

  define vref_step where
    "vref_step vref \<equiv>
       vref_for_level vref (level+1) || (pt_index level vptr << pt_bits_left level)"
    for vref

  have vref_for_level_step[simp]:
    "level \<le> max_pt_level \<Longrightarrow>
     vref_for_level (vref_step vref) (level + 1) = vref_for_level vref (level + 1)"
    for vref
    unfolding vref_step_def
    using vref_for_level_pt_index_idem[of level level level vref vptr] by simp

  have pt_walk_vref[simp]:
    "level \<le> max_pt_level \<Longrightarrow>
     pt_walk max_pt_level level pt (vref_step vref) =
     pt_walk max_pt_level level pt vref" for pt vref
    by (rule pt_walk_vref_for_level_eq; simp)

  have vref_step_user_region[simp]:
    "\<lbrakk> vref \<in> user_region; vptr \<in> user_region; level \<le> max_pt_level \<rbrakk>
     \<Longrightarrow> vref_step vref \<in> user_region"
    for vref
    unfolding vref_step_def
    using nlevel1 nlevel
    by (auto intro!: user_region_or vref_for_level_user_region
             simp: pt_bits_left_def bit_simps user_region_def
                   pt_index_def canonical_user_def word_eqI_simps
             dest!: max_pt_level_enum)

  have pt_slot_offset_step[simp]:
    "\<lbrakk> is_aligned pt (pt_bits level); vref \<in> user_region \<rbrakk> \<Longrightarrow>
    pt_slot_offset level pt (vref_step vref) = pt_slot_offset level pt vptr" for vref
    unfolding vref_step_def using nlevel1 nlevel
    apply simp
    apply (clarsimp simp: pt_slot_offset_or_def user_region_def canonical_user_def)
    apply (simp add: pt_index_def pt_bits_left_def)
    apply (rule conjI; clarsimp)
     apply (simp add: plus_one_eq_asid_pool vref_for_level_def pt_bits_left_def)
     apply (rule conjI, simp add: max_pt_level_def)
     apply (clarsimp simp: level_defs bit_simps maxPTLevel_def)
     apply (solves \<open>cases config_ARM_PA_SIZE_BITS_40; clarsimp?; word_eqI_solve\<close>)
    apply (clarsimp simp: vref_for_level_def pt_bits_left_def)
    apply (rule conjI; clarsimp)
     apply (subgoal_tac "nlevel = max_pt_level - 1")
      apply (clarsimp simp: level_defs bit_simps maxPTLevel_def split: if_split_asm)
      apply word_eqI_solve
     apply (subst (asm) add.commute[where a=2])
     apply (drule add_implies_diff)
     apply (simp add: max_pt_level_def)
    apply (simp add: pt_bits_def)
    apply (prop_tac "level_type (nlevel + 1) = NormalPT_T")
     apply (drule max_pt_level_enum)
     (* Unfolding config_ARM_PA_SIZE_BITS_40_def here, because the level_enum only produces a
        contradiction in one of the branches when PA_40 is set. *)
     apply (solves \<open>auto simp: level_defs Kernel_Config.config_ARM_PA_SIZE_BITS_40_def split: if_split_asm\<close>)[1]
    apply (simp add: bit_simps)
    apply word_eqI
    apply (drule max_pt_level_enum)
    by (cases config_ARM_PA_SIZE_BITS_40, auto simp: max_pt_level_def2)

  note vm_level.size_minus_one[simp]
  from minus.prems
  show ?case
    apply (subst lookupPTFromLevel.simps, subst pt_lookup_from_level_simps)
    apply (simp add: unlessE_whenE not_less)
    apply (rule corres_gen_asm, simp)
    apply (rule corres_initial_splitE[where r'=dc])
       apply (corresKsimp simp: lookup_failure_map_def)
      apply (rule corres_splitEE[where r'=pte_relation'])
         apply (simp, rule getObject_PTE_corres)
        apply (rule whenE_throwError_corres)
          apply (simp add: lookup_failure_map_def)
         apply (rename_tac pte pte', case_tac pte; simp add: isPageTablePTE_def)
        apply (rule corres_if)
          apply (clarsimp simp: AARCH64_A.is_PageTablePTE_def pptr_from_pte_def getPPtrFromPTE_def
                                paddr_from_ppn_def isPagePTE_def)
         apply (rule corres_returnOk[where P=\<top> and P'=\<top>], simp)
        apply (clarsimp simp: checkPTAt_def)
        apply (subst liftE_bindE, rule corres_stateAssert_implied[where P'=\<top>])
         apply (rule minus.hyps)
          apply (simp add: minus.hyps(2))
         apply (clarsimp simp: AARCH64_A.is_PageTablePTE_def pptr_from_pte_def getPPtrFromPTE_def
                               paddr_from_ppn_def isPagePTE_def)
        apply clarsimp
        apply (prop_tac "pt_at NormalPT_T (pptr_from_pte pte) s")
         apply (drule (2) valid_vspace_objs_strongD; assumption?)
          apply simp
         apply (simp add: state_relation_def)
         apply (clarsimp simp: pt_at_eq in_omonad AARCH64_A.is_PageTablePTE_def pptr_from_pte_def
                               getPPtrFromPTE_def isPagePTE_def paddr_from_ppn_def)
        apply (frule page_table_at_cross; assumption?)
         apply (fastforce simp: state_relation_def)
        apply (clarsimp simp: AARCH64_A.is_PageTablePTE_def pptr_from_pte_def getPPtrFromPTE_def
                              paddr_from_ppn_def isPagePTE_def)
        apply (fastforce simp: ghost_relation_def obj_at_def
                         elim!: state_relationE)
       apply wpsimp+
     apply (simp add: vm_level.neq_0_conv)
     apply (frule (5) vs_lookup_table_is_aligned)
     apply (rule conjI)
      apply (drule (5) valid_vspace_objs_strongD)
      apply (clarsimp simp: pte_at_def obj_at_def ptes_of_def in_omonad)
      apply (rule conjI, fastforce)
      apply (simp add: pt_slot_offset_def)
      apply (rule is_aligned_add)
       apply (erule is_aligned_weaken)
       apply (simp add: bit_simps)
      apply (rule is_aligned_shiftl, simp)
     apply clarsimp
     apply (rule_tac x=asid in exI)
     apply (rule_tac x="vref_step vref" in exI)
     apply (clarsimp simp: vs_lookup_table_def in_omonad split: if_split_asm)
     apply (rule conjI)
      apply (clarsimp simp: level_defs)
     apply (subst pt_walk_split_Some[where level'=level]; simp?)
      apply (drule vm_level.pred)
      apply simp
     apply (subst pt_walk.simps)
     apply (simp add: in_omonad)
    apply wpsimp
    done
qed

declare in_set_zip_refl[simp]

crunch storePTE
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp' simp: crunch_simps ignore_del: setObject)

lemmas storePTE_typ_ats[wp] = typ_at_lifts [OF storePTE_typ_at']

lemma setObject_asid_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setObject p' (v::asidpool) \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wp setObject_typ_at')

lemmas setObject_asid_typ_ats' [wp] = typ_at_lifts [OF setObject_asid_typ_at']

lemma getObject_pte_inv[wp]:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>rv :: pte. P\<rbrace>"
  by (simp add: getObject_inv loadObject_default_inv)

lemma corres_gets_global_pt [corres]:
  "corres (=) valid_global_arch_objs \<top>
              (gets global_pt) (gets (armKSGlobalUserVSpace \<circ> ksArchState))"
  by (clarsimp simp add: state_relation_def arch_state_relation_def)

lemmas getObject_PTE_corres'[corres] = getObject_PTE_corres[@lift_corres_args]
lemmas storePTE_corres'[corres] = storePTE_corres[@lift_corres_args]

lemma arch_cap_rights_update:
  "acap_relation c c' \<Longrightarrow>
   cap_relation (cap.ArchObjectCap (acap_rights_update (acap_rights c \<inter> msk) c))
                 (Arch.maskCapRights (rights_mask_map msk) c')"
  apply (cases c, simp_all add: AARCH64_H.maskCapRights_def
                                acap_rights_update_def Let_def isCap_simps)
  apply (simp add: maskVMRights_def vmrights_map_def rights_mask_map_def
                   validate_vm_rights_def vm_read_write_def vm_read_only_def
                   vm_kernel_only_def )
  done

lemma arch_deriveCap_inv:
  "\<lbrace>P\<rbrace> Arch.deriveCap arch_cap u \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp      add: AARCH64_H.deriveCap_def
                  cong: if_cong
             split del: if_split)
  apply (wp undefined_valid)
  apply (cases u; simp add: isCap_defs)
  done

lemma arch_deriveCap_valid:
  "\<lbrace>valid_cap' (ArchObjectCap arch_cap)\<rbrace>
     Arch.deriveCap u arch_cap
   \<lbrace>\<lambda>rv. valid_cap' rv\<rbrace>,-"
  apply (simp add: AARCH64_H.deriveCap_def split del: if_split)
  apply (wp undefined_validE_R)
  apply (cases arch_cap; simp add: isCap_defs)
  apply (simp add: valid_cap'_def capAligned_def capUntypedPtr_def AARCH64_H.capUntypedPtr_def)
  done

lemma mdata_map_simps[simp]:
  "mdata_map None = None"
  "mdata_map (Some (asid, ref)) = Some (ucast asid, ref)"
  by (auto simp add: mdata_map_def)

lemma arch_deriveCap_corres:
 "cap_relation (cap.ArchObjectCap c) (ArchObjectCap c') \<Longrightarrow>
  corres (ser \<oplus> (\<lambda>c c'. cap_relation c c'))
         \<top> \<top>
         (arch_derive_cap c)
         (Arch.deriveCap slot c')"
  unfolding arch_derive_cap_def AARCH64_H.deriveCap_def Let_def
  apply (cases c, simp_all add: isCap_simps split: option.splits split del: if_split)
      apply (clarify?, rule corres_noopE; wpsimp)+
  done

definition
  "vmattributes_map \<equiv> \<lambda>R. VMAttributes (Execute \<notin> R) (Device \<notin> R)"

lemma pte_relation'_Invalid_inv [simp]:
  "pte_relation' x AARCH64_H.pte.InvalidPTE = (x = AARCH64_A.pte.InvalidPTE)"
  by (cases x) auto

lemma asidHighBitsOf [simp]:
  "asidHighBitsOf asid = ucast (asid_high_bits_of (ucast asid))"
  by (word_eqI_solve simp: asidHighBitsOf_def asid_high_bits_of_def asidHighBits_def asid_low_bits_def)

lemma le_mask_asidBits_asid_wf:
  "asid_wf asid \<longleftrightarrow> asid \<le> mask asidBits"
  by (simp add: asidBits_def asidHighBits_def asid_wf_def asid_bits_defs mask_def)

lemma asid_le_mask_asidBits[simp]:
  "UCAST(asid_len \<rightarrow> machine_word_len) asid \<le> mask asidBits"
  by (rule ucast_leq_mask, simp add: asidBits_def asidHighBits_def asid_low_bits_def)

lemma asid_case_zero[simp]:
  "0 < asid \<Longrightarrow> 0 < UCAST(asid_len \<rightarrow> machine_word_len) asid"
  by word_bitwise

lemma find_vspace_for_asid_rewite:
  "find_vspace_for_asid asid =
   doE
     unlessE (0 < asid) $ throwError ExceptionTypes_A.InvalidRoot;
     entry_opt \<leftarrow> liftE $ gets (entry_for_asid asid);
     case entry_opt of
       Some entry \<Rightarrow> returnOk (ap_vspace entry)
     | None \<Rightarrow> throwError ExceptionTypes_A.InvalidRoot
   odE"
  unfolding find_vspace_for_asid_def vspace_for_asid_def
  apply (cases "0 < asid")
   apply simp (* rewrite unlessE before unfolding things *)
   apply (fastforce simp: bindE_def throw_opt_def liftE_def simpler_gets_def bind_def return_def
                          obind_None_eq
                    split: option.splits)
  apply (simp add: liftE_def simpler_gets_def bindE_def bind_def return_def throw_opt_def
                   throwError_def)
  done

lemma getPoolPtr_corres:
  "corres (=) (K (0 < asid)) \<top> (gets (pool_for_asid asid)) (getPoolPtr (ucast asid))"
  unfolding pool_for_asid_def getPoolPtr_def asidRange_def
  apply simp
  apply corres_pre
    apply (rule corres_assert_gen_asm)
    apply (rule corres_assert_gen_asm)
    apply (rule corres_trivial)
    apply (clarsimp simp: gets_return_gets_eq state_relation_def arch_state_relation_def
                          ucast_up_ucast_id is_up)
   apply (simp flip: mask_eq_exp_minus_1)
  apply simp
  done

lemma getASIDPoolEntry_corres:
  "corres (\<lambda>r r'. r = map_option abs_asid_entry r')
          (valid_vspace_objs and valid_asid_table and pspace_aligned and pspace_distinct
           and K (0 < asid))
          (no_0_obj')
          (gets (entry_for_asid asid))
          (getASIDPoolEntry (ucast asid))"
  unfolding entry_for_asid_def getASIDPoolEntry_def K_def
  apply (rule corres_gen_asm)
  apply (clarsimp simp: gets_obind_bind_eq entry_for_pool_def obind_comp_dist
                  cong: option.case_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=)"])
       apply (rule getPoolPtr_corres)
      apply (rule_tac x=pool_ptr and x'=poolPtr in option_corres)
        apply (rule corres_trivial, simp)
       apply clarsimp
       apply (rule monadic_rewrite_corres_l)
        apply (monadic_rewrite_l gets_oapply_liftM_rewrite)
        apply (rule monadic_rewrite_refl)
       apply (clarsimp simp: liftM_def)
       apply (rule corres_split[OF getObject_ASIDPool_corres[OF refl]])
         apply (rule corres_trivial)
         apply (case_tac rv', clarsimp)
         apply (clarsimp simp: asid_pool_relation_def asid_low_bits_of_def ucast_ucast_mask2
                               is_down asid_low_bits_def ucast_and_mask)
        apply wpsimp+
   apply (drule (1) pool_for_asid_validD)
   apply (simp add: asid_pools_at_eq)
  apply simp
  done

lemma no_0_page_table:
  "\<lbrakk> no_0_obj' s; page_table_at' pt_t 0 s \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: page_table_at'_def)
  apply (erule_tac x=0 in allE)
  apply simp
  done

crunch getASIDPoolEntry
  for no_0_obj'[wp]: no_0_obj'
  (wp: getObject_inv simp: loadObject_default_def)

lemma findVSpaceForASID_corres:
  assumes "asid' = ucast asid"
  shows "corres (lfr \<oplus> (=))
                (valid_vspace_objs and valid_asid_table
                    and pspace_aligned and pspace_distinct
                    and K (0 < asid))
                (no_0_obj')
                (find_vspace_for_asid asid) (findVSpaceForASID asid')" (is "corres _ ?P ?Q _ _")
  using assms
  apply (simp add: findVSpaceForASID_def)
  apply (rule corres_gen_asm)
  apply (subst find_vspace_for_asid_rewite)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_initial_splitE[where r'="\<lambda>r r'. r = map_option abs_asid_entry r'"])
       apply simp
       apply (rule getASIDPoolEntry_corres)
      apply (rule_tac Q="\<lambda>entry s. pspace_aligned s \<and> pspace_distinct s \<and>
                                   vspace_pt_at (ap_vspace entry) s"
                      in option_corres[where P=\<top> and P'=\<top> and Q'="\<lambda>_. no_0_obj'"])
        apply (clarsimp simp: lookup_failure_map_def)
       apply (rename_tac entry entry')
       apply (case_tac entry')
       apply (clarsimp simp: checkPTAt_def abs_asid_entry_def)
       apply (rename_tac p)
       apply (rule_tac Q="\<lambda>s. page_table_at' VSRootPT_T p s \<and>
                              gsPTTypes (ksArchState s) p = Some VSRootPT_T \<and>
                              no_0_obj' s" in corres_cross_over_guard)
        apply clarsimp
        apply (rule conjI)
         apply (erule (2) page_table_at_cross, simp add: state_relation_def)
        apply (fastforce simp: ghost_relation_def obj_at_def elim!: state_relationE)
       apply (simp add: liftE_bindE assertE_liftE)
       apply (rule corres_assert_assume)
        apply (rule corres_stateAssert_assume)
         apply (rule corres_returnOk, simp)
        apply clarsimp
       apply (fastforce dest: no_0_page_table)
      apply simp
     apply wpsimp
     apply (clarsimp simp: entry_for_asid_def)
     apply (drule (2) pool_for_asid_valid_vspace_objs)
     apply (fastforce simp: entry_for_pool_def)
    apply (wpsimp wp: hoare_drop_imps)+
  done

lemma setObject_arch:
  assumes X: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp X | simp)+
  done

lemma setObject_ASID_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject p (v::asidpool) \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (rule setObject_arch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_PTE_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject p (v::pte) \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (rule setObject_arch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_ASID_valid_arch [wp]:
  "setObject p (v::asidpool) \<lbrace>valid_arch_state'\<rbrace>"
  by (wpsimp wp: valid_arch_state_lift' setObject_ko_wp_at)
     (auto simp: objBits_simps pageBits_def is_vcpu'_def ko_wp_at'_def obj_at'_def)

lemma setObject_PTE_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::pte) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (wpsimp wp: valid_arch_state_lift' setObject_typ_at' setObject_ko_wp_at)
     (auto simp: objBits_simps pageBits_def is_vcpu'_def ko_wp_at'_def obj_at'_def)

lemma setObject_ASID_ct [wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::asidpool) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_default_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pte_ct [wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::pte) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_default_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_ASID_cur_tcb' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setObject p (e::asidpool) \<lbrace>\<lambda>_ s. cur_tcb' s\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply wp+
  done

lemma setObject_pte_cur_tcb' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setObject p (e::pte) \<lbrace>\<lambda>_ s. cur_tcb' s\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply wp+
  done

lemma getASID_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::asidpool) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def
                     in_magnitude_check pageBits_def in_monad valid_def obj_at'_def objBits_simps)

lemma storePTE_ctes [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> storePTE p pte \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  apply (rule ctes_of_from_cte_wp_at [where Q=\<top>, simplified])
  apply (rule storePTE_cte_wp_at')
  done

lemma setObject_ASID_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     setObject ptr (asid::asidpool)
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad projectKO_opts_defs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad projectKO_opts_defs)
  apply simp
  done

lemma setObject_ASID_ctes_of'[wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>
     setObject ptr (asid::asidpool)
   \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  by (rule ctes_of_from_cte_wp_at [where Q=\<top>, simplified]) wp

lemma clearMemory_vms':
  "valid_machine_state' s \<Longrightarrow>
   \<forall>x\<in>fst (clearMemory ptr bits (ksMachineState s)).
      valid_machine_state' (s\<lparr>ksMachineState := snd x\<rparr>)"
  apply (clarsimp simp: valid_machine_state'_def
                        disj_commute[of "pointerInUserData p s" for p s])
  apply (drule_tac x=p in spec, simp)
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = 0"
         in use_valid[where P=P and Q="\<lambda>_. P" for P], simp_all)
  apply (rule clearMemory_um_eq_0)
  done

lemma dmo_clearMemory_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (clearMemory w sz) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (simp add: valid_irq_masks'_def, elim allEI, clarsimp)
   apply (drule use_valid)
     apply (rule no_irq_clearMemory[simplified no_irq_def, rule_format])
    apply simp_all
  apply (drule clearMemory_vms')
  apply fastforce
  done

end
end
