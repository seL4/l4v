(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch-specific lemmas on arch get/set object etc *)

theory ArchArchAcc_R
imports ArchAcc_R
begin

unbundle l4v_word_context

context Arch begin arch_global_naming

named_theorems ArchAcc_R_assms

lemma asid_pool_at_ko:
  "asid_pool_at p s \<Longrightarrow> \<exists>pool. ko_at (ArchObj (RISCV64_A.ASIDPool pool)) p s"
  by (clarsimp simp: asid_pools_at_eq obj_at_def elim!: opt_mapE)

lemma corres_gets_asid[corres]:
  "corres (\<lambda>a c. a = c o ucast) \<top> \<top> (gets (riscv_asid_table \<circ> arch_state)) (gets (riscvKSASIDTable \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemma asid_low_bits [simp]:
  "asidLowBits = asid_low_bits"
  by (simp add: asid_low_bits_def asidLowBits_def)

lemma pteBits_pte_bits[simp]:
  "pteBits = pte_bits"
  by (simp add: bit_simps pteBits_def)

lemma pspace_aligned_cross[ArchAcc_R_assms]:
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
     apply (clarsimp simp: archObjSize_def pteBits_def table_size_def ptTranslationBits_def pte_bits_def)
     apply (rule is_aligned_add)
      apply (erule is_aligned_weaken)
      apply simp
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
     apply (simp add: bit_simps is_aligned_shift mask_def)
     apply word_bitwise
    apply (rule_tac x=pageBits in exI)
    apply (simp add: is_aligned_shift pbfs_atleast_pageBits)
    apply (simp add: mask_def shiftl_t2n mult_ac)
    apply (erule word_less_power_trans2, rule pbfs_atleast_pageBits)
    apply (simp add: pbfs_less_wb'[unfolded word_bits_def, simplified])
   apply fastforce+
  done

lemma obj_relation_cuts_range_mask_range[ArchAcc_R_assms]:
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

lemma pspace_distinct_cross[ArchAcc_R_assms]:
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
  apply (clarsimp simp: other_aobj_relation_def split: kernel_object.splits arch_kernel_object.splits)
  apply (clarsimp simp: objBits_simps)
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
   corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
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
  apply (clarsimp simp: other_aobj_relation_def asid_pool_relation_def)
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

lemma setObject_ASIDPool_corres[corres]:
  "\<lbrakk> a = inv ASIDPool a' o ucast; p' = p \<rbrakk> \<Longrightarrow>
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
  "is_aligned p pte_bits \<Longrightarrow> p + mask pte_bits \<le> table_base p + mask table_size"
  apply (simp add: is_aligned_mask bit_simps word_plus_and_or_coroll)
  apply word_bitwise
  apply (simp add: word_size)
  done

lemma pte_at_cross:
  "\<lbrakk> pte_at p s; pspace_relation (kheap s) (ksPSpace s'); pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> pte_at' p s'"
  apply (drule (2) pspace_distinct_cross)
  apply (clarsimp simp: pte_at_def obj_at_def typ_at'_def ko_wp_at'_def)
  apply (prop_tac "p \<in> pspace_dom (kheap s)")
   apply (clarsimp simp: pspace_dom_def)
   apply (rule bexI)
    prefer 2
    apply fastforce
   apply (clarsimp simp: ran_def image_iff)
   apply (rule_tac x="table_index p" in exI)
   apply (simp add: mask_pt_bits_inner_beauty)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule bspec, fastforce)
  apply clarsimp
  apply (erule_tac x="table_index p" in allE)
  apply (simp add: mask_pt_bits_inner_beauty)
  apply (clarsimp simp: pte_relation_def)
  apply (clarsimp simp: objBits_simps)
  apply (clarsimp simp: pspace_distinct'_def)
  apply (drule bspec, fastforce)
  apply (simp add: objBits_simps)
  done

lemma corres_cross_over_pte_at:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> pte_at p s \<and> pspace_distinct s \<and> pspace_aligned s;
     corres r P (P' and pte_at' p) f g\<rbrakk> \<Longrightarrow>
   corres r P P' f g"
  apply (rule corres_cross_over_guard[where Q="P' and pte_at' p"])
   apply (drule meta_spec, drule (1) meta_mp, clarsimp)
   apply (erule pte_at_cross; assumption?)
   apply (simp add: state_relation_def)
  apply assumption
  done

lemma getObject_PTE_corres[corres]:
  "p = p' \<Longrightarrow>
   corres pte_relation' (pte_at p and pspace_aligned and pspace_distinct) \<top>
          (get_pte p) (getObject p')"
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
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def in_magnitude_check objBits_simps bit_simps)
  apply (clarsimp simp: state_relation_def pspace_relation_def elim!: opt_mapE)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pte_relation_def)
  apply (erule_tac x="table_index p" in allE)
  apply (clarsimp simp: mask_pt_bits_inner_beauty[simplified bit_simps] bit_simps)
  done

lemmas aligned_distinct_pte_atI'
    = aligned_distinct_obj_atI'[where 'a=pte,
                                simplified, OF _ _ _ refl]

lemma pt_bits_slot_eq:
  "table_base p + (ucast x << pte_bits) = p \<Longrightarrow> x = ucast (p && mask table_size >> pte_bits)"
  for x :: pt_index
  unfolding bit_simps mask_def by word_bitwise clarsimp

lemma one_less_2p_pte_bits[simp]:
  "(1::machine_word) < 2 ^ pte_bits"
  by (simp add: bit_simps)

\<comment> \<open>setObject_other_corres unfortunately doesn't work here\<close>
lemma setObject_PT_corres:
  "pte_relation' pte pte' \<Longrightarrow>
   corres dc ((\<lambda>s. pts_of s (table_base p) = Some pt) and K (is_aligned p pte_bits) and
              pspace_aligned and pspace_distinct) \<top>
          (set_pt (table_base p) (pt(table_index p := pte)))
          (setObject p pte')"
  supply opt_mapE[elim!]
  apply (rule corres_cross_over_pte_at[where p=p])
   apply (simp add: pte_at_eq ptes_of_def in_omonad)
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
  apply (clarsimp simp: obj_at_def exec_gets a_type_simps opt_map_def exec_get put_def)
  apply (clarsimp simp: state_relation_def mask_pt_bits_inner_beauty)
  apply (rule conjI)
   apply (clarsimp simp: pspace_relation_def split del: if_split)
   apply (rule conjI)
    apply (subst pspace_dom_update, assumption)
     apply (simp add: a_type_def)
    apply (auto simp: dom_def)[1]
   apply (rule conjI)
    apply (drule bspec, blast)
    apply clarsimp
    apply (drule_tac x = x in spec)
    apply (clarsimp simp: pte_relation_def mask_pt_bits_inner_beauty
                   dest!: more_pt_inner_beauty)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: pte_relation_def mask_pt_bits_inner_beauty
                   dest!: more_pt_inner_beauty)
   apply clarsimp
   apply (drule bspec, assumption)
   apply clarsimp
   apply (erule (1) obj_relation_cutsE)
       apply simp
      apply clarsimp
     apply simp
     apply clarsimp
     apply (frule (1) pspace_alignedD)
     apply (drule_tac p=x in pspace_alignedD, assumption)
     apply simp
     apply (drule mask_alignment_ugliness)
        apply (simp add: pt_bits_def pageBits_def)
       apply (simp add: pt_bits_def pageBits_def)
      apply clarsimp
      apply (drule test_bit_size)
      apply (clarsimp simp: word_size bit_simps)
      apply arith
     apply ((simp split: if_split_asm)+)[2]
    apply (simp add: other_obj_relation_def split: Structures_A.kernel_object.splits)
   apply (simp add: other_aobj_relation_def split: arch_kernel_obj.splits)
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask pt_bits" in allE)+
   apply fastforce
  apply (extract_conjunct \<open>match conclusion in "ready_queues_relation_2 _ _ _ _ _" \<Rightarrow> -\<close>)
   apply (prop_tac "typ_at' (koTypeOf (injectKO pte')) p b")
    apply (simp add: typ_at'_def ko_wp_at'_def)
   subgoal by (fastforce dest: tcbs_of'_non_tcb_update)
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done

lemma storePTE_corres[corres]:
  "\<lbrakk> p = p'; pte_relation' pte pte' \<rbrakk> \<Longrightarrow>
  corres dc (pte_at p and pspace_aligned and pspace_distinct) \<top> (store_pte p pte) (storePTE p' pte')"
  apply (simp add: store_pte_def storePTE_def)
  apply (rule corres_assume_pre, simp add: pte_at_def)
  apply (rule corres_symb_exec_l)
     apply (erule setObject_PT_corres)
    apply (clarsimp simp: exs_valid_def gets_map_def fst_assert_opt in_omonad
                          exec_gets bind_assoc obj_at_def pte_at_def)
   apply (wpsimp simp: obj_at_def in_omonad)
  apply (wpsimp simp: obj_at_def in_omonad)
  done

lemmas tableBitSimps[simplified bit_simps pteBits_pte_bits, simplified] = ptBits_def
lemmas bitSimps = tableBitSimps

lemma bit_simps_corres[simp]:
  "ptBits = pt_bits"
  by (simp add: bit_simps bitSimps)

defs checkPTAt_def:
  "checkPTAt pt \<equiv> stateAssert (page_table_at' pt) []"

lemma pte_relation_must_pte:
  "pte_relation m (ArchObj (PageTable pt)) ko \<Longrightarrow> \<exists>pte. ko = (KOArch (KOPTE pte))"
  apply (case_tac ko)
   apply (simp_all add:pte_relation_def)
  apply clarsimp
  done

lemma page_table_at_cross:
  "\<lbrakk> pt_at p s; pspace_aligned s; pspace_distinct s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow>
   page_table_at' p s'"
  apply (clarsimp simp: page_table_at'_def)
  apply (rule context_conjI)
   apply (clarsimp simp: obj_at_def)
   apply (frule (1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply clarsimp
  apply (rule pte_at_cross; assumption?)
  apply (clarsimp simp: obj_at_def pte_at_def table_base_plus_ucast is_aligned_pte_offset)
  done

lemma getPTE_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::pte) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def in_magnitude_check
                     in_monad valid_def obj_at'_def objBits_simps)

(* FIXME: use more recent guard crossing framework that don't need a specific goal form.
          This was mostly left here to test compatibility bewtween corres and corresK methods *)
(* only applies when ptr is available in abstract and concrete guard at the same time *)
lemma pt_at_lift_eq:
  "\<forall>s s'. (s, s') \<in> state_relation \<longrightarrow>
          (pspace_aligned s \<and> pspace_distinct s \<and> pt_at ptr s) \<longrightarrow>
          \<top> s' \<longrightarrow>
          page_table_at' ptr s'"
  by (fastforce intro!: page_table_at_cross)

(* only applies for the "getPPtrFromHWPTE pte" pattern *)
lemma pt_at_lift_relation:
  "\<lbrakk> pte_relation' pte pte'; RISCV64_A.is_PageTablePTE pte \<rbrakk> \<Longrightarrow>
   \<forall>s s'. (s, s') \<in> state_relation \<longrightarrow>
          (pspace_aligned s \<and> pspace_distinct s \<and> pt_at (pptr_from_pte pte) s) \<longrightarrow>
          \<top> s' \<longrightarrow>
          page_table_at' (getPPtrFromHWPTE pte') s'"
  apply (cases pte; simp)
  apply (simp add: getPPtrFromHWPTE_def pptr_from_pte_def addr_from_ppn_def pt_at_lift_eq)
  done

lemmas checkPTAt_corres_pte[corres] =
  corres_stateAssert_r_cross[OF pt_at_lift_relation, folded checkPTAt_def]

lemmas checkPTAt_corres_eq[corres] =
  corres_stateAssert_r_cross[OF pt_at_lift_eq, folded checkPTAt_def]

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
    by (subst lookupPTFromLevel.simps, simp add: checkPTAt_def cong: if_cong)
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
  by (simp add: ptBitsLeft_def pt_bits_left_def)

lemma ptIndex_eq[simp]:
  "ptIndex (size level) = pt_index level"
  by (fastforce simp: ptIndex_def pt_index_def)

lemma ptSlotIndex_eq[simp]:
  "ptSlotIndex (size level) = pt_slot_offset level"
  by (fastforce simp: ptSlotIndex_def pt_slot_offset_def)

lemmas ptSlotIndex_0[simp] = ptSlotIndex_eq[where level=0, simplified]

lemma pteAtIndex_corres:
  "level' = size level \<Longrightarrow>
   corres pte_relation'
     (pte_at (pt_slot_offset level pt vptr) and pspace_aligned and pspace_distinct)
     \<top>
     (get_pte (pt_slot_offset level pt vptr))
     (pteAtIndex level' pt vptr)"
  by (simp add: pteAtIndex_def getObject_PTE_corres)

lemma user_region_or:
  "\<lbrakk> vref \<in> user_region; vref' \<in> user_region \<rbrakk> \<Longrightarrow> vref || vref' \<in> user_region"
  by (simp add: user_region_def canonical_user_def le_mask_high_bits word_size)


lemma lookupPTSlotFromLevel_corres[corres]:
  "\<lbrakk> level' = size level; pt' = pt \<rbrakk> \<Longrightarrow>
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
  have nlevel1: "nlevel < nlevel + 1" using bit0.pred by fastforce
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
    using vref_for_level_pt_index_idem[of level level vref level vptr] by simp

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
             simp: pt_bits_left_def bit_simps canonical_bit_def user_region_def
                   pt_index_def canonical_user_def word_eqI_simps
             dest!: max_pt_level_enum)

  have pt_slot_offset_step[simp]:
    "\<lbrakk> is_aligned pt pt_bits; vref \<in> user_region \<rbrakk> \<Longrightarrow>
    pt_slot_offset level pt (vref_step vref) = pt_slot_offset level pt vptr" for vref
    unfolding vref_step_def using nlevel1 nlevel
    by (auto simp: pt_slot_offset_or_def user_region_def canonical_user_def canonical_bit_def
                   word_eqI_simps pt_index_def bit_simps pt_bits_left_def
             dest!: max_pt_level_enum
             intro!: word_eqI)

  from `0 < level` `level' = size level` `pt' = pt` level
  show ?case
    apply (subst pt_lookup_slot_from_level_rec)
    apply (simp add: lookupPTSlotFromLevel.simps Let_def obind_comp_dist if_comp_dist
                     gets_the_if_distrib checkPTAt_def
                cong: if_cong)
    apply (rule corres_guard_imp, rule corres_split[where r'=pte_relation'])
         apply (rule pteAtIndex_corres, simp)
        apply (rule corres_if3)
          apply (rename_tac pte pte', case_tac pte; (simp add: isPageTablePTE_def))
         apply (rule corres_stateAssert_implied)
          apply (rule minus(1))
           apply (simp add: nlevel)
          apply (clarsimp simp: RISCV64_A.is_PageTablePTE_def pptr_from_pte_def getPPtrFromHWPTE_def
                                addr_from_ppn_def)
         apply clarsimp
         apply (rule page_table_at_cross; assumption?)
          apply (drule (2) valid_vspace_objs_strongD; assumption?)
           apply simp
          apply (clarsimp simp: pt_at_eq in_omonad RISCV64_A.is_PageTablePTE_def pptr_from_pte_def
                                getPPtrFromHWPTE_def addr_from_ppn_def)
         apply (simp add: state_relation_def)
        apply (rule corres_inst[where P=\<top> and P'=\<top>])
        apply (clarsimp simp: ptSlotIndex_def pt_slot_offset_def pt_index_def pt_bits_left_def
                              ptIndex_def ptBitsLeft_def)
       apply wpsimp+
     apply (frule (5) vs_lookup_table_is_aligned)
     apply (rule conjI)
      apply (drule (5) valid_vspace_objs_strongD)
      apply (clarsimp simp: pte_at_def obj_at_def elim!: opt_mapE)
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
      apply (drule bit0.pred)
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
  by corres

declare RISCV64_A.pte.sel[datatype_schematic]

lemma lookupPTFromLevel_corres:
  "\<lbrakk> level' = size level; pt' = pt \<rbrakk> \<Longrightarrow>
   corres (lfr \<oplus> (=))
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

  note minus.hyps(1)[corres]

  (* FIXME: unfortunate duplication from lookupPTSlotFromLevel_corres *)
  from `0 < level`
  obtain nlevel where nlevel: "level = nlevel + 1" by (auto intro: that[of "level-1"])
  with `0 < level`
  have nlevel1: "nlevel < nlevel + 1" using bit0.pred by fastforce
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
    using vref_for_level_pt_index_idem[of level level vref level vptr] by simp

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
             simp: pt_bits_left_def bit_simps canonical_bit_def user_region_def
                   pt_index_def canonical_user_def word_eqI_simps
             dest!: max_pt_level_enum)

  have pt_slot_offset_step[simp]:
    "\<lbrakk> is_aligned pt pt_bits; vref \<in> user_region \<rbrakk> \<Longrightarrow>
    pt_slot_offset level pt (vref_step vref) = pt_slot_offset level pt vptr" for vref
    unfolding vref_step_def using nlevel1 nlevel
    by (auto simp: pt_slot_offset_or_def user_region_def canonical_user_def canonical_bit_def
                   word_eqI_simps pt_index_def bit_simps pt_bits_left_def
             dest!: max_pt_level_enum
             intro!: word_eqI)

  note bit0.size_minus_one[simp]
  from minus.prems
  show ?case
    apply (subst lookupPTFromLevel.simps, subst pt_lookup_from_level_simps)
    apply (simp add: unlessE_whenE not_less)
    apply (rule corres_gen_asm, simp)
    apply (corres simp: lookup_failure_map_def)
         apply (rename_tac pte pte', case_tac pte; simp add: isPageTablePTE_def)
        apply (corres term_simp: RISCV64_A.is_PageTablePTE_def pptr_from_pte_def
                                 getPPtrFromHWPTE_def addr_from_ppn_def minus.hyps(2))
       apply wpsimp+
     apply (simp add: bit0.neq_0_conv)
     apply (frule (5) vs_lookup_table_is_aligned)
     apply (rule conjI)
      apply (drule (5) valid_vspace_objs_strongD)
      apply (clarsimp simp: pte_at_def obj_at_def elim!: opt_mapE)
      apply (simp add: pt_slot_offset_def)
      apply (rule is_aligned_add)
       apply (erule is_aligned_weaken)
       apply (simp add: bit_simps)
      apply (rule is_aligned_shiftl, simp)
     apply clarsimp
     apply (rule conjI)
      apply (rule_tac x=asid in exI)
      apply (rule_tac x="vref_step vref" in exI)
      apply (clarsimp simp: vs_lookup_table_def in_omonad split: if_split_asm)
      apply (rule conjI)
       apply (clarsimp simp: level_defs)
      apply (subst pt_walk_split_Some[where level'=level]; simp?)
       apply (drule bit0.pred)
       apply simp
      apply (subst pt_walk.simps)
      apply (simp add: in_omonad)
     apply (drule (1) valid_vspace_objs_pte, fastforce)
     apply (clarsimp simp: RISCV64_A.is_PageTablePTE_def pptr_from_pte_def
                           table_index_max_level_slots)
    apply simp
    done
qed

crunch storePTE
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp' simp: crunch_simps ignore_del: setObject)

lemmas storePTE_typ_ats[wp] = typ_at_lifts [OF storePTE_typ_at']

lemma setObject_asid_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setObject p' (v::asidpool) \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wp setObject_typ_at')

lemmas setObject_asid_typ_ats'[wp] = typ_at_lifts[OF setObject_asid_typ_at']

lemma getObject_pte_inv[wp]:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>rv :: pte. P\<rbrace>"
  by (simp add: getObject_inv loadObject_default_inv)

crunch copyGlobalMappings
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: mapM_x_wp')

lemmas copyGlobalMappings_typ_ats[wp] = typ_at_lifts [OF copyGlobalMappings_typ_at']

lemma corres_gets_global_pt [corres]:
  "corres (=) valid_global_arch_objs \<top>
              (gets global_pt) (gets (riscvKSGlobalPT \<circ> ksArchState))"
  apply (clarsimp simp add: state_relation_def arch_state_relation_def riscv_global_pt_def
                            riscvKSGlobalPT_def valid_global_arch_objs_def)
  apply (case_tac "riscvKSGlobalPTs (ksArchState s') maxPTLevel"; simp)
  done

lemma copy_global_mappings_corres [@lift_corres_args, corres]:
  "corres dc (valid_global_arch_objs and pspace_aligned and pspace_distinct and pt_at pt)
             \<top>
             (copy_global_mappings pt)
             (copyGlobalMappings pt)" (is "corres _ ?apre _ _ _")
  unfolding copy_global_mappings_def copyGlobalMappings_def objBits_simps archObjSize_def pptr_base_def
  apply corres
      apply (rule_tac P="pt_at global_pt and ?apre" and P'="\<top>" in corres_mapM_x[OF _ _ _ _ order_refl])
         apply (corres simp: ptIndex_def ptBitsLeft_def maxPTLevel_def ptTranslationBits_def pageBits_def
                             pt_index_def pt_bits_left_def level_defs
                | fastforce dest!: valid_global_arch_objs_pt_at
                            intro!: page_table_pte_atI
                            simp: bit_simps word_le_nat_alt word_less_nat_alt)+
  done

lemma arch_cap_rights_update:
  "acap_relation c c' \<Longrightarrow>
   cap_relation (cap.ArchObjectCap (acap_rights_update (acap_rights c \<inter> msk) c))
                 (Arch.maskCapRights (rights_mask_map msk) c')"
  apply (cases c, simp_all add: RISCV64_H.maskCapRights_def
                                acap_rights_update_def Let_def isCap_simps)
  apply (simp add: maskVMRights_def vmrights_map_def rights_mask_map_def
                   validate_vm_rights_def vm_read_write_def vm_read_only_def
                   vm_kernel_only_def )
  done

lemma arch_deriveCap_inv:
  "\<lbrace>P\<rbrace> Arch.deriveCap arch_cap u \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp      add: RISCV64_H.deriveCap_def
                  cong: if_cong
             split del: if_split)
  apply (wp undefined_valid)
  apply (cases u; simp add: isCap_defs)
  done

lemma arch_deriveCap_valid:
  "\<lbrace>valid_cap' (ArchObjectCap arch_cap)\<rbrace>
     Arch.deriveCap u arch_cap
   \<lbrace>\<lambda>rv. valid_cap' rv\<rbrace>,-"
  apply (simp add: RISCV64_H.deriveCap_def split del: if_split cong: if_cong)
  apply (wp undefined_validE_R)
  apply (cases arch_cap; simp add: isCap_defs)
  apply (simp add: valid_cap'_def capAligned_def global.capUntypedPtr_def capUntypedPtr_def)
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
  unfolding arch_derive_cap_def RISCV64_H.deriveCap_def Let_def
  apply (cases c, simp_all add: isCap_simps split: option.splits split del: if_split)
      apply (clarify?, rule corres_noopE; wpsimp)+
  done


definition
  "vmattributes_map \<equiv> \<lambda>R. VMAttributes (Execute \<notin> R)"

lemma pte_relation'_Invalid_inv [simp]:
  "pte_relation' x RISCV64_H.pte.InvalidPTE = (x = RISCV64_A.pte.InvalidPTE)"
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

lemma gets_opt_bind_throw_opt:
  "(gets (do { x \<leftarrow> f; g x }) >>= throw_opt E) =
   (do x_opt \<leftarrow> gets f;
       doE x \<leftarrow> throw_opt E x_opt;
           gets (g x) >>= throw_opt E
       odE
    od)"
  apply (rule ext)
  apply (simp add: bind_def simpler_gets_def throw_opt_def)
  apply (simp add: obind_def split: option.splits)
  done

lemma find_vspace_for_asid_rewite:
  "monadic_rewrite False True (valid_asid_table and K (0 < asid))
     (find_vspace_for_asid asid)
     (doE
        asid_table \<leftarrow> liftE $ gets (riscv_asid_table \<circ> arch_state);
        pool_ptr \<leftarrow> returnOk (asid_table (asid_high_bits_of asid));
        pool \<leftarrow> (case pool_ptr of
                  Some ptr \<Rightarrow> liftE $ get_asid_pool ptr
                | None \<Rightarrow> throwError ExceptionTypes_A.InvalidRoot);
        pt \<leftarrow> returnOk (pool (ucast asid));
        (case pt of
            Some ptr \<Rightarrow> returnOk ptr
          | None \<Rightarrow> throwError ExceptionTypes_A.InvalidRoot)
      odE)"
  unfolding find_vspace_for_asid_def vspace_for_asid_def pool_for_asid_def vspace_for_pool_def
  apply (clarsimp simp: monadic_rewrite_def)
  apply (simp add: gets_opt_bind_throw_opt liftE_bindE obind_comp_dist gets_map_def cong: option.case_cong)
  apply (clarsimp simp: o_def exec_gets throw_opt_def split: option.splits)
  apply (rule conjI; clarsimp)
   apply (drule (1) valid_asid_tableD)
   apply (clarsimp simp: obj_at_def opt_map_def)
  apply (simp add: liftE_bindE bind_assoc exec_gets opt_map_def asid_low_bits_of_def)
  done

lemma findVSpaceForASID_corres[corres]:
  assumes "asid' = ucast asid"
  shows "corres (lfr \<oplus> (=))
                (valid_vspace_objs and valid_asid_table
                    and pspace_aligned and pspace_distinct
                    and K (0 < asid))
                (no_0_obj')
                (find_vspace_for_asid asid) (findVSpaceForASID asid')" (is "corres _ ?P ?Q _ _")
  using assms
  apply (simp add: findVSpaceForASID_def)
  apply (rule corres_gen_asm, simp add: ucast_down_ucast_id is_down_def target_size source_size)
  apply (rule corres_guard_imp[where Q'="?Q"], rule monadic_rewrite_corres_l[where P="?P"],
         rule find_vspace_for_asid_rewite; simp)
  apply (simp add: liftE_bindE asidRange_def flip: mask_2pm1)
  apply (rule_tac r'="\<lambda>x y. x = y o ucast"
             in corres_underlying_split [OF _ _ gets_sp gets_sp])
   apply (clarsimp simp: state_relation_def arch_state_relation_def)
  apply (case_tac "rv (asid_high_bits_of asid)")
   apply (simp add: liftME_def lookup_failure_map_def)
  apply (simp add: liftME_def bindE_assoc)
  apply (simp add: liftE_bindE)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getObject_ASIDPool_corres[OF refl]])
      apply (rule_tac P="case_option \<top> pt_at (pool (ucast asid)) and pspace_aligned and pspace_distinct"
                 and P'="no_0_obj'" in corres_inst)
      apply (rule_tac F="pool (ucast asid) \<noteq> Some 0" in corres_req)
       apply (clarsimp simp: obj_at_def no_0_obj'_def state_relation_def
                             pspace_relation_def a_type_def)
       apply (simp split: Structures_A.kernel_object.splits
                          arch_kernel_obj.splits if_split_asm)
       apply (drule_tac f="\<lambda>S. 0 \<in> S" in arg_cong)
       apply (simp add: pspace_dom_def)
       apply (drule iffD1, rule rev_bexI, erule domI)
        apply simp
        apply (rule image_eqI[rotated])
         apply (rule rangeI[where x=0])
        apply simp
       apply clarsimp
      apply (simp add: mask_asid_low_bits_ucast_ucast asid_low_bits_of_def returnOk_def
                       lookup_failure_map_def ucast_ucast_a is_down
                  split: option.split)
      apply (corres corres: corres_returnTT)
     apply (wpsimp wp: getObject_inv loadObject_default_inv)+
   apply (clarsimp simp: o_def)
   apply (rule conjI)
    apply (rule valid_asid_tableD; simp)
   apply (clarsimp split: option.splits)
   apply (rule vs_lookup_table_pt_at[where vptr=0 and level=max_pt_level and asid=asid]; simp?)
   apply (simp add: vs_lookup_table_def pool_for_asid_def vspace_for_pool_def in_omonad obj_at_def
                    asid_low_bits_of_def)
  apply simp
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
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::asidpool) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (rule valid_arch_state_lift'; wp)

lemma setObject_PTE_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::pte) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (rule valid_arch_state_lift') (wp setObject_typ_at')+

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

end

interpretation ArchAcc_R?: ArchAcc_R
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact ArchAcc_R_assms)?)
qed

end
