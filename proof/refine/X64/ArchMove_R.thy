(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch specific lemmas that should be moved into theory files before Refine *)

theory ArchMove_R
imports
  Move_R
begin

(* Use one of these forms everywhere, rather than choosing at random. *)
lemmas cte_index_repair = mult.commute[where a="(2::'a::len word) ^ cte_level_bits"]
lemmas cte_index_repair_sym = cte_index_repair[symmetric]

lemmas of_nat_inj64 = of_nat_inj[where 'a=machine_word_len, folded word_bits_def]

context Arch begin arch_global_naming

lemma no_fail_in8[wp]:
  "no_fail \<top> (in8 a)"
  by (wpsimp simp: in8_def wp: no_fail_machine_op_lift)

lemma no_fail_in16[wp]:
  "no_fail \<top> (in16 a)"
  by (wpsimp simp: in16_def wp: no_fail_machine_op_lift)

lemma no_fail_in32[wp]:
  "no_fail \<top> (in32 a)"
  by (wpsimp simp: in32_def wp: no_fail_machine_op_lift)

lemma no_fail_out8[wp]:
  "no_fail \<top> (out8 a w)"
  by (wpsimp simp: out8_def)

lemma no_fail_out16[wp]:
  "no_fail \<top> (out16 a w)"
  by (wpsimp simp: out16_def)

lemma no_fail_out32[wp]:
  "no_fail \<top> (out32 a w)"
  by (wpsimp simp: out32_def)

lemma table_size_slot_eq:
  "((p::machine_word) && ~~ mask table_size) + (ucast x << word_size_bits) = p \<Longrightarrow>
    (x::9 word) = ucast (p && mask table_size >> word_size_bits)"
  apply (clarsimp simp: bit_simps mask_def)
  apply word_bitwise
  apply clarsimp
  done

lemmas pd_bits_slot_eq = table_size_slot_eq[folded pd_bits_def]
lemmas pt_bits_slot_eq = table_size_slot_eq[folded pt_bits_def]
lemmas pdpt_bits_slot_eq = table_size_slot_eq[folded pdpt_bits_def]
lemmas pml4_bits_slot_eq = table_size_slot_eq[folded pml4_bits_def]

lemma more_pd_inner_beauty:
  fixes x :: "9 word"
  fixes p :: machine_word
  assumes x: "x \<noteq> ucast (p && mask pd_bits >> word_size_bits)"
  shows "(p && ~~ mask pd_bits) + (ucast x << word_size_bits) = p \<Longrightarrow> False"
  by (rule mask_split_aligned_neg[OF _ _ x]; simp add: bit_simps)

(* Move to invariants? *)
definition
  "vspace_at_asid_ex asid \<equiv> \<lambda>s. \<exists>pm. vspace_at_asid asid pm s"

lemma no_fail_ioapicMapPinToVector[wp]: "no_fail \<top> (ioapicMapPinToVector a b c d e) "
  by (simp add: ioapicMapPinToVector_def)

lemma no_irq_ioapicMapPinToVector[wp]:
  "no_irq (ioapicMapPinToVector a b c d e)"
  by (simp add: ioapicMapPinToVector_def)

(* Move to Deterministic_AI*)
crunch copy_global_mappings
  for valid_etcbs[wp]: valid_etcbs (wp: mapM_x_wp')

(* Move to no_gs_types_simps in ArchRetype_AI *)
lemma no_gs_types_simps' [simp]:
  "ArchObject PDPTObj \<in> no_gs_types"
  "ArchObject PML4Obj \<in> no_gs_types"
  by (simp_all add: no_gs_types_def)

lemmas store_pde_typ_ats' [wp] = abs_typ_at_lifts [OF store_pde_typ_at]
lemmas store_pdpte_typ_ats' [wp] = abs_typ_at_lifts [OF store_pdpte_typ_at]
lemmas store_pte_typ_ats[wp] = store_pte_typ_ats abs_atyp_at_lifts[OF store_pte_typ_at]
lemmas store_pde_typ_ats[wp] = store_pde_typ_ats' abs_atyp_at_lifts[OF store_pde_typ_at]
lemmas store_pdpte_typ_ats[wp] = store_pdpte_typ_ats' abs_atyp_at_lifts[OF store_pdpte_typ_at]

(* Move to invariants *)
lemma find_vspace_for_asid_wp:
  "\<lbrace> valid_vspace_objs and pspace_aligned and K (asid \<noteq> 0)
        and (\<lambda>s. \<forall>pm. vspace_at_asid asid pm s \<longrightarrow> Q pm s)
        and (\<lambda>s. (\<forall>pm. \<not> vspace_at_asid asid pm s) \<longrightarrow> E ExceptionTypes_A.lookup_failure.InvalidRoot s) \<rbrace>
    find_vspace_for_asid asid
   \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (wpsimp simp: find_vspace_for_asid_def vspace_at_asid_def)
  apply (intro conjI impI allI)
    apply (erule mp; clarsimp; thin_tac "\<forall>pm. _ pm s")
    apply (erule vs_lookupE; clarsimp simp: vs_asid_refs_def graph_of_def)
    apply (drule vs_lookup1_trans_is_append)
    apply (clarsimp simp: up_ucast_inj_eq)
   apply (erule mp; clarsimp; thin_tac "\<forall>pm. _ pm s")
   apply (erule vs_lookupE; clarsimp simp: vs_asid_refs_def graph_of_def)
   apply (frule vs_lookup1_trans_is_append; clarsimp simp: up_ucast_inj_eq)
   apply (erule rtranclE; clarsimp)
   apply (frule vs_lookup1_wellformed.lookup1_is_append; clarsimp)
   apply (drule vs_lookup1_wellformed.lookup_trans_eq; clarsimp)
   apply (clarsimp simp: vs_lookup1_def vs_refs_def)
   apply (case_tac ko; clarsimp; rename_tac ako; case_tac ako; clarsimp)
   apply (clarsimp simp: graph_of_def obj_at_def mask_asid_low_bits_ucast_ucast)
  apply (drule spec; erule mp; thin_tac "_ s \<longrightarrow> _ s")
  apply (rule vs_lookupI)
   apply (fastforce simp: vs_asid_refs_def graph_of_def image_def)
  apply (rule rtrancl_into_rtrancl[rotated])
   apply (erule vs_lookup1I; fastforce simp: vs_refs_def graph_of_def image_def
                                             ucast_ucast_mask asid_low_bits_def)
  by simp

lemma no_fail_getFaultAddress[wp]: "no_fail \<top> getFaultAddress"
  by (simp add: getFaultAddress_def)

lemma no_fail_invalidateASID[wp]: "no_fail \<top> (invalidateASID a b)"
  by (simp add: invalidateASID_def)

lemma set_asid_pool_vspace_objs_unmap_single:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (X64_A.ASIDPool ap)) p\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  using set_asid_pool_vspace_objs_unmap[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

lemma hw_asid_invalidate_valid_arch_state[wp]:
  "\<lbrace>valid_arch_state\<rbrace> hw_asid_invalidate asid pm \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding hw_asid_invalidate_def by wp

crunch hw_asid_invalidate
  for valid_global_objs[wp]: "valid_global_objs"

(* Move to invariants *)
lemma get_pt_mapM_x_lower:
  assumes g: "\<And>P pt x. \<lbrace> \<lambda>s. P (kheap s pt_ptr) \<rbrace> g pt x \<lbrace> \<lambda>_ s. P (kheap s pt_ptr) \<rbrace>"
  assumes y: "ys \<noteq> []"
  notes [simp] = get_pt_def get_object_def gets_def get_def bind_def return_def
                 assert_def fail_def
  shows "do pt \<leftarrow> get_pt pt_ptr; mapM_x (g pt) ys od
          = mapM_x (\<lambda>y. get_pt pt_ptr >>= (\<lambda>pt. g pt y)) ys"
  apply (rule get_mapM_x_lower
                [where P="\<lambda>opt_pt s. case kheap s pt_ptr of
                                       Some (ArchObj (PageTable pt)) \<Rightarrow> opt_pt = Some pt
                                     | _ \<Rightarrow> opt_pt = None",
                 OF _ _ _ y])
    apply (wp g)
   apply (case_tac "kheap s pt_ptr"; simp; rename_tac ko; case_tac ko; simp;
          rename_tac ako; case_tac ako; simp)+
  done

(* Move to invariants *)
lemma get_pt_get_pte:
  assumes align: "is_aligned pt_ptr pt_bits"
  shows "do pt \<leftarrow> get_pt pt_ptr; f (pt i) od
            = do pte \<leftarrow> get_pte (pt_ptr + (ucast i << word_size_bits)); f pte od"
  proof -
    have i: "ucast i < (2::machine_word) ^ (pt_bits - word_size_bits)"
      by (rule less_le_trans[OF ucast_less]; simp add: bit_simps)
    have s: "ucast i << word_size_bits < (2::machine_word) ^ pt_bits"
      by (rule shiftl_less_t2n[OF i]; simp add: bit_simps)
    show ?thesis
      apply (simp add: get_pte_def is_aligned_add_helper align s)
      apply (simp add: shiftl_shiftr_id less_le_trans[OF i] bit_simps ucast_ucast_id)
      done
  qed

lemma flush_table_pde_at[wp]: "\<lbrace>pde_at p\<rbrace> flush_table a b c d \<lbrace>\<lambda>_. pde_at p\<rbrace>"
  by (wpsimp simp: flush_table_def pde_at_def wp: flush_table_typ_at mapM_x_wp')

lemma no_fail_invalidateTranslationSingleASID[wp]:
  "no_fail \<top> (invalidateTranslationSingleASID v a)"
  by (simp add: invalidateTranslationSingleASID_def)

lemma no_irq_invalidateTranslationSingleASID[wp]:
  "no_irq (invalidateTranslationSingleASID a b)"
  by (simp add: invalidateTranslationSingleASID_def)

end

end
