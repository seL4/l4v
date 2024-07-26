(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVSpaceEntries_AI
imports VSpaceEntries_AI
begin

context Arch begin arch_global_naming (*FIXME: arch-split*)

lemma a_type_pdD:
  "a_type ko = AArch APageDirectory \<Longrightarrow> \<exists>pd. ko = ArchObj (PageDirectory pd)"
  by (clarsimp)

primrec
  pde_range_sz :: "pde \<Rightarrow> nat"
where
    "pde_range_sz (InvalidPDE) = 0"
  | "pde_range_sz (SectionPDE ptr x y) = 0"
  | "pde_range_sz (SuperSectionPDE ptr x z) = 4"
  | "pde_range_sz (PageTablePDE ptr) = 0"

primrec
  pte_range_sz :: "pte \<Rightarrow> nat"
where
    "pte_range_sz (InvalidPTE) = 0"
  | "pte_range_sz (LargePagePTE ptr x y) = 4"
  | "pte_range_sz (SmallPagePTE ptr x y) = 0"

primrec
  pde_range :: "pde \<Rightarrow> 11 word \<Rightarrow> 11 word set"
where
    "pde_range (InvalidPDE) p = {}"
  | "pde_range (SectionPDE ptr x y) p = {p}"
  | "pde_range (SuperSectionPDE ptr x z) p =
     (if is_aligned p 4 then {x. x && ~~ mask 4 = p && ~~ mask 4} else {p})"
  | "pde_range (PageTablePDE ptr) p = {p}"

primrec
  pte_range :: "pte \<Rightarrow> 9 word \<Rightarrow> 9 word set"
where
    "pte_range (InvalidPTE) p = {}"
  | "pte_range (LargePagePTE ptr x y) p =
       (if is_aligned p 4 then {x. x && ~~ mask 4 = p && ~~ mask 4} else {p})"
  | "pte_range (SmallPagePTE ptr x y) p = {p}"

abbreviation "valid_pt_entries \<equiv> \<lambda>pt. valid_entries pte_range pt"

abbreviation "valid_pd_entries \<equiv> \<lambda>pd. valid_entries pde_range pd"

definition
  obj_valid_pdpt :: "kernel_object \<Rightarrow> bool"
where
 "obj_valid_pdpt obj \<equiv> case obj of
    ArchObj (PageTable pt) \<Rightarrow> valid_pt_entries pt \<and> entries_align pte_range_sz pt
  | ArchObj (PageDirectory pd) \<Rightarrow> valid_pd_entries pd \<and> entries_align pde_range_sz pd
  | _ \<Rightarrow> True"

lemmas obj_valid_pdpt_simps[simp]
    = obj_valid_pdpt_def
        [split_simps Structures_A.kernel_object.split
                     arch_kernel_obj.split]

abbreviation
  valid_pdpt_objs :: "'z state \<Rightarrow> bool"
where
 "valid_pdpt_objs s \<equiv> \<forall>x \<in> ran (kheap s). obj_valid_pdpt x"

lemma valid_pdpt_init[iff]:
  "valid_pdpt_objs init_A_st"
  by (auto simp: init_A_st_def init_kheap_def valid_entries_def entries_align_def
          elim!: ranE split: if_split_asm)

lemma set_object_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and K (obj_valid_pdpt obj)\<rbrace>
      set_object ptr obj
   \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: set_object_def get_object_def, wp)
  apply (auto simp: fun_upd_def[symmetric] del: ballI elim: ball_ran_updI)
  done

crunch cap_insert, cap_swap_for_delete,empty_slot
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps ignore:set_object)

crunch
  vcpu_save,vcpu_restore,vcpu_enable,get_vcpu,set_vcpu,vcpu_disable,vcpu_read_reg,
  read_vcpu_register,write_vcpu_register
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps ignore: set_object do_machine_op)

lemma vcpu_switch_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace>
     vcpu_switch v
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (rule hoare_pre)
  apply (wp | wpc | clarsimp)+
  done

crunch flush_page
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps ignore: set_object)

lemma add_3_eq_Suc'[simp]: "n + 3 = Suc (Suc (Suc n))" by simp

lemma shift_0x3C_set:
  "\<lbrakk> is_aligned p 7; 8 \<le> bits; bits < 32; len_of TYPE('a) = bits - 3 \<rbrakk> \<Longrightarrow>
   (\<lambda>x. ucast (x + p && mask bits >> 3) :: ('a :: len) word) ` set [0 :: word32 , 8 .e. 0x78]
        = {x. x && ~~ mask 4 = ucast (p && mask bits >> 3)}"
  apply (clarsimp simp: upto_enum_step_def word_shift_by_3 image_image)
  apply (subst image_cong[where N="{x. x < 2 ^ 4}"])
    apply (safe, simp_all)[1]
     apply (drule plus_one_helper2, simp_all)[1]
    apply (drule word_le_minus_one_leq, simp_all)[1]
   apply (rule_tac f="\<lambda>x. ucast (x && mask bits >> 3)" in arg_cong)
   apply (rule trans[OF add.commute is_aligned_add_or], assumption)
   apply (rule shiftl_less_t2n, simp_all)[1]
  apply safe
   apply (frule upper_bits_unset_is_l2p_32[THEN iffD2, rotated])
    apply (simp add: word_bits_conv)
   apply (rule word_eqI)
   apply (simp add: word_ops_nth_size word_size nth_ucast nth_shiftr
                    nth_shiftl neg_mask_test_bit
                    word_bits_conv)
   apply (safe, simp_all add: is_aligned_nth)[1]
  apply (rule_tac x="ucast x && mask 4" in image_eqI)
   apply (rule word_eqI[rule_format])
   apply (drule_tac x=n in word_eqD)
   apply (simp add: word_ops_nth_size word_size nth_ucast nth_shiftr
                    nth_shiftl)
   apply (safe, simp_all)
  apply (rule order_less_le_trans, rule and_mask_less_size)
   apply (simp_all add: word_size)
  done

lemma mapM_x_store_pte_updates:
  "\<forall>x \<in> set xs. f x && ~~ mask pt_bits = p \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> page_table_at p s \<longrightarrow> Q s) \<and>
        (\<forall>pt. ko_at (ArchObj (PageTable pt)) p s
           \<longrightarrow> Q (s \<lparr> kheap := (kheap s) (p := Some (ArchObj (PageTable (\<lambda>y. if y \<in> (\<lambda>x.
         ucast (f x && mask pt_bits >> 3)) ` set xs then pte else pt y)))) \<rparr>))\<rbrace>
     mapM_x (\<lambda>x. store_pte (f x) pte) xs
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
   apply wp
   apply (clarsimp simp: obj_at_def fun_upd_idem)
  apply (simp add: mapM_x_Cons)
  apply (rule bind_wp, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_pt_wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp simp add: vspace_bits_defs)
  apply (rule ext, clarsimp simp add: vspace_bits_defs)
  done

lemma valid_pt_entries_invalid[simp]:
  "valid_pt_entries (\<lambda>x. InvalidPTE)"
   by (simp add:valid_entries_def)

lemma valid_pd_entries_invalid[simp]:
  "valid_pd_entries (\<lambda>x. InvalidPDE)"
  by (simp add:valid_entries_def)

lemma entries_align_pte_update:
 "\<lbrakk>entries_align pte_range_sz pt;
  (\<forall>y. (P y) \<longrightarrow> is_aligned y (pte_range_sz pte))\<rbrakk>
  \<Longrightarrow> entries_align pte_range_sz (\<lambda>y. if (P y) then pte else pt y)"
  by (simp add:entries_align_def)

lemma entries_align_pde_update:
 "\<lbrakk>entries_align pde_range_sz pd;
  (\<forall>y. (P y) \<longrightarrow> is_aligned y (pde_range_sz pde))\<rbrakk>
  \<Longrightarrow> entries_align pde_range_sz (\<lambda>y. if (P y) then pde else pd y)"
  by (simp add:entries_align_def)


lemma valid_pdpt_objs_pdD:
  "\<lbrakk>valid_pdpt_objs s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PageDirectory pd))\<rbrakk>
   \<Longrightarrow> valid_pd_entries pd \<and> entries_align pde_range_sz pd"
  by (fastforce simp:ran_def)

lemma valid_pdpt_objs_ptD:
  "\<lbrakk>valid_pdpt_objs s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PageTable pt))\<rbrakk>
   \<Longrightarrow> valid_pt_entries pt \<and> entries_align pte_range_sz pt"
  by (fastforce simp:ran_def)

lemma mapM_x_store_invalid_pte_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and K (is_aligned p 7) \<rbrace>
     mapM_x (\<lambda>x. store_pte (x + p) InvalidPTE) [0, 8 .e. 0x78]
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (rule hoare_pre, rule_tac p="p && ~~ mask pt_bits" in mapM_x_store_pte_updates)
   apply clarsimp
   apply (rule mask_out_first_mask_some[where n=7])
    apply (drule_tac d=x in is_aligned_add_helper)
     apply (drule subsetD[OF upto_enum_step_subset])
     apply simp
     apply (erule order_le_less_trans, simp)
    apply (simp add: field_simps)
   apply (simp add: vspace_bits_defs)
  apply (clarsimp simp: ranI elim!: ranE split: if_split_asm)
  apply (intro conjI)
   apply (simp add: shift_0x3C_set vspace_bits_defs)
   apply (rule valid_entries_overwrite_groups
    [where S = "{x. x && ~~ mask 4 = ucast (p && mask 12 >> 3)}"])
      apply (fastforce simp add: obj_at_def ran_def)
     apply simp
    apply clarsimp
    apply (case_tac v)
      apply (simp split:if_splits)+
   apply (clarsimp)
   apply (case_tac v, simp_all split:if_splits)
    apply (intro conjI impI)
     apply (rule disjointI)
     apply (clarsimp)+
  apply (rule entries_align_pte_update)
   apply (clarsimp simp:obj_at_def)
   apply (drule(1) valid_pdpt_objs_ptD)
   apply simp
  apply (simp)
  done

lemma mapM_x_store_pde_updates:
  "\<forall>x \<in> set xs. f x && ~~ mask pd_bits = p \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> page_directory_at p s \<longrightarrow> Q s) \<and>
        (\<forall>pd. ko_at (ArchObj (PageDirectory pd)) p s
           \<longrightarrow> Q (s \<lparr> kheap := (kheap s) (p := Some (ArchObj (PageDirectory (\<lambda>y. if y \<in> (\<lambda>x.
         ucast (f x && mask pd_bits >> 3)) ` set xs then pde else pd y)))) \<rparr>))\<rbrace>
     mapM_x (\<lambda>x. store_pde (f x) pde) xs
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
   apply wp
   apply (clarsimp simp: obj_at_def fun_upd_idem)
  apply (simp add: mapM_x_Cons)
  apply (rule bind_wp, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_pd_wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp simp add: vspace_bits_defs)
  apply (rule ext, clarsimp simp add: vspace_bits_defs)
  done

lemma mapM_x_store_pde_valid_pdpt_objs:
  "\<lbrace>valid_pdpt_objs and K (is_aligned p 7)\<rbrace>
     mapM_x (\<lambda>x. store_pde (x + p) InvalidPDE) [0, 8 .e. 0x78]
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (rule hoare_pre, rule_tac p="p && ~~ mask pd_bits" in mapM_x_store_pde_updates)
   apply clarsimp
   apply (rule mask_out_first_mask_some[where n=7])
    apply (drule_tac d=x in is_aligned_add_helper)
     apply (drule subsetD[OF upto_enum_step_subset])
     apply simp
     apply (erule order_le_less_trans, simp)
    apply (simp add: field_simps)
   apply (simp add: vspace_bits_defs)
  apply (clarsimp simp: ranI elim!: ranE split: if_split_asm)
  apply (simp add: shift_0x3C_set vspace_bits_defs)
  apply (rule conjI)
   apply (rule_tac valid_entries_overwrite_groups
    [where S = "{x. x && ~~ mask 4 = ucast (p && mask 14 >> 3)}"])
      apply (fastforce simp add: obj_at_def ran_def)
     apply fastforce
    apply clarsimp
    apply (case_tac v, simp_all split:if_splits)
    apply clarsimp
    apply (case_tac v, simp_all split:if_splits)
   apply (intro conjI impI allI)
   apply (rule disjointI)
   apply clarsimp
  apply (rule entries_align_pde_update)
   apply (clarsimp simp:obj_at_def)
   apply (drule valid_pdpt_objs_pdD)
    apply (simp add:pd_bits_def pageBits_def)
   apply simp
  apply simp
  done

lemma store_invalid_pde_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and
    (\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s
      \<longrightarrow> pde = InvalidPDE)\<rbrace>
       store_pde p pde \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: store_pde_def set_pd_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
   apply (intro conjI)
   apply (rule valid_entries_overwrite_0, simp_all)
   apply (fastforce simp: ran_def)
  apply (simp add:fun_upd_def)
  apply (rule entries_align_pde_update)
   apply (drule(1) valid_pdpt_objs_pdD)
   apply simp
  apply simp
  done

lemma store_pde_non_master_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and
        (\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s
        \<longrightarrow> (pde_range_sz (pd (ucast (p && mask pd_bits >> 3) && ~~ mask 4)) = 0
        \<and> pde_range_sz pde = 0))\<rbrace>
       store_pde p pde \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: store_pde_def set_pd_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (intro conjI)
   apply (rule valid_entries_overwrite_0)
    apply (fastforce simp:ran_def)
   apply (drule bspec)
    apply fastforce
   apply (rename_tac p')
   apply (case_tac "pd p'"; cases pde; clarsimp simp: vspace_bits_defs)
  apply (simp add:fun_upd_def)
  apply (rule entries_align_pde_update)
   apply (drule(1) valid_pdpt_objs_pdD,simp)
  apply simp
  done

lemma store_invalid_pte_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and
        (\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits) s
        \<longrightarrow> pte = InvalidPTE)\<rbrace>
       store_pte p pte \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
   apply (intro conjI)
   apply (rule valid_entries_overwrite_0, simp_all)
   apply (fastforce simp: ran_def)
  apply (simp add:fun_upd_def)
  apply (rule entries_align_pte_update)
   apply (drule (1) valid_pdpt_objs_ptD,simp)
  apply simp
  done

lemma store_pte_non_master_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and
        (\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits) s
        \<longrightarrow> (pte_range_sz (pt (ucast (p && mask pt_bits >> 3) && ~~ mask 4)) = 0
        \<and> pte_range_sz pte = 0))\<rbrace>
       store_pte p pte \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (intro conjI)
   apply (rule valid_entries_overwrite_0)
    apply (fastforce simp:ran_def)
   apply (drule bspec)
    apply fastforce
   apply (case_tac "pt pa")
     apply simp
    apply (case_tac pte,simp_all)
    apply (clarsimp simp: vspace_bits_defs)
   apply (case_tac pte,simp_all)
  apply (simp add:fun_upd_def)
  apply (rule entries_align_pte_update)
   apply (drule (1) valid_pdpt_objs_ptD,simp)
  apply simp
  done

lemma unmap_page_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> unmap_page sz asid vptr pptr \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: unmap_page_def mapM_discarded
             cong: vmpage_size.case_cong)
  including no_pre apply wp
    prefer 2
    apply (rule valid_validE[OF find_pd_for_asid_inv])
  apply (rule hoare_pre)
   apply (wp get_object_wp get_pte_wp get_pde_wp lookup_pt_slot_inv_any
             store_invalid_pte_valid_pdpt
             store_invalid_pde_valid_pdpt
             mapM_x_store_invalid_pte_valid_pdpt mapM_x_store_pde_valid_pdpt_objs
                | simp add: mapM_x_map vspace_bits_defs largePagePTE_offsets_def superSectionPDE_offsets_def
                | wpc | simp add: check_mapping_pptr_def)+
  apply (simp add: fun_upd_def[symmetric] is_aligned_mask[symmetric])
  done

crunch flush_table
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps)

lemma unmap_page_table_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> unmap_page_table asid vptr pt \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: unmap_page_table_def)
  including no_pre apply (wp get_object_wp store_invalid_pde_valid_pdpt | wpc)+
  apply (simp add: obj_at_def)
  apply (simp add: page_table_mapped_def)
  apply (wp get_pde_wp | wpc)+
  apply simp
  apply (rule hoare_strengthen_postE, rule valid_validE,
         rule find_pd_for_asid_inv, simp_all)
  done

lemma set_simple_ko_valid_pdpt_objs[wp]:
   "\<lbrace>\<lambda>s. \<forall>x\<in>ran (kheap s). obj_valid_pdpt x\<rbrace>
       set_simple_ko param_a param_b param_c \<lbrace>\<lambda>_ s. \<forall>x\<in>ran (kheap s). obj_valid_pdpt x\<rbrace>"
  unfolding set_simple_ko_def
  apply (subst option.disc_eq_case(2))
  apply (wpsimp wp: set_object_valid_pdpt[THEN hoare_set_object_weaken_pre]
                    get_object_wp
              simp: a_type_simps obj_at_def)
  apply (clarsimp simp: a_type_def
                 split: kernel_object.splits)
  done

crunch finalise_cap, cap_swap_for_delete, empty_slot
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (wp: crunch_wps preemption_point_inv simp: crunch_simps unless_def ignore:set_object)

lemma preemption_point_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> preemption_point \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  by (wp preemption_point_inv | simp)+

lemmas cap_revoke_preservation_valid_pdpt_objs = cap_revoke_preservation[OF _,
                                                          where E=valid_pdpt_objs,
                                                          simplified, THEN validE_valid]

lemmas rec_del_preservation_valid_pdpt_objs = rec_del_preservation[OF _ _ _ _,
                                                    where P=valid_pdpt_objs, simplified]

crunch cap_delete, cap_revoke
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (rule: cap_revoke_preservation_valid_pdpt_objs)

crunch invalidate_tlb_by_asid, page_table_mapped
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"

lemma mapM_x_copy_pde_updates:
  "\<lbrakk> \<forall>x \<in> set xs. f x && ~~ mask pd_bits = 0; is_aligned p pd_bits;
               is_aligned p' pd_bits \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> page_directory_at p s \<longrightarrow> Q s) \<and> (\<not> page_directory_at p' s \<longrightarrow> Q s) \<and>
        (\<forall>pd pd'. ko_at (ArchObj (PageDirectory pd)) p s
                \<and> ko_at (ArchObj (PageDirectory pd')) p' s
           \<longrightarrow> Q (s \<lparr> kheap := (kheap s) (p' := Some (ArchObj (PageDirectory (\<lambda>y. if y \<in> (\<lambda>x.
         ucast (f x && mask pd_bits >> 3)) ` set xs then pd y else pd' y)))) \<rparr>))\<rbrace>
     mapM_x (\<lambda>x. get_pde (p + f x) >>= store_pde (p' + f x)) xs
   \<lbrace>\<lambda>_. Q\<rbrace>"
  including classic_wp_pre
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
   apply wp
   apply (clarsimp simp: obj_at_def fun_upd_idem dest!: a_type_pdD)
  apply (simp add: mapM_x_Cons)
  apply wp
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: store_pde_def set_pd_def set_object_def
             cong: bind_cong split del: if_split)
  apply (wp get_object_wp get_pde_wp)
  apply (clarsimp simp: obj_at_def a_type_simps mask_out_add_aligned[symmetric]
             split del: if_split)
  apply (simp add: a_type_simps, safe)
   apply (erule rsubst[where P=Q])
   apply (rule abstract_state.fold_congs[OF refl refl])
   apply (rule ext, clarsimp)
   apply (rule ext, simp)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp simp add: vspace_bits_defs)
  apply (rule ext, simp add: mask_add_aligned vspace_bits_defs)
  done

lemma copy_global_mappings_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs and valid_arch_state and pspace_aligned
            and K (is_aligned p pd_bits)\<rbrace>
       copy_global_mappings p \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_global_mappings_def)
  apply wp
  apply auto
  done

lemma in_pte_rangeD:
  "x \<in> pte_range v y \<Longrightarrow> x && ~~ mask 4 = y && ~~ mask 4"
  by (case_tac v,simp_all split:if_splits)

lemma in_pde_rangeD:
  "x \<in> pde_range v y \<Longrightarrow> x && ~~ mask 4 = y && ~~ mask 4"
  by (case_tac v,simp_all split:if_splits)

lemma mapM_x_store_pte_valid_pdpt2:
  "\<lbrace>valid_pdpt_objs and K (is_aligned ptr pt_bits)\<rbrace>
     mapM_x (\<lambda>x. store_pte x InvalidPTE) [ptr, ptr + 8 .e. ptr + 2 ^ pt_bits - 1]
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (rule mapM_x_wp')
  apply (simp add:store_pte_def set_pt_def)
  apply (wp get_pt_wp get_object_wp)
  apply (clarsimp simp: mask_in_range
    split:Structures_A.kernel_object.splits
    arch_kernel_obj.splits)
  apply (rule conjI)
   apply (rule valid_entries_overwrite_0)
    apply (fastforce simp:ran_def obj_at_def)
   apply simp
  apply (simp add:fun_upd_def obj_at_def)
  apply (rule entries_align_pte_update)
   apply (drule (1) valid_pdpt_objs_ptD,simp)
  apply simp
  done

lemma mapM_x_store_pde_valid_pdpt2:
  "\<lbrace>valid_pdpt_objs and K (is_aligned pd pd_bits)\<rbrace>
       mapM_x (\<lambda>x. store_pde ((x << 3) + pd) pde.InvalidPDE)
        [0.e.(kernel_base >> 20) - 1]
       \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule mapM_x_wp')
  apply (simp add:store_pde_def set_pd_def)
  apply (wp get_pd_wp get_object_wp)
  apply (clarsimp simp: mask_in_range
    split:Structures_A.kernel_object.splits
    arch_kernel_obj.splits)
  apply (rule conjI)
   apply (rule valid_entries_overwrite_0)
    apply (fastforce simp:ran_def obj_at_def)
   apply simp
  apply (simp add:fun_upd_def obj_at_def)
  apply (rule entries_align_pde_update)
   apply (drule (1) valid_pdpt_objs_pdD,simp)
  apply simp
  done

lemma non_invalid_in_pde_range:
  "pde \<noteq> InvalidPDE
  \<Longrightarrow> x \<in> pde_range pde x"
  by (case_tac pde,simp_all)

lemma non_invalid_in_pte_range:
  "pte \<noteq> InvalidPTE
  \<Longrightarrow> x \<in> pte_range pte x"
  by (case_tac pte,simp_all)

crunch cancel_badged_sends
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (simp: crunch_simps filterM_mapM wp: crunch_wps ignore: filterM)

crunch cap_move, cap_insert
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"

lemma invoke_cnode_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs and invs and valid_cnode_inv i\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp | wpc | simp split del: if_split)+
  done

crunch invoke_tcb
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (wp: check_cap_inv crunch_wps simp: crunch_simps
       ignore: check_cap_at)

lemma invoke_domain_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> invoke_domain t d \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  by (simp add: invoke_domain_def | wp)+

crunch set_extra_badge, transfer_caps_loop
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (rule: transfer_caps_loop_pres)

crunch send_ipc, send_signal,
    do_reply_transfer, invoke_irq_control, invoke_irq_handler
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps
         ignore: clearMemory const_on_failure set_object)

lemma valid_pdpt_objs_trans_state[simp]: "valid_pdpt_objs (trans_state f s) = valid_pdpt_objs s"
  apply (simp add: obj_valid_pdpt_def)
  done

lemma retype_region_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> retype_region ptr bits o_bits type dev \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: retype_region_def split del: if_split)
  apply (wp | simp only: valid_pdpt_objs_trans_state trans_state_update[symmetric])+
  apply (clarsimp simp: retype_addrs_fold foldr_upd_app_if ranI
                 elim!: ranE split: if_split_asm simp del:fun_upd_apply)
  apply (simp add: default_object_def default_arch_object_def
            split: Structures_A.kernel_object.splits
    Structures_A.apiobject_type.split aobject_type.split)+
  apply (simp add:entries_align_def)
  done

lemma detype_valid_pdpt[elim!]:
  "valid_pdpt_objs s \<Longrightarrow> valid_pdpt_objs (detype S s)"
  by (auto simp add: detype_def ran_def)

crunch create_cap
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (ignore: clearMemory simp: crunch_simps unless_def)

lemma init_arch_objects_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and pspace_aligned and valid_arch_state
           and K (\<exists>us sz. orefs = retype_addrs ptr type n us
               \<and> range_cover ptr sz (obj_bits_api type us) n)\<rbrace>
     init_arch_objects type ptr n obj_sz orefs
   \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (clarsimp simp: init_arch_objects_def
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc)+
     apply (rule_tac Q'="\<lambda>rv. valid_pdpt_objs and pspace_aligned and valid_arch_state"
                  in hoare_post_imp, simp)
     apply (rule mapM_x_wp')
     apply (rule hoare_pre, wp copy_global_mappings_valid_pdpt_objs)
     apply clarsimp
     apply (drule_tac sz=sz in retype_addrs_aligned)
        apply (simp add:range_cover_def)
       apply (drule range_cover.sz,simp add:word_bits_def)
      apply (simp add:range_cover_def)
     apply (clarsimp simp:obj_bits_api_def pd_bits_def pageBits_def
       arch_kobj_size_def default_arch_object_def range_cover_def)+
   apply wp
  apply simp
  done

lemma delete_objects_valid_pdpt:
  "\<lbrace>valid_pdpt_objs\<rbrace> delete_objects ptr bits \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  by (rule delete_objects_reduct) (wp detype_valid_pdpt)

crunch reset_untyped_cap
  for valid_pdpt[wp]: "valid_pdpt_objs"
  (wp: mapME_x_inv_wp crunch_wps simp: crunch_simps unless_def)

lemma invoke_untyped_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and invs and ct_active
          and valid_untyped_inv ui\<rbrace>
       invoke_untyped ui
   \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q)
      apply (wp init_arch_objects_valid_pdpt | simp)+
     apply (auto simp: post_retype_invs_def split: if_split_asm)[1]
    apply (wp | simp)+
  done

crunch perform_asid_pool_invocation,
     perform_asid_control_invocation
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (ignore: delete_objects wp: delete_objects_valid_pdpt hoare_weak_lift_imp)

abbreviation (input)
  "safe_pt_range \<equiv> \<lambda>slots s. obj_at (\<lambda>ko. \<exists>pt. ko = ArchObj (PageTable pt)
                                    \<and> (\<forall>x\<in>set (tl slots). pt (ucast (x && mask pt_bits >> 3))
                                      = pte.InvalidPTE))
                              (hd slots && ~~ mask pt_bits) s"

abbreviation (input)
  "safe_pd_range \<equiv> \<lambda>slots s. obj_at (\<lambda>ko. \<exists>pd. ko = ArchObj (PageDirectory pd)
                                    \<and> (\<forall>x\<in>set (tl slots). pd (ucast (x && mask pd_bits >> 3))
                                      = pde.InvalidPDE))
                              (hd slots && ~~ mask pd_bits) s"

definition
  "page_inv_entries_pre entries \<equiv>
   let slots = (case entries of Inl (pte, slots) \<Rightarrow> slots | Inr (pde, slots) \<Rightarrow> slots)
   in (if \<exists>sl. slots = [sl]
    then case entries of
        Inl (pte, _) \<Rightarrow> obj_at (\<lambda>ko. \<exists>pt pte. ko = ArchObj (PageTable pt)
                     \<and> pt (ucast (hd slots && mask pt_bits >> 3) && ~~ mask 4) = pte
                     \<and> pte_range_sz pte = 0)
                 (hd slots && ~~ mask pt_bits)
            and K (pte_range_sz pte = 0)
      | Inr (pde, _) \<Rightarrow> obj_at (\<lambda>ko. \<exists>pd pde. ko = ArchObj (PageDirectory pd)
                     \<and> pd (ucast (head slots && mask pd_bits >> 3) && ~~ mask 4)
                            = pde \<and> pde_range_sz pde = 0)
                 (hd slots && ~~ mask pd_bits)
           and K (pde_range_sz pde = 0)
    else  (\<lambda>s. (\<exists>p. is_aligned p 7 \<and> slots = map (\<lambda>x. x + p) [0, 8 .e. 0x78])))
   and K (case entries of Inl (pte,slots) \<Rightarrow> pte \<noteq> InvalidPTE
     | Inr (pde,slots) \<Rightarrow> pde \<noteq> InvalidPDE)"

definition
  "page_inv_entries_safe entries \<equiv>
   let slots = (case entries of Inl (pte, slots) \<Rightarrow> slots | Inr (pde, slots) \<Rightarrow> slots)
   in if \<exists>sl. slots = [sl]
    then case entries of
        Inl (pte, _) \<Rightarrow> obj_at (\<lambda>ko. \<exists>pt pte. ko = ArchObj (PageTable pt)
                     \<and> pt (ucast (hd slots && mask pt_bits >> 3) && ~~ mask 4) = pte
                     \<and> pte_range_sz pte = 0)
                 (hd slots && ~~ mask pt_bits)
            and K (pte_range_sz pte = 0)
      | Inr (pde, _) \<Rightarrow> obj_at (\<lambda>ko. \<exists>pd pde. ko = ArchObj (PageDirectory pd)
                     \<and> pd (ucast (head slots && mask pd_bits >> 3) && ~~ mask 4)
                            = pde \<and> pde_range_sz pde = 0)
                 (hd slots && ~~ mask pd_bits)
           and K (pde_range_sz pde = 0)
    else  (\<lambda>s. (\<exists>p. is_aligned p 7 \<and> slots = map (\<lambda>x. x + p) [0, 8 .e. 0x78]
                  \<and> (case entries of
                     Inl (pte, _) \<Rightarrow> safe_pt_range slots s
                   | Inr (pde, _) \<Rightarrow> safe_pd_range slots s
                     )))"

definition
  "page_inv_duplicates_valid iv \<equiv> case iv of
         PageMap asid cap ct_slot entries \<Rightarrow>
            page_inv_entries_safe entries
       | _ \<Rightarrow> \<top>"

lemma pte_range_interD:
 "pte_range pte p \<inter> pte_range pte' p' \<noteq> {}
  \<Longrightarrow> pte \<noteq> InvalidPTE \<and> pte' \<noteq> InvalidPTE
      \<and> p && ~~ mask 4 = p' && ~~ mask 4"
  apply (drule int_not_emptyD)
  apply (case_tac pte,simp_all split:if_splits)
   apply (case_tac pte',simp_all split:if_splits)
   apply clarsimp
   apply (case_tac pte',simp_all split:if_splits)
  apply (case_tac pte', simp_all split:if_splits)
  done

lemma pde_range_interD:
 "pde_range pde p \<inter> pde_range pde' p' \<noteq> {}
  \<Longrightarrow> pde \<noteq> InvalidPDE \<and> pde' \<noteq> InvalidPDE
      \<and> p && ~~ mask 4 = p' && ~~ mask 4"
  apply (drule int_not_emptyD)
  apply (case_tac pde,simp_all split:if_splits)
     apply (case_tac pde',simp_all split:if_splits)
    apply (case_tac pde',simp_all split:if_splits)
   apply clarsimp
   apply (case_tac pde', simp_all split:if_splits)
  apply (case_tac pde', simp_all split:if_splits)
  done

lemma pte_range_sz_le:
  "(pte_range_sz pte) \<le> 4"
  by (case_tac pte,simp_all)

lemma pde_range_sz_le:
  "(pde_range_sz pde) \<le> 4"
  by (case_tac pde,simp_all)

(* BUG , revisit the following lemmas , moved from ArchAcc_R.thy *)
lemma mask_pd_bits_shift_ucast_align[simp]:
  "is_aligned (ucast (p && mask pd_bits >> 3)::11 word) 4 =
   is_aligned ((p::word32) >> 3) 4"
  by (clarsimp simp: is_aligned_mask mask_def vspace_bits_defs) word_bitwise

lemma mask_pt_bits_shift_ucast_align[simp]:
  "is_aligned (ucast (p && mask pt_bits >> 3)::9 word) 4 =
   is_aligned ((p::word32) >> 3) 4"
  by (clarsimp simp: is_aligned_mask mask_def vspace_bits_defs)
     word_bitwise

lemma ucast_pt_index:
  "\<lbrakk>is_aligned (p::word32) (4 + pte_bits)\<rbrakk>
   \<Longrightarrow> ucast ((pa && mask 4) + (ucast (p && mask pt_bits >> pte_bits)::9 word))
   =  ucast (pa && mask 4) + (p && mask pt_bits >> pte_bits)"
  apply (simp add:is_aligned_mask mask_def vspace_bits_defs)
  apply word_bitwise
  apply (auto simp: carry_def)
  done

lemma unat_ucast_9_32:
  fixes x :: "9 word"
  shows "unat (ucast x :: word32) = unat x"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
   apply simp
  apply simp
  done

lemma store_pte_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and page_inv_entries_safe (Inl (pte, slots))\<rbrace>
       store_pte (hd slots) pte \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:page_inv_entries_safe_def split:if_splits)
   apply (clarsimp simp:store_pte_def set_pt_def)
   apply (wp get_pt_wp get_object_wp)
   apply (clarsimp simp:obj_at_def pte_bits_def
     split:pte.splits arch_kernel_obj.splits)
  apply (rule conjI)
    apply (drule(1) valid_pdpt_objs_ptD)
    apply (rule valid_entries_overwrite_0)
     apply simp
    apply (case_tac pte)
     apply simp+
    apply (case_tac "pta p",simp_all)
    apply clarsimp
   apply (simp add:fun_upd_def)
   apply (rule entries_align_pte_update)
    apply (drule (1) valid_pdpt_objs_ptD,simp)
   apply simp
  apply (simp add:hd_map_simp upto_enum_def upto_enum_step_def)
  apply (clarsimp simp:store_pte_def set_pt_def)
  apply (wp get_pt_wp get_object_wp)
  apply (clarsimp simp:obj_at_def pte_bits_def
     split:pte.splits arch_kernel_obj.splits)
  apply (drule(1) valid_pdpt_objs_ptD)
  apply (rule conjI)
   apply (rule valid_entries_overwrite_0)
    apply simp
   apply (rule ccontr)
   apply (drule pte_range_interD)
   apply clarsimp
   apply (simp add:ucast_neg_mask)
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 4])
    apply (rule is_aligned_shiftr[OF is_aligned_andI1])
    apply simp
   apply (drule_tac x = "((p && ~~ mask pt_bits)  + ((ucast pa) << 3))" in bspec)
    apply (clarsimp simp: tl_map_simp upto_0_to_n2 image_def)
    apply (rule_tac x = "unat (((ucast pa)::word32) - (p && mask pt_bits >> 3))" in bexI)
     apply (simp add:ucast_nat_def shiftl_t2n mask_out_sub_mask)
     apply (subst shiftl_t2n[where n = 3,simplified field_simps,simplified,symmetric])
     apply (subst shiftr_shiftl1)
      apply simp+
     apply (subst is_aligned_neg_mask_eq)
      apply (erule is_aligned_andI1[OF is_aligned_weaken])
      apply simp
     apply simp
    apply simp
    apply (drule_tac s = "ucast (p && mask pt_bits >> 3)" in sym)
    apply (simp add:mask_out_sub_mask field_simps)
    apply (drule_tac f = "ucast::(9 word\<Rightarrow>word32)" in arg_cong)
    apply (simp add: ucast_pt_index[simplified pte_bits_def])
    apply (simp add:unat_ucast_9_32)
    apply (rule conjI)
     apply (subgoal_tac "unat (pa && mask 4)\<noteq> 0")
      apply simp
     apply (simp add:unat_gt_0)
    apply (rule unat_less_helper)
    apply (rule le_less_trans[OF word_and_le1])
    apply (simp add:mask_def)
   apply (simp add:field_simps neg_mask_add_mask)
   apply (thin_tac "ucast y = x" for y x)
   apply (subst (asm) less_mask_eq[where n = pt_bits])
    apply (rule shiftl_less_t2n)
     apply (simp add:vspace_bits_defs)
     apply word_bitwise
    apply (simp add:vspace_bits_defs)
   apply (subst (asm) shiftl_shiftr_id)
    apply simp
   apply (simp,word_bitwise)
   apply (simp add:ucast_ucast_id)
  apply (simp add:fun_upd_def entries_align_def)
  apply (rule is_aligned_weaken[OF _ pte_range_sz_le])
  apply (simp add:is_aligned_shiftr)
  done


lemma ucast_pd_index:
  "\<lbrakk>is_aligned (p::word32) (4 + pde_bits)\<rbrakk>
   \<Longrightarrow> ucast ((pa && mask 4) + (ucast (p && mask pd_bits >> pde_bits)::11 word))
   =  ucast (pa && mask 4) + (p && mask pd_bits >> pde_bits)"
  apply (simp add:is_aligned_mask mask_def vspace_bits_defs)
  apply word_bitwise
  apply (auto simp:carry_def)
  done

lemma unat_ucast_11_32:
  "unat (ucast (x::(11 word))::word32) = unat x"
  apply (subst unat_ucast)
  apply (rule mod_less)
  apply (rule less_le_trans[OF unat_lt2p])
  apply simp
  done

lemma ucast_pd_index11:
  "\<lbrakk>is_aligned (p::word32) 7\<rbrakk>
   \<Longrightarrow> ucast ((pa && mask 4) + (ucast (p && mask 14 >> 3)::11 word))
   =  ucast (pa && mask 4) + (p && mask 14 >> 3)"
  apply (simp add:is_aligned_mask mask_def)
  apply word_bitwise
  apply (auto simp:carry_def)
  done


lemma store_pde_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and page_inv_entries_safe (Inr (pde, slots))\<rbrace>
       store_pde (hd slots) pde \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:page_inv_entries_safe_def split:if_splits)
   apply (clarsimp simp:store_pde_def set_pd_def)
   apply (wp get_pd_wp get_object_wp)
   apply (clarsimp simp:obj_at_def pde_bits_def
     split:pde.splits arch_kernel_obj.splits)
   apply (drule(1) valid_pdpt_objs_pdD)
   apply (rule conjI)
    apply (rule valid_entries_overwrite_0)
     apply simp
    apply (case_tac pde,simp_all)
     apply (case_tac "pda p",simp_all)
     apply clarsimp
    apply (case_tac "pda p",simp_all)
    apply clarsimp
   apply (simp add:fun_upd_def)
   apply (rule entries_align_pde_update)
    apply simp+
  apply (simp add:hd_map_simp upto_enum_def upto_enum_step_def)
  apply (clarsimp simp:store_pde_def set_pd_def)
  apply (wp get_pd_wp get_object_wp)
  apply (clarsimp simp:obj_at_def pde_bits_def
     split:pde.splits arch_kernel_obj.splits)
  apply (drule(1) valid_pdpt_objs_pdD)
  apply (rule conjI)
   apply (rule valid_entries_overwrite_0)
    apply simp
   apply (rule ccontr)
   apply (drule pde_range_interD)
   apply clarsimp
   apply (simp add:ucast_neg_mask)
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 4])
    apply (rule is_aligned_shiftr[OF is_aligned_andI1])
    apply simp
   apply (drule_tac x = "((p && ~~ mask pd_bits)  + ((ucast pa) << 3))" in bspec)
    apply (clarsimp simp: tl_map_simp upto_0_to_n2 image_def)
    apply (rule_tac x = "unat (((ucast pa)::word32) - (p && mask pd_bits >> 3))" in bexI)
     apply (simp add:ucast_nat_def shiftl_t2n mask_out_sub_mask)
     apply (subst shiftl_t2n[where n = 3,simplified field_simps,simplified,symmetric])
     apply (subst shiftr_shiftl1)
      apply simp+
     apply (subst is_aligned_neg_mask_eq)
      apply (erule is_aligned_andI1[OF is_aligned_weaken])
      apply simp
     apply simp
    apply simp
    apply (drule_tac s = "ucast (p && mask pd_bits >> 3)" in sym)
    apply (simp add:mask_out_sub_mask field_simps)
    apply (drule_tac f = "ucast::(11 word\<Rightarrow>word32)" in arg_cong)
    apply (simp add:ucast_pd_index[simplified pde_bits_def])
    apply (simp add:unat_ucast_11_32)
    apply (rule conjI)
     apply (subgoal_tac "unat (pa && mask 4)\<noteq> 0")
      apply simp
     apply (simp add:unat_gt_0)
    apply (rule unat_less_helper)
    apply (rule le_less_trans[OF word_and_le1])
    apply (simp add:mask_def)
   apply (simp add:field_simps neg_mask_add_mask)
   apply (thin_tac "ucast y = x" for y x)
   apply (subst (asm) less_mask_eq[where n = pd_bits])
    apply (rule shiftl_less_t2n)
     apply (simp add:vspace_bits_defs)
     apply word_bitwise
    apply (simp add:vspace_bits_defs)
   apply (subst (asm) shiftl_shiftr_id)
     apply simp
    apply (simp,word_bitwise)
   apply (simp add:ucast_ucast_id)
  apply (simp add:entries_align_def)
  apply (rule is_aligned_weaken[OF _ pde_range_sz_le])
  apply (simp add:is_aligned_shiftr)
  done


lemma set_cap_page_inv_entries_safe:
  "\<lbrace>page_inv_entries_safe x\<rbrace> set_cap y z \<lbrace>\<lambda>_. page_inv_entries_safe x\<rbrace>"
  apply (simp add:page_inv_entries_safe_def set_cap_def split_def
    get_object_def set_object_def)
  apply (wp | wpc)+
  apply (case_tac x)
  apply (auto simp:obj_at_def
    Let_def split:if_splits option.splits)
  done

crunch pte_check_if_mapped, pde_check_if_mapped
  for inv[wp]: "\<lambda>s. P s"

lemma perform_page_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and valid_page_inv pinv and page_inv_duplicates_valid pinv\<rbrace>
        perform_page_invocation pinv \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: perform_page_invocation_def page_inv_duplicates_valid_def)
  apply (cases pinv,
         simp_all add: mapM_discarded page_inv_entries_safe_def
            split: sum.split arch_cap.split option.split,
         safe intro!: hoare_gen_asm hoare_gen_asm[unfolded K_def],
         simp_all add: mapM_x_Nil mapM_x_Cons mapM_x_map)
            apply (wp store_pte_valid_pdpt store_pde_valid_pdpt get_master_pte_wp get_master_pde_wp
                      store_pte_non_master_valid_pdpt store_pde_non_master_valid_pdpt
                      mapM_x_wp'[OF store_invalid_pte_valid_pdpt
                        [where pte=pte.InvalidPTE, simplified]]
                      mapM_x_wp'[OF store_invalid_pde_valid_pdpt
                        [where pde=pde.InvalidPDE, simplified]]
                      set_cap_page_inv_entries_safe
                      hoare_vcg_imp_lift[OF set_cap_arch_obj_neg] hoare_vcg_all_lift
                 | clarsimp simp: cte_wp_at_weakenE[OF _ TrueI] obj_at_def
                                  pte_range_sz_def pde_range_sz_def swp_def valid_page_inv_def
                                  valid_slots_def page_inv_entries_safe_def pte_check_if_mapped_def
                                  pde_check_if_mapped_def
                           split: pte.splits pde.splits
                 | wp (once) hoare_drop_imps)+
  done

definition
  "pti_duplicates_valid iv \<equiv>
   case iv of PageTableMap cap ct_slot pde pd_slot
     \<Rightarrow> obj_at (\<lambda>ko. \<exists>pd pde. ko = ArchObj (PageDirectory pd)
                     \<and> pd (ucast (pd_slot && mask pd_bits >> 3) && ~~ mask 4)
                            = pde \<and> pde_range_sz pde = 0)
                 (pd_slot && ~~ mask pd_bits)

           and K (pde_range_sz pde = 0)
  | _ \<Rightarrow> \<top>"


definition
  "invocation_duplicates_valid i \<equiv>
   case i of
     InvokeArchObject (InvokePage pinv) \<Rightarrow> page_inv_duplicates_valid pinv
   | InvokeArchObject (InvokePageTable pti) \<Rightarrow> pti_duplicates_valid pti
   | _ \<Rightarrow> \<top>"

lemma perform_page_table_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and valid_pti pinv and pti_duplicates_valid pinv\<rbrace>
      perform_page_table_invocation pinv \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: perform_page_table_invocation_def split_def vspace_bits_defs
             cong: page_table_invocation.case_cong
                   option.case_cong cap.case_cong arch_cap.case_cong)
  apply (rule hoare_pre)
   apply (wp store_pde_non_master_valid_pdpt hoare_vcg_ex_lift
             set_cap_arch_obj mapM_x_store_pte_valid_pdpt2[simplified vspace_bits_defs, simplified]
              | wpc
              | simp add: swp_def
              | strengthen all_imp_ko_at_from_ex_strg)+
  apply (clarsimp simp: pti_duplicates_valid_def valid_pti_def)
  apply (auto simp: obj_at_def cte_wp_at_caps_of_state valid_cap_simps
                    cap_aligned_def vspace_bits_defs
            intro!: inj_onI)
  done

lemma perform_page_directory_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and valid_pdi pinv\<rbrace>
      perform_page_directory_invocation pinv \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: perform_page_directory_invocation_def split_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
  done

crunch perform_vcpu_invocation
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (ignore: delete_objects wp: delete_objects_valid_pdpt hoare_weak_lift_imp)


lemma perform_invocation_valid_pdpt[wp]:
  "\<lbrace>invs and ct_active and valid_invocation i and valid_pdpt_objs
           and invocation_duplicates_valid i\<rbrace>
      perform_invocation blocking call i
         \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (cases i, simp_all)
  apply (wp send_signal_interrupt_states | simp)+
  apply (simp add: arch_perform_invocation_def)
  apply (rule hoare_pre)
  apply (wp | wpc | simp)+
  apply (auto simp: valid_arch_inv_def invocation_duplicates_valid_def)
  done

lemma neg_mask_pt_7_4:
  "(ptr && mask pt_bits >> 3) && ~~ mask 4 =
   (ptr::word32) && ~~ mask 7 && mask pt_bits >> 3"
  by (word_eqI_solve simp: vspace_bits_defs)

lemma neg_mask_pd_7_4:
  "(ptr && mask pd_bits >> 3) && ~~ mask 4 =
   (ptr::word32) && ~~ mask 7 && mask pd_bits >> 3"
  by (word_eqI_solve simp: vspace_bits_defs)

lemma mask_out_same_pt:
  "\<lbrakk>is_aligned p 7; x < 2 ^ 7 \<rbrakk> \<Longrightarrow> p + x && ~~ mask pt_bits = p && ~~ mask pt_bits"
  apply (subst mask_lower_twice[symmetric,where n = 7])
   apply (simp add:vspace_bits_defs)
  apply (simp add:is_aligned_add_helper)
  done

lemma mask_out_same_pd:
  "\<lbrakk>is_aligned p 7; x < 2 ^ 7 \<rbrakk> \<Longrightarrow> p + x && ~~ mask pd_bits = p && ~~ mask pd_bits"
  apply (subst mask_lower_twice[symmetric,where n = 7])
   apply (simp add:pd_bits_def pageBits_def)
  apply (simp add:is_aligned_add_helper)
  done

lemma ensure_safe_mapping_ensures[wp]:
  "\<lbrace>valid_pdpt_objs and (case entries of (Inl (SmallPagePTE _ _ _, [_])) \<Rightarrow> \<top>
                  | (Inl (SmallPagePTE _ _ _, _)) \<Rightarrow> \<bottom>
                  | (Inl (LargePagePTE _ _ _, [])) \<Rightarrow> \<bottom>
                  | (Inr (SectionPDE _ _ _, [_])) \<Rightarrow> \<top>
                  | (Inr (SuperSectionPDE _ _ _, [])) \<Rightarrow> \<bottom>
                  | (Inr (SectionPDE _ _ _, _)) \<Rightarrow> \<bottom>
                  | _ \<Rightarrow> page_inv_entries_pre entries)\<rbrace>
     ensure_safe_mapping entries
   \<lbrace>\<lambda>rv. page_inv_entries_safe entries\<rbrace>,-"
  proof -
    have [simp]:
      "\<And>s a. page_inv_entries_pre (Inl (pte.InvalidPTE, a)) s \<Longrightarrow>
      page_inv_entries_safe (Inl (pte.InvalidPTE, a)) s"
      apply (clarsimp simp:page_inv_entries_pre_def page_inv_entries_safe_def
        split:if_splits)
      done
    have name_pre:
      "\<And>F P Q. (\<And>s. P s \<Longrightarrow> \<lbrace>(=) s \<rbrace> F \<lbrace>Q\<rbrace>, -) \<Longrightarrow> \<lbrace>P\<rbrace> F \<lbrace>Q\<rbrace>,-"
      apply (simp add:validE_R_def validE_def)
      apply (rule hoare_name_pre_state)
      apply assumption
      done
    have mask_neg_mask_order[simp]:
      "\<And>a m n. a && ~~ mask m && mask n = a && mask n && ~~ mask m"
       by (simp add:word_bw_comms word_bw_lcs)
    have align_entry_ptD:
      "\<And>pt m x xb xc. \<lbrakk>pt m = pte.LargePagePTE x xb xc; entries_align pte_range_sz pt\<rbrakk>
       \<Longrightarrow> is_aligned m 4"
      apply (simp add:entries_align_def)
      apply (drule_tac x = m in spec,simp)
      done
    have align_entry_pdD:
      "\<And>pd m x xb xc. \<lbrakk>pd m = pde.SuperSectionPDE x xb xc; entries_align pde_range_sz pd\<rbrakk>
       \<Longrightarrow> is_aligned m 4"
      apply (simp add:entries_align_def)
      apply (drule_tac x = m in spec,simp)
      done
    have pt_offset_bitwise[simp]:"\<And>a. (ucast ((a::word32) && mask pt_bits && ~~ mask 7  >> 3)::9 word)
      = (ucast (a  && mask pt_bits >> 3)::9 word) && ~~ mask 4"
    apply (simp add: vspace_bits_defs mask_def)
    apply word_bitwise
    done
    have pt_offset_bitwise_pt_bits[simp]:"\<And>a. (ucast ((a::word32) && mask pt_bits && ~~ mask 7  >> pte_bits)::9 word)
      = (ucast (a  && mask pt_bits >> 3)::9 word) && ~~ mask 4"
    by (simp add: pte_bits_def)
    have pd_offset_bitwise[simp]:"\<And>a. (ucast ((a::word32) && mask pd_bits && ~~ mask 7  >> 3)::11 word)
      = (ucast (a  && mask pd_bits >> 3)::11 word) && ~~ mask 4"
    apply (simp add: vspace_bits_defs mask_def)
    apply word_bitwise
    done
    have pd_offset_bitwise_pt_bits[simp]:"\<And>a. (ucast ((a::word32) && mask pd_bits && ~~ mask 7  >> pde_bits)::11 word)
      = (ucast (a  && mask pd_bits >> 3)::11 word) && ~~ mask 4"
    by (simp add: pde_bits_def)
    have mask_neq_0:
      "\<And>z zs xa p g. \<lbrakk>[0 :: word32, 8 .e. 0x78] = z # zs; xa \<in> set zs; is_aligned p 7; 7 \<le> g\<rbrakk>
         \<Longrightarrow> (p + xa && mask g >> 3) && mask 4 \<noteq> 0"
     apply (rule ccontr)
      apply (simp add:is_aligned_mask[symmetric])
       apply (drule is_aligned_shiftl[where n = 7 and m = 3,simplified])
      apply (subst (asm) shiftr_shiftl1)
       apply simp+
      apply (subst (asm) is_aligned_neg_mask_eq)
       apply (rule is_aligned_andI1)
       apply (erule aligned_add_aligned)
        apply (clarsimp simp :upto_enum_def upto_enum_step_def
         Fun.comp_def upto_0_to_n2 is_aligned_mult_triv2[where n = 3,simplified])
       apply simp
      apply (simp add:is_aligned_mask mask_twice
        pt_bits_def pageBits_def min_def)
      apply (subst (asm) is_aligned_mask[symmetric])
      apply (subst (asm) is_aligned_add_helper)
       apply simp
      apply (clarsimp simp :upto_enum_def upto_enum_step_def
         Fun.comp_def upto_0_to_n2)
      apply (subst shiftl_t2n
        [where n = 3,simplified field_simps,simplified,symmetric])+
      apply (rule shiftl_less_t2n[where m = 7,simplified])
       apply (rule word_of_nat_less)
       apply simp
      apply simp
     apply (clarsimp simp :upto_enum_def upto_enum_step_def
         Fun.comp_def upto_0_to_n2)
     apply (cut_tac x = "of_nat x" and n = 3 in word_power_nonzero_32)
         apply (simp add:word_of_nat_less word_bits_def of_nat_neq_0)+
     done
    have neq_pt_offset: "\<And>z zs xa (p::word32). \<lbrakk>[0 , 8 .e. 0x78] = z # zs;
        xa \<in> set zs;is_aligned p 7 \<rbrakk> \<Longrightarrow>
        ucast (p + xa && mask pt_bits >> 3) && ~~ mask 4 \<noteq> ((ucast (p + xa && mask pt_bits >> 3))::9 word)"
      apply (rule ccontr)
      apply (simp add:mask_out_sub_mask ucast_and_mask[symmetric])
      apply (drule arg_cong[where f = unat])
      apply (simp add:unat_ucast)
      apply (subst (asm) mod_less)
       apply (rule unat_less_helper)
       apply (rule le_less_trans[OF word_and_le1])
       apply (simp add:mask_def)
      apply (simp add:unat_eq_0)
      apply (drule(2) mask_neq_0[of _ _ _ _ pt_bits])
       apply (simp add:pt_bits_def pageBits_def)+
      done
    have neq_pd_offset: "\<And>z zs xa (p::word32). \<lbrakk>[0 , 8 .e. 0x78] = z # zs;
        xa \<in> set zs;is_aligned p 7 \<rbrakk> \<Longrightarrow>
        ucast (p + xa && mask pd_bits >> 3) && ~~ mask 4 \<noteq> ((ucast (p + xa && mask pd_bits >> 3)) :: 11 word)"
      apply (simp add:mask_out_sub_mask)
      apply (rule ccontr)
      apply (simp add:mask_out_sub_mask ucast_and_mask[symmetric])
      apply (drule arg_cong[where f = unat])
      apply (simp add:unat_ucast)
      apply (subst (asm) mod_less)
       apply (rule unat_less_helper)
       apply (rule le_less_trans[OF word_and_le1])
       apply (simp add:mask_def)
      apply (simp add:unat_eq_0)
      apply (drule(2) mask_neq_0[of _ _ _ _ pd_bits])
       apply (simp add:pd_bits_def pageBits_def)+
      done
    have invalid_pteI:
      "\<And>a pt x y z. \<lbrakk>valid_pt_entries pt; (a && ~~ mask 4) \<noteq> a;
       pt (a && ~~ mask 4) = pte.LargePagePTE x y z \<rbrakk>
       \<Longrightarrow> pt a = pte.InvalidPTE"
      apply (drule(1) valid_entriesD[rotated])
      apply (case_tac "pt a"; simp add:mask_lower_twice is_aligned_neg_mask split:if_splits)
      done
    have invalid_pdeI:
      "\<And>a pd x y z. \<lbrakk>valid_pd_entries pd; (a && ~~ mask 4) \<noteq> a;
       pd (a && ~~ mask 4) = pde.SuperSectionPDE x y z \<rbrakk>
       \<Longrightarrow> pd a = pde.InvalidPDE"
      apply (drule(1) valid_entriesD[rotated])
      apply (case_tac "pd a",
        simp_all add:mask_lower_twice is_aligned_neg_mask
        split:if_splits)
      done
    have inj[simp]:
      "\<And>p. is_aligned (p::word32) 7 \<Longrightarrow> inj_on (\<lambda>x. toEnum x * 8 + p) {Suc 0..<16}"
      apply (clarsimp simp:inj_on_def)
      apply (subst (asm) shiftl_t2n[where n = 3,simplified field_simps,simplified,symmetric])+
      apply (drule arg_cong[where f = "\<lambda>x. x >> 3"])
      apply (simp add:shiftl_shiftr_id word_of_nat_less)
      apply (simp add:of_nat_inj)
      done

  show ?thesis
  apply (rule name_pre)
  apply (case_tac entries)
   apply (case_tac a, case_tac aa)
     apply (simp add:page_inv_entries_pre_def page_inv_entries_safe_def
       | wp | intro conjI impI)+
     apply (simp split:list.splits add:page_inv_entries_pre_def)+
    apply (rename_tac obj_ref vm_attributes cap_rights slot slots)
    apply (elim conjE exE)
    apply (subst mapME_x_Cons)
    apply simp
    apply wp
     apply (rule_tac Q' = "\<lambda>r s. \<forall>x \<in> set slots. obj_at
                (\<lambda>ko. \<exists>pt. ko = ArchObj (PageTable pt) \<and>
                 pt (ucast (x && mask pt_bits >> 3)) = pte.InvalidPTE)
                (hd (slot # slots) && ~~ mask pt_bits) s" in hoare_strengthen_postE_R)
      apply (wp mapME_x_accumulate_checks[where Q = "\<lambda>s. valid_pdpt_objs s"] )
          apply (wp get_master_pte_wp| wpc | simp)+
         apply clarsimp
         apply (frule_tac x = xa in mask_out_same_pt)
          apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2)
          apply (subst shiftl_t2n[where n = 3,simplified field_simps,simplified,symmetric])
          apply (rule shiftl_less_t2n[where m = 7,simplified])
           apply (simp add:word_of_nat_less)
          apply simp
         apply (frule_tac x = z in mask_out_same_pt)
          apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2)
         apply (clarsimp simp:field_simps obj_at_def
           split:pte.splits)
         apply (intro conjI impI)
             apply (clarsimp simp: pte_bits_def)
            apply (drule(1) valid_pdpt_objs_ptD)
            apply (clarsimp simp: bit.conj_assoc)
            apply (frule align_entry_ptD,simp)
            apply (clarsimp simp: is_aligned_neg_mask_eq[of _ 4] pte_bits_def)
           apply clarsimp
           apply (drule(1) valid_pdpt_objs_ptD,clarify)
           apply (erule(4) invalid_pteI[OF _ neq_pt_offset])
          apply (clarsimp simp: pte_bits_def)
         apply (clarsimp simp:  pte_bits_def)
         apply (drule(1) valid_pdpt_objs_ptD)
         apply (frule align_entry_ptD,simp)
         apply simp
        apply (wp hoare_drop_imps |wpc|simp)+
      apply (clarsimp simp:upto_enum_def upto_enum_step_def
        upto_0_to_n2 Fun.comp_def distinct_map)
     apply (intro exI conjI,fastforce+)
     apply (simp add:obj_at_def hd_map_simp
         upto_0_to_n2 upto_enum_def upto_enum_step_def)
     apply (frule_tac x = 1 in bspec,fastforce+)
    apply ((wp hoare_drop_imps |wpc|simp)+)[1]
   apply (simp add:page_inv_entries_pre_def page_inv_entries_safe_def
       | wp | intro conjI impI)+
    apply (simp split:list.splits add:page_inv_entries_pre_def mapME_singleton)
    apply (wp get_master_pte_wp |wpc | simp)+
    apply (clarsimp simp:obj_at_def split:pte.splits)
   apply (clarsimp simp:page_inv_entries_safe_def split:list.splits)
  apply (simp split:list.splits add:page_inv_entries_pre_def mapME_singleton)
  apply (case_tac b,case_tac a)
     apply ((simp add:page_inv_entries_pre_def page_inv_entries_safe_def
       | wp | intro conjI impI)+)[1]
    apply simp
    apply wp[1]
   apply (simp split:list.splits add:page_inv_entries_pre_def mapME_singleton)
   apply (wp get_master_pde_wp | wpc | simp)+
   apply (clarsimp simp:obj_at_def page_inv_entries_safe_def pde_bits_def
     split:pde.splits)
  apply (simp split:list.splits if_splits
    add:page_inv_entries_pre_def Let_def page_inv_entries_safe_def)
  apply (elim conjE exE)
  apply (subst mapME_x_Cons)
  apply simp
  apply wp
   apply (rule_tac Q' = "\<lambda>r s. \<forall>x \<in> set x22.
                                 obj_at (\<lambda>ko. \<exists>pd. ko = ArchObj (PageDirectory pd) \<and>
                                                   pd (ucast (x && mask pd_bits >> 3)) = InvalidPDE)
                               (x21 && ~~ mask pd_bits) s" in hoare_strengthen_postE_R)
    apply (wp mapME_x_accumulate_checks[where Q = "\<lambda>s. valid_pdpt_objs s"] )
        apply (wp get_master_pde_wp| wpc | simp)+
       apply clarsimp
       apply (frule_tac x = xa in mask_out_same_pd)
        apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2)
        apply (subst shiftl_t2n[where n = 3,simplified field_simps,simplified,symmetric])
        apply (rule shiftl_less_t2n[where m = 7,simplified])
         apply (simp add:word_of_nat_less)
        apply simp
       apply (frule_tac x = z in mask_out_same_pd)
        apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2)
       apply (clarsimp simp: field_simps obj_at_def split: pde.splits)
       apply (drule(1) valid_pdpt_objs_pdD)
       apply (intro conjI impI; clarsimp simp: pde_bits_def)
          apply (frule align_entry_pdD,simp)
          apply (clarsimp simp: pde_bits_def)
         apply (frule(1) align_entry_pdD)
         apply simp
        apply (frule(1) align_entry_pdD)
        apply simp
       apply (frule(1) align_entry_pdD)
       apply (erule(4) invalid_pdeI[OF _ neq_pd_offset])
      apply (wp hoare_drop_imps |wpc|simp)+
    apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2 Fun.comp_def distinct_map)
   apply (intro exI conjI,fastforce+)
   apply (simp add:obj_at_def hd_map_simp upto_0_to_n2 upto_enum_def upto_enum_step_def)
   apply (frule_tac x = 1 in bspec,fastforce+)
  apply (wp get_master_pde_wp | simp | wpc)+
  done
qed

lemma create_mapping_entries_safe[wp]:
  "\<lbrace>\<exists>\<rhd>pd and K (vmsz_aligned vptr sz) and K (is_aligned pd pd_bits)
          and K (vptr < kernel_base)
          and valid_vspace_objs and pspace_aligned and
          (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits))\<rbrace>
      create_mapping_entries ptr vptr sz rights attrib pd
   \<lbrace>\<lambda>entries. case entries of (Inl (SmallPagePTE _ _ _, [_])) \<Rightarrow> \<top>
                  | (Inl (SmallPagePTE _ _ _, _)) \<Rightarrow> \<bottom>
                  | (Inl (LargePagePTE _ _ _, [])) \<Rightarrow> \<bottom>
                  | (Inr (SectionPDE _ _ _, [_])) \<Rightarrow> \<top>
                  | (Inr (SectionPDE _ _ _, _)) \<Rightarrow> \<bottom>
                  | (Inr (SuperSectionPDE _ _ _, [])) \<Rightarrow> \<bottom>
                  | _ \<Rightarrow> page_inv_entries_pre entries\<rbrace>,-"
  apply (cases sz, simp_all add: largePagePTE_offsets_def superSectionPDE_offsets_def)
     defer 2
     apply (wp | simp)+
   apply (simp split:list.split)
   apply (subgoal_tac "lookup_pd_slot pd vptr \<le> lookup_pd_slot pd vptr + 0x78")
    apply (clarsimp simp:upto_enum_def not_less upto_enum_step_def vspace_bits_defs
      page_inv_entries_pre_def Let_def)
    apply (clarsimp simp:upto_enum_step_def upto_enum_def
                     map_eq_Cons_conv upt_eq_Cons_conv)
    apply (drule_tac x = "lookup_pd_slot pd vptr" in spec)
    apply (subst (asm) upto_0_to_n2)
     apply simp
    apply clarsimp
    apply (drule lookup_pd_slot_aligned_6)
     apply (simp add: vspace_bits_defs)
    apply simp
   apply clarsimp
   apply (erule is_aligned_no_wrap'[OF lookup_pd_slot_aligned_6])
    apply (simp add: vspace_bits_defs)
   apply simp
  apply (wp get_pde_wp | simp add:lookup_pt_slot_def | wpc)+
  apply (clarsimp simp:upto_enum_def upto_enum_step_def
    page_inv_entries_pre_def Let_def )
  apply (drule_tac ref = refa in valid_vspace_objsD)
    apply (simp add:obj_at_def)
   apply simp
  apply (simp add: vspace_bits_defs)
  apply (drule_tac x = "ucast (lookup_pd_slot pd vptr && mask pd_bits >> 3)"
    in spec)
  apply (simp add: vspace_bits_defs)
  apply (clarsimp simp:not_less[symmetric] split:list.splits)
  apply (clarsimp simp:page_inv_entries_pre_def
    Let_def upto_enum_step_def upto_enum_def)
  apply (subst (asm) upto_0_to_n2)
   apply simp
  apply (clarsimp simp:not_less[symmetric])
  apply (subgoal_tac
    "(\<exists>xa xb. pda (ucast (lookup_pd_slot pd vptr && mask pd_bits >> 3))
     = pde.PageTablePDE x)
     \<longrightarrow> is_aligned (ptrFromPAddr x + ((vptr >> 12) && 0x1FF << 3)) 7")
   apply (clarsimp simp: vspace_bits_defs)
   apply (rule_tac x="ptrFromPAddr x + ((vptr >> 12) && 0x1FF << 3)" in exI)
   apply (subst map_upt_append[where x=15 and y=16]; simp add: mask_def del: upt_rec_numeral)
   apply (subst upt_rec_numeral)
   apply (simp add: mask_def del: upt_rec_numeral)
  apply clarsimp
  apply (rule aligned_add_aligned)
    apply (erule(1) pt_aligned)
   apply (rule is_aligned_shiftl[OF is_aligned_andI1])
   apply (rule is_aligned_shiftr)
   apply (simp add:vmsz_aligned_def)
  apply simp
  done

lemma decode_mmu_invocation_valid_pdpt[wp]:
  "\<lbrace>invs and valid_cap (cap.ArchObjectCap cap) and valid_pdpt_objs \<rbrace>
     decode_mmu_invocation label args cap_index slot cap excaps
   \<lbrace>invocation_duplicates_valid o Invocations_A.InvokeArchObject\<rbrace>, -"
  proof -
    have bitwise:"\<And>a. (ucast (((a::word32) && ~~ mask 7) && mask 14 >> 3)::11 word)
      = (ucast (a  && mask 14 >> 3)::11 word) && ~~ mask 4"
      apply (simp add:mask_def)
      apply word_bitwise
      done
    have sz:
      "\<And>vmpage_size. \<lbrakk>args ! 0 + 2 ^ pageBitsForSize vmpage_size - 1 < kernel_base;
        vmsz_aligned (args ! 0) vmpage_size\<rbrakk>
       \<Longrightarrow> args ! 0 < kernel_base"
      apply (rule le_less_trans[OF is_aligned_no_overflow])
       apply (simp add:vmsz_aligned_def)
      apply simp
      done
  show ?thesis
    supply if_split[split del]
    apply (simp add: decode_mmu_invocation_def)
    \<comment> \<open>Handle the easy cases first (trivial because of the post-condition invocation_duplicates_valid)\<close>
    apply (cases "invocation_type label \<notin> {ArchInvocationLabel ARMPageTableMap,
                                           ArchInvocationLabel ARMPageMap}")
     apply (wpsimp simp: invocation_duplicates_valid_def page_inv_duplicates_valid_def
                         pti_duplicates_valid_def Let_def
                   cong: if_cong)
    \<comment> \<open>Handle the two interesting cases now\<close>
    apply (clarsimp; erule disjE; cases cap;
           simp add: isPDFlushLabel_def isPageFlushLabel_def throwError_R')
       \<comment> \<open>PageTableMap\<close>
       apply (wpsimp simp: Let_def get_master_pde_def
                       wp: get_pde_wp hoare_drop_imps hoare_vcg_if_lift_ER)
       apply (fastforce simp: invocation_duplicates_valid_def pti_duplicates_valid_def
                              mask_lower_twice bitwise obj_at_def vspace_bits_defs if_apply_def2
                      split: if_splits)
      apply wp
     \<comment> \<open>PageMap\<close>
     apply (rename_tac dev pg_ptr rights sz pg_map)
     apply (wpsimp simp: Let_def invocation_duplicates_valid_def page_inv_duplicates_valid_def
                     wp: ensure_safe_mapping_ensures[THEN hoare_strengthen_postE_R]
                         check_vp_wpR hoare_vcg_if_lift_ER find_pd_for_asid_lookup_pd_wp)
     apply (fastforce simp: invs_psp_aligned page_directory_at_aligned_pd_bits word_not_le sz
                            valid_cap_def valid_arch_cap_def lookup_pd_slot_eq
                     split: if_splits)
    apply wp
    done
qed

lemma returnOk_lift :
  assumes P': "\<forall>s. P rv s"
  shows "\<lbrace>Q\<rbrace> (doE y \<leftarrow> f ; returnOk rv odE) \<lbrace>P\<rbrace>, -"
  by (wp,auto simp: returnOk_def return_def validE_R_def validE_def valid_def P')

lemma decode_vcpu_invocation_valid_pdpt[wp]:
  "\<lbrace>Q\<rbrace>
     decode_vcpu_invocation label args vcap excaps
   \<lbrace>invocation_duplicates_valid o Invocations_A.InvokeArchObject\<rbrace>, -"
  apply (simp add: decode_vcpu_invocation_def)
  apply (wpsimp simp: decode_vcpu_set_tcb_def
                      decode_vcpu_inject_irq_def decode_vcpu_read_register_def
                      decode_vcpu_write_register_def decode_vcpu_ack_vppi_def
                      if_apply_def2
    | simp add: invocation_duplicates_valid_def)+
  done

lemma arch_decode_invocation_valid_pdpt[wp]:
  notes find_pd_for_asid_inv[wp del]
  shows
  "\<lbrace>invs and valid_cap (cap.ArchObjectCap cap) and valid_pdpt_objs \<rbrace>
   arch_decode_invocation label args cap_index slot cap excaps
   \<lbrace>invocation_duplicates_valid o Invocations_A.InvokeArchObject\<rbrace>,-"
  proof -
  show ?thesis
    apply (simp add: arch_decode_invocation_def)
    apply (rule hoare_pre)
     apply (wp | wpc)+
    apply auto
    done
qed

lemma decode_invocation_valid_pdpt[wp]:
  "\<lbrace>invs and valid_cap cap and valid_pdpt_objs\<rbrace>
     decode_invocation label args cap_index slot cap excaps
   \<lbrace>invocation_duplicates_valid\<rbrace>,-"
  apply (simp add: decode_invocation_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc
            | simp only: invocation_duplicates_valid_def o_def uncurry_def split_def
                         Invocations_A.invocation.simps)+
  apply clarsimp
  done

crunch handle_fault, reply_from_kernel
  for valid_pdpt_objs[wp]: "valid_pdpt_objs"
  (simp: crunch_simps wp: crunch_wps)


lemma invocation_duplicates_valid_exst_update[simp]:
  "invocation_duplicates_valid i (trans_state f s) = invocation_duplicates_valid i s"
  apply (clarsimp simp add: invocation_duplicates_valid_def pti_duplicates_valid_def page_inv_duplicates_valid_def page_inv_entries_safe_def split: sum.splits invocation.splits arch_invocation.splits kernel_object.splits page_table_invocation.splits page_invocation.splits)+
  done


lemma set_thread_state_duplicates_valid[wp]:
  "\<lbrace>invocation_duplicates_valid i\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. invocation_duplicates_valid i\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: invocation_duplicates_valid_def pti_duplicates_valid_def
                        page_inv_duplicates_valid_def page_inv_entries_safe_def
                        Let_def
                 dest!: get_tcb_SomeD
                 split: Invocations_A.invocation.split arch_invocation.split_asm
                        page_table_invocation.split
                        page_invocation.split sum.split
                        )
  apply (auto simp add: obj_at_def page_inv_entries_safe_def)
  done

lemma handle_invocation_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and invs and ct_active\<rbrace>
        handle_invocation calling blocking \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  unfolding handle_invocation_def
  (* take long: *)
  by (wp syscall_valid set_thread_state_ct_st
               | simp add: split_def | wpc
               | wp (once) hoare_drop_imps)+
     (auto simp: ct_in_state_def elim: st_tcb_ex_cap)


crunch handle_event, activate_thread,switch_to_thread,
       switch_to_idle_thread
  for valid_pdpt[wp]: "valid_pdpt_objs"
  (simp: crunch_simps wp: crunch_wps OR_choice_weak_wp select_ext_weak_wp
      ignore: without_preemption getActiveIRQ resetTimer ackInterrupt
              getFAR getDFSR getIFSR OR_choice set_scheduler_action
              clearExMonitor)

lemma schedule_valid_pdpt[wp]: "\<lbrace>valid_pdpt_objs\<rbrace> schedule :: (unit,unit) s_monad \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (simp add: schedule_def allActiveTCBs_def)
  apply wpsimp
  done

lemma call_kernel_valid_pdpt[wp]:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and valid_pdpt_objs\<rbrace>
      (call_kernel e) :: (unit,unit) s_monad
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (cases e, simp_all add: call_kernel_def)
      apply (rule hoare_pre)
       apply (wp | simp | wpc
                 | rule conjI | clarsimp simp: ct_in_state_def
                 | erule pred_tcb_weakenE
                 | wp (once) hoare_drop_imps)+
  done

end

end
