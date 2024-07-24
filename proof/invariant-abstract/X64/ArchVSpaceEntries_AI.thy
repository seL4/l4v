(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVSpaceEntries_AI
imports VSpaceEntries_AI
begin

context Arch begin global_naming X64 (*FIXME: arch-split*)

lemma a_type_pml4D:
  "a_type ko = AArch APageMapL4 \<Longrightarrow> \<exists>pm. ko = ArchObj (PageMapL4 pm)"
  by (clarsimp)

primrec
  pde_range :: "pde \<Rightarrow> 9 word \<Rightarrow> 9 word set"
where
    "pde_range (InvalidPDE) p = {}"
  | "pde_range (LargePagePDE ptr x y) p = {p}"
  | "pde_range (PageTablePDE ptr x z) p = {p}"

primrec
  pdpte_range :: "pdpte \<Rightarrow> 9 word \<Rightarrow> 9 word set"
where
    "pdpte_range (InvalidPDPTE) p = {}"
  | "pdpte_range (HugePagePDPTE ptr x y) p = {p}"
  | "pdpte_range (PageDirectoryPDPTE ptr x z) p = {p}"

primrec
  pml4e_range :: "pml4e \<Rightarrow> 9 word \<Rightarrow> 9 word set"
where
    "pml4e_range (InvalidPML4E) p = {}"
  | "pml4e_range (PDPointerTablePML4E ptr x z) p = {p}"

primrec
  pte_range :: "pte \<Rightarrow> 9 word \<Rightarrow> 9 word set"
where
    "pte_range (InvalidPTE) p = {}"
  | "pte_range (SmallPagePTE ptr x y) p = {p}"

abbreviation "valid_pt_entries \<equiv> \<lambda>pt. valid_entries pte_range pt"
abbreviation "valid_pd_entries \<equiv> \<lambda>pd. valid_entries pde_range pd"

abbreviation "valid_pdpt_entries \<equiv> \<lambda>pdpt. valid_entries pdpte_range pdpt"

abbreviation "valid_pml4_entries \<equiv> \<lambda>pml4. valid_entries pml4e_range pml4"

definition
  obj_valid_vspace :: "kernel_object \<Rightarrow> bool"
where
 "obj_valid_vspace obj \<equiv> case obj of
    ArchObj (PageTable pt) \<Rightarrow> valid_pt_entries pt
  | ArchObj (PageDirectory pd) \<Rightarrow> valid_pd_entries pd
  | ArchObj (PDPointerTable pdpt) \<Rightarrow> valid_pdpt_entries pdpt
  | ArchObj (PageMapL4 pml4) \<Rightarrow> valid_pml4_entries pml4
  | _ \<Rightarrow> True"

lemmas obj_valid_vspace_simps[simp]
    = obj_valid_vspace_def
        [split_simps Structures_A.kernel_object.split
                     arch_kernel_obj.split]

abbreviation
  valid_vspace_objs' :: "'z state \<Rightarrow> bool"
where
 "valid_vspace_objs' s \<equiv> \<forall>x \<in> ran (kheap s). obj_valid_vspace x"

(* FIXME x64: initial state
lemma valid_vspace_init[iff]:
  "valid_vspace_objs' init_A_st"
proof -
  have P: "valid_pml4_entries (global_pm :: 9 word \<Rightarrow> _)"
    apply (clarsimp simp: valid_entries_def)
  also have Q: "entries_align range_sz (global_pm :: 9 word \<Rightarrow> _)"
    by (clarsimp simp: entries_align_def)
  thus ?thesis using P
    by (auto simp: init_A_st_def init_kheap_def
            elim!: ranE split: if_split_asm)
qed
*)

lemma set_object_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and K (obj_valid_vspace obj)\<rbrace>
      set_object ptr obj
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_def)
  apply (auto simp: fun_upd_def[symmetric] del: ballI elim: ball_ran_updI)
  done

crunch cap_insert, cap_swap_for_delete,empty_slot
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps simp: crunch_simps ignore:set_object)

(*
lemma shift_0x3C_set:
  "\<lbrakk> is_aligned p 6; 8 \<le> bits; bits < 32; len_of TYPE('a) = bits - 2 \<rbrakk> \<Longrightarrow>
   (\<lambda>x. ucast (x + p && mask bits >> 2) :: ('a :: len) word) ` set [0 :: word32 , 4 .e. 0x3C]
        = {x. x && ~~ mask 4 = ucast (p && mask bits >> 2)}"
  apply (clarsimp simp: upto_enum_step_def word_shift_by_2 image_image)
  apply (subst image_cong[where N="{x. x < 2 ^ 4}"])
    apply (safe, simp_all)[1]
     apply (drule plus_one_helper2, simp_all)[1]
    apply (drule word_le_minus_one_leq, simp_all)[1]
   apply (rule_tac f="\<lambda>x. ucast (x && mask bits >> 2)" in arg_cong)
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
   apply (drule_tac x="Suc (Suc n)" in spec)
   apply simp
  apply (rule_tac x="ucast x && mask 4" in image_eqI)
   apply (rule word_eqI)
   apply (drule_tac x=n in word_eqD)
   apply (simp add: word_ops_nth_size word_size nth_ucast nth_shiftr
                    nth_shiftl)
   apply (safe, simp_all)
  apply (rule order_less_le_trans, rule and_mask_less_size)
   apply (simp_all add: word_size)
  done
*)


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
  apply (simp add: store_pte_def set_pt_def set_object_def word_size_bits_def)
  apply (wp get_pt_wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp)
  apply (rule ext, clarsimp)
  done

lemma valid_pt_entries_invalid[simp]:
  "valid_pt_entries (\<lambda>x. InvalidPTE)"
   by (simp add:valid_entries_def)

lemma valid_pd_entries_invalid[simp]:
  "valid_pd_entries (\<lambda>x. InvalidPDE)"
  by (simp add:valid_entries_def)

lemma valid_pdpt_entries_invalid[simp]:
  "valid_pdpt_entries (\<lambda>x. InvalidPDPTE)"
  by (simp add:valid_entries_def)

lemma valid_pml4_entries_invalid[simp]:
  "valid_pml4_entries (\<lambda>x. InvalidPML4E)"
  by (simp add:valid_entries_def)

lemma valid_vspace_objs'_pml4D:
  "\<lbrakk>valid_vspace_objs' s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PageMapL4 pml4))\<rbrakk>
   \<Longrightarrow> valid_pml4_entries pml4"
  by (fastforce simp:ran_def)

lemma valid_vspace_objs'_pdptD:
  "\<lbrakk>valid_vspace_objs' s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PDPointerTable pdpt))\<rbrakk>
   \<Longrightarrow> valid_pdpt_entries pdpt"
  by (fastforce simp:ran_def)

lemma valid_vspace_objs'_pdD:
  "\<lbrakk>valid_vspace_objs' s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PageDirectory pd))\<rbrakk>
   \<Longrightarrow> valid_pd_entries pd"
  by (fastforce simp:ran_def)

lemma valid_vspace_objs'_ptD:
  "\<lbrakk>valid_vspace_objs' s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PageTable pt))\<rbrakk>
   \<Longrightarrow> valid_pt_entries pt"
  by (fastforce simp:ran_def)

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
  apply (simp add: store_pde_def set_pd_def set_object_def word_size_bits_def)
  apply (wp get_pd_wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp)
  apply (rule ext, clarsimp)
  done

lemma store_pde_valid_vspace_objs':
  "\<lbrace>valid_vspace_objs'\<rbrace>
       store_pde p pde \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: store_pde_def set_pd_def)
  apply (wpsimp wp: set_object_valid_vspace_objs')
  apply (clarsimp simp: obj_at_def)
  apply (rule valid_entries_overwrite_0)
   apply (fastforce simp:ran_def)
  apply (drule bspec)
   apply fastforce
  apply (case_tac "pd pa")
    apply simp_all
   apply (case_tac pde,simp_all)
  apply (case_tac pde,simp_all)
  done

lemma store_pte_valid_vspace_objs':
  "\<lbrace>valid_vspace_objs'\<rbrace>
       store_pte p pte \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wpsimp wp: set_object_valid_vspace_objs')
  apply (clarsimp simp: obj_at_def)
  apply (rule valid_entries_overwrite_0)
   apply (fastforce simp:ran_def)
  apply (drule bspec)
   apply fastforce
  apply (case_tac "pt pa")
   apply simp
  apply (case_tac pte,simp_all)
  done

lemma store_pdpte_valid_vspace_objs':
  "\<lbrace>valid_vspace_objs'\<rbrace>
       store_pdpte p pdpte \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: store_pdpte_def set_pdpt_def)
  apply (wpsimp wp: set_object_valid_vspace_objs')
  apply (clarsimp simp: obj_at_def)
  apply (rule valid_entries_overwrite_0)
   apply (fastforce simp:ran_def)
  apply (drule bspec)
   apply fastforce
  apply (case_tac "pd pa")
    apply simp
   apply (case_tac pdpte,simp_all)
  apply (case_tac pdpte,simp_all)
  done

lemma store_pml4e_valid_vspace_objs':
  "\<lbrace>valid_vspace_objs'\<rbrace>
       store_pml4e p pml4e \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: store_pml4e_def set_pml4_def)
  apply (wpsimp wp: set_object_valid_vspace_objs')
  apply (clarsimp simp: obj_at_def)
  apply (rule valid_entries_overwrite_0)
   apply (fastforce simp:ran_def)
  apply (drule bspec)
   apply fastforce
  apply (case_tac "pm pa")
   apply simp
  apply (case_tac pml4e,simp_all)
  done

lemma unmap_page_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> unmap_page sz asid vptr pptr \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: unmap_page_def mapM_discarded
             cong: vmpage_size.case_cong)
  apply (wp)
    prefer 2
    apply (rule valid_validE[OF find_vspace_for_asid_inv])
  apply (rule hoare_pre)
   apply (wp get_object_wp get_pte_wp get_pde_wp lookup_pt_slot_inv_any lookup_pd_slot_inv_any
             get_pdpte_wp lookup_pdpt_slot_inv_any
             store_pte_valid_vspace_objs' store_pde_valid_vspace_objs' store_pdpte_valid_vspace_objs'

                | simp add: mapM_x_map
                | wpc | simp add: check_mapping_pptr_def)+
  done

lemma flush_table_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> flush_table a b c d \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (wp mapM_x_wp' | wpc | simp add: flush_table_def | rule hoare_pre)+

crunch invalidate_page_structure_cache_asid
  for valid_vspace_objs'[wp]: valid_vspace_objs'

crunch get_cap
  for kheap[wp]: "\<lambda>s. P (kheap s)"
  (wp: crunch_wps simp: crunch_simps)

lemma flush_table_kheap[wp]:
  "\<lbrace>\<lambda>s. P (kheap s)\<rbrace> flush_table a b c d \<lbrace>\<lambda>rv s. P (kheap s)\<rbrace>"
  by (wp mapM_x_wp' | wpc | simp add: flush_table_def | rule hoare_pre)+

lemma unmap_page_table_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> unmap_page_table asid vptr pt \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (wp get_object_wp store_pde_valid_vspace_objs' get_pde_wp lookup_pd_slot_inv_any | wpc)+
  apply (simp add: obj_at_def)
  done

crunch set_simple_ko
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps)

crunch finalise_cap, cap_swap_for_delete, empty_slot
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps preemption_point_inv simp: crunch_simps unless_def ignore:set_object)

lemma preemption_point_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> preemption_point \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (wp preemption_point_inv | simp)+

lemmas cap_revoke_preservation_valid_vspace_objs = cap_revoke_preservation[OF _,
                                                          where E=valid_vspace_objs',
                                                          simplified, THEN validE_valid]

lemmas rec_del_preservation_valid_vspace_objs = rec_del_preservation[OF _ _ _ _,
                                                    where P=valid_vspace_objs', simplified]

crunch cap_delete, cap_revoke
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (rule: cap_revoke_preservation_valid_vspace_objs)

lemma mapM_x_copy_pml4e_updates:
  "\<lbrakk> \<forall>x \<in> set xs. f x && ~~ mask pml4_bits = 0; is_aligned p pml4_bits;
               is_aligned p' pml4_bits \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> page_map_l4_at p s \<longrightarrow> Q s) \<and> (\<not> page_map_l4_at p' s \<longrightarrow> Q s) \<and>
        (\<forall>pml4 pml4'. ko_at (ArchObj (PageMapL4 pml4)) p s
                \<and> ko_at (ArchObj (PageMapL4 pml4')) p' s
           \<longrightarrow> Q (s \<lparr> kheap := (kheap s) (p' := Some (ArchObj (PageMapL4 (\<lambda>y. if y \<in> (\<lambda>x.
         ucast (f x && mask pml4_bits >> 3)) ` set xs then pml4 y else pml4' y)))) \<rparr>))\<rbrace>
     mapM_x (\<lambda>x. get_pml4e (p + f x) >>= store_pml4e (p' + f x)) xs
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
   apply wp
   apply (clarsimp simp: obj_at_def fun_upd_idem dest!: a_type_pml4D)
  apply (simp add: mapM_x_Cons)
  apply wp
   apply (thin_tac "valid P f Q" for P f Q)
   apply (simp add: store_pml4e_def set_pml4_def set_object_def
              cong: bind_cong split del: if_split)
   apply (wp get_object_wp get_pml4e_wp)
  apply (clarsimp simp: obj_at_def a_type_simps mask_out_add_aligned[symmetric] word_size_bits_def
             split del: if_split)
  apply (simp add: a_type_simps, safe)
   apply (erule rsubst[where P=Q])
   apply (rule abstract_state.fold_congs[OF refl refl])
   apply (rule ext, clarsimp)
   apply (rule ext, simp)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp)
  apply (rule ext, simp add: mask_add_aligned)
  done

lemma copy_global_mappings_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and valid_arch_state and pspace_aligned
            and K (is_aligned p pml4_bits)\<rbrace>
       copy_global_mappings p \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_global_mappings_def)
  apply wp
   apply (rule_tac P="is_aligned global_pm pml4_bits" in hoare_gen_asm)
   apply (rule mapM_x_copy_pml4e_updates; simp)
   apply (clarsimp simp: mask_eq_x_eq_0[symmetric])
   apply (rule less_mask_eq, rule shiftl_less_t2n,
          simp_all add: bit_simps)[1]
   apply (drule plus_one_helper2, simp+)
  apply wp
  apply (clarsimp simp: invs_aligned_pml4D ranI
                 elim!: ranE split: if_split_asm)
  apply (rule_tac S="{x. ucast x \<ge> (get_pml4_index pptr_base)}"
                 in valid_entries_partial_copy)
     apply (fastforce simp: obj_at_def ran_def)
    apply (fastforce simp: obj_at_def ran_def)
   apply (clarsimp simp:image_def)
   apply (subst (asm) less_mask_eq)
    apply (rule shiftl_less_t2n)
     apply (simp add:pd_bits_def pageBits_def word_le_make_less bit_simps)
    apply (simp add:pd_bits_def pageBits_def bit_simps)
   apply (subst (asm) shiftl_shiftr1)
    apply (simp add: word_size_bits_def)
   apply (simp add:word_size)
   apply (subst (asm) less_mask_eq)
    apply (simp add:pd_bits_def pageBits_def le_less_trans bit_simps)
   apply (case_tac v)
    apply ((simp add:ucast_ucast_len pd_bits_def pageBits_def le_less_trans bit_simps)+)[2]
  apply (clarsimp simp:image_def)
  apply (rule disjointI)
  apply clarsimp
  apply (drule_tac x = "ucast x" in spec)
  apply (erule impE)
   apply (simp add: bit_simps)
   apply word_bitwise
  apply (subgoal_tac "get_pml4_index pptr_base \<le> ucast x")
   apply simp
   apply (subst (asm) less_mask_eq)
    apply (rule shiftl_less_t2n)
     apply (simp add: word_le_make_less bit_simps)
     apply word_bitwise
    apply (simp add: bit_simps)
   apply (subst (asm) shiftl_shiftr1)
    apply (simp add: word_size_bits_def)
   apply (simp add:word_size)
   apply (subst (asm) less_mask_eq)
    apply (rule less_le_trans[OF ucast_less])
     apply simp
    apply (simp add: word_size_bits_def)
   apply (simp add: word_size_bits_def get_pml4_index_def bit_simps)
   apply word_bitwise
  apply (case_tac v;simp)
  done

lemma in_pte_rangeD:
  "x \<in> pte_range v y \<Longrightarrow> x = y"
  by (case_tac v,simp_all split:if_splits)

lemma in_pde_rangeD:
  "x \<in> pde_range v y \<Longrightarrow> x = y"
  by (case_tac v,simp_all split:if_splits)

lemma in_pdpte_rangeD:
  "x \<in> pdpte_range v y \<Longrightarrow> x = y"
  by (case_tac v,simp_all split:if_splits)

lemma in_pml4e_rangeD:
  "x \<in> pml4e_range v y \<Longrightarrow> x = y"
  by (case_tac v,simp_all split:if_splits)


lemma non_invalid_in_pde_range:
  "pde \<noteq> InvalidPDE
  \<Longrightarrow> x \<in> pde_range pde x"
  by (case_tac pde,simp_all)

lemma non_invalid_in_pte_range:
  "pte \<noteq> InvalidPTE
  \<Longrightarrow> x \<in> pte_range pte x"
  by (case_tac pte,simp_all)

lemma non_invalid_in_pml4e_range:
  "pml4e \<noteq> InvalidPML4E
  \<Longrightarrow> x \<in> pml4e_range pml4e x"
  by (case_tac pml4e,simp_all)

lemma non_invalid_in_pdpte_range:
  "pdpte \<noteq> InvalidPDPTE
  \<Longrightarrow> x \<in> pdpte_range pdpte x"
  by (case_tac pdpte,simp_all)

crunch cancel_badged_sends
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps filterM_mapM wp: crunch_wps ignore: filterM)

crunch cap_move, cap_insert
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"

lemma invoke_cnode_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and valid_cnode_inv i\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp | wpc | simp split del: if_split)+
  done

crunch invoke_tcb
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: check_cap_inv crunch_wps simp: crunch_simps
       ignore: check_cap_at)

lemma invoke_domain_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> invoke_domain t d \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (simp add: invoke_domain_def | wp)+

crunch set_extra_badge, transfer_caps_loop
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (rule: transfer_caps_loop_pres)

crunch send_ipc, send_signal,
    do_reply_transfer, invoke_irq_control, invoke_irq_handler
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: crunch_wps simp: crunch_simps
         ignore: clearMemory const_on_failure set_object)

lemma valid_vspace_objs'_trans_state[simp]: "valid_vspace_objs' (trans_state f s) = valid_vspace_objs' s"
  apply (simp add: obj_valid_vspace_def)
  done

lemma retype_region_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> retype_region ptr bits o_bits type dev \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: retype_region_def split del: if_split)
  apply (wp | simp only: valid_vspace_objs'_trans_state trans_state_update[symmetric])+
  apply (clarsimp simp: retype_addrs_fold foldr_upd_app_if ranI
                 elim!: ranE split: if_split_asm simp del:fun_upd_apply)
  apply (simp add: default_object_def default_arch_object_def
            split: Structures_A.kernel_object.splits
    Structures_A.apiobject_type.split aobject_type.split)+
  done

lemma detype_valid_vspace[elim!]:
  "valid_vspace_objs' s \<Longrightarrow> valid_vspace_objs' (detype S s)"
  by (auto simp add: detype_def ran_def)

crunch create_cap
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (ignore: clearMemory simp: crunch_simps)

lemma init_arch_objects_valid_vspace:
  "\<lbrace>valid_vspace_objs' and pspace_aligned and valid_arch_state
           and K (orefs = retype_addrs ptr type n us)
           and K (range_cover ptr sz (obj_bits_api type us) n)\<rbrace>
     init_arch_objects type ptr n obj_sz orefs
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: init_arch_objects_def)
  apply (rule hoare_pre)
   apply (wp | wpc)+
     apply (rule_tac Q'="\<lambda>rv. valid_vspace_objs' and pspace_aligned and valid_arch_state"
                  in hoare_post_imp, simp)
     apply (rule mapM_x_wp')
     apply (rule hoare_pre, wp copy_global_mappings_valid_vspace_objs')
     apply clarsimp
     apply (drule retype_addrs_aligned[where sz = sz])
        apply (simp add:range_cover_def)
       apply (drule range_cover.sz,simp add:word_bits_def)
      apply (simp add:range_cover_def)
     apply (clarsimp simp:obj_bits_api_def bit_simps
       arch_kobj_size_def default_arch_object_def range_cover_def)+
  done

lemma delete_objects_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs'\<rbrace> delete_objects ptr bits \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  by (rule delete_objects_reduct) (wp detype_valid_vspace)

crunch reset_untyped_cap
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (wp: mapME_x_inv_wp crunch_wps simp: crunch_simps unless_def)

lemma invoke_untyped_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active
          and valid_untyped_inv ui\<rbrace>
       invoke_untyped ui
   \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q)
      apply (wp init_arch_objects_valid_vspace | simp)+
     apply (auto simp: post_retype_invs_def split: if_split_asm)[1]
    apply (wp | simp)+
  done

crunch perform_asid_pool_invocation,
     perform_asid_control_invocation
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (ignore: delete_objects set_object
       wp: hoare_weak_lift_imp crunch_wps
     simp: crunch_simps unless_def)

lemma pte_range_interD:
 "pte_range pte p \<inter> pte_range pte' p' \<noteq> {}
  \<Longrightarrow> pte \<noteq> InvalidPTE \<and> pte' \<noteq> InvalidPTE
      \<and> p = p'"
  apply (drule int_not_emptyD)
  apply (case_tac pte,simp_all split:if_splits)
   apply (case_tac pte',simp_all split:if_splits)
  done

lemma pde_range_interD:
 "pde_range pde p \<inter> pde_range pde' p' \<noteq> {}
  \<Longrightarrow> pde \<noteq> InvalidPDE \<and> pde' \<noteq> InvalidPDE
      \<and> p = p'"
  apply (drule int_not_emptyD)
  apply (case_tac pde,simp_all split:if_splits)
     apply (case_tac pde',simp_all split:if_splits)
    apply (case_tac pde',simp_all split:if_splits)
  done

lemma pdpte_range_interD:
 "pdpte_range pdpte p \<inter> pdpte_range pdpte' p' \<noteq> {}
  \<Longrightarrow> pdpte \<noteq> InvalidPDPTE \<and> pdpte' \<noteq> InvalidPDPTE
      \<and> p = p'"
  apply (drule int_not_emptyD)
  apply (case_tac pdpte,simp_all split:if_splits)
     apply (case_tac pdpte',simp_all split:if_splits)
    apply (case_tac pdpte',simp_all split:if_splits)
  done

lemma pml4e_range_interD:
 "pml4e_range pml4e p \<inter> pml4e_range pml4e' p' \<noteq> {}
  \<Longrightarrow> pml4e \<noteq> InvalidPML4E \<and> pml4e' \<noteq> InvalidPML4E
      \<and> p = p'"
  apply (drule int_not_emptyD)
  apply (case_tac pml4e,simp_all split:if_splits)
     apply (case_tac pml4e',simp_all split:if_splits)
  done

lemma mask_pd_bits_shift_ucast_align[simp]:
  "is_aligned (ucast (p && mask pml4_bits >> word_size_bits)::9 word) 4 =
   is_aligned ((p::machine_word) >> word_size_bits) 4"
  by (clarsimp simp: is_aligned_mask mask_def bit_simps) word_bitwise


crunch pte_check_if_mapped, pde_check_if_mapped
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"

lemma perform_page_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and valid_page_inv pinv\<rbrace>
        perform_page_invocation pinv \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: perform_page_invocation_def )
  apply (cases pinv,
         simp_all add: mapM_discarded
            split: sum.split arch_cap.split option.split,
         safe intro!: hoare_gen_asm hoare_gen_asm[unfolded K_def],
         simp_all add: mapM_x_Nil mapM_x_Cons mapM_x_map)
            apply (wp store_pte_valid_vspace_objs' store_pde_valid_vspace_objs'
                      store_pdpte_valid_vspace_objs'
                      hoare_vcg_imp_lift[OF set_cap_arch_obj_neg] hoare_vcg_all_lift
                 | clarsimp simp: cte_wp_at_weakenE[OF _ TrueI] obj_at_def
                                  swp_def valid_page_inv_def perform_page_invocation_unmap_def
                                  valid_slots_def pte_check_if_mapped_def
                                  pde_check_if_mapped_def
                           split: pte.splits pde.splits
                 | wpc
                 | wp (once) hoare_drop_imps)+
  done

lemma perform_page_table_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and valid_pti pinv\<rbrace>
      perform_page_table_invocation pinv \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: perform_page_table_invocation_def split_def
             cong: page_table_invocation.case_cong
                   option.case_cong cap.case_cong arch_cap.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift store_pde_valid_vspace_objs' store_pte_valid_vspace_objs'
             set_cap_arch_obj hoare_vcg_all_lift mapM_x_wp'
              | wpc
              | simp add: swp_def
              | strengthen all_imp_ko_at_from_ex_strg
              | wp (once) hoare_drop_imps)+
  done

lemma perform_page_directory_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and valid_pdi pinv\<rbrace>
      perform_page_directory_invocation pinv \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: perform_page_directory_invocation_def split_def
             cong: page_directory_invocation.case_cong
                   option.case_cong cap.case_cong arch_cap.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift store_pde_valid_vspace_objs' store_pte_valid_vspace_objs'
             store_pdpte_valid_vspace_objs'
             set_cap_arch_obj hoare_vcg_all_lift mapM_x_wp'
              | wpc
              | simp add: swp_def
              | strengthen all_imp_ko_at_from_ex_strg
              | wp (once) hoare_drop_imps)+
  done

lemma perform_pdpt_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and valid_pdpti pinv\<rbrace>
      perform_pdpt_invocation pinv \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: perform_pdpt_invocation_def split_def
             cong: pdpt_invocation.case_cong
                   option.case_cong cap.case_cong arch_cap.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift store_pde_valid_vspace_objs' store_pte_valid_vspace_objs'
             store_pdpte_valid_vspace_objs' store_pml4e_valid_vspace_objs'
             set_cap_arch_obj hoare_vcg_all_lift mapM_x_wp'
              | wpc
              | simp add: swp_def
              | strengthen all_imp_ko_at_from_ex_strg
              | wp (once) hoare_drop_imps)+
  done

crunch perform_io_port_invocation, perform_ioport_control_invocation
  for valid_vspace_objs'[wp]: valid_vspace_objs'

lemma perform_invocation_valid_vspace_objs'[wp]:
  "\<lbrace>invs and ct_active and valid_invocation i and valid_vspace_objs'\<rbrace>
      perform_invocation blocking call i
         \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (cases i, simp_all)
  apply (wp send_signal_interrupt_states | simp)+
  apply (simp add: arch_perform_invocation_def)
  apply (wp | wpc | simp)+
  apply (auto simp: valid_arch_inv_def )
  done

crunch handle_fault, reply_from_kernel
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps wp: crunch_wps)

lemma handle_invocation_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active\<rbrace>
        handle_invocation calling blocking \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid set_thread_state_ct_st
               | simp add: split_def | wpc
               | wp (once) hoare_drop_imps)+
  apply (auto simp: ct_in_state_def elim: st_tcb_ex_cap)
  done


crunch activate_thread,switch_to_thread, handle_hypervisor_fault,
       switch_to_idle_thread, handle_call, handle_recv, handle_reply,
       handle_send, handle_yield, handle_interrupt
  for valid_vspace_objs'[wp]: "valid_vspace_objs'"
  (simp: crunch_simps wp: crunch_wps OR_choice_weak_wp select_ext_weak_wp
      ignore: without_preemption getActiveIRQ resetTimer ackInterrupt
              getFaultAddress OR_choice set_scheduler_action)

lemma handle_event_valid_vspace_objs'[wp]:
  "\<lbrace>valid_vspace_objs' and invs and ct_active\<rbrace> handle_event e \<lbrace>\<lambda>rv. valid_vspace_objs'\<rbrace>"
  apply (case_tac e; simp)
   by (wp | wpc | simp add: handle_vm_fault_def | wp (once) hoare_drop_imps)+

lemma schedule_valid_vspace_objs'[wp]: "\<lbrace>valid_vspace_objs'\<rbrace> schedule :: (unit,unit) s_monad \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  apply (simp add: schedule_def allActiveTCBs_def)
  apply wpsimp
  done

lemma call_kernel_valid_vspace_objs'[wp]:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and valid_vspace_objs'\<rbrace>
      (call_kernel e) :: (unit,unit) s_monad
   \<lbrace>\<lambda>_. valid_vspace_objs'\<rbrace>"
  apply (cases e, simp_all add: call_kernel_def)
      apply (rule hoare_pre)
       apply (wp | simp add: handle_vm_fault_def | wpc
                 | rule conjI | clarsimp simp: ct_in_state_def
                 | erule pred_tcb_weakenE
                 | wp (once) hoare_drop_imps)+
  done

end

end
