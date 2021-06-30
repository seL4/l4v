(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory PageTableDuplicates
imports Syscall_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma set_ep_valid_duplicate' [wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setEndpoint ep v  \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:setEndpoint_def)
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = v,simplified])
  apply (clarsimp simp: updateObject_default_def assert_def bind_def when_def
                        alignError_def magnitudeCheck_def read_magnitudeCheck_def
                        assert_opt_def return_def fail_def
                 split: if_splits option.splits)
   apply (rule_tac ko = ba in valid_duplicates'_non_pd_pt_I)
       apply simp+
  apply (rule_tac ko = ba in valid_duplicates'_non_pd_pt_I)
      apply simp+
  done

lemma set_ntfn_valid_duplicate' [wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setNotification ep v  \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:setNotification_def)
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = v,simplified])
  apply (clarsimp simp: updateObject_default_def assert_def bind_def when_def
                        alignError_def magnitudeCheck_def read_magnitudeCheck_def
                        assert_opt_def return_def fail_def
                 split: if_splits option.splits)
   apply (rule_tac ko = ba in valid_duplicates'_non_pd_pt_I)
       apply simp+
  apply (rule_tac ko = ba in valid_duplicates'_non_pd_pt_I)
      apply simp+
  done

lemma setCTE_valid_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setCTE p cte \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:setCTE_def)
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = cte,simplified])
  apply (clarsimp simp:ObjectInstances_H.updateObject_cte assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def typeError_def
    split:if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

crunches cteInsert
  for valid_duplicates'[wp]: "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (wp: crunch_wps simp: crunch_simps)

lemma doMachineOp_ksPSpace_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksPSpace s)\<rbrace> doMachineOp f \<lbrace>\<lambda>ya s. P (ksPSpace s)\<rbrace>"
  by (simp add:doMachineOp_def split_def | wp)+

crunches threadSet, setBoundNotification, setExtraBadge
  for valid_duplicates'[wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: updateObject_default_inv)

lemma transferCapsToSlots_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  transferCapsToSlots ep buffer n caps slots mi
  \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by (rule transferCapsToSlots_pres1; wp)

lemma setObjectSC_valid_duplicates'[wp]:
  "setObject a (sc::sched_context) \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = sc,simplified])
  apply (clarsimp simp: updateObject_default_def assert_def bind_def
                        alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
                        assert_opt_def return_def fail_def typeError_def
                  split: if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

lemma setObjectReply_valid_duplicates'[wp]:
  "setObject a (r::reply) \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = r,simplified])
  apply (clarsimp simp: updateObject_default_def assert_def bind_def
                        alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
                        assert_opt_def return_def fail_def typeError_def
                  split: if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

crunches transferCaps, sendFaultIPC, handleFault, replyFromKernel, insertNewCap
  for valid_duplicates'[wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (ignore: transferCapsToSlots
       wp: crunch_wps hoare_vcg_const_Ball_lift hoare_vcg_all_lift get_rs_cte_at' whileM_inv
     simp: zipWithM_x_mapM ball_conj_distrib crunch_simps)

lemma koTypeOf_pte:
  "koTypeOf ko = ArchT PTET \<Longrightarrow> \<exists>pte. ko = KOArch (KOPTE pte)"
  "archTypeOf ako = PTET \<Longrightarrow> \<exists>pte. ako = KOPTE pte"
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object; simp)
  apply (case_tac ako; simp)
  done

lemma mapM_x_storePTE_updates:
  "\<lbrace>\<lambda>s. (\<forall>x\<in> set xs. pte_at' x s)
     \<and> Q (\<lambda>x. if (x \<in> set xs) then Some (KOArch (KOPTE pte)) else (ksPSpace s) x) \<rbrace>
     mapM_x (swp storePTE pte) xs
   \<lbrace>\<lambda>r s. Q (ksPSpace s)\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
  apply (simp add: mapM_x_Cons)
  apply (rule hoare_seq_ext, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: storePTE_def setObject_def)
  apply (wp | simp add:split_def updateObject_default_def)+
  apply clarsimp
  apply (intro conjI ballI)
   apply (drule(1) bspec)
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def objBits_defs
                   dest!: koTypeOf_pte
                   split:  kernel_object.split_asm)
   apply (simp add:ps_clear_def dom_fun_upd2[unfolded fun_upd_def])
   apply (simp add: lookupAround2_known1)
  apply (erule rsubst[where P=Q])
  apply (rule ext, clarsimp)
  done

lemma is_aligned_plus_bound:
  assumes al: "is_aligned p sz"
  assumes cmp: "sz \<le> lz"
  assumes b:  "b \<le> (2::word32) ^ sz - 1"
  assumes bound : "p < 2 ^ lz"
  assumes sz: "sz < word_bits"
  shows "p + b < 2 ^ lz"
  proof -
    have lower:"p + b \<le> p + (2 ^ sz - 1)"
      apply (rule word_plus_mono_right[OF b])
      apply (rule is_aligned_no_overflow'[OF al])
      done
    show ?thesis using bound sz
      apply -
      apply (rule le_less_trans[OF lower])
      apply (rule ccontr)
      apply (simp add:not_less)
      apply (drule neg_mask_mono_le[where n = sz])
      apply (subst (asm) is_aligned_neg_mask_eq)
       apply (rule is_aligned_weaken[OF is_aligned_triv cmp])
      apply (subst (asm) is_aligned_add_helper[THEN conjunct2,OF al])
       apply (simp add:word_bits_def)
      apply simp
    done
  qed

lemma page_table_at_set_list:
  "\<lbrakk>page_table_at' ptr s;pspace_aligned' s;sz \<le> ptBits;
   p && ~~ mask ptBits = ptr; is_aligned p sz; 2 \<le> sz\<rbrakk> \<Longrightarrow>
  set [p , p + 4 .e. p + mask sz] =
  {x. pte_at' x s \<and> x && ~~ mask sz = p}"
  apply (clarsimp simp:page_table_at'_def ptBits_def pteBits_def)
  apply (rule set_eqI)
  apply (rule iffI)
   apply (subst (asm) upto_enum_step_subtract)
    apply (simp add:field_simps mask_def)
    apply (erule is_aligned_no_overflow)
   apply (clarsimp simp:set_upto_enum_step_4
           image_def pageBits_def)
   apply (drule_tac x= "((p && mask 10) >> 2) + xb" in spec)
   apply (erule impE)
    apply (rule is_aligned_plus_bound[where lz = 8 and sz = "sz - 2" ,simplified])
        apply (rule is_aligned_shiftr)
        apply (rule is_aligned_andI1)
        apply (subgoal_tac "sz - 2 + 2 = sz")
         apply simp
        apply simp
       apply (simp add:field_simps)
      apply (simp add:shiftr_mask2)
      apply (simp add:mask_def not_less word_bits_def)
     apply (rule shiftr_less_t2n[where m = 8,simplified])
     apply (rule le_less_trans[OF _ mask_lt_2pn])
      apply (simp add:word_and_le1)
     apply simp
    apply (simp add:word_bits_def)
   apply (simp add:word_shiftl_add_distrib)
   apply (subst (asm) shiftr_shiftl1)
    apply simp+
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 2])
    apply (rule is_aligned_weaken)
     apply (erule is_aligned_andI1)
    apply simp
   apply (simp add:mask_out_sub_mask field_simps)
   apply (clarsimp simp:typ_at'_def mask_add_aligned
     ko_wp_at'_def dom_def)
   apply (rule less_mask_eq[symmetric])
   apply (subst (asm) shiftr_mask2)
    apply simp
   apply (simp add:shiftl_less_t2n word_shiftl_add_distrib
     word_bits_def mask_def shiftr_mask2)
  apply (clarsimp simp:objBits_simps pageBits_def archObjSize_def
     split:Structures_H.kernel_object.splits arch_kernel_object.splits)
  apply (subst upto_enum_step_subtract)
   apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask])
    apply (rule le_refl)
   apply (simp add:mask_lt_2pn word_bits_def)
  apply (simp add:image_def)
  apply (rule_tac x = "x && mask sz" in bexI)
   apply (simp add:mask_out_sub_mask)
  apply (simp add:set_upto_enum_step_4 image_def)
  apply (rule_tac x = "x && mask sz >> 2" in bexI)
   apply (subst shiftr_shiftl1)
    apply simp
   apply simp
   apply (subst is_aligned_neg_mask_eq)
    apply (rule is_aligned_andI1)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def
      dest!: koTypeOf_pte)
    apply (drule pspace_alignedD')
     apply simp
    apply (simp add:objBits_simps archObjSize_def pteBits_def)
   apply simp
  apply clarsimp
  apply (rule le_shiftr)
  apply (simp add:word_and_le1)
  done

lemma page_directory_at_set_list:
  "\<lbrakk>page_directory_at' ptr s;pspace_aligned' s;sz \<le> pdBits;
   p && ~~ mask pdBits = ptr; is_aligned p sz; 2 \<le> sz\<rbrakk> \<Longrightarrow>
  set [p , p + 4 .e. p + mask sz] =
  {x. pde_at' x s \<and> x && ~~ mask sz = p}"
  apply (clarsimp simp:page_directory_at'_def pdBits_def pdeBits_def)
  apply (rule set_eqI)
  apply (rule iffI)
   apply (subst (asm) upto_enum_step_subtract)
    apply (simp add:field_simps mask_def)
    apply (erule is_aligned_no_overflow)
   apply (clarsimp simp:set_upto_enum_step_4
           image_def pageBits_def)
   apply (drule_tac x= "((p && mask 14) >> 2) + xb" in spec)
   apply (erule impE)
    apply (rule is_aligned_plus_bound[where lz = 12 and sz = "sz - 2" ,simplified])
        apply (rule is_aligned_shiftr)
        apply (rule is_aligned_andI1)
        apply (subgoal_tac "sz - 2 + 2 = sz")
         apply simp
        apply simp
       apply (simp add:field_simps)
      apply (simp add:shiftr_mask2)
      apply (simp add:mask_def not_less word_bits_def)
     apply (rule shiftr_less_t2n[where m = 12,simplified])
     apply (rule le_less_trans[OF _ mask_lt_2pn])
      apply (simp add:word_and_le1)
     apply simp
    apply (simp add:word_bits_def)
   apply (simp add:word_shiftl_add_distrib)
   apply (subst (asm) shiftr_shiftl1)
    apply simp+
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 2])
    apply (rule is_aligned_weaken)
     apply (erule is_aligned_andI1)
    apply simp
   apply (simp add:mask_out_sub_mask field_simps)
   apply (clarsimp simp:typ_at'_def mask_add_aligned
     ko_wp_at'_def dom_def)
   apply (rule less_mask_eq[symmetric])
   apply (subst (asm) shiftr_mask2)
    apply simp
   apply (simp add:shiftl_less_t2n word_shiftl_add_distrib
     word_bits_def mask_def shiftr_mask2)
  apply (clarsimp simp:objBits_simps pageBits_def archObjSize_def
     split:Structures_H.kernel_object.splits arch_kernel_object.splits)
  apply (subst upto_enum_step_subtract)
   apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask])
    apply (rule le_refl)
   apply (simp add:mask_lt_2pn word_bits_def)
  apply (simp add:image_def)
  apply (rule_tac x = "x && mask sz" in bexI)
   apply (simp add:mask_out_sub_mask)
  apply (simp add:set_upto_enum_step_4 image_def)
  apply (rule_tac x = "x && mask sz >> 2" in bexI)
   apply (subst shiftr_shiftl1)
    apply simp
   apply simp
   apply (subst is_aligned_neg_mask_eq)
    apply (rule is_aligned_andI1)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def
      dest!: koTypeOf_pde)
    apply (drule pspace_alignedD')
     apply simp
    apply (simp add:objBits_simps archObjSize_def pdeBits_def)
   apply simp
  apply clarsimp
  apply (rule le_shiftr)
  apply (simp add:word_and_le1)
  done

lemma page_table_at_pte_atD':
  "\<lbrakk>page_table_at' p s;is_aligned p' 2; p' && ~~ mask ptBits = p\<rbrakk> \<Longrightarrow> pte_at' p' s"
  apply (clarsimp simp:page_table_at'_def)
  apply (drule_tac x = "p' && mask ptBits >> 2" in spec)
  apply (erule impE)
   apply (rule shiftr_less_t2n[where m = 8,simplified])
   apply (rule le_less_trans[OF word_and_le1])
   apply (simp add:ptBits_def mask_def pageBits_def pteBits_def)
  apply (subst (asm) shiftr_shiftl1)
   apply simp
  apply simp
  apply (subst (asm) is_aligned_neg_mask_eq[where n = 2])
   apply (simp add: is_aligned_andI1)
  apply (simp add:mask_out_sub_mask)
  done

lemma mapM_x_storePTE_update_helper:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)
    \<and> pspace_aligned' s
    \<and> page_table_at' ptr s
    \<and> word && ~~ mask ptBits = ptr
    \<and> sz \<le> ptBits \<and> 6 \<le> sz
    \<and> is_aligned word sz
    \<and> xs = [word , word + 4 .e. word + (mask sz)]
  \<rbrace>
  mapM_x (swp storePTE pte) xs
  \<lbrace>\<lambda>y s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (wp mapM_x_storePTE_updates)
  apply clarsimp
  apply (frule(2) page_table_at_set_list)
     apply simp+
  apply (subst vs_valid_duplicates'_def)
  apply clarsimp
  apply (intro conjI impI)
   apply clarsimp
   apply (thin_tac "x = y" for x y)
   apply (simp add:mask_lower_twice)
   apply (subgoal_tac "x && ~~ mask sz = y && ~~ mask sz")
    apply (drule(1) page_table_at_pte_atD')
     apply (drule mask_out_first_mask_some[where m = ptBits])
      apply (simp add:vs_ptr_align_def split:ARM_H.pte.splits)
     apply (simp add:mask_lower_twice vs_ptr_align_def
      split:ARM_H.pte.splits)
    apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
   apply (clarsimp simp:vs_ptr_align_def
      split:arch_kernel_obj.splits Structures_H.kernel_object.splits
      split:ARM_H.pte.splits)
   apply (drule mask_out_first_mask_some[where m = sz])
    apply simp
   apply (simp add:mask_lower_twice)
  apply clarsimp
  apply (intro conjI impI)
   apply (thin_tac "x = y" for x y)
   apply (clarsimp split:option.splits)
   apply (subgoal_tac "x && ~~ mask sz = y && ~~ mask sz")
    apply (drule_tac p' = x in page_table_at_pte_atD')
      apply (drule pspace_alignedD')
       apply simp
      apply (simp add:objBits_simps' archObjSize_def pteBits_def
        is_aligned_weaken[where y = 2] pageBits_def pdeBits_def vs_ptr_align_def
        split:kernel_object.splits arch_kernel_object.splits)
     apply (simp add:mask_lower_twice)
     apply (drule mask_out_first_mask_some[where m = ptBits])
      apply (simp add:vs_ptr_align_def
        split:kernel_object.splits arch_kernel_object.splits
        ARM_H.pte.splits ARM_H.pde.splits)
     apply (subst (asm) mask_lower_twice)
      apply (simp add:vs_ptr_align_def
        split:kernel_object.splits arch_kernel_object.splits
        ARM_H.pte.splits ARM_H.pde.splits)
     apply simp
    apply (simp add:vs_ptr_align_def
      split:kernel_object.splits arch_kernel_object.splits
      ARM_H.pte.splits)
   apply (simp add:mask_lower_twice)
   apply (drule mask_out_first_mask_some[where m = sz])
    apply (simp add:vs_ptr_align_def
      split:kernel_object.splits arch_kernel_object.splits
      ARM_H.pte.splits ARM_H.pde.splits)
   apply (subst (asm) mask_lower_twice)
    apply (simp add:vs_ptr_align_def
      split:kernel_object.splits arch_kernel_object.splits
      ARM_H.pte.splits ARM_H.pde.splits)
   apply simp
  apply (clarsimp split:option.splits)
  apply (drule_tac p' = y in valid_duplicates'_D)
     apply simp+
  done

lemma page_directory_at_pde_atD':
  "\<lbrakk>page_directory_at' p s;is_aligned p' 2; p' && ~~ mask pdBits = p\<rbrakk> \<Longrightarrow> pde_at' p' s"
  apply (clarsimp simp:page_directory_at'_def)
  apply (drule_tac x = "p' && mask pdBits >> 2" in spec)
  apply (erule impE)
   apply (rule shiftr_less_t2n[where m = 12,simplified])
   apply (rule le_less_trans[OF word_and_le1])
   apply (simp add:pdBits_def mask_def pageBits_def pdeBits_def)
  apply (subst (asm) shiftr_shiftl1)
   apply simp
  apply simp
  apply (subst (asm) is_aligned_neg_mask_eq[where n = 2])
   apply (simp add: is_aligned_andI1)
  apply (simp add:mask_out_sub_mask)
  done

lemma mapM_x_storePDE_updates:
  "\<lbrace>\<lambda>s. (\<forall>x\<in> set xs. pde_at' x s)
     \<and> Q (\<lambda>x. if (x \<in> set xs) then Some (KOArch (KOPDE pte)) else (ksPSpace s) x) \<rbrace>
     mapM_x (swp storePDE pte) xs
   \<lbrace>\<lambda>r s. Q (ksPSpace s)\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
  apply (simp add: mapM_x_Cons)
  apply (rule hoare_seq_ext, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: storePDE_def setObject_def)
  apply (wp | simp add:split_def updateObject_default_def)+
  apply clarsimp
  apply (intro conjI ballI)
   apply (drule(1) bspec)
   apply (clarsimp simp:typ_at'_def ko_wp_at'_def
     objBits_simps archObjSize_def dest!:koTypeOf_pde
     split:  Structures_H.kernel_object.split_asm  arch_kernel_object.split_asm if_split)
   apply (simp add:ps_clear_def dom_fun_upd2[unfolded fun_upd_def])+
  apply (erule rsubst[where P=Q])
  apply (rule ext, clarsimp)
  done

lemma mapM_x_storePDE_update_helper:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)
    \<and> pspace_aligned' s
    \<and> page_directory_at' ptr s
    \<and> word && ~~ mask pdBits = ptr
    \<and> sz \<le> pdBits \<and> 6 \<le> sz
    \<and> is_aligned word sz
    \<and> xs = [word , word + 4 .e. word + (mask sz)]
  \<rbrace>
  mapM_x (swp storePDE pte) xs
  \<lbrace>\<lambda>y s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (wp mapM_x_storePDE_updates)
  apply clarsimp
  apply (frule(2) page_directory_at_set_list)
     apply simp+
  apply (subst vs_valid_duplicates'_def)
  apply clarsimp
  apply (intro conjI impI)
   apply clarsimp
   apply (thin_tac "x = y" for x y)
   apply (simp add:mask_lower_twice)
   apply (subgoal_tac "y && ~~ mask sz = x && ~~ mask sz")
    apply (drule(1) page_directory_at_pde_atD')
     apply (drule mask_out_first_mask_some[where m = pdBits])
      apply (simp add:vs_ptr_align_def split:ARM_H.pde.splits)
     apply (simp add:mask_lower_twice vs_ptr_align_def
      split:ARM_H.pde.splits)
    apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
   apply (clarsimp simp:vs_ptr_align_def
      split:arch_kernel_obj.splits Structures_H.kernel_object.splits
      split:ARM_H.pde.splits)
   apply (drule mask_out_first_mask_some[where m = sz])
    apply simp
   apply (simp add:mask_lower_twice)
  apply clarsimp
  apply (intro conjI impI)
   apply (thin_tac "x = y" for x y)
   apply (clarsimp split:option.splits)
   apply (subgoal_tac "x && ~~ mask sz = y && ~~ mask sz")
    apply (drule_tac p' = x in page_directory_at_pde_atD')
      apply (drule pspace_alignedD')
       apply simp
      apply (simp add:objBits_simps' archObjSize_def pteBits_def
        is_aligned_weaken[where y = 2] pageBits_def pdeBits_def vs_ptr_align_def
        split:kernel_object.splits arch_kernel_object.splits)
     apply (simp add:mask_lower_twice)
     apply (drule mask_out_first_mask_some[where m = pdBits])
      apply (simp add:vs_ptr_align_def
        split:kernel_object.splits arch_kernel_object.splits
        ARM_H.pte.splits ARM_H.pde.splits)
     apply (subst (asm) mask_lower_twice)
      apply (simp add:vs_ptr_align_def
        split:kernel_object.splits arch_kernel_object.splits
        ARM_H.pte.splits ARM_H.pde.splits)
     apply simp
    apply (simp add:vs_ptr_align_def
      split:kernel_object.splits arch_kernel_object.splits
      ARM_H.pde.splits)
   apply (simp add:mask_lower_twice)
   apply (drule mask_out_first_mask_some[where m = sz])
    apply (simp add:vs_ptr_align_def
      split:kernel_object.splits arch_kernel_object.splits
      ARM_H.pte.splits ARM_H.pde.splits)
   apply (subst (asm) mask_lower_twice)
    apply (simp add:vs_ptr_align_def
      split:kernel_object.splits arch_kernel_object.splits
      ARM_H.pte.splits ARM_H.pde.splits)
   apply simp
  apply (clarsimp split:option.splits)
  apply (drule_tac p' = y in valid_duplicates'_D)
     apply simp+
  done

lemma vs_ptr_align_upbound:
  "vs_ptr_align a \<le> 6"
    by (simp add:vs_ptr_align_def
      split:Structures_H.kernel_object.splits
      arch_kernel_object.splits
      ARM_H.pde.splits ARM_H.pte.splits)

lemma is_aligned_le_mask:
  "\<lbrakk>is_aligned a n; a\<le>b\<rbrakk> \<Longrightarrow> a \<le> b && ~~ mask n"
  apply (drule neg_mask_mono_le)
  apply (subst (asm) is_aligned_neg_mask_eq)
  apply simp+
  done


lemma global_pd_offset:
  "\<lbrakk>is_aligned ptr pdBits ; x \<in> {ptr + (kernelBase >> 20 << 2)..ptr + 2 ^ pdBits - 1}\<rbrakk>
  \<Longrightarrow> ptr  + (x && mask pdBits) = x"
  apply (rule mask_eqI[where n = pdBits])
   apply (simp add:mask_add_aligned mask_twice pdBits_def pageBits_def)
  apply (subst mask_out_sub_mask)
  apply (simp add:mask_add_aligned mask_twice pdBits_def pageBits_def pdeBits_def)
  apply clarsimp
  apply (drule neg_mask_mono_le[where n = 14])
  apply (drule neg_mask_mono_le[where n = 14])
  apply (simp add:field_simps)
  apply (frule_tac d1 = "0x3FFF" and p1="ptr" in is_aligned_add_helper[THEN conjunct2])
   apply simp
  apply (frule_tac d1 = "kernelBase >> 20 << 2" and p1 = "ptr"
    in is_aligned_add_helper[THEN conjunct2])
   apply (simp add: ARM.kernelBase_def kernelBase_def)
  apply simp
  done

lemma globalPDEWindow_neg_mask:
  "\<lbrakk>x && ~~ mask (vs_ptr_align a) = y && ~~ mask (vs_ptr_align a);is_aligned ptr pdBits\<rbrakk>
  \<Longrightarrow> y \<in> {ptr + (kernelBase >> 20 << 2)..ptr + (2 ^ (pdBits) - 1)}
  \<Longrightarrow> x \<in> {ptr + (kernelBase >> 20 << 2)..ptr + (2 ^ (pdBits) - 1)}"
  apply (clarsimp simp:kernelBase_def ARM.kernelBase_def)
  apply (intro conjI)
   apply (rule_tac y = "y &&~~ mask (vs_ptr_align a)" in order_trans)
    apply (rule is_aligned_le_mask)
     apply (rule is_aligned_weaken[OF _ vs_ptr_align_upbound])
     apply (erule aligned_add_aligned[OF is_aligned_weaken[OF _ le_refl]])
      apply (simp add:is_aligned_def)
     apply (simp add:pdBits_def pageBits_def)
    apply simp
   apply (drule sym)
   apply (simp add:word_and_le2)
  apply (drule_tac x = y in neg_mask_mono_le[where n = pdBits])
  apply (subst (asm) is_aligned_add_helper)
    apply simp
   apply (simp add:pdBits_def pageBits_def pdeBits_def)
  apply (rule order_trans[OF and_neg_mask_plus_mask_mono[where n = pdBits]])
  apply (drule mask_out_first_mask_some[where m = pdBits])
   apply (cut_tac a = a in vs_ptr_align_upbound)
   apply (simp add:pdBits_def pageBits_def)
  apply (cut_tac a = a in vs_ptr_align_upbound)
  apply (drule le_trans[where k = 14])
   apply simp
  apply (simp add:and_not_mask_twice max_def
    pdBits_def pageBits_def pdeBits_def)
  apply (simp add:mask_def)
  apply (subst add.commute)
  apply (subst add.commute[where a = ptr])
  apply (rule word_plus_mono_right)
   apply simp
  apply (rule olen_add_eqv[THEN iffD2])
  apply (simp add:field_simps)
  apply (erule is_aligned_no_wrap')
  apply simp
  done

lemma copyGlobalMappings_ksPSpace_stable:
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  assumes ptr_al: "is_aligned ptr pdBits"
  shows
   "\<lbrace>\<lambda>s. ksPSpace s x = ko \<and> pspace_distinct' s \<and> pspace_aligned' s \<and>
    is_aligned (armKSGlobalPD (ksArchState s)) pdBits\<rbrace>
   copyGlobalMappings ptr
   \<lbrace>\<lambda>_ s. ksPSpace s x = (if x \<in> {ptr + (kernelBase >> 20 << 2)..ptr + (2 ^ pdBits - 1)}
           then ksPSpace s ((armKSGlobalPD (ksArchState s)) + (x && mask pdBits))
           else ko)\<rbrace>"
  proof -
    have not_aligned_eq_None:
      "\<And>x s. \<lbrakk>\<not> is_aligned x 2; pspace_aligned' s\<rbrakk> \<Longrightarrow> ksPSpace s x = None"
      apply (rule ccontr)
      apply clarsimp
      apply (drule(1) pspace_alignedD')
      apply (drule is_aligned_weaken[where y = 2])
       apply (case_tac y, simp_all add: objBits_simps' pageBits_def)
      apply (simp add: archObjSize_def pageBits_def
                       pteBits_def pdeBits_def
                  split: arch_kernel_object.splits)
      sorry
    have ptr_eqD:
      "\<And>p a b. \<lbrakk>p + a = ptr + b;is_aligned p pdBits;
            a < 2^ pdBits; b < 2^pdBits \<rbrakk>
       \<Longrightarrow> p = ptr"
      apply (drule arg_cong[where f = "\<lambda>x. x && ~~ mask pdBits"])
      apply (subst (asm) is_aligned_add_helper[THEN conjunct2])
        apply simp
       apply simp
      apply (subst (asm) is_aligned_add_helper[THEN conjunct2])
        apply (simp add:ptr_al)
       apply simp
      apply simp
      done
    have postfix_listD:
      "\<And>a as. suffix (a # as) [kernelBase >> 20.e.2 ^ (pdBits - 2) - 1]
       \<Longrightarrow> a \<in> set [kernelBase >> 20 .e. 2 ^ (pdBits - 2) - 1]"
       apply (clarsimp simp:suffix_def)
       apply (subgoal_tac "a \<in> set (zs @ a # as)")
        apply (drule sym)
        apply simp
       apply simp
       done
     have in_rangeD: "\<And>x.
       \<lbrakk>kernelBase >> 20 \<le> x; x \<le> 2 ^ (pdBits - 2) - 1\<rbrakk>
       \<Longrightarrow> ptr + (x << 2) \<in> {ptr + (kernelBase >> 20 << 2)..ptr + (2 ^ pdBits - 1)}"
       apply (clarsimp simp:blah)
       apply (intro conjI)
        apply (rule word_plus_mono_right)
         apply (simp add:ARM.kernelBase_def kernelBase_def pdBits_def pageBits_def pdeBits_def)
         apply (word_bitwise,simp)
        apply (rule is_aligned_no_wrap'[OF ptr_al])
        apply (simp add:pdBits_def pageBits_def pdeBits_def)
        apply (word_bitwise,simp)
       apply (rule word_plus_mono_right)
        apply (simp add:pdBits_def pageBits_def pdeBits_def)
        apply (word_bitwise,simp)
       apply (rule is_aligned_no_wrap'[OF ptr_al])
       apply (simp add:pdBits_def pageBits_def pdeBits_def)
       done

     have offset_bound:
       "\<And>x. \<lbrakk>is_aligned ptr 14;ptr + (kernelBase >> 20 << 2) \<le> x; x \<le> ptr + 0x3FFF\<rbrakk>
        \<Longrightarrow> x - ptr < 0x4000"
        apply (clarsimp simp: ARM.kernelBase_def kernelBase_def field_simps)
        apply unat_arith
        done

  show ?thesis
  apply (case_tac "\<not> is_aligned x 2")
   apply (rule hoare_name_pre_state)
   apply (clarsimp)
   apply (rule_tac Q = "\<lambda>r s. is_aligned (armKSGlobalPD (ksArchState s)) 2
      \<and> pspace_aligned' s" in hoare_post_imp)
    apply (frule_tac x = x in not_aligned_eq_None)
     apply simp
    apply (frule_tac x = x and s = sa in not_aligned_eq_None)
     apply simp
    apply clarsimp
    apply (drule_tac  x = "armKSGlobalPD (ksArchState sa) + (x && mask pdBits)"
      and  s = sa in not_aligned_eq_None[rotated])
     apply (subst is_aligned_mask)
     apply (simp add: mask_add_aligned mask_twice)
     apply (simp add:is_aligned_mask pdBits_def mask_def)
    apply simp
   apply (wp|simp)+
   apply (erule is_aligned_weaken)
   apply (simp add:pdBits_def)
  apply (simp add: copyGlobalMappings_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_conjI)
   apply (rule hoare_pre)
    apply (rule hoare_vcg_const_imp_lift)
    apply wp
     apply (rule_tac V="\<lambda>xs s. \<forall>x \<in> (set [kernelBase >> 20.e.2 ^ (pdBits - 2) - 1] - set xs).
                                 ksPSpace s (ptr + (x << 2)) = ksPSpace s (globalPD + (x << 2))"
             and I="\<lambda>s'. globalPD = (armKSGlobalPD (ksArchState s'))
                       \<and> globalPD = (armKSGlobalPD (ksArchState s))"
       in mapM_x_inv_wp2)
      apply (cut_tac ptr_al)
      apply (clarsimp simp:blah pdBits_def pageBits_def pdeBits_def)
      apply (drule_tac x="x - ptr >> 2" in spec)
      apply (frule offset_bound)
       apply simp+
      apply (erule impE)
       apply (rule conjI)
        apply (rule le_shiftr[where u="kernelBase >> 18" and n=2, simplified shiftr_shiftr, simplified])
        apply (rule word_le_minus_mono_left[where x=ptr and y="(kernelBase >> 18) + ptr", simplified])
         apply (simp add: ARM.kernelBase_def kernelBase_def field_simps)
        apply (simp add:field_simps)
        apply (erule is_aligned_no_wrap')
        apply (simp add: ARM.kernelBase_def kernelBase_def pdBits_def pageBits_def)
       apply (drule le_m1_iff_lt[THEN iffD1,THEN iffD2,rotated])
        apply simp
       apply (drule le_shiftr[where u = "x - ptr" and n = 2])
       apply simp
      apply (cut_tac b = 2 and c = 2 and a = "x - ptr" in shiftr_shiftl1)
       apply simp
      apply simp
      apply (cut_tac n = 2 and p = "x - ptr" in is_aligned_neg_mask_eq)
       apply (erule aligned_sub_aligned)
        apply (erule is_aligned_weaken,simp)
       apply simp
      apply simp
      apply (drule_tac t = x in
        global_pd_offset[symmetric,unfolded pdBits_def pageBits_def pdeBits_def,simplified])
       apply (clarsimp simp:blah field_simps)
      apply (subgoal_tac "x && mask 14 = x - ptr")
       apply clarsimp
      apply (simp add:field_simps)
     apply (wp hoare_vcg_all_lift getPDE_wp mapM_x_wp'
        | simp add: storePDE_def setObject_def split_def
        updateObject_default_def
        split: option.splits)+
     apply (clarsimp simp: objBits_simps archObjSize_def obj_at'_def scBits_simps
                           projectKO_def projectKO_opt_pde fail_def return_def oassert_opt_def)
     apply (intro conjI impI)
       apply (clarsimp simp: obj_at'_def objBits_simps scBits_simps
                             projectKO_def projectKO_opt_pde fail_def return_def pde.exhaust
                      split: Structures_H.kernel_object.splits  arch_kernel_object.splits)
      apply (drule_tac x = xa in bspec)
      apply simp
      apply (rule ccontr)
      apply (simp add: pdeBits_def)
     apply clarsimp
     apply (drule(1) ptr_eqD)
       apply (rule shiftl_less_t2n)
        apply (simp add:pdBits_def pageBits_def )
        apply (rule le_m1_iff_lt[THEN iffD1,THEN iffD1])
         apply (simp add: pdeBits_def)
        apply (simp add: pdeBits_def)
       apply (simp add:pdBits_def pageBits_def pdeBits_def)
      apply (simp add: pdeBits_def)
      apply (rule shiftl_less_t2n)
       apply (drule postfix_listD)
       apply (clarsimp simp:pdBits_def pdeBits_def le_less_trans)
      apply (simp add:pdBits_def pageBits_def pdeBits_def)
      apply (clarsimp simp: obj_at'_def objBits_simps scBits_simps
                            projectKO_def projectKO_opt_pde fail_def return_def
                     split: Structures_H.kernel_object.splits arch_kernel_object.splits)
     apply (drule_tac x = xa in bspec)
      apply (clarsimp simp:pdBits_def pdeBits_def le_less_trans)+
    apply wp
   apply (clarsimp simp:objBits_simps archObjSize_def pdeBits_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (rule hoare_vcg_const_imp_lift)
   apply wp
    apply (rule_tac Q = "\<lambda>r s'. ksPSpace s' x = ksPSpace s x \<and> globalPD = armKSGlobalPD (ksArchState s)"
      in hoare_post_imp)
     apply (wp hoare_vcg_all_lift getPDE_wp mapM_x_wp'
        | simp add: storePDE_def setObject_def split_def
        updateObject_default_def
        split: option.splits)+
    apply (clarsimp simp:objBits_simps archObjSize_def pdeBits_def dest!:in_rangeD)
   apply wp
  apply simp
  done
qed

lemma copyGlobalMappings_ksPSpace_same:
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows
  "\<lbrakk>is_aligned ptr pdBits\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. ksPSpace s x = ko \<and> pspace_distinct' s \<and> pspace_aligned' s \<and>
    is_aligned (armKSGlobalPD (ksArchState s)) pdBits \<and> ptr = armKSGlobalPD (ksArchState s)\<rbrace>
   copyGlobalMappings ptr
   \<lbrace>\<lambda>_ s. ksPSpace s x = ko\<rbrace>"
  apply (simp add:copyGlobalMappings_def)
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (rule hoare_pre)
   apply wp
    apply (rule_tac Q = "\<lambda>r s'. ksPSpace s' x = ksPSpace s x \<and> globalPD = armKSGlobalPD (ksArchState s)"
      in hoare_post_imp)
     apply simp
    apply (wp hoare_vcg_all_lift getPDE_wp mapM_x_wp'
    | simp add: storePDE_def setObject_def split_def
    updateObject_default_def
    split: option.splits)+
    apply (clarsimp simp:objBits_simps archObjSize_def)
    apply (clarsimp simp:obj_at'_def objBits_simps oassert_opt_def
      projectKO_def projectKO_opt_pde fail_def return_def
      split: Structures_H.kernel_object.splits
      arch_kernel_object.splits)
   apply wp
  apply simp
  done

lemmas copyGlobalMappings_ksPSpaceD = use_valid[OF _ copyGlobalMappings_ksPSpace_stable]
lemmas copyGlobalMappings_ksPSpace_sameD = use_valid[OF _ copyGlobalMappings_ksPSpace_same]

lemma copyGlobalMappings_ksPSpace_concrete:
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  assumes monad: "(r, s') \<in> fst (copyGlobalMappings ptr s)"
  and ps: "pspace_distinct' s" "pspace_aligned' s"
  and al: "is_aligned (armKSGlobalPD (ksArchState s)) pdBits"
          "is_aligned ptr pdBits"
  shows   "ksPSpace s' = (\<lambda>x.
           (if x \<in> {ptr + (kernelBase >> 20 << 2)..ptr + (2 ^ pdBits - 1)}
            then ksPSpace s ((x && mask pdBits) + armKSGlobalPD (ksArchState s)) else ksPSpace s x))"
  proof -
    have pd: "\<And>pd. \<lbrace>\<lambda>s. armKSGlobalPD (ksArchState s) = pd \<rbrace>
              copyGlobalMappings ptr \<lbrace>\<lambda>r s. armKSGlobalPD (ksArchState s) = pd \<rbrace>"
      by wp
    have comp: "\<And>x. x \<in> {ptr + (kernelBase >> 20 << 2)..ptr + 2 ^ pdBits - 1}
      \<Longrightarrow> ptr  + (x && mask pdBits) = x"
      using al
      apply -
      apply (rule mask_eqI[where n = pdBits])
       apply (simp add:mask_add_aligned mask_twice pdBits_def pageBits_def)
      apply (subst mask_out_sub_mask)
      apply (simp add:mask_add_aligned mask_twice pdBits_def pageBits_def)
      apply (clarsimp simp:blah)
      apply (drule neg_mask_mono_le[where n = 14])
      apply (drule neg_mask_mono_le[where n = 14])
      apply (simp add:field_simps pdeBits_def)
      apply (frule_tac d1 = "0x3FFF" and p1="ptr" in is_aligned_add_helper[THEN conjunct2])
       apply simp
      apply (frule_tac d1 = "kernelBase >> 20 << 2" and p1 = "ptr"
        in is_aligned_add_helper[THEN conjunct2])
       apply (simp add:ARM.kernelBase_def kernelBase_def)
      apply simp
      done

  show ?thesis
    using ps al monad
    apply -
    apply (rule ext)
    apply (frule_tac x = x in copyGlobalMappings_ksPSpaceD)
     apply simp+
    apply (clarsimp split:if_splits)
    apply (frule_tac x = "(armKSGlobalPD (ksArchState s') + (x && mask pdBits))"
           in copyGlobalMappings_ksPSpaceD)
     apply simp+
    apply (drule use_valid[OF _ pd])
     apply simp
    apply (clarsimp split: if_splits simp: field_simps)
    apply (clarsimp simp: mask_add_aligned)
    apply (frule comp)
    apply (clarsimp simp:pdBits_def pageBits_def mask_twice blah)
    apply (drule_tac y = "armKSGlobalPD a + b" for a b in neg_mask_mono_le[where n = 14])
    apply (drule_tac x = "armKSGlobalPD a + b" for a b in neg_mask_mono_le[where n = 14])
    apply (frule_tac d1 = "x && mask 14" in is_aligned_add_helper[THEN conjunct2])
     apply (simp add:mask_def pdeBits_def)
     apply (rule le_less_trans[OF word_and_le1])
     apply simp
    apply (frule_tac d1 = "kernelBase >> 20 << 2" in is_aligned_add_helper[THEN conjunct2])
     apply (simp add:ARM.kernelBase_def kernelBase_def)
    apply (simp add:field_simps pdeBits_def)
    apply (frule_tac d1 = "0x3FFF" and p1="ptr" in is_aligned_add_helper[THEN conjunct2])
     apply (simp add: pdeBits_def)
    apply (frule_tac d1 = "kernelBase >> 20 << 2" and p1 = "ptr"
      in is_aligned_add_helper[THEN conjunct2])
     apply (simp add:ARM.kernelBase_def kernelBase_def pdeBits_def)
    apply (simp add: pdeBits_def)
    apply (cut_tac copyGlobalMappings_ksPSpace_sameD)
       apply simp
      apply (rule monad)
     apply (simp add:al)
    apply (simp add:al add.commute)
  done
qed


lemma copyGlobalMappings_valid_duplicates':
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and pspace_distinct'
    and pspace_aligned'
    and (\<lambda>s. is_aligned (armKSGlobalPD (ksArchState s)) pdBits)
    and K (is_aligned ptr pdBits)\<rbrace>
  copyGlobalMappings ptr \<lbrace>\<lambda>y s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  proof -
      have neg_mask_simp: "\<And>x ptr' ptr a.
      \<lbrakk>is_aligned ptr pdBits\<rbrakk>
      \<Longrightarrow> x + ptr && ~~ mask (vs_ptr_align a) = (x && ~~ mask (vs_ptr_align a))
      + ptr"
        apply (cut_tac a = a in vs_ptr_align_upbound)
        apply (subst add.commute)
        apply (subst mask_out_add_aligned[symmetric])
         apply (erule is_aligned_weaken)
         apply (simp add: pdBits_def pageBits_def)+
        done
      have eq_trans: "\<And>a b c d f. (c = d) \<Longrightarrow> (a = f c) \<Longrightarrow> (b = f d) \<Longrightarrow> (a = b)"
        by auto
      have mask_sub_mask:"\<And>m n x. ((x::word32) && mask n) && ~~ mask m = (x && ~~ mask m ) && mask n"
        by (rule word_eqI, auto)

  show ?thesis
  apply (clarsimp simp:valid_def)
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp split:option.splits)
  apply (drule copyGlobalMappings_ksPSpace_concrete)
     apply simp+
  apply (intro conjI)
   apply clarsimp
   apply (frule_tac ptr = ptr in globalPDEWindow_neg_mask)
     apply simp
    apply simp
   apply (clarsimp split:if_splits)
   apply (drule_tac p' = "((y && mask pdBits) + armKSGlobalPD (ksArchState s))"
     in valid_duplicates'_D[rotated])
      apply (erule aligned_add_aligned[OF is_aligned_andI1])
       apply (erule is_aligned_weaken[where y = 2])
       apply (simp add:pdBits_def)
      apply simp
     apply (frule_tac x = "x && mask pdBits" and a = x2 and ptr = "armKSGlobalPD (ksArchState s)"
         in neg_mask_simp)
     apply (drule_tac x = "y && mask pdBits" and a = x2 and ptr = "armKSGlobalPD (ksArchState s)"
       in neg_mask_simp)
     apply (simp add:mask_sub_mask)
    apply simp
   apply simp
  apply (clarsimp split:if_splits)
   apply (drule_tac ptr = ptr in globalPDEWindow_neg_mask[OF sym])
     apply simp
    apply simp
   apply simp
  apply (drule_tac p' = y  in valid_duplicates'_D[rotated])
  apply simp+
  done
qed

lemma foldr_data_map_insert[simp]:
 "foldr (\<lambda>addr map a. if a = addr then Some b else map a)
 = foldr (\<lambda>addr. data_map_insert addr b)"
  apply (rule ext)+
  apply (simp add:data_map_insert_def[abs_def] fun_upd_def)
  done

lemma new_cap_addrs_same_align_pdpt_bits:
assumes inset: "p\<in>set (new_cap_addrs (2 ^ us) ptr ko)"
  and   lowbound: "vs_entry_align ko \<le> us"
  and   pdpt_align:"p && ~~ mask (vs_ptr_align ko) = p' && ~~ mask (vs_ptr_align ko)"
shows
    "\<lbrakk>is_aligned ptr (objBitsKO ko + us); us < 30;is_aligned p' 2\<rbrakk>
  \<Longrightarrow> p' \<in> set (new_cap_addrs (2 ^ us) ptr ko)"
  apply (subgoal_tac "\<And>x. \<lbrakk>is_aligned ptr (Suc (Suc us)); us < 30; is_aligned p' 2; 4 \<le> us; ptr + (of_nat x << 2) && ~~ mask 6 = p' && ~~ mask 6;
         x < 2 ^ us\<rbrakk>
        \<Longrightarrow> \<exists>x\<in>{0..<2 ^ us}. p' = ptr + (of_nat x << 2)")
   prefer 2
   using lowbound inset
   apply -
   apply (drule mask_out_first_mask_some[where m = "us + 2"])
    apply (simp add:mask_lower_twice)+
   apply (subst (asm) is_aligned_add_helper[THEN conjunct2])
     apply simp
    apply (rule shiftl_less_t2n)
     apply (simp add:of_nat_power)
    apply simp
   apply (rule_tac x= "unat (p' && mask (Suc (Suc us)) >> 2) " in bexI)
    apply simp
    apply (subst shiftr_shiftl1)
     apply simp+
    apply (subst is_aligned_neg_mask_eq[where n = 2])
     apply (erule is_aligned_andI1)
    apply (simp add:mask_out_sub_mask)
   apply simp
   apply (rule unat_less_power)
    apply (simp add:word_bits_def)
   apply (rule shiftr_less_t2n)
   apply (rule le_less_trans[OF word_and_le1])
   apply (rule less_le_trans[OF mask_lt_2pn])
    apply simp
   apply simp
  using pdpt_align
  apply (clarsimp simp: image_def vs_entry_align_def vs_ptr_align_def
    new_cap_addrs_def objBits_simps archObjSize_def pdeBits_def pteBits_def
    split:ARM_H.pde.splits ARM_H.pte.splits arch_kernel_object.splits
    Structures_H.kernel_object.splits)
  done

lemma valid_duplicates'_insert_ko:
  "\<lbrakk> vs_valid_duplicates' m; is_aligned ptr (objBitsKO ko + us);
    vs_entry_align ko \<le> us;
    objBitsKO ko + us < 32;
    \<forall>x\<in> set (new_cap_addrs (2^us) ptr ko). m x = None \<rbrakk>
  \<Longrightarrow>  vs_valid_duplicates'
  (foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs (2^us) ptr ko) m)"
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp simp: vs_entry_align_def
                        foldr_upd_app_if[folded data_map_insert_def])
  apply (clarsimp split:option.splits
         simp:foldr_upd_app_if[unfolded data_map_insert_def[symmetric]])
  apply (rule conjI)
   apply clarsimp
   apply (case_tac ko, simp_all add:vs_ptr_align_def)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all split: ARM_H.pte.splits)
    apply (drule(1) bspec)+
    apply (drule_tac p' = y in new_cap_addrs_same_align_pdpt_bits)
         apply (simp add:vs_entry_align_def)
        apply (simp add:vs_ptr_align_def)
       apply (simp add:objBits_simps archObjSize_def pteBits_def)+
   apply (clarsimp split: ARM_H.pde.splits simp:objBits_simps)
   apply (drule(1) bspec)+
   apply (drule_tac p' = y in new_cap_addrs_same_align_pdpt_bits)
        apply (simp add:vs_entry_align_def)
       apply (simp add:vs_ptr_align_def)
      apply (simp add:objBits_simps archObjSize_def pdeBits_def)+
  apply clarsimp
  apply (intro conjI impI allI)
   apply (drule(1) valid_duplicates'_D)
     apply fastforce
    apply (simp add:vs_ptr_align_def)
   apply simp
  apply (drule(2) valid_duplicates'_D)
      apply (clarsimp simp:vs_ptr_align_def
     split: Structures_H.kernel_object.splits
     ARM_H.pde.splits ARM_H.pte.splits
     arch_kernel_object.splits)
  apply simp
  done

lemma none_in_new_cap_addrs:
  "\<lbrakk>is_aligned ptr (objBitsKO obj + us); objBitsKO obj + us < word_bits;
  pspace_no_overlap' ptr (objBitsKO obj + us) s;
  pspace_aligned' s\<rbrakk>
  \<Longrightarrow> \<forall>x\<in>set (new_cap_addrs (2^us) ptr obj). ksPSpace s x = None"
  apply (rule ccontr,clarsimp)
  apply (drule not_in_new_cap_addrs[rotated - 1])
   apply simp+
  done

lemma valid_duplicates'_update:
  "\<lbrakk>is_aligned ptr (APIType_capBits ty us);pspace_aligned' s;
   vs_valid_duplicates' (ksPSpace s); vs_entry_align ko = 0;
   pspace_no_overlap' ptr (APIType_capBits ty us) s\<rbrakk> \<Longrightarrow> vs_valid_duplicates'
   (\<lambda>a. if a = ptr then Some ko else ksPSpace s a)"
  apply (subst vs_valid_duplicates'_def)
  apply clarsimp
  apply (intro conjI impI allI)
    apply (case_tac ko,
           simp_all add: vs_ptr_align_def vs_entry_align_def)
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object,
           simp_all split: ARM_H.pde.splits ARM_H.pte.splits)
   apply (clarsimp split:option.splits)
   apply (drule(2) pspace_no_overlap_base')
   apply (drule(2) valid_duplicates'_D)
    apply simp
   apply (clarsimp split: option.splits)+
  apply (drule valid_duplicates'_D)
   apply simp+
  done

lemma createObject_valid_duplicates'[wp]:
  "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and pspace_aligned' and pspace_distinct'
   and pspace_no_overlap' ptr (getObjectSize ty us)
   and (\<lambda>s. is_aligned (armKSGlobalPD (ksArchState s)) pdBits)
   and K (is_aligned ptr (getObjectSize ty us))
   and K (ty = APIObjectType apiobject_type.CapTableObject \<longrightarrow> us < 28)\<rbrace>
  RetypeDecls_H.createObject ty ptr us d
  \<lbrace>\<lambda>xa s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add:createObject_def)
  apply (rule hoare_pre)
  apply (wpc | wp| simp add: ARM_H.createObject_def split del: if_split)+
         apply (simp add: placeNewObject_def placeNewDataObject_def
                          placeNewObject'_def split_def split del: if_split
           | wp hoare_unless_wp[where P="d"] hoare_unless_wp[where Q=\<top>]
           | wpc | simp add: alignError_def split del: if_split)+
     apply (rule copyGlobalMappings_valid_duplicates')
    apply ((wp hoare_unless_wp[where P="d"] hoare_unless_wp[where Q=\<top>] | wpc
            | simp add: alignError_def placeNewObject_def
                        placeNewObject'_def split_def split del: if_split)+)[2]
  apply (intro conjI impI)
             apply clarsimp+
            apply (erule(2) valid_duplicates'_update)
             apply (clarsimp simp: vs_entry_align_def)+
            apply (erule(2) valid_duplicates'_update)
             apply (clarsimp simp: vs_entry_align_def)+
           apply ((clarsimp simp: new_cap_addrs_fold'[where n = "0x10",simplified]
            | (erule valid_duplicates'_insert_ko[where us = 4,simplified]
              , (simp add: toAPIType_def vs_entry_align_def
                           APIType_capBits_def objBits_simps pageBits_def)+)[1]
            | rule none_in_new_cap_addrs[where us = 4,simplified,THEN bspec,rotated -1]
            | simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
         apply ((clarsimp simp: new_cap_addrs_fold'[where n = "0x10",simplified]
           | (erule valid_duplicates'_insert_ko[where us = 4,simplified]
             , (simp add: toAPIType_def vs_entry_align_def
                          APIType_capBits_def objBits_simps pageBits_def)+)[1]
           | rule none_in_new_cap_addrs[where us = 4,simplified,THEN bspec,rotated -1]
           | simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
        apply ((clarsimp simp: new_cap_addrs_fold'[where n = "0x100",simplified]
          | (erule valid_duplicates'_insert_ko[where us = 8,simplified]
            , (simp add: toAPIType_def vs_entry_align_def
                         APIType_capBits_def objBits_simps pageBits_def)+)[1]
          | rule none_in_new_cap_addrs[where us = 8,simplified,THEN bspec,rotated -1]
          | simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
       apply (clarsimp simp: new_cap_addrs_fold'[where n = "0x100",simplified])
       apply (erule valid_duplicates'_insert_ko[where us = 8,simplified])
          apply (simp add: toAPIType_def vs_entry_align_def
                           APIType_capBits_def objBits_simps pageBits_def)+
       apply (rule none_in_new_cap_addrs[where us =8,simplified]
        ,(simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
      apply (clarsimp simp: new_cap_addrs_fold'[where n = "0x1000",simplified])
      apply (erule valid_duplicates'_insert_ko[where us = 12,simplified])
         apply (simp add: toAPIType_def vs_entry_align_def
                          APIType_capBits_def objBits_simps pageBits_def)+
      apply (rule none_in_new_cap_addrs[where us =12,simplified]
       ,(simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
     apply (clarsimp simp: new_cap_addrs_fold'[where n = "0x1000",simplified])
     apply (erule valid_duplicates'_insert_ko[where us = 12,simplified])
       apply (simp add: ARM_H.toAPIType_def vs_entry_align_def
                        APIType_capBits_def objBits_simps pageBits_def)+
     apply (rule none_in_new_cap_addrs[where us =12,simplified]
      ,(simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
    apply (clarsimp simp: objBits_simps ptBits_def archObjSize_def pageBits_def)
   apply (cut_tac ptr=ptr in new_cap_addrs_fold'[where n = "0x100" and ko = "(KOArch (KOPTE makeObject))"
      ,simplified objBits_simps])
    apply simp
   apply (clarsimp simp: archObjSize_def)
   apply (erule valid_duplicates'_insert_ko[where us = 8,simplified])
      apply (simp add: toAPIType_def archObjSize_def vs_entry_align_def
                       APIType_capBits_def objBits_simps pageBits_def
                       pdeBits_def pteBits_def
                split: ARM_H.pte.splits)+
    apply (rule none_in_new_cap_addrs[where us =8,simplified]
      ,(simp add: objBits_simps pageBits_def word_bits_conv archObjSize_def pteBits_def)+)[1]
   apply clarsimp
   apply (cut_tac ptr=ptr in new_cap_addrs_fold'[where n = "0x1000" and ko = "(KOArch (KOPDE makeObject))"
     ,simplified objBits_simps])
    apply simp
   apply (clarsimp simp: objBits_simps archObjSize_def pdBits_def pageBits_def)
   apply (frule(2) retype_aligned_distinct'[where n = 4096 and ko = "KOArch (KOPDE makeObject)"])
    apply (simp add:objBits_simps archObjSize_def)
    apply (rule range_cover_rel[OF range_cover_full])
       apply simp
      apply (simp add:APIType_capBits_def word_bits_def pdeBits_def)+
   apply (frule(2) retype_aligned_distinct'(2)[where n = 4096 and ko = "KOArch (KOPDE makeObject)"])
    apply (simp add:objBits_simps archObjSize_def)
    apply (rule range_cover_rel[OF range_cover_full])
       apply simp
      apply (simp add:APIType_capBits_def word_bits_def pdeBits_def)+
   apply (subgoal_tac "vs_valid_duplicates'
                (foldr (\<lambda>addr. data_map_insert addr (KOArch (KOPDE makeObject)))
                  (map (\<lambda>n. ptr + (n << 2)) [0.e.2 ^ (pdBits - 2) - 1]) (ksPSpace s))")
    apply (simp add:APIType_capBits_def pdBits_def pageBits_def pdeBits_def
     data_map_insert_def[abs_def])
   apply (clarsimp simp: archObjSize_def pdBits_def pageBits_def pdeBits_def)
   apply (rule valid_duplicates'_insert_ko[where us = 12,simplified])
      apply (simp add: ARM_H.toAPIType_def archObjSize_def vs_entry_align_def
                       APIType_capBits_def objBits_simps pageBits_def pdeBits_def
                split: ARM_H.pde.splits)+
   apply (rule none_in_new_cap_addrs[where us =12,simplified]
     ,(simp add: objBits_simps pageBits_def word_bits_conv archObjSize_def pdeBits_def)+)[1]
  apply (intro conjI impI allI)
        apply simp
       apply (fastforce elim!: valid_duplicates'_update simp: vs_entry_align_def)+
    apply (clarsimp simp:ARM_H.toAPIType_def word_bits_def
                   split:ARM_H.object_type.splits)
    apply (cut_tac ptr = ptr in new_cap_addrs_fold'[where n = "2^us"
               and ko = "(KOCTE makeObject)",simplified])
     apply (rule word_1_le_power)
     apply (clarsimp simp: word_bits_def)
    apply (drule_tac ptr = ptr and ko = "KOCTE makeObject" in
           valid_duplicates'_insert_ko[where us = us,simplified])
        apply (simp add: APIType_capBits_def is_aligned_mask toAPIType_def
                  split: ARM_H.object_type.splits)
       apply (simp add: vs_entry_align_def)
      apply (simp add: objBits_simps')
     apply (rule none_in_new_cap_addrs
            ,(simp add: objBits_simps' pageBits_def APIType_capBits_def
                        ARM_H.toAPIType_def
                        word_bits_conv archObjSize_def is_aligned_mask
                 split: ARM_H.object_type.splits)+)[1]
    apply (clarsimp simp: word_bits_def)
   apply (fastforce elim!: valid_duplicates'_update
                     simp: vs_entry_align_def)+
  done

crunch arch_inv[wp]: createNewObjects "\<lambda>s. P (armKSGlobalPD (ksArchState s))"
  (simp: crunch_simps zipWithM_x_mapM wp: crunch_wps hoare_unless_wp)


lemma createNewObjects_valid_duplicates'[wp]:
 "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and pspace_no_overlap' ptr sz and pspace_aligned'
    and pspace_distinct' and (\<lambda>s. is_aligned (armKSGlobalPD (ksArchState s)) pdBits)
    and K (range_cover ptr sz (Types_H.getObjectSize ty us) (length dest))
    and K (ptr \<noteq> 0)
    and K (ty = APIObjectType ArchTypes_H.apiobject_type.CapTableObject \<longrightarrow> us < 28)
    and K (ty = APIObjectType ArchTypes_H.apiobject_type.SchedContextObject \<longrightarrow> sc_size_bounds us)\<rbrace>
  createNewObjects ty src dest ptr us d
  \<lbrace>\<lambda>reply s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  proof (induct rule:rev_induct )
    case Nil
    show ?case
      by (simp add:createNewObjects_def zipWithM_x_mapM mapM_Nil | wp)+
   next
   case (snoc dest dests)
   show ?case
     apply (rule hoare_gen_asm)+
     apply clarsimp
     apply (frule range_cover.weak)
     apply (subst createNewObjects_Cons)
      apply (simp add: word_bits_def)
     apply wp
      apply (wp snoc.hyps)
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_post_imp[OF _ createNewObjects_pspace_no_overlap'[where sz = sz]])
       apply clarsimp
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_post_imp[OF _ createNewObjects_pspace_no_overlap'[where sz = sz]])
       apply clarsimp
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_post_imp[OF _ createNewObjects_pspace_no_overlap'[where sz = sz]])
       apply (rule pspace_no_overlap'_le)
        apply fastforce
       apply (simp add: range_cover.sz[where 'a=32, folded word_bits_def])+
      apply wp
     apply clarsimp
     apply (frule range_cover.aligned)
     apply (intro conjI aligned_add_aligned)
        apply (erule range_cover_le,simp)
       apply (rule is_aligned_shiftl_self)
      apply simp
     apply simp
     done
   qed

lemma valid_duplicates'_diffI:
  defines "heap_diff m m' \<equiv> {(x::word32). (m x \<noteq> m' x)}"
  shows "\<lbrakk>vs_valid_duplicates' m;
          vs_valid_duplicates' (\<lambda>x. if x \<in> (heap_diff m m') then m' x else None);
          vs_valid_duplicates' (\<lambda>x. if x \<in> (heap_diff m m') then None else m' x)\<rbrakk>
         \<Longrightarrow> vs_valid_duplicates' m'"
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp simp: heap_diff_def split: option.splits)
  apply (case_tac "m x = m' x")
   apply simp
   apply (case_tac "m y = m' y")
    apply (drule(2) valid_duplicates'_D)
    apply simp+
   apply (drule(2) valid_duplicates'_D)
   apply (thin_tac "vs_valid_duplicates' m" for m)
   apply (drule_tac p = x and ko = "the (m' x)" in valid_duplicates'_D)
      apply (clarsimp split:if_splits)
     apply assumption
    apply (clarsimp split:if_splits)+
   apply (case_tac "m y = m' y")
    apply clarsimp
   apply (thin_tac "vs_valid_duplicates' m" for m)
   apply (drule_tac p = x and ko = "the (m' x)" in valid_duplicates'_D)
      apply (clarsimp split:if_splits)
     apply assumption
    apply (simp split:if_splits)+
  apply (thin_tac "vs_valid_duplicates' m" for m)
  apply (drule_tac p = x and ko = "the (m' x)" in valid_duplicates'_D)
   apply (clarsimp split:if_splits)
    apply assumption
   apply (clarsimp split:if_splits)+
  done

lemma valid_duplicates_deleteObjects_helper:
  assumes vd:"vs_valid_duplicates' (m::(word32 \<rightharpoonup> Structures_H.kernel_object))"
  assumes inc: "\<And>p ko. \<lbrakk>m p = Some (KOArch ko);p \<in> {ptr .. ptr + 2 ^ sz - 1}\<rbrakk>
  \<Longrightarrow> 6 \<le> sz"
  assumes aligned:"is_aligned ptr sz"
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows "vs_valid_duplicates'  (\<lambda>x. if x \<in> {ptr .. ptr + 2 ^ sz - 1} then None else m x)"
  apply (rule valid_duplicates'_diffI,rule vd)
   apply (clarsimp simp: vs_valid_duplicates'_def split:option.splits)
  apply (clarsimp simp: vs_valid_duplicates'_def split:option.splits)
  apply (case_tac "the (m x)",simp_all add:vs_ptr_align_def)
           apply fastforce+
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object)
      apply fastforce+
     apply (clarsimp split:ARM_H.pte.splits)
     apply auto[1]
       apply (drule_tac p' = y in valid_duplicates'_D[OF vd])
         apply (simp add:vs_ptr_align_def)+
       apply clarsimp
       apply (drule(1) inc)
       apply (drule(1) mask_out_first_mask_some)
       apply (simp add:mask_lower_twice)
       apply (simp add: mask_in_range[OF aligned,symmetric])
      apply (drule_tac p' = y in valid_duplicates'_D[OF vd])
        apply simp
       apply (simp add:vs_ptr_align_def)
      apply simp
     apply (drule_tac p' = y in valid_duplicates'_D[OF vd])
       apply simp
      apply (simp add:vs_ptr_align_def)
     apply simp
    apply (clarsimp split:ARM_H.pde.splits)
    apply auto[1]
      apply (drule_tac p' = y in valid_duplicates'_D[OF vd])
        apply simp
       apply (simp add:vs_ptr_align_def)
      apply (drule(1) inc)
      apply (drule(1) mask_out_first_mask_some)
      apply (simp add:mask_lower_twice)
      apply (simp add: mask_in_range[OF aligned,symmetric])
     apply (drule_tac p' = y in valid_duplicates'_D[OF vd])
       apply simp
      apply (simp add:vs_ptr_align_def)
     apply simp
    apply (drule_tac p' = y in valid_duplicates'_D[OF vd])
      apply simp
     apply (simp add:vs_ptr_align_def)
    apply simp
   apply fastforce+
  done

lemma deleteObjects_valid_duplicates'[wp]:
  notes [simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows
  "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      K (is_aligned ptr sz)
   \<rbrace> deleteObjects ptr sz
   \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: deleteObjects_def2)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wp hoare_drop_imps|simp)+
  apply clarsimp
  apply (simp add:deletionIsSafe_def)
  apply (erule valid_duplicates_deleteObjects_helper)
   apply fastforce
  apply simp
  done

crunch arch_inv[wp]: resetUntypedCap "\<lambda>s. P (ksArchState s)"
  (simp: crunch_simps
     wp: hoare_drop_imps hoare_unless_wp mapME_x_inv_wp
         preemptionPoint_inv
   ignore: freeMemory)

crunch valid_duplicates[wp]: updateFreeIndex "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"

lemma untypedCap_is_aligned:
  "\<lbrakk>valid_objs' s; cte_wp_at' (isUntypedCap \<circ> cteCap) slot s; cte_wp_at' ((=) cap \<circ> cteCap) slot s\<rbrakk>
   \<Longrightarrow> is_aligned (capPtr cap) (capBlockSize cap)"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD], clarsimp+)
  apply (clarsimp simp: valid_cap_simps' capAligned_def isCap_simps)
  done

lemma resetUntypedCap_valid_duplicates'[wp]:
  "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s))
      and valid_objs' and cte_wp_at' (isUntypedCap o cteCap) slot\<rbrace>
   resetUntypedCap slot
   \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  (is "\<lbrace>?P\<rbrace> ?f \<lbrace>\<lambda>_. ?Q\<rbrace>")
  apply (clarsimp simp: resetUntypedCap_def)
  apply (rule validE_valid)
  apply (rule_tac B="\<lambda>cap. ?P and cte_wp_at' ((=) cap \<circ> cteCap) slot" in hoare_vcg_seqE[rotated])
   apply wpsimp
  apply (simp only: unlessE_def)
  apply (clarsimp; safe; (solves wpsimp)?)
    apply wpsimp
    apply (fastforce elim: untypedCap_is_aligned)
   apply wpsimp
   apply (fastforce elim: untypedCap_is_aligned)
  apply (wpsimp wp: mapME_x_inv_wp preemptionPoint_inv)
  apply (fastforce elim: untypedCap_is_aligned)
  done

lemma is_aligned_armKSGlobalPD:
  "valid_arch_state' s
    \<Longrightarrow> is_aligned (armKSGlobalPD (ksArchState s)) pdBits"
  by (clarsimp simp: valid_arch_state'_def page_directory_at'_def)

lemma new_CapTable_bound:
  "range_cover (ptr :: obj_ref) sz (APIType_capBits tp us) n
    \<Longrightarrow> tp = APIObjectType ArchTypes_H.apiobject_type.CapTableObject \<longrightarrow> us < 28"
  apply (frule range_cover.sz)
  apply (drule range_cover.sz(2))
  apply (clarsimp simp: APIType_capBits_def objBits_simps' word_bits_def)
  done

lemma invokeUntyped_valid_duplicates[wp]:
  notes hoare_whenE_wps[wp_split del] shows
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
         and valid_untyped_inv' ui and ct_active'\<rbrace>
   invokeUntyped ui
   \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s) \<rbrace>"
  apply (simp only: invokeUntyped_def updateCap_def)
  apply (rule hoare_name_pre_state)
  apply (cases ui)
  apply (clarsimp simp only: pred_conj_def valid_untyped_inv_wcap'
                             Invocations_H.untyped_invocation.simps)
  apply (frule(2) invokeUntyped_proofs.intro)
  apply (rule hoare_pre)
   apply simp
   apply (wp add: updateFreeIndex_pspace_no_overlap'
             del: whenE_E_wp whenE_R_wp)
   apply (rule hoare_post_impErr)
     apply (rule combine_validE)
      apply (rule_tac ui=ui in whenE_reset_resetUntypedCap_invs_etc)
     apply (rule hoare_whenE_wp)
     apply (rule valid_validE)
     apply (rule resetUntypedCap_valid_duplicates')
    defer
    apply simp
   apply (clarsimp simp del: valid_untyped_inv_wcap'.simps
                split del: if_split)
   apply (rule conjI, assumption)
   apply (auto simp: cte_wp_at_ctes_of isCap_simps)[1]
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule new_CapTable_bound)
  apply (frule invokeUntyped_proofs.not_0_ptr)
  apply (strengthen is_aligned_armKSGlobalPD)
  apply (frule cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD], clarsimp+)
  apply (clarsimp simp add: isCap_simps valid_cap_simps' capAligned_def)
  apply (auto split: if_split_asm)
  done

crunch valid_duplicates'[wp]:
  doReplyTransfer "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
(wp: crunch_wps isFinalCapability_inv
 simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  setVMRoot "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
(wp: crunch_wps simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  invalidateASIDEntry "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
(wp: crunch_wps simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  flushSpace "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
(wp: crunch_wps simp: crunch_simps unless_def)

lemma get_asid_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  getObject param_b \<lbrace>\<lambda>(pool::asidpool) s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:getObject_def | wp)+
  done

lemma set_asid_pool_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setObject a (pool::asidpool)
  \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = pool,simplified])
  apply (clarsimp simp:updateObject_default_def assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def typeError_def
    split:if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],clarsimp+)+
  done

crunch valid_duplicates'[wp]:
  suspend "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps gts_wp' simp: crunch_simps unless_def o_def)

crunch valid_duplicates'[wp]:
deletingIRQHandler  "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma storePDE_no_duplicates':
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)
    \<and> ko_wp_at' (\<lambda>ko. vs_entry_align ko = 0 ) ptr s
    \<and> vs_entry_align (KOArch (KOPDE pde)) = 0 \<rbrace>
   storePDE ptr pde
  \<lbrace>\<lambda>ya s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:storePDE_def setObject_def split_def | wp | wpc)+
    apply (simp add:updateObject_default_def)
    apply wp+
  apply clarsimp
  apply (subst vs_valid_duplicates'_def)
   apply clarsimp
  apply (intro conjI impI)
   apply (clarsimp simp:vs_ptr_align_def vs_entry_align_def
     split:option.splits
     ARM_H.pde.splits)
  apply clarsimp
  apply (intro conjI impI)
   apply (clarsimp split:option.splits)
   apply (drule_tac p = x in valid_duplicates'_D)
      apply simp
     apply simp
    apply simp
   apply (clarsimp simp:ko_wp_at'_def vs_entry_align_def
     vs_ptr_align_def
     split:if_splits option.splits arch_kernel_object.splits
     Structures_H.kernel_object.splits ARM_H.pde.splits
     ARM_H.pte.splits)
  apply (clarsimp split:option.splits)
  apply (drule_tac p = x in valid_duplicates'_D)
   apply simp+
  done

lemma storePTE_no_duplicates':
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)
    \<and> ko_wp_at' (\<lambda>ko. vs_entry_align ko = 0 ) ptr s
    \<and> vs_entry_align (KOArch (KOPTE pte)) = 0 \<rbrace>
   storePTE ptr pte
  \<lbrace>\<lambda>ya s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:storePTE_def setObject_def split_def | wp | wpc)+
    apply (simp add:updateObject_default_def)
    apply wp+
  apply clarsimp
  apply (subst vs_valid_duplicates'_def)
   apply clarsimp
  apply (intro conjI impI)
   apply (clarsimp simp:vs_entry_align_def vs_ptr_align_def
     split:option.splits
     ARM_H.pte.splits)
  apply clarsimp
  apply (intro conjI impI)
   apply (clarsimp split:option.splits)
   apply (drule_tac p = x in valid_duplicates'_D)
      apply simp
     apply simp
    apply simp
   apply (clarsimp simp:ko_wp_at'_def
     vs_ptr_align_def vs_entry_align_def
     split:if_splits option.splits arch_kernel_object.splits
     Structures_H.kernel_object.splits ARM_H.pde.splits
     ARM_H.pte.splits)
  apply (clarsimp split:option.splits)
  apply (drule_tac p = x in valid_duplicates'_D)
   apply simp+
  done

crunch valid_duplicates'[wp]:
 lookupPTSlot "\<lambda>s. valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma checkMappingPPtr_SmallPage:
  "\<lbrace>\<top>\<rbrace> checkMappingPPtr word ARMSmallPage (Inl p)
           \<lbrace>\<lambda>x s. ko_wp_at' (\<lambda>ko. vs_entry_align ko = 0) p s\<rbrace>,-"
  apply (simp add:checkMappingPPtr_def)
   apply (wp unlessE_wp getPTE_wp |wpc|simp add:)+
  apply (clarsimp simp:ko_wp_at'_def obj_at'_def)
  apply (clarsimp simp:projectKO_def projectKO_opt_pte
    return_def fail_def vs_entry_align_def oassert_opt_def
    split:kernel_object.splits
    arch_kernel_object.splits option.splits)
  done

lemma checkMappingPPtr_Section:
  "\<lbrace>\<top>\<rbrace> checkMappingPPtr word ARMSection (Inr p)
           \<lbrace>\<lambda>x s. ko_wp_at' (\<lambda>ko. vs_entry_align ko = 0) p s\<rbrace>,-"
  apply (simp add:checkMappingPPtr_def)
   apply (wp unlessE_wp getPDE_wp |wpc|simp add:)+
  apply (clarsimp simp:ko_wp_at'_def obj_at'_def)
  apply (clarsimp simp:projectKO_def projectKO_opt_pde
    return_def fail_def vs_entry_align_def oassert_opt_def
    split:kernel_object.splits
    arch_kernel_object.splits option.splits)
  done

lemma mapM_x_mapM_valid:
  "\<lbrace> P \<rbrace> mapM_x f xs \<lbrace>\<lambda>r. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>mapM f xs \<lbrace>\<lambda>r. Q\<rbrace>"
  apply (simp add:NonDetMonadLemmaBucket.mapM_x_mapM)
  apply (clarsimp simp:valid_def return_def bind_def)
  apply (drule spec)
  apply (erule impE)
   apply simp
  apply (drule(1) bspec)
  apply fastforce
  done

crunch valid_duplicates'[wp]:
 flushPage "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma lookupPTSlot_aligned:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> vmsz_aligned vptr sz \<and> sz \<noteq> ARMSuperSection\<rbrace>
   lookupPTSlot pd vptr
  \<lbrace>\<lambda>rv s. is_aligned rv ((pageBitsForSize sz) - 10)\<rbrace>,-"
  apply (simp add:lookupPTSlot_def)
  apply (wp|wpc|simp)+
  apply (wp getPDE_wp)
  apply (clarsimp simp:obj_at'_def vmsz_aligned_def)
  apply (clarsimp simp:projectKO_def fail_def oassert_opt_def
    projectKO_opt_pde return_def lookup_pt_slot_no_fail_def
    split:option.splits Structures_H.kernel_object.splits
    arch_kernel_object.splits)
  apply (erule(1) valid_objsE')
  apply (rule aligned_add_aligned)
     apply (simp add:valid_obj'_def)
     apply (erule is_aligned_ptrFromPAddr_n)
     apply (simp add:ptBits_def pageBits_def pteBits_def)
    apply (rule is_aligned_shiftl)
    apply (rule is_aligned_andI1)
    apply (rule is_aligned_shiftr)
    apply (case_tac sz,simp_all)[1]
   apply (simp add:ptBits_def word_bits_def pageBits_def)
  apply (case_tac sz,simp_all add:ptBits_def pageBits_def pteBits_def)
  done

crunch valid_arch_state'[wp]:
 flushPage valid_arch_state'
  (wp: crunch_wps  getHWASID_valid_arch' simp: crunch_simps unless_def)

crunch valid_arch_state'[wp]:
 flushTable "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma unmapPage_valid_duplicates'[wp]:
  notes checkMappingPPtr_inv[wp del] shows
  "\<lbrace>pspace_aligned' and valid_objs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
   and K (vmsz_aligned vptr vmpage_size)\<rbrace>
  unmapPage vmpage_size asiv vptr word \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:unmapPage_def)
   (* make sure checkMappingPPtr_SmallPage is first tried before checkMappingPPtr_inv *)
  apply ((wp storePTE_no_duplicates' mapM_x_mapM_valid
    storePDE_no_duplicates' checkMappingPPtr_Section
    mapM_x_storePDE_update_helper[where sz = 6]
    lookupPTSlot_page_table_at'
    checkMappingPPtr_SmallPage)+ | wpc
    | simp add:split_def conj_comms | wp (once) checkMappingPPtr_inv)+
         apply (rule_tac ptr = "p && ~~ mask ptBits" and word = p
            in mapM_x_storePTE_update_helper[where sz = 6])
        apply simp
        apply (wp mapM_x_mapM_valid)+
       apply (wp checkMappingPPtr_inv lookupPTSlot_page_table_at')+
      apply (rule hoare_post_imp_R[OF lookupPTSlot_aligned[where sz= vmpage_size]])
      apply (simp add:pageBitsForSize_def)
      apply (drule upto_enum_step_shift[where n = 6 and m = 2,simplified])
      apply (clarsimp simp:mask_def add.commute upto_enum_step_def largePagePTEOffsets_def pteBits_def)
     apply wp+
       apply ((wp storePTE_no_duplicates' mapM_x_mapM_valid
          storePDE_no_duplicates' checkMappingPPtr_Section
          checkMappingPPtr_SmallPage)+ | wpc
          | simp add:split_def conj_comms | wp (once) checkMappingPPtr_inv)+
       apply (rule_tac ptr = "p && ~~ mask pdBits" and word = p
          in mapM_x_storePDE_update_helper[where sz = 6])
      apply wp+
     apply (clarsimp simp:conj_comms)
     apply (wp checkMappingPPtr_inv static_imp_wp)+
   apply (clarsimp simp:conj_comms)
   apply (rule hoare_post_imp_R[where Q'= "\<lambda>r. pspace_aligned' and
     (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
     K(vmsz_aligned vptr vmpage_size \<and> is_aligned r pdBits)
     and page_directory_at' (lookup_pd_slot r vptr && ~~ mask pdBits)"])
    apply (wp findPDForASID_page_directory_at' | simp)+
   apply (clarsimp simp add:pdBits_def pageBits_def vmsz_aligned_def)
   apply (drule is_aligned_lookup_pd_slot)
    apply (erule is_aligned_weaken,simp)
   apply simp
   apply (drule upto_enum_step_shift[where n = 6 and m = 2,simplified])
   apply (clarsimp simp:mask_def add.commute upto_enum_step_def superSectionPDEOffsets_def pdeBits_def)
  apply (clarsimp simp:ptBits_def pageBits_def vs_entry_align_def)
  done

crunch ko_wp_at'[wp]:
 checkPDNotInASIDMap "\<lambda>s. ko_wp_at' P p s"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch ko_wp_at'[wp]:
 armv_contextSwitch "\<lambda>s. ko_wp_at' P p s"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch ko_wp_at'[wp]:
 setVMRootForFlush "\<lambda>s. ko_wp_at' P p s"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma unmapPageTable_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
    unmapPageTable aa ba word \<lbrace>\<lambda>x a. vs_valid_duplicates' (ksPSpace a)\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add:unmapPageTable_def)
   apply (wp|wpc|simp)+
      apply (wp storePDE_no_duplicates')+
   apply simp
  apply (simp add:pageTableMapped_def)
   apply (wp getPDE_wp |wpc|simp)+
   apply (rule hoare_post_imp_R[where Q' = "\<lambda>r s. vs_valid_duplicates' (ksPSpace s)"])
    apply wp
   apply (clarsimp simp:ko_wp_at'_def
     obj_at'_real_def projectKO_opt_pde)
   apply (clarsimp simp:vs_entry_align_def
     split:arch_kernel_object.splits
     ARM_H.pde.split Structures_H.kernel_object.splits)
  apply simp
  done

crunch valid_duplicates'[wp]:
 deleteASID "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunches deleteASIDPool, unbindNotification, prepareThreadDelete, unbindFromSC,
         schedContextUnbindAllTCBs, schedContextZeroRefillMax, schedContextUnbindYieldFrom,
         schedContextUnbindReply
  for valid_duplicates'[wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma archFinaliseCap_valid_duplicates'[wp]:
  "\<lbrace>valid_objs' and pspace_aligned' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
    and (valid_cap' (capability.ArchObjectCap arch_cap))\<rbrace>
  Arch.finaliseCap arch_cap is_final
  \<lbrace>\<lambda>ya a. vs_valid_duplicates' (ksPSpace a)\<rbrace>"
  apply (case_tac arch_cap; clarsimp simp: ARM_H.finaliseCap_def isPageCap_def isPageTableCap_def
                                           isPageDirectoryCap_def isASIDPoolCap_def)
      apply (intro conjI | clarsimp | wpsimp simp: valid_cap'_def)+
  done

lemma finaliseCap_valid_duplicates'[wp]:
  "\<lbrace>valid_objs' and pspace_aligned' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
  and (valid_cap' cap)\<rbrace>
  finaliseCap cap call final \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (cases cap; simp add: isCap_simps finaliseCap_def)
               apply (wpsimp wp: crunch_wps hoare_vcg_all_lift
                             simp: crunch_simps split: option.splits
                      | rule conjI)+
  done

crunch valid_duplicates'[wp]:
  capSwapForDelete "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  cteMove "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  cancelBadgedSends "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps filterM_preserved simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  invalidateTLBByASID "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps filterM_preserved simp: crunch_simps unless_def)

declare withoutPreemption_lift [wp del]

lemma valid_duplicates_finalise_prop_stuff:
  "no_cte_prop (vs_valid_duplicates' \<circ> ksPSpace) = vs_valid_duplicates' \<circ> ksPSpace"
  "finalise_prop_stuff (vs_valid_duplicates' \<circ> ksPSpace)"
  by (simp_all add: no_cte_prop_def finalise_prop_stuff_def
                    setCTE_valid_duplicates' o_def)

lemma finaliseSlot_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> vs_valid_duplicates' (ksPSpace s) \<and> sch_act_simple s
    \<and> (\<not> exposed \<longrightarrow> ex_cte_cap_to' slot s) \<rbrace>
  finaliseSlot slot exposed
  \<lbrace>\<lambda>_ s. invs' s \<and> vs_valid_duplicates' (ksPSpace s) \<and> sch_act_simple s \<rbrace>"
  unfolding finaliseSlot_def
  apply (rule validE_valid, rule hoare_pre,
    rule hoare_post_impErr, rule use_spec)
     apply (rule finaliseSlot_invs'[where p=slot and slot=slot and Pr="vs_valid_duplicates' o ksPSpace"])
      apply (simp_all add: valid_duplicates_finalise_prop_stuff)
   apply (wp | simp add: o_def)+
   apply (auto dest: cte_wp_at_valid_objs_valid_cap')
  done

lemma cteDelete_valid_duplicates':
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and sch_act_simple and K ex\<rbrace>
  cteDelete ptr ex
  \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cteDelete_def whenE_def split_def)
  apply (rule hoare_pre, wp finaliseSlot_invs)
   apply simp
   apply (rule valid_validE)
   apply (rule hoare_post_imp[OF _ finaliseSlot_valid_duplicates'])
   apply simp
  apply simp
  done

lemma cteRevoke_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. invs' s
        \<and> vs_valid_duplicates' (ksPSpace s)
        \<and> sch_act_simple s \<rbrace>
    cteRevoke cte
  \<lbrace>\<lambda>_ s. invs' s
       \<and> vs_valid_duplicates' (ksPSpace s)
       \<and> sch_act_simple s \<rbrace>"
  apply (rule cteRevoke_preservation)
   apply (wp cteDelete_invs' cteDelete_valid_duplicates' cteDelete_sch_act_simple)
     apply (fastforce simp: cteDelete_def sch_act_simple_def)+
  done

lemma mapM_x_storePTE_invalid_whole:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<and>
  s \<turnstile>' capability.ArchObjectCap (arch_capability.PageTableCap word option) \<and>
  pspace_aligned' s\<rbrace>
  mapM_x (swp storePTE ARM_H.pte.InvalidPTE)
  [word , word + 2 ^ pteBits .e. word + 2 ^ ptBits - 1]
  \<lbrace>\<lambda>y s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (wp mapM_x_storePTE_update_helper[where word = word and sz = ptBits and ptr = word])
  apply (clarsimp simp: valid_cap'_def capAligned_def pageBits_def ptBits_def objBits_simps
                        archObjSize_def pteBits_def)
  apply (simp add: mask_def field_simps pteBits_def)
  done

crunch valid_objs'[wp]:
  invalidateTLBByASID valid_objs'
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch pspace_aligned'[wp]:
  invalidateTLBByASID pspace_aligned'
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch valid_cap'[wp]:
  isFinalCapability "\<lambda>s. valid_cap' cap s"
  (wp: crunch_wps filterM_preserved simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  sendSignal "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps)

lemma invokeIRQControl_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<rbrace> performIRQControl a
   \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  unfolding performIRQControl_def by (wpsimp simp: ARM_H.performIRQControl_def)

crunch valid_duplicates'[wp]: InterruptDecls_H.invokeIRQHandler "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"

lemma invokeCNode_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> sch_act_simple s \<and> vs_valid_duplicates' (ksPSpace s)
  \<and> valid_cnode_inv' cinv s\<rbrace> invokeCNode cinv
  \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (case_tac cinv)
        apply (clarsimp simp add:invokeCNode_def | wp | intro conjI)+
       apply (rule valid_validE)
       apply (rule hoare_post_imp[OF _ cteRevoke_valid_duplicates'])
       apply simp
      apply (simp add:invs_valid_objs' invs_pspace_aligned')
     apply (clarsimp simp add:invokeCNode_def | wp | intro conjI)+
    apply (rule hoare_pre)
    apply (wp hoare_unless_wp | wpc | simp)+
   apply (simp add:invokeCNode_def)
  apply (simp add:cteDelete_def invokeCNode_def)
  apply (wp getSlotCap_inv hoare_drop_imp | simp add:locateSlot_conv whenE_def split_def | wpc)+
  apply (rule valid_validE)
   apply (rule hoare_post_imp[OF _ finaliseSlot_valid_duplicates'])
   apply simp
  apply (simp add:invs_valid_objs' invs_pspace_aligned')
  done

lemma getObject_pte_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::pte. P and ko_at' t r\<rbrace>"
  apply (wp getObject_ko_at)
  apply (auto simp: objBits_simps archObjSize_def pteBits_def)
  done

lemma getObject_pde_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::pde. P and ko_at' t r\<rbrace>"
  apply (wp getObject_ko_at)
  apply (auto simp: objBits_simps archObjSize_def pdeBits_def)
  done

lemma performPageInvocation_valid_duplicates'[wp]:
  "\<lbrace>invs' and valid_arch_inv' (invocation.InvokePage page_invocation)
  and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
    performPageInvocation page_invocation
    \<lbrace>\<lambda>y a. vs_valid_duplicates' (ksPSpace a)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (case_tac page_invocation)
  \<comment> \<open>PageFlush\<close>
     apply (simp_all add:performPageInvocation_def pteCheckIfMapped_def pdeCheckIfMapped_def)
     apply ((wp|simp|wpc)+)[2]
   \<comment> \<open>PageMap\<close>
   apply (clarsimp simp: pteCheckIfMapped_def pdeCheckIfMapped_def)
   apply (clarsimp simp:valid_pde_slots'_def valid_page_inv'_def
       valid_slots_duplicated'_def valid_arch_inv'_def )
   apply (rename_tac word1 cap word2 sum)
   apply (case_tac sum)
    apply (case_tac a)
    apply (case_tac aa)
      apply (clarsimp simp: pteCheckIfMapped_def)
      apply (wp mapM_x_mapM_valid | wpc | simp)+
        apply (clarsimp simp:valid_slots_duplicated'_def mapM_x_singleton)+
        apply (rule PageTableDuplicates.storePTE_no_duplicates', rule getPTE_wp)
      apply (wp hoare_vcg_all_lift hoare_drop_imps)
      apply (simp add:vs_entry_align_def)+
     apply (clarsimp simp: pteCheckIfMapped_def)
     apply (wp mapM_x_mapM_valid | simp)+
       apply (rule_tac sz = 6 and ptr = "p && ~~ mask ptBits" and word = p in
         mapM_x_storePTE_update_helper)
      apply (wp getPTE_wp hoare_vcg_all_lift hoare_drop_imps)+
     apply (simp add:ptBits_def pageBits_def)+
     apply (simp add:invs_pspace_aligned')
    apply simp
    apply (clarsimp simp:mapM_singleton pteCheckIfMapped_def)
    apply (wp PageTableDuplicates.storePTE_no_duplicates' getPTE_wp hoare_drop_imps | simp)+
      apply (simp add:vs_entry_align_def)+
   apply (clarsimp simp: pdeCheckIfMapped_def)
   apply (case_tac a)
      apply (clarsimp simp:valid_arch_inv'_def
          valid_page_inv'_def valid_slots'_def
          valid_slots_duplicated'_def mapM_singleton)
      apply (wp PageTableDuplicates.storePDE_no_duplicates' getPDE_wp hoare_drop_imps | simp)+
        apply (simp add:vs_entry_align_def)+
     apply (clarsimp simp:valid_arch_inv'_def
          valid_page_inv'_def valid_slots'_def
          valid_slots_duplicated'_def mapM_singleton)
     apply (wp PageTableDuplicates.storePDE_no_duplicates' getPDE_wp hoare_drop_imps | simp)+
       apply (simp add:vs_entry_align_def)+
    apply (clarsimp simp:valid_arch_inv'_def
          valid_page_inv'_def valid_slots'_def
          valid_slots_duplicated'_def mapM_singleton)
    apply (wp PageTableDuplicates.storePDE_no_duplicates' getPDE_wp hoare_drop_imps | simp)+
      apply (simp add:vs_entry_align_def)+
   apply (clarsimp simp:valid_arch_inv'_def
          valid_page_inv'_def valid_slots'_def
          valid_slots_duplicated'_def mapM_x_singleton)
   apply (wp mapM_x_mapM_valid | simp)+
     apply (rule_tac sz = 6 and ptr = "p && ~~ mask pdBits" and word = p
          in mapM_x_storePDE_update_helper)
    apply wp+
      apply (simp add:pageBits_def pdBits_def ptBits_def)+
    apply (simp add:invs_pspace_aligned')+
  apply clarsimp
  apply (rule hoare_pre)
   apply (wp |wpc |simp)+
  apply (clarsimp simp:valid_page_inv'_def
      valid_arch_inv'_def valid_cap'_def invs_valid_objs' invs_pspace_aligned')
  done

lemma placeASIDPool_valid_duplicates'[wp]:
  notes blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  shows "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<and> pspace_no_overlap' ptr pageBits s
   \<and> is_aligned ptr pageBits \<and> pspace_aligned' s\<rbrace>
  placeNewObject' ptr (KOArch (KOASIDPool makeObject)) 0
  \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:placeNewObject'_def)
  apply (wp hoare_unless_wp | wpc |
    simp add:alignError_def split_def)+
  apply (subgoal_tac "vs_valid_duplicates' (\<lambda>a. if a = ptr then Some (KOArch (KOASIDPool makeObject)) else ksPSpace s a)")
   apply fastforce
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp simp: vs_entry_align_def
         foldr_upd_app_if[unfolded data_map_insert_def[symmetric]])
  apply (clarsimp split:option.splits
         simp:foldr_upd_app_if[unfolded data_map_insert_def[symmetric]]
         vs_entry_align_def vs_ptr_align_def)
  apply (rule conjI)
   apply clarsimp
   apply (subgoal_tac "x \<in> obj_range' x x2")
    apply (subgoal_tac "x\<in> {ptr .. ptr + 2 ^ 12 - 1}")
     apply (drule(2) pspace_no_overlapD3')
      apply (simp add:pageBits_def)
      apply blast
    apply (simp add: pageBits_def
     split : ARM_H.pte.splits ARM_H.pde.splits
     arch_kernel_object.splits Structures_H.kernel_object.splits )
     apply (drule mask_out_first_mask_some[where m = 12])
      apply simp
     apply (clarsimp simp:mask_lower_twice field_simps blah word_and_le2)
     apply (rule order_trans[OF and_neg_mask_plus_mask_mono[where n = 12]])
     apply (simp add:mask_def)
    apply (drule mask_out_first_mask_some[where m = 12])
     apply simp
    apply (clarsimp simp:mask_lower_twice field_simps blah word_and_le2)
    apply (rule order_trans[OF and_neg_mask_plus_mask_mono[where n = 12]])
    apply (simp add:mask_def)
   apply (simp add:obj_range'_def blah)
   apply (rule is_aligned_no_overflow)
   apply (drule(2) pspace_alignedD')
  apply clarsimp
  apply (drule valid_duplicates'_D)
     apply (simp add:vs_entry_align_def vs_ptr_align_def)+
  done

lemma performArchInvocation_valid_duplicates':
  "\<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p
    and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
     Arch.performInvocation ai
   \<lbrace>\<lambda>reply s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: ARM_H.performInvocation_def performARMMMUInvocation_def)
  apply (cases ai, simp_all)
      apply (rename_tac page_table_invocation)
      apply (case_tac page_table_invocation)
       apply (rule hoare_name_pre_state)
       apply (clarsimp simp:valid_arch_inv'_def valid_pti'_def isCap_simps
              cte_wp_at_ctes_of is_arch_update'_def isPageTableCap_def
              split:arch_capability.splits)
       apply (clarsimp simp: performPageTableInvocation_def)
       apply (rule hoare_pre)
        apply (simp | wp getSlotCap_inv mapM_x_storePTE_invalid_whole[unfolded swp_def]
           | wpc)+
       apply fastforce
      apply (rule hoare_name_pre_state)
      apply (clarsimp simp:valid_arch_inv'_def isCap_simps valid_pti'_def
        cte_wp_at_ctes_of is_arch_update'_def isPageTableCap_def
        split:arch_capability.splits)
      apply (clarsimp simp: performPageTableInvocation_def)
      apply (wp storePDE_no_duplicates' | simp)+
     apply (rename_tac page_directory_invocation)
     apply (case_tac page_directory_invocation,
            simp_all add:performPageDirectoryInvocation_def)[]
      apply (wp+, simp)
     apply (wp)+
      apply simp
     apply simp
    apply(wp, simp)
   apply (rename_tac asidcontrol_invocation)
   apply (case_tac asidcontrol_invocation)
   apply (simp add:performASIDControlInvocation_def )
   apply (clarsimp simp:valid_aci'_def valid_arch_inv'_def)
   apply (rule hoare_name_pre_state)
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (case_tac ctea,clarsimp)
   apply (frule(1) ctes_of_valid_cap'[OF _ invs_valid_objs'])
   apply (wp static_imp_wp|simp)+
       apply (simp add:placeNewObject_def)
       apply (wp |simp add:alignError_def unless_def|wpc)+
      apply (wp updateFreeIndex_pspace_no_overlap' hoare_drop_imp
        getSlotCap_cte_wp_at deleteObject_no_overlap
        deleteObjects_invs_derivatives[where p="makePoolParent (case ai of InvokeASIDControl i \<Rightarrow> i)"]
        deleteObject_no_overlap
        deleteObjects_cte_wp_at')+
   apply (clarsimp simp:cte_wp_at_ctes_of)
   apply (strengthen refl ctes_of_valid_cap'[mk_strg I E])
   apply (clarsimp simp: conj_comms valid_cap_simps' capAligned_def
                         descendants_range'_def2 empty_descendants_range_in')
   apply (intro conjI; clarsimp)
   apply (drule(1) cte_cap_in_untyped_range, fastforce simp:cte_wp_at_ctes_of, simp_all)[1]
    apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
   apply clarsimp
  apply (rename_tac asidpool_invocation)
  apply (case_tac asidpool_invocation)
  apply (clarsimp simp:performASIDPoolInvocation_def)
  apply (wp | simp)+
  done

crunches restart
  for valid_duplicates'[wp]: "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (wp: crunch_wps)

crunches setPriority, setMCPriority
  for valid_duplicates'[wp]: "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (ignore: threadSet
       wp: setObject_ksInterrupt updateObject_default_inv crunch_wps
     simp: crunch_simps)

crunches installTCBCap, installThreadBuffer
  for valid_duplicates'[wp]: "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (wp:  crunch_wps checkCap_inv
   simp: crunch_simps getThreadVSpaceRoot_def getThreadFaultHandlerSlot_def
         getThreadTimeoutHandlerSlot_def
   ignore: checkCapAt)

lemma tc_caps_valid_duplicates':
  "\<lbrace>invs' and sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    tcb_at' t and ex_nonz_cap_to' t and
    case_option \<top> (valid_cap' o fst) croot and
    K (case_option True (isCNodeCap o fst) croot) and
    case_option \<top> (valid_cap' o fst) vroot and
    K (case_option True (isValidVTableRoot o fst) vroot) and
    case_option \<top> (valid_cap' o fst) fault_h and
    K (case_option True (isValidFaultHandler o fst) fault_h) and
    case_option \<top> (valid_cap' o fst) timeout_h and
    K (case_option True (isValidFaultHandler o fst) timeout_h) and
    case_option \<top> (valid_cap') (case_option None (case_option None (Some o fst) o snd) ipcb) and
    K (case_option True isArchObjectCap (case_option None (case_option None (Some o fst) o snd) ipcb))
    and K (case_option True (swp is_aligned msg_align_bits o fst) ipcb)\<rbrace>
      invokeTCB (ThreadControlCaps t sl fault_h timeout_h croot vroot ipcb)
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: invokeTCB_def)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift
                    installTCBCap_invs' installTCBCap_sch_act_simple)
  apply (fastforce simp: isValidFaultHandler_def isCap_simps isValidVTableRoot_def)
  done

crunches schedContextBindTCB
  for valid_duplicates'[wp]: "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"

lemma tc_sched_valid_duplicates':
  "\<lbrace>invs' and sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    tcb_at' t and ex_nonz_cap_to' t and
    case_option \<top> (valid_cap' o fst) sc_fh and
    K (valid_option_prio pri) and
    K (valid_option_prio mcp)\<rbrace>
      invokeTCB  (ThreadControlSched t sl sc_fh pri mcp sc_opt)
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by (wpsimp simp: mapTCBPtr_def stateAssertE_def invokeTCB_def wp: hoare_drop_imps)

crunches performTransfer, unbindNotification, bindNotification, setDomain
  for valid_duplicates'[wp]: "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (ignore: threadSet wp: setObject_ksInterrupt updateObject_default_inv
     simp: crunch_simps)


lemma invokeTCB_valid_duplicates'[wp]:
  "\<lbrace>invs' and sch_act_simple and ct_in_state' runnable' and tcb_inv_wf' ti and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
     invokeTCB ti
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (case_tac ti; simp only:)
          apply (simp add: invokeTCB_def)
          apply wp
          apply (clarsimp simp: invs'_def valid_state'_def
                         dest!: global'_no_ex_cap)
         apply (simp add: invokeTCB_def)
         apply wp
         apply (clarsimp simp: invs'_def valid_state'_def
                        dest!: global'_no_ex_cap)
        apply (wpsimp wp: tc_caps_valid_duplicates' split: option.splits)
       apply (wpsimp wp: tc_sched_valid_duplicates')
      apply (simp add:invokeTCB_def | wp mapM_x_wp' | intro impI conjI | wpc)+
  done

crunches invokeSchedContext, invokeSchedControlConfigureFlags
  for valid_duplicates'[wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (simp: crunch_simps wp: crunch_wps hoare_vcg_all_lift)

lemma performInvocation_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<and> invs' s \<and> sch_act_simple s
    \<and> valid_invocation' i s \<and> ct_active' s\<rbrace>
  RetypeDecls_H.performInvocation isBlocking isCall canDonate i
  \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp: performInvocation_def)
  apply (simp add: ct_in_state'_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply wpc
              apply (wpsimp wp: performArchInvocation_valid_duplicates'
                          simp: stateAssertE_def stateAssert_def)+
  apply (cases i)
             apply (clarsimp simp: simple_sane_strg sch_act_simple_def ct_in_state'_def
                        ct_active_runnable'[unfolded ct_in_state'_def]
                    | wp tcbinv_invs' arch_performInvocation_invs'
                    | rule conjI
                    | erule active_ex_cap')+
  apply simp
  done

lemma hi_valid_duplicates'[wp]:
  "\<lbrace>invs' and sch_act_simple and ct_active'
    and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
      handleInvocation isCall isBlocking canDonate firstPhase cptr
   \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s) \<rbrace>"
  apply (simp add: handleInvocation_def split_def
                   ts_Restart_case_helper')
  apply (wpsimp wp: syscall_valid' setThreadState_nonqueued_state_update rfk_invs' ct_in_state'_set
                    hoare_drop_imp)
  apply (fastforce simp add: tcb_at_invs' ct_in_state'_def
                             simple_sane_strg
                             sch_act_simple_def
                      elim!: pred_tcb'_weakenE st_tcb_ex_cap''
                       dest: st_tcb_at_idle_thread')+
  done

crunches activateIdleThread, schedContextCompleteYieldTo
  for valid_duplicates' [wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (ignore: setNextPC threadSet simp:crunch_simps)

lemma handleInterrupt_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  handleInterrupt irq \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: handleInterrupt_def)
  apply (rule conjI; rule impI)
   apply (wp hoare_vcg_all_lift hoare_drop_imps
             threadSet_pred_tcb_no_state getIRQState_inv haskell_fail_wp
          |wpc|simp add: handleReservedIRQ_def maskIrqSignal_def)+
  done

crunches awaken
  for valid_duplicates'[wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps)

crunch valid_duplicates' [wp]:
  schedule "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (ignore: setNextPC clearExMonitor threadSet simp: crunch_simps
   wp: hoare_drop_imps)

lemma activate_sch_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
     activateThread \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: activateThread_def getCurThread_def
             cong: if_cong Structures_H.thread_state.case_cong)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (wpsimp wp: threadGet_wp hoare_drop_imps)
  by (fastforce simp: obj_at'_def)

crunches receiveSignal, receiveIPC, handleYield, "VSpace_H.handleVMFault", handleHypervisorFault,
         lookupReply, checkBudgetRestart
  for valid_duplicates'[wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps)

lemma hs_valid_duplicates'[wp]:
  "\<lbrace>invs' and ct_active' and sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
  handleSend blocking \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule validE_valid)
  apply (simp add: handleSend_def getCapReg_def)
  apply (wp | simp)+
  done

lemma hc_valid_duplicates'[wp]:
  "\<lbrace>invs' and ct_active' and sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
     handleCall
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by (simp add: handleCall_def getCapReg_def | wp)+

lemma handleRecv_valid_duplicates'[wp]:
  "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
  handleRecv isBlocking canDonate \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: handleRecv_def cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply wp
      apply ((wp getNotification_wp | wpc | simp add: whenE_def split del: if_split)+)[1]
     apply (rule_tac Q="\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)" in hoare_post_impErr[rotated])
       apply (clarsimp simp: isCap_simps sch_act_sane_not)
      apply assumption
     apply (wp)+
  apply (auto elim: st_tcb_ex_cap'' pred_tcb'_weakenE
             dest!: st_tcb_at_idle_thread'
              simp: ct_in_state'_def sch_act_sane_def)
  done

lemma checkBudget_true:
  "\<lbrace>P\<rbrace> checkBudget \<lbrace>\<lambda>rv s. rv \<longrightarrow> P s\<rbrace>"
  unfolding checkBudget_def
  apply wpsimp
  apply (wpsimp wp: hoare_drop_imp)
  apply wpsimp
  apply (wpsimp wp: hoare_drop_imp)+
  done

lemma checkBudgetRestart_true:
  "\<lbrace>P\<rbrace> checkBudgetRestart \<lbrace>\<lambda>rv s. rv \<longrightarrow> P s\<rbrace>"
  unfolding checkBudgetRestart_def
  apply wpsimp
  apply (rule_tac Q="\<lambda>rv s. rv \<longrightarrow> P s" in hoare_strengthen_post[rotated], clarsimp)
  apply (wpsimp wp: checkBudget_true)+
  done

lemma checkBudgetRestart_gen:
  "\<lbrace>R\<rbrace> checkBudgetRestart \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow>
   \<lbrace>P and R\<rbrace> checkBudgetRestart \<lbrace>\<lambda>rv s. (rv \<longrightarrow> P s) \<and> (\<not>rv \<longrightarrow> Q s)\<rbrace>"
  apply (wpsimp wp: checkBudgetRestart_true)
  apply (wpsimp wp: hoare_drop_imp)+
  done

lemma setCurTime_invs'[wp]:
  "setCurTime v \<lbrace>invs'\<rbrace>"
  unfolding setCurTime_def
  apply wp
  apply (clarsimp simp: invs'_def cur_tcb'_def valid_state'_def valid_machine_state'_def
                        valid_irq_node'_def valid_release_queue_def valid_release_queue'_def)
  apply (clarsimp simp: ct_not_inQ_def valid_dom_schedule'_def ct_idle_or_in_cur_domain'_def
                        tcb_in_cur_domain'_def valid_queues'_def valid_queues_def valid_bitmapQ_def
                        bitmapQ_def valid_queues_no_bitmap_def bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def)
  done

lemma updateTimeStamp_invs'[wp]:
  "updateTimeStamp \<lbrace>invs'\<rbrace>"
  unfolding updateTimeStamp_def
  by (wpsimp wp: dmo_invs'_simple simp: getCurrentTime_def no_irq_def)

lemma updateTimeStamp_sch_act_simple[wp]:
  "updateTimeStamp \<lbrace>sch_act_simple\<rbrace>"
  unfolding updateTimeStamp_def sch_act_simple_def
  by (wpsimp wp: dmo_invs'_simple simp: setCurTime_def)

crunches updateTimeStamp
  for ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and pred_tcb_at'[wp]: "pred_tcb_at' p P t"
  and ksPSpace[wp]: "\<lambda>s. P (ksPSpace s)"
  and tcb_at'[wp]: "tcb_at' t"

crunches getCapReg, refillCapacity
  for inv[wp]: P

lemma handleEvent_valid_duplicates':
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    sch_act_simple and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)\<rbrace>
   handleEvent e
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (case_tac e; simp add: handleEvent_def)
       apply (rename_tac syscall, case_tac syscall)
  by (wpsimp wp: checkBudgetRestart_gen ct_in_state_thread_state_lift' |
      erule active_from_running')+

lemma callKernel_valid_duplicates':
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
    (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)\<rbrace>
   callKernel e
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: callKernel_def mcsIRQ_def)
  apply (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2 handleEvent_valid_duplicates')
  done

end

end
