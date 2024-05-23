(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory PageTableDuplicates
imports Syscall_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma set_ntfn_valid_duplicate' [wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setNotification ep v  \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:setNotification_def)
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = v,simplified])
  apply (clarsimp simp:updateObject_default_def assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def split:if_splits option.splits)
   apply (rule_tac ko = ba in valid_duplicates'_non_pd_pt_I)
       apply simp+
  apply (rule_tac ko = ba in valid_duplicates'_non_pd_pt_I)
      apply simp+
  done

crunch valid_duplicates' [wp]: cteInsert "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (wp: crunch_wps)

crunch valid_duplicates'[wp]: setupReplyMaster "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (wp: crunch_wps simp: crunch_simps)


(* we need the following lemma in Syscall_R *)
crunch inv[wp]: getRegister "P"

lemma doMachineOp_ksPSpace_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksPSpace s)\<rbrace> doMachineOp f \<lbrace>\<lambda>ya s. P (ksPSpace s)\<rbrace>"
  by (simp add:doMachineOp_def split_def | wp)+

lemma setEP_valid_duplicates'[wp]:
  " \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setEndpoint a b \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:setEndpoint_def)
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = b,simplified])
  apply (clarsimp simp:updateObject_default_def assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def typeError_def
    split:if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

lemma setTCB_valid_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setObject a (tcb::tcb) \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = tcb,simplified])
  apply (clarsimp simp:updateObject_default_def assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def typeError_def
    split:if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

crunches threadSet, setBoundNotification
  for valid_duplicates'[wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt updateObject_default_inv)

lemma tcbSchedEnqueue_valid_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  tcbSchedEnqueue a \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by (simp add:tcbSchedEnqueue_def unless_def setQueue_def | wp | wpc)+

crunch valid_duplicates'[wp]: rescheduleRequired "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt updateObject_default_inv)

lemma getExtraCptrs_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. P (ksPSpace s)\<rbrace> getExtraCPtrs a i  \<lbrace>\<lambda>r s. P (ksPSpace s)\<rbrace>"
  apply (simp add:getExtraCPtrs_def)
  apply (rule hoare_pre)
  apply (wpc|simp|wp mapM_wp')+
  done

crunch valid_duplicates'[wp]: getExtraCPtrs "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt asUser_inv updateObject_default_inv)

crunch valid_duplicates'[wp]: lookupExtraCaps "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt asUser_inv updateObject_default_inv mapME_wp)

crunch valid_duplicates'[wp]: setExtraBadge "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: setObject_ksInterrupt asUser_inv updateObject_default_inv mapME_wp)

crunch valid_duplicates'[wp]: getReceiveSlots "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (simp: unless_def getReceiveSlots_def
     wp: setObject_ksInterrupt asUser_inv updateObject_default_inv mapME_wp)

lemma transferCapsToSlots_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  transferCapsToSlots ep buffer n caps slots mi
  \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by (rule transferCapsToSlots_pres1; wp)

crunch valid_duplicates'[wp]: transferCaps "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (simp: unless_def
     wp: setObject_ksInterrupt asUser_inv updateObject_default_inv mapME_wp)

crunch valid_duplicates'[wp]: sendFaultIPC "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (ignore: transferCapsToSlots
       wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at'
     simp: zipWithM_x_mapM ball_conj_distrib)

crunch valid_duplicates'[wp]: handleFault "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (ignore: transferCapsToSlots
       wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at'
     simp: zipWithM_x_mapM ball_conj_distrib)

crunch valid_duplicates'[wp]: replyFromKernel "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (ignore: transferCapsToSlots
       wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at'
     simp: zipWithM_x_mapM ball_conj_distrib)

crunch valid_duplicates'[wp]: insertNewCap "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (ignore: transferCapsToSlots
       wp: crunch_wps hoare_vcg_const_Ball_lift get_rs_cte_at'
     simp: zipWithM_x_mapM ball_conj_distrib)

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
  apply (wp hoare_drop_imps | simp add:split_def updateObject_default_def)+
  apply clarsimp
  apply (intro conjI ballI)
   apply (drule(1) bspec)
   apply (clarsimp simp:typ_at'_def ko_wp_at'_def objBits_simps archObjSize_def lookupAround2_known1
                  dest!:koTypeOf_pte)
   apply (simp add:ps_clear_def dom_fun_upd2[unfolded fun_upd_def])
  apply (erule rsubst[where P=Q])
  apply (rule ext)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def lookupAround2_known1)
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
   p && ~~ mask ptBits = ptr; is_aligned p sz; 3 \<le> sz\<rbrakk> \<Longrightarrow>
  set [p , p + 8 .e. p + mask sz] =
  {x. pte_at' x s \<and> x && ~~ mask sz = p}"
  apply (clarsimp simp:page_table_at'_def ptBits_def)
  apply (rule set_eqI)
  apply (rule iffI)
   apply (subst (asm) upto_enum_step_subtract)
    apply (simp add:field_simps mask_def)
    apply (erule is_aligned_no_overflow)
   apply (clarsimp simp:set_upto_enum_step_8
           image_def pageBits_def)
   apply (drule_tac x= "((p && mask 12) >> 3) + xb" in spec)
   apply (erule impE)
    apply (rule is_aligned_plus_bound[where lz = 9 and sz = "sz - 3" ,simplified])
        apply (rule is_aligned_shiftr)
        apply (rule is_aligned_andI1)
        apply (subgoal_tac "sz - 3 + 3 = sz")
         apply simp
        apply simp
       apply (simp add:field_simps vspace_bits_defs)
      apply (simp add: vspace_bits_defs shiftr_mask2)
      apply (simp add:mask_def not_less word_bits_def)
     apply (rule shiftr_less_t2n[where m = 9,simplified])
     apply (rule le_less_trans[OF _ mask_lt_2pn])
      apply (simp add:word_and_le1)
     apply simp
    apply (simp add:word_bits_def vspace_bits_defs)
   apply (simp add:word_shiftl_add_distrib)
   apply (subst (asm) shiftr_shiftl1)
    apply simp+
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 3])
    apply (rule is_aligned_weaken)
     apply (erule is_aligned_andI1)
    apply simp
   apply (simp add:mask_out_sub_mask field_simps)
   apply (clarsimp simp:typ_at'_def mask_add_aligned vspace_bits_defs
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
   apply (simp add: vspace_bits_defs mask_lt_2pn word_bits_def)
  apply (simp add:image_def)
  apply (rule_tac x = "x && mask sz" in bexI)
   apply (simp add:mask_out_sub_mask)
  apply (simp add:set_upto_enum_step_8 image_def)
  apply (rule_tac x = "x && mask sz >> 3" in bexI)
   apply (subst shiftr_shiftl1)
    apply simp
   apply simp
   apply (subst is_aligned_neg_mask_eq)
    apply (rule is_aligned_andI1)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def
      dest!: koTypeOf_pte)
    apply (drule pspace_alignedD')
     apply simp
    apply (simp add:vspace_bits_defs objBits_simps archObjSize_def)
   apply simp
  apply clarsimp
  apply (rule le_shiftr)
  apply (simp add:word_and_le1)
  done

lemma page_directory_at_set_list:
  "\<lbrakk>page_directory_at' ptr s;pspace_aligned' s;sz \<le> pdBits;
   p && ~~ mask pdBits = ptr; is_aligned p sz; 3 \<le> sz\<rbrakk> \<Longrightarrow>
  set [p , p + 8 .e. p + mask sz] =
  {x. pde_at' x s \<and> x && ~~ mask sz = p}"
  apply (clarsimp simp:page_directory_at'_def pdBits_def)
  apply (rule set_eqI)
  apply (rule iffI)
   apply (subst (asm) upto_enum_step_subtract)
    apply (simp add:field_simps mask_def)
    apply (erule is_aligned_no_overflow)
   apply (clarsimp simp:set_upto_enum_step_8 vspace_bits_defs
           image_def pageBits_def)
   apply (drule_tac x= "((p && mask 14) >> 3) + xb" in spec)
   apply (erule impE)
    apply (rule is_aligned_plus_bound[where lz = 11 and sz = "sz - 3" ,simplified])
        apply (rule is_aligned_shiftr)
        apply (rule is_aligned_andI1)
        apply (subgoal_tac "sz - 3 + 3 = sz")
         apply simp
        apply simp
       apply (simp add:field_simps)
      apply (simp add:shiftr_mask2)
      apply (simp add:mask_def not_less word_bits_def)
     apply (rule shiftr_less_t2n[where m = 11,simplified])
     apply (rule le_less_trans[OF _ mask_lt_2pn])
      apply (simp add:word_and_le1)
     apply simp
    apply (simp add:word_bits_def)
   apply (simp add:word_shiftl_add_distrib)
   apply (subst (asm) shiftr_shiftl1)
    apply simp+
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 3])
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
   apply (simp add:mask_lt_2pn word_bits_def vspace_bits_defs)
  apply (simp add:image_def)
  apply (rule_tac x = "x && mask sz" in bexI)
   apply (simp add:mask_out_sub_mask)
  apply (simp add:set_upto_enum_step_8 image_def)
  apply (rule_tac x = "x && mask sz >> 3" in bexI)
   apply (subst shiftr_shiftl1)
    apply simp
   apply simp
   apply (subst is_aligned_neg_mask_eq)
    apply (rule is_aligned_andI1)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def
      dest!: koTypeOf_pde)
    apply (drule pspace_alignedD')
     apply simp
    apply (simp add:objBits_simps archObjSize_def vspace_bits_defs)
   apply simp
  apply clarsimp
  apply (rule le_shiftr)
  apply (simp add:word_and_le1)
  done

lemma page_table_at_pte_atD':
  "\<lbrakk>page_table_at' p s;is_aligned p' 3; p' && ~~ mask ptBits = p\<rbrakk> \<Longrightarrow> pte_at' p' s"
  apply (clarsimp simp:page_table_at'_def)
  apply (drule_tac x = "p' && mask ptBits >> 3" in spec)
  apply (erule impE)
   apply (rule shiftr_less_t2n[where m = 9,simplified])
   apply (rule le_less_trans[OF word_and_le1])
   apply (simp add:vspace_bits_defs mask_def)
  apply (subst (asm) shiftr_shiftl1)
   apply simp
  apply simp
  apply (subst (asm) is_aligned_neg_mask_eq[where n = 3])
   apply (simp add: is_aligned_andI1)
  apply (simp add:mask_out_sub_mask)
  done

lemma largePagePTEOffsets_bound:
  "(a, b) \<in> set (zip largePagePTEOffsets [0.e.0xF]) \<Longrightarrow> a < 128"
  apply (clarsimp simp: largePagePTEOffsets_def upto_enum_step_def vspace_bits_defs zip_map1)
  apply (drule in_set_zip1)
  apply clarsimp
  apply (rule word_less_power_trans2[where k=3 and m=7, simplified]; simp?)
  apply unat_arith
  done

lemma superSectionPDEOffsets_bound:
  "(a, b) \<in> set (zip superSectionPDEOffsets [0.e.0xF]) \<Longrightarrow> a < 128"
  apply (clarsimp simp: superSectionPDEOffsets_def upto_enum_step_def vspace_bits_defs zip_map1)
  apply (drule in_set_zip1)
  apply clarsimp
  apply (rule word_less_power_trans2[where k=3 and m=7, simplified]; simp?)
  apply unat_arith
  done

lemma mapM_x_storePTE_update_helper:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)
    \<and> pspace_aligned' s
    \<and> page_table_at' ptr s
    \<and> word && ~~ mask ptBits = ptr
    \<and> sz \<le> ptBits \<and> 7 \<le> sz
    \<and> is_aligned word sz
    \<and> xs = [word , word + 8 .e. word + (mask sz)]
  \<rbrace>
  mapM_x (swp storePTE InvalidPTE) xs
  \<lbrace>\<lambda>y s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (wp mapM_x_storePTE_updates)
  apply (clarsimp simp: )
  apply (frule(2) page_table_at_set_list[simplified vspace_bits_defs, simplified])
     apply simp+
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp split: option.splits kernel_object.split arch_kernel_object.split)
  apply (rule conjI)
   apply clarsimp
   apply (drule (2) valid_duplicates'_D)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply (rule conjI, clarsimp simp: vspace_bits_defs)
    apply (clarsimp simp: mask_lower_twice page_table_at'_def)
    apply (erule_tac x="(x >> 3) && mask 9" in allE)
    apply (clarsimp simp: and_mask_less'[of 9, simplified])
    apply (subgoal_tac "(x >> 3) && mask 9 << 3 = x && mask 12")
     apply (simp add: AND_NOT_mask_plus_AND_mask_eq)
    apply (subst aligned_shiftr_mask_shiftl)
     apply (drule (1) pspace_alignedD')
     apply (simp add: objBits_simps archObjSize_def vspace_bits_defs)
    apply simp
   apply (clarsimp simp: vspace_bits_defs mask_lower_twice)
   apply (drule (1) bspec, clarsimp)
   apply (clarsimp simp: mask_lower_twice)
   apply (subgoal_tac "x && ~~ mask 7 = (x && ~~ mask 7) + a && ~~ mask 7")
    apply (drule_tac p'="x && ~~ mask 7" in page_table_at_pte_atD')
      apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
     apply (simp add: vspace_bits_defs mask_lower_twice)
     apply (erule mask_out_first_mask_some_eq, simp)
    apply clarsimp
    apply (erule notE)
    apply (erule mask_out_first_mask_some_eq, simp)
    apply (subst neg_mask_add_aligned)
      apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
     apply (simp add: largePagePTEOffsets_bound)
    apply (simp add: mask_lower_twice)
  apply clarsimp
  apply (drule (2) valid_duplicates'_D)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply (rule conjI, clarsimp simp: vspace_bits_defs)
   apply (clarsimp simp: mask_lower_twice page_table_at'_def)
   apply (erule_tac x="(x >> 3) && mask 9" in allE)
   apply (clarsimp simp: and_mask_less'[of 9, simplified])
   apply (subgoal_tac "(x >> 3) && mask 9 << 3 = x && mask 12")
    apply (simp add: AND_NOT_mask_plus_AND_mask_eq)
   apply (subst aligned_shiftr_mask_shiftl)
    apply (drule (1) pspace_alignedD')
    apply (simp add: objBits_simps archObjSize_def vspace_bits_defs)
   apply simp
  apply (clarsimp simp: vspace_bits_defs mask_lower_twice)
  apply (drule (1) bspec, clarsimp)
  apply (clarsimp simp: mask_lower_twice)
  apply (subgoal_tac "x && ~~ mask 7 = (x && ~~ mask 7) + a && ~~ mask 7")
   apply (drule_tac p'="x && ~~ mask 7" in page_table_at_pte_atD')
     apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
    apply (simp add: vspace_bits_defs mask_lower_twice)
    apply (erule mask_out_first_mask_some_eq, simp)
   apply clarsimp
   apply (erule notE)
   apply (erule mask_out_first_mask_some_eq, simp)
  apply (subst neg_mask_add_aligned)
    apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
   apply (simp add: superSectionPDEOffsets_bound)
  apply (simp add: mask_lower_twice)
  done

lemma page_directory_at_pde_atD':
  "\<lbrakk>page_directory_at' p s;is_aligned p' 3; p' && ~~ mask pdBits = p\<rbrakk> \<Longrightarrow> pde_at' p' s"
  apply (clarsimp simp:page_directory_at'_def)
  apply (drule_tac x = "p' && mask pdBits >> 3" in spec)
  apply (erule impE)
   apply (rule shiftr_less_t2n[where m = 11,simplified])
   apply (rule le_less_trans[OF word_and_le1])
   apply (simp add:vspace_bits_defs mask_def)
  apply (subst (asm) shiftr_shiftl1)
   apply simp
  apply simp
  apply (subst (asm) is_aligned_neg_mask_eq[where n = 3])
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
  apply (wp hoare_drop_imps | simp add:split_def updateObject_default_def)+
  apply clarsimp
  apply (intro conjI ballI)
   apply (drule(1) bspec)
   apply (clarsimp simp:typ_at'_def ko_wp_at'_def objBits_simps archObjSize_def lookupAround2_known1
                  dest!:koTypeOf_pde)
   apply (simp add:ps_clear_def dom_fun_upd2[unfolded fun_upd_def])
  apply (erule rsubst[where P=Q])
  apply (rule ext)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def lookupAround2_known1)
  done

lemma mapM_x_storePDE_update_helper:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)
    \<and> pspace_aligned' s
    \<and> page_directory_at' ptr s
    \<and> word && ~~ mask pdBits = ptr
    \<and> sz \<le> pdBits \<and> 7 \<le> sz
    \<and> is_aligned word sz
    \<and> xs = [word , word + 8 .e. word + (mask sz)]
  \<rbrace>
  mapM_x (swp storePDE InvalidPDE) xs
  \<lbrace>\<lambda>y s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (wp mapM_x_storePDE_updates)
  apply (clarsimp simp: )
  apply (frule(2) page_directory_at_set_list[simplified vspace_bits_defs, simplified])
     apply simp+
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp split: option.splits kernel_object.split arch_kernel_object.split)
  apply (rule conjI)
   apply clarsimp
   apply (drule (2) valid_duplicates'_D)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply (rule conjI, clarsimp simp: vspace_bits_defs)
    apply (clarsimp simp: mask_lower_twice page_directory_at'_def)
    apply (erule_tac x="(x >> 3) && mask 11" in allE)
    apply (clarsimp simp: and_mask_less'[of 11, simplified])
    apply (subgoal_tac "(x >> 3) && mask 11 << 3 = x && mask 14")
     apply (simp add: AND_NOT_mask_plus_AND_mask_eq)
    apply (subst aligned_shiftr_mask_shiftl)
     apply (drule (1) pspace_alignedD')
     apply (simp add: objBits_simps archObjSize_def vspace_bits_defs)
    apply simp
   apply (clarsimp simp: vspace_bits_defs mask_lower_twice)
   apply (drule (1) bspec, clarsimp)
   apply (clarsimp simp: mask_lower_twice)
   apply (subgoal_tac "x && ~~ mask 7 = (x && ~~ mask 7) + a && ~~ mask 7")
    apply (drule_tac p'="x && ~~ mask 7" in page_directory_at_pde_atD')
      apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
     apply (simp add: vspace_bits_defs mask_lower_twice)
     apply (erule mask_out_first_mask_some_eq, simp)
    apply clarsimp
    apply (erule notE)
    apply (erule mask_out_first_mask_some_eq, simp)
    apply (subst neg_mask_add_aligned)
      apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
     apply (simp add: largePagePTEOffsets_bound)
    apply (simp add: mask_lower_twice)
  apply clarsimp
  apply (drule (2) valid_duplicates'_D)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply (rule conjI, clarsimp simp: vspace_bits_defs)
   apply (clarsimp simp: mask_lower_twice page_directory_at'_def)
   apply (erule_tac x="(x >> 3) && mask 11" in allE)
   apply (clarsimp simp: and_mask_less'[of 11, simplified])
   apply (subgoal_tac "(x >> 3) && mask 11 << 3 = x && mask 14")
    apply (simp add: AND_NOT_mask_plus_AND_mask_eq)
   apply (subst aligned_shiftr_mask_shiftl)
    apply (drule (1) pspace_alignedD')
    apply (simp add: objBits_simps archObjSize_def vspace_bits_defs)
   apply simp
  apply (clarsimp simp: vspace_bits_defs mask_lower_twice)
  apply (drule (1) bspec, clarsimp)
  apply (clarsimp simp: mask_lower_twice)
  apply (subgoal_tac "x && ~~ mask 7 = (x && ~~ mask 7) + a && ~~ mask 7")
   apply (drule_tac p'="x && ~~ mask 7" in page_directory_at_pde_atD')
     apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
    apply (simp add: vspace_bits_defs mask_lower_twice)
    apply (erule mask_out_first_mask_some_eq, simp)
   apply clarsimp
   apply (erule notE)
   apply (erule mask_out_first_mask_some_eq, simp)
  apply (subst neg_mask_add_aligned)
    apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
   apply (simp add: superSectionPDEOffsets_bound)
  apply (simp add: mask_lower_twice)
  done

lemma foldr_data_map_insert[simp]:
 "foldr (\<lambda>addr map a. if a = addr then Some b else map a)
 = foldr (\<lambda>addr. data_map_insert addr b)"
  apply (rule ext)+
  apply (simp add:data_map_insert_def[abs_def] fun_upd_def)
  done

definition
  "nondup_obj ko \<equiv> case ko of
     KOArch (KOPTE pte) \<Rightarrow> \<not>isLargePage pte
   | KOArch (KOPDE pde) \<Rightarrow> \<not>isSuperSection pde
   | _ \<Rightarrow> True"

lemma valid_duplicates'_insert_ko:
  "\<lbrakk> vs_valid_duplicates' m; is_aligned ptr (objBitsKO ko + us); objBitsKO ko + us < 32;
    nondup_obj ko; \<forall>x\<in> set (new_cap_addrs (2^us) ptr ko). m x = None \<rbrakk> \<Longrightarrow>
  vs_valid_duplicates' (foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs (2^us) ptr ko) m)"
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp simp: foldr_upd_app_if[folded data_map_insert_def])
  apply (rule conjI)
   apply (clarsimp simp: nondup_obj_def split: kernel_object.splits arch_kernel_object.splits)
  apply (clarsimp simp: option.splits)
  apply (clarsimp split: kernel_object.splits arch_kernel_object.splits)
  apply (rule conjI)
   apply (clarsimp simp: foldr_upd_app_if[folded data_map_insert_def])
   apply (drule (2) valid_duplicates'_D)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply fastforce
  apply (clarsimp simp: foldr_upd_app_if[folded data_map_insert_def])
  apply (drule (2) valid_duplicates'_D)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply fastforce
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
  "\<lbrakk> is_aligned ptr sz; pspace_aligned' s; vs_valid_duplicates' (ksPSpace s); nondup_obj ko;
     pspace_no_overlap' ptr sz s\<rbrakk> \<Longrightarrow>
   vs_valid_duplicates' (\<lambda>a. if a = ptr then Some ko else ksPSpace s a)"
  apply (subst vs_valid_duplicates'_def)
  apply clarsimp
  apply (intro conjI impI allI)
   apply (case_tac ko; simp add: nondup_obj_def)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp)
  apply (clarsimp split: option.splits)
  apply (drule(2) pspace_no_overlap_base')
  apply (clarsimp split: kernel_object.splits arch_kernel_object.splits)
  apply (rule conjI)
   apply clarsimp
   apply (drule(2) valid_duplicates'_D)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply fastforce
  apply clarsimp
  apply (drule(2) valid_duplicates'_D)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply fastforce
  done

lemma createObject_valid_duplicates'[wp]:
  "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and pspace_aligned' and pspace_distinct'
   and pspace_no_overlap' ptr (getObjectSize ty us)
   and K (is_aligned ptr (getObjectSize ty us))
   and K (ty = APIObjectType apiobject_type.CapTableObject \<longrightarrow> us < 28)\<rbrace>
  RetypeDecls_H.createObject ty ptr us d
  \<lbrace>\<lambda>xa s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add:createObject_def)
  apply (rule hoare_pre)
  apply (wpc | wp| simp add: ARM_HYP_H.createObject_def split del: if_split)+
         apply (simp add: placeNewObject_def placeNewDataObject_def
                          placeNewObject'_def split_def copyGlobalMappings_def
                     split del: if_split
           | wp unless_wp[where P="d"] unless_wp[where Q=\<top>]
           | wpc | simp add: alignError_def split del: if_split)+
  apply (intro conjI impI)
             apply clarsimp+
            apply (erule(2) valid_duplicates'_update)
             apply (clarsimp simp: nondup_obj_def)+
            apply (erule(2) valid_duplicates'_update)
             apply (clarsimp simp: nondup_obj_def)+
           apply ((clarsimp simp: new_cap_addrs_fold'[where n = "0x10",simplified]
            | (erule valid_duplicates'_insert_ko[where us = 4,simplified]
              , (simp add: toAPIType_def nondup_obj_def
                           APIType_capBits_def objBits_simps pageBits_def)+)[1]
            | rule none_in_new_cap_addrs[where us = 4,simplified,THEN bspec,rotated -1]
            | simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
         apply ((clarsimp simp: new_cap_addrs_fold'[where n = "0x10",simplified]
           | (erule valid_duplicates'_insert_ko[where us = 4,simplified]
             , (simp add: toAPIType_def nondup_obj_def
                          APIType_capBits_def objBits_simps pageBits_def)+)[1]
           | rule none_in_new_cap_addrs[where us = 4,simplified,THEN bspec,rotated -1]
           | simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
        apply ((clarsimp simp: new_cap_addrs_fold'[where n = "0x200",simplified]
          | (erule valid_duplicates'_insert_ko[where us = 9,simplified]
            , (simp add: toAPIType_def nondup_obj_def
                         APIType_capBits_def objBits_simps pageBits_def)+)[1]
          | rule none_in_new_cap_addrs[where us = 9,simplified,THEN bspec,rotated -1]
          | simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
       apply (clarsimp simp: new_cap_addrs_fold'[where n = "0x200",simplified])
       apply (erule valid_duplicates'_insert_ko[where us = 9,simplified])
          apply (simp add: toAPIType_def nondup_obj_def
                           APIType_capBits_def objBits_simps pageBits_def)+
       apply (rule none_in_new_cap_addrs[where us =9,simplified]
        ,(simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
      apply (clarsimp simp: new_cap_addrs_fold'[where n = "0x2000",simplified])
      apply (erule valid_duplicates'_insert_ko[where us = 13,simplified])
         apply (simp add: toAPIType_def nondup_obj_def
                          APIType_capBits_def objBits_simps pageBits_def)+
      apply (rule none_in_new_cap_addrs[where us =13,simplified]
       ,(simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
     apply (clarsimp simp: new_cap_addrs_fold'[where n = "0x2000",simplified])
     apply (erule valid_duplicates'_insert_ko[where us = 13,simplified])
       apply (simp add: ARM_HYP_H.toAPIType_def nondup_obj_def
                        APIType_capBits_def objBits_simps pageBits_def)+
     apply (rule none_in_new_cap_addrs[where us =13,simplified]
      ,(simp add: objBits_simps pageBits_def word_bits_conv)+)[1]
    apply (clarsimp simp: objBits_simps ptBits_def archObjSize_def pageBits_def)
   apply (cut_tac ptr=ptr in new_cap_addrs_fold'[where n = "0x200" and ko = "(KOArch (KOPTE makeObject))"
      ,simplified objBits_simps])
    apply simp
   apply (clarsimp simp: archObjSize_def pt_bits_def pte_bits_def)
   apply (erule valid_duplicates'_insert_ko[where us = 9,simplified])
      apply (simp add: toAPIType_def archObjSize_def nondup_obj_def makeObject_pte
                       APIType_capBits_def objBits_simps pageBits_def pte_bits_def
                split: ARM_HYP_H.pte.splits)+
    apply (rule none_in_new_cap_addrs[where us =9,simplified]
      ,(simp add: objBits_simps pageBits_def word_bits_conv archObjSize_def pte_bits_def)+)[1]
   apply (clarsimp simp: pd_bits_def pde_bits_def)
   apply (cut_tac ptr=ptr in new_cap_addrs_fold'[where n = "0x0800" and ko = "(KOArch (KOPDE makeObject))"
     ,simplified objBits_simps])
    apply simp
   apply (clarsimp simp: objBits_simps archObjSize_def pdBits_def pageBits_def pde_bits_def)
   apply (frule(2) retype_aligned_distinct'[where n = "0x0800" and ko = "KOArch (KOPDE makeObject)"])
    apply (simp add:objBits_simps archObjSize_def)
    apply (rule range_cover_rel[OF range_cover_full])
       apply simp
      apply (simp add:APIType_capBits_def word_bits_def pde_bits_def)+
   apply (frule(2) retype_aligned_distinct'(2)[where n = "2048" and ko = "KOArch (KOPDE makeObject)"])
    apply (simp add:objBits_simps archObjSize_def)
    apply (rule range_cover_rel[OF range_cover_full])
       apply simp
      apply (simp add:APIType_capBits_def word_bits_def pde_bits_def)+
   apply (subgoal_tac "vs_valid_duplicates'
                (foldr (\<lambda>addr. data_map_insert addr (KOArch (KOPDE makeObject)))
                  (map (\<lambda>n. ptr + (n << 3)) [0.e.0x7FF]) (ksPSpace s))")
     apply (simp add:APIType_capBits_def pdBits_def pageBits_def pde_bits_def pd_bits_def
     data_map_insert_def[abs_def])
    apply (clarsimp simp: archObjSize_def pdBits_def pageBits_def pdBits_def pd_bits_def pde_bits_def)
    apply (rule valid_duplicates'_insert_ko[where us = 11,simplified])
        apply (simp add: ARM_HYP_H.toAPIType_def archObjSize_def nondup_obj_def makeObject_pde
                       APIType_capBits_def objBits_simps pageBits_def pde_bits_def
                split: ARM_HYP_H.pde.splits)+
    apply (rule none_in_new_cap_addrs[where us =11,simplified],
           (simp add: objBits_simps pageBits_def word_bits_conv archObjSize_def pde_bits_def)+)[1]

   apply clarsimp
   apply (erule(2) valid_duplicates'_update)
    apply (clarsimp simp: nondup_obj_def)
   apply (clarsimp)
  apply (intro conjI impI allI)
     apply simp
     apply clarsimp
     apply (drule(2) valid_duplicates'_update) prefer 3
       apply fastforce
      apply (simp add: nondup_obj_def)
     apply simp
    apply clarsimp
    apply (drule(2) valid_duplicates'_update) prefer 3
      apply (fastforce simp: nondup_obj_def)+
   apply clarsimp
   apply (drule(2) valid_duplicates'_update) prefer 3
     apply (fastforce simp: nondup_obj_def)+
  apply (clarsimp simp:ARM_HYP_H.toAPIType_def word_bits_def
                 split:ARM_HYP_H.object_type.splits)
  apply (cut_tac ptr = ptr in new_cap_addrs_fold'[where n = "2^us"
   and ko = "(KOCTE makeObject)",simplified])
   apply (rule word_1_le_power)
   apply (clarsimp simp: word_bits_def)
  apply (drule_tac ptr = ptr and ko = "KOCTE makeObject" in
                   valid_duplicates'_insert_ko[where us = us,simplified])
      apply (simp add: APIType_capBits_def is_aligned_mask ARM_HYP_H.toAPIType_def
                split: ARM_HYP_H.object_type.splits)
     apply (simp add: objBits_simps')
    apply (simp add: nondup_obj_def)
   apply simp
   apply (rule none_in_new_cap_addrs
     ,(simp add: objBits_simps' pageBits_def APIType_capBits_def
                 ARM_HYP_H.toAPIType_def word_bits_conv archObjSize_def is_aligned_mask
          split: ARM_HYP_H.object_type.splits)+)[1]
  apply (clarsimp simp: word_bits_def)
 done


lemma createNewObjects_valid_duplicates'[wp]:
 "\<lbrace> (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and pspace_no_overlap' ptr sz
  and pspace_aligned' and pspace_distinct'
  and K (range_cover ptr sz (Types_H.getObjectSize ty us) (length dest) \<and>
      ptr \<noteq> 0 \<and> (ty = APIObjectType ArchTypes_H.apiobject_type.CapTableObject \<longrightarrow> us < 28) ) \<rbrace>
       createNewObjects ty src dest ptr us d
  \<lbrace>\<lambda>reply s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
proof (induct rule:rev_induct )
  case Nil
  show ?case
    by (simp add:createNewObjects_def zipWithM_x_mapM mapM_Nil | wp)+
next
  case (snoc dest dests)
  show ?case
    apply (rule hoare_gen_asm)
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

lemma neg_mask_add_aligned_special:
  assumes "q < 2 ^ 7" "7 \<le> n"
  shows "(p && ~~ mask 7) + q && ~~ mask n = p && ~~ mask n"
proof -
  from assms(1)
  have "((p && ~~ mask 7) + q && ~~ mask 7) && ~~ mask n = (p && ~~ mask 7) && ~~ mask n"
    by (simp add: is_aligned_neg_mask neg_mask_add_aligned)
  with assms(2)
  show ?thesis by (simp add: mask_lower_twice)
qed

lemma valid_duplicates_deleteObjects_helper:
  assumes vd:"vs_valid_duplicates' (m::(word32 \<rightharpoonup> Structures_H.kernel_object))"
  assumes inc: "\<And>p ko. \<lbrakk>m p = Some (KOArch ko);p \<in> {ptr .. ptr + 2 ^ sz - 1}\<rbrakk> \<Longrightarrow> 7 \<le> sz"
  assumes aligned:"is_aligned ptr sz"
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows "vs_valid_duplicates'  (\<lambda>x. if x \<in> {ptr .. ptr + 2 ^ sz - 1} then None else m x)"
  apply (clarsimp simp: vs_valid_duplicates'_def split:option.splits)
  apply (case_tac "the (m x)"; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object; clarsimp)
   apply (drule (1) valid_duplicates'_D[OF vd])
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply (rule conjI, clarsimp)
    apply (drule (1) inc)
    apply (clarsimp simp: vspace_bits_defs)
    apply (simp add: mask_lower_twice mask_in_range[OF aligned,symmetric])
   apply clarsimp
   apply (drule (1) bspec, clarsimp)
   apply (drule (1) inc)
   apply (simp add: mask_in_range[OF aligned,symmetric] vspace_bits_defs)
   apply (simp add: neg_mask_add_aligned_special largePagePTEOffsets_bound)
  apply (drule (1) valid_duplicates'_D[OF vd])
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply (rule conjI, clarsimp)
   apply (drule (1) inc)
   apply (clarsimp simp: vspace_bits_defs)
   apply (simp add: mask_lower_twice mask_in_range[OF aligned,symmetric])
  apply clarsimp
  apply (drule (1) bspec, clarsimp)
  apply (drule (1) inc)
  apply (simp add: mask_in_range[OF aligned,symmetric] vspace_bits_defs)
  apply (simp add: neg_mask_add_aligned_special superSectionPDEOffsets_bound)
  done

lemma deleteObjects_valid_duplicates'[wp]:
  notes blah[simp del] =  atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          atLeastAtMost_iff
  shows
  "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      K (is_aligned ptr sz)
   \<rbrace> deleteObjects ptr sz
   \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp:deleteObjects_def2)
  apply (wp hoare_drop_imps|simp)+
  apply clarsimp
  apply (simp add:deletionIsSafe_def)
  apply (erule valid_duplicates_deleteObjects_helper)
   apply fastforce
  apply simp
  done

crunch arch_inv[wp]: resetUntypedCap "\<lambda>s. P (ksArchState s)"
  (simp: crunch_simps
     wp: hoare_drop_imps unless_wp mapME_x_inv_wp
         preemptionPoint_inv
   ignore: freeMemory)

crunch valid_duplicates[wp]: updateFreeIndex "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"

lemma resetUntypedCap_valid_duplicates'[wp]:
  "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s))
      and valid_objs' and cte_wp_at' (isUntypedCap o cteCap) slot\<rbrace>
    resetUntypedCap slot
  \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  (is "\<lbrace>?P\<rbrace> ?f \<lbrace>\<lambda>_. ?Q\<rbrace>")
  apply (clarsimp simp: resetUntypedCap_def)
  apply (rule hoare_pre)
   apply (wp | simp add: unless_def)+
   apply (wp mapME_x_inv_wp preemptionPoint_inv | simp | wp (once) hoare_drop_imps)+
   apply (wp getSlotCap_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of split del: if_split)
  apply (frule cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD], clarsimp+)
  apply (clarsimp simp add: isCap_simps valid_cap_simps' capAligned_def)
  done

lemma new_CapTable_bound:
  "range_cover (ptr :: obj_ref) sz (APIType_capBits tp us) n
    \<Longrightarrow> tp = APIObjectType ArchTypes_H.apiobject_type.CapTableObject \<longrightarrow> us < 28"
  apply (frule range_cover.sz)
  apply (drule range_cover.sz(2))
  apply (clarsimp simp: APIType_capBits_def objBits_simps' word_bits_def)
  done

lemma invokeUntyped_valid_duplicates[wp]:
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
         and valid_untyped_inv' ui and ct_active'\<rbrace>
     invokeUntyped ui
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s) \<rbrace>"
  supply whenE_wps[wp_split del]
  apply (simp only: invokeUntyped_def updateCap_def)
  apply (rule hoare_name_pre_state)
  apply (cases ui)
  apply (clarsimp simp only: pred_conj_def valid_untyped_inv_wcap'
                             Invocations_H.untyped_invocation.simps)
  apply (frule(2) invokeUntyped_proofs.intro)
  apply (rule hoare_pre)
   apply simp
   apply (wp updateFreeIndex_pspace_no_overlap')
   apply ((rule validE_validE_R)?, rule hoare_post_impErr)
     apply (rule combine_validE)
      apply (rule_tac ui=ui in whenE_reset_resetUntypedCap_invs_etc)
     apply (rule whenE_wp)
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
  apply (frule cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD], clarsimp+)
  apply (clarsimp simp add: isCap_simps valid_cap_simps' capAligned_def)
  apply (auto split: if_split_asm)
  done

crunch valid_duplicates'[wp]:
  doReplyTransfer "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps isFinalCapability_inv
   simp: crunch_simps unless_def)

lemma setVCPU_valid_duplicates'[wp]:
 "setObject a (vcpu::vcpu) \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = vcpu,simplified])
  apply (clarsimp simp:updateObject_default_def assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def typeError_def projectKOs
    split:if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

crunch valid_duplicates'[wp]: vcpuSwitch "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps FalseI simp: crunch_simps)

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
  apply (simp add:getObject_def split_def| wp)+
  apply (simp add:loadObject_default_def|wp)+
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
  (wp: crunch_wps simp: crunch_simps unless_def o_def)

crunch valid_duplicates'[wp]:
  deletingIRQHandler "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma storePDE_no_duplicates':
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)
    \<and> ko_wp_at' (nondup_obj) ptr s
    \<and> nondup_obj (KOArch (KOPDE pde)) \<rbrace>
   storePDE ptr pde
  \<lbrace>\<lambda>ya s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  unfolding storePDE_def setObject_def
  apply (wpsimp wp: hoare_drop_imps simp: updateObject_default_def)
  apply (subst vs_valid_duplicates'_def, clarsimp)
  apply (rule conjI, clarsimp simp: nondup_obj_def)
  apply (clarsimp split: option.splits kernel_object.split arch_kernel_object.split)
  apply (rule conjI)
   apply clarsimp
   apply (drule (2) valid_duplicates'_D)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply (rule conjI)
    apply (clarsimp simp: ko_wp_at'_def nondup_obj_def)
   apply clarsimp
   apply (drule (1) bspec)
   apply clarsimp
   apply (clarsimp simp: ko_wp_at'_def nondup_obj_def addPTEOffset_def isLargePage_def')
   apply fastforce
  apply clarsimp
  apply (drule (2) valid_duplicates'_D)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply (rule conjI)
   apply (clarsimp simp: ko_wp_at'_def nondup_obj_def)
  apply clarsimp
  apply (drule (1) bspec)
  apply clarsimp
  apply (clarsimp simp: ko_wp_at'_def nondup_obj_def addPDEOffset_def isSuperSection_def')
  apply fastforce
  done

lemma storePTE_no_duplicates':
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)
    \<and> ko_wp_at' nondup_obj ptr s
    \<and> nondup_obj (KOArch (KOPTE pte)) \<rbrace>
   storePTE ptr pte
  \<lbrace>\<lambda>ya s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  unfolding storePTE_def setObject_def
  apply (wpsimp wp: hoare_drop_imps simp: updateObject_default_def)
  apply (subst vs_valid_duplicates'_def, clarsimp)
  apply (rule conjI, clarsimp simp: nondup_obj_def)
  apply (clarsimp split: option.splits kernel_object.split arch_kernel_object.split)
  apply (rule conjI)
   apply clarsimp
   apply (drule (2) valid_duplicates'_D)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply (rule conjI)
    apply (clarsimp simp: ko_wp_at'_def nondup_obj_def)
   apply clarsimp
   apply (drule (1) bspec)
   apply clarsimp
   apply (clarsimp simp: ko_wp_at'_def nondup_obj_def addPTEOffset_def isLargePage_def')
   apply fastforce
  apply clarsimp
  apply (drule (2) valid_duplicates'_D)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply (rule conjI)
   apply (clarsimp simp: ko_wp_at'_def nondup_obj_def)
  apply clarsimp
  apply (drule (1) bspec)
  apply clarsimp
  apply (clarsimp simp: ko_wp_at'_def nondup_obj_def addPDEOffset_def isSuperSection_def')
  apply fastforce
  done

crunch valid_duplicates'[wp]:
 lookupPTSlot "\<lambda>s. valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma checkMappingPPtr_SmallPage:
  "\<lbrace>\<top>\<rbrace> checkMappingPPtr word ARMSmallPage (Inl p)
           \<lbrace>\<lambda>x s. ko_wp_at' nondup_obj p s\<rbrace>,-"
  apply (simp add:checkMappingPPtr_def)
   apply (wp unlessE_wp getPTE_wp |wpc|simp add:)+
  apply (clarsimp simp:ko_wp_at'_def obj_at'_def)
  apply (clarsimp simp:projectKO_def projectKO_opt_pte
    return_def fail_def nondup_obj_def
    split:kernel_object.splits
    arch_kernel_object.splits option.splits)
  done

lemma checkMappingPPtr_Section:
  "\<lbrace>\<top>\<rbrace> checkMappingPPtr word ARMSection (Inr p)
           \<lbrace>\<lambda>x s. ko_wp_at' nondup_obj p s\<rbrace>,-"
  apply (simp add:checkMappingPPtr_def)
   apply (wp unlessE_wp getPDE_wp |wpc|simp add:)+
  apply (clarsimp simp:ko_wp_at'_def obj_at'_def)
  apply (clarsimp simp:projectKO_def projectKO_opt_pde
    return_def fail_def nondup_obj_def
    split:kernel_object.splits
    arch_kernel_object.splits option.splits)
  done

lemma mapM_x_mapM_valid:
  "\<lbrace> P \<rbrace> mapM_x f xs \<lbrace>\<lambda>r. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>mapM f xs \<lbrace>\<lambda>r. Q\<rbrace>"
  apply (simp add: mapM_x_mapM)
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
  "\<lbrace>\<lambda>s. valid_objs' s \<and> vmsz_aligned' vptr sz \<and> sz \<noteq> ARMSuperSection\<rbrace>
   lookupPTSlot pd vptr
  \<lbrace>\<lambda>rv s. is_aligned rv ((pageBitsForSize sz) - 9)\<rbrace>,-"
  apply (simp add:lookupPTSlot_def)
  apply (wp|wpc|simp)+
  apply (wp getPDE_wp)
  apply (clarsimp simp:obj_at'_def vmsz_aligned'_def)
  apply (clarsimp simp:projectKO_def fail_def
    projectKO_opt_pde return_def lookup_pt_slot_no_fail_def
    split:option.splits Structures_H.kernel_object.splits
    arch_kernel_object.splits)
  apply (erule(1) valid_objsE')
  apply (rule aligned_add_aligned)
     apply (simp add:valid_obj'_def)
     apply (erule is_aligned_ptrFromPAddr_n)
     apply (simp add:vspace_bits_defs)
    apply (rule is_aligned_shiftl)
    apply (rule is_aligned_andI1)
    apply (rule is_aligned_shiftr)
    apply (case_tac sz,simp_all add: vspace_bits_defs)[1]
   apply (simp add:vspace_bits_defs word_bits_def)
  apply (case_tac sz,simp_all add:ptBits_def pageBits_def)
  done

lemma doMachineOp_live_vcpu_at_tcb[wp]: "\<lbrakk>\<forall>s xb. (p s) = (p (s\<lparr>ksMachineState := xb\<rparr>))\<rbrakk> \<Longrightarrow> doMachineOp f \<lbrace>\<lambda>s. live_vcpu_at_tcb (p s) s\<rbrace>"
  apply (simp add: doMachineOp_def)
  apply wpsimp
    apply (rule_tac x=x in exI)
    apply (case_tac  "atcbVCPUPtr (tcbArch x)")
    apply clarsimp+
  done

crunch ko_at'_s[wp]: armv_contextSwitch "\<lambda>s. ko_at' t (ksCurThread s) s"

lemma flushPage_valid_arch_state'[wp]:
  "\<lbrace>\<lambda>s. valid_arch_state' s \<and> live_vcpu_at_tcb (ksCurThread s) s \<rbrace>
     flushPage a pd asid vptr
   \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: flushPage_def setVMRootForFlush_def getThreadVSpaceRoot_def)
  apply(wpsimp wp: crunch_wps getHWASID_valid_arch'
                   hoare_vcg_conj_lift
                   hoare_vcg_ex_lift
                   valid_case_option_post_wp'
               simp: crunch_simps unless_def
               cong: option.case_cong_weak)+
  apply (rule_tac x=x in exI)
  apply (clarsimp split: option.splits)
  done

crunch valid_arch_state'[wp]:
 flushTable "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma unmapPage_valid_duplicates'[wp]:
  notes checkMappingPPtr_inv[wp del] shows
  "\<lbrace>pspace_aligned' and valid_objs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
   and K (vmsz_aligned' vptr vmpage_size)\<rbrace>
  unmapPage vmpage_size asiv vptr word \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:unmapPage_def)
   (* make sure checkMappingPPtr_SmallPage is first tried before checkMappingPPtr_inv *)
  apply ((wp storePTE_no_duplicates' mapM_x_mapM_valid
    storePDE_no_duplicates' checkMappingPPtr_Section
    lookupPTSlot_page_table_at'
    checkMappingPPtr_SmallPage)+ | wpc
    | simp add:split_def conj_comms | wp (once) checkMappingPPtr_inv)+
          apply (rule_tac ptr = "p && ~~ mask ptBits" and word = p
            in mapM_x_storePTE_update_helper[where sz = 7])
          apply (wp checkMappingPPtr_inv lookupPTSlot_page_table_at'
                    Arch_R.lookupPTSlot_aligned | simp)+
      apply (rule hoare_post_imp_R[OF lookupPTSlot_aligned[where sz= vmpage_size]])
      apply (simp add:pageBitsForSize_def pt_bits_def pte_bits_def)
      apply (drule upto_enum_step_shift[where n = 7 and m = 3,simplified])
      apply (clarsimp simp: mask_def add.commute upto_enum_step_def largePagePTEOffsets_def
                            Let_def pte_bits_def)
     apply wp+
        apply ((wp storePTE_no_duplicates' mapM_x_mapM_valid
          storePDE_no_duplicates' checkMappingPPtr_Section
          checkMappingPPtr_SmallPage)+ | wpc
          | simp add:split_def conj_comms | wp (once) checkMappingPPtr_inv)+
        apply (rule_tac ptr = "p && ~~ mask pdBits" and word = p
                        in mapM_x_storePDE_update_helper[where sz = 7])
       apply (wp mapM_x_mapM_valid checkMappingPPtr_inv)+
   apply (clarsimp simp:conj_comms)
   apply (rule hoare_post_imp_R[where Q'= "\<lambda>r. pspace_aligned' and
     (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
     K(vmsz_aligned' vptr vmpage_size \<and> is_aligned r pdBits)
     and page_directory_at' (lookup_pd_slot r vptr && ~~ mask pdBits)"])
    apply (wp findPDForASID_page_directory_at'[unfolded pdBits_eq] findPDForASID_aligned[unfolded pdBits_eq] | simp)+
   apply (clarsimp simp add:pdBits_def pageBits_def vmsz_aligned'_def)
   apply (drule is_aligned_lookup_pd_slot)
    apply (erule is_aligned_weaken,simp add: pd_bits_def)
   apply simp
   apply (drule upto_enum_step_shift[where n = 7 and m = 3,simplified])
   apply (clarsimp simp: mask_def add.commute upto_enum_step_def pd_bits_def
                        superSectionPDEOffsets_def Let_def pde_bits_def)
  apply (clarsimp simp:ptBits_def pt_bits_def pageBits_def nondup_obj_def vmsz_aligned'_def)
  done

crunch ko_wp_at'[wp]:
 checkPDNotInASIDMap "\<lambda>s. ko_wp_at' P p s"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch ko_wp_at'[wp]:
 armv_contextSwitch "\<lambda>s. ko_wp_at' P p s"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma setVCPU_nondup_obj[wp]:
 "\<lbrace>\<lambda>s. ko_wp_at' nondup_obj p s\<rbrace>
   setObject a (vcpu::vcpu)
  \<lbrace>\<lambda>rv. ko_wp_at' nondup_obj p\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = vcpu,simplified])
  apply (clarsimp simp:ko_wp_at'_def)
  apply (intro conjI)
   subgoal
     by (clarsimp simp: updateObject_default_def assert_def bind_def
                           alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
                           assert_opt_def return_def fail_def typeError_def objBits_simps
                           nondup_obj_def projectKOs archObjSize_def
                    split: if_splits option.splits Structures_H.kernel_object.splits,
         (erule(1) ps_clear_updE)+)
  apply (clarsimp)
  apply (erule(1) ps_clear_updE)
  done

crunches vcpuSwitch, setVMRoot, setVMRootForFlush
  for nondup_obj[wp]: "ko_wp_at' nondup_obj p"
  (wp: crunch_wps FalseI simp: crunch_simps unless_def)

lemma unmapPageTable_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
    unmapPageTable aa ba word \<lbrace>\<lambda>x a. vs_valid_duplicates' (ksPSpace a)\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add:unmapPageTable_def)
   apply (wp|wpc|simp)+
      apply (wp storePDE_no_duplicates')+
  apply (simp add:pageTableMapped_def)
   apply (wp getPDE_wp |wpc|simp)+
   apply (rule hoare_post_imp_R[where Q' = "\<lambda>r s. vs_valid_duplicates' (ksPSpace s)"])
    apply wp
   apply (clarsimp simp:ko_wp_at'_def obj_at'_real_def projectKO_opt_pde)
   apply (clarsimp simp: nondup_obj_def
                  split: arch_kernel_object.splits pde.split kernel_object.splits)
  apply simp
  done

crunch valid_duplicates'[wp]:
 deleteASID "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunches deleteASIDPool, unbindNotification, prepareThreadDelete, vcpuFinalise
  for valid_duplicates'[wp]: "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma archFinaliseCap_valid_duplicates'[wp]:
  "\<lbrace>valid_objs' and pspace_aligned' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
    and (valid_cap' (capability.ArchObjectCap arch_cap))\<rbrace>
  Arch.finaliseCap arch_cap is_final
  \<lbrace>\<lambda>ya a. vs_valid_duplicates' (ksPSpace a)\<rbrace>"
  unfolding ARM_HYP_H.finaliseCap_def Let_def
  apply wpsimp
  apply (clarsimp simp: isCap_simps valid_cap'_def)
  done

lemma finaliseCap_valid_duplicates'[wp]:
  "\<lbrace>valid_objs' and pspace_aligned' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
  and (valid_cap' cap)\<rbrace>
  finaliseCap cap call final \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (case_tac cap,simp_all add:isCap_simps finaliseCap_def)
            apply (wp|intro conjI|clarsimp split: option.splits)+
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
  apply (rule validE_valid, rule hoare_pre, rule hoare_post_impErr, rule use_spec)
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
     apply (simp add:cteDelete_def)+
  done

lemma mapM_x_storePTE_invalid_whole:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<and>
  s \<turnstile>' capability.ArchObjectCap (arch_capability.PageTableCap word option) \<and>
  pspace_aligned' s\<rbrace>
  mapM_x (swp storePTE ARM_HYP_H.pte.InvalidPTE)
  [word , word + 2 ^ pte_bits .e. word + 2 ^ pt_bits - 1]
  \<lbrace>\<lambda>y s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (wp mapM_x_storePTE_update_helper[where word = word and sz = ptBits and ptr = word])
  apply (clarsimp simp: valid_cap'_def capAligned_def pageBits_def
                        ptBits_def objBits_simps archObjSize_def)
  apply (simp add: mask_def field_simps vspace_bits_defs is_aligned_neg_mask_eq')
  done

crunch valid_objs'[wp]:
  invalidateTLBByASID valid_objs'
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch pspace_aligned'[wp]:
  invalidateTLBByASID pspace_aligned'
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  isFinalCapability "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps filterM_preserved simp: crunch_simps unless_def)

crunch valid_cap'[wp]:
  isFinalCapability "\<lambda>s. valid_cap' cap s"
  (wp: crunch_wps filterM_preserved simp: crunch_simps unless_def)

crunch valid_duplicates'[wp]:
  sendSignal "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"

lemma invokeIRQControl_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<rbrace> performIRQControl a
  \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:performIRQControl_def )
  apply (rule hoare_pre)
  apply (wp|wpc | simp add:ARM_HYP_H.performIRQControl_def)+
 done

lemma invokeIRQHandler_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<rbrace> InterruptDecls_H.invokeIRQHandler a
  \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: Interrupt_H.invokeIRQHandler_def)
  apply (rule hoare_pre)
  apply (wp|wpc | simp add:ARM_HYP_H.performIRQControl_def invokeIRQHandler_def)+
  done

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
    apply (wp unless_wp | wpc | simp)+
   apply (simp add:invokeCNode_def)
   apply (wp getSlotCap_inv hoare_drop_imp
     |simp add:locateSlot_conv getThreadCallerSlot_def
     |wpc)+
  apply (simp add:cteDelete_def invokeCNode_def)
  apply (wp getSlotCap_inv hoare_drop_imp
     |simp add:locateSlot_conv getThreadCallerSlot_def
    whenE_def split_def
     |wpc)+
  apply (rule valid_validE)
   apply (rule hoare_post_imp[OF _ finaliseSlot_valid_duplicates'])
   apply simp
  apply (simp add:invs_valid_objs' invs_pspace_aligned')
  done

lemma getObject_pte_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::pte. P and ko_at' t r\<rbrace>"
  apply (wp getObject_ko_at)
  apply (auto simp: objBits_simps archObjSize_def pte_bits_def)
  done

lemma getObject_pde_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::pde. P and ko_at' t r\<rbrace>"
  apply (wp getObject_ko_at)
  apply (auto simp: objBits_simps archObjSize_def pde_bits_def)
  done

lemma vs_entry_align_nondup_obj:
  "(vs_entry_align ko = 0) = nondup_obj ko"
  by (clarsimp simp: nondup_obj_def vs_entry_align_def
              split: kernel_object.splits arch_kernel_object.splits pte.splits pde.splits)

fun the_i where
  "the_i [] x = 0" |
  "the_i (y#ys) x = (if x = y then 0 else Suc (the_i ys x))"

lemma the_ith_map_reduce:
  "a \<notin> set xs \<Longrightarrow>
   map (\<lambda>x. f x (n + (if x = a then 0 else Suc (the_i xs x)))) xs =
   map (\<lambda>x. f x (Suc n + the_i xs x)) xs"
  by (induct xs) auto

lemma the_ith_mapM_x_reduce:
  "a \<notin> set xs \<Longrightarrow>
   mapM_x (\<lambda>x. f x (n + (if x = a then 0 else Suc (the_i xs x)))) xs =
   mapM_x (\<lambda>x. f x (Suc n + the_i xs x)) xs"
  by (simp add: mapM_x_def the_ith_map_reduce)

lemma upto_enum_nat_Cons:
  "a \<le> b \<Longrightarrow> [a .e. b] = a # [Suc a .e. b]"
  by (simp add: upt_rec cong: if_weak_cong)

lemma map_zip_the_i:
  "distinct xs \<Longrightarrow>
   map f (zip xs [n .e. n + (length xs - Suc 0)]) =
   map (\<lambda>x. f (x, n + the_i xs x)) xs"
  supply upto_enum_nat[simp del]
  apply (induct xs arbitrary: n; clarsimp)
  apply (subst the_ith_map_reduce, assumption)
  apply (subst upto_enum_nat_Cons, simp)
  apply simp
  apply (drule_tac x="Suc n" in meta_spec)
  apply (case_tac xs; simp)
  done

lemma mapM_x_zip_the_i:
  "distinct xs \<Longrightarrow>
   mapM_x f (zip xs [n .e. n + (length xs - Suc 0)]) =
   mapM_x (\<lambda>x. f (x, n + the_i xs x)) xs"
  supply upto_enum_nat[simp del]
  by (simp add: mapM_x_def map_zip_the_i)

lemma upto_enum_word_of_nat:
  "\<lbrakk> a < 2^LENGTH('a); b < 2^LENGTH('a) \<rbrakk> \<Longrightarrow>
  [of_nat a::'a::len word .e. of_nat b] = map of_nat [a .e. b]"
  by (simp add: upto_enum_word take_bit_nat_eq_self unat_of_nat)

lemma map_shift_of_nat:
  "\<lbrakk> a < 2^LENGTH('a); b < 2^LENGTH('a) \<rbrakk> \<Longrightarrow>
  map f (zip xs [of_nat a::'a::len word .e. of_nat b]) = map (\<lambda>(x, i). f (x,of_nat i)) (zip xs [a .e. b])"
  by (simp add: map_zip_map2[where g=of_nat, symmetric] upto_enum_word_of_nat del: upto_enum_nat)

lemma mapM_x_shift_of_nat:
  "\<lbrakk> n' + n < 2^LENGTH('a) \<rbrakk> \<Longrightarrow>
  mapM_x f (zip xs [of_nat n'::'a::len word .e. of_nat (n' + n)]) = mapM_x (\<lambda>(x, i). f (x,of_nat i)) (zip xs [n' .e. n'+n])"
  by (simp add: mapM_x_def map_shift_of_nat del: upto_enum_nat of_nat_add)

lemma mapM_x_storePTE_slot_updates:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set xs. pte_at' x s) \<and> n + length xs < 2^word_bits \<and> distinct xs \<and>
        Q (\<lambda>x. if x \<in> set xs then Some (KOArch (KOPTE (addPTEOffset (LargePagePTE f a b c) (of_nat (n + the_i xs x))))) else (ksPSpace s) x) \<rbrace>
     mapM_x (\<lambda>(slot, i). storePTE slot (addPTEOffset (LargePagePTE f a b c) i)) (zip xs [of_nat n .e. of_nat (n + (length xs - Suc 0))])
   \<lbrace>\<lambda>r s. Q (ksPSpace s)\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (subst mapM_x_shift_of_nat)
    apply (clarsimp simp: word_bits_def, cases xs; simp)
  apply (subst mapM_x_zip_the_i, simp)
  apply (elim conjE)
  apply (thin_tac "Ball P S" for P S)
  apply (thin_tac "Q s" for s)
  apply (thin_tac "n + x < y" for x y)
  apply (induct xs arbitrary: n)
   apply (wpsimp simp: mapM_x_Nil)
  apply (simp add: mapM_x_Cons del: of_nat_add)
  apply (subst the_ith_mapM_x_reduce, simp)
  apply (drule_tac x="Suc n" in meta_spec)
  apply simp
  apply (rule hoare_seq_ext, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: storePTE_def setObject_def)
  apply (wp hoare_drop_imps | simp add:split_def updateObject_default_def)+
  apply clarsimp
  apply (intro conjI ballI)
   apply (drule(1) bspec)
   apply (clarsimp simp:typ_at'_def ko_wp_at'_def objBits_simps archObjSize_def lookupAround2_known1
                  dest!:koTypeOf_pte)
   apply (simp add:ps_clear_def dom_fun_upd2[unfolded fun_upd_def])
  apply (erule rsubst[where P=Q])
  apply (rule ext)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def lookupAround2_known1 add_ac)
  done

lemma mapM_x_storePDE_slot_updates:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set xs. pde_at' x s) \<and> n + length xs < 2^word_bits \<and> distinct xs \<and>
        Q (\<lambda>x. if x \<in> set xs then Some (KOArch (KOPDE (addPDEOffset (SuperSectionPDE f a b c) (of_nat (n + the_i xs x))))) else (ksPSpace s) x) \<rbrace>
     mapM_x (\<lambda>(slot, i). storePDE slot (addPDEOffset (SuperSectionPDE f a b c) i)) (zip xs [of_nat n .e. of_nat (n + (length xs - Suc 0))])
   \<lbrace>\<lambda>r s. Q (ksPSpace s)\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (subst mapM_x_shift_of_nat)
    apply (clarsimp simp: word_bits_def, cases xs; simp)
  apply (subst mapM_x_zip_the_i, simp)
  apply (elim conjE)
  apply (thin_tac "Ball P S" for P S)
  apply (thin_tac "Q s" for s)
  apply (thin_tac "n + x < y" for x y)
  apply (induct xs arbitrary: n)
   apply (wpsimp simp: mapM_x_Nil)
  apply (simp add: mapM_x_Cons del: of_nat_add)
  apply (subst the_ith_mapM_x_reduce, simp)
  apply (drule_tac x="Suc n" in meta_spec)
  apply simp
  apply (rule hoare_seq_ext, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: storePDE_def setObject_def)
  apply (wp hoare_drop_imps | simp add:split_def updateObject_default_def)+
  apply clarsimp
  apply (intro conjI ballI)
   apply (drule(1) bspec)
   apply (clarsimp simp:typ_at'_def ko_wp_at'_def objBits_simps archObjSize_def lookupAround2_known1
                  dest!:koTypeOf_pde)
   apply (simp add:ps_clear_def dom_fun_upd2[unfolded fun_upd_def])
  apply (erule rsubst[where P=Q])
  apply (rule ext)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def lookupAround2_known1 add_ac)
  done

lemma largePagePTEOffsets_aligned:
  "(a, b) \<in> set (zip largePagePTEOffsets [0.e.0xF::32 word]) \<Longrightarrow> is_aligned a 3"
  using is_aligned_mult_triv2[where n=3]
  by (auto simp: largePagePTEOffsets_def upto_enum_step_def vspace_bits_defs zip_map1)

lemma superSectionPDEOffsets_aligned:
  "(a, b) \<in> set (zip superSectionPDEOffsets [0.e.0xF::32 word]) \<Longrightarrow> is_aligned a 3"
  using is_aligned_mult_triv2[where n=3]
  by (auto simp: superSectionPDEOffsets_def upto_enum_step_def vspace_bits_defs zip_map1)

lemma slots_length:
  "is_aligned p 7 \<Longrightarrow> length [p , p + 8 .e. p + mask 7 :: machine_word] = 16"
  apply (drule is_aligned_no_overflow)
  apply (clarsimp simp: upto_enum_step_def mask_def word_le_not_less add_ac)
  done

lemma slots_distinct:
  "distinct [p , p + 8 .e. p + mask 7 :: machine_word]"
  apply (clarsimp simp: distinct_map upto_enum_step_def upto_enum_def mask_def o_def
                intro!: inj_onI)
  apply (rule word_of_nat_inj[where 'a=machine_word_len], fastforce+)
  apply (rule mult_pow2_inj[where n=3 and m=4]; simp add: mask_def word_of_nat_le)
  done

lemma addPTEOffset_LargePage:
  "addPTEOffset (LargePagePTE f a b c) x = LargePagePTE (addPAddr f (x * 0x1000)) a b c"
  by (simp add: addPTEOffset_def)

lemma the_i_slot_0:
  "is_aligned p 7 \<Longrightarrow> the_i [p , p + 8 .e. p + mask 7 :: 32 word] p = 0"
  apply (clarsimp simp: upto_enum_step_def)
  apply (subst map_length_unfold_one; simp add: mask_def)
  done

lemma the_i_map: "z \<in> set zs \<Longrightarrow> inj_on f (set zs) \<Longrightarrow> the_i (map f zs) (f z) = the_i zs z"
  unfolding inj_on_def
  apply (induct zs, fastforce)
  apply (case_tac "z \<in> set zs"; clarsimp)
  done

lemma the_i_app_in1: "x \<in> set xs \<Longrightarrow> the_i (xs @ ys) x = the_i xs x"
  by (induct xs) auto

lemma the_i_app_in2: "y \<notin> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> the_i (xs @ ys) y = length xs + the_i ys y"
  by (induct xs) auto

lemma the_i_range: "i < n \<Longrightarrow> the_i [0..<n] i = i"
  apply (induct n; simp)
  apply (case_tac "i=n"; simp add: the_i_app_in1 the_i_app_in2)
  done

lemma table_offset_the_i_helper:
  fixes a b p :: machine_word
  assumes "is_aligned p 7" "a = of_nat n * 8" "n < 16" "b = [0.e.0xF] ! n"
  shows "of_nat (the_i [p , p + 8 .e. p + mask 7] (p + of_nat n * 8))
          = [0.e.0xF::machine_word] ! n"
  using assms
  apply (clarsimp simp: upto_enum_step_def)
  apply (frule is_aligned_no_wrap'[where off="mask 7"]; simp add: mask_2pm1)
  apply (case_tac "p + 0x7F < p"; simp)
  apply (subst the_i_map)
    apply (simp add: word_of_nat_le)
   apply (rule inj_onI; simp)
   apply (rule mult_pow2_inj[where n=3 and m=4, simplified mask_def, simplified]; simp)
  apply (simp add: upto_enum_def)
  apply (rule subst[where P="\<lambda>w. of_nat (the_i _ w) = _", OF toEnum_of_nat])
   apply simp
  apply (subst the_i_map)
    apply simp
   apply (rule inj_onI; simp)
   apply (rule word_of_nat_inj[where 'a=machine_word_len]; simp)
  apply (simp add: the_i_range)
  done

lemma largePagePTEOffsets_the_i:
  "\<lbrakk> (a, b) \<in> set (zip largePagePTEOffsets [0.e.0xF::machine_word]); is_aligned p 7 \<rbrakk>
   \<Longrightarrow> of_nat (the_i [p, p + 8 .e. p + mask 7] (p + a)) = b"
  by (clarsimp simp: in_set_zip largePagePTEOffsets_nth length_largePagePTEOffsets
                     table_offset_the_i_helper)

lemma superSectionPDEOffsets_the_i:
  "\<lbrakk> (a, b) \<in> set (zip superSectionPDEOffsets [0.e.0xF::machine_word]); is_aligned p 7 \<rbrakk>
   \<Longrightarrow> of_nat (the_i [p, p + 8 .e. p + mask 7] (p + a)) = b"
  by (clarsimp simp: in_set_zip superSectionPDEOffsets_nth length_superSectionPDEOffsets
                     table_offset_the_i_helper)

lemma vmsz_aligned'_redundant:
  "vmsz_aligned' = vmsz_aligned"
  by (rule ext)+ (simp add: vmsz_aligned_def vmsz_aligned'_def)

lemma mask_out_lower_sum:
  "\<lbrakk> a < 2^n; n \<le> m \<rbrakk> \<Longrightarrow> (x && ~~ mask n) + a && ~~ mask m = x && ~~ mask m"
  apply (rule mask_out_first_mask_some_eq)
   prefer 2
   apply assumption
  apply (subst neg_mask_add_aligned)
    apply (simp add: is_aligned_andI2 is_aligned_neg_mask)
   apply assumption
  apply (simp add: mask_lower_twice)
  done

lemma mapM_x_largePagePTEOffsets:
  "\<lbrace>pspace_aligned' and page_table_at' (p && ~~ mask pt_bits) and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    K (slots = [p , p + 8 .e. p + mask 7] \<and> is_aligned p 7 \<and> vmsz_aligned' f ARMLargePage)\<rbrace>
   mapM_x (\<lambda>(slot, i). storePTE slot (addPTEOffset (LargePagePTE f a b c) i)) (zip slots [0.e.of_nat (length slots - Suc 0)])
   \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule mapM_x_storePTE_slot_updates [where n=0,simplified])
  apply clarsimp
  apply (clarsimp simp: page_table_at_set_list vspace_bits_defs)
  apply (simp add: word_bits_def slots_length slots_distinct)
  supply is_aligned_neg_mask[simp] mask_lower_twice[simp] the_i_slot_0[simp]
  supply addPTEOffset_LargePage[simp] vspace_bits_defs[simp] vmsz_aligned'_redundant[simp]
  supply is_aligned_add[simp] largePagePTEOffsets_aligned[simp] largePagePTEOffsets_bound[simp]
  apply (thin_tac "slots = xs" for xs)
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (thin_tac "p = y" for y)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply (frule_tac p'="x && ~~mask 7" in page_table_at_pte_atD'; clarsimp)
   apply (rule conjI; clarsimp simp: largePagePTEOffsets_the_i)
   apply (erule impE)
    apply (erule page_table_at_pte_atD'; simp add: mask_out_lower_sum)
   apply (erule notE)
   apply (simp add: mask_out_lower_sum)
  apply (clarsimp split: option.split kernel_object.split arch_kernel_object.split)
  apply (rule conjI; clarsimp)
   apply (drule (2) valid_duplicates'_D)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply (rule conjI; clarsimp simp: largePagePTEOffsets_the_i mask_out_lower_sum)
    apply (erule notE, erule page_table_at_pte_atD'; simp add: mask_out_lower_sum)
   apply (rule conjI; clarsimp)
    apply (erule notE, erule page_table_at_pte_atD'; simp add: mask_out_lower_sum)
   apply fastforce
  apply (drule (2) valid_duplicates'_D)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
  apply (rule conjI; clarsimp)
   apply (drule (1) bspec)
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
  apply fastforce
  done

lemma mapM_x_superSectionPDEOffsets:
  "\<lbrace>pspace_aligned' and page_directory_at' (p && ~~ mask pd_bits) and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    K (slots = [p , p + 8 .e. p + mask 7] \<and> is_aligned p 7 \<and> vmsz_aligned' f ARMSuperSection)\<rbrace>
   mapM_x (\<lambda>(slot, i). storePDE slot (addPDEOffset (ARM_HYP_H.SuperSectionPDE f a b c) i))
            (zip slots [0.e.of_nat (length slots - Suc 0)])
   \<lbrace>\<lambda>a b. vs_valid_duplicates' (ksPSpace b)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule mapM_x_storePDE_slot_updates [where n=0,simplified])
  apply clarsimp
  apply (clarsimp simp: page_directory_at_set_list vspace_bits_defs)
  apply (simp add: word_bits_def slots_length slots_distinct)
  supply is_aligned_neg_mask[simp] mask_lower_twice[simp] the_i_slot_0[simp]
  supply addPTEOffset_LargePage[simp] vspace_bits_defs[simp] vmsz_aligned'_redundant[simp]
  supply is_aligned_add[simp] superSectionPDEOffsets_aligned[simp] superSectionPDEOffsets_bound[simp]
  apply (thin_tac "slots = xs" for xs)
  apply (subst vs_valid_duplicates'_def)
  apply (clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (thin_tac "p = y" for y)
   apply (clarsimp simp: valid_pde_duplicates_at'_def)
   apply (frule_tac p'="x && ~~mask 7" in page_directory_at_pde_atD'; clarsimp)
   apply (rule conjI; clarsimp simp: superSectionPDEOffsets_the_i)
   apply (erule impE)
    apply (erule page_directory_at_pde_atD'; simp add: mask_out_lower_sum)
   apply (erule notE)
   apply (simp add: mask_out_lower_sum)
  apply (clarsimp split: option.split kernel_object.split arch_kernel_object.split)
  apply (rule conjI; clarsimp)
   apply (drule (2) valid_duplicates'_D)
   apply (clarsimp simp: valid_pte_duplicates_at'_def)
   apply (rule conjI; clarsimp)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
   apply (rule conjI; clarsimp)
    apply (drule (1) bspec)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
   apply fastforce
  apply (drule (2) valid_duplicates'_D)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply (rule conjI; clarsimp simp: superSectionPDEOffsets_the_i mask_out_lower_sum)
   apply (erule notE, erule page_directory_at_pde_atD'; simp add: mask_out_lower_sum)
  apply (rule conjI; clarsimp)
   apply (erule notE, erule page_directory_at_pde_atD'; simp add: mask_out_lower_sum)
  apply fastforce
  done

lemma updateCap_nondup_obj[wp]:
  "updateCap p c \<lbrace>ko_wp_at' (\<lambda>ko. nondup_obj ko) p'\<rbrace>"
  by (simp add: vs_entry_align_nondup_obj[symmetric]) wp

lemma performPageInvocation_valid_duplicates'[wp]:
  "\<lbrace>invs' and valid_arch_inv' (invocation.InvokePage page_invocation)
  and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
    performPageInvocation page_invocation
    \<lbrace>\<lambda>y a. vs_valid_duplicates' (ksPSpace a)\<rbrace>"
  supply vs_entry_align_nondup_obj[simp]
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
      apply clarsimp
      apply (simp add:nondup_obj_def)
     apply (clarsimp simp: pteCheckIfMapped_def)
     apply (wp mapM_x_mapM_valid | simp)+
       apply (rule_tac p = p in mapM_x_largePagePTEOffsets)
      apply (wp getPTE_wp hoare_vcg_all_lift hoare_drop_imps)+
     apply (simp add:vspace_bits_defs)+
     apply (simp add:invs_pspace_aligned' valid_slots'_def)
    apply simp
    apply (clarsimp simp:mapM_singleton pteCheckIfMapped_def)
    apply (wp PageTableDuplicates.storePTE_no_duplicates' getPTE_wp hoare_drop_imps | simp)+
      apply (simp add:nondup_obj_def)
     apply simp+
   apply (clarsimp simp: pdeCheckIfMapped_def)
   apply (case_tac a)
      apply (clarsimp simp:valid_arch_inv'_def
          valid_page_inv'_def valid_slots'_def
          valid_slots_duplicated'_def mapM_singleton)
      apply (wp PageTableDuplicates.storePDE_no_duplicates' getPDE_wp hoare_drop_imps | simp)+
        apply (simp add:nondup_obj_def)
       apply simp+
     apply (clarsimp simp:valid_arch_inv'_def
          valid_page_inv'_def valid_slots'_def
          valid_slots_duplicated'_def mapM_singleton)
     apply (wp PageTableDuplicates.storePDE_no_duplicates' getPDE_wp hoare_drop_imps | simp)+
       apply (simp add:nondup_obj_def)
      apply simp+
    apply (clarsimp simp:valid_arch_inv'_def
          valid_page_inv'_def valid_slots'_def
          valid_slots_duplicated'_def mapM_singleton)
    apply (wp PageTableDuplicates.storePDE_no_duplicates' getPDE_wp hoare_drop_imps | simp)+
      apply (simp add:nondup_obj_def)
     apply simp+
   apply (clarsimp simp:valid_arch_inv'_def
          valid_page_inv'_def valid_slots'_def
          valid_slots_duplicated'_def mapM_x_singleton)
   apply (wp mapM_x_mapM_valid | simp)+
     apply (rule_tac p=p in mapM_x_superSectionPDEOffsets)
    apply wp+
      apply (simp add:vspace_bits_defs)+
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
  apply (simp add: placeNewObject'_def)
  apply (wp unless_wp | wpc |  simp add:alignError_def split_def)+
  apply (subgoal_tac "vs_valid_duplicates' (\<lambda>a. if a = ptr then Some (KOArch (KOASIDPool makeObject)) else ksPSpace s a)")
   apply fastforce
  apply clarsimp
  apply (erule (2) valid_duplicates'_update)
   apply (simp add: nondup_obj_def)
  apply assumption
  done

crunch valid_duplicates'[wp]: performARMVCPUInvocation "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps)

lemma performArchInvocation_valid_duplicates':
  "\<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p
    and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
     Arch.performInvocation ai
   \<lbrace>\<lambda>reply s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  supply vs_entry_align_nondup_obj[simp]
  apply (simp add: ARM_HYP_H.performInvocation_def performARMMMUInvocation_def)
  apply (cases ai, simp_all)
       apply (rename_tac page_table_invocation)
       apply (case_tac page_table_invocation)
        apply (rule hoare_name_pre_state)
        apply (clarsimp simp: valid_arch_inv'_def valid_pti'_def isCap_simps
                              cte_wp_at_ctes_of is_arch_update'_def isPageTableCap_def
                       split: arch_capability.splits)
        apply (clarsimp simp: performARMMMUInvocation_def performPageTableInvocation_def)
        apply (simp | wp getSlotCap_inv mapM_x_storePTE_invalid_whole[unfolded swp_def] | wpc)+
        apply fastforce
       apply (rule hoare_name_pre_state)
       apply (clarsimp simp:valid_arch_inv'_def isCap_simps valid_pti'_def
        cte_wp_at_ctes_of is_arch_update'_def isPageTableCap_def
        split:arch_capability.splits)
       apply (clarsimp simp: performARMMMUInvocation_def performPageTableInvocation_def)
       apply (wp storePDE_no_duplicates' | simp)+
       apply (rename_tac page_directory_invocation)
       apply (case_tac page_directory_invocation,
              simp_all add: performARMMMUInvocation_def performPageDirectoryInvocation_def)[]
        apply (wp+, simp)
         apply (wp)+
       apply simp
      apply simp
     apply (simp add: performARMMMUInvocation_def)
     apply(wp, simp)
    apply (rename_tac asidcontrol_invocation)
    apply (case_tac asidcontrol_invocation)
    apply (simp add:performASIDControlInvocation_def performARMMMUInvocation_def)
    apply (clarsimp simp:valid_aci'_def valid_arch_inv'_def)
    apply (rule hoare_name_pre_state)
    apply (clarsimp simp:cte_wp_at_ctes_of)
    apply (case_tac ctea,clarsimp)
    apply (frule(1) ctes_of_valid_cap'[OF _ invs_valid_objs'])
    apply (wp hoare_weak_lift_imp|simp)+
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
   apply (clarsimp simp:performASIDPoolInvocation_def performARMMMUInvocation_def)
   apply (wp | simp)+
  done

crunches restart, setPriority, setMCPriority
  for valid_duplicates'[wp]: "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (ignore: threadSet wp: setObject_ksInterrupt updateObject_default_inv
     simp: crunch_simps)

crunch inv [wp]: getThreadBufferSlot P
  (wp: crunch_wps)

lemma tc_valid_duplicates':
  "\<lbrace>invs' and sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and tcb_at' a and ex_nonz_cap_to' a and
    case_option \<top> (valid_cap' o fst) e' and
    K (case_option True (isCNodeCap o fst) e') and
    case_option \<top> (valid_cap' o fst) f' and
    K (case_option True (isValidVTableRoot o fst) f') and
    case_option \<top> (valid_cap') (case_option None (case_option None (Some o fst) o snd) g) and
    K (valid_option_prio d) and
    K (valid_option_prio mcp) and
    K (case_option True isArchObjectCap (case_option None (case_option None (Some o fst) o snd) g))
    and K (case_option True (swp is_aligned msg_align_bits o fst) g)\<rbrace>
      invokeTCB (tcbinvocation.ThreadControl a sl b' mcp d e' f' g)
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: split_def invokeTCB_def getThreadCSpaceRoot getThreadVSpaceRoot
                   getThreadBufferSlot_def locateSlot_conv
             cong: option.case_cong)
  apply (rule hoare_walk_assmsE)
    apply (clarsimp simp: pred_conj_def option.splits [where P="\<lambda>x. x s" for s])
    apply ((wp case_option_wp threadSet_invs_trivial
               hoare_vcg_all_lift threadSet_cap_to' hoare_weak_lift_imp | simp add: inQ_def | fastforce)+)[2]
  apply (rule hoare_walk_assmsE)
    apply (clarsimp simp: pred_conj_def option.splits [where P="\<lambda>x. x s" for s])
    apply ((wp case_option_wp  setMCPriority_invs' hoare_weak_lift_imp
               typ_at_lifts[OF setMCPriority_typ_at']
               hoare_vcg_all_lift threadSet_cap_to' | simp add: inQ_def  | fastforce)+)[2]
   apply ((simp only: simp_thms cases_simp cong: conj_cong
         | (wp cteDelete_deletes cteDelete_invs' cteDelete_sch_act_simple
               case_option_wp[where m'="return ()", OF setPriority_valid_duplicates' return_inv,simplified]
               threadSet_ipcbuffer_trivial
               checkCap_inv[where P="tcb_at' t" for t]
               checkCap_inv[where P="valid_cap' c" for c]
               checkCap_inv[where P="\<lambda>s. P (ksReadyQueues s)" for P]
               checkCap_inv[where P="\<lambda>s. vs_valid_duplicates' (ksPSpace s)"]
               checkCap_inv[where P=sch_act_simple]
               cteDelete_valid_duplicates'
               hoare_vcg_const_imp_lift_R
               typ_at_lifts [OF setPriority_typ_at']
               assertDerived_wp
               threadSet_cte_wp_at'
               hoare_vcg_all_lift_R
               hoare_vcg_all_lift
               hoare_weak_lift_imp
               )[1]
         | wpc
         | simp add: inQ_def
         | wp hoare_vcg_conj_liftE1 cteDelete_invs' cteDelete_deletes
              hoare_vcg_const_imp_lift
         )+)
  apply (clarsimp simp: tcb_cte_cases_def cte_level_bits_def objBits_defs
                        tcbIPCBufferSlot_def)
  apply (auto dest!: isCapDs isValidVTableRootD
               simp: isCap_simps)
  done

crunches performTransfer, unbindNotification, bindNotification, setDomain
  for valid_duplicates'[wp]: "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (ignore: threadSet wp: setObject_ksInterrupt updateObject_default_inv
     simp: crunch_simps)


lemma invokeTCB_valid_duplicates'[wp]:
  "\<lbrace>invs' and sch_act_simple and ct_in_state' runnable' and tcb_inv_wf' ti and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
     invokeTCB ti
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (case_tac ti, simp_all only:)
       apply (simp add: invokeTCB_def)
       apply wp
       apply (clarsimp simp: invs'_def valid_state'_def
                      dest!: global'_no_ex_cap)
      apply (simp add: invokeTCB_def)
      apply wp
      apply (clarsimp simp: invs'_def valid_state'_def
                     dest!: global'_no_ex_cap)
     apply (wp tc_valid_duplicates')
     apply (clarsimp split:option.splits)
     apply (rename_tac option)
     apply (case_tac option, simp_all)
    apply (simp add:invokeTCB_def | wp mapM_x_wp' | intro impI conjI | wpc)+
  done

lemma performInvocation_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<and> invs' s \<and> sch_act_simple s
    \<and> valid_invocation' i s \<and> ct_active' s\<rbrace>
  RetypeDecls_H.performInvocation isBlocking isCall i
  \<lbrace>\<lambda>reply s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (clarsimp simp:performInvocation_def)
  apply (simp add:ct_in_state'_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
  apply wpc
   apply (wp performArchInvocation_valid_duplicates' |simp)+
  apply (cases i)
  apply (clarsimp simp: simple_sane_strg sch_act_simple_def
                    ct_in_state'_def ct_active_runnable'[unfolded ct_in_state'_def]
                  | wp tcbinv_invs' arch_performInvocation_invs'
                  | rule conjI | erule active_ex_cap')+
  apply simp
  done

lemma hi_valid_duplicates'[wp]:
  "\<lbrace>invs' and sch_act_simple and ct_active'
    and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
      handleInvocation isCall isBlocking
   \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s) \<rbrace>"
  apply (simp add: handleInvocation_def split_def
                   ts_Restart_case_helper')
  apply (wp syscall_valid' setThreadState_nonqueued_state_update
    rfk_invs' ct_in_state'_set | simp)+
    apply (fastforce simp add: tcb_at_invs' ct_in_state'_def
                              simple_sane_strg
                              sch_act_simple_def
                       elim!: pred_tcb'_weakenE st_tcb_ex_cap''
                        dest: st_tcb_at_idle_thread')+
  done

crunch valid_duplicates' [wp]:
  activateIdleThread "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (ignore: setNextPC threadSet simp:crunch_simps)

crunch valid_duplicates' [wp]:
  tcbSchedAppend "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (simp:crunch_simps wp:unless_wp)

lemma timerTick_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  timerTick \<lbrace>\<lambda>x s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:timerTick_def decDomainTime_def)
   apply (wp hoare_drop_imps|wpc|simp)+
  done

lemma vgicMaintenance_valid_duplicates'[wp]:
  "vgicMaintenance \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  unfolding vgicMaintenance_def Let_def by (wpsimp wp: hoare_drop_imps)

lemma vppiEvent_valid_duplicates'[wp]:
  "vppiEvent irq \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  unfolding vppiEvent_def Let_def by (wpsimp wp: hoare_drop_imps)

lemma handleInterrupt_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  handleInterrupt irq \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: handleInterrupt_def)
  apply (rule conjI; rule impI)
   apply (wp hoare_vcg_all_lift hoare_drop_imps
             threadSet_pred_tcb_no_state getIRQState_inv haskell_fail_wp
          |wpc|simp add: handleReservedIRQ_def maskIrqSignal_def)+
  done


crunch valid_duplicates' [wp]:
  schedule "(\<lambda>s. vs_valid_duplicates' (ksPSpace s))"
  (ignore: setNextPC clearExMonitor threadSet
     simp: crunch_simps wp:findM_inv hoare_drop_imps)

lemma activate_sch_valid_duplicates'[wp]:
  "\<lbrace>\<lambda>s. ct_in_state' activatable' s \<and> vs_valid_duplicates' (ksPSpace s)\<rbrace>
     activateThread \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: activateThread_def getCurThread_def
             cong: if_cong Structures_H.thread_state.case_cong)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_seq_ext[where B="\<lambda>st s.  (runnable' or idle') st
    \<and> vs_valid_duplicates' (ksPSpace s)"])
   apply (rule hoare_pre)
    apply (wp | wpc | simp add: setThreadState_runnable_simp)+
  apply (clarsimp simp: ct_in_state'_def cur_tcb'_def pred_tcb_at'
                 elim!: pred_tcb'_weakenE)
  done

crunch valid_duplicates'[wp]:
  receiveSignal "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"

crunch valid_duplicates'[wp]:
  receiveIPC "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: getNotification_wp gbn_wp' crunch_wps)

crunch valid_duplicates'[wp]:
  deleteCallerCap "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps)

crunch valid_duplicates'[wp]:
  handleReply "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps)

crunch valid_duplicates'[wp]:
  handleYield "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
 (ignore: threadGet simp:crunch_simps wp:unless_wp)

crunch valid_duplicates'[wp]:
  "VSpace_H.handleVMFault", handleHypervisorFault "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
 (ignore: getFAR getDFSR getIFSR simp:crunch_simps)

lemma hs_valid_duplicates'[wp]:
  "\<lbrace>invs' and ct_active' and sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
  handleSend blocking \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (rule validE_valid)
  apply (simp add: handleSend_def)
  apply (wp | simp)+
  done

lemma hc_valid_duplicates'[wp]:
  "\<lbrace>invs' and ct_active' and sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
     handleCall
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by (simp add: handleCall_def |  wp)+

lemma handleRecv_valid_duplicates'[wp]:
  "\<lbrace>(\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
  handleRecv isBlocking \<lbrace>\<lambda>r s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: handleRecv_def cong: if_cong)
  apply (rule hoare_pre)
   apply wp
       apply ((wp getNotification_wp | wpc | simp add: whenE_def split del: if_split)+)[1]

      apply (rule_tac Q="\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)"

                   in hoare_post_impErr[rotated])

        apply (clarsimp simp: isCap_simps sch_act_sane_not)
       apply assumption
      apply (wp deleteCallerCap_nonz_cap)+
  apply (auto elim: st_tcb_ex_cap'' pred_tcb'_weakenE
             dest!: st_tcb_at_idle_thread'
              simp: ct_in_state'_def sch_act_sane_def)
  done


lemma handleEvent_valid_duplicates':
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    sch_act_simple and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)\<rbrace>
   handleEvent e
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (case_tac e, simp_all add: handleEvent_def)
      apply (rename_tac syscall)
      apply (case_tac syscall)
            apply (wp handleReply_sane
              | simp add: active_from_running' simple_sane_strg cong: if_cong
              | wpc)+
  done

lemma dmo_getActiveIRQ_notin_non_kernel_IRQs[wp]:
  "\<lbrace>\<top>\<rbrace> doMachineOp (getActiveIRQ True) \<lbrace>\<lambda>irq _. irq \<notin> Some ` non_kernel_IRQs\<rbrace>"
  unfolding doMachineOp_def
  by (wpsimp simp: getActiveIRQ_def in_monad split: if_split_asm)

lemma non_kernel_IRQs_strg:
  "invs' s \<and> irq \<notin> Some ` non_kernel_IRQs \<and> Q \<Longrightarrow>
    (\<exists>y. irq = Some y) \<longrightarrow> invs' s \<and> (the irq \<in> non_kernel_IRQs \<longrightarrow> P) \<and> Q"
  by auto

(* nothing extra needed on this architecture *)
defs fastpathKernelAssertions_def:
  "fastpathKernelAssertions \<equiv> \<lambda>s. True"

lemma callKernel_valid_duplicates':
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
    (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)\<rbrace>
   callKernel e
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: callKernel_def fastpathKernelAssertions_def)
  apply (rule hoare_pre)
   apply (wp activate_invs' activate_sch_act schedule_sch
             hoare_drop_imp[where R="\<lambda>_. kernelExitAssertions"]
             schedule_sch_act_simple he_invs' hoare_vcg_if_lift3
          | simp add: no_irq_getActiveIRQ
          | strengthen non_kernel_IRQs_strg, simp cong: conj_cong)+
   apply (rule hoare_post_impErr)
     apply (rule valid_validE)
     prefer 2
     apply assumption
    apply (wp handleEvent_valid_duplicates')
   apply simp
  apply simp
  done

end

end
