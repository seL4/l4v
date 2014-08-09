(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
  CSpace refinement
*)

theory CSpace_R
imports
  CSpace_I
  "../invariant-abstract/DetSchedSchedule_AI"
begin

lemma isMDBParentOf_CTE1:
  "isMDBParentOf (CTE cap node) cte =
   (\<exists>cap' node'. cte = CTE cap' node' \<and> sameRegionAs cap cap'
      \<and> mdbRevocable node
      \<and> (isEndpointCap cap \<longrightarrow> capEPBadge cap \<noteq> 0 \<longrightarrow>
           capEPBadge cap = capEPBadge cap' \<and> \<not> mdbFirstBadged node')
      \<and> (isAsyncEndpointCap cap \<longrightarrow> capAEPBadge cap \<noteq> 0 \<longrightarrow>
           capAEPBadge cap = capAEPBadge cap' \<and> \<not> mdbFirstBadged node'))"
  apply (simp add: isMDBParentOf_def Let_def split: cte.splits split del: split_if)
  apply (clarsimp simp: Let_def)
  apply (fastforce simp: isCap_simps)
  done

lemma isMDBParentOf_CTE:
  "isMDBParentOf (CTE cap node) cte =
   (\<exists>cap' node'. cte = CTE cap' node' \<and> sameRegionAs cap cap'
      \<and> mdbRevocable node
      \<and> (capBadge cap, capBadge cap') \<in> capBadge_ordering (mdbFirstBadged node'))"
  apply (simp add: isMDBParentOf_CTE1)
  apply (intro arg_cong[where f=Ex] ext conj_cong refl)
  apply (cases cap, simp_all add: isCap_simps)
   apply (auto elim!: sameRegionAsE simp: isCap_simps)
  done

lemma isMDBParentOf_trans:
  "\<lbrakk> isMDBParentOf a b; isMDBParentOf b c \<rbrakk> \<Longrightarrow> isMDBParentOf a c"
  apply (cases a)
  apply (clarsimp simp: isMDBParentOf_CTE)
  apply (frule(1) sameRegionAs_trans, simp)
  apply (erule(1) capBadge_ordering_trans)
  done

lemma parentOf_trans:
  "\<lbrakk> s \<turnstile> a parentOf b; s \<turnstile> b parentOf c \<rbrakk> \<Longrightarrow> s \<turnstile> a parentOf c"
  by (auto simp: parentOf_def elim: isMDBParentOf_trans)

lemma subtree_parent:
  "s \<turnstile> a \<rightarrow> b \<Longrightarrow> s \<turnstile> a parentOf b"
  by (erule subtree.induct) auto

lemma leadsto_is_prev:
  "\<lbrakk> m \<turnstile> p \<leadsto> c; m c = Some (CTE cap node);
    valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow>
  p = mdbPrev node"
  by (fastforce simp add: next_unfold' valid_dlist_def Let_def no_0_def)

lemma subtree_target_Some:
  "m \<turnstile> a \<rightarrow> b \<Longrightarrow> m b \<noteq> None"
  by (erule subtree.cases) (auto simp: parentOf_def)

lemma subtree_prev_loop:
  "\<lbrakk> m p = Some (CTE cap node); no_loops m; valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow>
  m \<turnstile> p \<rightarrow> mdbPrev node = False"
  apply clarsimp
  apply (frule subtree_target_Some)
  apply (drule subtree_mdb_next)
  apply (subgoal_tac "m \<turnstile> p \<leadsto>\<^sup>+ p")
   apply (simp add: no_loops_def)
  apply (erule trancl_into_trancl)
  apply (clarsimp simp: mdb_next_unfold)
  apply (fastforce simp: next_unfold' valid_dlist_def no_0_def Let_def)
  done

lemma subtree_trans_lemma:
  assumes "s \<turnstile> b \<rightarrow> c"
  shows "s \<turnstile> a \<rightarrow> b \<Longrightarrow> s \<turnstile> a \<rightarrow> c"
  using assms
proof induct
  case direct_parent
  thus ?case
    by (blast intro: trans_parent parentOf_trans subtree_parent)
next
  case (trans_parent y z)
  have IH: "s \<turnstile> a \<rightarrow> b \<Longrightarrow> s \<turnstile> a \<rightarrow> y" by fact+
  have step: "s \<turnstile> y \<leadsto> z" "z \<noteq> 0" "s \<turnstile> b parentOf z" by fact+

  have "s \<turnstile> a \<rightarrow> b" by fact+
  hence "s \<turnstile> a \<rightarrow> y" and "s \<turnstile> a parentOf b" by (auto intro: IH subtree_parent)
  moreover
  with step
  have "s \<turnstile> a parentOf z" by - (rule parentOf_trans)
  ultimately
  show ?case using step by - (rule subtree.trans_parent)
qed

lemma subtree_trans: "\<lbrakk> s \<turnstile> a \<rightarrow> b; s \<turnstile> b \<rightarrow> c \<rbrakk> \<Longrightarrow> s \<turnstile> a \<rightarrow> c"
  by (rule subtree_trans_lemma)

lemma same_arch_region_as_relation:
  "\<lbrakk>acap_relation c d; acap_relation c' d'\<rbrakk> \<Longrightarrow>
  arch_same_region_as c c' =
  sameRegionAs (ArchObjectCap d) (ArchObjectCap d')"
  apply (cases c)
  apply ((cases c', auto simp: ArchRetype_H.sameRegionAs_def sameRegionAs_def Let_def isCap_simps)[1])+
  done

lemma is_phyiscal_relation:
  "cap_relation c c' \<Longrightarrow> is_physical c = isPhysicalCap c'"
  by (auto simp: is_physical_def arch_is_physical_def
           split: cap.splits arch_cap.splits)

lemma obj_ref_of_relation:
  "\<lbrakk> cap_relation c c'; capClass c' = PhysicalClass \<rbrakk> \<Longrightarrow>
  obj_ref_of c = capUntypedPtr c'"
  by (cases c, simp_all) (case_tac arch_cap, auto)

lemma obj_size_relation:
  "\<lbrakk> cap_relation c c'; capClass c' = PhysicalClass \<rbrakk> \<Longrightarrow>
  obj_size c = capUntypedSize c'"
  apply (cases c, simp_all add: objBits_def objBitsKO_def zbits_map_def
                                cte_level_bits_def
                         split: option.splits sum.splits)
  apply (case_tac arch_cap,
         simp_all add: objBits_def ArchRetype_H.capUntypedSize_def asid_low_bits_def
                       pageBits_def)
  done

lemma same_region_as_relation:
    "\<lbrakk> cap_relation c d; cap_relation c' d' \<rbrakk> \<Longrightarrow>
  same_region_as c c' = sameRegionAs d d'"
  apply (cases c)
            apply clarsimp
           apply (clarsimp simp: sameRegionAs_def isCap_simps Let_def is_phyiscal_relation)
           apply (auto simp: obj_ref_of_relation obj_size_relation cong: conj_cong)[1]
          apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def)[1]
         apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def)[1]
        apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def)[1]
       apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def bits_of_def)[1]
      apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def)[1]
     apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def)[1]
    apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def)[1]
   apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def)[1]
   apply (cases c', auto simp: sameRegionAs_def isCap_simps Let_def)[1]
  apply simp
  apply (cases c')
  apply (clarsimp simp: same_arch_region_as_relation|
         clarsimp simp: sameRegionAs_def isCap_simps Let_def)+
  done

lemma can_be_is:
  "\<lbrakk> cap_relation c (cteCap cte); cap_relation c' (cteCap cte');
     mdbRevocable (cteMDBNode cte) = r;
     mdbFirstBadged (cteMDBNode cte') = r' \<rbrakk> \<Longrightarrow>
  should_be_parent_of c r c' r' = isMDBParentOf cte cte'"
  unfolding should_be_parent_of_def isMDBParentOf_def
  apply (cases cte)
  apply (cases cte')
  apply (clarsimp split del: split_if)
  apply (case_tac "mdbRevocable mdbnode")
   prefer 2
   apply simp
  apply (clarsimp split del: split_if)
  apply (case_tac "RetypeDecls_H.sameRegionAs capability capabilitya")
   prefer 2
   apply (simp add: same_region_as_relation)
  apply (simp add: same_region_as_relation split del: split_if)
  apply (cases c, simp_all add: isCap_simps)
    apply (cases c', auto simp: sameRegionAs_def Let_def isCap_simps)[1]
   apply (cases c', auto simp: sameRegionAs_def isCap_simps is_cap_simps)[1]
  apply (auto simp: Let_def)[1]
  done

lemma no_fail_getCTE [wp]:
  "no_fail (cte_at' p) (getCTE p)"
  apply (simp add: getCTE_def getObject_def split_def
                   loadObject_cte alignCheck_def unless_def
                   alignError_def is_aligned_mask[symmetric]
             cong: kernel_object.case_cong)
  apply (rule no_fail_pre, (wp | wpc)+)
  apply (clarsimp simp: cte_wp_at'_def getObject_def
                        loadObject_cte split_def in_monad
                 dest!: in_singleton
             split del: split_if)
  apply (clarsimp simp: in_monad typeError_def objBits_simps
                        magnitudeCheck_def
                 split: kernel_object.split_asm split_if_asm option.split_asm
             split del: split_if)
       apply simp+
  done

lemma tcb_cases_related:
  "tcb_cap_cases ref = Some (getF, setF, restr) \<Longrightarrow>
    \<exists>getF' setF'. (\<forall>x. tcb_cte_cases (cte_map (x, ref) - x) = Some (getF', setF'))
               \<and> (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow> cap_relation (getF tcb) (cteCap (getF' tcb')))"
  by (simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1
                cte_map_def tcb_relation_def
         split: split_if_asm)

lemma pspace_relation_cte_wp_at:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
    cte_wp_at (op = c) (cref, oref) s; pspace_aligned' s';
     pspace_distinct' s' \<rbrakk>
  \<Longrightarrow> cte_wp_at' (\<lambda>cte. cap_relation c (cteCap cte)) (cte_map (cref, oref)) s'"
  apply (simp add: cte_wp_at_cases)
  apply (erule disjE)
   apply clarsimp
   apply (drule(1) pspace_relation_absD)
   apply (simp add: unpleasant_helper)
   apply (drule spec, drule mp, erule domI)
   apply (clarsimp simp: cte_relation_def)
   apply (drule(2) aligned_distinct_obj_atI'[where 'a=cte])
    apply simp
   apply (drule ko_at_imp_cte_wp_at')
   apply (clarsimp elim!: cte_wp_at_weakenE')
  apply clarsimp
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (simp split: kernel_object.split_asm)
  apply (drule(2) aligned_distinct_obj_atI'[where 'a=tcb])
   apply simp
  apply (drule tcb_cases_related)
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
  apply (erule(2) cte_wp_at_tcbI')
   apply fastforce
  apply simp
  done

lemma pspace_relation_ctes_ofI:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
    cte_wp_at (op = c) slot s; pspace_aligned' s';
     pspace_distinct' s' \<rbrakk>
  \<Longrightarrow> \<exists>cte. ctes_of s' (cte_map slot) = Some cte \<and> cap_relation c (cteCap cte)"
  apply (cases slot, clarsimp)
  apply (drule(3) pspace_relation_cte_wp_at)
  apply (simp add: cte_wp_at_ctes_of)
  done

lemma get_cap_corres_P:
  "corres (\<lambda>x y. cap_relation x (cteCap y) \<and> P x)
          (cte_wp_at P cslot_ptr)
          (pspace_aligned' and pspace_distinct')
          (get_cap cslot_ptr) (getCTE (cte_map cslot_ptr))"
  apply (rule corres_stronger_no_failI)
   apply (rule no_fail_pre, wp)
   apply clarsimp
   apply (drule cte_wp_at_norm)
   apply (clarsimp simp: state_relation_def)
   apply (drule (3) pspace_relation_ctes_ofI)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (cases cslot_ptr)
  apply (rename_tac oref cref)
  apply (clarsimp simp: cte_wp_at_def)
  apply (frule in_inv_by_hoareD[OF getCTE_inv])
  apply (drule use_valid [where P="\<top>", OF _ getCTE_sp TrueI])
  apply (clarsimp simp: state_relation_def)
  apply (drule pspace_relation_ctes_ofI)
     apply (simp add: cte_wp_at_def)
    apply assumption+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemmas get_cap_corres = get_cap_corres_P[where P="\<top>", simplified]

lemma cap_relation_masks:
  "cap_relation c c' \<Longrightarrow> cap_relation
      (cap_rights_update (cap_rights c \<inter> rmask) c)
      (RetypeDecls_H.maskCapRights (rights_mask_map rmask) c')"
apply (case_tac c, simp_all add: isCap_defs maskCapRights_def Let_def
                                 rights_mask_map_def maskVMRights_def
                                 AllowSend_def AllowRecv_def
                                 cap_rights_update_def
                          split del: split_if)
apply (clarsimp simp add: isCap_defs)
by (rule ArchAcc_R.arch_cap_rights_update
         [simplified, simplified rights_mask_map_def])

lemma getCTE_wp:
  "\<lbrace>\<lambda>s. cte_at' p s \<longrightarrow> (\<exists>cte. cte_wp_at' (op = cte) p s \<and> Q cte s)\<rbrace> getCTE p \<lbrace>Q\<rbrace>"
  apply (clarsimp simp add: getCTE_def valid_def cte_wp_at'_def)
  apply (drule getObject_cte_det)
  apply clarsimp
  done

lemma getCTE_ctes_of:
  "\<lbrace>\<lambda>s. ctes_of s p \<noteq> None \<longrightarrow> P (the (ctes_of s p)) (ctes_of s)\<rbrace> getCTE p \<lbrace>\<lambda>rv s. P rv (ctes_of s)\<rbrace>"
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma getCTE_ctes_of_weakened:
  "\<lbrace>\<lambda>s. P (the (ctes_of s p)) (ctes_of s)\<rbrace> getCTE p \<lbrace>\<lambda>rv s. P rv (ctes_of s)\<rbrace>"
  by (wp getCTE_ctes_of, simp)

lemma getCTE_wp':
  "\<lbrace>\<lambda>s. \<forall>cte. cte_wp_at' (op = cte) p s \<longrightarrow> Q cte s\<rbrace> getCTE p \<lbrace>Q\<rbrace>"
  apply (clarsimp simp add: getCTE_def valid_def cte_wp_at'_def)
  apply (drule getObject_cte_det)
  apply clarsimp
  done

lemma getSlotCap_corres:
  "cte_ptr' = cte_map cte_ptr \<Longrightarrow>
   corres cap_relation
     (cte_at cte_ptr)
     (pspace_distinct' and pspace_aligned')
     (get_cap cte_ptr)
     (getSlotCap cte_ptr')"
  apply (simp add: getSlotCap_def)
  apply (subst bind_return [symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_cap_corres])
      apply (rule corres_trivial, simp)
     apply (wp | simp)+
  done

lemma maskCapRights [simp]:
  "cap_relation c c' \<Longrightarrow>
  cap_relation (mask_cap msk c) (maskCapRights (rights_mask_map msk) c')"
  by (simp add: mask_cap_def cap_relation_masks)

lemma maskCap_valid [simp]:
  "s \<turnstile>' RetypeDecls_H.maskCapRights R cap = s \<turnstile>' cap"
  by (simp    add: valid_cap'_def maskCapRights_def isCap_simps
                   capAligned_def ArchRetype_H.maskCapRights_def
            split: capability.split arch_capability.split
        split del: split_if)

lemma getSlotCap_valid_cap:
  "\<lbrace>valid_objs'\<rbrace> getSlotCap t \<lbrace>\<lambda>r. valid_cap' r and cte_at' t\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_valid_cap | simp)+
  done

lemmas getSlotCap_valid_cap1 [wp] = getSlotCap_valid_cap [THEN hoare_conjD1]
lemmas getSlotCap_valid_cap2 [wp] = getSlotCap_valid_cap [THEN hoare_conjD2]

lemma resolveAddressBits_real_cte_at':
  "\<lbrace> valid_objs' and valid_cap' cap \<rbrace>
  resolveAddressBits cap addr depth
  \<lbrace>\<lambda>rv. real_cte_at' (fst rv)\<rbrace>, -"
proof (induct rule: resolveAddressBits.induct)
  case (1 cap addr depth)
  show ?case
    apply (clarsimp simp: validE_def validE_R_def valid_def split: sum.split)
    apply (subst (asm) resolveAddressBits.simps)
    apply (simp only: Let_def split: split_if_asm)
     prefer 2
     apply (simp add: in_monad)
    apply (simp only: in_bindE_R K_bind_def)
    apply (elim exE conjE)
    apply (simp only: split: split_if_asm)
     apply (clarsimp simp: in_monad locateSlot_def)
     apply (cases cap)
       apply (simp_all add: isCap_defs)[12]
     apply (clarsimp simp add: valid_cap'_def objBits_simps)
    apply (simp only: in_bindE_R K_bind_def)
    apply (elim exE conjE)
    apply (simp only: cap_case_CNodeCap split: split_if_asm)
     apply (drule_tac cap=nextCap in isCapDs(4), elim exE)
     apply (simp only: in_bindE_R K_bind_def)
     apply (frule (12) 1 [OF refl], (assumption | rule refl)+)
     apply (clarsimp simp: in_monad locateSlot_def objBits_simps)
     apply (cases cap)
       apply (simp_all add: isCap_defs)[12]
     apply (frule in_inv_by_hoareD [OF getSlotCap_inv])
     apply simp
     apply (frule (1) post_by_hoare [OF getSlotCap_valid_cap])
     apply (simp add: valid_def validE_def validE_R_def)
     apply (erule allE, erule impE, blast)
     apply (drule (1) bspec)
     apply simp
    apply (clarsimp simp: in_monad locateSlot_def objBits_simps)
    apply (cases cap)
     apply (simp_all add: isCap_defs)[12]
    apply (frule in_inv_by_hoareD [OF getSlotCap_inv])
    apply (clarsimp simp: valid_cap'_def)
    done
qed

lemma resolveAddressBits_cte_at':
  "\<lbrace> valid_objs' and valid_cap' cap \<rbrace>
  resolveAddressBits cap addr depth
  \<lbrace>\<lambda>rv. cte_at' (fst rv)\<rbrace>, \<lbrace>\<lambda>rv s. True\<rbrace>"
  apply (fold validE_R_def)
  apply (rule hoare_post_imp_R)
   apply (rule resolveAddressBits_real_cte_at')
  apply (erule real_cte_at')
  done

declare AllowSend_def[simp]
declare AllowRecv_def[simp]

lemma cap_map_update_data:
  assumes "cap_relation c c'"
  shows   "cap_relation (update_cap_data p x c) (updateCapData p x c')"
proof -
  note simps = update_cap_data_def updateCapData_def word_size
               isCap_defs is_cap_defs Let_def
               cap_rights_update_def badge_update_def
  { fix x :: word32
    def y \<equiv> "(x >> 8) && mask 18"
    def z \<equiv> "unat ((x >> 3) && mask 5)"
    have "of_bl (to_bl (y && mask z)) = (of_bl (replicate (32-z) False @ drop (32-z) (to_bl y))::word32)"
      by (simp add: bl_and_mask)
    then
    have "y && mask z = of_bl (drop (32 - z) (to_bl y))"
      apply simp
      apply (subst test_bit_eq_iff [symmetric])
      apply (rule ext)
      apply (clarsimp simp: test_bit_of_bl nth_append)
      done
  } note x = this
  from assms
  show ?thesis
  apply (cases c)
            apply (simp_all add: simps)[5]
       defer
       apply (simp_all add: simps)[4]
   apply (clarsimp simp: simps the_arch_cap_def)
   apply (case_tac arch_cap)
        apply (simp_all add: simps arch_update_cap_data_def
                             ArchRetype_H.updateCapData_def)[5]
  -- CNodeCap
  apply (simp add: simps word_bits_def the_cnode_cap_def andCapRights_def
                   rightsFromWord_def data_to_rights_def nth_ucast)
  apply (insert x)
  apply (subgoal_tac "unat ((x >> 3) && mask 5) < unat (2^5::word32)")
   prefer 2
   apply (fold word_less_nat_alt)[1]
   apply (rule and_mask_less_size)
   apply (simp add: word_size)
  apply (simp add: word_bw_assocs)
  done
qed

lemma cte_map_shift:
  assumes bl: "to_bl cref' = zs @ cref"
  assumes pre: "guard \<le> cref"
  assumes len: "cbits + length guard \<le> length cref"
  assumes aligned: "is_aligned ptr (4 + cbits)"
  assumes cbits: "cbits \<le> word_bits - cte_level_bits"
  shows
  "ptr + 16 * ((cref' >> length cref - (cbits + length guard)) && mask cbits) =
   cte_map (ptr, take cbits (drop (length guard) cref))"
proof -
  let ?l = "length cref - (cbits + length guard)"
  from pre obtain xs where
    xs: "cref = guard @ xs" by (auto simp: prefixeq_def less_eq_list_def)
  hence len_c: "length cref = length guard + length xs" by simp
  with len have len_x: "cbits \<le> length xs" by simp

  from bl xs
  have cref': "to_bl cref' = zs @ guard @ xs" by simp
  hence "length (to_bl cref') = length \<dots>" by simp
  hence 32: "32 = length zs + length guard + length xs" by simp

  have len_conv [simp]: "size ptr = word_bits"
    by (simp add: word_size word_bits_def)

  have "to_bl ((cref' >> ?l) && mask cbits) = (replicate (32 - cbits) False) @
        drop (32 - cbits) (to_bl (cref' >> ?l))"
    by (simp add: bl_shiftl word_size bl_and_mask
                  cte_level_bits_def word_bits_def)
  also
  from len_c len_x cref' 32
  have "\<dots> = (replicate (32 - cbits) False) @ take cbits xs"
    by (simp add: bl_shiftr word_size add_ac)
  also
  from len_x len_c 32
  have "\<dots> = to_bl (of_bl (take cbits (drop (length guard) cref)) :: word32)"
    by (simp add: xs word_rev_tf takefill_alt rev_take rev_drop)

  finally
    show ?thesis
      by (simp add: cte_map_def)
qed

lemma cte_map_shift':
  "\<lbrakk> to_bl cref' = zs @ cref; guard \<le> cref; length cref = cbits + length guard;
    is_aligned ptr (4 + cbits); cbits \<le> word_bits - cte_level_bits \<rbrakk> \<Longrightarrow>
  ptr + 16 * (cref' && mask cbits) = cte_map (ptr, drop (length guard) cref)"
  by (auto dest: cte_map_shift)

lemma cap_relation_Null2 [simp]:
  "cap_relation c NullCap = (c = cap.NullCap)"
  by (cases c) auto

lemma cnode_cap_case_if:
  "(case c of CNodeCap _ _ _ _ \<Rightarrow> f | _ \<Rightarrow> g) = (if isCNodeCap c then f else g)"
  by (auto simp: isCap_simps split: capability.splits)

declare resolve_address_bits'.simps[simp del]

lemma rab_corres':
  "\<lbrakk> cap_relation (fst a) c'; drop (32-bits) (to_bl cref') = snd a;
     bits = length (snd a) \<rbrakk> \<Longrightarrow>
  corres (lfr \<oplus> (\<lambda>(cte, bits) (cte', bits').
                   cte' = cte_map cte \<and> length bits = bits'))
          (valid_objs and pspace_aligned and valid_cap (fst a))
          (valid_objs' and pspace_distinct' and pspace_aligned' and valid_cap' c')
          (resolve_address_bits a)
          (resolveAddressBits c' cref' bits)"
unfolding resolve_address_bits_def
proof (induct a arbitrary: c' cref' bits rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
  proof (cases "isCNodeCap c'")
    case True
    with "1.prems"
    obtain ptr guard' guard cbits where caps:
      "cap = cap.CNodeCap ptr cbits guard"
      "c' = CNodeCap ptr cbits (of_bl guard) (length guard)"
      apply (cases cap, simp_all add: isCap_defs)
       apply auto
      done
    with "1.prems"
    have IH: "\<And>vd vc c' f' cref' bits.
      \<lbrakk> cbits + length guard \<noteq> 0; \<not> length cref < cbits + length guard; guard \<le> cref;
        vc = drop (cbits + length guard) cref; vc \<noteq> []; vd \<noteq> cap.NullCap;
       cap_relation vd c'; bits = length vc; is_cnode_cap vd;
       drop (32 - bits) (to_bl cref') = vc \<rbrakk>
      \<Longrightarrow> corres (lfr \<oplus> (\<lambda>(cte, bits) (cte', bits').
                   cte' = cte_map cte \<and> length bits = bits'))
    (valid_objs and pspace_aligned and (\<lambda>s. s \<turnstile> fst (vd,vc)))
    (valid_objs' and pspace_distinct' and pspace_aligned' and (\<lambda>s. s \<turnstile>' c'))
    (resolve_address_bits' z (vd, vc))
    (CSpace_H.resolveAddressBits c' cref' bits)"
      apply -
      apply (rule "1.hyps" [of _ cbits guard, OF caps(1)])
      prefer 7
        apply (clarsimp simp: in_monad)
        apply (rule get_cap_success)
      apply (auto simp: in_monad intro!: get_cap_success) (* takes time *)
      done
    note split_if [split del]
    { assume "cbits + length guard = 0 \<or> cbits = 0 \<and> guard = []"
      hence ?thesis
        apply (simp add: caps isCap_defs
                         resolveAddressBits.simps resolve_address_bits'.simps)
        apply (rule corres_fail)
        apply (clarsimp simp: valid_cap_def)
        done
    }
    moreover
    { assume "cbits + length guard \<noteq> 0 \<and> \<not>(cbits = 0 \<and> guard = [])"
      hence [simp]: "((cbits + length guard = 0) = False) \<and>
                     ((cbits = 0 \<and> guard = []) = False) \<and>
                    (0 < cbits \<or> guard \<noteq> []) " by simp
      note split_if [split del]
      from "1.prems"
      have ?thesis
        apply -
        apply (rule corres_assume_pre)
        apply (subgoal_tac "is_aligned ptr (4 + cbits) \<and> cbits \<le> word_bits - cte_level_bits")
         prefer 2
         apply (clarsimp simp: caps)
         apply (erule valid_CNodeCapE)
           apply fastforce
          apply fastforce
         apply fastforce
        apply (thin_tac "?t \<in> state_relation")
        apply (erule conjE)
        apply (subst resolveAddressBits.simps)
        apply (subst resolve_address_bits'.simps)
        apply (simp add: caps isCap_defs Let_def)
        apply (simp add: linorder_not_less drop_postfix_eq)
        apply (erule exE)
        apply (cases "guard \<le> cref")
         prefer 2
         apply (clarsimp simp: guard_mask_shift lookup_failure_map_def unlessE_whenE)
        apply (clarsimp simp: guard_mask_shift unlessE_whenE)
        apply (cases "length cref < cbits + length guard")
         apply (clarsimp simp: lookup_failure_map_def)
        apply (simp add: guard_mask_shift locateSlot_def returnOk_liftE [symmetric])
        apply (cases "length cref = cbits + length guard")
         apply clarsimp
         apply (rule corres_noopE)
          prefer 2
          apply (rule no_fail_pre, wp)[1]
         apply wp
         apply (clarsimp simp: objBits_simps)
         apply (erule (2) valid_CNodeCapE)
         apply (erule (3) cte_map_shift')
         apply simp
        apply simp
        apply (subgoal_tac "cbits + length guard < length cref")
         prefer 2
         apply simp
        apply simp
        apply (rule corres_initial_splitE)
           apply clarsimp
           apply (rule corres_guard_imp)
             apply (rule getSlotCap_corres)
             apply (simp add: objBits_simps)
             apply (erule (1) cte_map_shift)
               apply simp
              apply assumption
             apply assumption
            apply clarsimp
            apply (clarsimp simp: valid_cap_def)
            apply (erule cap_table_at_cte_at)
            apply simp
           apply clarsimp
          apply (case_tac "is_cnode_cap rv")
           prefer 2
           apply (simp add: cnode_cap_case_if)
           apply (rule corres_noopE)
            prefer 2
            apply (rule no_fail_pre, rule no_fail_returnOK)
            apply (rule TrueI)
           prefer 2
           apply (simp add: unlessE_whenE cnode_cap_case_if)
           apply (rule IH, (simp_all)[9])
            apply clarsimp
           apply (drule postfix_dropD)
           apply clarsimp
           apply (subgoal_tac "32 + (cbits + length guard) - length cref = (cbits + length guard) + (32 - length cref)")
            prefer 2
            apply (drule len_drop_lemma)
             apply simp
            apply arith
           apply simp
           apply (subst drop_drop [symmetric])
           apply simp
          apply wp
          apply (clarsimp simp: objBits_simps)
          apply (erule (1) cte_map_shift)
            apply simp
           apply assumption
          apply assumption
         apply wp
         apply clarsimp
         apply (rule hoare_chain)
           apply (rule hoare_conj [OF get_cap_inv [of "valid_objs and pspace_aligned"] get_cap_valid])
          apply clarsimp
         apply clarsimp
        apply clarsimp
       apply wp
        apply simp
       apply simp
       done
    }
    ultimately
    show ?thesis by fast
  next
    case False
    with "1.prems"
    show ?thesis
      by (cases cap)
         (auto simp: resolve_address_bits'.simps resolveAddressBits.simps
                     isCap_defs lookup_failure_map_def)
  qed
qed

lemma rab_corres:
  "\<lbrakk> cap_relation (fst a) c'; drop (32-bits) (to_bl cref') = snd a;
     bits = length (snd a) \<rbrakk> \<Longrightarrow>
  corres (lfr \<oplus> (\<lambda>(cte, bits) (cte', bits').
                   cte' = cte_map cte \<and> length bits = bits'))
          (invs and valid_cap (fst a)) (invs' and valid_cap' c')
          (resolve_address_bits a)
          (resolveAddressBits c' cref' bits)"
  using rab_corres' by (rule corres_guard_imp) auto

lemma getThreadCSpaceRoot:
  "getThreadCSpaceRoot t = return t"
  by (simp add: getThreadCSpaceRoot_def locateSlot_def
                tcbCTableSlot_def)

lemma getThreadVSpaceRoot:
  "getThreadVSpaceRoot t = return (t+16)"
  by (simp add: getThreadVSpaceRoot_def locateSlot_def objBits_simps
                tcbVTableSlot_def shiftl_t2n)

lemma getSlotCap_tcb_corres:
  "corres (\<lambda>t c. cap_relation (tcb_ctable t) c)
          (tcb_at t and valid_objs and pspace_aligned)
          (pspace_distinct' and pspace_aligned')
          (gets_the (get_tcb t))
          (getSlotCap t)"
  (is "corres ?r ?P ?Q ?f ?g")
  using get_cap_corres [where cslot_ptr = "(t, tcb_cnode_index 0)"]
  apply (simp add: getSlotCap_def liftM_def[symmetric])
  apply (drule corres_guard_imp [where P="?P" and P'="?Q"])
    apply (clarsimp simp: cte_at_cases tcb_at_def
                   dest!: get_tcb_SomeD)
   apply simp
  apply (subst(asm) corres_cong [OF refl refl gets_the_tcb_get_cap[symmetric] refl refl])
   apply simp
  apply (simp add: o_def cte_map_def tcb_cnode_index_def)
  done

lemma lookup_slot_corres:
  "corres (lfr \<oplus> (\<lambda>(cref, bits) cref'. cref' = cte_map cref))
        (valid_objs and pspace_aligned and tcb_at t)
        (valid_objs' and pspace_aligned' and pspace_distinct' and tcb_at' t)
        (lookup_slot_for_thread t (to_bl cptr))
        (lookupSlotForThread t cptr)"
  apply (unfold lookup_slot_for_thread_def lookupSlotForThread_def)
  apply (simp add: returnOk_bindE const_def)
  apply (simp add: getThreadCSpaceRoot)
  apply (fold returnOk_liftE)
  apply (simp add: returnOk_bindE)
  apply (rule corres_initial_splitE)
     apply (subst corres_liftE_rel_sum)
     apply (rule corres_guard_imp)
       apply (rule getSlotCap_tcb_corres)
      apply simp
     apply simp
    apply (subst bindE_returnOk[symmetric])
    apply (rule corres_initial_splitE)
       apply (rule rab_corres')
          apply simp
         apply (simp add: word_size)
        apply simp
       apply (clarsimp simp: word_size)
      prefer 4
      apply wp
      apply clarsimp
      apply (erule (1) objs_valid_tcb_ctable)
     prefer 4
     apply wp
      apply clarsimp
     apply simp
    prefer 2
    apply (rule hoare_vcg_precond_impE)
     apply (rule resolve_address_bits_cte_at [unfolded validE_R_def])
    apply clarsimp
   prefer 2
   apply (rule hoare_vcg_precond_impE)
    apply (rule resolveAddressBits_cte_at')
   apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (simp add: returnOk_def split_def)
  done

lemmas rab_cte_at' [wp] = resolveAddressBits_cte_at' [folded validE_R_def]

lemma lookupSlot_cte_at_wp[wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupSlotForThread t addr \<lbrace>\<lambda>rv. cte_at' rv\<rbrace>, \<lbrace>\<lambda>r. \<top>\<rbrace>"
  apply (simp add: lookupSlotForThread_def)
  apply (simp add: getThreadCSpaceRoot_def locateSlot_def tcbCTableSlot_def)
  apply (wp | simp add: split_def)+
  done

lemma lookupSlot_inv[wp]:
  "\<lbrace>P\<rbrace> lookupSlotForThread t addr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookupSlotForThread_def)
  apply (simp add: getThreadCSpaceRoot_def locateSlot_def tcbCTableSlot_def)
  apply (wp | simp add: split_def)+
  done

lemma lc_corres:
 "corres (lfr \<oplus> cap_relation)
         (valid_objs and pspace_aligned and tcb_at t)
         (valid_objs' and pspace_aligned' and pspace_distinct' and tcb_at' t)
         (lookup_cap t (to_bl ref)) (lookupCap t ref)"
  apply (simp add: lookup_cap_def lookupCap_def bindE_assoc
                   lookupCapAndSlot_def liftME_def split_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF _ lookup_slot_corres])
      apply (simp add: split_def getSlotCap_def liftM_def[symmetric] o_def)
      apply (rule get_cap_corres)
     apply (rule hoare_pre, wp lookup_slot_cte_at_wp|simp)+
  done

lemma setObject_cte_obj_at_tcb':
  assumes x: "\<And>tcb f. P (tcbCTable_update f tcb) = P tcb"
             "\<And>tcb f. P (tcbVTable_update f tcb) = P tcb"
             "\<And>tcb f. P (tcbReply_update f tcb) = P tcb"
             "\<And>tcb f. P (tcbCaller_update f tcb) = P tcb"
             "\<And>tcb f. P (tcbIPCBufferFrame_update f tcb) = P tcb"
  shows
  "\<lbrace>\<lambda>s. P' (obj_at' (P :: tcb \<Rightarrow> bool) p s)\<rbrace>
  setObject c (cte::cte)
  \<lbrace>\<lambda>_ s. P' (obj_at' P p s)\<rbrace>"
  apply (clarsimp simp: setObject_def in_monad split_def
                        valid_def lookupAround2_char1
                        obj_at'_def ps_clear_upd' projectKOs
             split del: split_if)
  apply (clarsimp elim!: rsubst[where P=P'])
  apply (clarsimp simp: updateObject_cte in_monad objBits_simps
                        tcbCTableSlot_def tcbVTableSlot_def x
                        typeError_def
                 split: split_if_asm
                        Structures_H.kernel_object.split_asm)
  done

lemma setCTE_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setCTE c cte \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (clarsimp simp add: setCTE_def) (wp setObject_typ_at')

lemmas setObject_typ_at [wp] = setObject_typ_at' [where P=id, simplified]

lemma setCTE_typ_at [wp]:
  "\<lbrace>typ_at' T p\<rbrace> setCTE c cte \<lbrace>\<lambda>_. typ_at' T p\<rbrace>"
  by (clarsimp simp add: setCTE_def) wp

lemmas setCTE_typ_ats [wp] = typ_at_lifts [OF setCTE_typ_at']

lemma setCTE_st_tcb_at':
  "\<lbrace>st_tcb_at' P t\<rbrace>
     setCTE c cte
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  unfolding st_tcb_at'_def setCTE_def
  apply (rule setObject_cte_obj_at_tcb')
   apply simp+
  done

lemma setObject_cte_ksCurDomain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject ptr (cte::cte) \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_cte_inv | simp)+
  done

lemma setCTE_tcb_in_cur_domain':
  "\<lbrace>tcb_in_cur_domain' t\<rbrace>
     setCTE c cte
   \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  unfolding tcb_in_cur_domain'_def setCTE_def
  apply (rule_tac f="\<lambda>s. ksCurDomain s" in hoare_lift_Pf)
  apply (wp setObject_cte_obj_at_tcb' | simp)+
  done

lemma tcbCTable_upd_simp [simp]:
  "tcbCTable (tcbCTable_update (\<lambda>_. x) tcb) = x"
  by (cases tcb) simp

lemma tcbVTable_upd_simp [simp]:
  "tcbVTable (tcbVTable_update (\<lambda>_. x) tcb) = x"
  by (cases tcb) simp

lemma setCTE_ctes_of_wp [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s (p \<mapsto> cte))\<rbrace>
  setCTE p cte
  \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  by (simp add: setCTE_def ctes_of_setObject_cte)

lemma setCTE_weak_cte_wp_at:
 "\<lbrace>\<lambda>s. (if p = ptr then P (cteCap cte) else cte_wp_at' (\<lambda>c. P (cteCap c)) p s)\<rbrace>
  setCTE ptr cte
  \<lbrace>\<lambda>uu s. cte_wp_at'(\<lambda>c. P (cteCap c)) p s\<rbrace>"
  apply (simp add: cte_wp_at_ctes_of)
  apply wp
  apply clarsimp
  done

lemma updateMDB_weak_cte_wp_at:
 "\<lbrace>cte_wp_at' (\<lambda>c. P (cteCap c)) p\<rbrace>
  updateMDB m f
  \<lbrace>\<lambda>uu. cte_wp_at'(\<lambda>c. P (cteCap c)) p\<rbrace>"
  unfolding updateMDB_def
  apply simp
  apply safe
  apply (wp setCTE_weak_cte_wp_at)
  apply (rule hoare_post_imp [OF _ getCTE_sp])
  apply (clarsimp simp: cte_wp_at'_def)
  done

lemma cte_wp_at_extract':
  "\<lbrakk> cte_wp_at' (\<lambda>c. c = x) p s; cte_wp_at' P p s \<rbrakk> \<Longrightarrow> P x"
  by (clarsimp simp: cte_wp_at_ctes_of)

lemma cteCap_update_id [simp]:
  "cteCap (cteCap_update (\<lambda>_. cap) c) = cap"
  by (cases c) simp

lemmas setCTE_valid_objs = setCTE_valid_objs'

lemma updateMDB_objs [wp]:
  "\<lbrace>valid_objs'\<rbrace>
   updateMDB p f
  \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: updateMDB_def)
  apply clarsimp
  apply (wp setCTE_valid_objs | simp)+
  done


lemma capFreeIndex_update_valid_cap':
  "\<lbrakk>fa \<le> fb; fb \<le> 2 ^ bits; is_aligned (of_nat fb :: word32) 4;
    s \<turnstile>' capability.UntypedCap v bits fa\<rbrakk>
   \<Longrightarrow> s \<turnstile>' capability.UntypedCap v bits fb"
  apply (clarsimp simp:valid_cap'_def capAligned_def valid_untyped'_def ko_wp_at'_def)
  apply (intro conjI impI allI)
  apply (elim allE)
    apply (erule(1) impE)+
    apply (erule disjE)
      apply simp_all
    apply (rule disjI1)
    apply clarsimp
   apply (erule disjoint_subset2[rotated])
   apply (clarsimp)
   apply (rule word_plus_mono_right)
    apply (rule of_nat_mono_maybe_le[THEN iffD1])
     apply (subst word_bits_def[symmetric])
     apply (erule less_le_trans[OF _  power_increasing])
      apply simp
     apply simp
   apply (subst word_bits_def[symmetric])
   apply (erule le_less_trans)
   apply (erule less_le_trans[OF _ power_increasing])
      apply simp+
   apply (erule is_aligned_no_wrap')
   apply (rule word_of_nat_less)
   apply simp
  apply (erule allE)+
  apply (erule(1) impE)+
  apply simp
  done

lemma maxFreeIndex_update_valid_cap'[simp]:
  "s \<turnstile>' capability.UntypedCap v0a v1a fa \<Longrightarrow>
   s \<turnstile>' capability.UntypedCap v0a v1a (maxFreeIndex v1a)"
  apply (rule capFreeIndex_update_valid_cap'[rotated -1])
   apply assumption
  apply (clarsimp simp:valid_cap'_def capAligned_def
    valid_untyped'_def ko_wp_at'_def maxFreeIndex_def shiftL_nat)+
  apply (erule is_aligned_weaken[OF is_aligned_triv])
  done

lemma cap_insert_objs' [wp]:
  "\<lbrace>valid_objs'
    and valid_cap' cap\<rbrace>
   cteInsert cap src dest \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: cteInsert_def updateCap_def setUntypedCapAsFull_def bind_assoc split del: split_if)
  apply (wp setCTE_valid_objs)
      apply simp
      apply wp
      apply (clarsimp simp: updateCap_def)
      apply (wp|simp)+
    apply (rule hoare_drop_imp)+
    apply wp
  apply (rule hoare_strengthen_post[OF getCTE_sp])
  apply (clarsimp simp:isCap_simps)
  done

lemma cteInsert_weak_cte_wp_at:
  "\<lbrace>\<lambda>s. if p = dest then P cap else p \<noteq> src \<and>
        cte_wp_at' (\<lambda>c. P (cteCap c)) p s\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>uu. cte_wp_at'(\<lambda>c. P (cteCap c)) p\<rbrace>"
  unfolding cteInsert_def error_def updateCap_def setUntypedCapAsFull_def
  apply (simp add: bind_assoc split del: split_if)
  apply (wp setCTE_weak_cte_wp_at updateMDB_weak_cte_wp_at static_imp_wp | simp)+
   apply (wp getCTE_ctes_wp)
   apply (clarsimp simp: isCap_simps split:split_if_asm| rule conjI)+
done

lemma setCTE_valid_cap:
  "\<lbrace>valid_cap' c\<rbrace> setCTE ptr cte \<lbrace>\<lambda>r. valid_cap' c\<rbrace>"
  by (rule typ_at_lifts, rule setCTE_typ_at')

lemma setCTE_weak_cte_at:
 "\<lbrace>\<lambda>s. cte_at' p s\<rbrace>
  setCTE ptr cte
  \<lbrace>\<lambda>uu. cte_at' p\<rbrace>"
  by (rule typ_at_lifts, rule setCTE_typ_at')

lemma updateMDB_valid_cap:
  "\<lbrace>valid_cap' c\<rbrace> updateMDB ptr f \<lbrace>\<lambda>_. valid_cap' c\<rbrace>"
  unfolding updateMDB_def
  apply simp
  apply rule
  apply (wp setCTE_valid_cap)
  done

lemma set_is_modify:
  "m p = Some cte \<Longrightarrow>
  m (p \<mapsto> cteMDBNode_update (\<lambda>_. (f (cteMDBNode cte))) cte) =
  m (p \<mapsto> cteMDBNode_update f cte)"
  apply (case_tac cte)
  apply (rule ext)
  apply clarsimp
  done

lemma updateMDB_ctes_of_wp:
  "\<lbrace>\<lambda>s. (p \<noteq> 0 \<longrightarrow> P (modify_map (ctes_of s) p (cteMDBNode_update f))) \<and>
        (p = 0 \<longrightarrow> P (ctes_of s))\<rbrace>
  updateMDB p f
  \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: updateMDB_def)
  apply safe
  apply wp
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (simp add: modify_map_def set_is_modify)
  done

lemma updateMDB_ctes_of_no_0 [wp]:
  "\<lbrace>\<lambda>s. no_0 (ctes_of s) \<and>
        P (modify_map (ctes_of s) p (cteMDBNode_update f))\<rbrace>
  updateMDB p f
  \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  by (wp updateMDB_ctes_of_wp) clarsimp

lemma updateMDB_no_0 [wp]:
  "\<lbrace>\<lambda>s. no_0 (ctes_of s)\<rbrace>
  updateMDB p f
  \<lbrace>\<lambda>rv s. no_0 (ctes_of s)\<rbrace>"
  by wp simp

definition
  "revokable' srcCap cap \<equiv>
  if isEndpointCap cap then capEPBadge cap \<noteq> capEPBadge srcCap
  else if isAsyncEndpointCap cap then capAEPBadge cap \<noteq> capAEPBadge srcCap
  else if isUntypedCap cap then True
  else if isIRQHandlerCap cap then isIRQControlCap srcCap
  else False"

lemma isMDBParentOf_next_update [simp]:
  "isMDBParentOf (cteMDBNode_update (mdbNext_update f) cte) cte' =
   isMDBParentOf cte cte'"
  "isMDBParentOf cte (cteMDBNode_update (mdbNext_update f) cte') =
   isMDBParentOf cte cte'"
   apply (cases cte)
   apply (cases cte')
   apply (simp add: isMDBParentOf_def)
  apply (cases cte)
  apply (cases cte')
  apply (clarsimp simp: isMDBParentOf_def)
  done

lemma isMDBParentOf_next_update_cte [simp]:
  "isMDBParentOf (CTE cap (mdbNext_update f node)) cte' =
   isMDBParentOf (CTE cap node) cte'"
  "isMDBParentOf cte (CTE cap (mdbNext_update f node)) =
   isMDBParentOf cte (CTE cap node)"
   apply (cases cte')
   apply (simp add: isMDBParentOf_def)
  apply (cases cte)
  apply (clarsimp simp: isMDBParentOf_def)
  done

lemma valid_mdbD1':
  "\<lbrakk> ctes_of s p = Some cte; mdbNext (cteMDBNode cte) \<noteq> 0; valid_mdb' s \<rbrakk> \<Longrightarrow>
  \<exists>c. ctes_of s (mdbNext (cteMDBNode cte)) = Some c \<and> mdbPrev (cteMDBNode c) = p"
  by (clarsimp simp add: valid_mdb'_def valid_mdb_ctes_def valid_dlist_def Let_def)

lemma valid_mdbD2':
  "\<lbrakk> ctes_of s p = Some cte; mdbPrev (cteMDBNode cte) \<noteq> 0; valid_mdb' s \<rbrakk> \<Longrightarrow>
  \<exists>c. ctes_of s (mdbPrev (cteMDBNode cte)) = Some c \<and> mdbNext (cteMDBNode c) = p"
  by (clarsimp simp add: valid_mdb'_def valid_mdb_ctes_def valid_dlist_def Let_def)

lemma rev_prev_update [simp]:
  "cteMDBNode_update (\<lambda>m. mdbRevocable_update f (mdbPrev_update f' y)) =
   cteMDBNode_update (mdbPrev_update f') o (cteMDBNode_update (\<lambda>m. mdbRevocable_update f y))"
  apply (rule ext)
  apply (case_tac x)
  apply simp
  apply (cases y)
  apply simp
  done

lemma prev_next_update:
  "cteMDBNode_update (mdbNext_update f) (cteMDBNode_update (mdbPrev_update f') x) =
   cteMDBNode_update (mdbPrev_update f') (cteMDBNode_update (mdbNext_update f) x)"
  apply (cases x)
  apply simp
  apply (case_tac mdbnode)
  apply simp
  done

lemmas modify_map_prev_next_up [simp] =
  modify_map_com [where f="cteMDBNode_update (mdbNext_update f)" and
                        g="cteMDBNode_update (mdbPrev_update f')", standard,
                  OF prev_next_update]

lemma update_prev_next_trancl:
  assumes nxt: "m \<turnstile> x \<leadsto>\<^sup>+ y"
  shows "(modify_map m ptr (cteMDBNode_update (mdbPrev_update z))) \<turnstile> x \<leadsto>\<^sup>+ y"
proof (cases "m ptr")
  case None
  thus ?thesis using nxt
    by (simp add: modify_map_def) (simp add: None [symmetric] fun_upd_triv)
next
  case (Some cte)
  let ?m = "m(ptr \<mapsto> cteMDBNode_update (mdbPrev_update z) cte)"

  from nxt have "?m \<turnstile> x \<leadsto>\<^sup>+ y"
  proof induct
    case (base y)
    thus ?case using Some
      by - (rule r_into_trancl, clarsimp simp: next_unfold')
  next
    case (step q r)
    show ?case
    proof (rule trancl_into_trancl)
      show "?m \<turnstile> q \<leadsto> r" using step(2) Some
        by (simp only: mdb_next_update, clarsimp simp: next_unfold')
    qed fact+
  qed
  thus ?thesis using Some
    by (simp add: modify_map_def)
qed

lemma update_prev_next_trancl2:
  assumes nxt: "(modify_map m ptr (cteMDBNode_update (mdbPrev_update z))) \<turnstile> x \<leadsto>\<^sup>+ y"
  shows   "m \<turnstile> x \<leadsto>\<^sup>+ y"
proof (cases "m ptr")
  case None
  thus ?thesis using nxt
    by (simp add: modify_map_def) (simp add: None [symmetric] fun_upd_triv)
next
  case (Some cte)
  let ?m = "m(ptr \<mapsto> cteMDBNode_update (mdbPrev_update z) cte)"

  from nxt have "m \<turnstile> x \<leadsto>\<^sup>+ y"
  proof induct
    case (base y)
    thus ?case using Some
      by (auto intro!: r_into_trancl
        simp: modify_map_def mdb_next_update next_unfold' split: split_if_asm)
  next
    case (step q r)
    show ?case
    proof
      show "m \<turnstile> q \<leadsto> r" using step(2) Some
      by (auto simp: modify_map_def mdb_next_update next_unfold' split: split_if_asm)
    qed fact+
  qed
  thus ?thesis using Some
    by (simp add: modify_map_def)
qed

lemma no_loops_modify_map_prev:
  "no_loops m \<Longrightarrow> no_loops (modify_map m ptr (cteMDBNode_update (mdbPrev_update f)))"
  unfolding no_loops_def
  apply (erule contrapos_pp)
  apply simp
  apply (erule exEI)
  apply (erule update_prev_next_trancl2)
  done

lemma next_update_lhs:
  "(m(p \<mapsto> cte) \<turnstile> p \<leadsto> x) = (x = mdbNext (cteMDBNode cte))"
  by (auto simp: mdb_next_update)

lemma next_update_lhs_trancl:
  assumes np: "\<not> m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* p"
  shows   "(m(p \<mapsto> cte) \<turnstile> p \<leadsto>\<^sup>+ x) = (m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* x)"
proof
  assume "m(p \<mapsto> cte) \<turnstile> p \<leadsto>\<^sup>+ x"
  thus "m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* x"
  proof (cases rule: tranclE2')
    case base
    thus ?thesis
      by (simp add: next_update_lhs)
  next
    case (trancl q)
    hence "m(p \<mapsto> cte) \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>+ x"
      by (simp add: next_update_lhs)
    thus ?thesis
      by (rule trancl_into_rtrancl [OF mdb_trancl_update_other]) fact+
  qed
next
  assume "m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* x"
  hence "m(p \<mapsto> cte) \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* x"
    by (rule mdb_rtrancl_other_update) fact+
  moreover
  have "m(p \<mapsto> cte) \<turnstile> p \<leadsto> mdbNext (cteMDBNode cte)" by (simp add:  next_update_lhs)
  ultimately show "m(p \<mapsto> cte) \<turnstile> p \<leadsto>\<^sup>+ x" by simp
qed

lemma next_update_lhs_rtrancl:
  assumes np: "\<not> m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* p"
  shows   "(m(p \<mapsto> cte) \<turnstile> p \<leadsto>\<^sup>* x) = (p = x \<or> m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* x)"
  apply rule
   apply (erule next_rtrancl_tranclE)
  apply (auto simp add: next_update_lhs_trancl [OF np, symmetric])
  done

definition
  cte_mdb_prop :: "(word32 \<rightharpoonup> cte) \<Rightarrow> word32 \<Rightarrow> (mdbnode \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cte_mdb_prop m p P \<equiv> (\<exists>cte. m p = Some cte \<and> P (cteMDBNode cte))"

lemma cte_mdb_prop_no_0:
  "\<lbrakk> no_0 m; cte_mdb_prop m p P \<rbrakk> \<Longrightarrow> p \<noteq> 0"
  unfolding cte_mdb_prop_def no_0_def
  by auto

lemma valid_dlist_insert_link:
  assumes vmdb: "valid_mdb_ctes m"
  and       cn: "mdbNext (cteMDBNode cte) = post"
  and       cp: "mdbPrev (cteMDBNode cte) = pre"
  and  mtarget: "cte_mdb_prop m target (\<lambda>m. mdbPrev m = nullPointer \<and> mdbNext m = nullPointer)"
  and    mpost: "cte_mdb_prop m post (\<lambda>c. mdbPrev c = pre)"
  and     mpre: "cte_mdb_prop m pre (\<lambda>c. mdbNext c = post)"
  and    tpost: "post \<noteq> target"
  and     tpre: "pre \<noteq> target"
  and  prepost: "post \<noteq> pre"
  shows   "valid_dlist
  (modify_map
    (modify_map (m(target \<mapsto> cte)) pre (cteMDBNode_update (mdbNext_update (\<lambda>_. target))))
    post (cteMDBNode_update (mdbPrev_update (\<lambda>_. target))))"
  (is "valid_dlist ?M")
proof -
  let ?nxt = "\<lambda>c. mdbNext (cteMDBNode c)"
  let ?prv = "\<lambda>c. mdbPrev (cteMDBNode c)"

  from vmdb have vd: "valid_dlist m" ..
  from vmdb have no0: "no_0 m" ..
  hence pre0: "pre \<noteq> 0" and post0: "post \<noteq> 0" and target0: "target \<noteq> 0"
    using mpre mpost mtarget

 by (auto elim!: cte_mdb_prop_no_0)

  from mpre obtain precte where precte: "m pre = Some precte"
      and nprecte: "?nxt precte = post" unfolding cte_mdb_prop_def by auto

  from mpost obtain postcte where postcte: "m post = Some postcte"
      and npostcte: "?prv postcte = pre" unfolding cte_mdb_prop_def by auto

  have rn: "\<forall>x. \<not> cte_mdb_prop m x (\<lambda>c. mdbNext c = target)" using mtarget
    unfolding cte_mdb_prop_def using vmdb target0
    by (auto elim: valid_dlistE elim!: valid_mdb_ctesE simp: nullPointer_def no_0_def)

  have rp: "\<forall>x. \<not> cte_mdb_prop m x (\<lambda>c. mdbPrev c = target)" using mtarget
    unfolding cte_mdb_prop_def using vmdb target0
    by (auto elim: valid_dlistE elim!: valid_mdb_ctesE simp: nullPointer_def no_0_def)

  show ?thesis
  proof
    fix ptr cte'
    assume m1: "?M ptr = Some cte'" and mp: "?prv cte' \<noteq> 0"

    let ?thesis = "\<exists>c. ?M (?prv cte') = Some c \<and> ?nxt c = ptr"
    {
      assume "ptr = post"
      hence ?thesis using m1 mp cn cp tpost tpre prepost
        by (clarsimp simp: modify_map_app split: split_if_asm)
    } moreover
    {
      assume p: "ptr = pre"

      hence cc: "cte' = cteMDBNode_update (mdbNext_update (\<lambda>_. target)) precte"
        using m1 precte prepost tpre
        by (simp add: modify_map_other modify_map_same)

      from vmdb have nl: "no_loops m" ..
      have "post \<noteq> ?prv cte'"
      proof
        assume "post = ?prv cte'"
        hence "m \<turnstile> post \<leadsto> pre" using postcte vd cc post0
          by (auto simp: next_unfold' elim: valid_dlistE intro: precte)
        moreover have "m \<turnstile> pre \<leadsto> post" using precte nprecte
          by (simp add: next_unfold')
        ultimately have "m \<turnstile> post \<leadsto>\<^sup>+ post" by simp
        thus False using nl unfolding no_loops_def by auto
      qed

      moreover have "pre \<noteq> ?prv cte'"
      proof
        assume "pre = ?prv cte'"
        hence "m \<turnstile> pre \<leadsto> pre" using precte vd cc pre0
          by (auto simp: next_unfold' elim: valid_dlistE intro: precte)
        thus False using nl unfolding no_loops_def by auto
      qed

      ultimately have ?thesis using p vd cc rp precte nprecte post0 mp
        unfolding cte_mdb_prop_def
        by (fastforce simp: modify_map_other elim!: valid_dlistEp)
    } moreover
    {
      assume "ptr = target"

      hence ?thesis using m1 tpre tpost cp prepost precte
        by (simp add: modify_map_other modify_map_same)
    } moreover
    {
      assume "ptr \<noteq> pre" and "ptr \<noteq> post" and "ptr \<noteq> target"
      hence ?thesis using m1 mp vd tpre cn cp rn rp precte nprecte
        unfolding cte_mdb_prop_def
        by (auto elim: valid_dlistEp simp: modify_map_app)
    }
    ultimately show ?thesis using prepost tpre tpost
      by (cases "ptr = post \<or> ptr = ptr \<or> ptr = target") auto
  next (* clag --- dual of above *)
    fix ptr cte'
    assume m1: "?M ptr = Some cte'" and mp: "?nxt cte' \<noteq> 0"

    let ?thesis = "\<exists>c. ?M (?nxt cte') = Some c \<and> ?prv c = ptr"
    {
      assume "ptr = pre"
      hence ?thesis using m1 mp cn cp tpost tpre prepost
        by (clarsimp simp: modify_map_app split: split_if_asm)
    } moreover
    {
      assume p: "ptr = post"

      hence cc: "cte' = cteMDBNode_update (mdbPrev_update (\<lambda>_. target)) postcte"
        using m1 postcte prepost tpost
        by (simp add: modify_map_other modify_map_same)

      from vmdb have nl: "no_loops m" ..
      have "pre \<noteq> ?nxt cte'"
      proof
        assume "pre = ?nxt cte'"
        hence "m \<turnstile> post \<leadsto> pre" using postcte vd cc pre0
          by (auto simp: next_unfold' elim!: valid_dlistE intro: precte)
        moreover have "m \<turnstile> pre \<leadsto> post" using precte nprecte
          by (simp add: next_unfold')
        ultimately have "m \<turnstile> post \<leadsto>\<^sup>+ post" by simp
        thus False using nl unfolding no_loops_def by auto
      qed

      moreover have "post \<noteq> ?nxt cte'"
      proof
        assume "post = ?nxt cte'"
        hence "m \<turnstile> post \<leadsto> post" using postcte vd cc post0
          by (auto simp: next_unfold' elim: valid_dlistE intro: precte)
        thus False using nl unfolding no_loops_def by auto
      qed

      ultimately have ?thesis using p vd cc rn postcte npostcte pre0 mp
        unfolding cte_mdb_prop_def
        by (fastforce simp: modify_map_other elim!: valid_dlistEn)
    } moreover
    {
      assume "ptr = target"

      hence ?thesis using m1 tpre tpost cn prepost postcte
        by (simp add: modify_map_other modify_map_same)
    } moreover
    {
      assume "ptr \<noteq> pre" and "ptr \<noteq> post" and "ptr \<noteq> target"
      hence ?thesis using m1 mp vd tpre tpost cn cp rn rp postcte npostcte precte nprecte
        unfolding cte_mdb_prop_def
        by (auto elim: valid_dlistEn simp: modify_map_app)
    }
    ultimately show ?thesis using prepost tpre tpost
      by (cases "ptr = post \<or> ptr = ptr \<or> ptr = target") auto
  qed
qed

lemma mdb_chain_0_modify_map_prev:
  "mdb_chain_0 m \<Longrightarrow> mdb_chain_0 (modify_map m ptr (cteMDBNode_update (mdbPrev_update f)))"
  unfolding mdb_chain_0_def
  apply rule
  apply (rule update_prev_next_trancl)
   apply (clarsimp simp: modify_map_def dom_def split: option.splits split_if_asm)
   done

lemma mdb_chain_0_modify_map_next:
  assumes chain: "mdb_chain_0 m"
  and      no0:  "no_0 m"
  and     dom:   "target \<in> dom m"
  and   npath:   "\<not> m \<turnstile> target \<leadsto>\<^sup>* ptr"
  shows
  "mdb_chain_0 (modify_map m ptr (cteMDBNode_update (mdbNext_update (\<lambda>_. target))))"
  (is "mdb_chain_0 ?M")
  unfolding mdb_chain_0_def
proof
  fix x
  assume "x \<in> dom ?M"
  hence xd: "x \<in> dom m"
    by (clarsimp simp: modify_map_def dom_def split: split_if_asm)
  hence x0: "m \<turnstile> x \<leadsto>\<^sup>+ 0" using chain unfolding mdb_chain_0_def by simp

  from dom have t0: "m \<turnstile> target \<leadsto>\<^sup>+ 0"
    using chain unfolding mdb_chain_0_def by simp

  show "?M \<turnstile> x \<leadsto>\<^sup>+ 0"
  proof (cases "m ptr")
    case None
    thus ?thesis
      by (simp add: modify_map_def, rule subst, subst fun_upd_triv) (rule x0)
  next
    case (Some cte)
    show ?thesis
    proof (cases "m \<turnstile> x \<leadsto>\<^sup>* ptr")
      case False
      thus ?thesis
        apply (subst next_update_is_modify [symmetric, OF _ refl])
        apply (rule Some)
        apply (erule mdb_trancl_other_update [OF x0])
        done
    next
      case True
      hence "?M \<turnstile> x \<leadsto>\<^sup>* ptr"
        apply (subst next_update_is_modify [symmetric, OF _ refl])
        apply (rule Some)
        apply (erule next_rtrancl_tranclE)
        apply simp
        apply (rule trancl_into_rtrancl)
        apply (erule no_loops_upd_last [OF mdb_chain_0_no_loops [OF chain no0]])
        done
      moreover have "?M \<turnstile> ptr \<leadsto> target"
        apply (subst next_update_is_modify [symmetric, OF _ refl])
        apply (rule Some)
        apply (simp add: mdb_next_update)
        done
      moreover have "?M \<turnstile> target \<leadsto>\<^sup>+ 0" using t0
        apply (subst next_update_is_modify [symmetric, OF _ refl])
        apply (rule Some)
        apply (erule mdb_trancl_other_update [OF _ npath])
        done
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma mdb_chain_0D:
  "\<lbrakk> mdb_chain_0 m; p \<in> dom m \<rbrakk> \<Longrightarrow> m \<turnstile> p \<leadsto>\<^sup>+ 0"
  unfolding mdb_chain_0_def by auto

lemma mdb_chain_0_nextD:
  "\<lbrakk> mdb_chain_0 m; m p = Some cte \<rbrakk> \<Longrightarrow> m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* 0"
  apply (drule mdb_chain_0D)
   apply (erule domI)
  apply (erule tranclE2)
   apply (simp add: next_unfold')
  apply (simp add: next_unfold')
  done

lemma null_mdb_no_next:
  "\<lbrakk> valid_dlist m; no_0 m;
  cte_mdb_prop m target (\<lambda>m. mdbPrev m = nullPointer \<and> mdbNext m = nullPointer) \<rbrakk>
  \<Longrightarrow> \<not> m \<turnstile> x \<leadsto> target"
  unfolding cte_mdb_prop_def
  by (auto elim: valid_dlistE elim!: valid_mdb_ctesE
    simp: nullPointer_def no_0_def next_unfold')

lemma null_mdb_no_trancl:
  "\<lbrakk> valid_dlist m; no_0 m;
  cte_mdb_prop m target (\<lambda>m. mdbPrev m = nullPointer \<and> mdbNext m = nullPointer) \<rbrakk>
  \<Longrightarrow> \<not> m \<turnstile> x \<leadsto>\<^sup>+ target"
  by (auto dest: null_mdb_no_next elim: tranclE)

lemma null_mdb_no_next2:
  "\<lbrakk> no_0 m; x \<noteq> 0;
  cte_mdb_prop m target (\<lambda>m. mdbPrev m = nullPointer \<and> mdbNext m = nullPointer) \<rbrakk>
  \<Longrightarrow> \<not> m \<turnstile> target \<leadsto> x"
  unfolding cte_mdb_prop_def
  by (auto elim!: valid_mdb_ctesE simp: nullPointer_def no_0_def next_unfold')

lemma null_mdb_no_trancl2:
  "\<lbrakk> no_0 m; x \<noteq> 0;
  cte_mdb_prop m target (\<lambda>m. mdbPrev m = nullPointer \<and> mdbNext m = nullPointer) \<rbrakk>
  \<Longrightarrow> \<not> m \<turnstile> target \<leadsto>\<^sup>+ x"
  apply rule
  apply (erule tranclE2)
   apply (drule (2) null_mdb_no_next2)
   apply simp
  apply (drule (1) no_0_lhs_trancl)
  apply (drule (2) null_mdb_no_next2, fastforce)
  done

definition
  "capASID cap \<equiv> case cap of
    ArchObjectCap (PageCap _ _ _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageDirectoryCap _ (Some asid)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

lemmas capASID_simps [simp] =
  capASID_def [split_simps capability.split arch_capability.split option.split prod.split]

definition
  "cap_asid_base' cap \<equiv> case cap of
    ArchObjectCap (ASIDPoolCap _ asid) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

lemmas cap_asid_base'_simps [simp] =
  cap_asid_base'_def [split_simps capability.split arch_capability.split option.split prod.split]

definition
  "cap_vptr' cap \<equiv> case cap of
    ArchObjectCap (PageCap _ _ _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | ArchObjectCap (PageTableCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | _ \<Rightarrow> None"

lemmas cap_vptr'_simps [simp] =
  cap_vptr'_def [split_simps capability.split arch_capability.split option.split prod.split]

definition
  "weak_derived' cap cap' \<equiv>
  capMasterCap cap = capMasterCap cap' \<and>
  capBadge cap = capBadge cap' \<and>
  capASID cap = capASID cap' \<and>
  cap_asid_base' cap = cap_asid_base' cap' \<and>
  cap_vptr' cap = cap_vptr' cap' \<and>
  (isReplyCap cap \<longrightarrow> cap = cap')"

lemma capASID_update [simp]:
  "capASID (RetypeDecls_H.updateCapData P x c) = capASID c"
  unfolding capASID_def
  apply (cases c, simp_all add: updateCapData_def isCap_simps Let_def)
  apply (case_tac arch_capability,
         simp_all add: updateCapData_def
                       ArchRetype_H.updateCapData_def
                       isCap_simps Let_def)
  done

lemma cap_vptr_update' [simp]:
  "cap_vptr' (RetypeDecls_H.updateCapData P x c) = cap_vptr' c"
  unfolding capASID_def
  apply (cases c, simp_all add: updateCapData_def isCap_simps Let_def)
  apply (case_tac arch_capability,
         simp_all add: updateCapData_def
                       ArchRetype_H.updateCapData_def
                       isCap_simps Let_def)
  done

lemma cap_asid_base_update' [simp]:
  "cap_asid_base' (RetypeDecls_H.updateCapData P x c) = cap_asid_base' c"
  unfolding cap_asid_base'_def
  apply (cases c, simp_all add: updateCapData_def isCap_simps Let_def)
  apply (case_tac arch_capability,
         simp_all add: updateCapData_def
                       ArchRetype_H.updateCapData_def
                       isCap_simps Let_def)
  done

lemma updateCapData_Master:
  "updateCapData P d cap \<noteq> NullCap \<Longrightarrow>
   capMasterCap (updateCapData P d cap) = capMasterCap cap"
  apply (cases cap, simp_all add: updateCapData_def isCap_simps Let_def
                           split: split_if_asm)
  apply (case_tac arch_capability, simp_all add: ArchRetype_H.updateCapData_def)
  done

lemma updateCapData_Reply:
  "isReplyCap (updateCapData P x c) = isReplyCap c"
  apply (cases "updateCapData P x c = NullCap")
   apply (clarsimp simp: isCap_simps)
   apply (simp add: updateCapData_def isCap_simps Let_def)
  apply (drule updateCapData_Master)
  apply (rule master_eqI, rule isCap_Master)
  apply simp
  done

lemma weak_derived_updateCapData:
  "\<lbrakk> (updateCapData P x c) \<noteq> NullCap; weak_derived' c c';
      capBadge (updateCapData P x c) = capBadge c' \<rbrakk>
  \<Longrightarrow> weak_derived' (updateCapData P x c) c'"
  apply (clarsimp simp add: weak_derived'_def updateCapData_Master)
  apply (clarsimp elim: impE dest!: iffD1[OF updateCapData_Reply])
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: Let_def isCap_simps updateCapData_def)
  done

lemma maskCapRights_Reply:
  "isReplyCap (maskCapRights r c) = isReplyCap c"
  apply (insert capMasterCap_maskCapRights)
  apply (rule master_eqI, rule isCap_Master)
  apply simp
  done

lemma capASID_mask [simp]:
  "capASID (maskCapRights x c) = capASID c"
  unfolding capASID_def
  apply (cases c, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (case_tac arch_capability,
         simp_all add: maskCapRights_def ArchRetype_H.maskCapRights_def isCap_simps Let_def)
  done

lemma cap_vptr_mask' [simp]:
  "cap_vptr' (maskCapRights x c) = cap_vptr' c"
  unfolding cap_vptr'_def
  apply (cases c, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (case_tac arch_capability,
         simp_all add: maskCapRights_def ArchRetype_H.maskCapRights_def isCap_simps Let_def)
  done

lemma cap_asid_base_mask' [simp]:
  "cap_asid_base' (maskCapRights x c) = cap_asid_base' c"
  unfolding cap_vptr'_def
  apply (cases c, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (case_tac arch_capability,
         simp_all add: maskCapRights_def ArchRetype_H.maskCapRights_def isCap_simps Let_def)
  done

lemma weak_derived_maskCapRights:
  "\<lbrakk> weak_derived' c c' \<rbrakk> \<Longrightarrow> weak_derived' (maskCapRights x c) c'"
  apply (clarsimp simp: weak_derived'_def)
  apply (clarsimp dest!: iffD1[OF maskCapRights_Reply])
  apply (clarsimp simp: isCap_simps maskCapRights_def Let_def)
  done

lemma mdb_next_dlistD:
  "\<lbrakk> m \<turnstile> p \<leadsto> p'; p' \<noteq> 0; valid_dlist m \<rbrakk> \<Longrightarrow> \<exists>cap node. m p' = Some (CTE cap node) \<and> mdbPrev node = p"
  apply (clarsimp simp: mdb_next_unfold)
  apply (erule (1) valid_dlistEn)
   apply simp
  apply (case_tac cte')
  apply clarsimp
  done

lemmas cteInsert_valid_objs = cap_insert_objs'

lemma cteInsert_valid_cap:
  "\<lbrace>valid_cap' c\<rbrace> cteInsert cap src dest \<lbrace> \<lambda>_. valid_cap' c\<rbrace>"
  unfolding cteInsert_def updateCap_def setUntypedCapAsFull_def
  apply (simp split del: split_if)
  apply (wp updateMDB_valid_cap setCTE_valid_cap )
   prefer 2
   apply (rule getCTE_sp)
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule getCTE_sp)
  apply clarsimp
  done

lemma subtree_not_Null:
  assumes null: "m p = Some (CTE capability.NullCap node)"
  assumes sub: "m \<turnstile> c \<rightarrow> p"
  shows "False" using sub null
  by induct (auto simp: parentOf_def)

lemma Null_not_subtree:
  assumes null: "m c = Some (CTE capability.NullCap node)"
  assumes sub: "m \<turnstile> c \<rightarrow> p"
  shows "False" using sub null
  by induct (auto simp: parentOf_def)

lemma subtree_Null_update:
  assumes "no_0 m" "valid_dlist m"
  assumes null: "m p = Some (CTE NullCap node)"
  assumes node: "mdbPrev node = 0"
  assumes init: "mdbNext (cteMDBNode cte) = 0"
  shows "m \<turnstile> c \<rightarrow> c' = m (p \<mapsto> cte) \<turnstile> c \<rightarrow> c'"
proof
  assume "m \<turnstile> c \<rightarrow> c'"
  thus "m (p \<mapsto> cte) \<turnstile> c \<rightarrow> c'" using null init
  proof induct
    case direct_parent
    thus ?case
      apply -
      apply (rule subtree.direct_parent)
        apply (clarsimp simp add: mdb_next_unfold parentOf_def)
       apply assumption
      apply (simp add: parentOf_def)
      apply (rule conjI)
       apply clarsimp
      apply clarsimp
      done
  next
    case (trans_parent y z)
    have "m \<turnstile> c \<rightarrow> y" "m \<turnstile> y \<leadsto> z" "z \<noteq> 0" "m \<turnstile> c parentOf z" by fact+
    with trans_parent.prems
    show ?case
      apply -
      apply (rule subtree.trans_parent)
         apply (erule (1) trans_parent.hyps)
        apply (clarsimp simp: mdb_next_unfold parentOf_def)
        apply (drule (1) subtree_not_Null)
        apply simp
       apply assumption
      apply (fastforce simp: parentOf_def)
      done
  qed
next
  assume m: "m (p \<mapsto> cte) \<turnstile> c \<rightarrow> c'"
  thus "m \<turnstile> c \<rightarrow> c'" using assms m
  proof induct
    case (direct_parent x)
    thus ?case
      apply -
      apply (cases "c=p")
       apply (clarsimp simp: mdb_next_unfold)
      apply (rule subtree.direct_parent)
        apply (clarsimp simp: mdb_next_unfold)
       apply assumption
      apply (cases "p\<noteq>x")
       apply (clarsimp simp: parentOf_def  split: split_if_asm)
      apply clarsimp
      apply (clarsimp simp: mdb_next_unfold)
      apply (case_tac z)
      apply clarsimp
      apply (clarsimp simp: no_0_def valid_dlist_def Let_def)
      apply (erule_tac x=c in allE)
      apply clarsimp
      done
  next
    case (trans_parent x y)
    have "m(p \<mapsto> cte) \<turnstile> c \<rightarrow> x" "m(p \<mapsto> cte) \<turnstile> x \<leadsto> y"
         "y \<noteq> 0" "m(p \<mapsto> cte) \<turnstile> c parentOf y" by fact+
    with trans_parent.prems
    show ?case
      apply -
      apply (cases "p=x")
       apply clarsimp
       apply (clarsimp simp: mdb_next_unfold)
      apply (frule (5) trans_parent.hyps)
      apply (rule subtree.trans_parent)
         apply assumption
        apply (clarsimp simp: mdb_next_unfold)
       apply assumption
      apply (clarsimp simp: parentOf_def simp del: fun_upd_apply)
      apply (cases "p=y")
       apply clarsimp
       apply (clarsimp simp: mdb_next_unfold)
       apply (clarsimp simp: valid_dlist_def Let_def)
       apply (erule_tac x=x in allE)
       apply (clarsimp simp: no_0_def)
      apply (case_tac "p\<noteq>c")
       apply clarsimp
      apply clarsimp
      apply (erule (1) Null_not_subtree)
      done
  qed
qed


corollary descendants_of_Null_update':
  assumes "no_0 m" "valid_dlist m"
  assumes "m p = Some (CTE NullCap node)"
  assumes "mdbPrev node = 0"
  assumes "mdbNext (cteMDBNode cte) = 0"
  shows "descendants_of' c (m (p \<mapsto> cte)) = descendants_of' c m" using assms
  by (simp add: descendants_of'_def subtree_Null_update [symmetric])

lemma ps_clear_16:
  "\<lbrakk> ps_clear p 9 s; is_aligned p 9 \<rbrakk> \<Longrightarrow> ksPSpace s (p + 16) = None"
  apply (simp add: ps_clear_def)
  apply (drule equals0D[where a="p + 16"])
  apply (simp add: dom_def field_simps)
  apply (drule mp)
   apply (rule word_plus_mono_right)
    apply simp
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (erule mp)
  apply (erule is_aligned_no_wrap')
  apply simp
  done

lemma ps_clear_16':
  "\<lbrakk> ksPSpace s p = Some (KOTCB tcb); pspace_aligned' s; pspace_distinct' s \<rbrakk>
      \<Longrightarrow> ksPSpace s (p + 16) = None"
  by (clarsimp simp: pspace_aligned'_def pspace_distinct'_def
                     objBits_simps ps_clear_16
        | drule(1) bspec[OF _ domI])+

lemma cte_at_cte_map_in_obj_bits:
  "\<lbrakk> cte_at p s; pspace_aligned s; valid_objs s \<rbrakk>
     \<Longrightarrow> cte_map p \<in> {fst p .. fst p + 2 ^ (obj_bits (the (kheap s (fst p)))) - 1}
           \<and> kheap s (fst p) \<noteq> None"
  apply (simp add: cte_at_cases)
  apply (elim disjE conjE exE)
   apply (clarsimp simp: well_formed_cnode_n_def)
   apply (drule(1) pspace_alignedD[rotated])
   apply (erule(1) valid_objsE)
   apply (frule arg_cong[where f="\<lambda>S. snd p \<in> S"])
   apply (simp(no_asm_use) add: domIff)
   apply (clarsimp simp: cte_map_def split_def obj_bits.simps cte_level_bits_def
                         well_formed_cnode_n_def length_set_helper ex_with_length
                         valid_obj_def valid_cs_size_def valid_cs_def)
   apply (subgoal_tac "of_bl (snd p) * 16 < 2 ^ (4 + length (snd p))")
    apply (rule conjI)
     apply (erule is_aligned_no_wrap')
     apply assumption
    apply (subst add_diff_eq[symmetric])
    apply (rule word_plus_mono_right)
     apply (erule minus_one_helper3)
    apply (erule is_aligned_no_wrap')
    apply (rule word_power_less_1)
    apply (simp add: cte_level_bits_def word_bits_def)
   apply (simp add: power_add)
   apply (subst mult_commute, rule word_mult_less_mono1)
     apply (rule of_bl_length)
     apply (simp add: word_bits_def)
    apply simp
   apply (simp add: cte_level_bits_def word_bits_def)
   apply (drule power_strict_increasing [where a="2 :: nat"])
    apply simp
   apply simp
  apply (clarsimp simp: cte_map_def split_def field_simps)
  apply (subgoal_tac "of_bl (snd p) * 16 < (512 :: word32)")
   apply (drule(1) pspace_alignedD[rotated])
   apply (rule conjI)
    apply (erule is_aligned_no_wrap')
     apply (simp add: word_bits_conv)
    apply simp
   apply (rule word_plus_mono_right)
    apply (drule minus_one_helper3)
    apply simp
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1
              split: split_if_asm)
  done

lemma cte_map_inj:
  assumes neq: "p \<noteq> p'"
  assumes c1: "cte_at p s"
  assumes c2: "cte_at p' s"
  assumes vo: "valid_objs s"
  assumes al: "pspace_aligned s"
  assumes pd: "pspace_distinct s"
  shows "cte_map p \<noteq> cte_map p'"
  using cte_at_cte_map_in_obj_bits [OF c1 al vo]
        cte_at_cte_map_in_obj_bits [OF c2 al vo]
        pd
  apply (clarsimp simp: pspace_distinct_def
              simp del: atLeastAtMost_iff Int_atLeastAtMost)
  apply (elim allE, drule mp)
   apply (erule conjI)+
   defer
   apply (simp add: field_simps
               del: atLeastAtMost_iff Int_atLeastAtMost)
   apply blast
  apply (clarsimp simp: cte_map_def split_def)
  apply (thin_tac "?b \<le> ?a")+
  apply (rule notE[OF neq])
  apply (insert cte_at_length_limit [OF c1 vo])
  apply (simp add: shiftl_t2n[where n=4, simplified, simplified mult_ac, symmetric]
                   word_bits_def cte_level_bits_def Pair_fst_snd_eq)
  apply (insert cte_at_cref_len[where p="fst p" and c="snd p" and c'="snd p'", simplified, OF c1])
  apply (simp add: c2)
  apply (subst rev_is_rev_conv[symmetric])
  apply (rule nth_equalityI)
   apply simp
  apply clarsimp
  apply (drule_tac x="i + 4" in word_eqD)
  apply (simp add: nth_shiftl test_bit_of_bl nth_rev)
  done

lemma cte_map_inj_ps:
  assumes "p \<noteq> p'"
  assumes "cte_at p s"
  assumes "cte_at p' s"
  assumes "valid_pspace s"
  shows "cte_map p \<noteq> cte_map p'" using assms
  apply -
  apply (rule cte_map_inj)
  apply (auto simp: valid_pspace_def)
  done

lemma cte_map_inj_eq:
  "\<lbrakk>cte_map p = cte_map p';
   cte_at p s; cte_at p' s;
   valid_objs s; pspace_aligned s; pspace_distinct s\<rbrakk>
  \<Longrightarrow> p = p'"
  apply (rule classical)
  apply (drule (5) cte_map_inj)
  apply simp
  done

lemma tcb_cases_related2:
  "tcb_cte_cases (v - x) = Some (getF, setF) \<Longrightarrow>
   \<exists>getF' setF' restr. tcb_cap_cases (tcb_cnode_index (unat ((v - x) >> 4))) = Some (getF', setF', restr)
          \<and> cte_map (x, tcb_cnode_index (unat ((v - x) >> 4))) = v
          \<and> (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow> cap_relation (getF' tcb) (cteCap (getF tcb')))
          \<and> (\<forall>tcb tcb' cap cte. tcb_relation tcb tcb' \<longrightarrow> cap_relation cap (cteCap cte)
                        \<longrightarrow> tcb_relation (setF' (\<lambda>x. cap) tcb) (setF (\<lambda>x. cte) tcb'))"
  apply (clarsimp simp: tcb_cte_cases_def tcb_relation_def
                        tcb_cap_cases_simps[simplified]
                 split: split_if_asm)
  apply (simp_all add: tcb_cnode_index_def cte_map_def field_simps to_bl_1)
  done

lemma other_obj_relation_KOCTE[simp]:
  "\<not> other_obj_relation ko (KOCTE cte)"
  by (simp add: other_obj_relation_def
         split: Structures_A.kernel_object.splits
                ARM_Structs_A.arch_kernel_obj.splits)

lemma cte_map_pulls_tcb_to_abstract:
  "\<lbrakk> y = cte_map z; pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' x = Some (KOTCB tcb);
     pspace_aligned s; pspace_distinct s; valid_objs s;
     cte_at z s; (y - x) \<in> dom tcb_cte_cases \<rbrakk>
     \<Longrightarrow> \<exists>tcb'. kheap s x = Some (TCB tcb') \<and> tcb_relation tcb' tcb
                  \<and> (z = (x, tcb_cnode_index (unat ((y - x) >> 4))))"
  apply (rule pspace_dom_relatedE, assumption+)
  apply (erule(1) obj_relation_cutsE, simp_all)
  apply (clarsimp simp: other_obj_relation_def
                 split: Structures_A.kernel_object.split_asm
                        ARM_Structs_A.arch_kernel_obj.split_asm)
  apply (drule tcb_cases_related2)
  apply clarsimp
  apply (frule(1) cte_wp_at_tcbI [OF _ _ TrueI, where t="(a, b)", standard, simplified])
  apply (erule(5) cte_map_inj_eq [OF sym])
  done

lemma pspace_relation_update_tcbs:
  "\<lbrakk> pspace_relation s s'; s x = Some (TCB otcb); s' x = Some (KOTCB otcb');
        tcb_relation tcb tcb' \<rbrakk>
       \<Longrightarrow> pspace_relation (s(x \<mapsto> TCB tcb)) (s'(x \<mapsto> KOTCB tcb'))"
  apply (simp add: pspace_relation_def pspace_dom_update
                   dom_fun_upd2 a_type_def
              del: dom_fun_upd)
  apply (erule conjE)
  apply (rule ballI, drule(1) bspec)
  apply (rule conjI, simp add: other_obj_relation_def)
  apply (clarsimp split: Structures_A.kernel_object.split_asm)
  apply (drule bspec, fastforce)
  apply clarsimp
  apply (erule(1) obj_relation_cutsE, simp_all)
  done

lemma cte_map_pulls_cte_to_abstract:
  "\<lbrakk> y = cte_map z; pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' y = Some (KOCTE cte);
     valid_objs s; pspace_aligned s; pspace_distinct s; cte_at z s \<rbrakk>
     \<Longrightarrow> \<exists>sz cs cap. kheap s (fst z) = Some (CNode sz cs) \<and> cs (snd z) = Some cap
                  \<and> cap_relation cap (cteCap cte)"
  apply (rule pspace_dom_relatedE, assumption+)
  apply (erule(1) obj_relation_cutsE, simp_all)
  apply clarsimp
  apply (frule(1) cte_map_inj_eq[OF sym], simp_all)
  apply (rule cte_wp_at_cteI, fastforce+)
  done

lemma pspace_relation_update_ctes:
  assumes ps: "pspace_relation s s'"
    and octe: "s' z = Some (KOCTE octe)"
    and  s'': "\<And>x. s'' x = (case (s x) of None \<Rightarrow> None | Some ko \<Rightarrow>
                    (case ko of CNode sz cs \<Rightarrow>
                          Some (CNode sz (\<lambda>y. if y \<in> dom cs \<and> cte_map (x, y) = z
                                              then Some cap else cs y))
                                    | _ \<Rightarrow> Some ko))"
     and rel: "cap_relation cap (cteCap cte')"
       shows  "pspace_relation s'' (s'(z \<mapsto> KOCTE cte'))"
proof -
  have funny_update_no_dom:
    "\<And>fun P v. dom (\<lambda>y. if y \<in> dom fun \<and> P y then Some v else fun y)
      = dom fun"
    by (rule set_eqI, simp add: domIff)

  have funny_update_well_formed_cnode:
    "\<And>sz fun P v.
      well_formed_cnode_n sz (\<lambda>y. if y \<in> dom fun \<and> P y then Some v else fun y)
      = well_formed_cnode_n sz fun"
    by (simp add: well_formed_cnode_n_def funny_update_no_dom)

  have obj_relation_cuts1:
  "\<And>ko x. obj_relation_cuts (the (case ko of CNode sz cs \<Rightarrow>
                                       Some (CNode sz (\<lambda>y. if y \<in> dom cs \<and> cte_map (x, y) = z
                                                           then Some cap else cs y))
                                    | _ \<Rightarrow> Some ko)) x
             = obj_relation_cuts ko x"
    by (simp split: Structures_A.kernel_object.split
               add: funny_update_well_formed_cnode funny_update_no_dom)

  have domEq[simp]:
    "dom s'' = dom s"
    using s''
    apply (intro set_eqI)
    apply (simp add: domIff split: option.split Structures_A.kernel_object.split)
    done

  have obj_relation_cuts2:
  "\<And>x. x \<in> dom s'' \<Longrightarrow> obj_relation_cuts (the (s'' x)) x = obj_relation_cuts (the (s x)) x"
    using s''
    by (clarsimp simp add: obj_relation_cuts1 dest!: domD)

  show ?thesis using ps octe
    apply (clarsimp simp add: pspace_relation_def dom_fun_upd2
                    simp del: dom_fun_upd split del: split_if)
    apply (rule conjI)
     apply (erule subst[where t="dom s'"])
     apply (simp add: pspace_dom_def obj_relation_cuts2)
    apply (simp add: obj_relation_cuts2)
    apply (rule ballI, drule(1) bspec)+
    apply clarsimp
    apply (intro conjI impI)
     apply (simp add: s'')
     apply (rule obj_relation_cutsE, assumption+, simp_all)[1]
     apply (clarsimp simp: cte_relation_def rel)
    apply (rule obj_relation_cutsE, assumption+, simp_all add: s'')
     apply (clarsimp simp: cte_relation_def)
    apply (clarsimp simp: is_other_obj_relation_type other_obj_relation_def
                   split: Structures_A.kernel_object.split_asm)
    done
qed

definition pspace_relations where
  "pspace_relations ekh kh kh' \<equiv> pspace_relation kh kh' \<and> ekheap_relation ekh kh'"

lemma set_cap_not_quite_corres_prequel:
  assumes cr:
  "pspace_relations (ekheap s) (kheap s) (ksPSpace s')"
  "(x,t') \<in> fst (setCTE p' c' s')"
  "valid_objs s" "pspace_aligned s" "pspace_distinct s" "cte_at p s"
  "pspace_aligned' s'" "pspace_distinct' s'"
  assumes c: "cap_relation c (cteCap c')"
  assumes p: "p' = cte_map p"
  shows "\<exists>t. ((),t) \<in> fst (set_cap c p s) \<and>
             pspace_relations (ekheap t) (kheap t) (ksPSpace t')"
  using cr
  apply (clarsimp simp: setCTE_def setObject_def in_monad split_def)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim disjE exE conjE)
   apply (clarsimp simp: lookupAround2_char1 pspace_relations_def)
   apply (frule(5) cte_map_pulls_tcb_to_abstract[OF p])
    apply (simp add: domI)
   apply (frule tcb_cases_related2)
   apply (clarsimp simp: set_cap_def2 split_def bind_def get_object_def
                         simpler_gets_def assert_def fail_def return_def
                         set_object_def get_def put_def)
   apply (rule conjI)
    apply (erule(2) pspace_relation_update_tcbs)
    apply (simp add: c)
   apply (clarsimp simp: ekheap_relation_def pspace_relation_def)
   apply (drule bspec, erule domI)
   apply (clarsimp simp: etcb_relation_def tcb_cte_cases_def split: split_if_asm)
  apply (clarsimp simp: pspace_relations_def)
  apply (frule(5) cte_map_pulls_cte_to_abstract[OF p])
  apply (clarsimp simp: set_cap_def split_def bind_def get_object_def
                        simpler_gets_def assert_def fail_def return_def
                        set_object_def get_def put_def domI)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_cs_def valid_cs_size_def exI)
  apply (rule conjI)
   apply (erule(1) pspace_relation_update_ctes[where cap=c])
    apply clarsimp
    apply (intro conjI impI)
     apply (rule ext, clarsimp simp add: domI p)
     apply (drule cte_map_inj_eq [OF _ _ cr(6) cr(3-5)])
      apply (simp add: cte_at_cases domI)
     apply (simp add: Pair_fst_snd_eq)
    apply (insert p)[1]
    apply (clarsimp split: option.split Structures_A.kernel_object.split
                   intro!: ext)
    apply (drule cte_map_inj_eq [OF _ _ cr(6) cr(3-5)])
     apply (simp add: cte_at_cases domI well_formed_cnode_invsI[OF cr(3)])
    apply clarsimp
   apply (simp add: c)
  apply (clarsimp simp: ekheap_relation_def pspace_relation_def)
  apply (drule bspec, erule domI)
  apply (clarsimp simp: etcb_relation_def tcb_cte_cases_def split: split_if_asm)
  done

lemma setCTE_pspace_only:
  "(rv, s') \<in> fst (setCTE p v s) \<Longrightarrow> \<exists>ps'. s' = ksPSpace_update (\<lambda>s. ps') s"
  apply (clarsimp simp: setCTE_def setObject_def in_monad split_def
                 dest!: in_inv_by_hoareD [OF updateObject_cte_inv])
  apply (rule exI, rule refl)
  done

lemma set_cap_not_quite_corres:
  assumes cr:
  "pspace_relations (ekheap s) (kheap s) (ksPSpace s')"
  "cur_thread s = ksCurThread s'"
  "idle_thread s = ksIdleThread s'"
  "machine_state s = ksMachineState s'"
  "work_units_completed s = ksWorkUnitsCompleted s'"
  "domain_index s = ksDomScheduleIdx s'"
  "domain_list s = ksDomSchedule s'"
  "cur_domain s = ksCurDomain s'"
  "domain_time s = ksDomainTime s'"
  "(x,t') \<in> fst (updateCap p' c' s')"
  "valid_objs s" "pspace_aligned s" "pspace_distinct s" "cte_at p s"
  "pspace_aligned' s'" "pspace_distinct' s'"
  "interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s')"
  "(arch_state s, ksArchState s') \<in> arch_state_relation"
  assumes c: "cap_relation c c'"
  assumes p: "p' = cte_map p"
  shows "\<exists>t. ((),t) \<in> fst (set_cap c p s) \<and>
             pspace_relations (ekheap t) (kheap t) (ksPSpace t') \<and>
             cdt t = cdt s \<and>
             cdt_list t = cdt_list s \<and>
             ekheap t = ekheap s \<and>
             scheduler_action t = scheduler_action s \<and>
             ready_queues t = ready_queues s \<and>
             is_original_cap t = is_original_cap s \<and>
             interrupt_state_relation (interrupt_irq_node t) (interrupt_states t)
                              (ksInterruptState t') \<and>
             (arch_state t, ksArchState t') \<in> arch_state_relation \<and>
             cur_thread t = ksCurThread t' \<and>
             idle_thread t = ksIdleThread t' \<and>
             machine_state t = ksMachineState t' \<and>
             work_units_completed t = ksWorkUnitsCompleted t' \<and>
             domain_index t = ksDomScheduleIdx t' \<and>
             domain_list t = ksDomSchedule t' \<and>
             cur_domain t = ksCurDomain t' \<and>
             domain_time t = ksDomainTime t'"
  using cr
  apply (clarsimp simp: updateCap_def in_monad)
  apply (drule use_valid [OF _ getCTE_sp[where P="\<lambda>s. s2 = s"], OF _ refl, standard])
  apply clarsimp
  apply (drule(7) set_cap_not_quite_corres_prequel)
    apply simp
    apply (rule c)
   apply (rule p)
  apply (erule exEI)
  apply clarsimp
  apply (frule setCTE_pspace_only)
  apply (clarsimp simp: set_cap_def split_def in_monad set_object_def
                        get_object_def
                 split: Structures_A.kernel_object.split_asm split_if_asm)
  done

lemma descendants_of_eq':
  assumes "cte_at p s"
  assumes "cte_at src s"
  assumes "cdt_relation (swp cte_at s) (cdt s) m'"
  assumes "valid_mdb s"
  assumes "valid_objs s" "pspace_aligned s" "pspace_distinct s"
  shows "(cte_map src \<in> descendants_of' (cte_map p) m') = (src \<in> descendants_of p (cdt s))"
  using assms
  apply (simp add: cdt_relation_def del: split_paired_All)
  apply (rule iffI)
   prefer 2
   apply (auto simp del: split_paired_All)[1]
  apply (erule_tac x=p in allE)
  apply simp
  apply (drule sym)
  apply clarsimp
  apply (frule (1) descendants_of_cte_at)
  apply (drule (5) cte_map_inj_eq)
  apply simp
  done

lemma updateCap_stuff:
  assumes "(x, s'') \<in> fst (updateCap p cap s')"
  shows "(ctes_of s'' = modify_map (ctes_of s') p (cteCap_update (K cap))) \<and>
         gsUserPages s'' = gsUserPages s' \<and>
         gsCNodes s'' = gsCNodes s' \<and>
         ksMachineState s'' = ksMachineState s' \<and>
         ksWorkUnitsCompleted s'' = ksWorkUnitsCompleted s' \<and>
         ksCurThread s'' = ksCurThread s' \<and>
         ksIdleThread s'' = ksIdleThread s' \<and>
         ksReadyQueues s'' = ksReadyQueues s' \<and>
         ksSchedulerAction s'' = ksSchedulerAction s' \<and>
         (ksArchState s'' = ksArchState s') \<and>
         (pspace_aligned' s' \<longrightarrow> pspace_aligned' s'') \<and>
         (pspace_distinct' s' \<longrightarrow> pspace_distinct' s'')" using assms
  apply (clarsimp simp: updateCap_def in_monad)
  apply (drule use_valid [where P="\<lambda>s. s2 = s", OF _ getCTE_sp refl, standard])
  apply (rule conjI)
   apply (erule use_valid [OF _ setCTE_ctes_of_wp])
   apply (clarsimp simp: cte_wp_at_ctes_of modify_map_apply)
  apply (frule setCTE_pspace_only)
  apply (clarsimp simp: setCTE_def)
  apply (intro conjI impI)
   apply (erule(1) use_valid [OF _ setObject_aligned])
  apply (erule(1) use_valid [OF _ setObject_distinct])
  done

(* FIXME: move *)
lemma pspace_relation_cte_wp_atI':
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
     cte_wp_at' (op = cte) x s'; valid_objs s \<rbrakk>
  \<Longrightarrow> \<exists>c slot. cte_wp_at (op = c) slot s \<and> cap_relation c (cteCap cte) \<and> x = cte_map slot"
  apply (simp add: cte_wp_at_cases')
  apply (elim disjE conjE exE)
   apply (erule(1) pspace_dom_relatedE)
   apply (erule(1) obj_relation_cutsE, simp_all)[1]
   apply (intro exI, rule conjI[OF _ conjI [OF _ refl]])
    apply (simp add: cte_wp_at_cases domI well_formed_cnode_invsI)
   apply simp
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE, simp_all)
  apply (simp add: other_obj_relation_def
            split: Structures_A.kernel_object.split_asm
                   ARM_Structs_A.arch_kernel_obj.split_asm)
  apply (subgoal_tac "n = x - y", clarsimp)
   apply (drule tcb_cases_related2, clarsimp)
   apply (intro exI, rule conjI)
    apply (erule(1) cte_wp_at_tcbI[where t="(a, b)", simplified, standard])
    apply fastforce
   apply simp
  apply clarsimp
  done

lemma pspace_relation_cte_wp_atI:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
     ctes_of (s' :: kernel_state) x = Some cte; valid_objs s \<rbrakk>
  \<Longrightarrow> \<exists>c slot. cte_wp_at (op = c) slot s \<and> cap_relation c (cteCap cte) \<and> x = cte_map slot"
  apply (erule pspace_relation_cte_wp_atI'[where x=x])
   apply (simp add: cte_wp_at_ctes_of)
  apply assumption
  done

lemma sameRegion_corres:
  "\<lbrakk> sameRegionAs c' d'; cap_relation c c'; cap_relation d d' \<rbrakk>
  \<Longrightarrow> same_region_as c d"
  by (simp add: same_region_as_relation)

lemma is_final_cap_unique:
  assumes cte: "ctes_of s' (cte_map slot) = Some cte"
  assumes fin: "cte_wp_at (\<lambda>c. final_matters c \<and> is_final_cap' c s) slot s"
  assumes psr: "pspace_relation (kheap s) (ksPSpace s')"
  assumes cte': "ctes_of s' x = Some cte'"
  assumes neq: "x \<noteq> cte_map slot"
  assumes region: "sameRegionAs (cteCap cte) (cteCap cte')"
  assumes valid: "pspace_aligned s" "valid_objs s" "pspace_aligned' s'" "pspace_distinct' s'"
  shows "False"
proof -
  from fin obtain c where
    c: "cte_wp_at (op = c) slot s" and
    final: "is_final_cap' c s" and
    fm: "final_matters c"
    by (auto simp add: cte_wp_at_cases)
  with valid psr cte
  have cr: "cap_relation c (cteCap cte)"
    by (auto dest!: pspace_relation_ctes_ofI)
  from cte' psr valid
  obtain slot' c' where
    c': "cte_wp_at (op = c') slot' s" and
    cr': "cap_relation c' (cteCap cte')" and
    x: "x = cte_map slot'"
    by (auto dest!: pspace_relation_cte_wp_atI)
  with neq
  have s: "slot \<noteq> slot'" by clarsimp
  from region cr cr'
  have reg: "same_region_as c c'" by (rule sameRegion_corres)
  hence fm': "final_matters c'" using fm
    apply -
    apply (rule ccontr)
    apply (simp add: final_matters_def split: cap.split_asm arch_cap.split_asm)
    done
  hence ref: "obj_refs c = obj_refs c'" using fm reg
    apply (simp add: final_matters_def split: cap.split_asm arch_cap.split_asm)
    done
  have irq: "cap_irqs c = cap_irqs c'" using reg fm fm'
    by (simp add: final_matters_def split: cap.split_asm)

  from final have refs_non_empty: "obj_refs c \<noteq> {} \<or> cap_irqs c \<noteq> {}"
    by (clarsimp simp add: is_final_cap'_def)

  def S \<equiv> "{cref. \<exists>cap'. fst (get_cap cref s) = {(cap', s)} \<and>
                      (obj_refs c \<inter> obj_refs cap' \<noteq> {}
                         \<or> cap_irqs c \<inter> cap_irqs cap' \<noteq> {})}"

  have "is_final_cap' c s = (\<exists>cref. S = {cref})"
    by (simp add: is_final_cap'_def S_def)
  moreover
  from c refs_non_empty
  have "slot \<in> S" by (simp add: S_def cte_wp_at_def)
  moreover
  from c' refs_non_empty ref irq
  have "slot' \<in> S" by (simp add: S_def cte_wp_at_def)
  ultimately
  show False using s final by auto
qed

lemma obj_refs_relation_Master:
  "cap_relation cap cap' \<Longrightarrow>
   obj_refs cap = (if isUntypedCap (capMasterCap cap') then {}
                    else if capClass (capMasterCap cap') = PhysicalClass
                    then {capUntypedPtr (capMasterCap cap')}
                    else {})"
  by (simp add: isCap_simps
         split: cap_relation_split_asm arch_cap.split_asm)

lemma cap_irqs_relation_Master:
  "cap_relation cap cap' \<Longrightarrow>
   cap_irqs cap = (case capMasterCap cap' of IRQHandlerCap irq \<Rightarrow> {irq} | _ \<Rightarrow> {})"
  by (simp split: cap_relation_split_asm arch_cap.split_asm)

lemma is_final_cap_unique_sym:
  assumes cte: "ctes_of s' (cte_map slot) = Some cte"
  assumes fin: "cte_wp_at (\<lambda>c. is_final_cap' c s) slot s"
  assumes psr: "pspace_relation (kheap s) (ksPSpace s')"
  assumes cte': "ctes_of s' x = Some cte'"
  assumes neq: "x \<noteq> cte_map slot"
  assumes master: "capMasterCap (cteCap cte') = capMasterCap (cteCap cte)"
  assumes valid: "pspace_aligned s" "valid_objs s" "pspace_aligned' s'" "pspace_distinct' s'"
  shows "False"
proof -
  from fin obtain c where
    c: "cte_wp_at (op = c) slot s" and
    final: "is_final_cap' c s"
    by (auto simp add: cte_wp_at_cases)
  with valid psr cte
  have cr: "cap_relation c (cteCap cte)"
    by (auto dest!: pspace_relation_ctes_ofI)
  from cte' psr valid
  obtain slot' c' where
    c': "cte_wp_at (op = c') slot' s" and
    cr': "cap_relation c' (cteCap cte')" and
    x: "x = cte_map slot'"
    by (auto dest!: pspace_relation_cte_wp_atI)
  with neq
  have s: "slot \<noteq> slot'" by clarsimp
  have irq: "cap_irqs c = cap_irqs c'"
  using master cr cr'
  by (simp add: cap_irqs_relation_Master)
  have ref: "obj_refs c = obj_refs c'"
  using master cr cr'
  by (simp add: obj_refs_relation_Master)

  from final have refs_non_empty: "obj_refs c \<noteq> {} \<or> cap_irqs c \<noteq> {}"
    by (clarsimp simp add: is_final_cap'_def)

  def S \<equiv> "{cref. \<exists>cap'. fst (get_cap cref s) = {(cap', s)} \<and>
                      (obj_refs c \<inter> obj_refs cap' \<noteq> {}
                         \<or> cap_irqs c \<inter> cap_irqs cap' \<noteq> {})}"

  have "is_final_cap' c s = (\<exists>cref. S = {cref})"
    by (simp add: is_final_cap'_def S_def)
  moreover
  from c refs_non_empty
  have "slot \<in> S" by (simp add: S_def cte_wp_at_def)
  moreover
  from c' refs_non_empty ref irq
  have "slot' \<in> S" by (simp add: S_def cte_wp_at_def)
  ultimately
  show False using s final by auto
qed

lemma isMDBParent_sameRegion:
  "isMDBParentOf cte cte' \<Longrightarrow> sameRegionAs (cteCap cte) (cteCap cte')"
  by (simp add: isMDBParentOf_def split: cte.split_asm split_if_asm)

lemma is_final_descendants:
  "\<lbrakk> ctes_of s' (cte_map slot) = Some cte;
     cte_wp_at (\<lambda>c. final_matters c \<and> is_final_cap' c s) slot s;
     pspace_relation (kheap s) (ksPSpace s');
     no_loops (ctes_of s');
     pspace_aligned s; valid_objs s; pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
  \<Longrightarrow> descendants_of' (cte_map slot) (ctes_of s') = {}"
  apply (clarsimp simp add: descendants_of'_def)
  apply (subgoal_tac "x \<noteq> cte_map slot")
   prefer 2
   apply clarsimp
   apply (drule subtree_mdb_next)
   apply (simp add: no_loops_trancl_simp)
  apply (erule subtree.cases)
   apply (clarsimp simp: parentOf_def)
   apply (drule isMDBParent_sameRegion)
   apply (erule (9) is_final_cap_unique)
  apply (clarsimp simp: parentOf_def)
  apply (drule isMDBParent_sameRegion)
  apply (erule (9) is_final_cap_unique)
  done

lemma is_final_no_child:
  "\<lbrakk> ctes_of s' (cte_map slot) = Some cte;
     cte_wp_at (\<lambda>c. final_matters c \<and> is_final_cap' c s) slot s;
     pspace_relation (kheap s) (ksPSpace s');
     no_loops (ctes_of s');
     pspace_aligned s; valid_objs s; pspace_aligned' s'; pspace_distinct' s';
     ctes_of s' \<turnstile> x \<rightarrow> cte_map slot \<rbrakk>
  \<Longrightarrow> \<exists>cte'. ctes_of s' x = Some cte' \<and>
            capMasterCap (cteCap cte') \<noteq> capMasterCap (cteCap cte) \<and>
            sameRegionAs (cteCap cte') (cteCap cte)"
  apply (subgoal_tac "x \<noteq> cte_map slot")
   prefer 2
   apply clarsimp
   apply (drule subtree_mdb_next)
   apply (simp add: no_loops_trancl_simp)
  apply (rule classical)
  apply clarsimp
  apply (frule cte_wp_at_weakenE, erule conjunct2)
  apply (erule subtree.cases)
   apply (clarsimp simp: parentOf_def)
   apply (drule isMDBParent_sameRegion)
   apply clarsimp
   apply (erule(9) is_final_cap_unique_sym)
  apply (clarsimp simp: parentOf_def)
  apply (drule isMDBParent_sameRegion)
  apply simp
  apply (erule(9) is_final_cap_unique_sym)
  done

lemma no_loops_no_subtree:
  "no_loops m \<Longrightarrow> m \<turnstile> x \<rightarrow> x = False"
  apply clarsimp
  apply (drule subtree_mdb_next)
  apply (simp add: no_loops_def)
  done

definition
  "caps_contained2 m \<equiv>
  \<forall>c c' cap n cap' n'.
  m c = Some (CTE cap n) \<longrightarrow> m c' = Some (CTE cap' n') \<longrightarrow>
  (isCNodeCap cap' \<or> isThreadCap cap') \<longrightarrow>
  capUntypedPtr cap' \<in> untypedRange cap \<longrightarrow>
  capUntypedPtr cap' + capUntypedSize cap' - 1 \<in> untypedRange cap"

lemma capUntypedPtr_capRange:
  "\<lbrakk> ctes_of s p = Some (CTE cap node);
     capClass cap = PhysicalClass;
     valid_objs' s \<rbrakk> \<Longrightarrow>
  capUntypedPtr cap \<in> capRange cap"
  apply (erule capAligned_capUntypedPtr[rotated])
  apply (drule (1) ctes_of_valid_cap')
  apply (erule valid_capAligned)
  done

lemma caps_contained2:
  "\<lbrakk> caps_contained' (ctes_of s); valid_objs' s \<rbrakk> \<Longrightarrow> caps_contained2 (ctes_of s)"
  apply (clarsimp simp: caps_contained2_def caps_contained'_def)
  apply (rule conjI, clarsimp)
   apply (erule_tac x=c in allE, erule_tac x=c' in allE)
   apply simp
   apply (clarsimp simp add: isCap_simps)
   apply (drule_tac p=c' in capUntypedPtr_capRange)
     apply simp
    apply assumption
   apply clarsimp
   apply (erule impE)
    apply fastforce
   apply (simp add: capRange_def isCap_simps)
   apply fastforce
  apply (erule_tac x=c in allE, erule_tac x=c' in allE)
  apply simp
  apply (clarsimp simp add: isCap_simps)
  apply (drule_tac p=c' in capUntypedPtr_capRange)
    apply simp
   apply assumption
  apply clarsimp
  apply (erule impE)
   apply fastforce
  apply (simp add: capRange_def isCap_simps)
  apply fastforce
  done

lemma descendants_of_update_ztc:
  assumes c: "\<And>x. \<lbrakk> m \<turnstile> x \<rightarrow> slot; \<not> P \<rbrakk> \<Longrightarrow>
                  \<exists>cte'. m x = Some cte'
                    \<and> capMasterCap (cteCap cte') \<noteq> capMasterCap (cteCap cte)
                    \<and> sameRegionAs (cteCap cte') (cteCap cte)"
  assumes m: "m slot = Some cte"
  assumes z: "isZombie cap \<or> isCNodeCap cap \<or> isThreadCap cap"
  defines "cap' \<equiv> cteCap cte"
  assumes F: "\<And>x cte'. \<lbrakk> m x = Some cte'; x \<noteq> slot; P \<rbrakk>
               \<Longrightarrow> isUntypedCap (cteCap cte') \<or> capClass (cteCap cte') \<noteq> PhysicalClass
                    \<or> capUntypedPtr (cteCap cte') \<noteq> capUntypedPtr cap'"
  assumes pu: "capRange cap' = capRange cap \<and> capUntypedPtr cap' = capUntypedPtr cap"
  assumes a: "capAligned cap'"
  assumes t: "isZombie cap' \<or> isCNodeCap cap' \<or> isThreadCap cap'"
  assumes n: "no_loops m"
  defines "m' \<equiv> m(slot \<mapsto> cteCap_update (\<lambda>_. cap) cte)"
  shows "((c \<noteq> slot \<or> P) \<longrightarrow> descendants_of' c m \<subseteq> descendants_of' c m')
           \<and> (P \<longrightarrow> descendants_of' c m' \<subseteq> descendants_of' c m)"
proof (simp add: descendants_of'_def subset_iff,
       simp only: all_simps(6)[symmetric], intro conjI allI)
  note isMDBParentOf_CTE[simp]

  have utp: "capUntypedPtr cap' \<in> capRange cap'"
    using t a
    by (auto elim!: capAligned_capUntypedPtr simp: isCap_simps)

  have ztc_parent: "\<And>cap cap'. isZombie cap \<or> isCNodeCap cap \<or> isThreadCap cap
                            \<Longrightarrow> sameRegionAs cap cap'
                            \<Longrightarrow> capUntypedPtr cap = capUntypedPtr cap'
                                 \<and> capClass cap' = PhysicalClass \<and> \<not> isUntypedCap cap'"
    by (auto simp: isCap_simps sameRegionAs_def3)

  have ztc_child: "\<And>cap cap'. isZombie cap \<or> isCNodeCap cap \<or> isThreadCap cap
                            \<Longrightarrow> sameRegionAs cap' cap
                            \<Longrightarrow> capClass cap' = PhysicalClass \<and>
                                  (isUntypedCap cap' \<or> capUntypedPtr cap' = capUntypedPtr cap)"
    by (auto simp: isCap_simps sameRegionAs_def3)

  have notparent: "\<And>x cte'. \<lbrakk> m x = Some cte'; x \<noteq> slot; P \<rbrakk>
                               \<Longrightarrow> \<not> isMDBParentOf cte cte'"
    using t utp
    apply clarsimp
    apply (drule_tac cte'=cte' in F, simp+)
    apply (simp add: cap'_def)
    apply (cases cte, case_tac cte', clarsimp)
    apply (frule(1) ztc_parent, clarsimp)
    done

  have notparent2: "\<And>x cte'. \<lbrakk> m x = Some cte'; x \<noteq> slot; P \<rbrakk>
                               \<Longrightarrow> \<not> isMDBParentOf (cteCap_update (\<lambda>_. cap) cte) cte'"
    using z utp
    apply clarsimp
    apply (drule_tac cte'=cte' in F, simp+)
    apply (cases cte, case_tac cte', clarsimp)
    apply (frule(1) ztc_parent)
    apply (clarsimp simp: pu)
    done

  fix x
  { assume cx: "m \<turnstile> c \<rightarrow> x" and cP: "c \<noteq> slot \<or> P"
    hence c_neq_x [simp]: "c \<noteq> x"
      by (clarsimp simp: n no_loops_no_subtree)
    from cx c_neq_x cP m
    have s_neq_c [simp]: "c \<noteq> slot"
      apply (clarsimp simp del: c_neq_x)
      apply (drule subtree_parent)
      apply (clarsimp simp: parentOf_def notparent)
      done

    have parent: "\<And>x cte'. \<lbrakk> m x = Some cte'; isMDBParentOf cte' cte; m \<turnstile> x \<rightarrow> slot; x \<noteq> slot \<rbrakk>
                                \<Longrightarrow> isMDBParentOf cte' (cteCap_update (\<lambda>_. cap) cte)"
      using t z pu
      apply -
      apply (cases P)
       apply (frule(2) F)
       apply (clarsimp simp: cap'_def)
       apply (case_tac cte')
       apply (case_tac cte)
       apply clarsimp
       apply (frule(1) ztc_child)
       apply (case_tac "isUntypedCap capability")
        apply (simp add: isCap_simps)
        apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
       apply simp
      apply (frule(1) c, clarsimp)
      apply (clarsimp simp: cap'_def)
      apply (case_tac cte')
      apply (case_tac cte)
      apply clarsimp
      apply (erule sameRegionAsE)
         apply (clarsimp simp: sameRegionAs_def3 isCap_simps)+
      done

    from cx
    have "m' \<turnstile> c \<rightarrow> x"
    proof induct
      case (direct_parent c')
      hence "m \<turnstile> c \<rightarrow> c'" by (rule subtree.direct_parent)
      with direct_parent m
      show ?case
        apply -
        apply (rule subtree.direct_parent)
          apply (clarsimp simp add: mdb_next_unfold m'_def m)
         apply assumption
        apply (clarsimp simp: parentOf_def)
        apply (clarsimp simp add: m'_def)
        apply (erule(2) parent)
        apply simp
        done
    next
      case (trans_parent c' c'')
      moreover
      from trans_parent
      have "m \<turnstile> c \<rightarrow> c''" by - (rule subtree.trans_parent)
      ultimately
      show ?case using  z m pu t
        apply -
        apply (erule subtree.trans_parent)
          apply (clarsimp simp: mdb_next_unfold m'_def m)
         apply assumption
        apply (clarsimp simp: parentOf_def m'_def)
        apply (erule(2) parent)
        apply simp
        done
    qed
  }
    thus "(c = slot \<longrightarrow> P) \<longrightarrow> m \<turnstile> c \<rightarrow> x \<longrightarrow> m' \<turnstile> c \<rightarrow> x"
      by blast

  { assume subcx: "m' \<turnstile> c \<rightarrow> x" and P: "P"

    have mdb_next_eq: "\<And>x y. m' \<turnstile> x \<leadsto> y = m \<turnstile> x \<leadsto> y"
      by (simp add: mdb_next_unfold m'_def m)
    have mdb_next_eq_trans: "\<And>x y. m' \<turnstile> x \<leadsto>\<^sup>+ y = m \<turnstile> x \<leadsto>\<^sup>+ y"
      apply (rule arg_cong[where f="\<lambda>S. v \<in> S\<^sup>+", standard])
      apply (simp add: set_eq_iff mdb_next_eq)
      done

    have subtree_neq: "\<And>x y. m' \<turnstile> x \<rightarrow> y \<Longrightarrow> x \<noteq> y"
      apply clarsimp
      apply (drule subtree_mdb_next)
      apply (clarsimp simp: mdb_next_eq_trans n no_loops_trancl_simp)
      done

    have parent2: "\<And>x cte'. \<lbrakk> m x = Some cte'; isMDBParentOf cte' (cteCap_update (\<lambda>_. cap) cte);
                                         x \<noteq> slot \<rbrakk>
                                \<Longrightarrow> isMDBParentOf cte' cte"
      using t z pu P
      apply (drule_tac cte'=cte' in F, simp, simp)
      apply (simp add: cap'_def)
      apply (cases cte, case_tac cte', clarsimp)
      apply (frule(1) ztc_child)
      apply (case_tac "isUntypedCap capabilitya")
       apply (simp add:isCap_simps)
       apply (clarsimp simp: isCap_simps sameRegionAs_def3)
      apply clarsimp
      done

    from subcx have "m \<turnstile> c \<rightarrow> x"
    proof induct
      case (direct_parent c')
      thus ?case
        using subtree_neq [OF subtree.direct_parent [OF direct_parent(1-3)]]
        apply -
        apply (rule subtree.direct_parent)
          apply (clarsimp simp: mdb_next_unfold m'_def m split: split_if_asm)
         apply assumption
        apply (insert z m t pu)
        apply (simp add: cap'_def)
        apply (simp add: m'_def parentOf_def split: split_if_asm)
         apply (clarsimp simp: parent2)
        apply (clarsimp simp add: notparent2 [OF _ _ P])
        done
    next
      case (trans_parent c' c'')
      thus ?case
        using subtree_neq [OF subtree.trans_parent [OF trans_parent(1, 3-5)]]
        apply -
        apply (erule subtree.trans_parent)
          apply (clarsimp simp: mdb_next_unfold m'_def m split: split_if_asm)
         apply assumption
        apply (insert z m t pu)
        apply (simp add: cap'_def)
        apply (simp add: m'_def parentOf_def split: split_if_asm)
         apply (clarsimp simp: parent2)
        apply (clarsimp simp: notparent2 [OF _ _ P])
        done
    qed
  }
    thus "P \<longrightarrow> m' \<turnstile> c \<rightarrow> x \<longrightarrow> m \<turnstile> c \<rightarrow> x"
      by simp
qed

lemma use_update_ztc_one:
  "((c \<noteq> slot \<or> True) \<longrightarrow> descendants_of' c m \<subseteq> descendants_of' c m')
           \<and> (True \<longrightarrow> descendants_of' c m' \<subseteq> descendants_of' c m)
      \<Longrightarrow> descendants_of' c m = descendants_of' c m'"
  by clarsimp

lemma use_update_ztc_two:
  "((c \<noteq> slot \<or> False) \<longrightarrow> descendants_of' c m \<subseteq> descendants_of' c m')
           \<and> (False \<longrightarrow> descendants_of' c m' \<subseteq> descendants_of' c m)
       \<Longrightarrow> descendants_of' slot m = {}
       \<Longrightarrow> descendants_of' c m \<subseteq> descendants_of' c m'"
  by auto

lemmas cte_wp_at'_obj_at' = cte_wp_at_obj_cases'

lemma cte_at'_obj_at':
  "cte_at' addr s = (obj_at' (\<lambda>_ :: cte. True) addr s
                      \<or> (\<exists>n \<in> dom tcb_cte_cases. tcb_at' (addr - n) s))"
  by (simp add: cte_wp_at'_obj_at')

lemma ctes_of_valid:
  "\<lbrakk> cte_wp_at' (op = cte) p s; valid_objs' s \<rbrakk>
  \<Longrightarrow> s \<turnstile>' cteCap cte"
  apply (simp add: cte_wp_at'_obj_at')
  apply (erule disjE)
   apply (subgoal_tac "ko_at' cte p s")
    apply (drule (1) ko_at_valid_objs')
     apply (simp add: projectKOs)
    apply (simp add: valid_obj'_def valid_cte'_def)
   apply (simp add: obj_at'_def projectKOs cte_level_bits_def objBits_simps)
  apply clarsimp
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (drule (1) ko_at_valid_objs')
   apply (simp add: projectKOs)
  apply (simp add: valid_obj'_def valid_tcb'_def)
  apply (fastforce intro: ranI)
  done

lemma caps_contained_srel:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace (s' :: kernel_state));
     valid_objs s; pspace_aligned s \<rbrakk>
  \<Longrightarrow> caps_contained2 (ctes_of s')"
  apply (frule (1) valid_objs_caps_contained)
  apply (unfold caps_contained_def caps_contained2_def)
  apply (intro allI impI)
  apply (frule_tac x=c in pspace_relation_cte_wp_atI, assumption+)
  apply (frule_tac x=c' in pspace_relation_cte_wp_atI, assumption+)
  apply clarify
  apply (erule_tac x=ca in allE, erule allE)
  apply (erule_tac x=cb in allE, erule allE)
  apply (erule (1) impE, erule (1) impE)
  apply clarsimp
  apply (case_tac ca, simp_all)
   apply (clarsimp simp: valid_cap'_def)
   apply (case_tac cb, simp_all add: isCap_simps objBits_simps
                                     cte_level_bits_def)[1]
   apply clarsimp
  apply clarsimp
  done

lemma no_fail_setCTE [wp]:
  "no_fail (cte_at' p) (setCTE p c)"
  apply (clarsimp simp: setCTE_def setObject_def split_def unless_def
                        updateObject_cte alignCheck_def alignError_def
                        typeError_def is_aligned_mask[symmetric]
                  cong: kernel_object.case_cong)
  apply (rule no_fail_pre)
   apply (wp, wpc, wp)
  apply (clarsimp simp: cte_wp_at'_def getObject_def split_def
                        in_monad loadObject_cte
                 dest!: in_singleton
             split del: split_if)
  apply (clarsimp simp: typeError_def alignCheck_def alignError_def
                        in_monad is_aligned_mask[symmetric] objBits_simps
                        magnitudeCheck_def
                 split: kernel_object.split_asm split_if_asm option.splits
             split del: split_if)
    apply simp_all
  done

lemma no_fail_updateCap [wp]:
  "no_fail (cte_at' p) (updateCap p cap')"
  apply (simp add: updateCap_def)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma capRange_cap_relation:
  "\<lbrakk> cap_relation cap cap'; cap_relation cap cap' \<Longrightarrow> capClass cap' = PhysicalClass \<rbrakk>
    \<Longrightarrow> capRange cap' = {obj_ref_of cap .. obj_ref_of cap + obj_size cap - 1}"
  by (simp add: capRange_def objBits_simps cte_level_bits_def
                asid_low_bits_def pageBits_def zbits_map_def
         split: cap_relation_split_asm arch_cap.split_asm
                option.split sum.split)

lemma cap_relation_untyped_ptr_obj_refs:
  "cap_relation cap cap' \<Longrightarrow> capClass cap' = PhysicalClass \<Longrightarrow> \<not> isUntypedCap cap'
        \<Longrightarrow> capUntypedPtr cap' \<in> obj_refs cap"
  by (clarsimp simp: isCap_simps
              split: cap_relation_split_asm arch_cap.split_asm)

lemma obj_refs_cap_relation_untyped_ptr:
  "\<lbrakk> cap_relation cap cap'; obj_refs cap \<noteq> {} \<rbrakk> \<Longrightarrow> capUntypedPtr cap' \<in> obj_refs cap"
  by (clarsimp split: cap_relation_split_asm arch_cap.split_asm)

lemma is_final_untyped_ptrs:
  "\<lbrakk> ctes_of (s' :: kernel_state) (cte_map slot) = Some cte; ctes_of s' y = Some cte'; cte_map slot \<noteq> y;
     pspace_relation (kheap s) (ksPSpace s'); valid_objs s; pspace_aligned s; pspace_distinct s;
     cte_wp_at (\<lambda>cap. is_final_cap' cap s \<and> obj_refs cap \<noteq> {}) slot s \<rbrakk>
         \<Longrightarrow> capClass (cteCap cte') \<noteq> PhysicalClass
           \<or> isUntypedCap (cteCap cte')
           \<or> capUntypedPtr (cteCap cte) \<noteq> capUntypedPtr (cteCap cte')"
  apply clarsimp
  apply (drule(2) pspace_relation_cte_wp_atI[rotated])+
  apply clarsimp
  apply (drule_tac s=s in cte_map_inj_eq,
          (clarsimp elim!: cte_wp_at_weakenE[OF _ TrueI])+)
  apply (clarsimp simp: cte_wp_at_def)
  apply (erule(3) final_cap_duplicate [where r="Inl (capUntypedPtr (cteCap cte))",
                                       OF _ _ distinct_lemma[where f=cte_map]])
    apply (rule obj_ref_is_obj_irq_ref)
    apply (erule(1) obj_refs_cap_relation_untyped_ptr)
   apply (rule obj_ref_is_obj_irq_ref)
   apply (erule(1) obj_refs_cap_relation_untyped_ptr)
  apply (rule obj_ref_is_obj_irq_ref)
  apply (drule(2) cap_relation_untyped_ptr_obj_refs)+
  apply simp
  done

lemma capClass_ztc_relation:
  "\<lbrakk> is_zombie c \<or> is_cnode_cap c \<or> is_thread_cap c;
       cap_relation c c' \<rbrakk> \<Longrightarrow> capClass c' = PhysicalClass"
  by (auto simp: is_cap_simps)

lemma pspace_relationsD:
  "\<lbrakk>pspace_relation kh kh'; ekheap_relation ekh kh'\<rbrakk> \<Longrightarrow> pspace_relations ekh kh kh'"
  by (simp add: pspace_relations_def)

lemma cap_update_corres:
  "\<lbrakk>cap_relation cap cap';
    is_zombie cap \<or> is_cnode_cap cap \<or> is_thread_cap cap \<rbrakk>
   \<Longrightarrow> corres dc (\<lambda>s. invs s \<and>
                      cte_wp_at (\<lambda>c. (is_zombie c \<or> is_cnode_cap c \<or>
                                      is_thread_cap c) \<and>
                                     is_final_cap' c s \<and>
                                     obj_ref_of c = obj_ref_of cap \<and>
                                     obj_size c = obj_size cap) slot s)
                 invs'
                 (set_cap cap slot) (updateCap (cte_map slot) cap')"
  apply (rule corres_stronger_no_failI)
   apply (rule no_fail_pre, wp)
   apply clarsimp
   apply (drule cte_wp_at_norm)
   apply (clarsimp simp: state_relation_def)
   apply (drule (1) pspace_relation_ctes_ofI)
     apply fastforce
    apply fastforce
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp add: state_relation_def)
  apply (drule(1) pspace_relationsD)
  apply (frule (3) set_cap_not_quite_corres)
                  apply fastforce
                 apply fastforce
                apply fastforce
               apply fastforce
              apply assumption
             apply fastforce
            apply fastforce
           apply fastforce
          apply fastforce
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply fastforce
       apply fastforce
      apply assumption
     apply assumption
    apply assumption
   apply (rule refl)
  apply clarsimp
  apply (rule bexI)
   prefer 2
   apply simp
  apply (clarsimp simp: in_set_cap_cte_at_swp pspace_relations_def)
  apply (drule updateCap_stuff)
  apply simp
  apply (rule conjI)
   apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    apply (unfold cdt_list_relation_def)[1]
    apply (intro allI impI)
    apply (erule_tac x=c in allE)
    apply (auto elim!: modify_map_casesE)[1]
   apply (unfold revokable_relation_def)[1]
   apply (drule set_cap_caps_of_state_monad)
   apply (simp add: cte_wp_at_caps_of_state del: split_paired_All)
   apply (intro allI impI)
   apply (erule_tac x=c in allE)
   apply (erule impE[where P="\<exists>y. v = Some y", standard])
    apply (clarsimp simp: null_filter_def is_zombie_def split: split_if_asm)
   apply (auto elim!: modify_map_casesE del: disjE)[1]
  apply (case_tac "ctes_of b (cte_map slot)")
   apply (simp add: modify_map_None)
  apply (simp add: modify_map_apply)
  apply (simp add: cdt_relation_def del: split_paired_All)
  apply (intro allI impI)
  apply (rule use_update_ztc_one [OF descendants_of_update_ztc])
         apply simp
        apply assumption
       apply (auto simp: is_cap_simps isCap_simps)[1]
      apply (frule(3) is_final_untyped_ptrs [OF _ _ not_sym], clarsimp+)
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       apply (simp add: is_cap_simps, elim disjE exE, simp_all)[1]
      apply (simp add: disj_ac eq_commute)
     apply (drule cte_wp_at_eqD, clarsimp)
     apply (drule(1) pspace_relation_ctes_ofI, clarsimp+)
     apply (drule(1) capClass_ztc_relation)+
     apply (simp add: capRange_cap_relation obj_ref_of_relation[symmetric])
    apply (rule valid_capAligned, rule ctes_of_valid)
     apply (simp add: cte_wp_at_ctes_of)
    apply clarsimp
   apply (drule cte_wp_at_eqD, clarsimp)
   apply (drule(1) pspace_relation_ctes_ofI, clarsimp+)
   apply (simp add: is_cap_simps, elim disjE exE, simp_all add: isCap_simps)[1]
  apply clarsimp
  done

lemma exst_set_cap:
  "(x,s') \<in> fst (set_cap p c s) \<Longrightarrow> exst s' = exst s"
  by (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
               split: split_if_asm Structures_A.kernel_object.splits)

lemma cap_relation_NullCap [simp]:
  "cap_relation c NullCap = (c = Structures_A.NullCap)"
  by (cases c) auto

lemma updateMDB_eqs:
  assumes "(x, s'') \<in> fst (updateMDB p f s')"
  shows "ksMachineState s'' = ksMachineState s' \<and>
         ksWorkUnitsCompleted s'' = ksWorkUnitsCompleted s' \<and>
         ksCurThread s'' = ksCurThread s' \<and>
         ksIdleThread s'' = ksIdleThread s' \<and>
         ksReadyQueues s'' = ksReadyQueues s' \<and>
         ksInterruptState s'' = ksInterruptState s' \<and>
         ksArchState s'' = ksArchState s' \<and>
         ksSchedulerAction s'' = ksSchedulerAction s' \<and>
         gsUserPages s'' = gsUserPages s' \<and>
         gsCNodes s'' = gsCNodes s' \<and>
         ksDomScheduleIdx s'' = ksDomScheduleIdx s' \<and>
         ksDomSchedule s''    = ksDomSchedule s' \<and>
         ksCurDomain s''      = ksCurDomain s' \<and>
         ksDomainTime s''     = ksDomainTime s'" using assms
  apply (clarsimp simp: updateMDB_def Let_def in_monad split: split_if_asm)
  apply (drule in_inv_by_hoareD [OF getCTE_inv])
  apply (clarsimp simp: setCTE_def setObject_def in_monad split_def)
  apply (drule in_inv_by_hoareD [OF updateObject_cte_inv])
  apply simp
  done

lemma updateMDB_pspace_relation:
  assumes "(x, s'') \<in> fst (updateMDB p f s')"
  assumes "pspace_relation (kheap s) (ksPSpace s')"
  assumes "pspace_aligned' s'" "pspace_distinct' s'"
  shows "pspace_relation (kheap s) (ksPSpace s'')" using assms
  apply (clarsimp simp: updateMDB_def Let_def in_monad split: split_if_asm)
  apply (drule_tac P="op = s'" in use_valid [OF _ getCTE_sp], rule refl)
  apply clarsimp
  apply (clarsimp simp: setCTE_def setObject_def in_monad
                        split_def)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim disjE conjE exE)
   apply (clarsimp simp: cte_wp_at_cases' lookupAround2_char1)
   apply (erule disjE)
    apply (clarsimp simp: tcb_ctes_clear)
   apply clarsimp
   apply (rule pspace_dom_relatedE, assumption+)
   apply (rule obj_relation_cutsE, assumption+, simp_all)[1]
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          ARM_Structs_A.arch_kernel_obj.split_asm
                    simp: other_obj_relation_def)
   apply (frule(1) tcb_cte_cases_aligned_helpers(1))
   apply (frule(1) tcb_cte_cases_aligned_helpers(2))
   apply (clarsimp simp del: diff_neg_mask)
   apply (subst map_upd_triv[symmetric, where t="kheap s"], assumption)
   apply (erule(2) pspace_relation_update_tcbs)
   apply (case_tac tcba)
   apply (simp add: tcb_cte_cases_def tcb_relation_def del: diff_neg_mask
             split: split_if_asm)
  apply (clarsimp simp: cte_wp_at_cases')
  apply (erule disjE)
   apply (rule pspace_dom_relatedE, assumption+)
   apply (rule obj_relation_cutsE, assumption+, simp_all)[1]
   apply (clarsimp simp: cte_relation_def)
   apply (simp add: pspace_relation_def dom_fun_upd2
               del: dom_fun_upd)
   apply (erule conjE)
   apply (rule ballI, drule(1) bspec)
   apply (rule ballI, drule(1) bspec)
   apply clarsimp
   apply (rule obj_relation_cutsE, assumption+, simp_all)[1]
   apply (clarsimp simp: cte_relation_def)
  apply clarsimp
  apply (drule_tac y=p in tcb_ctes_clear[rotated], assumption+)
   apply fastforce
  apply fastforce
  done

lemma updateMDB_ekheap_relation:
  assumes "(x, s'') \<in> fst (updateMDB p f s')"
  assumes "ekheap_relation (ekheap s) (ksPSpace s')"
  shows "ekheap_relation (ekheap s) (ksPSpace s'')" using assms
  apply (clarsimp simp: updateMDB_def Let_def setCTE_def setObject_def in_monad ekheap_relation_def etcb_relation_def split_def split: split_if_asm)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (drule_tac P="op = s'" in use_valid [OF _ getCTE_sp], rule refl)
  apply (drule bspec, erule domI)
  apply (clarsimp simp: tcb_cte_cases_def lookupAround2_char1 split: split_if_asm)
  done

lemma updateMDB_pspace_relations:
  assumes "(x, s'') \<in> fst (updateMDB p f s')"
  assumes "pspace_relations (ekheap s) (kheap s) (ksPSpace s')"
  assumes "pspace_aligned' s'" "pspace_distinct' s'"
  shows "pspace_relations (ekheap s) (kheap s) (ksPSpace s'')" using assms
  by (simp add: pspace_relations_def updateMDB_pspace_relation updateMDB_ekheap_relation)

lemma updateMDB_ctes_of:
  assumes "(x, s') \<in> fst (updateMDB p f s)"
  assumes "no_0 (ctes_of s)"
  shows "ctes_of s' = modify_map (ctes_of s) p (cteMDBNode_update f)"
  using assms
  apply (clarsimp simp: valid_def)
  apply (drule use_valid)
    apply (rule updateMDB_ctes_of_no_0)
   prefer 2
   apply assumption
  apply simp
  done

crunch aligned[wp]: updateMDB "pspace_aligned'"
crunch pdistinct[wp]: updateMDB "pspace_distinct'"

lemma updateMDB_the_lot:
  assumes "(x, s'') \<in> fst (updateMDB p f s')"
  assumes "pspace_relations (ekheap s) (kheap s) (ksPSpace s')"
  assumes "pspace_aligned' s'" "pspace_distinct' s'" "no_0 (ctes_of s')"
  shows "ctes_of s'' = modify_map (ctes_of s') p (cteMDBNode_update f) \<and>
         ksMachineState s'' = ksMachineState s' \<and>
         ksWorkUnitsCompleted s'' = ksWorkUnitsCompleted s' \<and>
         ksCurThread s'' = ksCurThread s' \<and>
         ksIdleThread s'' = ksIdleThread s' \<and>
         ksReadyQueues s'' = ksReadyQueues s' \<and>
         ksSchedulerAction s'' = ksSchedulerAction s' \<and>
         ksInterruptState s'' = ksInterruptState s' \<and>
         ksArchState s'' = ksArchState s' \<and>
         gsUserPages s'' = gsUserPages s' \<and>
         gsCNodes s'' = gsCNodes s' \<and>
         pspace_relations (ekheap s) (kheap s) (ksPSpace s'') \<and>
         pspace_aligned' s'' \<and> pspace_distinct' s'' \<and>
         no_0 (ctes_of s'') \<and>
         ksDomScheduleIdx s'' = ksDomScheduleIdx s' \<and>
         ksDomSchedule s''    = ksDomSchedule s' \<and>
         ksCurDomain s''      = ksCurDomain s' \<and>
         ksDomainTime s''     = ksDomainTime s'"
using assms
  apply (simp add: updateMDB_eqs updateMDB_pspace_relations split del: split_if)
  apply (frule (1) updateMDB_ctes_of)
  apply clarsimp
  apply (rule conjI)
   apply (erule use_valid)
    apply wp
   apply simp
  apply (erule use_valid)
   apply wp
  apply simp
  done

lemma revokable_eq:
  "\<lbrakk> cap_relation c c'; cap_relation src_cap src_cap'; sameRegionAs src_cap' c';
     is_untyped_cap src_cap \<longrightarrow> \<not> is_ep_cap c \<and> \<not> is_aep_cap c\<rbrakk>
  \<Longrightarrow> revokable src_cap c = revokable' src_cap' c'"
  apply (clarsimp simp: isCap_simps objBits_simps pageBits_def
                        bits_of_def revokable_def revokable'_def
                        sameRegionAs_def3
                 split: cap_relation_split_asm arch_cap.split_asm)
    apply auto
  done

lemma isMDBParentOf_prev_update [simp]:
  "isMDBParentOf (cteMDBNode_update (mdbPrev_update f) cte) cte' =
   isMDBParentOf cte cte'"
  "isMDBParentOf cte (cteMDBNode_update (mdbPrev_update f) cte') =
   isMDBParentOf cte cte'"
   apply (cases cte)
   apply (cases cte')
   apply (simp add: isMDBParentOf_def)
  apply (cases cte)
  apply (cases cte')
  apply (clarsimp simp: isMDBParentOf_def)
  done

lemma prev_update_subtree [simp]:
  "modify_map m' x (cteMDBNode_update (mdbPrev_update f)) \<turnstile> a \<rightarrow> b = m' \<turnstile> a \<rightarrow> b"
  (is "?m' = ?m")
proof
  assume "?m"
  thus ?m'
  proof induct
    case (direct_parent c)
    thus ?case
      apply -
      apply (rule subtree.direct_parent)
        apply (clarsimp simp add: mdb_next_unfold modify_map_def)
       apply assumption
      apply (clarsimp simp add: parentOf_def modify_map_def)
      apply fastforce
      done
  next
    case (trans_parent c c')
    thus ?case
      apply -
      apply (rule subtree.trans_parent)
         apply (rule trans_parent.hyps)
        apply (clarsimp simp add: mdb_next_unfold modify_map_def)
       apply assumption
      apply (clarsimp simp add: parentOf_def modify_map_def)
      apply fastforce
      done
  qed
next
  assume "?m'"
  thus ?m
  proof induct
    case (direct_parent c)
    thus ?case
      apply -
      apply (rule subtree.direct_parent)
        apply (clarsimp simp add: mdb_next_unfold modify_map_def split: split_if_asm)
       apply assumption
      apply (clarsimp simp add: parentOf_def modify_map_def split: split_if_asm)
      done
  next
    case (trans_parent c c')
    thus ?case
      apply -
      apply (rule subtree.trans_parent)
         apply (rule trans_parent.hyps)
        apply (clarsimp simp add: mdb_next_unfold modify_map_def split: split_if_asm)
       apply assumption
      apply (clarsimp simp add: parentOf_def modify_map_def split: split_if_asm)
      done
  qed
qed

lemma prev_update_modify_mdb_relation:
  "cdt_relation c m (modify_map m' x (cteMDBNode_update (mdbPrev_update f)))
  = cdt_relation c m m'"
  by (fastforce simp: cdt_relation_def descendants_of'_def)

lemma subtree_prev_0:
  assumes s: "m \<turnstile> a \<rightarrow> b"
  assumes n: "m b = Some cte" "mdbPrev (cteMDBNode cte) = 0"
  assumes d: "valid_dlist m"
  assumes 0: "no_0 m"
  shows "False" using s n
proof induct
  case (direct_parent c)
  have "m \<turnstile> a \<leadsto> c" by fact+
  then obtain cte' where a: "m a = Some cte'" and "mdbNext (cteMDBNode cte') = c"
    by (auto simp add: mdb_next_unfold)
  moreover
  have "m c = Some cte" by fact+
  moreover
  have "c \<noteq> 0" by fact+
  ultimately
  have "mdbPrev (cteMDBNode cte) = a" using d
    by (fastforce simp add: valid_dlist_def Let_def)
  moreover
  have "mdbPrev (cteMDBNode cte) = 0" by fact+
  moreover
  from a have "a \<noteq> 0" using assms by auto
  ultimately
  show False by simp
next
  case (trans_parent c' c)
  have "m \<turnstile> c' \<leadsto> c" by fact+
  then obtain cte' where c': "m c' = Some cte'" and "mdbNext (cteMDBNode cte') = c"
    by (auto simp add: mdb_next_unfold)
  moreover
  have "m c = Some cte" by fact+
  moreover
  have "c \<noteq> 0" by fact+
  ultimately
  have "mdbPrev (cteMDBNode cte) = c'" using d
    by (fastforce simp add: valid_dlist_def Let_def)
  moreover
  have "mdbPrev (cteMDBNode cte) = 0" by fact+
  moreover
  from c' have "c' \<noteq> 0" using assms by auto
  ultimately
  show False by simp
qed

lemma subtree_next_0:
  assumes s: "m \<turnstile> a \<rightarrow> b"
  assumes n: "m a = Some cte" "mdbNext (cteMDBNode cte) = 0"
  shows "False" using s n
  by induct (auto simp: mdb_next_unfold)

definition
  "isArchCap P cap \<equiv> case cap of ArchObjectCap acap \<Rightarrow> P acap | _ \<Rightarrow> False"

lemma isArchCap_simps[simp]:
  "isArchCap P (capability.ThreadCap xc) = False"
  "isArchCap P capability.NullCap = False"
  "isArchCap P capability.DomainCap = False"
  "isArchCap P (capability.AsyncEndpointCap xca xba xaa xd) = False"
  "isArchCap P (capability.EndpointCap xda xcb xbb xab xe) = False"
  "isArchCap P (capability.IRQHandlerCap xf) = False"
  "isArchCap P (capability.Zombie xbc xac xg) = False"
  "isArchCap P (capability.ArchObjectCap xh) = P xh"
  "isArchCap P (capability.ReplyCap xad xi) = False"
  "isArchCap P (capability.UntypedCap xae xj f) = False"
  "isArchCap P (capability.CNodeCap xfa xea xdb xcc) = False"
  "isArchCap P capability.IRQControlCap = False"
  by (simp add: isArchCap_def)+

definition
  vsCapRef :: "capability \<Rightarrow> vs_ref list option"
where
  "vsCapRef cap \<equiv> case cap of
   ArchObjectCap (ASIDPoolCap _ asid) \<Rightarrow>
     Some [VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageDirectoryCap _ (Some asid)) \<Rightarrow>
     Some [VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageTableCap _ (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageCap _ _ ARMSmallPage (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 12) && mask 8) (Some APageTable),
           VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageCap _ _ ARMLargePage (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 12) && mask 8) (Some APageTable),
           VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageCap _ _ ARMSection (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageCap _ _ ARMSuperSection (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | _ \<Rightarrow> None"

definition
  "badge_derived' cap' cap \<equiv>
    capMasterCap cap = capMasterCap cap' \<and>
    (capBadge cap, capBadge cap') \<in> capBadge_ordering False"

definition
  "is_derived' m p cap' cap \<equiv>
  cap' \<noteq> NullCap \<and>
  \<not> isZombie cap \<and>
  \<not> isIRQControlCap cap' \<and>
  badge_derived' cap' cap \<and>
  (isUntypedCap cap \<longrightarrow> descendants_of' p m = {}) \<and>
  (isReplyCap cap = isReplyCap cap') \<and>
  (isReplyCap cap \<longrightarrow> capReplyMaster cap) \<and>
  (isReplyCap cap' \<longrightarrow> \<not> capReplyMaster cap') \<and>
  (vsCapRef cap = vsCapRef cap' \<or> isArchCap isPageCap cap') \<and>
  ((isArchCap isPageTableCap cap \<or> isArchCap isPageDirectoryCap cap)
        \<longrightarrow> capASID cap = capASID cap' \<and> capASID cap \<noteq> None)"

lemma zbits_map_eq[simp]:
  "(zbits_map zbits = zbits_map zbits')
      = (zbits = zbits')"
  by (simp add: zbits_map_def split: option.split sum.split)

lemma master_cap_relation:
  "\<lbrakk> cap_relation c c'; cap_relation d d' \<rbrakk> \<Longrightarrow>
  (capMasterCap c' = capMasterCap d') =
  (cap_master_cap c = cap_master_cap d)"
  by (auto simp add: cap_master_cap_def capMasterCap_def split: cap.splits arch_cap.splits)

lemma cap_badge_relation:
  "\<lbrakk> cap_relation c c'; cap_relation d d' \<rbrakk> \<Longrightarrow>
  (capBadge c' = capBadge d') =
  (cap_badge c = cap_badge d)"
  by (auto simp add: cap_badge_def split: cap.splits arch_cap.splits)

lemma capBadge_ordering_relation:
  "\<lbrakk> cap_relation c c'; cap_relation d d' \<rbrakk> \<Longrightarrow>
  ((capBadge c', capBadge d') \<in> capBadge_ordering f) =
  ((cap_badge c, cap_badge d) \<in> capBadge_ordering f)"
  apply (cases c)
   apply (auto simp add: cap_badge_def capBadge_ordering_def split: cap.splits)
  done

lemma is_untyped_relation:
  "cap_relation c c' \<Longrightarrow> isUntypedCap c' = is_untyped_cap c"
  by (cases c, auto simp: is_cap_simps isCap_simps)

lemma is_zombie_relation:
  "cap_relation c c' \<Longrightarrow> isZombie c' = is_zombie c"
  by (cases c, auto simp: is_cap_simps isCap_simps)

lemma is_reply_cap_relation:
  "cap_relation c c' \<Longrightarrow> is_reply_cap c = (isReplyCap c' \<and> \<not> capReplyMaster c')"
  by (cases c, auto simp: is_cap_simps isCap_simps)

lemma is_reply_master_relation:
  "cap_relation c c' \<Longrightarrow>
   is_master_reply_cap c = (isReplyCap c' \<and> capReplyMaster c')"
  by (cases c, auto simp add: is_cap_simps isCap_simps)

lemma cap_asid_cap_relation:
  "cap_relation c c' \<Longrightarrow> capASID c' = cap_asid c"
  by (auto simp: capASID_def cap_asid_def split: cap.splits arch_cap.splits)

lemma vs_cap_ref_cap_relation:
  "cap_relation c c' \<Longrightarrow> vsCapRef c' = vs_cap_ref c"
  apply (simp add: vsCapRef_def vs_cap_ref_def
         split: cap_relation_split_asm option.splits
                arch_cap.splits vmpage_size.splits)
  done

lemma cap_asid_base_cap_relation:
  "cap_relation c c' \<Longrightarrow> cap_asid_base' c' = cap_asid_base c"
  by (auto simp: cap_asid_base_def cap_asid_base'_def split: cap.splits arch_cap.splits)

lemma cap_vptr_cap_relation:
  "cap_relation c c' \<Longrightarrow> cap_vptr' c' = cap_vptr c"
  by (auto simp: cap_vptr'_def cap_vptr_def split: cap.splits arch_cap.splits)

lemma isIRQControlCap_relation:
  "cap_relation c c' \<Longrightarrow> isIRQControlCap c' = (c = cap.IRQControlCap)"
  by (cases c) (auto simp: isCap_simps)

lemma isArchCapE[elim!]:
  "\<lbrakk> isArchCap P cap; \<And>arch_cap. cap = ArchObjectCap arch_cap \<Longrightarrow> P arch_cap \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (cases cap, simp_all)

lemma is_pt_pd_cap_relation:
  "cap_relation c c' \<Longrightarrow> isArchCap isPageTableCap c' = is_pt_cap c"
  "cap_relation c c' \<Longrightarrow> isArchCap isPageDirectoryCap c' = is_pd_cap c"
  by (auto simp: is_pt_cap_def is_pd_cap_def isCap_simps
          split: cap_relation_split_asm arch_cap.split_asm)

lemma is_derived_eq:
  "\<lbrakk> cap_relation c c'; cap_relation d d';
     cdt_relation (swp cte_at s) (cdt s) (ctes_of s'); cte_at p s \<rbrakk> \<Longrightarrow>
  is_derived (cdt s) p c d = is_derived' (ctes_of s') (cte_map p) c' d'"
  unfolding cdt_relation_def
  apply (erule allE, erule impE, simp)
  apply (clarsimp simp: is_derived_def is_derived'_def badge_derived'_def)
  apply (rule conjI)
   apply (clarsimp simp: is_cap_simps isCap_simps)
   apply (cases c, auto simp: isCap_simps cap_master_cap_def capMasterCap_def)[1]
  apply (simp add:vsCapRef_def)
  apply (simp add:vs_cap_ref_def)
  apply (case_tac "isIRQControlCap d'")
   apply (frule(1) master_cap_relation)
   apply (clarsimp simp: isCap_simps cap_master_cap_def
                         is_zombie_def is_reply_cap_def is_master_reply_cap_def
                  split: cap_relation_split_asm arch_cap.split_asm)[1]
  apply (frule(1) master_cap_relation)
  apply (frule(1) cap_badge_relation)
  apply (frule cap_asid_cap_relation)
  apply (frule(1) capBadge_ordering_relation)
  apply (case_tac d)
   apply (simp_all add: isCap_simps is_cap_simps cap_master_cap_def
     vs_cap_ref_def vsCapRef_def capMasterCap_def
     split: cap_relation_split_asm arch_cap.split_asm)
   apply fastforce
  apply ((auto split:arch_cap.splits arch_capability.splits)[3])
  apply (clarsimp split:option.splits arch_cap.splits arch_capability.splits)
  apply (intro conjI|clarsimp)+
    apply fastforce
   apply clarsimp+
  apply (clarsimp split:option.splits arch_cap.splits arch_capability.splits)
  apply (intro conjI|clarsimp)+
   apply fastforce
  done

locale masterCap =
  fixes cap cap'
  assumes master: "capMasterCap cap = capMasterCap cap'"
begin

lemma isZombie [simp]:
  "isZombie cap' = isZombie cap" using master
  by (simp add: capMasterCap_def isZombie_def split: capability.splits)

lemma isUntypedCap [simp]:
  "isUntypedCap cap' = isUntypedCap cap" using master
  by (simp add: capMasterCap_def isUntypedCap_def split: capability.splits)

lemma isArchPageCap [simp]:
  "isArchPageCap cap' = isArchPageCap cap" using master
  by (simp add: capMasterCap_def isArchPageCap_def
           split: capability.splits arch_capability.splits)

lemma isIRQHandlerCap [simp]:
  "isIRQHandlerCap cap' = isIRQHandlerCap cap" using master
  by (simp add: capMasterCap_def isIRQHandlerCap_def split: capability.splits)

lemma isEndpointCap [simp]:
  "isEndpointCap cap' = isEndpointCap cap" using master
  by (simp add: capMasterCap_def isEndpointCap_def split: capability.splits)

lemma isAsyncEndpointCap [simp]:
  "isAsyncEndpointCap cap' = isAsyncEndpointCap cap" using master
  by (simp add: capMasterCap_def isAsyncEndpointCap_def split: capability.splits)

lemma isIRQControlCap [simp]:
  "isIRQControlCap cap' = isIRQControlCap cap" using master
  by (simp add: capMasterCap_def isIRQControlCap_def split: capability.splits)

lemma isReplyCap [simp]:
  "isReplyCap cap' = isReplyCap cap" using master
  by (simp add: capMasterCap_def isReplyCap_def split: capability.splits)

lemma isNullCap [simp]:
  "isNullCap cap' = isNullCap cap" using master
  by (simp add: capMasterCap_def split: capability.splits)

lemma isDomainCap [simp]:
  "isDomainCap cap' = isDomainCap cap" using master
  by (simp add: capMasterCap_def split: capability.splits)

lemma capRange [simp]:
  "capRange cap' = capRange cap" using master
  by (simp add: capRange_def capMasterCap_def split: capability.splits arch_capability.splits)

lemma isDomain1:
  "(cap' = DomainCap) = (cap = DomainCap)" using master
  by (simp add: capMasterCap_def split: capability.splits)

lemma isDomain2:
  "(DomainCap = cap') = (DomainCap = cap)" using master
  by (simp add: capMasterCap_def split: capability.splits)

lemma isNull1:
  "(cap' = NullCap) = (cap = NullCap)" using master
  by (simp add: capMasterCap_def split: capability.splits)

lemma isNull2:
  "(NullCap = cap') = (NullCap = cap)" using master
  by (simp add: capMasterCap_def split: capability.splits)

lemmas isNull [simp] = isNull1 isNull2

lemmas isDomain [simp] = isDomain1 isDomain2

lemma sameRegionAs1:
  "sameRegionAs c cap' = sameRegionAs c cap" using master
  by (simp add: sameRegionAs_def3)

lemma sameRegionAs2:
  "sameRegionAs cap' c = sameRegionAs cap c" using master
  by (simp add: sameRegionAs_def3)

lemmas sameRegionAs [simp] = sameRegionAs1 sameRegionAs2

lemma isMDBParentOf1:
  assumes "\<not>isReplyCap cap"
  assumes "\<not>isEndpointCap cap"
  assumes "\<not>isAsyncEndpointCap cap"
  shows "isMDBParentOf c (CTE cap' m) = isMDBParentOf c (CTE cap m)"
proof -
  from assms
  have c':
    "\<not>isReplyCap cap'" "\<not>isEndpointCap cap'"
    "\<not>isAsyncEndpointCap cap'" by auto
  note isReplyCap [simp del] isEndpointCap [simp del] isAsyncEndpointCap [simp del]
  from c' assms
  show ?thesis
  apply (cases c, clarsimp)
  apply (simp add: isMDBParentOf_CTE)
  apply (rule iffI)
   apply clarsimp
   apply (clarsimp simp: capBadge_ordering_def capBadge_def isCap_simps sameRegionAs_def3
                   split: split_if_asm)
  apply clarsimp
  apply (clarsimp simp: capBadge_ordering_def capBadge_def isCap_simps sameRegionAs_def3
                  split: split_if_asm)
  done
qed

lemma isMDBParentOf2:
  assumes "\<not>isReplyCap cap"
  assumes "\<not>isEndpointCap cap"
  assumes "\<not>isAsyncEndpointCap cap"
  shows "isMDBParentOf (CTE cap' m) c = isMDBParentOf (CTE cap m) c"
proof -
  from assms
  have c':
    "\<not>isReplyCap cap'" "\<not>isEndpointCap cap'"
    "\<not>isAsyncEndpointCap cap'" by auto
  note isReplyCap [simp del] isEndpointCap [simp del] isAsyncEndpointCap [simp del]
  from c' assms
  show ?thesis
  apply (cases c, clarsimp)
  apply (simp add: isMDBParentOf_CTE)
  apply (auto simp: capBadge_ordering_def capBadge_def isCap_simps sameRegionAs_def3
                  split: split_if_asm)[1]
  done
qed

lemmas isMDBParentOf = isMDBParentOf1 isMDBParentOf2

end


lemma same_master_descendants:
  assumes slot: "m slot = Some cte"
  assumes master: "capMasterCap (cteCap cte) = capMasterCap cap'"
  assumes c': "\<not>isReplyCap cap'" "\<not>isEndpointCap cap'" "\<not>isAsyncEndpointCap cap'"
  defines "m' \<equiv> m(slot \<mapsto> cteCap_update (\<lambda>_. cap') cte)"
  shows "descendants_of' p m' = descendants_of' p m"
proof (rule set_eqI, simp add: descendants_of'_def)
  obtain cap n where cte: "cte = CTE cap n" by (cases cte)
  then
  interpret masterCap cap cap'
    using master by (simp add: masterCap_def)

  from c'
  have c: "\<not>isReplyCap cap"
          "\<not>isEndpointCap cap"
          "\<not>isAsyncEndpointCap cap" by auto

  note parent [simp] = isMDBParentOf [OF c]

  { fix a b
    from slot
    have "m' \<turnstile> a \<leadsto> b = m \<turnstile> a \<leadsto> b"
      by (simp add: m'_def mdb_next_unfold)
  } note this [simp]

  { fix a b
    from slot cte
    have "m' \<turnstile> a parentOf b = m \<turnstile> a parentOf b"
      by (simp add: m'_def parentOf_def)
  } note this [simp]

  fix x
  { assume "m \<turnstile> p \<rightarrow> x"
    hence "m' \<turnstile> p \<rightarrow> x"
    proof induct
      case (direct_parent c')
      thus ?case
        by (auto intro: subtree.direct_parent)
    next
      case trans_parent
      thus ?case
        by (auto elim: subtree.trans_parent)
    qed
  }
  moreover {
    assume "m' \<turnstile> p \<rightarrow> x"
    hence "m \<turnstile> p \<rightarrow> x"
    proof induct
      case (direct_parent c')
      thus ?case
        by (auto intro: subtree.direct_parent)
    next
      case trans_parent
      thus ?case
        by (auto elim: subtree.trans_parent)
    qed
  }
  ultimately
  show "m' \<turnstile> p \<rightarrow> x = m \<turnstile> p \<rightarrow> x" by blast
qed

lemma is_ep_cap_relation:
  "cap_relation c c' \<Longrightarrow> isEndpointCap c' = is_ep_cap c"
  apply (simp add: isCap_simps is_cap_simps)
  apply (cases c, auto)
  done

lemma is_aep_cap_relation:
  "cap_relation c c' \<Longrightarrow> isAsyncEndpointCap c' = is_aep_cap c"
  apply (simp add: isCap_simps is_cap_simps)
  apply (cases c, auto)
  done

lemma set_cap_same_master:
  "\<lbrakk> cap_relation cap cap' \<rbrakk> \<Longrightarrow>
   corres dc (valid_objs and pspace_aligned and pspace_distinct and
              cte_wp_at (\<lambda>c. cap_master_cap c = cap_master_cap cap \<and>
                             \<not>is_reply_cap c \<and> \<not>is_master_reply_cap c \<and>
                             \<not>is_ep_cap c \<and> \<not>is_aep_cap c) slot)
             (pspace_aligned' and pspace_distinct' and
              (\<lambda>s. ctes_of s (cte_map slot) = Some cte))
     (set_cap cap slot)
     (setObject (cte_map slot) (cteCap_update (\<lambda>_. cap') cte))"
  apply (fold setCTE_def)
  apply (rule corres_stronger_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply clarsimp
  apply (clarsimp simp add: state_relation_def)
  apply (drule (1) pspace_relationsD)
  apply (frule (4) set_cap_not_quite_corres_prequel)
       apply (erule cte_wp_at_weakenE, rule TrueI)
      apply assumption
     apply assumption
    apply simp
   apply (rule refl)
  apply clarsimp
  apply (rule bexI)
   prefer 2
   apply assumption
  apply (clarsimp simp: pspace_relations_def)
  apply (subst conj_assoc[symmetric])
  apply (rule conjI)
   apply (frule setCTE_pspace_only)
   apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                       split: split_if_asm Structures_A.kernel_object.splits)
  apply (rule conjI)
   apply (frule setCTE_pspace_only)
   apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    prefer 2
    apply (rule conjI)
     prefer 2
     apply (frule setCTE_pspace_only)
     apply clarsimp
     apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                    split: split_if_asm Structures_A.kernel_object.splits)
    apply (frule set_cap_caps_of_state_monad)
    apply (drule is_original_cap_set_cap)
    apply clarsimp
    apply (erule use_valid [OF _ setCTE_ctes_of_wp])
    apply (clarsimp simp: revokable_relation_def simp del: fun_upd_apply)
    apply (clarsimp split: split_if_asm)
     apply (drule cte_map_inj_eq)
          prefer 2
          apply (erule cte_wp_at_weakenE, rule TrueI)
         apply (simp add: null_filter_def split: split_if_asm)
          apply (erule cte_wp_at_weakenE, rule TrueI)
         apply (erule caps_of_state_cte_at)
        apply fastforce
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (simp add: null_filter_def split: split_if_asm)
     apply (erule_tac x=aa in allE, erule_tac x=bb in allE)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (erule disjE)
      apply (clarsimp simp: cap_master_cap_simps dest!: cap_master_cap_eqDs)
     apply (cases cte)
     apply clarsimp
    apply (subgoal_tac "(aa,bb) \<noteq> slot")
     prefer 2
     apply clarsimp
    apply (simp add: null_filter_def cte_wp_at_caps_of_state split: split_if_asm)
   apply (frule mdb_set_cap, frule exst_set_cap)
   apply (erule use_valid [OF _ setCTE_ctes_of_wp])
   apply (clarsimp simp: cdt_list_relation_def)
   apply (cases cte)
   apply clarsimp
  apply (clarsimp simp: cdt_relation_def)
  apply (frule set_cap_caps_of_state_monad)
  apply (frule mdb_set_cap)
  apply clarsimp
  apply (erule use_valid [OF _ setCTE_ctes_of_wp])
  apply (frule cte_wp_at_norm)
  apply (clarsimp simp del: fun_upd_apply)
  apply (frule (1) pspace_relation_ctes_ofI)
    apply fastforce
   apply fastforce
  apply (clarsimp simp del: fun_upd_apply)
  apply (subst same_master_descendants)
       apply assumption
      apply (clarsimp simp: master_cap_relation)
     apply (frule_tac d=c in master_cap_relation [symmetric], assumption)
     apply (frule is_reply_cap_relation[symmetric],
            drule is_reply_master_relation[symmetric])+
     apply simp
     apply (drule masterCap.intro)
     apply (drule masterCap.isReplyCap)
     apply simp
    apply (drule is_ep_cap_relation)+
    apply (drule master_cap_ep)
    apply simp
   apply (drule is_aep_cap_relation)+
   apply (drule master_cap_aep)
   apply simp
  apply (simp add: in_set_cap_cte_at)
  done

(* Just for convenience like free_index_update *)
definition freeIndex_update where
  "freeIndex_update c' g \<equiv> case c' of capability.UntypedCap ref sz f \<Rightarrow> capability.UntypedCap ref sz (g f) | _ \<Rightarrow> c'"

lemma freeIndex_update_not_untyped[simp]: "\<not>isUntypedCap c \<Longrightarrow> freeIndex_update c g = c"
   by (case_tac c,simp_all add:freeIndex_update_def isCap_simps)

locale mdb_insert =
  mdb_ptr_src: mdb_ptr m _ _ src src_cap src_node +
  mdb_ptr_dest: mdb_ptr m _ _ dest dest_cap dest_node
  for m src src_cap src_node dest dest_cap dest_node +

  fixes c' :: capability

  assumes dest_cap: "dest_cap = NullCap"
  assumes dest_prev: "mdbPrev dest_node = 0"
  assumes dest_next: "mdbNext dest_node = 0"

  assumes valid_badges: "valid_badges m"
  assumes ut_rev: "ut_revocable' m"

  fixes n

  defines "n \<equiv>
           modify_map
             (modify_map
               (modify_map m dest (cteCap_update (\<lambda>_. c')))
               dest
               (cteMDBNode_update
                 (\<lambda>m. mdbFirstBadged_update (\<lambda>a. revokable' src_cap c')
                     (mdbRevocable_update (\<lambda>a. revokable' src_cap c')
                     (mdbPrev_update (\<lambda>a. src) src_node)))))
             src
             (cteMDBNode_update (mdbNext_update (\<lambda>a. dest)))"

  assumes neq: "src \<noteq> dest"

locale mdb_insert_der = mdb_insert +
    assumes partial_is_derived': "is_derived' m src c' src_cap"


context mdb_insert
begin

lemmas src = mdb_ptr_src.m_p
lemmas dest = mdb_ptr_dest.m_p

lemma no_0_n [intro!]: "no_0 n" by (auto simp: n_def)
lemmas n_0_simps [iff] = no_0_simps [OF no_0_n]

lemmas neqs [simp] = neq neq [symmetric]

definition
  "new_dest \<equiv> CTE c' (mdbFirstBadged_update (\<lambda>a. revokable' src_cap c')
                     (mdbRevocable_update (\<lambda>a. revokable' src_cap c')
                     (mdbPrev_update (\<lambda>a. src) src_node)))"

definition
  "new_src \<equiv> CTE src_cap (mdbNext_update (\<lambda>a. dest) src_node)"

lemma n: "n = m (dest \<mapsto> new_dest, src \<mapsto> new_src)"
  using src dest
  by (simp add: n_def modify_map_apply new_dest_def new_src_def)

lemma dest_no_parent [iff]:
  "m \<turnstile> dest \<rightarrow> x = False" using dest dest_next
  by (auto dest: subtree_next_0)

lemma dest_no_child [iff]:
  "m \<turnstile> x \<rightarrow> dest = False" using dest dest_prev
  by (auto dest: subtree_prev_0)

lemma dest_no_descendants: "descendants_of' dest m = {}"
  by (simp add: descendants_of'_def)

lemma descendants_not_dest: "dest \<in> descendants_of' p m \<Longrightarrow> False"
  by (simp add: descendants_of'_def)

lemma src_next: "m \<turnstile> src \<leadsto> mdbNext src_node"
  by (simp add: src mdb_next_unfold)

lemma src_next_rtrancl_conv [simp]:
  "m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* dest = m \<turnstile> src \<leadsto>\<^sup>+ dest"
  apply (rule iffI)
   apply (insert src_next)
   apply (erule (1) rtrancl_into_trancl2)
  apply (drule tranclD)
  apply (clarsimp simp: mdb_next_unfold)
  done

lemma dest_no_next [iff]:
  "m \<turnstile> x \<leadsto> dest = False" using dest dest_prev dlist
  apply clarsimp
  apply (simp add: mdb_next_unfold)
  apply (elim exE conjE)
  apply (case_tac z)
  apply simp
  apply (rule dlistEn [where p=x], assumption)
   apply clarsimp
  apply clarsimp
  done

lemma dest_no_next_trans [iff]:
  "m \<turnstile> x \<leadsto>\<^sup>+ dest = False"
  by (clarsimp dest!: tranclD2)

lemma dest_no_prev [iff]:
  "m \<turnstile> dest \<leadsto> p = (p = 0)" using dest dest_next
  by (simp add: mdb_next_unfold)

lemma dest_no_prev_trancl [iff]:
  "m \<turnstile> dest \<leadsto>\<^sup>+ p = (p = 0)"
  apply (rule iffI)
   apply (drule tranclD)
   apply (clarsimp simp: dest_next)
  apply simp
  apply (insert chain dest)
  apply (simp add: mdb_chain_0_def)
  apply auto
  done

lemma chain_n:
  "mdb_chain_0 n"
proof -
  from chain
  have "m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* 0" using dlist src
    apply (cases "mdbNext src_node = 0")
     apply simp
    apply (erule dlistEn, simp)
    apply (auto simp: mdb_chain_0_def)
    done
  moreover
  have "\<not>m \<turnstile> mdbNext src_node \<leadsto>\<^sup>* src"
    using src_next
    apply clarsimp
    apply (drule (1) rtrancl_into_trancl2)
    apply simp
    done
  moreover
  have "\<not> m \<turnstile> 0 \<leadsto>\<^sup>* dest" using no_0 dest
    by (auto elim!: next_rtrancl_tranclE dest!: no_0_lhs_trancl)
  moreover
  have "\<not> m \<turnstile> 0 \<leadsto>\<^sup>* src" using no_0 src
    by (auto elim!: next_rtrancl_tranclE dest!: no_0_lhs_trancl)
  moreover
  note chain
  ultimately
  show "mdb_chain_0 n" using no_0 src dest
    apply (simp add: n new_src_def new_dest_def)
    apply (auto intro!: mdb_chain_0_update no_0_update simp: next_update_lhs_rtrancl)
    done
qed

lemma no_loops_n: "no_loops n" using chain_n no_0_n
  by (rule mdb_chain_0_no_loops)

lemma irrefl_direct_simp_n [iff]:
  "n \<turnstile> x \<leadsto> x = False"
  using no_loops_n by (rule no_loops_direct_simp)

lemma irrefl_trancl_simp [iff]:
  "n \<turnstile> x \<leadsto>\<^sup>+ x = False"
  using no_loops_n by (rule no_loops_trancl_simp)

lemma n_direct_eq:
  "n \<turnstile> p \<leadsto> p' = (if p = src then p' = dest else
                 if p = dest then m \<turnstile> src \<leadsto> p'
                 else m \<turnstile> p \<leadsto> p')"
  using src dest dest_prev
  by (auto simp: mdb_next_update n new_src_def new_dest_def
                 src_next mdb_next_unfold)

lemma n_dest:
  "n dest = Some new_dest"
  by (simp add: n)

end

lemma revokable_plus_orderD:
  "\<lbrakk> revokable' old new; (capBadge old, capBadge new) \<in> capBadge_ordering P;
       capMasterCap old = capMasterCap new \<rbrakk>
      \<Longrightarrow> (isUntypedCap new \<or> (\<exists>x. capBadge old = Some 0 \<and> capBadge new = Some x \<and> x \<noteq> 0))"
  by (clarsimp simp: revokable'_def isCap_simps split: split_if_asm)

lemma valid_badges_def2:
  "valid_badges m =
  (\<forall>p p' cap node cap' node'.
   m p = Some (CTE cap node) \<longrightarrow>
   m p' = Some (CTE cap' node') \<longrightarrow>
   m \<turnstile> p \<leadsto> p' \<longrightarrow>
   capMasterCap cap = capMasterCap cap' \<longrightarrow>
   capBadge cap \<noteq> None \<longrightarrow>
   capBadge cap \<noteq> capBadge cap' \<longrightarrow>
   capBadge cap' \<noteq> Some 0 \<longrightarrow>
   mdbFirstBadged node')"
  apply (simp add: valid_badges_def)
  apply (intro arg_cong[where f=All] ext imp_cong [OF refl])
  apply (case_tac cap, simp_all add: isCap_simps cong: weak_imp_cong)
   apply (fastforce simp: sameRegionAs_def3 isCap_simps)+
  done

lemma sameRegionAs_update_untyped:
  "RetypeDecls_H.sameRegionAs (capability.UntypedCap a b c) =
   RetypeDecls_H.sameRegionAs (capability.UntypedCap a b c')"
  apply (rule ext)
  apply (case_tac x)
    apply (clarsimp simp:sameRegionAs_def isCap_simps)+
  done

lemma sameRegionAs_update_untyped':
  "RetypeDecls_H.sameRegionAs cap (capability.UntypedCap a b f) =
   RetypeDecls_H.sameRegionAs cap (capability.UntypedCap a b f')"
  apply (case_tac cap)
    apply (clarsimp simp:sameRegionAs_def isCap_simps)+
  done

(*The newly inserted cap should never have children.*)
lemma (in mdb_insert_der) dest_no_parent_n:
  "n \<turnstile> dest \<rightarrow> p = False"
  using src partial_is_derived' valid_badges ut_rev
  apply clarsimp
  apply (erule subtree.induct)
   prefer 2
   apply simp
  apply (clarsimp simp: parentOf_def mdb_next_unfold n_dest new_dest_def n)
  apply (cases "mdbNext src_node = dest")
   apply (subgoal_tac "m \<turnstile> src \<leadsto> dest")
    apply simp
   apply (subst mdb_next_unfold)
   apply (simp add: src)
  apply (case_tac "isUntypedCap src_cap")
  apply (clarsimp simp: isCap_simps isMDBParentOf_CTE is_derived'_def
    badge_derived'_def freeIndex_update_def capMasterCap_def split:capability.splits)
   apply (simp add: ut_revocable'_def)
   apply (drule spec[where x=src], simp add: isCap_simps)
   apply (simp add: descendants_of'_def)
   apply (drule spec[where x="mdbNext src_node"])
   apply (erule notE, rule direct_parent)
     apply (simp add: mdb_next_unfold)
    apply simp
   apply (simp add: parentOf_def src isMDBParentOf_CTE isCap_simps cong:sameRegionAs_update_untyped)
  apply (clarsimp simp: isMDBParentOf_CTE is_derived'_def
    badge_derived'_def)
  apply (drule(2) revokable_plus_orderD)
  apply (erule sameRegionAsE, simp_all)
    apply (simp add: valid_badges_def2)
    apply (erule_tac x=src in allE)
    apply (erule_tac x="mdbNext src_node" in allE)
    apply (clarsimp simp: src mdb_next_unfold)
    apply (case_tac "capBadge cap'", simp_all)
   apply (clarsimp simp:isCap_simps capMasterCap_def vsCapRef_def split:capability.splits)
  apply (clarsimp simp:isCap_simps)
  done

locale mdb_insert_child = mdb_insert_der +
  assumes child:
  "isMDBParentOf
   (CTE src_cap src_node)
   (CTE c' (mdbFirstBadged_update (\<lambda>a. revokable' src_cap c')
           (mdbRevocable_update (\<lambda>a. revokable' src_cap c')
           (mdbPrev_update (\<lambda>a. src) src_node))))"

context mdb_insert_child
begin

lemma new_child [simp]:
  "isMDBParentOf new_src new_dest"
  by (simp add: new_src_def new_dest_def) (rule child)

lemma n_dest_child:
  "n \<turnstile> src \<rightarrow> dest"
  apply (rule subtree.direct_parent)
    apply (simp add: n_direct_eq)
   apply simp
  apply (clarsimp simp: parentOf_def src dest n)
  done

lemma parent_m_n:
  assumes "m \<turnstile> p \<rightarrow> p'"
  shows "if p' = src then n \<turnstile> p \<rightarrow> dest \<and> n \<turnstile> p \<rightarrow> p' else n \<turnstile> p \<rightarrow> p'" using assms
proof induct
  case (direct_parent c)
  thus ?case
    apply (cases "p = src")
     apply simp
     apply (rule conjI, clarsimp)
     apply clarsimp
     apply (rule subtree.trans_parent [where c'=dest])
        apply (rule n_dest_child)
       apply (simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (clarsimp simp: new_src_def src)
    apply simp
    apply (subgoal_tac "n \<turnstile> p \<rightarrow> c")
     prefer 2
     apply (rule subtree.direct_parent)
       apply (clarsimp simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (fastforce simp: new_src_def src)
    apply clarsimp
    apply (erule subtree_trans)
    apply (rule n_dest_child)
    done
next
  case (trans_parent c d)
  thus ?case
    apply -
    apply (cases "c = dest", simp)
    apply (cases "d = dest", simp)
    apply (cases "c = src")
     apply clarsimp
     apply (erule subtree.trans_parent [where c'=dest])
       apply (clarsimp simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (rule conjI, clarsimp)
     apply (clarsimp simp: new_src_def src)
    apply clarsimp
    apply (subgoal_tac "n \<turnstile> p \<rightarrow> d")
     apply clarsimp
     apply (erule subtree_trans, rule n_dest_child)
    apply (erule subtree.trans_parent)
      apply (simp add: n_direct_eq)
     apply simp
    apply (clarsimp simp: parentOf_def n)
    apply (fastforce simp: src new_src_def)
    done
qed

lemma n_to_dest [simp]:
  "n \<turnstile> p \<leadsto> dest = (p = src)"
  by (simp add: n_direct_eq)

lemma parent_n_m:
  assumes "n \<turnstile> p \<rightarrow> p'"
  shows "if p' = dest then p \<noteq> src \<longrightarrow> m \<turnstile> p \<rightarrow> src else m \<turnstile> p \<rightarrow> p'"
proof -
  from assms have [simp]: "p \<noteq> dest" by (clarsimp simp: dest_no_parent_n)
  from assms
  show ?thesis
  proof induct
    case (direct_parent c)
    thus ?case
      apply simp
      apply (rule conjI)
       apply clarsimp
      apply clarsimp
      apply (rule subtree.direct_parent)
        apply (simp add: n_direct_eq split: split_if_asm)
       apply simp
      apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
      done
  next
    case (trans_parent c d)
    thus ?case
      apply clarsimp
      apply (rule conjI, clarsimp)
      apply (clarsimp split: split_if_asm)
      apply (simp add: n_direct_eq)
      apply (cases "p=src")
       apply simp
       apply (rule subtree.direct_parent, assumption, assumption)
       apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
      apply clarsimp
      apply (erule subtree.trans_parent, assumption, assumption)
      apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
     apply (erule subtree.trans_parent)
       apply (simp add: n_direct_eq split: split_if_asm)
      apply assumption
     apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
     done
 qed
qed

lemma descendants:
  "descendants_of' p n =
   (if src \<in> descendants_of' p m \<or> p = src
   then descendants_of' p m \<union> {dest} else descendants_of' p m)"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def)
  apply (fastforce dest!: parent_n_m dest: parent_m_n simp: n_dest_child split: split_if_asm)
  done

end

locale mdb_insert_sib = mdb_insert_der +
  assumes no_child:
  "\<not>isMDBParentOf
   (CTE src_cap src_node)
   (CTE c' (mdbFirstBadged_update (\<lambda>a. revokable' src_cap c')
           (mdbRevocable_update (\<lambda>a. revokable' src_cap c')
           (mdbPrev_update (\<lambda>a. src) src_node))))"
begin

(* If dest is inserted as sibling, src can not have had children.
   If it had had children, then dest_node which is just a derived copy
   of src_node would be a child as well. *)
lemma src_no_mdb_parent:
  "isMDBParentOf (CTE src_cap src_node) cte = False"
  using no_child partial_is_derived'
  apply clarsimp
  apply (case_tac cte)
  apply (clarsimp simp: isMDBParentOf_CTE is_derived'_def badge_derived'_def)
  apply (erule sameRegionAsE)
     apply (clarsimp simp add: sameRegionAs_def3)
     apply (cases src_cap,auto simp:capMasterCap_def revokable'_def vsCapRef_def freeIndex_update_def
         isCap_simps split:capability.splits arch_capability.splits)[1]
    apply (clarsimp simp: isCap_simps sameRegionAs_def3 capMasterCap_def freeIndex_update_def
       split:capability.splits arch_capability.splits)
   apply (clarsimp simp: isCap_simps sameRegionAs_def3 freeIndex_update_def
                         capRange_def vsCapRef_def split:capability.splits
               simp del: Int_atLeastAtMost atLeastAtMost_iff)
   apply auto[1]
  apply (clarsimp simp: isCap_simps sameRegionAs_def3)
  done

lemma src_no_parent:
  "m \<turnstile> src \<rightarrow> p = False"
  by (clarsimp dest!: subtree_parent simp: src_no_mdb_parent parentOf_def src)

lemma parent_preserved:
  "isMDBParentOf cte (CTE src_cap src_node) \<Longrightarrow> isMDBParentOf cte new_dest"
  using partial_is_derived'
  apply (cases cte)
  apply (case_tac "isUntypedCap src_cap")
   apply (clarsimp simp:isCap_simps isMDBParentOf_CTE freeIndex_update_def new_dest_def)
   apply (clarsimp simp:is_derived'_def isCap_simps badge_derived'_def capMasterCap_def split:capability.splits)
   apply (clarsimp simp:sameRegionAs_def2 capMasterCap_def isCap_simps split:capability.splits)
  apply (clarsimp simp: isMDBParentOf_CTE)
  apply (clarsimp simp: new_dest_def)
  apply (rename_tac cap node)
  apply (clarsimp simp: is_derived'_def badge_derived'_def)
  apply (rule conjI)
   apply (simp add: sameRegionAs_def2)
  apply (cases "revokable' src_cap c'")
   apply simp
   apply (drule(2) revokable_plus_orderD)
   apply (erule disjE)
    apply (clarsimp simp: isCap_simps)
   apply (fastforce elim: capBadge_ordering_trans)+
  done

lemma src_no_parent_n [simp]:
  "n \<turnstile> src \<rightarrow> p = False"
  apply clarsimp
  apply (erule subtree.induct)
   apply (simp add: n_direct_eq)
   apply (clarsimp simp: parentOf_def n src dest new_src_def
                         new_dest_def no_child)
  apply simp
  done

lemma parent_n:
  "n \<turnstile> p \<rightarrow> p' \<Longrightarrow> if p' = dest then m \<turnstile> p \<rightarrow> src else m \<turnstile> p \<rightarrow> p'"
  apply (cases "p=dest", simp add: dest_no_parent_n)
  apply (cases "p=src", simp)
  apply (erule subtree.induct)
   apply simp
   apply (rule conjI)
    apply (clarsimp simp: n_direct_eq)
   apply clarsimp
   apply (rule direct_parent)
     apply (simp add: n_direct_eq)
    apply assumption
   apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
  apply simp
  apply (rule conjI)
   apply (clarsimp simp: n_direct_eq split: split_if_asm)
  apply (clarsimp simp: n_direct_eq split: split_if_asm)
   apply (erule trans_parent, assumption, assumption)
   apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
  apply (erule trans_parent, assumption, assumption)
  apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
  done

lemma parent_m:
  "m \<turnstile> p \<rightarrow> p' \<Longrightarrow> n \<turnstile> p \<rightarrow> p' \<and> (p' = src \<longrightarrow> n \<turnstile> p \<rightarrow> dest)"
  apply (cases "p=src", simp add: src_no_parent)
  apply (erule subtree.induct)
   apply (rule conjI)
    apply (rule direct_parent)
      apply (clarsimp simp: n_direct_eq)
     apply assumption
    apply (fastforce simp add: parentOf_def n src new_src_def)
   apply clarsimp
   apply (rule trans_parent [where c'=src])
      apply (rule direct_parent)
        apply (simp add: n_direct_eq)
        apply (rule notI, simp)
       apply simp
      apply (simp add: parentOf_def n src new_src_def)
      apply (clarsimp simp: dest dest_cap)
     apply (simp add: n_direct_eq)
    apply simp
   apply (clarsimp simp: parentOf_def dest src n)
   apply (rule conjI, clarsimp simp: dest dest_cap)
   apply (clarsimp intro!: parent_preserved)
  apply clarsimp
  apply (case_tac "c'=src")
   apply simp
   apply (erule trans_parent [where c'=dest])
     apply (clarsimp simp: n_direct_eq)
    apply clarsimp
   apply (fastforce simp: parentOf_def dest src n)
  apply clarsimp
  apply (rule conjI)
   apply (erule trans_parent)
     apply (simp add: n_direct_eq)
     apply clarsimp
    apply assumption
   apply (fastforce simp: parentOf_def dest src n new_src_def)
  apply clarsimp
  apply (rule trans_parent [where c'=src])
     apply (erule trans_parent)
       apply (simp add: n_direct_eq)
       apply clarsimp
      apply simp
     apply (fastforce simp: parentOf_def dest src n new_src_def)
    apply (simp add: n_direct_eq)
   apply simp
  apply (fastforce simp: parentOf_def dest src n new_src_def
                  intro!: parent_preserved)
  done

lemma parent_n_eq:
  "n \<turnstile> p \<rightarrow> p' = (if p' = dest then m \<turnstile> p \<rightarrow> src else m \<turnstile> p \<rightarrow> p')"
  apply (rule iffI)
   apply (erule parent_n)
  apply (simp split: split_if_asm)
   apply (drule parent_m, simp)
  apply (drule parent_m, clarsimp)
  done

lemma descendants:
  "descendants_of' p n =
   descendants_of' p m \<union> (if src \<in> descendants_of' p m then {dest} else {})"
  by (rule set_eqI) (simp add: descendants_of'_def parent_n_eq)

end

lemma mdb_None:
  assumes F: "\<And>p'. cte_map p \<in> descendants_of' p' m' \<Longrightarrow> False"
  assumes R: "cdt_relation (swp cte_at s) (cdt s) m'"
  assumes "valid_mdb s"
  shows "cdt s p = None"
  apply (simp add: descendants_of_None [symmetric])
  apply clarsimp
  apply (frule descendants_of_cte_at2, rule assms)
  apply (insert R)
  apply (simp add: cdt_relation_def)
  apply (erule allE, erule allE, erule (1) impE)
  apply (rule_tac p'="cte_map (a,b)" in F)
  apply (drule sym)
  apply simp
  done

declare split_if [split del]

lemma derived_sameRegionAs:
  "\<lbrakk> is_derived' m p cap' cap; s \<turnstile>' cap' \<rbrakk>
       \<Longrightarrow> sameRegionAs cap cap'"
  unfolding is_derived'_def badge_derived'_def
  apply (simp add: sameRegionAs_def3)
  apply (cases "isUntypedCap cap \<or> isArchPageCap cap")
   apply (rule disjI2, rule disjI1)
   apply (erule disjE)
    apply (clarsimp simp: isCap_simps valid_cap'_def capAligned_def
                          is_aligned_no_overflow capRange_def
          split:capability.splits arch_capability.splits option.splits)
    apply (clarsimp simp: isCap_simps valid_cap'_def capAligned_def
                          is_aligned_no_overflow capRange_def
          split:capability.splits arch_capability.splits option.splits)
    apply (clarsimp simp: isCap_simps valid_cap'_def
                          is_aligned_no_overflow capRange_def
          split:capability.splits arch_capability.splits option.splits)






  done

lemma no_fail_updateMDB [wp]:
  "no_fail (\<lambda>s. p \<noteq> 0 \<longrightarrow> cte_at' p s) (updateMDB p f)"
  apply (simp add: updateMDB_def)
  apply (rule no_fail_pre, wp)
  apply (simp split: split_if)
  done

lemma updateMDB_cte_at' [wp]:
 "\<lbrace>cte_at' p\<rbrace>
  updateMDB x y
  \<lbrace>\<lambda>uu. cte_at' p\<rbrace>"
  unfolding updateMDB_def
  apply simp
  apply safe
  apply (wp setCTE_weak_cte_wp_at)
  apply (simp split: split_if)
  done

lemma updateCap_cte_at' [wp]:
 "\<lbrace>cte_at' p\<rbrace> updateCap c p' \<lbrace>\<lambda>_. cte_at' p\<rbrace>"
  unfolding updateCap_def by wp

lemma nullMDBNode_pointers[simp]:
  "mdbPrev nullMDBNode = nullPointer"
  "mdbNext nullMDBNode = nullPointer"
  by (simp add: nullMDBNode_def)+

(* Arguments to capability_case need to be in the same order as the constructors in 'capabilility' data type *)
lemma revokable'_fold:
  "revokable' srcCap cap =
  (capability_case \<bottom>                                                    (* ThreadCap        *)
                   False                                                (* NullCap          *)
                   (\<lambda>x xa xb xc. capAEPBadge cap \<noteq> capAEPBadge srcCap)  (* AsyncEndpointCap *)
                   (\<lambda>c. isIRQControlCap srcCap)                         (* IRQHandlerCap    *)
                   (\<lambda>x xa xb xc xd. capEPBadge cap \<noteq> capEPBadge srcCap) (* EndpointCap      *)
                   False                                                (* DomainCap        *)
                   (\<lambda>word zombie_type nat. False)                       (* Zombie           *)
                   \<bottom>                                                    (* ArchObjectCap    *)
                   (\<lambda>x b. False)                                        (* ReplyCap         *)
                   (\<lambda>x n1 n2. True)                                     (* UntypedCap       *)
                   (\<lambda>word1 nat1 word2 nat. False)                       (* CNodeCap         *)
                   False                                                (* IRQControlCap    *)
                   cap)"
  by (simp add: revokable'_def isCap_simps split: capability.splits)

lemma cap_relation_untyped_free_index_update:
  "\<lbrakk>cap_relation cap cap';isUntypedCap cap'\<or> is_untyped_cap cap;a = a'\<rbrakk>
   \<Longrightarrow> cap_relation (cap\<lparr>free_index:= a\<rparr>) (cap'\<lparr>capFreeIndex:=a'\<rparr>)"
  apply (clarsimp simp:isCap_simps)
  apply (case_tac cap)
    apply (clarsimp simp:free_index_update_def capFreeIndex_update.simps)+
  done

lemma maxFreeIndex_eq[simp]: "maxFreeIndex nat1 = max_free_index nat1"
  by (clarsimp simp:maxFreeIndex_def max_free_index_def shiftL_nat)

lemma max_free_index_relation:
  "\<lbrakk>cap_relation cap cap';isUntypedCap cap'\<or> is_untyped_cap cap\<rbrakk>
   \<Longrightarrow> maxFreeIndex (capBlockSize cap') = max_free_index (cap_bits cap)"
 apply (clarsimp simp:isCap_simps is_cap_simps)
 apply (case_tac cap)
   apply (auto)
done

definition maskedAsFull :: "capability \<Rightarrow> capability \<Rightarrow> capability"
where "maskedAsFull srcCap newCap \<equiv>
  if isUntypedCap srcCap \<and> isUntypedCap newCap \<and>
     capPtr srcCap = capPtr newCap \<and> capBlockSize srcCap = capBlockSize newCap
  then capFreeIndex_update (\<lambda>_. maxFreeIndex (capBlockSize srcCap)) srcCap
  else srcCap"

lemma is_derived_maskedAsFull[simp]:
  "is_derived' m slot c (maskedAsFull src_cap' a) =
   is_derived' m slot c src_cap'"
  apply (clarsimp simp: maskedAsFull_def isCap_simps split:if_splits)
  apply (case_tac c)
    apply (clarsimp simp:is_derived'_def vsCapRef_def isCap_simps badge_derived'_def )+
done


lemma maskedAsFull_revokable:
  "is_derived' x y c' src_cap' \<Longrightarrow>
   revokable' (maskedAsFull src_cap' a) c' = revokable' src_cap' c'"
  apply (case_tac src_cap')
    apply (simp_all add:maskedAsFull_def isCap_simps)
  apply (case_tac c')
    apply (simp_all add:maskedAsFull_def is_derived'_def isCap_simps vsCapRef_def)
    apply (simp_all add:badge_derived'_def capMasterCap_simps split:arch_capability.splits)
  apply (clarsimp split:if_splits simp:revokable'_def isCap_simps)
  done

lemma parentOf_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> isAsyncEndpointCap (cteCap cte)  = isAsyncEndpointCap (cteCap cte')
  \<and> (isAsyncEndpointCap (cteCap cte) \<longrightarrow> (capAEPBadge (cteCap cte) = capAEPBadge (cteCap cte')))
  \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
  \<and> (isEndpointCap (cteCap cte) \<longrightarrow> (capEPBadge (cteCap cte) = capEPBadge (cteCap cte')))
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows "(m  \<turnstile> p parentOf x) \<Longrightarrow> (m'  \<turnstile> p parentOf x)"
  apply (clarsimp simp:parentOf_def)
    apply (frule iffD1[OF dom,OF domI])
    apply (frule iffD1[OF dom[where x = p],OF domI])
    apply clarsimp
    apply (frule_tac x1 = p in conjunct1[OF sameRegion])
      apply assumption
    apply (frule_tac x1 = x in conjunct2[OF sameRegion])
      apply assumption
    apply (drule_tac x = "cteCap y" in fun_cong)
    apply (drule_tac x = "cteCap cte'" in fun_cong)
    apply (drule_tac x = p in misc)
      apply assumption
    apply (drule_tac x = x in misc)
      apply assumption
    apply (clarsimp simp:isMDBParentOf_def split:cte.splits split_if_asm)
    apply (clarsimp simp: sameRegionAs_def isCap_simps split:if_splits | rule conjI)+
done

lemma parentOf_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> isAsyncEndpointCap (cteCap cte)  = isAsyncEndpointCap (cteCap cte')
  \<and> (isAsyncEndpointCap (cteCap cte) \<longrightarrow> (capAEPBadge (cteCap cte) = capAEPBadge (cteCap cte')))
  \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
  \<and> (isEndpointCap (cteCap cte) \<longrightarrow> (capEPBadge (cteCap cte) = capEPBadge (cteCap cte')))
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows "(m  \<turnstile> p parentOf x) = (m'  \<turnstile> p parentOf x)"
  apply (rule iffI)
    apply (rule parentOf_preserve_oneway[OF dom sameRegion misc node])
      apply (assumption)+
  apply (rule parentOf_preserve_oneway)
  apply (auto simp:dom sameRegion misc node)
done

lemma updateUntypedCap_descendants_of:
  "\<lbrakk>m src = Some cte; isUntypedCap (cteCap cte)\<rbrakk>
   \<Longrightarrow> descendants_of' slot (m(src \<mapsto> cteCap_update
           (\<lambda>_. (capFreeIndex_update (\<lambda>_. idx) (cteCap cte))) cte)) =
       descendants_of' slot m"
  apply (rule set_eqI)
  apply (clarsimp simp:descendants_of'_def subtree_def)
   apply (rule_tac x = x in fun_cong)
   apply (rule_tac f = lfp in arg_cong)
   apply (rule ext)+
  apply (cut_tac x  = xa in parentOf_preserve
  [where m = "m(src \<mapsto> cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. idx) (cteCap cte)) cte)"
   and  m' = m and p = slot])
    apply (clarsimp,rule iffI,fastforce+)
    apply (clarsimp simp:isCap_simps split:if_splits)
    apply (clarsimp simp:sameRegionAs_def isCap_simps split:if_splits)
    apply (rule ext)
    apply (clarsimp simp:sameRegionAs_def isCap_simps split:if_splits)+
   apply (simp add:mdb_next_def split:if_splits)
  apply (simp del:fun_upd_apply)
  apply (subgoal_tac "\<And>p. m(src \<mapsto> cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. idx) (cteCap cte)) cte) \<turnstile> p \<leadsto> xa
     = m \<turnstile> p \<leadsto> xa")
  apply simp
  apply (clarsimp simp:mdb_next_rel_def mdb_next_def split:if_splits)
  done

lemma set_untyped_cap_corres:
  "\<lbrakk>cap_relation cap (cteCap cte); is_untyped_cap cap; idx' = idx\<rbrakk>
   \<Longrightarrow> corres dc (cte_wp_at (op = cap) src and valid_objs and
                  pspace_aligned and pspace_distinct)
                 (cte_wp_at' (op = cte) (cte_map src) and
                  pspace_distinct' and pspace_aligned')
                 (set_cap (free_index_update (\<lambda>_. idx) cap) src)
                 (setCTE (cte_map src) (cteCap_update
                    (\<lambda>cap. (capFreeIndex_update (\<lambda>_. idx') (cteCap cte))) cte))"
  apply (case_tac cte)
  apply (clarsimp simp:is_cap_simps)
  apply (rule corres_stronger_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply clarsimp
  apply (clarsimp simp add: state_relation_def split_def)
  apply (drule (1) pspace_relationsD)
  apply (frule_tac c = "cap.UntypedCap r bits idx"
                in set_cap_not_quite_corres_prequel)
         apply assumption+
       apply (erule cte_wp_at_weakenE, rule TrueI)
      apply assumption+
    apply simp+
  apply clarsimp
  apply (rule bexI)
   prefer 2
   apply assumption
  apply (clarsimp simp: pspace_relations_def)
  apply (subst conj_assoc[symmetric])
  apply (rule conjI)
   apply (frule setCTE_pspace_only)
   apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                    split: split_if_asm Structures_A.kernel_object.splits)
  apply (rule conjI)
   apply (frule setCTE_pspace_only)
   apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    apply (frule mdb_set_cap, frule exst_set_cap)
    apply (erule use_valid [OF _ setCTE_ctes_of_wp])
    apply (clarsimp simp: cdt_list_relation_def cte_wp_at_ctes_of split: split_if_asm)
   apply (rule conjI)
    prefer 2
    apply (frule setCTE_pspace_only)
    apply clarsimp
    apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                    split: split_if_asm Structures_A.kernel_object.splits)
   apply (frule set_cap_caps_of_state_monad)
   apply (drule is_original_cap_set_cap)
   apply clarsimp
   apply (erule use_valid [OF _ setCTE_ctes_of_wp])
   apply (clarsimp simp: revokable_relation_def simp del: fun_upd_apply)
   apply (clarsimp split: split_if_asm)
    apply (frule cte_map_inj_eq)
         prefer 2
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply (simp add: null_filter_def split: split_if_asm)
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply (erule caps_of_state_cte_at)
       apply fastforce
      apply fastforce
     apply fastforce
    apply clarsimp
    apply (simp add: null_filter_def split: split_if_asm)
    apply (erule_tac x=aa in allE, erule_tac x=bb in allE)
    apply (case_tac cte)
    apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps isCap_simps cte_wp_at_ctes_of)
   apply (simp add: null_filter_def cte_wp_at_caps_of_state split: split_if_asm)
   apply (erule_tac x=aa in allE, erule_tac x=bb in allE)
   apply (clarsimp)
  apply (clarsimp simp: cdt_relation_def)
  apply (frule set_cap_caps_of_state_monad)
  apply (frule mdb_set_cap)
  apply clarsimp
  apply (erule use_valid [OF _ setCTE_ctes_of_wp])
  apply (frule cte_wp_at_norm)
  apply (clarsimp simp:cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (drule_tac slot = "cte_map (aa,bb)" in updateUntypedCap_descendants_of)
   apply (clarsimp simp:isCap_simps)
  apply (drule_tac x = aa in spec)
  apply (drule_tac x = bb in spec)
  apply (erule impE)
   apply (clarsimp simp: cte_wp_at_caps_of_state split:if_splits)
  apply auto
  done

lemma getCTE_get:
  "\<lbrace>cte_wp_at' P src\<rbrace> getCTE src \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  done

lemma set_untyped_cap_as_full_corres:
  "\<lbrakk>cap_relation c c'; src' = cte_map src; dest' = cte_map dest;
    cap_relation src_cap (cteCap srcCTE); rv = cap.NullCap;
    cteCap rv' = capability.NullCap; mdbPrev (cteMDBNode rv') = nullPointer \<and>
    mdbNext (cteMDBNode rv') = nullPointer\<rbrakk>
   \<Longrightarrow> corres dc (cte_wp_at (op = src_cap) src and valid_objs and
                  pspace_aligned and pspace_distinct)
                 (cte_wp_at' (op = srcCTE) (cte_map src) and
                  pspace_aligned' and pspace_distinct')
                 (set_untyped_cap_as_full src_cap c src)
                 (setUntypedCapAsFull (cteCap srcCTE) c' (cte_map src))"
  apply (clarsimp simp:set_untyped_cap_as_full_def setUntypedCapAsFull_def max_free_index_relation
    split:if_splits)
  apply (intro conjI impI)
    apply (clarsimp simp del:capFreeIndex_update.simps simp:updateCap_def)
      apply (rule corres_guard_imp)
        apply (rule corres_symb_exec_r)
           apply (rule_tac F="cte = srcCTE" in corres_gen_asm2)
           apply (simp)
           apply (rule set_untyped_cap_corres)
             apply simp+
           apply (clarsimp simp:free_index_update_def isCap_simps is_cap_simps)
           apply (subst identity_eq)
        apply (wp getCTE_sp getCTE_get)
       apply (rule no_fail_pre[OF no_fail_getCTE])
       apply (clarsimp simp:cte_wp_at_ctes_of)+
   apply (clarsimp simp:is_cap_simps isCap_simps)+
  apply (case_tac c,simp_all)
  apply (case_tac src_cap,simp_all)
  done

lemma cap_relation_masked_as_full:
  "\<lbrakk>cap_relation src_cap src_cap';cap_relation c c'\<rbrakk> \<Longrightarrow>
    cap_relation (masked_as_full src_cap c) (maskedAsFull src_cap' c')"
  apply (clarsimp simp:masked_as_full_def maskedAsFull_def is_cap_simps isCap_simps split:if_splits)
  apply (intro conjI impI)
    apply (clarsimp simp:free_index_update_def maxFreeIndex_def max_free_index_def shiftL_nat)
    apply fastforce
  apply (elim impE disjE)
    apply (clarsimp)
    apply (case_tac src_cap,simp_all)
      apply (case_tac c,simp_all)
    apply (case_tac src_cap)
      apply (case_tac c,fastforce+)
    apply clarsimp
      apply (case_tac c)
       apply simp_all
    apply clarsimp
  apply (case_tac src_cap,simp_all)
  apply (case_tac c,simp_all)
done

lemma setUntypedCapAsFull_pspace_distinct[wp]:
  "\<lbrace>pspace_distinct' and cte_wp_at' (op = srcCTE) slot\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) c slot \<lbrace>\<lambda>r. pspace_distinct'\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits)
  apply (intro conjI impI)
    apply (clarsimp simp:valid_def)
    apply (drule updateCap_stuff)
    apply simp
  apply (wp|clarsimp)+
done

lemma setUntypedCapAsFull_pspace_aligned[wp]:
  "\<lbrace>pspace_aligned' and cte_wp_at' (op = srcCTE) slot\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) c slot
   \<lbrace>\<lambda>r. pspace_aligned'\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits)
  apply (intro conjI impI)
    apply (clarsimp simp:valid_def)
    apply (drule updateCap_stuff)
    apply simp
  apply (wp|clarsimp)+
done

(* wp rules about setFreeIndex and setUntypedCapAsFull *)
lemma setUntypedCapAsFull_ctes_of:
  "\<lbrace>\<lambda>s. src \<noteq> dest \<and> P (ctes_of s dest) \<or>
        src = dest \<and> P (Some (CTE (maskedAsFull (cteCap srcCTE) cap)
                                  (cteMDBNode srcCTE))) \<and>
        cte_wp_at' (op = srcCTE) src s\<rbrace>
  setUntypedCapAsFull (cteCap srcCTE) cap src
  \<lbrace>\<lambda>r s. P (ctes_of s dest)\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits)
  apply (intro conjI impI)
    apply (simp add:updateCap_def)
    apply (wp getCTE_wp)
    apply (clarsimp split:if_splits simp:cte_wp_at_ctes_of if_distrib)
    apply (case_tac "src = dest")
      apply (case_tac srcCTE)
      apply (clarsimp simp:maskedAsFull_def)
    apply clarsimp
  apply wp
  apply (case_tac srcCTE)
  apply (fastforce simp:maskedAsFull_def cte_wp_at_ctes_of split: if_splits)
  done

lemma setUntypedCapAsFull_ctes_of_no_0:
  "\<lbrace>\<lambda>s. no_0 ((ctes_of s)(a:=b)) \<and> cte_wp_at' (op = srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>r s. no_0 ((ctes_of s)(a:=b)) \<rbrace>"
  apply (clarsimp simp:no_0_def split:if_splits)
  apply (wp hoare_vcg_imp_lift setUntypedCapAsFull_ctes_of[where dest = 0])
    apply (auto simp:cte_wp_at_ctes_of)
  done

lemma valid_dlist_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'"
  shows  "valid_dlist m \<Longrightarrow> valid_dlist m'"
  apply (clarsimp simp:valid_dlist_def Let_def)
  apply (frule domI[where m = m'],drule iffD2[OF dom],erule domE)
    apply (elim allE impE)
    apply assumption
  apply (intro conjI impI)
    apply clarsimp
    apply (frule(1) misc)
    apply (clarsimp)
    apply (frule_tac b = cte' in domI[where m = m])
    apply (drule iffD1[OF dom])
    apply clarsimp
    apply (drule(1) misc)+
    apply simp
  apply clarsimp
  apply (frule(1) misc)
  apply (clarsimp)
  apply (frule_tac b = cte' in domI[where m = m])
  apply (drule iffD1[OF dom])
  apply clarsimp
  apply (drule(1) misc)+
  apply simp
done

lemma valid_dlist_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'"
  shows  "valid_dlist m = valid_dlist m'"
  apply (rule iffI)
   apply (rule valid_dlist_preserve_oneway[OF dom misc])
     apply simp+
  apply (rule valid_dlist_preserve_oneway)
    apply (simp add:dom misc)+
done

lemma ut_revocable_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'
  \<and> isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')"
  shows  "ut_revocable' m \<Longrightarrow> ut_revocable' m'"
  apply (clarsimp simp:ut_revocable'_def Let_def)
  apply (drule_tac x = p in spec)
  apply (frule domI[where m = m'],drule iffD2[OF dom],erule domE)
    apply (case_tac r)
    apply clarsimp
    apply (elim allE impE)
    apply (frule(1) misc)
    apply (clarsimp)
    apply (drule(1) misc)+
    apply simp
done

lemma ut_revocable_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'
  \<and> isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')"
  shows  "ut_revocable' m = ut_revocable' m'"
  apply (rule iffI)
    apply (rule ut_revocable_preserve_oneway[OF dom misc])
    apply (assumption)+
  apply (rule ut_revocable_preserve_oneway[OF dom[symmetric]])
  apply (simp add:misc)+
done

lemma class_links_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> capClass (cteCap cte) = capClass (cteCap cte')"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows  "class_links m \<Longrightarrow> class_links m'"
  apply (clarsimp simp:class_links_def Let_def)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (frule domI[where m = m'],drule iffD2[OF dom],erule domE)
    apply (case_tac r)
    apply clarsimp
    apply (frule_tac b = cte' in domI[where m = m'],drule iffD2[OF dom],erule domE)
    apply (elim allE impE)
      apply simp
    apply (frule(1) misc)
    apply (clarsimp simp:mdb_next_rel_def node)
  apply (drule(1) misc)+
    apply simp
done

lemma class_links_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> capClass (cteCap cte) = capClass (cteCap cte')"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows  "class_links m = class_links m'"
  apply (rule iffI)
    apply (rule class_links_preserve_oneway[OF dom misc])
    apply (simp add:node)+
  apply (rule class_links_preserve_oneway)
  apply (simp add:dom misc node)+
done

lemma distinct_zombies_preserve_oneway:
  assumes dom: "\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:
  "\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
      isZombie (cteCap cte) = isZombie (cteCap cte') \<and>
      isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte') \<and>
      isArchPageCap (cteCap cte) = isArchPageCap (cteCap cte') \<and>
      capBits (cteCap cte) = capBits (cteCap cte') \<and>
      capUntypedPtr (cteCap cte) = capUntypedPtr (cteCap cte') \<and>
      capClass (cteCap cte) = capClass (cteCap cte')"
  assumes node: "\<And>p. mdb_next m p = mdb_next m' p"
  shows  "distinct_zombies m \<Longrightarrow> distinct_zombies m'"
  apply (clarsimp simp:distinct_zombies_def distinct_zombie_caps_def Let_def)
  apply (drule_tac x = ptr in spec)
  apply (drule_tac x = ptr' in spec)
  apply (frule domI[where m = m'],drule iffD2[OF dom],erule domE)
    apply (case_tac r)
    apply clarsimp
    apply (frule_tac a=ptr' in domI[where m = m'],drule iffD2[OF dom],erule domE)
    apply clarsimp
    apply (drule(1) misc)+
    apply clarsimp
  done

lemma distinct_zombies_preserve:
  assumes dom: "\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:
  "\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
      isZombie (cteCap cte) = isZombie (cteCap cte') \<and>
      isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte') \<and>
      isArchPageCap (cteCap cte) = isArchPageCap (cteCap cte') \<and>
      capBits (cteCap cte) = capBits (cteCap cte') \<and>
      capUntypedPtr (cteCap cte) = capUntypedPtr (cteCap cte') \<and>
      capClass (cteCap cte) = capClass (cteCap cte')"
  assumes node: "\<And>p. mdb_next m p = mdb_next m' p"
  shows  "distinct_zombies m = distinct_zombies m'"
  apply (rule iffI)
    apply (rule distinct_zombies_preserve_oneway[OF dom misc node])
     apply (assumption)+
  apply (rule distinct_zombies_preserve_oneway)
    apply (simp add:dom misc node)+
  done

lemma caps_contained'_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> untypedRange (cteCap cte) = untypedRange (cteCap cte')
  \<and> capRange (cteCap cte) = capRange (cteCap cte')
  \<and> cteMDBNode cte = cteMDBNode cte'"
  shows "caps_contained' m \<Longrightarrow> caps_contained' m'"
  apply (clarsimp simp:caps_contained'_def)
    apply (frule iffD2[OF dom,OF domI])
    apply (frule_tac x1 = p' in iffD2[OF dom,OF domI])
    apply clarsimp
    apply (case_tac y,case_tac ya)
    apply (drule_tac x= p in spec)
    apply (drule_tac x= p' in spec)
    apply (frule_tac x = p in misc)
      apply assumption
    apply (frule_tac x = p' in misc)
      apply assumption
    apply (elim allE impE)
      apply fastforce+
  done

lemma caps_contained'_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> untypedRange (cteCap cte) = untypedRange (cteCap cte')
  \<and> capRange (cteCap cte) = capRange (cteCap cte')
  \<and> cteMDBNode cte = cteMDBNode cte'"
  shows "caps_contained' m = caps_contained' m'"
  apply (rule iffI)
    apply (rule caps_contained'_preserve_oneway[OF dom misc])
      apply (assumption)+
  apply (rule caps_contained'_preserve_oneway)
  apply (auto simp:dom misc)
  done

lemma is_chunk_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'
  \<and> sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows " \<lbrakk>m x =Some (CTE a b);m' x = Some (CTE c d)\<rbrakk> \<Longrightarrow> is_chunk m a p p' \<Longrightarrow> is_chunk m' c p p'"
  apply (clarsimp simp:is_chunk_def)
   apply (drule_tac x= p'' in spec)
    apply (subgoal_tac "m \<turnstile> p \<leadsto>\<^sup>+ p'' = m' \<turnstile> p \<leadsto>\<^sup>+ p''")
     apply (subgoal_tac "m \<turnstile> p'' \<leadsto>\<^sup>* p' = m' \<turnstile> p'' \<leadsto>\<^sup>* p'")
     apply (frule iffD1[OF dom,OF domI])
     apply (clarsimp)
     apply (frule_tac x1 = p'' in iffD1[OF dom,OF domI])
     apply clarsimp
     apply (frule_tac x = p'' in sameRegion,assumption)
     apply clarsimp
     apply (frule_tac x = x in sameRegion,assumption)
     apply clarsimp
     apply (case_tac y)
     apply (drule_tac fun_cong)+
     apply fastforce
    apply simp
   apply (erule iffD1[OF connect_eqv_singleE',rotated -1])
   apply (clarsimp simp: mdb_next_rel_def node)
  apply (rule connect_eqv_singleE)
  apply (clarsimp simp: mdb_next_rel_def node)
  done

lemma is_chunk_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'
  \<and> sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows " \<lbrakk>m x =Some (CTE a b);m' x = Some (CTE c d)\<rbrakk> \<Longrightarrow> is_chunk m a p p' = is_chunk m' c p p'"
  apply (rule iffI)
    apply (rule is_chunk_preserve_oneway[OF dom sameRegion node],assumption+)
  apply (rule is_chunk_preserve_oneway)
  apply (auto simp:dom sameRegion node)
  done

lemma mdb_chunked_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'
  \<and> sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows
  "mdb_chunked m \<Longrightarrow> mdb_chunked m'"
  apply (clarsimp simp:mdb_chunked_def)
  apply (drule_tac x=p in spec)
  apply (drule_tac x=p' in spec)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply clarsimp
  apply (case_tac ya)
  apply (case_tac y)
  apply (frule_tac x = p in sameRegion,assumption)
  apply (frule_tac x = p' in sameRegion,assumption)
  apply clarsimp
  apply (erule impE)
   apply (drule fun_cong)+
   apply fastforce
   apply (subgoal_tac "m \<turnstile> p \<leadsto>\<^sup>+ p' = m' \<turnstile> p \<leadsto>\<^sup>+ p'")
     apply (subgoal_tac "m \<turnstile> p' \<leadsto>\<^sup>+ p = m' \<turnstile> p' \<leadsto>\<^sup>+ p")
       apply (frule_tac m = m and
              x = p and c = cap and p = p and p'=p' in is_chunk_preserve[rotated -1])
              apply (simp add:dom)
              apply (rule sameRegion)
          apply simp+
        apply (rule node)
      apply assumption
     apply (frule_tac x = p' and c = cap' and p = p' and p'=p in is_chunk_preserve[rotated -1])
              apply (rule dom)
              apply (rule sameRegion)
            apply assumption+
         apply (rule node)
      apply assumption
    apply clarsimp
    apply (rule connect_eqv_singleE)
  apply (clarsimp simp:mdb_next_rel_def node)
  apply (rule connect_eqv_singleE)
  apply (clarsimp simp:mdb_next_rel_def node)
  done

lemma mdb_chunked_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'
  \<and> sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows
  "mdb_chunked m = mdb_chunked m'"
   apply (rule iffI)
     apply (erule mdb_chunked_preserve_oneway[rotated -1])
       apply (simp add:dom sameRegion node)+
   apply (erule mdb_chunked_preserve_oneway[rotated -1])
   apply (simp add:dom[symmetric])
   apply (frule sameRegion)
     apply assumption
     apply simp
   apply (simp add:node)
  done

lemma valid_badges_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    isAsyncEndpointCap (cteCap cte)  = isAsyncEndpointCap (cteCap cte')
  \<and> (isAsyncEndpointCap (cteCap cte) \<longrightarrow> (capAEPBadge (cteCap cte) = capAEPBadge (cteCap cte')))
  \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
  \<and> (isEndpointCap (cteCap cte) \<longrightarrow> (capEPBadge (cteCap cte) = capEPBadge (cteCap cte')))
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes mdb_next:"\<And>p. mdb_next m p = mdb_next m' p"
  shows "valid_badges m \<Longrightarrow> valid_badges m'"
  apply (clarsimp simp:valid_badges_def)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply clarsimp
  apply (case_tac y,case_tac ya)
  apply clarsimp
  apply (erule impE)
   apply (simp add: mdb_next mdb_next_rel_def)
  apply (erule impE)
   apply (drule(1) sameRegion)+
   apply clarsimp
   apply (drule fun_cong)+
   apply fastforce
  apply (drule(1) misc)+
  apply (clarsimp simp:isCap_simps sameRegionAs_def split:if_splits)
  done

lemma valid_badges_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    isAsyncEndpointCap (cteCap cte)  = isAsyncEndpointCap (cteCap cte')
  \<and> (isAsyncEndpointCap (cteCap cte) \<longrightarrow> (capAEPBadge (cteCap cte) = capAEPBadge (cteCap cte')))
  \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
  \<and> (isEndpointCap (cteCap cte) \<longrightarrow> (capEPBadge (cteCap cte) = capEPBadge (cteCap cte')))
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes mdb_next:"\<And>p. mdb_next m p = mdb_next m' p"
  shows "valid_badges m = valid_badges m'"
  apply (rule iffI)
    apply (rule valid_badges_preserve_oneway[OF dom misc sameRegion mdb_next])
    apply assumption+
  apply (rule valid_badges_preserve_oneway)
  apply (simp add:dom misc sameRegion mdb_next)+
  done

lemma mdb_untyped'_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> untypedRange (cteCap cte) = untypedRange (cteCap cte')
  \<and> isAsyncEndpointCap (cteCap cte)  = isAsyncEndpointCap (cteCap cte')
  \<and> (isAsyncEndpointCap (cteCap cte) \<longrightarrow> (capAEPBadge (cteCap cte) = capAEPBadge (cteCap cte')))
  \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
  \<and> (isEndpointCap (cteCap cte) \<longrightarrow> (capEPBadge (cteCap cte) = capEPBadge (cteCap cte')))
  \<and> capRange (cteCap cte) = capRange (cteCap cte')
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'
  \<and> sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes mdb_next:"\<And>p. mdb_next m p = mdb_next m' p"
  shows
  "untyped_mdb' m \<Longrightarrow> untyped_mdb' m'"
  apply (clarsimp simp:untyped_mdb'_def)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply clarsimp
  apply (case_tac y,case_tac ya)
  apply (frule misc)
    apply fastforce
  apply clarsimp
  apply (frule_tac x = p' in misc)
    apply fastforce
  apply (frule_tac x = p in misc)
    apply assumption
  apply clarsimp
  apply (clarsimp simp: descendants_of'_def Invariants_H.subtree_def)
  apply (erule_tac f1 = "\<lambda>x. lfp x ?x" in iffD1[OF arg_cong,rotated])
    apply (rule ext)+
      apply (subgoal_tac "\<And>p p'. (m \<turnstile> p \<leadsto> p') = (m' \<turnstile> p \<leadsto> p')")
        apply (thin_tac "?x \<longrightarrow> ?y")+
        apply (thin_tac "?P aa")+
        apply (subgoal_tac "(m \<turnstile> p parentOf x) = (m' \<turnstile> p parentOf x)")
        apply fastforce
      apply (rule parentOf_preserve[OF dom])
  apply (simp add:misc sameRegion mdb_next mdb_next_rel_def)+
  done


lemma untyped_mdb'_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> untypedRange (cteCap cte) = untypedRange (cteCap cte')
  \<and> isAsyncEndpointCap (cteCap cte)  = isAsyncEndpointCap (cteCap cte')
  \<and> (isAsyncEndpointCap (cteCap cte) \<longrightarrow> (capAEPBadge (cteCap cte) = capAEPBadge (cteCap cte')))
  \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
  \<and> (isEndpointCap (cteCap cte) \<longrightarrow> (capEPBadge (cteCap cte) = capEPBadge (cteCap cte')))
  \<and> capRange (cteCap cte) = capRange (cteCap cte')
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow> cteMDBNode cte = cteMDBNode cte'
  \<and> sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes mdb_next:"\<And>p. mdb_next m p = mdb_next m' p"
  shows
  "untyped_mdb' m = untyped_mdb' m'"
  apply (rule iffI)
    apply (erule mdb_untyped'_preserve_oneway[rotated -1])
      apply (simp add:dom misc sameRegion range mdb_next)+
   apply (erule mdb_untyped'_preserve_oneway[rotated -1])
   apply (simp add:dom[symmetric])
     apply (frule(1) misc,simp)
     apply (frule(1) sameRegion,simp)
   apply (simp add:mdb_next[symmetric])+
done

lemma mdb_inc'_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> untypedRange (cteCap cte) = untypedRange (cteCap cte')
  \<and> (isUntypedCap (cteCap cte) \<longrightarrow> usableUntypedRange (cteCap cte') \<subseteq> usableUntypedRange (cteCap cte))
  \<and> isAsyncEndpointCap (cteCap cte)  = isAsyncEndpointCap (cteCap cte')
  \<and> (isAsyncEndpointCap (cteCap cte) \<longrightarrow> (capAEPBadge (cteCap cte) = capAEPBadge (cteCap cte')))
  \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
  \<and> (isEndpointCap (cteCap cte) \<longrightarrow> (capEPBadge (cteCap cte) = capEPBadge (cteCap cte')))
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes mdb_next:"\<And>p. mdb_next m p = mdb_next m' p"
  shows
  "untyped_inc' m \<Longrightarrow> untyped_inc' m'"
  apply (clarsimp simp:untyped_inc'_def)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply clarsimp
  apply (case_tac y,case_tac ya)
  apply (drule_tac x = capability in spec)
  apply clarsimp
  apply (frule_tac x = p' in misc)
    apply assumption
  apply (frule_tac x = p in misc)
    apply assumption
  apply clarsimp
  apply (subgoal_tac  "\<And>p p'. (p' \<in>descendants_of' p m) = (p' \<in> descendants_of' p m')")
  apply (intro conjI impI)
       apply clarsimp+
      apply (drule(1) disjoint_subset2[rotated],simp add:Int_ac)
     apply clarsimp+
    apply (drule(1) disjoint_subset2[rotated],simp add:Int_ac)
   apply clarsimp
  apply (drule_tac x = p' in meta_spec)
  apply (drule_tac x = p in meta_spec)
   apply (erule disjE)
    apply clarsimp+
  apply (thin_tac "?P")+
    apply (clarsimp simp: descendants_of'_def Invariants_H.subtree_def)
    apply (rule_tac f = "\<lambda>x. lfp x ?c" in arg_cong)
      apply (subgoal_tac "\<And>p p'. (m \<turnstile> p \<leadsto> p') = (m' \<turnstile> p \<leadsto> p')")
        apply (rule ext)+
        apply clarsimp
        apply (subgoal_tac "(m \<turnstile> pa parentOf x) = (m' \<turnstile> pa parentOf x)")
        apply fastforce
      apply (rule parentOf_preserve[OF dom])
  apply (simp add:misc sameRegion mdb_next mdb_next_rel_def)+
done

lemma irq_control_preserve_oneway:
  assumes dom: "\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:
  "\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
      isIRQControlCap (cteCap cte) = isIRQControlCap (cteCap cte') \<and>
      cteMDBNode cte = cteMDBNode cte'"
  shows "irq_control m \<Longrightarrow> irq_control m'"
  apply (clarsimp simp:irq_control_def)
    apply (frule iffD2[OF dom,OF domI])
    apply clarsimp
    apply (frule(1) misc)
    apply (clarsimp simp:isCap_simps)
    apply (case_tac y)
    apply (elim allE impE)
      apply fastforce
    apply clarsimp
    apply (drule_tac x = p' in spec)
    apply (erule impE)
    apply (frule_tac x1 = p' in iffD2[OF dom,OF domI])
    apply clarsimp
    apply (drule(1) misc)+
    apply (case_tac y)
    apply (simp add:isCap_simps)+
  done

lemma irq_control_preserve:
  assumes dom: "\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:
  "\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
      isIRQControlCap (cteCap cte) = isIRQControlCap (cteCap cte') \<and>
      cteMDBNode cte = cteMDBNode cte'"
  shows "irq_control m = irq_control m'"
  apply (rule iffI[OF irq_control_preserve_oneway[OF dom misc]])
    apply (assumption)+
  apply (rule irq_control_preserve_oneway)
  apply (simp add:dom misc)+
  done

locale mdb_inv_preserve =
  fixes m m'
  assumes dom: "\<And>x. (x\<in> dom m)  = (x\<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> isNullCap (cteCap cte) = isNullCap (cteCap cte')
  \<and> isReplyCap (cteCap cte) = isReplyCap (cteCap cte')
  \<and> (isReplyCap (cteCap cte) \<longrightarrow> capReplyMaster (cteCap cte) = capReplyMaster (cteCap cte'))
  \<and> isAsyncEndpointCap (cteCap cte)  = isAsyncEndpointCap (cteCap cte')
  \<and> (isAsyncEndpointCap (cteCap cte) \<longrightarrow> (capAEPBadge (cteCap cte) = capAEPBadge (cteCap cte')))
  \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
  \<and> (isEndpointCap (cteCap cte) \<longrightarrow> (capEPBadge (cteCap cte) = capEPBadge (cteCap cte')))
  \<and> untypedRange (cteCap cte) = untypedRange (cteCap cte')
  \<and> capClass (cteCap cte) = capClass (cteCap cte')
  \<and> isZombie (cteCap cte) = isZombie (cteCap cte')
  \<and> isArchPageCap (cteCap cte) = isArchPageCap (cteCap cte')
  \<and> capBits (cteCap cte) = capBits (cteCap cte')
  \<and> RetypeDecls_H.capUntypedPtr (cteCap cte) = RetypeDecls_H.capUntypedPtr (cteCap cte')
  \<and> capRange (cteCap cte) = capRange (cteCap cte')
  \<and> isIRQControlCap (cteCap cte) = isIRQControlCap (cteCap cte')
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
     sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes mdb_next:"\<And>p. mdb_next m p = mdb_next m' p"
begin

lemma preserve_stuff:
  "valid_dlist m = valid_dlist m'
 \<and> ut_revocable' m = ut_revocable' m'
 \<and> class_links m = class_links m'
 \<and> distinct_zombies m = distinct_zombies m'
 \<and> caps_contained' m = caps_contained' m'
 \<and> mdb_chunked m = mdb_chunked m'
 \<and> valid_badges m = valid_badges m'
 \<and> untyped_mdb' m = untyped_mdb' m'
 \<and> irq_control m = irq_control m'"
  apply (intro conjI)
    apply (rule valid_dlist_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
    apply (rule ut_revocable_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
    apply (rule class_links_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
    apply (rule distinct_zombies_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
    apply (rule caps_contained'_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
    apply (rule mdb_chunked_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
    apply (rule valid_badges_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
    apply (rule untyped_mdb'_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
    apply (rule irq_control_preserve)
      apply (simp add:mdb_inv_preserve_def dom misc sameRegion mdb_next)+
  done

lemma untyped_inc':
  assumes subeq: "\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte';isUntypedCap (cteCap cte)\<rbrakk> \<Longrightarrow>
  usableUntypedRange (cteCap cte') \<subseteq> usableUntypedRange (cteCap cte)"
  shows "untyped_inc' m \<Longrightarrow> untyped_inc' m'"
  apply (clarsimp simp:untyped_inc'_def)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply clarsimp
  apply (case_tac y,case_tac ya)
  apply (drule_tac x = capability in spec)
  apply clarsimp
  apply (frule_tac x = p' in misc)
    apply assumption
  apply (frule_tac x = p in misc)
    apply assumption
  apply clarsimp
  apply (drule(1) subeq,simp)+
  apply (subgoal_tac  "\<And>p p'. (p' \<in>descendants_of' p m) = (p' \<in> descendants_of' p m')")
  apply clarsimp
  apply (intro conjI impI)
    apply clarsimp
    apply (drule(1) disjoint_subset2[rotated],clarsimp+)+
   apply (erule disjE)
   apply clarsimp+
  apply (thin_tac "?P")+
    apply (clarsimp simp: descendants_of'_def Invariants_H.subtree_def)
    apply (rule_tac f = "\<lambda>x. lfp x ?c" in arg_cong)
      apply (subgoal_tac "\<And>p p'. (m \<turnstile> p \<leadsto> p') = (m' \<turnstile> p \<leadsto> p')")
        apply (rule ext)+
        apply clarsimp
        apply (subgoal_tac "(m \<turnstile> pa parentOf x) = (m' \<turnstile> pa parentOf x)")
        apply fastforce
      apply (rule parentOf_preserve[OF dom])
  apply (simp add:misc sameRegion mdb_next mdb_next_rel_def)+
  done

lemma descendants_of:
  "descendants_of' p m = descendants_of' p m'"
  apply (rule set_eqI)
  apply (clarsimp simp:descendants_of'_def Invariants_H.subtree_def)
   apply (rule_tac f = "\<lambda>x. lfp x ?c" in arg_cong)
   apply (rule ext)+
    apply (subgoal_tac "\<And>p p'. (m \<turnstile> p \<leadsto> p') = (m' \<turnstile> p \<leadsto> p')")
    apply clarsimp
     apply (subgoal_tac "(m \<turnstile> p parentOf xa) = (m' \<turnstile> p parentOf xa)")
        apply fastforce
      apply (rule parentOf_preserve[OF dom])
  apply (simp add:misc sameRegion mdb_next mdb_next_rel_def)+
  done

lemma by_products:
  "reply_masters_rvk_fb m = reply_masters_rvk_fb m'
 \<and> no_0 m = no_0 m' \<and> mdb_chain_0 m = mdb_chain_0 m'
 \<and> valid_nullcaps m = valid_nullcaps m'"
apply (intro conjI)
  apply (simp add:ran_dom reply_masters_rvk_fb_def mdb_inv_preserve_def dom misc sameRegion mdb_next)
    apply (rule iffI)
    apply clarsimp
    apply (drule_tac x = y in bspec)
     apply (rule iffD2[OF dom])
     apply clarsimp
    apply (frule iffD2[OF dom,OF domI],rotate_tac)
    apply (clarsimp simp:misc)+
    apply (drule_tac x = y in bspec)
     apply (rule iffD1[OF dom])
     apply clarsimp
    apply (frule iffD1[OF dom,OF domI],rotate_tac)
   apply (clarsimp simp:misc)+
   apply (clarsimp simp:no_0_def)
   apply (rule ccontr)
   apply (simp add:dom_in)
   apply (subst (asm) dom[symmetric])
   apply fastforce
   apply (rule iffI)
   apply (clarsimp simp:mdb_chain_0_def)
      apply (drule_tac x =x in bspec)
      apply (rule iffD2[OF dom],clarsimp)
      apply (erule_tac iffD1[OF connect_eqv_singleE,rotated])
      apply (cut_tac p = p in mdb_next)
      apply (clarsimp simp: mdb_next_rel_def)
    apply (clarsimp simp:mdb_chain_0_def)
      apply (drule_tac x =x in bspec)
      apply (rule iffD1[OF dom],clarsimp)
      apply (erule_tac iffD1[OF connect_eqv_singleE,rotated])
      apply (cut_tac p = p in mdb_next)
      apply (clarsimp simp: mdb_next_rel_def)
   apply (simp add:valid_nullcaps_def)
   apply (rule forall_eq,clarsimp)+
     apply (rule iffI)
      apply clarsimp
      apply (frule iffD2[OF dom,OF domI])
      apply (clarsimp)
      apply (case_tac y)
      apply (drule misc)
        apply assumption
        apply (clarsimp simp:isCap_simps)
     apply clarsimp
     apply (frule iffD1[OF dom,OF domI])
     apply (clarsimp)
     apply (case_tac y)
     apply (drule misc)
       apply assumption
       apply (clarsimp simp:isCap_simps)
done

end

lemma mdb_inv_preserve_modify_map:
  "mdb_inv_preserve m m' \<Longrightarrow>
   mdb_inv_preserve (modify_map m slot (cteMDBNode_update f))
                    (modify_map m' slot (cteMDBNode_update f))"
  apply (clarsimp simp:mdb_inv_preserve_def split:if_splits)
  apply (intro conjI)
    apply (clarsimp simp:modify_map_dom)
    apply (clarsimp simp:modify_map_def split:if_splits)+
    apply (clarsimp simp:map_option_def split:option.splits if_splits)
    apply (drule_tac x = p in spec)+
    apply (intro conjI allI impI)
      apply (clarsimp simp:mdb_next_def split:if_splits)+
  done

lemma mdb_inv_preserve_updateCap:
  "\<lbrakk>m slot = Some cte;isUntypedCap (cteCap cte)\<rbrakk> \<Longrightarrow>
   mdb_inv_preserve m (modify_map m slot
     (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap cte))))"
  apply (clarsimp simp:mdb_inv_preserve_def modify_map_dom isCap_simps modify_map_def split:if_splits)
  apply (intro conjI impI allI)
    apply fastforce
    apply (simp add:sameRegionAs_update_untyped)
    apply (rule ext,simp add:sameRegionAs_update_untyped')
    apply (simp add:mdb_next_def split:if_splits)
  done

lemma mdb_inv_preserve_fun_upd:
  "mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (m(a \<mapsto> b)) (m'(a \<mapsto> b))"
  by (clarsimp simp:mdb_inv_preserve_def mdb_next_def split:if_splits)

lemma updateCap_ctes_of_wp:
  "\<lbrace>\<lambda>s.  P (modify_map (ctes_of s) ptr (cteCap_update (\<lambda>_. cap)))\<rbrace>
  updateCap ptr cap
  \<lbrace>\<lambda>r s.  P (ctes_of s)\<rbrace>"
  by (rule validI, simp add: updateCap_stuff)

lemma updateCapFreeIndex_mdb_chain_0:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (mdb_chain_0 (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (mdb_chain_0 (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.by_products)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_valid_badges:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (valid_badges (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (valid_badges (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_caps_contained:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (caps_contained' (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (caps_contained' (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_valid_nullcaps:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (valid_nullcaps (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (valid_nullcaps (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.by_products)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_ut_revocable:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (ut_revocable'(Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (ut_revocable' (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_class_links:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (class_links (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (class_links (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_reply_masters_rvk_fb:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (reply_masters_rvk_fb (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (reply_masters_rvk_fb (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.by_products)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_distinct_zombies:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (distinct_zombies (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (distinct_zombies (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_mdb_chunked:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (mdb_chunked (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (mdb_chunked (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_untyped_mdb':
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (untyped_mdb' (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (untyped_mdb' (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateCapFreeIndex_irq_control:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (irq_control (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (irq_control (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma setUntypedCapAsFull_mdb_chunked:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (mdb_chunked (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (mdb_chunked (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
   apply (wp updateCapFreeIndex_mdb_chunked)
   apply (clarsimp simp:preserve cte_wp_at_ctes_of)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_untyped_mdb':
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (untyped_mdb' (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (untyped_mdb' (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_untyped_mdb')
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_mdb_chain_0:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (mdb_chain_0 (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (mdb_chain_0 (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
   apply (wp updateCapFreeIndex_mdb_chain_0)
   apply (clarsimp simp:preserve cte_wp_at_ctes_of)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_irq_control:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (irq_control (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (irq_control (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_irq_control)
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_valid_badges:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (valid_badges (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (valid_badges (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_valid_badges)
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_caps_contained:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (caps_contained' (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (caps_contained' (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_caps_contained)
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_valid_nullcaps:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (valid_nullcaps (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (valid_nullcaps (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_valid_nullcaps)
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_ut_revocable:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (ut_revocable' (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (ut_revocable' (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_ut_revocable)
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_class_links:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (class_links(Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (class_links (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_class_links)
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_distinct_zombies:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (distinct_zombies (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (distinct_zombies (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_distinct_zombies)
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma setUntypedCapAsFull_reply_masters_rvk_fb:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (reply_masters_rvk_fb (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (reply_masters_rvk_fb (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
    apply (wp updateCapFreeIndex_reply_masters_rvk_fb)
    apply (clarsimp simp:cte_wp_at_ctes_of preserve)+
  apply wp
  apply clarsimp
done

lemma modify_map_eq[simp]:
  "\<lbrakk>m slot = Some srcCTE; cap = cteCap srcCTE\<rbrakk>
   \<Longrightarrow>(modify_map m slot (cteCap_update (\<lambda>_. cap))) = m"
  apply (rule ext)
  apply (case_tac srcCTE)
  apply (auto simp:modify_map_def split:if_splits)
  done

lemma setUntypedCapAsFull_ctes:
 "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>c. c = srcCTE) src s \<and>
   P (modify_map (ctes_of s) src (cteCap_update (\<lambda>_. maskedAsFull (cteCap srcCTE) cap)))
  \<rbrace>
 setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (ctes_of s)\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
   apply (wp updateCap_ctes_of_wp)
   apply (clarsimp simp:isCap_simps max_free_index_def maskedAsFull_def)
  apply wp
  apply (clarsimp simp:isCap_simps cte_wp_at_ctes_of
    max_free_index_def maskedAsFull_def split:if_splits)
  done

lemma setUntypedCapAsFull_valid_cap:
  "\<lbrace>valid_cap' cap and cte_wp_at' (op = srcCTE) slot\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) c slot
   \<lbrace>\<lambda>r. valid_cap' cap\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits)
  apply (intro conjI impI)
    apply (clarsimp simp:updateCap_def)
  apply (wp|clarsimp)+
done

lemma cteCap_update_simps:
  "cteCap_update f srcCTE = CTE (f (cteCap srcCTE)) (cteMDBNode srcCTE)"
  apply (case_tac srcCTE)
  apply auto
done

lemma setUntypedCapAsFull_cte_wp_at:
  "\<lbrace>cte_wp_at' (op = srcCTE) slot and
    (\<lambda>s. cte_wp_at' (\<lambda>c. P c) dest s \<and> dest \<noteq> slot \<or>
         dest = slot \<and> cte_wp_at' (\<lambda>c. P (CTE (maskedAsFull (cteCap c) c')
                                              (cteMDBNode c))) slot s) \<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) c' slot
   \<lbrace>\<lambda>r s. cte_wp_at' (\<lambda>c. P c) dest s\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def cte_wp_at_ctes_of split:if_splits)
   apply (case_tac "dest = slot")
    apply (intro conjI impI)
      apply (clarsimp simp:updateCap_def)
      apply (wp getCTE_wp)
      apply (clarsimp simp:maskedAsFull_def cte_wp_at_ctes_of cteCap_update_simps)
    apply wp
    apply (case_tac srcCTE)
    apply (fastforce simp:maskedAsFull_def cte_wp_at_ctes_of)
  apply (intro conjI impI)
    apply (clarsimp simp:updateCap_def | wp setCTE_weak_cte_wp_at getCTE_wp)+
    apply (simp add:cte_wp_at'_def)
  apply (clarsimp simp:updateCap_def | wp setCTE_weak_cte_wp_at getCTE_wp)+
  done

lemma maskedAsFull_freeIndex_update:
  "maskedAsFull srcCap newCap =
   freeIndex_update srcCap
     (\<lambda>c. if isUntypedCap srcCap \<and> isUntypedCap newCap \<and>
             capPtr srcCap = capPtr newCap \<and>
             capBlockSize srcCap = capBlockSize newCap
          then maxFreeIndex (capBlockSize srcCap)
          else capFreeIndex srcCap)"
  apply (case_tac "isUntypedCap srcCap")
  apply (clarsimp simp:maskedAsFull_def isCap_simps freeIndex_update_def split:if_splits simp:maxFreeIndex_def)
  apply (intro conjI)
    apply fastforce+
  apply (clarsimp simp:maskedAsFull_def isCap_simps
    split:if_splits simp:maxFreeIndex_def)
  done

lemma mdb_inv_preserve_sym:"mdb_inv_preserve a b \<Longrightarrow> mdb_inv_preserve b a"
 by (simp add:mdb_inv_preserve_def)


lemma mdb_inv_preserve_refl[simp]:
  "mdb_inv_preserve m m"
   by (simp add:mdb_inv_preserve_def)

lemma setUntypedCapAsFull_mdb[wp]:
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> cte_wp_at' (\<lambda>c. c = srcCTE) slot s \<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap slot
   \<lbrace>\<lambda>rv s. valid_mdb' s\<rbrace>"
  apply (clarsimp simp:valid_mdb'_def)
  apply (wp setUntypedCapAsFull_ctes)
  apply (subgoal_tac "mdb_inv_preserve (ctes_of s) (modify_map (ctes_of s) slot
              (cteCap_update (\<lambda>_.  maskedAsFull (cteCap srcCTE) cap)))")
    apply (frule mdb_inv_preserve.untyped_inc')
      apply (clarsimp simp:modify_map_def max_free_index_def
        maskedAsFull_def isCap_simps cte_wp_at_ctes_of
        split:if_splits)
   apply (clarsimp simp:valid_mdb_ctes_def mdb_inv_preserve.preserve_stuff)+
   apply (clarsimp simp:mdb_inv_preserve.by_products[OF mdb_inv_preserve_sym])
  apply (clarsimp simp:maskedAsFull_def cte_wp_at_ctes_of split:if_splits)
  apply (erule(1) mdb_inv_preserve_updateCap)
  done

lemma untyped_inc'_maskedAsFull:
  "\<lbrakk>untyped_inc' m ;m slot = Some srcCTE\<rbrakk>
   \<Longrightarrow> untyped_inc' (modify_map m slot
                       (cteCap_update (\<lambda>_. maskedAsFull (cteCap srcCTE) c')))"
  apply (rule mdb_inv_preserve.untyped_inc'[where m = m])
    apply (clarsimp simp:maskedAsFull_def split:if_splits)
    apply (erule(1) mdb_inv_preserve_updateCap)
   apply (case_tac cte)
   apply (clarsimp simp:modify_map_def maskedAsFull_def max_free_index_def
     isCap_simps split:if_splits)
  apply simp
  done

lemma (in mdb_insert_abs_sib) next_slot_no_parent':
  "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m; m src = None\<rbrakk>
    \<Longrightarrow> next_slot p t (m(dest := None)) = next_slot p t m"
  by (insert next_slot_no_parent, simp add: n_def)

lemma no_parent_next_not_child_None:
  "\<lbrakk>m p = None; finite_depth m\<rbrakk> \<Longrightarrow> next_not_child p t m = None"
  apply(rule next_not_child_NoneI)
    apply(fastforce simp: descendants_of_def cdt_parent_defs dest: tranclD2)
   apply(simp add: next_sib_def)
  apply(simp)
  done

lemma (in mdb_insert_abs_sib) next_slot':
  "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m; m src = Some src_p; t src = []\<rbrakk>
    \<Longrightarrow> next_slot p (t(src_p := list_insert_after (t src_p) src dest))
        (m(dest := Some src_p)) =
       (if p = src then Some dest
        else if p = dest then next_slot src t m else next_slot p t m)"
  by (insert next_slot, simp add: n_def)

lemmas valid_list_def = valid_list_2_def

crunch valid_list[wp]: set_untyped_cap_as_full valid_list

lemma updateMDB_the_lot':
  assumes "(x, s'') \<in> fst (updateMDB p f s')"
  assumes "pspace_relations (ekheap sa) (kheap s) (ksPSpace s')"
  assumes "pspace_aligned' s'" "pspace_distinct' s'" "no_0 (ctes_of s')" "ekheap s = ekheap sa"
  shows "ctes_of s'' = modify_map (ctes_of s') p (cteMDBNode_update f) \<and>
         ksMachineState s'' = ksMachineState s' \<and>
         ksWorkUnitsCompleted s'' = ksWorkUnitsCompleted s' \<and>
         ksCurThread s'' = ksCurThread s' \<and>
         ksIdleThread s'' = ksIdleThread s' \<and>
         ksReadyQueues s'' = ksReadyQueues s' \<and>
         ksSchedulerAction s'' = ksSchedulerAction s' \<and>
         ksInterruptState s'' = ksInterruptState s' \<and>
         ksArchState s'' = ksArchState s' \<and>
         gsUserPages s'' = gsUserPages s' \<and>
         gsCNodes s'' = gsCNodes s' \<and>
         pspace_relations (ekheap s) (kheap s) (ksPSpace s'') \<and>
         pspace_aligned' s'' \<and> pspace_distinct' s'' \<and>
         no_0 (ctes_of s'') \<and>
         ksDomScheduleIdx s'' = ksDomScheduleIdx s' \<and>
         ksDomSchedule s''    = ksDomSchedule s' \<and>
         ksCurDomain s''      = ksCurDomain s' \<and>
         ksDomainTime s''     = ksDomainTime s'"
  apply (rule updateMDB_the_lot)
      using assms
      apply (fastforce simp: pspace_relations_def)+
      done

lemma cins_corres:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
        trans_state_update'[symmetric,simp]
  assumes "cap_relation c c'" "src' = cte_map src" "dest' = cte_map dest"
  shows "corres dc
        (valid_objs and pspace_distinct and pspace_aligned and
         valid_mdb and valid_list and K (src\<noteq>dest) and
         cte_wp_at (\<lambda>c. c=Structures_A.NullCap) dest and
         (\<lambda>s. cte_wp_at (is_derived (cdt s) src c) src s))
        (pspace_distinct' and pspace_aligned' and valid_mdb' and valid_cap' c' and
         cte_wp_at' (\<lambda>c. cteCap c=NullCap) dest')
        (cap_insert c src dest)
        (cteInsert c' src' dest')"
  (is "corres _ (?P and (\<lambda>s. cte_wp_at _ _ s)) (?P' and cte_wp_at' _ _) _ _")
  using assms
  unfolding cap_insert_def cteInsert_def
  apply (fold revokable_def revokable'_fold)
  apply simp
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_cap_corres])
      apply (rule corres_split [OF _ get_cap_corres])
        apply (rule_tac F="cteCap rv' = NullCap" in corres_gen_asm2)
        apply simp
        apply (rule_tac P="?P and cte_at dest and
                            (\<lambda>s. cte_wp_at (is_derived (cdt s) src c) src s) and
                            cte_wp_at (op = src_cap) src" and
                        Q="?P' and
                           cte_wp_at' (op = rv') (cte_map dest) and
                           cte_wp_at' (op = srcCTE) (cte_map src)"
                        in corres_assert_assume)
         prefer 2
         apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def valid_nullcaps_def)
         apply (case_tac rv')
         apply (simp add: initMDBNode_def)
         apply (erule allE)+
         apply (erule (1) impE)
         apply (simp add: nullPointer_def)
        apply (rule corres_guard_imp)
          apply (rule_tac R="\<lambda>r. ?P and cte_at dest and
                            (\<lambda>s. (is_derived (cdt s) src c) src_cap) and
                            cte_wp_at (op = (masked_as_full src_cap c)) src" and
                        R'="\<lambda>r. ?P' and cte_wp_at' (op = rv') (cte_map dest) and
                           cte_wp_at' (op = (CTE (maskedAsFull (cteCap srcCTE) c') (cteMDBNode srcCTE)))
                           (cte_map src)"
                        in corres_split[where r'=dc])
             apply (rule corres_stronger_no_failI)
              apply (rule no_fail_pre)
               apply (wp hoare_weak_lift_imp)
              apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def)
              apply (erule_tac valid_dlistEn[where p = "cte_map src"])
                apply (simp+)[3]
             apply (clarsimp simp: corres_underlying_def state_relation_def
                                   in_monad valid_mdb'_def valid_mdb_ctes_def)
             apply (drule (1) pspace_relationsD)
             apply (drule (18) set_cap_not_quite_corres)
              apply (rule refl)
             apply (elim conjE exE)
             apply (rule bind_execI, assumption)
             apply (subgoal_tac "mdb_insert_abs (cdt a) src dest")
              prefer 2
              apply (erule mdb_insert_abs.intro)
              apply (rule mdb_Null_None)
              apply (simp add: op_equal)
              apply simp
              apply (rule mdb_Null_descendants)
              apply (simp add: op_equal)
              apply simp
             apply (subgoal_tac "no_mloop (cdt a)")
              prefer 2
              apply (simp add: valid_mdb_def)
             apply (clarsimp simp: exec_gets update_cdt_def bind_assoc
                              set_cdt_def
                              exec_get exec_put set_original_def modify_def simp del: fun_upd_apply
                                | (rule bind_execI[where f="cap_insert_ext x y z i p",standard], clarsimp simp: exec_gets exec_get put_def mdb_insert_abs.cap_insert_ext_det_def2 update_cdt_list_def set_cdt_list_def, rule refl))+
             apply (clarsimp simp: put_def state_relation_def)
             apply (drule updateCap_stuff)
             apply clarsimp
             apply (drule (3) updateMDB_the_lot', simp, simp, elim conjE)
             apply (drule (3) updateMDB_the_lot', simp, simp, elim conjE)
             apply (drule (3) updateMDB_the_lot', simp, simp,  elim conjE)
             apply (clarsimp simp: cte_wp_at_ctes_of nullPointer_def
                              prev_update_modify_mdb_relation)
             apply (subgoal_tac "cte_map dest \<noteq> 0")
              prefer 2
              apply (clarsimp simp: valid_mdb'_def
                               valid_mdb_ctes_def no_0_def)
             apply (subgoal_tac "cte_map src \<noteq> 0")
              prefer 2
              apply (clarsimp simp: valid_mdb'_def
                               valid_mdb_ctes_def no_0_def)
             apply (thin_tac "ksMachineState ?t = ?p")+
             apply (thin_tac "ksCurThread ?t = ?p")+
             apply (thin_tac "ksIdleThread ?t = ?p")+
             apply (thin_tac "ksReadyQueues ?t = ?p")+
             apply (thin_tac "ksSchedulerAction ?t = ?p")+
             apply (clarsimp simp: pspace_relations_def)

             apply (rule conjI)
              apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)
             apply (rule conjI)
              defer
              apply(rule conjI)
               apply (thin_tac "ctes_of ?s = ?t")+
               apply (thin_tac "pspace_relation ?s ?t")+
               apply (thin_tac "machine_state ?t = ?s")+
               apply (case_tac "srcCTE")
               apply (rename_tac src_cap' src_node)
               apply (case_tac "rv'")
               apply (rename_tac dest_node)
               apply (clarsimp simp: in_set_cap_cte_at_swp)
               apply (subgoal_tac "cte_at src a \<and> is_derived (cdt a) src c src_cap")
                prefer 2
                apply (fastforce simp: cte_wp_at_def)
               apply (erule conjE)
               apply (subgoal_tac "mdb_insert (ctes_of b) (cte_map src) (maskedAsFull src_cap' c') src_node
                                  (cte_map dest) NullCap dest_node")
                prefer 2
                apply (rule mdb_insert.intro)
                  apply (rule mdb_ptr.intro)
                   apply (rule vmdb.intro, simp add: valid_mdb_ctes_def)
                  apply (erule mdb_ptr_axioms.intro)
                 apply (rule mdb_ptr.intro)
                  apply (rule vmdb.intro, simp add: valid_mdb_ctes_def)
                 apply (erule mdb_ptr_axioms.intro)
                apply (rule mdb_insert_axioms.intro)
                     apply (rule refl)
                    apply assumption
                   apply assumption
                  apply assumption
                 apply assumption
                apply (erule (5) cte_map_inj)
               apply (frule mdb_insert_der.intro)
                apply (rule mdb_insert_der_axioms.intro)
                apply (simp add: is_derived_eq)
               apply (simp (no_asm_simp) add: cdt_relation_def split: split_if)
               apply (subgoal_tac "descendants_of dest (cdt a) = {}")
                prefer 2
                apply (drule mdb_insert.dest_no_descendants)
                apply (fastforce simp add: cdt_relation_def)
               apply (subgoal_tac "mdb_insert_abs (cdt a) src dest")
                prefer 2
                apply (erule mdb_insert_abs.intro)
                 apply (rule mdb_None)
                   apply (erule(1) mdb_insert.descendants_not_dest)
                  apply assumption
                 apply assumption
                apply assumption
               apply(simp add: cdt_list_relation_def)
               apply(subgoal_tac "no_mloop (cdt a) \<and> finite_depth (cdt a)")
                prefer 2
                apply(simp add: finite_depth valid_mdb_def)
               apply(intro conjI impI allI)
                apply(simp cong: option.case_cong)
                apply(simp split: option.split)
                apply(subgoal_tac "\<forall>aa. cdt a src = Some aa \<longrightarrow> src \<noteq> aa")
                 prefer 2
                 apply(fastforce simp: no_mloop_weaken)
                apply(simp add: fun_upd_twist)
                apply(rule allI)
                apply(case_tac "next_child src (cdt_list (a))")
                 apply(frule next_child_NoneD)
                 apply(subst mdb_insert_abs.next_slot)
                     apply(simp_all)[5]
                 apply(case_tac "ca=src")
                  apply(simp)
                  apply(clarsimp simp: modify_map_def)
                  apply(fastforce split: split_if_asm)
                 apply(case_tac "ca = dest")
                  apply(simp)
                  apply(rule impI)
                  apply(clarsimp simp: modify_map_def const_def)
                  apply(simp split: split_if_asm)
                    apply(drule_tac p="cte_map src" in valid_mdbD1')
                      apply(simp)
                     apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                    apply(clarsimp)
                   apply(drule cte_map_inj_eq)
                        apply(simp_all)[6]
                  apply(erule_tac x=src in allE)+
                  apply(fastforce)
                 apply(simp)
                 apply(rule impI)
                 apply(subgoal_tac "cte_at ca a")
                  prefer 2
                  apply(rule cte_at_next_slot)
                     apply(simp_all)[4]
                 apply(clarsimp simp: modify_map_def const_def)
                 apply(simp split: split_if_asm)
                       apply(drule cte_map_inj_eq)
                            apply(simp_all)[6]
                      apply(drule_tac p="cte_map src" in valid_mdbD1')
                        apply(simp)
                       apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                      apply(clarsimp)
                     apply(clarsimp)
                     apply(case_tac z)
                     apply(erule_tac x="(aa, bb)" in allE)+
                     apply(fastforce)
                    apply(drule cte_map_inj_eq)
                         apply(simp_all)[6]
                   apply(drule cte_map_inj_eq)
                        apply(simp_all)[6]
                  apply(drule cte_map_inj_eq)
                       apply(simp_all)[6]
                 apply(erule_tac x="(aa, bb)" in allE)+
                 apply(fastforce)

                apply(frule(1) next_childD)
                apply(simp add: mdb_insert_abs.next_slot)
                apply(case_tac "ca=src")
                 apply(simp)
                 apply(clarsimp simp: modify_map_def)
                 apply(fastforce split: split_if_asm)
                apply(case_tac "ca = dest")
                 apply(simp)
                 apply(rule impI)
                 apply(clarsimp simp: modify_map_def const_def)
                 apply(simp split: split_if_asm)
                   apply(drule_tac p="cte_map src" in valid_mdbD1')
                     apply(simp)
                    apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                   apply(clarsimp)
                  apply(drule cte_map_inj_eq)
                       apply(simp_all)[6]
                 apply(erule_tac x=src in allE)+
                 apply(fastforce)
                apply(simp)
                apply(rule impI)
                apply(subgoal_tac "cte_at ca a")
                 prefer 2
                 apply(rule cte_at_next_slot)
                    apply(simp_all)[4]
                apply(clarsimp simp: modify_map_def const_def)
                apply(simp split: split_if_asm)
                      apply(drule cte_map_inj_eq)
                           apply(simp_all)[6]
                     apply(drule_tac p="cte_map src" in valid_mdbD1')
                       apply(simp)
                      apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                     apply(clarsimp)
                    apply(clarsimp)
                    apply(case_tac z)
                    apply(erule_tac x="(aa, bb)" in allE)+
                    apply(fastforce)
                   apply(drule cte_map_inj_eq)
                        apply(simp_all)[6]
                  apply(drule cte_map_inj_eq)
                       apply(simp_all)[6]
                 apply(drule cte_map_inj_eq)
                      apply(simp_all)[6]
                apply(erule_tac x="(aa, bb)" in allE)+
                apply(fastforce)

               apply(subgoal_tac "mdb_insert_sib (ctes_of b) (cte_map src) (maskedAsFull src_cap' c')
         src_node (cte_map dest) capability.NullCap dest_node c'")
                prefer 2
                apply(simp add: mdb_insert_sib_def)
                apply(rule mdb_insert_sib_axioms.intro)
                apply (subst can_be_is [symmetric])
                    apply simp
                    apply (rule cap_relation_masked_as_full)
                     apply (simp+)[3]
                  apply simp
                 apply simp
                apply simp
                apply (subst (asm) revokable_eq, assumption, assumption)
                  apply (rule derived_sameRegionAs)
                   apply (subst is_derived_eq[symmetric], assumption,
                  assumption, assumption, assumption, assumption)
                  apply assumption
                 apply (clarsimp simp: cte_wp_at_def is_derived_def is_cap_simps cap_master_cap_simps
                         dest!:cap_master_cap_eqDs)
                apply (subgoal_tac "is_original_cap a src = mdbRevocable src_node")
                 apply (frule(4) iffD1[OF is_derived_eq])
                 apply (drule_tac src_cap' = src_cap' in
                   maskedAsFull_revokable[where a = c',symmetric])
                 apply(simp)
                apply (simp add: revokable_relation_def)
                apply (erule_tac x=src in allE)+
                apply simp
                apply (erule impE)
                 apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state split: if_splits)
                 apply (clarsimp simp: masked_as_full_def is_cap_simps free_index_update_def split: if_splits)
                apply(simp)

               apply(subgoal_tac "cdt_list (a) src = []")
                prefer 2
                apply(rule ccontr)
                apply(simp add: empty_list_empty_desc)
                apply(simp add: no_children_empty_desc[symmetric])
                apply(erule exE)
                apply(drule_tac p="cte_map caa" in mdb_insert_sib.src_no_parent)
                apply(subgoal_tac "cte_map caa\<in>descendants_of' (cte_map src) (ctes_of b)")
                 apply(simp add: descendants_of'_def)
                apply(simp add: cdt_relation_def)
                apply(erule_tac x=src in allE)
                apply(drule child_descendant)+
                apply(drule_tac x=caa and f=cte_map in imageI)
                apply(simp)

               apply(case_tac "cdt a src")
                apply(simp)
                apply(subst mdb_insert_abs_sib.next_slot_no_parent')
                     apply(simp add: mdb_insert_abs_sib_def)
                    apply(simp_all add: fun_upd_idem)[5]

                apply(case_tac "ca=src")
                 apply(simp add: next_slot_def no_parent_next_not_child_None)
                apply(case_tac "ca = dest")
                 apply(simp add: next_slot_def no_parent_next_not_child_None
                         mdb_insert_abs.dest empty_list_empty_desc)
                apply(case_tac "next_slot ca (cdt_list (a)) (cdt a)")
                 apply(simp)
                apply(simp)
                apply(subgoal_tac "cte_at ca a")
                 prefer 2
                 apply(rule cte_at_next_slot)
                    apply(simp_all)[4]
                apply(clarsimp simp: modify_map_def const_def)
                apply(simp split: split_if_asm)
                      apply(drule cte_map_inj_eq)
                           apply(simp_all)[6]
                     apply(drule_tac p="cte_map src" in valid_mdbD1')
                        apply(simp)
                      apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                     apply(clarsimp)
                    apply(clarsimp)
                    apply(case_tac z)
                    apply(erule_tac x="(aa, bb)" in allE)+
                    apply(fastforce)
                   apply(drule cte_map_inj_eq)
                        apply(simp_all)[6]
                  apply(drule cte_map_inj_eq)
                       apply(simp_all)[6]
                 apply(drule cte_map_inj_eq)
                      apply(simp_all)[6]
                apply(erule_tac x="(aa, bb)" in allE)+
                apply(fastforce)

               apply(simp add: fun_upd_idem)
               apply(subst mdb_insert_abs_sib.next_slot')
                     apply(simp add: mdb_insert_abs_sib_def)
                    apply(simp_all)[5]
               apply(case_tac "ca=src")
                apply(clarsimp simp: modify_map_def)
                apply(fastforce split: split_if_asm)
               apply(case_tac "ca = dest")
                apply(simp)
                apply(case_tac "next_slot src (cdt_list (a)) (cdt a)")
                 apply(simp)
                apply(simp)
                apply(clarsimp simp: modify_map_def const_def)
                apply(simp split: split_if_asm)
                  apply(drule_tac p="cte_map src" in valid_mdbD1')
                    apply(simp)
                   apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                  apply(clarsimp)
                 apply(drule cte_map_inj_eq)
                      apply(simp_all)[6]
                apply(erule_tac x=src in allE)+
                apply(fastforce)
               apply(simp)
               apply(case_tac "next_slot ca (cdt_list (a)) (cdt a)")
                apply(simp)
               apply(simp)
               apply(subgoal_tac "cte_at ca a")
                prefer 2
                apply(rule cte_at_next_slot)
                   apply(simp_all)[4]
               apply(clarsimp simp: modify_map_def const_def)
               apply(simp split: split_if_asm)
                     apply(drule cte_map_inj_eq)
                          apply(simp_all)[6]
                    apply(drule_tac p="cte_map src" in valid_mdbD1')
                       apply(simp)
                     apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                    apply(clarsimp)
                   apply(clarsimp)
                   apply(case_tac z)
                   apply(erule_tac x="(aa, bb)" in allE)+
                   apply(fastforce)
                  apply(drule cte_map_inj_eq)
                       apply(simp_all)[6]
                 apply(drule cte_map_inj_eq)
                      apply(simp_all)[6]
                apply(drule cte_map_inj_eq)
                     apply(simp_all)[6]
               apply(erule_tac x="(aa, bb)" in allE)+
               apply(fastforce)
              apply (thin_tac "ctes_of ?t = ?t'")+
              apply (clarsimp simp: modify_map_apply)
              apply (clarsimp simp: revokable_relation_def  split: split_if)
              apply (rule conjI)
              apply clarsimp
               apply (subgoal_tac "mdbRevocable node = revokable' (cteCap srcCTE) c'")
                prefer 2
                apply (case_tac rv')
                apply (clarsimp simp add: const_def modify_map_def split: split_if_asm)
               apply simp
               apply (rule revokable_eq, assumption, assumption)
                apply (rule derived_sameRegionAs)
                 apply (drule(3) is_derived_eq[THEN iffD1,rotated -1])
                  apply (simp add: cte_wp_at_def)
                 apply assumption
                apply assumption
               apply (clarsimp simp: cap_master_cap_simps cte_wp_at_def is_derived_def is_cap_simps
                  split:if_splits dest!:cap_master_cap_eqDs)
              apply clarsimp
              apply (case_tac srcCTE)
              apply (case_tac rv')
              apply clarsimp
              apply (subgoal_tac "\<exists>cap' node'. ctes_of b (cte_map (aa,bb)) = Some (CTE cap' node')")
               prefer 2
               apply (clarsimp simp: modify_map_def split: split_if_asm)
               apply (case_tac z)
               apply clarsimp
              apply clarsimp
              apply (drule set_cap_caps_of_state_monad)+
              apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
               prefer 2
               apply (clarsimp simp: cte_wp_at_caps_of_state null_filter_def split: if_splits)

              apply clarsimp
              apply (subgoal_tac "cte_at (aa,bb) a")
               prefer 2
               apply (drule null_filter_caps_of_stateD)
               apply (erule cte_wp_at_weakenE, rule TrueI)
              apply (subgoal_tac "mdbRevocable node = mdbRevocable node'")
               apply clarsimp
              apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map dest")
               apply (clarsimp simp: modify_map_def split: split_if_asm)
              apply (erule (5) cte_map_inj)
(* FIX ME *)

             apply (rule set_untyped_cap_as_full_corres)
                   apply simp+
            apply (wp set_untyped_cap_full_valid_objs set_untyped_cap_as_full_valid_mdb
               set_untyped_cap_as_full_cte_wp_at setUntypedCapAsFull_valid_cap
               setUntypedCapAsFull_cte_wp_at | clarsimp simp: cte_wp_at_caps_of_state| wps)+
         apply (case_tac rv',clarsimp simp:cte_wp_at_ctes_of maskedAsFull_def)
        apply (wp getCTE_wp' get_cap_wp)
    apply clarsimp
    apply (fastforce elim: cte_wp_at_weakenE)
   apply (clarsimp simp: cte_wp_at'_def)
  apply (thin_tac "ctes_of ?s = ?t")+
  apply (thin_tac "pspace_relation ?s ?t")+
  apply (thin_tac "machine_state ?t = ?s")+
  apply (case_tac "srcCTE")
  apply (rename_tac src_cap' src_node)
  apply (case_tac "rv'")
  apply (rename_tac dest_node)
  apply (clarsimp simp: in_set_cap_cte_at_swp)
  apply (subgoal_tac "cte_at src a \<and> is_derived (cdt a) src c src_cap")
   prefer 2
   apply (fastforce simp: cte_wp_at_def)
  apply (erule conjE)
  apply (subgoal_tac "mdb_insert (ctes_of b) (cte_map src) (maskedAsFull src_cap' c') src_node
                                 (cte_map dest) NullCap dest_node")
   prefer 2
   apply (rule mdb_insert.intro)
     apply (rule mdb_ptr.intro)
      apply (rule vmdb.intro, simp add: valid_mdb_ctes_def)
     apply (erule mdb_ptr_axioms.intro)
    apply (rule mdb_ptr.intro)
     apply (rule vmdb.intro, simp add: valid_mdb_ctes_def)
    apply (erule mdb_ptr_axioms.intro)
   apply (rule mdb_insert_axioms.intro)
        apply (rule refl)
       apply assumption
      apply assumption
     apply assumption
    apply assumption
   apply (erule (5) cte_map_inj)
  apply (frule mdb_insert_der.intro)
   apply (rule mdb_insert_der_axioms.intro)
   apply (simp add: is_derived_eq)
  apply (simp (no_asm_simp) add: cdt_relation_def split: split_if)
  apply (subgoal_tac "descendants_of dest (cdt a) = {}")
   prefer 2
   apply (drule mdb_insert.dest_no_descendants)
   apply (fastforce simp add: cdt_relation_def simp del: split_paired_All)
  apply (subgoal_tac "mdb_insert_abs (cdt a) src dest")
   prefer 2
   apply (erule mdb_insert_abs.intro)
    apply (rule mdb_None)
      apply (erule(1) mdb_insert.descendants_not_dest)
     apply assumption
    apply assumption
   apply assumption
  apply (rule conjI)
   apply (intro impI allI)
   apply (unfold const_def)
   apply (frule(4) iffD1[OF is_derived_eq])
   apply (drule_tac src_cap' = src_cap' in
     maskedAsFull_revokable[where a = c',symmetric])
   apply simp
   apply (subst mdb_insert_child.descendants)
    apply (rule mdb_insert_child.intro)
    apply simp
    apply (rule mdb_insert_child_axioms.intro)
    apply (subst can_be_is [symmetric])
        apply simp
       apply (rule cap_relation_masked_as_full)
       apply (simp+)[3]
      apply simp
     apply simp
    apply (subst (asm) revokable_eq, assumption, assumption)
      apply (rule derived_sameRegionAs)
       apply (subst is_derived_eq[symmetric], assumption, assumption,
                    assumption, assumption, assumption)
      apply assumption
     apply (clarsimp simp: cte_wp_at_def is_derived_def is_cap_simps cap_master_cap_simps
                     dest!:cap_master_cap_eqDs)
    apply (subgoal_tac "is_original_cap a src = mdbRevocable src_node")
     prefer 2
     apply (simp add: revokable_relation_def del: split_paired_All)
     apply (erule_tac x=src in allE)
     apply (erule impE)
      apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state cap_master_cap_simps
       split: if_splits dest!:cap_master_cap_eqDs)
      apply (clarsimp simp: masked_as_full_def is_cap_simps free_index_update_def split: if_splits)
     apply simp
    apply clarsimp
   apply (subst mdb_insert_abs.descendants_child, assumption)
   apply (frule_tac p=ca in in_set_cap_cte_at)
   apply (subst descendants_of_eq')
          prefer 2
          apply assumption
         apply (simp_all)[6]
   apply (simp add: cdt_relation_def split: split_if del: split_paired_All)
   apply clarsimp
   apply (drule (5) cte_map_inj)+
   apply simp
  apply clarsimp
  apply (subst mdb_insert_abs_sib.descendants, erule mdb_insert_abs_sib.intro)
  apply (frule(4) iffD1[OF is_derived_eq])
  apply (drule_tac src_cap' = src_cap' in
    maskedAsFull_revokable[where a = c',symmetric])
  apply simp
  apply (subst mdb_insert_sib.descendants)
   apply (rule mdb_insert_sib.intro, assumption)
   apply (rule mdb_insert_sib_axioms.intro)
   apply (subst can_be_is [symmetric])
       apply simp
       apply (rule cap_relation_masked_as_full)
        apply (simp+)[3]
     apply simp
    apply simp
   apply simp
   apply (subst (asm) revokable_eq, assumption, assumption)
     apply (rule derived_sameRegionAs)
      apply (subst is_derived_eq[symmetric], assumption, assumption,
                   assumption, assumption, assumption)
     apply assumption
    apply (clarsimp simp: cte_wp_at_def is_derived_def is_cap_simps cap_master_cap_simps
                   dest!:cap_master_cap_eqDs)
   apply (subgoal_tac "is_original_cap a src = mdbRevocable src_node")
    apply simp
   apply (simp add: revokable_relation_def del: split_paired_All)
   apply (erule_tac x=src in allE)
   apply (erule impE)
    apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state split: if_splits)
    apply (clarsimp simp: masked_as_full_def is_cap_simps free_index_update_def split: if_splits)
   apply simp
  apply (simp split: split_if)
  apply (frule_tac p="(aa, bb)" in in_set_cap_cte_at)
  apply (rule conjI)
   apply (clarsimp simp: descendants_of_eq')
   apply (simp add: cdt_relation_def del: split_paired_All)
  apply (clarsimp simp: descendants_of_eq')
  apply (simp add: cdt_relation_def del: split_paired_All)
  done


declare split_if [split]

lemma updateCap_no_0:
  "\<lbrace>\<lambda>s. no_0 (ctes_of s)\<rbrace> updateCap cap ptr \<lbrace>\<lambda>_ s. no_0 (ctes_of s)\<rbrace>"
  apply (simp add: updateCap_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of no_0_def)
  done

lemma revokable_relation_prev [simp]:
  "revokable_relation revo cs (modify_map m p (cteMDBNode_update (mdbPrev_update f))) =
  revokable_relation revo cs m"
  apply (rule iffI)
   apply (clarsimp simp add: revokable_relation_def)
   apply (erule allE, erule allE, erule impE, erule exI)
   apply (clarsimp simp: modify_map_def split: split_if_asm)
  apply (clarsimp simp add: revokable_relation_def modify_map_def)
  apply (erule allE, erule allE, erule impE, erule exI)
  apply (case_tac z)
  apply auto
  done

lemma revokable_relation_next [simp]:
  "revokable_relation revo cs (modify_map m p (cteMDBNode_update (mdbNext_update f))) =
  revokable_relation revo cs m"
  apply (rule iffI)
   apply (clarsimp simp add: revokable_relation_def)
   apply (erule allE, erule allE, erule impE, erule exI)
   apply (clarsimp simp: modify_map_def split: split_if_asm)
  apply (clarsimp simp add: revokable_relation_def modify_map_def)
  apply (erule allE, erule allE, erule impE, erule exI)
  apply (case_tac z)
  apply auto
  done

lemma revokable_relation_cap [simp]:
  "revokable_relation revo cs (modify_map m p (cteCap_update f)) =
  revokable_relation revo cs m"
  apply (rule iffI)
   apply (clarsimp simp add: revokable_relation_def)
   apply (erule allE, erule allE, erule impE, erule exI)
   apply (clarsimp simp: modify_map_def split: split_if_asm)
  apply (clarsimp simp add: revokable_relation_def modify_map_def)
  apply (erule allE, erule allE, erule impE, erule exI)
  apply (case_tac z)
  apply auto
  done

lemma mdb_cap_update:
  "cteMDBNode_update f (cteCap_update f' x) =
   cteCap_update f' (cteMDBNode_update f x)"
  by (cases x) simp

lemmas modify_map_mdb_cap =
  modify_map_com [where f="cteMDBNode_update f" and
                        g="cteCap_update f'", standard,
                  OF mdb_cap_update]

lemma prev_leadstoD:
  "\<lbrakk> m \<turnstile> mdbPrev node \<leadsto> c; m p = Some (CTE cap node);
    valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow>
  c = p"
  by (fastforce simp add: next_unfold' valid_dlist_def Let_def no_0_def)

lemma pre_mdb_next_update:
  "(mdb_next (m(x \<mapsto> y)) a = Some b) =
  (if a = x then mdbNext (cteMDBNode y) = b else mdb_next m a = Some b)"
  unfolding mdb_next_def by clarsimp

lemma mdb_next_into_next_rel:
  "mdb_next m p = Some c \<Longrightarrow> m \<turnstile> p \<leadsto> c"
  unfolding mdb_next_rel_def by simp

lemma prev_leadstoI:
  "\<lbrakk> m p = Some (CTE cap node); mdbPrev node \<noteq> 0; valid_dlist m\<rbrakk>
  \<Longrightarrow> m \<turnstile> mdbPrev node \<leadsto> p"
  by (fastforce simp add: valid_dlist_def Let_def next_unfold')

lemma next_rel_into_mdb_next:
  "m \<turnstile> p \<leadsto> c \<Longrightarrow> mdb_next m p = Some c"
  unfolding mdb_next_rel_def by simp

lemma mdb_next_modify_prev:
  "modify_map m x (cteMDBNode_update (mdbPrev_update f)) \<turnstile> a \<leadsto> b = m \<turnstile> a \<leadsto> b"
  by (auto simp add: next_unfold' modify_map_def)

lemma mdb_next_modify_revocable:
  "modify_map m x (cteMDBNode_update (mdbRevocable_update f)) \<turnstile> a \<leadsto> b = m \<turnstile> a \<leadsto> b"
  by (auto simp add: next_unfold' modify_map_def)

lemma mdb_next_modify_cap:
  "modify_map m x (cteCap_update f) \<turnstile> a \<leadsto> b = m \<turnstile> a \<leadsto> b"
  by (auto simp add: next_unfold' modify_map_def)

lemmas mdb_next_modify [simp] =
  mdb_next_modify_prev
  mdb_next_modify_revocable
  mdb_next_modify_cap

lemma no_loops_lift:
  "\<lbrakk> cte_at p s;
     no_loops (tree_to_ctes s');
    cdt_relation (swp cte_at s) (cdt s) (tree_to_ctes s') \<rbrakk>
  \<Longrightarrow> cdt s \<turnstile> p cdt_parent_of\<^sup>+ p = False"
  apply (unfold no_loops_def cdt_relation_def descendants_of_def cdt_parent_defs descendants_of'_def)
  apply (erule allE, erule impE, fastforce)
  apply clarsimp
  apply (drule equalityD1)
  apply (drule subsetD)
   apply (rule rev_image_eqI)
    apply clarsimp
    apply assumption
   apply (rule refl)
  apply simp
  apply (drule subtree_mdb_next)
  apply simp
  done

lemma in_getCTE:
  "(cte, s') \<in> fst (getCTE p s) \<Longrightarrow> s' = s \<and> cte_wp_at' (op = cte) p s"
  apply (frule in_inv_by_hoareD [OF getCTE_inv])
  apply (drule use_valid [OF _ getCTE_cte_wp_at], rule TrueI)
  apply (simp add: cte_wp_at'_def)
  done

lemma isMDBParentOf_eq_parent:
  "\<lbrakk> isMDBParentOf c cte;
     weak_derived' (cteCap c) (cteCap c');
     mdbRevocable (cteMDBNode c') = mdbRevocable (cteMDBNode c) \<rbrakk>
  \<Longrightarrow> isMDBParentOf c' cte"
  apply (cases c)
  apply (cases c')
  apply (cases cte)
  apply clarsimp
  apply (clarsimp simp: weak_derived'_def isMDBParentOf_CTE)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps)
  done

lemma isMDBParentOf_eq_child:
  "\<lbrakk> isMDBParentOf cte c;
     weak_derived' (cteCap c) (cteCap c');
     mdbFirstBadged (cteMDBNode c') = mdbFirstBadged (cteMDBNode c) \<rbrakk>
  \<Longrightarrow> isMDBParentOf cte c'"
  apply (cases c)
  apply (cases c')
  apply (cases cte)
  apply clarsimp
  apply (clarsimp simp: weak_derived'_def isMDBParentOf_CTE)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps)
  done

lemma isMDBParentOf_eq:
  "\<lbrakk> isMDBParentOf c d;
     weak_derived' (cteCap c) (cteCap c');
     mdbRevocable (cteMDBNode c') = mdbRevocable (cteMDBNode c);
     weak_derived' (cteCap d) (cteCap d');
     mdbFirstBadged (cteMDBNode d') = mdbFirstBadged (cteMDBNode d) \<rbrakk>
  \<Longrightarrow> isMDBParentOf c' d'"
  apply (drule (2) isMDBParentOf_eq_parent)
  apply (erule (2) isMDBParentOf_eq_child)
  done

lemma weak_derived_refl' [intro!, simp]:
  "weak_derived' c c"
  by (simp add: weak_derived'_def)

lemma weak_derived_sym':
  "weak_derived' c d \<Longrightarrow> weak_derived' d c"
  by (clarsimp simp: weak_derived'_def isCap_simps)

locale mdb_swap =
  mdb_ptr_src: mdb_ptr m _ _ src src_cap src_node +
  mdb_ptr_dest: mdb_ptr m _ _ dest dest_cap dest_node
  for m src src_cap src_node dest dest_cap dest_node +

  assumes neq: "src \<noteq> dest"

  fixes scap dcap

  assumes src_derived: "weak_derived' src_cap scap"
  assumes dest_derived: "weak_derived' dest_cap dcap"

  fixes n'
  defines "n' \<equiv>
    modify_map
      (modify_map
        (modify_map
          (modify_map m src (cteCap_update (\<lambda>_. dcap)))
          dest
          (cteCap_update (\<lambda>_. scap)))
        (mdbPrev src_node)
        (cteMDBNode_update (mdbNext_update (\<lambda>_. dest))))
      (mdbNext src_node)
      (cteMDBNode_update (mdbPrev_update (\<lambda>_. dest)))"

  fixes dest2
  assumes dest2: "n' dest = Some dest2"

  fixes n
  defines "n \<equiv>
             (modify_map
               (modify_map
                 (modify_map
                   (modify_map n'
                    src (cteMDBNode_update (const (cteMDBNode dest2))))
                 dest (cteMDBNode_update (const src_node)))
               (mdbPrev (cteMDBNode dest2)) (cteMDBNode_update (mdbNext_update (\<lambda>_. src))))
             (mdbNext (cteMDBNode dest2)) (cteMDBNode_update (mdbPrev_update (\<lambda>_. src))))"

begin

lemma no_0_n' [intro!]: "no_0 n'" by (auto simp: n'_def)
lemma no_0_n [intro!]: "no_0 n" by (auto simp: n_def)

lemmas n_0_simps [iff] = no_0_simps [OF no_0_n]
lemmas n'_0_simps [iff] = no_0_simps [OF no_0_n']

lemmas neqs [simp] = neq neq [symmetric]

lemma src: "m src = Some (CTE src_cap src_node)" ..
lemma dest: "m dest = Some (CTE dest_cap dest_node)" ..

lemma src_prev:
  "\<lbrakk> mdbPrev src_node = p; p \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>cap node. m p = Some (CTE cap node) \<and> mdbNext node = src"
  using src
  apply -
  apply (erule dlistEp, simp)
  apply (case_tac cte')
  apply simp
  done

lemma src_next:
  "\<lbrakk> mdbNext src_node = p; p \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>cap node. m p = Some (CTE cap node) \<and> mdbPrev node = src"
  using src
  apply -
  apply (erule dlistEn, simp)
  apply (case_tac cte')
  apply simp
  done

lemma dest_prev:
  "\<lbrakk> mdbPrev dest_node = p; p \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>cap node. m p = Some (CTE cap node) \<and> mdbNext node = dest"
  using dest
  apply -
  apply (erule dlistEp, simp)
  apply (case_tac cte')
  apply simp
  done

lemma dest_next:
  "\<lbrakk> mdbNext dest_node = p; p \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>cap node. m p = Some (CTE cap node) \<and> mdbPrev node = dest"
  using dest
  apply -
  apply (erule dlistEn, simp)
  apply (case_tac cte')
  apply simp
  done

lemma next_dest_prev_src [simp]:
  "(mdbNext dest_node = src) = (mdbPrev src_node = dest)"
  apply (rule iffI)
   apply (drule dest_next, simp)
   apply (clarsimp simp: src)
  apply (drule src_prev, simp)
  apply (clarsimp simp: dest)
  done

lemmas next_dest_prev_src_sym [simp] = next_dest_prev_src [THEN x_sym]

lemma prev_dest_next_src [simp]:
  "(mdbPrev dest_node = src) = (mdbNext src_node = dest)"
  apply (rule iffI)
   apply (drule dest_prev, simp)
   apply (clarsimp simp: src)
  apply (drule src_next, simp)
  apply (clarsimp simp: dest)
  done

lemmas prev_dest_next_src_sym [simp] = prev_dest_next_src [THEN x_sym]

lemma revokable_n':
  "\<lbrakk> n' p = Some (CTE cap node) \<rbrakk> \<Longrightarrow>
   \<exists>cap' node'. m p = Some (CTE cap' node') \<and> mdbRevocable node = mdbRevocable node'"
  by (fastforce simp add: n'_def elim!: modify_map_casesE)

lemma badge_n':
  "\<lbrakk> n' p = Some (CTE cap node) \<rbrakk> \<Longrightarrow>
   \<exists>cap' node'. m p = Some (CTE cap' node') \<and> mdbFirstBadged node = mdbFirstBadged node'"
  by (fastforce simp add: n'_def elim!: modify_map_casesE)

lemma revokable:
  "n p = Some (CTE cap node) \<Longrightarrow>
  if p = src then mdbRevocable node = mdbRevocable dest_node
  else if p = dest then mdbRevocable node = mdbRevocable src_node
  else \<exists>cap' node'. m p = Some (CTE cap' node') \<and>
                    mdbRevocable node = mdbRevocable node'"
  apply (drule sym)
  apply (insert src dest dest2 [symmetric])[1]
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def const_def split: split_if_asm)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def const_def split: split_if_asm)
  apply (clarsimp simp: n_def)
  apply (clarsimp simp add: modify_map_def map_option_case split: split_if_asm option.splits)
     apply (case_tac aa, clarsimp, erule revokable_n')
    apply (case_tac a, clarsimp, erule revokable_n')
   apply (case_tac a, clarsimp, erule revokable_n')
  apply (rule revokable_n')
  apply (erule sym)
  done

lemma badge_n:
  "n p = Some (CTE cap node) \<Longrightarrow>
  if p = src then mdbFirstBadged node = mdbFirstBadged dest_node
  else if p = dest then mdbFirstBadged node = mdbFirstBadged src_node
  else \<exists>cap' node'. m p = Some (CTE cap' node') \<and>
                    mdbFirstBadged node = mdbFirstBadged node'"
  apply (drule sym)
  apply (insert src dest dest2 [symmetric])[1]
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def const_def split: split_if_asm)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def const_def split: split_if_asm)
  apply (clarsimp simp: n_def)
  apply (clarsimp simp add: modify_map_def map_option_case split: split_if_asm option.splits)
     apply (case_tac aa, clarsimp, erule badge_n')
    apply (case_tac a, clarsimp, erule badge_n')
   apply (case_tac a, clarsimp, erule badge_n')
  apply (rule badge_n')
  apply (erule sym)
  done

lemma n'_cap:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  if p = src then cap = dcap
  else if p = dest then cap = scap
  else \<exists>node'. m p = Some (CTE cap node')"
  apply clarsimp
  apply (rule conjI)
   apply (fastforce simp add: n'_def modify_map_cases)
  apply clarsimp
  apply (rule conjI)
   apply (fastforce simp add: n'_def modify_map_cases)
  apply clarsimp
  apply (simp add: n'_def modify_map_cases)
  apply fastforce
  done

lemma n_cap:
  "n p = Some (CTE cap node) \<Longrightarrow>
  if p = src then cap = dcap
  else if p = dest then cap = scap
  else \<exists>node'. m p = Some (CTE cap node')"
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (drule sym)
   apply (insert src dest dest2 [symmetric])[1]
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def split: split_if_asm)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (drule sym)
   apply (insert src dest dest2 [symmetric])[1]
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def split: split_if_asm)
  apply clarsimp
  apply (insert src dest dest2)
  apply (clarsimp simp: n_def modify_map_cases)
  apply (auto dest: n'_cap)
  done

lemma dest2_cap [simp]:
  "cteCap dest2 = scap"
  using dest2 by (cases dest2) (simp add: n'_cap)

lemma n'_next:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  if p = mdbPrev src_node then mdbNext node = dest
  else \<exists>cap' node'. m p = Some (CTE cap' node') \<and> mdbNext node = mdbNext node'"
  apply (simp add: n'_def)
  apply (rule conjI)
   apply clarsimp
   apply (simp add: modify_map_cases)
   apply clarsimp
  apply clarsimp
  apply (auto simp add: modify_map_cases)
  done

lemma dest2_next:
  "mdbNext (cteMDBNode dest2) =
  (if dest = mdbPrev src_node then dest else mdbNext dest_node)"
  using dest2 dest by (cases dest2) (clarsimp dest!: n'_next)

lemma n'_prev:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  if p = mdbNext src_node then mdbPrev node = dest
  else \<exists>cap' node'. m p = Some (CTE cap' node') \<and> mdbPrev node = mdbPrev node'"
  apply (simp add: n'_def)
  apply (rule conjI)
   apply clarsimp
   apply (simp add: modify_map_cases)
   apply clarsimp
  apply clarsimp
  apply (auto simp add: modify_map_cases)
  done

lemma dest2_prev:
  "mdbPrev (cteMDBNode dest2) =
  (if dest = mdbNext src_node then dest else mdbPrev dest_node)"
  using dest2 dest by (cases dest2) (clarsimp dest!: n'_prev)

lemma dest2_rev [simp]:
  "mdbRevocable (cteMDBNode dest2) = mdbRevocable dest_node"
  using dest2 dest by (cases dest2) (clarsimp dest!: revokable_n')

lemma dest2_bdg [simp]:
  "mdbFirstBadged (cteMDBNode dest2) = mdbFirstBadged dest_node"
  using dest2 dest by (cases dest2) (clarsimp dest!: badge_n')

definition
  "dest2_node \<equiv> MDB (if dest = mdbPrev src_node then dest else mdbNext dest_node)
                    (if dest = mdbNext src_node then dest else mdbPrev dest_node)
                    (mdbRevocable dest_node)
                    (mdbFirstBadged dest_node)"

lemma dest2_parts [simp]:
  "dest2 = CTE scap dest2_node"
  unfolding dest2_node_def
  apply (subst dest2_prev [symmetric])
  apply (subst dest2_next [symmetric])
  apply (subst dest2_rev [symmetric])
  apply (subst dest2_bdg [symmetric])
  apply (subst dest2_cap [symmetric])
  apply (cases dest2)
  apply (case_tac mdbnode)
  apply (simp del: dest2_prev dest2_cap)
  done

lemma prev_dest_src [simp]:
  "(mdbPrev dest_node = mdbPrev src_node) = (mdbPrev dest_node = 0 \<and> mdbPrev src_node = 0)"
  apply (subst mdb_ptr.p_prev_eq)
    apply (rule mdb_ptr_axioms)
   apply rule
  apply simp
  done

lemmas prev_dest_src_sym [simp] = prev_dest_src [THEN x_sym]

lemma next_dest_src [simp]:
  "(mdbNext dest_node = mdbNext src_node) = (mdbNext dest_node = 0 \<and> mdbNext src_node = 0)"
  apply (subst mdb_ptr.p_next_eq)
    apply (rule mdb_ptr_axioms)
   apply rule
  apply simp
  done

lemmas next_dest_src_sym [simp] = next_dest_src [THEN x_sym]

definition
  s_d_swp :: "word32 \<Rightarrow> word32"
where
  "s_d_swp p \<equiv> s_d_swap p src dest"

declare s_d_swp_def [simp]


lemma n_exists:
  "m p = Some (CTE cap node) \<Longrightarrow> \<exists>cap' node'. n p = Some (CTE cap' node')"
  apply (simp add: n_def n'_def)
  apply (intro modify_map_exists)
  apply simp
  done

lemma m_exists:
  "n p = Some (CTE cap node) \<Longrightarrow> \<exists>cap' node'. m p = Some (CTE cap' node')"
  apply (simp add: n_def n'_def)
  apply (drule modify_map_exists_rev, clarsimp)+
  done

lemma next_src_node [simp]:
  "(m (mdbNext src_node) = Some (CTE cap src_node)) = False"
  apply clarsimp
  apply (subgoal_tac "m \<turnstile> mdbNext src_node \<leadsto> mdbNext src_node")
   apply simp
  apply (simp add: mdb_next_unfold)
  done

lemma mdbNext_update_self [simp]:
  "(mdbNext_update (\<lambda>_. x) node = node) = (mdbNext node = x)"
  by (cases node) auto

lemmas p_next_eq_src = mdb_ptr_src.p_next_eq

lemma next_m_n:
  shows "m \<turnstile> p \<leadsto> p' = n \<turnstile> s_d_swp p \<leadsto> s_d_swp p'"
  using assms src dest
  apply (simp add: n_def n'_def modify_map_mdb_cap const_def)
  apply (simp add: s_d_swap_def)
  apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp)
    apply (clarsimp simp: mdb_next_unfold modify_map_cases dest2_node_def
                    split: split_if_asm)
   apply clarsimp
   apply (rule conjI, clarsimp)
    apply (clarsimp simp: mdb_next_unfold modify_map_cases)
    apply (auto simp add: dest2_node_def split: split_if_asm)[1]
   apply clarsimp
   apply (simp add: mdb_next_unfold modify_map_cases)
   apply (simp add: dest2_node_def const_def)
   apply (intro impI)
   apply (rule conjI, clarsimp)
   apply (rule iffI)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp)
    apply (clarsimp simp: mdb_next_unfold modify_map_cases dest2_node_def)
    apply (rule conjI)
     apply clarsimp
     apply (rule_tac x="CTE dest_cap (mdbNext_update (\<lambda>_. src) src_node)"
                     in exI)
     apply simp
     apply (rule_tac x=dest_node in exI)
     apply clarsimp
    apply clarsimp
   apply clarsimp
   apply (rule conjI, clarsimp)
    apply (clarsimp simp: mdb_next_unfold modify_map_cases dest2_node_def
                    split: split_if_asm)
   apply clarsimp
   apply (clarsimp simp: mdb_next_unfold modify_map_cases dest2_node_def)
   apply (rule conjI, clarsimp)
   apply clarsimp
   apply (rule iffI)
    apply clarsimp
    apply (rule_tac x="CTE dest_cap src_node" in exI)
    apply simp
    apply (case_tac "mdbPrev src_node = dest")
     apply clarsimp
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (simp add: mdb_next_unfold modify_map_cases dest2_node_def)
   apply (rule conjI, clarsimp)
    apply (case_tac "m p", simp)
    apply (case_tac a)
    apply (rename_tac cap node)
    apply clarsimp
    apply (frule p_next_eq_src [where p'=p])
    apply simp
    apply (case_tac "mdbNext src_node = 0", simp)
    apply simp
    apply (rule allI)
    apply (rule disjCI2)
    apply simp
    apply (erule disjE)
     apply clarsimp
    apply (rule disjCI2)
    apply (clarsimp del: notI)
    apply (rule notI)
    apply (erule dlistEn [where p=p])
     apply clarsimp
    apply clarsimp
   apply clarsimp
   apply (case_tac "m p", simp)
   apply (case_tac a)
   apply (rename_tac cap node)
   apply clarsimp
   apply (case_tac "mdbPrev dest_node = p")
    apply simp
    apply (frule dest_prev, clarsimp)
    apply (elim exE conjE)
    apply simp
    apply (case_tac "mdbNext src_node = p")
     apply fastforce
    apply fastforce
   apply (subgoal_tac "dest \<noteq> mdbNext node")
    prefer 2
    apply (rule notI)
    apply (erule dlistEn [where p=p])
     apply clarsimp
    apply clarsimp
   apply simp
   apply (rule allI)
   apply (cases "mdbNext src_node = p")
    apply simp
    apply (subgoal_tac "mdbPrev src_node \<noteq> p")
     prefer 2
     apply clarsimp
    apply simp
    apply (subgoal_tac "src \<noteq> mdbNext node")
     apply clarsimp
    apply (rule notI)
    apply (erule dlistEn [where p=p])
     apply clarsimp
    apply clarsimp
   apply simp
   apply (subgoal_tac "src \<noteq> mdbPrev node")
    prefer 2
    apply (rule notI)
    apply (erule dlistEp [where p=p])
     apply clarsimp
    apply clarsimp
   apply (rule disjCI2)
   apply simp
   apply (erule disjE)
    apply clarsimp
   apply simp
   apply (rule disjCI)
   apply simp
   apply (erule dlistEn [where p=p])
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (simp add: mdb_next_unfold modify_map_cases dest2_node_def)
   apply (case_tac "m p", simp)
   apply (case_tac a)
   apply (rename_tac cap node)
   apply simp
   apply (rule conjI)
    apply (rule impI)
    apply simp
    apply (rule iffI)
     apply simp
     apply (rule dlistEn [where p=p], assumption, clarsimp)
     apply clarsimp
    apply (elim exE conjE)
    apply (case_tac "mdbPrev src_node = p")
     apply simp
     apply (drule src_prev, clarsimp)
     apply clarsimp
    apply clarsimp
    apply (drule p_next_eq_src [where p'=p])
    apply simp
   apply clarsimp
   apply (rule iffI)
    apply simp
    apply (subgoal_tac "mdbPrev src_node = p")
     prefer 2
     apply (erule dlistEn [where p=p], clarsimp)
     apply clarsimp
    apply fastforce
   apply (elim exE conjE)
   apply simp
   apply (case_tac "mdbPrev dest_node = p")
    apply (frule dest_prev)
     apply clarsimp
    apply clarsimp
   apply simp
   apply (case_tac "mdbNext src_node = p")
    apply simp
    apply (elim exE conjE)
    apply (frule src_next, clarsimp)
    apply simp
    apply (case_tac "mdbPrev src_node = p")
     apply clarsimp
    apply (subgoal_tac "mdbNext (cteMDBNode z) = mdbNext node")
     prefer 2
     apply (case_tac nodea)
     apply (case_tac z)
     apply (case_tac mdbnode)
     apply clarsimp
    apply simp
    apply (rule dlistEn [where p=p], assumption, clarsimp)
    apply clarsimp
   apply simp
   apply (case_tac "mdbPrev src_node = p")
    apply simp
    apply (frule src_prev, clarsimp)
    apply simp
   apply simp
   apply (rule dlistEn [where p=p], assumption, clarsimp)
   apply clarsimp
  apply clarsimp
  apply (simp add: mdb_next_unfold modify_map_cases dest2_node_def)
  apply (rule conjI)
   apply (rule impI)
   apply simp
   apply (case_tac "m p", simp)
   apply (case_tac a)
   apply (rename_tac cap node)
   apply simp
   apply (case_tac "mdbPrev src_node \<noteq> p")
    apply simp
   apply simp
   apply (frule src_prev, clarsimp)
   apply simp
  apply clarsimp
  apply (case_tac "m p", simp)
  apply (case_tac a)
  apply (rename_tac cap node)
  apply simp
  apply (case_tac "mdbPrev dest_node = p")
   apply simp
   apply (frule dest_prev, clarsimp)
   apply clarsimp
  apply simp
  apply (case_tac "mdbPrev src_node = p")
   apply simp
   apply (frule src_prev, clarsimp)
   apply fastforce
  apply simp
  apply (case_tac "mdbNext src_node = p")
   apply simp
  apply simp
  done

lemma n_next:
  "n p = Some (CTE cap node) \<Longrightarrow>
  if p = dest then
    (if mdbNext src_node = dest then mdbNext node = src
    else mdbNext node = mdbNext src_node)
  else if p = src then
    (if mdbNext dest_node = src then mdbNext node = dest
    else mdbNext node = mdbNext dest_node)
  else if p = mdbPrev src_node then mdbNext node = dest
  else if p = mdbPrev dest_node then mdbNext node = src
  else \<exists>cap' node'. m p = Some (CTE cap' node') \<and> mdbNext node = mdbNext node'"
  apply (simp add: n_def del: dest2_parts split del: split_if)
  apply (simp only: dest2_next dest2_prev split del: split_if)
  apply (simp add: dest2_node_def split del: split_if)
  apply (simp add: n'_def const_def cong: if_cong split del: split_if)
  apply(case_tac "p=dest")
   apply(clarsimp simp: modify_map_cases const_def split: split_if_asm)
  apply(case_tac "p=src")
   apply(simp split del: split_if)
   apply(clarsimp simp: modify_map_cases const_def split: split_if_asm)
  apply(case_tac "p=mdbPrev src_node")
   apply(simp split del: split_if)
   apply(clarsimp simp: modify_map_cases const_def split: split_if_asm)
    apply(fastforce)
   apply(fastforce)
  apply(case_tac "p=mdbPrev dest_node")
   apply(simp split del: split_if)
   apply(clarsimp simp: modify_map_cases const_def split: split_if_asm)
   apply(fastforce)
  apply(simp split del: split_if)
  apply (clarsimp simp: modify_map_cases const_def split: split_if_asm)
    apply(fastforce)+
    done

lemma parent_of_m_n:
  "m \<turnstile> p parentOf c =
   n \<turnstile> s_d_swp p parentOf s_d_swp c"
  apply (clarsimp simp add: parentOf_def)
  apply (rule iffI)
   apply clarsimp
   apply (case_tac cte, case_tac cte')
   apply (rename_tac cap0 node0 cap1 node1)
   apply clarsimp
   apply (subgoal_tac "\<exists>cap0' node0'. n (s_d_swap c src dest) = Some (CTE cap0' node0')")
    prefer 2
    apply (simp add: s_d_swap_def)
    apply (fastforce intro: n_exists)
   apply (subgoal_tac "\<exists>cap1' node1'. n (s_d_swap p src dest) = Some (CTE cap1' node1')")
    prefer 2
    apply (simp add: s_d_swap_def)
    apply (fastforce intro: n_exists)
   apply clarsimp
   apply (insert src_derived dest_derived)[1]
   apply (erule isMDBParentOf_eq)
      apply simp
      apply (drule n_cap)+
      apply (simp add: s_d_swap_def src dest split: split_if_asm)
     apply simp
     apply (drule revokable)+
     apply (simp add: s_d_swap_def src dest split: split_if_asm)
    apply simp
    apply (drule n_cap)+
    apply (simp add: s_d_swap_def src dest split: split_if_asm)
   apply simp
   apply (drule badge_n)+
   apply (simp add: s_d_swap_def src dest split: split_if_asm)
  apply clarsimp
  apply (case_tac cte, case_tac cte')
  apply (rename_tac cap0 node0 cap1 node1)
  apply clarsimp
  apply (subgoal_tac "\<exists>cap0' node0' cap1' node1'.
                      m c = Some (CTE cap0' node0') \<and>
                      m p = Some (CTE cap1' node1')")
   prefer 2
   apply (drule m_exists)+
   apply clarsimp
   apply (simp add: s_d_swap_def src dest split: split_if_asm)
  apply clarsimp
  apply (insert src_derived dest_derived)[1]
  apply (erule isMDBParentOf_eq)
     apply simp
     apply (rule weak_derived_sym')
     apply (drule n_cap)+
     apply (simp add: s_d_swap_def src dest split: split_if_asm)
    apply simp
    apply (drule revokable)+
    apply (simp add: s_d_swap_def src dest split: split_if_asm)
   apply simp
   apply (rule weak_derived_sym')
   apply (drule n_cap)+
   apply (simp add: s_d_swap_def src dest split: split_if_asm)
  apply simp
  apply (drule badge_n)+
  apply (simp add: s_d_swap_def src dest split: split_if_asm)
  done

lemma parency_m_n:
  assumes "m \<turnstile> p \<rightarrow> p'"
  shows "n \<turnstile> s_d_swp p \<rightarrow> s_d_swp p'" using assms
proof induct
  case (direct_parent c)
  thus ?case
    apply -
    apply (rule subtree.direct_parent)
      apply (subst (asm) next_m_n, assumption)
     apply simp
    apply (subst (asm) parent_of_m_n, assumption)
    done
next
  case (trans_parent c c')
  thus ?case
    apply -
    apply (erule subtree.trans_parent)
      apply (subst (asm) next_m_n, assumption)
     apply simp
    apply (subst (asm) parent_of_m_n, assumption)
    done
qed

lemma parency_n_m:
  assumes "n \<turnstile> p \<rightarrow> p'"
  shows "m \<turnstile> s_d_swp p \<rightarrow> s_d_swp p'" using assms
proof induct
  case (direct_parent c)
  thus ?case
    apply -
    apply (rule subtree.direct_parent)
      apply (subst next_m_n, simp)
     apply simp
    apply (subst parent_of_m_n, simp)
    done
next
  case (trans_parent c c')
  thus ?case
    apply -
    apply (erule subtree.trans_parent)
      apply (subst next_m_n, simp)
     apply simp
    apply (subst parent_of_m_n, simp)
    done
qed

lemma parency:
  "n \<turnstile> p \<rightarrow> p' = m \<turnstile> s_d_swp p \<rightarrow> s_d_swp p'"
  apply (rule iffI)
   apply (erule parency_n_m)
  apply (drule parency_m_n)
  apply simp
  done

lemma descendants:
  "descendants_of' p n =
  (let swap = \<lambda>S. S - {src,dest} \<union>
                (if src \<in> S then {dest} else {}) \<union>
                (if dest \<in> S then {src} else {}) in
  swap (descendants_of' (s_d_swp p) m))"
  apply (simp add: Let_def parency descendants_of'_def s_d_swap_def)
  apply auto
  done

end

lemma inj_on_descendants_cte_map:
  "\<lbrakk> valid_mdb s;
     valid_objs s; pspace_distinct s; pspace_aligned s \<rbrakk> \<Longrightarrow>
  inj_on cte_map (descendants_of p (cdt s))"
  apply (clarsimp simp add: inj_on_def)
  apply (drule (1) descendants_of_cte_at)+
  apply (drule (5) cte_map_inj_eq)
  apply simp
  done

lemmas revokable_relation_simps [simp del] =
  revokable_relation_cap revokable_relation_next revokable_relation_prev

declare split_if [split del]

(*
lemma corres_bind_ext:
"corres_underlying srel nf rrel G G' g (g') \<Longrightarrow>
corres_underlying srel nf rrel G G' (do do_extended_op (return ()); g od) (g')"
  apply (simp add: corres_underlying_def do_extended_op_def return_def gets_def get_def put_def bind_def select_f_def modify_def mk_ef_def wrap_ext_op_det_ext_ext_def wrap_ext_op_unit_def)
  done
*)

(* consider putting in AINVS or up above cins_corres *)
lemma next_slot_eq:
  "\<lbrakk>next_slot p t' m' = x; t' = t; m' = m\<rbrakk> \<Longrightarrow> next_slot p t m = x"
  by simp

lemma cap_swap_corres:
  assumes srcdst: "src' = cte_map src" "dest' = cte_map dest"
  assumes scr: "cap_relation scap scap'"
  assumes dcr: "cap_relation dcap dcap'"
  assumes wf_caps: "wellformed_cap scap" "wellformed_cap dcap"
  notes trans_state_update'[symmetric,simp]
  shows "corres dc
         (valid_objs and pspace_aligned and pspace_distinct and
          valid_mdb and valid_list and
          (\<lambda>s. cte_wp_at (weak_derived scap) src s \<and>
               cte_wp_at (weak_derived dcap) dest s \<and>
               src \<noteq> dest \<and> (\<forall>cap. tcb_cap_valid cap src s)
                  \<and> (\<forall>cap. tcb_cap_valid cap dest s)))
         (valid_mdb' and pspace_aligned' and pspace_distinct' and
          (\<lambda>s. cte_wp_at' (weak_derived' scap' o cteCap) src' s \<and>
               cte_wp_at' (weak_derived' dcap' o cteCap) dest' s))
         (cap_swap scap src dcap dest) (cteSwap scap' src' dcap' dest')"
  (is "corres _ ?P ?P' _ _") using assms
  apply (unfold cap_swap_def cteSwap_def)
  apply (cases "src=dest")
   apply (rule corres_assume_pre)
   apply simp
  apply (rule corres_assume_pre)
  apply (subgoal_tac "cte_map src \<noteq> cte_map dest")
   prefer 2
   apply (erule cte_map_inj)
       apply (fastforce simp: cte_wp_at_def)
      apply (fastforce simp: cte_wp_at_def)
     apply simp
    apply simp
   apply simp
  apply (thin_tac "?P s")
  apply (thin_tac "?P' s'")
  apply (thin_tac "?t : state_relation")
  apply clarsimp
  apply (rule corres_symb_exec_r)
     prefer 2
     apply (rule getCTE_sp)
    defer
    apply wp
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: cte_wp_at'_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply (wp hoare_weak_lift_imp getCTE_wp' updateCap_no_0 updateCap_ctes_of_wp|
           simp add: cte_wp_at_ctes_of)+
   apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def modify_map_exists_eq)
   apply (rule conjI)
    apply clarsimp
    apply (erule (2) valid_dlistEp)
    apply simp
   apply (rule conjI)
    apply clarsimp
    apply (erule (2) valid_dlistEn)
    apply simp
   apply clarsimp
   apply (case_tac cte)
   apply (rename_tac cap node)
   apply (case_tac cte1)
   apply (rename_tac src_cap src_node)
   apply (case_tac ctea)
   apply (rename_tac dest_cap dest_node)
   apply clarsimp
   apply (rule conjI, clarsimp)
    apply (subgoal_tac "mdbPrev node = mdbNext src_node \<or>
                        mdbPrev node = mdbPrev dest_node")
     apply (erule disjE)
      apply simp
      apply (erule (1) valid_dlistEn, simp)
      apply simp
     apply (erule_tac p="cte_map dest" in valid_dlistEp, assumption, simp)
     apply simp
    apply (auto simp: modify_map_if split: split_if_asm)[1]
   apply clarsimp
   apply (subgoal_tac "mdbNext node = mdbPrev src_node \<or>
                       mdbNext node = mdbNext dest_node")
    apply (erule disjE)
     apply simp
     apply (erule (1) valid_dlistEp, simp)
     apply simp
    apply (erule_tac p="cte_map dest" in valid_dlistEn, assumption, simp)
    apply simp
   apply (auto simp: modify_map_if split: split_if_asm)[1]
  apply (clarsimp simp: corres_underlying_def in_monad
                        state_relation_def)
  apply (clarsimp simp: valid_mdb'_def)
  apply (drule(1) pspace_relationsD)
  apply (drule (12) set_cap_not_quite_corres)
      apply (erule cte_wp_at_weakenE, rule TrueI)
     apply assumption+
   apply (rule refl)
  apply (elim exE conjE)
  apply (rule bind_execI, assumption)
  apply (drule updateCap_stuff, elim conjE, erule(1) impE)
  apply (subgoal_tac "valid_objs t \<and> pspace_distinct t \<and> pspace_aligned t \<and> cte_at dest t")
   prefer 2
   apply (rule conjI)
    apply (erule use_valid, rule set_cap_valid_objs)
    apply simp
    apply (drule_tac p=dest in cte_wp_at_norm, clarsimp)
    apply (drule (1) cte_wp_valid_cap)
    apply (erule (2) weak_derived_valid_cap)
   apply (fastforce elim: use_valid [OF _ set_cap_aligned]
                         use_valid [OF _ set_cap_cte_at]
                         use_valid [OF _ set_cap_distinct]
                         cte_wp_at_weakenE)
  apply (elim conjE)
  apply (drule (14) set_cap_not_quite_corres)
       apply simp
      apply assumption+
   apply (rule refl)
  apply (elim exE conjE)
  apply (rule bind_execI, assumption)
  apply (clarsimp simp: exec_gets)
  apply (clarsimp simp: set_cdt_def bind_assoc)

  apply (clarsimp simp: set_original_def bind_assoc exec_get exec_put exec_gets modify_def cap_swap_ext_def
         update_cdt_list_def set_cdt_list_def simp del: fun_upd_apply
        | rule refl | clarsimp simp: put_def simp del: fun_upd_apply )+
  apply (simp cong: option.case_cong)
  apply (drule updateCap_stuff, elim conjE, erule(1) impE)
  apply (drule (2) updateMDB_the_lot', fastforce, fastforce, simp, clarsimp)
  apply (drule (2) updateMDB_the_lot', fastforce, fastforce, simp, clarsimp)
  apply (drule in_getCTE, clarsimp)
  apply (drule (2) updateMDB_the_lot', fastforce, fastforce, simp, clarsimp)+
  apply (thin_tac "ksMachineState ?t = ?p")+
  apply (thin_tac "ksCurThread ?t = ?p")+
  apply (thin_tac "ksReadyQueues ?t = ?p")+
  apply (thin_tac "ksSchedulerAction ?t = ?p")+
  apply (thin_tac "machine_state ?t = ?p")+
  apply (thin_tac "cur_thread ?t = ?p")+
  apply (thin_tac "ksDomScheduleIdx ?t = ?p")+
  apply (thin_tac "ksDomSchedule ?t = ?p")+
  apply (thin_tac "ksCurDomain ?t = ?p")+
  apply (thin_tac "ksDomainTime ?t = ?p")+
  apply (clarsimp simp: cte_wp_at_ctes_of in_set_cap_cte_at_swp cong: if_cong)
  apply (thin_tac "ctes_of ?x = ?y")+
  apply (case_tac cte1)
  apply (rename_tac src_cap src_node)
  apply (case_tac cte)
  apply (rename_tac dest_cap dest_node)
  apply clarsimp
  apply (subgoal_tac "mdb_swap (ctes_of b) (cte_map src) src_cap src_node
                               (cte_map dest)  dest_cap dest_node scap' dcap' cte2")
   prefer 2
   apply (rule mdb_swap.intro)
     apply (rule mdb_ptr.intro)
      apply (erule vmdb.intro)
     apply (erule mdb_ptr_axioms.intro)
    apply (rule mdb_ptr.intro)
     apply (erule vmdb.intro)
    apply (erule mdb_ptr_axioms.intro)
   apply (erule mdb_swap_axioms.intro)
     apply (erule weak_derived_sym')
    apply (erule weak_derived_sym')
   apply assumption
  apply (clarsimp simp: pspace_relations_def)
  apply (rule conjI)
   apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)
  apply(subst conj_assoc[symmetric])
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp add: revokable_relation_def in_set_cap_cte_at
                   simp del: split_paired_All)
   apply (drule set_cap_caps_of_state_monad)+
   apply (thin_tac "pspace_relation ?s ?t")+
   apply (simp del: split_paired_All split: split_if)
   apply (rule conjI)
    apply (clarsimp simp: cte_wp_at_caps_of_state simp del: split_paired_All)
    apply (drule(1) mdb_swap.revokable)
    apply (erule_tac x="dest" in allE)
    apply (erule impE)
     apply (clarsimp simp: null_filter_def weak_derived_Null split: if_splits)
    apply simp
   apply (clarsimp simp del: split_paired_All)
   apply (rule conjI)
    apply (clarsimp simp: cte_wp_at_caps_of_state simp del: split_paired_All)
    apply (drule (1) mdb_swap.revokable)
    apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map src")
     apply (simp del: split_paired_All)
     apply (erule_tac x="src" in allE)
     apply (erule impE)
      apply (clarsimp simp: null_filter_def weak_derived_Null split: if_splits)
      apply simp
    apply (drule caps_of_state_cte_at)+
    apply (erule (5) cte_map_inj)
   apply (clarsimp simp: cte_wp_at_caps_of_state simp del: split_paired_All)
   apply (drule (1) mdb_swap.revokable)
   apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
    prefer 2
    apply (clarsimp simp: null_filter_def split: if_splits)
   apply clarsimp
   apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map src")
    apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map dest")
     apply (clarsimp simp del: split_paired_All)
    apply (drule caps_of_state_cte_at)+
    apply (drule null_filter_caps_of_stateD)+
    apply (erule cte_map_inj, erule cte_wp_cte_at, assumption+)
   apply (drule caps_of_state_cte_at)+
   apply (drule null_filter_caps_of_stateD)+
   apply (erule cte_map_inj, erule cte_wp_cte_at, assumption+)
  apply (subgoal_tac "no_loops (ctes_of b)")
   prefer 2
   apply (simp add: valid_mdb_ctes_def mdb_chain_0_no_loops)
  apply (subgoal_tac "mdb_swap_abs (cdt a) src dest a")
   prefer 2
   apply (erule mdb_swap_abs.intro)
      apply (erule cte_wp_at_weakenE, rule TrueI)
     apply (erule cte_wp_at_weakenE, rule TrueI)
    apply (rule refl)
   apply assumption
  apply (frule mdb_swap_abs''.intro)
  apply (drule_tac t="cdt_list (a)" in mdb_swap_abs'.intro)
   apply (simp add: mdb_swap_abs'_axioms_def)
  apply (thin_tac "modify_map ?m ?f ?p ?p' = ?t")
  apply(rule conjI)
   apply (simp add: cdt_relation_def del: split_paired_All)
   apply (intro allI impI)
   apply (subst mdb_swap.descendants, assumption)
   apply (subst mdb_swap_abs.descendants, assumption)
   apply (simp add: mdb_swap_abs.s_d_swp_def mdb_swap.s_d_swp_def
              del: split_paired_All)
   apply (subst image_Un)+
   apply (subgoal_tac "cte_at (s_d_swap c src dest) a")
    prefer 2
    apply (simp add: s_d_swap_def split: split_if)
    apply (rule conjI, clarsimp simp: cte_wp_at_caps_of_state)
    apply (rule impI, rule conjI, clarsimp simp: cte_wp_at_caps_of_state)
    apply (fastforce dest: in_set_cap_cte_at)
   apply (subgoal_tac "s_d_swap (cte_map c) (cte_map src) (cte_map dest) =
                       cte_map (s_d_swap c src dest)")
    prefer 2
    apply (simp add: s_d_swap_def split: if_splits)
    apply (drule cte_map_inj,
           erule cte_wp_at_weakenE, rule TrueI,
           erule cte_wp_at_weakenE, rule TrueI,
           assumption+)+
    apply simp
   apply (subgoal_tac "descendants_of' (cte_map (s_d_swap c src dest)) (ctes_of b) =
                       cte_map ` descendants_of (s_d_swap c src dest) (cdt a)")
    prefer 2
    apply (simp del: split_paired_All)
   apply simp
   apply (simp split: split_if)
   apply (frule_tac p="s_d_swap c src dest" in inj_on_descendants_cte_map, assumption+)
   apply (rule conjI, clarsimp)
    apply (rule conjI, clarsimp)
     apply (subst inj_on_image_set_diff, assumption)
       apply (rule subset_refl)
      apply simp
     apply simp
    apply clarsimp
    apply (rule conjI, clarsimp)
     apply (drule cte_map_inj_eq)
          apply (erule cte_wp_at_weakenE, rule TrueI)
         apply (erule (1) descendants_of_cte_at)
        apply assumption+
     apply simp
    apply (subst insert_minus_eq, assumption)
    apply clarsimp
    apply (subst insert_minus_eq [where x="cte_map dest"], assumption)
    apply (subst inj_on_image_set_diff)
       apply (erule (3) inj_on_descendants_cte_map)
      apply (rule subset_refl)
     apply clarsimp
    apply auto[1]
   apply clarsimp
   apply (rule conjI, clarsimp)
    apply (rule conjI, clarsimp)
     apply (drule cte_map_inj_eq)
          apply (erule cte_wp_at_weakenE, rule TrueI)
         apply (erule (1) descendants_of_cte_at)
        apply assumption+
     apply simp
    apply clarsimp
    apply (subst inj_on_image_set_diff)
       apply (erule (3) inj_on_descendants_cte_map)
      apply (rule subset_refl)
     apply clarsimp
    apply simp
   apply clarsimp
   apply (rule conjI, clarsimp)
    apply (drule cte_map_inj_eq)
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply (erule (1) descendants_of_cte_at)
       apply assumption+
    apply simp
   apply clarsimp
   apply (drule cte_map_inj_eq)
        apply (erule cte_wp_at_weakenE, rule TrueI)
       apply (erule (1) descendants_of_cte_at)
      apply assumption+
   apply simp
  apply(clarsimp simp: cdt_list_relation_def)
  apply(subst next_slot_eq[OF mdb_swap_abs'.next_slot])
     apply(assumption)
    apply(fastforce split: option.split)
   apply(simp)
  apply(frule finite_depth)
  apply(frule mdb_swap.n_next)
   apply(simp)
  apply(case_tac "(aa, bb)=src")
   apply(case_tac "next_slot dest (cdt_list (a)) (cdt a) = Some src")
    apply(simp)
    apply(erule_tac x="fst dest" in allE, erule_tac x="snd dest" in allE)
    apply(simp)
   apply(simp)
   apply(case_tac "next_slot dest (cdt_list (a)) (cdt a)")
    apply(simp)
   apply(simp)
   apply(erule_tac x="fst dest" in allE, erule_tac x="snd dest" in allE)
   apply(simp)
   apply(subgoal_tac "mdbNext dest_node \<noteq> cte_map src")
    apply(simp)
   apply(simp)
   apply(rule_tac s=a in cte_map_inj)
        apply(simp)
       apply(rule cte_at_next_slot')
          apply(simp)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(erule cte_wp_at_weakenE, rule TrueI)
     apply(simp_all)[3]
  apply(case_tac "(aa, bb)=dest")
   apply(case_tac "next_slot src (cdt_list (a)) (cdt a) = Some dest")
    apply(simp)
    apply(erule_tac x="fst src" in allE, erule_tac x="snd src" in allE)
    apply(simp)
   apply(simp)
   apply(case_tac "next_slot src (cdt_list (a)) (cdt a)")
    apply(simp)
   apply(simp)
   apply(erule_tac x="fst src" in allE, erule_tac x="snd src" in allE)
   apply(simp)
   apply(subgoal_tac "mdbNext src_node \<noteq> cte_map dest")
    apply(simp)
   apply(simp)
   apply(rule_tac s=a in cte_map_inj)
        apply(simp)
       apply(rule cte_at_next_slot')
          apply(simp)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(erule cte_wp_at_weakenE, rule TrueI)
     apply(simp_all)[3]
  apply(case_tac "next_slot (aa, bb) (cdt_list (a)) (cdt a) = Some src")
   apply(simp)
   apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
   apply(simp)
   apply(subgoal_tac "cte_at (aa, bb) a")
    apply(subgoal_tac "cte_map (aa, bb) \<noteq> cte_map dest \<and>
                        cte_map (aa, bb) \<noteq> cte_map src \<and>
                        cte_map (aa, bb) = mdbPrev src_node")
     apply(clarsimp)
    apply(rule conjI)
     apply(rule cte_map_inj)
          apply(simp_all)[6]
     apply(erule cte_wp_at_weakenE, simp)
    apply(rule conjI)
     apply(rule cte_map_inj)
          apply(simp_all)[6]
     apply(erule cte_wp_at_weakenE, simp)
    apply(frule mdb_swap.m_exists)
     apply(simp)
    apply(clarsimp)
    apply(frule_tac cte="CTE cap' node'" in valid_mdbD1')
      apply(clarsimp)
     apply(simp add: valid_mdb'_def)
    apply(clarsimp)
   apply(rule cte_at_next_slot)
      apply(simp_all)[4]
  apply(case_tac "next_slot (aa, bb) (cdt_list (a)) (cdt a) = Some dest")
   apply(simp)
   apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
   apply(simp)
   apply(subgoal_tac "cte_at (aa, bb) a")
    apply(subgoal_tac "cte_map (aa, bb) \<noteq> cte_map dest \<and>
                        cte_map (aa, bb) \<noteq> cte_map src \<and>
                        cte_map (aa, bb) = mdbPrev dest_node")
     apply(subgoal_tac "cte_map (aa, bb) \<noteq> mdbPrev src_node")
      apply(clarsimp)
     apply(clarsimp simp: mdb_swap.prev_dest_src)
    apply(rule conjI)
     apply(rule cte_map_inj)
          apply(simp_all)[6]
     apply(erule cte_wp_at_weakenE, simp)
    apply(rule conjI)
     apply(rule cte_map_inj)
          apply(simp_all)[6]
     apply(erule cte_wp_at_weakenE, simp)
    apply(frule mdb_swap.m_exists)
     apply(simp)
    apply(clarsimp)
    apply(frule_tac cte="CTE cap' node'" in valid_mdbD1')
      apply(clarsimp)
     apply(simp add: valid_mdb'_def)
    apply(clarsimp)
   apply(rule cte_at_next_slot)
      apply(simp_all)[4]
  apply(simp)
  apply(case_tac "next_slot (aa, bb) (cdt_list (a)) (cdt a)")
   apply(simp)
  apply(clarsimp)
  apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
  apply(simp)
  apply(subgoal_tac "cte_at (aa, bb) a")
   apply(subgoal_tac "cte_map (aa, bb) \<noteq> cte_map dest \<and>
                      cte_map (aa, bb) \<noteq> cte_map src \<and>
                      cte_map (aa, bb) \<noteq> mdbPrev src_node \<and>
                      cte_map (aa, bb) \<noteq> mdbPrev dest_node")
    apply(clarsimp)
   apply(rule conjI)
    apply(rule cte_map_inj)
         apply(simp_all)[6]
    apply(erule cte_wp_at_weakenE, simp)
   apply(rule conjI)
    apply(rule cte_map_inj)
         apply(simp_all)[6]
    apply(erule cte_wp_at_weakenE, simp)
   apply(rule conjI)
    apply(frule mdb_swap.m_exists)
     apply(simp)
    apply(clarsimp)
     apply(frule_tac cte="CTE src_cap src_node" in valid_mdbD2')
      apply(clarsimp)
     apply(simp add: valid_mdb'_def)
    apply(clarsimp)
    apply(drule cte_map_inj_eq)
         apply(rule cte_at_next_slot')
            apply(simp_all)[4]
        apply(simp_all)[5]
    apply(erule cte_wp_at_weakenE, simp)
   apply(frule mdb_swap.m_exists)
    apply(simp)
   apply(clarsimp)
   apply(frule_tac cte="CTE dest_cap dest_node" in valid_mdbD2')
     apply(clarsimp)
    apply(simp add: valid_mdb'_def)
   apply(clarsimp)
   apply(drule cte_map_inj_eq)
         apply(rule cte_at_next_slot')
           apply(simp_all)[4]
        apply(simp_all)[5]
    apply(erule cte_wp_at_weakenE, simp)
  apply(rule cte_at_next_slot)
     apply(simp_all)
     done


lemma cap_swap_for_delete_corres:
  assumes "src' = cte_map src" "dest' = cte_map dest"
  shows "corres dc
         (valid_objs and pspace_aligned and pspace_distinct and
          valid_mdb and valid_list and cte_at src and cte_at dest
          and (\<lambda>s. \<forall>cap. tcb_cap_valid cap src s)
          and (\<lambda>s. \<forall>cap. tcb_cap_valid cap dest s))
         (valid_mdb' and pspace_distinct' and pspace_aligned')
         (cap_swap_for_delete src dest) (capSwapForDelete src' dest')"
  using assms
  apply (simp add: cap_swap_for_delete_def capSwapForDelete_def)
  apply (cases "src = dest")
   apply (clarsimp simp: when_def)
  apply (rule corres_assume_pre)
  apply clarsimp
  apply (frule_tac s=s in cte_map_inj)
       apply (simp add: caps_of_state_cte_at)+
  apply (simp add: when_def liftM_def)
  apply (rule corres_guard_imp)
    apply (rule_tac P1=wellformed_cap in corres_split [OF _ get_cap_corres_P])
      apply (rule_tac P1=wellformed_cap in corres_split [OF _ get_cap_corres_P])
        apply (rule cap_swap_corres, rule refl, rule refl, clarsimp+)
       apply (wp get_cap_wp getCTE_wp')
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (drule (1) caps_of_state_valid_cap)+
   apply (simp add: valid_cap_def2)
  apply (clarsimp simp: cte_wp_at_ctes_of)
done

declare split_if [split]
declare revokable_relation_simps [simp]

definition
  "no_child' s cte \<equiv>
  let next = mdbNext (cteMDBNode cte) in
  (next \<noteq> 0 \<longrightarrow> cte_at' next s \<longrightarrow> cte_wp_at' (\<lambda>cte'. \<not>isMDBParentOf cte cte') next s)"

definition
  "child_save' s cte' cte \<equiv>
  let cap = cteCap cte; cap' = cteCap cte' in
  sameRegionAs cap cap' \<and>
  (isEndpointCap cap \<longrightarrow> (capEPBadge cap = capEPBadge cap' \<or> no_child' s cte)) \<and>
  (isAsyncEndpointCap cap \<longrightarrow> (capAEPBadge cap = capAEPBadge cap' \<or> no_child' s cte))"

lemma subtree_no_parent:
  assumes "m \<turnstile> p \<rightarrow> x"
  assumes "mdbNext (cteMDBNode cte) \<noteq> 0"
  assumes "\<not> isMDBParentOf cte next"
  assumes "m p = Some cte"
  assumes "m (mdbNext (cteMDBNode cte)) = Some next"
  shows "False" using assms
  by induct (auto simp: parentOf_def mdb_next_unfold)

lemma ensure_no_children_corres:
  "p' = cte_map p \<Longrightarrow>
  corres (ser \<oplus> dc) (cte_at p) (pspace_aligned' and pspace_distinct' and cte_at' p' and valid_mdb')
         (ensure_no_children p) (ensureNoChildren p')"
  apply (simp add: ensureNoChildren_def ensure_no_children_descendants
                   liftE_bindE nullPointer_def)
  apply (rule corres_symb_exec_r)
     defer
     apply (rule getCTE_sp)
    apply wp
   apply (rule no_fail_pre, wp)
   apply simp
  apply clarsimp
  apply (case_tac "mdbNext (cteMDBNode cte) = 0")
   apply (simp add: whenE_def)
   apply (clarsimp simp: returnOk_def corres_underlying_def return_def)
   apply (erule notE)
   apply (clarsimp simp: state_relation_def cdt_relation_def
                   simp del: split_paired_All)
   apply (erule allE, erule (1) impE)
   apply (subgoal_tac "descendants_of' (cte_map p) (ctes_of b) = {}")
    apply simp
   apply (clarsimp simp: descendants_of'_def)
   apply (subst (asm) cte_wp_at_ctes_of)
   apply clarsimp
   apply (erule (2) subtree_next_0)
  apply (simp add: whenE_def)
  apply (rule corres_symb_exec_r)
     defer
     apply (rule getCTE_sp)
    apply wp
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def)
   apply (erule (2) valid_dlistEn)
   apply simp
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: corres_underlying_def
                         throwError_def returnOk_def return_def)
   apply (subgoal_tac "pspace_aligned' b \<and> pspace_distinct' b")
    prefer 2
    apply fastforce
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (clarsimp simp: state_relation_def cdt_relation_def
                   simp del: split_paired_All)
   apply (erule allE, erule (1) impE)
   apply (clarsimp simp: descendants_of'_def)
   apply (subgoal_tac "ctes_of b \<turnstile> cte_map p \<rightarrow> mdbNext (cteMDBNode cte)")
    apply simp
   apply (rule direct_parent)
     apply (simp add: mdb_next_unfold)
    apply assumption
   apply (simp add: parentOf_def)
  apply clarsimp
  apply (clarsimp simp: corres_underlying_def
                        throwError_def returnOk_def return_def)
  apply (subgoal_tac "pspace_aligned' b \<and> pspace_distinct' b")
   prefer 2
   apply fastforce
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: state_relation_def cdt_relation_def
                  simp del: split_paired_All)
  apply (erule allE, erule (1) impE)
  apply (subgoal_tac "descendants_of' (cte_map p) (ctes_of b) = {}")
   apply simp
  apply (clarsimp simp: descendants_of'_def)
  apply (erule (4) subtree_no_parent)
  done

lemma ensure_no_children_save':
  "\<lbrace>\<top>\<rbrace> ensureNoChildren p \<lbrace>\<lambda>_ s. cte_wp_at' (no_child' s) p s\<rbrace>, -"
  apply (simp add: ensureNoChildren_def whenE_def)
  apply (wp getCTE_wp')
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule cte_wp_at_weakenE')
   apply (clarsimp simp: no_child'_def Let_def)
   apply (erule cte_wp_at_weakenE')
   apply simp
  apply clarsimp
  apply (erule cte_wp_at_weakenE')
  apply (clarsimp simp: no_child'_def Let_def nullPointer_def)
  done

locale mdb_move =
  mdb_ptr m _ _ src src_cap src_node
    for m src src_cap src_node +

  fixes dest cap'

  fixes old_dest_node
  assumes dest: "m dest = Some (CTE NullCap old_dest_node)"
  assumes prev: "mdbPrev old_dest_node = 0"
  assumes nxt: "mdbNext old_dest_node = 0"

  assumes parency: "weak_derived' src_cap cap'"
  assumes not_null: "src_cap \<noteq> NullCap"
  assumes neq: "src \<noteq> dest"

  fixes n
  defines "n \<equiv>
    modify_map
     (modify_map
       (modify_map
         (modify_map
           (modify_map m dest (cteCap_update (\<lambda>_. cap')))
             src (cteCap_update (\<lambda>_. NullCap)))
           dest (cteMDBNode_update (\<lambda>m. src_node)))
         src (cteMDBNode_update (\<lambda>m. nullMDBNode)))
       (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (\<lambda>_. dest)))"

  fixes m'
  defines "m' \<equiv>
  modify_map n (mdbNext src_node)
               (cteMDBNode_update (mdbPrev_update (\<lambda>_. dest)))"
begin

lemmas src = m_p

lemma [intro?]:
  shows src_0: "src \<noteq> 0"
  and  dest_0: "dest \<noteq> 0"
  using no_0 src dest
  by (auto simp: no_0_def)

lemma src_prev:
  "mdbPrev src_node \<noteq> dest"
proof (cases "mdbPrev src_node = 0")
  case True thus ?thesis using dest_0 by simp
next
  case False
  with src dlist
  obtain cte' where
    "m (mdbPrev src_node) = Some cte'"
    "mdbNext (cteMDBNode cte') = src"
    by (auto elim: valid_dlistE)
  with dest nxt src_0
  show ?thesis
    apply -
    apply (rule notI)
    apply hypsubst
    apply simp
    done
qed

lemma src_neq_next [simp]:
  "src \<noteq> mdbNext src_node"
  using src no_loops by clarsimp

lemma src_neq_prev [simp]:
  "src \<noteq> mdbPrev src_node"
proof
  assume "src = mdbPrev src_node"
  with src dlist no_0
  have "src = mdbNext src_node"
    by (fastforce simp: valid_dlist_def Let_def no_0_def)
  thus False by simp
qed

lemmas src_neq_next2 [simp] = src_neq_next [symmetric]
lemmas src_neq_prev2 [simp] = src_neq_prev [symmetric]

lemma n:
  "n = modify_map (m(dest \<mapsto> CTE cap' src_node,
                     src \<mapsto> CTE capability.NullCap nullMDBNode))
                  (mdbPrev src_node)
                  (cteMDBNode_update (mdbNext_update (\<lambda>_. dest)))"
  using neq src dest no_0
  by (simp add: n_def modify_map_apply)

lemma dest_no_parent [iff]:
  "m \<turnstile> dest \<rightarrow> x = False" using dest nxt
  by (auto dest: subtree_next_0)

lemma dest_no_child [iff]:
  "m \<turnstile> x \<rightarrow> dest = False" using dest prev
  by (auto dest: subtree_prev_0)

lemma src_no_parent [iff]:
  "n \<turnstile> src \<rightarrow> x = False"
  apply clarsimp
  apply (erule subtree_next_0)
   apply (auto simp add: n modify_map_def nullPointer_def)
  done

lemma no_0_n: "no_0 n" by (simp add: n_def no_0)
lemma  no_0': "no_0 m'" by (simp add: m'_def no_0_n)

lemma next_neq_dest [simp]:
  "mdbNext src_node \<noteq> dest"
  using dlist src dest prev dest_0 no_0
  by (fastforce simp add: valid_dlist_def no_0_def Let_def)

lemma prev_neq_dest [simp]:
  "mdbPrev src_node \<noteq> dest"
  using dlist src dest nxt dest_0 no_0
  by (fastforce simp add: valid_dlist_def no_0_def Let_def)

lemmas next_neq_dest2 [simp] = next_neq_dest [symmetric]
lemmas prev_neq_dest2 [simp] = prev_neq_dest [symmetric]

lemma prev_next_0:
  "(mdbPrev src_node = mdbNext src_node) =
   (mdbPrev src_node = 0 \<and> mdbNext src_node = 0)"
proof -
  { assume "mdbPrev src_node = mdbNext src_node"
    moreover
    assume "mdbNext src_node \<noteq> 0"
    ultimately
    obtain cte where
      "m (mdbNext src_node) = Some cte"
      "mdbNext (cteMDBNode cte) = src"
      using src dlist
      by (fastforce simp add: valid_dlist_def Let_def)
    hence "m \<turnstile> src \<leadsto>\<^sup>+ src" using src
      apply -
      apply (rule trancl_trans)
       apply (rule r_into_trancl)
       apply (simp add: next_unfold')
      apply (rule r_into_trancl)
      apply (simp add: next_unfold')
      done
    with no_loops
    have False by (simp add: no_loops_def)
  }
  thus ?thesis by auto
qed

lemma next_prev_0:
  "(mdbNext src_node = mdbPrev src_node) =
   (mdbPrev src_node = 0 \<and> mdbNext src_node = 0)"
  by auto

lemma dlist':
  "valid_dlist m'"
  using src dest prev neq nxt dlist no_0
  apply (simp add: m'_def n no_0_def)
  apply (simp add: valid_dlist_def Let_def)
  apply clarsimp
  apply (case_tac cte)
  apply (rename_tac cap node)
  apply (rule conjI)
   apply (clarsimp simp: modify_map_def nullPointer_def split: split_if_asm)
      apply (case_tac z)
      apply fastforce
     apply (case_tac z)
     apply clarsimp
     apply (rule conjI)
      apply fastforce
     apply clarsimp
     apply (rule conjI, fastforce)
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (subgoal_tac "mdbNext mdbnode = mdbPrev src_node")
       prefer 2
       apply fastforce
      apply (subgoal_tac "mdbNext mdbnode = src")
       prefer 2
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (frule_tac x=src in spec, erule allE, erule (1) impE)
      apply fastforce
     apply fastforce
    apply fastforce
   apply (rule conjI, clarsimp)
    apply fastforce
   apply (clarsimp, rule conjI, fastforce)
   apply (clarsimp, rule conjI)
    apply clarsimp
    apply (frule_tac x=src in spec, erule allE, erule (1) impE)
    apply fastforce
   apply fastforce
  apply (clarsimp simp: modify_map_def nullPointer_def split: split_if_asm)
     apply (case_tac z)
     apply (clarsimp, rule conjI, fastforce)
     apply (clarsimp, rule conjI, fastforce)
     apply (clarsimp, rule conjI)
      apply clarsimp
      apply (frule_tac x=src in spec, erule allE, erule (1) impE)
      apply fastforce
     apply (clarsimp, rule conjI)
      apply clarsimp
      apply (frule_tac x=src in spec, erule allE, erule (1) impE)
      apply fastforce
     apply fastforce
    apply (case_tac z)
    apply fastforce
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: next_prev_0)
   apply fastforce
  apply clarsimp
  apply (rule conjI, fastforce)
  apply (clarsimp, rule conjI)
   apply clarsimp
   apply (frule_tac x=src in spec, erule allE, erule (1) impE)
   apply fastforce
  apply (clarsimp, rule conjI)
   apply clarsimp
   apply (frule_tac x=src in spec, erule allE, erule (1) impE)
   apply fastforce
  apply fastforce
  done

lemma src_no_child [iff]:
  "n \<turnstile> x \<rightarrow> src = False"
proof -
  from src_neq_next
  have "m' src = Some (CTE capability.NullCap nullMDBNode)"
    by (simp add: m'_def n modify_map_def)
  hence "m' \<turnstile> x \<rightarrow> src = False" using dlist' no_0'
    by (auto elim!: subtree_prev_0 simp: nullPointer_def)
  thus ?thesis by (simp add: m'_def)
qed

lemma [iff]:
  "m \<turnstile> dest parentOf c = False"
  using dest by (simp add: parentOf_def)

lemma [iff]:
  "mdbNext src_node \<noteq> dest"
proof
  assume "mdbNext src_node = dest"
  moreover have "dest \<noteq> 0" ..
  ultimately
  have "mdbPrev old_dest_node = src"
    using src dest dlist
    by (fastforce elim: valid_dlistEn)
  with prev
  show False by (simp add: src_0)
qed

lemmas no_loops_simps [simp] =
  no_loops_direct_simp [OF no_loops] no_loops_trancl_simp [OF no_loops]

lemma dest_source [iff]:
  "(m \<turnstile> dest \<leadsto> x) = (x = 0)"
  using dest nxt by (simp add: next_unfold')

lemma dest_no_target [iff]:
  "m \<turnstile> p \<leadsto> dest = False"
  using dlist no_0 prev dest
  by (fastforce simp: valid_dlist_def Let_def no_0_def next_unfold')

lemma no_src_subtree_m_n:
  assumes no_src: "\<not> m \<turnstile> p \<rightarrow> src" "p \<noteq> src"
  assumes px: "m \<turnstile> p \<rightarrow> x"
  assumes xs: "x \<noteq> src"
  shows "n \<turnstile> p \<rightarrow> x" using px xs
proof induct
  case (direct_parent c)
  thus ?case using neq no_src no_loops
    apply -
    apply (rule subtree.direct_parent)
      apply (clarsimp simp add: n mdb_next_update simp del: fun_upd_apply)
      apply (cases "m (mdbPrev src_node)")
       apply (subst modify_map_None)
        apply simp
       apply (clarsimp simp add: mdb_next_update simp del: fun_upd_apply)
      apply (subst modify_map_apply)
       apply simp
      apply (clarsimp simp add: mdb_next_update simp del: fun_upd_apply)
      apply (rule conjI)
       apply clarsimp
      apply (clarsimp)
      apply (drule prev_leadstoD)
         apply (rule src)
        apply (rule dlist)
       apply (rule no_0)
      apply simp
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None)
      apply simp
     apply (clarsimp simp add: parentOf_def n)
     apply (rule conjI)
      apply clarsimp
     apply (fastforce simp add: parentOf_def n)
    apply (subst modify_map_apply)
     apply simp
    apply (fastforce simp add: parentOf_def n)
    done
next
  case (trans_parent c c')
  thus ?case using no_src
    apply (cases "c = src")
     apply simp
    apply clarsimp
    apply (erule subtree.trans_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst modify_map_None)
        apply simp
       apply (clarsimp simp add: n mdb_next_update)
      apply (subst modify_map_apply)
       apply simp
      apply (clarsimp simp add: n mdb_next_update)
      apply (rule conjI, fastforce)
      apply clarsimp
      apply (drule prev_leadstoD)
         apply (rule src)
        apply (rule dlist)
       apply (rule no_0)
      apply simp
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (rule conjI)
      apply clarsimp
     apply (clarsimp simp: dest)
    apply (subst modify_map_apply)
     apply simp
    apply (fastforce simp: parentOf_def n)
    done
qed

lemma capMaster_isReply_eq:
  "capMasterCap c = capMasterCap c' \<Longrightarrow>
   isReplyCap c = isReplyCap c'"
  by (clarsimp simp: capMasterCap_def isCap_simps split: capability.split_asm)

lemma parent_preserved:
  "isMDBParentOf cte' (CTE cap' src_node) =
   isMDBParentOf cte' (CTE src_cap src_node)"
  using parency unfolding weak_derived'_def
  apply (cases cte')
  apply (simp add: isMDBParentOf_CTE sameRegionAs_def2)
  done

lemma children_preserved:
  "isMDBParentOf (CTE cap' src_node) cte' =
   isMDBParentOf (CTE src_cap src_node) cte'"
  using parency unfolding weak_derived'_def
  apply (cases cte')
  apply (simp add: isMDBParentOf_CTE sameRegionAs_def2)
  done

lemma no_src_subtree_n_m:
  assumes no_src: "\<not> m \<turnstile> p \<rightarrow> src" "p \<noteq> src" "p \<noteq> dest"
  assumes px: "n \<turnstile> p \<rightarrow> x"
  shows "m \<turnstile> p \<rightarrow> x" using px
proof induct
  case (direct_parent c)
  thus ?case using neq no_src no_loops
    apply -
    apply (case_tac "c=dest")
     apply (cases "m (mdbPrev src_node)")
      apply (unfold n)[1]
      apply (subst (asm) modify_map_None, simp)+
      apply (clarsimp simp: mdb_next_update)
     apply (rename_tac cte')
     apply clarsimp
     apply (subgoal_tac "p = mdbPrev src_node")
      prefer 2
      apply (simp add: n)
      apply (subst (asm) modify_map_apply, simp)
      apply (clarsimp simp:_mdb_next_update split: split_if_asm)
     apply clarsimp
     apply (simp add: n)
     apply (subst (asm) modify_map_apply, simp)+
     apply (insert dest)[1]
     apply (clarsimp simp add: parentOf_def mdb_next_unfold)
     apply (subgoal_tac "m \<turnstile> mdbPrev src_node \<rightarrow> src")
      apply simp
     apply (rule subtree.direct_parent)
       apply (rule prev_leadstoI)
         apply (rule src)
        apply (insert no_0, clarsimp simp: no_0_def)[1]
       apply (rule dlist)
      apply (rule src_0)
     apply (simp add: parentOf_def src parent_preserved)
    apply (rule subtree.direct_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst (asm) modify_map_None, simp)+
       apply (simp add: mdb_next_update)
      apply (subst (asm) modify_map_apply, simp)+
      apply (simp add: mdb_next_update split: split_if_asm)
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst (asm) modify_map_None, simp)+
     apply (clarsimp simp add: parentOf_def split: split_if_asm)
    apply (subst (asm) modify_map_apply, simp)+
    apply (clarsimp simp add: parentOf_def split: split_if_asm)
    done
next
  case (trans_parent c c')
  thus ?case using neq no_src
    apply -
    apply (case_tac "c' = dest")
     apply clarsimp
     apply (subgoal_tac "c = mdbPrev src_node")
      prefer 2
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst (asm) modify_map_None, simp)+
       apply (clarsimp simp: mdb_next_update split: split_if_asm)
      apply (subst (asm) modify_map_apply, simp)+
      apply (clarsimp simp: mdb_next_update split: split_if_asm)
     apply clarsimp
     apply (cases "m (mdbPrev src_node)")
      apply (unfold n)[1]
      apply (subst (asm) modify_map_None, simp)+
      apply (clarsimp simp: mdb_next_update)
     apply (subgoal_tac "m \<turnstile> p \<rightarrow> src")
      apply simp
     apply (rule subtree.trans_parent, assumption)
       apply (rule prev_leadstoI)
         apply (rule src)
        apply (insert no_0, clarsimp simp: no_0_def)[1]
       apply (rule dlist)
      apply (rule src_0)
     apply (clarsimp simp: n)
     apply (subst (asm) modify_map_apply, simp)+
     apply (clarsimp simp: parentOf_def src parent_preserved
                     split: split_if_asm)
    apply (rule subtree.trans_parent, assumption)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst (asm) modify_map_None, simp)+
       apply (simp add: mdb_next_update split: split_if_asm)
      apply (subst (asm) modify_map_apply, simp)+
      apply (simp add: mdb_next_update split: split_if_asm)
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst (asm) modify_map_None, simp)+
     apply (clarsimp simp: parentOf_def split: split_if_asm)
    apply (subst (asm) modify_map_apply, simp)+
    apply (clarsimp simp: parentOf_def split: split_if_asm)
    done
qed

lemma subtree_m_n:
  assumes p_neq: "p \<noteq> dest" "p \<noteq> src"
  assumes px: "m \<turnstile> p \<rightarrow> x"
  shows "if x = src then n \<turnstile> p \<rightarrow> dest else n \<turnstile> p \<rightarrow> x" using px
proof induct
  case (direct_parent c)
  thus ?case using p_neq
    apply -
    apply simp
    apply (rule conjI)
     apply clarsimp
     apply (drule leadsto_is_prev)
        apply (rule src)
       apply (rule dlist)
      apply (rule no_0)
     apply (clarsimp simp: parentOf_def)
     apply (rule subtree.direct_parent)
       apply (simp add: n modify_map_apply mdb_next_update)
      apply (rule dest_0)
     apply (clarsimp simp: n modify_map_apply parentOf_def
                           neq [symmetric] src parent_preserved)
    apply clarsimp
    apply (rule subtree.direct_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst modify_map_None, simp)
       apply (simp add: mdb_next_update)
      apply (subst modify_map_apply, simp)
      apply (clarsimp simp: mdb_next_update)
      apply (drule prev_leadstoD)
         apply (rule src)
        apply (rule dlist)
       apply (rule no_0)
      apply simp
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None, simp)
     apply (clarsimp simp add: parentOf_def)
    apply (subst modify_map_apply, simp)
    apply (clarsimp simp add: parentOf_def)
    apply fastforce
    done
next
  case (trans_parent c c')
  thus ?case using p_neq
    apply -
    apply (clarsimp split: split_if_asm)
    apply (erule subtree.trans_parent)
      apply (clarsimp simp: next_unfold' src n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst modify_map_None, simp)
       apply (clarsimp simp add: neq [symmetric] src split: option.splits)
      apply (subst modify_map_apply, simp)
      apply (clarsimp simp add: neq [symmetric] src split: option.splits)
     apply assumption
    apply (clarsimp simp: mdb_next_unfold src n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None, simp)
     apply (simp add: parentOf_def)
    apply (subst modify_map_apply, simp)
    apply (fastforce simp add: parentOf_def)
    apply (rule conjI)
     apply clarsimp
     apply (cases "m c", simp add: mdb_next_unfold)
     apply (drule leadsto_is_prev)
       apply (rule src)
      apply (rule dlist)
     apply (rule no_0)
     apply clarsimp
     apply (erule subtree.trans_parent)
       apply (simp add: n modify_map_apply mdb_next_update)
      apply (rule dest_0)
     apply (clarsimp simp: n modify_map_apply parentOf_def neq [symmetric] src)
     apply (rule conjI, clarsimp)
     apply (clarsimp simp: parent_preserved)
    apply clarsimp
    apply (erule subtree.trans_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst modify_map_None, simp)
       apply (clarsimp simp add: mdb_next_update)
      apply (subst modify_map_apply, simp)
      apply (clarsimp simp add: mdb_next_update)
      apply (rule conjI, clarsimp)
      apply clarsimp
      apply (drule prev_leadstoD, rule src, rule dlist, rule no_0)
      apply simp
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None, simp)
     apply (clarsimp simp add: parentOf_def)
    apply (subst modify_map_apply, simp)
    apply (fastforce simp add: parentOf_def)
    done
qed

lemmas neq_sym [simp] = neq [symmetric]

lemma sub_tree_loop [simp]:
  "m \<turnstile> x \<rightarrow> x = False"
  by (clarsimp dest!: subtree_mdb_next)

lemmas src_prev_loop [simp] =
  subtree_prev_loop [OF src no_loops dlist no_0]

lemma subtree_src_dest:
  "m \<turnstile> src \<rightarrow> x \<Longrightarrow> n \<turnstile> dest \<rightarrow> x"
  apply (erule subtree.induct)
   apply (clarsimp simp: mdb_next_unfold src)
   apply (rule subtree.direct_parent)
     apply (simp add: n)
     apply (cases "m (mdbPrev src_node)")
      apply (subst modify_map_None, simp)
      apply (simp add: mdb_next_update)
     apply (subst modify_map_apply, simp)
     apply (simp add: mdb_next_update)
    apply assumption
   apply (simp add: n)
   apply (clarsimp simp add: modify_map_def parentOf_def src children_preserved)
  apply (subgoal_tac "c'' \<noteq> src")
   prefer 2
   apply (drule (3) subtree.trans_parent)
   apply clarsimp
  apply (erule subtree.trans_parent)
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None, simp)
     apply (simp add: mdb_next_update)
     apply fastforce
    apply (subst modify_map_apply, simp)
    apply (simp add: mdb_next_update)
    apply fastforce
   apply assumption
  apply (fastforce simp: n modify_map_def parentOf_def src children_preserved)
  done

lemma src_next [simp]:
  "m \<turnstile> src \<leadsto> mdbNext src_node"
  by (simp add: next_unfold' src)

lemma dest_no_trancl_target [simp]:
  "m \<turnstile> x \<leadsto>\<^sup>+ dest = False"
  by (clarsimp dest!: tranclD2)

lemma m'_next:
  "\<lbrakk>m' p = Some (CTE cte' node'); m p = Some (CTE cte node)\<rbrakk>
    \<Longrightarrow> mdbNext node'
      = (if p = src then 0
         else if p = dest then mdbNext src_node
         else if mdbNext node = src then dest
         else mdbNext node)"
  apply(simp, intro conjI impI)
       apply(clarsimp simp: n m'_def modify_map_def split: split_if_asm)
      apply(clarsimp simp: n m'_def modify_map_def nullPointer_def)
     apply(subgoal_tac "mdbPrev src_node = p")
      prefer 2
      apply(erule dlistEn)
       apply(simp)
      apply(case_tac "cte'a")
      apply(clarsimp simp: src)
     apply(clarsimp simp: n m'_def modify_map_def split: split_if_asm)
    apply(clarsimp simp: dest n m'_def modify_map_def)
   apply(clarsimp simp: n m'_def modify_map_def nullPointer_def)
  apply(clarsimp simp: n m'_def modify_map_def split: split_if_asm)
  apply(insert m_p no_0)
  apply(erule_tac p=src in dlistEp)
   apply(clarsimp simp: no_0_def)
  apply(clarsimp)
  done


lemma mdb_next_from_dest:
  "n \<turnstile> dest \<leadsto>\<^sup>+ x \<Longrightarrow> m \<turnstile> src \<leadsto>\<^sup>+ x"
  apply (erule trancl_induct)
   apply (rule r_into_trancl)
   apply (simp add: n modify_map_def next_unfold' src)
  apply (cases "m (mdbPrev src_node)")
   apply (simp add: n)
   apply (subst (asm) modify_map_None, simp)+
   apply (clarsimp simp: mdb_next_update split: split_if_asm)
   apply (fastforce intro: trancl_into_trancl)
  apply (simp add: n)
  apply (subst (asm) modify_map_apply, simp)+
  apply (clarsimp simp: mdb_next_update split: split_if_asm)
   apply (subgoal_tac "m \<turnstile> src \<leadsto>\<^sup>+ src")
    apply simp
   apply (erule trancl_into_trancl)
   apply (rule prev_leadstoI, rule src)
    apply (insert no_0)[1]
    apply (clarsimp simp add: no_0_def)
   apply (rule dlist)
  apply (fastforce intro: trancl_into_trancl)
  done

lemma dest_loop:
  "n \<turnstile> dest \<rightarrow> dest = False"
  apply clarsimp
  apply (drule subtree_mdb_next)
  apply (drule mdb_next_from_dest)
  apply simp
  done


lemma subtree_dest_src:
  "n \<turnstile> dest \<rightarrow> x \<Longrightarrow> m \<turnstile> src \<rightarrow> x"
  apply (erule subtree.induct)
   apply (clarsimp simp: mdb_next_unfold src)
   apply (rule subtree.direct_parent)
     apply (simp add: n)
     apply (cases "m (mdbPrev src_node)")
      apply (subst (asm) modify_map_None, simp)+
      apply (clarsimp simp add: mdb_next_update next_unfold src)
     apply (subst (asm) modify_map_apply, simp)+
     apply (clarsimp simp add: mdb_next_update  next_unfold src)
    apply assumption
   apply (simp add: n)
   apply (simp add: modify_map_def parentOf_def)
   apply (clarsimp simp: next_prev_0 src children_preserved)
  apply (subgoal_tac "c' \<noteq> dest")
   prefer 2
   apply clarsimp
  apply (subgoal_tac "c'' \<noteq> dest")
   prefer 2
   apply clarsimp
   apply (drule (3) trans_parent)
   apply (simp add: dest_loop)
  apply (subgoal_tac "c' \<noteq> mdbPrev src_node")
   prefer 2
   apply clarsimp
  apply (erule subtree.trans_parent)
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst (asm) modify_map_None, simp)+
     apply (simp add: mdb_next_update nullPointer_def split: split_if_asm)
    apply (subst (asm) modify_map_apply, simp)+
    apply (simp add: mdb_next_update nullPointer_def split: split_if_asm)
   apply assumption
  apply (clarsimp simp add: n modify_map_def parentOf_def src children_preserved
                  split: split_if_asm)
  done

lemma subtree_n_m:
  assumes p_neq: "p \<noteq> dest" "p \<noteq> src"
  assumes px: "n \<turnstile> p \<rightarrow> x"
  shows "if x = dest then m \<turnstile> p \<rightarrow> src else m \<turnstile> p \<rightarrow> x" using px
proof induct
  case (direct_parent c)
  thus ?case using p_neq
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "p = mdbPrev src_node")
      prefer 2
      apply (drule mdb_next_modify_prev [where x="mdbNext src_node" and f="\<lambda>_. dest", THEN iffD2])
      apply (fold m'_def)
      apply (drule leadsto_is_prev)
         apply (fastforce simp: n m'_def modify_map_def)
        apply (rule dlist')
       apply (rule no_0')
      apply simp
     apply clarsimp
     apply (rule subtree.direct_parent)
       apply (rule prev_leadstoI)
         apply (rule src)
        apply (insert no_0)[1]
        apply (clarsimp simp add: next_unfold' n modify_map_def no_0_def split: split_if_asm)
       apply (rule dlist)
      apply (rule src_0)
     apply (clarsimp simp: parentOf_def n modify_map_def src parent_preserved)
    apply clarsimp
    apply (rule subtree.direct_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst (asm) modify_map_None, simp)+
       apply (simp add: next_unfold' mdb_next_unfold)
      apply (subst (asm) modify_map_apply, simp)+
      apply (simp add: mdb_next_update split: split_if_asm)
     apply assumption
    apply (simp add: n)
    apply (clarsimp simp add: parentOf_def modify_map_def split: split_if_asm)
    done
next
  case (trans_parent c c')
  thus ?case using p_neq
    apply -
    apply (simp split: split_if_asm)
     apply clarsimp
     apply (subgoal_tac "c' = mdbNext src_node")
      prefer 2
      apply (clarsimp simp add: mdb_next_unfold n modify_map_def)
     apply clarsimp
     apply (erule subtree.trans_parent)
       apply (simp add: mdb_next_unfold src)
      apply assumption
     apply (clarsimp simp add: parentOf_def modify_map_def n split: split_if_asm)
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "c = mdbPrev src_node")
      prefer 2
      apply (drule mdb_next_modify_prev [where x="mdbNext src_node" and f="\<lambda>_. dest", THEN iffD2])
      apply (fold m'_def)
      apply (drule leadsto_is_prev)
         apply (fastforce simp: n m'_def modify_map_def)
        apply (rule dlist')
       apply (rule no_0')
      apply simp
     apply clarsimp
     apply (erule subtree.trans_parent)
       apply (rule prev_leadstoI)
         apply (rule src)
        apply (insert no_0)[1]
        apply (clarsimp simp: next_unfold' no_0_def n modify_map_def)
       apply (rule dlist)
      apply (rule src_0)
     apply (clarsimp simp: parentOf_def n modify_map_def src
                           parent_preserved split: split_if_asm)
    apply clarsimp
    apply (erule subtree.trans_parent)
      apply (clarsimp simp add: n modify_map_def mdb_next_unfold nullPointer_def split: split_if_asm)
     apply assumption
    apply (clarsimp simp add: n modify_map_def parentOf_def split: split_if_asm)
    done
qed

lemma descendants:
  "descendants_of' p m' =
  (if p = src
   then {}
   else if p = dest
   then descendants_of' src m
   else descendants_of' p m - {src} \<union>
        (if src \<in> descendants_of' p m then {dest} else {}))"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def m'_def)
  apply (auto simp: subtree_m_n intro: subtree_src_dest subtree_dest_src no_src_subtree_n_m)
  apply (auto simp: subtree_n_m)
  done
end

context mdb_move_abs
begin

end

context mdb_move
begin

lemma descendants_dest:
  "descendants_of' dest m = {}"
  by (simp add: descendants_of'_def)

lemma dest_descendants:
  "dest \<notin> descendants_of' x m"
  by (simp add: descendants_of'_def)

end

lemma updateCap_dynamic_duo:
  "\<lbrakk> (rv, s') \<in> fst (updateCap x cap s); pspace_aligned' s; pspace_distinct' s \<rbrakk>
       \<Longrightarrow> pspace_aligned' s' \<and> pspace_distinct' s'"
  unfolding updateCap_def
  apply (rule conjI)
   apply (erule use_valid | wp | assumption)+
  done

declare const_apply[simp]

lemma next_slot_eq2:
  "\<lbrakk>case n q of None \<Rightarrow> next_slot p t' m' = x | Some q' \<Rightarrow> next_slot p (t'' q') (m'' q') = x;
    case n q of None \<Rightarrow> (t' = t \<and> m' = m) | Some q' \<Rightarrow> t'' q' = t \<and> m'' q' = m\<rbrakk>
    \<Longrightarrow> next_slot p t m = x"
  apply(simp split: option.splits)
  done

abbreviation "einvs \<equiv> (invs and valid_list and valid_sched)"

lemma set_cap_not_quite_corres':
  assumes cr:
  "pspace_relations (ekheap (a)) (kheap s) (ksPSpace s')"
  "ekheap (s)      = ekheap (a)"
  "cur_thread s    = ksCurThread s'"
  "idle_thread s   = ksIdleThread s'"
  "machine_state s = ksMachineState s'"
  "work_units_completed s = ksWorkUnitsCompleted s'"
  "domain_index s  = ksDomScheduleIdx s'"
  "domain_list s   = ksDomSchedule s'"
  "cur_domain s    = ksCurDomain s'"
  "domain_time s   = ksDomainTime s'"
  "(x,t') \<in> fst (updateCap p' c' s')"
  "valid_objs s" "pspace_aligned s" "pspace_distinct s" "cte_at p s"
  "pspace_aligned' s'" "pspace_distinct' s'"
  "interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s')"
  "(arch_state s, ksArchState s') \<in> arch_state_relation"
  assumes c: "cap_relation c c'"
  assumes p: "p' = cte_map p"
  shows "\<exists>t. ((),t) \<in> fst (set_cap c p s) \<and>
             pspace_relations (ekheap t) (kheap t) (ksPSpace t') \<and>
             cdt t              = cdt s \<and>
             cdt_list t         = cdt_list (s) \<and>
             ekheap t           = ekheap (s) \<and>
             scheduler_action t = scheduler_action (s) \<and>
             ready_queues t     = ready_queues (s) \<and>
             is_original_cap t  = is_original_cap s \<and>
             interrupt_state_relation (interrupt_irq_node t) (interrupt_states t)
                              (ksInterruptState t') \<and>
             (arch_state t, ksArchState t') \<in> arch_state_relation \<and>
             cur_thread t    = ksCurThread t' \<and>
             idle_thread t   = ksIdleThread t' \<and>
             machine_state t = ksMachineState t' \<and>
             work_units_completed t = ksWorkUnitsCompleted t' \<and>
             domain_index t  = ksDomScheduleIdx t' \<and>
             domain_list t   = ksDomSchedule t' \<and>
             cur_domain t    = ksCurDomain t' \<and>
             domain_time t   = ksDomainTime t'"
  apply (rule set_cap_not_quite_corres)
                using cr
                apply (fastforce simp: c p pspace_relations_def)+
                done

lemma cap_move_corres:
  assumes cr: "cap_relation cap cap'"
  notes trans_state_update'[symmetric,simp]
  shows
  "corres dc (einvs and
              cte_at ptr and
              cte_wp_at (\<lambda>c. c = cap.NullCap) ptr' and
              valid_cap cap and tcb_cap_valid cap ptr' and K (ptr \<noteq> ptr'))
             (invs' and
              cte_wp_at' (\<lambda>c. weak_derived' cap' (cteCap c) \<and> cteCap c \<noteq> NullCap) (cte_map ptr) and
              cte_wp_at' (\<lambda>c. cteCap c = NullCap) (cte_map ptr'))
          (cap_move cap ptr ptr') (cteMove cap' (cte_map ptr) (cte_map ptr'))"
  (is "corres _ ?P ?P' _ _")
  apply (simp add: cap_move_def cteMove_def const_def)
  apply (rule corres_symb_exec_r)
     defer
     apply (rule getCTE_sp)
    apply wp
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp add: cte_wp_at_ctes_of)
  apply (rule corres_assert_assume)
   prefer 2
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule corres_assert_assume)
   prefer 2
   apply clarsimp
   apply (drule invs_mdb')
   apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def)
   apply (case_tac oldCTE)
   apply (clarsimp simp: valid_nullcaps_def initMDBNode_def)
   apply (erule allE)+
   apply (erule (1) impE)
   apply (clarsimp simp: nullPointer_def)
  apply (rule corres_symb_exec_r)
     defer
     apply (rule getCTE_sp)
    apply wp
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp add: cte_wp_at_ctes_of)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp hoare_weak_lift_imp)
   apply (clarsimp simp add: cte_wp_at_ctes_of)
   apply (drule invs_mdb')
   apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def)
   apply (rule conjI)
    apply clarsimp
    apply (erule (2) valid_dlistEp, simp)
   apply clarsimp
   apply (erule (2) valid_dlistEn, simp)
  apply (clarsimp simp: in_monad state_relation_def)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac oldCTE)
  apply (rename_tac x old_dest_node)
  apply (case_tac cte)
  apply (rename_tac src_cap src_node)
  apply clarsimp
  apply (subgoal_tac "\<exists>c. caps_of_state a ptr = Some c")
   prefer 2
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply clarsimp
  apply (subgoal_tac "cap_relation c src_cap")
   prefer 2
   apply (drule caps_of_state_cteD)
   apply (drule (1) pspace_relation_ctes_ofI)
     apply fastforce
    apply fastforce
   apply fastforce
   apply (drule (1) pspace_relationsD)
   apply (drule_tac p=ptr' in set_cap_not_quite_corres, assumption+)
            apply fastforce
           apply fastforce
          apply fastforce
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply fastforce
       apply fastforce
      apply assumption
     apply fastforce
    apply (rule cr)
   apply (rule refl)
  apply (clarsimp simp: split_def)
  apply (rule bind_execI, assumption)
  apply (drule_tac p=ptr and c="cap.NullCap" in set_cap_not_quite_corres')
                 apply assumption+
            apply (frule use_valid [OF _ set_cap_valid_objs])
             apply fastforce
            apply assumption
           apply (frule use_valid [OF _ set_cap_aligned])
            apply fastforce
           apply assumption
          apply (frule use_valid [OF _ set_cap_distinct])
           apply fastforce
          apply assumption
         apply (frule use_valid [OF _ set_cap_cte_at])
          prefer 2
          apply assumption
         apply assumption
        apply (drule updateCap_stuff)
        apply (elim conjE mp, fastforce)
       apply (drule updateCap_stuff)
       apply (elim conjE mp, fastforce)
      apply assumption
     apply simp
    apply simp
   apply (rule refl)
  apply clarsimp
  apply (rule bind_execI, assumption)
  apply(subgoal_tac "mdb_move_abs ptr ptr' (cdt a) a")
  apply (frule mdb_move_abs'.intro)
   prefer 2
   apply(rule mdb_move_abs.intro)
      apply(clarsimp)
     apply(fastforce elim!: cte_wp_at_weakenE)
    apply(simp)
   apply(simp)
  apply (clarsimp simp: exec_gets exec_get exec_put set_cdt_def
                        set_original_def bind_assoc modify_def
         |(rule bind_execI[where f="cap_move_ext x y z x'",standard], clarsimp simp: mdb_move_abs'.cap_move_ext_det_def2 update_cdt_list_def set_cdt_list_def put_def) | rule refl )+
  apply (clarsimp simp: put_def)
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (frule updateCap_dynamic_duo, fastforce, fastforce)
  apply (frule(2) updateCap_dynamic_duo [OF _ conjunct1 conjunct2])
  apply (subgoal_tac "no_0 (ctes_of b)")
   prefer 2
   apply fastforce
  apply (frule(1) use_valid [OF _ updateCap_no_0])
  apply (frule(2) use_valid [OF _ updateCap_no_0, OF _ use_valid [OF _ updateCap_no_0]])
  apply (elim conjE)
  apply (drule (5) updateMDB_the_lot', elim conjE)
  apply (drule (4) updateMDB_the_lot, elim conjE)
  apply (drule (4) updateMDB_the_lot, elim conjE)
  apply (drule (4) updateMDB_the_lot, elim conjE)
  apply (drule updateCap_stuff, elim conjE, erule (1) impE)
  apply (drule updateCap_stuff, clarsimp)
  apply (subgoal_tac "pspace_distinct' b \<and> pspace_aligned' b")
   prefer 2
   apply fastforce
  apply (thin_tac "ctes_of ?t = ?s")+
  apply (thin_tac "ksMachineState ?t = ?p")+
  apply (thin_tac "ksCurThread ?t = ?p")+
  apply (thin_tac "ksIdleThread ?t = ?p")+
  apply (thin_tac "ksReadyQueues ?t = ?p")+
  apply (thin_tac "ksSchedulerAction ?t = ?p")+
  apply (subgoal_tac "\<forall>p. cte_at p ta = cte_at p a")
   prefer 2
   apply (simp add: set_cap_cte_eq)
  apply (clarsimp simp add: swp_def cte_wp_at_ctes_of simp del: split_paired_All)
  apply (subgoal_tac "cte_at ptr' a")
   prefer 2
   apply (erule cte_wp_at_weakenE, rule TrueI)
  apply (subgoal_tac "cte_map ptr \<noteq> cte_map ptr'")
   prefer 2
   apply (erule (2) cte_map_inj)
     apply fastforce
    apply fastforce
   apply fastforce
  apply (clarsimp simp: pspace_relations_def)
  apply (rule conjI)
   apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)
  apply (subst conj_assoc[symmetric])
  apply (rule conjI)
   defer
   apply (drule set_cap_caps_of_state_monad)+
   apply (simp add: modify_map_mdb_cap)
   apply (simp add: modify_map_apply)
   apply (clarsimp simp add: revokable_relation_def simp del: fun_upd_apply)
   apply simp
   apply (rule conjI)
    apply clarsimp
    apply (erule_tac x="fst ptr" in allE)
    apply (erule_tac x="snd ptr" in allE)
    apply simp
    apply (erule impE)
     apply (clarsimp simp: cte_wp_at_caps_of_state null_filter_def split: split_if_asm)
    apply simp
   apply clarsimp
   apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
    prefer 2
    apply (clarsimp simp: null_filter_def split: if_splits)
   apply clarsimp
   apply (subgoal_tac "cte_at (aa,bb) a")
    prefer 2
    apply (drule null_filter_caps_of_stateD)
    apply (erule cte_wp_cte_at)
   apply (frule_tac p="(aa,bb)" and p'="ptr'" in cte_map_inj, assumption+)
      apply fastforce
     apply fastforce
    apply fastforce
   apply (clarsimp split: split_if_asm)
   apply (subgoal_tac "(aa,bb) \<noteq> ptr")
    apply (frule_tac p="(aa,bb)" and p'="ptr" in cte_map_inj, assumption+)
       apply fastforce
      apply fastforce
     apply fastforce
    apply clarsimp
   apply (simp add: null_filter_def split: if_splits)
  apply (subgoal_tac "mdb_move (ctes_of b) (cte_map ptr) src_cap src_node (cte_map ptr') cap' old_dest_node")
   prefer 2
   apply (rule mdb_move.intro)
    apply (rule mdb_ptr.intro)
     apply (rule vmdb.intro)
     apply (simp add: valid_pspace'_def valid_mdb'_def)
    apply (erule mdb_ptr_axioms.intro)
   apply (rule mdb_move_axioms.intro)
        apply assumption
       apply (simp add: nullPointer_def)
      apply (simp add: nullPointer_def)
     apply (erule weak_derived_sym')
    apply clarsimp
   apply assumption
  apply (rule conjI)
   apply (simp (no_asm) add: cdt_relation_def)
   apply clarsimp
   apply (subst mdb_move.descendants, assumption)
   apply (subst mdb_move_abs.descendants[simplified fun_upd_apply])
    apply (rule mdb_move_abs.intro)
       apply fastforce
      apply (fastforce elim!: cte_wp_at_weakenE)
     apply simp
    apply simp
   apply (case_tac "(aa,bb) = ptr", simp)
   apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map ptr")
    prefer 2
    apply (erule (2) cte_map_inj, fastforce, fastforce, fastforce)
   apply (case_tac "(aa,bb) = ptr'")
    apply (simp add: cdt_relation_def del: split_paired_All)
   apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map ptr'")
    prefer 2
    apply (erule (2) cte_map_inj, fastforce, fastforce, fastforce)
   apply (simp only: if_False)
   apply simp
   apply (subgoal_tac "descendants_of' (cte_map (aa, bb)) (ctes_of b) =
                       cte_map ` descendants_of (aa, bb) (cdt a)")
    prefer 2
    apply (simp add: cdt_relation_def del: split_paired_All)
   apply simp
   apply (rule conjI)
    apply clarsimp
    apply (subst inj_on_image_set_diff)
       apply (rule inj_on_descendants_cte_map)
          apply fastforce
         apply fastforce
        apply fastforce
       apply fastforce
      apply (rule subset_refl)
     apply simp
    apply simp
   apply clarsimp
   apply (drule (1) cte_map_inj_eq)
       apply (erule descendants_of_cte_at)
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply clarsimp
  apply(clarsimp simp: cdt_list_relation_def)

  apply(subst next_slot_eq2)
    apply(simp split: option.splits)
    apply(intro conjI impI)
     apply(rule mdb_move_abs'.next_slot_no_parent)
       apply(simp, fastforce, simp)
    apply(intro allI impI)
    apply(rule mdb_move_abs'.next_slot)
      apply(simp, fastforce, simp)
   apply(fastforce split: option.splits)
  apply(case_tac "ctes_of b (cte_map (aa, bb))")
   apply(clarsimp simp: modify_map_def split: split_if_asm)
  apply(case_tac ab)
  apply(frule mdb_move.m'_next)
    apply(simp, fastforce)
  apply(case_tac "(aa, bb) = ptr")
   apply(simp)
  apply(case_tac "(aa, bb) = ptr'")
   apply(case_tac "next_slot ptr (cdt_list (a)) (cdt a)")
    apply(simp)
   apply(simp)
   apply(erule_tac x="fst ptr" in allE)
   apply(erule_tac x="snd ptr" in allE)
   apply(clarsimp split: split_if_asm)
  apply(frule invs_mdb, frule invs_valid_pspace)
  apply(frule finite_depth)
  apply simp
  apply(case_tac "next_slot (aa, bb) (cdt_list (a)) (cdt a) = Some ptr")
   apply(frule(3) cte_at_next_slot)
   apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
   apply(clarsimp simp: cte_map_inj_eq valid_pspace_def split: split_if_asm)
  apply(simp)
  apply(case_tac "next_slot (aa, bb) (cdt_list (a)) (cdt a)")
   apply(simp)
  apply(frule(3) cte_at_next_slot)
  apply(frule(3) cte_at_next_slot')
  apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
  apply(clarsimp simp: cte_map_inj_eq valid_pspace_def split: split_if_asm)
  done

lemmas cur_tcb_lift =
  hoare_lift_Pf [where f = ksCurThread and P = tcb_at', folded cur_tcb'_def]

lemma valid_queues_lift:
  assumes tat1: "\<And>d p tcb. \<lbrace>obj_at' (inQ d p) tcb\<rbrace> f \<lbrace>\<lambda>_. obj_at' (inQ d p) tcb\<rbrace>"
  and     tat2: "\<And>p tcb. \<lbrace>st_tcb_at' runnable' tcb\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at' runnable' tcb\<rbrace>"
  and     prq: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  shows   "\<lbrace>Invariants_H.valid_queues\<rbrace> f \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  proof -
    have tat:  "\<And>d p tcb. \<lbrace>obj_at' (inQ d p) tcb and st_tcb_at' runnable' tcb\<rbrace> f
                         \<lbrace>\<lambda>_. obj_at' (inQ d p) tcb and st_tcb_at' runnable' tcb\<rbrace>"
      apply (rule hoare_chain [OF hoare_vcg_conj_lift [OF tat1 tat2]])
       apply (fastforce)+
       done
    have tat_combined: "\<And>d p tcb. \<lbrace>obj_at' (inQ d p and runnable' \<circ> tcbState) tcb\<rbrace> f
                         \<lbrace>\<lambda>_. obj_at' (inQ d p and runnable' \<circ> tcbState) tcb\<rbrace>"
      apply (rule hoare_chain [OF tat])
       apply (fastforce simp add: obj_at'_and st_tcb_at'_def)+
      done
    show ?thesis
      apply (clarsimp simp: Invariants_H.valid_queues_def)
      apply (wp tat_combined prq hoare_vcg_all_lift hoare_vcg_conj_lift hoare_Ball_helper)
      done
  qed

lemma valid_queues_lift':
  assumes tat: "\<And>d p tcb. \<lbrace>\<lambda>s. \<not> obj_at' (inQ d p) tcb s\<rbrace> f \<lbrace>\<lambda>_ s. \<not> obj_at' (inQ d p) tcb s\<rbrace>"
  and     prq: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  shows   "\<lbrace>valid_queues'\<rbrace> f \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp only: valid_queues'_def imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
            tat prq)
  done

lemma setCTE_norq [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setCTE ptr cte \<lbrace>\<lambda>r s. P (ksReadyQueues s) \<rbrace>"
  by (clarsimp simp: valid_def dest!: setCTE_pspace_only)

crunch nosch[wp]: cteInsert "\<lambda>s. P (ksSchedulerAction s)"
  (wp: updateObject_cte_inv hoare_drop_imps)

crunch norq[wp]: cteInsert "\<lambda>s. P (ksReadyQueues s)"
  (wp: updateObject_cte_inv hoare_drop_imps)

crunch typ_at'[wp]: cteInsert "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_drop_imps setCTE_typ_at')

lemmas updateMDB_typ_ats [wp] = typ_at_lifts [OF updateMDB_typ_at']
lemmas updateCap_typ_ats [wp] = typ_at_lifts [OF updateCap_typ_at']
lemmas cteInsert_typ_ats [wp] = typ_at_lifts [OF cteInsert_typ_at']

lemma setObject_cte_ct:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject t (v::cte) \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  by (clarsimp simp: valid_def setCTE_def[symmetric] dest!: setCTE_pspace_only)

crunch ct[wp]: cteInsert "\<lambda>s. P (ksCurThread s)"
  (wp: setObject_cte_ct hoare_drop_imps ignore: setObject)

context mdb_insert
begin

lemma n_src_dest:
  "n \<turnstile> src \<leadsto> dest"
  by (simp add: n_direct_eq)

lemma dest_chain_0 [simp, intro!]:
  "n \<turnstile> dest \<leadsto>\<^sup>+ 0"
  using chain_n n_dest
  by (simp add: mdb_chain_0_def) blast

lemma m_tranclD:
  "m \<turnstile> p \<leadsto>\<^sup>+ p' \<Longrightarrow> p' \<noteq> dest \<and> (p = dest \<longrightarrow> p' = 0) \<and> n \<turnstile> p \<leadsto>\<^sup>+ p'"
  apply (erule trancl_induct)
   apply (rule context_conjI, clarsimp)
   apply (rule context_conjI, clarsimp)
   apply (cases "p = src")
    apply simp
    apply (rule trancl_trans)
     apply (rule r_into_trancl)
     apply (rule n_src_dest)
    apply (rule r_into_trancl)
    apply (simp add: n_direct_eq)
   apply (cases "p = dest", simp)
   apply (rule r_into_trancl)
   apply (simp add: n_direct_eq)
  apply clarsimp
  apply (rule context_conjI, clarsimp)
  apply (rule context_conjI, clarsimp simp: mdb_next_unfold)
  apply (case_tac "y = src")
   apply clarsimp
   apply (erule trancl_trans)
   apply (rule trancl_trans)
    apply (rule r_into_trancl)
    apply (rule n_src_dest)
   apply (rule r_into_trancl)
   apply (simp add: n_direct_eq)
  apply (case_tac "y = dest", simp)
  apply (erule trancl_trans)
  apply (rule r_into_trancl)
  apply (simp add: n_direct_eq)
  done

lemma n_trancl_eq':
  "n \<turnstile> p \<leadsto>\<^sup>+ p' =
  (if p' = dest then m \<turnstile> p \<leadsto>\<^sup>* src
   else if p = dest then m \<turnstile> src \<leadsto>\<^sup>+ p'
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  apply (rule iffI)
   apply (erule trancl_induct)
    apply (clarsimp simp: n_direct_eq)
    apply (fastforce split: split_if_asm)
   apply (clarsimp simp: n_direct_eq split: split_if_asm)
      apply fastforce
     apply fastforce
    apply (fastforce intro: trancl_trans)
   apply (fastforce intro: trancl_trans)
  apply (simp split: split_if_asm)
    apply (drule rtranclD)
    apply (erule disjE)
     apply (fastforce intro: n_src_dest)
    apply (clarsimp dest!: m_tranclD)
    apply (erule trancl_trans)
    apply (fastforce intro: n_src_dest)
   apply (drule m_tranclD, clarsimp)
   apply (drule tranclD)
   apply clarsimp
   apply (insert n_src_dest)[1]
   apply (drule (1) next_single_value)
   apply (clarsimp simp: rtrancl_eq_or_trancl)
  apply (drule m_tranclD)
  apply clarsimp
  done

lemma n_trancl_eq:
  "n \<turnstile> p \<leadsto>\<^sup>+ p' =
  (if p' = dest then p = src \<or> m \<turnstile> p \<leadsto>\<^sup>+ src
   else if p = dest then m \<turnstile> src \<leadsto>\<^sup>+ p'
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  by (auto simp add: n_trancl_eq' rtrancl_eq_or_trancl)

lemma n_rtrancl_eq:
  "n \<turnstile> p \<leadsto>\<^sup>* p' =
  (if p' = dest then p = dest \<or> p \<noteq> dest \<and> m \<turnstile> p \<leadsto>\<^sup>* src
   else if p = dest then p' \<noteq> src \<and> m \<turnstile> src \<leadsto>\<^sup>* p'
   else m \<turnstile> p \<leadsto>\<^sup>* p')"
  by (auto simp: n_trancl_eq rtrancl_eq_or_trancl)


lemma n_cap:
  "n p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then cap = c' \<and> m p = Some (CTE dest_cap node')
          else m p = Some (CTE cap node')"
  by (simp add: n src dest new_src_def new_dest_def split: split_if_asm)

lemma m_cap:
  "m p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then cap = dest_cap \<and> n p = Some (CTE c' node')
          else n p = Some (CTE cap node')"
  apply (simp add: n new_src_def new_dest_def)
  apply (cases "p=dest")
   apply (auto simp: src dest)
  done

lemma chunked_m:
  "mdb_chunked m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma derived_region1 [simp]:
  "badge_derived' c' src_cap \<Longrightarrow>
  sameRegionAs c' cap = sameRegionAs src_cap cap"
  by (clarsimp simp add: badge_derived'_def sameRegionAs_def2)

lemma derived_region2 [simp]:
  "badge_derived' c' src_cap \<Longrightarrow>
  sameRegionAs cap c' = sameRegionAs cap src_cap"
  by (clarsimp simp add: badge_derived'_def sameRegionAs_def2)

lemma chunked_n:
  assumes b: "badge_derived' c' src_cap"
  shows "mdb_chunked n"
  using chunked_m src b
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule n_cap)+
  apply clarsimp
  apply (simp split: split_if_asm)
    apply clarsimp
    apply (erule_tac x=src in allE)
    apply (erule_tac x=p' in allE)
    apply simp
    apply (case_tac "src=p'")
     apply (clarsimp simp: n_trancl_eq)
     apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
     apply (drule (1) trancl_rtrancl_trancl)
     apply simp
    apply (clarsimp simp: n_trancl_eq)
    apply (rule conjI)
     apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq)
     apply (erule_tac x=p'' in allE)
     apply clarsimp
     apply (drule_tac p=p'' in m_cap)
     apply (clarsimp split: split_if_asm)
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (rule conjI)
     apply clarsimp
     apply (erule_tac x=src in allE)
     apply simp
    apply clarsimp
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap)
    apply (clarsimp split: split_if_asm)
   apply (clarsimp simp: n_trancl_eq)
   apply (case_tac "p=src")
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (drule (1) trancl_rtrancl_trancl)
    apply simp
   apply simp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=src in allE)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap)
    apply clarsimp
   apply clarsimp
   apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap)
   apply clarsimp
  apply (clarsimp simp: n_trancl_eq)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (simp add: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (erule sameRegionAsE, simp_all add: sameRegionAs_def3)[1]
       apply blast
      apply blast
     apply (clarsimp simp: isCap_simps)
    apply fastforce
   apply clarsimp
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap)
   apply clarsimp
  apply clarsimp
  apply (simp add: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (erule_tac x=p in allE, simp, erule(1) sameRegionAs_trans)
   apply fastforce
  apply clarsimp
  apply (erule_tac x=p'' in allE)
  apply clarsimp
  apply (drule_tac p=p'' in m_cap)
  apply clarsimp
  done

end

context mdb_insert_der
begin

lemma untyped_c':
  "untypedRange c' = untypedRange src_cap"
  "isUntypedCap c' = isUntypedCap src_cap"
  using partial_is_derived'
  apply -
   apply (case_tac "isUntypedCap src_cap")
     apply (clarsimp simp:isCap_simps freeIndex_update_def is_derived'_def
       badge_derived'_def capMasterCap_def split:if_splits capability.splits)+
  done

lemma capRange_c':
  "capRange c' = capRange src_cap"
  using partial_is_derived' untyped_c'
  apply -
  apply (case_tac "isUntypedCap src_cap")
   apply (clarsimp simp:untypedCapRange)
  apply (rule master_eqI, rule capRange_Master)
  apply simp
  apply (rule arg_cong)
  apply (auto simp:isCap_simps freeIndex_update_def is_derived'_def
       badge_derived'_def capMasterCap_def split:if_splits capability.splits)
  done

lemma untyped_no_parent:
  "isUntypedCap src_cap \<Longrightarrow> \<not> m \<turnstile> src \<rightarrow> p"
  using partial_is_derived' untyped_c'
  by (clarsimp simp: is_derived'_def isCap_simps freeIndex_update_def descendants_of'_def)

end

lemma (in mdb_insert) n_revocable:
  "n p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then mdbRevocable node = revokable' src_cap c'
          else mdbRevocable node = mdbRevocable node' \<and> m p = Some (CTE cap node')"
  using src dest
  by (clarsimp simp: n new_src_def new_dest_def split: split_if_asm)

lemma (in mdb_insert_der) irq_control_n:
  "irq_control n"
  using src dest partial_is_derived'
  apply (clarsimp simp: irq_control_def)
  apply (frule n_cap)
  apply (drule n_revocable)
  apply (clarsimp split: split_if_asm)
   apply (simp add: is_derived'_def isCap_simps)
  apply (frule irq_revocable, rule irq_control)
  apply clarsimp
  apply (drule n_cap)
  apply (clarsimp split: split_if_asm)
  apply (erule disjE)
   apply (clarsimp simp: is_derived'_def isCap_simps)
  apply (erule (1) irq_controlD, rule irq_control)
  done

context mdb_insert_child
begin

lemma untyped_mdb_n:
  shows "untyped_mdb' n"
  using untyped_mdb
  apply (clarsimp simp add: untyped_mdb'_def descendants split del: split_if)
  apply (drule n_cap)+
  apply (clarsimp split: split_if_asm)
   apply (erule disjE, clarsimp)
   apply (simp add: descendants_of'_def)
   apply (erule_tac x=p in allE)
   apply (erule_tac x=src in allE)
   apply (simp add: src untyped_c' capRange_c')
  apply (erule disjE)
   apply clarsimp
   apply (simp add: descendants_of'_def untyped_c')
   apply (erule_tac x=src in allE)
   apply (erule_tac x=p' in allE)
   apply (fastforce simp: src dest: untyped_no_parent)
  apply (case_tac "p=src", simp)
  apply simp
  done

lemma parent_untyped_must_not_usable:
  "\<lbrakk>ptr \<noteq> src; m ptr = Some (CTE ccap node');
    untypedRange ccap = untypedRange src_cap; capAligned src_cap;
    isUntypedCap src_cap \<rbrakk>
   \<Longrightarrow> usableUntypedRange ccap = {}"
  using untyped_inc src
  apply (clarsimp simp:untyped_inc'_def)
  apply (erule_tac x = ptr in allE)
  apply (erule_tac x = src in allE)
  apply clarsimp
  apply (subgoal_tac "isUntypedCap ccap")
   apply clarsimp
   apply (drule_tac p = ptr in untyped_no_parent)
   apply (simp add:descendants_of'_def)
  apply (drule (1) aligned_untypedRange_non_empty)
  apply (case_tac ccap,simp_all add:isCap_simps)
  done

lemma untyped_inc_n:
  "\<lbrakk>capAligned src_cap;isUntypedCap src_cap \<longrightarrow> usableUntypedRange src_cap = {}\<rbrakk>
   \<Longrightarrow> untyped_inc' n"
  using untyped_inc
  apply (clarsimp simp add: untyped_inc'_def descendants split del: split_if)
  apply (drule n_cap)+
  apply (clarsimp split: split_if_asm)
   apply (case_tac "p=dest", simp)
   apply (simp add: descendants_of'_def untyped_c')
   apply (erule_tac x=p in allE)
   apply (erule_tac x=src in allE)
   apply (simp add: src)
   apply (frule_tac p=p in untyped_no_parent)
   apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (case_tac "p = src")
     using src
     apply clarsimp
    apply (drule(4) parent_untyped_must_not_usable)
    apply simp
   apply (intro conjI)
      apply clarsimp
     apply clarsimp
     using src
     apply clarsimp
    apply clarsimp
  apply (case_tac "p=dest")
   apply (simp add: descendants_of'_def untyped_c')
   apply (erule_tac x=p' in allE)
   apply (erule_tac x=src in allE)
     apply (clarsimp simp:src)
  apply (frule_tac p=p' in untyped_no_parent)
   apply (case_tac "p' = src")
    apply (clarsimp simp:src)
   apply (elim disjE)
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply simp+
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply simp+
   apply (clarsimp simp:Int_ac)
  apply (erule_tac x=p' in allE)
   apply (erule_tac x=p in allE)
  apply (case_tac "p' = src")
    apply (clarsimp simp:src descendants_of'_def untyped_c')
   apply (elim disjE)
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply (simp,intro conjI,clarsimp+)
     apply (intro conjI)
       apply clarsimp+
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply (simp,intro conjI,clarsimp+)
     apply (intro conjI)
       apply clarsimp+
   apply (clarsimp simp:Int_ac,intro conjI,clarsimp+)
  apply (clarsimp simp:descendants_of'_def)
  apply (case_tac "p = src")
   apply simp
   apply (elim disjE)
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply (simp,intro conjI,clarsimp+)
     apply (intro conjI)
       apply clarsimp+
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply clarsimp+
     apply fastforce
   apply (clarsimp simp:Int_ac,intro conjI,clarsimp+)
  apply (intro conjI)
   apply (elim disjE)
    apply (simp add:Int_ac)+
  apply clarsimp
  done

end

context mdb_insert_sib
begin

lemma untyped_mdb_n:
  shows "untyped_mdb' n"
  using untyped_mdb
  apply (clarsimp simp add: untyped_mdb'_def descendants split del: split_if)
  apply (drule n_cap)+
  apply (clarsimp split: split_if_asm simp: descendants_of'_def capRange_c' untyped_c')
   apply (erule_tac x=src in allE)
   apply (erule_tac x=p' in allE)
   apply (fastforce simp: src dest: untyped_no_parent)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=src in allE)
  apply (simp add: src)
  done

lemma not_untyped: "capAligned c' \<Longrightarrow> \<not>isUntypedCap src_cap"
  using no_child partial_is_derived' ut_rev src
  apply (clarsimp simp: ut_revocable'_def isMDBParentOf_CTE)
  apply (erule_tac x=src in allE)
  apply simp
  apply (clarsimp simp: is_derived'_def freeIndex_update_def isCap_simps capAligned_def
                        badge_derived'_def)
  apply (clarsimp simp: sameRegionAs_def3 capMasterCap_def isCap_simps interval_empty
                        is_aligned_no_overflow split:capability.splits)
  done

lemma untyped_inc_n:
  assumes c': "capAligned c'"
  shows "untyped_inc' n"
  using untyped_inc not_untyped [OF c']
  apply (clarsimp simp add: untyped_inc'_def descendants split del: split_if)
  apply (drule n_cap)+
  apply (clarsimp split: split_if_asm)
   apply (simp add: descendants_of'_def untyped_c')
  apply (case_tac "p = dest")
   apply (clarsimp simp: untyped_c')
  apply simp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply simp
  done

end

lemma trancl_prev_update:
  "modify_map m ptr (cteMDBNode_update (mdbPrev_update z)) \<turnstile> x \<leadsto>\<^sup>+ y = m \<turnstile> x \<leadsto>\<^sup>+ y"
  apply (rule iffI)
   apply (erule update_prev_next_trancl2)
  apply (erule update_prev_next_trancl)
  done

lemma rtrancl_prev_update:
  "modify_map m ptr (cteMDBNode_update (mdbPrev_update z)) \<turnstile> x \<leadsto>\<^sup>* y = m \<turnstile> x \<leadsto>\<^sup>* y"
  by (simp add: trancl_prev_update rtrancl_eq_or_trancl)

lemma mdb_chunked_prev_update:
  "mdb_chunked (modify_map m x (cteMDBNode_update (mdbPrev_update f))) = mdb_chunked m"
  apply (simp add: mdb_chunked_def trancl_prev_update rtrancl_prev_update is_chunk_def)
  apply (rule iffI)
   apply clarsimp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=p' in allE)
   apply (erule_tac x=cap in allE)
   apply (simp add: modify_map_if split: split_if_asm)
   apply (erule impE, blast)
   apply (erule allE, erule impE, blast)
   apply clarsimp
   apply blast
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply (erule_tac x=cap in allE)
  apply (simp add: modify_map_if split: split_if_asm)
    apply (erule impE, blast)
    apply clarsimp
    apply blast
   apply (erule allE, erule impE, blast)
   apply clarsimp
   apply blast
  apply clarsimp
  apply blast
  done

lemma descendants_of_prev_update:
  "descendants_of' p (modify_map m x (cteMDBNode_update (mdbPrev_update f))) =
   descendants_of' p m"
  by (simp add: descendants_of'_def)

lemma untyped_mdb_prev_update:
  "untyped_mdb' (modify_map m x (cteMDBNode_update (mdbPrev_update f))) = untyped_mdb' m"
  apply (simp add: untyped_mdb'_def descendants_of_prev_update)
  apply (rule iffI)
   apply clarsimp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=p' in allE)
   apply (erule_tac x=c in allE)
   apply (simp add: modify_map_if split: split_if_asm)
   apply (erule impE, blast)
   apply (erule allE, erule impE, blast)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply (erule_tac x=c in allE)
  apply (simp add: modify_map_if split: split_if_asm)
  apply clarsimp
  done

lemma untyped_inc_prev_update:
  "untyped_inc' (modify_map m x (cteMDBNode_update (mdbPrev_update f))) = untyped_inc' m"
  apply (simp add: untyped_inc'_def descendants_of_prev_update)
  apply (rule iffI)
   apply clarsimp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=p' in allE)
   apply (erule_tac x=c in allE)
   apply (simp add: modify_map_if split: split_if_asm)
   apply (erule impE, blast)
   apply (erule allE, erule impE, blast)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply (erule_tac x=c in allE)
  apply (simp add: modify_map_if split: split_if_asm)
  apply clarsimp
  done

lemma is_derived_badge_derived':
  "is_derived' m src cap cap' \<Longrightarrow> badge_derived' cap cap'"
  by (simp add: is_derived'_def)

lemma cteInsert_mdb_chain_0:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. mdb_chain_0 (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (fold revokable'_fold)
  apply (simp add: valid_mdb'_def split del: split_if)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0  mdb_inv_preserve_modify_map
    setUntypedCapAsFull_mdb_chain_0 mdb_inv_preserve_fun_upd | simp del:fun_upd_apply)+
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac x)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert (ctes_of s) src s_cap s_node dest NullCap ?node")
   apply (drule mdb_insert.chain_n)
   apply (rule mdb_chain_0_modify_map_prev)
   apply (simp add:modify_map_apply)
  apply (clarsimp simp: valid_badges_def)
   apply unfold_locales
          apply (assumption|rule refl)+
    apply (simp add: valid_mdb_ctes_def)
   apply (simp add: valid_mdb_ctes_def)
  apply assumption
  done

lemma cteInsert_mdb_chunked:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. mdb_chunked (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (fold revokable'_fold)
  apply (simp add: valid_mdb'_def split del: split_if)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map
    setUntypedCapAsFull_mdb_chunked mdb_inv_preserve_fun_upd,simp)
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac cteb)
  apply (rename_tac d_cap d_node)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert (ctes_of s) src s_cap s_node dest NullCap d_node")
   apply (drule mdb_insert.chunked_n, erule is_derived_badge_derived')
   apply (clarsimp simp: modify_map_apply mdb_chunked_prev_update)
  apply unfold_locales
          apply (assumption|rule refl)+
    apply (simp add: valid_mdb_ctes_def)
   apply (simp add: valid_mdb_ctes_def)
  apply assumption
  done

lemma cteInsert_untyped_mdb:
  "\<lbrace>valid_mdb' and pspace_distinct' and pspace_aligned' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. untyped_mdb' (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: split_if)
  apply (fold revokable'_fold)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map
    setUntypedCapAsFull_untyped_mdb' mdb_inv_preserve_fun_upd,simp)
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac cteb)
  apply (rename_tac d_cap d_node)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert_der (ctes_of s) src s_cap s_node dest NullCap d_node cap")
   prefer 2
   apply unfold_locales[1]
            apply (assumption|rule refl)+
      apply (simp add: valid_mdb_ctes_def)
     apply (simp add: valid_mdb_ctes_def)
    apply assumption
   apply assumption
  apply (case_tac "isMDBParentOf (CTE s_cap s_node) (CTE cap
                   (mdbFirstBadged_update (\<lambda>a. revokable' s_cap cap)
                     (mdbRevocable_update (\<lambda>a. revokable' s_cap cap) (mdbPrev_update (\<lambda>a. src) s_node))))")
   apply (subgoal_tac "mdb_insert_child (ctes_of s) src s_cap s_node dest NullCap d_node cap")
    prefer 2
    apply (simp add: mdb_insert_child_def mdb_insert_child_axioms_def)
   apply (drule mdb_insert_child.untyped_mdb_n)
   apply (clarsimp simp: modify_map_apply untyped_mdb_prev_update
                         descendants_of_prev_update)
  apply (subgoal_tac "mdb_insert_sib (ctes_of s) src s_cap s_node dest NullCap d_node cap")
   prefer 2
   apply (simp add: mdb_insert_sib_def mdb_insert_sib_axioms_def)
  apply (drule mdb_insert_sib.untyped_mdb_n)
  apply (clarsimp simp: modify_map_apply untyped_mdb_prev_update
                        descendants_of_prev_update)
  done

lemma valid_mdb_ctes_maskedAsFull:
  "\<lbrakk>valid_mdb_ctes m;m src = Some (CTE s_cap s_node)\<rbrakk>
   \<Longrightarrow> valid_mdb_ctes (m(src \<mapsto> CTE (maskedAsFull s_cap cap) s_node))"
  apply (clarsimp simp:fun_upd_apply maskedAsFull_def)
  apply (intro conjI impI)
  apply (frule mdb_inv_preserve_updateCap
    [where m = m and slot = src and index = "max_free_index (capBlockSize cap)"])
    apply simp
   apply (drule mdb_inv_preserve_sym)
   apply (clarsimp simp:valid_mdb_ctes_def modify_map_def)
   apply (frule mdb_inv_preserve.preserve_stuff,simp)
   apply (frule mdb_inv_preserve.by_products,simp)
   apply (rule mdb_inv_preserve.untyped_inc')
    apply (erule mdb_inv_preserve_sym)
    apply (clarsimp split:split_if_asm simp: isCap_simps max_free_index_def)
   apply simp
  apply (subgoal_tac "m = m(src \<mapsto> CTE s_cap s_node)")
   apply simp
  apply (rule ext)
  apply clarsimp
  done

lemma capAligned_maskedAsFull:
  "capAligned s_cap \<Longrightarrow> capAligned (maskedAsFull s_cap cap)"
 apply (case_tac s_cap)
   apply (clarsimp simp:isCap_simps capAligned_def maskedAsFull_def max_free_index_def)+
 done

lemma maskedAsFull_derived':
  "\<lbrakk>m src = Some (CTE s_cap s_node); is_derived' m ptr b c\<rbrakk>
   \<Longrightarrow> is_derived' (m(src \<mapsto> CTE (maskedAsFull s_cap cap) s_node)) ptr b c"
  apply (subgoal_tac "m(src \<mapsto> CTE (maskedAsFull s_cap cap) s_node)
     = (modify_map m src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))")
   apply simp
   apply (clarsimp simp:maskedAsFull_def is_derived'_def)
   apply (intro conjI impI)
    apply (simp add:modify_map_def del:cteCap_update.simps)
   apply (subst same_master_descendants)
       apply simp
      apply (clarsimp simp:isCap_simps capASID_def )+
   apply (clarsimp simp:modify_map_def)
   done

lemma maskedAsFull_usable_empty:
  "\<lbrakk>capMasterCap cap = capMasterCap s_cap;
    isUntypedCap (maskedAsFull s_cap cap)\<rbrakk>
   \<Longrightarrow> usableUntypedRange (maskedAsFull s_cap cap) = {}"
  apply (simp add:isCap_simps maskedAsFull_def max_free_index_def split:split_if_asm)
   apply fastforce+
  done

lemma capAligned_master:
  "\<lbrakk>capAligned cap; capMasterCap cap = capMasterCap ncap\<rbrakk> \<Longrightarrow> capAligned ncap"
  apply (case_tac cap)
   apply (clarsimp simp:capAligned_def)+
  apply (case_tac arch_capability)
   apply (clarsimp simp:capAligned_def)+
  done

lemma cteInsert_untyped_inc':
  "\<lbrace>valid_mdb' and pspace_distinct' and pspace_aligned' and valid_objs' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. untyped_inc' (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: split_if)
  apply (fold revokable'_fold)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map
    setUntypedCapAsFull_untyped_mdb' mdb_inv_preserve_fun_upd)
  apply (wp getCTE_wp setUntypedCapAsFull_ctes)
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac cteb)
  apply (rename_tac d_cap d_node)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert_der
    (modify_map (ctes_of s) src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))
    src (maskedAsFull s_cap cap) s_node dest NullCap d_node cap")
   prefer 2
   apply unfold_locales[1]
          apply (clarsimp simp:modify_map_def valid_mdb_ctes_maskedAsFull)+
      apply (erule(2) valid_mdb_ctesE[OF valid_mdb_ctes_maskedAsFull])
      apply (clarsimp simp:modify_map_def)
     apply (erule(2) valid_mdb_ctesE[OF valid_mdb_ctes_maskedAsFull])
    apply simp
   apply (clarsimp simp:modify_map_def maskedAsFull_derived')
  apply (case_tac "isMDBParentOf (CTE (maskedAsFull s_cap cap) s_node) (CTE cap
                   (mdbFirstBadged_update (\<lambda>a. revokable' (maskedAsFull s_cap cap) cap)
                   (mdbRevocable_update (\<lambda>a. revokable' (maskedAsFull s_cap cap) cap)
                   (mdbPrev_update (\<lambda>a. src) s_node))))")
   apply (subgoal_tac "mdb_insert_child
     (modify_map (ctes_of s) src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))
     src (maskedAsFull s_cap cap) s_node dest NullCap d_node cap")
    prefer 2
    apply (simp add: mdb_insert_child_def mdb_insert_child_axioms_def)
    apply (drule mdb_insert_child.untyped_inc_n)
      apply (rule capAligned_maskedAsFull[OF valid_capAligned])
      apply (erule(1) ctes_of_valid_cap')
     apply (intro impI maskedAsFull_usable_empty)
      apply (clarsimp simp:is_derived'_def badge_derived'_def)
     apply simp
   apply (clarsimp simp: modify_map_apply untyped_inc_prev_update maskedAsFull_revokable
                         descendants_of_prev_update)
  apply (subgoal_tac "mdb_insert_sib
    (modify_map (ctes_of s) src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))
    src (maskedAsFull s_cap cap) s_node dest NullCap d_node cap")
   prefer 2
   apply (simp add: mdb_insert_sib_def mdb_insert_sib_axioms_def)
  apply (drule mdb_insert_sib.untyped_inc_n)
   apply (rule capAligned_master[OF valid_capAligned])
   apply (erule(1) ctes_of_valid_cap')
    apply (clarsimp simp:is_derived'_def badge_derived'_def)
  apply (clarsimp simp: modify_map_apply untyped_inc_prev_update maskedAsFull_revokable
                        descendants_of_prev_update)
  done

lemma irq_control_prev_update:
  "irq_control (modify_map m x (cteMDBNode_update (mdbPrev_update f))) = irq_control m"
  apply (simp add: irq_control_def)
  apply (rule iffI)
   apply clarsimp
   apply (simp only: modify_map_if)
   apply (erule_tac x=p in allE)
   apply (simp (no_asm_use) split: split_if_asm)
   apply (case_tac "x=p")
    apply fastforce
   apply clarsimp
   apply (erule_tac x=p' in allE)
   apply simp
   apply (case_tac "x=p'")
    apply simp
   apply fastforce
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (simp add: modify_map_if split: split_if_asm)
   apply clarsimp
   apply (case_tac "x=p'")
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (case_tac "x=p'")
   apply clarsimp
  apply clarsimp
  done

lemma cteInsert_irq_control:
  "\<lbrace>valid_mdb' and pspace_distinct' and pspace_aligned' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. irq_control (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: split_if)
  apply (fold revokable'_fold)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0 setUntypedCapAsFull_irq_control mdb_inv_preserve_fun_upd
    mdb_inv_preserve_modify_map,simp)
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac cteb)
  apply (rename_tac d_cap d_node)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert_der (ctes_of s) src s_cap s_node dest NullCap d_node cap")
   prefer 2
   apply unfold_locales[1]
            apply (assumption|rule refl)+
      apply (simp add: valid_mdb_ctes_def)
     apply (simp add: valid_mdb_ctes_def)
    apply assumption+
  apply (drule mdb_insert_der.irq_control_n)
  apply (clarsimp simp: modify_map_apply irq_control_prev_update)
  done

lemma capMaster_isUntyped:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> isUntypedCap c = isUntypedCap c'"
  by (simp add: capMasterCap_def isCap_simps split: capability.splits)

lemma capMaster_capRange:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> capRange c = capRange c'"
  by (simp add: capMasterCap_def capRange_def split: capability.splits arch_capability.splits)

lemma capMaster_untypedRange:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> untypedRange c = untypedRange c'"
  by (simp add: capMasterCap_def capRange_def split: capability.splits arch_capability.splits)

lemma capMaster_capClass:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> capClass c = capClass c'"
  by (simp add: capMasterCap_def split: capability.splits arch_capability.splits)

lemma valid_dlist_no_0_prev:
  "\<lbrakk> m p = Some (CTE c n); m (mdbNext n) = Some (CTE c' (MDB x 0 b1 b2)); valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow> False"
  apply (erule (1) valid_dlistE)
   apply clarsimp
  apply clarsimp
  done

lemma distinct_zombies_nonCTE_modify_map:
  "\<And>m x f. \<lbrakk> \<And>cte. cteCap (f cte) = cteCap cte \<rbrakk>
	   \<Longrightarrow> distinct_zombies (modify_map m x f) = distinct_zombies m"
  apply (simp add: distinct_zombies_def modify_map_def o_def)
  apply (rule_tac f=distinct_zombie_caps in arg_cong)
  apply (rule ext)
  apply (simp add: option_map_comp o_def)
  done

lemma setUntypedCapAsFull_ctes_of_no_0':
  "\<lbrace>\<lambda>s. no_0 (ctes_of s) \<and> cte_wp_at' (op = srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>r s. no_0 (ctes_of s)\<rbrace>"
  apply (clarsimp simp:no_0_def split:if_splits)
  apply (wp hoare_vcg_imp_lift setUntypedCapAsFull_ctes_of[where dest = 0])
    apply (auto simp:cte_wp_at_ctes_of)
done

(* FIXME: move *)
lemma mdb_inv_preserve_update_cap_same:
  "mdb_inv_preserve m m'
   \<Longrightarrow> mdb_inv_preserve (modify_map m dest (cteCap_update (\<lambda>_. cap)))
                        (modify_map m' dest (cteCap_update (\<lambda>_. cap)))"
  apply (simp (no_asm) add:mdb_inv_preserve_def)
  apply (intro conjI allI)
     apply (drule mdb_inv_preserve.dom)
     apply (simp add:modify_map_dom)
    apply (clarsimp simp:modify_map_def split del:if_splits split:split_if_asm)
    apply (drule(2) mdb_inv_preserve.misc,simp)+
   apply (clarsimp simp:mdb_inv_preserve.sameRegion
     modify_map_def split:if_splits)+
 apply (case_tac "p = dest")
   apply (clarsimp simp:mdb_next_def map_option_def split:option.splits )
   apply (intro conjI allI impI)
     apply (rule ccontr,clarify)
     apply (fastforce dest!:iffD2[OF mdb_inv_preserve.dom,OF _ domI])
     apply (rule ccontr,simp)
     apply (fastforce dest!:iffD1[OF mdb_inv_preserve.dom,OF _ domI])
   apply (drule mdb_inv_preserve.mdb_next[where p = dest])
   apply (clarsimp simp:mdb_next_def map_option_def split:option.splits)+
 apply (intro conjI allI impI)
  apply (rule ccontr,clarify)
  apply (fastforce dest!:iffD2[OF mdb_inv_preserve.dom,OF _ domI])
  apply (rule ccontr,simp)
  apply (fastforce dest!:iffD1[OF mdb_inv_preserve.dom,OF _ domI])
 apply (drule_tac p = p in mdb_inv_preserve.mdb_next)
 apply (clarsimp simp:mdb_next_def map_option_def split:option.splits)
done

lemma updateCapFreeIndex_dlist:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (valid_dlist (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (valid_dlist (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma setUntypedCapAsFull_valid_dlist:
  assumes preserve:
  "\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
  "\<lbrace>\<lambda>s. P (valid_dlist (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>r s. P (valid_dlist (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
   apply (wp updateCapFreeIndex_dlist)
   apply (clarsimp simp:preserve cte_wp_at_ctes_of)+
  apply wp
  apply clarsimp
  done

lemma valid_dlist_prevD:
  "\<lbrakk>m p = Some cte;valid_dlist m;mdbPrev (cteMDBNode cte) \<noteq> 0\<rbrakk>
   \<Longrightarrow> (\<exists>cte'. m (mdbPrev (cteMDBNode cte)) = Some cte' \<and>
               mdbNext (cteMDBNode cte') = p)"
  by (clarsimp simp:valid_dlist_def Let_def)

lemma valid_dlist_nextD:
  "\<lbrakk>m p = Some cte;valid_dlist m;mdbNext (cteMDBNode cte) \<noteq> 0\<rbrakk>
   \<Longrightarrow> (\<exists>cte'. m (mdbNext (cteMDBNode cte)) = Some cte' \<and>
               mdbPrev (cteMDBNode cte') = p)"
  by (clarsimp simp:valid_dlist_def Let_def)

lemma no_loops_no_l2_loop:
  "\<lbrakk>valid_dlist m; no_loops m; m p = Some cte;mdbPrev (cteMDBNode cte) = mdbNext (cteMDBNode cte)\<rbrakk>
       \<Longrightarrow> mdbNext (cteMDBNode cte) = 0"
  apply (rule ccontr)
  apply (subgoal_tac "m \<turnstile> p \<leadsto> (mdbNext (cteMDBNode cte))")
   prefer 2
   apply (clarsimp simp:mdb_next_rel_def mdb_next_def)
  apply (subgoal_tac "m \<turnstile> (mdbNext (cteMDBNode cte)) \<leadsto> p")
   prefer 2
   apply (clarsimp simp:mdb_next_rel_def mdb_next_def)
   apply (frule(2) valid_dlist_nextD)
   apply clarsimp
   apply (frule(1) valid_dlist_prevD)
   apply simp+
  apply (drule(1) transitive_closure_trans)
  apply (simp add:no_loops_def)
  done

lemma cteInsert_no_0:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and
    (\<lambda>s. src \<noteq> dest) and K (capAligned cap) and valid_objs' and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>_ s. no_0 (ctes_of s) \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: split_if)
  apply (fold revokable'_fold)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
      apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
      apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
        setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map getCTE_wp
        setUntypedCapAsFull_valid_dlist mdb_inv_preserve_fun_upd | simp)+
  apply (intro conjI impI)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (clarsimp simp:valid_mdb_ctes_def no_0_def)
  done

lemma cteInsert_valid_dlist:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and
    (\<lambda>s. src \<noteq> dest) and K (capAligned cap) and valid_objs' and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>_ s. valid_dlist (ctes_of s) \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: split_if)
  apply (fold revokable'_fold)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
      apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
      apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
        setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map getCTE_wp
        setUntypedCapAsFull_valid_dlist mdb_inv_preserve_fun_upd | simp)+
  apply (intro conjI impI)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (intro conjI)
   apply (clarsimp simp:valid_mdb_ctes_def no_0_def)+
  apply (frule mdb_chain_0_no_loops)
   apply (simp add:no_0_def)
  apply (rule valid_dlistI)
   apply (case_tac "p = dest")
    apply (clarsimp simp:modify_map_def nullPointer_def split:split_if_asm)+
   apply (frule(2) valid_dlist_prevD)
    apply simp
    apply (subgoal_tac "mdbPrev (cteMDBNode ctea) \<noteq> mdbNext (cteMDBNode ctea)")
    prefer 2
     apply (clarsimp)
     apply (drule(3) no_loops_no_l2_loop[rotated -1],simp)
    apply (subgoal_tac "mdbPrev (cteMDBNode ctea) \<noteq> dest")
    apply clarsimp+
   apply (frule_tac p = p and m = "ctes_of sa" in valid_dlist_prevD)
    apply simp+
   apply fastforce
  apply (case_tac "p = dest")
   apply (clarsimp simp:modify_map_def nullPointer_def split:split_if_asm)+
   apply (frule(2) valid_dlist_nextD,clarsimp)
  apply (clarsimp simp:modify_map_def nullPointer_def split:split_if_asm)
   apply (frule(2) valid_dlist_nextD)
    apply simp
    apply (subgoal_tac "mdbPrev (cteMDBNode ctea) \<noteq> mdbNext (cteMDBNode ctea)")
    prefer 2
     apply (clarsimp)
     apply (drule(3) no_loops_no_l2_loop[rotated -1],simp)
     apply clarsimp
     apply (intro conjI impI)
      apply clarsimp+
     apply (drule_tac cte = cte' in no_loops_no_l2_loop,simp)
      apply simp+
   apply (frule(2) valid_dlist_nextD)
    apply clarsimp
   apply (frule_tac p = p and m = "ctes_of sa" in valid_dlist_nextD)
    apply clarsimp+
   apply (rule conjI)
    apply fastforce
   apply (intro conjI impI,clarsimp+)
   apply (frule_tac valid_dlist_nextD)
    apply clarsimp+
  apply (frule_tac valid_dlist_nextD)
  apply clarsimp+
  done

lemma cteInsert_mdb' [wp]:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and (\<lambda>s. src \<noteq> dest) and K (capAligned cap) and valid_objs' and
   (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s) \<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (simp add:valid_mdb'_def valid_mdb_ctes_def revokable'_fold[symmetric])
  apply (rule_tac Q = "\<lambda>r s. valid_dlist (ctes_of s) \<and> irq_control (ctes_of s) \<and>
               no_0 (ctes_of s) \<and> mdb_chain_0 (ctes_of s) \<and>
               mdb_chunked (ctes_of s) \<and> untyped_mdb' (ctes_of s) \<and> untyped_inc' (ctes_of s) \<and>
               ?Q s"
     in hoare_strengthen_post)
   prefer 2
   apply clarsimp
   apply assumption
  apply (rule hoare_name_pre_state)
  apply (wp cteInsert_no_0 cteInsert_valid_dlist cteInsert_mdb_chain_0 cteInsert_untyped_inc'
            cteInsert_mdb_chunked cteInsert_untyped_mdb cteInsert_irq_control)
  apply (unfold cteInsert_def)
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: split_if)
  apply (fold revokable'_fold)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
      apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
      apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
        setUntypedCapAsFull_ctes_of_no_0
        setUntypedCapAsFull_valid_dlist setUntypedCapAsFull_distinct_zombies
        setUntypedCapAsFull_valid_badges setUntypedCapAsFull_caps_contained
        setUntypedCapAsFull_valid_nullcaps setUntypedCapAsFull_ut_revocable
        setUntypedCapAsFull_class_links setUntypedCapAsFull_reply_masters_rvk_fb
        mdb_inv_preserve_fun_upd
        mdb_inv_preserve_modify_map getCTE_wp| simp del:fun_upd_apply)+
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  defer
  apply (clarsimp simp:valid_mdb_ctes_def valid_mdb'_def simp del:fun_upd_apply)+
  apply (case_tac cte)
  apply (case_tac x)
  apply (case_tac mdbnode)
  apply (case_tac mdbnodea)
  apply (clarsimp simp:valid_mdb_ctes_def no_0_def nullPointer_def)
  apply (intro conjI impI)
  apply clarsimp
  apply (rename_tac s src_cap word1 word2 bool1a bool2a bool1 bool2)
proof -
  fix s :: kernel_state
  fix bool1 bool2 src_cap word1 word2 bool1a bool2a
  let ?c1 = "(CTE src_cap (MDB word1 word2 bool1a bool2a))"
  let ?c2 = "(CTE capability.NullCap (MDB 0 0 bool1 bool2))"
  let ?C = "(modify_map
             (modify_map
               (modify_map (ctes_of s(dest \<mapsto> CTE cap (MDB 0 0 bool1 bool2))) dest
                 (cteMDBNode_update (\<lambda>a. MDB word1 src (revokable' src_cap cap) (revokable' src_cap cap))))
               src (cteMDBNode_update (mdbNext_update (\<lambda>_. dest))))
             word1 (cteMDBNode_update (mdbPrev_update (\<lambda>_. dest))))"
  let ?m = "ctes_of s"
  let ?prv = "\<lambda>cte. mdbPrev (cteMDBNode cte)"
  let ?nxt = "\<lambda>cte. mdbNext (cteMDBNode cte)"

  assume "pspace_distinct' s" and "pspace_aligned' s" and srcdest: "src \<noteq> dest"
     and dest0: "dest \<noteq> 0"
     and cofs: "ctes_of s src = Some ?c1" and cofd: "ctes_of s dest = Some ?c2"
     and is_der: "is_derived' (ctes_of s) src cap src_cap"
     and aligned: "capAligned cap"
     and vd: "valid_dlist ?m"
     and no0: "?m 0 = None"
     and chain: "mdb_chain_0 ?m"
     and badges: "valid_badges ?m"
     and chunk: "mdb_chunked ?m"
     and contained: "caps_contained' ?m"
     and untyped_mdb: "untyped_mdb' ?m"
     and untyped_inc: "untyped_inc' ?m"
     and class_links: "class_links ?m"
     and distinct_zombies: "distinct_zombies ?m"
     and irq: "irq_control ?m"
     and reply_masters_rvk_fb: "reply_masters_rvk_fb ?m"
     and vn: "valid_nullcaps ?m"
     and ut_rev:"ut_revocable' ?m"

  have no_loop: "no_loops ?m"
     apply (rule mdb_chain_0_no_loops[OF chain])
     apply (simp add:no_0_def no0)
     done

  have badge: "badge_derived' cap src_cap"
     using is_der
     by (clarsimp simp:is_derived'_def)

  have vmdb: "valid_mdb_ctes ?m"
    by (auto simp: vmdb_def valid_mdb_ctes_def no_0_def, fact+)

  have src0: "src \<noteq> 0"
    using cofs no0 by clarsimp

  have destnull:
    "cte_mdb_prop ?m dest (\<lambda>m. mdbPrev m = 0 \<and> mdbNext m = 0)"
    using cofd unfolding cte_mdb_prop_def
    by auto

  have srcwd: "?m \<turnstile> src \<leadsto> word1"
    using cofs by (simp add: next_unfold')

  have w1ned[simp]: "word1 \<noteq> dest"
  proof (cases "word1 = 0")
    case True thus ?thesis using dest0 by auto
  next
    case False
    thus ?thesis using cofs cofd src0 dest0 False vd
      by - (erule (1) valid_dlistEn, (clarsimp simp: nullPointer_def)+)
  qed

  have w2ned[simp]: "word2 \<noteq> dest"
  proof (cases "word2 = 0")
    case True thus ?thesis using dest0 by auto
  next
    case False
    thus ?thesis using cofs cofd src0 dest0 False vd
      by - (erule (1) valid_dlistEp, (clarsimp simp: nullPointer_def)+)
  qed

  have w1nes[simp]: "word1 \<noteq> src" using vmdb cofs
    by - (drule (1) no_self_loop_next, simp)

  have w2nes[simp]: "word2 \<noteq> src" using vmdb cofs
    by - (drule (1) no_self_loop_prev, simp)

  from is_der have notZomb1: "\<not> isZombie cap"
    by (clarsimp simp: isCap_simps is_derived'_def badge_derived'_def)

  from is_der have notZomb2: "\<not> isZombie src_cap"
    by (clarsimp simp: isCap_simps is_derived'_def)

  from badge have masters: "capMasterCap cap = capMasterCap src_cap"
     by (clarsimp simp: badge_derived'_def)

  note blah[simp] = w2nes[symmetric] w1nes[symmetric] w1ned[symmetric]
    w2ned[symmetric] srcdest srcdest[symmetric]

  have mdb_next_disj:
   "\<And>p p'. (?C \<turnstile> p \<leadsto> p' \<Longrightarrow>
   ?m \<turnstile> p \<leadsto> p' \<and> p \<noteq> src \<and> p'\<noteq> dest \<and> (p' = word1 \<longrightarrow> p' = 0)
   \<or> p = src \<and> p' = dest \<or> p = dest \<and> p' = word1)"
   apply (case_tac "p = src")
   apply (clarsimp simp:mdb_next_unfold modify_map_cases)
   apply (case_tac "p = dest")
   apply (clarsimp simp:mdb_next_unfold modify_map_cases)+
   using cofs cofd vd no0
   apply -
   apply (case_tac "p = word1")
    apply clarsimp
    apply (intro conjI)
     apply clarsimp
     apply (frule_tac p = "word1" and m = "?m" in valid_dlist_nextD)
      apply clarsimp+
     apply (frule_tac p = "mdbNext node" and m = "?m" in valid_dlist_nextD)
      apply clarsimp+
    apply (frule_tac p = "mdbNext node" in no_loops_no_l2_loop[OF _ no_loop])
     apply simp+
  apply (intro conjI)
   apply clarsimp
    apply (frule_tac p = p and m = "?m" in valid_dlist_nextD)
     apply (clarsimp+)[3]
  apply (intro impI)
  apply (rule ccontr)
  apply clarsimp
    apply (frule_tac p = src and m = "?m" in valid_dlist_nextD)
  apply clarsimp+
    apply (frule_tac p = p and m = "?m" in valid_dlist_nextD)
  apply clarsimp+
  done

  have ctes_ofD:
   "\<And>p cte. \<lbrakk>?C p = Some cte; p\<noteq> dest; p\<noteq> src\<rbrakk> \<Longrightarrow> \<exists>cteb. (?m p = Some cteb \<and> cteCap cte = cteCap cteb)"
   by (clarsimp simp:modify_map_def split:if_splits)


  show "valid_badges ?C"
  using srcdest badge cofs badges cofd
  unfolding valid_badges_def
  apply (intro impI allI)
  apply (drule mdb_next_disj)
  apply (elim disjE)
    defer
    apply (clarsimp simp:modify_map_cases dest0 src0)
    apply (clarsimp simp:revokable'_def badge_derived'_def)
    apply (case_tac src_cap,auto simp:isCap_simps sameRegionAs_def)[1]
  apply (clarsimp simp:modify_map_cases valid_badges_def)
    apply (frule_tac x=src in spec, erule_tac x=word1 in allE, erule allE, erule impE)
    apply fastforce
    apply simp
    apply (clarsimp simp:mdb_next_unfold badge_derived'_def split: split_if_asm)
    apply (thin_tac "All ?P")
    apply (cases src_cap,
       auto simp:mdb_next_unfold isCap_simps sameRegionAs_def Let_def split: if_splits)[1]
  apply (case_tac "word1 = p'")
     apply (clarsimp simp:modify_map_cases valid_badges_def mdb_next_unfold src0 dest0 no0)+
  apply (case_tac "p = dest")
   apply (clarsimp simp:dest0 src0 no0)+
  apply (case_tac z)
  apply clarsimp
  apply (drule_tac x = p in spec,drule_tac x = "mdbNext mdbnode" in spec)
  apply (auto simp:isCap_simps sameRegionAs_def)
  done

  from badge
  have isUntyped_eq: "isUntypedCap cap = isUntypedCap src_cap"
   apply (clarsimp simp:badge_derived'_def)
   apply (case_tac cap,auto simp:isCap_simps)
   done

  from badge
  have [simp]: "capRange cap = capRange src_cap"
   apply (clarsimp simp:badge_derived'_def)
   apply (case_tac cap)
     apply (clarsimp simp:isCap_simps capRange_def dest!:capMasterCap_eqDs)+
    apply (case_tac arch_capability)
   apply (clarsimp simp:isCap_simps capRange_def dest!:capMasterCap_eqDs)+
   done

  have [simp]: "untypedRange cap = untypedRange src_cap"
     using badge
     apply (clarsimp simp:badge_derived'_def dest!:capMaster_untypedRange)
     done

  from contained badge srcdest cofs cofd is_der no0
  show "caps_contained' ?C"
  apply (clarsimp simp add: caps_contained'_def)
  apply (case_tac "p = dest")
   apply (case_tac "p' = dest")
    apply (clarsimp simp:modify_map_def split:if_splits)
    apply (case_tac src_cap,auto)[1]
   apply (case_tac "p' = src")
    apply (clarsimp simp:modify_map_def split:if_splits)
    apply (clarsimp simp:badge_derived'_def)
    apply (case_tac src_cap,auto)[1]
   apply (drule(2) ctes_ofD)
   apply (clarsimp simp:modify_map_def split:if_splits)
   apply (frule capRange_untyped)
   apply (erule_tac x=src in allE, erule_tac x=p' in allE, simp)
    apply (case_tac cteb)
    apply (clarsimp)
    apply blast
   apply (case_tac "p' = dest")
    apply (case_tac "p = src")
     apply (clarsimp simp:modify_map_def split:if_splits)
     apply (drule capRange_untyped)
     apply (case_tac cap,auto simp:isCap_simps badge_derived'_def)[1]
    apply (clarsimp simp:modify_map_def split:if_splits)
    apply (drule_tac x = word1 in spec)
    apply (drule_tac x = src in spec)
    apply (case_tac z)
    apply (clarsimp simp:isUntyped_eq)
    apply blast
    apply (drule_tac x = p in spec)
    apply (drule_tac x = src in spec)
    apply (frule capRange_untyped)
    apply (clarsimp simp:isUntyped_eq)
    apply blast
   apply (drule_tac x = p in spec)
   apply (drule_tac x = p' in spec)
   apply (clarsimp simp:modify_map_def split:if_splits)
    apply ((case_tac z,fastforce)+)[5]
   apply fastforce+
   done

  show "valid_nullcaps ?C"
  using is_der vn cofs vd no0
  apply (simp add: valid_nullcaps_def srcdest [symmetric])
  apply (clarsimp simp:modify_map_def is_derived'_def)
  apply (rule conjI)
    apply (clarsimp simp: is_derived'_def badge_derived'_def)+
  apply (drule_tac x = word1 in spec)
  apply (case_tac z)
  apply (clarsimp simp:nullMDBNode_def)
  apply (drule(1) valid_dlist_nextD)
    apply simp
   apply clarsimp
  apply (simp add:nullPointer_def src0)
  done

  from vmdb srcdest cofs ut_rev
  show "ut_revocable' ?C"
  apply (clarsimp simp: valid_mdb_ctes_def ut_revocable'_def modify_map_def)
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: revokable'_def isCap_simps)+
   apply auto
  apply (drule_tac x= src in spec)
   apply clarsimp
  apply (case_tac z)
   apply clarsimp
  done

  from class_links srcdest badge cofs cofd no0 vd
  show "class_links ?C"
  unfolding class_links_def
  apply (intro allI impI)
  apply (drule mdb_next_disj)
  apply (elim disjE)
    apply (clarsimp simp:modify_map_def mdb_next_unfold split:split_if_asm)
   apply (clarsimp simp: badge_derived'_def modify_map_def
    split: split_if_asm)
   apply (erule capMaster_capClass)
  apply (clarsimp simp:modify_map_def split:if_splits)
  apply (drule_tac x = src in spec)
  apply (drule_tac x = word1 in spec)
  apply (clarsimp simp:mdb_next_unfold)
  apply (case_tac z)
   apply (clarsimp simp:badge_derived'_def)
  apply (drule capMaster_capClass)
  apply simp
  done

 from distinct_zombies badge
 show "distinct_zombies ?C"
 apply (simp add:distinct_zombies_nonCTE_modify_map)
 apply (erule_tac distinct_zombies_copyMasterE[where x=src])
   apply (rule cofs)
  apply (simp add: masters)
 apply (simp add: notZomb1 notZomb2)
 done

 from reply_masters_rvk_fb is_der
 show "reply_masters_rvk_fb ?C"
   apply (clarsimp simp:reply_masters_rvk_fb_def)
   apply (erule ranE)
   apply (clarsimp simp:modify_map_def split:split_if_asm)
    apply fastforce+
   apply (clarsimp simp:is_derived'_def isCap_simps)
   apply fastforce
 done
qed

crunch state_refs_of'[wp]: cteInsert "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps)

crunch aligned'[wp]: cteInsert pspace_aligned'
  (wp: crunch_wps)

crunch distinct'[wp]: cteInsert pspace_distinct'
  (wp: crunch_wps)

crunch no_0_obj' [wp]: cteInsert no_0_obj'
  (wp: crunch_wps)

lemma cteInsert_valid_pspace:
  "\<lbrace>valid_pspace' and valid_cap' cap and (\<lambda>s. src \<noteq> dest) and valid_objs' and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def
  apply (rule hoare_pre)
  apply (wp cteInsert_valid_objs)
  apply (fastforce elim: valid_capAligned)
  done

lemma setCTE_ko_wp_at_live[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' live' p' s)\<rbrace>
    setCTE p v
   \<lbrace>\<lambda>rv s. P (ko_wp_at' live' p' s)\<rbrace>"
  apply (clarsimp simp: setCTE_def setObject_def split_def
                        valid_def in_monad ko_wp_at'_def
             split del: split_if
                 elim!: rsubst[where P=P])
  apply (drule(1) updateObject_cte_is_tcb_or_cte [OF _ refl, rotated])
  apply (elim exE conjE disjE)
   apply (clarsimp simp: ps_clear_upd' objBits_simps
                         lookupAround2_char1)
   apply (simp add: tcb_cte_cases_def split: split_if_asm)
  apply (clarsimp simp: ps_clear_upd' objBits_simps)
  done

lemma setCTE_iflive':
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte'. \<forall>p'\<in>zobj_refs' (cteCap cte')
                          - zobj_refs' (cteCap cte).
                                ko_wp_at' (Not \<circ> live') p' s) p s
      \<and> if_live_then_nonz_cap' s\<rbrace>
     setCTE p cte
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  unfolding if_live_then_nonz_cap'_def ex_nonz_cap_to'_def
  apply (rule hoare_pre)
   apply (simp only: imp_conv_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
             hoare_vcg_ex_lift setCTE_weak_cte_wp_at)
  apply clarsimp
  apply (drule spec, drule(1) mp)
  apply clarsimp
  apply (rule_tac x=cref in exI)
  apply (clarsimp simp: cte_wp_at'_def)
  apply (rule ccontr)
  apply (drule bspec, fastforce)
  apply (clarsimp simp: ko_wp_at'_def)
  done

lemma updateMDB_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s\<rbrace>
     updateMDB p m
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  apply (clarsimp simp: updateMDB_def)
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (wp setCTE_iflive')
  apply (clarsimp elim!: cte_wp_at_weakenE')
  done

lemma updateCap_iflive':
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte'. \<forall>p'\<in>zobj_refs' (cteCap cte')
                          - zobj_refs' cap.
                                ko_wp_at' (Not \<circ> live') p' s) p s
      \<and> if_live_then_nonz_cap' s\<rbrace>
     updateCap p cap
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  apply (simp add: updateCap_def)
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (wp setCTE_iflive')
  apply (clarsimp elim!: cte_wp_at_weakenE')
  done

lemma setCTE_ko_wp_at_not_live[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' (Not \<circ> live') p' s)\<rbrace>
    setCTE p v
   \<lbrace>\<lambda>rv s. P (ko_wp_at' (Not \<circ> live') p' s)\<rbrace>"
  apply (clarsimp simp: setCTE_def setObject_def split_def
                        valid_def in_monad ko_wp_at'_def
             split del: split_if
                 elim!: rsubst[where P=P])
  apply (drule(1) updateObject_cte_is_tcb_or_cte [OF _ refl, rotated])
  apply (elim exE conjE disjE)
   apply (clarsimp simp: ps_clear_upd' objBits_simps
                         lookupAround2_char1)
   apply (simp add: tcb_cte_cases_def split: split_if_asm)
  apply (clarsimp simp: ps_clear_upd' objBits_simps)
  done

lemma setUntypedCapAsFull_ko_wp_not_at'[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' (Not \<circ> live') p' s)\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>r s. P ( ko_wp_at' (Not \<circ> live') p' s)\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def updateCap_def)
  apply (wp setCTE_ko_wp_at_live setCTE_ko_wp_at_not_live)
done

lemma setUntypedCapAsFull_ko_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' live' p' s)\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>r s. P ( ko_wp_at' live' p' s)\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def updateCap_def)
  apply (wp setCTE_ko_wp_at_live setCTE_ko_wp_at_live)
  done

(*FIXME:MOVE*)
lemma zobj_refs'_capFreeIndex_update[simp]:
  "isUntypedCap ctecap \<Longrightarrow>
   zobj_refs' (capFreeIndex_update f (ctecap)) = zobj_refs' ctecap"
  by (case_tac ctecap,auto simp:isCap_simps)

lemma setUntypedCapAsFull_if_live_then_nonz_cap':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> cte_wp_at' (op = srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  apply (clarsimp simp:if_live_then_nonz_cap'_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply (clarsimp simp:setUntypedCapAsFull_def split del:if_splits)
  apply (wp hoare_vcg_split_if)
    apply (clarsimp simp:ex_nonz_cap_to'_def cte_wp_at_ctes_of)
    apply (wp updateCap_ctes_of_wp)
 apply clarsimp
 apply (elim allE impE)
  apply (assumption)
 apply (clarsimp simp:ex_nonz_cap_to'_def cte_wp_at_ctes_of modify_map_def split:if_splits)
 apply (rule_tac x = cref in exI)
 apply (intro conjI impI)
   apply clarsimp+
  done


lemma maskedAsFull_simps[simp]:
  "maskedAsFull capability.NullCap cap =  capability.NullCap"
  by (auto simp:maskedAsFull_def)

lemma cteInsert_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest s\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: cteInsert_def split del: split_if)
  apply (wp updateCap_iflive' hoare_drop_imps)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (wp hoare_vcg_conj_lift hoare_vcg_ex_lift hoare_vcg_ball_lift getCTE_wp
    setUntypedCapAsFull_ctes_of setUntypedCapAsFull_if_live_then_nonz_cap')
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (intro conjI)
  apply (rule_tac x = "case (ctes_of s dest) of Some a \<Rightarrow>a" in exI)
    apply (intro conjI impI)
    apply (clarsimp)
    apply (case_tac cte,simp)
  apply clarsimp+
  done

lemma ifunsafe'_def2:
  "if_unsafe_then_cap' =
    (\<lambda>s. \<forall>cref cte. ctes_of s cref = Some cte \<and> cteCap cte \<noteq> NullCap
              \<longrightarrow> (\<exists>cref' cte'. ctes_of s cref' = Some cte'
                                  \<and> cref \<in> cte_refs' (cteCap cte') (irq_node' s)))"
  by (clarsimp intro!: ext
                 simp: if_unsafe_then_cap'_def cte_wp_at_ctes_of
                       ex_cte_cap_to'_def)

lemma ifunsafe'_def3:
  "if_unsafe_then_cap' =
    (\<lambda>s. \<forall>cref cap. cteCaps_of s cref = Some cap \<and> cap \<noteq> NullCap
              \<longrightarrow> (\<exists>cref' cap'. cteCaps_of s cref' = Some cap'
                          \<and> cref \<in> cte_refs' cap' (irq_node' s)))"
  apply (simp add: cteCaps_of_def o_def ifunsafe'_def2)
  apply (fastforce intro!: ext)
  done

lemma tree_cte_cteCap_eq:
  "cte_wp_at' (P \<circ> cteCap) p s = (case_option False P (cteCaps_of s p))"
  apply (simp add: cte_wp_at_ctes_of cteCaps_of_def)
  apply (cases "ctes_of s p", simp_all)
  done

lemma updateMDB_cteCaps_of:
  "\<lbrace>\<lambda>s. P (cteCaps_of s)\<rbrace> updateMDB ptr f \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (wp updateMDB_ctes_of_wp)
  apply (safe elim!: rsubst [where P=P] intro!: ext)
  apply (case_tac "ctes_of s x")
   apply (clarsimp simp: modify_map_def)+
  done

lemma setCTE_ksInterruptState[wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setCTE param_a param_b \<lbrace>\<lambda>_ s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_cte_inv | simp add: setCTE_def)+

crunch ksInterruptState[wp]: cteInsert "\<lambda>s. P (ksInterruptState s)"
  (ignore: setObject wp: crunch_wps)

lemmas updateMDB_cteCaps_of_ksInt[wp]
    = hoare_use_eq [where f=ksInterruptState, OF updateMDB_ksInterruptState updateMDB_cteCaps_of]

lemma updateCap_cteCaps_of:
  "\<lbrace>\<lambda>s. P (modify_map (cteCaps_of s) ptr (K cap))\<rbrace> updateCap ptr cap \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (wp updateCap_ctes_of_wp)
  apply (erule rsubst [where P=P])
  apply (case_tac "ctes_of s ptr")
   apply (clarsimp intro!: ext simp: modify_map_def)+
  done

lemmas updateCap_cteCaps_of_int[wp]
    = hoare_use_eq[where f=ksInterruptState, OF updateCap_ksInterruptState updateCap_cteCaps_of]

lemma getCTE_cteCap_wp:
  "\<lbrace>\<lambda>s. case (cteCaps_of s ptr) of None \<Rightarrow> True | Some cap \<Rightarrow> Q cap s\<rbrace> getCTE ptr \<lbrace>\<lambda>rv. Q (cteCap rv)\<rbrace>"
  apply (wp getCTE_wp)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of)
  done

lemma capFreeIndex_update_cte_refs'[simp]:
  "isUntypedCap a \<Longrightarrow> cte_refs' (capFreeIndex_update f a) = cte_refs' a "
  apply (rule ext)
  apply (clarsimp simp:isCap_simps)
  done

lemma cteInsert_ifunsafe'[wp]:
  "\<lbrace>if_unsafe_then_cap' and cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest
        and ex_cte_cap_to' dest\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp add: ifunsafe'_def3 cteInsert_def setUntypedCapAsFull_def
             split del: split_if)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of ex_cte_cap_to'_def
                        cteCaps_of_def
                 dest!: modify_map_K_D
                 split: split_if_asm)
  apply (intro conjI)
    apply clarsimp
    apply (erule_tac x = crefa in allE)
    apply (clarsimp simp:modify_map_def split:split_if_asm)
      apply (rule_tac x = cref in exI)
     apply fastforce
    apply (clarsimp simp:isCap_simps)
    apply (rule_tac x = cref' in exI)
     apply fastforce
  apply (intro conjI impI)
   apply clarsimp
   apply (rule_tac x = cref' in exI)
     apply fastforce
  apply (clarsimp simp:modify_map_def)
  apply (erule_tac x = crefa in allE)
  apply (intro conjI impI)
    apply clarsimp
    apply (rule_tac x = cref in exI)
     apply fastforce
    apply (clarsimp simp:isCap_simps)
    apply (rule_tac x = cref' in exI)
     apply fastforce
done

lemma setCTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> setCTE ptr v \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb')
   apply (simp_all add: inQ_def)
  done

lemma setCTE_valid_queues'[wp]:
  "\<lbrace>valid_queues'\<rbrace> setCTE p cte \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp only: valid_queues'_def imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

crunch inQ[wp]: cteInsert "\<lambda>s. P (obj_at' (inQ d p) t s)"
  (wp: crunch_wps)

lemma setCTE_it'[wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setCTE c p \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def updateObject_cte)
  apply (wp|wpc|simp add: unless_def)+
  done

lemma setCTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> setCTE p cte \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: valid_idle'_def)
  apply (rule hoare_lift_Pf [where f="ksIdleThread"])
   apply (wp setCTE_st_tcb_at')
  done

crunch it[wp]: getCTE "\<lambda>s. P (ksIdleThread s)"

lemma getCTE_no_idle_cap:
  "\<lbrace>valid_global_refs'\<rbrace>
   getCTE p
   \<lbrace>\<lambda>rv s. ksIdleThread s \<notin> capRange (cteCap rv)\<rbrace>"
  apply (wp getCTE_wp)
  apply (clarsimp simp: valid_global_refs'_def valid_refs'_def cte_wp_at_ctes_of)
  apply blast
  done

lemma updateMDB_idle'[wp]:
 "\<lbrace>valid_idle'\<rbrace> updateMDB p m \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (clarsimp simp add: updateMDB_def)
  apply (rule hoare_pre)
  apply (wp | simp add: valid_idle'_def)+
  done

lemma updateCap_idle':
 "\<lbrace>valid_idle'\<rbrace> updateCap p c \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: updateCap_def)
  apply (wp | simp)+
  done

crunch idle [wp]: setUntypedCapAsFull "valid_idle'"
  (wp: crunch_wps simp: cte_wp_at_ctes_of)

lemma cteInsert_idle'[wp]:
 "\<lbrace>valid_idle'\<rbrace> cteInsert cap src dest \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: cteInsert_def)
  apply (wp updateMDB_idle' updateCap_idle' | rule hoare_drop_imp | simp)+
  done

lemma setCTE_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setCTE p c \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def updateObject_cte)
  apply (wp|wpc|simp add: unless_def)+
  done

lemma setCTE_valid_arch[wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setCTE p c \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (wp valid_arch_state_lift' setCTE_typ_at')

lemma setCTE_global_refs[wp]:
  "\<lbrace>\<lambda>s. P (global_refs' s)\<rbrace> setCTE p c \<lbrace>\<lambda>_ s. P (global_refs' s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def updateObject_cte global_refs'_def)
  apply (wp|wpc|simp add: unless_def)+
  done

lemma setCTE_valid_globals[wp]:
  "\<lbrace>valid_global_refs' and (\<lambda>s. kernel_data_refs \<inter> capRange (cteCap c) = {})\<rbrace>
  setCTE p c
  \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_refs'_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=global_refs'])
   apply wp
   apply (clarsimp simp: ran_def)
   apply (case_tac "a = p", clarsimp)
   apply fastforce
  apply wp
  done

lemma updateMDB_global_refs [wp]:
 "\<lbrace>valid_global_refs'\<rbrace> updateMDB p m \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (clarsimp simp add: updateMDB_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of valid_global_refs'_def valid_refs'_def)
  apply blast
  done

lemma updateCap_global_refs [wp]:
 "\<lbrace>valid_global_refs' and (\<lambda>s. kernel_data_refs \<inter> capRange cap = {})\<rbrace>
  updateCap p cap
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (clarsimp simp add: updateCap_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

crunch arch [wp]: cteInsert "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps simp: cte_wp_at_ctes_of)

lemma cteInsert_valid_arch [wp]:
 "\<lbrace>valid_arch_state'\<rbrace> cteInsert cap src dest \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  by (rule valid_arch_state_lift') wp

lemma cteInsert_valid_irq_handlers'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_handlers' s \<and> (\<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def cteInsert_def
                   irq_issued'_def setUntypedCapAsFull_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (intro conjI impI)
    apply (clarsimp simp:ran_dom modify_map_dom)
    apply (drule bspec)
      apply fastforce
    apply (clarsimp simp:isCap_simps modify_map_def split:if_splits)
  apply (clarsimp simp:ran_dom modify_map_dom)
  apply (drule bspec)
    apply fastforce
  apply (clarsimp simp:modify_map_def split:if_splits)
done

lemma setCTE_valid_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> setCTE x y \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (wp valid_pde_mappings_lift' setCTE_typ_at')
  apply (simp add: setCTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_cte typeError_def in_monad
                 split: Structures_H.kernel_object.split_asm split_if_asm)
  done

crunch pde_mappings' [wp]: cteInsert valid_pde_mappings'
  (wp: crunch_wps)

lemma setCTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> setCTE x y \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (rule valid_irq_states_lift')
  apply wp
  apply (simp add: setCTE_def)
  apply (wp setObject_ksMachine)
  apply (simp add: updateObject_cte)
  apply (rule hoare_pre)
  apply (wp hoare_unless_wp|wpc|simp)+
  apply fastforce
  done

crunch irq_states' [wp]: cteInsert valid_irq_states'
  (wp: crunch_wps)

crunch st_tcb_at'[wp]: cteInsert "st_tcb_at' P t"
  (wp: crunch_wps)

lemma setCTE_cteCaps_of[wp]:
  "\<lbrace>\<lambda>s. P ((cteCaps_of s)(p \<mapsto> cteCap cte))\<rbrace>
      setCTE p cte
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply wp
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  done

crunch inQ[wp]: setupReplyMaster "\<lambda>s. P (obj_at' (inQ d p) t s)"
  (wp: crunch_wps)
crunch norq[wp]: setupReplyMaster "\<lambda>s. P (ksReadyQueues s)"
  (wp: crunch_wps)
crunch ct[wp]: setupReplyMaster "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps)
crunch state_refs_of'[wp]: setupReplyMaster "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps)
crunch it[wp]: setupReplyMaster "\<lambda>s. P (ksIdleThread s)"
  (wp: setCTE_it')
crunch nosch[wp]: setupReplyMaster "\<lambda>s. P (ksSchedulerAction s)"
crunch irq_node'[wp]: setupReplyMaster "\<lambda>s. P (irq_node' s)"
  (ignore: updateObject)

lemmas setCTE_cteCap_wp_irq[wp] =
    hoare_use_eq_irq_node' [OF setCTE_irq_node' setCTE_cteCaps_of]

crunch global_refs'[wp]: setUntypedCapAsFull "\<lambda>s. P (global_refs' s) "
  (simp: crunch_simps)

lemma setUntypedCapAsFull_valid_refs'[wp]:
  "\<lbrace>\<lambda>s. valid_refs' R (ctes_of s) \<and> cte_wp_at' (op = srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>yb s. valid_refs' R (ctes_of s)\<rbrace>"
  apply (clarsimp simp:valid_refs'_def setUntypedCapAsFull_def split del:if_splits)
  apply (rule hoare_pre)
  apply (wp updateCap_ctes_of_wp)
  apply (clarsimp simp:ran_dom)
  apply (drule_tac x = y in bspec)
    apply (drule_tac a = y in domI)
    apply (simp add:modify_map_dom)
  apply (clarsimp simp:modify_map_def cte_wp_at_ctes_of
    isCap_simps split:if_splits)
done

lemma setUntypedCapAsFull_valid_global_refs'[wp]:
  "\<lbrace>\<lambda>s. valid_global_refs' s \<and> cte_wp_at' (op = srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>yb s. valid_global_refs' s\<rbrace>"
  apply (clarsimp simp: valid_global_refs'_def)
  apply (rule hoare_pre,wps)
  apply wp
  apply simp
done

lemma cteInsert_valid_globals [wp]:
 "\<lbrace>valid_global_refs' and (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: cteInsert_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of is_derived'_def badge_derived'_def)
  apply (drule capMaster_capRange)
  apply (drule (1) valid_global_refsD')
  apply simp
  done

crunch arch [wp]: cteInsert "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps simp: cte_wp_at_ctes_of)

crunch pde_mappings' [wp]: cteInsert valid_pde_mappings'
  (wp: crunch_wps)

lemma setCTE_ksMachine[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setCTE x y \<lbrace>\<lambda>_ s. P (ksMachineState s)\<rbrace>"
  apply (clarsimp simp: setCTE_def)
  apply (wp setObject_ksMachine)
  apply (clarsimp simp: updateObject_cte
                 split: Structures_H.kernel_object.splits)
  apply (safe, (wp hoare_unless_wp | simp)+)
  done

crunch ksMachine[wp]: cteInsert "\<lambda>s. P (ksMachineState s)"
  (wp: crunch_wps)

lemma cteInsert_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> cteInsert cap src dest \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: cteInsert_def valid_machine_state'_def pointerInUserData_def)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift)
   apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv |
          intro hoare_drop_imp)+
  done

crunch pspace_domain_valid[wp]: cteInsert "pspace_domain_valid"
  (wp: crunch_wps)

lemma setCTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setCTE ptr cte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF setCTE_nosch])
  apply (simp add: setCTE_def ct_not_inQ_def)
  apply (rule hoare_weaken_pre)
  apply (wps setObject_cte_ct)
  apply (rule setObject_cte_obj_at_tcb')
       apply (clarsimp simp add: obj_at'_def)+
  done

crunch ct_not_inQ[wp]: cteInsert "ct_not_inQ"
  (simp: crunch_simps wp: hoare_drop_imp)

lemma setCTE_ksCurDomain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>
      setCTE p cte
   \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setCTE_def)
  apply wp
  done

lemma setObject_cte_ksDomSchedule[wp]: "\<lbrace> \<lambda>s. P (ksDomSchedule s) \<rbrace> setObject ptr (v::cte) \<lbrace> \<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_cte_inv | simp)+
  done

lemma setCTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>
      setCTE p cte
   \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setCTE_def)
  apply wp
  done

crunch ksCurDomain[wp]: cteInsert "\<lambda>s. P (ksCurDomain s)"
  (wp:  crunch_wps )

crunch ksIdleThread[wp]: cteInsert "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps)

crunch ksDomSchedule[wp]: cteInsert "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps)

lemma setCTE_tcbDomain_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t\<rbrace> setCTE ptr v \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

crunch tcbDomain_inv[wp]: cteInsert "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  (wp: crunch_simps hoare_drop_imps)

lemma setCTE_tcbPriority_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace> setCTE ptr v \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

crunch tcbPriority_inv[wp]: cteInsert "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"
  (wp: crunch_simps hoare_drop_imps)


lemma cteInsert_ct_idle_or_in_cur_domain'[wp]: "\<lbrace> ct_idle_or_in_cur_domain' \<rbrace> cteInsert a b c \<lbrace> \<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
  apply (wp hoare_vcg_disj_lift)
  done

lemma setObject_cte_domIdx:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject t (v::cte) \<lbrace>\<lambda>rv s. P (ksDomScheduleIdx s)\<rbrace>"
  by (clarsimp simp: valid_def setCTE_def[symmetric] dest!: setCTE_pspace_only)

crunch ksDomScheduleIdx[wp]: cteInsert "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: setObject_cte_domIdx hoare_drop_imps ignore: setObject)

lemma cteInsert_invs:
 "\<lbrace>invs' and cte_wp_at' (\<lambda>c. cteCap c=NullCap) dest and valid_cap' cap and
  (\<lambda>s. src \<noteq> dest) and (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)
  and ex_cte_cap_to' dest and (\<lambda>s. \<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wp cur_tcb_lift tcb_in_cur_domain'_lift sch_act_wf_lift CSpace_R.valid_queues_lift
            valid_irq_node_lift valid_queues_lift' irqs_masked_lift
            cteInsert_norq | simp add: st_tcb_at'_def)+
  apply (auto simp: invs'_def valid_state'_def valid_pspace'_def elim: valid_capAligned)
  done

lemma derive_cap_corres:
 "\<lbrakk>cap_relation c c'; cte = cte_map slot \<rbrakk> \<Longrightarrow>
  corres (ser \<oplus> cap_relation)
         (cte_at slot)
         (pspace_aligned' and pspace_distinct' and cte_at' cte and valid_mdb')
         (derive_cap slot c) (deriveCap cte c')"
  apply (unfold derive_cap_def deriveCap_def)
  apply (case_tac c)
            apply (simp_all add: returnOk_def Let_def is_zombie_def isCap_simps
                          split: sum.splits)
   apply (rule corres_initial_splitE [OF ensure_no_children_corres])
      apply simp
     apply clarsimp
    apply wp
  apply clarsimp
  apply (rule corres_rel_imp)
   apply (rule corres_guard_imp)
     apply (rule arch_derive_corres)
     apply (clarsimp simp: o_def)+
  done

lemma deriveCap_inv[wp]:
  "\<lbrace>P\<rbrace> deriveCap cte c \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (case_tac c, simp_all add: deriveCap_def ensureNoChildren_def whenE_def
    isCap_simps Let_def, wp)
     apply clarsimp
     apply (wp  arch_deriveCap_inv | simp)+
  done

lemma lookup_cap_valid':
  "\<lbrace>valid_objs'\<rbrace> lookupCap t c \<lbrace>valid_cap'\<rbrace>, -"
  apply (simp add: lookupCap_def lookupCapAndSlot_def
                   lookupSlotForThread_def split_def)
  apply (wp | simp)+
  done

lemma capAligned_Null [simp]:
  "capAligned NullCap"
  by (simp add: capAligned_def is_aligned_def word_bits_def)

lemma guarded_lookup_valid_cap':
  "\<lbrace> valid_objs' \<rbrace> nullCapOnFailure (lookupCap t c) \<lbrace>\<lambda>rv. valid_cap' rv \<rbrace>"
  apply (simp add: nullCapOnFailure_def)
  apply wp
  apply (simp add: valid_cap'_def)
  apply (fold validE_R_def)
  apply (rule lookup_cap_valid')
  done

lemma setObject_tcb_tcb':
  "\<lbrace>tcb_at' p\<rbrace> setObject p (t::tcb) \<lbrace>\<lambda>rv. tcb_at' p\<rbrace>"
  apply (rule obj_at_setObject1)
    apply (simp add: updateObject_default_def in_monad)
   apply (simp add: projectKOs)
  apply (simp add: objBits_simps)
  done

lemma cte_wp_at'_conjI:
  "\<lbrakk> cte_wp_at' P p s; cte_wp_at' Q p s \<rbrakk> \<Longrightarrow> cte_wp_at' (\<lambda>c. P c \<and> Q c) p s"
  by (auto simp add: cte_wp_at'_def)

crunch inv'[wp]: rangeCheck "P"
  (simp: crunch_simps)

lemma lookupSlotForCNodeOp_inv'[wp]:
  "\<lbrace>P\<rbrace> lookupSlotForCNodeOp src root ptr depth \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: lookupSlotForCNodeOp_def split_def unlessE_def
             cong: if_cong split del: split_if)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps)
  apply simp
  done

lemma unifyFailure_inv [wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> unifyFailure f \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding unifyFailure_def
  apply (simp add: rethrowFailure_def const_def o_def)
  apply wp
  apply simp
  done

(* FIXME: move *)
lemma loadWordUser_inv [wp]:
  "\<lbrace>P\<rbrace> loadWordUser p \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding loadWordUser_def
  by (wp dmo_inv' loadWord_inv)

lemma capTransferFromWords_inv:
  "\<lbrace>P\<rbrace> capTransferFromWords buffer \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: capTransferFromWords_def)
  apply wp
  done

lemma lct_inv' [wp]:
  "\<lbrace>P\<rbrace> loadCapTransfer b \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding loadCapTransfer_def
  apply (wp capTransferFromWords_inv)
  done

lemma maskCapRightsNull [simp]:
  "maskCapRights R NullCap = NullCap"
  by (simp add: maskCapRights_def isCap_defs)

lemma maskCapRightsUntyped [simp]:
  "maskCapRights R (UntypedCap r n f) = UntypedCap r n f"
  by (simp add: maskCapRights_def isCap_defs Let_def)

lemma maskCapRightsZombie [simp]:
  "maskCapRights R (Zombie p b n) = Zombie p b n"
  by (simp add: maskCapRights_def isCap_defs Let_def)

(* FIXME: move *)
lemma cap_relation_update_masks:
  "cap_relation a c'
   \<Longrightarrow> cap_relation
         (cap_rights_update (cap_rights a - {AllowWrite}) a)
         (maskCapRights (capAllowWrite_update (\<lambda>_. False) allRights) c')"
  apply (drule_tac rmask="UNIV - {AllowWrite}" in cap_relation_masks)
  by (simp add: rights_mask_map_def allRights_def)

declare if_option_Some[simp]

lemma lookup_cap_corres:
  "\<lbrakk> epcptr = to_bl epcptr' \<rbrakk> \<Longrightarrow>
   corres (lfr \<oplus> cap_relation)
     (valid_objs and pspace_aligned and tcb_at thread)
     (valid_objs' and pspace_distinct' and pspace_aligned' and tcb_at' thread)
     (lookup_cap thread epcptr)
     (lookupCap thread epcptr')"
  apply (simp add: lookup_cap_def lookupCap_def lookupCapAndSlot_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE [OF _ lookup_slot_corres])
      apply (simp add: split_def)
      apply (subst bindE_returnOk[symmetric])
      apply (rule corres_splitEE)
         prefer 2
         apply simp
         apply (rule getSlotCap_corres, rule refl)
        apply (rule corres_returnOk [of _ \<top> \<top>])
        apply simp
     apply wp
   apply auto
  done

lemma ensureNoChildren_inv[wp]:
  "\<lbrace>P\<rbrace> ensureNoChildren ptr \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: ensureNoChildren_def whenE_def)
  apply (wp hoare_drop_imps)
  apply auto
  done

lemma ensure_empty_corres:
  "q = cte_map p \<Longrightarrow>
   corres (ser \<oplus> dc) (invs and cte_at p) invs'
                     (ensure_empty p) (ensureEmptySlot q)"
  apply (clarsimp simp add: ensure_empty_def ensureEmptySlot_def unlessE_whenE liftE_bindE)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_cap_corres])
      apply (rule corres_trivial)
      apply (case_tac cap, auto simp add: whenE_def returnOk_def)[1]
     apply wp
   apply (clarsimp simp: invs_valid_objs invs_psp_aligned)
  apply fastforce
  done

lemma ensureEmpty_inv[wp]:
  "\<lbrace>P\<rbrace> ensureEmptySlot p \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: ensureEmptySlot_def unlessE_whenE whenE_def | wp)+

lemma lsfc_corres:
  "\<lbrakk>cap_relation c c'; ptr = to_bl ptr'\<rbrakk>
  \<Longrightarrow> corres (ser \<oplus> (\<lambda>cref cref'. cref' = cte_map cref))
            (valid_objs and pspace_aligned and valid_cap c)
            (valid_objs' and pspace_aligned' and pspace_distinct' and valid_cap' c')
            (lookup_slot_for_cnode_op s c ptr depth)
            (lookupSlotForCNodeOp s c' ptr' depth)"
  apply (simp add: lookup_slot_for_cnode_op_def lookupSlotForCNodeOp_def)
  apply (clarsimp simp: lookup_failure_map_def split_def word_size)
  apply (clarsimp simp: rangeCheck_def[unfolded fun_app_def unlessE_def] whenE_def
                        word_bits_def toInteger_nat fromIntegral_def fromInteger_nat)
  apply (rule corres_lookup_error)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE [OF _ rab_corres'])
         apply (rule corres_trivial)
         apply (clarsimp simp: returnOk_def lookup_failure_map_def
                         split: list.split)
        apply simp+
     apply wp
   apply clarsimp
  apply clarsimp
  done

(* this helper characterisation of ctes_of
   is needed in CNodeInv and Untyped *)

lemma ensureNoChildren_wp:
  "\<lbrace>\<lambda>s. Q s \<and> (descendants_of' p (ctes_of s) = {} \<longrightarrow> P () s)\<rbrace> ensureNoChildren p \<lbrace>P\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>"
  apply (simp add: ensureNoChildren_def whenE_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of nullPointer_def descendants_of'_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule (4) subtree_no_parent)
  apply clarsimp
  apply (erule (2) subtree_next_0)
  done

lemma set_cap_pspace_corres:
  "cap_relation cap (cteCap cte) \<Longrightarrow>
   corres_underlying {(s, s'). pspace_relations (ekheap (s)) (kheap s) (ksPSpace s')} True dc
      (pspace_distinct and pspace_aligned and valid_objs and cte_at p)
      (pspace_aligned' and pspace_distinct' and cte_at' (cte_map p))
      (set_cap cap p)
      (setCTE (cte_map p) cte)"
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply simp
  apply clarsimp
  apply (drule(8) set_cap_not_quite_corres_prequel)
   apply simp
  apply fastforce
  done

(* FIXME: move to StateRelation *)
lemma ghost_relation_of_heap:
  "ghost_relation h ups cns \<longleftrightarrow> ups_of_heap h = ups \<and> cns_of_heap h = cns"
  apply (rule iffI)
   apply (rule conjI)
    apply (rule ext)
    apply (clarsimp simp add: ghost_relation_def ups_of_heap_def)
    apply (drule_tac x=x in spec)
    apply (auto simp add: ghost_relation_def ups_of_heap_def
                split: option.splits Structures_A.kernel_object.splits
                       arch_kernel_obj.splits)[1]
   apply (rule ext)
   apply (clarsimp simp add: ghost_relation_def cns_of_heap_def)
   apply (drule_tac x=x in spec)+
   apply (rule ccontr)
   apply (simp split: option.splits Structures_A.kernel_object.splits
                      arch_kernel_obj.splits)[1]
   apply (simp split: split_if_asm)
    apply force
   apply (drule not_sym)
   apply clarsimp
   apply (erule_tac x=y in allE)
   apply simp
  apply (auto simp add: ghost_relation_def ups_of_heap_def cns_of_heap_def
              split: option.splits Structures_A.kernel_object.splits
                     arch_kernel_obj.splits split_if_asm)
  done

lemma corres_caps_decomposition:
  assumes x: "corres_underlying {(s, s'). pspace_relations (ekheap (s)) (kheap s) (ksPSpace s')} True r P P' f g"
  assumes u: "\<And>P. \<lbrace>\<lambda>s. P (new_caps s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_mdb s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_list s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cdt_list (s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_rvk s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ctes s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ms s)\<rbrace> f \<lbrace>\<lambda>rv s. P (machine_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ms' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_wuc s)\<rbrace> f \<lbrace>\<lambda>rv s. P (work_units_completed s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_wuc' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksWorkUnitsCompleted s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ct s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ct' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_as s)\<rbrace> f \<lbrace>\<lambda>rv s. P (arch_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_as' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_id s)\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_id' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqn s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqs s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_states s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqs' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ups s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ups_of_heap (kheap s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ups' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (gsUserPages s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cns s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cns_of_heap (kheap s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cns' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (gsCNodes s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_sa' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_rqs' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_di s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_index s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dl s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cd s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dt s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dsi' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomScheduleIdx s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ds' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cd' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dt' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomainTime s)\<rbrace>"
  assumes z: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> cdt_relation (op \<noteq> None \<circ> new_caps s) (new_mdb s) (new_ctes s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> cdt_list_relation (new_list s) (new_mdb s) (new_ctes s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> sched_act_relation (new_action s) (new_sa' s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> ready_queues_relation (new_queues s) (new_rqs' s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> revokable_relation (new_rvk s) (null_filter (new_caps s)) (new_ctes s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> (new_as s, new_as' s') \<in> arch_state_relation
                            \<and> interrupt_state_relation (new_irqn s) (new_irqs s) (new_irqs' s')
                            \<and> new_ct s = new_ct' s' \<and> new_id s = new_id' s'
                            \<and> new_ms s = new_ms' s' \<and> new_di s = new_dsi' s'
                            \<and> new_dl s = new_ds' s' \<and> new_cd s = new_cd' s' \<and> new_dt s = new_dt' s' \<and> new_wuc s = new_wuc' s'"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> new_ups s = new_ups' s'"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> new_cns s = new_cns' s'"
  shows "corres r P P' f g"
proof -
  have all_ext: "\<And>f f'. (\<forall>p. f p = f' p) = (f = f')"
    by (fastforce intro!: ext)
  have mdb_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. cdt_relation (op \<noteq> None \<circ> new_caps s) (new_mdb s) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. \<exists>m ca. (\<forall>p. ca p = (op \<noteq> None \<circ> caps_of_state s) p) \<and> m = cdt s
                            \<and> cdt_relation ca m ctes\<rbrace>"
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift u)
    apply (subst all_ext)
    apply (simp add: o_def)
    done
  note mdb_wp = mdb_wp' [simplified all_ext simp_thms]
  have list_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. cdt_list_relation (new_list s) (new_mdb s) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. \<exists>m t. t = cdt_list s \<and> m = cdt s
                            \<and> cdt_list_relation t m ctes\<rbrace>"
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift u)
    apply (simp add: o_def)
    done
  note list_wp = list_wp' [simplified all_ext simp_thms]
  have rvk_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. revokable_relation (new_rvk s) (null_filter (new_caps s)) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) ctes\<rbrace>"
    unfolding revokable_relation_def
    apply (simp only: imp_conv_disj)
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_disj_lift u)
    done
  have exs_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. revokable_relation (new_rvk s) (null_filter (new_caps s)) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) ctes\<rbrace>"
    unfolding revokable_relation_def
    apply (simp only: imp_conv_disj)
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_disj_lift u)
    done
  note rvk_wp = rvk_wp' [simplified all_ext simp_thms]
  have swp_cte_at:
    "\<And>s. swp cte_at s = (op \<noteq> None \<circ> caps_of_state s)"
    by (rule ext, simp, subst neq_commute, simp add: cte_wp_at_caps_of_state)
  have abs_irq_together':
    "\<And>P. \<lbrace>\<lambda>s. P (new_irqn s) (new_irqs s)\<rbrace> f
             \<lbrace>\<lambda>rv s. \<exists>irn. interrupt_irq_node s = irn \<and> P irn (interrupt_states s)\<rbrace>"
    by (wp hoare_vcg_ex_lift u, simp)
  note abs_irq_together = abs_irq_together'[simplified]
  show ?thesis
    unfolding state_relation_def swp_cte_at
    apply (subst conj_assoc[symmetric])
    apply (subst pspace_relations_def[symmetric])
    apply (rule corres_underlying_decomposition [OF x])
     apply (simp add: ghost_relation_of_heap)
     apply (wp hoare_vcg_conj_lift mdb_wp rvk_wp list_wp u abs_irq_together)
    apply (intro z[simplified o_def] conjI | simp add: state_relation_def pspace_relations_def swp_cte_at
          | (clarsimp, drule (1) z(6), simp add: state_relation_def pspace_relations_def swp_cte_at))+
    done
qed

lemma getCTE_symb_exec_r:
  "corres_underlying sr nf dc \<top> (cte_at' p) (return ()) (getCTE p)"
  apply (rule corres_no_failI, wp)
  apply (clarsimp simp: return_def
                 elim!: use_valid [OF _ getCTE_inv])
  done

lemma updateMDB_symb_exec_r:
  "corres_underlying {(s, s'). pspace_relations (ekheap s) (kheap s) (ksPSpace s')} nf dc
        \<top> (pspace_aligned' and pspace_distinct' and (no_0 \<circ> ctes_of) and (\<lambda>s. p \<noteq> 0 \<longrightarrow> cte_at' p s))
        (return ()) (updateMDB p m)"
  using no_fail_updateMDB [of p m]
  apply (clarsimp simp: corres_underlying_def return_def no_fail_def)
  apply (drule(1) updateMDB_the_lot, simp, assumption+)
  apply clarsimp
  done

lemma updateMDB_ctes_of_cases:
  "\<lbrace>\<lambda>s. P (modify_map (ctes_of s) p (if p = 0 then id else cteMDBNode_update f))\<rbrace>
     updateMDB p f \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: updateMDB_def split del: split_if)
  apply (rule hoare_pre, wp getCTE_ctes_of)
  apply (clarsimp simp: modify_map_def map_option_case
                 split: option.split
          | rule conjI ext | erule rsubst[where P=P])+
  apply (case_tac y, simp)
  done

crunch ct[wp]: updateMDB "\<lambda>s. P (ksCurThread s)"

lemma setCTE_state_bits[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  "\<lbrace>\<lambda>s. Q (ksIdleThread s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. Q (ksIdleThread s)\<rbrace>"
  "\<lbrace>\<lambda>s. R (ksArchState s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. R (ksArchState s)\<rbrace>"
  "\<lbrace>\<lambda>s. S (ksInterruptState s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. S (ksInterruptState s)\<rbrace>"
  apply (simp_all add: setCTE_def setObject_def split_def)
  apply (wp updateObject_cte_inv | simp)+
  done

crunch ms'[wp]: updateMDB "\<lambda>s. P (ksMachineState s)"
crunch idle'[wp]: updateMDB "\<lambda>s. P (ksIdleThread s)"
crunch arch'[wp]: updateMDB "\<lambda>s. P (ksArchState s)"
crunch int'[wp]: updateMDB "\<lambda>s. P (ksInterruptState s)"

lemma cte_map_eq_subst:
  "\<lbrakk> cte_at p s; cte_at p' s; valid_objs s; pspace_aligned s; pspace_distinct s \<rbrakk>
     \<Longrightarrow> (cte_map p = cte_map p') = (p = p')"
  by (fastforce elim!: cte_map_inj_eq)

lemma revokable_relation_simp:
  "\<lbrakk> (s, s') \<in> state_relation; null_filter (caps_of_state s) p = Some c; ctes_of s' (cte_map p) = Some (CTE cap node) \<rbrakk>
      \<Longrightarrow> mdbRevocable node = is_original_cap s p"
  apply (cases p, clarsimp simp: state_relation_def revokable_relation_def)
  apply (elim allE, erule impE, erule exI)
  apply (elim allE, erule (1) impE)
  apply simp
  done

lemma setCTE_gsUserPages[wp]:
  "\<lbrace>\<lambda>s. P (gsUserPages s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. P (gsUserPages s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def)
  apply (wp updateObject_cte_inv crunch_wps | simp)+
  done

lemma setCTE_gsCNodes[wp]:
  "\<lbrace>\<lambda>s. P (gsCNodes s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. P (gsCNodes s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def)
  apply (wp updateObject_cte_inv crunch_wps | simp)+
  done

lemma set_original_symb_exec_l':
  "corres_underlying {(s, s'). f (ekheap s) (kheap s) s'} nf dc P P' (set_original p b) (return x)"
  by (simp add: corres_underlying_def return_def set_original_def in_monad Bex_def)

lemma setCTE_schedule_index[wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. P (ksDomScheduleIdx s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def)
  apply (wp updateObject_cte_inv crunch_wps | simp)+
  done

lemma setCTE_schedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def)
  apply (wp updateObject_cte_inv crunch_wps | simp)+
  done

lemma setCTE_domain_time[wp]:
  "\<lbrace>\<lambda>s. P (ksDomainTime s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. P (ksDomainTime s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def)
  apply (wp updateObject_cte_inv crunch_wps | simp)+
  done

lemma setCTE_work_units_completed[wp]:
  "\<lbrace>\<lambda>s. P (ksWorkUnitsCompleted s)\<rbrace> setCTE p v \<lbrace>\<lambda>_ s. P (ksWorkUnitsCompleted s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def)
  apply (wp updateObject_cte_inv crunch_wps | simp)+
  done

lemma create_reply_master_corres:
  "sl' = cte_map sl \<Longrightarrow>
   corres dc
      (cte_wp_at (op = cap.NullCap) sl and valid_pspace and valid_mdb and valid_list)
      (cte_wp_at' (\<lambda>c. cteCap c = NullCap \<and> mdbPrev (cteMDBNode c) = 0) sl'
       and valid_mdb' and valid_pspace')
      (do
         y \<leftarrow> set_original sl True;
         set_cap (cap.ReplyCap thread True) sl
       od)
      (setCTE sl' (CTE (capability.ReplyCap thread True) initMDBNode))"
  apply clarsimp
  apply (rule corres_caps_decomposition)
                                 defer
                                 apply (wp|simp)+
          apply (clarsimp simp: o_def cdt_relation_def cte_wp_at_ctes_of
                     split del: split_if cong: if_cong simp del: id_apply)
          apply (case_tac cte, clarsimp)
          apply (fold fun_upd_def)
          apply (subst descendants_of_Null_update')
               apply fastforce
              apply fastforce
             apply assumption
            apply assumption
           apply (simp add: nullPointer_def)
          apply (subgoal_tac "cte_at (a, b) s")
           prefer 2
           apply (drule not_sym, clarsimp simp: cte_wp_at_caps_of_state
                                         split: split_if_asm)
          apply (simp add: state_relation_def cdt_relation_def)
         apply (clarsimp simp: o_def cdt_list_relation_def cte_wp_at_ctes_of
                    split del: split_if cong: if_cong simp del: id_apply)
         apply (case_tac cte, clarsimp)
         apply (clarsimp simp: state_relation_def cdt_list_relation_def)
         apply (simp split: split_if_asm)
         apply (erule_tac x=a in allE, erule_tac x=b in allE)
         apply clarsimp
         apply(case_tac "next_slot (a, b) (cdt_list s) (cdt s)")
          apply(simp)
         apply(simp)
         apply(fastforce simp: valid_mdb'_def valid_mdb_ctes_def valid_nullcaps_def)
        apply (clarsimp simp: state_relation_def)
       apply (clarsimp simp: state_relation_def)
      apply (clarsimp simp add: revokable_relation_def cte_wp_at_ctes_of
                     split del: split_if)
      apply simp
      apply (rule conjI)
       apply (clarsimp simp: initMDBNode_def)
      apply clarsimp
      apply (subgoal_tac "null_filter (caps_of_state s) (a, b) \<noteq> None")
       prefer 2
       apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state
                      split: split_if_asm)
      apply (subgoal_tac "cte_at (a,b) s")
       prefer 2
       apply clarsimp
       apply (drule null_filter_caps_of_stateD)
       apply (erule cte_wp_cte_at)
      apply (clarsimp split: split_if_asm cong: conj_cong
                       simp: cte_map_eq_subst revokable_relation_simp
                             cte_wp_at_cte_at valid_pspace_def)
     apply (clarsimp simp: state_relation_def)
    apply (clarsimp elim!: state_relationE simp: ghost_relation_of_heap)+
  apply (rule corres_guard_imp)
    apply (rule corres_underlying_symb_exec_l [OF set_original_symb_exec_l'])
     apply (rule set_cap_pspace_corres)
     apply simp
    apply wp
   apply (clarsimp simp: cte_wp_at_cte_at valid_pspace_def)
  apply (clarsimp simp: valid_pspace'_def cte_wp_at'_def)
  done

lemma cte_map_nat_to_cref:
  "\<lbrakk> n < 2 ^ b; b < 32 \<rbrakk> \<Longrightarrow>
   cte_map (p, nat_to_cref b n) = p + (of_nat n * 16)"
  apply (clarsimp simp: cte_map_def nat_to_cref_def
                 dest!: less_is_drop_replicate)
  apply (rule arg_cong [where f="\<lambda>x. x * 16"])
  apply (subst of_drop_to_bl)
  apply (simp add: word_bits_def)
  apply (subst mask_eq_iff_w2p)
   apply (simp add: word_size)
  apply (simp add: word_less_nat_alt word_size word_bits_def)
  apply (rule order_le_less_trans)
   defer
   apply assumption
  apply (subst unat_of_nat)
  apply (rule mod_le_dividend)
  done

lemma valid_nullcapsE:
  "\<lbrakk> valid_nullcaps m; m p = Some (CTE NullCap n);
    \<lbrakk> mdbPrev n = 0; mdbNext n = 0 \<rbrakk> \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
  by (fastforce simp: valid_nullcaps_def nullMDBNode_def nullPointer_def)

lemma valid_nullcaps_prev:
  "\<lbrakk> m (mdbPrev n) = Some (CTE NullCap n'); m p = Some (CTE c n);
    no_0 m; valid_dlist m; valid_nullcaps m \<rbrakk> \<Longrightarrow> False"
  apply (erule (1) valid_nullcapsE)
  apply (erule_tac p=p in valid_dlistEp, assumption)
   apply clarsimp
  apply clarsimp
  done

lemma valid_nullcaps_next:
  "\<lbrakk> m (mdbNext n) = Some (CTE NullCap n'); m p = Some (CTE c n);
    no_0 m; valid_dlist m; valid_nullcaps m \<rbrakk> \<Longrightarrow> False"
  apply (erule (1) valid_nullcapsE)
  apply (erule_tac p=p in valid_dlistEn, assumption)
   apply clarsimp
  apply clarsimp
  done

defs noReplyCapsFor_def:
  "noReplyCapsFor \<equiv> \<lambda>t s. \<forall>sl m. \<not> cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t m) sl s"

lemma pspace_relation_no_reply_caps:
  assumes pspace: "pspace_relation (kheap s) (ksPSpace s')"
  and       invs: "invs s"
  and        tcb: "tcb_at t s"
  and     m_cte': "cte_wp_at' (op = cte) sl' s'"
  and     m_null: "cteCap cte = capability.NullCap"
  and       m_sl: "sl' = cte_map (t, tcb_cnode_index 2)"
  shows           "noReplyCapsFor t s'"
proof -
  from tcb have m_cte: "cte_at (t, tcb_cnode_index 2) s"
    by (clarsimp elim!: tcb_at_cte_at)
  have m_cte_null:
    "cte_wp_at (\<lambda>c. c = cap.NullCap) (t, tcb_cnode_index 2) s"
    using pspace invs
    apply (frule_tac pspace_relation_cte_wp_atI')
      apply (rule assms)
     apply clarsimp
    apply (clarsimp simp: m_sl)
    apply (frule cte_map_inj_eq)
         apply (rule m_cte)
        apply (erule cte_wp_cte_at)
       apply clarsimp+
    apply (clarsimp elim!: cte_wp_at_weakenE simp: m_null)
    done
  have no_reply_caps:
    "\<forall>sl m. \<not> cte_wp_at (\<lambda>c. c = cap.ReplyCap t m) sl s"
    by (rule no_reply_caps_for_thread [OF invs tcb m_cte_null])
  hence noReplyCaps:
    "\<forall>sl m. \<not> cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t m) sl s'"
    apply (intro allI)
    apply (clarsimp simp: cte_wp_at_neg2 cte_wp_at_ctes_of simp del: split_paired_All)
    apply (frule pspace_relation_cte_wp_atI [OF pspace _ invs_valid_objs [OF invs]])
    apply (clarsimp simp: cte_wp_at_neg2 simp del: split_paired_All)
    apply (drule_tac x="(a, b)" in spec)
    apply (clarsimp simp: cte_wp_cte_at cte_wp_at_caps_of_state)
    apply (case_tac c, simp_all)
    apply fastforce
    done
  thus ?thesis
    by (simp add: noReplyCapsFor_def)
qed

lemma setup_reply_master_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t)
       (setup_reply_master t) (setupReplyMaster t)"
  apply (simp add: setupReplyMaster_def setup_reply_master_def)
  apply (simp add: locateSlot_def tcbReplySlot_def objBits_def objBitsKO_def)
  apply (simp add: nullMDBNode_def, fold initMDBNode_def)
  apply (rule_tac F="t + 0x20 = cte_map (t, tcb_cnode_index 2)"
               in corres_req)
   apply (clarsimp simp: tcb_cnode_index_def2 cte_map_nat_to_cref)
  apply clarsimp
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split [OF _ get_cap_corres])
      apply (rule corres_when)
       apply fastforce
      apply (rule_tac P'="einvs and tcb_at t" in corres_stateAssert_implied)
       apply (rule create_reply_master_corres)
       apply simp
      apply (subgoal_tac "\<exists>cte. cte_wp_at' (op = cte) (cte_map (t, tcb_cnode_index 2)) s'
                              \<and> cteCap cte = capability.NullCap")
       apply (fastforce dest: pspace_relation_no_reply_caps
                             state_relation_pspace_relation)
      apply (clarsimp simp: cte_map_def tcb_cnode_index_def cte_wp_at_ctes_of)
     apply (rule_tac Q="\<lambda>rv. einvs and tcb_at t and
                             cte_wp_at (op = rv) (t, tcb_cnode_index 2)"
                  in hoare_strengthen_post)
      apply (wp hoare_drop_imps get_cap_wp)
     apply (clarsimp simp: invs_def valid_state_def elim!: cte_wp_at_weakenE)
    apply (rule_tac Q="\<lambda>rv. valid_pspace' and valid_mdb' and
                            cte_wp_at' (op = rv) (cte_map (t, tcb_cnode_index 2))"
                 in hoare_strengthen_post)
     apply (wp hoare_drop_imps getCTE_wp')
    apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def)
    apply (case_tac r, fastforce elim: valid_nullcapsE)
   apply (fastforce elim: tcb_at_cte_at)
  apply (clarsimp simp: cte_at'_obj_at' tcb_cte_cases_def cte_map_def)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
  done

crunch tcb'[wp]: setupReplyMaster "tcb_at' t"
  (wp: crunch_wps)

crunch idle'[wp]: setupReplyMaster "valid_idle'"

(* Levity: added (20090126 19:32:14) *)
declare stateAssert_wp [wp]

lemma setupReplyMaster_valid_mdb:
  "slot = t + 2 ^ objBits (undefined :: cte) * tcbReplySlot \<Longrightarrow>
   \<lbrace>valid_mdb' and valid_pspace' and tcb_at' t\<rbrace>
   setupReplyMaster t
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (clarsimp simp: setupReplyMaster_def locateSlot_def
                        nullMDBNode_def)
  apply (fold initMDBNode_def)
  apply (wp setCTE_valid_mdb getCTE_wp')
  apply clarsimp
  apply (intro conjI)
      apply (case_tac cte)
      apply (fastforce simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def
                            no_mdb_def
                      elim: valid_nullcapsE)
     apply (frule obj_at_aligned')
      apply (simp add: valid_cap'_def capAligned_def
                       objBits_def objBitsKO_def word_bits_def)+
    apply (clarsimp simp: valid_pspace'_def)
   apply (clarsimp simp: caps_no_overlap'_def capRange_def)
  apply (clarsimp simp: fresh_virt_cap_class_def
                 elim!: ranE)
  apply (clarsimp simp add: noReplyCapsFor_def cte_wp_at_ctes_of)
  apply (case_tac x)
  apply (case_tac capability, simp_all)
   apply (case_tac arch_capability, simp_all)
  apply fastforce
  done

lemma setupReplyMaster_valid_objs [wp]:
  "\<lbrace> valid_objs' and pspace_aligned' and pspace_distinct' and tcb_at' t\<rbrace>
  setupReplyMaster t
  \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_def)
  apply (wp setCTE_valid_objs getCTE_wp')
  apply (clarsimp)
  apply (frule obj_at_aligned')
   apply (simp add: valid_cap'_def capAligned_def
                         objBits_def objBitsKO_def word_bits_def)+
  done

lemma setupReplyMaster_wps[wp]:
  "\<lbrace>pspace_aligned'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  "\<lbrace>pspace_distinct'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  "slot = cte_map (t, tcb_cnode_index 2) \<Longrightarrow>
   \<lbrace>\<lambda>s. P ((cteCaps_of s)(slot \<mapsto> (capability.ReplyCap t True))) \<and> P (cteCaps_of s)\<rbrace>
      setupReplyMaster t
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp_all add: setupReplyMaster_def locateSlot_def)
   apply (wp hoare_drop_imps
            | simp add: o_def
            | rule hoare_strengthen_post [OF getCTE_sp])+
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: tcbReplySlot_def objBits_def objBitsKO_def
                        tcb_cnode_index_def2 cte_map_nat_to_cref)
  done

crunch no_0_obj'[wp]: setupReplyMaster no_0_obj'
  (wp: crunch_wps)

lemma setupReplyMaster_valid_pspace':
  "\<lbrace>valid_pspace' and tcb_at' t\<rbrace>
     setupReplyMaster t
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (wp setupReplyMaster_valid_mdb)
     apply (simp_all add: valid_pspace'_def)
  done

lemma setupReplyMaster_ifunsafe'[wp]:
  "slot = t + 2 ^ objBits (undefined :: cte) * tcbReplySlot \<Longrightarrow>
   \<lbrace>if_unsafe_then_cap' and ex_cte_cap_to' slot\<rbrace>
     setupReplyMaster t
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp add: ifunsafe'_def3 setupReplyMaster_def locateSlot_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of cteCaps_of_def)
  apply (drule_tac x=crefa in spec)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=cref in exI, fastforce)
  apply clarsimp
  apply (rule_tac x=cref' in exI, fastforce)
  done


lemma setupReplyMaster_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_def)
  apply (wp setCTE_iflive' getCTE_wp')
  apply (clarsimp elim!: cte_wp_at_weakenE')
  done

lemma setupReplyMaster_global_refs[wp]:
  "\<lbrace>\<lambda>s. valid_global_refs' s \<and> thread \<notin> global_refs' s\<rbrace>
    setupReplyMaster thread
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: capRange_def)
  done

crunch valid_arch'[wp]: setupReplyMaster "valid_arch_state'"

lemma ex_nonz_tcb_cte_caps':
  "\<lbrakk>ex_nonz_cap_to' t s; tcb_at' t s; valid_objs' s; sl \<in> dom tcb_cte_cases\<rbrakk> \<Longrightarrow>
   ex_cte_cap_to' (t + sl) s"
  apply (clarsimp simp: ex_nonz_cap_to'_def ex_cte_cap_to'_def cte_wp_at_ctes_of)
  apply (subgoal_tac "s \<turnstile>' cteCap cte")
   apply (rule_tac x=cref in exI, rule_tac x=cte in exI)
   apply (clarsimp simp: valid_cap'_def obj_at'_def projectKOs dom_def
                  split: cte.split_asm capability.split_asm)
  apply (case_tac cte)
  apply (clarsimp simp: ctes_of_valid_cap')
  done

lemma ex_nonz_cap_not_global':
  "\<lbrakk>ex_nonz_cap_to' t s; valid_objs' s; valid_global_refs' s\<rbrakk> \<Longrightarrow>
   t \<notin> global_refs' s"
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (frule(1) valid_global_refsD')
  apply clarsimp
  apply (drule orthD1, erule (1) subsetD)
  apply (subgoal_tac "s \<turnstile>' cteCap cte")
   apply (fastforce simp: valid_cap'_def capRange_def capAligned_def
                         is_aligned_no_overflow
                  split: cte.split_asm capability.split_asm)
  apply (case_tac cte)
  apply (clarsimp simp: ctes_of_valid_cap')
  done

crunch typ_at'[wp]: setupReplyMaster "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_drop_imps)

lemma setCTE_irq_handlers':
  "\<lbrace>\<lambda>s. valid_irq_handlers' s \<and> (\<forall>irq. cteCap cte = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)\<rbrace>
     setCTE ptr cte
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def cteCaps_of_def irq_issued'_def)
  apply (wp hoare_use_eq [where f=ksInterruptState, OF setCTE_ksInterruptState setCTE_ctes_of_wp])
  apply (auto simp: ran_def)
  done

lemma setupReplyMaster_irq_handlers'[wp]:
  "\<lbrace>valid_irq_handlers'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_conv)
  apply (wp setCTE_irq_handlers' getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

crunch irq_states' [wp]: setupReplyMaster valid_irq_states'
crunch irqs_makes' [wp]: setupReplyMaster irqs_masked'
  (lift: irqs_masked_lift)
crunch pde_mappings' [wp]: setupReplyMaster valid_pde_mappings'

crunch st_tcb_at' [wp]: setupReplyMaster "st_tcb_at' P t"

crunch ksMachine[wp]: setupReplyMaster "\<lambda>s. P (ksMachineState s)"

lemma setupReplyMaster_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def )
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply wp
  done

crunch pspace_domain_valid[wp]: setupReplyMaster "pspace_domain_valid"
crunch ct_not_inQ[wp]: setupReplyMaster "ct_not_inQ"
crunch ksCurDomain[wp]: setupReplyMaster "\<lambda>s. P (ksCurDomain s)"
crunch ksCurThread[wp]: setupReplyMaster "\<lambda>s. P (ksCurThread s)"
crunch ksIdlethread[wp]: setupReplyMaster "\<lambda>s. P (ksIdleThread s)"
crunch ksDomSchedule[wp]: setupReplyMaster "\<lambda>s. P (ksDomSchedule s)"
crunch scheduler_action[wp]: setupReplyMaster "\<lambda>s. P (ksSchedulerAction s)"
crunch obj_at'_inQ[wp]: setupReplyMaster "obj_at' (inQ d p) t"
crunch tcbDomain_inv[wp]: setupReplyMaster "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
crunch tcbPriority_inv[wp]: setupReplyMaster "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"
crunch ready_queues[wp]: setupReplyMaster "\<lambda>s. P (ksReadyQueues s)"

crunch ksDomScheduleIdx[wp]: setupReplyMaster "\<lambda>s. P (ksDomScheduleIdx s)"

lemma setupReplyMaster_invs'[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
     setupReplyMaster t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp setupReplyMaster_valid_pspace' sch_act_wf_lift tcb_in_cur_domain'_lift ct_idle_or_in_cur_domain'_lift
             valid_queues_lift cur_tcb_lift valid_queues_lift' hoare_vcg_disj_lift
             valid_irq_node_lift | simp)+
  apply (clarsimp simp: ex_nonz_tcb_cte_caps' valid_pspace'_def
                        objBits_def objBitsKO_def tcbReplySlot_def
                        ex_nonz_cap_not_global' dom_def)
  done

crunch st_tcb'[wp]: setupReplyMaster "st_tcb_at' P t"
  (wp: crunch_wps setCTE_st_tcb_at')

lemma setupReplyMaster_cte_wp_at'':
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) p and K (\<not> P NullCap)\<rbrace>
     setupReplyMaster t
   \<lbrace>\<lambda>rv s. cte_wp_at' (P \<circ> cteCap) p s\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_def tree_cte_cteCap_eq)
  apply (wp getCTE_wp')
  apply (fastforce simp: cte_wp_at_ctes_of cteCaps_of_def)
  done

lemmas setupReplyMaster_cte_wp_at' = setupReplyMaster_cte_wp_at''[unfolded o_def]

lemma setupReplyMaster_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: ex_nonz_cap_to'_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift setupReplyMaster_cte_wp_at')
  apply clarsimp
  done

crunch st_tcb_at'[wp]: updateMDB "st_tcb_at' P p"
crunch st_tcb_at'[wp]: cteInsert "st_tcb_at' P p"

definition
  is_arch_update' :: "capability \<Rightarrow> cte \<Rightarrow> bool"
where
  "is_arch_update' cap cte \<equiv> isArchObjectCap cap \<and> capMasterCap cap = capMasterCap (cteCap cte)"

lemma mdb_next_pres:
  "\<lbrakk> m p = Some v;
 mdbNext (cteMDBNode x) = mdbNext (cteMDBNode v) \<rbrakk> \<Longrightarrow>
  m(p \<mapsto> x) \<turnstile> a \<leadsto> b = m \<turnstile> a \<leadsto> b"
  by (simp add: mdb_next_unfold)

lemma mdb_next_trans_next_pres:
  "\<lbrakk> m p = Some v; mdbNext (cteMDBNode x) = mdbNext (cteMDBNode v) \<rbrakk> \<Longrightarrow>
   m(p \<mapsto> x) \<turnstile> a \<leadsto>\<^sup>+ b = m \<turnstile> a \<leadsto>\<^sup>+ b"
  apply (rule iffI)
   apply (erule trancl_induct)
    apply (fastforce simp: mdb_next_pres)
   apply (erule trancl_trans)
   apply (rule r_into_trancl)
   apply (fastforce simp: mdb_next_pres)
  apply (erule trancl_induct)
   apply (rule r_into_trancl)
   apply (simp add: mdb_next_pres del: fun_upd_apply)
  apply (erule trancl_trans)
  apply (fastforce simp: mdb_next_pres simp del: fun_upd_apply)
  done

lemma mdb_next_rtrans_next_pres:
  "\<lbrakk> m p = Some v; mdbNext (cteMDBNode x) = mdbNext (cteMDBNode v) \<rbrakk> \<Longrightarrow>
   m(p \<mapsto> x) \<turnstile> a \<leadsto>\<^sup>* b = m \<turnstile> a \<leadsto>\<^sup>* b"
  by (simp add: rtrancl_eq_or_trancl mdb_next_trans_next_pres)

lemma arch_update_descendants':
  "\<lbrakk> is_arch_update' cap oldcte; m p = Some oldcte\<rbrakk> \<Longrightarrow>
  descendants_of' x (m(p \<mapsto> cteCap_update (\<lambda>_. cap) oldcte)) = descendants_of' x m"
  apply (erule same_master_descendants)
  apply (auto simp: is_arch_update'_def isCap_simps)
  done

lemma arch_update_setCTE_mdb:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' (op = oldcte) p and valid_mdb'\<rbrace>
  setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
  \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (simp add: valid_mdb'_def)
  apply wp
  apply (clarsimp simp: valid_mdb_ctes_def cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (rule conjI)
   apply (rule valid_dlistI)
    apply (fastforce split: split_if_asm elim: valid_dlistE)
   apply (fastforce split: split_if_asm elim: valid_dlistE)
  apply (rule conjI)
   apply (clarsimp simp: no_0_def)
  apply (rule conjI)
   apply (simp add: mdb_chain_0_def mdb_next_trans_next_pres)
   apply blast
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: valid_badges_def mdb_next_pres simp del: fun_upd_apply)
   apply (clarsimp simp: is_arch_update'_def)
   apply (clarsimp split: split_if_asm)
     apply (clarsimp simp: isCap_simps)
    prefer 2
    apply fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p in allE)
   apply simp
   apply (simp add: sameRegionAs_def3)
   apply (rule conjI)
    apply (clarsimp simp: isCap_simps)
   apply (clarsimp simp: isCap_simps)
  apply (rule conjI)
   apply (clarsimp simp: caps_contained'_def simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (frule capMaster_untypedRange)
   apply (frule capMaster_capRange)
   apply (drule sym [where s="capMasterCap cap"])
   apply (frule masterCap.intro)
   apply (clarsimp simp: masterCap.isUntypedCap split: split_if_asm)
      apply fastforce
     apply fastforce
    apply (erule_tac x=pa in allE)
    apply (erule_tac x=p in allE)
    apply fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   apply fastforce
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (clarsimp simp: mdb_chunked_def mdb_next_trans_next_pres simp del: fun_upd_apply)
   apply (drule sym [where s="capMasterCap cap"])
   apply (frule masterCap.intro)
   apply (clarsimp split: split_if_asm)
     apply (erule_tac x=p in allE)
     apply (erule_tac x=p' in allE)
     apply (clarsimp simp: masterCap.sameRegionAs)
     apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                      mdb_next_rtrans_next_pres)
     apply fastforce
    apply (erule_tac x=pa in allE)
    apply (erule_tac x=p in allE)
    apply (clarsimp simp: masterCap.sameRegionAs)
    apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                     mdb_next_rtrans_next_pres)
    apply fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   apply clarsimp
   apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                    mdb_next_rtrans_next_pres)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: is_arch_update'_def untyped_mdb'_def arch_update_descendants'
                   simp del: fun_upd_apply)
   apply (cases oldcte)
   apply clarsimp
   apply (clarsimp split: split_if_asm)
    apply (clarsimp simp: isCap_simps)
   apply (frule capMaster_isUntyped)
   apply (drule capMaster_capRange)
   apply simp
  apply (rule conjI)
   apply (clarsimp simp: untyped_inc'_def arch_update_descendants'
                   simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (drule capMaster_untypedRange)
   apply (clarsimp split: split_if_asm)
     apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: isCap_simps)
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   apply clarsimp
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: valid_nullcaps_def is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: ut_revocable'_def is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply (clarsimp simp: class_links_def simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def mdb_next_pres)
   apply (drule capMaster_capClass)
   apply (clarsimp split: split_if_asm)
   apply fastforce
  apply (rule conjI)
   apply (erule(1) distinct_zombies_sameMasterE)
   apply (clarsimp simp: is_arch_update'_def)
  apply (clarsimp simp: irq_control_def)
  apply (cases oldcte)
  apply (subgoal_tac "cap \<noteq> IRQControlCap")
   prefer 2
   apply (clarsimp simp: is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply clarsimp
  apply (simp add: reply_masters_rvk_fb_def)
  apply (erule ball_ran_fun_updI)
  apply (clarsimp simp add: is_arch_update'_def isCap_simps)
  done

lemma capMaster_zobj_refs:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> zobj_refs' c = zobj_refs' c'"
  by (simp add: capMasterCap_def split: capability.splits arch_capability.splits)

lemma cte_refs_Master:
  "cte_refs' (capMasterCap cap) = cte_refs' cap"
  by (rule ext, simp add: capMasterCap_def split: capability.split)

lemma zobj_refs_Master:
  "zobj_refs' (capMasterCap cap) = zobj_refs' cap"
  by (simp add: capMasterCap_def split: capability.split)

lemma capMaster_same_refs:
  "capMasterCap a = capMasterCap b \<Longrightarrow> cte_refs' a = cte_refs' b \<and> zobj_refs' a = zobj_refs' b"
  apply (rule conjI)
   apply (rule master_eqI, rule cte_refs_Master, simp)
  apply (rule master_eqI, rule zobj_refs_Master, simp)
  done

lemma arch_update_setCTE_iflive:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' (op = oldcte) p and if_live_then_nonz_cap'\<rbrace>
  setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
  \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (wp setCTE_iflive')
  apply (clarsimp simp: cte_wp_at_ctes_of is_arch_update'_def dest!: capMaster_zobj_refs)
  done

lemma arch_update_setCTE_ifunsafe:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' (op = oldcte) p and if_unsafe_then_cap'\<rbrace>
  setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
  \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (clarsimp simp: ifunsafe'_def2 cte_wp_at_ctes_of pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=irq_node'])
   prefer 2
   apply wp
  apply (clarsimp simp: cte_wp_at_ctes_of is_arch_update'_def)
  apply (frule capMaster_same_refs)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (erule_tac x=p in allE)
   apply clarsimp
   apply (erule impE)
    apply clarsimp
   apply clarsimp
   apply (rule_tac x=cref' in exI)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=cref in allE)
  apply clarsimp
  apply (rule_tac x=cref' in exI)
  apply clarsimp
  done

lemma setCTE_cur_tcb[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setCTE ptr val \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp cur_tcb_lift)

lemma setCTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setCTE ptr val \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def )
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply wp
  done

lemma arch_update_setCTE_invs:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' (op = oldcte) p and invs' and valid_cap' cap\<rbrace>
  setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp arch_update_setCTE_mdb valid_queues_lift sch_act_wf_lift tcb_in_cur_domain'_lift ct_idle_or_in_cur_domain'_lift
             arch_update_setCTE_iflive arch_update_setCTE_ifunsafe
             valid_irq_node_lift setCTE_typ_at' setCTE_irq_handlers'
             valid_queues_lift' setCTE_st_tcb_at' irqs_masked_lift
             setCTE_norq hoare_vcg_disj_lift| simp add: st_tcb_at'_def)+
  apply clarsimp
  apply (clarsimp simp: valid_global_refs'_def is_arch_update'_def cte_wp_at_ctes_of isCap_simps)
  apply (drule capMaster_capRange)
  apply (clarsimp simp: valid_refs'_def)
  apply fastforce
  done

definition
  "safe_parent_for' m p cap \<equiv>
  \<exists>parent node. m p = Some (CTE parent node) \<and>
  sameRegionAs parent cap \<and>
  ((\<exists>irq. cap = IRQHandlerCap irq) \<and>
   parent = IRQControlCap \<and>
   (\<forall>p n'. m p \<noteq> Some (CTE cap n'))
  \<or>
   isUntypedCap parent \<and> descendants_of' p m = {} \<and> capRange cap \<noteq> {})"

definition
  "is_simple_cap' cap \<equiv>
  cap \<noteq> NullCap \<and>
  cap \<noteq> IRQControlCap \<and>
  \<not> isUntypedCap cap \<and>
  \<not> isReplyCap cap \<and>
  \<not> isEndpointCap cap \<and>
  \<not> isAsyncEndpointCap cap \<and>
  \<not> isThreadCap cap \<and>
  \<not> isCNodeCap cap \<and>
  \<not> isZombie cap \<and>
  \<not> isArchPageCap cap"


(* FIXME: duplicated *)
locale mdb_insert_simple = mdb_insert +
  assumes safe_parent: "safe_parent_for' m src c'"
  assumes simple: "is_simple_cap' c'"
begin

lemma dest_no_parent_n:
  "n \<turnstile> dest \<rightarrow> p = False"
  using src simple safe_parent
  apply clarsimp
  apply (erule subtree.induct)
   prefer 2
   apply simp
  apply (clarsimp simp: parentOf_def mdb_next_unfold n_dest new_dest_def n)
  apply (cases "mdbNext src_node = dest")
   apply (subgoal_tac "m \<turnstile> src \<leadsto> dest")
    apply simp
   apply (subst mdb_next_unfold)
   apply (simp add: src)
  apply (clarsimp simp: isMDBParentOf_CTE)
  apply (clarsimp simp: is_simple_cap'_def revokable'_def)
  apply (cases c', auto simp: isCap_simps)
  apply (clarsimp simp add: sameRegionAs_def2)
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: safe_parent_for'_def isCap_simps)
  done

lemma src_node_revokable [simp]:
  "mdbRevocable src_node"
  using safe_parent ut_rev src
  apply (clarsimp simp add: safe_parent_for'_def)
  apply (erule disjE)
   apply clarsimp
   apply (erule irq_revocable, rule irq_control)
  apply (clarsimp simp: ut_revocable'_def)
  done

lemma new_child [simp]:
  "isMDBParentOf new_src new_dest"
  using safe_parent ut_rev src
  apply (simp add: new_src_def new_dest_def isMDBParentOf_def)
  apply (clarsimp simp: safe_parent_for'_def)
  apply (auto simp: isCap_simps)
  done

lemma n_dest_child:
  "n \<turnstile> src \<rightarrow> dest"
  apply (rule subtree.direct_parent)
    apply (simp add: n_direct_eq)
   apply simp
  apply (clarsimp simp: parentOf_def src dest n)
  done

lemma parent_m_n:
  assumes "m \<turnstile> p \<rightarrow> p'"
  shows "if p' = src then n \<turnstile> p \<rightarrow> dest \<and> n \<turnstile> p \<rightarrow> p' else n \<turnstile> p \<rightarrow> p'" using assms
proof induct
  case (direct_parent c)
  thus ?case
    apply (cases "p = src")
     apply simp
     apply (rule conjI, clarsimp)
     apply clarsimp
     apply (rule subtree.trans_parent [where c'=dest])
        apply (rule n_dest_child)
       apply (simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (clarsimp simp: new_src_def src)
    apply simp
    apply (subgoal_tac "n \<turnstile> p \<rightarrow> c")
     prefer 2
     apply (rule subtree.direct_parent)
       apply (clarsimp simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (fastforce simp: new_src_def src)
    apply clarsimp
    apply (erule subtree_trans)
    apply (rule n_dest_child)
    done
next
  case (trans_parent c d)
  thus ?case
    apply -
    apply (cases "c = dest", simp)
    apply (cases "d = dest", simp)
    apply (cases "c = src")
     apply clarsimp
     apply (erule subtree.trans_parent [where c'=dest])
       apply (clarsimp simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (rule conjI, clarsimp)
     apply (clarsimp simp: new_src_def src)
    apply clarsimp
    apply (subgoal_tac "n \<turnstile> p \<rightarrow> d")
     apply clarsimp
     apply (erule subtree_trans, rule n_dest_child)
    apply (erule subtree.trans_parent)
      apply (simp add: n_direct_eq)
     apply simp
    apply (clarsimp simp: parentOf_def n)
    apply (fastforce simp: src new_src_def)
    done
qed

lemma n_to_dest [simp]:
  "n \<turnstile> p \<leadsto> dest = (p = src)"
  by (simp add: n_direct_eq)

lemma parent_n_m:
  assumes "n \<turnstile> p \<rightarrow> p'"
  shows "if p' = dest then p \<noteq> src \<longrightarrow> m \<turnstile> p \<rightarrow> src else m \<turnstile> p \<rightarrow> p'"
proof -
  from assms have [simp]: "p \<noteq> dest" by (clarsimp simp: dest_no_parent_n)
  from assms
  show ?thesis
  proof induct
    case (direct_parent c)
    thus ?case
      apply simp
      apply (rule conjI)
       apply clarsimp
      apply clarsimp
      apply (rule subtree.direct_parent)
        apply (simp add: n_direct_eq split: split_if_asm)
       apply simp
      apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
      done
  next
    case (trans_parent c d)
    thus ?case
      apply clarsimp
      apply (rule conjI, clarsimp)
      apply (clarsimp split: split_if_asm)
      apply (simp add: n_direct_eq)
      apply (cases "p=src")
       apply simp
       apply (rule subtree.direct_parent, assumption, assumption)
       apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
      apply clarsimp
      apply (erule subtree.trans_parent, assumption, assumption)
      apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
     apply (erule subtree.trans_parent)
       apply (simp add: n_direct_eq split: split_if_asm)
      apply assumption
     apply (clarsimp simp: parentOf_def n src new_src_def split: split_if_asm)
     done
 qed
qed


lemma descendants:
  "descendants_of' p n =
   (if src \<in> descendants_of' p m \<or> p = src
   then descendants_of' p m \<union> {dest} else descendants_of' p m)"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def)
  apply (fastforce dest!: parent_n_m dest: parent_m_n simp: n_dest_child split: split_if_asm)
  done

end

declare split_if [split del]

lemma safe_parent_for_maskedAsFull[simp]:
  "safe_parent_for' m p (maskedAsFull src_cap a) = safe_parent_for' m p src_cap"
  apply (clarsimp simp:safe_parent_for'_def)
  apply (rule iffI)
    apply (clarsimp simp:maskedAsFull_def isCap_simps split:if_splits cap.splits
    cong:sameRegionAs_update_untyped')+
done

lemma setUntypedCapAsFull_safe_parent_for':
  "\<lbrace>\<lambda>s. safe_parent_for' (ctes_of s) slot a \<and> cte_wp_at' (op = srcCTE) slot s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) c' slot
   \<lbrace>\<lambda>rv s. safe_parent_for' (ctes_of s) slot a\<rbrace>"
  apply (clarsimp simp:safe_parent_for'_def setUntypedCapAsFull_def split:if_splits)
  apply (intro conjI impI)
   apply (wp updateCap_ctes_of_wp)
   apply (subgoal_tac "mdb_inv_preserve (ctes_of s)
     (modify_map (ctes_of s) slot
     (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. max_free_index (capBlockSize c')) (cteCap srcCTE))))")
     apply (frule mdb_inv_preserve.descendants_of[where p = slot])
     apply (clarsimp simp:isCap_simps modify_map_def cte_wp_at_ctes_of simp del:fun_upd_apply)
     apply (clarsimp cong:sameRegionAs_update_untyped)
   apply (rule mdb_inv_preserve_updateCap)
     apply (simp add:cte_wp_at_ctes_of)
   apply simp
 apply wp
 apply simp
done

lemma maskedAsFull_revokable_safe_parent:
  "\<lbrakk>is_simple_cap' c'; safe_parent_for' m p c'; m p = Some cte;
    cteCap cte = (maskedAsFull src_cap' a)\<rbrakk>
   \<Longrightarrow> revokable' (maskedAsFull src_cap' a) c' = revokable' src_cap' c'"
   apply (clarsimp simp:revokable'_def maskedAsFull_def split:if_splits)
   apply (intro allI impI conjI)
     apply (clarsimp simp:isCap_simps is_simple_cap'_def)+
done

lemma is_simple_cap'_maskedAsFull[simp]:
  "is_simple_cap' (maskedAsFull src_cap' c') =  is_simple_cap' src_cap'"
  by (auto simp: is_simple_cap'_def maskedAsFull_def isCap_simps split:if_splits)

lemma cins_corres_simple:
  assumes "cap_relation c c'" "src' = cte_map src" "dest' = cte_map dest"
  notes trans_state_update'[symmetric,simp]
  shows "corres dc
        (valid_objs and pspace_distinct and pspace_aligned and
         valid_mdb and valid_list and K (src\<noteq>dest) and
         cte_wp_at (\<lambda>c. c=cap.NullCap) dest and
         K (is_simple_cap c) and
         (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src c) src s))
        (pspace_distinct' and pspace_aligned' and valid_mdb' and valid_cap' c' and
         K (is_simple_cap' c') and
         cte_wp_at' (\<lambda>c. cteCap c=NullCap) dest' and
         (\<lambda>s. safe_parent_for' (ctes_of s) src' c'))
        (cap_insert c src dest)
        (cteInsert c' src' dest')"
  (is "corres _ (?P and (\<lambda>s. cte_wp_at _ _ s)) (?P' and cte_wp_at' _ _ and _) _ _")
  using assms
  unfolding cap_insert_def cteInsert_def
  apply (fold revokable_def revokable'_fold)
  apply simp
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_cap_corres])
      apply (rule corres_split [OF _ get_cap_corres])
        apply (rule_tac F="cteCap rv' = NullCap" in corres_gen_asm2)
        apply simp
        apply (rule_tac P="?P and cte_at dest and
                            (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src c) src s) and
                            cte_wp_at (op = src_cap) src" and
                        Q="?P' and
                           cte_wp_at' (op = rv') (cte_map dest) and
                           cte_wp_at' (op = srcCTE) (cte_map src) and
                           (\<lambda>s. safe_parent_for' (ctes_of s) src' c')"
                        in corres_assert_assume)
         prefer 2
         apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def valid_nullcaps_def)
         apply (case_tac rv')
         apply (simp add: initMDBNode_def)
         apply (erule allE)+
         apply (erule (1) impE)
         apply (simp add: nullPointer_def)
       apply (rule corres_guard_imp)
         apply (rule_tac R="\<lambda>r. ?P and cte_at dest and
                            (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src c) src s) and
                            cte_wp_at (op = (masked_as_full src_cap c)) src" and
                        R'="\<lambda>r. ?P' and cte_wp_at' (op = rv') (cte_map dest)
           and cte_wp_at' (op = (CTE (maskedAsFull (cteCap srcCTE) c') (cteMDBNode srcCTE))) (cte_map src)
           and (\<lambda>s. safe_parent_for' (ctes_of s) src' c')"
                        in corres_split[where r'=dc])
        apply (rule corres_stronger_no_failI)
         apply (rule no_fail_pre, wp hoare_weak_lift_imp)
         apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def)
         apply (erule_tac valid_dlistEn[where p = "cte_map src"])
           apply (simp+)[3]
        apply (clarsimp simp: corres_underlying_def state_relation_def
                              in_monad valid_mdb'_def valid_mdb_ctes_def)
        apply (drule (1) pspace_relationsD)
        apply (drule (18) set_cap_not_quite_corres)
         apply (rule refl)
        apply (elim conjE exE)
        apply (rule bind_execI, assumption)
        apply (subgoal_tac "mdb_insert_abs (cdt a) src dest")
              prefer 2
              apply (clarsimp simp: cte_wp_at_caps_of_state valid_mdb_def2)
              apply (rule mdb_insert_abs.intro)
                apply clarsimp
               apply (erule (1) mdb_cte_at_Null_None)
              apply (erule (1) mdb_cte_at_Null_descendants)
        apply (subgoal_tac "no_mloop (cdt a)")
         prefer 2
         apply (simp add: valid_mdb_def)
        apply (clarsimp simp: exec_gets update_cdt_def bind_assoc set_cdt_def
                              exec_get exec_put set_original_def modify_def
                    simp del: fun_upd_apply

               | (rule bind_execI[where f="cap_insert_ext x y z x' y'",standard], clarsimp simp: mdb_insert_abs.cap_insert_ext_det_def2 update_cdt_list_def set_cdt_list_def put_def simp del: fun_upd_apply) | rule refl)+

        apply (clarsimp simp: put_def state_relation_def simp del: fun_upd_apply)
        apply (drule updateCap_stuff)
        apply clarsimp
        apply (drule (3) updateMDB_the_lot', simp, simp, elim conjE)
        apply (drule (3) updateMDB_the_lot', simp, simp, elim conjE)
        apply (drule (3) updateMDB_the_lot', simp, simp, elim conjE)
        apply (clarsimp simp: pspace_relations_def)
        apply (rule conjI)
         apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)
        apply (clarsimp simp: cte_wp_at_ctes_of nullPointer_def prev_update_modify_mdb_relation)
        apply (subgoal_tac "cte_map dest \<noteq> 0")
         prefer 2
         apply (clarsimp simp: valid_mdb'_def
                               valid_mdb_ctes_def no_0_def)
        apply (subgoal_tac "cte_map src \<noteq> 0")
         prefer 2
         apply (clarsimp simp: valid_mdb'_def
                               valid_mdb_ctes_def no_0_def)
        apply (thin_tac "ksMachineState ?t = ?p")+
        apply (thin_tac "ksCurThread ?t = ?p")+
        apply (thin_tac "ksIdleThread ?t = ?p")+
        apply (thin_tac "ksReadyQueues ?t = ?p")+
        apply (thin_tac "ksSchedulerAction ?t = ?p")+
        apply (subgoal_tac "should_be_parent_of src_cap (is_original_cap a src) c (revokable src_cap c) = True")
         prefer 2
         apply (subst should_be_parent_of_masked_as_full[symmetric])
         apply (subst safe_parent_is_parent)
            apply (simp add: cte_wp_at_caps_of_state)
           apply (simp add: cte_wp_at_caps_of_state)
          apply simp
         apply simp
        apply (subst conj_assoc[symmetric])
        apply (rule conjI)
         defer
         apply (thin_tac "ctes_of ?t = ?t'")+
         apply (clarsimp simp: modify_map_apply)
         apply (clarsimp simp: revokable_relation_def simp del: fun_upd_apply)
         apply (simp split: split_if)
         apply (rule conjI)
          apply clarsimp
          apply (subgoal_tac "mdbRevocable node = revokable' (cteCap srcCTE) c'")
           prefer 2
           apply (case_tac rv')
           apply (clarsimp simp add: const_def modify_map_def split: split_if_asm)
          apply clarsimp
          apply (rule revokable_eq, assumption, assumption)
           apply (subst same_region_as_relation [symmetric])
             prefer 3
             apply (rule safe_parent_same_region)
             apply (simp add: cte_wp_at_caps_of_state safe_parent_for_masked_as_full)
            apply assumption
           apply assumption
          apply (clarsimp simp: cte_wp_at_def is_simple_cap_def)
         apply clarsimp
         apply (case_tac srcCTE)
         apply (case_tac rv')
         apply clarsimp
         apply (subgoal_tac "\<exists>cap' node'. ctes_of b (cte_map (aa,bb)) = Some (CTE cap' node')")
          prefer 2
          apply (clarsimp simp: modify_map_def split: split_if_asm)
         apply clarsimp
         apply (drule set_cap_caps_of_state_monad)+
         apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
          prefer 2
          apply (clarsimp simp: cte_wp_at_caps_of_state null_filter_def split: if_splits)
         apply clarsimp
         apply (subgoal_tac "cte_at (aa,bb) a")
          prefer 2
          apply (drule null_filter_caps_of_stateD)
          apply (erule cte_wp_at_weakenE, rule TrueI)
         apply (subgoal_tac "mdbRevocable node = mdbRevocable node'")
          apply clarsimp
         apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map dest")
          apply (clarsimp simp: modify_map_def split: split_if_asm)
         apply (erule (5) cte_map_inj)
         apply (rule set_untyped_cap_as_full_corres)
         apply simp+
          apply (wp set_untyped_cap_full_valid_objs set_untyped_cap_as_full_valid_mdb set_untyped_cap_as_full_valid_list
             set_untyped_cap_as_full_cte_wp_at setUntypedCapAsFull_valid_cap
             setUntypedCapAsFull_cte_wp_at setUntypedCapAsFull_safe_parent_for' | clarsimp | wps)+
          apply (clarsimp simp:cte_wp_at_caps_of_state )
         apply (case_tac rv',clarsimp simp:cte_wp_at_ctes_of maskedAsFull_def)
        apply (wp getCTE_wp' get_cap_wp)
     apply clarsimp
     apply (fastforce elim: cte_wp_at_weakenE)
    apply (clarsimp simp: cte_wp_at'_def)
   apply (thin_tac "ctes_of ?s = ?t")+
   apply (thin_tac "pspace_relation ?s ?t")+
   apply (thin_tac "machine_state ?t = ?s")+
   apply (case_tac "srcCTE")
   apply (rename_tac src_cap' src_node)
   apply (case_tac "rv'")
   apply (rename_tac dest_node)
   apply (clarsimp simp: in_set_cap_cte_at_swp)
   apply (subgoal_tac "cte_at src a \<and> safe_parent_for (cdt a) src c src_cap")
    prefer 2
    apply (fastforce simp: cte_wp_at_def safe_parent_for_masked_as_full)
   apply (erule conjE)

   apply (subgoal_tac "mdb_insert (ctes_of b) (cte_map src) (maskedAsFull src_cap' c') src_node
                                  (cte_map dest) NullCap dest_node")
    prefer 2
    apply (rule mdb_insert.intro)
      apply (rule mdb_ptr.intro)
     apply (rule vmdb.intro, simp add: valid_mdb_ctes_def)
    apply (erule mdb_ptr_axioms.intro)
     apply (rule mdb_ptr.intro)
    apply (rule vmdb.intro, simp add: valid_mdb_ctes_def)
   apply (erule mdb_ptr_axioms.intro)
          apply (rule mdb_insert_axioms.intro)
         apply (rule refl)
        apply assumption
       apply assumption
      apply assumption
     apply assumption
   apply (erule (5) cte_map_inj)
  apply (rule conjI)
   apply (simp (no_asm_simp) add: cdt_relation_def split: split_if)
   apply (intro impI allI)
   apply (frule mdb_insert_simple_axioms.intro)
    apply(clarsimp simp:cte_wp_at_ctes_of)
   apply (drule (1) mdb_insert_simple.intro)
   apply (drule_tac src_cap' = src_cap' in maskedAsFull_revokable_safe_parent[symmetric])
      apply simp+
   apply (subst mdb_insert_simple.descendants)
    apply simp
   apply (subst mdb_insert_abs.descendants_child, assumption)
   apply (frule set_cap_caps_of_state_monad)
   apply (subgoal_tac "cte_at (aa,bb) a")
    prefer 2
    apply (clarsimp simp: cte_wp_at_caps_of_state split: split_if_asm)
   apply (simp add: descendants_of_eq' cdt_relation_def split: split_if del: split_paired_All)
   apply clarsimp
   apply (drule (5) cte_map_inj)+
   apply simp
  (* exact reproduction of proof in cins_corres,
     as it does not used is_derived *)
  apply(simp add: cdt_list_relation_def del: split_paired_All split_paired_Ex)
  apply(subgoal_tac "no_mloop (cdt a) \<and> finite_depth (cdt a)")
   prefer 2
   apply(simp add: finite_depth valid_mdb_def)
  apply(intro impI allI)
  apply(simp add: fun_upd_twist)

  apply(subst next_slot_eq[OF mdb_insert_abs.next_slot])
        apply(simp_all del: fun_upd_apply)
   apply(simp split: option.splits del: fun_upd_apply add: fun_upd_twist)
   apply(intro allI impI)
   apply(subgoal_tac "src \<noteq> (aa, bb)")
    prefer 2
    apply(rule notI)
    apply(simp add: valid_mdb_def no_mloop_weaken)
   apply(subst fun_upd_twist, simp, simp)

  apply(case_tac "ca=src")
   apply(simp)
   apply(clarsimp simp: modify_map_def)
   apply(fastforce split: split_if_asm)
  apply(case_tac "ca = dest")
   apply(simp)
   apply(case_tac "next_slot src (cdt_list (a)) (cdt a)")
    apply(simp)
   apply(simp)
   apply(clarsimp simp: modify_map_def const_def)
   apply(simp split: split_if_asm)
     apply(drule_tac p="cte_map src" in valid_mdbD1')
       apply(simp)
      apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
     apply(clarsimp)
    apply(drule cte_map_inj_eq)
         apply(simp_all)[6]
   apply(erule_tac x="fst src" in allE)
   apply(erule_tac x="snd src" in allE)
   apply(fastforce)
  apply(simp)
  apply(case_tac "next_slot ca (cdt_list (a)) (cdt a)")
   apply(simp)
  apply(simp)
  apply(subgoal_tac "cte_at ca a")
   prefer 2
   apply(rule cte_at_next_slot)
      apply(simp_all)[5]
  apply(clarsimp simp: modify_map_def const_def)
  apply(simp split: split_if_asm)
        apply(drule cte_map_inj_eq)
             apply(simp_all)[6]
       apply(drule_tac p="cte_map src" in valid_mdbD1')
         apply(simp)
        apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
       apply(clarsimp)
      apply(clarsimp)
      apply(case_tac z)
      apply(erule_tac x=aa in allE)
      apply(erule_tac x=bb in allE)
      apply(fastforce)
     apply(drule cte_map_inj_eq)
          apply(simp_all)[6]
    apply(drule cte_map_inj_eq)
        apply(simp_all)[6]
   apply(drule cte_map_inj_eq)
       apply(simp_all)[6]
  apply(fastforce)
  done

declare split_if [split]

lemma sameRegion_capRange_sub:
  "sameRegionAs cap cap' \<Longrightarrow> capRange cap' \<subseteq> capRange cap"
  apply (clarsimp simp: sameRegionAs_def2 isCap_Master capRange_Master)
  apply (erule disjE)
   apply (clarsimp dest!: capMaster_capRange)
  apply (erule disjE)
   apply fastforce
  apply (clarsimp simp: isCap_simps capRange_def)
  done

lemma safe_parent_for_capRange:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> capRange cap \<subseteq> capRange (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def)
  apply (erule disjE)
   apply (clarsimp simp: capRange_def)
  apply (auto simp: sameRegionAs_def2 isCap_simps capRange_def capMasterCap_def capRange_Master
         split:capability.splits arch_capability.splits)
  done

lemma safe_parent_Null:
  "\<lbrakk> m src = Some (CTE NullCap n); safe_parent_for' m src c' \<rbrakk> \<Longrightarrow> False"
  by (simp add: safe_parent_for'_def)

lemma notUntypedRange:
  "\<not>isUntypedCap cap \<Longrightarrow> untypedRange cap = {}"
  by (cases cap) (auto simp: isCap_simps)

lemma safe_parent_for_untypedRange:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> untypedRange cap \<subseteq> untypedRange (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def)
  apply (erule disjE)
   apply clarsimp
  apply clarsimp
  apply (simp add: sameRegionAs_def2)
  apply (erule disjE)
   apply clarsimp
   apply (drule capMaster_untypedRange)
   apply blast
  apply (erule disjE)
   apply (clarsimp simp: capRange_Master untypedCapRange)
   apply (cases "isUntypedCap cap")
    apply (clarsimp simp: capRange_Master untypedCapRange)
    apply blast
   apply (drule notUntypedRange)
   apply simp
  apply (clarsimp simp: isCap_Master isCap_simps)
  done

lemma safe_parent_for_capUntypedRange:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> capRange cap \<subseteq> untypedRange (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def)
  apply (erule disjE)
   apply (clarsimp simp: capRange_def)
  apply clarsimp
  apply (simp add: sameRegionAs_def2)
  apply (erule disjE)
   apply clarsimp
   apply (frule capMaster_capRange)
   apply (clarsimp simp: capRange_Master untypedCapRange)
  apply (erule disjE)
   apply (clarsimp simp: capRange_Master untypedCapRange)
   apply blast
  apply (clarsimp simp: isCap_Master isCap_simps)
  done

lemma safe_parent_for_descendants':
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE pcap n); isUntypedCap pcap \<rbrakk> \<Longrightarrow> descendants_of' p m = {}"
  by (auto simp: safe_parent_for'_def isCap_simps)

lemma safe_parent_not_ep':
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> \<not>isEndpointCap src_cap"
  by (auto simp: safe_parent_for'_def isCap_simps)

lemma safe_parent_not_aep':
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> \<not>isAsyncEndpointCap src_cap"
  by (auto simp: safe_parent_for'_def isCap_simps)

lemma safe_parent_capClass:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> capClass cap = capClass src_cap"
  apply (auto simp: safe_parent_for'_def isCap_simps sameRegionAs_def2 capRange_Master capRange_def
           capMasterCap_def
           split: capability.splits arch_capability.splits)
  done

locale mdb_insert_simple' = mdb_insert_simple +
  fixes n'
  defines  "n' \<equiv> modify_map n (mdbNext src_node) (cteMDBNode_update (mdbPrev_update (\<lambda>_. dest)))"
begin

lemma no_0_n' [intro!]: "no_0 n'" by (auto simp: n'_def)
lemmas n_0_simps' [iff] = no_0_simps [OF no_0_n']

lemmas no_0_m_prev [iff] = no_0_prev [OF no_0]
lemmas no_0_n_prev [iff] = no_0_prev [OF no_0_n']

lemma chain_n': "mdb_chain_0 n'"
  unfolding n'_def
  by (rule mdb_chain_0_modify_map_prev) (rule chain_n)

lemma no_loops_n': "no_loops n'" using chain_n' no_0_n'
  by (rule mdb_chain_0_no_loops)

lemma irrefl_direct_simp_n' [iff]:
  "n' \<turnstile> x \<leadsto> x = False"
  using no_loops_n' by (rule no_loops_direct_simp)

lemma irrefl_trancl_simp' [iff]:
  "n \<turnstile> x \<leadsto>\<^sup>+ x = False"
  using no_loops_n by (rule no_loops_trancl_simp)

lemma n_direct_eq':
  "n' \<turnstile> p \<leadsto> p' = (if p = src then p' = dest else
                 if p = dest then m \<turnstile> src \<leadsto> p'
                 else m \<turnstile> p \<leadsto> p')"
  by (simp add: n'_def mdb_next_modify n_direct_eq)

lemma dest_no_next_p:
  "m p = Some cte \<Longrightarrow> mdbNext (cteMDBNode cte) \<noteq> dest"
  using dest dest_prev
  apply (cases cte)
  apply (rule notI)
  apply (rule dlistEn, assumption)
   apply clarsimp
  apply clarsimp
  done

lemma dest_no_src_next [iff]:
  "mdbNext src_node \<noteq> dest"
  using src by (clarsimp dest!: dest_no_next_p)

lemma n_dest':
  "n' dest = Some new_dest"
  by (simp add: n'_def n modify_map_if new_dest_def)

lemma n_src_dest':
  "n' \<turnstile> src \<leadsto> dest"
  by (simp add: n_src_dest n'_def)

lemma dest_chain_0' [simp, intro!]:
  "n' \<turnstile> dest \<leadsto>\<^sup>+ 0"
  using chain_n' n_dest'
  by (simp add: mdb_chain_0_def) blast

lemma n'_trancl_eq':
  "n' \<turnstile> p \<leadsto>\<^sup>+ p' =
  (if p' = dest then m \<turnstile> p \<leadsto>\<^sup>* src
   else if p = dest then m \<turnstile> src \<leadsto>\<^sup>+ p'
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  unfolding n'_def trancl_prev_update
  by (simp add: n_trancl_eq')

lemma n'_trancl_eq:
  "n' \<turnstile> p \<leadsto>\<^sup>+ p' =
  (if p' = dest then p = src \<or> m \<turnstile> p \<leadsto>\<^sup>+ src
   else if p = dest then m \<turnstile> src \<leadsto>\<^sup>+ p'
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  unfolding n'_def trancl_prev_update
  by (simp add: n_trancl_eq)

lemma n_rtrancl_eq':
  "n' \<turnstile> p \<leadsto>\<^sup>* p' =
  (if p' = dest then p = dest \<or> p \<noteq> dest \<and> m \<turnstile> p \<leadsto>\<^sup>* src
   else if p = dest then p' \<noteq> src \<and> m \<turnstile> src \<leadsto>\<^sup>* p'
   else m \<turnstile> p \<leadsto>\<^sup>* p')"
  unfolding n'_def rtrancl_prev_update
  by (simp add: n_rtrancl_eq)

lemma n'_cap:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then cap = c' \<and> m p = Some (CTE dest_cap node')
          else m p = Some (CTE cap node')"
  by (auto simp add: n'_def n src dest new_src_def new_dest_def modify_map_if split: split_if_asm)

lemma n'_rev:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then mdbRevocable node = revokable' src_cap c' \<and> m p = Some (CTE dest_cap node')
          else m p = Some (CTE cap node') \<and> mdbRevocable node = mdbRevocable node'"
  by (auto simp add: n'_def n src dest new_src_def new_dest_def modify_map_if split: split_if_asm)

lemma m_cap':
  "m p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then cap = dest_cap \<and> n' p = Some (CTE c' node')
          else n' p = Some (CTE cap node')"
  apply (simp add: n'_def n new_src_def new_dest_def modify_map_if)
  apply (cases "p=dest")
   apply (auto simp: src dest)
  done

lemma dest_no_parent_n' [simp]:
  "n' \<turnstile> dest \<rightarrow> p = False"
  by (simp add: n'_def dest_no_parent_n)

lemma descendants':
  "descendants_of' p n' =
   (if src \<in> descendants_of' p m \<or> p = src
   then descendants_of' p m \<union> {dest} else descendants_of' p m)"
  by (simp add: n'_def descendants descendants_of_prev_update)

lemma ut_revocable_n' [simp]:
  "ut_revocable' n'"
  using dest
  apply (clarsimp simp: ut_revocable'_def)
  apply (frule n'_cap)
  apply (drule n'_rev)
  apply clarsimp
  apply (clarsimp simp: n_dest' new_dest_def split: split_if_asm)
   apply (clarsimp simp: revokable'_def isCap_simps)
  apply (drule_tac p=p and m=m in ut_revocableD', assumption)
   apply (rule ut_rev)
  apply simp
  done

lemma valid_nc' [simp]:
  "valid_nullcaps n'"
  unfolding valid_nullcaps_def
  using src dest dest_prev dest_next simple safe_parent
  apply (clarsimp simp: n'_def n_def modify_map_if)
  apply (rule conjI)
   apply (clarsimp simp: is_simple_cap'_def)
  apply clarsimp
  apply (rule conjI)
   apply (fastforce dest!: safe_parent_Null)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_nullcaps_next, rule no_0, rule dlist, rule nullcaps)
   apply simp
  apply clarsimp
  apply (erule nullcapsD', rule nullcaps)
  done

lemma n'_prev_eq:
  "n' \<turnstile> p \<leftarrow> p' =
  (if p' = mdbNext src_node \<and> p' \<noteq> 0 then p = dest
   else if p' = dest then p = src
   else m \<turnstile> p \<leftarrow> p')"
  using src dest dest_prev dest_next
  apply (cases "p' = 0", simp)
  apply (simp split del: split_if)
  apply (cases "p' = mdbNext src_node")
   apply (clarsimp simp: modify_map_apply n'_def n_def mdb_prev_def)
   apply (clarsimp simp: modify_map_if)
   apply (rule iffI, clarsimp)
   apply clarsimp
   apply (rule dlistEn, assumption, simp)
   apply clarsimp
   apply (case_tac cte')
   apply clarsimp
  apply (cases "p' = dest")
   apply (clarsimp simp: modify_map_if n'_def n_def mdb_prev_def)
  apply clarsimp
  apply (clarsimp simp: modify_map_if n'_def n_def mdb_prev_def)
  apply (cases "p' = src", simp)
  apply clarsimp
  apply (rule iffI, clarsimp)
  apply clarsimp
  apply (case_tac z)
  apply clarsimp
  done

lemma m_prev_of_next:
  "m \<turnstile> p \<leftarrow> mdbNext src_node = (p = src \<and> mdbNext src_node \<noteq> 0)"
  using src
  apply (clarsimp simp: mdb_prev_def)
  apply (rule iffI)
   apply clarsimp
   apply (rule dlistEn, assumption, clarsimp)
   apply clarsimp
  apply clarsimp
  apply (rule dlistEn, assumption, clarsimp)
  apply clarsimp
  done

lemma src_next_eq:
  "m \<turnstile> p \<leadsto> mdbNext src_node = (if mdbNext src_node \<noteq> 0 then p = src else m \<turnstile> p \<leadsto> 0)"
  using src
  apply -
  apply (rule iffI)
   prefer 2
   apply (clarsimp split: split_if_asm)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule (1) dlist_nextD0)
   apply (clarsimp simp: m_prev_of_next)
  apply clarsimp
  done

lemma src_next_eq':
  "m (mdbNext src_node) = Some cte \<Longrightarrow> m \<turnstile> p \<leadsto> mdbNext src_node = (p = src)"
  by (subst src_next_eq) auto

lemma dest_no_prev [iff]:
  "\<not> m \<turnstile> dest \<leftarrow> p"
  using dest dest_next
  apply (clarsimp simp: mdb_prev_def)
  apply (rule dlistEp [where p=p], assumption, clarsimp)
  apply clarsimp
  done

lemma src_prev [iff]:
  "m \<turnstile> src \<leftarrow> p = (p = mdbNext src_node \<and> p \<noteq> 0)"
  using src
  apply -
  apply (rule iffI)
   prefer 2
   apply (clarsimp simp: mdb_ptr_src.next_p_prev)
  apply (clarsimp simp: mdb_prev_def)
  apply (rule conjI)
   prefer 2
   apply clarsimp
  apply (rule dlistEp [where p=p], assumption, clarsimp)
  apply simp
  done

lemma blurg: "(\<forall>c c'. Q c \<longrightarrow> P c') = (\<forall>c. Q c \<longrightarrow> (\<forall>c'. P c'))"
  apply simp
done

lemma dlist' [simp]:
  "valid_dlist n'"
  using src dest
  apply (unfold valid_dlist_def3 n_direct_eq' n'_prev_eq)
  apply (split split_if)
  apply (split split_if)
  apply (split split_if)
  apply (split split_if)
  apply (split split_if)
  apply (split split_if)
  apply (split split_if)
  apply simp
  apply (intro conjI impI allI notI)
         apply (fastforce simp: src_next_eq')
        apply (clarsimp simp: src_next_eq split: split_if_asm)
       apply (simp add: mdb_ptr_src.p_next)
      apply (erule (1) dlist_nextD0)
     apply clarsimp
    apply clarsimp
   apply clarsimp
  apply (erule (1) dlist_prevD0)
  done

lemma utRange_c':
  "untypedRange c' \<subseteq> untypedRange src_cap"
  using safe_parent src
  by - (drule (1) safe_parent_for_untypedRange, simp)

lemma capRange_c':
  "capRange c' \<subseteq> capRange src_cap"
  using safe_parent src
  by - (drule (1) safe_parent_for_capRange, simp)

lemma not_ut_c' [simp]:
  "\<not>isUntypedCap c'"
  using simple
  by (simp add: is_simple_cap'_def)

lemma utCapRange_c':
  "capRange c' \<subseteq> untypedRange src_cap"
  using safe_parent src
  by - (drule (1) safe_parent_for_capUntypedRange, simp)

lemma ut_descendants:
  "isUntypedCap src_cap \<Longrightarrow> descendants_of' src m = {}"
  using safe_parent src
  by (rule safe_parent_for_descendants')

lemma ut_mdb' [simp]:
  "untyped_mdb' n'"
  using src dest utRange_c' capRange_c' utCapRange_c'
  apply (clarsimp simp: untyped_mdb'_def)
  apply (drule n'_cap)+
  apply (clarsimp simp: descendants')
  apply (clarsimp split: split_if_asm)
   apply (cases "isUntypedCap src_cap")
    prefer 2
    apply (drule_tac p=p and p'=src and m=m in untyped_mdbD', assumption+)
      apply blast
     apply (rule untyped_mdb)
    apply simp
   apply (frule ut_descendants)
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply clarsimp
   apply blast
  apply (fastforce elim: untyped_mdbD' intro!: untyped_mdb)
  done

lemma n'_badge:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then mdbFirstBadged node = revokable' src_cap c' \<and> m p = Some (CTE dest_cap node')
          else m p = Some (CTE cap node') \<and> mdbFirstBadged node = mdbFirstBadged node'"
  by (auto simp add: n'_def n src dest new_src_def new_dest_def modify_map_if split: split_if_asm)

lemma src_not_ep [simp]:
  "\<not>isEndpointCap src_cap"
  using safe_parent src by (rule safe_parent_not_ep')

lemma src_not_aep [simp]:
  "\<not>isAsyncEndpointCap src_cap"
  using safe_parent src by (rule safe_parent_not_aep')

lemma c_not_ep [simp]:
  "\<not>isEndpointCap c'"
  using simple by (simp add: is_simple_cap'_def)

lemma c_not_aep [simp]:
  "\<not>isAsyncEndpointCap c'"
  using simple by (simp add: is_simple_cap'_def)

lemma valid_badges' [simp]:
  "valid_badges n'"
  using simple src dest
  apply (clarsimp simp: valid_badges_def)
  apply (simp add: n_direct_eq')
  apply (frule_tac p=p in n'_badge)
  apply (frule_tac p=p' in n'_badge)
  apply (drule n'_cap)+
  apply (clarsimp split: split_if_asm)
  apply (insert valid_badges)
  apply (simp add: valid_badges_def)
  apply blast
  done

lemma caps_contained' [simp]:
  "caps_contained' n'"
  using src dest capRange_c' utCapRange_c'
  apply (clarsimp simp: caps_contained'_def)
  apply (drule n'_cap)+
  apply clarsimp
  apply (clarsimp split: split_if_asm)
     apply (drule capRange_untyped)
     apply simp
    apply (drule capRange_untyped)
    apply clarsimp
   apply (cases "isUntypedCap src_cap")
    prefer 2
    apply (drule_tac p=p and p'=src in caps_containedD', assumption+)
      apply blast
     apply (rule caps_contained)
    apply blast
   apply (frule capRange_untyped)
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply (clarsimp simp: ut_descendants)
   apply blast
  apply (drule (3) caps_containedD', rule caps_contained)
  apply blast
  done

lemma capClass_c' [simp]:
  "capClass c' = capClass src_cap"
  using safe_parent src by (rule safe_parent_capClass)

lemma class_links' [simp]:
  "class_links n'"
  using src dest
  apply (clarsimp simp: class_links_def)
  apply (simp add: n_direct_eq')
  apply (case_tac cte, case_tac cte')
  apply clarsimp
  apply (drule n'_cap)+
  apply clarsimp
  apply (clarsimp split: split_if_asm)
   apply (drule (2) class_linksD, rule class_links)
   apply simp
  apply (drule (2) class_linksD, rule class_links)
  apply simp
  done

lemma untyped_inc' [simp]:
  "untyped_inc' n'"
  using src dest
  apply (clarsimp simp: untyped_inc'_def)
  apply (drule n'_cap)+
  apply (clarsimp simp: descendants')
  apply (clarsimp split: split_if_asm)
  apply (rule conjI)
   apply clarsimp
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule_tac p=src and p'=p' in untyped_incD', assumption+, rule untyped_inc)
   apply (clarsimp simp: ut_descendants)
   apply (intro conjI, clarsimp+)
  apply (drule (3) untyped_incD', rule untyped_inc)
  apply clarsimp
  done

lemma sameRegion_src [simp]:
  "sameRegionAs src_cap c'"
  using safe_parent src
  apply (simp add: safe_parent_for'_def)
  done

lemma sameRegion_src_c':
  "sameRegionAs cap src_cap \<Longrightarrow> sameRegionAs cap c'"
  using safe_parent simple src capRange_c'
  apply (simp add: safe_parent_for'_def)
  apply (erule disjE)
   apply (clarsimp simp: sameRegionAs_def2 isCap_simps capRange_def)
  apply clarsimp
  apply (simp add: sameRegionAs_def2 isCap_Master capRange_Master)
  apply (erule disjE)
   prefer 2
   apply (clarsimp simp: isCap_simps)
  apply (elim conjE)
  apply (erule disjE)
   prefer 2
   apply (clarsimp simp: isCap_simps)
  apply simp
  apply blast
  done

lemma sameRegion_c_src':
  "sameRegionAs c' cap \<Longrightarrow> sameRegionAs src_cap cap"
  using safe_parent simple src capRange_c'
  apply (simp add: safe_parent_for'_def)
  apply (erule disjE)
   apply clarsimp
   apply (clarsimp simp: sameRegionAs_def2 capRange_def isCap_simps)
  apply clarsimp
  apply (simp add: sameRegionAs_def2 isCap_Master capRange_Master)
  apply (erule disjE)
   prefer 2
   apply clarsimp
   apply (erule disjE, blast)
   apply (clarsimp simp: isCap_simps)
   apply (clarsimp simp: capRange_def)
  apply (elim conjE)
  apply (drule capMaster_capRange)
  apply simp
  done

lemma safe_not_next_region:
  "\<lbrakk> m \<turnstile> src \<leadsto> p; m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent src
  unfolding safe_parent_for'_def
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: mdb_next_unfold)
   apply (clarsimp simp: sameRegionAs_def2 isCap_simps)
  apply (clarsimp simp: descendants_of'_def)
  apply (erule_tac x=p in allE)
  apply (erule notE, rule direct_parent, assumption)
   apply clarsimp
  apply (simp add: parentOf_def)
  apply (simp add: isMDBParentOf_def)
  apply (erule sameRegionAs_trans [rotated])
  apply (rule sameRegion_src)
  done

lemma irq_c'_new:
  assumes irq_src: "isIRQControlCap src_cap"
  shows "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent irq_src src
  apply (clarsimp simp: safe_parent_for'_def isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps)
  done

lemma ut_capRange_non_empty:
  "isUntypedCap src_cap \<Longrightarrow> capRange c' \<noteq> {}"
  using safe_parent src unfolding safe_parent_for'_def
  by (clarsimp simp: isCap_simps)

lemma ut_sameRegion_non_empty:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs c' cap \<rbrakk> \<Longrightarrow> capRange cap \<noteq> {}"
  using simple safe_parent src
  apply (clarsimp simp: is_simple_cap'_def sameRegionAs_def2 isCap_Master)
  apply (erule disjE)
   apply (clarsimp simp: ut_capRange_non_empty dest!: capMaster_capRange)
  apply clarsimp
  apply (clarsimp simp: safe_parent_for'_def)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (clarsimp simp: isCap_simps capRange_def)
  done

lemma ut_c'_new:
  assumes ut_src: "isUntypedCap src_cap"
  shows "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using src simple
  apply clarsimp
  apply (drule untyped_mdbD', rule ut_src, assumption)
     apply (clarsimp simp: is_simple_cap'_def sameRegionAs_def2 isCap_Master capRange_Master)
     apply (fastforce simp: isCap_simps)
    apply (frule sameRegion_capRange_sub)
    apply (drule ut_sameRegion_non_empty [OF ut_src])
    apply (insert utCapRange_c')
    apply blast
   apply (rule untyped_mdb)
  apply (simp add: ut_descendants [OF ut_src])
  done

lemma c'_new:
  "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent src unfolding safe_parent_for'_def
  apply (elim exE conjE)
  apply (erule disjE)
   apply (erule irq_c'_new [rotated])
   apply (clarsimp simp: isCap_simps)
  apply clarsimp
  apply (drule (1) ut_c'_new)
  apply simp
  done

lemma irq_control_src:
  "\<lbrakk> isIRQControlCap src_cap;
     m p = Some (CTE cap node);
     sameRegionAs cap c' \<rbrakk> \<Longrightarrow> p = src"
  using safe_parent src unfolding safe_parent_for'_def
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2 isCap_Master)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps capRange_def)
  apply (clarsimp simp: isCap_simps)
  apply (drule (1) irq_controlD, rule irq_control)
  apply simp
  done

lemma not_irq_parentD:
  "\<not> isIRQControlCap src_cap \<Longrightarrow>
  isUntypedCap src_cap \<and> descendants_of' src m = {} \<and> capRange c' \<noteq> {}"
  using src safe_parent unfolding safe_parent_for'_def
  by (clarsimp simp: isCap_simps)

lemma ut_src_only_ut_c_parents:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs cap c'; m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow> isUntypedCap cap"
  using safe_parent src unfolding safe_parent_for'_def
  apply clarsimp
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply clarsimp
  apply (rule ccontr)
  apply (drule (3) untyped_mdbD')
    apply (frule sameRegion_capRange_sub)
    apply (insert utCapRange_c')[1]
    apply blast
   apply (rule untyped_mdb)
  apply simp
  done

lemma ut_src:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs cap c'; m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow>
  isUntypedCap cap \<and> untypedRange cap \<inter> untypedRange src_cap \<noteq> {}"
  apply (frule (2) ut_src_only_ut_c_parents)
  apply simp
  apply (frule sameRegion_capRange_sub)
  apply (insert utCapRange_c')[1]
  apply (simp add: untypedCapRange)
  apply (drule ut_capRange_non_empty)
  apply blast
  done


lemma chunked' [simp]:
  "mdb_chunked n'"
  using src dest
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule n'_cap)+
  apply (clarsimp simp: n'_trancl_eq)
  apply (clarsimp split: split_if_asm)
    prefer 3
    apply (frule (3) mdb_chunkedD, rule chunked)
    apply clarsimp
    apply (rule conjI, clarsimp)
     apply (clarsimp simp: is_chunk_def n'_trancl_eq n_rtrancl_eq' n_dest' new_dest_def)
     apply (rule conjI, clarsimp)
      apply (rule conjI, clarsimp)
      apply clarsimp
      apply (erule_tac x=src in allE)
      apply simp
      apply (erule sameRegion_src_c')
     apply clarsimp
     apply (erule_tac x=p'' in allE)
     apply clarsimp
     apply (frule_tac p=p'' in m_cap')
     apply clarsimp
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n'_trancl_eq n_rtrancl_eq' n_dest' new_dest_def)
    apply (rule conjI, clarsimp)
     apply (rule conjI, clarsimp)
     apply clarsimp
     apply (erule_tac x=src in allE)
     apply simp
     apply (erule sameRegion_src_c')
    apply clarsimp
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (frule_tac p=p'' in m_cap')
    apply clarsimp
   apply (case_tac "p' = src")
    apply simp
    apply (clarsimp simp: is_chunk_def)
    apply (simp add: n'_trancl_eq n_rtrancl_eq')
    apply (erule disjE)
     apply (simp add: n_dest' new_dest_def)
    apply clarsimp
    apply (drule (1) trancl_rtrancl_trancl)
    apply simp
   apply clarsimp
   apply (drule c'_new)
   apply (erule (1) notE)
  apply (case_tac "p=src")
   apply clarsimp
   apply (clarsimp simp: is_chunk_def)
   apply (simp add: n'_trancl_eq n_rtrancl_eq')
   apply (erule disjE)
    apply (clarsimp simp: n_dest' new_dest_def)
   apply clarsimp
   apply (drule (1) trancl_rtrancl_trancl)
   apply simp
  apply (case_tac "isIRQControlCap src_cap")
   apply (drule (2) irq_control_src)
   apply simp
  apply (drule not_irq_parentD)
  apply clarsimp
  apply (frule (2) ut_src)
  apply clarsimp
  apply (subgoal_tac "src \<in> descendants_of' p m")
   prefer 2
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply clarsimp
   apply fastforce
  apply (frule_tac m=m and p=p and p'=src in mdb_chunkedD, assumption+)
     apply (clarsimp simp: descendants_of'_def)
     apply (drule subtree_parent)
     apply (clarsimp simp: parentOf_def isMDBParentOf_def split: split_if_asm)
    apply simp
   apply (rule chunked)
  apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (rule conjI)
    prefer 2
    apply clarsimp
    apply (drule (1) trancl_trans, simp)
   apply (clarsimp simp: is_chunk_def)
   apply (simp add: n'_trancl_eq n_rtrancl_eq' split: split_if_asm)
    apply (clarsimp simp: n_dest' new_dest_def)
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap')
   apply clarsimp
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) trancl_trans, simp)
  apply (clarsimp simp: descendants_of'_def)
  apply (drule subtree_mdb_next)
  apply (drule (1) trancl_trans)
  apply simp
  done

lemma distinct_zombies_m:
  "distinct_zombies m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma untyped_rangefree:
  "\<lbrakk> isUntypedCap src_cap; m x = Some cte; x \<noteq> src; \<not> isUntypedCap (cteCap cte) \<rbrakk>
          \<Longrightarrow> capRange (cteCap cte) \<noteq> capRange c'"
  apply (frule ut_descendants)
  apply (cases cte, clarsimp)
  apply (frule(2) untyped_mdbD' [OF src _ _ _ _ untyped_mdb])
   apply (simp add: untypedCapRange[symmetric])
   apply (frule ut_capRange_non_empty)
   apply (cut_tac capRange_c')
   apply blast
  apply simp
  done

lemma notZomb:
  "\<not> isZombie src_cap" "\<not> isZombie c'"
  using sameRegion_src simple
  by (auto simp: isCap_simps sameRegionAs_def3
       simp del: sameRegion_src,
      auto simp: is_simple_cap'_def isCap_simps)

lemma notArchPage:
  "\<not> isArchPageCap c'"
  using simple
  by (clarsimp simp: isCap_simps is_simple_cap'_def)

lemma distinct_zombies[simp]:
  "distinct_zombies n'"
  using distinct_zombies_m
  apply (simp add: n'_def distinct_zombies_nonCTE_modify_map)
  apply (simp add: n_def modify_map_apply src dest)
  apply (rule distinct_zombies_sameE[rotated])
        apply (simp add: src)
       apply simp+
  apply (cases "isUntypedCap src_cap")
   apply (erule distinct_zombies_seperateE)
   apply (case_tac "y = src")
    apply (clarsimp simp add: src)
   apply (frule(3) untyped_rangefree)
   apply (simp add: capRange_def)
  apply (rule sameRegionAsE [OF sameRegion_src], simp_all)
    apply (erule distinct_zombies_copyMasterE, rule src)
     apply simp
    apply (simp add: notZomb)
   apply (simp add: notArchPage)
  apply (erule distinct_zombies_sameMasterE, rule dest)
  apply (clarsimp simp: isCap_simps)
  done

lemma irq' [simp]:
  "irq_control n'" using simple
  apply (clarsimp simp: irq_control_def)
  apply (frule n'_cap)
  apply (drule n'_rev)
  apply (clarsimp split: split_if_asm)
   apply (simp add: is_simple_cap'_def)
  apply (frule irq_revocable, rule irq_control)
  apply clarsimp
  apply (drule n'_cap)
  apply (clarsimp split: split_if_asm)
  apply (erule disjE)
   apply (clarsimp simp: is_simple_cap'_def)
  apply (erule (1) irq_controlD, rule irq_control)
  done

lemma reply_masters_rvk_fb:
  "reply_masters_rvk_fb m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma reply_masters_rvk_fb' [simp]:
  "reply_masters_rvk_fb n'"
   using reply_masters_rvk_fb simple
   apply (simp add: reply_masters_rvk_fb_def n'_def
                    n_def ball_ran_modify_map_eq)
   apply (subst ball_ran_modify_map_eq)
    apply (clarsimp simp: modify_map_def m_p is_simple_cap'_def)
   apply (simp add: ball_ran_modify_map_eq m_p is_simple_cap'_def
                    dest_cap isCap_simps)
   done

lemma mdb:
  "valid_mdb_ctes n'"
  by (simp add: valid_mdb_ctes_def no_0_n' chain_n')

end

lemma updateCapFreeIndex_no_0:
  assumes preserve:"\<And>m m'.  mdb_inv_preserve m m'
  \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (no_0(Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (no_0 (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.by_products)
    apply simp
  apply (rule preserve)
  apply (simp add:cte_wp_at_ctes_of)+
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma setUntypedCapAsFull_no_0:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m'
  \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (no_0 (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
setUntypedCapAsFull (cteCap srcCTE) cap src
 \<lbrace>\<lambda>r s. P (no_0 (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
   apply (wp updateCapFreeIndex_no_0)
   apply (clarsimp simp:preserve cte_wp_at_ctes_of)+
  apply wp
  apply clarsimp
done

lemma cteInsert_simple_mdb':
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and (\<lambda>s. src \<noteq> dest) and K (capAligned cap) and
    (\<lambda>s. safe_parent_for' (ctes_of s) src cap) and K (is_simple_cap' cap) \<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding cteInsert_def valid_mdb'_def
  apply (fold revokable'_fold)
  apply simp
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (wp updateCap_ctes_of_wp getCTE_wp' setUntypedCapAsFull_ctes
     mdb_inv_preserve_updateCap mdb_inv_preserve_modify_map mdb_inv_preserve_update_cap_same | clarsimp)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI)
   apply (clarsimp simp: valid_mdb_ctes_def)
  apply (case_tac cte)
  apply (rename_tac src_cap src_node)
  apply (case_tac ctea)
  apply (rename_tac dest_cap dest_node)
  apply clarsimp
  apply (subst modify_map_eq)
     apply simp+
   apply (clarsimp simp:maskedAsFull_def is_simple_cap'_def)
  apply (subgoal_tac "mdb_insert_simple'
    (ctes_of sa) src src_cap src_node dest NullCap dest_node cap")
   prefer 2
   apply (intro mdb_insert_simple'.intro
                mdb_insert_simple.intro mdb_insert_simple_axioms.intro
                mdb_ptr.intro mdb_insert.intro vmdb.intro
                mdb_ptr_axioms.intro mdb_insert_axioms.intro)
              apply (simp add:modify_map_def valid_mdb_ctes_maskedAsFull)+
         apply (clarsimp simp:nullPointer_def)+
       apply ((clarsimp simp:valid_mdb_ctes_def)+)
  apply (drule mdb_insert_simple'.mdb)
  apply (clarsimp simp:valid_mdb_ctes_def)
  done

lemma cteInsert_valid_globals_simple:
 "\<lbrace>valid_global_refs' and (\<lambda>s. safe_parent_for' (ctes_of s) src cap)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: cteInsert_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) safe_parent_for_capRange)
  apply (drule (1) valid_global_refsD')
  apply blast
  done

lemma cteInsert_simple_invs:
 "\<lbrace>invs' and cte_wp_at' (\<lambda>c. cteCap c=NullCap) dest and valid_cap' cap and
  (\<lambda>s. src \<noteq> dest) and (\<lambda>s. safe_parent_for' (ctes_of s) src cap)
  and (\<lambda>s. \<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)
  and ex_cte_cap_to' dest and K (is_simple_cap' cap)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
   apply (wp cur_tcb_lift sch_act_wf_lift valid_queues_lift tcb_in_cur_domain'_lift
             valid_irq_node_lift valid_queues_lift' irqs_masked_lift
             cteInsert_simple_mdb' cteInsert_valid_globals_simple
             cteInsert_norq | simp add: st_tcb_at'_def)+
  apply (auto simp: invs'_def valid_state'_def valid_pspace'_def elim: valid_capAligned)
  done


lemma ensureEmptySlot_stronger [wp]:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = NullCap) p s \<longrightarrow> P s\<rbrace> ensureEmptySlot p \<lbrace>\<lambda>rv. P\<rbrace>, -"
  apply (simp add: ensureEmptySlot_def whenE_def unlessE_whenE)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at'_def)
  done

lemma lookupSlotForCNodeOp_real_cte_at'[wp]:
  "\<lbrace>valid_objs' and valid_cap' rootCap\<rbrace>
     lookupSlotForCNodeOp isSrc rootCap cref depth
   \<lbrace>\<lambda>rv. real_cte_at' rv\<rbrace>,-"
  apply (simp add: lookupSlotForCNodeOp_def split_def unlessE_def
                     split del: split_if cong: if_cong)
  apply (rule hoare_pre)
   apply (wp resolveAddressBits_real_cte_at' | simp | wp_once hoare_drop_imps)+
  done

lemma cte_refs_maskCapRights[simp]:
  "cte_refs' (maskCapRights rghts cap) = cte_refs' cap"
  by (rule ext, cases cap,
      simp_all add: maskCapRights_def isCap_defs Let_def
                    ArchRetype_H.maskCapRights_def
         split del: split_if
             split: arch_capability.split)

lemma capASID_PageCap_None [simp]:
  "capASID (ArchObjectCap (PageCap r R page_size None)) = None"
  by (simp add: capASID_def)

lemma getSlotCap_cap_to'[wp]:
  "\<lbrace>\<top>\<rbrace> getSlotCap cp \<lbrace>\<lambda>rv s. \<forall>r\<in>cte_refs' rv (irq_node' s). ex_cte_cap_to' r s\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (fastforce simp: cte_wp_at_ctes_of ex_cte_cap_to'_def)
  done

lemma getSlotCap_cap_to2:
  "\<lbrace>\<top> and K (\<forall>cap. P cap \<longrightarrow> Q cap)\<rbrace>
     getSlotCap slot
   \<lbrace>\<lambda>rv s. P rv \<longrightarrow> (\<forall>x \<in> cte_refs' rv (irq_node' s). ex_cte_cap_wp_to' Q x s)\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of ex_cte_cap_wp_to'_def)
  apply fastforce
  done

lemma locateSlot_cap_to'[wp]:
  "\<lbrace>\<lambda>s. isCNodeCap cap \<and> (\<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_wp_to' P r s)\<rbrace>
     locateSlot (capCNodePtr cap) (v && mask (capCNodeBits cap))
   \<lbrace>ex_cte_cap_wp_to' P\<rbrace>"
  apply (simp add: locateSlot_def)
  apply wp
  apply (clarsimp dest!: isCapDs valid_capAligned
                   simp: objBits_simps mult_ac capAligned_def)
  apply (erule bspec)
  apply (case_tac "bits < word_bits")
   apply simp
   apply (rule and_mask_less_size)
   apply (simp add: word_bits_def word_size)
  apply (simp add: power_overflow word_bits_def)
  done

lemma rab_cap_to'':
  assumes P: "\<And>cap. isCNodeCap cap \<longrightarrow> P cap"
  shows
  "s \<turnstile> \<lbrace>\<lambda>s. isCNodeCap cap \<longrightarrow> (\<forall>r\<in>cte_refs' cap (irq_node' s). ex_cte_cap_wp_to' P r s)\<rbrace>
     resolveAddressBits cap cref depth
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to' P (fst rv) s\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
proof (induct arbitrary: s rule: resolveAddressBits.induct)
  case (1 cap fn cref depth)
  show ?case
    apply (subst resolveAddressBits.simps)
    apply (simp add: Let_def split_def cap_case_CNodeCap[unfolded isCap_simps]
               split del: split_if cong: if_cong)
    apply (rule hoare_pre_spec_validE)
     apply ((elim exE | wp_once spec_strengthen_postE[OF "1.hyps"])+,
              (rule refl conjI | simp add: in_monad split del: split_if del: cte_refs'.simps)+)
            apply (wp getSlotCap_cap_to2
                     | simp    add: assertE_def split_def whenE_def
                        split del: split_if | simp add: imp_conjL[symmetric]
                     | wp_once hoare_drop_imps)+
    apply (clarsimp simp: P)
  done
qed

lemma rab_cap_to'[wp]:
  "\<lbrace>(\<lambda>s. isCNodeCap cap \<longrightarrow> (\<forall>r\<in>cte_refs' cap (irq_node' s). ex_cte_cap_wp_to' P r s))
              and K (\<forall>cap. isCNodeCap cap \<longrightarrow> P cap)\<rbrace>
     resolveAddressBits cap cref depth
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to' P (fst rv) s\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (unfold validE_R_def)
  apply (rule use_spec, rule rab_cap_to'')
  apply simp
  done

lemma lookupCNode_cap_to'[wp]:
  "\<lbrace>\<lambda>s. \<forall>r\<in>cte_refs' rootCap (irq_node' s). ex_cte_cap_to' r s\<rbrace>
     lookupSlotForCNodeOp isSrc rootCap cref depth
   \<lbrace>\<lambda>p. ex_cte_cap_to' p\<rbrace>,-"
  apply (simp add: lookupSlotForCNodeOp_def Let_def split_def unlessE_def
             split del: split_if cong: if_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | simp)+
  done

lemma badge_derived'_refl[simp]: "badge_derived' c c"
  by (simp add: badge_derived'_def)

lemma derived'_not_Null:
  "\<not> is_derived' m p c capability.NullCap"
  "\<not> is_derived' m p capability.NullCap c"
  by (clarsimp simp: is_derived'_def badge_derived'_def)+

lemma getSlotCap_wp:
  "\<lbrace>\<lambda>s.  (\<exists>cap. cte_wp_at' (\<lambda>c. cteCap c = cap) p s \<and> Q cap s)\<rbrace>
   getSlotCap p \<lbrace>Q\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at'_def)
  done

lemma storeWordUser_typ_at' :
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> storeWordUser v w \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  unfolding storeWordUser_def by wp

lemma arch_update_updateCap_invs:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and invs' and valid_cap' cap\<rbrace>
  updateCap p cap
  \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: updateCap_def)
  apply (wp arch_update_setCTE_invs getCTE_wp')
  apply clarsimp
  done

lemma updateCap_same_master:
  "\<lbrakk> cap_relation cap cap' \<rbrakk> \<Longrightarrow>
   corres dc (valid_objs and pspace_aligned and pspace_distinct and
              cte_wp_at (\<lambda>c. cap_master_cap c = cap_master_cap cap \<and>
                             \<not>is_reply_cap c \<and> \<not>is_master_reply_cap c \<and>
                             \<not>is_ep_cap c \<and> \<not>is_aep_cap c) slot)
             (pspace_aligned' and pspace_distinct' and cte_at' (cte_map slot))
     (set_cap cap slot)
     (updateCap (cte_map slot) cap')" (is "_ \<Longrightarrow> corres _ ?P ?P' _ _")
  apply (unfold updateCap_def)
  apply (rule corres_guard_imp)
    apply (rule_tac Q="?P" and R'="\<lambda>cte. ?P' and (\<lambda>s. ctes_of s (cte_map slot) = Some cte)"
      in corres_symb_exec_r_conj)
       apply (rule corres_stronger_no_failI)
        apply (rule no_fail_pre, wp)
        apply (clarsimp simp: cte_wp_at_ctes_of)
       apply clarsimp
       apply (clarsimp simp add: state_relation_def)
       apply (drule (1) pspace_relationsD)
       apply (frule (4) set_cap_not_quite_corres_prequel)
            apply (erule cte_wp_at_weakenE, rule TrueI)
           apply assumption
          apply assumption
         apply simp
        apply (rule refl)
       apply clarsimp
       apply (rule bexI)
        prefer 2
        apply assumption
       apply (clarsimp simp: pspace_relations_def)
       apply (subst conj_assoc[symmetric])
       apply (rule conjI)
        apply (frule setCTE_pspace_only)
        apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                         split: split_if_asm Structures_A.kernel_object.splits)
       apply (rule conjI)
        apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)
        apply (intro allI conjI)
         apply (frule use_valid[OF _ setCTE_gsUserPages])
          prefer 2
          apply simp+
        apply (frule use_valid[OF _ setCTE_gsCNodes])
         prefer 2
         apply simp+
       apply (subst conj_assoc[symmetric])
       apply (rule conjI)
        prefer 2
        apply (rule conjI)
         prefer 2
         apply (frule setCTE_pspace_only)
         apply clarsimp
         apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                         split: split_if_asm Structures_A.kernel_object.splits)
        apply (frule set_cap_caps_of_state_monad)
        apply (drule is_original_cap_set_cap)
        apply clarsimp
        apply (erule use_valid [OF _ setCTE_ctes_of_wp])
        apply (clarsimp simp: revokable_relation_def simp del: fun_upd_apply)
        apply (clarsimp split: split_if_asm)
        apply (drule cte_map_inj_eq)
              prefer 2
              apply (erule cte_wp_at_weakenE, rule TrueI)
             apply (simp add: null_filter_def split: split_if_asm)
              apply (erule cte_wp_at_weakenE, rule TrueI)
             apply (erule caps_of_state_cte_at)
            apply fastforce
           apply fastforce
          apply fastforce
         apply clarsimp
         apply (simp add: null_filter_def split: split_if_asm)
          apply (erule_tac x=aa in allE, erule_tac x=bb in allE)
         apply (clarsimp simp: cte_wp_at_caps_of_state)
         apply (erule disjE)
          apply (clarsimp simp: cap_master_cap_simps dest!: cap_master_cap_eqDs)
         apply (case_tac rv)
         apply clarsimp
        apply (subgoal_tac "(aa,bb) \<noteq> slot")
         prefer 2
         apply clarsimp
        apply (simp add: null_filter_def cte_wp_at_caps_of_state split: split_if_asm)
       apply (clarsimp simp: cdt_relation_def)
       apply (frule set_cap_caps_of_state_monad)
       apply (frule mdb_set_cap, frule exst_set_cap)
       apply clarsimp
       apply (erule use_valid [OF _ setCTE_ctes_of_wp])
       apply (frule cte_wp_at_norm)
       apply (clarsimp simp del: fun_upd_apply)
       apply (frule (1) pspace_relation_ctes_ofI)
         apply fastforce
        apply fastforce
       apply (clarsimp simp del: fun_upd_apply)
       apply (subst same_master_descendants)
            apply assumption
           apply (clarsimp simp: master_cap_relation)
          apply (frule_tac d=c in master_cap_relation [symmetric], assumption)
          apply (frule is_reply_cap_relation[symmetric],
                 drule is_reply_master_relation[symmetric])+
          apply simp
          apply (drule masterCap.intro)
          apply (drule masterCap.isReplyCap)
          apply simp
         apply (drule is_ep_cap_relation)+
         apply (drule master_cap_ep)
         apply simp
        apply (drule is_aep_cap_relation)+
        apply (drule master_cap_aep)
        apply simp
       apply (simp add: in_set_cap_cte_at)
       apply(simp add: cdt_list_relation_def split del: split_if)
       apply(intro allI impI)
       apply(erule_tac x=aa in allE)+
       apply(erule_tac x=bb in allE)+
       apply(clarsimp split: split_if_asm)
       apply(case_tac rv, clarsimp)
      apply (wp getCTE_wp')
     apply clarsimp
    apply (rule no_fail_pre, wp)
    apply clarsimp
    apply assumption
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma diminished_cte_refs':
  "diminished' cap cap' \<Longrightarrow> cte_refs' cap n = cte_refs' cap' n"
  by (clarsimp simp: diminished'_def)

lemma diminished_Untyped' :
  "diminished' (UntypedCap r n x) cap = (cap = UntypedCap r n x)"
  apply (rule iffI)
    apply (case_tac cap)
    apply (clarsimp simp:isCap_simps maskCapRights_def diminished'_def split:split_if_asm)+
    apply (case_tac arch_capability)
    apply (clarsimp simp:isCap_simps ArchRetype_H.maskCapRights_def maskCapRights_def diminished'_def Let_def)+
done

lemma updateCapFreeIndex_valid_mdb_ctes:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  and     coin  :"\<And>m cte. \<lbrakk>m src = Some cte\<rbrakk> \<Longrightarrow> (\<exists>cte'. (Q m) src = Some cte' \<and> cteCap cte = cteCap cte')"
  and     assoc :"\<And>m f. Q (modify_map m src (cteCap_update f)) = modify_map (Q m) src (cteCap_update f)"
  shows
 "\<lbrace>\<lambda>s. usableUntypedRange (capFreeIndex_update (\<lambda>_. index) cap) \<subseteq> usableUntypedRange cap \<and> isUntypedCap cap
       \<and>  valid_mdb_ctes (Q (ctes_of s)) \<and> cte_wp_at' (\<lambda>c. cteCap c = cap) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) cap)
 \<lbrace>\<lambda>r s. (valid_mdb_ctes (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) cap))))")
    apply (clarsimp simp:valid_mdb_ctes_def)
   apply (intro conjI)
      apply ((simp add:mdb_inv_preserve.preserve_stuff
        mdb_inv_preserve.by_products)+)[7]
     apply (rule mdb_inv_preserve.untyped_inc')
    apply assumption
    apply (clarsimp simp:assoc cte_wp_at_ctes_of)
    apply (clarsimp simp:modify_map_def split:if_splits)
   apply (drule coin)
    apply clarsimp
    apply (erule(1) subsetD)
   apply simp
   apply (simp_all add:mdb_inv_preserve.preserve_stuff
       mdb_inv_preserve.by_products)
  apply (rule preserve)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma updateFreeIndex_pspace':
  "\<lbrace>\<lambda>s. (capFreeIndex cap \<le> idx \<and> idx \<le> 2 ^ capBlockSize cap \<and>
         is_aligned (of_nat idx :: word32) 4 \<and> isUntypedCap cap) \<and>
        valid_pspace' s \<and> cte_wp_at' (\<lambda>c. cteCap c = cap) src s\<rbrace>
   updateCap src (capFreeIndex_update (\<lambda>_. idx) cap)
   \<lbrace>\<lambda>r s. valid_pspace' s\<rbrace>"
   apply (clarsimp simp:valid_pspace'_def)
   apply (rule hoare_pre)
    apply (rule hoare_vcg_conj_lift)
     apply (clarsimp simp:updateCap_def)
     apply (wp getCTE_wp)
    apply (clarsimp simp:valid_mdb'_def)
    apply (wp updateCapFreeIndex_valid_mdb_ctes)
    apply (simp | wp)+
  apply (clarsimp simp:cte_wp_at_ctes_of valid_mdb'_def)
  apply (case_tac cte,simp add:isCap_simps)
  apply (drule(1) ctes_of_valid_cap')
  apply (subgoal_tac "usableUntypedRange (capFreeIndex_update (\<lambda>_. idx) capability)
          \<subseteq> usableUntypedRange capability")
   apply (clarsimp simp:valid_cap'_def capAligned_def valid_untyped'_def
          simp del:atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff usableUntypedRange.simps
          split del:if_splits)
   apply (drule_tac x = ptr' in spec)
   apply (clarsimp simp:ko_wp_at'_def
          simp del:atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff usableUntypedRange.simps
          split del:if_splits)
   apply blast
  apply (clarsimp simp:isCap_simps valid_cap'_def capAligned_def
                  split:if_splits)
  apply (erule order_trans[rotated])
  apply (rule word_plus_mono_right)
   apply (rule of_nat_mono_maybe_le[THEN iffD1])
    apply (subst word_bits_def[symmetric])
    apply (erule less_le_trans[OF _  power_increasing])
     apply simp
    apply simp
   apply (subst word_bits_def[symmetric])
   apply (erule le_less_trans)
   apply (erule less_le_trans[OF _ power_increasing])
    apply simp+
  apply (erule is_aligned_no_wrap')
  apply (rule word_of_nat_less)
   apply simp
  done

lemma updateFreeIndex_invs':
  "\<lbrace>\<lambda>s. (capFreeIndex cap \<le> idx \<and> idx \<le> 2 ^ capBlockSize cap \<and>
         isUntypedCap cap \<and> is_aligned (of_nat idx :: word32) 4) \<and>
        invs' s \<and> cte_wp_at' (\<lambda>c. cteCap c = cap) src s\<rbrace>
   updateCap src (capFreeIndex_update (\<lambda>_. idx) cap)
   \<lbrace>\<lambda>r s. invs' s\<rbrace>"
   apply (clarsimp simp:invs'_def valid_state'_def )
   apply (wp updateFreeIndex_pspace' sch_act_wf_lift valid_queues_lift updateCap_iflive' tcb_in_cur_domain'_lift
             | simp add: st_tcb_at'_def)+
        apply (rule hoare_pre)
         apply (rule hoare_vcg_conj_lift)
         apply (simp add: ifunsafe'_def3 cteInsert_def setUntypedCapAsFull_def
               split del: split_if)
         apply (wp getCTE_wp)
       apply (rule hoare_vcg_conj_lift)
        apply (simp add:updateCap_def)
        apply wp
       apply (wp valid_irq_node_lift)
       apply (rule hoare_vcg_conj_lift)
        apply (simp add:updateCap_def)
        apply (wp setCTE_irq_handlers' getCTE_wp)
       apply (simp add:updateCap_def)
       apply (wp irqs_masked_lift valid_queues_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)
      apply (clarsimp simp:cte_wp_at_ctes_of)
      apply (intro conjI allI impI)
         apply (clarsimp simp: modify_map_def cteCaps_of_def ifunsafe'_def3 split:if_splits)
          apply (drule_tac x=src in spec)
          apply (clarsimp simp:isCap_simps)
          apply (rule_tac x = cref' in exI)
          apply clarsimp
         apply (drule_tac x = cref in spec)
         apply clarsimp
         apply (rule_tac x = cref' in exI)
         apply clarsimp
        apply (drule(1) valid_global_refsD')
  apply (clarsimp simp:isCap_simps cte_wp_at_ctes_of)+
  done

end
