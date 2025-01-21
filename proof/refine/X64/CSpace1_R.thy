(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  CSpace refinement
*)

theory CSpace1_R
imports
  CSpace_I
  "AInvs.ArchDetSchedSchedule_AI"
begin

context Arch begin arch_global_naming

(* IOPortControl caps are unique and always revocable. Defined separately from archMDBAssertions,
   because locale mdb_insert_simple needs a form that only takes a cte_heap. *)
definition arch_mdb_assert :: "cte_heap \<Rightarrow> bool" where
  "arch_mdb_assert m \<equiv>
   \<forall>p n. m p = Some (CTE (ArchObjectCap IOPortControlCap) n) \<longrightarrow>
         mdbRevocable n \<and>
         (\<forall>p' n'. m p' = Some (CTE (ArchObjectCap IOPortControlCap) n') \<longrightarrow> p' = p)"

end

arch_requalify_consts
  arch_mdb_assert

defs archMDBAssertions_def:
  "archMDBAssertions s \<equiv> arch_mdb_assert (ctes_of s)"

context Arch begin global_naming X64_A (*FIXME: arch-split*)

lemmas final_matters_def = final_matters_def[simplified final_matters_arch_def]

declare final_matters_simps[simp del]

lemmas final_matters_simps[simp]
    = final_matters_def[split_simps cap.split arch_cap.split]

end

context begin interpretation Arch . (*FIXME: arch-split*)

lemma isMDBParentOf_CTE1:
  "isMDBParentOf (CTE cap node) cte =
   (\<exists>cap' node'. cte = CTE cap' node' \<and> sameRegionAs cap cap'
      \<and> mdbRevocable node
      \<and> (isEndpointCap cap \<longrightarrow> capEPBadge cap \<noteq> 0 \<longrightarrow>
           capEPBadge cap = capEPBadge cap' \<and> \<not> mdbFirstBadged node')
      \<and> (isNotificationCap cap \<longrightarrow> capNtfnBadge cap \<noteq> 0 \<longrightarrow>
           capNtfnBadge cap = capNtfnBadge cap' \<and> \<not> mdbFirstBadged node'))"
  apply (simp add: isMDBParentOf_def Let_def split: cte.splits split del: if_split)
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
  by (cases c; cases c') (auto simp: X64_H.sameRegionAs_def sameRegionAs_def Let_def isCap_simps)

lemma is_phyiscal_relation:
  "cap_relation c c' \<Longrightarrow> is_physical c = isPhysicalCap c'"
  by (auto simp: is_physical_def arch_is_physical_def
           split: cap.splits arch_cap.splits)

lemma obj_ref_of_relation:
  "\<lbrakk> cap_relation c c'; capClass c' = PhysicalClass \<rbrakk> \<Longrightarrow>
  obj_ref_of c = capUntypedPtr c'"
  by (cases c; simp) (rename_tac arch_cap, case_tac arch_cap, auto)

lemma obj_size_relation:
  "\<lbrakk> cap_relation c c'; capClass c' = PhysicalClass \<rbrakk> \<Longrightarrow>
  obj_size c = capUntypedSize c'"
  apply (cases c, simp_all add: objBits_simps' zbits_map_def
                                cte_level_bits_def
                         split: option.splits sum.splits)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap,
    simp_all add: objBits_def X64_H.capUntypedSize_def asid_low_bits_def
                  bit_simps)
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
  apply (rename_tac cap mdbnode)
  apply (cases cte')
  apply (rename_tac cap' mdbnode')
  apply (clarsimp split del: if_split)
  apply (case_tac "mdbRevocable mdbnode")
   prefer 2
   apply simp
  apply (clarsimp split del: if_split)
  apply (case_tac "RetypeDecls_H.sameRegionAs cap cap'")
   prefer 2
   apply (simp add: same_region_as_relation)
  apply (simp add: same_region_as_relation split del: if_split)
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
             split del: if_split)
  apply (clarsimp simp: in_monad typeError_def objBits_simps
                        magnitudeCheck_def
                 split: kernel_object.split_asm if_split_asm option.split_asm
             split del: if_split)
       apply simp+
  done

lemma tcb_cases_related:
  "tcb_cap_cases ref = Some (getF, setF, restr) \<Longrightarrow>
    \<exists>getF' setF'. (\<forall>x. tcb_cte_cases (cte_map (x, ref) - x) = Some (getF', setF'))
               \<and> (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow> cap_relation (getF tcb) (cteCap (getF' tcb')))"
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  by (simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1
                cte_map_def' tcb_relation_def
         split: if_split_asm)

lemma pspace_relation_cte_wp_at:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
    cte_wp_at ((=) c) (cref, oref) s; pspace_aligned' s';
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
  apply (clarsimp simp: tcb_relation_cut_def)
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
     cte_wp_at ((=) c) slot s; pspace_aligned' s';
     pspace_distinct' s' \<rbrakk>
  \<Longrightarrow> \<exists>cte. ctes_of s' (cte_map slot) = Some cte \<and> cap_relation c (cteCap cte)"
  apply (cases slot, clarsimp)
  apply (drule(3) pspace_relation_cte_wp_at)
  apply (simp add: cte_wp_at_ctes_of)
  done

lemma pspace_relation_caps_of_state_cross:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
     caps_of_state s slot = Some c; pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> \<exists>cte. ctes_of s' (cte_map slot) = Some cte \<and> cap_relation c (cteCap cte)"
  for s' :: kernel_state
  by (auto simp: cte_wp_at_caps_of_state
           intro!: pspace_relation_ctes_ofI pspace_aligned_cross pspace_distinct_cross)

lemma caps_of_state_cross:
  "\<lbrakk> caps_of_state s slot = Some cap; pspace_aligned s; pspace_distinct s; (s,s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> \<exists>cap'. cteCaps_of s' (cte_map slot) = Some cap' \<and> cap_relation cap cap'"
  apply (erule state_relationE)
  apply (drule (3) pspace_relation_caps_of_state_cross)
  apply (fastforce simp: cteCaps_of_def)
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
                          split del: if_split)
  apply (clarsimp simp add: isCap_defs)
  by (rule ArchAcc_R.arch_cap_rights_update
         [simplified, simplified rights_mask_map_def])

lemma getCTE_wp:
  "\<lbrace>\<lambda>s. cte_at' p s \<longrightarrow> (\<exists>cte. cte_wp_at' ((=) cte) p s \<and> Q cte s)\<rbrace> getCTE p \<lbrace>Q\<rbrace>"
  apply (clarsimp simp add: getCTE_def valid_def cte_wp_at'_def)
  apply (drule getObject_cte_det)
  apply clarsimp
  done

lemma getCTE_ctes_of:
  "\<lbrace>\<lambda>s. ctes_of s p \<noteq> None \<longrightarrow> P (the (ctes_of s p)) (ctes_of s)\<rbrace> getCTE p \<lbrace>\<lambda>rv s. P rv (ctes_of s)\<rbrace>"
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma getCTE_wp':
  "\<lbrace>\<lambda>s. \<forall>cte. cte_wp_at' ((=) cte) p s \<longrightarrow> Q cte s\<rbrace> getCTE p \<lbrace>Q\<rbrace>"
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
    apply (rule corres_split[OF get_cap_corres])
      apply (rule corres_trivial, simp)
     apply (wp | simp)+
  done

lemma maskCapRights [simp]:
  "cap_relation c c' \<Longrightarrow>
  cap_relation (mask_cap msk c) (maskCapRights (rights_mask_map msk) c')"
  by (simp add: mask_cap_def cap_relation_masks)

lemma maskCap_valid [simp]:
  "s \<turnstile>' RetypeDecls_H.maskCapRights R cap = s \<turnstile>' cap"
  apply (simp    add: valid_cap'_def maskCapRights_def isCap_simps
                   capAligned_def X64_H.maskCapRights_def
            split: capability.split arch_capability.split
        split del: if_split)
  apply clarsimp (* FIXME arch-split: unclear why *)
  done

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
    apply (simp only: Let_def split: if_split_asm)
     prefer 2
     apply (simp add: in_monad)
    apply (simp only: in_bindE_R K_bind_def)
    apply (elim exE conjE)
    apply (simp only: split: if_split_asm)
     apply (clarsimp simp: in_monad locateSlot_conv stateAssert_def)
     apply (cases cap)
       apply (simp_all add: isCap_defs)[12]
     apply (clarsimp simp add: valid_cap'_def objBits_simps' cte_level_bits_def
                        split: option.split_asm)
    apply (simp only: in_bindE_R K_bind_def)
    apply (elim exE conjE)
    apply (simp only: cap_case_CNodeCap split: if_split_asm)
     apply (drule_tac cap=nextCap in isCapDs(4), elim exE)
     apply (simp only: in_bindE_R K_bind_def)
     apply (frule (12) 1 [OF refl], (assumption | rule refl)+)
     apply (clarsimp simp: in_monad locateSlot_conv objBits_simps stateAssert_def)
     apply (cases cap)
       apply (simp_all add: isCap_defs)[12]
     apply (frule in_inv_by_hoareD [OF getSlotCap_inv])
     apply simp
     apply (frule (1) post_by_hoare [OF getSlotCap_valid_cap])
     apply (simp add: valid_def validE_def validE_R_def)
     apply (erule allE, erule impE, blast)
     apply (drule (1) bspec)
     apply simp
    apply (clarsimp simp: in_monad locateSlot_conv objBits_simps stateAssert_def)
    apply (cases cap)
     apply (simp_all add: isCap_defs)[12]
    apply (frule in_inv_by_hoareD [OF getSlotCap_inv])
    apply (clarsimp simp: valid_cap'_def cte_level_bits_def objBits_defs)
    done
qed

lemma resolveAddressBits_cte_at':
  "\<lbrace> valid_objs' and valid_cap' cap \<rbrace>
  resolveAddressBits cap addr depth
  \<lbrace>\<lambda>rv. cte_at' (fst rv)\<rbrace>, \<lbrace>\<lambda>rv s. True\<rbrace>"
  apply (fold validE_R_def)
  apply (rule hoare_strengthen_postE_R)
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
               isCap_defs is_cap_defs Let_def badge_bits_def
               cap_rights_update_def badge_update_def
  { fix x :: machine_word
    define y where "y \<equiv> (x >> 6) && mask 58" (* guard_bits *)
    define z where "z \<equiv> unat (x && mask 6)" (* cnode_guard_size_bits *)
    have "of_bl (to_bl (y && mask z)) = (of_bl (replicate (64-z) False @ drop (64-z) (to_bl y))::machine_word)"
      by (simp add: bl_and_mask)
    then
    have "y && mask z = of_bl (drop (64 - z) (to_bl y))"
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
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap; simp add: simps arch_update_cap_data_def
                             X64_H.updateCapData_def)
  \<comment> \<open>CNodeCap\<close>
  apply (simp add: simps word_bits_def the_cnode_cap_def andCapRights_def
                   rightsFromWord_def data_to_rights_def nth_ucast cteRightsBits_def cteGuardBits_def)
  apply (insert x)
  apply (subgoal_tac "unat (x && mask 6) < unat (2^6::machine_word)")
   prefer 2
   apply (fold word_less_nat_alt)[1]
   apply (rule and_mask_less_size)
   apply (simp add: word_size)
  apply (simp add: word_bw_assocs cnode_padding_bits_def cnode_guard_size_bits_def)
  done
qed


lemma cte_map_shift:
  assumes bl: "to_bl cref' = zs @ cref"
  assumes pre: "guard \<le> cref"
  assumes len: "cbits + length guard \<le> length cref"
  assumes aligned: "is_aligned ptr (5 + cbits)" (* cte_level_bits *)
  assumes cbits: "cbits \<le> word_bits - cte_level_bits"
  shows
  "ptr + 32 * ((cref' >> length cref - (cbits + length guard)) && mask cbits) = \<comment> \<open>2^cte_level_bits\<close>
   cte_map (ptr, take cbits (drop (length guard) cref))"
proof -
  let ?l = "length cref - (cbits + length guard)"
  from pre obtain xs where
    xs: "cref = guard @ xs" by (auto simp: prefix_def less_eq_list_def)
  hence len_c: "length cref = length guard + length xs" by simp
  with len have len_x: "cbits \<le> length xs" by simp

  from bl xs
  have cref': "to_bl cref' = zs @ guard @ xs" by simp
  hence "length (to_bl cref') = length \<dots>" by simp
  hence 64: "64 = length zs + length guard + length xs" by simp

  have len_conv [simp]: "size ptr = word_bits"
    by (simp add: word_size word_bits_def)

  have "to_bl ((cref' >> ?l) && mask cbits) = (replicate (64 - cbits) False) @
        drop (64 - cbits) (to_bl (cref' >> ?l))"
    by (simp add: bl_shiftl word_size bl_and_mask
                  cte_level_bits_def word_bits_def)
  also
  from len_c len_x cref' 64
  have "\<dots> = (replicate (64 - cbits) False) @ take cbits xs"
    by (simp add: bl_shiftr word_size add.commute add.left_commute)
  also
  from len_x len_c 64
  have "\<dots> = to_bl (of_bl (take cbits (drop (length guard) cref)) :: machine_word)"
    by (simp add: xs word_rev_tf takefill_alt rev_take rev_drop)

  finally
    show ?thesis
      by (simp add: cte_map_def')
qed

lemma cte_map_shift':
  "\<lbrakk> to_bl cref' = zs @ cref; guard \<le> cref; length cref = cbits + length guard;
    is_aligned ptr (5 + cbits); cbits \<le> word_bits - cte_level_bits \<rbrakk> \<Longrightarrow>
  ptr + 32 * (cref' && mask cbits) = cte_map (ptr, drop (length guard) cref)"
  by (auto dest: cte_map_shift)

lemma cap_relation_Null2 [simp]:
  "cap_relation c NullCap = (c = cap.NullCap)"
  by (cases c) auto

lemmas cnode_cap_case_if = cap_case_CNodeCap

lemma corres_stateAssert_assume_stronger:
  "\<lbrakk> corres_underlying sr nf nf' r P Q f (g ());
    \<And>s s'. \<lbrakk> (s, s') \<in> sr; P s; Q s' \<rbrakk> \<Longrightarrow> P' s' \<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' r P Q f (stateAssert P' [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule_tac F="P' x" in corres_req)
     apply clarsimp
    apply (auto elim: corres_guard_imp)[1]
   apply wp+
  done

lemma cap_table_at_gsCNodes:
  "cap_table_at bits ptr s \<Longrightarrow> (s, s') \<in> state_relation
    \<Longrightarrow> gsCNodes s' ptr = Some bits"
  apply (clarsimp simp: state_relation_def ghost_relation_def
                        obj_at_def is_cap_table)
  apply blast
  done

lemma rab_corres':
  "\<lbrakk> cap_relation (fst a) c'; drop (64-bits) (to_bl cref') = snd a;
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
       drop (64 - bits) (to_bl cref') = vc \<rbrakk>
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
    note if_split [split del]
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
      note if_split [split del]
      from "1.prems"
      have ?thesis
        apply -
        apply (rule corres_assume_pre)
        apply (subgoal_tac "is_aligned ptr (5 + cbits) \<and> cbits \<le> word_bits - cte_level_bits") (*cte_level_bits *)
         prefer 2
         apply (clarsimp simp: caps)
         apply (erule valid_CNodeCapE)
           apply fastforce
          apply fastforce
         apply (fastforce simp: word_bits_def cte_level_bits_def)
        apply (thin_tac "t \<in> state_relation" for t)
        apply (erule conjE)
        apply (subst resolveAddressBits.simps)
        apply (subst resolve_address_bits'.simps)
        apply (simp add: caps isCap_defs Let_def)
        apply (simp add: linorder_not_less drop_postfix_eq)
        apply (simp add: liftE_bindE[where a="locateSlotCap a b" for a b])
        apply (simp add: locateSlot_conv)
        apply (rule corres_stateAssert_assume_stronger[rotated])
         apply (clarsimp simp: valid_cap_def cap_table_at_gsCNodes isCap_simps)
         apply (rule and_mask_less_size, simp add: word_bits_def word_size cte_level_bits_def)
        apply (erule exE)
        apply (cases "guard \<le> cref")
         prefer 2
         apply (clarsimp simp: guard_mask_shift lookup_failure_map_def unlessE_whenE)
        apply (clarsimp simp: guard_mask_shift unlessE_whenE)
        apply (cases "length cref < cbits + length guard")
         apply (simp add: lookup_failure_map_def)
        apply simp
        apply (cases "length cref = cbits + length guard")
         apply clarsimp
         apply (rule corres_noopE)
          prefer 2
          apply wp
         apply wp
         apply (clarsimp simp: objBits_simps cte_level_bits_def)
         apply (erule (2) valid_CNodeCapE)
         apply (erule (3) cte_map_shift')
         apply simp
        apply simp
        apply (subgoal_tac "cbits + length guard < length cref"; simp)
        apply (rule corres_initial_splitE)
           apply clarsimp
           apply (rule corres_guard_imp)
             apply (rule getSlotCap_corres)
             apply (simp add: objBits_simps cte_level_bits_def)
             apply (erule (1) cte_map_shift)
               apply simp
              apply assumption
             apply (simp add: cte_level_bits_def)
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
           apply (subgoal_tac "64 + (cbits + length guard) - length cref = (cbits + length guard) + (64 - length cref)")
            prefer 2
            apply (drule len_drop_lemma)
             apply simp
            apply arith
           apply simp
           apply (subst drop_drop [symmetric])
           apply simp
          apply wp
          apply (clarsimp simp: objBits_simps cte_level_bits_def)
          apply (erule (1) cte_map_shift)
            apply simp
           apply assumption
          apply (simp add: cte_level_bits_def)
         apply (wp get_cap_wp)
         apply clarsimp
         apply (erule (1) cte_wp_valid_cap)
        apply wpsimp
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

lemma getThreadCSpaceRoot:
  "getThreadCSpaceRoot t = return t"
  by (simp add: getThreadCSpaceRoot_def locateSlot_conv
                tcbCTableSlot_def)

lemma getThreadVSpaceRoot:
  "getThreadVSpaceRoot t = return (t+2^cteSizeBits)" (*2^cte_level_bits*)
  by (simp add: getThreadVSpaceRoot_def locateSlot_conv objBits_simps'
                tcbVTableSlot_def shiftl_t2n cte_level_bits_def)

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

lemma lookupSlotForThread_corres:
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
    apply (rule hoare_weaken_preE)
     apply (rule resolve_address_bits_cte_at [unfolded validE_R_def])
    apply clarsimp
   prefer 2
   apply (rule hoare_weaken_preE)
    apply (rule resolveAddressBits_cte_at')
   apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (simp add: returnOk_def split_def)
  done

lemmas rab_cte_at' [wp] = resolveAddressBits_cte_at' [folded validE_R_def]

lemma lookupSlot_cte_at_wp[wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupSlotForThread t addr \<lbrace>\<lambda>rv. cte_at' rv\<rbrace>, \<lbrace>\<lambda>r. \<top>\<rbrace>"
  apply (simp add: lookupSlotForThread_def)
  apply (simp add: getThreadCSpaceRoot_def locateSlot_conv tcbCTableSlot_def)
  apply (wp | simp add: split_def)+
  done

lemma lookupSlot_inv[wp]:
  "\<lbrace>P\<rbrace> lookupSlotForThread t addr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookupSlotForThread_def)
  apply (simp add: getThreadCSpaceRoot_def locateSlot_conv tcbCTableSlot_def)
  apply (wp | simp add: split_def)+
  done

lemma lookupCap_corres:
 "corres (lfr \<oplus> cap_relation)
         (valid_objs and pspace_aligned and tcb_at t)
         (valid_objs' and pspace_aligned' and pspace_distinct' and tcb_at' t)
         (lookup_cap t (to_bl ref)) (lookupCap t ref)"
  apply (simp add: lookup_cap_def lookupCap_def bindE_assoc
                   lookupCapAndSlot_def liftME_def split_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF lookupSlotForThread_corres])
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
                        obj_at'_def ps_clear_upd projectKOs
             split del: if_split)
  apply (clarsimp elim!: rsubst[where P=P'])
  apply (clarsimp simp: updateObject_cte in_monad objBits_simps
                        tcbCTableSlot_def tcbVTableSlot_def x
                        typeError_def
                 split: if_split_asm
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

lemma setCTE_ctes_of_wp [wp]:
  "\<lbrace>\<lambda>s. P ((ctes_of s) (p \<mapsto> cte))\<rbrace>
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
  apply (wp setCTE_weak_cte_wp_at getCTE_wp)
  apply (auto simp: cte_wp_at'_def)
  done

lemma cte_wp_at_extract':
  "\<lbrakk> cte_wp_at' (\<lambda>c. c = x) p s; cte_wp_at' P p s \<rbrakk> \<Longrightarrow> P x"
  by (clarsimp simp: cte_wp_at_ctes_of)

lemmas setCTE_valid_objs = setCTE_valid_objs'

lemma capFreeIndex_update_valid_cap':
  "\<lbrakk>fa \<le> fb; fb \<le> 2 ^ bits; is_aligned (of_nat fb :: machine_word) minUntypedSizeBits;
    s \<turnstile>' capability.UntypedCap d v bits fa\<rbrakk>
   \<Longrightarrow> s \<turnstile>' capability.UntypedCap d v bits fb"
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
  "s \<turnstile>' capability.UntypedCap d v0a v1a fa \<Longrightarrow>
   s \<turnstile>' capability.UntypedCap d v0a v1a (maxFreeIndex v1a)"
  apply (rule capFreeIndex_update_valid_cap'[rotated -1])
   apply assumption
  apply (clarsimp simp: valid_cap'_def capAligned_def ko_wp_at'_def
                        maxFreeIndex_def shiftL_nat)+
  apply (erule is_aligned_weaken[OF is_aligned_triv])
  done

lemma ctes_of_valid_cap'':
  "\<lbrakk> ctes_of s p = Some r; valid_objs' s\<rbrakk> \<Longrightarrow> s \<turnstile>' (cteCap r)"
  apply (rule cte_wp_at_valid_objs_valid_cap'[where P="(=) r", simplified])
   apply (simp add: cte_wp_at_ctes_of)
  apply assumption
  done

lemma cap_insert_objs' [wp]:
  "\<lbrace>valid_objs' and valid_cap' cap\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: cteInsert_def updateCap_def setUntypedCapAsFull_def)
  apply (wpsimp wp: setCTE_valid_objs | wp getCTE_wp')+
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps
                  dest!: ctes_of_valid_cap'')
  done

lemma cteInsert_weak_cte_wp_at:
  "\<lbrace>\<lambda>s. if p = dest then P cap else p \<noteq> src \<and>
        cte_wp_at' (\<lambda>c. P (cteCap c)) p s\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>uu. cte_wp_at'(\<lambda>c. P (cteCap c)) p\<rbrace>"
  unfolding cteInsert_def error_def updateCap_def setUntypedCapAsFull_def
  apply (simp add: bind_assoc split del: if_split)
  apply (wp setCTE_weak_cte_wp_at updateMDB_weak_cte_wp_at hoare_weak_lift_imp | simp)+
   apply (wp getCTE_ctes_wp)+
   apply (clarsimp simp: isCap_simps split:if_split_asm| rule conjI)+
done

lemma setCTE_valid_cap:
  "\<lbrace>valid_cap' c\<rbrace> setCTE ptr cte \<lbrace>\<lambda>r. valid_cap' c\<rbrace>"
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

lemma prev_next_update:
  "cteMDBNode_update (mdbNext_update f) (cteMDBNode_update (mdbPrev_update f') x) =
   cteMDBNode_update (mdbPrev_update f') (cteMDBNode_update (mdbNext_update f) x)"
  apply (cases x)
  apply (rename_tac cap mdbnode)
  apply (case_tac mdbnode)
  apply simp
  done

lemmas modify_map_prev_next_up [simp] =
  modify_map_com [where f="cteMDBNode_update (mdbNext_update f)" and
                        g="cteMDBNode_update (mdbPrev_update f')" for f f',
                  OF prev_next_update]

lemma update_prev_next_trancl:
  assumes nxt: "m \<turnstile> x \<leadsto>\<^sup>+ y"
  shows "(modify_map m ptr (cteMDBNode_update (mdbPrev_update z))) \<turnstile> x \<leadsto>\<^sup>+ y"
proof (cases "m ptr")
  case None
  thus ?thesis using nxt
    by (simp add: modify_map_def)
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
    by (simp add: modify_map_def)
next
  case (Some cte)
  let ?m = "m(ptr \<mapsto> cteMDBNode_update (mdbPrev_update z) cte)"

  from nxt have "m \<turnstile> x \<leadsto>\<^sup>+ y"
  proof induct
    case (base y)
    thus ?case using Some
      by (fastforce simp: modify_map_def mdb_next_update next_unfold' split: if_split_asm)
  next
    case (step q r)
    show ?case
    proof
      show "m \<turnstile> q \<leadsto> r" using step(2) Some
      by (auto simp: modify_map_def mdb_next_update next_unfold' split: if_split_asm)
    qed fact+
  qed
  thus ?thesis using Some
    by (simp add: modify_map_def)
qed

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
  cte_mdb_prop :: "(machine_word \<rightharpoonup> cte) \<Rightarrow> machine_word \<Rightarrow> (mdbnode \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cte_mdb_prop m p P \<equiv> (\<exists>cte. m p = Some cte \<and> P (cteMDBNode cte))"

lemma cte_mdb_prop_no_0:
  "\<lbrakk> no_0 m; cte_mdb_prop m p P \<rbrakk> \<Longrightarrow> p \<noteq> 0"
  unfolding cte_mdb_prop_def no_0_def
  by auto

lemma mdb_chain_0_modify_map_prev:
  "mdb_chain_0 m \<Longrightarrow> mdb_chain_0 (modify_map m ptr (cteMDBNode_update (mdbPrev_update f)))"
  unfolding mdb_chain_0_def
  apply rule
  apply (rule update_prev_next_trancl)
   apply (clarsimp simp: modify_map_def dom_def split: option.splits if_split_asm)
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
    by (clarsimp simp: modify_map_def dom_def split: if_split_asm)
  hence x0: "m \<turnstile> x \<leadsto>\<^sup>+ 0" using chain unfolding mdb_chain_0_def by simp

  from dom have t0: "m \<turnstile> target \<leadsto>\<^sup>+ 0"
    using chain unfolding mdb_chain_0_def by simp

  show "?M \<turnstile> x \<leadsto>\<^sup>+ 0"
  proof (cases "m ptr")
    case None
    thus ?thesis
      by (simp add: modify_map_def) (rule x0)
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

definition
  "capASID cap \<equiv> case cap of
    ArchObjectCap (PageCap _ _ _ _ _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageDirectoryCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PDPointerTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PML4Cap _ (Some asid)) \<Rightarrow> Some asid
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
    ArchObjectCap (PageCap _ _ _ _ _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | ArchObjectCap (PageTableCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | ArchObjectCap (PageDirectoryCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
  | ArchObjectCap (PDPointerTableCap _ (Some (_, vptr))) \<Rightarrow> Some vptr
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
  \<comment> \<open>check all fields of ReplyCap except capReplyCanGrant\<close>
  (isReplyCap cap \<longrightarrow> capTCBPtr cap = capTCBPtr cap' \<and>
                     capReplyMaster cap = capReplyMaster cap')"

lemma capASID_update [simp]:
  "capASID (RetypeDecls_H.updateCapData P x c) = capASID c"
  unfolding capASID_def
  apply (cases c, simp_all add: updateCapData_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: updateCapData_def
                       X64_H.updateCapData_def
                       isCap_simps Let_def)
  done

lemma cap_vptr_update' [simp]:
  "cap_vptr' (RetypeDecls_H.updateCapData P x c) = cap_vptr' c"
  unfolding capASID_def
  apply (cases c, simp_all add: updateCapData_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: updateCapData_def
                       X64_H.updateCapData_def
                       isCap_simps Let_def)
  done

lemma cap_asid_base_update' [simp]:
  "cap_asid_base' (RetypeDecls_H.updateCapData P x c) = cap_asid_base' c"
  unfolding cap_asid_base'_def
  apply (cases c, simp_all add: updateCapData_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: updateCapData_def
                       X64_H.updateCapData_def
                       isCap_simps Let_def)
  done

lemma updateCapData_Master:
  "updateCapData P d cap \<noteq> NullCap \<Longrightarrow>
   capMasterCap (updateCapData P d cap) = capMasterCap cap"
  apply (cases cap, simp_all add: updateCapData_def isCap_simps Let_def
                           split: if_split_asm)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability, simp_all add: X64_H.updateCapData_def)
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

lemma maskCapRights_Reply[simp]:
  "isReplyCap (maskCapRights r c) = isReplyCap c"
  apply (insert capMasterCap_maskCapRights)
  apply (rule master_eqI, rule isCap_Master)
  apply simp
  done

lemma capASID_mask [simp]:
  "capASID (maskCapRights x c) = capASID c"
  unfolding capASID_def
  apply (cases c, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: maskCapRights_def X64_H.maskCapRights_def isCap_simps Let_def)
  done

lemma cap_vptr_mask' [simp]:
  "cap_vptr' (maskCapRights x c) = cap_vptr' c"
  unfolding cap_vptr'_def
  apply (cases c, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: maskCapRights_def X64_H.maskCapRights_def isCap_simps Let_def)
  done

lemma cap_asid_base_mask' [simp]:
  "cap_asid_base' (maskCapRights x c) = cap_asid_base' c"
  unfolding cap_vptr'_def
  apply (cases c, simp_all add: maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: maskCapRights_def X64_H.maskCapRights_def isCap_simps Let_def)
  done

lemmas cteInsert_valid_objs = cap_insert_objs'

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
       apply (clarsimp simp: parentOf_def  split: if_split_asm)
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

lemma ps_clear_32:
  "\<lbrakk> ps_clear p tcbBlockSizeBits s; is_aligned p tcbBlockSizeBits \<rbrakk>
    \<Longrightarrow> ksPSpace s (p + 2^cteSizeBits) = None"
  apply (simp add: ps_clear_def)
  apply (drule equals0D[where a="p + 2^cteSizeBits"])
  apply (simp add: dom_def add.commute objBits_defs take_bit_Suc mask_def)
  apply (drule mp)
   apply (rule word_plus_mono_right)
    apply simp
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (erule mp)
  apply (erule is_aligned_no_wrap')
  apply simp
  done

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
   apply (clarsimp simp: cte_map_def split_def
                         well_formed_cnode_n_def length_set_helper ex_with_length
                         valid_obj_def valid_cs_size_def valid_cs_def)
   apply (subgoal_tac "of_bl (snd p) * 2^cte_level_bits < 2 ^ (cte_level_bits + length (snd p))")
    apply (rule conjI)
     apply (erule is_aligned_no_wrap')
     apply assumption
    apply (subst add_diff_eq[symmetric])
    apply (rule word_plus_mono_right)
     apply (erule word_le_minus_one_leq)
    apply (erule is_aligned_no_wrap')
    apply (rule word_power_less_1)
    apply (simp add: cte_level_bits_def word_bits_def)
   apply (simp add: power_add)
   apply (subst mult.commute, rule word_mult_less_mono1)
     apply (rule of_bl_length)
     apply (simp add: word_bits_def)
    apply (simp add: cte_level_bits_def)
   apply (simp add: cte_level_bits_def word_bits_def)
   apply (drule power_strict_increasing [where a="2 :: nat"])
    apply simp
   apply simp
  apply (clarsimp simp: cte_map_def split_def field_simps)
  apply (subgoal_tac "of_bl (snd p) * 2^cte_level_bits < (2^tcb_bits :: machine_word)")
   apply (drule(1) pspace_alignedD[rotated])
   apply (rule conjI)
    apply (erule is_aligned_no_wrap')
     apply (simp add: word_bits_conv)
    apply simp
   apply (rule word_plus_mono_right)
    apply (drule word_le_minus_one_leq)
    apply simp
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1 cte_level_bits_def
              split: if_split_asm)
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
  apply (thin_tac "b \<le> a" for b a)+
  apply (rule notE[OF neq])
  apply (insert cte_at_length_limit [OF c1 vo])
  apply (simp add: shiftl_t2n[where n=5, simplified, simplified mult.commute, symmetric]
                   word_bits_def cte_level_bits_def prod_eq_iff)
  apply (insert cte_at_cref_len[where p="fst p" and c="snd p" and c'="snd p'", simplified, OF c1])
  apply (simp add: c2 prod_eqI)
  apply (subst rev_is_rev_conv[symmetric])
  apply (rule nth_equalityI)
   apply simp
  apply clarsimp
  apply (drule_tac x="i + 5" in word_eqD)
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
   \<exists>getF' setF' restr. tcb_cap_cases (tcb_cnode_index (unat ((v - x) >> cte_level_bits))) = Some (getF', setF', restr)
          \<and> cte_map (x, tcb_cnode_index (unat ((v - x) >> cte_level_bits))) = v
          \<and> (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow> cap_relation (getF' tcb) (cteCap (getF tcb')))
          \<and> (\<forall>tcb tcb' cap cte. tcb_relation tcb tcb' \<longrightarrow> cap_relation cap (cteCap cte)
                        \<longrightarrow> tcb_relation (setF' (\<lambda>x. cap) tcb) (setF (\<lambda>x. cte) tcb'))"
  apply (clarsimp simp: tcb_cte_cases_def tcb_relation_def cte_level_bits_def cteSizeBits_def
                        tcb_cap_cases_simps[simplified]
                 split: if_split_asm)
  apply (simp_all add: tcb_cnode_index_def cte_level_bits_def cte_map_def field_simps to_bl_1)
  done

lemma other_obj_relation_KOCTE[simp]:
  "\<not> other_obj_relation ko (KOCTE cte)"
  by (simp add: other_obj_relation_def
         split: Structures_A.kernel_object.splits
                X64_A.arch_kernel_obj.splits)

lemma cte_map_pulls_tcb_to_abstract:
  "\<lbrakk> y = cte_map z; pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' x = Some (KOTCB tcb);
     pspace_aligned s; pspace_distinct s; valid_objs s;
     cte_at z s; (y - x) \<in> dom tcb_cte_cases \<rbrakk>
     \<Longrightarrow> \<exists>tcb'. kheap s x = Some (TCB tcb') \<and> tcb_relation tcb' tcb
                  \<and> (z = (x, tcb_cnode_index (unat ((y - x) >> cte_level_bits))))"
  apply (rule pspace_dom_relatedE, assumption+)
  apply (erule(1) obj_relation_cutsE;
         clarsimp simp: other_obj_relation_def
                 split: Structures_A.kernel_object.split_asm
                        X64_A.arch_kernel_obj.split_asm if_split_asm)
  apply (drule tcb_cases_related2)
  apply clarsimp
  apply (frule(1) cte_wp_at_tcbI [OF _ _ TrueI, where t="(a, b)" for a b, simplified])
  apply (erule(5) cte_map_inj_eq [OF sym])
  done

lemma pspace_relation_update_tcbs:
  "\<lbrakk> pspace_relation s s'; s x = Some (TCB otcb); s' x = Some (KOTCB otcb');
        tcb_relation tcb tcb' \<rbrakk>
       \<Longrightarrow> pspace_relation (s(x \<mapsto> TCB tcb)) (s'(x \<mapsto> KOTCB tcb'))"
  apply (simp add: pspace_relation_def pspace_dom_update
                   dom_fun_upd2
              del: dom_fun_upd)
  apply (erule conjE)
  apply (rule ballI, drule(1) bspec)
  apply (clarsimp simp: tcb_relation_cut_def split: Structures_A.kernel_object.split_asm)
  apply (drule bspec, fastforce)
  apply clarsimp
  apply (erule(1) obj_relation_cutsE, simp_all split: if_split_asm)
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
  apply (rule cte_wp_at_cteI, (fastforce split: if_split_asm)+)
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
                    simp del: dom_fun_upd split del: if_split)
    apply (rule conjI)
     apply (erule subst[where t="dom s'"])
     apply (simp add: pspace_dom_def obj_relation_cuts2)
    apply (simp add: obj_relation_cuts2)
    apply (rule ballI, drule(1) bspec)+
    apply clarsimp
    apply (intro conjI impI)
     apply (simp add: s'')
     apply (rule obj_relation_cutsE, assumption+, simp_all split: if_split_asm)[1]
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
   apply (clarsimp simp: etcb_relation_def tcb_cte_cases_def split: if_split_asm)
  apply (clarsimp simp: pspace_relations_def)
  apply (frule(5) cte_map_pulls_cte_to_abstract[OF p])
  apply (clarsimp simp: set_cap_def split_def bind_def get_object_def
                        simpler_gets_def assert_def a_type_def fail_def return_def
                        set_object_def get_def put_def domI)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_cs_def valid_cs_size_def exI)
  apply (rule conjI, clarsimp)
   apply (rule conjI)
    apply (erule(1) pspace_relation_update_ctes[where cap=c])
     apply clarsimp
     apply (intro conjI impI)
      apply (rule ext, clarsimp simp add: domI p)
      apply (drule cte_map_inj_eq [OF _ _ cr(6) cr(3-5)])
       apply (simp add: cte_at_cases domI)
      apply (simp add: prod_eq_iff)
     apply (insert p)[1]
     apply (clarsimp split: option.split Structures_A.kernel_object.split
                    intro!: ext)
     apply (drule cte_map_inj_eq [OF _ _ cr(6) cr(3-5)])
      apply (simp add: cte_at_cases domI well_formed_cnode_invsI[OF cr(3)])
     apply clarsimp
    apply (simp add: c)
   apply (clarsimp simp: ekheap_relation_def pspace_relation_def)
   apply (drule bspec, erule domI)
   apply (clarsimp simp: etcb_relation_def tcb_cte_cases_def split: if_split_asm)
  apply (simp add: wf_cs_insert)
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
  apply (drule use_valid [OF _ getCTE_sp[where P="\<lambda>s. s2 = s" for s2], OF _ refl])
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
                 split: Structures_A.kernel_object.split_asm if_split_asm)
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

lemma setObject_cte_tcbSchedPrevs_of_use_valid_ksPSpace:
  assumes step: "(x, s\<lparr>ksPSpace := ps\<rparr>) \<in> fst (setObject p (cte :: cte) s)"
  assumes pre: "P (tcbSchedPrevs_of s)"
  shows "P (ps |> tcb_of' |> tcbSchedPrev)"
  using use_valid[OF step setObject_cte_tcbSchedPrevs_of(1)] pre
  by auto

lemma setObject_cte_tcbSchedNexts_of_use_valid_ksPSpace:
  assumes step: "(x, s\<lparr>ksPSpace := ps\<rparr>) \<in> fst (setObject p (cte :: cte) s)"
  assumes pre: "P (tcbSchedNexts_of s)"
  shows "P (ps |> tcb_of' |> tcbSchedNext)"
  using use_valid[OF step setObject_cte_tcbSchedNexts_of(1)] pre
  by auto

lemma setObject_cte_inQ_of_use_valid_ksPSpace:
  assumes step: "(x, s\<lparr>ksPSpace := ps\<rparr>) \<in> fst (setObject p (cte :: cte) s)"
  assumes pre: "P (inQ domain priority |< tcbs_of' s)"
  shows "P (inQ domain priority |< (ps |> tcb_of'))"
  using use_valid[OF step setObject_cte_inQ(1)] pre
  by auto

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
         (pspace_distinct' s' \<longrightarrow> pspace_distinct' s'') \<and>
         tcbSchedPrevs_of s'' = tcbSchedPrevs_of s' \<and>
         tcbSchedNexts_of s'' = tcbSchedNexts_of s' \<and>
         (\<forall>domain priority.
            (inQ domain priority |< tcbs_of' s'') = (inQ domain priority |< tcbs_of' s'))"
  using assms
  apply (clarsimp simp: updateCap_def in_monad)
  apply (drule use_valid [where P="\<lambda>s. s2 = s" for s2, OF _ getCTE_sp refl])
  apply (rule conjI)
   apply (erule use_valid [OF _ setCTE_ctes_of_wp])
   apply (clarsimp simp: cte_wp_at_ctes_of modify_map_apply)
  apply (frule setCTE_pspace_only)
  apply (clarsimp simp: setCTE_def)
  apply (intro conjI impI)
      apply (erule(1) use_valid [OF _ setObject_aligned])
     apply (erule(1) use_valid [OF _ setObject_distinct])
    apply (erule setObject_cte_tcbSchedPrevs_of_use_valid_ksPSpace; simp)
   apply (erule setObject_cte_tcbSchedNexts_of_use_valid_ksPSpace; simp)
  apply (fastforce elim: setObject_cte_inQ_of_use_valid_ksPSpace)
  done

(* FIXME: move *)
lemma pspace_relation_cte_wp_atI':
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
     cte_wp_at' ((=) cte) x s'; valid_objs s \<rbrakk>
  \<Longrightarrow> \<exists>c slot. cte_wp_at ((=) c) slot s \<and> cap_relation c (cteCap cte) \<and> x = cte_map slot"
  apply (simp add: cte_wp_at_cases')
  apply (elim disjE conjE exE)
   apply (erule(1) pspace_dom_relatedE)
   apply (erule(1) obj_relation_cutsE, simp_all split: if_split_asm)[1]
   apply (intro exI, rule conjI[OF _ conjI [OF _ refl]])
    apply (simp add: cte_wp_at_cases domI well_formed_cnode_invsI)
   apply (simp split: if_split_asm)
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE, simp_all split: if_split_asm)
   apply (subgoal_tac "n = x - y", clarsimp)
    apply (drule tcb_cases_related2, clarsimp)
    apply (intro exI, rule conjI)
     apply (erule(1) cte_wp_at_tcbI[where t="(a, b)" for a b, simplified])
     apply fastforce
    apply simp
   apply clarsimp
  apply (simp add: other_obj_relation_def
            split: Structures_A.kernel_object.split_asm X64_A.arch_kernel_obj.split_asm)
  done

lemma pspace_relation_cte_wp_atI:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
     ctes_of (s' :: kernel_state) x = Some cte; valid_objs s \<rbrakk>
  \<Longrightarrow> \<exists>c slot. cte_wp_at ((=) c) slot s \<and> cap_relation c (cteCap cte) \<and> x = cte_map slot"
  apply (erule pspace_relation_cte_wp_atI'[where x=x])
   apply (simp add: cte_wp_at_ctes_of)
  apply assumption
  done

lemma caps_of_state_rev_cross:
  "\<lbrakk> ctes_of s' p = Some cte; valid_objs s; (s,s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> \<exists>cap slot. caps_of_state s slot = Some cap \<and> p = cte_map slot \<and> cap_relation cap (cteCap cte)"
  apply (erule state_relationE)
  apply (drule (2) pspace_relation_cte_wp_atI)
  apply (fastforce simp: cte_wp_at_caps_of_state)
  done

lemma cap_relation_IOPortControlCap[simp]:
  "cap_relation cap (ArchObjectCap IOPortControlCap) =
   (cap = Structures_A.ArchObjectCap X64_A.IOPortControlCap)"
  apply (cases cap; simp)
  apply (rename_tac acap, case_tac acap; simp)
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
    c: "cte_wp_at ((=) c) slot s" and
    final: "is_final_cap' c s" and
    fm: "final_matters c"
    by (auto simp add: cte_wp_at_cases)
  with valid psr cte
  have cr: "cap_relation c (cteCap cte)"
    by (auto dest!: pspace_relation_ctes_ofI)
  from cte' psr valid
  obtain slot' c' where
    c': "cte_wp_at ((=) c') slot' s" and
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
  have arch_ref: "arch_gen_refs c = arch_gen_refs c'" using fm reg
    by (clarsimp simp: final_matters_def is_cap_simps arch_gen_obj_refs_def
                   split: cap.split_asm arch_cap.split_asm)

  from final have refs_non_empty: "obj_refs c \<noteq> {} \<or> cap_irqs c \<noteq> {} \<or> arch_gen_refs c \<noteq> {}"
    by (clarsimp simp add: is_final_cap'_def gen_obj_refs_def)

  define S where "S \<equiv> {cref. \<exists>cap'. fst (get_cap cref s) = {(cap', s)} \<and>
                                    (gen_obj_refs c \<inter> gen_obj_refs cap' \<noteq> {})}"

  have "is_final_cap' c s = (\<exists>cref. S = {cref})"
    by (simp add: is_final_cap'_def S_def)
  moreover
  from c refs_non_empty
  have "slot \<in> S" by (simp add: S_def cte_wp_at_def gen_obj_refs_def)
  moreover
  from c' refs_non_empty ref irq arch_ref
  have "slot' \<in> S" by (simp add: S_def cte_wp_at_def gen_obj_refs_def)
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

lemma arch_gen_refs_relation_Master:
  "cap_relation cap cap' \<Longrightarrow>
   arch_gen_refs cap = (case capMasterCap cap' of ArchObjectCap (IOPortCap f l) \<Rightarrow> {IOPortRef f} | _ \<Rightarrow> {})"
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
    c: "cte_wp_at ((=) c) slot s" and
    final: "is_final_cap' c s"
    by (auto simp add: cte_wp_at_cases)
  with valid psr cte
  have cr: "cap_relation c (cteCap cte)"
    by (auto dest!: pspace_relation_ctes_ofI)
  from cte' psr valid
  obtain slot' c' where
    c': "cte_wp_at ((=) c') slot' s" and
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
  have arch_ref: "arch_gen_refs c = arch_gen_refs c'"
  using master cr cr'
  by (clarsimp simp: arch_gen_refs_relation_Master)

  from final have refs_non_empty: "obj_refs c \<noteq> {} \<or> cap_irqs c \<noteq> {} \<or> arch_gen_refs c \<noteq> {}"
    by (clarsimp simp add: is_final_cap'_def gen_obj_refs_def)

  define S where "S \<equiv> {cref. \<exists>cap'. fst (get_cap cref s) = {(cap', s)} \<and>
                                    (gen_obj_refs c \<inter> gen_obj_refs cap' \<noteq> {})}"

  have "is_final_cap' c s = (\<exists>cref. S = {cref})"
    by (simp add: is_final_cap'_def S_def)
  moreover
  from c refs_non_empty
  have "slot \<in> S" by (simp add: S_def cte_wp_at_def gen_obj_refs_def)
  moreover
  from c' refs_non_empty ref irq arch_ref
  have "slot' \<in> S" by (simp add: S_def cte_wp_at_def gen_obj_refs_def)
  ultimately
  show False using s final by auto
qed

lemma isMDBParent_sameRegion:
  "isMDBParentOf cte cte' \<Longrightarrow> sameRegionAs (cteCap cte) (cteCap cte')"
  by (simp add: isMDBParentOf_def split: cte.split_asm if_split_asm)

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
       apply (rename_tac capability mdbnode)
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
      apply (rule arg_cong[where f="\<lambda>S. v \<in> S\<^sup>+" for v])
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
      apply (cases cte)
      apply (case_tac cte')
      apply (rename_tac cap' node')
      apply (clarsimp)
      apply (frule(1) ztc_child)
      apply (case_tac "isUntypedCap cap'")
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
          apply (clarsimp simp: mdb_next_unfold m'_def m split: if_split_asm)
         apply assumption
        apply (insert z m t pu)
        apply (simp add: cap'_def)
        apply (simp add: m'_def parentOf_def split: if_split_asm)
         apply (clarsimp simp: parent2)
        apply (clarsimp simp add: notparent2 [OF _ _ P])
        done
    next
      case (trans_parent c' c'')
      thus ?case
        using subtree_neq [OF subtree.trans_parent [OF trans_parent(1, 3-5)]]
        apply -
        apply (erule subtree.trans_parent)
          apply (clarsimp simp: mdb_next_unfold m'_def m split: if_split_asm)
         apply assumption
        apply (insert z m t pu)
        apply (simp add: cap'_def)
        apply (simp add: m'_def parentOf_def split: if_split_asm)
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
  "\<lbrakk> cte_wp_at' ((=) cte) p s; valid_objs' s \<rbrakk>
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
  apply (fastforce)
  done

lemma no_fail_setCTE [wp]:
  "no_fail (cte_at' p) (setCTE p c)"
  apply (clarsimp simp: setCTE_def setObject_def split_def unless_def
                        updateObject_cte alignCheck_def alignError_def
                        typeError_def is_aligned_mask[symmetric]
                  cong: kernel_object.case_cong)
  apply (wp|wpc)+
  apply (clarsimp simp: cte_wp_at'_def getObject_def split_def
                        in_monad loadObject_cte
                 dest!: in_singleton
             split del: if_split)
  apply (clarsimp simp: typeError_def alignCheck_def alignError_def
                        in_monad is_aligned_mask[symmetric] objBits_simps
                        magnitudeCheck_def
                 split: kernel_object.split_asm if_split_asm option.splits
             split del: if_split)
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
  by (simp add: capRange_def objBits_simps' cte_level_bits_def
                asid_low_bits_def zbits_map_def bit_simps
         split: cap_relation_split_asm arch_cap.split_asm
                option.split sum.split)

lemma cap_relation_untyped_ptr_obj_refs:
  "cap_relation cap cap' \<Longrightarrow> capClass cap' = PhysicalClass \<Longrightarrow> \<not> isUntypedCap cap'
        \<Longrightarrow> capUntypedPtr cap' \<in> obj_refs cap"
  by (clarsimp simp add: isCap_simps
               simp del: not_ex
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
  apply (erule(3) final_cap_duplicate [where r="ObjRef (capUntypedPtr (cteCap cte))",
                                       OF _ _ distinct_lemma[where f=cte_map]])
    apply (rule obj_ref_is_gen_obj_ref)
    apply (erule(1) obj_refs_cap_relation_untyped_ptr)
   apply (rule obj_ref_is_gen_obj_ref)
   apply (erule(1) obj_refs_cap_relation_untyped_ptr)
  apply (rule obj_ref_is_gen_obj_ref)
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

lemma updateCap_corres:
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
  apply (frule (3) set_cap_not_quite_corres; fastforce?)
   apply (erule cte_wp_at_weakenE, rule TrueI)
  apply clarsimp
  apply (rule bexI)
   prefer 2
   apply simp
  apply (clarsimp simp: in_set_cap_cte_at_swp pspace_relations_def)
  apply (drule updateCap_stuff)
  apply simp
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    apply (unfold cdt_list_relation_def)[1]
    apply (intro allI impI)
    apply (erule_tac x=c in allE)
    subgoal by (auto elim!: modify_map_casesE)[1]
   apply (unfold revokable_relation_def)[1]
   apply (drule set_cap_caps_of_state_monad)
   apply (simp add: cte_wp_at_caps_of_state del: split_paired_All)
   apply (intro allI impI)
   apply (erule_tac x=c in allE)
   apply (erule impE[where P="\<exists>y. v = Some y" for v])
    subgoal by (clarsimp simp: null_filter_def is_zombie_def split: if_split_asm)
   subgoal by (auto elim!: modify_map_casesE del: disjE)[1] (* slow *)
  apply (case_tac "ctes_of b (cte_map slot)")
   apply (simp add: modify_map_None)
  apply (simp add: modify_map_apply)
  apply (simp add: cdt_relation_def del: split_paired_All)
  apply (intro allI impI)
  apply (rule use_update_ztc_one [OF descendants_of_update_ztc])
         apply simp
        apply assumption
       subgoal by (auto simp: is_cap_simps isCap_simps)[1]
      apply (frule(3) is_final_untyped_ptrs [OF _ _ not_sym], clarsimp+)
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       subgoal by (simp add: is_cap_simps, elim disjE exE, simp_all)[1]
      apply (simp add: eq_commute)
     apply (drule cte_wp_at_norm, clarsimp)
     apply (drule(1) pspace_relation_ctes_ofI, clarsimp+)
     apply (drule(1) capClass_ztc_relation)+
     apply (simp add: capRange_cap_relation obj_ref_of_relation[symmetric])
    apply (rule valid_capAligned, rule ctes_of_valid)
     apply (simp add: cte_wp_at_ctes_of)
    apply clarsimp
   apply (drule cte_wp_at_norm, clarsimp)
   apply (drule(1) pspace_relation_ctes_ofI, clarsimp+)
   subgoal by (simp add: is_cap_simps, elim disjE exE, simp_all add: isCap_simps)[1]
  apply clarsimp
  done

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
  apply (clarsimp simp: updateMDB_def Let_def in_monad split: if_split_asm)
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
  apply (clarsimp simp: updateMDB_def Let_def in_monad split: if_split_asm)
  apply (drule_tac P="(=) s'" in use_valid [OF _ getCTE_sp], rule refl)
  apply clarsimp
  apply (clarsimp simp: setCTE_def setObject_def in_monad
                        split_def)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim disjE conjE exE)
   apply (clarsimp simp: cte_wp_at_cases' lookupAround2_char1)
   apply (erule disjE)
    apply (clarsimp simp: tcb_ctes_clear cte_level_bits_def objBits_defs)
   apply clarsimp
   apply (rule pspace_dom_relatedE, assumption+)
   apply (rule obj_relation_cutsE, assumption+;
          clarsimp split: Structures_A.kernel_object.split_asm
                          X64_A.arch_kernel_obj.split_asm if_split_asm
                    simp: other_obj_relation_def)
   apply (frule(1) tcb_cte_cases_aligned_helpers(1))
   apply (frule(1) tcb_cte_cases_aligned_helpers(2))
   apply (clarsimp simp del: diff_neg_mask)
   apply (subst map_upd_triv[symmetric, where t="kheap s"], assumption)
   apply (erule(2) pspace_relation_update_tcbs)
   apply (case_tac tcba)
   subgoal by (simp add: tcb_cte_cases_def tcb_relation_def del: diff_neg_mask
                    split: if_split_asm)
  apply (clarsimp simp: cte_wp_at_cases')
  apply (erule disjE)
   apply (rule pspace_dom_relatedE, assumption+)
   apply (rule obj_relation_cutsE, assumption+, simp_all split: if_split_asm)[1]
   apply (clarsimp simp: cte_relation_def)
   apply (simp add: pspace_relation_def dom_fun_upd2
               del: dom_fun_upd)
   apply (erule conjE)
   apply (rule ballI, drule(1) bspec)
   apply (rule ballI, drule(1) bspec)
   apply clarsimp
   apply (rule obj_relation_cutsE, assumption+, simp_all split: if_split_asm)[1]
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
  apply (clarsimp simp: updateMDB_def Let_def setCTE_def setObject_def in_monad ekheap_relation_def etcb_relation_def split_def split: if_split_asm)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (drule_tac P="(=) s'" in use_valid [OF _ getCTE_sp], rule refl)
  apply (drule bspec, erule domI)
  by (clarsimp simp: tcb_cte_cases_def lookupAround2_char1 split: if_split_asm)

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

crunch updateMDB
  for aligned[wp]: "pspace_aligned'"
crunch updateMDB
  for pdistinct[wp]: "pspace_distinct'"
crunch updateMDB
  for tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
crunch updateMDB
  for tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
crunch updateMDB
  for inQ_opt_pred[wp]: "\<lambda>s. P (inQ d p |< tcbs_of' s)"
crunch updateMDB
  for inQ_opt_pred'[wp]: "\<lambda>s. P (\<lambda>d p. inQ d p |< tcbs_of' s)"
crunch updateMDB
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (wp: crunch_wps simp: crunch_simps setObject_def updateObject_cte)

lemma setCTE_rdyq_projs[wp]:
  "setCTE p f \<lbrace>\<lambda>s. P (ksReadyQueues s) (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                      (\<lambda>d p. inQ d p |< tcbs_of' s)\<rbrace>"
  apply (rule hoare_lift_Pf2[where f=ksReadyQueues])
   apply (rule hoare_lift_Pf2[where f=tcbSchedNexts_of])
    apply (rule hoare_lift_Pf2[where f=tcbSchedPrevs_of])
     apply wpsimp+
  done

crunch updateMDB
  for rdyq_projs[wp]:"\<lambda>s. P (ksReadyQueues s) (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                             (\<lambda>d p. inQ d p |< tcbs_of' s)"

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
         ksDomainTime s''     = ksDomainTime s' \<and>
         tcbSchedNexts_of s'' = tcbSchedNexts_of s' \<and>
         tcbSchedPrevs_of s'' = tcbSchedPrevs_of s' \<and>
         (\<forall>domain priority.
            (inQ domain priority |< tcbs_of' s'') = (inQ domain priority |< tcbs_of' s'))"
using assms
  apply (simp add: updateMDB_eqs updateMDB_pspace_relations split del: if_split)
  apply (frule (1) updateMDB_ctes_of)
  apply clarsimp
  apply (rule conjI)
   apply (erule use_valid)
    apply wp
   apply simp
  apply (erule use_valid, wpsimp wp: hoare_vcg_all_lift)
  apply (simp add: comp_def)
  done

lemma is_cap_revocable_eq:
  "\<lbrakk> cap_relation c c'; cap_relation src_cap src_cap'; sameRegionAs src_cap' c';
     is_untyped_cap src_cap \<longrightarrow> \<not> is_ep_cap c \<and> \<not> is_ntfn_cap c\<rbrakk>
  \<Longrightarrow> is_cap_revocable c src_cap = isCapRevocable c' src_cap'"
  by (clarsimp simp: isCap_simps objBits_simps bit_simps arch_is_cap_revocable_def
                     bits_of_def is_cap_revocable_def Retype_H.isCapRevocable_def
                     sameRegionAs_def3 isCapRevocable_def
               split: cap_relation_split_asm arch_cap.split_asm)

lemma isMDBParentOf_prev_update [simp]:
  "isMDBParentOf (cteMDBNode_update (mdbPrev_update f) cte) cte' =
   isMDBParentOf cte cte'"
  "isMDBParentOf cte (cteMDBNode_update (mdbPrev_update f) cte') =
   isMDBParentOf cte cte'"
  by (cases cte, cases cte', simp add: isMDBParentOf_def)+

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
        apply (clarsimp simp add: mdb_next_unfold modify_map_def split: if_split_asm)
       apply assumption
      apply (clarsimp simp add: parentOf_def modify_map_def split: if_split_asm)
      done
  next
    case (trans_parent c c')
    thus ?case
      apply -
      apply (rule subtree.trans_parent)
         apply (rule trans_parent.hyps)
        apply (clarsimp simp add: mdb_next_unfold modify_map_def split: if_split_asm)
       apply assumption
      apply (clarsimp simp add: parentOf_def modify_map_def split: if_split_asm)
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
  "isArchCap P (capability.NotificationCap xca xba xaa xd) = False"
  "isArchCap P (capability.EndpointCap xda xcb xbb xab xe xi) = False"
  "isArchCap P (capability.IRQHandlerCap xf) = False"
  "isArchCap P (capability.Zombie xbc xac xg) = False"
  "isArchCap P (capability.ArchObjectCap xh) = P xh"
  "isArchCap P (capability.ReplyCap xad xi xia) = False"
  "isArchCap P (capability.UntypedCap d xae xj f) = False"
  "isArchCap P (capability.CNodeCap xfa xea xdb xcc) = False"
  "isArchCap P capability.IRQControlCap = False"
  by (simp add: isArchCap_def)+

definition
  vsCapRef :: "capability \<Rightarrow> vs_ref list option"
where
  "vsCapRef cap \<equiv> case cap of
   ArchObjectCap (ASIDPoolCap _ asid) \<Rightarrow>
     Some [VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PML4Cap _ (Some asid)) \<Rightarrow>
     Some [VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PDPointerTableCap _ (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageDirectoryCap _ (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageTableCap _ (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 21) && mask 9) (Some APageDirectory),
           VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageCap _ _ _ X64SmallPage _ (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 12) && mask 9) (Some APageTable),
           VSRef ((vptr >> 21) && mask 9) (Some APageDirectory),
           VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageCap _ _ _ X64LargePage _ (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 21) && mask 9) (Some APageDirectory),
           VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | ArchObjectCap (PageCap _ _ _ X64HugePage _ (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
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
  \<not> isIOPortControlCap' cap' \<and>
  badge_derived' cap' cap \<and>
  (isUntypedCap cap \<longrightarrow> descendants_of' p m = {}) \<and>
  (isReplyCap cap = isReplyCap cap') \<and>
  (isReplyCap cap \<longrightarrow> capReplyMaster cap) \<and>
  (isReplyCap cap' \<longrightarrow> \<not> capReplyMaster cap') \<and>
  (vsCapRef cap = vsCapRef cap' \<or> isArchCap isPageCap cap') \<and>
  ((isArchCap isPageTableCap cap \<or> isArchCap isPageDirectoryCap cap \<or> isArchCap isPDPointerTableCap cap
     \<or> isArchCap isPML4Cap cap)
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
   by (auto simp add: cap_badge_def capBadge_ordering_def split: cap.splits)

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

lemma isArchCapE[elim!]:
  "\<lbrakk> isArchCap P cap; \<And>arch_cap. cap = ArchObjectCap arch_cap \<Longrightarrow> P arch_cap \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (cases cap, simp_all)

lemma is_derived_eq:
  "\<lbrakk> cap_relation c c'; cap_relation d d';
     cdt_relation (swp cte_at s) (cdt s) (ctes_of s'); cte_at p s \<rbrakk> \<Longrightarrow>
  is_derived (cdt s) p c d = is_derived' (ctes_of s') (cte_map p) c' d'"
  unfolding cdt_relation_def
  apply (erule allE, erule impE, simp)
  apply (clarsimp simp: is_derived_def is_derived'_def badge_derived'_def)
  apply (rule conjI)
   apply (clarsimp simp: is_cap_simps isCap_simps)
  subgoal by (cases c, auto simp: isCap_simps cap_master_cap_def capMasterCap_def vsCapRef_def
                                   vs_cap_ref_def)[1]
  apply (case_tac "isIRQControlCap d'")
   apply (frule(1) master_cap_relation)
  subgoal by (clarsimp simp: isCap_simps cap_master_cap_def
                        is_zombie_def is_reply_cap_def is_master_reply_cap_def
                 split: cap_relation_split_asm arch_cap.split_asm)[1]
  apply (case_tac "isIOPortControlCap' d'")
   apply (frule(1) master_cap_relation)
  subgoal by (clarsimp simp: isCap_simps cap_master_cap_def is_cap_simps is_zombie_def
                       split: cap_relation_split_asm arch_cap.split_asm)
  apply (frule(1) master_cap_relation)
  apply (frule(1) cap_badge_relation)
  apply (frule cap_asid_cap_relation)
  apply (frule(1) capBadge_ordering_relation)
  by (case_tac d; simp add: isCap_simps is_cap_simps cap_master_cap_def
                            vs_cap_ref_def vsCapRef_def capMasterCap_def
                     split: cap_relation_split_asm arch_cap.split_asm)
     (auto split:arch_cap.splits arch_capability.splits option.splits) (* slow *)
end

locale masterCap =
  fixes cap cap'
  assumes master: "capMasterCap cap = capMasterCap cap'"
begin
interpretation Arch . (*FIXME: arch-split*)

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

lemma isArchIOPortCap [simp]:
  "isArchIOPortCap cap' = isArchIOPortCap cap" using master
  by (simp add: capMasterCap_def isArchIOPortCap_def
           split: capability.splits arch_capability.splits)

lemma isIOPortControlCap' [simp]:
  "isIOPortControlCap' cap' = isIOPortControlCap' cap" using master
  by (simp add: capMasterCap_def isCap_simps
           split: capability.splits arch_capability.splits)

lemma isIRQHandlerCap [simp]:
  "isIRQHandlerCap cap' = isIRQHandlerCap cap" using master
  by (simp add: capMasterCap_def isIRQHandlerCap_def split: capability.splits)

lemma isEndpointCap [simp]:
  "isEndpointCap cap' = isEndpointCap cap" using master
  by (simp add: capMasterCap_def isEndpointCap_def split: capability.splits)

lemma isNotificationCap [simp]:
  "isNotificationCap cap' = isNotificationCap cap" using master
  by (simp add: capMasterCap_def isNotificationCap_def split: capability.splits)

lemma isIRQControlCap [simp]:
  "isIRQControlCap cap' = isIRQControlCap cap" using master
  by (simp add: capMasterCap_def isIRQControlCap_def split: capability.splits)

lemma isReplyCap [simp]:
  "isReplyCap cap' = isReplyCap cap" using master
  by (simp add: capMasterCap_def isReplyCap_def split: capability.splits)

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
  assumes "\<not>isNotificationCap cap"
  shows "isMDBParentOf c (CTE cap' m) = isMDBParentOf c (CTE cap m)"
proof -
  from assms
  have c':
    "\<not>isReplyCap cap'" "\<not>isEndpointCap cap'"
    "\<not>isNotificationCap cap'" by auto
  note isReplyCap [simp del] isEndpointCap [simp del] isNotificationCap [simp del]
  from c' assms
  show ?thesis
  apply (cases c, clarsimp)
  apply (simp add: isMDBParentOf_CTE)
  apply (rule iffI)
   apply clarsimp
   apply (clarsimp simp: capBadge_ordering_def capBadge_def isCap_simps sameRegionAs_def3
                   split: if_split_asm)
  apply clarsimp
  apply (clarsimp simp: capBadge_ordering_def capBadge_def isCap_simps sameRegionAs_def3
                  split: if_split_asm)
  done
qed

lemma isMDBParentOf2:
  assumes "\<not>isReplyCap cap"
  assumes "\<not>isEndpointCap cap"
  assumes "\<not>isNotificationCap cap"
  shows "isMDBParentOf (CTE cap' m) c = isMDBParentOf (CTE cap m) c"
proof -
  from assms
  have c':
    "\<not>isReplyCap cap'" "\<not>isEndpointCap cap'"
    "\<not>isNotificationCap cap'" by auto
  note isReplyCap [simp del] isEndpointCap [simp del] isNotificationCap [simp del]
  from c' assms
  show ?thesis
  apply (cases c, clarsimp)
  apply (simp add: isMDBParentOf_CTE)
  apply (auto simp: capBadge_ordering_def capBadge_def isCap_simps sameRegionAs_def3
                  split: if_split_asm)[1]
  done
qed

lemmas isMDBParentOf = isMDBParentOf1 isMDBParentOf2

end


lemma same_master_descendants:
  assumes slot: "m slot = Some cte"
  assumes master: "capMasterCap (cteCap cte) = capMasterCap cap'"
  assumes c': "\<not>isReplyCap cap'" "\<not>isEndpointCap cap'" "\<not>isNotificationCap cap'"
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
          "\<not>isNotificationCap cap" by auto

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

lemma is_ntfn_cap_relation:
  "cap_relation c c' \<Longrightarrow> isNotificationCap c' = is_ntfn_cap c"
  apply (simp add: isCap_simps is_cap_simps)
  apply (cases c, auto)
  done

(* Just for convenience like free_index_update *)
definition freeIndex_update where
  "freeIndex_update c' g \<equiv> case c' of capability.UntypedCap d ref sz f \<Rightarrow> capability.UntypedCap d ref sz (g f) | _ \<Rightarrow> c'"

lemma freeIndex_update_not_untyped[simp]: "\<not>isUntypedCap c \<Longrightarrow> freeIndex_update c g = c"
   by (case_tac c,simp_all add:freeIndex_update_def isCap_simps)

locale mdb_insert =
  mdb_ptr_src?: mdb_ptr m _ _ src src_cap src_node +
  mdb_ptr_dest?: mdb_ptr m _ _ dest dest_cap dest_node
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
                 (\<lambda>m. mdbFirstBadged_update (\<lambda>a. isCapRevocable c' src_cap)
                     (mdbRevocable_update (\<lambda>a. isCapRevocable c' src_cap)
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
  "new_dest \<equiv> CTE c' (mdbFirstBadged_update (\<lambda>a. isCapRevocable c' src_cap)
                     (mdbRevocable_update (\<lambda>a. isCapRevocable c' src_cap)
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
  "\<lbrakk> isCapRevocable new old; (capBadge old, capBadge new) \<in> capBadge_ordering P;
       capMasterCap old = capMasterCap new \<rbrakk>
      \<Longrightarrow> (isUntypedCap new \<or> (\<exists>x. capBadge old = Some 0 \<and> capBadge new = Some x \<and> x \<noteq> 0))"
  by (clarsimp simp: Retype_H.isCapRevocable_def X64_H.isCapRevocable_def isCap_simps
                        X64_H.arch_capability.simps
              split: if_split_asm capability.split_asm X64_H.arch_capability.split_asm)

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
  "RetypeDecls_H.sameRegionAs (capability.UntypedCap d a b c) =
   RetypeDecls_H.sameRegionAs (capability.UntypedCap d a b c')"
  apply (rule ext)
  apply (case_tac x)
    apply (clarsimp simp:sameRegionAs_def isCap_simps)+
  done

lemma sameRegionAs_update_untyped':
  "RetypeDecls_H.sameRegionAs cap (capability.UntypedCap d a b f) =
   RetypeDecls_H.sameRegionAs cap (capability.UntypedCap d a b f')"
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
                        badge_derived'_def freeIndex_update_def capMasterCap_def
                 split: capability.splits)
   apply (simp add: ut_revocable'_def)
   apply (drule spec[where x=src], simp add: isCap_simps)
   apply (simp add: descendants_of'_def)
   apply (drule spec[where x="mdbNext src_node"])
   apply (erule notE, rule direct_parent)
     apply (simp add: mdb_next_unfold)
    apply simp
   apply (simp add: parentOf_def src isMDBParentOf_CTE isCap_simps
              cong: sameRegionAs_update_untyped)
  apply (clarsimp simp: isMDBParentOf_CTE is_derived'_def badge_derived'_def)
  apply (drule(2) revokable_plus_orderD)
  apply (erule sameRegionAsE, simp_all)
     apply (simp add: valid_badges_def2)
     apply (erule_tac x=src in allE)
     apply (erule_tac x="mdbNext src_node" in allE)
     apply (clarsimp simp: src mdb_next_unfold)
     apply (case_tac "capBadge cap'", simp_all)
    apply (clarsimp simp add: isCap_simps capMasterCap_def vsCapRef_def
                    simp del: not_ex
                       split: capability.splits)
   apply (clarsimp simp: isCap_simps)+
  done

locale mdb_insert_child = mdb_insert_der +
  assumes child:
  "isMDBParentOf
   (CTE src_cap src_node)
   (CTE c' (mdbFirstBadged_update (\<lambda>a. isCapRevocable c' src_cap)
           (mdbRevocable_update (\<lambda>a. isCapRevocable c' src_cap)
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
        apply (simp add: n_direct_eq split: if_split_asm)
       apply simp
      apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
      done
  next
    case (trans_parent c d)
    thus ?case
      apply clarsimp
      apply (rule conjI, clarsimp)
      apply (clarsimp split: if_split_asm)
      apply (simp add: n_direct_eq)
      apply (cases "p=src")
       apply simp
       apply (rule subtree.direct_parent, assumption, assumption)
       apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
      apply clarsimp
      apply (erule subtree.trans_parent, assumption, assumption)
      apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
     apply (erule subtree.trans_parent)
       apply (simp add: n_direct_eq split: if_split_asm)
      apply assumption
     apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
     done
 qed
qed

lemma descendants:
  "descendants_of' p n =
   (if src \<in> descendants_of' p m \<or> p = src
   then descendants_of' p m \<union> {dest} else descendants_of' p m)"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def)
  apply (fastforce dest!: parent_n_m dest: parent_m_n simp: n_dest_child split: if_split_asm)
  done

end

locale mdb_insert_sib = mdb_insert_der +
  assumes no_child:
  "\<not>isMDBParentOf
   (CTE src_cap src_node)
   (CTE c' (mdbFirstBadged_update (\<lambda>a. isCapRevocable c' src_cap)
           (mdbRevocable_update (\<lambda>a. isCapRevocable c' src_cap)
           (mdbPrev_update (\<lambda>a. src) src_node))))"
begin
interpretation Arch . (*FIXME: arch-split*)

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
     subgoal by (cases src_cap; auto simp: capMasterCap_def Retype_H.isCapRevocable_def X64_H.isCapRevocable_def
                                     vsCapRef_def freeIndex_update_def isCap_simps
                                       split: capability.split_asm arch_capability.split_asm) (* long *)
    apply (clarsimp simp: isCap_simps sameRegionAs_def3 capMasterCap_def freeIndex_update_def
       split:capability.splits arch_capability.splits)
   apply (clarsimp simp: isCap_simps sameRegionAs_def3 freeIndex_update_def
                         capRange_def vsCapRef_def split:capability.splits
               simp del: Int_atLeastAtMost atLeastAtMost_iff)
   apply auto[1]
  apply (clarsimp simp: isCap_simps sameRegionAs_def3)+
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
  apply (cases "isCapRevocable c' src_cap")
   apply simp
   apply (drule(2) revokable_plus_orderD)
   apply (erule disjE)
     apply (clarsimp simp: isCap_simps)
     by ((fastforce elim: capBadge_ordering_trans simp: isCap_simps)+)

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
   apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
  apply simp
  apply (rule conjI)
   apply (clarsimp simp: n_direct_eq split: if_split_asm)
  apply (clarsimp simp: n_direct_eq split: if_split_asm)
   apply (erule trans_parent, assumption, assumption)
   apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
  apply (erule trans_parent, assumption, assumption)
  apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
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
  apply (simp split: if_split_asm)
   apply (drule parent_m, simp)
  apply (drule parent_m, clarsimp)
  done

lemma descendants:
  "descendants_of' p n =
   descendants_of' p m \<union> (if src \<in> descendants_of' p m then {dest} else {})"
  by (rule set_eqI) (simp add: descendants_of'_def parent_n_eq)

end
context begin interpretation Arch . (*FIXME: arch-split*)
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

declare if_split [split del]

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
                   split: capability.splits arch_capability.splits option.splits)
   apply (clarsimp simp: isCap_simps valid_cap'_def capAligned_def
                         is_aligned_no_overflow capRange_def
                  split: capability.splits arch_capability.splits option.splits)
  apply (clarsimp simp: isCap_simps valid_cap'_def valid_arch_cap'_def
                        is_aligned_no_overflow capRange_def
                 split: capability.splits arch_capability.splits option.splits)
  done

lemma no_fail_updateMDB [wp]:
  "no_fail (\<lambda>s. p \<noteq> 0 \<longrightarrow> cte_at' p s) (updateMDB p f)"
  apply (simp add: updateMDB_def)
  apply (rule no_fail_pre, wp)
  apply (simp split: if_split)
  done

lemma updateMDB_cte_at' [wp]:
 "\<lbrace>cte_at' p\<rbrace>
  updateMDB x y
  \<lbrace>\<lambda>uu. cte_at' p\<rbrace>"
  by (wpsimp wp: updateMDB_weak_cte_wp_at)

lemma updateCap_cte_at' [wp]:
 "\<lbrace>cte_at' p\<rbrace> updateCap c p' \<lbrace>\<lambda>_. cte_at' p\<rbrace>"
  unfolding updateCap_def by wp

lemma nullMDBNode_pointers[simp]:
  "mdbPrev nullMDBNode = nullPointer"
  "mdbNext nullMDBNode = nullPointer"
  by (simp add: nullMDBNode_def)+

lemma maxFreeIndex_eq[simp]: "maxFreeIndex nat1 = max_free_index nat1"
  by (clarsimp simp:maxFreeIndex_def max_free_index_def shiftL_nat)

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
   isCapRevocable c' (maskedAsFull src_cap' a) = isCapRevocable c' src_cap'"
  apply (case_tac src_cap')
    apply (simp_all add:maskedAsFull_def isCap_simps)
  apply (case_tac c')
    apply (simp_all add:maskedAsFull_def is_derived'_def isCap_simps vsCapRef_def)
    apply (simp_all add:badge_derived'_def capMasterCap_simps split:arch_capability.splits)
  apply (clarsimp split:if_splits simp:Retype_H.isCapRevocable_def X64_H.isCapRevocable_def isCap_simps)
  done

lemma parentOf_preserve_oneway:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte')
  \<and> (isNotificationCap (cteCap cte) \<longrightarrow> (capNtfnBadge (cteCap cte) = capNtfnBadge (cteCap cte')))
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
    apply ((simp only: isMDBParentOf_def split_def split: cte.splits if_split_asm); clarsimp)
    by (clarsimp simp: sameRegionAs_def isCap_simps Let_def split: if_split_asm)+ (* long *)

lemma parentOf_preserve:
  assumes dom:"\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
    sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte')
  \<and> (isNotificationCap (cteCap cte) \<longrightarrow> (capNtfnBadge (cteCap cte) = capNtfnBadge (cteCap cte')))
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

crunch setCTE
  for tcbQueued[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"

lemma setCTE_UntypedCap_corres:
  "\<lbrakk>cap_relation cap (cteCap cte); is_untyped_cap cap; idx' = idx\<rbrakk>
   \<Longrightarrow> corres dc (cte_wp_at ((=) cap) src and valid_objs and
                  pspace_aligned and pspace_distinct)
                 (cte_wp_at' ((=) cte) (cte_map src) and
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
  apply (frule_tac c = "cap.UntypedCap dev r bits idx"
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
  apply clarsimp
  apply (rule conjI)
   apply (frule setCTE_pspace_only)
   apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                    split: if_split_asm Structures_A.kernel_object.splits)
  apply (extract_conjunct \<open>match conclusion in "ready_queues_relation _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp: ready_queues_relation_def Let_def)
   apply (rule use_valid[OF _ setCTE_tcbSchedPrevs_of], assumption)
   apply (rule use_valid[OF _ setCTE_tcbSchedNexts_of], assumption)
   apply (rule use_valid[OF _ setCTE_ksReadyQueues], assumption)
   apply (rule use_valid[OF _ setCTE_inQ_opt_pred], assumption)
   apply (rule use_valid[OF _ set_cap_exst], assumption)
   apply clarsimp
  apply (rule conjI)
   apply (frule setCTE_pspace_only)
   apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    apply (frule mdb_set_cap, frule exst_set_cap)
    apply (erule use_valid [OF _ setCTE_ctes_of_wp])
    apply (clarsimp simp: cdt_list_relation_def cte_wp_at_ctes_of split: if_split_asm)
   apply (rule conjI)
    prefer 2
    apply (frule setCTE_pspace_only)
    apply clarsimp
    apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                    split: if_split_asm Structures_A.kernel_object.splits)
   apply (frule set_cap_caps_of_state_monad)
   apply (drule is_original_cap_set_cap)
   apply clarsimp
   apply (erule use_valid [OF _ setCTE_ctes_of_wp])
   apply (clarsimp simp: revokable_relation_def simp del: fun_upd_apply)
   apply (clarsimp split: if_split_asm)
    apply (frule cte_map_inj_eq)
         prefer 2
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply (simp add: null_filter_def split: if_split_asm)
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply (erule caps_of_state_cte_at)
       apply fastforce
      apply fastforce
     apply fastforce
    apply clarsimp
    apply (simp add: null_filter_def split: if_split_asm)
    apply (erule_tac x=aa in allE, erule_tac x=bb in allE)
    apply (case_tac cte)
    apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps isCap_simps cte_wp_at_ctes_of)
   apply (simp add: null_filter_def cte_wp_at_caps_of_state split: if_split_asm)
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

lemma setUntypedCapAsFull_corres:
  "\<lbrakk>cap_relation c c'; src' = cte_map src;
    cap_relation src_cap (cteCap srcCTE); rv = cap.NullCap;
    cteCap rv' = capability.NullCap; mdbPrev (cteMDBNode rv') = nullPointer \<and>
    mdbNext (cteMDBNode rv') = nullPointer\<rbrakk>
   \<Longrightarrow> corres dc (cte_wp_at ((=) src_cap) src and valid_objs and
                  pspace_aligned and pspace_distinct)
                 (cte_wp_at' ((=) srcCTE) (cte_map src) and
                  pspace_aligned' and pspace_distinct')
                 (set_untyped_cap_as_full src_cap c src)
                 (setUntypedCapAsFull (cteCap srcCTE) c' (cte_map src))"
  apply (clarsimp simp:set_untyped_cap_as_full_def setUntypedCapAsFull_def
    split:if_splits)
  apply (intro conjI impI)
    apply (clarsimp simp del:capFreeIndex_update.simps simp:updateCap_def)
      apply (rule corres_guard_imp)
        apply (rule corres_symb_exec_r)
           apply (rule_tac F="cte = srcCTE" in corres_gen_asm2)
           apply (simp)
           apply (rule setCTE_UntypedCap_corres)
             apply simp+
           apply (clarsimp simp:free_index_update_def isCap_simps is_cap_simps)
           apply (subst identity_eq)
        apply (wp getCTE_sp getCTE_get)+
       apply (clarsimp simp:cte_wp_at_ctes_of)+
   apply (clarsimp simp:is_cap_simps isCap_simps)+
  apply (case_tac c,simp_all)
  apply (case_tac src_cap,simp_all)
  done

(* FIXME: SELFOUR-421 move *)
lemma isUntypedCap_simps[simp]:
  "isUntypedCap (capability.UntypedCap uu uv uw ux) = True"
  "isUntypedCap (capability.NullCap) = False"
  "isUntypedCap (capability.EndpointCap v va vb vc vd ve) = False"
  "isUntypedCap (capability.NotificationCap v va vb vc) = False"
  "isUntypedCap (capability.ReplyCap v1 v2 v3) = False"
  "isUntypedCap (capability.CNodeCap x1 x2 x3 x4) = False"
  "isUntypedCap (capability.ThreadCap v) = False"
  "isUntypedCap (capability.DomainCap) = False"
  "isUntypedCap (capability.IRQControlCap) = False"
  "isUntypedCap (capability.IRQHandlerCap y1) = False"
  "isUntypedCap (capability.Zombie v va1 vb1) = False"
  "isUntypedCap (capability.ArchObjectCap z) = False"
  by (simp_all add: isUntypedCap_def split: capability.splits)

lemma cap_relation_masked_as_full:
  "\<lbrakk>cap_relation src_cap src_cap';cap_relation c c'\<rbrakk> \<Longrightarrow>
    cap_relation (masked_as_full src_cap c) (maskedAsFull src_cap' c')"
  apply (clarsimp simp: masked_as_full_def maskedAsFull_def
                 split: if_splits)
  apply (case_tac src_cap; clarsimp)
  by (case_tac c; clarsimp)

lemma setUntypedCapAsFull_pspace_distinct[wp]:
  "\<lbrace>pspace_distinct' and cte_wp_at' ((=) srcCTE) slot\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) c slot \<lbrace>\<lambda>r. pspace_distinct'\<rbrace>"
  apply (clarsimp simp: setUntypedCapAsFull_def split:if_splits)
  apply (intro conjI impI)
    apply (clarsimp simp:valid_def)
    apply (drule updateCap_stuff)
    apply simp
  apply (wp|clarsimp)+
done

lemma setUntypedCapAsFull_pspace_aligned[wp]:
  "\<lbrace>pspace_aligned' and cte_wp_at' ((=) srcCTE) slot\<rbrace>
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
        cte_wp_at' ((=) srcCTE) src s\<rbrace>
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
  "\<lbrace>\<lambda>s. no_0 ((ctes_of s)(a:=b)) \<and> cte_wp_at' ((=) srcCTE) src s\<rbrace>
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
    isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte')
  \<and> (isNotificationCap (cteCap cte) \<longrightarrow> (capNtfnBadge (cteCap cte) = capNtfnBadge (cteCap cte')))
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
    isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte')
  \<and> (isNotificationCap (cteCap cte) \<longrightarrow> (capNtfnBadge (cteCap cte) = capNtfnBadge (cteCap cte')))
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
  \<and> isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte')
  \<and> (isNotificationCap (cteCap cte) \<longrightarrow> (capNtfnBadge (cteCap cte) = capNtfnBadge (cteCap cte')))
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
  apply (erule_tac f1 = "\<lambda>x. lfp x y" for y in iffD1[OF arg_cong,rotated])
    apply (rule ext)+
      apply (subgoal_tac "\<And>p p'. (m \<turnstile> p \<leadsto> p') = (m' \<turnstile> p \<leadsto> p')")
        apply (thin_tac "P" for P)+
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
  \<and> isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte')
  \<and> (isNotificationCap (cteCap cte) \<longrightarrow> (capNtfnBadge (cteCap cte) = capNtfnBadge (cteCap cte')))
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

end
locale mdb_inv_preserve =
  fixes m m'
  assumes dom: "\<And>x. (x\<in> dom m)  = (x\<in> dom m')"
  assumes misc:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
  isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte')
  \<and> isNullCap (cteCap cte) = isNullCap (cteCap cte')
  \<and> isReplyCap (cteCap cte) = isReplyCap (cteCap cte')
  \<and> (isReplyCap (cteCap cte) \<longrightarrow> capReplyMaster (cteCap cte) = capReplyMaster (cteCap cte'))
  \<and> isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte')
  \<and> (isNotificationCap (cteCap cte) \<longrightarrow> (capNtfnBadge (cteCap cte) = capNtfnBadge (cteCap cte')))
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
  \<and> X64_H.isIOPortControlCap' (cteCap cte) = X64_H.isIOPortControlCap' (cteCap cte')
  \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes sameRegion:"\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
     sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
  \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes mdb_next:"\<And>p. mdb_next m p = mdb_next m' p"
begin
interpretation Arch . (*FIXME: arch-split*)
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
  apply (rename_tac cte cte')
  apply (case_tac cte)
  apply (rename_tac cap node)
  apply (case_tac cte')
  apply (drule_tac x = cap in spec)
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
  apply (thin_tac "P" for P)+
    apply (clarsimp simp: descendants_of'_def Invariants_H.subtree_def)
    apply (rule_tac f = "\<lambda>x. lfp x c" for c in arg_cong)
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
   apply (rule_tac f = "\<lambda>x. lfp x c" for c in arg_cong)
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
  apply (clarsimp simp:option_map_def o_def split:option.splits if_splits)
  apply (drule_tac x = p in spec)+
  apply (intro allI conjI impI)
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

lemma updateCap_cte_wp_at':
  "\<lbrace>\<lambda>s. cte_at' ptr s \<longrightarrow> Q (cte_wp_at' (\<lambda>cte. if p = ptr then P' (CTE cap (cteMDBNode cte)) else P' cte) p s)\<rbrace>
        updateCap ptr cap \<lbrace>\<lambda>rv s. Q (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add:updateCap_def cte_wp_at_ctes_of)
  apply (wp setCTE_ctes_of_wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac cte, auto split: if_split)
  done

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
  "\<lbrace>valid_cap' cap and cte_wp_at' ((=) srcCTE) slot\<rbrace>
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
  "\<lbrace>cte_wp_at' ((=) srcCTE) slot and
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

lemma mdb_inv_preserve_sym:"mdb_inv_preserve a b \<Longrightarrow> mdb_inv_preserve b a"
 by (simp add:mdb_inv_preserve_def)


lemma mdb_inv_preserve_refl[simp]:
  "mdb_inv_preserve m m"
   by (simp add:mdb_inv_preserve_def)

context begin interpretation Arch . (* FIXME arch-split *)

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

end

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

crunch set_untyped_cap_as_full
  for valid_list[wp]: valid_list

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
         ksDomainTime s''     = ksDomainTime s' \<and>
         tcbSchedNexts_of s'' = tcbSchedNexts_of s' \<and>
         tcbSchedPrevs_of s'' = tcbSchedPrevs_of s' \<and>
         (\<forall>domain priority.
            (inQ domain priority |< tcbs_of' s'') = (inQ domain priority |< tcbs_of' s'))"
  apply (rule updateMDB_the_lot)
      using assms
      apply (fastforce simp: pspace_relations_def)+
   done

lemma cte_map_inj_eq':
  "\<lbrakk>(cte_map p = cte_map p');
   cte_at p s \<and> cte_at p' s \<and>
   valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s\<rbrakk>
  \<Longrightarrow> p = p'"
  apply (rule cte_map_inj_eq; fastforce)
  done

context begin interpretation Arch . (*FIXME: arch-split*)

lemma arch_mdb_assertD:
  "\<lbrakk> m p = Some (CTE (ArchObjectCap IOPortControlCap) n); m p' = Some (CTE (ArchObjectCap IOPortControlCap) n');
    arch_mdb_assert m \<rbrakk> \<Longrightarrow> p' = p"
  unfolding arch_mdb_assert_def by blast

lemma ioport_revocable:
  "\<lbrakk> m p = Some (CTE (ArchObjectCap IOPortControlCap) n); arch_mdb_assert m \<rbrakk> \<Longrightarrow> mdbRevocable n"
  unfolding arch_mdb_assert_def by blast

lemma arch_mdb_assert_cross:
  "\<lbrakk> valid_arch_mdb (is_original_cap s) (caps_of_state s); ioport_control_unique s; valid_objs s;
     (s,s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> arch_mdb_assert (ctes_of s')"
  unfolding arch_mdb_assert_def valid_arch_mdb_def
  apply clarsimp
  apply (frule (2) caps_of_state_rev_cross)
  apply clarsimp
  apply (rule conjI)
   (* revocable *)
   apply (simp add: ioport_revocable_def)
   apply (erule allE, erule allE, erule (1) impE)
   apply (erule state_relationE)
   apply (clarsimp simp: revokable_relation_def)
   apply (force simp: null_filter_def)
  (* ioport_control_unique *)
  apply (thin_tac "ctes_of s' _ = _")
  apply (clarsimp simp: ioport_control_unique_def)
  apply (drule (2) caps_of_state_rev_cross)
  apply fastforce
  done

(* interface lemma: generic statement, arch-specific proof *)
lemma archMDBAssertions_cross:
  "\<lbrakk> valid_arch_mdb (is_original_cap s) (caps_of_state s); valid_arch_state s; valid_objs s;
     (s, s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> archMDBAssertions s'"
  unfolding archMDBAssertions_def
  by (drule arch_mdb_assert_cross; simp add: valid_arch_state_def)

lemma cteInsert_corres:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
        trans_state_update'[symmetric,simp]
  assumes "cap_relation c c'" "src' = cte_map src" "dest' = cte_map dest"
  shows "corres dc
        (valid_objs and pspace_distinct and pspace_aligned and
         valid_mdb and valid_list and K (src\<noteq>dest) and
         cte_wp_at (\<lambda>c. c=Structures_A.NullCap) dest and
         (\<lambda>s. cte_wp_at (is_derived (cdt s) src c) src s) and valid_arch_state)
        (pspace_distinct' and pspace_aligned' and valid_mdb' and valid_cap' c' and
         cte_wp_at' (\<lambda>c. cteCap c=NullCap) dest')
        (cap_insert c src dest)
        (cteInsert c' src' dest')"
  (is "corres _ (?P and (\<lambda>s. cte_wp_at _ _ s) and valid_arch_state) (?P' and cte_wp_at' _ _) _ _")
  using assms
  unfolding cap_insert_def cteInsert_def
  apply simp
  (* this lemma doesn't use the assertion, but does need to establish it *)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (rule archMDBAssertions_cross; simp add: valid_mdb_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres])
      apply (rule corres_split[OF get_cap_corres])
        apply (rule_tac F="cteCap oldCTE = NullCap" in corres_gen_asm2)
        apply simp
        apply (rule_tac P="?P and cte_at dest and
                            (\<lambda>s. cte_wp_at (is_derived (cdt s) src c) src s) and
                            cte_wp_at ((=) src_cap) src" and
                        Q="?P' and
                           cte_wp_at' ((=) oldCTE) (cte_map dest) and
                           cte_wp_at' ((=) srcCTE) (cte_map src)"
                        in corres_assert_assume)
         prefer 2
         apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def valid_nullcaps_def)
         apply (case_tac oldCTE)
         apply (simp add: initMDBNode_def)
         apply (erule allE)+
         apply (erule (1) impE)
         apply (simp add: nullPointer_def)
        apply (rule corres_guard_imp)
          apply (rule_tac R="\<lambda>r. ?P and cte_at dest and
                            (\<lambda>s. (is_derived (cdt s) src c) src_cap) and
                            cte_wp_at ((=) (masked_as_full src_cap c)) src" and
                        R'="\<lambda>r. ?P' and cte_wp_at' ((=) oldCTE) (cte_map dest) and
                           cte_wp_at' ((=) (CTE (maskedAsFull (cteCap srcCTE) c') (cteMDBNode srcCTE)))
                           (cte_map src)"
                        in corres_split[where r'=dc])
             apply (rule setUntypedCapAsFull_corres; simp)
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
                               | (rule bind_execI[where f="cap_insert_ext x y z i p" for x y z i p], clarsimp simp: exec_gets exec_get put_def mdb_insert_abs.cap_insert_ext_det_def2 update_cdt_list_def set_cdt_list_def, rule refl))+
            apply (clarsimp simp: put_def state_relation_def)
            apply (drule updateCap_stuff)
            apply clarsimp
            apply (drule (3) updateMDB_the_lot', simp only: no_0_modify_map, simp only:, elim conjE)
            apply (drule (3) updateMDB_the_lot', simp only: no_0_modify_map, simp only:, elim conjE)
            apply (drule (3) updateMDB_the_lot', simp only: no_0_modify_map, simp only:,  elim conjE)
            apply (clarsimp simp: cte_wp_at_ctes_of nullPointer_def prev_update_modify_mdb_relation)
            apply (subgoal_tac "cte_map dest \<noteq> 0")
             prefer 2
             subgoal by (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def no_0_def)
            apply (subgoal_tac "cte_map src \<noteq> 0")
             prefer 2
             subgoal by (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def no_0_def)
            apply (thin_tac "ksMachineState t = p" for p t)+
            apply (thin_tac "ksCurThread t = p" for p t)+
            apply (thin_tac "ksIdleThread t = p" for p t)+
            apply (thin_tac "ksSchedulerAction t = p" for p t)+
            apply (clarsimp simp: pspace_relations_def)
            apply (rule conjI)
             subgoal by (simp only: simp_thms ghost_relation_typ_at set_cap_a_type_inv data_at_def)
            apply (thin_tac "ready_queues t = p" for t p)+
            apply (thin_tac "cur_domain t = p" for t p)+
            apply (thin_tac "ksDomScheduleIdx t = p" for t p)+
            apply (thin_tac "ksDomSchedule t = p" for t p)+
            apply (thin_tac "ksCurDomain t = p" for t p)+
            apply (thin_tac "ksDomainTime t = p" for t p)+
            apply (thin_tac "idle_thread t = p" for t p)+
            apply (thin_tac "work_units_completed t = p" for t p)+
            apply (thin_tac "domain_index t = p" for t p)+
            apply (thin_tac "domain_list t = p" for t p)+
            apply (thin_tac "domain_time t = p" for t p)+
            apply (thin_tac "ekheap t = p" for t p)+
            apply (thin_tac "scheduler_action t = p" for t p)+
            apply (thin_tac "ksArchState t = p" for t p)+
            apply (thin_tac "gsCNodes t = p" for t p)+
            apply (thin_tac "ksWorkUnitsCompleted t = p" for t p)+
            apply (thin_tac "ksInterruptState t = p" for t p)+
            apply (thin_tac "gsUserPages t = p" for t p)+
            apply (thin_tac "pspace_relation s s'" for s s')+
            apply (thin_tac "ekheap_relation e p" for e p)+
            apply (thin_tac "interrupt_state_relation n s s'" for n s s')+
            apply (thin_tac "sched_act_relation s s'" for s s')+
            apply (thin_tac "ready_queues_relation s s'" for s s')+
            apply (thin_tac "ghost_relation p s s'" for p s s')+
            apply (thin_tac "cur_thread t = p" for t p)+
            apply (thin_tac "(s,s') \<in> arch_state_relation" for s s')+
            apply (thin_tac "ctes_of s = t" for s t)+
            apply (thin_tac "machine_state t = s" for s t)+
            apply (rule conjI)
             defer
             apply(rule conjI)
              apply (case_tac "srcCTE")
              apply (rename_tac src_cap' src_node)
              apply (case_tac "oldCTE")
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
              apply (simp (no_asm_simp) add: cdt_relation_def split: if_split)
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
                 subgoal by(fastforce split: if_split_asm)
                apply(case_tac "ca = dest")
                 apply(simp)
                 apply(rule impI)
                 apply(clarsimp simp: modify_map_def const_def)
                 apply(simp split: if_split_asm)
                   apply(drule_tac p="cte_map src" in valid_mdbD1')
                     subgoal by(simp)
                    subgoal by(simp add: valid_mdb'_def valid_mdb_ctes_def)
                   subgoal by(clarsimp)
                  subgoal by(drule cte_map_inj_eq'; simp)
                 apply(erule_tac x=src in allE)+
                 subgoal by(fastforce)
                apply(simp)
                apply(rule impI)
                apply(subgoal_tac "cte_at ca a")
                 prefer 2
                 apply(rule cte_at_next_slot)
                    apply(simp_all)[4]
                apply(clarsimp simp: modify_map_def const_def)
                apply(simp split: if_split_asm)
                      apply(drule cte_map_inj_eq'; simp)
                     apply(drule_tac p="cte_map src" in valid_mdbD1')
                       subgoal by(simp)
                      subgoal by(simp add: valid_mdb'_def valid_mdb_ctes_def)
                     subgoal by(clarsimp)
                    apply(clarsimp)
                    apply(case_tac z)
                    apply(erule_tac x="(aa, bb)" in allE)+
                    subgoal by(fastforce)
                   apply(drule cte_map_inj_eq'; simp)
                  apply(drule cte_map_inj_eq'; simp)
                 apply(drule cte_map_inj_eq'; simp)
                apply(erule_tac x="(aa, bb)" in allE)+
                subgoal by(fastforce)

               apply(frule(1) next_childD)
               apply(simp add: mdb_insert_abs.next_slot)
               apply(case_tac "ca=src")
                apply(simp)
                apply(clarsimp simp: modify_map_def)
                subgoal by(fastforce split: if_split_asm)
               apply(case_tac "ca = dest")
                apply(simp)
                apply(rule impI)
                apply(clarsimp simp: modify_map_def const_def)
                apply(simp split: if_split_asm)
                  apply(drule_tac p="cte_map src" in valid_mdbD1')
                    subgoal by(simp)
                   apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                  subgoal by(clarsimp)
                 apply(drule cte_map_inj_eq'; simp)
                apply(erule_tac x=src in allE)+
                subgoal by(fastforce)
               apply(simp)
               apply(rule impI)
               apply(subgoal_tac "cte_at ca a")
                prefer 2
                subgoal by (rule cte_at_next_slot; simp)
               apply(clarsimp simp: modify_map_def const_def)
               apply(simp split: if_split_asm)
                     apply(drule cte_map_inj_eq'; simp)
                    apply(drule_tac p="cte_map src" in valid_mdbD1')
                      subgoal by(simp)
                     subgoal by(simp add: valid_mdb'_def valid_mdb_ctes_def)
                    subgoal by(clarsimp)
                   apply(clarsimp)
                   apply(case_tac z)
                   apply(erule_tac x="(aa, bb)" in allE)+
                   subgoal by(fastforce)
                  apply(drule cte_map_inj_eq'; simp)
                 apply(drule cte_map_inj_eq'; simp)
                apply(drule cte_map_inj_eq'; simp)
               apply(erule_tac x="(aa, bb)" in allE)+
               subgoal by(fastforce)

              apply(subgoal_tac "mdb_insert_sib (ctes_of b) (cte_map src) (maskedAsFull src_cap' c')
                                                src_node (cte_map dest) capability.NullCap
                                                dest_node c'")
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
               apply (subst (asm) is_cap_revocable_eq, assumption, assumption)
                 apply (rule derived_sameRegionAs)
                  apply (subst is_derived_eq[symmetric]; assumption)
                 apply assumption
                subgoal by (clarsimp simp: cte_wp_at_def is_derived_def is_cap_simps cap_master_cap_simps
                                    dest!:cap_master_cap_eqDs)
               apply (subgoal_tac "is_original_cap a src = mdbRevocable src_node")
                apply (frule(4) iffD1[OF is_derived_eq])
                apply (drule_tac src_cap' = src_cap' in
                  maskedAsFull_revokable[where a = c',symmetric])
                subgoal by(simp)
               apply (simp add: revokable_relation_def)
               apply (erule_tac x=src in allE)+
               apply simp
               apply (erule impE)
                apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state split: if_splits)
                subgoal by (clarsimp simp: masked_as_full_def is_cap_simps free_index_update_def split: if_splits)
               apply(simp)

              apply(subgoal_tac "cdt_list (a) src = []")
               prefer 2
               apply(rule ccontr)
               apply(simp add: empty_list_empty_desc)
               apply(simp add: no_children_empty_desc[symmetric])
               apply(erule exE)
               apply(drule_tac p="cte_map caa" in mdb_insert_sib.src_no_parent)
               apply(subgoal_tac "cte_map caa\<in>descendants_of' (cte_map src) (ctes_of b)")
                subgoal by(simp add: descendants_of'_def)
               apply(simp add: cdt_relation_def)
               apply(erule_tac x=src in allE)
               apply(drule child_descendant)+
               apply(drule_tac x=caa and f=cte_map in imageI)
               subgoal by(simp)

              apply(case_tac "cdt a src")
               apply(simp)
               apply(subst mdb_insert_abs_sib.next_slot_no_parent')
                    apply(simp add: mdb_insert_abs_sib_def)
                   apply(simp_all add: fun_upd_idem)[5]

               apply(case_tac "ca=src")
                subgoal by(simp add: next_slot_def no_parent_next_not_child_None)
               apply(case_tac "ca = dest")
                subgoal by(simp add: next_slot_def no_parent_next_not_child_None
                                     mdb_insert_abs.dest empty_list_empty_desc)
               apply(case_tac "next_slot ca (cdt_list (a)) (cdt a)")
                subgoal by(simp)
               apply(simp)
               apply(subgoal_tac "cte_at ca a")
                prefer 2
                subgoal by (rule cte_at_next_slot; simp)
               apply(clarsimp simp: modify_map_def const_def)
               apply(simp split: if_split_asm)
                     apply(drule cte_map_inj_eq'; simp)
                    apply(drule_tac p="cte_map src" in valid_mdbD1')
                       apply(simp)
                     subgoal by(simp add: valid_mdb'_def valid_mdb_ctes_def)
                    subgoal by(clarsimp)
                   apply(clarsimp)
                   apply(case_tac z)
                   apply(erule_tac x="(aa, bb)" in allE)+
                   subgoal by(fastforce)
                  apply(drule cte_map_inj_eq')
                   apply(simp_all)[2]
                 apply(drule cte_map_inj_eq')
                  apply(simp_all)[2]
                apply(drule cte_map_inj_eq')
                 apply(simp_all)[2]
               apply(erule_tac x="(aa, bb)" in allE)+
               subgoal by(fastforce)
              apply(simp add: fun_upd_idem)
              apply(subst mdb_insert_abs_sib.next_slot')
                    subgoal by(simp add: mdb_insert_abs_sib_def)
                   apply(simp_all)[5]
              apply(case_tac "ca=src")
               apply(simp)
               apply(clarsimp simp: modify_map_def)
               subgoal by(fastforce split: if_split_asm)
              apply(case_tac "ca = dest")
               apply(simp)
               apply(case_tac "next_slot src (cdt_list (a)) (cdt a)")
                subgoal by(simp)
               apply(simp)
               apply(clarsimp simp: modify_map_def const_def)
               apply(simp split: if_split_asm)
                 apply(drule_tac p="cte_map src" in valid_mdbD1')
                   subgoal by(simp)
                  apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
                 subgoal by(clarsimp)
                apply(drule cte_map_inj_eq')
                 apply(simp_all)[2]
               apply(erule_tac x=src in allE)+
               subgoal by(fastforce)
              apply(simp)
              apply(case_tac "next_slot ca (cdt_list (a)) (cdt a)")
               subgoal by(simp)
              apply(simp)
              apply(subgoal_tac "cte_at ca a")
               prefer 2
               subgoal by (rule cte_at_next_slot; simp)
              apply(clarsimp simp: modify_map_def const_def)
              apply(simp split: if_split_asm)
                    apply(drule cte_map_inj_eq'; simp)
                   apply(drule_tac p="cte_map src" in valid_mdbD1')
                      subgoal by(simp)
                    subgoal by(simp add: valid_mdb'_def valid_mdb_ctes_def)
                   subgoal by(clarsimp)
                  apply(clarsimp)
                  apply(case_tac z)
                  apply(erule_tac x="(aa, bb)" in allE)+
                  subgoal by(fastforce)
                 apply(drule cte_map_inj_eq'; simp)
                apply(drule cte_map_inj_eq'; simp)
               apply(drule cte_map_inj_eq'; simp)
              apply(erule_tac x="(aa, bb)" in allE)+
              subgoal by(fastforce)
             apply (clarsimp simp: modify_map_apply)
             apply (clarsimp simp: revokable_relation_def  split: if_split)
             apply (rule conjI)
             apply clarsimp
              apply (subgoal_tac "mdbRevocable node = isCapRevocable c' (cteCap srcCTE)")
               prefer 2
               apply (case_tac oldCTE)
               subgoal by (clarsimp simp add: const_def modify_map_def split: if_split_asm)
              apply simp
              apply (rule is_cap_revocable_eq, assumption, assumption)
               apply (rule derived_sameRegionAs)
                apply (drule(3) is_derived_eq[THEN iffD1,rotated -1])
                 subgoal by (simp add: cte_wp_at_def)
                apply assumption
               apply assumption
              subgoal by (clarsimp simp: cap_master_cap_simps cte_wp_at_def is_derived_def is_cap_simps
                                  split:if_splits dest!:cap_master_cap_eqDs)
             apply clarsimp
             apply (case_tac srcCTE)
             apply (case_tac oldCTE)
             apply clarsimp
             apply (subgoal_tac "\<exists>cap' node'. ctes_of b (cte_map (aa,bb)) = Some (CTE cap' node')")
              prefer 2
              apply (clarsimp simp: modify_map_def split: if_split_asm)
              apply (case_tac z)
              subgoal by clarsimp
             apply clarsimp
             apply (drule set_cap_caps_of_state_monad)+
             apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
              prefer 2
              subgoal by (clarsimp simp: cte_wp_at_caps_of_state null_filter_def split: if_splits)

             apply clarsimp
             apply (subgoal_tac "cte_at (aa,bb) a")
              prefer 2
              apply (drule null_filter_caps_of_stateD)
              apply (erule cte_wp_at_weakenE, rule TrueI)
             apply (subgoal_tac "mdbRevocable node = mdbRevocable node'")
              subgoal by clarsimp
             apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map dest")
              subgoal by (clarsimp simp: modify_map_def split: if_split_asm)
             apply (erule (5) cte_map_inj)
(* FIXME *)
            apply (wp set_untyped_cap_full_valid_objs set_untyped_cap_as_full_valid_mdb
                      set_untyped_cap_as_full_cte_wp_at setUntypedCapAsFull_valid_cap
                      setUntypedCapAsFull_cte_wp_at | clarsimp simp: cte_wp_at_caps_of_state| wps)+
         apply (case_tac oldCTE, clarsimp simp:cte_wp_at_ctes_of maskedAsFull_def)
        apply (wp getCTE_wp' get_cap_wp)+
    apply clarsimp
    subgoal by (fastforce elim: cte_wp_at_weakenE)
   apply (clarsimp simp: cte_wp_at'_def)
  apply (case_tac "srcCTE")
  apply (rename_tac src_cap' src_node)
  apply (case_tac "oldCTE")
  apply (rename_tac dest_node)
  apply (clarsimp simp: in_set_cap_cte_at_swp)
  apply (subgoal_tac "cte_at src a \<and> is_derived (cdt a) src c src_cap")
   prefer 2
   subgoal by (fastforce simp: cte_wp_at_def)
  apply (erule conjE)
  apply (subgoal_tac "mdb_insert (ctes_of b) (cte_map src) (maskedAsFull src_cap' c') src_node
                                 (cte_map dest) NullCap dest_node")
   prefer 2
   apply (rule mdb_insert.intro)
     apply (rule mdb_ptr.intro)
      subgoal by (rule vmdb.intro, simp add: valid_mdb_ctes_def)
     apply (erule mdb_ptr_axioms.intro)
    apply (rule mdb_ptr.intro)
     subgoal by (rule vmdb.intro, simp add: valid_mdb_ctes_def)
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
  apply (simp (no_asm_simp) add: cdt_relation_def split: if_split)
  apply (subgoal_tac "descendants_of dest (cdt a) = {}")
   prefer 2
   apply (drule mdb_insert.dest_no_descendants)
   subgoal by (fastforce simp add: cdt_relation_def)
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
   apply (drule_tac src_cap' = src_cap' in maskedAsFull_revokable[where a = c',symmetric])
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
    apply (subst (asm) is_cap_revocable_eq, assumption, assumption)
      apply (rule derived_sameRegionAs)
       apply (subst is_derived_eq[symmetric], assumption, assumption,
                    assumption, assumption, assumption)
      apply assumption
     subgoal by (clarsimp simp: cte_wp_at_def is_derived_def is_cap_simps cap_master_cap_simps
                          dest!:cap_master_cap_eqDs)
    apply (subgoal_tac "is_original_cap a src = mdbRevocable src_node")
     prefer 2
     apply (simp add: revokable_relation_def)
     apply (erule_tac x=src in allE)
     apply (erule impE)
      apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state cap_master_cap_simps
                      split: if_splits dest!:cap_master_cap_eqDs)
      subgoal by (clarsimp simp: masked_as_full_def is_cap_simps free_index_update_def split: if_splits)
     subgoal by simp
    subgoal by clarsimp
   apply (subst mdb_insert_abs.descendants_child, assumption)
   apply (frule_tac p=ca in in_set_cap_cte_at)
   apply (subst descendants_of_eq')
          prefer 2
          apply assumption
         apply (simp_all)[6]
   apply (simp add: cdt_relation_def split: if_split)
   apply clarsimp
   apply (drule (5) cte_map_inj)+
   apply simp
  apply clarsimp
  apply (subst mdb_insert_abs_sib.descendants, erule mdb_insert_abs_sib.intro)
  apply (frule(4) iffD1[OF is_derived_eq])
  apply (drule_tac src_cap' = src_cap' in maskedAsFull_revokable[where a = c',symmetric])
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
   apply (subst (asm) is_cap_revocable_eq, assumption, assumption)
     apply (rule derived_sameRegionAs)
      apply (subst is_derived_eq[symmetric], assumption, assumption,
                   assumption, assumption, assumption)
     apply assumption
    subgoal by (clarsimp simp: cte_wp_at_def is_derived_def is_cap_simps cap_master_cap_simps
                        dest!:cap_master_cap_eqDs)
   apply (subgoal_tac "is_original_cap a src = mdbRevocable src_node")
    subgoal by simp
   apply (simp add: revokable_relation_def)
   apply (erule_tac x=src in allE)
   apply (erule impE)
    apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state split: if_splits)
    subgoal by (clarsimp simp: masked_as_full_def is_cap_simps free_index_update_def split: if_splits)
   subgoal by simp
  apply (simp split: if_split)
  apply (frule_tac p="(aa, bb)" in in_set_cap_cte_at)
  apply (rule conjI)
   apply (clarsimp simp: descendants_of_eq')
   subgoal by (simp add: cdt_relation_def)
  apply (clarsimp simp: descendants_of_eq')
  subgoal by (simp add: cdt_relation_def)
  done


declare if_split [split]

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
   apply (clarsimp simp: modify_map_def split: if_split_asm)
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
   apply (clarsimp simp: modify_map_def split: if_split_asm)
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
   apply (clarsimp simp: modify_map_def split: if_split_asm)
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
                        g="cteCap_update f'" for f f',
                  OF mdb_cap_update]

lemma prev_leadstoD:
  "\<lbrakk> m \<turnstile> mdbPrev node \<leadsto> c; m p = Some (CTE cap node);
    valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow>
  c = p"
  by (fastforce simp add: next_unfold' valid_dlist_def Let_def no_0_def)

lemma prev_leadstoI:
  "\<lbrakk> m p = Some (CTE cap node); mdbPrev node \<noteq> 0; valid_dlist m\<rbrakk>
  \<Longrightarrow> m \<turnstile> mdbPrev node \<leadsto> p"
  by (fastforce simp add: valid_dlist_def Let_def next_unfold')

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

lemma in_getCTE:
  "(cte, s') \<in> fst (getCTE p s) \<Longrightarrow> s' = s \<and> cte_wp_at' ((=) cte) p s"
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
end
locale mdb_swap =
  mdb_ptr_src?: mdb_ptr m _ _ src src_cap src_node +
  mdb_ptr_dest?: mdb_ptr m _ _ dest dest_cap dest_node
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

lemma cteMDBNode_update_split_asm:
  "P (cteMDBNode_update f cte) = (\<not> (\<exists>cap mdb. cte = CTE cap mdb \<and> \<not> P (CTE cap (f mdb))))"
  by (cases cte, simp)

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
   apply (simp add: modify_map_def const_def split: if_split_asm)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def const_def split: if_split_asm)
  apply (clarsimp simp: n_def)
  apply (clarsimp simp add: modify_map_def map_option_case split: if_split_asm option.splits)
     apply (auto split: cteMDBNode_update_split_asm elim: revokable_n' revokable_n'[OF sym])
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
   apply (simp add: modify_map_def const_def split: if_split_asm)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def const_def split: if_split_asm)
  apply (clarsimp simp: n_def)
  apply (clarsimp simp add: modify_map_def map_option_case split: if_split_asm option.splits)
     apply (auto split: cteMDBNode_update_split_asm elim: badge_n' badge_n'[OF sym])
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
   apply (simp add: modify_map_def split: if_split_asm)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (drule sym)
   apply (insert src dest dest2 [symmetric])[1]
   apply (simp add: n_def n'_def modify_map_apply)
   apply (simp add: modify_map_def split: if_split_asm)
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
  by (auto simp add: modify_map_cases)

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
  apply (rename_tac mdbnode)
  apply (case_tac mdbnode)
  apply (simp del: dest2_cap)
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
  s_d_swp :: "machine_word \<Rightarrow> machine_word"
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
  using src dest
  apply (simp add: n_def n'_def modify_map_mdb_cap const_def)
  apply (simp add: s_d_swap_def)
  apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp)
    apply (clarsimp simp: mdb_next_unfold modify_map_cases dest2_node_def
                    split: if_split_asm)
   apply clarsimp
   apply (rule conjI, clarsimp)
    apply (clarsimp simp: mdb_next_unfold modify_map_cases)
    apply (auto simp add: dest2_node_def split: if_split_asm)[1]
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
                    split: if_split_asm)
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
    apply hypsubst_thin
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
     apply (rename_tac capability mdbnode)
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
  apply (simp add: n_def del: dest2_parts split del: if_split)
  apply (simp only: dest2_next dest2_prev split del: if_split)
  apply (simp add: dest2_node_def split del: if_split)
  apply (simp add: n'_def const_def cong: if_cong split del: if_split)
  apply(case_tac "p=dest")
   apply(clarsimp simp: modify_map_cases const_def split: if_split_asm)
  apply(case_tac "p=src")
   apply(simp split del: if_split)
   apply(clarsimp simp: modify_map_cases const_def split: if_split_asm)
  apply(case_tac "p=mdbPrev src_node")
   apply(simp split del: if_split)
   apply(clarsimp simp: modify_map_cases const_def split: if_split_asm)
    apply(fastforce)
   apply(fastforce)
  apply(case_tac "p=mdbPrev dest_node")
   apply(simp split del: if_split)
   apply(clarsimp simp: modify_map_cases const_def split: if_split_asm)
   apply(fastforce)
  apply(simp split del: if_split)
  apply (clarsimp simp: modify_map_cases const_def split: if_split_asm)
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
      subgoal by (simp add: s_d_swap_def src dest split: if_split_asm)
     apply simp
     apply (drule revokable)+
     subgoal by (simp add: s_d_swap_def src dest split: if_split_asm)
    apply simp
    apply (drule n_cap)+
    subgoal by (simp add: s_d_swap_def src dest split: if_split_asm)
   apply simp
   apply (drule badge_n)+
   subgoal by (simp add: s_d_swap_def src dest split: if_split_asm)
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
   apply (simp add: s_d_swap_def src dest split: if_split_asm)
  apply clarsimp
  apply (insert src_derived dest_derived)[1]
  apply (erule isMDBParentOf_eq)
     apply simp
     apply (rule weak_derived_sym')
     apply (drule n_cap)+
     apply (simp add: s_d_swap_def src dest split: if_split_asm)
    apply simp
    apply (drule revokable)+
    subgoal by (simp add: s_d_swap_def src dest split: if_split_asm)
   apply simp
   apply (rule weak_derived_sym')
   apply (drule n_cap)+
   subgoal by (simp add: s_d_swap_def src dest split: if_split_asm)
  apply simp
  apply (drule badge_n)+
  subgoal by (simp add: s_d_swap_def src dest split: if_split_asm)
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

declare if_split [split del]

(*
lemma corres_bind_ext:
"corres_underlying srel nf rrel G G' g (g') \<Longrightarrow>
corres_underlying srel nf rrel G G' (do do_extended_op (return ()); g od) (g')"
  apply (simp add: corres_underlying_def do_extended_op_def return_def gets_def get_def put_def bind_def select_f_def modify_def mk_ef_def wrap_ext_op_det_ext_ext_def wrap_ext_op_unit_def)
  done
*)

(* consider putting in AINVS or up above cteInsert_corres *)
lemma next_slot_eq:
  "\<lbrakk>next_slot p t' m' = x; t' = t; m' = m\<rbrakk> \<Longrightarrow> next_slot p t m = x"
  by simp

lemma inj_on_image_set_diff15 : (* for compatibility of assumptions *)
  "\<lbrakk>inj_on f C; A \<subseteq> C; B \<subseteq> C\<rbrakk> \<Longrightarrow> f ` (A - B) = f ` A - f ` B"
by (rule inj_on_image_set_diff; auto)

lemma cteSwap_corres:
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
  (is "corres _ ?P ?P' _ _") using assms including no_pre
  supply None_upd_eq[simp del]
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
  apply (thin_tac "t : state_relation" for t)
  apply (thin_tac "(P and (\<lambda>s. Q s)) s" for Q P)
  apply (thin_tac "(P and (\<lambda>s. Q s)) s'" for Q P)
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
    apply (auto simp: modify_map_if split: if_split_asm)[1]
   apply clarsimp
   apply (subgoal_tac "mdbNext node = mdbPrev src_node \<or>
                       mdbNext node = mdbNext dest_node")
    apply (erule disjE)
     apply simp
     apply (erule (1) valid_dlistEp, simp)
     apply simp
    apply (erule_tac p="cte_map dest" in valid_dlistEn, assumption, simp)
    apply simp
   apply (auto simp: modify_map_if split: if_split_asm)[1]
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
  apply (drule (2) updateMDB_the_lot')
     apply (erule (1) impE, assumption)
    apply (fastforce simp only: no_0_modify_map)
   apply assumption
  apply (elim conjE TrueE, simp only:)
  apply (drule (2) updateMDB_the_lot', fastforce, simp only: no_0_modify_map, assumption)
  apply (drule in_getCTE, elim conjE, simp only:)
  apply (drule (2) updateMDB_the_lot', fastforce, simp only: no_0_modify_map, assumption)
  apply (elim conjE TrueE, simp only:)
  apply (drule (2) updateMDB_the_lot', fastforce, simp only: no_0_modify_map, assumption)
  apply (elim conjE TrueE, simp only:)
  apply (drule (2) updateMDB_the_lot', fastforce, simp only: no_0_modify_map, assumption)
  apply (elim conjE TrueE, simp only:)
  apply (drule (2) updateMDB_the_lot', fastforce, simp only: no_0_modify_map, assumption)
  apply (simp only: pspace_relations_def refl)
  apply (rule conjI, rule TrueI)+
  apply (thin_tac "ksMachineState t = p" for t p)+
  apply (thin_tac "ksCurThread t = p" for t p)+
  apply (thin_tac "ksReadyQueues t = p" for t p)+
  apply (thin_tac "ksSchedulerAction t = p" for t p)+
  apply (thin_tac "machine_state t = p" for t p)+
  apply (thin_tac "cur_thread t = p" for t p)+
  apply (thin_tac "ksDomScheduleIdx t = p" for t p)+
  apply (thin_tac "ksDomSchedule t = p" for t p)+
  apply (thin_tac "ksCurDomain t = p" for t p)+
  apply (thin_tac "ksDomainTime t = p" for t p)+
  apply (thin_tac "ready_queues t = p" for t p)+
  apply (thin_tac "cur_domain t = p" for t p)+
  apply (thin_tac "idle_thread t = p" for t p)+
  apply (thin_tac "work_units_completed t = p" for t p)+
  apply (thin_tac "domain_index t = p" for t p)+
  apply (thin_tac "domain_list t = p" for t p)+
  apply (thin_tac "domain_time t = p" for t p)+
  apply (thin_tac "ekheap t = p" for t p)+
  apply (thin_tac "scheduler_action t = p" for t p)+
  apply (thin_tac "ksArchState t = p" for t p)+
  apply (thin_tac "gsCNodes t = p" for t p)+
  apply (thin_tac "ksWorkUnitsCompleted t = p" for t p)+
  apply (thin_tac "ksInterruptState t = p" for t p)+
  apply (thin_tac "ksIdleThread t = p" for t p)+
  apply (thin_tac "gsUserPages t = p" for t p)+
  apply (thin_tac "ekheap_relation e p" for e p)+
  apply (thin_tac "interrupt_state_relation n s s'" for n s s')+
  apply (thin_tac "(s,s') \<in> arch_state_relation" for s s')+
  apply (thin_tac "sched_act_relation s s'" for s s')+
  apply (thin_tac "ready_queues_relation s s'" for s s')+
  apply (simp only: simp_thms no_0_modify_map)
  apply (clarsimp simp: cte_wp_at_ctes_of cong: if_cong)
  apply (thin_tac "ctes_of x = y" for x y)+
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
  apply (rule conjI)
   subgoal by (simp only: simp_thms ghost_relation_typ_at set_cap_a_type_inv X64.data_at_def)
  apply (thin_tac "ksArchState t = p" for t p)+
  apply (thin_tac "gsCNodes t = p" for t p)+
  apply (thin_tac "ksWorkUnitsCompleted t = p" for t p)+
  apply (thin_tac "ksInterruptState t = p" for t p)+
  apply (thin_tac "ksIdleThread t = p" for t p)+
  apply (thin_tac "gsUserPages t = p" for t p)+
  apply (thin_tac "ekheap_relation e p" for e p)+
  apply (thin_tac "ksMachineState t = p" for t p)+
  apply (thin_tac "ksCurThread t = p" for t p)+
  apply (thin_tac "ksReadyQueues t = p" for t p)+
  apply (thin_tac "ksSchedulerAction t = p" for t p)+
  apply (thin_tac "ksDomScheduleIdx t = p" for t p)+
  apply (thin_tac "ksDomSchedule t = p" for t p)+
  apply (thin_tac "ksCurDomain t = p" for t p)+
  apply (thin_tac "ksDomainTime t = p" for t p)+
  apply (thin_tac "pspace_relation s t" for s t)+
  apply (thin_tac "ghost_relation h s t" for h s t)+
  apply(subst conj_assoc[symmetric])
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp add: revokable_relation_def in_set_cap_cte_at
                   simp del: split_paired_All)
   apply (drule set_cap_caps_of_state_monad)+
   apply (simp del: split_paired_All split: if_split)
   apply (rule conjI)
    apply (clarsimp simp: cte_wp_at_caps_of_state simp del: split_paired_All)
    apply (drule(1) mdb_swap.revokable)
    apply (erule_tac x="dest" in allE)
    apply (erule impE)
     subgoal by (clarsimp simp: null_filter_def weak_derived_Null split: if_splits)
    subgoal by simp
   apply (clarsimp simp del: split_paired_All)
   apply (rule conjI)
    apply (clarsimp simp: cte_wp_at_caps_of_state simp del: split_paired_All)
    apply (drule (1) mdb_swap.revokable)
    apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map src")
     apply (simp del: split_paired_All)
     apply (erule_tac x="src" in allE)
     apply (erule impE)
      subgoal by (clarsimp simp: null_filter_def weak_derived_Null split: if_splits)
     subgoal by simp
    apply (drule caps_of_state_cte_at)+
    apply (erule (5) cte_map_inj)
   apply (clarsimp simp: cte_wp_at_caps_of_state simp del: split_paired_All)
   apply (drule (1) mdb_swap.revokable)
   apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
    prefer 2
    subgoal by (clarsimp simp: null_filter_def split: if_splits)
   apply clarsimp
   apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map src")
    apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map dest")
     subgoal by (clarsimp simp del: split_paired_All)
    apply (drule caps_of_state_cte_at)+
    apply (drule null_filter_caps_of_stateD)+
    apply (erule cte_map_inj, erule cte_wp_cte_at, assumption+)
   apply (drule caps_of_state_cte_at)+
   apply (drule null_filter_caps_of_stateD)+
   apply (erule cte_map_inj, erule cte_wp_cte_at, assumption+)
  apply (subgoal_tac "no_loops (ctes_of b)")
   prefer 2
   subgoal by (simp add: valid_mdb_ctes_def mdb_chain_0_no_loops)
  apply (subgoal_tac "mdb_swap_abs (cdt a) src dest a")
   prefer 2
   apply (erule mdb_swap_abs.intro)
      apply (erule cte_wp_at_weakenE, rule TrueI)
     apply (erule cte_wp_at_weakenE, rule TrueI)
    apply (rule refl)
   apply assumption
  apply (frule mdb_swap_abs''.intro)
  apply (drule_tac t="cdt_list (a)" in mdb_swap_abs'.intro)
   subgoal by (simp add: mdb_swap_abs'_axioms_def)
  apply (thin_tac "modify_map m f p p' = t" for m f p p' t)
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
    apply (simp add: s_d_swap_def split: if_split)
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
   apply (simp split: if_split)
   apply (frule_tac p="s_d_swap c src dest" in inj_on_descendants_cte_map, assumption+)
   apply (rule conjI, clarsimp)
    apply (rule conjI, clarsimp)
     apply (subst inj_on_image_set_diff15, assumption)
       apply (rule subset_refl)
      apply simp
     apply simp
    apply clarsimp
    apply (rule conjI, clarsimp)
     apply (drule cte_map_inj_eq)
          apply (erule cte_wp_at_weakenE, rule TrueI)
         apply (erule (1) descendants_of_cte_at)
        apply assumption+
     subgoal by simp
    apply (subst insert_minus_eq, assumption)
    apply clarsimp
    apply (subst insert_minus_eq [where x="cte_map dest"], assumption)
    apply (subst inj_on_image_set_diff15)
       apply (erule (3) inj_on_descendants_cte_map)
      apply (rule subset_refl)
     apply clarsimp
    subgoal by auto
   apply clarsimp
   apply (rule conjI, clarsimp)
    apply (rule conjI, clarsimp)
     apply (drule cte_map_inj_eq)
          apply (erule cte_wp_at_weakenE, rule TrueI)
         apply (erule (1) descendants_of_cte_at)
        apply assumption+
     apply simp
    apply clarsimp
    apply (subst inj_on_image_set_diff15)
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
     apply(rule cte_map_inj; simp?)
     apply(erule cte_wp_at_weakenE, simp)
    apply(rule conjI)
     apply(rule cte_map_inj; simp?)
     apply(erule cte_wp_at_weakenE, simp)
    apply(frule mdb_swap.m_exists)
     apply(simp)
    apply(clarsimp)
    apply(frule_tac cte="CTE cap' node'" in valid_mdbD1')
      apply(clarsimp)
     apply(simp add: valid_mdb'_def)
    apply(clarsimp)
   subgoal by (rule cte_at_next_slot; simp)
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
     apply(rule cte_map_inj; simp?)
     apply(erule cte_wp_at_weakenE, simp)
    apply(rule conjI)
     apply(rule cte_map_inj; simp?)
     apply(erule cte_wp_at_weakenE, simp)
    apply(frule mdb_swap.m_exists)
     apply(simp)
    apply(clarsimp)
    apply(frule_tac cte="CTE cap' node'" in valid_mdbD1')
      apply(clarsimp)
     apply(simp add: valid_mdb'_def)
    apply(clarsimp)
   subgoal by (rule cte_at_next_slot; simp)
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
    apply(rule cte_map_inj; simp?)
    apply(erule cte_wp_at_weakenE, simp)
   apply(rule conjI)
    apply(rule cte_map_inj; simp?)
    apply(erule cte_wp_at_weakenE, simp)
   apply(rule conjI)
    apply(frule mdb_swap.m_exists)
     apply(simp)
    apply(clarsimp)
     apply(frule_tac cte="CTE src_cap src_node" in valid_mdbD2')
      subgoal by (clarsimp)
     apply(simp add: valid_mdb'_def)
    apply(clarsimp)
    apply(drule cte_map_inj_eq; simp?)
     subgoal by (rule cte_at_next_slot'; simp)
    apply(erule cte_wp_at_weakenE, simp)
   apply(frule mdb_swap.m_exists)
    apply(simp)
   apply(clarsimp)
   apply(frule_tac cte="CTE dest_cap dest_node" in valid_mdbD2')
     apply(clarsimp)
    apply(simp add: valid_mdb'_def)
   apply(clarsimp)
   apply(drule cte_map_inj_eq; simp?)
    subgoal by (rule cte_at_next_slot'; simp)
   apply(erule cte_wp_at_weakenE, simp)
  by (rule cte_at_next_slot; simp)


lemma capSwapForDelete_corres:
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
    apply (rule_tac P1=wellformed_cap in corres_split[OF get_cap_corres_P])
      apply (rule_tac P1=wellformed_cap in corres_split[OF get_cap_corres_P])
        apply (rule cteSwap_corres, rule refl, rule refl, clarsimp+)
       apply (wp get_cap_wp getCTE_wp')+
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (drule (1) caps_of_state_valid_cap)+
   apply (simp add: valid_cap_def2)
  apply (clarsimp simp: cte_wp_at_ctes_of)
done

declare if_split [split]
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
  (isNotificationCap cap \<longrightarrow> (capNtfnBadge cap = capNtfnBadge cap' \<or> no_child' s cte))"

lemma subtree_no_parent:
  assumes "m \<turnstile> p \<rightarrow> x"
  assumes "mdbNext (cteMDBNode cte) \<noteq> 0"
  assumes "\<not> isMDBParentOf cte next"
  assumes "m p = Some cte"
  assumes "m (mdbNext (cteMDBNode cte)) = Some next"
  shows "False" using assms
  by induct (auto simp: parentOf_def mdb_next_unfold)

context begin interpretation Arch . (*FIXME: arch-split*)

lemma ensureNoChildren_corres:
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

end
end
