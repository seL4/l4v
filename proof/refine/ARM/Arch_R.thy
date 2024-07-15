(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Top level architecture related proofs.
*)

theory Arch_R
imports Untyped_R Finalise_R
begin

unbundle l4v_word_context

context begin interpretation Arch . (*FIXME: arch_split*)

declare is_aligned_shiftl [intro!]
declare is_aligned_shiftr [intro!]

definition
  "asid_ci_map i \<equiv>
  case i of ARM_A.MakePool frame slot parent base \<Rightarrow>
  ARM_H.MakePool frame (cte_map slot) (cte_map parent) base"

definition
  "valid_aci' aci \<equiv> case aci of MakePool frame slot parent base \<Rightarrow>
  \<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = NullCap) slot s \<and>
      cte_wp_at' (\<lambda>cte. \<exists>idx.  cteCap cte = UntypedCap False frame pageBits idx) parent s \<and>
      descendants_of' parent (ctes_of s) = {} \<and>
      slot \<noteq> parent \<and>
      ex_cte_cap_to' slot s \<and>
      sch_act_simple s \<and>
      is_aligned base asid_low_bits \<and> base \<le> 2^asid_bits - 1"

lemma vp_strgs':
  "valid_pspace' s \<longrightarrow> pspace_distinct' s"
  "valid_pspace' s \<longrightarrow> pspace_aligned' s"
  "valid_pspace' s \<longrightarrow> valid_mdb' s"
  by auto

lemma safe_parent_strg':
  "cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap False frame pageBits idx) p s \<and>
   descendants_of' p (ctes_of s) = {} \<and>
   valid_pspace' s
  \<longrightarrow> safe_parent_for' (ctes_of s) p (ArchObjectCap (ASIDPoolCap frame base))"
  apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply (simp add: isCap_simps)
  apply (subst conj_comms)
  apply (rule context_conjI)
   apply (drule ctes_of_valid_cap', fastforce)
   apply (clarsimp simp: valid_cap'_def capAligned_def)
   apply (drule is_aligned_no_overflow)
   apply (clarsimp simp: capRange_def asid_low_bits_def pageBits_def)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps capRange_def asid_low_bits_def pageBits_def)
  done

lemma descendants_of'_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q (descendants_of' t (null_filter' (ctes_of s)))\<rbrace>
   \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q (descendants_of' t (ctes_of s))\<rbrace>"
  apply (clarsimp simp:valid_def)
  apply (subst null_filter_descendants_of')
  prefer 2
   apply fastforce
  apply simp
  done

lemma createObject_typ_at':
  "\<lbrace>\<lambda>s.  koTypeOf ty = otype \<and> is_aligned ptr (objBitsKO ty) \<and> objBitsKO ty < word_bits \<and>
         pspace_aligned' s \<and> pspace_bounded' s \<and> pspace_no_overlap' ptr (objBitsKO ty) s\<rbrace>
   createObjects' ptr (Suc 0) ty 0
   \<lbrace>\<lambda>rv s. typ_at' otype ptr s\<rbrace>"
  apply (clarsimp simp:createObjects'_def alignError_def split_def | wp unless_wp | wpc )+
  apply (clarsimp simp:obj_at'_def ko_wp_at'_def typ_at'_def)+
  apply (subgoal_tac "ps_clear ptr (objBitsKO ty)
    (s\<lparr>ksPSpace := \<lambda>a. if a = ptr then Some ty else ksPSpace s a\<rparr>)")
  apply (simp add:ps_clear_def)+
  apply (rule ccontr)
  apply (drule int_not_emptyD)
  apply clarsimp
  apply (unfold pspace_no_overlap'_def)
  apply (erule allE)+
  apply (erule(1) impE)
  apply (subgoal_tac "x \<in> {x..x + 2 ^ objBitsKO y - 1}")
   apply (fastforce simp: p_assoc_help)
  apply (rule first_in_uptoD)
  apply (frule(1) pspace_alignedD')
  apply (drule(1) pspace_boundedD')
  apply (clarsimp simp: is_aligned_no_wrap' p_assoc_help)
  done


lemma set_cap_device_and_range_aligned:
  "is_aligned ptr sz \<Longrightarrow> \<lbrace>\<lambda>_. True\<rbrace>
    set_cap
     (cap.UntypedCap dev ptr sz idx)
     aref
    \<lbrace>\<lambda>rv s.
        \<exists>slot.
           cte_wp_at
            (\<lambda>c. cap_is_device c = dev \<and>
                 up_aligned_area ptr sz \<subseteq> cap_range c)
            slot s\<rbrace>"
  apply (subst is_aligned_neg_mask_eq[symmetric])
   apply simp
  apply (wp set_cap_device_and_range)
  done

lemma performASIDControlInvocation_corres:
  "asid_ci_map i = i' \<Longrightarrow>
  corres dc
         (einvs and ct_active and valid_aci i and schact_is_rct)
         (invs' and ct_active' and valid_aci' i')
         (perform_asid_control_invocation i)
         (performASIDControlInvocation i')"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (cases i)
  apply (rename_tac word1 prod1 prod2 word2)
  apply (clarsimp simp: asid_ci_map_def)
  apply (simp add: perform_asid_control_invocation_def placeNewObject_def2
                   performASIDControlInvocation_def)
  apply (rule corres_name_pre)
  apply (clarsimp simp:valid_aci_def valid_aci'_def cte_wp_at_ctes_of cte_wp_at_caps_of_state)
  apply (subgoal_tac "valid_cap' (capability.UntypedCap False word1 pageBits idx) s'")
   prefer 2
   apply (case_tac ctea)
   apply clarsimp
   apply (erule ctes_of_valid_cap')
   apply fastforce
  apply (frule valid_capAligned)
  apply (clarsimp simp: capAligned_def page_bits_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (erule deleteObjects_corres)
       apply (simp add:pageBits_def)
      apply (rule corres_split[OF getSlotCap_corres], simp)
        apply (rule_tac F = " pcap = (cap.UntypedCap False word1 pageBits idxa)" in corres_gen_asm)
        apply (rule corres_split[OF updateFreeIndex_corres])
            apply (clarsimp simp:is_cap_simps)
           apply (simp add: free_index_of_def)
          apply (rule corres_split)
             apply (rule corres_retype [where ty="Inl (KOArch (KOASIDPool F))",
                                        unfolded APIType_map2_def makeObjectKO_def,
                                        THEN createObjects_corres',simplified,
                                        where val = "makeObject::asidpool"])
                   apply simp
                  apply (simp add: objBits_simps obj_bits_api_def arch_kobj_size_def
                                   default_arch_object_def archObjSize_def)+
               apply (simp add: obj_relation_retype_def default_object_def
                                default_arch_object_def objBits_simps archObjSize_def)
               apply (simp add: other_obj_relation_def asid_pool_relation_def)
               apply (simp add: makeObject_asidpool const_def inv_def)
              apply (rule range_cover_full)
               apply (simp add:obj_bits_api_def arch_kobj_size_def default_arch_object_def)+
            apply (rule corres_split)
               apply (rule cteInsert_simple_corres, simp, rule refl, rule refl)
              apply (rule_tac F="is_aligned word2 asid_low_bits" in corres_gen_asm)
              apply (simp add: is_aligned_mask dc_def[symmetric])
              apply (rule corres_split[where P=\<top> and P'=\<top> and r'="\<lambda>t t'. t = t' o ucast"])
                 apply (clarsimp simp: state_relation_def arch_state_relation_def)
                apply (rule corres_trivial)
                apply (rule corres_modify)
                apply (thin_tac "x \<in> state_relation" for x)
                apply (clarsimp simp: state_relation_def arch_state_relation_def o_def)
                apply (rule ext)
                apply clarsimp
                apply (erule_tac P = "x = asid_high_bits_of word2" in notE)
                apply (rule word_eqI[rule_format])
                apply (drule_tac x1="ucast x" in bang_eq [THEN iffD1])
                apply (erule_tac x=n in allE)
                apply (simp add: word_size nth_ucast)
               apply wp+
           apply (strengthen safe_parent_strg[where idx = "2^pageBits"])
           apply (strengthen invs_valid_objs invs_distinct
                             invs_psp_aligned invs_mdb
                  | simp cong:conj_cong)+
           apply (wp retype_region_plain_invs[where sz = pageBits]
                     retype_cte_wp_at[where sz = pageBits])+
          apply (strengthen vp_strgs'
                 safe_parent_strg'[where idx = "2^pageBits"])
          apply (simp cong: conj_cong)
          apply (wp createObjects_valid_pspace'
                    [where sz = pageBits and ty="Inl (KOArch (KOASIDPool undefined))"])
               apply (simp add: makeObjectKO_def)+
           apply (simp add:objBits_simps archObjSize_def range_cover_full)+
          apply (clarsimp simp:valid_cap'_def)
          apply (wp createObject_typ_at'
                    createObjects_orig_cte_wp_at'[where sz = pageBits])
          apply (rule descendants_of'_helper)
          apply (wp createObjects_null_filter'
                    [where sz = pageBits and ty="Inl (KOArch (KOASIDPool undefined))"])

         apply (clarsimp simp: conj_comms obj_bits_api_def arch_kobj_size_def
                objBits_simps archObjSize_def default_arch_object_def
                pred_conj_def)
         apply (clarsimp simp: conj_comms
               | strengthen invs_mdb invs_valid_pspace)+
         apply (simp add:region_in_kernel_window_def)
         apply (wp set_untyped_cap_invs_simple[where sz = pageBits]
                   set_cap_cte_wp_at
                   set_cap_caps_no_overlap[where sz = pageBits]
                   set_cap_no_overlap
                   set_cap_device_and_range_aligned[where dev = False,simplified]
                   set_untyped_cap_caps_overlap_reserved[where sz = pageBits])+
        apply (clarsimp simp: conj_comms obj_bits_api_def arch_kobj_size_def
                              objBits_simps archObjSize_def default_arch_object_def
                              makeObjectKO_def range_cover_full
                        simp del: capFreeIndex_update.simps
               | strengthen invs_valid_pspace' invs_pspace_aligned'
                            invs_pspace_distinct' invs_pspace_bounded'
                            exI[where x="makeObject :: asidpool"])+
        apply (wp updateFreeIndex_forward_invs'
          updateFreeIndex_pspace_no_overlap'
          updateFreeIndex_caps_no_overlap''
          updateFreeIndex_descendants_of2
          updateFreeIndex_cte_wp_at
          updateFreeIndex_caps_overlap_reserved
            | simp add: descendants_of_null_filter' split del: if_split)+
       apply (wp get_cap_wp)+
     apply (subgoal_tac "word1 && ~~ mask pageBits = word1 \<and> pageBits \<le> word_bits \<and> word_size_bits \<le> pageBits")
      prefer 2
      apply (clarsimp simp:pageBits_def word_bits_def is_aligned_neg_mask_eq word_size_bits_def)
     apply (simp only:delete_objects_rewrite)
     apply wp+
    apply (clarsimp simp: conj_comms)
    apply (clarsimp simp: conj_comms ex_disj_distrib
           | strengthen invs_valid_pspace' invs_pspace_aligned' invs_pspace_bounded'
                        invs_pspace_distinct')+
    apply (wp deleteObjects_invs'[where p="makePoolParent i'"]
              deleteObjects_cte_wp_at'
              deleteObjects_descendants[where p="makePoolParent i'"])
    apply (clarsimp split del: if_split simp:valid_cap'_def)
    apply (wp hoare_vcg_ex_lift
              deleteObjects_caps_no_overlap''[where slot="makePoolParent i'"]
              deleteObject_no_overlap
              deleteObjects_ct_active'[where cref="makePoolParent i'"])
    apply (clarsimp simp: is_simple_cap_def valid_cap'_def max_free_index_def is_cap_simps
                    cong: conj_cong)
    apply (strengthen empty_descendants_range_in')
    apply (wp deleteObjects_descendants[where p="makePoolParent i'"]
              deleteObjects_cte_wp_at'
              deleteObjects_null_filter[where p="makePoolParent i'"])
   apply (clarsimp simp:invs_mdb max_free_index_def invs_untyped_children schact_is_rct)
   apply (subgoal_tac "detype_locale x y sa" for x y)
    prefer 2
    apply (simp add:detype_locale_def)
    apply (fastforce simp:cte_wp_at_caps_of_state descendants_range_def2
            empty_descendants_range_in invs_untyped_children)
   apply (intro conjI)
          apply (clarsimp)
         apply (erule(1) caps_of_state_valid)
        subgoal by (fastforce simp: cte_wp_at_caps_of_state descendants_range_def2
                                    empty_descendants_range_in)
       apply (fold_subgoals (prefix))[2]
      subgoal premises prems using prems by (clarsimp simp:invs_def valid_state_def)+
     apply (clarsimp simp:cte_wp_at_caps_of_state)
    apply (drule detype_locale.non_null_present)
     apply (fastforce simp:cte_wp_at_caps_of_state)
    apply simp
   apply (frule_tac ptr = "(aa,ba)" in detype_invariants [rotated 3])
         apply fastforce
        apply simp
       apply (clarsimp simp: schact_is_rct)
      apply (simp add: cte_wp_at_caps_of_state)
     apply (simp add: is_cap_simps)
    apply (simp add:empty_descendants_range_in descendants_range_def2)
   apply (frule intvl_range_conv[where bits = pageBits])
    apply (clarsimp simp:pageBits_def word_bits_def)
   apply (clarsimp simp: invs_valid_objs cte_wp_at_caps_of_state range_cover_full
                         invs_psp_aligned invs_distinct cap_master_cap_simps is_cap_simps
                         is_simple_cap_def)
   apply (clarsimp simp: conj_comms)
   apply (rule conjI,clarsimp)
   apply (frule ex_cte_cap_protects)
        apply (simp add:cte_wp_at_caps_of_state)
       apply (simp add:empty_descendants_range_in)
      apply fastforce
     apply (rule subset_refl)
    apply fastforce
   apply clarsimp
   apply (rule conjI,clarsimp simp:clear_um_def)
   apply (simp add:detype_clear_um_independent)
   apply (rule conjI,erule caps_no_overlap_detype[OF descendants_range_caps_no_overlapI])
     apply (clarsimp simp:is_aligned_neg_mask_eq cte_wp_at_caps_of_state)
     apply (simp add:empty_descendants_range_in)+
   apply (rule conjI)
    apply clarsimp
    apply (drule_tac p = "(aa,ba)" in cap_refs_in_kernel_windowD2[OF caps_of_state_cteD])
     apply fastforce
    apply (clarsimp simp: region_in_kernel_window_def valid_cap_def
                          cap_aligned_def is_aligned_neg_mask_eq detype_def clear_um_def)
   apply (rule conjI, rule pspace_no_overlap_subset,
         rule pspace_no_overlap_detype[OF caps_of_state_valid])
        apply (simp add:invs_psp_aligned invs_valid_objs is_aligned_neg_mask_eq)+
   apply (simp add: detype_def clear_um_def)
  apply (drule_tac x = "cte_map (aa,ba)" in pspace_relation_cte_wp_atI[OF state_relation_pspace_relation])
    apply (simp add:invs_valid_objs)+
  apply clarsimp
  apply (drule cte_map_inj_eq)
       apply ((fastforce simp:cte_wp_at_caps_of_state)+)[5]
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_valid_pspace' conj_comms cte_wp_at_ctes_of
                       valid_cap_simps')
  apply (strengthen refl)
  apply clarsimp
  apply (frule empty_descendants_range_in')
  apply (intro conjI,
         simp_all add: is_simple_cap'_def isCap_simps descendants_range'_def2
                       null_filter_descendants_of'[OF null_filter_simp']
                       capAligned_def asid_low_bits_def)
       apply (erule descendants_range_caps_no_overlapI')
        apply (fastforce simp:cte_wp_at_ctes_of is_aligned_neg_mask_eq)
       apply (simp add:empty_descendants_range_in')
      apply (simp add:word_bits_def pageBits_def)
     apply (rule is_aligned_weaken)
      apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1,simplified])
     apply (simp add:pageBits_def)
    apply clarsimp
    apply (drule(1) cte_cap_in_untyped_range)
         apply (fastforce simp: cte_wp_at_ctes_of)
        apply assumption+
     apply fastforce
    apply simp
   apply clarsimp
   apply (drule (1) cte_cap_in_untyped_range)
        apply (fastforce simp add: cte_wp_at_ctes_of)
       apply assumption+
     apply (clarsimp simp: invs'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
    apply fastforce+
  done

definition
  archinv_relation :: "arch_invocation \<Rightarrow> Arch.invocation \<Rightarrow> bool"
where
  "archinv_relation ai ai' \<equiv> case ai of
     arch_invocation.InvokePageTable pti \<Rightarrow>
       \<exists>pti'. ai' = InvokePageTable pti' \<and> page_table_invocation_map pti pti'
   | arch_invocation.InvokePageDirectory pdi \<Rightarrow>
       \<exists>pdi'. ai' = InvokePageDirectory pdi' \<and> page_directory_invocation_map pdi pdi'
   | arch_invocation.InvokePage pgi \<Rightarrow>
       \<exists>pgi'. ai' = InvokePage pgi' \<and> page_invocation_map pgi pgi'
   | arch_invocation.InvokeASIDControl aci \<Rightarrow>
       \<exists>aci'. ai' = InvokeASIDControl aci' \<and> aci' = asid_ci_map aci
   | arch_invocation.InvokeASIDPool ap \<Rightarrow>
       \<exists>ap'. ai' = InvokeASIDPool ap' \<and>  ap' = asid_pool_invocation_map ap"

definition
  valid_arch_inv' :: "Arch.invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_arch_inv' ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> valid_pti' pti
   | InvokePageDirectory pdi \<Rightarrow> \<top>
   | InvokePage pgi \<Rightarrow> valid_page_inv' pgi
   | InvokeASIDControl aci \<Rightarrow> valid_aci' aci
   | InvokeASIDPool ap \<Rightarrow> valid_apinv' ap"

lemma mask_vmrights_corres:
  "maskVMRights (vmrights_map R) (rightsFromWord d) =
  vmrights_map (mask_vm_rights R (data_to_rights d))"
  by (clarsimp simp: rightsFromWord_def data_to_rights_def
                     vmrights_map_def Let_def maskVMRights_def
                     mask_vm_rights_def nth_ucast
                     validate_vm_rights_def vm_read_write_def
                     vm_kernel_only_def vm_read_only_def
               split: bool.splits)

lemma vm_attributes_corres:
  "vmattributes_map (attribs_from_word w) = attribsFromWord w"
  by (clarsimp simp: attribsFromWord_def attribs_from_word_def
                     Let_def vmattributes_map_def)

lemma checkVPAlignment_corres:
  "corres (ser \<oplus> dc) \<top> \<top>
          (check_vp_alignment sz w)
          (checkVPAlignment sz w)"
  apply (simp add: check_vp_alignment_def checkVPAlignment_def)
  apply (cases sz, simp_all add: corres_returnOk unlessE_whenE is_aligned_mask)
     apply ((rule corres_guard_imp, rule corres_whenE, rule refl, auto)[1])+
  done

lemma checkVP_wpR [wp]:
  "\<lbrace>\<lambda>s. vmsz_aligned w sz \<longrightarrow> P () s\<rbrace>
  checkVPAlignment sz w \<lbrace>P\<rbrace>, -"
  apply (simp add: checkVPAlignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp whenE_wp|wpc)+
  apply (simp add: is_aligned_mask vmsz_aligned_def)
  done

lemma asidHighBits [simp]:
  "asidHighBits = asid_high_bits"
  by (simp add: asidHighBits_def asid_high_bits_def)

declare word_unat_power [symmetric, simp del]

lemma ARMMMU_improve_cases:
  "(if isPageDirectoryCap cap then P
    else if isPageTableCap cap then Q
    else if isPageCap cap then R
    else if isASIDControlCap cap then S
    else if isASIDPoolCap cap then T
    else undefined)
    =
   (if isPageDirectoryCap cap then P
    else if isPageTableCap cap then Q
    else if isPageCap cap then R
    else if isASIDControlCap cap then S
    else T)"
  by (cases cap, simp_all add: isCap_simps)


crunch "ARM_H.decodeInvocation"
  for inv[wp]: "P"
  (wp: crunch_wps mapME_x_inv_wp getASID_wp
   simp: crunch_simps ARMMMU_improve_cases)

lemma case_option_corresE:
  assumes nonec: "corres r Pn Qn (nc >>=E f) (nc' >>=E g)"
  and     somec: "\<And>v'. corres r (Ps v') (Qs v') (sc v' >>=E f) (sc' v' >>=E g)"
  shows "corres r (case_option Pn Ps v) (case_option Qn Qs v) (case_option nc sc v >>=E f) (case_option nc' sc' v >>=E g)"
  apply (cases v)
   apply simp
   apply (rule nonec)
  apply simp
  apply (rule somec)
  done


lemma cap_relation_Untyped_eq:
  "cap_relation c (UntypedCap d p sz f) = (c = cap.UntypedCap d p sz f)"
  by (cases c) auto

lemma vmsz_aligned_less_kernel_base_eq:
  "\<lbrakk>ptr + 2 ^ pageBitsForSize vmpage_size - 1 < kernel_base;vmsz_aligned ptr vmpage_size\<rbrakk>
   \<Longrightarrow> ptr < kernel_base"
  apply (simp add:vmsz_aligned_def)
  apply (rule ccontr)
  apply (simp add:not_less)
  apply (drule(1) less_le_trans)
  apply (drule is_aligned_no_overflow)
  apply (simp add:not_less[symmetric])
  done

declare check_vp_alignment_inv[wp del]

lemma select_ext_fa:
  "free_asid_select asid_tbl \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_select asid_tbl) S) :: (7 word) det_ext_monad)
   = return (free_asid_select asid_tbl)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def fail_def)

lemma select_ext_fap:
  "free_asid_pool_select p b \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_pool_select p b) S) :: (10 word) det_ext_monad)
   = return (free_asid_pool_select p b)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def)

lemma lookup_pt_slot_no_fail_corres[simp]:
  "lookupPTSlotFromPT pt vptr
    = (do stateAssert (page_table_at' pt) []; return (lookup_pt_slot_no_fail pt vptr) od)"
  by (simp add: lookup_pt_slot_no_fail_def lookupPTSlotFromPT_def mask_def checkPTAt_def
                ptBits_def pteBits_def pageBits_def)

lemma page_base_corres[simp]:
  "pageBase vaddr vmsize = page_base vaddr vmsize"
  by (clarsimp simp: pageBase_def page_base_def)

lemma flush_type_map:
  "ARM_H.isPageFlushLabel (invocation_type (mi_label mi))
   \<or> ARM_H.isPDFlushLabel (invocation_type (mi_label mi))
  \<Longrightarrow> labelToFlushType (mi_label mi) =
          flush_type_map (label_to_flush_type (invocation_type (mi_label mi)))"
  by (clarsimp simp: label_to_flush_type_def labelToFlushType_def flush_type_map_def
                        ARM_H.isPageFlushLabel_def ARM_H.isPDFlushLabel_def
                 split: ARM_A.flush_type.splits invocation_label.splits arch_invocation_label.splits)

lemma resolveVAddr_corres:
  "\<lbrakk> is_aligned pd pd_bits; vaddr < kernel_base \<rbrakk> \<Longrightarrow>
  corres (=) (pspace_aligned and valid_vspace_objs and page_directory_at pd
                 and (\<exists>\<rhd> (lookup_pd_slot pd vaddr && ~~ mask pd_bits)))
                (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> vs_valid_duplicates' (ksPSpace s))
          (resolve_vaddr pd vaddr) (resolveVAddr pd vaddr)"
  apply (clarsimp simp: resolve_vaddr_def resolveVAddr_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac R="\<lambda>rv s. valid_pde rv s \<and> pspace_aligned s"
               and R'="\<lambda>_ s. pspace_distinct' s \<and> pspace_aligned' s
                           \<and> vs_valid_duplicates' (ksPSpace s)"
                in corres_split[OF get_master_pde_corres])
       apply simp
      apply (case_tac rv, simp_all add: pde_relation'_def)[1]
      apply (rule corres_stateAssert_assume_stronger)
       apply (rule stronger_corres_guard_imp)
         apply (rule corres_split[OF get_master_pte_corres[OF refl]])
           apply (rule corres_trivial)
           apply (case_tac rva, simp_all add: pte_relation'_def)[1]
          apply (wp get_master_pte_inv)+
        apply (clarsimp simp: page_table_pte_at_lookupI)
       apply (clarsimp simp: page_table_pte_at_lookupI' page_table_at_state_relation)
      apply clarsimp
      apply (erule(3) page_table_at_state_relation)
     apply wpsimp+
   apply (clarsimp simp: page_directory_pde_at_lookupI less_kernel_base_mapping_slots)
  apply (clarsimp simp: page_directory_pde_at_lookupI' page_directory_at_state_relation)
  done

lemma decodeARMPageFlush_corres:
  "\<lbrakk>invocation_type (mi_label mi) = l; ARM_H.isPageFlushLabel l\<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> archinv_relation)
           (invs and
            valid_cap (cap.ArchObjectCap (arch_cap.PageCap d word seta vmpage_size option)) and
            cte_wp_at
             ((=) (cap.ArchObjectCap (arch_cap.PageCap d word seta vmpage_size option)))
             slot and
            (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
           (invs' and
            valid_cap'
             (capability.ArchObjectCap
               (arch_capability.PageCap d word (vmrights_map seta) vmpage_size option)) and
            (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s) and
            (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
           (if Suc 0 < length args
            then let start = args ! 0; end = args ! 1
                 in doE (asid, vaddr) \<leftarrow>
                        case option of
                        None \<Rightarrow> throwError ExceptionTypes_A.syscall_error.IllegalOperation
                        | Some x \<Rightarrow> returnOk x;
                        pd \<leftarrow> lookup_error_on_failure False $ find_pd_for_asid asid;
                        whenE (end \<le> start) $
                        throwError $ ExceptionTypes_A.syscall_error.InvalidArgument 1;
                        page_size \<leftarrow> returnOk $ 1 << pageBitsForSize vmpage_size;
                        whenE (page_size \<le> start \<or> page_size < end) $
                        throwError $ ExceptionTypes_A.syscall_error.InvalidArgument 0;
                        returnOk $
                        arch_invocation.InvokePage $
                        ARM_A.page_invocation.PageFlush
                         (label_to_flush_type l) (start + vaddr)
                         (end + vaddr - 1) (addrFromPPtr word + start) pd asid
                    odE
            else throwError ExceptionTypes_A.syscall_error.TruncatedMessage)
           (decodeARMPageFlush (mi_label mi) args
             (arch_capability.PageCap d word (vmrights_map seta) vmpage_size option))"
  apply (simp add: decodeARMPageFlush_def split del: if_split)
  apply (cases args, simp)
  apply (rename_tac a0 as)
  apply (case_tac as, simp)
  apply (rename_tac a1 as')
  apply (cases option, simp)
  apply (case_tac a)
  apply (rename_tac asid vref)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule corres_lookup_error)
       apply (rule find_pd_for_asid_corres[OF refl])
      apply (rule whenE_throwError_corres, simp)
       apply simp
      apply (rule whenE_throwError_corres, simp)
       apply simp
      apply (rule corres_trivial)
      apply (rule corres_returnOk)
      apply (clarsimp simp: archinv_relation_def page_invocation_map_def
                            label_to_flush_type_def labelToFlushType_def flush_type_map_def
                            ARM_H.isPageFlushLabel_def
                     split: flush_type.splits invocation_label.splits arch_invocation_label.splits)
     apply wp+
   apply (fastforce simp: valid_cap_def mask_def
                          invs_vspace_objs[simplified])
  apply (auto)
  done

lemma vs_lookup_pages1I:
  "\<lbrakk> ko_at ko p s; (r, p') \<in> vs_refs_pages ko;
          rs' = r # rs \<rbrakk> \<Longrightarrow> ((rs,p) \<unrhd>1 (rs',p')) s"
  by (fastforce simp add: vs_lookup_pages1_def)

lemma vs_refs_pages_ptI:
  "pt x = pte \<Longrightarrow> pte_ref_pages pte = Some r'
    \<Longrightarrow> (VSRef (ucast x) (Some APageTable), r') \<in> vs_refs_pages (ArchObj (PageTable pt))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pt_largeI
    = vs_refs_pages_ptI[where pte="ARM_A.pte.LargePagePTE x y z" for x y z,
        unfolded pte_ref_pages_def, simplified, OF _ refl]

lemmas vs_refs_pages_pt_smallI
    = vs_refs_pages_ptI[where pte="ARM_A.pte.SmallPagePTE x y z" for x y z,
        unfolded pte_ref_pages_def, simplified, OF _ refl]

lemma vs_refs_pages_pdI:
  "pd x = pde \<Longrightarrow> pde_ref_pages pde = Some r'
    \<Longrightarrow> x \<notin> kernel_mapping_slots
    \<Longrightarrow> (VSRef (ucast x) (Some APageDirectory), r') \<in> vs_refs_pages (ArchObj (PageDirectory pd))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pd_sectionI
    = vs_refs_pages_pdI[where pde="ARM_A.pde.SectionPDE x y z w" for x y z w,
        unfolded pde_ref_pages_def, simplified, OF _ refl]

lemmas vs_refs_pages_pd_supersectionI
    = vs_refs_pages_pdI[where pde="ARM_A.pde.SuperSectionPDE x y z" for x y z,
        unfolded pde_ref_pages_def, simplified, OF _ refl]

lemma get_master_pde_sp:
  "\<lbrace> P \<rbrace> get_master_pde pd_slot \<lbrace> \<lambda>pde s. P s
    \<and> (\<exists>pd pd_slot'. ko_at (ArchObj (PageDirectory pd)) (pd_slot && ~~ mask pd_bits) s
        \<and> pd_slot' && ~~ mask pd_bits = pd_slot && ~~ mask pd_bits
        \<and> ((ucast (pd_slot' && mask pd_bits >> 2) \<in> kernel_mapping_slots)
            \<longrightarrow> (ucast (pd_slot && mask pd_bits >> 2) \<in> kernel_mapping_slots))
        \<and> pd (ucast (pd_slot' && mask pd_bits >> 2)) = pde)  \<rbrace>"
  apply (simp add: get_master_pde_def)
  apply (wp get_pde_wp | wpc)+
  apply (clarsimp simp: obj_at_def)
  apply (safe, simp_all add: exI[where x=pd_slot])
  apply (cut_tac max.absorb2[where a=6 and b=pd_bits])
   apply (clarsimp simp: word_bw_assocs neg_mask_combine)
   apply (rule_tac x="pd_slot && ~~ mask 6" in exI)
   apply (simp add: word_bw_assocs neg_mask_combine)
   apply (clarsimp simp: kernel_mapping_slots_def)
   apply (erule order_trans)
   apply (rule ucast_mono_le)
    apply (rule le_shiftr)
    apply (metis word_and_le1 word_bw_assocs(1) word_bw_comms(1))
   apply (rule shiftr_less_t2n)
   apply (rule order_less_le_trans, rule and_mask_less_size)
    apply (simp add: pd_bits_def pageBits_def word_size)
   apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: pd_bits_def pageBits_def)
  done

lemma get_master_pte_wp:
  "\<lbrace> \<lambda>s. (\<forall>pt pt_slot'. ko_at (ArchObj (PageTable pt)) (pt_slot && ~~ mask pt_bits) s
        \<and> pt_slot' && ~~ mask pt_bits = pt_slot && ~~ mask pt_bits
            \<longrightarrow> Q (pt (ucast (pt_slot' && mask pt_bits >> 2))) s)  \<rbrace>
    get_master_pte pt_slot \<lbrace> Q \<rbrace>"
  apply (simp add: get_master_pte_def)
  apply (wp get_pte_wp | wpc)+
  apply clarsimp
  apply (drule spec, drule_tac x="pt_slot && ~~ mask 6" in spec)
  apply (cut_tac max.absorb2[where a=6 and b=pt_bits])
   apply (simp add: word_bw_assocs neg_mask_combine obj_at_def)
   apply fastforce
  apply (simp add: pt_bits_def pageBits_def)
  done

lemma resolve_vaddr_valid_mapping_size:
  "\<lbrace> valid_vs_lookup and pspace_aligned and valid_vspace_objs and page_directory_at pd
                 and (\<exists>\<rhd> (lookup_pd_slot pd vaddr && ~~ mask pd_bits))
                 and valid_objs and K (vaddr < kernel_base) \<rbrace>
    resolve_vaddr pd vaddr \<lbrace> \<lambda>rv s. case rv of None \<Rightarrow> True
    | Some (a, b) \<Rightarrow> \<exists>p cap. caps_of_state s p = Some cap
        \<and> (case cap of cap.ArchObjectCap c \<Rightarrow> is_page_cap c | _ \<Rightarrow> False)
        \<and> cap_bits cap = pageBitsForSize a \<rbrace> "
  apply (simp add: resolve_vaddr_def)
  apply (rule bind_wp[OF _ get_master_pde_sp])
  apply (rule hoare_pre)
   apply (wp get_master_pte_wp | wpc
     | simp add: lookup_pt_slot_no_fail_def)+
  apply (clarsimp simp: obj_at_def)
  apply (frule(1) pspace_alignedD, simp)
  apply (drule_tac y=pd_bits in is_aligned_weaken, simp add: pd_bits_def pageBits_def)
  apply (frule valid_vspace_objsD, simp add: obj_at_def lookup_pd_slot_eq, simp)
  apply (simp add: lookup_pd_slot_eq less_kernel_base_mapping_slots)
  apply (drule bspec, simp)
  apply (rule conjI)
   apply clarsimp
   apply (drule vs_lookup_step)
    apply (rule vs_lookup1I, simp add: obj_at_def)
     apply (erule(1) vs_refs_pdI2)
    apply simp
   apply (drule sym[where s=pd])
   apply (simp add: lookup_pd_slot_eq)
   apply (frule(1) is_aligned_pt)
   apply (frule is_aligned_weaken[where x=pt_bits and y=10])
    apply (simp add: pt_bits_def pageBits_def)
   apply (simp add: vaddr_segment_nonsense3)
   apply (frule valid_vspace_objsD, simp add: obj_at_def, simp)
   apply (drule vs_lookup_pages_vs_lookupI)
   apply (rule conjI)
    apply (clarsimp simp:)
    apply (drule_tac x="ucast (pt_slot' && mask pt_bits >> 2)" in spec)
    apply (drule vs_lookup_pages_step)
     apply (rule vs_lookup_pages1I, simp add: obj_at_def)
      apply (erule vs_refs_pages_pt_largeI)
     apply simp
    apply (drule(1) valid_vs_lookupD)
    apply simp
    apply (erule exEI)+
    apply (clarsimp simp: vs_cap_ref_def split: cap.split_asm arch_cap.split_asm
           option.split_asm vmpage_size.split_asm)
    apply (frule(1) caps_of_state_valid_cap)
    apply (clarsimp simp: valid_cap_def obj_at_def data_at_def a_type_simps
                   split: if_split_asm)
   apply (clarsimp simp: vaddr_segment_nonsense4)
   apply (drule_tac x="ucast (pt_slot' && mask pt_bits >> 2)" in spec)
   apply (drule vs_lookup_pages_step)
    apply (rule vs_lookup_pages1I, simp add: obj_at_def)
     apply (erule vs_refs_pages_pt_smallI)
    apply simp
   apply (drule(1) valid_vs_lookupD)
   apply simp
   apply (erule exEI)+
   apply (clarsimp simp: vs_cap_ref_def split: cap.split_asm arch_cap.split_asm
          option.split_asm vmpage_size.split_asm)
   apply (frule(1) caps_of_state_valid_cap)
   apply (clarsimp simp: valid_cap_def obj_at_def data_at_def a_type_simps
                  split: if_split_asm)
  apply (drule vs_lookup_pages_vs_lookupI)
  apply (rule conjI)
   apply clarsimp
   apply (drule vs_lookup_pages_step)
    apply (rule vs_lookup_pages1I, simp add: obj_at_def)
     apply (erule(1) vs_refs_pages_pd_sectionI)
    apply simp
   apply (drule(1) valid_vs_lookupD)
   apply simp
   apply (erule exEI)+
   apply (clarsimp simp: vs_cap_ref_def split: cap.split_asm arch_cap.split_asm
          option.split_asm vmpage_size.split_asm)
    apply (frule(1) caps_of_state_valid_cap)
    apply (clarsimp simp: valid_cap_def obj_at_def data_at_def a_type_simps
                   split: if_split_asm)
   apply (frule(1) caps_of_state_valid_cap)
   apply (clarsimp simp: valid_cap_def obj_at_def data_at_def a_type_simps
                  split: if_split_asm)
  apply clarsimp
  apply (drule vs_lookup_pages_step)
   apply (rule vs_lookup_pages1I, simp add: obj_at_def)
    apply (erule(1) vs_refs_pages_pd_supersectionI)
   apply simp
  apply (drule(1) valid_vs_lookupD)
  apply simp
  apply (erule exEI)+
  apply (clarsimp simp: vs_cap_ref_def
                 split: cap.split_asm arch_cap.split_asm
                        option.split_asm vmpage_size.split_asm)
   apply (frule(1) caps_of_state_valid_cap)
   apply (clarsimp simp: valid_cap_def obj_at_def data_at_def a_type_simps
                  split: if_split_asm)
  apply (frule(1) caps_of_state_valid_cap)
  apply (clarsimp simp: valid_cap_def obj_at_def data_at_def a_type_simps
                 split: if_split_asm)
  done

lemmas whenE_throwError_corres_terminal =
  whenE_throwError_corres[where m="returnOk ()" and m'="returnOk ()", OF _ _ corres_returnOkTT, simplified]

lemma arch_decodeInvocation_corres:
notes check_vp_inv[wp del] check_vp_wpR[wp]
  (* FIXME: check_vp_inv shadowed check_vp_wpR.  Instead,
     check_vp_wpR should probably be generalised to replace check_vp_inv. *)
shows
  "\<lbrakk> acap_relation arch_cap arch_cap';
     list_all2 cap_relation (map fst excaps) (map fst excaps');
     list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
   corres
   (ser \<oplus> archinv_relation)
   (invs and valid_cap (cap.ArchObjectCap arch_cap) and
        cte_wp_at ((=) (cap.ArchObjectCap arch_cap)) slot and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_at (snd x) s))
   (invs' and valid_cap' (capability.ArchObjectCap arch_cap') and
     (\<lambda>s. \<forall>x\<in>set excaps'. s \<turnstile>' fst x \<and> cte_at' (snd x) s) and
     (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
   (arch_decode_invocation (mi_label mi) args (to_bl cptr') slot
      arch_cap excaps)
   (Arch.decodeInvocation (mi_label mi) args cptr'
     (cte_map slot) arch_cap' excaps')"
  apply (simp add: arch_decode_invocation_def ARM_H.decodeInvocation_def decodeARMMMUInvocation_def
              split del: if_split)
  apply (cases arch_cap)
      apply (simp add: isCap_simps split del: if_split)
      apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel ARMASIDPoolAssign")
       apply (simp split: invocation_label.split arch_invocation_label.split)
      apply (rename_tac word1 word2)
      apply (cases "excaps", simp)
      apply (cases "excaps'", simp)
      apply clarsimp
      apply (case_tac a, simp_all)[1]
      apply (rename_tac arch_capa)
      apply (case_tac arch_capa, simp_all)[1]
      apply (rename_tac word3 option)
      apply (case_tac option, simp_all)[1]
      apply (rule corres_guard_imp)
        apply (rule corres_splitEE)
           apply (rule corres_trivial [where r="ser \<oplus> (\<lambda>p p'. p = p' o ucast)"])
           apply (clarsimp simp: state_relation_def arch_state_relation_def)
          apply (rule whenE_throwError_corres, simp)
            apply (simp add: lookup_failure_map_def)
           apply simp
          apply (rule_tac P="\<lambda>s. asid_table (asid_high_bits_of word2) = Some word1 \<longrightarrow> asid_pool_at word1 s" and
                          P'="pspace_aligned' and pspace_distinct' and pspace_bounded'" in corres_inst)
          apply (simp add: liftME_return)
          apply (rule whenE_throwError_corres_initial, simp)
           apply auto[1]
          apply (rule corres_guard_imp)
            apply (rule corres_splitEE)
               apply simp
               apply (rule get_asid_pool_corres_inv')
              apply (simp add: bindE_assoc)
              apply (rule corres_splitEE)
                 apply (rule corres_whenE)
                   apply (subst conj_assoc [symmetric])
                   apply (subst assocs_empty_dom_comp [symmetric])
                   apply (rule dom_ucast_eq)
                  apply (rule corres_trivial)
                  apply simp
                 apply simp
                apply (rule_tac F="- dom pool \<inter> {x. ucast x + word2 \<noteq> 0} \<noteq> {}" in corres_gen_asm)
                apply (frule dom_hd_assocsD)
                apply (simp add: select_ext_fap[simplified free_asid_pool_select_def]
                                 free_asid_pool_select_def)
                apply (simp add: returnOk_liftE[symmetric])
                apply (rule corres_returnOk)
                apply (simp add: archinv_relation_def asid_pool_invocation_map_def)
               apply (rule hoare_pre, wp whenE_wp)
               apply (clarsimp simp: ucast_fst_hd_assocs)
               apply (wp hoareE_TrueI whenE_wp getASID_wp | simp)+
           apply ((clarsimp simp: p2_low_bits_max | rule TrueI impI)+)[2]
         apply (wp whenE_wp getASID_wp)+
       apply (clarsimp simp: valid_cap_def)
      apply auto[1]
     apply (simp add: isCap_simps split del: if_split)
     apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel ARMASIDControlMakePool")
      apply (simp split: invocation_label.split arch_invocation_label.split)
     apply (subgoal_tac "length excaps' = length excaps")
      prefer 2
      apply (simp add: list_all2_iff)
     apply (cases args, simp)
     apply (rename_tac a0 as)
     apply (case_tac as, simp)
     apply (rename_tac a1 as')
     apply (cases excaps, simp)
     apply (rename_tac excap0 exs)
     apply (case_tac exs)
      apply (auto split: list.split)[1]
     apply (rename_tac excap1 exss)
     apply (case_tac excap0)
     apply (rename_tac c0 slot0)
     apply (case_tac excap1)
     apply (rename_tac c1 slot1)
     apply (clarsimp simp: Let_def split del: if_split)
     apply (cases excaps', simp)
     apply (case_tac list, simp)
     apply (rename_tac c0' exs' c1'  exss')
     apply (clarsimp split del: if_split)
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE[where r'="\<lambda>p p'. p = p' o ucast"])
          apply (rule corres_trivial)
          apply (clarsimp simp: state_relation_def arch_state_relation_def)
         apply (simp only: bindE_assoc)
         apply (rule corres_splitEE)
            apply (rule corres_whenE)
              apply (subst assocs_empty_dom_comp [symmetric])
              apply (simp add: o_def)
              apply (rule dom_ucast_eq_7)
             apply (rule corres_trivial, simp, simp)
           apply (simp split del: if_split)
           apply (rule_tac F="- dom (asidTable \<circ> ucast) \<inter> {x. x \<le> 2 ^ asid_high_bits - 1} \<noteq> {}"
                    in corres_gen_asm)
           apply (drule dom_hd_assocsD)
           apply (simp add: select_ext_fa[simplified free_asid_select_def]
                            free_asid_select_def o_def returnOk_liftE[symmetric]
                 split del: if_split)
           apply (thin_tac "fst a \<notin> b \<and> P" for a b P)
           apply (case_tac "isUntypedCap a \<and> capBlockSize a = objBits (makeObject::asidpool)
                            \<and> \<not> capIsDevice a")
            prefer 2
            apply (rule corres_guard_imp)
              apply (rule corres_trivial)
              apply (case_tac ad, simp_all add: isCap_simps split del: if_split)[1]
               apply (case_tac x21, simp_all split del: if_split)[1]
               apply (clarsimp simp: objBits_simps archObjSize_def
                          split del: if_split)
              apply clarsimp
             apply (rule TrueI)+
           apply (clarsimp simp: isCap_simps cap_relation_Untyped_eq lookupTargetSlot_def
                                 objBits_simps archObjSize_def bindE_assoc split_def)
           apply (rule corres_splitEE)
              apply (fold ser_def)
              apply (rule ensureNoChildren_corres, rule refl)
             apply (rule corres_splitEE)
                apply (erule lookupSlotForCNodeOp_corres, rule refl)
               apply (rule corres_splitEE)
                  apply (rule ensureEmptySlot_corres)
                  apply clarsimp
                 apply (rule corres_returnOk[where P="\<top>"])
                 apply (clarsimp simp add: archinv_relation_def asid_ci_map_def split_def)
                 apply (clarsimp simp add: ucast_assocs[unfolded o_def] split_def
                                           filter_map asid_high_bits_def)
                 apply (simp add: ord_le_eq_trans [OF word_n1_ge])
                apply (wp hoare_drop_imps)+
          apply (simp add: o_def validE_R_def)
          apply (wp whenE_wp)+
      apply fastforce
     apply clarsimp
     apply (simp add: null_def split_def asid_high_bits_def word_le_make_less)
     apply (subst hd_map, assumption)
     \<comment> \<open>need abstract guard to show list nonempty\<close>
     apply (simp add: word_le_make_less)
     apply (subst ucast_ucast_len)
      apply (drule hd_in_set)
      apply simp
     apply fastforce
    apply (simp add: isCap_simps split del: if_split)
    apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageMap")
     apply (rename_tac dev frame_ptr cap_rights vmpage_size map_data)
     apply (case_tac "\<not>(2 < length args \<and> excaps \<noteq> [])", clarsimp split: list.splits)
     apply (simp add: Let_def neq_Nil_conv)
     apply (elim exE conjE)
     apply (rename_tac pd_cap pd_cap_cnode pd_cap_slot excaps_rest)
     apply (clarsimp split: list.split, intro conjI impI allI; clarsimp)
     apply (rename_tac vaddr rights_mask attr pd_cap' excaps'_rest args_rest)
     apply (rule corres_guard_imp)
       apply (rule_tac P="\<nexists>pd asid. pd_cap = cap.ArchObjectCap (arch_cap.PageDirectoryCap pd (Some asid))"
                in corres_symmetric_bool_cases[where Q=\<top> and Q'=\<top>, OF refl])
        apply (case_tac pd_cap; clarsimp; rename_tac pd_acap pd_acap'; case_tac pd_acap; clarsimp)
       apply (rule corres_splitEE[where r'="(=)" and P=\<top> and P'=\<top>])
          apply (clarsimp simp: corres_returnOkTT)
         apply (rule_tac F="pd_cap = cap.ArchObjectCap (arch_cap.PageDirectoryCap (fst rv) (Some (snd rv)))"
                  in corres_gen_asm)
         apply (clarsimp cong: option.case_cong)
         apply (rename_tac vspace asid)
         apply wpfix \<comment> \<open>get asid and vspace parameters in schematic preconditions\<close>
         apply (rule_tac P="map_data = None \<and> kernel_base \<le> vaddr + 2 ^ pageBitsForSize vmpage_size - 1
                            \<or> (\<exists>asid' vaddr'. map_data = Some (asid', vaddr') \<and> (asid',vaddr') \<noteq> (asid,vaddr))"
                  in corres_symmetric_bool_cases[where Q=\<top> and Q'=\<top>, OF refl])
          apply (erule disjE; clarsimp simp: whenE_def kernel_base_def pptrBase_def
                                      split: option.splits)
         apply clarsimp
         apply (rule corres_splitEE[where r'=dc and P=\<top> and P'=\<top>])
            apply (case_tac map_data
                   ; clarsimp simp: whenE_def kernel_base_def pptrBase_def
                                    corres_returnOkTT)
           \<comment> \<open>pd=undefined as vspace_at_asid not used in find_pd_for_asid_corres and avoid unresolved schematics\<close>
           apply (rule corres_splitEE[
                         OF corres_lookup_error[OF find_pd_for_asid_corres[where pd=undefined, OF refl]]])
             apply (rule whenE_throwError_corres; simp)
             apply (rule corres_splitEE[where r'=dc, OF checkVPAlignment_corres])
               apply (rule corres_splitEE[OF createMappingEntries_corres]
                      ; simp add: mask_vmrights_corres vm_attributes_corres)
                 apply (rule corres_splitEE[OF ensureSafeMapping_corres], assumption)
                   apply (rule corres_returnOkTT)
                   \<comment> \<open>program split done, now prove resulting preconditions and Hoare triples\<close>
                   apply (simp add: archinv_relation_def page_invocation_map_def)
                  apply wpsimp+
            apply (wp find_pd_for_asid_pd_at_asid_again)
           apply (wp findPDForASID_pd_at_wp)
          apply wpsimp
         apply wpsimp
        apply wpsimp
       apply wpsimp
      apply (clarsimp simp: cte_wp_at_caps_of_state cong: conj_cong)
      apply (rename_tac pd_ptr asid')
      apply (prop_tac "is_aligned pd_ptr pd_bits")
       apply (clarsimp simp: valid_cap_simps cap_aligned_def pd_bits)
      apply (prop_tac "\<forall>vaddr. lookup_pd_slot pd_ptr vaddr && ~~ mask pd_bits = pd_ptr")
       apply (clarsimp simp: lookup_pd_slot_eq)
      apply (fastforce simp: valid_cap_simps mask_def aligned_sum_less_kernel_base word_not_le
                             vmsz_aligned_def vspace_at_asid_def
                     intro!: page_directory_pde_at_lookupI page_directory_at_aligned_pd_bits)
     apply fastforce

    apply (simp split del: if_split)
    apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageUnmap")
     apply simp
     apply (rule corres_returnOk)
     apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
    apply (cases "ARM_H.isPageFlushLabel (invocation_type (mi_label mi))")
     apply (clarsimp simp: ARM_H.isPageFlushLabel_def split del: if_split)
     apply (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: if_split)
        apply (rule decodeARMPageFlush_corres[simplified];
                clarsimp simp: ARM_H.isPageFlushLabel_def)+
    apply (clarsimp simp: ARM_H.isPageFlushLabel_def split del: if_split)
    apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageGetAddress")
     apply simp
     apply (rule corres_returnOk)
     apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
    subgoal by (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: if_split)
   apply (simp add: isCap_simps split del: if_split)
   apply (simp split: invocation_label.split arch_invocation_label.splits split del: if_split)
   apply (intro conjI impI allI)
    apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
    apply (clarsimp simp: neq_Nil_conv)
    apply (rule whenE_throwError_corres_initial, simp+)
    apply (simp split: cap.split arch_cap.split option.split,
           intro conjI allI impI, simp_all)[1]
    apply (rule whenE_throwError_corres_initial, simp)
     apply (simp add: kernel_base_def pptrBase_def)
    apply (rule corres_guard_imp)
      apply (rule corres_splitEE)
         apply (rule corres_lookup_error)
         apply (rule find_pd_for_asid_corres[OF refl])
        apply (rule whenE_throwError_corres, simp, simp)
        apply (rule corres_splitEE)
           apply (simp add: pageBits_def ptBits_def pdeBits_def)
           apply (rule get_master_pde_corres')
          apply (simp add: unlessE_whenE)
          apply (rule corres_splitEE)
             apply (rule corres_whenE)
               apply clarsimp
               apply (case_tac oldpde, simp_all)[1]
              apply (rule corres_trivial)
              apply simp
             apply simp
            apply (rule corres_trivial)
            apply (rule corres_returnOk)
            apply (clarsimp simp: archinv_relation_def page_table_invocation_map_def)
            apply (clarsimp simp: attribs_from_word_def attribsFromWord_def Let_def)
            apply (simp add: shiftr_shiftl1 pageBits_def ptBits_def pdeBits_def pteBits_def)
           apply (wp whenE_wp get_master_pde_wp getPDE_wp find_pd_for_asid_inv
                  | wp (once) hoare_drop_imps)+
     apply (fastforce simp: valid_cap_def mask_def
                            invs_vspace_objs[simplified])
    apply (clarsimp simp: valid_cap'_def)
    apply fastforce
   apply (clarsimp simp: unlessE_whenE liftE_bindE)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_symb_exec_r_conj)
        apply (rule_tac F="isArchCap isPageTableCap (cteCap cteVal)"
               in corres_gen_asm2)
        apply (rule corres_split[OF isFinalCapability_corres[where ptr=slot]])
          apply (drule mp)
           apply (clarsimp simp: isCap_simps final_matters'_def)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def
                                                page_table_invocation_map_def)
         apply (wp getCTE_wp' | wp (once) hoare_drop_imps)+
      apply (clarsimp)
     apply (rule no_fail_pre, rule no_fail_getCTE)
     apply (erule conjunct2)
    apply (clarsimp simp: cte_wp_at_caps_of_state
                          cap_rights_update_def acap_rights_update_def)
   apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (clarsimp simp: cte_wp_at_ctes_of
                         cap_rights_update_def acap_rights_update_def
                         cte_wp_at_caps_of_state)
   apply (drule pspace_relation_ctes_ofI[OF _ caps_of_state_cteD, rotated],
          erule invs_pspace_aligned', clarsimp+)
   apply (simp add: isCap_simps)
  apply (simp add: isCap_simps split del: if_split)
  apply (cases "ARM_H.isPDFlushLabel (invocation_type (mi_label mi))")
   apply (clarsimp split del: if_split)
   apply (cases args, simp)
   apply (rename_tac a0 as)
   apply (case_tac as, simp)
   apply (rename_tac a1 as')
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule whenE_throwError_corres, simp)
      apply clarsimp
     apply (rule whenE_throwError_corres, simp)
      apply (clarsimp simp: kernel_base_def pptrBase_def)
     apply (rule case_option_corresE)
      apply (rule corres_trivial)
      apply clarsimp
     apply clarsimp
     apply (rule corres_splitEE)
        apply (rule corres_lookup_error)
        apply (rule find_pd_for_asid_corres[OF refl])
       apply (rule whenE_throwError_corres, simp)
        apply clarsimp
       apply (simp add: liftE_bindE)
       apply (rule corres_split[OF _ _ resolve_vaddr_valid_mapping_size])
         apply clarsimp
         apply (rule resolveVAddr_corres[THEN corres_gen_asm])
          apply simp
         apply (clarsimp simp: not_le)
        apply (case_tac rva)
         apply clarsimp
         apply (rule_tac P'="pspace_aligned' and pspace_distinct'
               and valid_global_refs'" in corres_inst[where P="\<top>"])
         apply (rule corres_returnOk)
         apply (clarsimp simp: archinv_relation_def page_directory_invocation_map_def)
        apply (clarsimp simp: Let_def liftE_bindE checkValidMappingSize_def)
        apply (rule corres_stateAssert_implied[where P'="\<top>", simplified])
         apply (rule corres_guard_imp)
           apply (rule whenE_throwError_corres, simp)
            apply clarsimp
           apply (rule corres_trivial)
           apply (rule corres_returnOk)
           apply (clarsimp simp: archinv_relation_def page_directory_invocation_map_def
                                 flush_type_map)+
        apply (clarsimp simp: state_relation_def)
        apply (frule pspace_relation_cte_wp_at,
               simp add: cte_wp_at_caps_of_state, simp+)
        apply (clarsimp simp: cte_wp_at_ctes_of)
        apply (drule(1) valid_global_refsD_with_objSize)
        subgoal by (clarsimp simp: is_page_cap_def split: cap.split_asm)
       apply (wp hoare_drop_imps)+
    apply (clarsimp simp: valid_cap_simps mask_2pm1 linorder_not_le split: option.split)
    apply (intro conjI; (clarsimp)?)
   apply (clarsimp simp: invs'_def valid_pspace'_def
                  split: option.splits)
  apply clarsimp
  done

lemma arch_performInvocation_corres:
  "archinv_relation ai ai' \<Longrightarrow>
   corres (dc \<oplus> (=))
     (einvs and ct_active and valid_arch_inv ai and schact_is_rct)
     (invs' and ct_active' and valid_arch_inv' ai' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
     (arch_perform_invocation ai) (Arch.performInvocation ai')"
  apply add_cur_tcb'
  apply (clarsimp simp: arch_perform_invocation_def
                        ARM_H.performInvocation_def
                        performARMMMUInvocation_def)
  apply (cases ai)
      apply (clarsimp simp: archinv_relation_def)
      apply (rule corres_underlying_split[OF _ corres_return_eq_same[OF refl]])
        apply (erule corres_guard_imp [OF performPageTableInvocation_corres])
         apply (fastforce simp: valid_arch_inv_def)
        apply (fastforce simp: valid_arch_inv'_def)
       apply wp
      apply wp
     apply (clarsimp simp: archinv_relation_def)
     apply (rule corres_underlying_split[OF _ corres_return_eq_same[OF refl]])
       apply (erule corres_guard_imp [OF performPageDirectoryInvocation_corres])
        apply (fastforce simp: valid_arch_inv_def)
       apply (fastforce simp: valid_arch_inv'_def)
      apply wp
     apply wp
    apply (clarsimp simp: archinv_relation_def)
    apply (erule corres_guard_imp [OF performPageInvocation_corres])
     apply (fastforce simp: valid_arch_inv_def)
    apply (fastforce simp: valid_arch_inv'_def)
   apply (clarsimp simp: archinv_relation_def)
   apply (rule corres_underlying_split[OF _ corres_return_eq_same[OF refl]])
     apply (rule corres_guard_imp [OF performASIDControlInvocation_corres], rule refl)
      apply (fastforce simp: valid_arch_inv_def)
     apply (fastforce simp: valid_arch_inv'_def)
    apply wp
   apply wp
  apply (clarsimp simp: archinv_relation_def)
  apply (rule corres_underlying_split[OF _ corres_return_eq_same[OF refl]])
    apply (rule corres_guard_imp [OF performASIDPoolInvocation_corres], rule refl)
     apply (fastforce simp: valid_arch_inv_def)
    apply (fastforce simp: valid_arch_inv'_def)
   apply wp+
  done

lemma asid_pool_typ_at_ext':
  "asid_pool_at' = obj_at' (\<top>::asidpool \<Rightarrow> bool)"
  apply (rule ext)+
  apply (simp add: typ_at_to_obj_at_arches)
  done

lemma st_tcb_strg':
  "st_tcb_at' P p s \<longrightarrow> tcb_at' p s"
  by (auto simp: pred_tcb_at')

lemma performASIDControlInvocation_tcb_at':
  "\<lbrace>st_tcb_at' active' p and invs' and ct_active' and valid_aci' aci\<rbrace>
  performASIDControlInvocation aci
  \<lbrace>\<lambda>y. tcb_at' p\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: performASIDControlInvocation_def split: asidcontrol_invocation.splits)
  apply (clarsimp simp: valid_aci'_def cte_wp_at_ctes_of cong: conj_cong)
  apply (wp hoare_weak_lift_imp  |simp add:placeNewObject_def2)+
      apply (wp createObjects_orig_obj_at2' updateFreeIndex_pspace_no_overlap' getSlotCap_wp hoare_weak_lift_imp)+
   apply (clarsimp simp: projectKO_opts_defs)
   apply (strengthen st_tcb_strg' [where P=\<top>])
   apply (wp deleteObjects_invs_derivatives[where p="makePoolParent aci"]
     hoare_vcg_ex_lift deleteObjects_cte_wp_at'[where d=False]
     deleteObjects_st_tcb_at'[where p="makePoolParent aci"] hoare_weak_lift_imp
     updateFreeIndex_pspace_no_overlap' deleteObject_no_overlap[where d=False])+
  apply (case_tac ctea)
  apply (clarsimp)
  apply (frule ctes_of_valid_cap')
   apply (simp add:invs_valid_objs')+
  apply (clarsimp simp:valid_cap'_def capAligned_def cte_wp_at_ctes_of)
  apply (strengthen refl order_refl
                    pred_tcb'_weakenE[mk_strg I E])
  apply (clarsimp simp: conj_comms invs_valid_pspace' isCap_simps
                        descendants_range'_def2 empty_descendants_range_in')
  apply (frule ctes_of_valid', clarsimp, simp,
    drule capFreeIndex_update_valid_cap'[where fb="2 ^ pageBits", rotated -1],
    simp_all)
   apply (simp add: pageBits_def is_aligned_def minUntypedSizeBits_def)
  apply (simp add: valid_cap_simps' range_cover_def objBits_simps archObjSize_def
                   capAligned_def unat_eq_0 and_mask_eq_iff_shiftr_0[symmetric]
                   word_bw_assocs untypedBits_defs)
  apply clarsimp
  apply (drule(1) cte_cap_in_untyped_range,
    fastforce simp add: cte_wp_at_ctes_of, assumption, simp_all)
   apply (clarsimp simp: invs'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
  apply clarsimp
  done

lemma invokeArch_tcb_at':
  "\<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p\<rbrace>
     Arch.performInvocation ai
   \<lbrace>\<lambda>rv. tcb_at' p\<rbrace>"
  apply (simp add: ARM_H.performInvocation_def performARMMMUInvocation_def)
  apply (cases ai, simp_all)
     apply (wp, clarsimp simp: pred_tcb_at')
    apply (wp, clarsimp simp: pred_tcb_at')
    apply (wp, clarsimp simp: st_tcb_strg'[rule_format])
   apply (wp performASIDControlInvocation_tcb_at', clarsimp simp: valid_arch_inv'_def)
  apply (wp, clarsimp simp: pred_tcb_at')
  done

end

context begin interpretation Arch .

crunch pspace_no_overlap'[wp]: setThreadState "pspace_no_overlap' w s"
  (simp: unless_def wp: crunch_wps)

lemma valid_slots_duplicated_lift':
  assumes ko_wp_at':
    "\<And>P p. \<lbrace>ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p \<rbrace> f \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p\<rbrace>"
  and pt_at:
  "\<And>p. \<lbrace>page_table_at' p \<rbrace> f \<lbrace>\<lambda>rv. page_table_at' p\<rbrace>"
  and pd_at:
  "\<And>p. \<lbrace>page_directory_at' p\<rbrace> f \<lbrace>\<lambda>rv. page_directory_at' p\<rbrace>"
  shows
  "\<lbrace>valid_slots_duplicated' x\<rbrace> f \<lbrace>\<lambda>r. valid_slots_duplicated' x\<rbrace>"
  apply (simp add:valid_slots_duplicated'_def)
  apply (case_tac x)
   apply (case_tac a)
    apply (case_tac aa)
     apply simp_all
      apply (rule hoare_pre)
      apply simp
      apply (wp hoare_vcg_ex_lift ko_wp_at' pt_at pd_at | simp)+
  apply (case_tac b)
   apply (case_tac a)
      apply (wp hoare_vcg_ex_lift ko_wp_at' pt_at pd_at | simp)+
  done

lemma setTCB_pdpt_bits'[wp]:
 "\<lbrace>\<lambda>s. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p s\<rbrace>
   setObject a (tcb::tcb)
  \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = tcb,simplified])
  apply (clarsimp simp:ko_wp_at'_def)
  apply (intro conjI)
   subgoal by (clarsimp simp:updateObject_default_def assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def typeError_def objBits_simps
    vs_entry_align_def
    split:if_splits option.splits Structures_H.kernel_object.splits,
    ((erule(1) ps_clear_updE)+))
  apply (clarsimp)
  apply (erule(1) ps_clear_updE)
  done

crunch
  threadSet
  for vs_entry_align'[wp]: "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (wp: crunch_wps)

crunch
  addToBitmap
  for vs_entry_align'[wp]: "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (wp: crunch_wps)

lemma tcbSchedEnqueue_vs_entry_align[wp]:
 "\<lbrace>\<lambda>s. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p s\<rbrace>
   tcbSchedEnqueue pa
  \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def tcbQueuePrepend_def setQueue_def)
  by (wp unless_wp | simp)+

crunch
  setThreadState
  for vs_entry_align[wp]: "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (wp: crunch_wps)

crunches setThreadState
  for sc_at'_n[wp]: "sc_at'_n n p"
  (simp: crunch_simps wp: crunch_wps)

lemma sts_valid_arch_inv':
  "\<lbrace>valid_arch_inv' ai\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_arch_inv' ai\<rbrace>"
  apply (cases ai, simp_all add: valid_arch_inv'_def)
      apply (clarsimp simp: valid_pti'_def split: page_table_invocation.splits)
      apply (intro allI conjI impI)
       apply (wp | simp)+
    apply (rename_tac page_invocation)
    apply (case_tac page_invocation, simp_all add: valid_page_inv'_def)[1]
        apply (wp valid_slots_lift' valid_slots_duplicated_lift'|simp)+
   apply (clarsimp simp: valid_aci'_def split: asidcontrol_invocation.splits)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (rule hoare_pre, wp)
  apply clarsimp
  apply (clarsimp simp: valid_apinv'_def split: asidpool_invocation.splits)
  apply (rule hoare_pre, wp)
  apply (simp add: o_def)
  done

lemma less_pptrBase_valid_pde_offset':
  "\<lbrakk> vptr < pptrBase; x = 0 \<or> is_aligned vptr 24; x \<le> 0xF \<rbrakk>
     \<Longrightarrow> valid_pde_mapping_offset' (((x * 4) + (vptr >> 20 << 2)) && mask pdBits)"
  apply (clarsimp simp: pptrBase_def pdBits_def pageBits_def
                        valid_pde_mapping_offset'_def pd_asid_slot_def)
  apply (drule word_le_minus_one_leq, simp add: pdeBits_def)
  apply (drule le_shiftr[where u=vptr and n=20])
  apply (subst(asm) iffD2[OF mask_eq_iff_w2p])
    apply (simp add: word_size)
   apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem])
  apply (erule disjE)
   apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem])
  apply (frule arg_cong[where f="\<lambda>v. v && mask 6"])
  apply (subst(asm) field_simps, subst(asm) is_aligned_add_helper[where n=6],
         rule is_aligned_shiftl)
    apply (rule is_aligned_shiftr, simp)
   apply (simp add: unat_arith_simps iffD1[OF unat_mult_lem])
  apply (simp add: mask_def[where n=6])
  apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem])
  done

lemmas less_pptrBase_valid_pde_offset''
    = less_pptrBase_valid_pde_offset'[where x=0, simplified]

lemma createMappingEntries_valid_pde_slots':
  "\<lbrace>K (vmsz_aligned vptr sz \<and> is_aligned pd pdBits
                \<and> vptr < pptrBase)\<rbrace>
     createMappingEntries base vptr sz vm_rights attrib pd
   \<lbrace>\<lambda>rv s. valid_pde_slots' rv\<rbrace>,-"
  apply (simp add: createMappingEntries_def valid_pde_slots'_def)
  apply (cases sz, simp_all)
     apply (wp | simp)+
   apply (clarsimp simp: lookup_pd_slot_def Let_def mask_add_aligned)
   apply (erule less_pptrBase_valid_pde_offset'')
  apply (rule hoare_pre, wp)
  apply (clarsimp simp: vmsz_aligned_def superSectionPDEOffsets_def pdeBits_def del: ballI)
  apply (subst p_0x3C_shift[symmetric])
   apply (simp add: lookup_pd_slot_def Let_def)
   apply (erule aligned_add_aligned)
     apply (rule is_aligned_shiftl, rule is_aligned_shiftr)
     apply simp
    apply (simp add: pdBits_def pageBits_def word_bits_def)
   apply (simp add: pdBits_def pageBits_def)
  apply (clarsimp simp: upto_enum_step_def linorder_not_less pd_bits_def
                        lookup_pd_slot_def Let_def field_simps
                        mask_add_aligned pdeBits_def take_bit_Suc)
  apply (erule less_pptrBase_valid_pde_offset'
    [unfolded pdBits_def pageBits_def pdeBits_def, simplified], simp+)
  done

lemma inv_ASIDPool: "inv ASIDPool = (\<lambda>v. case v of ASIDPool a \<Rightarrow> a)"
  apply (rule ext)
  apply (case_tac v)
  apply simp
  apply (rule inv_f_f, rule inj_onI)
  apply simp
  done

lemma findPDForASID_aligned[wp]:
  "\<lbrace>valid_objs'\<rbrace> findPDForASID p \<lbrace>\<lambda>rv s. is_aligned rv pdBits\<rbrace>,-"
  apply (simp add: findPDForASID_def assertE_def cong: option.case_cong
                      split del: if_split)
  apply (rule hoare_pre)
   apply (wp getASID_wp | wpc)+
  apply clarsimp
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: projectKOs valid_obj'_def inv_ASIDPool ranI
                 split: asidpool.split_asm)
  done

lemma findPDForASID_valid_offset'[wp]:
  "\<lbrace>valid_objs' and K (vptr < pptrBase)\<rbrace> findPDForASID p
   \<lbrace>\<lambda>rv s. valid_pde_mapping_offset' (rv + (vptr >> 20 << 2) && mask pdBits)\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_strengthen_postE_R, rule findPDForASID_aligned)
  apply (simp add: mask_add_aligned)
  apply (erule less_pptrBase_valid_pde_offset'')
  done

lemma eq_arch_update':
  "ArchObjectCap cp = cteCap cte \<Longrightarrow> is_arch_update' (ArchObjectCap cp) cte"
  by (clarsimp simp: is_arch_update'_def isCap_simps)

lemma lookupPTSlot_page_table_at':
  "\<lbrace>valid_objs'\<rbrace> lookupPTSlot pd vptr
  \<lbrace>\<lambda>rv s. page_table_at' (rv && ~~ mask ptBits) s\<rbrace>,-"
  apply (simp add:lookupPTSlot_def)
  apply (wp getPDE_wp|wpc|simp add:checkPTAt_def)+
  apply (clarsimp simp:ptBits_def lookup_pt_slot_no_fail_def pteBits_def)
  apply (subst vaddr_segment_nonsense3[unfolded pt_bits_def pageBits_def,simplified])
   apply (simp add:page_table_at'_def ptBits_def pageBits_def pteBits_def)
  apply simp
  done

lemma findPDForASID_page_directory_at':
  notes checkPDAt_inv[wp del]
  shows "\<lbrace>\<top>\<rbrace> findPDForASID asiv
    \<lbrace>\<lambda>rv s. page_directory_at' (lookup_pd_slot rv vptr && ~~ mask pdBits) s\<rbrace>,-"
  apply (simp add:findPDForASID_def)
   apply (wp getASID_wp|simp add:checkPDAt_def | wpc)+
  apply (clarsimp simp:lookup_pd_slot_def pdBits_def pdeBits_def)
  apply (subst vaddr_segment_nonsense[unfolded pd_bits_def pdeBits_def pageBits_def,simplified])
   apply (simp add:page_directory_at'_def pdBits_def pageBits_def pdeBits_def)
  apply simp
  done

definition "slots_duplicated_ensured \<equiv> \<lambda>m s. case m of
  Inl (pte, xs) \<Rightarrow> (case pte of
    pte.LargePagePTE _ _ _ _ _ \<Rightarrow> \<exists>p. xs = [p, p+4 .e. p + mask 6] \<and> is_aligned p 6
        \<and> page_table_at' (p && ~~ mask ptBits) s
    | pte.InvalidPTE  \<Rightarrow> False
    | _ \<Rightarrow> \<exists>p. xs = [p]
      \<and> page_table_at' (p && ~~ mask ptBits) s)
  | Inr (pde, xs) \<Rightarrow> (case pde of
    pde.SuperSectionPDE _ _ _ _ _ _ \<Rightarrow> \<exists>p. xs = [p, p+4 .e. p + mask 6] \<and> is_aligned p 6
        \<and> page_directory_at' (p && ~~ mask pdBits) s \<and> is_aligned p 6
    | pde.InvalidPDE  \<Rightarrow> False
    | _ \<Rightarrow> \<exists>p. xs = [p]
      \<and> page_directory_at' (p && ~~ mask pdBits) s)"


lemma ensureSafeMapping_valid_slots_duplicated':
  "\<lbrace>\<lambda>s. slots_duplicated_ensured entries s\<rbrace>
  ensureSafeMapping entries
  \<lbrace>\<lambda>rv s. valid_slots_duplicated' entries s\<rbrace>,-"
  apply (simp add:ensureSafeMapping_def)
  apply (case_tac entries)
   apply (case_tac a)
   apply (case_tac aa)
     apply (rule hoare_pre)
      apply (simp add:slots_duplicated_ensured_def | wp)+
    apply (rule hoare_pre)
     apply (wp mapME_x_inv_wp getPTE_wp| wpc)+
     apply clarsimp
    apply (clarsimp simp:valid_slots_duplicated'_def)
   apply (simp add:slots_duplicated_ensured_def)
   apply (rule hoare_pre)
    apply (rule_tac P = "\<exists>p. b = [p]" and
      P' = "\<lambda>s. \<exists>p. b = [p] \<and> page_table_at' (p && ~~ mask ptBits) s" in hoare_gen_asmE)
    apply (clarsimp simp:mapME_singleton)
    apply (wp getPTE_wp|wpc)+
    apply (clarsimp simp:valid_slots_duplicated'_def obj_at'_real_def split:option.splits)
    apply (intro impI conjI)
     apply (erule ko_wp_at'_weakenE)
     apply (simp add:projectKO_opt_pte vs_entry_align_def
       split:Structures_H.kernel_object.splits
       arch_kernel_object.splits)
    apply (erule ko_wp_at'_weakenE)
    apply (simp add:projectKO_opt_pte vs_entry_align_def
      split:Structures_H.kernel_object.splits
      arch_kernel_object.splits)
   apply clarsimp
  apply (case_tac b)
  apply (case_tac a)
    apply (rule hoare_pre)
    apply (simp add:slots_duplicated_ensured_def | wp)+
   apply (rule hoare_pre)
    apply (rule_tac P = "\<exists>p. ba = [p]" and
      P' = "\<lambda>s. \<exists>p. ba = [p] \<and> page_directory_at' (p && ~~ mask pdBits) s" in hoare_gen_asmE)
    apply (clarsimp simp:mapME_singleton)
    apply (wp getPDE_wp|wpc)+
    apply (clarsimp simp:valid_slots_duplicated'_def obj_at'_real_def split:option.splits)
    apply (intro impI conjI)
     apply (erule ko_wp_at'_weakenE)
     apply (simp add:projectKO_opt_pde vs_entry_align_def
       split:Structures_H.kernel_object.splits
       arch_kernel_object.splits)
    apply (erule ko_wp_at'_weakenE)
    apply (simp add:projectKO_opt_pde vs_entry_align_def
      split:Structures_H.kernel_object.splits
      arch_kernel_object.splits)
   apply clarsimp
  apply (simp add:slots_duplicated_ensured_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp getPDE_wp| wpc)+
   apply clarsimp
  apply (fastforce simp:valid_slots_duplicated'_def)
  done

(* FIXME: this lemma is too specific *)
lemma lookupPTSlot_aligned:
  "\<lbrace>\<lambda>s. is_aligned vptr 16 \<and> valid_objs' s\<rbrace> lookupPTSlot pd vptr \<lbrace>\<lambda>p s. is_aligned p 6\<rbrace>,-"
  apply (simp add:lookupPTSlot_def)
  apply (wp getPDE_wp |wpc|simp)+
  apply (clarsimp simp:obj_at'_real_def ko_wp_at'_def)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp:projectKO_opt_pde
    split:Structures_H.kernel_object.splits arch_kernel_object.splits)
  apply (simp add:valid_obj'_def lookup_pt_slot_no_fail_def)
  apply (rule aligned_add_aligned)
    apply (erule is_aligned_ptrFromPAddr_n)
    apply (simp add: ptBits_def pteBits_def)
   apply (rule is_aligned_shiftl,simp)
   apply (rule is_aligned_andI1)
   apply (rule is_aligned_shiftr)
   apply simp
  apply (simp add: ptBits_def)
  done

lemma createMappingEntires_valid_slots_duplicated'[wp]:
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s) \<and> vmsz_aligned vptr vmsz \<and> valid_objs' s
   \<and>  page_directory_at' (lookup_pd_slot pd vptr && ~~ mask pdBits) s \<and> is_aligned pd pdBits\<rbrace>
  createMappingEntries base vptr vmsz vmrights attrib pd
  \<lbrace>\<lambda>rv s. slots_duplicated_ensured rv s\<rbrace>, -"
  apply (clarsimp simp:createMappingEntries_def)
  apply (rule hoare_pre)
   apply (wpc | wp lookupPTSlot_page_table_at'
          | simp add: slots_duplicated_ensured_def)+
     apply (rule_tac Q' = "\<lambda>p s. is_aligned p 6 \<and> page_table_at' (p && ~~ mask ptBits) s"
                  in hoare_strengthen_postE_R)
      apply (wp lookupPTSlot_aligned lookupPTSlot_page_table_at')
     apply (rename_tac rv s)
     apply (rule_tac x = rv in exI)
     apply (clarsimp simp: largePagePTEOffsets_def pteBits_def)
     apply (frule is_aligned_no_wrap'[where off = "0x3c"])
      apply simp
     apply (drule upto_enum_step_shift[where n = 6 and m = 2,simplified])
     apply (clarsimp simp: mask_def add.commute upto_enum_step_def take_bit_Suc)
    apply simp
    apply wp+
  apply (intro conjI impI; clarsimp)
    apply ((clarsimp simp: vmsz_aligned_def slots_duplicated_ensured_def)+)[2]
  apply (drule lookup_pd_slot_aligned_6)
   apply (simp add: pdBits_def pageBits_def pdeBits_def)
  apply (clarsimp simp: slots_duplicated_ensured_def)
  apply (rule_tac x = "(lookup_pd_slot pd vptr)" in exI)
  apply clarsimp
  apply (frule is_aligned_no_wrap'[where off = "0x3c" and sz = 6])
   apply simp
  apply (drule upto_enum_step_shift[where n = 6 and m = 2,simplified])
  apply (clarsimp simp: mask_def add.commute upto_enum_step_def take_bit_Suc
                        superSectionPDEOffsets_def pdeBits_def)
  done

lemma arch_decodeARMPageFlush_wf:
  "ARM_H.isPageFlushLabel (invocation_type label) \<Longrightarrow>
       \<lbrace>invs' and
        valid_cap'
         (capability.ArchObjectCap (arch_capability.PageCap d word vmrights vmpage_size option)) and
        cte_wp_at'
         ((=) (capability.ArchObjectCap (arch_capability.PageCap d word vmrights vmpage_size option)) \<circ>
          cteCap)
         slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple and
        (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
       decodeARMPageFlush label args (arch_capability.PageCap d word vmrights vmpage_size option)
       \<lbrace>valid_arch_inv'\<rbrace>, -"
  apply (simp add: decodeARMPageFlush_def)
  apply (rule hoare_pre)
   apply (wp throwE_R whenE_throwError_wp | wpc | clarsimp simp: if_apply_def2)+
   apply (wpsimp simp: valid_arch_inv'_def valid_page_inv'_def)
  apply fastforce
  done

lemma arch_decodeInvocation_wf[wp]:
  notes ensureSafeMapping_inv[wp del]
  shows "\<lbrace>invs' and valid_cap' (ArchObjectCap arch_cap) and
    cte_wp_at' ((=) (ArchObjectCap arch_cap) o cteCap) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' ((=) (fst x) o cteCap) (snd x) s) and
    sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
   Arch.decodeInvocation label args cap_index slot arch_cap excaps
   \<lbrace>valid_arch_inv'\<rbrace>,-"
  apply (cases arch_cap)
      apply (simp add: decodeARMMMUInvocation_def ARM_H.decodeInvocation_def
                       Let_def split_def isCap_simps
                 cong: if_cong split del: if_split)
      apply (rule hoare_pre)
       apply ((wp whenE_throwError_wp getASID_wp
               | wpc | simp add: valid_arch_inv'_def valid_apinv'_def)+)[1]
      apply (clarsimp simp: word_neq_0_conv valid_cap'_def valid_arch_inv'_def valid_apinv'_def)
      apply (rule conjI)
       apply (erule cte_wp_at_weakenE')
       apply (simp, drule_tac t="cteCap c" in sym, simp)
      apply (subst (asm) conj_assoc [symmetric])
      apply (subst (asm) assocs_empty_dom_comp [symmetric])
      apply (drule dom_hd_assocsD)
      apply (simp add: capAligned_def)
      apply (elim conjE)
      apply (subst field_simps, erule is_aligned_add_less_t2n)
        apply assumption
       apply (simp add: asid_low_bits_def asid_bits_def)
      apply assumption
     \<comment> \<open>ASIDControlCap\<close>
     apply (simp add: decodeARMMMUInvocation_def ARM_H.decodeInvocation_def
                      Let_def split_def isCap_simps
                cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong
                      list.case_cong prod.case_cong
           split del: if_split)
     apply (rule hoare_pre)
      apply ((wp whenE_throwError_wp ensureEmptySlot_stronger
              | wpc
              | simp add: valid_arch_inv'_def valid_aci'_def is_aligned_shiftl_self
               split del: if_split)+)[1]
          apply (rule_tac Q'=
                      "\<lambda>rv. K (fst (hd [p\<leftarrow>assocs asidTable . fst p \<le> 2 ^ asid_high_bits - 1 \<and> snd p = None])
                               << asid_low_bits \<le> 2 ^ asid_bits - 1) and
                            real_cte_at' rv and
                            ex_cte_cap_to' rv and
                            cte_wp_at' (\<lambda>cte. \<exists>idx. cteCap cte = (UntypedCap False frame pageBits idx))
                                       (snd (excaps!0)) and
                            sch_act_simple and
                            (\<lambda>s. descendants_of' (snd (excaps!0)) (ctes_of s) = {}) "
                            in hoare_strengthen_postE_R)
           apply (simp add: lookupTargetSlot_def)
           apply wp
          apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (simp split del: if_split)
         apply (wp ensureNoChildren_sp whenE_throwError_wp|wpc)+
     apply clarsimp
     apply (rule conjI)
      apply (clarsimp simp: null_def neq_Nil_conv)
      apply (drule filter_eq_ConsD)
      apply clarsimp
      apply (rule shiftl_less_t2n)
       apply (simp add: asid_bits_def asid_low_bits_def asid_high_bits_def)
       apply unat_arith
      apply (simp add: asid_bits_def)
     apply clarsimp
     apply (rule conjI, fastforce)
     apply (clarsimp simp: cte_wp_at_ctes_of objBits_simps archObjSize_def)
     apply (rule conjI)
      apply (case_tac cteb; clarsimp)
      apply (drule ctes_of_valid_cap', fastforce)
      apply assumption
     apply (simp add: ex_cte_cap_to'_def cte_wp_at_ctes_of)
     apply (drule_tac t="cteCap ctea" in sym, simp)
     apply (drule_tac t="cteCap cte" in sym, clarsimp)
     apply (rule_tac x=ba in exI)
     apply simp
    \<comment> \<open>PageCap\<close>
    apply (simp add: decodeARMMMUInvocation_def ARM_H.decodeInvocation_def
                       Let_def split_def isCap_simps
                cong: if_cong split del: if_split)
    apply (cases "invocation_type label = ArchInvocationLabel ARMPageMap")
     apply (rename_tac word vmrights vmpage_size option)
     apply (simp add: split_def split del: if_split
                cong: list.case_cong prod.case_cong)
     apply (rule hoare_pre)
      apply (wpsimp simp: valid_arch_inv'_def valid_page_inv'_def)
            apply (rule hoare_vcg_conj_lift_R,(wp ensureSafeMapping_inv)[1])+
            apply (wpsimp wp: whenE_throwError_wp checkVP_wpR hoare_vcg_const_imp_lift_R
                              ensureSafeMapping_valid_slots_duplicated'
                              createMappingEntries_valid_pde_slots' findPDForASID_page_directory_at'
                        simp: valid_arch_inv'_def valid_page_inv'_def)+
        apply (rule hoare_drop_impE_R)
        apply (wpsimp wp: whenE_throwError_wp checkVP_wpR hoare_vcg_const_imp_lift_R
                          ensureSafeMapping_valid_slots_duplicated'
                          createMappingEntries_valid_pde_slots' findPDForASID_page_directory_at'
                    simp: valid_arch_inv'_def valid_page_inv'_def)+
     apply (clarsimp simp: neq_Nil_conv invs_valid_objs' linorder_not_le
                           cte_wp_at_ctes_of)
     apply (drule ctes_of_valid', fastforce)+
     apply (case_tac option; clarsimp, drule_tac t="cteCap cte" in sym, simp)
      apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def
                            is_arch_update'_def isCap_simps capAligned_def vmsz_aligned_def
                      cong: conj_cong)
      apply (rule conjI)
       apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size; simp)
      apply (rule conjI)
       apply (erule order_le_less_trans[rotated])
       apply (erule is_aligned_no_overflow'[simplified field_simps])
      apply (clarsimp simp: page_directory_at'_def pdBits_eq lookup_pd_slot_eq)+
     apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def
                           is_arch_update'_def isCap_simps capAligned_def vmsz_aligned_def
                     cong: conj_cong)
     apply (rule conjI)
      apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size, simp_all)[1]
     apply (simp add: vmsz_aligned_def pd_bits)
     apply (clarsimp simp: page_directory_at'_def lookup_pd_slot_eq[simplified pd_bits])
    apply (cases "invocation_type label = ArchInvocationLabel ARMPageUnmap")
     apply (simp split del: if_split)
     apply (rule hoare_pre, wp)
     apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
     apply (thin_tac "Ball S P" for S P)
     apply (erule cte_wp_at_weakenE')
     apply (clarsimp simp: is_arch_update'_def isCap_simps)
    apply (cases "ARM_H.isPageFlushLabel (invocation_type label)")
     apply (clarsimp simp: ARM_H.isPageFlushLabel_def
                    split: invocation_label.splits arch_invocation_label.splits)
        apply (rule arch_decodeARMPageFlush_wf,
               clarsimp simp: ARM_H.isPageFlushLabel_def)+
    apply (cases "invocation_type label = ArchInvocationLabel ARMPageGetAddress")
     apply (simp split del: if_split)
     apply (rule hoare_pre, wp)
     apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
    apply (simp add: ARM_H.isPageFlushLabel_def throwError_R'
              split: invocation_label.split_asm arch_invocation_label.split_asm)
   \<comment> \<open>PageTableCap\<close>
   apply (simp add: decodeARMMMUInvocation_def ARM_H.decodeInvocation_def
                    Let_def split_def isCap_simps vs_entry_align_def
              cong: if_cong list.case_cong invocation_label.case_cong
                    arch_invocation_label.case_cong prod.case_cong
         split del: if_split)
   apply (rename_tac word option)
   apply (rule hoare_pre)
    apply ((wp whenE_throwError_wp isFinalCapability_inv getPDE_wp
            | wpc | simp add: valid_arch_inv'_def valid_pti'_def unlessE_whenE
            | rule_tac x="fst p" in hoare_imp_eq_substR)+)
                  apply (rule_tac Q'=
"\<lambda>b c. ko_at' ARM_H.pde.InvalidPDE (b + (hd args >> 20 << 2)) c \<longrightarrow>
         cte_wp_at'
          (is_arch_update'
            (capability.ArchObjectCap
              (arch_capability.PageTableCap word (Some (snd p, hd args >> 20 << 20)))))
          slot c \<and>
         c \<turnstile>' capability.ArchObjectCap
                (arch_capability.PageTableCap word (Some (snd p, hd args >> 20 << 20))) \<and>
         is_aligned (addrFromPPtr word) ptBits \<and>
         valid_pde_mapping_offset' (b + (hd args >> 20 << 2) && mask pdBits)
        " in hoare_strengthen_postE_R)
                   apply ((wp whenE_throwError_wp isFinalCapability_inv getPDE_wp
                           | wpc | simp add: valid_arch_inv'_def valid_pti'_def unlessE_whenE
                           | rule_tac x="fst p" in hoare_imp_eq_substR
                           | rule hoare_drop_impE_R)+)
                  apply (clarsimp simp: ko_wp_at'_def obj_at'_real_def)
                  apply (clarsimp simp: projectKO_opt_pde vs_entry_align_def
                                        pageBits_def ptBits_def pdeBits_def pteBits_def
                                 split: Structures_H.kernel_object.splits arch_kernel_object.splits)
                 apply ((wp whenE_throwError_wp isFinalCapability_inv
                         | wpc | simp add: valid_arch_inv'_def valid_pti'_def if_apply_def2
                         | rule hoare_drop_imp)+)[15]
   apply (clarsimp simp: linorder_not_le isCap_simps cte_wp_at_ctes_of)
   apply (frule eq_arch_update')
   apply (case_tac option; clarsimp)
   apply (drule_tac t="cteCap ctea" in sym, simp)
   apply (clarsimp simp: is_arch_update'_def isCap_simps valid_cap'_def capAligned_def)
   apply (thin_tac "Ball S P" for S P)+
   apply (drule ctes_of_valid', fastforce)+
   apply (clarsimp simp: valid_cap'_def ptBits_def is_aligned_addrFromPPtr_n invs_valid_objs'
                         and_not_mask[symmetric] pteBits_def)
   apply (erule order_le_less_trans[rotated])
   apply (rule word_and_le2)
  apply (simp add: valid_cap'_def capAligned_def)
  apply (simp add: decodeARMMMUInvocation_def ARM_H.decodeInvocation_def isCap_simps Let_def)
  apply (cases "ARM_H.isPDFlushLabel (invocation_type label)"; simp)
   apply (cases args; wpsimp simp: valid_arch_inv'_def)
  apply wp
  done

crunch setMRs
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
    (ignore: getRestartPC setRegister transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option
        mapM_wp'
   simp: split_def zipWithM_x_mapM)

crunch performARMMMUInvocation
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_cte_inv getASID_wp)

lemmas setObject_cte_st_tcb_at' [wp] = setCTE_pred_tcb_at' [unfolded setCTE_def]

crunch performPageDirectoryInvocation, performPageTableInvocation, performPageInvocation,
            performASIDPoolInvocation
  for st_tcb_at': "st_tcb_at' P t"
  (wp: crunch_wps getASID_wp getObject_cte_inv simp: crunch_simps)

lemmas arch_finalise_cap_aligned' = finaliseCap_aligned'

lemmas arch_finalise_cap_distinct' = finaliseCap_distinct'

crunch "Arch.finaliseCap"
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  (wp: crunch_wps getASID_wp simp: crunch_simps)

lemma invs_asid_table_strengthen':
  "invs' s \<and> asid_pool_at' ap s \<and> asid \<le> 2 ^ asid_high_bits - 1 \<longrightarrow>
   invs' (s\<lparr>ksArchState :=
            armKSASIDTable_update (\<lambda>_. ((armKSASIDTable \<circ> ksArchState) s)(asid \<mapsto> ap)) (ksArchState s)\<rparr>)"
  apply (clarsimp simp: invs'_def valid_dom_schedule'_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_global_refs'_def global_refs'_def)
  apply (clarsimp simp: valid_arch_state'_def)
  apply (clarsimp simp: valid_asid_table'_def ran_def)
  apply (rule conjI)
   apply (clarsimp split: if_split_asm)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: valid_pspace'_def)
  apply (simp add: valid_machine_state'_def)
  done

lemma ex_cte_not_in_untyped_range:
  "\<lbrakk>(ctes_of s) cref = Some (CTE (capability.UntypedCap d ptr bits idx) mnode);
    descendants_of' cref (ctes_of s) = {}; invs' s;
    ex_cte_cap_wp_to' (\<lambda>_. True) x s; valid_global_refs' s\<rbrakk>
   \<Longrightarrow> x \<notin> {ptr .. ptr + 2 ^ bits - 1}"
  apply clarsimp
  apply (drule(1) cte_cap_in_untyped_range)
   apply (fastforce simp:cte_wp_at_ctes_of)+
  done

lemma performASIDControlInvocation_invs' [wp]:
  "\<lbrace>invs' and ct_active' and valid_aci' aci\<rbrace>
  performASIDControlInvocation aci \<lbrace>\<lambda>y. invs'\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: performASIDControlInvocation_def valid_aci'_def
    placeNewObject_def2 cte_wp_at_ctes_of
    split: asidcontrol_invocation.splits)
  apply (rename_tac w1 w2 w3 w4 cte ctea idx)
  apply (case_tac ctea)
  apply (clarsimp)
  apply (frule ctes_of_valid_cap')
   apply fastforce
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift)
       apply (strengthen invs_asid_table_strengthen')
       apply (wp cteInsert_simple_invs)
      apply (wp createObjects'_wp_subst[OF
                createObjects_no_cte_invs [where sz = pageBits and ty="Inl (KOArch (KOASIDPool pool))" for pool]]
                createObjects_orig_cte_wp_at'[where sz = pageBits]  hoare_vcg_const_imp_lift
         |simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def cong: rev_conj_cong
         |strengthen safe_parent_strg'[where idx= "2^ pageBits"])+
      apply (rule hoare_vcg_conj_lift)
       apply (rule descendants_of'_helper)
       apply (wp createObjects_null_filter'
                  [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))" for ap]
                 createObjects_valid_pspace'
                  [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))" for ap]
          | simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def
                cong: rev_conj_cong)+
       apply (simp add: objBits_simps archObjSize_def valid_cap'_def capAligned_def range_cover_full)
      apply (wp  createObjects'_wp_subst[OF createObjects_ex_cte_cap_to[where sz = pageBits]]
                 createObjects_orig_cte_wp_at'[where sz = pageBits]
                 hoare_vcg_const_imp_lift
         |simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def cong: rev_conj_cong
         |strengthen safe_parent_strg'[where idx = "2^ pageBits"])+
     apply (simp add:asid_pool_typ_at_ext'[symmetric])
     apply (wp createObject_typ_at')
    apply (simp add: objBits_simps archObjSize_def valid_cap'_def
         capAligned_def range_cover_full makeObjectKO_def
         projectKOs asid_pool_typ_at_ext'
         cong: rev_conj_cong)
    apply (clarsimp simp:conj_comms
                         descendants_of_null_filter'
      | strengthen invs_pspace_aligned' invs_pspace_distinct' invs_pspace_bounded'
          invs_pspace_aligned' invs_valid_pspace')+
    apply (wp updateFreeIndex_forward_invs'
           updateFreeIndex_cte_wp_at
           updateFreeIndex_pspace_no_overlap'
           updateFreeIndex_caps_no_overlap''
           updateFreeIndex_descendants_of2
           updateFreeIndex_caps_overlap_reserved
           updateCap_cte_wp_at_cases hoare_weak_lift_imp
           getSlotCap_wp)+
  apply (clarsimp simp:conj_comms ex_disj_distrib is_aligned_mask
           | strengthen invs_valid_pspace' invs_pspace_aligned' invs_pspace_bounded'
                        invs_pspace_distinct' empty_descendants_range_in')+
  apply (wp deleteObjects_invs'[where p="makePoolParent aci"]
            hoare_vcg_ex_lift
            deleteObjects_caps_no_overlap''[where slot="makePoolParent aci"]
            deleteObject_no_overlap
            deleteObjects_cap_to'[where p="makePoolParent aci"]
            deleteObjects_ct_active'[where cref="makePoolParent aci"]
            deleteObjects_descendants[where p="makePoolParent aci"]
            deleteObjects_cte_wp_at'
            deleteObjects_null_filter[where p="makePoolParent aci"])
  apply (frule valid_capAligned)
  apply (clarsimp simp: invs_mdb' invs_valid_pspace' capAligned_def
                        cte_wp_at_ctes_of is_simple_cap'_def isCap_simps)
  apply (strengthen refl ctes_of_valid_cap'[mk_strg I E])
  apply (clarsimp simp: conj_comms invs_valid_objs')
  apply (frule_tac ptr="w1" in descendants_range_caps_no_overlapI'[where sz = pageBits])
    apply (fastforce simp: cte_wp_at_ctes_of)
   apply (simp add:empty_descendants_range_in')
  apply (frule(1) if_unsafe_then_capD'[OF _ invs_unsafe_then_cap',rotated])
   apply (fastforce simp:cte_wp_at_ctes_of)
  apply (drule ex_cte_not_in_untyped_range[rotated -2])
      apply (simp add:invs_valid_global')+
  apply (drule ex_cte_not_in_untyped_range[rotated -2])
      apply (simp add:invs_valid_global')+
  apply (subgoal_tac "is_aligned (2 ^ pageBits) minUntypedSizeBits")
   prefer 2
   apply (rule is_aligned_weaken)
    apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1,simplified])
   apply (simp add: pageBits_def minUntypedSizeBits_def)
  apply (frule_tac cte="CTE (capability.UntypedCap False a b c) m" for a b c m in valid_global_refsD', clarsimp)
  apply (simp add: Int_commute)
  by (auto simp:empty_descendants_range_in' objBits_simps max_free_index_def
                    archObjSize_def asid_low_bits_def word_bits_def pageBits_def
                    range_cover_full descendants_range'_def2 is_aligned_mask
                    null_filter_descendants_of'[OF null_filter_simp']
                    valid_cap_simps' mask_def)+

lemma doFlush_underlying_memory[wp]:
  "\<lbrace> \<lambda>m'. underlying_memory m' p = um \<rbrace>
   doFlush flush_type vstart vend pstart
   \<lbrace> \<lambda>_ m'. underlying_memory m' p = um \<rbrace>"
  unfolding doFlush_def by(cases flush_type; wpsimp)

(* FIXME: move *)
lemma dmo_invs'_simple:
  "no_irq f \<Longrightarrow>
   (\<And>p um. \<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace> f \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>) \<Longrightarrow>
   \<lbrace> invs' \<rbrace> doMachineOp f \<lbrace> \<lambda>y. invs' \<rbrace>"
  by (rule hoare_pre, rule dmo_invs', wp no_irq, simp_all add:valid_def split_def)

(* FIXME: move *)
lemma doFlush_invs[wp]:
  "\<lbrace> invs' \<rbrace> doMachineOp (doFlush flush_type vstart vend pstart) \<lbrace> \<lambda>y. invs' \<rbrace>"
  by(wp dmo_invs'_simple)

lemma performPageDirectoryInvocation_invs'[wp]:
  "\<lbrace> invs' \<rbrace> performPageDirectoryInvocation pdi \<lbrace> \<lambda>rv. invs' \<rbrace>"
  by(cases pdi, simp_all add:performPageDirectoryInvocation_def, (wp|simp)+)

lemma arch_performInvocation_invs':
  "\<lbrace>invs' and ct_active' and valid_arch_inv' invocation\<rbrace>
  Arch.performInvocation invocation
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding ARM_H.performInvocation_def
  by (cases invocation,
      simp_all add: performARMMMUInvocation_def valid_arch_inv'_def,
      (wp|simp)+)

end

end
