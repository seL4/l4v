(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
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

lemmas [datatype_schematic] = cap.sel list.sel(1) list.sel(3)

context begin interpretation Arch . (*FIXME: arch-split*)

declare arch_cap.sel [datatype_schematic]
declare is_aligned_shiftl [intro!]
declare is_aligned_shiftr [intro!]

definition
  "asid_ci_map i \<equiv>
  case i of RISCV64_A.MakePool frame slot parent base \<Rightarrow>
  RISCV64_H.MakePool frame (cte_map slot) (cte_map parent) (ucast base)"

definition
  "valid_aci' aci \<equiv> case aci of MakePool frame slot parent base \<Rightarrow>
  \<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = NullCap) slot s \<and>
      cte_wp_at' (\<lambda>cte. \<exists>idx.  cteCap cte = UntypedCap False frame pageBits idx) parent s \<and>
      descendants_of' parent (ctes_of s) = {} \<and>
      slot \<noteq> parent \<and>
      ex_cte_cap_to' slot s \<and>
      sch_act_simple s \<and>
      is_aligned base asid_low_bits \<and> asid_wf base"

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
   apply (clarsimp simp: capRange_def asid_low_bits_def bit_simps)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps capRange_def asid_low_bits_def bit_simps)
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
  "\<lbrace>\<lambda>s.  koTypeOf ty = otype \<and> is_aligned ptr (objBitsKO ty) \<and>
         pspace_aligned' s \<and> pspace_no_overlap' ptr (objBitsKO ty) s\<rbrace>
   createObjects' ptr (Suc 0) ty 0
   \<lbrace>\<lambda>rv s. typ_at' otype ptr s\<rbrace>"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (clarsimp simp:createObjects'_def alignError_def split_def | wp unless_wp | wpc )+
  apply (clarsimp simp:obj_at'_def ko_wp_at'_def typ_at'_def pspace_distinct'_def)+
  apply (subgoal_tac "ps_clear ptr (objBitsKO ty)
    (s\<lparr>ksPSpace := \<lambda>a. if a = ptr then Some ty else ksPSpace s a\<rparr>)")
  apply (simp add:ps_clear_def)+
  apply (rule ccontr)
  apply (drule int_not_emptyD)
  apply clarsimp
  apply (unfold pspace_no_overlap'_def)
  apply (erule allE)+
  apply (erule(1) impE)
  apply (subgoal_tac "x \<in> mask_range x (objBitsKO y)")
   apply (fastforce simp: is_aligned_neg_mask_eq)
  apply (drule(1) pspace_alignedD')
  apply (clarsimp simp: is_aligned_no_overflow_mask)
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
  apply (rename_tac p slot p' slot' word2)
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
             apply (rule corres_retype [where ty="Inl (KOArch (KOASIDPool F))" for F,
                                        unfolded APIType_map2_def makeObjectKO_def,
                                        THEN createObjects_corres',simplified,
                                        where val = "makeObject::asidpool"])
                   apply simp
                  apply (simp add: objBits_simps obj_bits_api_def arch_kobj_size_def
                                   default_arch_object_def)+
               apply (simp add: obj_relation_retype_def default_object_def
                                default_arch_object_def objBits_simps)
               apply (simp add: other_aobj_relation_def asid_pool_relation_def)
               apply (simp add: makeObject_asidpool const_def inv_def)
              apply (rule range_cover_full)
               apply (simp add:obj_bits_api_def arch_kobj_size_def default_arch_object_def)+
            apply (rule corres_split)
               apply (rule cteInsert_simple_corres, simp, rule refl, rule refl)
              apply (rule_tac F="asid_low_bits_of word2 = 0" in corres_gen_asm)
              apply (simp add: is_aligned_mask dc_def[symmetric])
              apply (rule corres_split[where P=\<top> and P'=\<top> and r'="\<lambda>t t'. t = t' o ucast"])
                 apply (clarsimp simp: state_relation_def arch_state_relation_def)
                apply (rule corres_trivial)
                apply (rule corres_modify)
                apply (thin_tac "x \<in> state_relation" for x)
                apply (clarsimp simp: state_relation_def arch_state_relation_def o_def)
                apply (rule ext)
                apply (clarsimp simp: up_ucast_inj_eq)
               apply wp+
           apply (strengthen safe_parent_strg[where idx = "2^pageBits"])
           apply (strengthen invs_valid_objs invs_distinct
                             invs_psp_aligned invs_mdb invs_arch_state
                  | simp cong:conj_cong)+
           apply (wp retype_region_plain_invs[where sz = pageBits]
                     retype_cte_wp_at[where sz = pageBits])+
          apply (strengthen vp_strgs'
                 safe_parent_strg'[where idx = "2^pageBits"])
          apply (simp cong: conj_cong)
          apply (wp createObjects_valid_pspace'
                    [where sz = pageBits and ty="Inl (KOArch (KOASIDPool undefined))"])
                apply (simp add: makeObjectKO_def)+
              apply (simp add:objBits_simps range_cover_full valid_cap'_def)+
            apply (fastforce intro!: canonical_address_neq_mask simp: kernel_mappings_canonical)
           apply (rule in_kernel_mappings_neq_mask, (simp add: valid_cap'_def bit_simps)+)[1]
          apply (clarsimp simp:valid_cap'_def)
          apply (wp createObject_typ_at'
                    createObjects_orig_cte_wp_at'[where sz = pageBits])
          apply (rule descendants_of'_helper)
          apply (wp createObjects_null_filter'
                    [where sz = pageBits and ty="Inl (KOArch (KOASIDPool undefined))"])
         apply (clarsimp simp: conj_comms obj_bits_api_def arch_kobj_size_def
                               objBits_simps default_arch_object_def pred_conj_def)
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
                              objBits_simps default_arch_object_def
                              makeObjectKO_def range_cover_full
                        simp del: capFreeIndex_update.simps
               | strengthen invs_valid_pspace' invs_pspace_aligned'
                            invs_pspace_distinct'
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
      apply (clarsimp simp:bit_simps word_bits_def is_aligned_neg_mask_eq)
     apply (simp only:delete_objects_rewrite)
     apply wp+
    apply (clarsimp simp: conj_comms)
    apply (clarsimp simp: conj_comms ex_disj_distrib
           | strengthen invs_valid_pspace' invs_pspace_aligned'
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
   apply (clarsimp simp:invs_mdb max_free_index_def invs_untyped_children)
   apply (prop_tac "detype_locale x y sa" for x y)
    apply (simp add: detype_locale_def)
    apply (fastforce simp: cte_wp_at_caps_of_state descendants_range_def2
                           empty_descendants_range_in invs_untyped_children)
   apply (intro conjI)
          apply (clarsimp)
         apply (erule(1) caps_of_state_valid)
         subgoal by (fastforce simp:cte_wp_at_caps_of_state descendants_range_def2 empty_descendants_range_in)
       apply (fold_subgoals (prefix))[2]
     subgoal premises prems using prems by (clarsimp simp:invs_def valid_state_def)+
      apply (clarsimp simp: schact_is_rct_def)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (drule detype_locale.non_null_present)
     apply (fastforce simp: cte_wp_at_caps_of_state)
    apply simp
   apply (frule_tac ptr = "(p', slot')" in detype_invariants [rotated 3])
        apply fastforce
       apply simp
      apply (simp add: cte_wp_at_caps_of_state)
     apply (simp add: is_cap_simps)
    apply (simp add:empty_descendants_range_in descendants_range_def2)
   apply (frule intvl_range_conv[where bits = pageBits])
    apply (clarsimp simp:pageBits_def word_bits_def)
   apply (clarsimp simp: invs_valid_objs cte_wp_at_caps_of_state range_cover_full
                         invs_psp_aligned invs_distinct cap_master_cap_simps is_cap_simps
                         is_simple_cap_def)
   apply (clarsimp simp: conj_comms)
   apply (rule conjI, clarsimp simp: is_aligned_asid_low_bits_of_zero)
   apply (frule ex_cte_cap_protects)
        apply (simp add:cte_wp_at_caps_of_state)
       apply (simp add:empty_descendants_range_in)
      apply fastforce
     apply (rule subset_refl)
    apply fastforce
   apply (clarsimp simp: is_simple_cap_arch_def)
   apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp simp: clear_um_def)
   apply (simp add:detype_clear_um_independent)
   apply (rule conjI)
    apply clarsimp
    apply (drule_tac p = "(p', slot')" in cap_refs_in_kernel_windowD2[OF caps_of_state_cteD])
     apply fastforce
    apply (clarsimp simp: region_in_kernel_window_def valid_cap_def
                          cap_aligned_def is_aligned_neg_mask_eq detype_def clear_um_def)
    apply fastforce
   apply (rule conjI,erule caps_no_overlap_detype[OF descendants_range_caps_no_overlapI])
     apply (clarsimp simp:is_aligned_neg_mask_eq cte_wp_at_caps_of_state)
     apply (simp add:empty_descendants_range_in)+
   apply (rule conjI, rule pspace_no_overlap_subset,
         rule pspace_no_overlap_detype[OF caps_of_state_valid])
        apply (simp add:invs_psp_aligned invs_valid_objs is_aligned_neg_mask_eq)+
   apply (clarsimp simp: detype_def clear_um_def valid_sched_def
                         st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def)
  apply (simp add: detype_def clear_um_def)
  apply (drule_tac x = "cte_map (p', slot')" in pspace_relation_cte_wp_atI[OF state_relation_pspace_relation])
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
      apply (simp add:word_bits_def bit_simps)
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
     apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
    apply fastforce
   apply simp
  apply clarsimp
  done

definition
  archinv_relation :: "arch_invocation \<Rightarrow> Arch.invocation \<Rightarrow> bool"
where
  "archinv_relation ai ai' \<equiv> case ai of
     arch_invocation.InvokePageTable pti \<Rightarrow>
       \<exists>pti'. ai' = InvokePageTable pti' \<and> page_table_invocation_map pti pti'
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

declare check_vp_alignment_inv[wp del]

lemma select_ext_fa:
  "free_asid_select asid_tbl \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_select asid_tbl) S) :: _ det_ext_monad)
   = return (free_asid_select asid_tbl)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def fail_def)

lemma select_ext_fap:
  "free_asid_pool_select p b \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_pool_select p b) S) :: _ det_ext_monad)
   = return (free_asid_pool_select p b)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def)

lemmas vmsz_aligned_imp_aligned
    = vmsz_aligned_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN is_aligned_weaken]

lemma checkSlot_corres:
  "(\<And>pte pte'. pte_relation' pte pte' \<Longrightarrow> test' pte' = test pte) \<Longrightarrow>
   corres (ser \<oplus> dc)
          (pte_at p and pspace_aligned and pspace_distinct) \<top>
          (check_slot p test)
          (checkSlot p test')"
  apply (simp add: check_slot_def checkSlot_def unlessE_whenE liftE_bindE)
  apply (corres corres: corres_throwErrorTT[of ser])
  done

lemma vmrights_map_vm_kernel_only[simp]:
  "vmrights_map vm_kernel_only = VMKernelOnly"
  by (simp add: vmrights_map_def vm_kernel_only_def)

lemma not_in_vm_kernel_only[simp]:
  "x \<notin> vm_kernel_only"
  by (simp add: vm_kernel_only_def)

lemma vmrights_map_VMKernelOnly:
  "vmrights_map (mask_vm_rights R r) = VMKernelOnly \<Longrightarrow> mask_vm_rights R r = vm_kernel_only"
  by (auto simp: vmrights_map_def mask_vm_rights_def validate_vm_rights_def vm_read_write_def
                 vm_read_only_def split: if_splits)

lemma machine_word_len_pageBits_shift[simp]:
  "UCAST(pte_ppn_len \<rightarrow> machine_word_len) (UCAST(machine_word_len \<rightarrow> pte_ppn_len) (p >> pageBits))
   = p >> pageBits"
  by (word_eqI_solve simp: ucast_ucast_mask pageBits_def dest: bit_imp_possible_bit)

lemma vmrights_map_empty[simp]:
  "vmrights_map {} = VMKernelOnly"
  by (simp add: vmrights_map_def)

lemma pte_relation_make_user[simp]:
  "pte_relation'
     (make_user_pte p (attribs_from_word a) (mask_vm_rights R (data_to_rights r)))
     (makeUserPTE p (\<not>attribsFromWord a) (maskVMRights (vmrights_map R) (rightsFromWord r)))"
  by (auto simp: make_user_pte_def makeUserPTE_def attribs_from_word_def
                 attribsFromWord_def mask_vmrights_corres vmrights_map_VMKernelOnly)

lemma below_user_vtop_in_user_region:
  "p < user_vtop \<Longrightarrow> p \<in> user_region"
  apply (simp add: user_region_def canonical_user_def user_vtop_def pptrUserTop_def)
  apply (simp add: bit_simps is_aligned_mask canonical_bit_def)
  by (word_bitwise, clarsimp simp: word_size)

lemma vmsz_aligned_user_region:
  "\<lbrakk> vmsz_aligned p sz;  p + (2 ^ pageBitsForSize sz - 1) < pptrUserTop \<rbrakk>
   \<Longrightarrow> p \<in> user_region"
  using pbfs_atleast_pageBits[of sz]
  apply (simp flip: mask_2pm1 add: vmsz_aligned_def)
  apply (simp add: user_region_def canonical_user_def pptrUserTop_def)
  apply (simp add: bit_simps is_aligned_mask canonical_bit_def word_plus_and_or_coroll)
  by (word_bitwise, clarsimp simp: word_size)

lemma decodeX64FrameInvocation_corres:
  "\<lbrakk>cap = arch_cap.FrameCap p R sz d opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at ((=) (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_frame_invocation l args slot cap excaps)
            (decodeRISCVFrameInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_frame_invocation_def decodeRISCVFrameInvocation_def Let_def isCap_simps
        split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel RISCVPageMap")
   apply (case_tac "\<not>(2 < length args \<and> excaps \<noteq> [])")
    apply (auto simp: decode_fr_inv_map_def split: list.split)[1]
   apply (simp add: decode_fr_inv_map_def Let_def neq_Nil_conv)
   apply (elim exE conjE)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (simp add: decodeRISCVFrameInvocationMap_def)
   apply (simp split: cap.split, intro conjI impI allI, simp_all)[1]
   apply (rename_tac arch_capa)
   apply (case_tac arch_capa, simp_all)[1]
   apply (rename_tac wd opt')
   apply (case_tac opt'; simp add: mdata_map_def)
   apply (rename_tac av, case_tac av, simp)
   apply (rename_tac a v)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        apply (rule corres_lookup_error)
        apply (rule findVSpaceForASID_corres[OF refl])
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_splitEE[where r'=dc])
          apply (rule corres_whenE)
            apply (simp add: pptr_base_def user_vtop_def pptrUserTop_def shiftl_t2n mask_def)
           apply (rule corres_trivial, simp)
          apply simp
         apply (rule corres_splitEE[where r'=dc])
            apply (rule checkVPAlignment_corres)
           apply (rule corres_splitEE)
              apply (simp only: corres_liftE_rel_sum)
              apply (rule lookupPTSlot_corres)
             apply (clarsimp simp: unlessE_whenE)
             apply (rule corres_splitEE[where r'=dc])
                apply datatype_schem
                apply (rule corres_whenE, simp)
                 apply (rule corres_trivial, clarsimp simp: lookup_failure_map_def)
                apply simp
               apply (rule corres_splitEE[where r'=dc])
                  apply (cases opt; clarsimp)
                   apply (fold ser_def)
                   apply (rule checkSlot_corres)
                   apply fastforce
                  apply (rule corres_guard_imp)
                    apply (rule whenE_throwError_corres)
                      apply fastforce
                     apply (rule up_ucast_inj_eq[THEN arg_cong_Not, symmetric], simp)
                    apply (rule whenE_throwError_corres)
                      apply fastforce
                     apply presburger
                    apply (rule checkSlot_corres)
                    apply (case_tac pte; simp add: is_PageTablePTE_def RISCV64_H.isPageTablePTE_def)
                   apply blast
                  apply blast
                 apply (rule corres_trivial, rule corres_returnOk)
                 apply (clarsimp simp: archinv_relation_def page_invocation_map_def mapping_map_def)
                apply (wpsimp simp: if_apply_def2
                              wp: validE_validE_R[OF find_vspace_for_asid_wp, simplified])+
    apply (clarsimp simp: invs_psp_aligned invs_distinct invs_vspace_objs invs_valid_asid_table
                          cte_wp_at_caps_of_state is_cap_simps)
    apply (rule conjI; clarsimp?)
     apply (clarsimp simp: valid_cap_def wellformed_mapdata_def)
    apply (rule conjI)
     apply (rule exI)+
     apply (rule conjI, erule vspace_for_asid_vs_lookup, simp)
    apply (rule conjI)
     apply (simp add: not_le vmsz_aligned_user_region mask_def user_vtop_def)
    apply clarsimp
    apply (drule (1) pt_lookup_slot_vs_lookup_slotI, clarsimp)
    apply (erule vs_lookup_slot_pte_at; assumption?)
    apply (simp add: not_le vmsz_aligned_user_region mask_def user_vtop_def)
   apply fastforce
  \<comment> \<open>PageUnmap\<close>
  apply (simp split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel RISCVPageUnmap")
   apply simp
   apply (rule corres_returnOk)
   apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
  \<comment> \<open>PageGetAddress\<close>
  apply (cases "invocation_type l = ArchInvocationLabel RISCVPageGetAddress")
   apply simp
   apply (rule corres_returnOk)
   apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: if_split)

lemma VMReadWrite_vmrights_map[simp]: "vmrights_map vm_read_write = VMReadWrite"
  by (simp add: vmrights_map_def vm_read_write_def)

lemma gets_vspace_for_asid_is_catch:
  "gets (vspace_for_asid a) = ((liftME Some (find_vspace_for_asid a)) <catch> const (return None))"
  apply (simp add: find_vspace_for_asid_def liftME_def liftE_bindE catch_def)
  apply (rule ext)
  apply (clarsimp simp: bind_def simpler_gets_def throw_opt_def bindE_def throwError_def return_def
                        returnOk_def
                  split: option.splits)
  done

lemma maybeVSpaceForASID_corres:
  "a' = ucast a \<Longrightarrow>
   corres (=)
          (valid_vspace_objs and valid_asid_table and pspace_aligned and pspace_distinct
             and K (0 < a))
          no_0_obj'
          (gets (vspace_for_asid a)) (maybeVSpaceForASID a')"
  apply (simp add: maybeVSpaceForASID_def gets_vspace_for_asid_is_catch)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch)
       apply (simp add: o_def)
       apply (rule findVSpaceForASID_corres, simp)
      apply (rule corres_trivial, simp)
     apply wpsimp+
  done

crunch isFinalCapability
  for no_0_obj'[wp]: no_0_obj'
  (simp: crunch_simps wp: crunch_wps)

lemma decodeX64PageTableInvocation_corres:
  "\<lbrakk>cap = arch_cap.PageTableCap p opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at ((=) (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_page_table_invocation l args slot cap excaps)
            (decodeRISCVPageTableInvocation l args (cte_map slot) cap' excaps')"
  supply option.case_cong[cong]
  apply (simp add: decode_page_table_invocation_def decodeRISCVPageTableInvocation_def Let_def
                   isCap_simps
              split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel RISCVPageTableMap")
   apply (simp add: decode_pt_inv_map_def
               split: invocation_label.split arch_invocation_label.splits split del: if_split)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (clarsimp simp: neq_Nil_conv Let_def decodeRISCVPageTableInvocationMap_def)
   apply (rule whenE_throwError_corres_initial; (fastforce simp: mdata_map_def)?)
   apply (simp split: cap.split arch_cap.split option.split,
             intro conjI allI impI, simp_all)[1]
   apply (rule whenE_throwError_corres_initial; simp?)
    apply (simp add: user_vtop_def pptrUserTop_def)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        apply (rule corres_lookup_error)
        apply (rule findVSpaceForASID_corres[OF refl])
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_splitEE)
          apply (simp)
          apply (rule lookupPTSlot_corres)
         apply clarsimp
         apply (rule corres_splitEE)
            apply simp
            apply datatype_schem
            apply (rule getObject_PTE_corres)
           apply (simp add: unlessE_whenE)
           apply (rule corres_splitEE[where r'=dc])
              apply (rule corres_whenE)
                apply clarsimp
                apply (case_tac old_pte; simp)
               apply (rule corres_trivial, simp)
              apply simp
             apply (rule corres_trivial, rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def page_table_invocation_map_def
                                   ucast_ucast_mask)
             apply (subst word_le_mask_eq; simp?)
             apply (rule leq_mask_shift)
             apply (simp add: bit_simps le_mask_high_bits word_size)
            apply ((clarsimp cong: if_cong
                     | wp whenE_wp hoare_vcg_all_liftE_R getPTE_wp get_pte_wp
                     | wp (once) hoare_drop_imps)+)
    apply (clarsimp simp: invs_vspace_objs invs_valid_asid_table invs_psp_aligned invs_distinct)
    apply (clarsimp simp: valid_cap_def wellformed_mapdata_def not_le below_user_vtop_in_user_region)
    apply (rule conjI)
     apply (rule exI)+
     apply (rule conjI, erule vspace_for_asid_vs_lookup, simp)
    apply clarsimp
    apply (drule (1) pt_lookup_slot_vs_lookup_slotI, clarsimp)
    apply (erule vs_lookup_slot_pte_at; simp add: below_user_vtop_in_user_region)
   apply fastforce
    \<comment> \<open>PageTableUnmap\<close>
  apply (clarsimp simp: isCap_simps)+
  apply (cases "invocation_type l = ArchInvocationLabel RISCVPageTableUnmap")
   apply (clarsimp simp: unlessE_whenE liftE_bindE)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_symb_exec_r_conj)
        apply (rule_tac F="isArchCap isPageTableCap (cteCap cteVal)"
                                 in corres_gen_asm2)
        apply (rule corres_split[OF isFinalCapability_corres[where ptr=slot]])
          apply (drule mp)
           apply (clarsimp simp: isCap_simps final_matters'_def)
          apply (rule whenE_throwError_corres; simp)
          apply (rule option_corres)
            apply (cases opt; simp add: mdata_map_def)
            apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def
                                                  page_table_invocation_map_def)
           apply (cases opt, clarsimp simp: mdata_map_def)
           apply (clarsimp simp: bind_bindE_assoc)
           apply (rule corres_split)
              apply datatype_schem
              apply (rule maybeVSpaceForASID_corres, simp)
             apply (rule whenE_throwError_corres; simp)
             apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def
                                                   page_table_invocation_map_def)
            apply (simp|wp)+
          apply (cases opt; simp add: mdata_map_def)
         apply (simp | wp getCTE_wp' | wp (once) hoare_drop_imps)+
      apply (clarsimp)
     apply (rule no_fail_pre, rule no_fail_getCTE)
     apply (erule conjunct2)
    apply (clarsimp simp: cte_wp_at_caps_of_state invs_vspace_objs
                          invs_valid_asid_table invs_psp_aligned invs_distinct)
    apply (clarsimp simp: valid_cap_def wellformed_mapdata_def)
   apply (clarsimp simp: cte_wp_at_ctes_of cap_rights_update_def acap_rights_update_def
                         cte_wp_at_caps_of_state)
   apply (drule pspace_relation_ctes_ofI[OF _ caps_of_state_cteD, rotated],
                erule invs_pspace_aligned', clarsimp+)
   apply (simp add: isCap_simps invs_no_0_obj')
  apply (simp add: isCap_simps split del: if_split)
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits)


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
     (\<lambda>s. \<forall>x\<in>set excaps'. s \<turnstile>' fst x \<and> cte_at' (snd x) s))
   (arch_decode_invocation (mi_label mi) args (to_bl cptr') slot
      arch_cap excaps)
   (Arch.decodeInvocation (mi_label mi) args cptr'
     (cte_map slot) arch_cap' excaps')"
  apply (simp add: arch_decode_invocation_def
                   RISCV64_H.decodeInvocation_def
                   decodeRISCVMMUInvocation_def
              split del: if_split)
  apply (cases arch_cap)
     \<comment> \<open>ASIDPoolCap\<close>
     apply (simp add: isCap_simps decodeRISCVMMUInvocation_def decode_asid_pool_invocation_def
                      decodeRISCVASIDPoolInvocation_def Let_def
                 split del: if_split)
     apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel RISCVASIDPoolAssign")
      apply (simp split: invocation_label.split arch_invocation_label.split)
     apply (rename_tac word1 word2)
     apply (cases "excaps", simp)
     apply (cases "excaps'", simp)
     apply clarsimp
     apply (case_tac a, simp_all)[1]
     apply (rename_tac arch_capa)
     apply (case_tac arch_capa, simp_all)[1]
     apply (rename_tac word3 option)
     apply (case_tac option, simp_all add: mdata_map_def)[1]
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE)
          apply (rule corres_trivial [where r="ser \<oplus> (\<lambda>p p'. p = p' o ucast)"])
          apply (clarsimp simp: state_relation_def arch_state_relation_def)
         apply (rule whenE_throwError_corres, simp)
           apply (simp add: lookup_failure_map_def)
          apply simp
         apply (rule_tac P="\<lambda>s. (asid_table (asid_high_bits_of word2) = Some word1 \<longrightarrow> asid_pool_at word1 s) \<and>
                                pspace_aligned s \<and> pspace_distinct s \<and> is_aligned word2 asid_low_bits" and
                         P'="\<top>" in corres_inst)
         apply (simp add: liftME_return)
         apply (rule whenE_throwError_corres_initial, simp)
          apply auto[1]
         apply (rule corres_guard_imp)
           apply (rule corres_splitEE)
              apply simp
              apply (rule get_asid_pool_corres_inv'[OF refl])
             apply (simp add: bindE_assoc)
             apply (rule_tac F="is_aligned word2 asid_low_bits" in corres_gen_asm)
             apply (rule corres_splitEE)
                apply (rule corres_whenE)
                  apply (subst conj_assoc [symmetric])
                  apply (subst assocs_empty_dom_comp [symmetric])
                  apply (erule dom_ucast_eq)
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
      apply (auto simp: valid_cap_def)[1]
     apply auto[1]
    \<comment> \<open>ASIDControlCap\<close>
    apply (simp add: isCap_simps decodeRISCVMMUInvocation_def decode_asid_control_invocation_def
                     Let_def decodeRISCVASIDControlInvocation_def
                split del: if_split)
    apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel RISCVASIDControlMakePool")
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
        apply (rule corres_splitEE)
           apply (rule corres_whenE)
             apply (subst assocs_empty_dom_comp [symmetric])
             apply (simp add: o_def)
             apply (rule dom_ucast_eq_8)
            apply (rule corres_trivial, simp, simp)
          apply (simp split del: if_split)
          apply (rule_tac F="- dom (asidTable \<circ> ucast) \<inter> {x. x \<le> 2 ^ asid_high_bits - 1} \<noteq> {}" in corres_gen_asm)
          apply (drule dom_hd_assocsD)
          apply (simp add: select_ext_fa[simplified free_asid_select_def]
                     free_asid_select_def o_def returnOk_liftE[symmetric] split del: if_split)
          apply (thin_tac "fst a \<notin> b \<and> P" for a b P)
          apply (case_tac "isUntypedCap a \<and> capBlockSize a = objBits (makeObject::asidpool) \<and> \<not> capIsDevice a")
           prefer 2
           apply (rule corres_guard_imp)
             apply (rule corres_trivial)
             apply (case_tac ad; simp add: isCap_simps split del: if_split)
              apply (case_tac x21; simp split del: if_split)
              apply (clarsimp simp: objBits_simps split del: if_split)
             apply clarsimp
            apply (rule TrueI)+
          apply (clarsimp simp: isCap_simps cap_relation_Untyped_eq lookupTargetSlot_def
                                objBits_simps bindE_assoc split_def)
          apply (rule corres_splitEE)
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
     apply (fastforce simp: asid_high_bits_def)
    apply clarsimp
    apply (simp add: null_def split_def asid_high_bits_def  word_le_make_less)
    apply (subst hd_map, assumption)
    (* need abstract guard to show list nonempty *)
    apply (simp add: word_le_make_less)
    apply (simp add: ucast_ucast_mask2 is_down)
    apply (frule hd_in_set)
    apply clarsimp
    apply (prop_tac "\<forall>x::machine_word. x < 2^asid_high_bits \<longrightarrow> x && mask asid_high_bits = x")
     apply (clarsimp simp: and_mask_eq_iff_le_mask le_mask_iff_lt_2n[THEN iffD1] asid_high_bits_def)
    apply (simp add: asid_high_bits_def)
    apply (erule allE, erule (1) impE)
    apply (simp add: ucast_shiftl)
    apply (subst ucast_ucast_len)
     apply (drule hd_in_set)
     apply (rule shiftl_less_t2n; simp add: asid_low_bits_def)
    apply (fastforce)

   \<comment> \<open>PageCap\<close>
   apply (rename_tac word cap_rights vmpage_size option)
   apply (simp add: isCap_simps decodeRISCVMMUInvocation_def Let_def split del: if_split)
   apply (rule decodeX64FrameInvocation_corres; simp)

  \<comment> \<open>PageTableCap\<close>
  apply (simp add: isCap_simps decodeRISCVMMUInvocation_def Let_def  split del: if_split)
  apply (rule decodeX64PageTableInvocation_corres; simp)
  done


lemma arch_performInvocation_corres:
  "archinv_relation ai ai' \<Longrightarrow>
   corres (dc \<oplus> (=))
     (einvs and ct_active and valid_arch_inv ai and schact_is_rct)
     (invs' and ct_active' and valid_arch_inv' ai')
     (arch_perform_invocation ai) (Arch.performInvocation ai')"
  apply (clarsimp simp: arch_perform_invocation_def
                        RISCV64_H.performInvocation_def
                        performRISCVMMUInvocation_def)
  apply (clarsimp simp: archinv_relation_def)
  apply (cases ai)
     apply (clarsimp simp: archinv_relation_def performRISCVMMUInvocation_def)
     apply (rule corres_guard_imp, rule corres_split_nor)
          apply (rule performPageTableInvocation_corres; wpsimp)
         apply (rule corres_trivial, simp)
        apply wpsimp+
      apply (fastforce simp: valid_arch_inv_def)
     apply (fastforce simp: valid_arch_inv'_def)
    apply (clarsimp simp: archinv_relation_def)
    apply (rule corres_guard_imp)
      apply (rule performPageInvocation_corres; wpsimp)
     apply wpsimp+
     apply (fastforce simp: valid_arch_inv_def)
    apply (fastforce simp: valid_arch_inv'_def)
   apply (clarsimp simp: archinv_relation_def)
   apply (rule corres_guard_imp, rule corres_split_nor)
        apply (rule performASIDControlInvocation_corres; wpsimp)
       apply (rule corres_trivial, simp)
      apply wpsimp+
    apply (fastforce simp: valid_arch_inv_def)
   apply (fastforce simp: valid_arch_inv'_def)
  apply (clarsimp simp: archinv_relation_def)
  apply (rule corres_guard_imp, rule corres_split_nor)
       apply (rule performASIDPoolInvocation_corres; wpsimp)
      apply (rule corres_trivial, simp)
     apply wpsimp+
   apply (fastforce simp: valid_arch_inv_def)
  apply (fastforce simp: valid_arch_inv'_def)
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
   apply (simp add: pageBits_def is_aligned_def untypedBits_defs)
  apply (simp add: valid_cap_simps' range_cover_def objBits_simps untypedBits_defs
                   capAligned_def unat_eq_0 and_mask_eq_iff_shiftr_0[symmetric]
                   word_bw_assocs)
  apply clarsimp
  apply (drule(1) cte_cap_in_untyped_range,
         fastforce simp add: cte_wp_at_ctes_of, assumption, simp_all)
   apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
  apply clarsimp
  done

lemma invokeArch_tcb_at':
  "\<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p\<rbrace>
     Arch.performInvocation ai
   \<lbrace>\<lambda>rv. tcb_at' p\<rbrace>"
  apply (simp add: RISCV64_H.performInvocation_def performRISCVMMUInvocation_def)
  apply (wpsimp simp: performRISCVMMUInvocation_def pred_tcb_at' valid_arch_inv'_def
                  wp: performASIDControlInvocation_tcb_at')
  done

crunch setThreadState
  for pspace_no_overlap'[wp]: "pspace_no_overlap' w s"
  (simp: unless_def)

lemma sts_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  by (wp ex_cte_cap_to'_pres)


lemma sts_valid_arch_inv':
  "\<lbrace>valid_arch_inv' ai\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_arch_inv' ai\<rbrace>"
  apply (cases ai, simp_all add: valid_arch_inv'_def)
     apply (clarsimp simp: valid_pti'_def split: page_table_invocation.splits)
     apply (rule conjI|clarsimp|wpsimp)+
    apply (rename_tac page_invocation)
    apply (case_tac page_invocation, simp_all add: valid_page_inv'_def)[1]
       apply (wp  |simp)+
   apply (clarsimp simp: valid_aci'_def split: asidcontrol_invocation.splits)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (rule hoare_pre, wp)
   apply clarsimp
  apply (clarsimp simp: valid_apinv'_def split: asidpool_invocation.splits)
  apply (rule hoare_pre, wp)
  apply simp
  done

lemma inv_ASIDPool: "inv ASIDPool = (\<lambda>v. case v of ASIDPool a \<Rightarrow> a)"
  apply (rule ext)
  apply (case_tac v)
  apply simp
  apply (rule inv_f_f, rule inj_onI)
  apply simp
  done

lemma eq_arch_update':
  "ArchObjectCap cp = cteCap cte \<Longrightarrow> is_arch_update' (ArchObjectCap cp) cte"
  by (clarsimp simp: is_arch_update'_def isCap_simps)

lemma decode_page_inv_wf[wp]:
  "cap = (arch_capability.FrameCap word vmrights vmpage_size d option) \<Longrightarrow>
      \<lbrace>invs' and valid_cap' (capability.ArchObjectCap cap ) and
        cte_wp_at' ((=) (capability.ArchObjectCap cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeRISCVFrameInvocation label args slot cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, -"
  apply (simp add: decodeRISCVFrameInvocation_def Let_def isCap_simps
             cong: if_cong split del: if_split)
  apply (wpsimp simp: decodeRISCVFrameInvocationMap_def valid_arch_inv'_def valid_page_inv'_def
                      checkSlot_def if_apply_def2
                  wp: getPTE_wp hoare_vcg_all_lift lookupPTSlot_inv
         | wp (once) hoare_drop_imps)+
  apply ((rule conjI; clarsimp)+;
           (clarsimp simp: cte_wp_at_ctes_of,
            (drule_tac t="cteCap _" in sym)+,
            (drule ctes_of_valid', fastforce)+,
            clarsimp simp: valid_cap'_def ptBits_def pageBits_def
                           is_arch_update'_def isCap_simps capAligned_def wellformed_mapdata'_def
                           vmsz_aligned_user_region not_le))
  done

lemma below_pptrUserTop_in_user_region:
  "p < pptrUserTop \<Longrightarrow> p \<in> user_region"
  apply (simp add: user_region_def canonical_user_def pptrUserTop_def)
  apply (simp add: bit_simps is_aligned_mask canonical_bit_def)
  by (word_bitwise, clarsimp simp: word_size)

lemma decode_page_table_inv_wf[wp]:
  "arch_cap = PageTableCap word option \<Longrightarrow>
       \<lbrace>invs' and valid_cap' (capability.ArchObjectCap arch_cap) and
        cte_wp_at' ((=) (capability.ArchObjectCap arch_cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeRISCVPageTableInvocation label args slot arch_cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  supply if_cong[cong] if_split [split del]
  apply (clarsimp simp: decodeRISCVPageTableInvocation_def Let_def isCap_simps)
  apply (wpsimp simp: decodeRISCVPageTableInvocationMap_def valid_arch_inv'_def valid_pti'_def
                      maybeVSpaceForASID_def o_def if_apply_def2
                wp: getPTE_wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                    lookupPTSlot_inv isFinalCapability_inv
         | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: not_le isCap_simps cte_wp_at_ctes_of eq_arch_update')
  apply (drule_tac t="cteCap cte" in sym)
  apply (simp add: valid_cap'_def capAligned_def)
  apply (clarsimp simp: is_arch_update'_def isCap_simps
                  split: if_split)
  apply (rule conjI; clarsimp)
  apply (drule_tac t="cteCap ctea" in sym)
  apply (drule ctes_of_valid', fastforce)+
  apply (clarsimp simp: valid_cap'_def)
  apply (simp add: wellformed_mapdata'_def below_pptrUserTop_in_user_region neg_mask_user_region)
  done

lemma capMaster_isPageTableCap:
  "capMasterCap cap' = capMasterCap cap \<Longrightarrow>
   isArchCap isPageTableCap cap' = isArchCap isPageTableCap cap"
  by (simp add: capMasterCap_def isArchCap_def isPageTableCap_def
           split: capability.splits arch_capability.splits)

lemma arch_decodeInvocation_wf[wp]:
  shows "\<lbrace>invs' and valid_cap' (ArchObjectCap arch_cap) and
    cte_wp_at' ((=) (ArchObjectCap arch_cap) o cteCap) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' ((=) (fst x) o cteCap) (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. \<forall>r \<in> cte_refs' (fst x) (irq_node' s). ex_cte_cap_to' r s) and
    (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile>' fst x) and
    sch_act_simple\<rbrace>
   Arch.decodeInvocation label args cap_index slot arch_cap excaps
   \<lbrace>valid_arch_inv'\<rbrace>,-"
  apply (cases arch_cap)
     apply (simp add: decodeRISCVMMUInvocation_def RISCV64_H.decodeInvocation_def
                       Let_def split_def isCap_simps  decodeRISCVASIDControlInvocation_def
                  cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong prod.case_cong
                  split del: if_split)
     apply (rule hoare_pre)
      apply ((wp whenE_throwError_wp ensureEmptySlot_stronger|
              wpc|
              simp add: valid_arch_inv'_def valid_aci'_def is_aligned_shiftl_self
                           split del: if_split)+)[1]
          apply (rule_tac Q'=
                      "\<lambda>rv. K (fst (hd [p\<leftarrow>assocs asidTable . fst p \<le> 2 ^ asid_high_bits - 1 \<and> snd p = None])
                               << asid_low_bits \<le> 2 ^ asid_bits - 1) and
                            real_cte_at' rv and
                            ex_cte_cap_to' rv and
                            cte_wp_at' (\<lambda>cte. \<exists>idx. cteCap cte = (UntypedCap False frame pageBits idx)) (snd (excaps!0)) and
                            sch_act_simple and
                            (\<lambda>s. descendants_of' (snd (excaps!0)) (ctes_of s) = {}) "
                            in hoare_strengthen_postE_R)
           apply (simp add: lookupTargetSlot_def)
           apply wp
          apply (clarsimp simp: cte_wp_at_ctes_of asid_wf_def mask_def)
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
     apply (clarsimp simp: cte_wp_at_ctes_of objBits_simps)

    \<comment> \<open>ASIDPool cap\<close>
    apply (simp add: decodeRISCVMMUInvocation_def RISCV64_H.decodeInvocation_def
                     Let_def split_def isCap_simps decodeRISCVASIDPoolInvocation_def)
    apply (wpsimp simp: valid_arch_inv'_def valid_apinv'_def wp: getASID_wp
             split_del: if_split)
    apply (clarsimp simp: word_neq_0_conv valid_cap'_def valid_arch_inv'_def valid_apinv'_def)
    apply (rule conjI)
     apply (erule cte_wp_at_weakenE')
     apply (simp, drule_tac t="cteCap c" in sym, simp add: isCap_simps)
    apply (subst (asm) conj_assoc [symmetric],
           subst (asm) assocs_empty_dom_comp [symmetric])
    apply (drule dom_hd_assocsD)
    apply (simp add: capAligned_def asid_wf_def mask_def)
    apply (elim conjE)
    apply (subst field_simps, erule is_aligned_add_less_t2n)
      apply assumption
     apply (simp add: asid_low_bits_def asid_bits_def)
      apply assumption

   \<comment> \<open>PageCap\<close>
   apply (simp add: decodeRISCVMMUInvocation_def isCap_simps RISCV64_H.decodeInvocation_def
              cong: if_cong split del: if_split)
   apply (wp, simp+)

  \<comment> \<open>PageTableCap\<close>
  apply (simp add: decodeRISCVMMUInvocation_def isCap_simps RISCV64_H.decodeInvocation_def
             cong: if_cong split del: if_split)
  apply (wpsimp, simp+)
  done

crunch setMRs
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
    (ignore: getRestartPC setRegister transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option
        mapM_wp'
   simp: split_def zipWithM_x_mapM)

crunch performRISCVMMUInvocation
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: crunch_simps
   wp: crunch_wps getObject_cte_inv getASID_wp)

lemmas setObject_cte_st_tcb_at' [wp] = setCTE_pred_tcb_at' [unfolded setCTE_def]

crunch performPageTableInvocation,
                   performPageInvocation,
                   performASIDPoolInvocation
  for st_tcb_at': "st_tcb_at' P t"
  (wp: crunch_wps getASID_wp getObject_cte_inv simp: crunch_simps pteAtIndex_def)

lemma performASIDControlInvocation_st_tcb_at':
  "\<lbrace>st_tcb_at' (P and (\<noteq>) Inactive and (\<noteq>) IdleThreadState) t and
    valid_aci' aci and invs' and ct_active'\<rbrace>
    performASIDControlInvocation aci
  \<lbrace>\<lambda>y. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: performASIDControlInvocation_def split: asidcontrol_invocation.splits)
  apply (clarsimp simp: valid_aci'_def cte_wp_at_ctes_of cong: conj_cong)
  apply (rule hoare_pre)
   apply (wp createObjects_orig_obj_at'[where P="P \<circ> tcbState", folded st_tcb_at'_def]
             updateFreeIndex_pspace_no_overlap' getSlotCap_wp
             hoare_vcg_ex_lift
             deleteObjects_cte_wp_at' deleteObjects_invs_derivatives
             deleteObjects_st_tcb_at'
             hoare_weak_lift_imp
        | simp add: placeNewObject_def2)+
  apply (case_tac ctea)
  apply (clarsimp)
  apply (frule ctes_of_valid_cap')
   apply (simp add:invs_valid_objs')+
  apply (clarsimp simp:valid_cap'_def capAligned_def cte_wp_at_ctes_of)
  apply (rule conjI)
    apply clarsimp
    apply (drule (1) cte_cap_in_untyped_range)
        apply (fastforce simp add: cte_wp_at_ctes_of)
       apply assumption+
      subgoal by (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
     subgoal by fastforce
    apply simp
   apply (rule conjI,assumption)
  apply (clarsimp simp:invs_valid_pspace' objBits_simps range_cover_full descendants_range'_def2
                       isCap_simps)
  apply (intro conjI)
               apply (fastforce simp:empty_descendants_range_in')+
       apply clarsimp
       apply (drule (1) cte_cap_in_untyped_range)
           apply (fastforce simp add: cte_wp_at_ctes_of)
          apply assumption+
         apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
        apply fastforce
       apply simp
  apply auto
  done

lemmas arch_finalise_cap_aligned' = ArchRetypeDecls_H_RISCV64_H_finaliseCap_aligned'

lemmas arch_finalise_cap_distinct' = ArchRetypeDecls_H_RISCV64_H_finaliseCap_distinct'

crunch "Arch.finaliseCap"
  for st_tcb_at'[wp]: "st_tcb_at' P t"
  (wp: crunch_wps getASID_wp simp: crunch_simps)

lemma invs_asid_table_strengthen':
  "invs' s \<and> asid_pool_at' ap s \<and> asid \<le> 2 ^ asid_high_bits - 1 \<longrightarrow>
   invs' (s\<lparr>ksArchState :=
            riscvKSASIDTable_update (\<lambda>_. ((riscvKSASIDTable \<circ> ksArchState) s)(asid \<mapsto> ap)) (ksArchState s)\<rparr>)"
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_global_refs'_def global_refs'_def)
  apply (clarsimp simp: valid_arch_state'_def)
  apply (clarsimp simp: valid_asid_table'_def ran_def mask_def)
  apply (rule conjI)
   apply (clarsimp split: if_split_asm)
   apply (fastforce simp: mask_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_pspace'_def)
  apply (simp add: valid_machine_state'_def)
  done

lemma ex_cte_not_in_untyped_range:
  "\<lbrakk>(ctes_of s) cref = Some (CTE (capability.UntypedCap d ptr bits idx) mnode);
    descendants_of' cref (ctes_of s) = {}; invs' s;
    ex_cte_cap_wp_to' (\<lambda>_. True) x s; valid_global_refs' s\<rbrakk>
   \<Longrightarrow> x \<notin> mask_range ptr bits"
  apply clarsimp
  apply (drule(1) cte_cap_in_untyped_range)
   apply (fastforce simp:cte_wp_at_ctes_of)+
  done

lemma kernel_mappings_canonical_pt_base:
  "x \<in> kernel_mappings \<Longrightarrow> canonical_address (table_base x)"
  apply (simp add: kernel_mappings_def pptr_base_def RISCV64.pptrBase_def canonical_address_range
                   canonical_bit_def bit_simps)
  by (word_bitwise, clarsimp simp: word_size)

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
                createObjects_no_cte_invs[where sz = pageBits and ty="Inl (KOArch (KOASIDPool pool))" for pool]]
                createObjects_orig_cte_wp_at'[where sz = pageBits]  hoare_vcg_const_imp_lift
         |simp add: makeObjectKO_def asid_pool_typ_at_ext' valid_cap'_def cong: rev_conj_cong
         |strengthen safe_parent_strg'[where idx= "2^ pageBits"])+
      apply (rule hoare_vcg_conj_lift)
       apply (rule descendants_of'_helper)
       apply (wp createObjects_null_filter'
                  [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))" for ap]
                 createObjects_valid_pspace'
                  [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))" for ap]
          | simp add: makeObjectKO_def asid_pool_typ_at_ext' valid_cap'_def
                cong: rev_conj_cong)+
       apply (simp add: objBits_simps valid_cap'_def capAligned_def range_cover_full)
      apply (wp  createObjects'_wp_subst[OF createObjects_ex_cte_cap_to[where sz = pageBits]]
                 createObjects_orig_cte_wp_at'[where sz = pageBits]
                 hoare_vcg_const_imp_lift
         |simp add: makeObjectKO_def asid_pool_typ_at_ext' valid_cap'_def
                    isCap_simps
                    canonical_address_neq_mask
               cong: rev_conj_cong
         |strengthen safe_parent_strg'[where idx = "2^ pageBits"]
         | rule in_kernel_mappings_neq_mask
         | simp add: bit_simps kernel_mappings_canonical_pt_base[unfolded bit_simps])+
     apply (simp add:asid_pool_typ_at_ext'[symmetric])
     apply (wp createObject_typ_at')
    apply (simp add: objBits_simps valid_cap'_def
         capAligned_def range_cover_full makeObjectKO_def
         asid_pool_typ_at_ext'
         cong: rev_conj_cong)
    apply (clarsimp simp:conj_comms
                         descendants_of_null_filter'
      | strengthen invs_pspace_aligned' invs_pspace_distinct'
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
           | strengthen invs_valid_pspace' invs_pspace_aligned'
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
    apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1, simplified])
   apply (simp add: pageBits_def untypedBits_defs)
  apply (frule_tac cte="CTE (capability.UntypedCap False a b c) m" for a b c m in valid_global_refsD', clarsimp)
  apply (simp add: Int_commute)
  by (auto simp:empty_descendants_range_in' objBits_simps max_free_index_def
                    asid_low_bits_def word_bits_def live'_def hyp_live'_def
                    range_cover_full descendants_range'_def2 is_aligned_mask
                    null_filter_descendants_of'[OF null_filter_simp'] bit_simps
                    valid_cap_simps' mask_def kernel_mappings_canonical)


lemma arch_performInvocation_invs':
  "\<lbrace>invs' and ct_active' and valid_arch_inv' invocation\<rbrace>
  Arch.performInvocation invocation
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding RISCV64_H.performInvocation_def
  by (cases invocation, simp_all add: performRISCVMMUInvocation_def valid_arch_inv'_def; wpsimp)

end

end
