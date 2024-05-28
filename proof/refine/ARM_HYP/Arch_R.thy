(*
 * Copyright 2022, Proofcraft Pty Ltd
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
  ARM_HYP_H.MakePool frame (cte_map slot) (cte_map parent) base"

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
  "\<lbrace>\<lambda>s.  koTypeOf ty = otype \<and> is_aligned ptr (objBitsKO ty) \<and>
         pspace_aligned' s \<and> pspace_no_overlap' ptr (objBitsKO ty) s\<rbrace>
   createObjects' ptr (Suc 0) ty 0
   \<lbrace>\<lambda>rv s. typ_at' otype ptr s\<rbrace>"
  apply (clarsimp simp:createObjects'_def alignError_def split_def | wp unless_wp | wpc )+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def pspace_distinct'_def)+
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
   apply (fastforce simp:is_aligned_neg_mask_eq p_assoc_help)
  apply (drule(1) pspace_alignedD')
  apply (fastforce simp: is_aligned_no_wrap' p_assoc_help)
  done

lemma retype_region2_ext_retype_region_ArchObject:
  "retype_region ptr n us (ArchObject x)=
  retype_region2 ptr n us (ArchObject x)"
  apply (rule ext)
  apply (simp add:retype_region_def retype_region2_def bind_assoc
    retype_region2_ext_def retype_region_ext_def default_ext_def)
  apply (rule ext)
  apply (intro monad_eq_split_tail ext)+
     apply simp
    apply simp
   apply (simp add:gets_def get_def bind_def return_def simpler_modify_def )
   apply (rule_tac x = xc in fun_cong)
   apply (rule_tac f = do_extended_op in arg_cong)
   apply (rule ext)
   apply simp
  apply simp
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
      apply (rule corres_split[OF getSlotCap_corres])
         apply simp
        apply (rule_tac F = " pcap = (cap.UntypedCap False word1 pageBits idxa)" in corres_gen_asm)
        apply (rule corres_split[OF updateFreeIndex_corres])
            apply (clarsimp simp:is_cap_simps)
           apply (simp add: free_index_of_def)
          apply (rule corres_split)
             apply (simp add: retype_region2_ext_retype_region_ArchObject )
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
      apply (clarsimp simp:pageBits_def word_bits_def is_aligned_neg_mask_eq word_size_bits_def)
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
   apply (subgoal_tac "detype_locale x y sa" for x y)
    prefer 2
    apply (simp add:detype_locale_def)
    apply (fastforce simp:cte_wp_at_caps_of_state descendants_range_def2
            empty_descendants_range_in invs_untyped_children)
   apply (intro conjI)
          apply (clarsimp)
         apply (erule(1) caps_of_state_valid)
        subgoal by (fastforce simp:cte_wp_at_caps_of_state
                descendants_range_def2 empty_descendants_range_in)
       apply (fold_subgoals (prefix))[2]
       subgoal premises prems using prems by (clarsimp simp:invs_def valid_state_def)+
     apply (clarsimp simp:cte_wp_at_caps_of_state)
    apply (drule detype_locale.non_null_present)
     apply (fastforce simp:cte_wp_at_caps_of_state)
    apply simp
   apply (frule_tac ptr = "(aa,ba)" in detype_invariants [rotated 3])
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
   apply (clarsimp simp: detype_def clear_um_def detype_ext_def valid_sched_def valid_etcbs_def
            st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def is_etcb_at_def)
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
     apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
    apply fastforce
   apply simp
  apply clarsimp
  done

definition
  vcpu_invocation_map :: "vcpu_invocation \<Rightarrow> vcpuinvocation"
where
  "vcpu_invocation_map vcpui \<equiv> case vcpui of
      vcpu_invocation.VCPUSetTCB v  t                 \<Rightarrow> VCPUSetTCB v t
   |  vcpu_invocation.VCPUInjectIRQ obj n vreg        \<Rightarrow> VCPUInjectIRQ obj n vreg
   |  vcpu_invocation.VCPUReadRegister obj vreg       \<Rightarrow> VCPUReadRegister obj vreg
   |  vcpu_invocation.VCPUWriteRegister obj vreg word \<Rightarrow> VCPUWriteRegister obj vreg word
   |  vcpu_invocation.VCPUAckVPPI obj irq \<Rightarrow> VCPUAckVPPI obj irq
"

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
       \<exists>ap'. ai' = InvokeASIDPool ap' \<and>  ap' = asid_pool_invocation_map ap
   | arch_invocation.InvokeVCPU vcpui \<Rightarrow>
       \<exists>vcpui'. ai' = InvokeVCPU vcpui' \<and> vcpui' = vcpu_invocation_map vcpui"


definition
  valid_arch_inv' :: "Arch.invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_arch_inv' ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> valid_pti' pti
   | InvokePageDirectory pdi \<Rightarrow> \<top>
   | InvokePage pgi \<Rightarrow> valid_page_inv' pgi
   | InvokeASIDControl aci \<Rightarrow> valid_aci' aci
   | InvokeASIDPool ap \<Rightarrow> valid_apinv' ap
   | InvokeVCPU v \<Rightarrow> valid_vcpuinv' v"

lemma mask_vmrights_corres:
  "maskVMRights (vmrights_map R) (rightsFromWord d) =
  vmrights_map (mask_vm_rights R (data_to_rights d))"
  by (clarsimp simp: rightsFromWord_def data_to_rights_def
                     vmrights_map_def Let_def maskVMRights_def
                     mask_vm_rights_def nth_ucast
                     validate_vm_rights_def vm_read_write_def
                     vm_kernel_only_def vm_read_only_def
               split: bool.splits)

definition
  "parity_mask attrs \<equiv> case attrs of VMAttributes c p xn \<Rightarrow> VMAttributes c False xn"

lemma vm_attributes_corres:
  "vmattributes_map (attribs_from_word w) = attribsFromWord w"
  by (clarsimp simp: attribsFromWord_def attribs_from_word_def
                     Let_def vmattributes_map_def parity_mask_def)

lemma checkVPAlignment_corres:
  "corres (ser \<oplus> dc) \<top> \<top>
          (check_vp_alignment sz w)
          (checkVPAlignment sz w)"
  apply (simp add: check_vp_alignment_def checkVPAlignment_def)
  apply (cases sz, simp_all add: corres_returnOk unlessE_whenE is_aligned_mask)
     apply ((rule corres_guard_imp, rule corres_whenE, rule refl, auto)[1])+
  done

lemma checkVP_wpR [wp]:
  "\<lbrace>\<lambda>s. vmsz_aligned' w sz \<longrightarrow> P () s\<rbrace>
  checkVPAlignment sz w \<lbrace>P\<rbrace>, -"
  apply (simp add: checkVPAlignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp whenE_wp|wpc)+
  apply (simp add: is_aligned_mask vmsz_aligned'_def)
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
    else if isVCPUCap cap then U
    else undefined)
    =
   (if isPageDirectoryCap cap then P
    else if isPageTableCap cap then Q
    else if isPageCap cap then R
    else if isASIDControlCap cap then S
    else if isASIDPoolCap cap then T
    else U)"
  by (cases cap, simp_all add: isCap_simps) (* not sure if this is useful as is *)

lemma decodeVCPUInjectIRQ_inv[wp]: "\<lbrace>P\<rbrace> decodeVCPUInjectIRQ a b \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: decodeVCPUInjectIRQ_def Let_def wp: whenE_wp getVCPU_wp | rule conjI)+

crunch inv [wp]: "ARM_HYP_H.decodeInvocation" "P"
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
  by (simp add: lookup_pt_slot_no_fail_def lookupPTSlotFromPT_def mask_def checkPTAt_def)

lemma page_base_corres[simp]:
  "pageBase vaddr vmsize = page_base vaddr vmsize"
  by (clarsimp simp: pageBase_def page_base_def)

lemma flush_type_map:
  "ARM_HYP_H.isPageFlushLabel (invocation_type (mi_label mi))
   \<or> ARM_HYP_H.isPDFlushLabel (invocation_type (mi_label mi))
  \<Longrightarrow> labelToFlushType (mi_label mi) =
          flush_type_map (label_to_flush_type (invocation_type (mi_label mi)))"
  by (clarsimp simp: label_to_flush_type_def labelToFlushType_def flush_type_map_def
                        ARM_HYP_H.isPageFlushLabel_def ARM_HYP_H.isPDFlushLabel_def
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
      apply (case_tac rv;
             clarsimp simp: master_pde_relation_def pde_relation'_def isSuperSection_def' page_base_def
                     split: if_split_asm)
      apply (rule corres_stateAssert_assume_stronger)
       apply (rule stronger_corres_guard_imp)
         apply (rule corres_split[OF get_master_pte_corres])
           apply (rule corres_trivial)
           apply (case_tac rv;
                  clarsimp simp: master_pte_relation_def pte_relation'_def isLargePage_def' page_base_def
                          split: if_split_asm)
          apply (wp get_master_pte_inv)+
        apply (clarsimp simp: page_table_pte_at_lookupI)
       apply (clarsimp simp: page_table_pte_at_lookupI' page_table_at_state_relation)
      apply clarsimp
      apply (erule(3) page_table_at_state_relation)
     apply wpsimp+
   apply (clarsimp simp: page_directory_pde_at_lookupI)
  apply (clarsimp simp: page_directory_pde_at_lookupI' page_directory_at_state_relation)
  done

lemma decodeARMPageFlush_corres:
  "ARM_HYP_H.isPageFlushLabel (invocation_type (mi_label mi)) \<Longrightarrow>
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
            then let start = args ! 0; end = args ! 1; pstart = start + addrFromPPtr word
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
                        whenE (pstart < physBase \<or> ARM_HYP.paddrTop < end - start + pstart) $
                        throwError ExceptionTypes_A.syscall_error.IllegalOperation;
                        returnOk $
                        arch_invocation.InvokePage $
                        ARM_A.page_invocation.PageFlush \<comment> \<open>Must use word in hyp mode.\<close>
                         (label_to_flush_type (invocation_type (mi_label mi))) (start + word)
                         (end + word - 1) pstart pd asid
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
  apply (clarsimp simp: Let_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule corres_lookup_error)
       apply (rule find_pd_for_asid_corres[OF refl])
      apply (rule whenE_throwError_corres, simp)
       apply simp
      apply (rule whenE_throwError_corres, simp)
       apply simp
      apply (rule whenE_throwError_corres, simp)
       apply (clarsimp simp: add.commute fromPAddr_def)
      apply (rule corres_trivial)
      apply (rule corres_returnOk)
    apply (clarsimp simp: archinv_relation_def page_invocation_map_def flush_type_map_def)
      apply (clarsimp simp: archinv_relation_def page_invocation_map_def
                            label_to_flush_type_def labelToFlushType_def flush_type_map_def
                            ARM_HYP_H.isPageFlushLabel_def
                     split: flush_type.splits invocation_label.splits arch_invocation_label.splits)
     apply wp+
   apply (fastforce simp: valid_cap_def mask_def)
  apply auto
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
    \<Longrightarrow> (VSRef (ucast x) (Some APageDirectory), r') \<in> vs_refs_pages (ArchObj (PageDirectory pd))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pd_sectionI
    = vs_refs_pages_pdI[where pde="ARM_A.pde.SectionPDE x y z" for x y z,
        unfolded pde_ref_pages_def, simplified, OF _ refl]

lemmas vs_refs_pages_pd_supersectionI
    = vs_refs_pages_pdI[where pde="ARM_A.pde.SuperSectionPDE x y z" for x y z,
        unfolded pde_ref_pages_def, simplified, OF _ refl]

lemma get_master_pde_sp:
  "\<lbrace> P \<rbrace> get_master_pde pd_slot \<lbrace> \<lambda>pde s. P s
    \<and> (\<exists>pd pd_slot'. ko_at (ArchObj (PageDirectory pd)) (pd_slot && ~~ mask pd_bits) s
        \<and> pd_slot' && ~~ mask pd_bits = pd_slot && ~~ mask pd_bits
\<comment> \<open>     \<and> ((ucast (pd_slot' && mask pd_bits >> 2) \<in> kernel_mapping_slots)
            \<longrightarrow> (ucast (pd_slot && mask pd_bits >> 2) \<in> kernel_mapping_slots))\<close>
        \<and> pd (ucast (pd_slot' && mask pd_bits >> 3)) = pde)  \<rbrace>"
  apply (simp add: get_master_pde_def)
  apply (wp get_pde_wp | wpc)+
  apply (clarsimp simp: obj_at_def)
  apply (safe, simp_all add: exI[where x=pd_slot] vspace_bits_defs)
  apply (cut_tac max.absorb2[where a=6 and b=pd_bits])
   apply (clarsimp simp: word_bw_assocs neg_mask_combine)
   apply (rule_tac x="pd_slot && ~~ mask 7" in exI)
   apply (clarsimp simp add: word_bw_assocs neg_mask_combine pd_bits_def)+
  done

lemma get_master_pte_wp:
  "\<lbrace> \<lambda>s. (\<forall>pt pt_slot'. ko_at (ArchObj (PageTable pt)) (pt_slot && ~~ mask pt_bits) s
        \<and> pt_slot' && ~~ mask pt_bits = pt_slot && ~~ mask pt_bits
            \<longrightarrow> Q (pt (ucast (pt_slot' && mask pt_bits >> pte_bits))) s)  \<rbrace>
    get_master_pte pt_slot \<lbrace> Q \<rbrace>"
  apply (simp add: get_master_pte_def)
  apply (wp get_pte_wp | wpc)+
  apply clarsimp
  apply (drule spec, drule_tac x="pt_slot && ~~ mask 7" in spec)
  apply (cut_tac max.absorb2[where a=7 and b=pt_bits])
   apply (simp add: word_bw_assocs neg_mask_combine obj_at_def)
   apply fastforce
  apply (simp add: pt_bits_def pageBits_def)
  done

lemma vaddr_segment_nonsense5:
  "is_aligned (p :: word32) 12 \<Longrightarrow> p + ((vaddr >> 12) && mask 9 << 3) && ~~ mask pt_bits = p"
  by (frule vaddr_segment_nonsense3) (simp add:  mask_def)

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
  apply (drule_tac y=pd_bits in is_aligned_weaken, simp add: vspace_bits_defs)
  apply (frule valid_vspace_objsD, simp add: obj_at_def lookup_pd_slot_eq, simp)
  apply (simp add: lookup_pd_slot_eq)
  apply (drule_tac x="ucast (pd_slot' && mask pd_bits >> 3)" in spec)
  apply (rule conjI)
   apply clarsimp
   apply (drule vs_lookup_step)
    apply (rule vs_lookup1I, simp add: obj_at_def)
     apply (erule vs_refs_pdI2)
    apply simp
   apply (drule sym[where s=pd])
   apply (simp add: lookup_pd_slot_eq)
   apply (frule(1) is_aligned_pt)
   apply (frule is_aligned_weaken[where x=pt_bits and y=10])
    apply (simp add: pt_bits_def pageBits_def pte_bits_def)
   apply (simp add: vspace_bits_defs)
   apply (frule_tac vaddr=vaddr in  vaddr_segment_nonsense5, simp add: vspace_bits_defs)
   apply (frule_tac  valid_vspace_objsD, simp add: obj_at_def, simp)
   apply (drule vs_lookup_pages_vs_lookupI)
   apply (rule conjI)
    apply clarsimp
    apply (drule_tac x="ucast (pt_slot' && mask pt_bits >> 3)" in spec)
    apply (drule vs_lookup_pages_step)
     apply (rule vs_lookup_pages1I, simp add: obj_at_def)
      apply (erule vs_refs_pages_pt_largeI)
     apply simp
    apply (drule(1) valid_vs_lookupD)
    apply simp
    apply (erule exEI)+
    apply (clarsimp simp: vs_cap_ref_def vspace_bits_defs split: cap.split_asm arch_cap.split_asm
           option.split_asm vmpage_size.split_asm)
    apply (frule(1) caps_of_state_valid_cap)
    apply (clarsimp simp: valid_cap_def obj_at_def data_at_def a_type_simps
                   split: if_split_asm)+
   apply (drule_tac x="ucast (pt_slot' && mask pt_bits >> 3)" in spec)
   apply (drule vs_lookup_pages_step)
    apply (rule vs_lookup_pages1I, simp add: obj_at_def)
     apply (erule vs_refs_pages_pt_smallI)
    apply simp
   apply (drule(1) valid_vs_lookupD)
   apply simp
   apply (erule exEI)+
   apply (clarsimp simp: vs_cap_ref_def vspace_bits_defs split: cap.split_asm arch_cap.split_asm
          option.split_asm vmpage_size.split_asm)
   apply (frule(1) caps_of_state_valid_cap)
   apply (clarsimp simp: valid_cap_def obj_at_def data_at_def a_type_simps
                  split: if_split_asm)+
  apply (drule vs_lookup_pages_vs_lookupI)
  apply (rule conjI)
   apply clarsimp
   apply (drule vs_lookup_pages_step)
    apply (rule vs_lookup_pages1I, simp add: obj_at_def)
     apply (erule vs_refs_pages_pd_sectionI)
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
    apply (erule vs_refs_pages_pd_supersectionI)
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

lemma list_all2_Cons: "list_all2 f (x#xs) b \<Longrightarrow> \<exists>y ys. b = y # ys"
  by (induct b; simp)

lemma corres_gets_numlistregs [corres]:
  "corres (=) \<top> \<top>
      (gets (arm_gicvcpu_numlistregs \<circ> arch_state)) (gets (armKSGICVCPUNumListRegs \<circ> ksArchState))"
  by (clarsimp simp: state_relation_def arch_state_relation_def)

theorem corres_throwError_ser[corres]:
  "corres (ser \<oplus> r) (\<lambda>_. b = syscall_error_map a) (\<lambda>_. True) (throwError a) (throwError b)"
  by simp

lemmas corres_liftE_rel_sumI = corres_liftE_rel_sum[THEN iffD2]
lemmas corres_liftMI = corres_liftM_simp[THEN iffD2]
lemmas corres_liftM2I = corres_liftM2_simp[THEN iffD2]

lemma get_vcpu_LR_corres[corres]:
  "corres (r \<oplus> (\<lambda>vcpu lr. vgic_lr (vcpu_vgic vcpu) = lr)) (vcpu_at v) (vcpu_at' v)
             (liftE (get_vcpu v)) (liftE (liftM (vgicLR \<circ> vcpuVGIC) (getObject v)))"
  apply simp
  apply (rule corres_rel_imp, rule getObject_vcpu_corres)
  apply (rename_tac vcpu', case_tac vcpu')
  apply (clarsimp simp: vcpu_relation_def vgic_map_def)
  done

lemma vgi_mask[simp]:
  "vgicIRQMask = vgic_irq_mask"
  "vgicIRQActive = vgic_irq_active"
  by (auto simp: vgicIRQMask_def vgic_irq_mask_def vgic_irq_active_def vgicIRQActive_def)

lemma decodeARMVCPUInvocation_corres:
  notes if_split [split del]
  shows
  "\<lbrakk>acap_relation arch_cap arch_cap'; list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps')\<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> archinv_relation)
          (invs and valid_cap (cap.ArchObjectCap arch_cap)
                and (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
           (invs' and valid_cap' (capability.ArchObjectCap arch_cap')
                  and (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s)
                  and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
                (decode_vcpu_invocation  label args arch_cap excaps)
                (decodeARMVCPUInvocation label args cptr' cte arch_cap' excaps')"
  apply (simp add: decode_vcpu_invocation_def decodeARMVCPUInvocation_def)
  apply (cases arch_cap; cases "invocation_type label"; simp add: isVCPUCap_def)
  apply (rename_tac vcpui)
  apply (case_tac vcpui; simp split del: if_split)
      (* set_tcb *)
      apply (simp add: decode_vcpu_set_tcb_def decodeVCPUSetTCB_def Let_def isVCPUCap_def)
      apply (cases excaps; simp add: null_def)
      apply (frule list_all2_Cons)
      apply clarsimp
      apply (case_tac a; clarsimp simp add: cap_relation_def)
      apply (corresK corres: corres_returnOkTT)
      apply (clarsimp simp: archinv_relation_def vcpu_invocation_map_def)
     (* inject_irq *)
     apply (simp add: decode_vcpu_inject_irq_def decodeVCPUInjectIRQ_def isVCPUCap_def)
     apply (cases args; clarsimp)
     apply (case_tac list; clarsimp simp add: rangeCheck_def range_check_def unlessE_whenE)
     apply (clarsimp simp: shiftL_nat whenE_bindE_throwError_to_if)
     apply (corresKsimp wp: get_vcpu_wp)
     apply (clarsimp simp: archinv_relation_def vcpu_invocation_map_def ucast_id
                        valid_cap'_def valid_cap_def
                        make_virq_def makeVIRQ_def split:if_split)
    (* read register *)
    apply (clarsimp simp: decode_vcpu_read_register_def decodeVCPUReadReg_def)
    apply (cases args; clarsimp simp: isCap_simps whenE_def split: if_split)
    apply (rule corres_returnOk)
    apply (simp add: archinv_relation_def vcpu_invocation_map_def)
   (* write register *)
   apply (clarsimp simp: decode_vcpu_write_register_def decodeVCPUWriteReg_def)
   apply (cases args; clarsimp simp: isCap_simps)
   apply (case_tac list; clarsimp)
   apply (clarsimp simp: whenE_def split: if_split)
   apply (rule corres_returnOk)
   apply (simp add: archinv_relation_def vcpu_invocation_map_def ucast_id)
  (* ack vppi *)
  apply (simp add: decode_vcpu_ack_vppi_def decodeVCPUAckVPPI_def isVCPUCap_def)
  apply (cases args; clarsimp simp: isCap_simps)
  apply (simp add: arch_check_irq_def rangeCheck_def ucast_nat_def minIRQ_def unlessE_def
                   word_le_not_less)
  apply (case_tac "a > Kernel_Config.maxIRQ"; simp add:  ucast_nat_def word_le_not_less)
  apply (clarsimp simp: irq_vppi_event_index_def irqVPPIEventIndex_def IRQ_def toEnum_unat_ucast
                        le_maxIRQ_machine_less_irqBits_val)
  apply (fastforce simp: archinv_relation_def vcpu_invocation_map_def
                   intro: corres_returnOk
                   split: if_splits)
  done

lemma corres_splitEE':
  assumes "corres_underlying sr nf nf' (f \<oplus> r') P P' a c"
  assumes "\<And>rv rv'. r' rv rv'
           \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (R rv) (R' rv') (b rv) (d rv')"
  assumes "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows   "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  by (rule corres_splitEE; rule assms)

lemmas vmsz_aligned_imp_aligned
    = vmsz_aligned_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN is_aligned_weaken]

lemma arch_decodeInvocation_corres:
notes check_vp_inv[wp del] check_vp_wpR[wp] [[goals_limit = 1]]
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
  unfolding arch_decode_invocation_def ARM_HYP_H.decodeInvocation_def
            decodeARMMMUInvocation_def decode_mmu_invocation_def
  apply (cases arch_cap)
       apply (simp add: isCap_simps Let_def split del: if_split)
       apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel ARMASIDPoolAssign")
        apply (clarsimp  split: invocation_label.split arch_invocation_label.split)
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
           apply (rule_tac P="\<lambda>s. asid_table (asid_high_bits_of word2) = Some word1 \<longrightarrow> asid_pool_at word1 s"
                    and P'="pspace_aligned' and pspace_distinct'" in corres_inst)
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
                       free_asid_select_def o_def returnOk_liftE[symmetric] split del: if_split)
            apply (thin_tac "fst a \<notin> b \<and> P" for a b P)
            apply (case_tac "isUntypedCap a \<and> capBlockSize a = objBits (makeObject::asidpool)
                             \<and> \<not> capIsDevice a")
             prefer 2
             apply (rule corres_guard_imp)
               apply (rule corres_trivial)
               apply (case_tac ad, simp_all add: isCap_simps
                                      split del: if_split)[1]
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
      apply (simp add: null_def split_def asid_high_bits_def
                       word_le_make_less)
      apply (subst hd_map, assumption)
    (* need abstract guard to show list nonempty *)
      apply (simp add: word_le_make_less)
      apply (subst ucast_ucast_len)
       apply (drule hd_in_set)
       apply simp
      apply fastforce
     apply (simp add: isCap_simps split del: if_split)
     apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageMap")
      apply (rename_tac dev frame_ptr cap_rights vmpage_size map_data)
      apply (case_tac "\<not>(2 < length args \<and> excaps \<noteq> [])")
       apply (clarsimp simp: Let_def split: list.split)
      apply (simp add: Let_def neq_Nil_conv)
      apply (elim exE conjE)
      apply (rename_tac pd_cap pd_cap_cnode pd_cap_slot excaps_rest)
      apply (clarsimp split: list.split, intro conjI impI allI; clarsimp)
      apply (rename_tac vaddr rights_mask attr pd_cap' excaps'_rest args_rest)
      apply (rule corres_guard_imp)
        apply (rule_tac P="\<nexists>pd asid. pd_cap = cap.ArchObjectCap (arch_cap.PageDirectoryCap pd (Some asid))"
                 in corres_symmetric_bool_cases[where Q=\<top> and Q'=\<top>, OF refl])
         apply (case_tac pd_cap; clarsimp; rename_tac pd_acap pd_acap'; case_tac pd_acap; clarsimp)
        apply (rule corres_splitEE'[where r'="(=)" and P=\<top> and P'=\<top>])
           apply (clarsimp simp: corres_returnOkTT)
          apply (rule_tac F="pd_cap = cap.ArchObjectCap (arch_cap.PageDirectoryCap (fst rv) (Some (snd rv)))"
                   in corres_gen_asm)
          apply (clarsimp cong: option.case_cong)
          apply (rename_tac vspace asid)
          apply wpfix \<comment> \<open>get asid and vspace parameters in schematic preconditions\<close>
          apply (rule_tac P="map_data = None \<and> kernel_base \<le> vaddr + 2 ^ pageBitsForSize vmpage_size - 1
                             \<or> (\<exists>asid' vaddr'. map_data = Some (asid', vaddr') \<and> (asid',vaddr') \<noteq> (asid,vaddr))"
                   in corres_symmetric_bool_cases[where Q=\<top> and Q'=\<top>, OF refl])
           apply (erule disjE
                  ; clarsimp simp: whenE_def kernel_base_def pptrBase_def ARM_HYP.pptrBase_def
                            split: option.splits)
          apply clarsimp
          apply (rule corres_splitEE'[where r'=dc and P=\<top> and P'=\<top>])
             apply (case_tac map_data
                    ; clarsimp simp: whenE_def kernel_base_def pptrBase_def ARM_HYP.pptrBase_def
                                     corres_returnOkTT)
            \<comment> \<open>pd=undefined as vspace_at_asid not used in find_pd_for_asid_corres and avoid unresolved schematics\<close>
            apply (rule corres_splitEE'[
                          OF corres_lookup_error[OF find_pd_for_asid_corres[where pd=undefined, OF refl]]])
              apply (rule whenE_throwError_corres; simp)
              apply (rule corres_splitEE'[where r'=dc, OF checkVPAlignment_corres])
                apply (rule corres_splitEE'[OF createMappingEntries_corres]
                       ; simp add: mask_vmrights_corres vm_attributes_corres)
                  apply (rule corres_splitEE'[OF ensureSafeMapping_corres], assumption)
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
        apply (clarsimp simp: valid_cap_simps cap_aligned_def)
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
     apply (cases "ARM_HYP_H.isPageFlushLabel (invocation_type (mi_label mi))")
      apply (clarsimp simp: ARM_HYP_H.isPageFlushLabel_def split del: if_split)
      apply (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: if_split)
         apply (rule decodeARMPageFlush_corres,
                clarsimp simp: ARM_HYP_H.isPageFlushLabel_def)+
     apply (clarsimp simp: ARM_HYP_H.isPageFlushLabel_def split del: if_split)
     apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageGetAddress")
      apply simp
      apply (rule corres_returnOk)
      apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
     subgoal by (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: if_split)
    apply (simp add: isCap_simps Let_def split del: if_split)
    apply (simp split: invocation_label.split arch_invocation_label.splits split del: if_split)
    apply (intro conjI impI allI)
     apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
     apply (clarsimp simp: neq_Nil_conv)
     apply (rule whenE_throwError_corres_initial, simp+)
     apply (simp split: cap.split arch_cap.split option.split,
            intro conjI allI impI, simp_all)[1]
     apply (rule whenE_throwError_corres_initial, simp)
      apply (simp add: kernel_base_def ARM_HYP.pptrBase_def pptrBase_def)
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE)
          apply (rule corres_lookup_error)
          apply (rule find_pd_for_asid_corres [OF refl])
         apply (rule whenE_throwError_corres, simp, simp)
         apply (rule corres_splitEE)
            apply simp
            apply (rule get_master_pde_corres')
           apply (simp add: unlessE_whenE)
           apply (rule corres_splitEE)

              apply (rule corres_whenE)
                apply clarsimp
                apply (case_tac oldpde
                       ; clarsimp simp: master_pde_relation_def isSuperSection_def' split: if_split_asm)
               apply (rule corres_trivial)
               apply simp
              apply simp
             apply (rule corres_trivial)
             apply (rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def page_table_invocation_map_def)
             apply (simp add: shiftr_shiftl1)
            apply (wp whenE_wp get_master_pde_wp getPDE_wp find_pd_for_asid_inv
                   | wp (once) hoare_drop_imps)+
      apply (fastforce simp: valid_cap_def mask_def)
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
     apply (clarsimp simp: cte_wp_at_caps_of_state cap_rights_update_def acap_rights_update_def)
     apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
    apply (clarsimp simp: cte_wp_at_ctes_of cap_rights_update_def acap_rights_update_def
                          cte_wp_at_caps_of_state)
    apply (drule pspace_relation_ctes_ofI[OF _ caps_of_state_cteD, rotated],
           erule invs_pspace_aligned', clarsimp+)
    apply (simp add: isCap_simps)
   apply (simp add: isCap_simps split del: if_split)
   apply (cases "ARM_HYP_H.isPDFlushLabel (invocation_type (mi_label mi))")
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
       apply (clarsimp simp: kernel_base_def ARM_HYP.pptrBase_def pptrBase_def)
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
            apply (clarsimp simp: archinv_relation_def page_directory_invocation_map_def flush_type_map)+
         apply (clarsimp simp: state_relation_def)
         apply (frule pspace_relation_cte_wp_at, simp add: cte_wp_at_caps_of_state, simp+)
         apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (drule(1) valid_global_refsD_with_objSize)
         subgoal by (clarsimp simp: is_page_cap_def split: cap.split_asm)
        apply (wp hoare_drop_imps)+
     apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_cap_simps mask_2pm1
                           valid_arch_state_def valid_arch_caps_def linorder_not_le
                    split: option.splits)
    apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                   split: option.splits)
   apply clarsimp
  apply (simp, rule corres_guard_imp[OF decodeARMVCPUInvocation_corres]; simp)
  done


lemma invokeVCPUInjectIRQ_corres:
  "corres (=) (vcpu_at v) (vcpu_at' v)
        (do y \<leftarrow> invoke_vcpu_inject_irq v index virq;
                 return []
         od)
        (invokeVCPUInjectIRQ v index virq)"
  unfolding invokeVCPUInjectIRQ_def invoke_vcpu_inject_irq_def
  apply (clarsimp simp: bind_assoc)
  apply (corresKsimp corres: getObject_vcpu_corres setObject_VCPU_corres wp: get_vcpu_wp)
  apply clarsimp
  done

lemma [wp]:"no_fail \<top> getSCTLR"
  by (clarsimp simp: getSCTLR_def)

lemma invokeVCPUReadReg_corres:
  "corres (=) (vcpu_at v) (vcpu_at' v and no_0_obj')
                 (invoke_vcpu_read_register v r)
                 (invokeVCPUReadReg v r)"
  unfolding invoke_vcpu_read_register_def invokeVCPUReadReg_def read_vcpu_register_def readVCPUReg_def
  apply (rule corres_discard_r)
  apply (corresKsimp corres: getObject_vcpu_corres wp: get_vcpu_wp)
  apply (clarsimp simp: vcpu_relation_def split: option.splits)
  apply (wpsimp simp: getCurThread_def)+
  done


lemma invokeVCPUWriteReg_corres:
  "corres (=) (vcpu_at vcpu) (vcpu_at' vcpu and no_0_obj')
        (do y \<leftarrow> invoke_vcpu_write_register vcpu r v;
                 return []
         od)
        (invokeVCPUWriteReg vcpu r v)"
  unfolding invokeVCPUWriteReg_def invoke_vcpu_write_register_def write_vcpu_register_def
            writeVCPUReg_def
  apply (rule corres_discard_r)
  apply (corresKsimp corres: setObject_VCPU_corres getObject_vcpu_corres wp: get_vcpu_wp)
  subgoal by (auto simp: vcpu_relation_def split: option.splits)
  apply (wpsimp simp: getCurThread_def)+
  done

lemma archThreadSet_VCPU_Some_corres[corres]:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
    (arch_thread_set (tcb_vcpu_update (\<lambda>_. Some v)) t)
    (archThreadSet (atcbVCPUPtr_update (\<lambda>_. Some v)) t)"
  apply (rule archThreadSet_corres)
  apply (simp add: arch_tcb_relation_def)
  done

crunches dissociateVCPUTCB
  for no_0_obj'[wp]: no_0_obj'
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  (simp: crunch_simps wp: crunch_wps)

lemma vcpuSwitch_corres'':
  "vcpu' = vcpu
   \<Longrightarrow> corres dc (\<lambda>s. (vcpu \<noteq> None \<longrightarrow> vcpu_at  (the vcpu) s) \<and> valid_arch_state s)
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             (vcpu_switch vcpu)
             (vcpuSwitch vcpu')"
  apply (rule stronger_corres_guard_imp, rule vcpuSwitch_corres')
    by (clarsimp simp: valid_arch_state_def is_vcpu_def obj_at_def)+

lemma associateVCPUTCB_corres:
  "corres (=) (invs and vcpu_at v and tcb_at t)
               (invs' and vcpu_at' v and tcb_at' t)
               (do y \<leftarrow> associate_vcpu_tcb v t;
                   return []
                od)
               (associateVCPUTCB v t)"
  unfolding associate_vcpu_tcb_def associateVCPUTCB_def
  apply (clarsimp simp: bind_assoc)
  apply (corresKsimp search: getObject_vcpu_corres setObject_VCPU_corres vcpuSwitch_corres''
                        wp: get_vcpu_wp getVCPU_wp hoare_vcg_imp_lift'
                      simp: vcpu_relation_def)
      apply (rule_tac Q="\<lambda>_. invs and tcb_at t" in hoare_strengthen_post)
       apply wp
      apply clarsimp
      apply (rule conjI)
       apply (clarsimp simp: vcpu_relation_def)
      apply (rule conjI)
       apply (frule (1) sym_refs_vcpu_tcb, fastforce)
       apply (fastforce simp: obj_at_def)+
     apply (wpsimp)+
     apply (rule_tac Q="\<lambda>_. invs' and tcb_at' t" in hoare_strengthen_post)
      apply wpsimp
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (frule valid_objs_valid_vcpu'[rotated], fastforce)
      apply (simp add: valid_vcpu'_def typ_at_tcb')
      apply (clarsimp simp: typ_at_to_obj_at_arches obj_at'_def)
     apply (fastforce simp: typ_at_to_obj_at_arches obj_at'_def)
    apply (corresKsimp wp: arch_thread_get_wp getObject_tcb_wp
                    simp: archThreadGet_def)+
  apply (simp add: vcpu_relation_def)
  apply (intro allI conjI impI;
    (solves \<open>clarsimp simp: obj_at_def\<close>)?)
    apply (frule (1) sym_refs_tcb_vcpu, fastforce)
    apply (clarsimp simp: obj_at_def)
   apply (frule (1) sym_refs_vcpu_tcb, fastforce)
   apply (clarsimp simp: obj_at_def)
  apply (frule invs_arch_state)
  apply (clarsimp simp: valid_arch_state_def obj_at_def is_vcpu_def)
  apply normalise_obj_at'
  apply (drule valid_objs_valid_tcb'[rotated], fastforce)
  apply (clarsimp simp: valid_tcb'_def valid_arch_tcb'_def invs_no_0_obj')
  apply (drule valid_objs_valid_vcpu'[rotated], fastforce)
  apply (fastforce simp: valid_vcpu'_def typ_at_tcb')
  done

lemma invokeVCPUAckVPPI_corres:
  "corres (=) (vcpu_at vcpu) (vcpu_at' vcpu)
        (do y \<leftarrow> invoke_vcpu_ack_vppi vcpu vppi;
                 return []
         od)
        (invokeVCPUAckVPPI vcpu vppi)"
  unfolding invokeVCPUAckVPPI_def invoke_vcpu_ack_vppi_def write_vcpu_register_def
            writeVCPUReg_def
  by (corresKsimp corres: setObject_VCPU_corres getObject_vcpu_corres wp: get_vcpu_wp)
     (auto simp: vcpu_relation_def split: option.splits)

lemma performARMVCPUInvocation_corres:
  notes inv_corres = invokeVCPUInjectIRQ_corres invokeVCPUReadReg_corres
                     invokeVCPUWriteReg_corres associateVCPUTCB_corres
                     invokeVCPUAckVPPI_corres
  shows "corres (=) (einvs and ct_active and valid_vcpu_invocation iv)
                       (invs' and ct_active' and valid_vcpuinv' (vcpu_invocation_map iv))
                (perform_vcpu_invocation iv) (performARMVCPUInvocation (vcpu_invocation_map iv))"
  unfolding perform_vcpu_invocation_def performARMVCPUInvocation_def
  apply (cases iv; simp add: vcpu_invocation_map_def valid_vcpu_invocation_def valid_vcpuinv'_def)
     apply (rule inv_corres [THEN corres_guard_imp]; simp add: invs_no_0_obj')+
  done

lemma arch_performInvocation_corres:
  assumes "archinv_relation ai ai'"
  shows   "corres (dc \<oplus> (=))
                  (einvs and ct_active and valid_arch_inv ai and schact_is_rct)
                  (invs' and ct_active' and valid_arch_inv' ai' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
                  (arch_perform_invocation ai) (Arch.performInvocation ai')"
proof -
  note invocation_corres =  performPageTableInvocation_corres performPageDirectoryInvocation_corres
                            performASIDControlInvocation_corres performASIDPoolInvocation_corres performPageInvocation_corres performARMVCPUInvocation_corres
  from assms show ?thesis
  unfolding arch_perform_invocation_def ARM_HYP_H.performInvocation_def performARMMMUInvocation_def
  apply clarsimp
  apply (cases ai; clarsimp simp add: archinv_relation_def liftE_bind_return_bindE_returnOk[symmetric])
       by (rule corres_underlying_split[where r'=dc, OF _ corres_trivial]
             | rule invocation_corres[THEN corres_guard_imp]
             | (fastforce simp: valid_arch_inv_def valid_arch_inv'_def)+
             | wpsimp+)+
qed


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
   apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
  apply clarsimp
  done

crunches writeVCPUReg, readVCPUReg, performARMVCPUInvocation
  for tcb_at'[wp]: "tcb_at' p"

lemma invokeArch_tcb_at':
  "\<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p\<rbrace>
     Arch.performInvocation ai
   \<lbrace>\<lambda>rv. tcb_at' p\<rbrace>"
  apply (simp add: ARM_HYP_H.performInvocation_def)
  apply (cases ai; simp add: performARMMMUInvocation_def)
       apply (wp, clarsimp simp: pred_tcb_at')
      apply (wp, clarsimp simp: pred_tcb_at')
     apply (wp, clarsimp simp: st_tcb_strg'[rule_format])
    apply (wp performASIDControlInvocation_tcb_at', clarsimp simp: valid_arch_inv'_def)
   apply (wp, clarsimp simp: pred_tcb_at')
  apply wpsimp
  done

crunch pspace_no_overlap'[wp]: setThreadState "pspace_no_overlap' w s"
  (simp: unless_def)

lemma sts_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  by (wp ex_cte_cap_to'_pres)

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

crunch vs_entry_align'[wp]:
  threadSet "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (wp: crunch_wps)

crunch vs_entry_align'[wp]:
  addToBitmap "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (wp: crunch_wps)

lemma tcbSchedEnqueue_vs_entry_align[wp]:
 "\<lbrace>\<lambda>s. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p s\<rbrace>
   tcbSchedEnqueue pa
  \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def tcbQueuePrepend_def setQueue_def)
  by (wp unless_wp | simp)+

crunch vs_entry_align[wp]:
  setThreadState  "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (wp: crunch_wps)

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
   apply simp
  apply (rename_tac vcpui)
  apply (case_tac vcpui; wpsimp simp: valid_vcpuinv'_def)
  done

lemma less_pptrBase_valid_pde_offset':
  "\<lbrakk> vptr < pptrBase; x = 0 \<or> is_aligned vptr 25; x \<le> 0x0F \<rbrakk>
     \<Longrightarrow> valid_pde_mapping_offset' (((x * 8) + (vptr >> 21 << 3)) && mask pdBits)"
  apply (clarsimp simp: ARM_HYP.pptrBase_def pptrBase_def pdBits_def pageBits_def
                        valid_pde_mapping_offset'_def pd_asid_slot_def pt_index_bits_def
                        vspace_bits_defs)
  apply (drule word_le_minus_one_leq, simp)
  apply (drule le_shiftr[where u=vptr and n=21])
  apply (subst(asm) iffD2[OF mask_eq_iff_w2p])
    apply (simp add: word_size)
   apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem])
  apply (erule disjE)
   apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem])
  apply (frule arg_cong[where f="\<lambda>v. v && mask 7"])
  apply (subst(asm) field_simps, subst(asm) is_aligned_add_helper[where n=7],
         rule is_aligned_shiftl)
    apply (rule is_aligned_shiftr, simp)
   apply simp
   apply (simp add: unat_arith_simps iffD1[OF unat_mult_lem])
  apply (simp add: shiftl_t2n unat_arith_simps iffD1[OF unat_mult_lem])
  done

lemmas less_pptrBase_valid_pde_offset''
    = less_pptrBase_valid_pde_offset'[where x=0, simplified pd_bits_def pdBits_def pdeBits_def, simplified]

lemma createMappingEntries_valid_pde_slots':
  "\<lbrace>K (vmsz_aligned' vptr sz \<and> is_aligned pd pdBits
                \<and> vptr < pptrBase)\<rbrace>
     createMappingEntries base vptr sz vm_rights attrib pd
   \<lbrace>\<lambda>rv s. valid_pde_slots' rv\<rbrace>,-"
  apply (simp add: createMappingEntries_def valid_pde_slots'_def)
  apply (cases sz, simp_all)
     apply (wp | simp)+
   apply (clarsimp simp: lookup_pd_slot_def Let_def mask_add_aligned vspace_bits_defs)
   apply (erule less_pptrBase_valid_pde_offset'')
  apply (rule hoare_pre, wp)
  apply (clarsimp simp: vmsz_aligned'_def superSectionPDEOffsets_def vspace_bits_defs del: ballI)
  apply (simp add: lookup_pd_slot_def Let_def vspace_bits_defs)
  apply (clarsimp simp: upto_enum_step_def linorder_not_less pd_bits_def
                        lookup_pd_slot_def Let_def field_simps
                        mask_add_aligned)
  apply (erule less_pptrBase_valid_pde_offset' [simplified pdBits_def pdeBits_def, simplified])
   apply simp
  apply simp
  done

lemma inv_ASIDPool: "inv ASIDPool = (\<lambda>v. case v of ASIDPool a \<Rightarrow> a)"
  apply (rule ext)
  apply (case_tac v)
  apply simp
  apply (rule inv_f_f, rule inj_onI)
  apply simp
  done

lemma findPDForASID_aligned[wp]:
  "\<lbrace>valid_objs'\<rbrace> findPDForASID p \<lbrace>\<lambda>rv s. is_aligned rv pd_bits\<rbrace>,-"
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
   \<lbrace>\<lambda>rv s. valid_pde_mapping_offset' (rv + (vptr >> 21 << 3) && mask pd_bits)\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_strengthen_postE_R, rule findPDForASID_aligned)
  apply (simp add: mask_add_aligned vspace_bits_defs)
  apply (erule less_pptrBase_valid_pde_offset'')
  done

lemma eq_arch_update':
  "ArchObjectCap cp = cteCap cte \<Longrightarrow> is_arch_update' (ArchObjectCap cp) cte"
  by (clarsimp simp: is_arch_update'_def isCap_simps)

lemma lookupPTSlot_page_table_at':
  "\<lbrace>valid_objs'\<rbrace> lookupPTSlot pd vptr
  \<lbrace>\<lambda>rv s. page_table_at' (rv && ~~ mask pt_bits) s\<rbrace>,-"
  apply (simp add:lookupPTSlot_def)
  apply (wp getPDE_wp|wpc|simp add:checkPTAt_def)+
  apply (clarsimp simp:ptBits_def lookup_pt_slot_no_fail_def pt_bits_def pte_bits_def pageBits_def mask_def[of 9])
  apply (subst vaddr_segment_nonsense3[unfolded pt_bits_def pte_bits_def,simplified])
   apply (simp add:page_table_at'_def pageBits_def pt_bits_def pte_bits_def)
  apply simp
  done

lemma findPDForASID_page_directory_at':
  notes checkPDAt_inv[wp del]
  shows "\<lbrace>\<top>\<rbrace> findPDForASID asiv
    \<lbrace>\<lambda>rv s. page_directory_at' (lookup_pd_slot rv vptr && ~~ mask pd_bits) s\<rbrace>,-"
  apply (simp add:findPDForASID_def)
   apply (wp getASID_wp|simp add:checkPDAt_def | wpc)+
  apply (clarsimp simp:lookup_pd_slot_def pdBits_def pageBits_def pte_bits_def pt_bits_def pde_bits_def pd_bits_def)
  apply (subst vaddr_segment_nonsense[unfolded pd_bits_def pde_bits_def,simplified])
   apply (simp add:page_directory_at'_def pdBits_def pageBits_def pd_bits_def pde_bits_def)
  apply simp
  done

definition "slots_duplicated_ensured \<equiv> \<lambda>m s. case m of
  Inl (pte, xs) \<Rightarrow> (case pte of
    pte.LargePagePTE _ _ _ _ \<Rightarrow> \<exists>p. xs = [p, p+8 .e. p + mask 7] \<and> is_aligned p 7
        \<and> page_table_at' (p && ~~ mask ptBits) s
    | pte.InvalidPTE  \<Rightarrow> False
    | _ \<Rightarrow> \<exists>p. xs = [p]
      \<and> page_table_at' (p && ~~ mask ptBits) s)
  | Inr (pde, xs) \<Rightarrow> (case pde of
    pde.SuperSectionPDE _ _ _ _ \<Rightarrow> \<exists>p. xs = [p, p+8 .e. p + mask 7] \<and> is_aligned p 7
        \<and> page_directory_at' (p && ~~ mask pdBits) s \<and> is_aligned p 7
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
     apply (simp add:slots_duplicated_ensured_def hoare_FalseE_R)+
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
   apply (clarsimp simp add: vspace_bits_defs)
  apply (case_tac b)
  apply (case_tac a)
   apply (simp add:slots_duplicated_ensured_def hoare_FalseE_R | wp)+
   apply (rule hoare_pre)
    apply (rule_tac P = "\<exists>p. ba = [p]" and
      P' = "\<lambda>s. \<exists>p. ba = [p] \<and> page_directory_at' (p && ~~ mask pdBits) s" in hoare_gen_asmE)
    apply (clarsimp simp:mapME_singleton)
    apply (wp getPDE_wp|wpc|clarsimp)+
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
  "\<lbrace>\<lambda>s. is_aligned vptr 16 \<and> valid_objs' s\<rbrace> lookupPTSlot pd vptr \<lbrace>\<lambda>p s. is_aligned p 7\<rbrace>,-"
  apply (simp add:lookupPTSlot_def)
  apply (wp getPDE_wp |wpc|simp)+
  apply (clarsimp simp:obj_at'_real_def ko_wp_at'_def)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp:projectKO_opt_pde
    split:Structures_H.kernel_object.splits arch_kernel_object.splits)
  apply (simp add:valid_obj'_def lookup_pt_slot_no_fail_def)
  apply (rule aligned_add_aligned)
    apply (erule is_aligned_ptrFromPAddr_n)
    apply (simp add: pt_bits_def pte_bits_def)
   apply (rule is_aligned_shiftl)
   apply (rule is_aligned_andI1)
   apply (rule is_aligned_shiftr)
   apply (simp add: pte_bits_def pageBits_def pt_bits_def)
  apply (simp add: pt_bits_def)
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
     apply (rule_tac Q' = "\<lambda>p s. is_aligned p 7 \<and> page_table_at' (p && ~~ mask pt_bits) s"
                  in hoare_strengthen_postE_R)
      apply (wp lookupPTSlot_aligned lookupPTSlot_page_table_at'
             | simp add: vspace_bits_defs largePagePTEOffsets_def superSectionPDEOffsets_def)+
     apply (rename_tac rv s)
     apply (rule_tac x = rv in exI)
     apply clarsimp
     apply (frule is_aligned_no_wrap'[where off = "0x78"])
      apply simp
     apply (drule upto_enum_step_shift[where n = 7 and m = 3,simplified])
     apply (clarsimp simp:mask_def add.commute upto_enum_step_def)
    apply wp+
  apply (intro conjI impI; clarsimp)
    apply ((clarsimp simp: vmsz_aligned_def slots_duplicated_ensured_def)+)[2]
  apply (drule lookup_pd_slot_aligned_6)
   apply (simp add:pdBits_def pageBits_def pd_bits_def pde_bits_def)
  apply (clarsimp simp:slots_duplicated_ensured_def)
  apply (rule_tac x = "(lookup_pd_slot pd vptr)" in exI)
  apply (clarsimp simp: superSectionPDEOffsets_def Let_def pde_bits_def)
  apply (frule is_aligned_no_wrap'[where off = "0x78" and sz = 7])
   apply simp
  apply (drule upto_enum_step_shift[where n = 7 and m = 3,simplified])
  apply (clarsimp simp:mask_def add.commute upto_enum_step_def)
  done

lemma arch_decodeARMPageFlush_wf:
  "ARM_HYP_H.isPageFlushLabel (invocation_type label) \<Longrightarrow>
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
  apply (wpsimp wp: whenE_throwError_wp simp: valid_arch_inv'_def valid_page_inv'_def if_apply_def2)
  done

lemma zobj_refs_maksCapRights[simp]:
  "zobj_refs' (maskCapRights R cap) = zobj_refs' cap"
  by (cases cap; clarsimp simp: maskCapRights_def ARM_HYP_H.maskCapRights_def Let_def isCap_simps)

lemma arch_decodeInvocation_wf[wp]:
  notes ensureSafeMapping_inv[wp del]
  shows "\<lbrace>invs' and valid_cap' (ArchObjectCap arch_cap) and
    cte_wp_at' ((=) (ArchObjectCap arch_cap) o cteCap) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' ((=) (fst x) o cteCap) (snd x) s) and
    sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
   Arch.decodeInvocation label args cap_index slot arch_cap excaps
   \<lbrace>valid_arch_inv'\<rbrace>,-"
  apply (cases arch_cap)
       apply (simp add: decodeARMMMUInvocation_def ARM_HYP_H.decodeInvocation_def
                        Let_def split_def isCap_simps
                  cong: if_cong split del: if_split)
       apply (rule hoare_pre)
        apply (wpsimp wp: whenE_throwError_wp getASID_wp)
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
      apply (simp add: decodeARMMMUInvocation_def ARM_HYP_H.decodeInvocation_def
                       Let_def split_def isCap_simps
                 cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong
                       list.case_cong prod.case_cong
            split del: if_split)
      apply (rule hoare_pre)
       apply (wpsimp wp: whenE_throwError_wp ensureEmptySlot_stronger
                   simp: valid_arch_inv'_def valid_aci'_def is_aligned_shiftl_self
              split_del: if_split)
                apply (rule_tac Q'=
                            "\<lambda>rv. K (fst (hd [p\<leftarrow>assocs asidTable . fst p \<le> 2 ^ asid_high_bits - 1
                                          \<and> snd p = None])
                                     << asid_low_bits \<le> 2 ^ asid_bits - 1) and
                                  real_cte_at' rv and
                                  ex_cte_cap_to' rv and
                                  cte_wp_at'
                                    (\<lambda>cte. \<exists>idx. cteCap cte = (UntypedCap False frame pageBits idx))
                                    (snd (excaps!0)) and
                                  sch_act_simple and
                                  (\<lambda>s. descendants_of' (snd (excaps!0)) (ctes_of s) = {}) "
                                  in hoare_strengthen_postE_R)
                 apply (simp add: lookupTargetSlot_def)
                 apply wp
                apply (clarsimp simp: cte_wp_at_ctes_of)
               apply (simp split del: if_split)
               apply (wpsimp wp: ensureNoChildren_sp whenE_throwError_wp)+
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
       apply (case_tac cteb)
       apply clarsimp
       apply (drule ctes_of_valid_cap', fastforce)
       apply assumption
      apply (simp add: ex_cte_cap_to'_def cte_wp_at_ctes_of)
      apply (drule_tac t="cteCap ctea" in sym, simp)
      apply (drule_tac t="cteCap cte" in sym, clarsimp)
      apply (rule_tac x=ba in exI)
      apply simp
     \<comment> \<open>PageCap\<close>
     apply (simp add: decodeARMMMUInvocation_def ARM_HYP_H.decodeInvocation_def
                      Let_def split_def isCap_simps
                cong: if_cong split del: if_split)
     apply (cases "invocation_type label = ArchInvocationLabel ARMPageMap")
      apply (rename_tac word vmrights vmpage_size option)
      apply (simp add: split_def split del: if_split
                 cong: list.case_cong prod.case_cong)
      apply (rule hoare_pre)
       apply (wpsimp simp: valid_arch_inv'_def valid_page_inv'_def)+
             apply (rule hoare_vcg_conj_lift_R,(wp ensureSafeMapping_inv)[1])+
             apply (wpsimp wp: whenE_throwError_wp checkVP_wpR hoare_vcg_const_imp_lift_R hoare_drop_impE_R
                               ensureSafeMapping_valid_slots_duplicated'
                               createMappingEntries_valid_pde_slots' findPDForASID_page_directory_at'
                         simp: valid_arch_inv'_def valid_page_inv'_def)+
      apply (clarsimp simp: neq_Nil_conv invs_valid_objs' linorder_not_le
                            cte_wp_at_ctes_of)
      apply (drule ctes_of_valid', fastforce)+
      apply (case_tac option; clarsimp, drule_tac t="cteCap cte" in sym, simp)
       apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def
                             is_arch_update'_def isCap_simps capAligned_def vmsz_aligned'_def
                       cong: conj_cong)
       apply (rule conjI)
        apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size, simp_all)[1]
       apply (simp add: vmsz_aligned_def)

       apply (rule conjI)
        apply (erule order_le_less_trans[rotated])
        apply (erule is_aligned_no_overflow'[simplified field_simps])
       apply (clarsimp simp: page_directory_at'_def lookup_pd_slot_eq)+
      apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def
                            is_arch_update'_def isCap_simps capAligned_def vmsz_aligned'_def
                      cong: conj_cong)

      apply (rule conjI)
       apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size, simp_all)[1]
      apply (simp add: vmsz_aligned_def)
      apply (clarsimp simp: page_directory_at'_def lookup_pd_slot_eq)

     apply (cases "invocation_type label = ArchInvocationLabel ARMPageUnmap")
      apply (simp split del: if_split)
      apply (rule hoare_pre, wp)
      apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
      apply (thin_tac "Ball S P" for S P)
      apply (erule cte_wp_at_weakenE')
      apply (clarsimp simp: is_arch_update'_def isCap_simps)
     apply (cases "ARM_HYP_H.isPageFlushLabel (invocation_type label)")
      apply (clarsimp simp: ARM_HYP_H.isPageFlushLabel_def split: invocation_label.splits arch_invocation_label.splits)
         apply (rule arch_decodeARMPageFlush_wf,
                clarsimp simp: ARM_HYP_H.isPageFlushLabel_def)+
     apply (cases "invocation_type label = ArchInvocationLabel ARMPageGetAddress")
      apply (simp split del: if_split)
      apply (rule hoare_pre, wp)
      apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
     apply (simp add: ARM_HYP_H.isPageFlushLabel_def throwError_R'
               split: invocation_label.split_asm arch_invocation_label.split_asm)
    \<comment> \<open>PageTableCap\<close>
    apply (simp add: decodeARMMMUInvocation_def ARM_HYP_H.decodeInvocation_def
                     Let_def split_def isCap_simps vs_entry_align_def
                cong: if_cong list.case_cong invocation_label.case_cong arch_invocation_label.case_cong prod.case_cong
                split del: if_split)
    apply (rename_tac word option)
    apply (rule hoare_pre)
     apply (wp whenE_throwError_wp isFinalCapability_inv getPDE_wp | wpc
            | simp add: valid_arch_inv'_def valid_pti'_def unlessE_whenE
            | rule_tac x="fst p" in hoare_imp_eq_substR)+
             apply (rule_tac Q'="\<lambda>b c. ko_at' ARM_HYP_H.pde.InvalidPDE (b + (hd args >> 21 << 3)) c \<longrightarrow>
                          cte_wp_at'
                           (is_arch_update'
                             (capability.ArchObjectCap (arch_capability.PageTableCap word (Some (snd p, hd args >> 21 << 21)))))
                           slot c \<and>
                          c \<turnstile>' capability.ArchObjectCap (arch_capability.PageTableCap word (Some (snd p, hd args >> 21 << 21))) \<and>
                          is_aligned (addrFromPPtr word) ptBits \<and>
                          valid_pde_mapping_offset' (b + (hd args >> 21 << 3) && mask pd_bits)
                         " in hoare_strengthen_postE_R)
              apply (wp whenE_throwError_wp isFinalCapability_inv getPDE_wp | wpc
                     | simp add: valid_arch_inv'_def valid_pti'_def unlessE_whenE
                     | rule_tac x="fst p" in hoare_imp_eq_substR
                     | rule hoare_drop_impE_R)+
             apply (clarsimp simp: ko_wp_at'_def obj_at'_real_def)
             apply (clarsimp simp: projectKO_opt_pde vs_entry_align_def vspace_bits_defs
                            split: Structures_H.kernel_object.splits arch_kernel_object.splits)
            apply ((wp whenE_throwError_wp isFinalCapability_inv
                    | wpc | simp add: valid_arch_inv'_def valid_pti'_def if_apply_def2
                    | rule hoare_drop_imp)+)[19]
    apply (clarsimp simp: linorder_not_le isCap_simps cte_wp_at_ctes_of)
    apply (frule eq_arch_update')
    apply (case_tac option; clarsimp)
    apply (drule_tac t="cteCap ctea" in sym, simp)
    apply (clarsimp simp: is_arch_update'_def isCap_simps valid_cap'_def capAligned_def)

    apply (thin_tac "Ball S P" for S P)+
    apply (drule ctes_of_valid', fastforce)+
    apply (clarsimp simp: valid_cap'_def ptBits_def is_aligned_addrFromPPtr_n invs_valid_objs'
                          vs_entry_align_def and_not_mask[symmetric] vspace_bits_defs)
    apply (erule order_le_less_trans[rotated])
    apply (rule word_and_le2)
   \<comment> \<open>PageDirectoryCap\<close>
   apply (simp add: decodeARMMMUInvocation_def ARM_HYP_H.decodeInvocation_def isCap_simps Let_def)

   apply (cases "ARM_HYP_H.isPDFlushLabel (invocation_type label)", simp_all)
    apply (cases args; simp)
     apply wp
    apply (wpsimp wp: whenE_throwError_wp simp: valid_arch_inv'_def)
   apply wp

  supply if_split [split del]
  \<comment> \<open>VCPUCap\<close>
  apply (simp add: ARM_HYP_H.decodeInvocation_def decodeARMVCPUInvocation_def Let_def)
  apply (wpsimp wp: whenE_throwError_wp getVCPU_wp
              simp: decodeVCPUSetTCB_def decodeVCPUInjectIRQ_def Let_def
                    decodeVCPUReadReg_def decodeVCPUWriteReg_def decodeVCPUAckVPPI_def)
  apply (clarsimp simp: valid_arch_inv'_def valid_vcpuinv'_def null_def isCap_simps valid_cap'_def)
  apply (rename_tac vcpu s tcb)
  apply (clarsimp simp: neq_Nil_conv ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (rename_tac cref exc' cte')
  apply (frule_tac p=cref in ctes_of_valid', fastforce)
  apply (subgoal_tac "s \<turnstile>' ThreadCap tcb")
   prefer 2
   apply clarsimp
  apply (drule_tac t="cteCap cte'" in sym, simp)
  apply (rule conjI)
   apply (clarsimp simp: valid_cap'_def)
  apply (drule_tac t="cteCap cte" in sym, simp)
  by fastforce

crunch nosch[wp]: setMRs "\<lambda>s. P (ksSchedulerAction s)"
    (ignore: getRestartPC setRegister transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option
        mapM_wp'
   simp: split_def zipWithM_x_mapM)

crunches performARMMMUInvocation, performARMVCPUInvocation
  for nosch [wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_cte_inv getASID_wp)

lemmas setObject_cte_st_tcb_at' [wp] = setCTE_pred_tcb_at' [unfolded setCTE_def]

crunch st_tcb_at': performPageDirectoryInvocation, performPageTableInvocation, performPageInvocation,
            performASIDPoolInvocation "st_tcb_at' P t"
  (wp: crunch_wps getASID_wp getObject_cte_inv FalseI simp: crunch_simps)

crunch st_tcb_at': performARMVCPUInvocation "st_tcb_at' P t"
  (wp: crunch_wps simp: crunch_simps)

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
  apply (clarsimp simp:invs_valid_pspace' objBits_simps archObjSize_def
    range_cover_full descendants_range'_def2 isCap_simps)
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

crunch aligned': "Arch.finaliseCap" pspace_aligned'
  (wp: crunch_wps getASID_wp simp: crunch_simps)

lemmas arch_finalise_cap_aligned' = finaliseCap_aligned'

crunch distinct': "Arch.finaliseCap" pspace_distinct'
  (wp: crunch_wps getASID_wp simp: crunch_simps)

lemmas arch_finalise_cap_distinct' = finaliseCap_distinct'

crunch nosch [wp]: "Arch.finaliseCap" "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getASID_wp simp: crunch_simps updateObject_default_def)

crunch st_tcb_at' [wp]: "Arch.finaliseCap" "st_tcb_at' P t"
  (wp: crunch_wps getASID_wp simp: crunch_simps)

crunch typ_at' [wp]: "Arch.finaliseCap" "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps getASID_wp simp: crunch_simps)

crunch cte_wp_at':  "Arch.finaliseCap" "cte_wp_at' P p"
  (wp: crunch_wps getASID_wp simp: crunch_simps)

lemma invs_asid_table_strengthen':
  "invs' s \<and> asid_pool_at' ap s \<and> asid \<le> 2 ^ asid_high_bits - 1 \<longrightarrow>
   invs' (s\<lparr>ksArchState :=
            armKSASIDTable_update (\<lambda>_. ((armKSASIDTable \<circ> ksArchState) s)(asid \<mapsto> ap)) (ksArchState s)\<rparr>)"
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_global_refs'_def global_refs'_def)
  apply (clarsimp simp: valid_arch_state'_def)
  apply (clarsimp simp: valid_asid_table'_def ran_def)
  apply (rule conjI)
   apply (clarsimp split: if_split_asm)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: valid_pspace'_def)
  apply (simp add: valid_machine_state'_def split: option.splits prod.splits)
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
    apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1,simplified])
   apply (simp add:pageBits_def minUntypedSizeBits_def)
  apply (frule_tac cte="CTE (capability.UntypedCap False a b c) m" for a b c m in valid_global_refsD', clarsimp)
  apply (simp add: Int_commute)
  by (auto simp:empty_descendants_range_in' objBits_simps max_free_index_def
                    archObjSize_def asid_low_bits_def word_bits_def pageBits_def
                    range_cover_full descendants_range'_def2 is_aligned_mask
                    null_filter_descendants_of'[OF null_filter_simp']
                    valid_cap_simps' mask_def live'_def hyp_live'_def arch_live'_def)

lemma doFlush_underlying_memory[wp]:
  "\<lbrace> \<lambda>m'. underlying_memory m' p = um \<rbrace>
   doFlush flush_type vstart vend pstart
   \<lbrace> \<lambda>_ m'. underlying_memory m' p = um \<rbrace>"
  unfolding doFlush_def by(cases flush_type; wpsimp simp: Let_def)

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

lemma archThreadSet_ex_nonz_cap_to'[wp]:
  "archThreadSet f t \<lbrace>ex_nonz_cap_to' v\<rbrace>"
  unfolding ex_nonz_cap_to'_def cte_wp_at_ctes_of by wp

lemma assoc_invs':
  "\<lbrace>invs' and
    ko_at' (vcpu\<lparr>vcpuTCBPtr:= None\<rparr>) v and
    obj_at' (\<lambda>tcb. atcbVCPUPtr (tcbArch tcb) = None) t and
    ex_nonz_cap_to' v and ex_nonz_cap_to' t\<rbrace>
   do y \<leftarrow> archThreadSet (atcbVCPUPtr_update (\<lambda>_. Some v)) t;
      setObject v (vcpuTCBPtr_update (\<lambda>_. Some t) vcpu)
   od
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_tcb_valid_objs setObject_vcpu_valid_objs'
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_valid_arch' valid_bitmaps_lift sym_heap_sched_pointers_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb valid_arch_tcb'_def
        | wp (once) hoare_vcg_imp_lift)+
  apply (drule (1) valid_objs_valid_vcpu')
  apply (clarsimp simp: valid_vcpu'_def)
  apply (rule conjI)
   apply (clarsimp simp: typ_at_to_obj_at_arches obj_at'_def)
  apply (rule conjI)
   apply (clarsimp simp: typ_at_tcb' obj_at'_def)

  supply fun_upd_apply[simp]
  apply (clarsimp simp: hyp_live'_def arch_live'_def)
  apply (rule_tac rfs'="state_hyp_refs_of' s" in delta_sym_refs, assumption)
   apply (clarsimp split: if_split_asm)
   apply (clarsimp simp: state_hyp_refs_of'_def obj_at'_def projectKOs tcb_vcpu_refs'_def
                  split: option.splits if_split_asm)
  by (clarsimp simp: state_hyp_refs_of'_def obj_at'_def projectKOs split: option.splits if_split_asm)

lemma asUser_obj_at_vcpu[wp]:
  "\<lbrace>obj_at' (P :: vcpu \<Rightarrow> bool) t\<rbrace>
   asUser t' f
   \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
  apply (simp add: asUser_def threadGet_stateAssert_gets_asUser)
  apply (wpsimp wp: threadSet_ko_wp_at2' simp: obj_at'_real_def)
  apply (simp add: asUser_fetch_def projectKOs split: option.splits)
  done

lemma archThreadSet_obj_at'_vcpu[wp]:
  "archThreadSet f t \<lbrace>obj_at' (P::vcpu \<Rightarrow> bool) p\<rbrace>"
  unfolding archThreadSet_def
  by (wpsimp wp: obj_at_setObject2 simp: updateObject_default_def in_monad)

lemma asUser_atcbVCPUPtr[wp]:
  "asUser t' f \<lbrace>obj_at' (\<lambda>t. P (atcbVCPUPtr (tcbArch t))) t\<rbrace>"
  unfolding asUser_def threadGet_stateAssert_gets_asUser
  by (wpsimp simp: asUser_fetch_def obj_at'_def projectKOs atcbContextGet_def atcbContextSet_def)

lemma dissociateVCPUTCB_no_vcpu[wp]:
  "\<lbrace>\<lambda>s. t \<noteq> t' \<longrightarrow> obj_at' (\<lambda>tcb. atcbVCPUPtr (tcbArch tcb) = None) t s\<rbrace>
   dissociateVCPUTCB vcpu t' \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. atcbVCPUPtr (tcbArch tcb) = None) t\<rbrace>"
  unfolding dissociateVCPUTCB_def
  by (wpsimp wp: getVCPU_wp setObject_tcb_strongest simp: archThreadSet_def archThreadGet_def)

lemma dissociateVCPUTCB_no_tcb[wp]:
  "\<lbrace>ko_at' v vcpu\<rbrace> dissociateVCPUTCB vcpu tcb \<lbrace>\<lambda>rv. ko_at' (vcpuTCBPtr_update Map.empty v) vcpu\<rbrace>"
  unfolding dissociateVCPUTCB_def
  apply (wpsimp wp: obj_at_setObject3 getVCPU_wp
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def archThreadGet_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma dissociateVCPUTCB_ex_nonz_cap_to'[wp]:
  "dissociateVCPUTCB v' t \<lbrace>ex_nonz_cap_to' v\<rbrace>"
  unfolding ex_nonz_cap_to'_def cte_wp_at_ctes_of by wp

lemma vcpuTCBPtr_update_Some_vcpu_live[wp]:
  "\<lbrace>if vcpuPtr = vcpuPtr'
    then ko_wp_at' is_vcpu' vcpuPtr
    else ko_wp_at' (is_vcpu' and hyp_live') vcpuPtr\<rbrace>
   setObject vcpuPtr' (vcpuTCBPtr_update (\<lambda>_. Some tcbPtr) vcpu)
   \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') vcpuPtr\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps archObjSize_def)
   apply (clarsimp simp: vcpu_bits_def pageBits_def)
  by (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def hyp_live'_def
                     arch_live'_def
              split: if_splits)

lemma vcpuTCBPtr_update_Some_valid_arch_state'[wp]:
  "setObject vcpuPtr (vcpuTCBPtr_update (\<lambda>_. Some tptr) vcpu) \<lbrace>valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift
           | rule hoare_lift_Pf[where f=ksArchState])
  by (auto simp: pred_conj_def o_def ko_wp_at'_def)

definition associateVCPUTCB_helper where
  "associateVCPUTCB_helper vcpu v t = do
    y \<leftarrow> archThreadSet (atcbVCPUPtr_update (\<lambda>_. Some v)) t;
    setObject v (vcpuTCBPtr_update (\<lambda>_. Some t) vcpu)
   od"

lemma associateVCPUTCB_invs'[wp]:
  "\<lbrace>invs' and ex_nonz_cap_to' vcpu and ex_nonz_cap_to' tcb and vcpu_at' vcpu\<rbrace>
   associateVCPUTCB vcpu tcb
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: associateVCPUTCB_def)
  apply (subst bind_assoc[symmetric], fold associateVCPUTCB_helper_def)
  apply wpsimp
       apply (rule_tac Q="\<lambda>_ s. invs' s \<and> ko_wp_at' (is_vcpu' and hyp_live') vcpu s" in hoare_post_imp)
        apply simp
       apply (rule hoare_vcg_conj_lift)
        apply (wpsimp wp: assoc_invs'[folded associateVCPUTCB_helper_def])
       apply (clarsimp simp: associateVCPUTCB_helper_def)
       apply (wpsimp simp: vcpu_at_is_vcpu'[symmetric])+
     apply (wpsimp wp: getVCPU_wp)
    apply (rule_tac Q="\<lambda>_. invs' and obj_at' (\<lambda>tcb. atcbVCPUPtr (tcbArch tcb) = None) tcb and
                           ex_nonz_cap_to' vcpu and ex_nonz_cap_to' tcb and vcpu_at' vcpu"
                    in hoare_strengthen_post)
     apply wpsimp
    apply (clarsimp simp: obj_at'_def projectKOs)
    apply (rename_tac v obj)
    apply (case_tac v, simp)
   apply (wpsimp wp: getObject_tcb_wp simp: archThreadGet_def)
  apply (clarsimp simp: obj_at'_def projectKOs)
  done

lemma invokeVCPUInjectIRQ_invs'[wp]:
  "invokeVCPUInjectIRQ v ir idx \<lbrace>invs'\<rbrace>"
  unfolding invokeVCPUInjectIRQ_def
  apply (wpsimp wp: dmo_invs'
              simp: set_gic_vcpu_ctrl_lr_def machine_op_lift_def machine_rest_lift_def)
  apply (clarsimp simp: in_monad select_f_def)
  done

lemma invokeVCPUAckVPPI_invs'[wp]:
  "invokeVCPUAckVPPI vcpu_ptr irq \<lbrace>invs'\<rbrace>"
  unfolding invokeVCPUAckVPPI_def
  by (wpsimp wp: dmo_invs' setVCPU_VPPIMasked_invs'
             simp: set_gic_vcpu_ctrl_lr_def machine_op_lift_def machine_rest_lift_def vcpuUpdate_def)

lemma invokeVCPUReadReg_inv[wp]:
  "invokeVCPUReadReg vcpu r \<lbrace>P\<rbrace>"
  unfolding invokeVCPUReadReg_def readVCPUReg_def vcpuReadReg_def
  by (wpsimp wp: dmo_inv' simp: readVCPUHardwareReg_def getSCTLR_def)

lemma invokeVCPUWriteReg_invs'[wp]:
  "invokeVCPUWriteReg vcpu r v \<lbrace>invs'\<rbrace>"
  unfolding invokeVCPUWriteReg_def writeVCPUReg_def vcpuWriteReg_def vcpuUpdate_def
  by (wpsimp wp: dmo_machine_op_lift_invs' setVCPU_regs_invs')

lemma performARMVCPUInvocation_invs'[wp]:
  "\<lbrace>invs' and valid_vcpuinv' i\<rbrace> performARMVCPUInvocation i \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding performARMVCPUInvocation_def valid_vcpuinv'_def by wpsimp

lemma arch_performInvocation_invs':
  "\<lbrace>invs' and ct_active' and valid_arch_inv' invocation\<rbrace>
  Arch.performInvocation invocation
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding ARM_HYP_H.performInvocation_def
  by (cases invocation,
      simp_all add: performARMMMUInvocation_def valid_arch_inv'_def,
      (wp|simp)+)

end

end
