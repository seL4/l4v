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
  Top level architecture related proofs.
*)

theory Arch_R
imports Untyped_R Finalise_R
begin

declare is_aligned_shiftl [intro!]
declare is_aligned_shiftr [intro!]

definition
  "asid_ci_map i \<equiv>  
  case i of ArchInvocation_A.MakePool frame slot parent base \<Rightarrow> 
  ArchRetypeDecls_H.MakePool frame (cte_map slot) (cte_map parent) base"

definition
  "valid_aci' aci \<equiv> case aci of MakePool frame slot parent base \<Rightarrow> 
  \<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = NullCap) slot s \<and>
      cte_wp_at' (\<lambda>cte. \<exists>idx.  cteCap cte = UntypedCap frame pageBits idx) parent s \<and>  
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
  "cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap frame pageBits idx) p s \<and> 
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
   apply (clarsimp simp: capRange_def asid_low_bits_def pageBits_def interval_empty)
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
  apply (clarsimp simp:createObjects'_def alignError_def split_def | wp hoare_unless_wp | wpc )+
    apply (simp add:obj_at'_def)+
   apply (wp hoare_unless_wp)
  apply (clarsimp simp:ko_wp_at'_def typ_at'_def pspace_distinct'_def)+
  apply (subgoal_tac "ps_clear ptr (objBitsKO ty) 
    (s\<lparr>ksPSpace := \<lambda>a. if a = ptr then Some ty else ksPSpace s a\<rparr>)")
  apply (simp add:ps_clear_def)+
  apply (rule ccontr)
  apply (drule WordLemmaBucket.int_not_emptyD)
  apply clarsimp
  apply (unfold pspace_no_overlap'_def)
  apply (erule allE)+
  apply (erule(1) impE)
  apply (subgoal_tac "x \<in> {x..x + 2 ^ objBitsKO y - 1}")
   apply (fastforce simp:is_aligned_neg_mask_eq p_assoc_help)
  apply (drule(1) pspace_alignedD')
  apply (clarsimp simp: is_aligned_no_wrap' p_assoc_help)
  done

lemma retype_region2_ext_retype_region_ArchObject:
  "retype_region ptr n us (ArchObject x)=
  retype_region2 ptr n us (ArchObject x)"
  apply (simp add:retype_region_def retype_region2_def bind_assoc
    retype_region2_ext_def retype_region_ext_def default_ext_def)
  apply (rule ext)
  apply (intro monad_eq_split_tail ext)+
     apply simp
    apply simp
   apply (simp add:gets_def get_def bind_def return_def simpler_modify_def )
   apply (rule_tac x = xb in fun_cong)
   apply (rule_tac f = do_extended_op in arg_cong)
   apply (rule ext)
   apply simp
  apply simp
  done

lemma pac_corres:
  "asid_ci_map i = i' \<Longrightarrow> 
  corres dc 
         (einvs and ct_active and valid_aci i) 
         (invs' and ct_active' and valid_aci' i') 
         (perform_asid_control_invocation i) 
         (performASIDControlInvocation i')"
  apply (cases i)
  apply (rename_tac word1 prod1 prod2 word2)
  apply (clarsimp simp: asid_ci_map_def)
  apply (simp add: perform_asid_control_invocation_def placeNewObject_def2
                   performASIDControlInvocation_def)
  apply (rule corres_name_pre)
  apply (clarsimp simp:valid_aci_def valid_aci'_def cte_wp_at_ctes_of cte_wp_at_caps_of_state)
  apply (subgoal_tac "valid_cap' (capability.UntypedCap word1 pageBits idx) s'")
   prefer 2
   apply (case_tac ctea)
   apply clarsimp
   apply (erule ctes_of_valid_cap')
   apply fastforce
  apply (frule valid_capAligned)
  apply (clarsimp simp: capAligned_def page_bits_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       prefer 2
       apply (erule detype_corres)
       apply (simp add:pageBits_def)
      apply (rule corres_split[OF _ getSlotCap_corres])
         apply (rule_tac F = " pcap = (cap.UntypedCap word1 pageBits idxa)" in corres_gen_asm)
         apply (rule corres_split[OF _ updateCap_same_master])
            apply (rule corres_split)
               prefer 2
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
                 prefer 2
                 apply (rule cins_corres_simple, simp, rule refl, rule refl)
                apply (rule_tac F="is_aligned word2 asid_low_bits" in corres_gen_asm)
                apply (simp add: is_aligned_mask dc_def[symmetric])
                apply (rule corres_split [where P=\<top> and P'=\<top> and r'="\<lambda>t t'. t = t' o ucast"])
                   prefer 2
                   apply (clarsimp simp: state_relation_def arch_state_relation_def)
                  apply (rule corres_trivial)
                  apply (rule corres_modify)
                  apply (thin_tac "x \<in> state_relation" for x)
                  apply (clarsimp simp: state_relation_def arch_state_relation_def o_def)
                  apply (rule ext)
                  apply clarsimp
                  apply (erule_tac P = "x = asid_high_bits_of word2" in notE)
                  apply (rule word_eqI)
                  apply (drule_tac x1="ucast x" in bang_eq [THEN iffD1])
                  apply (erule_tac x=n in allE)
                  apply (simp add: word_size nth_ucast)
                 apply wp
             apply (strengthen safe_parent_strg[where idx = "2^pageBits"])
             apply (strengthen invs_valid_objs invs_distinct
                               invs_psp_aligned invs_mdb
                    | simp cong:conj_cong)+
             apply (wp retype_region_plain_invs[where sz = pageBits]
                       retype_cte_wp_at[where sz = pageBits])
            apply (strengthen vp_strgs'
                   safe_parent_strg'[where idx = "2^pageBits"])
            apply (simp cong: conj_cong)
            apply (wp createObjects_valid_pspace'
                      [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))"])
               apply (simp add: makeObjectKO_def)+
              apply (simp add:objBits_simps archObjSize_def range_cover_full)+
            apply (clarsimp simp:valid_cap'_def)
            apply (wp createObject_typ_at'
                      createObjects_orig_cte_wp_at'[where sz = pageBits])
            apply (rule descendants_of'_helper)
            apply (wp createObjects_null_filter'
                      [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))"])
           apply (clarsimp simp:is_cap_simps)
          apply (clarsimp simp: conj_comms obj_bits_api_def arch_kobj_size_def
                 objBits_simps archObjSize_def default_arch_object_def
                 pred_conj_def)
          apply (clarsimp simp: conj_comms
                | strengthen invs_mdb invs_valid_pspace)+
          apply (simp add:region_in_kernel_window_def)
          apply (wp set_untyped_cap_invs_simple[where sz = pageBits]
                    set_cap_cte_wp_at
                    set_cap_caps_no_overlap[where sz = pageBits]
                    set_cap_no_overlap[where sz = pageBits]
                    set_untyped_cap_caps_overlap_reserved[where sz = pageBits])
         apply (clarsimp simp: conj_comms obj_bits_api_def arch_kobj_size_def
                               objBits_simps archObjSize_def default_arch_object_def
                               makeObjectKO_def range_cover_full
                         simp del: capFreeIndex_update.simps 
                | strengthen invs_valid_pspace' invs_pspace_aligned'
                             invs_pspace_distinct')+
         apply (wp updateFreeIndex_invs_simple'
           updateFreeIndex_pspace_no_overlap'
           updateFreeIndex_caps_no_overlap''
           updateFreeIndex_descendants_of'
           updateCap_cte_wp_at_cases)
         apply (rule hoare_vcg_conj_lift)
          apply (rule_tac P1 = "\<lambda>m. m x = {}" for x in hoare_strengthen_post[OF
                          updateFreeIndex_descendants_of'])
          apply (clarsimp, assumption)
         apply (wp updateFreeIndex_caps_overlap_reserved' updateCap_cte_wp_at_cases)
        apply simp
       apply (wp get_cap_wp)
      apply (wp getSlotCap_wp)
     apply (subgoal_tac "word1 && ~~ mask pageBits = word1 \<and> pageBits \<le> word_bits \<and> 2 \<le> pageBits")
      prefer 2
      apply (clarsimp simp:pageBits_def word_bits_def is_aligned_neg_mask_eq)
     apply (simp only:delete_objects_rewrite)
     apply wp
    apply (clarsimp simp: conj_comms)
    apply (clarsimp simp: conj_comms ex_disj_distrib
           | strengthen invs_valid_pspace' invs_pspace_aligned'
                        invs_pspace_distinct')+
    apply (wp deleteObjects_invs' deleteObjects_cte_wp_at')
    apply (rule_tac Q= "\<lambda>r s. ct_active' s \<and>
                               (\<exists>x. (x = capability.UntypedCap word1 pageBits idx \<and> F r s x))" for F
                     in hoare_strengthen_post)
     prefer 2
     apply (elim conjE)
     apply (rule conjI)
      apply assumption
     apply (erule exE)
     apply (rule_tac x = x in exI)
     apply (elim conjE)
     apply (rule conjI)
      apply (clarsimp simp: isCap_simps)
     apply assumption
    apply (clarsimp split del: split_if simp:valid_cap'_def)
    apply (wp hoare_vcg_ex_lift deleteObjects_caps_no_overlap''
              deleteObject_no_overlap deleteObjects_ct_active')
    apply (clarsimp simp: is_simple_cap_def valid_cap'_def max_free_index_def is_cap_simps
                    cong: conj_cong)
    apply (wp deleteObjects_descendants deleteObjects_cte_wp_at' deleteObjects_null_filter)
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
        apply fastforce
       apply fastforce
      apply (simp add: cte_wp_at_caps_of_state)
     apply (simp add: is_cap_simps)
    apply (simp add:empty_descendants_range_in descendants_range_def2)
   apply (frule intvl_range_conv[where bits = pageBits])
    apply (clarsimp simp:pageBits_def word_bits_def)
   apply (clarsimp simp: invs_valid_objs cte_wp_at_caps_of_state conj_comms range_cover_full
                         invs_psp_aligned invs_distinct cap_master_cap_simps is_cap_simps
                         is_simple_cap_def)
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
   apply (rule conjI,rule pspace_no_overlap_detype[OF caps_of_state_valid])
       apply (simp add:invs_psp_aligned invs_valid_objs)+
   apply (rule conjI,erule caps_no_overlap_detype[OF descendants_range_caps_no_overlapI])
     apply (clarsimp simp:is_aligned_neg_mask_eq cte_wp_at_caps_of_state)
     apply (simp add:empty_descendants_range_in)+
   apply (rule conjI)
    apply clarsimp
    apply (drule_tac p = "(aa,ba)" in cap_refs_in_kernel_windowD2[OF caps_of_state_cteD])
     apply fastforce
    apply (clarsimp simp: region_in_kernel_window_def valid_cap_def
                          cap_aligned_def is_aligned_neg_mask_eq detype_def clear_um_def)
   apply (clarsimp simp: detype_def clear_um_def detype_ext_def valid_sched_def valid_etcbs_def
            st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def is_etcb_at_def)
  apply (simp add: detype_def clear_um_def)
  apply (drule_tac x = "cte_map (aa,ba)" in pspace_relation_cte_wp_atI[OF state_relation_pspace_relation])
    apply (simp add:invs_valid_objs)+
  apply clarsimp
  apply (drule cte_map_inj_eq)
       apply ((fastforce simp:cte_wp_at_caps_of_state)+)[5]
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_valid_pspace' conj_comms cte_wp_at_ctes_of)
  apply (frule empty_descendants_range_in')
  apply (intro conjI)
                          apply (simp_all add: is_simple_cap'_def isCap_simps descendants_range'_def2
                                               null_filter_descendants_of'[OF null_filter_simp']
                                               capAligned_def asid_low_bits_def)
           apply (erule descendants_range_caps_no_overlapI')
            apply (fastforce simp:cte_wp_at_ctes_of is_aligned_neg_mask_eq)
           apply (simp add:empty_descendants_range_in')
          apply (simp add:word_bits_def pageBits_def)
         apply (clarsimp simp:max_free_index_def)
        apply (clarsimp simp:max_free_index_def)
        apply (rule is_aligned_weaken)
         apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1,simplified])
        apply (simp add:pageBits_def)
       apply clarsimp
       apply (drule(1) cte_cap_in_untyped_range)
            apply (fastforce simp:cte_wp_at_ctes_of)
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
     by (fastforce simp:cte_wp_at_ctes_of)+

definition
  archinv_relation :: "arch_invocation \<Rightarrow> ArchRetypeDecls_H.invocation \<Rightarrow> bool"
where
  "archinv_relation ai ai' \<equiv> case ai of
     arch_invocation.InvokePageTable pti \<Rightarrow> 
       \<exists>pti'. ai' = InvokePageTable pti' \<and> page_table_invocation_map pti pti'
   | arch_invocation.InvokePageDirectory pdi \<Rightarrow>
       \<exists>pdi'. ai' = InvokePageDirectory pdi' \<and> page_directory_invocation_map pdi pdi'
   | arch_invocation.InvokePage pi \<Rightarrow>
       \<exists>pi'. ai' = InvokePage pi' \<and> page_invocation_map pi pi'
   | arch_invocation.InvokeASIDControl aci \<Rightarrow>
       \<exists>aci'. ai' = InvokeASIDControl aci' \<and> aci' = asid_ci_map aci 
   | arch_invocation.InvokeASIDPool ap \<Rightarrow>
       \<exists>ap'. ai' = InvokeASIDPool ap' \<and>  ap' = asid_pool_invocation_map ap"

definition
  valid_arch_inv' :: "ArchRetypeDecls_H.invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_arch_inv' ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> valid_pti' pti
   | InvokePageDirectory pdi \<Rightarrow> \<top>
   | InvokePage pi \<Rightarrow> valid_page_inv' pi
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

lemma check_vp_corres:
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
   apply (wp hoare_whenE_wp|wpc)+
  apply (simp add: is_aligned_mask vmsz_aligned'_def)
  done

lemma checkVP_inv: "\<lbrace>P\<rbrace> checkVPAlignment sz w \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: checkVPAlignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_whenE_wp|wpc)+
  apply simp
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

crunch inv [wp]: "ArchRetypeDecls_H.decodeInvocation" "P"
  (wp: crunch_wps mapME_x_inv_wp getASID_wp
   simp: forME_x_def crunch_simps
         ARMMMU_improve_cases
   ignore: forME_x getObject)

(* FIXME: Move *)
lemma case_option_corres:
  assumes nonec: "corres r Pn Qn (nc >>= f) (nc' >>= g)"
  and     somec: "\<And>v'. corres r (Ps v') (Qs v') (sc v' >>= f) (sc' v' >>= g)"
  shows "corres r (case_option Pn Ps v) (case_option Qn Qs v) (case_option nc sc v >>= f) (case_option nc' sc' v >>= g)"
  apply (cases v)
   apply simp  
   apply (rule nonec)
  apply simp
  apply (rule somec)
  done

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
  "cap_relation c (UntypedCap p sz f) = (c = cap.UntypedCap p sz f)"
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

(*
lemma guard_abstract_actual_iff: "(guard_abstract_op abstract actual = {}) = (actual = {})"
  apply (auto simp: guard_abstract_op_def)
  done


lemma free_asid_pool_select_guarded: 
    "(- dom pool \<inter> {x. ucast x + word2 \<noteq> 0}) \<noteq> {} \<Longrightarrow> 
     guard_abstract_op {fst (hd [(x, y)\<leftarrow>assocs pool . ucast x + word2 \<noteq> 0 \<and> y = None])}
             (- dom pool \<inter> {x. ucast x + word2 \<noteq> 0}) = 
      {fst (hd [(x, y)\<leftarrow>assocs pool . ucast x + word2 \<noteq> 0 \<and> y = None])}"
  apply (rule guard_abstract_op_abstract)
  apply (drule dom_hd_assocsD | clarsimp)+
  done

lemma free_asid_select_guarded:
     "(- dom (arm_asid_table (arch_state s)) \<inter> {x. x \<le> 2 ^ asid_high_bits - 1}) \<noteq> {} \<Longrightarrow>
      guard_abstract_op
             {fst (hd [(x, y)\<leftarrow>assocs (arm_asid_table (arch_state s)) .
                       x \<le> 2 ^ asid_high_bits - 1 \<and> y = None])}
             (- dom (arm_asid_table (arch_state s)) \<inter> {x. x \<le> 2 ^ asid_high_bits - 1}) =
             {fst (hd [(x, y)\<leftarrow>assocs (arm_asid_table (arch_state s)) .
                       x \<le> 2 ^ asid_high_bits - 1 \<and> y = None])}"
  apply (rule guard_abstract_op_abstract)
  apply (drule dom_hd_assocsD | clarsimp)+
  done *)

lemma select_ext_fa:
  "free_asid_select at \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_select at) S) :: (8 word) det_ext_monad)
   = return (free_asid_select at)"
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
  by (clarsimp simp: pageBase_def page_base_def complement_def)

lemma flush_type_map:
  "ArchLabelFuns_H.isPageFlushLabel (invocation_type (mi_label mi))
   \<or> ArchLabelFuns_H.isPDFlushLabel (invocation_type (mi_label mi))
  \<Longrightarrow> labelToFlushType (mi_label mi) =
          flush_type_map (label_to_flush_type (invocation_type (mi_label mi)))"
  by (clarsimp simp: label_to_flush_type_def labelToFlushType_def flush_type_map_def
                        ArchLabelFuns_H.isPageFlushLabel_def ArchLabelFuns_H.isPDFlushLabel_def
                 split: ArchInvocation_A.flush_type.splits invocation_label.splits arch_invocation_label.splits)

lemma resolve_vaddr_corres:
  "\<lbrakk> is_aligned pd pd_bits; vaddr < kernel_base \<rbrakk> \<Longrightarrow>
  corres (op =) (pspace_aligned and valid_arch_objs and page_directory_at pd
                 and (\<exists>\<rhd> (lookup_pd_slot pd vaddr && ~~ mask pd_bits)))
                (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> vs_valid_duplicates' (ksPSpace s))
          (resolve_vaddr pd vaddr) (resolveVAddr pd vaddr)"
  apply (clarsimp simp: resolve_vaddr_def resolveVAddr_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac R="\<lambda>rv s. valid_pde rv s \<and> pspace_aligned s"
               and R'="\<lambda>_ s. pspace_distinct' s \<and> pspace_aligned' s
                           \<and> vs_valid_duplicates' (ksPSpace s)"
                in corres_split[OF _ get_master_pde_corres])
      apply (case_tac rv, simp_all add: pde_relation'_def)[1]
      apply (rule corres_stateAssert_assume_stronger)
       apply (rule stronger_corres_guard_imp)
         apply (rule corres_split[OF _ get_master_pte_corres])
           apply (rule corres_trivial)
           apply (case_tac rva, simp_all add: pte_relation'_def)[1]
          apply (wp get_master_pte_inv)
        apply (clarsimp simp: page_table_pte_at_lookupI)
       apply (clarsimp simp: page_table_pte_at_lookupI' page_table_at_state_relation)
      apply clarsimp
      apply (erule(3) page_table_at_state_relation)
     apply wp
   apply (clarsimp simp: page_directory_pde_at_lookupI less_kernel_base_mapping_slots)
  apply (clarsimp simp: page_directory_pde_at_lookupI' page_directory_at_state_relation)
  done

lemma dec_arch_inv_page_flush_corres:
  "ArchLabelFuns_H.isPageFlushLabel (invocation_type (mi_label mi)) \<Longrightarrow>
   corres (ser \<oplus> archinv_relation)
           (invs and
            valid_cap (cap.ArchObjectCap (arch_cap.PageCap word seta vmpage_size option)) and
            cte_wp_at
             (is_arch_diminished
               (cap.ArchObjectCap (arch_cap.PageCap word seta vmpage_size option)))
             slot and
            (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
           (invs' and
            valid_cap'
             (capability.ArchObjectCap
               (arch_capability.PageCap word (vmrights_map seta) vmpage_size option)) and
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
                        ArchInvocation_A.page_invocation.PageFlush
                         (label_to_flush_type (invocation_type (mi_label mi))) (start + vaddr)
                         (end + vaddr - 1) (addrFromPPtr word + start) pd asid
                    odE
            else throwError ExceptionTypes_A.syscall_error.TruncatedMessage)
           (decodeARMPageFlush (mi_label mi) args
             (arch_capability.PageCap word (vmrights_map seta) vmpage_size option))"
  apply (simp add: decodeARMPageFlush_def split del: split_if)
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
       prefer 2
       apply (rule corres_lookup_error)
       apply (rule find_pd_for_asid_corres)
      apply (rule whenE_throwError_corres, simp)
       apply simp
      apply (rule whenE_throwError_corres, simp)
       apply simp
      apply (rule corres_trivial)
      apply (rule corres_returnOk)
      apply (clarsimp simp: archinv_relation_def page_invocation_map_def
                            label_to_flush_type_def labelToFlushType_def flush_type_map_def
                            ArchLabelFuns_H.isPageFlushLabel_def
                     split: ArchRetypeDecls_H.flush_type.splits invocation_label.splits arch_invocation_label.splits)
     apply wp
   apply (fastforce simp: valid_cap_def mask_def)
  apply auto
  done

lemma lookup_pd_slot_mask_6_gumpf:
  "is_aligned pd pd_bits \<Longrightarrow>
    lookup_pd_slot pd vaddr && ~~ mask 6
        = lookup_pd_slot pd (vaddr && ~~ mask (pageBitsForSize ARMSuperSection))"
  apply (clarsimp simp: lookup_pd_slot_def pageBits_def
                        is_aligned_mask pd_bits_def shiftr_shiftl1)
  apply (simp add: shiftr_over_and_dist)
  apply (simp add: mask_def word_bw_assocs)
  apply word_bitwise
  apply (clarsimp simp: xor3_simps carry_simps)
  done

lemma neg_mask_combine:
  "~~ mask a && ~~ mask b = ~~ mask (max a b)"
  by (auto simp: word_ops_nth_size word_size intro!: word_eqI)

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
    = vs_refs_pages_ptI[where pte="Arch_Structs_A.pte.LargePagePTE x y z" for x y z,
        unfolded pte_ref_pages_def, simplified, OF _ refl]

lemmas vs_refs_pages_pt_smallI
    = vs_refs_pages_ptI[where pte="Arch_Structs_A.pte.SmallPagePTE x y z" for x y z,
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
    = vs_refs_pages_pdI[where pde="Arch_Structs_A.pde.SectionPDE x y z w" for x y z w,
        unfolded pde_ref_pages_def, simplified, OF _ refl]

lemmas vs_refs_pages_pd_supersectionI
    = vs_refs_pages_pdI[where pde="Arch_Structs_A.pde.SuperSectionPDE x y z" for x y z,
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
    apply (metis word_and_le1 word_bw_assocs word_bw_comms)
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
  "\<lbrace> valid_vs_lookup and pspace_aligned and valid_arch_objs and page_directory_at pd
                 and (\<exists>\<rhd> (lookup_pd_slot pd vaddr && ~~ mask pd_bits))
                 and valid_objs and K (vaddr < kernel_base) \<rbrace>
    resolve_vaddr pd vaddr \<lbrace> \<lambda>rv s. case rv of None \<Rightarrow> True
    | Some (a, b) \<Rightarrow> \<exists>p cap. caps_of_state s p = Some cap
        \<and> (case cap of cap.ArchObjectCap c \<Rightarrow> is_page_cap c | _ \<Rightarrow> False)
        \<and> cap_bits cap = pageBitsForSize a \<rbrace> "
  apply (simp add: resolve_vaddr_def)
  apply (rule hoare_seq_ext[OF _ get_master_pde_sp])
  apply (rule hoare_pre)
   apply (wp get_master_pte_wp | wpc
     | simp add: lookup_pt_slot_no_fail_def)+
  apply (clarsimp simp: obj_at_def)
  apply (frule(1) pspace_alignedD, simp)
  apply (drule_tac y=pd_bits in is_aligned_weaken, simp add: pd_bits_def pageBits_def)
  apply (frule valid_arch_objsD, simp add: obj_at_def lookup_pd_slot_eq, simp)
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
   apply (frule valid_arch_objsD, simp add: obj_at_def, simp)
   apply (drule vs_lookup_pages_vs_lookupI)
   apply (rule conjI)
    apply clarsimp
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
    apply (clarsimp simp: valid_cap_def obj_at_def)
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
   apply (clarsimp simp: valid_cap_def obj_at_def)
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
    apply (clarsimp simp: valid_cap_def obj_at_def)
   apply (frule(1) caps_of_state_valid_cap)
   apply (clarsimp simp: valid_cap_def obj_at_def)
  
  apply clarsimp
  apply (drule vs_lookup_pages_step)
   apply (rule vs_lookup_pages1I, simp add: obj_at_def)
    apply (erule(1) vs_refs_pages_pd_supersectionI)
   apply simp
  apply (drule(1) valid_vs_lookupD)
  apply simp
  apply (erule exEI)+
  apply (clarsimp simp: vs_cap_ref_def split: cap.split_asm arch_cap.split_asm
         option.split_asm vmpage_size.split_asm)
   apply (frule(1) caps_of_state_valid_cap)
   apply (clarsimp simp: valid_cap_def obj_at_def)
  apply (frule(1) caps_of_state_valid_cap)
  apply (clarsimp simp: valid_cap_def obj_at_def)
  done

lemma dec_arch_inv_corres:
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
        cte_wp_at (is_arch_diminished (cap.ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_at (snd x) s))
  (invs' and valid_cap' (capability.ArchObjectCap arch_cap') and
    (\<lambda>s. \<forall>x\<in>set excaps'. s \<turnstile>' fst x \<and> cte_at' (snd x) s) and 
    (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
    (arch_decode_invocation (mi_label mi) args (to_bl cptr') slot
       arch_cap excaps)
    (ArchRetypeDecls_H.decodeInvocation (mi_label mi) args cptr'
       (cte_map slot) arch_cap' excaps')" 
  apply (simp add: arch_decode_invocation_def
                   ArchRetype_H.decodeInvocation_def
                   decodeARMMMUInvocation_def
              split del: split_if)
  apply (cases arch_cap)
      apply (simp add: isCap_simps split del: split_if)
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
           prefer 2
           apply (rule corres_trivial [where r="ser \<oplus> (\<lambda>p p'. p = p' o ucast)"])
           apply (clarsimp simp: state_relation_def arch_state_relation_def)
          apply (rule whenE_throwError_corres, simp)
            apply (simp add: lookup_failure_map_def)
           apply simp
          apply (rule_tac P="\<lambda>s. asid_table (asid_high_bits_of word2) = Some word1 \<longrightarrow> asid_pool_at word1 s" and 
                          P'="pspace_aligned' and pspace_distinct'" in corres_inst)
          apply (simp add: liftME_return)
          apply (rule whenE_throwError_corres_initial, simp)
           apply auto[1]
          apply (rule corres_guard_imp)
            apply (rule corres_splitEE)
               prefer 2
               apply simp      
               apply (rule get_asid_pool_corres_inv')
              apply (simp add: bindE_assoc)
              apply (rule corres_splitEE)
                 prefer 2
                 apply (rule corres_whenE)
                   apply (subst conj_assoc [symmetric])
                   apply (subst assocs_empty_dom_comp [symmetric])
                   apply (rule dom_ucast_eq)
                  apply (rule corres_trivial)
                  apply simp
                 apply simp
                apply (rule_tac F="- dom pool \<inter> {x. x \<le> 2 ^ asid_low_bits - 1 \<and> ucast x + word2 \<noteq> 0} \<noteq> {}" in corres_gen_asm)
                apply (frule dom_hd_assocsD)
                apply (simp add: select_ext_fap[simplified free_asid_pool_select_def]
                                 free_asid_pool_select_def)
                apply (simp add: returnOk_liftE[symmetric])
                apply (rule corres_returnOk)
                apply (simp add: archinv_relation_def asid_pool_invocation_map_def)
               apply (wp hoare_whenE_wp)
               apply (clarsimp simp: ucast_fst_hd_assocs)
              apply (wp hoareE_TrueI hoare_whenE_wp getASID_wp | simp)+
           apply ((clarsimp simp: p2_low_bits_max | rule TrueI impI)+)[2]
         apply (wp hoare_whenE_wp getASID_wp)
       apply (clarsimp simp: valid_cap_def)
      apply auto[1]
     apply (simp add: isCap_simps split del: split_if)
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
     apply (clarsimp simp: Let_def split del: split_if)
     apply (cases excaps', simp)
     apply (case_tac list, simp)
     apply (rename_tac c0' exs' c1'  exss')
     apply (clarsimp split del: split_if)
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE [where r'="\<lambda>p p'. p = p' o ucast"])
          prefer 2
          apply (rule corres_trivial)
          apply (clarsimp simp: state_relation_def arch_state_relation_def)
         apply (simp only: bindE_assoc)
         apply (rule corres_splitEE)
            prefer 2
            apply (rule corres_whenE)
              apply (subst assocs_empty_dom_comp [symmetric])
              apply (simp add: o_def)
              apply (rule dom_ucast_eq_8)
             apply (rule corres_trivial, simp, simp)
           apply (simp split del: split_if)
           apply (rule_tac F="- dom (asidTable \<circ> ucast) \<inter> {x. x \<le> 2 ^ asid_high_bits - 1} \<noteq> {}" in corres_gen_asm)
           apply (drule dom_hd_assocsD)
           apply (simp add: select_ext_fa[simplified free_asid_select_def]
                      free_asid_select_def o_def returnOk_liftE[symmetric] split del: split_if)
           apply (thin_tac "fst a \<notin> b \<and> P" for a b P)
           apply (case_tac "isUntypedCap a \<and> capBlockSize a = objBits (makeObject::asidpool)")
            prefer 2
            apply (rule corres_guard_imp)
              apply (rule corres_trivial)
              apply (case_tac ad, simp_all add: isCap_simps
                                     split del: split_if)[1]
               apply (clarsimp simp: objBits_simps archObjSize_def
                          split del: split_if)
              apply clarsimp
             apply (rule TrueI)+
           apply (clarsimp simp: isCap_simps cap_relation_Untyped_eq lookupTargetSlot_def 
                                 objBits_simps archObjSize_def bindE_assoc split_def)
           apply (rule corres_splitEE)
              prefer 2
              apply (fold ser_def)
              apply (rule ensure_no_children_corres, rule refl)
             apply (rule corres_splitEE)
                prefer 2
                apply (erule lsfc_corres, rule refl)
               apply (rule corres_splitEE)
                  prefer 2 
                  apply (rule ensure_empty_corres)
                  apply clarsimp
                 apply (rule corres_returnOk[where P="\<top>"])
                 apply (clarsimp simp add: archinv_relation_def asid_ci_map_def split_def)
                 apply (clarsimp simp add: ucast_assocs[unfolded o_def] split_def
                                           filter_map asid_high_bits_def)
                 apply (simp add: ord_le_eq_trans [OF word_n1_ge])
                apply wp
          apply (simp add: o_def validE_R_def)
          apply (wp hoare_whenE_wp)
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
    apply (rename_tac word cap_rights vmpage_size option)
    apply (simp add: isCap_simps split del: split_if)
    apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageMap")
     apply (case_tac "\<not>(2 < length args \<and> excaps \<noteq> [])")
      apply (auto split: list.split)[1]
     apply (simp add: Let_def neq_Nil_conv)
     apply (elim exE conjE)
     apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
     apply (rule corres_guard_imp)
       apply (rule whenE_throwError_corres)
         apply simp
        apply simp
       apply (simp split: cap.split,
              intro conjI impI allI, simp_all)[1]
       apply (rename_tac arch_capa)
       apply (case_tac arch_capa, simp_all)[1]
       apply (rename_tac wd opt)
       apply (case_tac opt, simp_all)[1]
       apply (rename_tac optv)
       apply (rule corres_splitEE)
          prefer 2
          apply (rule corres_lookup_error) 
          apply (rule_tac P="valid_arch_state and valid_arch_objs and
                             pspace_aligned and equal_kernel_mappings and valid_global_objs and
                             valid_cap (cap.ArchObjectCap
                                         (arch_cap.PageDirectoryCap wd (Some optv)))"
                     in corres_guard_imp)
            apply (rule find_pd_for_asid_corres)
           apply (clarsimp simp: valid_cap_def)
           apply (simp add: mask_def)
          apply assumption
         apply (rule whenE_throwError_corres, simp, simp)
         apply (rule_tac R="\<lambda>_ s. valid_arch_objs s \<and> pspace_aligned s
                                  \<and> hd args + 2 ^ pageBitsForSize vmpage_size - 1 < kernel_base \<and>
                                  valid_arch_state s \<and> equal_kernel_mappings s \<and> valid_global_objs s \<and>
                                  s \<turnstile> (fst (hd excaps)) \<and> (\<exists>\<rhd> (lookup_pd_slot (obj_ref_of (fst (hd excaps))) (hd args) && ~~ mask pd_bits)) s \<and>
                                  (\<exists>\<rhd> rv') s \<and> page_directory_at rv' s" 
                     and R'="\<lambda>_ s. s \<turnstile>' (fst (hd excaps')) \<and> valid_objs' s \<and>
                                    pspace_aligned' s \<and> pspace_distinct' s \<and>
                                    valid_arch_state' s \<and> vs_valid_duplicates' (ksPSpace s)"
                         in corres_splitEE)
            prefer 2
            apply (rule corres_whenE)
              apply (simp add: kernel_base_def Platform.kernelBase_def kernelBase_def shiftl_t2n)
             apply (rule corres_trivial, simp)
            apply simp
           apply (rule corres_guard_imp)
             apply (rule corres_splitEE)
                prefer 2
                apply (rule check_vp_corres)
               apply (rule corres_splitEE)
                  prefer 2
                  apply (simp only: Platform.addrFromPPtr_def)
                  apply (rule create_mapping_entries_corres)
                   apply (simp add: mask_vmrights_corres)
                  apply (simp add: vm_attributes_corres)
                 apply (rule corres_splitEE)
                    prefer 2
                    apply (erule ensure_safe_mapping_corres)
                   apply (rule corres_trivial)
                   apply (rule corres_returnOk)
                   apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
                  apply (wp hoare_whenE_wp check_vp_wpR)
            apply (clarsimp simp: valid_cap_def  dest!: vmsz_aligned_less_kernel_base_eq)
            apply (frule_tac vptr="hd args" in page_directory_pde_at_lookupI, assumption)
            apply (clarsimp simp: vmsz_aligned_def pageBitsForSize_def page_directory_at_aligned_pd_bits 
              split: vmpage_size.splits)
           apply (clarsimp simp: valid_cap'_def)
          apply simp
          apply (rule whenE_throwError_wp[unfolded validE_R_def])
         apply (wp hoare_whenE_wp)
        apply (rule hoare_drop_imps)+
        apply (simp add:not_le)
        apply (wp hoare_drop_imps)
      apply (clarsimp simp: invs_def valid_state_def)
     apply fastforce
    apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageRemap")
     apply (case_tac "\<not>(1 < length args \<and> excaps \<noteq> [])")
      subgoal by (auto split: list.split)
     apply (simp add: Let_def split: list.split)
     apply (case_tac args, simp) 
     apply (clarsimp simp: split_def)
     apply (rename_tac w1 w2 w3)
     apply (case_tac excaps', simp)
     apply clarsimp
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE [where r' = "op ="])
          prefer 2
          apply (clarsimp simp: list_all2_Cons2)
          apply (case_tac "fst (hd excaps)", simp_all)[1]
          apply clarsimp
          apply (rename_tac arch_capa arch_capb)
          apply (case_tac arch_capa, simp_all)[1]
          apply (rename_tac opt)
          apply (case_tac opt, simp_all)[1]
          apply (rule corres_returnOkTT)
          apply simp
         apply (simp add: Let_def split: list.split)
         apply (rule case_option_corresE)
          apply (rule corres_trivial)
          apply simp
         apply simp
         apply (rule corres_splitEE)
            prefer 2
            apply (rule corres_lookup_error)
            apply (rule find_pd_for_asid_corres)
           apply (rule whenE_throwError_corres)
             apply simp
            apply simp
           apply simp
           apply (rule corres_splitEE)         
              prefer 2
              apply (rule check_vp_corres)
             apply (rule corres_splitEE)
                prefer 2
                apply (simp only: Platform.addrFromPPtr_def)
                apply (rule create_mapping_entries_corres)
                 apply (simp add: mask_vmrights_corres)
                apply (simp add: vm_attributes_corres)
               apply (rule corres_splitEE)
                  prefer 2
                  apply (erule ensure_safe_mapping_corres)
                 apply (rule corres_trivial)
                 apply (rule corres_returnOk)
                 apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
                apply wp
            apply (subgoal_tac "valid_arch_objs s \<and> pspace_aligned s \<and> 
                                (snd v')  < kernel_base \<and>
                                equal_kernel_mappings s \<and> valid_global_objs s \<and> valid_arch_state s \<and>
                                (\<exists>\<rhd> (lookup_pd_slot (fst pa) (snd v') && ~~ mask pd_bits)) s \<and>
                                page_directory_at (fst pa) s \<and> (\<exists>\<rhd> (fst pa)) s")
             prefer 2
             apply assumption
            apply clarsimp
            apply (frule_tac pd = aa and vptr = bc in page_directory_pde_at_lookupI,assumption)
            apply (clarsimp simp: vmsz_aligned_def pageBitsForSize_def 
              page_directory_at_aligned_pd_bits split:vmpage_size.splits)
           apply wp
          apply (wpc | wp throwE_R | wp_once hoare_drop_imps)+
      apply clarsimp
      apply (drule bspec [where x = "excaps ! 0"])
       apply simp
      apply (clarsimp simp: valid_cap_def mask_def split: option.split)
      apply (fastforce simp: invs_def valid_state_def valid_pspace_def)
     apply (clarsimp split: option.split)
     apply fastforce

    apply (simp split del: split_if)
    apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageUnmap")
     apply simp
     apply (rule corres_returnOk)
     apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
    apply (cases "ArchLabelFuns_H.isPageFlushLabel (invocation_type (mi_label mi))")
     apply (clarsimp simp: ArchLabelFuns_H.isPageFlushLabel_def split del: split_if)
     apply (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: split_if)
        apply (rule dec_arch_inv_page_flush_corres, 
                clarsimp simp: ArchLabelFuns_H.isPageFlushLabel_def)+
    apply (clarsimp simp: ArchLabelFuns_H.isPageFlushLabel_def split del: split_if)
    apply (cases "invocation_type (mi_label mi) = ArchInvocationLabel ARMPageGetAddress")
     apply simp
     apply (rule corres_returnOk)
     apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
    subgoal by (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: split_if)
   apply (simp add: isCap_simps split del: split_if)
   apply (simp split: invocation_label.split arch_invocation_label.splits split del: split_if)
   apply (intro conjI impI allI)
    apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
    apply (clarsimp simp: neq_Nil_conv)
    apply (rule whenE_throwError_corres_initial, simp+)
    apply (simp split: cap.split arch_cap.split option.split,
           intro conjI allI impI, simp_all)[1]
    apply (rule whenE_throwError_corres_initial, simp)
     apply (simp add: kernel_base_def Platform.kernelBase_def kernelBase_def)
    apply (rule corres_guard_imp)
      apply (rule corres_splitEE)
         prefer 2
         apply (rule corres_lookup_error)
         apply (rule find_pd_for_asid_corres)
        apply (rule whenE_throwError_corres, simp, simp)
        apply (rule corres_splitEE)
           prefer 2
           apply simp
           (* apply (rule get_pde_corres') *)
           apply (rule get_master_pde_corres')
          apply (simp add: unlessE_whenE)
          apply (rule corres_splitEE)
             prefer 2

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
            apply (simp add: shiftr_shiftl1)
           apply (wp hoare_whenE_wp get_master_pde_wp getPDE_wp find_pd_for_asid_inv
                     | wp_once hoare_drop_imps)+
     apply (fastforce simp: valid_cap_def mask_def)
    apply (clarsimp simp: valid_cap'_def)
    apply fastforce
   apply (clarsimp simp: unlessE_whenE liftE_bindE)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_symb_exec_r_conj)
        apply (rule_tac F="isArchCap isPageTableCap (cteCap cteVal)"
               in corres_gen_asm2)
        apply (rule corres_split[OF _ final_cap_corres[where ptr=slot]])
          apply (drule mp)
           apply (clarsimp simp: isCap_simps final_matters'_def)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def 
                                                page_table_invocation_map_def)
         apply (wp getCTE_wp' | wp_once hoare_drop_imps)+
      apply (clarsimp)
     apply (rule no_fail_pre, rule no_fail_getCTE)
     apply (erule conjunct2)
    apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_diminished_def
                          cap_rights_update_def acap_rights_update_def)
    apply (frule diminished_is_update[rotated])
     apply (frule (2) caps_of_state_valid)
    apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (clarsimp simp: cte_wp_at_ctes_of is_arch_diminished_def
                         cap_rights_update_def acap_rights_update_def
                         cte_wp_at_caps_of_state)
   apply (frule diminished_is_update[rotated])
    apply (frule (2) caps_of_state_valid)
   apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (drule pspace_relation_ctes_ofI[OF _ caps_of_state_cteD, rotated],
          erule invs_pspace_aligned', clarsimp+)
   apply (simp add: isCap_simps)
  apply (simp add: isCap_simps split del: split_if)
  apply (cases "ArchLabelFuns_H.isPDFlushLabel (invocation_type (mi_label mi))")
   apply (clarsimp split del: split_if)
   apply (cases args, simp)
   apply (rename_tac a0 as)
   apply (case_tac as, simp)
   apply (rename_tac a1 as')
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule whenE_throwError_corres, simp)
      apply clarsimp
     apply (rule whenE_throwError_corres, simp)
      apply (clarsimp simp: kernel_base_def Platform.kernelBase_def kernelBase_def)
     apply (rule case_option_corresE)
      apply (rule corres_trivial)
      apply clarsimp
     apply clarsimp
     apply (rule corres_splitEE)
        prefer 2
        apply (rule corres_lookup_error)
        apply (rule find_pd_for_asid_corres)
       apply (rule whenE_throwError_corres, simp)
        apply clarsimp
       apply (simp add: liftE_bindE)
       apply (rule corres_split[OF _ _ resolve_vaddr_valid_mapping_size])
         prefer 2
         apply clarsimp
         apply (rule resolve_vaddr_corres[THEN corres_gen_asm])
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
       apply (wp hoare_drop_imps)
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_cap_simps mask_2pm1
                          valid_arch_state_def valid_arch_caps_def linorder_not_le
                   split: option.splits)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                  split: option.splits)
  apply clarsimp
  done

lemma inv_arch_corres:
  "archinv_relation ai ai' \<Longrightarrow>
   corres (intr \<oplus> op=)
     (einvs and ct_active and valid_arch_inv ai) 
     (invs' and ct_active' and valid_arch_inv' ai' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
     (arch_perform_invocation ai) (ArchRetypeDecls_H.performInvocation ai')"
  apply (clarsimp simp: arch_perform_invocation_def 
                        ArchRetype_H.performInvocation_def 
                        performARMMMUInvocation_def)
  apply (rule corres_split' [where r'=dc])
     prefer 2
     apply (rule corres_trivial)
     apply simp
    apply (cases ai)
        apply (clarsimp simp: archinv_relation_def)
        apply (erule corres_guard_imp [OF perform_page_table_corres])
         apply (fastforce simp: valid_arch_inv_def)
        apply (fastforce simp: valid_arch_inv'_def)
       apply (clarsimp simp: archinv_relation_def)
       apply (erule corres_guard_imp [OF perform_page_directory_corres])
        apply (fastforce simp: valid_arch_inv_def)
       apply (fastforce simp: valid_arch_inv'_def)
      apply (clarsimp simp: archinv_relation_def)
      apply (erule corres_guard_imp [OF perform_page_corres])
       apply (fastforce simp: valid_arch_inv_def)
      apply (fastforce simp: valid_arch_inv'_def)
     apply (clarsimp simp: archinv_relation_def)
     apply (rule corres_guard_imp [OF pac_corres], rule refl)
      apply (fastforce simp: valid_arch_inv_def)
     apply (fastforce simp: valid_arch_inv'_def)
    apply (clarsimp simp: archinv_relation_def)
    apply (rule corres_guard_imp [OF pap_corres], rule refl)
     apply (fastforce simp: valid_arch_inv_def)
    apply (fastforce simp: valid_arch_inv'_def)
   apply wp
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
  apply (rule hoare_pre)
   apply (wp static_imp_wp  |simp add:placeNewObject_def2)+
    apply (wp createObjects_orig_obj_at2' updateFreeIndex_pspace_no_overlap' getSlotCap_wp static_imp_wp)
   apply (clarsimp simp: projectKO_opts_defs)
   apply (strengthen st_tcb_strg' [where P=\<top>]) 
   apply (wp deleteObjects_invs_derivatives
     hoare_vcg_ex_lift deleteObjects_cte_wp_at'
     deleteObjects_st_tcb_at' deleteObjects_invs_derivatives static_imp_wp)
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
      apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
     apply fastforce
    apply simp
   apply (rule conjI,assumption)
  apply (clarsimp simp:invs_valid_pspace' objBits_simps archObjSize_def
    range_cover_full descendants_range'_def2)
  apply (intro conjI)
               apply (fastforce simp:empty_descendants_range_in')+
         apply (erule pred_tcb'_weakenE)
          apply fastforce
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

lemma invokeArch_tcb_at':
  "\<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p\<rbrace>
     ArchRetypeDecls_H.performInvocation ai
   \<lbrace>\<lambda>rv. tcb_at' p\<rbrace>"
  apply (simp add: ArchRetype_H.performInvocation_def performARMMMUInvocation_def)
  apply (cases ai, simp_all)
     apply (wp, clarsimp simp: pred_tcb_at')
    apply (wp, clarsimp simp: pred_tcb_at')
    apply (wp, clarsimp simp: st_tcb_strg'[rule_format])
   apply (wp performASIDControlInvocation_tcb_at', clarsimp simp: valid_arch_inv'_def)
  apply (wp, clarsimp simp: pred_tcb_at')
  done 

(* FIXME random place to have these *)
lemma pspace_no_overlap_queuesL1 [simp]:
  "pspace_no_overlap' w sz (ksReadyQueuesL1Bitmap_update f s) = pspace_no_overlap' w sz s"
  by (simp add: pspace_no_overlap'_def)

(* FIXME random place to have these *)
lemma pspace_no_overlap_queuesL2 [simp]:
  "pspace_no_overlap' w sz (ksReadyQueuesL2Bitmap_update f s) = pspace_no_overlap' w sz s"
  by (simp add: pspace_no_overlap'_def)

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
                        projectKOs pspace_aligned'_def ps_clear_upd'
                        objBits_def[symmetric] lookupAround2_char1
                 split: split_if_asm)
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

lemma ko_wp_at'_cong:
 "ksPSpace s = ksPSpace m \<Longrightarrow> ko_wp_at' P p s = ko_wp_at' P p m"
  by (simp add:ko_wp_at'_def ps_clear_def)

crunch vs_entry_align'[wp]:
  threadSet "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (ignore: getObject setObject wp:crunch_wps)

crunch vs_entry_align'[wp]:
  addToBitmap "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (ignore: getObject setObject wp:crunch_wps)

lemma tcbSchedEnqueue_vs_entry_align[wp]:
 "\<lbrace>\<lambda>s. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p s\<rbrace>
   tcbSchedEnqueue pa
  \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def setQueue_def)
  by (wp hoare_unless_wp | simp)+

crunch vs_entry_align[wp]:
  setThreadState  "ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p"
  (ignore: getObject setObject wp:crunch_wps)

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
  done

lemma less_kernelBase_valid_pde_offset':
  "\<lbrakk> vptr < kernelBase; x = 0 \<or> is_aligned vptr 24; x \<le> 0xF \<rbrakk>
     \<Longrightarrow> valid_pde_mapping_offset' (((x * 4) + (vptr >> 20 << 2)) && mask pdBits)"
  apply (clarsimp simp: kernelBase_def Platform.kernelBase_def pdBits_def pageBits_def
                        valid_pde_mapping_offset'_def pd_asid_slot_def)
  apply (drule minus_one_helper3, simp)
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

lemmas less_kernelBase_valid_pde_offset''
    = less_kernelBase_valid_pde_offset'[where x=0, simplified]

lemma createMappingEntries_valid_pde_slots':
  "\<lbrace>K (vmsz_aligned' vptr sz \<and> is_aligned pd pdBits
                \<and> vptr < kernelBase)\<rbrace>
     createMappingEntries base vptr sz vm_rights attrib pd
   \<lbrace>\<lambda>rv s. valid_pde_slots' rv\<rbrace>,-"
  apply (simp add: createMappingEntries_def valid_pde_slots'_def)
  apply (cases sz, simp_all)
     apply (wp | simp)+
   apply (clarsimp simp: lookup_pd_slot_def Let_def mask_add_aligned)
   apply (erule less_kernelBase_valid_pde_offset'')
  apply (rule hoare_pre, wp)
  apply (clarsimp simp: vmsz_aligned'_def del: ballI)
  apply (subst p_0x3C_shift)
   apply (simp add: lookup_pd_slot_def Let_def)
   apply (erule aligned_add_aligned)
     apply (rule is_aligned_shiftl, rule is_aligned_shiftr)
     apply simp
    apply (simp add: pdBits_def pageBits_def word_bits_def)
   apply (simp add: pdBits_def pageBits_def)
  apply (clarsimp simp: upto_enum_step_def linorder_not_less pd_bits_def
                        lookup_pd_slot_def Let_def field_simps
                        mask_add_aligned)
  apply (erule less_kernelBase_valid_pde_offset'
    [unfolded pdBits_def pageBits_def, simplified], simp+)
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
                      split del: split_if)
  apply (rule hoare_pre)
   apply (wp getASID_wp | wpc)+
  apply clarsimp
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: projectKOs valid_obj'_def inv_ASIDPool ranI
                 split: asidpool.split_asm)
  done

lemma findPDForASID_valid_offset'[wp]:
  "\<lbrace>valid_objs' and K (vptr < kernelBase)\<rbrace> findPDForASID p
   \<lbrace>\<lambda>rv s. valid_pde_mapping_offset' (rv + (vptr >> 20 << 2) && mask pdBits)\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_post_imp_R, rule findPDForASID_aligned)
  apply (simp add: mask_add_aligned)
  apply (erule less_kernelBase_valid_pde_offset'')
  done

lemma diminished_arch_update':
  "diminished' (ArchObjectCap cp) (cteCap cte) \<Longrightarrow> is_arch_update' (ArchObjectCap cp) cte"
  by (clarsimp simp: is_arch_update'_def isCap_simps
                     diminished'_def)

lemma lookupPTSlot_page_table_at':
  "\<lbrace>valid_objs'\<rbrace> lookupPTSlot pd vptr 
  \<lbrace>\<lambda>rv s. page_table_at' (rv && ~~ mask ptBits) s\<rbrace>,-"
  apply (simp add:lookupPTSlot_def)
  apply (wp getPDE_wp|wpc|simp add:checkPTAt_def)+
  apply (clarsimp simp:ptBits_def lookup_pt_slot_no_fail_def)
  apply (subst vaddr_segment_nonsense3[unfolded pt_bits_def,simplified])
   apply (simp add:page_table_at'_def ptBits_def pageBits_def)
  apply simp
  done

lemma findPDForASID_page_directory_at':
  notes checkPDAt_inv[wp del]
  shows "\<lbrace>\<top>\<rbrace> findPDForASID asiv
    \<lbrace>\<lambda>rv s. page_directory_at' (lookup_pd_slot rv vptr && ~~ mask pdBits) s\<rbrace>,-"
  apply (simp add:findPDForASID_def)
   apply (wp getASID_wp|simp add:checkPDAt_def | wpc)+
  apply (clarsimp simp:lookup_pd_slot_def pdBits_def)
  apply (subst vaddr_segment_nonsense[unfolded pd_bits_def,simplified])
   apply (simp add:page_directory_at'_def pdBits_def pageBits_def)
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

lemma is_aligned_ptrFromPAddr_aligned:
  "m \<le> 28 \<Longrightarrow> is_aligned (Platform.ptrFromPAddr p) m = is_aligned p m"
  apply (simp add:Platform.ptrFromPAddr_def is_aligned_mask
    physMappingOffset_def kernelBase_addr_def Platform.physBase_def physBase_def)
  apply (subst add.commute)
  apply (subst mask_add_aligned)
   apply (erule is_aligned_weaken[rotated])
   apply (simp add:is_aligned_def)
  apply simp
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
    apply (rule is_aligned_ptrFromPAddr_aligned[where m = 6,THEN iffD2])
     apply simp
    apply (erule is_aligned_weaken)
    apply (simp add:ptBits_def pageBits_def)
   apply (rule is_aligned_shiftl,simp)
   apply (rule is_aligned_andI1)
   apply (rule is_aligned_shiftr)
   apply simp
  apply simp
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
     apply (rule_tac Q' = "\<lambda>p s.  is_aligned p 6 \<and> page_table_at' (p && ~~ mask ptBits) s"
       in  hoare_post_imp_R)
      apply (wp lookupPTSlot_aligned lookupPTSlot_page_table_at')
     apply (rule_tac x = r in exI)
     apply clarsimp
     apply (frule is_aligned_no_wrap'[where off = "0x3c"])
      apply simp
     apply (drule upto_enum_step_shift[where n = 6 and m = 2,simplified])
     apply (clarsimp simp:mask_def add.commute upto_enum_step_def)
     apply (drule(1) le_less_trans)
     apply simp
    apply wp
   apply (intro conjI impI)
            apply ((clarsimp simp: vmsz_aligned_def pageBitsForSize_def
              slots_duplicated_ensured_def
              split:vmpage_size.splits)+)[9]
   apply clarsimp
   apply (drule lookup_pd_slot_aligned_6)
    apply (simp add:pdBits_def pageBits_def)
   apply (clarsimp simp:slots_duplicated_ensured_def)
   apply (rule_tac x = "(lookup_pd_slot pd vptr)" in exI)
   apply clarsimp
   apply (frule is_aligned_no_wrap'[where off = "0x3c" and sz = 6])
    apply simp
   apply (drule upto_enum_step_shift[where n = 6 and m = 2,simplified])
   apply (clarsimp simp:mask_def add.commute upto_enum_step_def)
   apply (drule(1) le_less_trans)
   apply simp
   done

lemma arch_decodeARMPageFlush_wf:
  "ArchLabelFuns_H.isPageFlushLabel (invocation_type label) \<Longrightarrow>
       \<lbrace>invs' and
        valid_cap'
         (capability.ArchObjectCap (arch_capability.PageCap word vmrights vmpage_size option)) and
        cte_wp_at'
         (diminished'
           (capability.ArchObjectCap (arch_capability.PageCap word vmrights vmpage_size option)) \<circ>
          cteCap)
         slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' (diminished' (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple and
        (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
       decodeARMPageFlush label args (arch_capability.PageCap word vmrights vmpage_size option)
       \<lbrace>valid_arch_inv'\<rbrace>, -"
  apply (simp add: decodeARMPageFlush_def)
  apply (rule hoare_pre)
   apply (wp throwE_R whenE_throwError_wp | wpc | clarsimp)+
   apply (simp add: valid_arch_inv'_def valid_page_inv'_def)
  apply fastforce
  done

lemma arch_decodeInvocation_wf[wp]:
  notes ensureSafeMapping_inv[wp del]
  shows "\<lbrace>invs' and valid_cap' (ArchObjectCap arch_cap) and 
    cte_wp_at' (diminished' (ArchObjectCap arch_cap) o cteCap) slot and  
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' (diminished' (fst x) o cteCap) (snd x) s) and
    sch_act_simple and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))\<rbrace>
   ArchRetypeDecls_H.decodeInvocation label args cap_index slot arch_cap excaps
   \<lbrace>valid_arch_inv'\<rbrace>,-" 
  apply (cases arch_cap)
      apply (simp add: decodeARMMMUInvocation_def ArchRetype_H.decodeInvocation_def 
                       Let_def split_def isCap_simps
                  cong: if_cong split del: split_if)
      apply (rule hoare_pre)
       apply ((wp whenE_throwError_wp getASID_wp|
               wpc|
               simp add: valid_arch_inv'_def valid_apinv'_def)+)[1]
      apply (clarsimp simp: word_neq_0_conv valid_cap'_def)
      apply (rule conjI)
       apply (erule cte_wp_at_weakenE')
       apply (clarsimp simp: diminished_isPDCap)
      apply (subst (asm) conj_assoc [symmetric])
      apply (subst (asm) assocs_empty_dom_comp [symmetric])
      apply (drule dom_hd_assocsD)
      apply (simp add: capAligned_def)
      apply (elim conjE)
      apply (subst field_simps, erule is_aligned_add_less_t2n)
        apply assumption
       apply (simp add: asid_low_bits_def asid_bits_def)
      apply assumption
     apply (simp add: decodeARMMMUInvocation_def ArchRetype_H.decodeInvocation_def 
                       Let_def split_def isCap_simps 
                  cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong prod.case_cong
                  split del: split_if)
     apply (rule hoare_pre) 
      apply ((wp whenE_throwError_wp ensureEmptySlot_stronger|
              wpc|
              simp add: valid_arch_inv'_def valid_aci'_def is_aligned_shiftl_self
                           split del: split_if)+)[1] 
          apply (rule_tac Q'=
                      "\<lambda>rv. K (fst (hd [p\<leftarrow>assocs asidTable . fst p \<le> 2 ^ asid_high_bits - 1 \<and> snd p = None]) 
                               << asid_low_bits \<le> 2 ^ asid_bits - 1) and
                            real_cte_at' rv and 
                            ex_cte_cap_to' rv and                               
                            cte_wp_at' (\<lambda>cte. \<exists>idx. cteCap cte = (UntypedCap frame pageBits idx)) (snd (excaps!0)) and
                            sch_act_simple and
                            (\<lambda>s. descendants_of' (snd (excaps!0)) (ctes_of s) = {}) "
                            in hoare_post_imp_R)
           apply (simp add: lookupTargetSlot_def)
           apply wp
          apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (simp split del: split_if) 
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
      apply (case_tac cteb)
      apply clarsimp
      apply (drule ctes_of_valid_cap', fastforce)
      apply (simp add: diminished_valid') 
     apply clarsimp
     apply (simp add: ex_cte_cap_to'_def cte_wp_at_ctes_of)
     apply (rule_tac x=ba in exI)
     apply (simp add: diminished_cte_refs')
    apply (simp add: decodeARMMMUInvocation_def ArchRetype_H.decodeInvocation_def 
                       Let_def split_def isCap_simps
                cong: if_cong split del: split_if)
    apply (cases "invocation_type label = ArchInvocationLabel ARMPageMap")
     apply (rename_tac word vmrights vmpage_size option)
     apply (simp add: split_def split del: split_if
                cong: list.case_cong prod.case_cong)
     apply (rule hoare_pre)
      apply (wp|wpc|simp add:valid_arch_inv'_def valid_page_inv'_def)+
            apply (rule hoare_vcg_conj_lift_R,(wp ensureSafeMapping_inv)[1])+
            apply ((wp whenE_throwError_wp checkVP_wpR hoare_vcg_const_imp_lift_R
                 ensureSafeMapping_valid_slots_duplicated'
                 createMappingEntries_valid_pde_slots' findPDForASID_page_directory_at'
               | wpc
               | simp add: valid_arch_inv'_def valid_page_inv'_def
               | rule_tac x="fst p" in hoare_imp_eq_substR)+)[8]
     apply (clarsimp simp: neq_Nil_conv invs_valid_objs' linorder_not_le
                           cte_wp_at_ctes_of)
     apply (drule ctes_of_valid', fastforce)+
     apply (clarsimp simp: diminished_valid' [symmetric])
     apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def)
     apply (clarsimp simp: is_arch_update'_def isCap_simps capAligned_def
                           vmsz_aligned'_def 
                    dest!: diminished_capMaster)
     apply (rule conjI)
      apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size, simp_all)[1]
     apply (simp add:vmsz_aligned_def)
     apply (erule order_le_less_trans[rotated])
     apply (erule is_aligned_no_overflow'[simplified field_simps])
    apply (cases "invocation_type label = ArchInvocationLabel ARMPageRemap")
     apply (rename_tac word vmrights vmpage_size option)
     apply (simp add: split_def invs_valid_objs' split del: split_if
                cong: list.case_cong prod.case_cong)
     apply (rule hoare_pre)
      apply (wp|wpc|simp add:valid_arch_inv'_def valid_page_inv'_def)+
            apply (rule hoare_vcg_conj_lift_R,(wp ensureSafeMapping_inv)[1])+
      apply ((wp whenE_throwError_wp checkVP_wpR hoare_vcg_const_imp_lift_R
                 ensureSafeMapping_valid_slots_duplicated'
                 createMappingEntries_valid_pde_slots'
                | wpc
                | simp add: valid_arch_inv'_def valid_page_inv'_def)+)[6]
        apply (simp add: eq_commute[where b="fst x" for x])
        apply ((wp whenE_throwError_wp checkVP_wpR hoare_vcg_const_imp_lift_R
                   hoare_drop_impE_R findPDForASID_page_directory_at'
                   createMappingEntries_valid_pde_slots'
                  | wpc
                  | simp add: valid_arch_inv'_def valid_page_inv'_def)+)[3]
     apply (clarsimp simp: invs_valid_objs' linorder_not_le
                           cte_wp_at_ctes_of)
     apply (drule ctes_of_valid', fastforce)+
     apply (clarsimp simp: diminished_valid' [symmetric])
     apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def)
     apply (clarsimp simp: is_arch_update'_def isCap_simps capAligned_def
                           vmsz_aligned'_def pdBits_def pageBits_def vmsz_aligned_def
                    dest!: diminished_capMaster)
     apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size, simp_all)[1]
    apply (cases "invocation_type label = ArchInvocationLabel ARMPageUnmap")
     apply (simp split del: split_if)
     apply (rule hoare_pre, wp) 
     apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
     apply (thin_tac "Ball S P" for S P)
     apply (erule cte_wp_at_weakenE')
     apply (clarsimp simp: is_arch_update'_def isCap_simps dest!: diminished_capMaster)
    apply (cases "ArchLabelFuns_H.isPageFlushLabel (invocation_type label)")
     apply (clarsimp simp: ArchLabelFuns_H.isPageFlushLabel_def split: invocation_label.splits arch_invocation_label.splits)
        apply (rule arch_decodeARMPageFlush_wf,
               clarsimp simp: ArchLabelFuns_H.isPageFlushLabel_def)+
    apply (cases "invocation_type label = ArchInvocationLabel ARMPageGetAddress")
     apply (simp split del: split_if)
     apply (rule hoare_pre, wp)
     apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
    apply (simp add: ArchLabelFuns_H.isPageFlushLabel_def throwError_R'
              split: invocation_label.split_asm arch_invocation_label.split_asm)
   apply (simp add: decodeARMMMUInvocation_def ArchRetype_H.decodeInvocation_def 
                    Let_def split_def isCap_simps vs_entry_align_def
               cong: if_cong list.case_cong invocation_label.case_cong arch_invocation_label.case_cong prod.case_cong
               split del: split_if)
   apply (rename_tac word option)
   apply (rule hoare_pre)
    apply ((wp whenE_throwError_wp isFinalCapability_inv getPDE_wp
      | wpc |
      simp add: valid_arch_inv'_def valid_pti'_def unlessE_whenE|
      rule_tac x="fst p" in hoare_imp_eq_substR
      )+)
              apply (rule_tac Q'="\<lambda>b c. ko_at' Hardware_H.pde.InvalidPDE (b + (hd args >> 20 << 2)) c \<longrightarrow>
                 cte_wp_at'
                  (is_arch_update'
                    (capability.ArchObjectCap (arch_capability.PageTableCap word (Some (snd p, hd args >> 20 << 20)))))
                  slot c \<and>
                 c \<turnstile>' capability.ArchObjectCap (arch_capability.PageTableCap word (Some (snd p, hd args >> 20 << 20))) \<and>
                 is_aligned (addrFromPPtr word) ptBits \<and>
                 valid_pde_mapping_offset' (b + (hd args >> 20 << 2) && mask pdBits)
                " in hoare_post_imp_R)
              apply ((wp whenE_throwError_wp isFinalCapability_inv getPDE_wp
                | wpc |
                simp add: valid_arch_inv'_def valid_pti'_def unlessE_whenE|
                rule_tac x="fst p" in hoare_imp_eq_substR
                | rule hoare_drop_impE_R)+)
             apply (clarsimp simp:ko_wp_at'_def obj_at'_real_def)
             apply (clarsimp simp: projectKO_opt_pde vs_entry_align_def
               split:Structures_H.kernel_object.splits
               arch_kernel_object.splits)
            apply ((wp whenE_throwError_wp isFinalCapability_inv
                | wpc |simp add: valid_arch_inv'_def valid_pti'_def unlessE_whenE |
                  rule hoare_drop_imp)+)[14]
   apply (clarsimp simp: linorder_not_le isCap_simps
                         cte_wp_at_ctes_of diminished_arch_update')
   apply (simp add: valid_cap'_def capAligned_def)
   apply (rule conjI)
    apply (clarsimp simp: is_arch_update'_def isCap_simps
                   dest!: diminished_capMaster)
   apply (clarsimp simp: neq_Nil_conv vs_entry_align_def invs_valid_objs'
                         ptBits_def pageBits_def is_aligned_addrFromPPtr_n)
   apply (thin_tac "Ball S P" for S P)+
   apply (drule ctes_of_valid', fastforce)+
   apply (clarsimp simp: diminished_valid' [symmetric])
   apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def is_aligned_addrFromPPtr_n
                         invs_valid_objs' vs_entry_align_def and_not_mask[symmetric])
   apply (erule order_le_less_trans[rotated])
   apply (rule word_and_le2)
   apply (simp add: decodeARMMMUInvocation_def ArchRetype_H.decodeInvocation_def isCap_simps Let_def)
  apply(cases "ArchLabelFuns_H.isPDFlushLabel (invocation_type label)", simp_all)
  apply(cases args, simp_all)
  apply(rule hoare_pre, wp)
   defer
   apply(rule hoare_pre, wp)
   apply(case_tac list, simp_all)
    defer
    apply(wp)
   apply(simp add:split_def, wp)
         apply(case_tac xb, simp_all)[]
          apply (wp whenE_throwError_wp)
         apply(simp add:valid_arch_inv'_def)+
        apply wp
   apply(simp, wp)
  apply(rule throwError_R')
  done

lemma setObject_cte_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (cte::cte) \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  apply (rule setObject_nosch)
  apply (simp add: updateObject_cte)
  apply (rule hoare_pre)
   apply (wp|wpc|simp add: unless_def)+
  done

lemma setObject_pte_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  apply (rule setObject_nosch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_pde_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  apply (rule setObject_nosch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

crunch nosch[wp]: setMRs "\<lambda>s. P (ksSchedulerAction s)"
    (ignore: getRestartPC setRegister transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option
        mapM_wp'
   simp: split_def zipWithM_x_mapM)

crunch nosch [wp]: performARMMMUInvocation "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: getObject setObject
   wp: crunch_wps getObject_cte_inv getASID_wp)

lemma arch_pinv_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
     ArchRetypeDecls_H.performInvocation invok
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: ArchRetype_H.performInvocation_def) wp

lemmas setObject_cte_st_tcb_at' [wp] = setCTE_pred_tcb_at' [unfolded setCTE_def]

crunch st_tcb_at': performPageDirectoryInvocation, performPageTableInvocation, performPageInvocation,
            performASIDPoolInvocation "st_tcb_at' P t"
  (ignore: getObject setObject
   wp: crunch_wps getASID_wp getObject_cte_inv simp: crunch_simps)

lemma performASIDControlInvocation_st_tcb_at':
  "\<lbrace>st_tcb_at' (P and op \<noteq> Inactive and op \<noteq> IdleThreadState) t and 
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
             static_imp_wp
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
    range_cover_full descendants_range'_def2)
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

lemma arch_pinv_st_tcb_at':
  "\<lbrace>valid_arch_inv' ai and st_tcb_at' (P and op \<noteq> Inactive and op \<noteq> IdleThreadState) t and 
    invs' and ct_active'\<rbrace>
     ArchRetypeDecls_H.performInvocation ai
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>" (is "?pre (pi ai) ?post")
proof(cases ai)
  txt {* The preservation rules for each invocation have already been proved by crunch, so
    this just becomes a case distinction. *}
  case InvokePage thus ?thesis
    by (simp add: ArchRetype_H.performInvocation_def performARMMMUInvocation_def,
        wp performPageInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokeASIDControl thus ?thesis
    by (simp add: ArchRetype_H.performInvocation_def performARMMMUInvocation_def
                  valid_arch_inv'_def,
        wp performASIDControlInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokeASIDPool thus ?thesis
    by (simp add: ArchRetype_H.performInvocation_def performARMMMUInvocation_def
                  valid_arch_inv'_def,
        wp performASIDPoolInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokePageTable thus ?thesis
    by (simp add: ArchRetype_H.performInvocation_def performARMMMUInvocation_def
                  valid_arch_inv'_def,
        wp performPageTableInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokePageDirectory thus ?thesis
    by (simp add: ArchRetype_H.performInvocation_def performARMMMUInvocation_def
                  valid_arch_inv'_def,
        wp performPageDirectoryInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
qed

crunch aligned': "ArchRetypeDecls_H.finaliseCap" pspace_aligned'
  (ignore: getObject wp: crunch_wps getASID_wp simp: crunch_simps)

lemmas arch_finalise_cap_aligned' = finaliseCap_aligned'

crunch distinct': "ArchRetypeDecls_H.finaliseCap" pspace_distinct'
  (ignore: getObject wp: crunch_wps getASID_wp simp: crunch_simps)

lemmas arch_finalise_cap_distinct' = finaliseCap_distinct'

crunch nosch [wp]: "ArchRetypeDecls_H.finaliseCap" "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: getObject wp: crunch_wps getASID_wp simp: crunch_simps updateObject_default_def)

crunch st_tcb_at' [wp]: "ArchRetypeDecls_H.finaliseCap" "st_tcb_at' P t"
  (ignore: getObject setObject wp: crunch_wps getASID_wp simp: crunch_simps)

crunch typ_at' [wp]: "ArchRetypeDecls_H.finaliseCap" "\<lambda>s. P (typ_at' T p s)"
  (ignore: getObject setObject wp: crunch_wps getASID_wp simp: crunch_simps)

crunch cte_wp_at':  "ArchRetypeDecls_H.finaliseCap" "cte_wp_at' P p"
  (ignore: getObject setObject wp: crunch_wps getASID_wp simp: crunch_simps)

lemma invs_asid_table_strenghten':
  "invs' s \<and> asid_pool_at' ap s \<and> asid \<le> 2 ^ asid_high_bits - 1 \<longrightarrow>
   invs' (s\<lparr>ksArchState :=
            armKSASIDTable_update (\<lambda>_. (armKSASIDTable \<circ> ksArchState) s(asid \<mapsto> ap)) (ksArchState s)\<rparr>)"
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_global_refs'_def global_refs'_def)
  apply (clarsimp simp: valid_arch_state'_def)
  apply (clarsimp simp: valid_asid_table'_def ran_def)
  apply (rule conjI)
   apply (clarsimp split: split_if_asm)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: valid_pspace'_def)
  apply (simp add: valid_machine_state'_def)
  done

lemma freeIndexUpdate_ex_cte:
  "\<lbrace>\<lambda>s. ex_cte_cap_wp_to' (\<lambda>_. True) slot s \<and>
        cte_wp_at' (\<lambda>c. cteCap c = pcap) src s \<and> isUntypedCap pcap\<rbrace>
   updateCap src (capFreeIndex_update (\<lambda>_. idx) pcap)
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to' (\<lambda>_. True) slot s\<rbrace>"
  apply (clarsimp simp:ex_cte_cap_wp_to'_def)
  apply (rule hoare_pre)
  apply (wps)
  apply (wp hoare_vcg_ex_lift updateCap_cte_wp_at_cases)
  apply (clarsimp simp:cte_wp_at_ctes_of isCap_simps)
  apply (rule_tac x = cref in exI)
   apply clarsimp
  done

lemma ex_cte_not_in_untyped_range:
  "\<lbrakk>(ctes_of s) cref = Some (CTE (capability.UntypedCap ptr bits idx) mnode);
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
       apply (strengthen invs_asid_table_strenghten')
       apply (wp cteInsert_simple_invs)
      apply (wp createObjects'_wp_subst[where c = "makeObject::asidpool",OF _
                createObjects_no_cte_invs [where sz = pageBits and ty="Inl (KOArch (KOASIDPool pool))"]]
                createObjects_orig_cte_wp_at'[where sz = pageBits]  hoare_vcg_const_imp_lift
         |simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def cong: rev_conj_cong
         |strengthen safe_parent_strg'[where idx= "2^ pageBits"])+
      apply (rule hoare_vcg_conj_lift)
       apply (rule descendants_of'_helper)
       apply (wp createObjects_null_filter'
                  [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))"]
                 createObjects_valid_pspace' 
                  [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))"]
          | simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def 
                cong: rev_conj_cong)+
       apply (simp add: objBits_simps archObjSize_def valid_cap'_def capAligned_def range_cover_full)
      apply (wp  createObjects'_wp_subst[where c = "makeObject::asidpool",OF _
                    createObjects_ex_cte_cap_to[where sz = pageBits]]
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
    apply (clarsimp simp:conj_comms | 
      strengthen invs_pspace_aligned' invs_pspace_distinct'
      invs_pspace_aligned' invs_valid_pspace')+
    apply (wp updateFreeIndex_invs_simple' updateCap_ct_active'
           updateFreeIndex_pspace_no_overlap'
           updateFreeIndex_caps_no_overlap''
           updateCap_cte_wp_at_cases freeIndexUpdate_ex_cte static_imp_wp)
    apply (rule hoare_vcg_conj_lift)
      apply (rule_tac P1 = "\<lambda>m. m x = {}" for x in hoare_strengthen_post[OF 
           updateFreeIndex_descendants_of'])
      apply (clarsimp,assumption)
     apply (wp updateFreeIndex_caps_overlap_reserved' getSlotCap_wp
                   updateCap_cte_wp_at_cases updateCap_ct_active')
  apply (clarsimp simp:conj_comms ex_disj_distrib is_aligned_mask
           | strengthen invs_valid_pspace' invs_pspace_aligned'
                        invs_pspace_distinct')+
     apply (wp deleteObjects_invs' deleteObjects_cte_wp_at' )
     apply (rule_tac Q= "\<lambda>r s. \<exists>x. (x = capability.UntypedCap w1 pageBits idx \<and> F r s x)"
                     for F in hoare_strengthen_post)
    prefer 2
    apply (erule exE)
    apply (rule_tac x = x in exI)
    apply (elim conjE)
    apply (rule conjI)
     apply (clarsimp simp:isCap_simps)
    apply assumption
   apply (clarsimp split del:if_splits simp:valid_cap'_def max_free_index_def)
   apply (wp hoare_vcg_ex_lift deleteObjects_caps_no_overlap''
             deleteObjects_cte_wp_at' deleteObjects_null_filter
             deleteObject_no_overlap deleteObjects_descendants)
   apply (wp deleteObjects_cap_to' deleteObjects_ct_active'
             deleteObjects_descendants deleteObjects_cte_wp_at' deleteObjects_null_filter)
  apply (frule valid_capAligned)
  apply (clarsimp simp: invs_mdb' invs_valid_pspace' capAligned_def
                        cte_wp_at_ctes_of is_simple_cap'_def isCap_simps)
  apply (frule_tac ptr="w1" in descendants_range_caps_no_overlapI'[where sz = pageBits])
    apply (fastforce simp:is_aligned_neg_mask_eq cte_wp_at_ctes_of)
   apply (simp add:empty_descendants_range_in')
  apply (frule(1) if_unsafe_then_capD'[OF _ invs_unsafe_then_cap',rotated])
   apply (fastforce simp:cte_wp_at_ctes_of)
  apply (drule ex_cte_not_in_untyped_range[rotated -2])
      apply (simp add:invs_valid_global')+
  apply (drule ex_cte_not_in_untyped_range[rotated -2])
      apply (simp add:invs_valid_global')+
  apply (subgoal_tac "is_aligned (2 ^ pageBits) 4")
   prefer 2
   apply (rule is_aligned_weaken)
    apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1,simplified])
   apply (simp add:pageBits_def)
  apply (frule_tac cte="CTE (capability.UntypedCap a b c) m" for a b c m in valid_global_refsD', clarsimp)
  apply (simp add: is_aligned_neg_mask_eq Int_commute)
  by (auto simp:empty_descendants_range_in' objBits_simps
                    archObjSize_def asid_low_bits_def word_bits_def pageBits_def
                    range_cover_full descendants_range'_def2 is_aligned_mask
                    null_filter_descendants_of'[OF null_filter_simp'])

lemma doFlush_underlying_memory[wp]:
  "\<lbrace> \<lambda>m'. underlying_memory m' p = um \<rbrace>
   doFlush flush_type vstart vend pstart
   \<lbrace> \<lambda>_ m'. underlying_memory m' p = um \<rbrace>"
  unfolding doFlush_def by(cases flush_type, simp_all, wp)

(* FIXME: move *)
lemma dmo_invs'_simple:
  "no_irq f \<Longrightarrow>
   (\<And>p um. \<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace> f \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>) \<Longrightarrow>
   \<lbrace> invs' \<rbrace> doMachineOp f \<lbrace> \<lambda>y. invs' \<rbrace>"
  by(rule hoare_pre, rule dmo_invs', wp, simp_all add:valid_def split_def)

(* FIXME: move *)
lemma doFlush_invs[wp]:
  "\<lbrace> invs' \<rbrace> doMachineOp (doFlush flush_type vstart vend pstart) \<lbrace> \<lambda>y. invs' \<rbrace>"
  by(wp dmo_invs'_simple)

lemma performPageDirectoryInvocation_invs'[wp]:
  "\<lbrace> invs' \<rbrace> performPageDirectoryInvocation pdi \<lbrace> \<lambda>rv. invs' \<rbrace>"
  by(cases pdi, simp_all add:performPageDirectoryInvocation_def, (wp|simp)+)

lemma arch_performInvocation_invs':
  "\<lbrace>invs' and ct_active' and valid_arch_inv' invocation\<rbrace> 
  ArchRetypeDecls_H.performInvocation invocation 
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding ArchRetype_H.performInvocation_def
  by (cases invocation,
      simp_all add: performARMMMUInvocation_def valid_arch_inv'_def,
      (wp|simp)+)

end
