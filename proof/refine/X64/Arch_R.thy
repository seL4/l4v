(*
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
  case i of X64_A.MakePool frame slot parent base \<Rightarrow>
  X64_H.MakePool frame (cte_map slot) (cte_map parent) base"

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
  apply (subgoal_tac "x \<in> {x..x + 2 ^ objBitsKO y - 1}")
   apply (fastforce simp:is_aligned_neg_mask_eq p_assoc_help)
  apply (drule(1) pspace_alignedD')
  apply (clarsimp simp: is_aligned_no_wrap' p_assoc_help)
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
        apply (rule_tac F = " pcap = (cap.UntypedCap False word1 pageBits idxa)"
                in corres_gen_asm)
        apply (rule corres_split[OF updateFreeIndex_corres])
            apply (clarsimp simp:is_cap_simps)
           apply (simp add: free_index_of_def)
          apply (rule corres_split)
             apply (simp add: retype_region2_ext_retype_region_ArchObject )
             apply (rule corres_retype [where ty="Inl (KOArch (KOASIDPool F))" for F,
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
              apply (rule_tac F="asid_low_bits_of word2 = 0" in corres_gen_asm)
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
              apply (simp add:objBits_simps archObjSize_def range_cover_full valid_cap'_def)+
            apply (fastforce elim!: canonical_address_neq_mask)
           apply (rule in_kernel_mappings_neq_mask, (simp add: valid_cap'_def bit_simps)+)[1]
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
   apply (rule conjI, clarsimp simp: is_aligned_asid_low_bits_of_zero)
   apply (frule ex_cte_cap_protects)
        apply (simp add:cte_wp_at_caps_of_state)
       apply (simp add:empty_descendants_range_in)
      apply fastforce
     apply (rule subset_refl)
    apply fastforce
   apply clarsimp
   apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp simp: clear_um_def)
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

(* FIXME x64: move *)
definition
  ioport_data_relation :: "io_port_invocation_data \<Rightarrow> ioport_invocation_data \<Rightarrow> bool"
where
  "ioport_data_relation d d' \<equiv> case d of
    X64_A.IOPortIn8 \<Rightarrow> d' = IOPortIn8
  | X64_A.IOPortIn16 \<Rightarrow> d' = IOPortIn16
  | X64_A.IOPortIn32 \<Rightarrow> d' = IOPortIn32
  | X64_A.IOPortOut8 w \<Rightarrow> d' = IOPortOut8 w
  | X64_A.IOPortOut16 w \<Rightarrow> d' = IOPortOut16 w
  | X64_A.IOPortOut32 w \<Rightarrow> d' = IOPortOut32 w"

definition
  ioport_invocation_map :: "io_port_invocation \<Rightarrow> ioport_invocation \<Rightarrow> bool"
where
  "ioport_invocation_map i i' \<equiv> case i of
       X64_A.IOPortInvocation iop dat \<Rightarrow> \<exists>dat'. i' = IOPortInvocation iop dat' \<and> ioport_data_relation dat dat'"

definition
  ioport_control_inv_relation :: "io_port_control_invocation \<Rightarrow> ioport_control_invocation \<Rightarrow> bool"
where
  "ioport_control_inv_relation i i' \<equiv> case i of
    IOPortControlInvocation f l slot slot' \<Rightarrow>
            (i' = IOPortControlIssue f l (cte_map slot) (cte_map slot'))"

definition
  ioport_control_inv_valid' :: "ioport_control_invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "ioport_control_inv_valid' i \<equiv> case i of
     IOPortControlIssue f l ptr ptr' \<Rightarrow> (cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) ptr and
        cte_wp_at' (\<lambda>cte. cteCap cte = ArchObjectCap IOPortControlCap) ptr' and
        ex_cte_cap_to' ptr and real_cte_at' ptr and
        (\<lambda>s. {f..l} \<inter> issued_ioports' (ksArchState s) = {}) and K (f \<le> l))"

definition
  archinv_relation :: "arch_invocation \<Rightarrow> Arch.invocation \<Rightarrow> bool"
where
  "archinv_relation ai ai' \<equiv> case ai of
     arch_invocation.InvokePageTable pti \<Rightarrow>
       \<exists>pti'. ai' = InvokePageTable pti' \<and> page_table_invocation_map pti pti'
   | arch_invocation.InvokePageDirectory pdi \<Rightarrow>
       \<exists>pdi'. ai' = InvokePageDirectory pdi' \<and> page_directory_invocation_map pdi pdi'
   | arch_invocation.InvokePDPT pdpti \<Rightarrow>
       \<exists>pdpti'. ai' = InvokePDPT pdpti' \<and> pdpt_invocation_map pdpti pdpti'
   | arch_invocation.InvokePage pgi \<Rightarrow>
       \<exists>pgi'. ai' = InvokePage pgi' \<and> page_invocation_map pgi pgi'
   | arch_invocation.InvokeASIDControl aci \<Rightarrow>
       \<exists>aci'. ai' = InvokeASIDControl aci' \<and> aci' = asid_ci_map aci
   | arch_invocation.InvokeASIDPool ap \<Rightarrow>
       \<exists>ap'. ai' = InvokeASIDPool ap' \<and>  ap' = asid_pool_invocation_map ap
   | arch_invocation.InvokeIOPort iopi \<Rightarrow>
       \<exists>iopi'. ai' = InvokeIOPort iopi' \<and> ioport_invocation_map iopi iopi'
   | arch_invocation.InvokeIOPortControl iopci \<Rightarrow>
       \<exists>iopci'. ai' = InvokeIOPortControl iopci' \<and> ioport_control_inv_relation iopci iopci'"

definition
  valid_arch_inv' :: "Arch.invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_arch_inv' ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> valid_pti' pti
   | InvokePageDirectory pdi \<Rightarrow> valid_pdi' pdi
   | InvokePDPT pdpti \<Rightarrow> valid_pdpti' pdpti
   | InvokePage pgi \<Rightarrow> valid_page_inv' pgi
   | InvokeASIDControl aci \<Rightarrow> valid_aci' aci
   | InvokeASIDPool ap \<Rightarrow> valid_apinv' ap
   | InvokeIOPort i \<Rightarrow> \<top>
   | InvokeIOPortControl ic \<Rightarrow> ioport_control_inv_valid' ic"

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
  apply (simp add: checkVPAlignment_def)
  by (wpsimp wp: whenE_wp simp: is_aligned_mask vmsz_aligned_def)

lemma asidHighBits [simp]:
  "asidHighBits = asid_high_bits"
  by (simp add: asidHighBits_def asid_high_bits_def)

declare word_unat_power [symmetric, simp del]

crunch inv [wp]: "X64_H.decodeInvocation" "P"
  (wp: crunch_wps mapME_x_inv_wp getASID_wp
   simp: forME_x_def crunch_simps)

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
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_select asid_tbl) S) :: (3 word) det_ext_monad)
   = return (free_asid_select asid_tbl)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def fail_def)

lemma select_ext_fap:
  "free_asid_pool_select p b \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_pool_select p b) S) :: (9 word) det_ext_monad)
   = return (free_asid_pool_select p b)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def)

lemma vs_refs_pages_ptI:
  "pt x = pte \<Longrightarrow> pte_ref_pages pte = Some r'
    \<Longrightarrow> (VSRef (ucast x) (Some APageTable), r') \<in> vs_refs_pages (ArchObj (PageTable pt))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pt_smallI
    = vs_refs_pages_ptI[where pte="X64_A.pte.SmallPagePTE x y z" for x y z,
        unfolded pte_ref_pages_def, simplified, OF _ refl]

lemma vs_refs_pages_pdI:
  "pd x = pde \<Longrightarrow> pde_ref_pages pde = Some r'
    \<Longrightarrow> (VSRef (ucast x) (Some APageDirectory), r') \<in> vs_refs_pages (ArchObj (PageDirectory pd))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pd_largeI
    = vs_refs_pages_pdI[where pde="X64_A.pde.LargePagePDE x y z " for x y z ,
        unfolded pde_ref_pages_def, simplified, OF _ refl]

lemma vs_refs_pages_pdptI:
  "pdpt x = pdpte \<Longrightarrow> pdpte_ref_pages pdpte = Some r'
    \<Longrightarrow> (VSRef (ucast x) (Some APDPointerTable), r') \<in> vs_refs_pages (ArchObj (PDPointerTable pdpt))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pdpt_hugeI
    = vs_refs_pages_pdptI[where pdpte="X64_A.pdpte.HugePagePDPTE x y z " for x y z ,
        unfolded pdpte_ref_pages_def, simplified, OF _ refl]

lemma userVTop_conv[simp]: "userVTop = user_vtop"
  by (simp add: userVTop_def user_vtop_def X64.pptrUserTop_def)

lemma find_vspace_for_asid_lookup_slot [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace>
  find_vspace_for_asid asid
  \<lbrace>\<lambda>rv. \<exists>\<rhd> (lookup_pml4_slot rv vptr && ~~ mask pml4_bits)\<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_post_imp_R)
    apply (rule hoare_vcg_R_conj)
     apply (rule hoare_vcg_R_conj)
      apply (rule find_vspace_for_asid_inv [where P="\<top>", THEN valid_validE_R])
     apply (rule find_vspace_for_asid_lookup)
    apply (rule find_vspace_for_asid_aligned_pm)
   apply clarsimp
   apply (subst lookup_pml4_slot_eq)
    apply (auto simp: bit_simps)
  done

lemmas vmsz_aligned_imp_aligned
    = vmsz_aligned_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN is_aligned_weaken]

lemma corres_splitEE':
  assumes "corres_underlying sr nf nf' (f \<oplus> r') P P' a c"
  assumes "\<And>rv rv'. r' rv rv'
           \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (R rv) (R' rv') (b rv) (d rv')"
  assumes "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows   "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  by (rule corres_splitEE; rule assms)

lemma decodeX64FrameInvocation_corres:
  "\<lbrakk>cap = arch_cap.PageCap d p R mt sz opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at ((=) (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_page_invocation l args slot cap excaps)
            (decodeX64FrameInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_page_invocation_def decodeX64FrameInvocation_def Let_def isCap_simps
        split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PageMap")
   apply (case_tac "\<not>(2 < length args \<and> excaps \<noteq> [])", clarsimp split: list.splits)
   apply (simp add: Let_def neq_Nil_conv)
   apply (elim exE conjE)
   apply (rename_tac pm_cap pm_cap_cnode pm_cap_slot excaps_rest)
   apply (clarsimp split: list.split, intro conjI impI allI; clarsimp)
   apply (rename_tac vaddr rights_mask attr pd_cap' excaps'_rest args_rest)
   apply (rule corres_guard_imp)
     apply (rule_tac P="\<nexists>pm asid. pm_cap = cap.ArchObjectCap (arch_cap.PML4Cap pm (Some asid))"
                   in corres_symmetric_bool_cases[where Q=\<top> and Q'=\<top>, OF refl])
      apply (case_tac pm_cap; clarsimp; rename_tac pm_acap pm_acap'; case_tac pm_acap; clarsimp)
     apply (rule corres_splitEE'[where r'="(=)" and P=\<top> and P'=\<top>])
        apply (clarsimp simp: corres_returnOkTT)
       apply (rule_tac F="pm_cap = cap.ArchObjectCap (arch_cap.PML4Cap (fst rv) (Some (snd rv)))"
                in corres_gen_asm)
       apply (clarsimp cong: option.case_cong)
       apply (rename_tac vspace asid)
       apply wpfix \<comment> \<open>get asid and vspace parameters in schematic preconditions\<close>
       apply (rule_tac P=
                "(opt = None \<and> (user_vtop < vaddr \<or> user_vtop < vaddr + 2 ^ pageBitsForSize sz))
                 \<or> (\<exists>asid' vaddr'. opt = Some (asid', vaddr')
                                   \<and> (asid' \<noteq> asid \<or> mt \<noteq> VMVSpaceMap \<or> vaddr' \<noteq> vaddr))"
                in corres_symmetric_bool_cases[where Q=\<top> and Q'=\<top>, OF refl]; clarsimp)
        apply (case_tac opt; clarsimp)
        apply (case_tac "asid' \<noteq> asid"; clarsimp)
        apply (case_tac "mt \<noteq> VMVSpaceMap"; clarsimp)
       apply (rule corres_splitEE'[where r'=dc])
          apply (case_tac opt; clarsimp simp: whenE_def)
           apply (rule corres_returnOkTT, simp)
          apply (rule corres_returnOkTT, simp)
         apply (rule corres_splitEE'[OF corres_lookup_error[OF findVSpaceForASID_corres]], simp)
           apply (rule whenE_throwError_corres; simp)
           apply (rule corres_splitEE'[where r'=dc, OF checkVPAlignment_corres])
             apply (rule corres_splitEE'[OF createMappingEntries_corres]
                    ; simp add: mask_vmrights_corres vm_attributes_corres)
               apply (rule corres_splitEE'[OF ensureSafeMapping_corres], assumption)
                 apply (rule corres_returnOkTT)
                 \<comment> \<open>program split done, now prove resulting preconditions and Hoare triples\<close>
                 apply (simp add: archinv_relation_def page_invocation_map_def)
                 apply wpsimp+
             apply (wp createMappingEntries_wf)
            apply wpsimp+
          apply (wp find_vspace_for_asid_wp)
         apply (wp findVSpaceForASID_vs_at_wp)
        apply wpsimp
       apply wpsimp
      apply wpsimp
     apply wpsimp
    apply (clarsimp simp: cte_wp_at_caps_of_state cong: conj_cong)
    apply (rename_tac pm_ptr asid')
    apply (prop_tac "is_aligned pm_ptr pml4_bits")
     apply (clarsimp simp: valid_cap_simps cap_aligned_def pml4_bits_def)
    apply (clarsimp simp: invs_implies)
    apply (case_tac "asid' = asid"; clarsimp)
    apply (prop_tac "0 < asid \<and> asid_wf asid \<and> asid \<noteq> 0", clarsimp simp: valid_cap_simps)
    apply clarsimp
    apply (prop_tac "vspace_at_asid asid pm_ptr s \<longrightarrow> (\<exists>ref. (ref \<rhd> pm_ptr) s)")
     apply (fastforce simp: vspace_at_asid_def)
    apply (case_tac opt; clarsimp simp: valid_cap_simps)
  using aligned_sum_le_user_vtop le_user_vtop_canonical_address le_user_vtop_less_pptr_base word_not_le
    apply blast
  apply fastforce

  \<comment> \<open>PageUnmap\<close>
  apply (simp split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PageUnmap")
   apply simp
   apply (rule corres_returnOk)
   apply (clarsimp simp: archinv_relation_def page_invocation_map_def)

  \<comment> \<open>PageGetAddress\<close>
  apply (cases "invocation_type l = ArchInvocationLabel X64PageGetAddress")
   apply simp
   apply (rule corres_returnOk)
   apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: if_split)

lemma VMReadWrite_vmrights_map[simp]: "vmrights_map vm_read_write = VMReadWrite"
  by (simp add: vmrights_map_def vm_read_write_def)

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
            (decodeX64PageTableInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_page_table_invocation_def decodeX64PageTableInvocation_def Let_def
      isCap_simps
      split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PageTableMap")
   apply (simp split: invocation_label.split arch_invocation_label.splits split del: if_split)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (clarsimp simp: neq_Nil_conv Let_def)
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (simp split: cap.split arch_cap.split option.split,
             intro conjI allI impI, simp_all)[1]
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        apply (rule corres_lookup_error)
        apply (rule findVSpaceForASID_corres[OF refl])
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_splitEE)
          apply (rule corres_lookup_error)
          apply (rule lookupPDSlot_corres)
         apply (rule corres_splitEE)
            apply simp
            apply (rule getObject_PDE_corres')
           apply (simp add: unlessE_whenE)
           apply (rule corres_splitEE)
              apply (rule corres_whenE)
                apply clarsimp
                apply (case_tac old_pde; simp )[1]
               apply (rule corres_trivial)
               apply simp
              apply simp
             apply (rule corres_trivial)
             apply (rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def page_table_invocation_map_def)
             apply (clarsimp simp: attribs_from_word_def filter_frame_attrs_def
                                   attribsFromWord_def Let_def)
            apply ((clarsimp cong: if_cong
                     | wp whenE_wp hoare_vcg_all_lift_R getPDE_wp get_pde_wp
                     | wp (once) hoare_drop_imps)+)[6]
      apply (clarsimp intro!: validE_R_validE)
      apply (rule_tac Q'="\<lambda>rv s.  pspace_aligned s \<and> valid_vspace_objs s \<and> valid_arch_state s \<and>
                           equal_kernel_mappings s \<and> valid_global_objs s \<and>
                           (\<exists>ref. (ref \<rhd> rv) s) \<and> typ_at (AArch APageMapL4) rv s \<and>
                           is_aligned rv pml4_bits"
                       in hoare_post_imp_R[rotated])
       apply fastforce
      apply (wpsimp | wp (once) hoare_drop_imps)+
    apply (fastforce simp: valid_cap_def mask_def)
   apply (clarsimp simp: valid_cap'_def)
   apply fastforce
    \<comment> \<open>PageTableUnmap\<close>
  apply (clarsimp simp: isCap_simps)+
  apply (cases "invocation_type l = ArchInvocationLabel X64PageTableUnmap")
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
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits)

lemma decodeX64PageDirectoryInvocation_corres:
  "\<lbrakk>cap = arch_cap.PageDirectoryCap p opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at ((=) (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_page_directory_invocation l args slot cap excaps)
            (decodeX64PageDirectoryInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_page_directory_invocation_def decodeX64PageDirectoryInvocation_def Let_def
                   isCap_simps
      split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PageDirectoryMap")
   apply (simp split: invocation_label.split arch_invocation_label.splits split del: if_split)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (clarsimp simp: neq_Nil_conv Let_def)
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (simp split: cap.split arch_cap.split option.split,
      intro conjI allI impI, simp_all)[1]
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        apply (rule corres_lookup_error)
        apply (rule findVSpaceForASID_corres[OF refl])
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_splitEE)
          apply (rule corres_lookup_error)
          apply (rule lookupPDPTSlot_corres)
         apply (rule corres_splitEE)
            apply simp
            apply (rule getObject_PDPTE_corres')
           apply (simp add: unlessE_whenE)
           apply (rule corres_splitEE)
              apply (rule corres_whenE)
                apply clarsimp
                apply (case_tac old_pdpte; simp )[1]
               apply (rule corres_trivial)
               apply simp
              apply simp
             apply (rule corres_trivial)
             apply (rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def page_directory_invocation_map_def)
             apply (clarsimp simp: attribs_from_word_def filter_frame_attrs_def
                                   attribsFromWord_def Let_def)
            apply ((clarsimp cong: if_cong
                        | wp whenE_wp hoare_vcg_all_lift_R getPDPTE_wp get_pdpte_wp
                        | wp (once) hoare_drop_imps)+)[6]
      apply (clarsimp intro!: validE_R_validE)
      apply (rule_tac Q'="\<lambda>rv s.  pspace_aligned s \<and> valid_vspace_objs s \<and> valid_arch_state s \<and>
                           equal_kernel_mappings s \<and> valid_global_objs s \<and>
                           (\<exists>ref. (ref \<rhd> rv) s) \<and> typ_at (AArch APageMapL4) rv s \<and>
                           is_aligned rv pml4_bits"
                        in hoare_post_imp_R[rotated])
       apply fastforce
      apply (wpsimp | wp (once) hoare_drop_imps)+
    apply (fastforce simp: valid_cap_def mask_def)
   apply (clarsimp simp: valid_cap'_def)
   apply fastforce
    \<comment> \<open>PageDirectoryUnmap\<close>
  apply (clarsimp simp: isCap_simps)+
  apply (cases "invocation_type l = ArchInvocationLabel X64PageDirectoryUnmap")
   apply (clarsimp simp: unlessE_whenE liftE_bindE)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_symb_exec_r_conj)
        apply (rule_tac F="isArchCap isPageDirectoryCap (cteCap cteVal)"
      in corres_gen_asm2)
        apply (rule corres_split[OF isFinalCapability_corres[where ptr=slot]])
          apply (drule mp)
           apply (clarsimp simp: isCap_simps final_matters'_def)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def
                        page_directory_invocation_map_def)
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
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits)

lemma decodeX64PDPointerTableInvocation_corres:
  "\<lbrakk>cap = arch_cap.PDPointerTableCap p opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at ((=) (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_pdpt_invocation l args slot cap excaps)
            (decodeX64PDPointerTableInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_pdpt_invocation_def decodeX64PDPointerTableInvocation_def Let_def
                   isCap_simps
      split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PDPTMap")
   apply (simp split: invocation_label.split arch_invocation_label.splits split del: if_split)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (clarsimp simp: neq_Nil_conv Let_def)
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (simp split: cap.split arch_cap.split option.split,
      intro conjI allI impI, simp_all)[1]
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        apply (rule corres_lookup_error)
        apply (rule findVSpaceForASID_corres[OF refl])
       apply (rule whenE_throwError_corres, simp, simp)
         apply (rule corres_splitEE)
            apply simp
            apply (rule get_pml4e_corres')
           apply (simp add: unlessE_whenE)
           apply (rule corres_splitEE)
              apply (rule corres_whenE)
                apply clarsimp
                apply (case_tac old_pml4e; simp )[1]
               apply (rule corres_trivial)
               apply simp
              apply simp
             apply (rule corres_trivial)
             apply (rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def pdpt_invocation_map_def)
             apply (clarsimp simp: attribs_from_word_def filter_frame_attrs_def
                                   attribsFromWord_def Let_def)
            apply ((clarsimp cong: if_cong
                    | wp whenE_wp hoare_vcg_all_lift_R getPML4E_wp get_pml4e_wp
                    | wp (once) hoare_drop_imps)+)
    apply (fastforce simp: valid_cap_def mask_def intro!: page_map_l4_pml4e_at_lookupI)
   apply (clarsimp simp: valid_cap'_def)
   apply fastforce
    \<comment> \<open>PDPTUnmap\<close>
  apply (clarsimp simp: isCap_simps)+
  apply (cases "invocation_type l = ArchInvocationLabel X64PDPTUnmap")
   apply (clarsimp simp: unlessE_whenE liftE_bindE)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_symb_exec_r_conj)
        apply (rule_tac F="isArchCap isPDPointerTableCap (cteCap cteVal)"
                     in corres_gen_asm2)
        apply (rule corres_split[OF isFinalCapability_corres[where ptr=slot]])
          apply (drule mp)
           apply (clarsimp simp: isCap_simps final_matters'_def)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def
                        pdpt_invocation_map_def)
         apply (wp getCTE_wp' | wp (once) hoare_drop_imps)+
      apply (clarsimp)
     apply (rule no_fail_pre, rule no_fail_getCTE)
     apply (erule conjunct2)
    apply (clarsimp simp: cte_wp_at_caps_of_state cap_rights_update_def acap_rights_update_def)
   apply (clarsimp simp: cte_wp_at_ctes_of cap_rights_update_def acap_rights_update_def
                         cte_wp_at_caps_of_state)
   apply (drule pspace_relation_ctes_ofI[OF _ caps_of_state_cteD, rotated],
                   erule invs_pspace_aligned', clarsimp+)
   apply (simp add: isCap_simps)
  apply (simp add: isCap_simps split del: if_split)
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits)

lemma ensurePortOperationAllowed_corres:
  "\<lbrakk>cap = arch_cap.IOPortCap f l; acap_relation cap cap'\<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> dc) (valid_cap (cap.ArchObjectCap cap) and K (w \<le> 0xFFFF \<and> (x = 1\<or> x = 2 \<or> x = 4))) (valid_cap' (ArchObjectCap cap'))
     (ensure_port_operation_allowed cap w x)
     (ensurePortOperationAllowed cap' w x)"
  apply (simp add: ensure_port_operation_allowed_def ensurePortOperationAllowed_def)
  apply (rule corres_gen_asm)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply (rule corres_assertE_assume; (rule impI, assumption))
      apply (rule corres_split_eqrE)
         apply (rule corres_assertE_assume)
          apply (rule impI, assumption)+
        apply (rule corres_whenE, simp)
         apply clarsimp
        apply clarsimp
       apply wp+
   apply (clarsimp simp: valid_cap_def; elim disjE; clarsimp)
    apply (subst add.commute, subst no_olen_add, simp add: word_le_def)+
  apply (clarsimp simp: valid_cap'_def; elim disjE; clarsimp)
   apply (subst add.commute, subst no_olen_add, simp add: word_le_def)+
  done

lemma ucast_ucast_ioport_max [simp]:
  "UCAST(16 \<rightarrow> 32) (UCAST(64 \<rightarrow> 16) y) \<le> 0xFFFF"
  by word_bitwise

lemma decode_port_inv_corres:
  "\<lbrakk>cap = arch_cap.IOPortCap f l; acap_relation cap cap' \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap))
            (invs' and valid_cap' (capability.ArchObjectCap cap'))
            (decode_port_invocation label args cap)
            (decodeX64PortInvocation label args slot cap' extraCaps')"
  apply (simp add: decode_port_invocation_def decodeX64PortInvocation_def)
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortIn8")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (intro conjI impI)
   apply (clarsimp simp: neq_Nil_conv)
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule ensurePortOperationAllowed_corres, simp, simp)
       apply (rule corres_returnOkTT)
       apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortIn16")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (intro conjI impI)
   apply (clarsimp simp: neq_Nil_conv)
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule ensurePortOperationAllowed_corres, simp, simp)
       apply (rule corres_returnOkTT)
       apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortIn32")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (intro conjI impI)
   apply (clarsimp simp: neq_Nil_conv)
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule ensurePortOperationAllowed_corres, simp, simp)
       apply (rule corres_returnOkTT)
       apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortOut8")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (clarsimp simp: neq_Nil_conv split: list.splits)+
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule ensurePortOperationAllowed_corres, simp, simp)
       apply (rule corres_returnOkTT)
       apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortOut16")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (clarsimp simp: neq_Nil_conv split: list.splits)+
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule ensurePortOperationAllowed_corres, simp, simp)
       apply (rule corres_returnOkTT)
       apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortOut32")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (clarsimp simp: neq_Nil_conv split: list.splits)+
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule ensurePortOperationAllowed_corres, simp, simp)
       apply (rule corres_returnOkTT)
       apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
      apply wpsimp+
  apply (clarsimp simp: isCap_simps Let_def split: arch_invocation_label.splits invocation_label.splits)
  done

lemma free_range_corres:
  "(\<not> foldl (\<lambda>x y. x \<or> f y) False (ls::'a::len word list)) = (set ls \<inter> Collect f = {})"
  apply (subst foldl_fun_or_alt)
  apply (fold orList_def)
  apply (simp only: orList_False)
  by auto

lemma isIOPortRangeFree_corres:
  "f \<le> l \<Longrightarrow> corres (=) \<top> \<top>
     (is_ioport_range_free f l)
     (isIOPortRangeFree f l)"
  apply (clarsimp simp: is_ioport_range_free_def isIOPortRangeFree_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF corres_gets_allocated_io_ports])
   apply (rule corres_return_eq_same)
      apply (auto simp: free_range_corres)
  done

lemma isIOPortRangeFree_wp:
  "\<lbrace>\<lambda>s. \<forall>rv. (rv \<longrightarrow> {f..l} \<inter> issued_ioports' (ksArchState s) = {}) \<longrightarrow> Q rv s\<rbrace> isIOPortRangeFree f l \<lbrace>Q\<rbrace>"
  apply (wpsimp simp: isIOPortRangeFree_def)
  apply (subst free_range_corres)
  apply (clarsimp simp: issued_ioports'_def)
  by (simp add: disjoint_iff_not_equal)

lemma decodeX64PortInvocation_corres:
  "\<lbrakk>list_all2 cap_relation caps caps'; cap = arch_cap.IOPortControlCap; acap_relation cap cap'\<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> archinv_relation)
     (invs and (\<lambda>s. \<forall>cp \<in> set caps. s \<turnstile> cp))
     (invs' and (\<lambda>s. \<forall>cp \<in> set caps'. s \<turnstile>' cp))
     (decode_ioport_control_invocation label args slot cap caps)
     (decodeX64PortInvocation label args (cte_map slot) cap' caps')"
  supply if_splits[split del]
  apply (clarsimp simp: decode_ioport_control_invocation_def X64_H.decodeX64PortInvocation_def Let_def)
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortControlIssue")
   apply (clarsimp split: if_splits simp: isCap_simps)
   apply (rule conjI, clarsimp split del: if_splits)
    prefer 2
    apply clarsimp
    apply (cases caps, simp)
    apply (auto split: arch_invocation_label.splits list.splits invocation_label.splits
                 simp: length_Suc_conv list_all2_Cons1 whenE_rangeCheck_eq liftE_bindE split_def)[2]
  apply (cases caps, simp split: list.split)
  apply (case_tac "\<exists>n. length args = Suc (Suc (Suc (Suc n)))",
              clarsimp simp: length_Suc_conv list_all2_Cons1 whenE_rangeCheck_eq
                             liftE_bindE split_def)
   prefer 2 apply (auto split: list.split)[1]
   apply (clarsimp simp: Let_def)
   apply (rule corres_guard_imp)
     apply (rule whenE_throwError_corres)
       apply clarsimp
      apply clarsimp
     apply (rule corres_split_eqr[OF isIOPortRangeFree_corres])
        apply (clarsimp simp: word_le_not_less)
       apply (clarsimp simp: unlessE_whenE)
       apply (rule whenE_throwError_corres)
         apply clarsimp
        apply clarsimp
       apply (clarsimp simp: lookupTargetSlot_def)
       apply (rule corres_splitEE[OF lookupSlotForCNodeOp_corres])
           apply (clarsimp simp: cap_relation_def)
          apply clarsimp
         apply (rule corres_splitEE[OF ensureEmptySlot_corres])
            apply clarsimp
           apply (rule corres_returnOkTT)
           apply (clarsimp simp: archinv_relation_def ioport_control_inv_relation_def)
          apply wp
         apply wp
        apply wpsimp
       apply wpsimp
      apply clarsimp
      apply (wpsimp wp: is_ioport_range_free_wp)
     apply clarsimp
     apply (wpsimp wp: isIOPortRangeFree_wp)
    apply (clarsimp simp: invs_valid_objs)
   apply (clarsimp simp: invs_valid_objs' invs_pspace_aligned')
  apply (clarsimp simp: isCap_simps split: invocation_label.splits arch_invocation_label.splits)
  done

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
                   X64_H.decodeInvocation_def
                   decodeX64MMUInvocation_def
              split del: if_split)
  apply (cases arch_cap)
      \<comment> \<open>ASIDPoolCap\<close>
      apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def
                       decodeX64ASIDPoolInvocation_def Let_def
            split del: if_split)
      apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel X64ASIDPoolAssign")
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
                          P'="pspace_aligned' and pspace_distinct'" in corres_inst)
          apply (simp add: liftME_return)
          apply (rule whenE_throwError_corres_initial, simp)
           apply auto[1]
          apply (rule corres_guard_imp)
            apply (rule corres_splitEE)
               apply simp
               apply (rule get_asid_pool_corres_inv'[OF refl])
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
     \<comment> \<open>ASIDControlCap\<close>
     apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def
                      Let_def decodeX64ASIDControlInvocation_def
           split del: if_split)
     apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel X64ASIDControlMakePool")
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
     apply (simp add: null_def split_def asid_high_bits_def
                      word_le_make_less)
     apply (subst hd_map, assumption)
                   (* need abstract guard to show list nonempty *)
     apply (simp add: word_le_make_less)
     apply (subst ucast_ucast_len)
      apply (drule hd_in_set)
      apply simp
     apply fastforce
    \<comment> \<open>IOPortCap\<close>
        apply (simp add: isCap_simps isIOCap_def Let_def split del: if_split)
        apply (rule corres_guard_imp, rule decode_port_inv_corres; simp)

\<comment> \<open>IOPortControlCap\<close>
       apply (simp add: isCap_simps isIOCap_def Let_def split del: if_split)
       apply (rule corres_guard_imp, rule decodeX64PortInvocation_corres; simp)

    \<comment> \<open>PageCap\<close>
    apply (rename_tac word cap_rights vmpage_size option)
    apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
          split del: if_split)
        apply (rule decodeX64FrameInvocation_corres; simp)

   \<comment> \<open>PageTableCap\<close>
   apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
         split del: if_split)
   apply (rule decodeX64PageTableInvocation_corres; simp)

  \<comment> \<open>PageDirectoryCap\<close>
  apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
        split del: if_split)
  apply (rule decodeX64PageDirectoryInvocation_corres; simp)

  \<comment> \<open>PDPointerTableCap\<close>
  apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
        split del: if_split)
  apply (rule decodeX64PDPointerTableInvocation_corres; simp)

  \<comment> \<open>PML4Cap - no invocations\<close>
  apply (clarsimp simp: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
              split del: if_split)
  done

lemma not_InvokeIOPort_rel:"\<lbrakk>archinv_relation ai ai'; \<forall>x. ai \<noteq> arch_invocation.InvokeIOPort x\<rbrakk> \<Longrightarrow>
          \<forall>y. ai' \<noteq> InvokeIOPort y"
  by (clarsimp simp: archinv_relation_def split: arch_invocation.splits)

lemma not_InvokeIOPort_perform_simp':"\<forall>y. ai' \<noteq> InvokeIOPort y \<Longrightarrow>
    (case ai' of invocation.InvokeIOPort x \<Rightarrow> performX64PortInvocation ai'
             | _ \<Rightarrow> performX64MMUInvocation ai') = performX64MMUInvocation ai'"
  by (case_tac ai'; clarsimp)

lemmas not_InvokeIOPort_perform_simp[simp] = not_InvokeIOPort_perform_simp'[OF not_InvokeIOPort_rel]

lemma port_in_corres[corres]:
  "no_fail \<top> a \<Longrightarrow> corres (=) \<top> \<top> (port_in a) (portIn a)"
  apply (clarsimp simp: port_in_def portIn_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_machine_op[OF corres_Id], simp+)
  by wpsimp+

lemma port_out_corres[@lift_corres_args, corres]:
  "no_fail \<top> (a w) \<Longrightarrow> corres (=) \<top> \<top> (port_out a w) (portOut a w)"
  apply (clarsimp simp: port_out_def portOut_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_machine_op[OF corres_Id], simp+)
     apply wpsimp+
  done

lemma perform_port_inv_corres:
  "\<lbrakk>archinv_relation ai ai'; ai = arch_invocation.InvokeIOPort x\<rbrakk>
  \<Longrightarrow> corres (dc \<oplus> (=))
        (einvs and ct_active and valid_arch_inv ai)
        (invs' and ct_active' and valid_arch_inv' ai')
        (liftE (perform_io_port_invocation x))
        (performX64PortInvocation ai')"
  apply (clarsimp simp: perform_io_port_invocation_def performX64PortInvocation_def
                        archinv_relation_def ioport_invocation_map_def)
  apply (case_tac x; clarsimp)
  apply (corresKsimp corres: port_in_corres simp: ioport_data_relation_def)
  by (auto simp: no_fail_in8 no_fail_in16 no_fail_in32
                    no_fail_out8 no_fail_out16 no_fail_out32)

crunches setIOPortMask
  for valid_pspace'[wp]: valid_pspace'
  and valid_cap'[wp]: "valid_cap' c"

lemma setIOPortMask_invs':
  "\<lbrace>invs' and (\<lambda>s. \<not> b \<longrightarrow> (\<forall>cap'\<in>ran (cteCaps_of s). cap_ioports' cap' \<inter> {f..l} = {}))\<rbrace> setIOPortMask f l b \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wpsimp wp: setIOPortMask_ioports' simp: invs'_def valid_state'_def setIOPortMask_def simp_del: fun_upd_apply)
  apply (clarsimp simp: foldl_map foldl_fun_upd_value valid_global_refs'_def global_refs'_def
                        valid_arch_state'_def valid_machine_state'_def)
  apply (case_tac b; clarsimp simp: valid_ioports'_simps foldl_fun_upd_value)
   apply (drule_tac x=cap in bspec, assumption)
   apply auto[1]
  apply (drule_tac x=cap in bspec, assumption)
  by auto

lemma valid_ioports_issuedD':
  "\<lbrakk>valid_ioports' s; cteCaps_of s src = Some cap\<rbrakk> \<Longrightarrow> cap_ioports' cap \<subseteq> issued_ioports' (ksArchState s)"
  apply (clarsimp simp: valid_ioports'_def all_ioports_issued'_def)
  by auto

lemma performX64PortInvocation_corres:
  "\<lbrakk>archinv_relation ai ai'; ai = arch_invocation.InvokeIOPortControl x\<rbrakk> \<Longrightarrow>
   corres (dc \<oplus> (=))
      (einvs and ct_active and valid_arch_inv ai)
      (invs' and ct_active' and valid_arch_inv' ai')
      (liftE (do perform_ioport_control_invocation x; return [] od))
      (performX64PortInvocation ai')"
  apply (clarsimp simp: perform_ioport_control_invocation_def performX64PortInvocation_def
                        archinv_relation_def ioport_control_inv_relation_def)
  apply (case_tac x; clarsimp simp: bind_assoc simp del: split_paired_All)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor[OF set_ioport_mask_corres])
      apply (rule corres_split_nor[OF cteInsert_simple_corres])
           apply (clarsimp simp: cap_relation_def)
          apply simp
         apply simp
        apply (rule corres_return_eq_same, simp)
       apply wpsimp
      apply wpsimp
     apply (clarsimp simp: is_simple_cap_def is_cap_simps)
     apply wpsimp
     apply (strengthen invs_distinct[mk_strg] invs_psp_aligned_strg invs_strgs)
     apply (wpsimp wp: set_ioport_mask_invs set_ioport_mask_safe_parent_for)
    apply (clarsimp simp: is_simple_cap'_def isCap_simps)
    apply wpsimp
    apply (strengthen invs_mdb'[mk_strg])
    apply (wpsimp wp: setIOPortMask_invs')
   apply (clarsimp simp: invs_valid_objs valid_arch_inv_def valid_iocontrol_inv_def cte_wp_at_caps_of_state)
   apply (fastforce simp: safe_parent_for_def safe_parent_for_arch_def)
  apply (clarsimp simp: invs_pspace_distinct' invs_pspace_aligned' valid_arch_inv'_def ioport_control_inv_valid'_def
                        valid_cap'_def capAligned_def word_bits_def)
  apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
  apply (case_tac ctea)
  apply (clarsimp simp: isCap_simps sameRegionAs_def3)
  apply (drule_tac src=p in valid_ioports_issuedD'[OF invs_valid_ioports'])
   apply (fastforce simp: cteCaps_of_def)
  apply force
  done

lemma arch_ioport_inv_case_simp:
  "\<lbrakk>archinv_relation ai ai';
     \<nexists>x. ai = arch_invocation.InvokeIOPort x;
     \<nexists>x. ai = arch_invocation.InvokeIOPortControl x\<rbrakk>
    \<Longrightarrow> (case ai' of
          invocation.InvokeIOPort x \<Rightarrow> performX64PortInvocation ai'
          | invocation.InvokeIOPortControl x \<Rightarrow>
              performX64PortInvocation ai'
          | _ \<Rightarrow> performX64MMUInvocation ai') = performX64MMUInvocation ai'"
  by (clarsimp simp: archinv_relation_def split: invocation.splits arch_invocation.splits)


lemma arch_performInvocation_corres:
  "archinv_relation ai ai' \<Longrightarrow>
   corres (dc \<oplus> (=))
     (einvs and ct_active and valid_arch_inv ai and schact_is_rct)
     (invs' and ct_active' and valid_arch_inv' ai')
     (arch_perform_invocation ai) (Arch.performInvocation ai')"
  apply (clarsimp simp: arch_perform_invocation_def
                        X64_H.performInvocation_def
                        performX64MMUInvocation_def)
  apply (cases "\<exists>x. ai = arch_invocation.InvokeIOPort x")
   apply (clarsimp simp: archinv_relation_def)
   apply (rule corres_guard_imp[OF perform_port_inv_corres[where ai=ai, simplified]];
                clarsimp simp: archinv_relation_def)
  apply (cases "\<exists>x. ai = arch_invocation.InvokeIOPortControl x")
   apply (clarsimp simp: archinv_relation_def)
   apply (rule corres_guard_imp[OF performX64PortInvocation_corres[where ai=ai, simplified]];
                clarsimp simp: archinv_relation_def)
  apply (subst arch_ioport_inv_case_simp; simp)
  apply (clarsimp simp: archinv_relation_def)
  apply (clarsimp simp: performX64MMUInvocation_def)
  apply (cases ai)
         apply (clarsimp simp: archinv_relation_def performX64MMUInvocation_def)
         apply (rule corres_guard_imp, rule corres_split_nor)
              apply (rule performPageTableInvocation_corres; wpsimp)
             apply (rule corres_trivial, simp)
            apply wpsimp+
          apply (fastforce simp: valid_arch_inv_def)
         apply (fastforce simp: valid_arch_inv'_def)
        apply (clarsimp simp: archinv_relation_def)
        apply (rule corres_guard_imp, rule corres_split_nor)
             apply (rule performPageDirectoryInvocation_corres; wpsimp)
            apply (rule corres_trivial, simp)
           apply wpsimp+
         apply (fastforce simp: valid_arch_inv_def)
        apply (fastforce simp: valid_arch_inv'_def)
       apply (clarsimp simp: archinv_relation_def)
       apply (rule corres_guard_imp, rule corres_split_nor)
            apply (rule performPDPTInvocation_corres; wpsimp)
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
   apply clarsimp
  apply clarsimp
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
  apply (simp add: valid_cap_simps' range_cover_def objBits_simps archObjSize_def untypedBits_defs
                   capAligned_def unat_eq_0 and_mask_eq_iff_shiftr_0[symmetric]
                   word_bw_assocs)
  apply clarsimp
  apply (drule(1) cte_cap_in_untyped_range,
         fastforce simp add: cte_wp_at_ctes_of, assumption, simp_all)
   apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
  apply clarsimp
  done

crunch tcb_at'[wp]: performX64PortInvocation "tcb_at' t"

lemma invokeArch_tcb_at':
  "\<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p\<rbrace>
     Arch.performInvocation ai
   \<lbrace>\<lambda>rv. tcb_at' p\<rbrace>"
  apply (simp add: X64_H.performInvocation_def performX64MMUInvocation_def)
  apply (wpsimp simp: performX64MMUInvocation_def pred_tcb_at' valid_arch_inv'_def
                  wp: performASIDControlInvocation_tcb_at')
  done

crunch pspace_no_overlap'[wp]: setThreadState "pspace_no_overlap' w s"
  (simp: unless_def)

lemma sts_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  by (wp ex_cte_cap_to'_pres)


lemma valid_slots_lift':
  assumes t: "\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' T p\<rbrace>"
  shows "\<lbrace>valid_slots' x\<rbrace> f \<lbrace>\<lambda>rv. valid_slots' x\<rbrace>"
  apply (clarsimp simp: valid_slots'_def)
  apply (case_tac x, clarsimp split: vmpage_entry.splits)
  apply safe
   apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift t valid_pde_lift' valid_pte_lift' valid_pdpte_lift', simp)+
  done

lemma sts_valid_arch_inv':
  "\<lbrace>valid_arch_inv' ai\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_arch_inv' ai\<rbrace>"
  apply (cases ai, simp_all add: valid_arch_inv'_def)
         apply (clarsimp simp: valid_pdpti'_def split: pdptinvocation.splits)
         apply (intro allI conjI impI)
          apply wpsimp+
        apply (clarsimp simp: valid_pdi'_def split: page_directory_invocation.splits)
        apply (intro allI conjI impI)
         apply wpsimp+
       apply (clarsimp simp: valid_pti'_def split: page_table_invocation.splits)
       apply (intro allI conjI impI)
        apply (wp | simp)+
      apply (rename_tac page_invocation)
      apply (case_tac page_invocation, simp_all add: valid_page_inv'_def)[1]
         apply (wp valid_slots_lift' |simp)+
     apply (clarsimp simp: valid_aci'_def split: asidcontrol_invocation.splits)
     apply (clarsimp simp: cte_wp_at_ctes_of)
     apply (rule hoare_pre, wp)
     apply clarsimp
    apply (clarsimp simp: valid_apinv'_def split: asidpool_invocation.splits)
    apply (rule hoare_pre, wp)
    apply simp
   apply wp
  apply (clarsimp simp: ioport_control_inv_valid'_def split:ioport_control_invocation.splits)
  apply wpsimp
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

lemma lookup_pdpt_slot_no_fail_corres[simp]:
  "lookupPDPTSlotFromPDPT pt vptr
    = (do stateAssert (pd_pointer_table_at' pt) []; return (lookup_pdpt_slot_no_fail pt vptr) od)"
  by (simp add: lookup_pdpt_slot_no_fail_def lookupPDPTSlotFromPDPT_def
                mask_def checkPDPTAt_def word_size_bits_def)

lemma lookup_pd_slot_no_fail_corres[simp]:
  "lookupPDSlotFromPD pt vptr
    = (do stateAssert (page_directory_at' pt) []; return (lookup_pd_slot_no_fail pt vptr) od)"
  by (simp add: lookup_pd_slot_no_fail_def lookupPDSlotFromPD_def
                mask_def checkPDAt_def word_size_bits_def)

lemma lookup_pt_slot_no_fail_corres[simp]:
  "lookupPTSlotFromPT pt vptr
    = (do stateAssert (page_table_at' pt) []; return (lookup_pt_slot_no_fail pt vptr) od)"
  by (simp add: lookup_pt_slot_no_fail_def lookupPTSlotFromPT_def
                mask_def checkPTAt_def word_size_bits_def)

lemma decode_page_inv_wf[wp]:
  "cap = (arch_capability.PageCap word vmrights mt vmpage_size d option) \<Longrightarrow>
      \<lbrace>invs' and valid_cap' (capability.ArchObjectCap cap ) and
        cte_wp_at' ((=) (capability.ArchObjectCap cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeX64FrameInvocation label args slot cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, -"
  apply (simp add: decodeX64FrameInvocation_def Let_def isCap_simps
             cong: if_cong split del: if_split)
  apply (cases "invocation_type label = ArchInvocationLabel X64PageMap")
   apply (simp add: split_def split del: if_split
              cong: list.case_cong prod.case_cong)
   apply (rule hoare_pre)
    apply (wp createMappingEntries_wf checkVP_wpR whenE_throwError_wp hoare_vcg_const_imp_lift_R
           | wpc | simp add: valid_arch_inv'_def valid_page_inv'_def | wp (once) hoare_drop_imps)+
   apply (clarsimp simp: neq_Nil_conv invs_valid_objs' linorder_not_le
                           cte_wp_at_ctes_of)
   apply (drule ctes_of_valid', fastforce)+
   apply (drule_tac t="cteCap cte" in sym)
   apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def)
   apply (clarsimp simp: is_arch_update'_def isCap_simps capAligned_def vmsz_aligned_def)
   apply (rule conjI)
    apply (clarsimp simp: valid_cap_simps)
    apply (rule conjI)
     apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size; simp add: bit_simps)
    apply (subgoal_tac "x < pptr_base", simp add: pptr_base_def)
    apply (fastforce simp flip: word_le_not_less
                         intro: le_user_vtop_less_pptr_base
                          elim: word_add_increasing[where w="w-1" for w, simplified algebra_simps]
                                is_aligned_no_overflow)
   apply clarsimp
   apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size; simp add: bit_simps)
  apply (cases "invocation_type label = ArchInvocationLabel X64PageUnmap")
   apply (simp split del: if_split)
   apply (rule hoare_pre, wp)
   apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
   apply (thin_tac "Ball S P" for S P)
   apply (erule cte_wp_at_weakenE')
   apply (clarsimp simp: is_arch_update'_def isCap_simps)
  apply (cases "invocation_type label = ArchInvocationLabel X64PageGetAddress")
   apply (simp split del: if_split)
   apply (rule hoare_pre, wp)
   apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
  by (simp add:throwError_R'
              split: invocation_label.splits arch_invocation_label.splits)

lemma decode_page_table_inv_wf[wp]:
  "arch_cap = PageTableCap word option \<Longrightarrow>
       \<lbrace>invs' and valid_cap' (capability.ArchObjectCap arch_cap) and
        cte_wp_at' ((=) (capability.ArchObjectCap arch_cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeX64PageTableInvocation label args slot arch_cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  apply (simp add: decodeX64PageTableInvocation_def Let_def isCap_simps split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply ((wp whenE_throwError_wp isFinalCapability_inv getPDE_wp
           | wpc
           | simp add: valid_arch_inv'_def valid_pti'_def if_apply_def2
           | wp (once) hoare_drop_imps)+)
  apply (clarsimp simp: linorder_not_le isCap_simps cte_wp_at_ctes_of)
  apply (frule eq_arch_update')
  apply (case_tac option; clarsimp)
  apply (drule_tac t="cteCap ctea" in sym, simp)
  apply (clarsimp simp: is_arch_update'_def isCap_simps valid_cap'_def capAligned_def)
  apply (thin_tac "Ball S P" for S P)+
  apply (drule ctes_of_valid', fastforce)+
  apply (clarsimp simp: valid_cap'_def bit_simps is_aligned_addrFromPPtr_n
                        invs_valid_objs' and_not_mask[symmetric])
  apply (clarsimp simp: mask_def X64.pptrBase_def X64.pptrUserTop_def user_vtop_def)
  apply word_bitwise
  apply auto
  done

lemma decode_page_directory_inv_wf[wp]:
  "arch_cap = PageDirectoryCap word option \<Longrightarrow>
       \<lbrace>invs' and valid_cap' (capability.ArchObjectCap arch_cap) and
        cte_wp_at' ((=) (capability.ArchObjectCap arch_cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeX64PageDirectoryInvocation label args slot arch_cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  apply (simp add: decodeX64PageDirectoryInvocation_def Let_def isCap_simps split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply ((wp whenE_throwError_wp isFinalCapability_inv getPDPTE_wp
           | wpc
           | simp add: valid_arch_inv'_def valid_pdi'_def if_apply_def2
           | wp (once) hoare_drop_imps)+)
  apply (clarsimp simp: linorder_not_le isCap_simps cte_wp_at_ctes_of)
  apply (frule eq_arch_update')
  apply (case_tac option; clarsimp)
  apply (drule_tac t="cteCap ctea" in sym, simp)
  apply (clarsimp simp: is_arch_update'_def isCap_simps valid_cap'_def capAligned_def)
  apply (thin_tac "Ball S P" for S P)+
  apply (drule ctes_of_valid', fastforce)+
  apply (clarsimp simp: valid_cap'_def bit_simps is_aligned_addrFromPPtr_n
                        invs_valid_objs' and_not_mask[symmetric])
  apply (clarsimp simp: mask_def X64.pptrBase_def X64.pptrUserTop_def user_vtop_def)
  apply word_bitwise
  apply auto
  done

lemma decode_pdpt_inv_wf[wp]:
  "arch_cap = PDPointerTableCap word option \<Longrightarrow>
       \<lbrace>invs' and valid_cap' (capability.ArchObjectCap arch_cap) and
        cte_wp_at' ((=) (capability.ArchObjectCap arch_cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' ((=) (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeX64PDPointerTableInvocation label args slot arch_cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  apply (simp add: decodeX64PDPointerTableInvocation_def Let_def isCap_simps split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply ((wp whenE_throwError_wp isFinalCapability_inv getPML4E_wp
           | wpc
           | simp add: valid_arch_inv'_def valid_pdpti'_def if_apply_def2
           | wp (once) hoare_drop_imps)+)
  apply (clarsimp simp: linorder_not_le isCap_simps cte_wp_at_ctes_of)
  apply (frule eq_arch_update')
  apply (case_tac option; clarsimp)
  apply (drule_tac t="cteCap ctea" in sym, simp)
  apply (clarsimp simp: is_arch_update'_def isCap_simps valid_cap'_def capAligned_def)
  apply (thin_tac "Ball S P" for S P)+
  apply (drule ctes_of_valid', fastforce)+
  apply (clarsimp simp: valid_cap'_def bit_simps is_aligned_addrFromPPtr_n
                        invs_valid_objs' and_not_mask[symmetric])
  apply (clarsimp simp: mask_def X64.pptrBase_def X64.pptrUserTop_def user_vtop_def)
  apply word_bitwise
  apply auto
  done

lemma decode_port_inv_wf:
  "arch_cap = IOPortCap f l \<Longrightarrow>
       \<lbrace>\<top>\<rbrace>
       decodeX64PortInvocation label args slot arch_cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  apply (clarsimp simp: decodeX64PortInvocation_def Let_def isCap_simps split del: if_split cong: if_cong)
  by (wpsimp simp: valid_arch_inv'_def)

lemma decode_port_control_inv_wf:
  "arch_cap = IOPortControlCap \<Longrightarrow>
     \<lbrace>\<lambda>s. invs' s \<and> (\<forall>cap \<in> set caps. s \<turnstile>' cap)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_to' r s)
        \<and> cte_wp_at' (\<lambda>cte. cteCap cte = ArchObjectCap IOPortControlCap) slot s\<rbrace>
       decodeX64PortInvocation label args slot arch_cap caps
     \<lbrace>valid_arch_inv'\<rbrace>, -"
     apply (clarsimp simp add: decodeX64PortInvocation_def Let_def split_def
                    unlessE_whenE isCap_simps lookupTargetSlot_def
                split del: if_split cong: if_cong list.case_cong prod.case_cong
                                          arch_invocation_label.case_cong)
  apply (rule hoare_pre)
   apply (simp add: rangeCheck_def unlessE_whenE lookupTargetSlot_def valid_arch_inv'_def
                    ioport_control_inv_valid'_def
              cong: list.case_cong prod.case_cong
          | wp whenE_throwError_wp ensureEmptySlot_stronger isIOPortRangeFree_wp
          | wpc
          | wp (once) hoare_drop_imps)+
  by (auto simp: invs_valid_objs')


lemma arch_decodeInvocation_wf[wp]:
  notes ensureSafeMapping_inv[wp del]
  shows "\<lbrace>invs' and valid_cap' (ArchObjectCap arch_cap) and
    cte_wp_at' ((=) (ArchObjectCap arch_cap) o cteCap) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' ((=) (fst x) o cteCap) (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. \<forall>r \<in> cte_refs' (fst x) (irq_node' s). ex_cte_cap_to' r s) and
    (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile>' fst x) and
    sch_act_simple\<rbrace>
   Arch.decodeInvocation label args cap_index slot arch_cap excaps
   \<lbrace>valid_arch_inv'\<rbrace>,-"
  apply (cases arch_cap)
      \<comment> \<open>ASIDPool cap\<close>
      apply (simp add: decodeX64MMUInvocation_def X64_H.decodeInvocation_def
                       Let_def split_def isCap_simps isIOCap_def decodeX64ASIDPoolInvocation_def
                  cong: if_cong split del: if_split)
      apply (rule hoare_pre)
       apply ((wp whenE_throwError_wp getASID_wp|
               wpc|
               simp add: valid_arch_inv'_def valid_apinv'_def)+)[1]
      apply (clarsimp simp: word_neq_0_conv valid_cap'_def valid_arch_inv'_def valid_apinv'_def)
      apply (rule conjI)
       apply (erule cte_wp_at_weakenE')
       apply (simp, drule_tac t="cteCap c" in sym, simp)
      apply (subst (asm) conj_assoc [symmetric])
      apply (subst (asm) assocs_empty_dom_comp [symmetric])
      apply (drule dom_hd_assocsD)
      apply (simp add: capAligned_def asid_wf_def)
      apply (elim conjE)
      apply (subst field_simps, erule is_aligned_add_less_t2n)
        apply assumption
       apply (simp add: asid_low_bits_def asid_bits_def)
      apply assumption
     \<comment> \<open>ASIDControlCap\<close>
     apply (simp add: decodeX64MMUInvocation_def X64_H.decodeInvocation_def
                       Let_def split_def isCap_simps isIOCap_def decodeX64ASIDControlInvocation_def
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
                            in hoare_post_imp_R)
           apply (simp add: lookupTargetSlot_def)
           apply wp
          apply (clarsimp simp: cte_wp_at_ctes_of asid_wf_def)
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
    \<comment> \<open>IOPortCap\<close>
    apply (simp add: decodeX64MMUInvocation_def X64_H.decodeInvocation_def
                       Let_def split_def isCap_simps isIOCap_def valid_arch_inv'_def
                cong: if_cong split del: if_split)
    apply (wp decode_port_inv_wf, simp+)
    \<comment> \<open>IOPortControlCap\<close>
    apply (simp add: decodeX64MMUInvocation_def X64_H.decodeInvocation_def Let_def isCap_simps
                     split_def isIOCap_def
               cong: if_cong
          split del: if_split)
    apply (wp decode_port_control_inv_wf, simp)
    apply (clarsimp simp: cte_wp_at_ctes_of)

    \<comment> \<open>PageCap\<close>
        apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def Let_def isIOCap_def
                   cong: if_cong split del: if_split)
        apply (wp, simp+)

    \<comment> \<open>PageTableCap\<close>
    apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def isIOCap_def Let_def
               cong: if_cong split del: if_split)
    apply (wpsimp, simp+)

    \<comment> \<open>PageDirectoryCap\<close>
    apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def isIOCap_def Let_def
               cong: if_cong split del: if_split)
    apply (wpsimp, simp+)

    \<comment> \<open>PDPointerTableCap\<close>
    apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def isIOCap_def Let_def
               cong: if_cong split del: if_split)
    apply (wpsimp, simp+)

      \<comment> \<open>PML4Cap\<close>
  apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def isIOCap_def Let_def
               cong: if_cong split del: if_split)
  by (wpsimp)

crunch nosch[wp]: setMRs "\<lambda>s. P (ksSchedulerAction s)"
    (ignore: getRestartPC setRegister transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option
        mapM_wp'
   simp: split_def zipWithM_x_mapM)

crunches performX64MMUInvocation, performX64PortInvocation
  for nosch [wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: crunch_simps
   wp: crunch_wps getObject_cte_inv getASID_wp)

lemmas setObject_cte_st_tcb_at' [wp] = setCTE_pred_tcb_at' [unfolded setCTE_def]

crunch st_tcb_at': performPageDirectoryInvocation, performPageTableInvocation,
                   performPageInvocation, performPDPTInvocation,
                   performASIDPoolInvocation, performX64PortInvocation "st_tcb_at' P t"
  (wp: crunch_wps getASID_wp getObject_cte_inv simp: crunch_simps)

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
            x64KSASIDTable_update (\<lambda>_. ((x64KSASIDTable \<circ> ksArchState) s)(asid \<mapsto> ap)) (ksArchState s)\<rparr>)"
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
  apply (simp add: valid_machine_state'_def)
  apply (clarsimp simp: valid_ioports'_simps)
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

lemma ucast_asid_high_btis_of_le [simp]:
  "ucast (asid_high_bits_of w) \<le> (2 ^ asid_high_bits - 1 :: machine_word)"
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
  apply (rule ucast_less)
   apply simp
  apply (simp add: asid_high_bits_def)
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
                createObjects_no_cte_invs[where sz = pageBits and ty="Inl (KOArch (KOASIDPool pool))" for pool]]
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
         |simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def
                    not_ioport_cap_safe_ioport_insert' isCap_simps
                    canonical_address_neq_mask
               cong: rev_conj_cong
         |strengthen safe_parent_strg'[where idx = "2^ pageBits"]
         | rule in_kernel_mappings_neq_mask
         | simp add: bit_simps)+
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
    apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1, simplified])
   apply (simp add: pageBits_def untypedBits_defs)
  apply (frule_tac cte="CTE (capability.UntypedCap False a b c) m" for a b c m in valid_global_refsD', clarsimp)
  apply (simp add: Int_commute)
  by (auto simp:empty_descendants_range_in' objBits_simps max_free_index_def
                    archObjSize_def asid_low_bits_def word_bits_def
                    range_cover_full descendants_range'_def2 is_aligned_mask
                    null_filter_descendants_of'[OF null_filter_simp'] bit_simps
                    valid_cap_simps' mask_def)+


lemma dmo_out8_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (out8 a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_out8 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: out8_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_out16_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (out16 a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_out16 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: out16_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_out32_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (out32 a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_out32 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: out32_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_in8_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (in8 a) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_in8 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: in8_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_in16_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (in16 a) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_in16 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: in16_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_in32_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (in32 a) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_in32 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: in32_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma setIOPortMask_safe_ioport_insert':
  "\<lbrace>\<lambda>s. (\<forall>cap\<in>ran (cteCaps_of s). cap_ioports' ac \<inter> cap_ioports' cap = {}) \<and>
      ac = ArchObjectCap (IOPortCap f l)\<rbrace>
     setIOPortMask f l True
   \<lbrace>\<lambda>rv s. safe_ioport_insert' ac NullCap s\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: safe_ioport_insert'_def issued_ioports'_def setIOPortMask_def)
  apply wpsimp
  by (clarsimp simp: cte_wp_at_ctes_of foldl_map foldl_fun_upd_value)

lemma setIOPortMask_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> setIOPortMask f l b \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  by (wp ex_cte_cap_to'_pres)

lemma arch_performInvocation_invs':
  "\<lbrace>invs' and ct_active' and valid_arch_inv' invocation\<rbrace>
  Arch.performInvocation invocation
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding X64_H.performInvocation_def
  apply (cases invocation, simp_all add: performX64MMUInvocation_def valid_arch_inv'_def,
      (wp|wpc|simp)+)
    apply (clarsimp simp: performX64PortInvocation_def)
    apply (wpsimp simp: portIn_def portOut_def)
   apply (clarsimp simp: invs'_def cur_tcb'_def)
  apply (clarsimp simp: performX64PortInvocation_def)
  apply (wpsimp wp: cteInsert_simple_invs setIOPortMask_invs' setIOPortMask_safe_ioport_insert')
  apply (clarsimp simp: ioport_control_inv_valid'_def valid_cap'_def capAligned_def word_bits_def
                        is_simple_cap'_def isCap_simps)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp simp: safe_parent_for'_def)
   apply (case_tac ctea)
   apply (clarsimp simp: isCap_simps sameRegionAs_def3)
   apply (drule_tac src=p in valid_ioports_issuedD'[OF invs_valid_ioports'])
    apply (fastforce simp: cteCaps_of_def)
   apply force
  using ranD valid_ioports_issuedD' by fastforce

end

end
