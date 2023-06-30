(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory VSpace_C
imports TcbAcc_C CSpace_C PSpace_C TcbQueue_C
begin

context kernel_m begin

lemma pageBitsForSize_le:
  "pageBitsForSize x \<le> 24"
  by (simp add: pageBitsForSize_def split: vmpage_size.splits)

lemma unat_of_nat_pageBitsForSize [simp]:
  "unat (of_nat (pageBitsForSize x)::word32) = pageBitsForSize x"
  apply (subst unat_of_nat32)
   apply (rule order_le_less_trans, rule pageBitsForSize_le)
   apply (simp add: word_bits_def)
  apply simp
  done

lemma rf_asidTable:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; valid_arch_state' \<sigma>; idx \<le> mask asid_high_bits \<rbrakk>
     \<Longrightarrow> case armKSASIDTable (ksArchState \<sigma>)
                idx of
        None \<Rightarrow>
            index (armKSASIDTable_' (globals x)) (unat idx) =
               NULL
             | Some v \<Rightarrow>
                 index (armKSASIDTable_' (globals x)) (unat idx) = Ptr v \<and>
                 index (armKSASIDTable_' (globals x)) (unat idx) \<noteq> NULL"
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                             carch_state_relation_def
                             array_relation_def)
  apply (drule_tac x=idx in spec)+
  apply (clarsimp simp: mask_def split: option.split)
  apply (drule sym, simp)
  apply (simp add: option_to_ptr_def option_to_0_def)
  apply (clarsimp simp: invs'_def valid_state'_def valid_arch_state'_def
                        valid_asid_table'_def ran_def)
  done

lemma getKSASIDTable_ccorres_stuff:
  "\<lbrakk> invs' \<sigma>; (\<sigma>, x) \<in> rf_sr; idx' = unat idx;
             idx < 2 ^ asid_high_bits \<rbrakk>
     \<Longrightarrow> case armKSASIDTable (ksArchState \<sigma>)
                idx of
        None \<Rightarrow>
            index (armKSASIDTable_' (globals x))
                idx' =
               NULL
             | Some v \<Rightarrow>
                 index (armKSASIDTable_' (globals x))
                  idx' = Ptr v \<and>
                 index (armKSASIDTable_' (globals x))
                  idx' \<noteq> NULL"
  apply (drule rf_asidTable [where idx=idx])
    apply fastforce
   apply (simp add: mask_def)
   apply (simp add: word_le_minus_one_leq)
  apply (clarsimp split: option.splits)
  done

lemma asidLowBits_handy_convs:
  "sint Kernel_C.asidLowBits = 10"
  "Kernel_C.asidLowBits \<noteq> 0x20"
  "unat Kernel_C.asidLowBits = asid_low_bits"
  by (simp add: Kernel_C.asidLowBits_def asid_low_bits_def)+

lemma rf_sr_armKSASIDTable:
  "\<lbrakk> (s, s') \<in> rf_sr; n \<le> 2 ^ asid_high_bits - 1 \<rbrakk>
       \<Longrightarrow> index (armKSASIDTable_' (globals s')) (unat n)
               = option_to_ptr (armKSASIDTable (ksArchState s) n)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                     carch_state_relation_def array_relation_def)

lemma asid_high_bits_word_bits:
  "asid_high_bits < word_bits"
  by (simp add: asid_high_bits_def word_bits_def)

lemma rf_sr_asid_map_pd_to_hwasids:
  "(s, s') \<in> rf_sr \<Longrightarrow>
   asid_map_pd_to_hwasids (armKSASIDMap (ksArchState s))
       = set_option \<circ> (pde_stored_asid \<circ>\<^sub>m cslift s' \<circ>\<^sub>m pd_pointer_to_asid_slot)"
  by (simp add: rf_sr_def cstate_relation_def Let_def
                carch_state_relation_def)

lemma pd_at_asid_cross_over:
  "\<lbrakk> pd_at_asid' pd asid s; asid \<le> mask asid_bits;
          (s, s') \<in> rf_sr\<rbrakk>
      \<Longrightarrow> \<exists>apptr ap pde. index (armKSASIDTable_' (globals s')) (unat (asid >> asid_low_bits))
                     = (ap_Ptr apptr) \<and> cslift s' (ap_Ptr apptr) = Some (asid_pool_C.asid_pool_C ap)
                  \<and> index ap (unat (asid && 2 ^ asid_low_bits - 1)) = pde_Ptr pd
                  \<and> cslift s' (pde_Ptr (pd + 0x3FC0)) = Some pde
                  \<and> is_aligned pd pdBits
                  \<and> array_assertion (pde_Ptr pd) 4096 (hrs_htd (t_hrs_' (globals s')))
                  \<and> (valid_pde_mappings' s \<longrightarrow> pde_get_tag pde = scast pde_pde_invalid)"
  apply (clarsimp simp: pd_at_asid'_def)
  apply (subgoal_tac "asid >> asid_low_bits \<le> 2 ^ asid_high_bits - 1")
   prefer 2
   apply (simp add: asid_high_bits_word_bits)
   apply (rule shiftr_less_t2n)
   apply (simp add: mask_def)
   apply (simp add: asid_low_bits_def asid_high_bits_def asid_bits_def)
  apply (simp add: rf_sr_armKSASIDTable)
  apply (subgoal_tac "ucast (asid_high_bits_of asid) = asid >> asid_low_bits")
   prefer 2
   apply (simp add: asid_high_bits_of_def ucast_ucast_mask asid_high_bits_def[symmetric])
   apply (subst mask_eq_iff_w2p, simp add: asid_high_bits_def word_size)
   apply (rule shiftr_less_t2n)
   apply (simp add: mask_def, simp add: asid_bits_def asid_low_bits_def asid_high_bits_def)
  apply (simp add: option_to_ptr_def option_to_0_def)
  apply (rule cmap_relationE1 [OF rf_sr_cpspace_asidpool_relation],
         assumption, erule ko_at_projectKO_opt)
  apply (clarsimp simp: casid_pool_relation_def array_relation_def
                 split: asid_pool_C.split_asm)
  apply (drule spec, drule sym [OF mp])
   apply (rule_tac y=asid in word_and_le1)
  apply (frule(1) page_directory_at_rf_sr)
  apply (clarsimp simp: mask_2pm1[symmetric] option_to_ptr_def option_to_0_def
                        page_directory_at'_def typ_at_to_obj_at_arches)
  apply (drule_tac x="pd_asid_slot" in spec, simp add: pd_asid_slot_def)
  apply (drule obj_at_ko_at'[where 'a=pde], clarsimp)
  apply (rule cmap_relationE1 [OF rf_sr_cpde_relation],
         assumption, erule ko_at_projectKO_opt)
  apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
  apply (clarsimp simp: valid_pde_mappings'_def)
  apply (elim allE, drule(1) mp)
  apply (simp add: valid_pde_mapping'_def valid_pde_mapping_offset'_def
                   pd_asid_slot_def mask_add_aligned)
  apply (simp add: mask_def pdBits_def pageBits_def)
  apply (clarsimp simp add: cpde_relation_def Let_def)
  by (simp add: pde_lift_def Let_def pdeBits_def split: if_split_asm)

lemma findPDForASIDAssert_pd_at_wp2:
  "\<lbrace>\<lambda>s. \<forall>pd. pd_at_asid' pd asid s
        \<and> pd \<notin> ran (option_map snd \<circ> armKSASIDMap (ksArchState s) |` (- {asid}))
        \<and> option_map snd (armKSASIDMap (ksArchState s) asid) \<in> {None, Some pd}
         \<longrightarrow> P pd s\<rbrace> findPDForASIDAssert asid \<lbrace>P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: findPDForASIDAssert_def const_def
                    checkPDAt_def checkPDUniqueToASID_def
                    checkPDASIDMapMembership_def)
   apply (wp findPDForASID_pd_at_wp)
  apply clarsimp
  apply (drule spec, erule mp)
  apply clarsimp
  apply (clarsimp split: option.split_asm)
  done

lemma asid_shiftr_low_bits_less:
  "(asid :: word32) \<le> mask asid_bits \<Longrightarrow> asid >> asid_low_bits < 0x80"
  apply (rule_tac y="2 ^ 7" in order_less_le_trans)
   apply (rule shiftr_less_t2n)
   apply (simp add: le_mask_iff_lt_2n[THEN iffD1] asid_bits_def asid_low_bits_def)
  apply simp
  done

lemma loadHWASID_ccorres:
  "ccorres (\<lambda>a b. a = pde_stored_asid b \<and> pde_get_tag b = scast pde_pde_invalid)
                   ret__struct_pde_C_'
      (valid_pde_mappings' and (\<lambda>_. asid \<le> mask asid_bits))  (UNIV \<inter> {s. asid_' s = asid}) []
      (loadHWASID asid) (Call loadHWASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_')
   apply (rule ccorres_Guard_Seq)+
   apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_gets])
     apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_findPDForASIDAssert])
       apply (rename_tac pd)
       apply (rule_tac P="\<lambda>s. pd_at_asid' pd asid s \<and> asidMap = armKSASIDMap (ksArchState s)
                               \<and> pd \<notin> ran (option_map snd o armKSASIDMap (ksArchState s)
                                                     |` (- {asid}))
                               \<and> option_map snd (armKSASIDMap (ksArchState s) asid) \<in> {None, Some pd}
                               \<and> valid_pde_mappings' s"
                   in ccorres_from_vcg_throws[where P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
       apply (frule(2) pd_at_asid_cross_over)
       apply (clarsimp simp: asidLowBits_handy_convs word_sless_def word_sle_def)
       apply (clarsimp simp: typ_heap_simps order_le_less_trans[OF word_and_le1]
                             array_assertion_shrink_right ptr_add_assertion_def
                             arg_cong[where f="\<lambda>x. 2 ^ x", OF meta_eq_to_obj_eq, OF asid_low_bits_def])
       apply (clarsimp split: option.split)
       apply (frule_tac x=pd in fun_cong [OF rf_sr_asid_map_pd_to_hwasids])
       apply (simp add: asid_map_pd_to_hwasids_def
                        pd_pointer_to_asid_slot_def)
       apply (intro conjI allI impI)
        apply (rule ccontr, clarsimp)
        apply (drule singleton_eqD)
        apply (clarsimp elim!: ranE)
        apply (erule notE, rule_tac a=xa in ranI)
        apply (simp add: restrict_map_def split: if_split)
        apply clarsimp
       apply clarsimp
       apply (drule_tac x=a in eqset_imp_iff)
       apply (drule iffD1)
        apply fastforce
       apply simp
      apply wp[1]
     apply (rule findPDForASIDAssert_pd_at_wp2)
    apply wp+
  apply (clarsimp simp: asidLowBits_handy_convs word_sless_def word_sle_def
                        Collect_const_mem asid_shiftr_low_bits_less)
  done

lemma array_relation_update:
  "\<lbrakk> array_relation R bnd table (arr :: 'a['b :: finite]);
               x' = unat (x :: ('td :: len) word); R v v';
               unat bnd < card (UNIV :: 'b set) \<rbrakk>
     \<Longrightarrow> array_relation R bnd (table (x := v))
               (Arrays.update arr x' v')"
  by (simp add: array_relation_def word_le_nat_alt split: if_split)

lemma asid_map_pd_to_hwasids_update:
  "\<lbrakk> pd \<notin> ran (option_map snd \<circ> m |` (- {asid}));
         \<forall>hw_asid pd'. m asid = Some (hw_asid, pd') \<longrightarrow> pd' = pd \<rbrakk> \<Longrightarrow>
   asid_map_pd_to_hwasids (m (asid \<mapsto> (hw_asid, pd)))
        = (asid_map_pd_to_hwasids m) (pd := {hw_asid})"
  apply (rule ext, rule set_eqI)
  apply (simp add: asid_map_pd_to_hwasids_def split: if_split)
  apply (intro conjI impI)
   apply (rule iffI)
    apply (rule ccontr, clarsimp elim!: ranE split: if_split_asm)
    apply (erule notE, rule ranI, simp add: restrict_map_def)
    apply (subst if_P, assumption)
    apply simp
   apply (fastforce split: if_split)
  apply (simp add: ran_def split: if_split)
  apply (rule iffI)
   apply fastforce
  apply (erule exEI)
  apply clarsimp
  done

lemma storeHWASID_ccorres:
  "ccorres dc xfdc (valid_pde_mappings' and (\<lambda>_. asid \<le> mask asid_bits))
                   (UNIV \<inter> {s. asid_' s = asid} \<inter> {s. hw_asid_' s = ucast hw_asid}) []
     (storeHWASID asid hw_asid) (Call storeHWASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_' hw_asid_')
   apply (rule ccorres_Guard_Seq)+
   apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_findPDForASIDAssert])
     apply (rename_tac pd)
     apply (rule_tac P="\<lambda>s. pd_at_asid' pd asid s
                               \<and> pd \<notin> ran (option_map snd o armKSASIDMap (ksArchState s)
                                                     |` (- {asid}))
                               \<and> option_map snd (armKSASIDMap (ksArchState s) asid) \<in> {None, Some pd}
                               \<and> valid_pde_mappings' s"
                   in ccorres_from_vcg[where P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: Collect_const_mem word_sle_def word_sless_def
                           asidLowBits_handy_convs simpler_gets_def
                           simpler_modify_def bind_def)
     apply (frule(2) pd_at_asid_cross_over)
     apply (clarsimp simp: typ_heap_simps)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           cpspace_relation_def)
     apply (clarsimp simp: typ_heap_simps cmachine_state_relation_def
                           carch_state_relation_def pd_at_asid'_def
                           fun_upd_def[symmetric] carch_globals_def
                           order_le_less_trans[OF word_and_le1]
                           ptr_add_assertion_positive
                           array_assertion_shrink_right
                           arg_cong[where f="\<lambda>x. 2 ^ x", OF meta_eq_to_obj_eq, OF asid_low_bits_def])
     apply (subgoal_tac "ucast hw_asid <s (256 :: sword32) \<and> ucast hw_asid < (256 :: sword32)
                           \<and> (0 :: sword32) <=s ucast hw_asid")
      prefer 2
      subgoal by (simp add: word_sless_msb_less ucast_less[THEN order_less_le_trans]
                            word_0_sle_from_less)
     apply (simp add: word_sless_def word_sle_def cslift_ptr_safe)
     apply (intro conjI)
       apply (erule iffD1 [OF cmap_relation_cong, rotated -1], simp_all)[1]
       apply (simp split: if_split_asm)
       apply (clarsimp simp: cpde_relation_def Let_def
                             pde_lift_pde_invalid
                       cong: ARM_H.pde.case_cong)
      apply (erule array_relation_update)
        subgoal by simp
       subgoal by (simp add: option_to_0_def)
      subgoal by simp
     apply (subst asid_map_pd_to_hwasids_update, assumption)
      subgoal by clarsimp
     apply (rule ext, simp add: pd_pointer_to_asid_slot_def map_comp_def split: if_split)
     apply (clarsimp simp: pde_stored_asid_def)
     apply (subst less_mask_eq)
      apply (rule order_less_le_trans, rule ucast_less)
       subgoal by simp
      subgoal by simp
     apply (subst ucast_up_ucast_id)
      subgoal by (simp add: is_up_def source_size_def target_size_def word_size)
     subgoal by simp
    apply wp[1]
   apply (rule findPDForASIDAssert_pd_at_wp2)
  apply (clarsimp simp: asidLowBits_handy_convs word_sle_def word_sless_def
                        Collect_const_mem asid_shiftr_low_bits_less)
  done

lemma invalidateHWASIDEntry_ccorres:
  "hwasid' = unat hwasid \<Longrightarrow>
   ccorres dc xfdc \<top> UNIV
   [] (invalidateHWASIDEntry hwasid)
      (Basic (\<lambda>s. globals_update (
          armKSHWASIDTable_'_update
            (\<lambda>_. Arrays.update (armKSHWASIDTable_' (globals s))
                hwasid' (scast asidInvalid))) s))"
  apply (clarsimp simp: invalidateHWASIDEntry_def)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: bind_def simpler_gets_def
                        simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def
                        Let_def)
  apply (clarsimp simp: carch_state_relation_def carch_globals_def
                        cmachine_state_relation_def)
  apply (simp add: array_relation_def split: if_split, erule allEI)
  apply (clarsimp simp: word_le_nat_alt)
  apply (simp add: option_to_0_def asidInvalid_def)
  done

lemma asid_map_pd_to_hwasids_clear:
  "\<lbrakk> pd \<notin> ran (option_map snd \<circ> m |` (- {asid}));
         \<forall>hw_asid pd'. m asid = Some (hw_asid, pd') \<longrightarrow> pd' = pd \<rbrakk> \<Longrightarrow>
   asid_map_pd_to_hwasids (m (asid := None))
        = (asid_map_pd_to_hwasids m) (pd := {})"
  apply (rule ext, rule set_eqI)
  apply (simp add: asid_map_pd_to_hwasids_def split: if_split)
  apply (intro conjI impI)
   apply (clarsimp elim!: ranE split: if_split_asm)
   apply (erule notE, rule ranI, simp add: restrict_map_def)
   apply (subst if_P, assumption)
   apply simp
  apply (simp add: ran_def split: if_split)
  apply (rule iffI)
   apply fastforce
  apply (erule exEI)
  apply clarsimp
  done

lemma invalidateASID_ccorres:
  "ccorres dc xfdc (valid_pde_mappings' and (\<lambda>_. asid \<le> mask asid_bits))
                   (UNIV \<inter> {s. asid_' s = asid}) []
     (invalidateASID asid) (Call invalidateASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_')
   apply (rule ccorres_Guard_Seq)+
   apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_findPDForASIDAssert])
     apply (rename_tac pd)
     apply (rule_tac P="\<lambda>s. pd_at_asid' pd asid s \<and> valid_pde_mappings' s
                               \<and> pd \<notin> ran (option_map snd o armKSASIDMap (ksArchState s)
                                                     |` (- {asid}))
                               \<and> option_map snd (armKSASIDMap (ksArchState s) asid) \<in> {None, Some pd}"
                   in ccorres_from_vcg[where P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: Collect_const_mem word_sle_def word_sless_def
                           asidLowBits_handy_convs simpler_gets_def
                           simpler_modify_def bind_def)
     apply (frule(2) pd_at_asid_cross_over)
     apply (clarsimp simp: typ_heap_simps)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           cpspace_relation_def
                           ptr_add_assertion_positive
                           array_assertion_shrink_right)
     apply (clarsimp simp: typ_heap_simps cmachine_state_relation_def
                           carch_state_relation_def pd_at_asid'_def carch_globals_def
                           fun_upd_def[symmetric] order_le_less_trans[OF word_and_le1]
                           arg_cong[where f="\<lambda>x. 2 ^ x", OF meta_eq_to_obj_eq, OF asid_low_bits_def])
     apply (intro conjI)
      apply (erule iffD1 [OF cmap_relation_cong, rotated -1], simp_all)[1]
      apply (simp split: if_split_asm)
      apply (clarsimp simp: cpde_relation_def Let_def
                            pde_lift_pde_invalid
                      cong: ARM_H.pde.case_cong)
     apply (subst asid_map_pd_to_hwasids_clear, assumption)
      subgoal by clarsimp
     apply (rule ext, simp add: pd_pointer_to_asid_slot_def map_comp_def split: if_split)
     subgoal by (clarsimp simp: pde_stored_asid_def)
    apply wp[1]
   apply (wp findPDForASIDAssert_pd_at_wp2)
  apply (clarsimp simp: asidLowBits_handy_convs word_sle_def word_sless_def
                        asid_shiftr_low_bits_less)
  done

definition
  "vm_fault_type_from_H fault \<equiv>
  case fault of
    vmfault_type.ARMDataAbort \<Rightarrow> (scast Kernel_C.ARMDataAbort :: word32)
  | vmfault_type.ARMPrefetchAbort \<Rightarrow> scast Kernel_C.ARMPrefetchAbort"

lemma handleVMFault_ccorres:
  "ccorres ((\<lambda>a ex v. ex = scast EXCEPTION_FAULT \<and> (\<exists>vf.
                      a = ArchFault (VMFault (seL4_Fault_VMFault_CL.address_CL vf) [instructionFault_CL vf, FSR_CL vf]) \<and>
                      errfault v = Some (SeL4_Fault_VMFault vf))) \<currency>
           (\<lambda>_. \<bottom>))
           (liftxf errstate id (K ()) ret__unsigned_long_')
           \<top>
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>vm_faultType = vm_fault_type_from_H vm_fault\<rbrace>)
          []
           (handleVMFault thread vm_fault)
           (Call handleVMFault_'proc)"
  apply (cinit lift: vm_faultType_')
   apply wpc
    apply (simp add: vm_fault_type_from_H_def Kernel_C.ARMDataAbort_def Kernel_C.ARMPrefetchAbort_def)
    apply (simp add: ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (ctac (no_vcg) add: getFAR_ccorres pre: ccorres_liftE_Seq)
     apply (ctac (no_vcg) add: getDFSR_ccorres pre: ccorres_liftE_Seq)
     apply clarsimp
     apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
     apply (clarsimp simp add: throwError_def throw_def return_def)
     apply (rule conseqPre)
      apply vcg
     apply (clarsimp simp: errstate_def)
     apply (clarsimp simp: EXCEPTION_FAULT_def EXCEPTION_NONE_def)
     apply (simp add: seL4_Fault_VMFault_lift)
    apply wp+
   apply (simp add: vm_fault_type_from_H_def Kernel_C.ARMDataAbort_def Kernel_C.ARMPrefetchAbort_def)
   apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff)
   apply (rule ccorres_rhs_assoc)+
   apply csymbr
   apply csymbr
   apply (ctac (no_vcg) pre: ccorres_liftE_Seq)
    apply (ctac (no_vcg) add: getIFSR_ccorres pre: ccorres_liftE_Seq)
     apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
     apply (clarsimp simp add: throwError_def throw_def return_def)
     apply (rule conseqPre)
      apply vcg
     apply (clarsimp simp: errstate_def)
     apply (clarsimp simp: EXCEPTION_FAULT_def EXCEPTION_NONE_def)
     apply (simp add: seL4_Fault_VMFault_lift)
    apply wp+
  apply simp
  done

lemma unat_asidLowBits [simp]:
  "unat Kernel_C.asidLowBits = asidLowBits"
  by (simp add: asidLowBits_def Kernel_C.asidLowBits_def asid_low_bits_def)

lemma rf_sr_asidTable_None:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; asid && mask asid_bits = asid; valid_arch_state' \<sigma>  \<rbrakk> \<Longrightarrow>
  (index (armKSASIDTable_' (globals x)) (unat (asid >> asid_low_bits)) = ap_Ptr 0) =
  (armKSASIDTable (ksArchState \<sigma>) (ucast (asid_high_bits_of asid)) = None)"
  apply (simp add: asid_high_bits_of_def ucast_ucast_mask)
  apply (subgoal_tac "(asid >> asid_low_bits) && mask 7 = asid >> asid_low_bits")(*asid_low_bits*)
   prefer 2
   apply (rule word_eqI)
   apply (subst (asm) bang_eq)
   apply (simp add: word_size nth_shiftr asid_bits_def asid_low_bits_def)
   apply (case_tac "n < 7", simp) (*asid_low_bits*)
   apply (clarsimp simp: linorder_not_less)
   apply (erule_tac x="n+10" in allE)
   apply (simp add: add.commute)
  apply simp
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)
  apply (simp add: array_relation_def option_to_0_def)
  apply (erule_tac x="asid >> asid_low_bits" in allE)
  apply (erule impE)
   prefer 2
   apply (drule sym [where t="index a b" for a b])
   apply (simp add: option_to_0_def option_to_ptr_def split: option.splits)
   apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def ran_def)
  apply (simp add: and_mask_eq_iff_le_mask)
  apply (simp add: asid_high_bits_def mask_def)
  done

lemma leq_asid_bits_shift:
  "x \<le> mask asid_bits \<Longrightarrow> (x::word32) >> asid_low_bits \<le> mask asid_high_bits"
  apply (rule word_leI)
  apply (simp add: nth_shiftr word_size)
  apply (rule ccontr)
  apply (clarsimp simp: linorder_not_less asid_high_bits_def asid_low_bits_def)
  apply (simp add: mask_def)
  apply (simp add: upper_bits_unset_is_l2p_32 [symmetric])
  apply (simp add: asid_bits_def word_bits_def)
  apply (erule_tac x="10+n" in allE)
  apply (simp add: linorder_not_less)
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done

lemma ucast_asid_high_bits_is_shift:
  "asid \<le> mask asid_bits \<Longrightarrow> ucast (asid_high_bits_of asid) = (asid >> asid_low_bits)"
  apply (simp add: mask_def upper_bits_unset_is_l2p_32 [symmetric])
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr nth_ucast asid_low_bits_def asid_bits_def word_bits_def)
  apply (erule_tac x="10+n" in allE)
  apply simp
  apply (case_tac "n < 7", simp) (*asid_low_bits*)
  apply (clarsimp simp add: linorder_not_less)
  apply (frule test_bit_size)
  apply (simp add: word_size)
  done





lemma cap_small_frame_cap_get_capFMappedASID_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_small_frame_cap\<rbrace>
         Call cap_small_frame_cap_get_capFMappedASID_'proc
       \<lbrace>\<acute>ret__unsigned_long =
             (cap_small_frame_cap_CL.capFMappedASIDHigh_CL (cap_small_frame_cap_lift \<^bsup>s\<^esup>cap) << asidLowBits)
               + (cap_small_frame_cap_CL.capFMappedASIDLow_CL (cap_small_frame_cap_lift \<^bsup>s\<^esup>cap))\<rbrace>"
  apply vcg
  apply (clarsimp simp: asidLowBits_def Kernel_C.asidLowBits_def word_sle_def
                        asid_low_bits_def)
  done

lemma cap_frame_cap_get_capFMappedASID_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_frame_cap\<rbrace>
         Call cap_frame_cap_get_capFMappedASID_'proc
       \<lbrace>\<acute>ret__unsigned_long =
             (cap_frame_cap_CL.capFMappedASIDHigh_CL (cap_frame_cap_lift \<^bsup>s\<^esup>cap) << asidLowBits)
               + (cap_frame_cap_CL.capFMappedASIDLow_CL (cap_frame_cap_lift \<^bsup>s\<^esup>cap))\<rbrace>"
  apply vcg
  apply (clarsimp simp: asidLowBits_def Kernel_C.asidLowBits_def word_sle_def
                        asid_low_bits_def)
  done



definition
  generic_frame_cap_get_capFMappedASID_CL :: "cap_CL option \<Rightarrow> word32" where
  "generic_frame_cap_get_capFMappedASID_CL \<equiv> \<lambda>cap. case cap of
      Some (Cap_small_frame_cap c) \<Rightarrow>
                 (cap_small_frame_cap_CL.capFMappedASIDHigh_CL  c << asidLowBits)
               + (cap_small_frame_cap_CL.capFMappedASIDLow_CL c)
    | Some (Cap_frame_cap c) \<Rightarrow>
                 (cap_frame_cap_CL.capFMappedASIDHigh_CL c << asidLowBits)
               + (cap_frame_cap_CL.capFMappedASIDLow_CL c)
    | Some _ \<Rightarrow> 0"

lemma generic_frame_cap_get_capFMappedASID_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_small_frame_cap \<or>
                cap_get_tag \<acute>cap = scast cap_frame_cap\<rbrace>
       Call generic_frame_cap_get_capFMappedASID_'proc
       \<lbrace>\<acute>ret__unsigned_long = generic_frame_cap_get_capFMappedASID_CL (cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: generic_frame_cap_get_capFMappedASID_CL_def  Kernel_C.asidLowBits_def word_sle_def )

  apply (intro conjI impI, simp_all)
    apply (clarsimp simp: cap_lift_small_frame_cap cap_small_frame_cap_lift_def)
   apply (clarsimp simp: cap_lift_frame_cap cap_frame_cap_lift_def)
  done


lemma generic_frame_cap_get_capFIsMapped_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_small_frame_cap \<or>
                cap_get_tag \<acute>cap = scast cap_frame_cap\<rbrace>
       Call generic_frame_cap_get_capFIsMapped_'proc
       \<lbrace>\<acute>ret__unsigned_long = (if generic_frame_cap_get_capFMappedASID_CL (cap_lift \<^bsup>s\<^esup>cap) \<noteq> 0 then 1 else 0)\<rbrace>"
  apply vcg
  apply (clarsimp simp: generic_frame_cap_get_capFMappedASID_CL_def if_distrib [where f=scast]
                  cong: if_cong)
  done




definition
  generic_frame_cap_get_capFMappedAddress_CL :: "cap_CL option \<Rightarrow> word32" where
  "generic_frame_cap_get_capFMappedAddress_CL \<equiv> \<lambda>cap. case cap of
      Some (Cap_small_frame_cap c) \<Rightarrow> cap_small_frame_cap_CL.capFMappedAddress_CL c
    | Some (Cap_frame_cap c) \<Rightarrow> cap_frame_cap_CL.capFMappedAddress_CL c
    | Some _ \<Rightarrow> 0"

lemma generic_frame_cap_get_capFMappedAddress_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_small_frame_cap \<or>
                cap_get_tag \<acute>cap = scast cap_frame_cap\<rbrace>
       Call generic_frame_cap_get_capFMappedAddress_'proc
       \<lbrace>\<acute>ret__unsigned_long = generic_frame_cap_get_capFMappedAddress_CL (cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: generic_frame_cap_get_capFMappedAddress_CL_def)
  apply (auto simp: cap_lift_small_frame_cap cap_small_frame_cap_lift_def
                    cap_lift_frame_cap cap_frame_cap_lift_def)
done



definition
  generic_frame_cap_set_capFMappedAddress_CL :: "cap_CL option \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> cap_CL option " where
  "generic_frame_cap_set_capFMappedAddress_CL \<equiv> \<lambda>cap asid addr. case cap of
      Some (Cap_small_frame_cap c) \<Rightarrow>
             Some ( Cap_small_frame_cap
                     (c \<lparr> cap_small_frame_cap_CL.capFMappedASIDHigh_CL := (asid >> asidLowBits) && mask asidHighBits,
                          cap_small_frame_cap_CL.capFMappedASIDLow_CL  := asid && mask asidLowBits,
                          cap_small_frame_cap_CL.capFMappedAddress_CL := addr AND NOT (mask 12) \<rparr>))
    | Some (Cap_frame_cap c) \<Rightarrow>
             Some ( Cap_frame_cap
                     (c \<lparr> cap_frame_cap_CL.capFMappedASIDHigh_CL := (asid >> asidLowBits) && mask asidHighBits,
                          cap_frame_cap_CL.capFMappedASIDLow_CL  := asid && mask asidLowBits,
                          cap_frame_cap_CL.capFMappedAddress_CL := addr AND NOT (mask 14) \<rparr>))
    | Some ccap \<Rightarrow> Some ccap"


lemma generic_frame_cap_set_capFMappedAddress_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_small_frame_cap \<or>
                cap_get_tag \<acute>cap = scast cap_frame_cap\<rbrace>
       Call generic_frame_cap_set_capFMappedAddress_'proc
       \<lbrace> cap_lift \<acute>ret__struct_cap_C
         = generic_frame_cap_set_capFMappedAddress_CL (cap_lift \<^bsup>s\<^esup>cap)  (\<^bsup>s\<^esup>asid ) (\<^bsup>s\<^esup>addr )  \<rbrace>"
  apply vcg
  apply (clarsimp simp: generic_frame_cap_set_capFMappedAddress_CL_def)
  apply (intro conjI impI)
    by (clarsimp simp: cap_lift_small_frame_cap cap_small_frame_cap_lift_def
                       cap_lift_frame_cap cap_frame_cap_lift_def)+

lemma clift_ptr_safe:
  "clift (h, x) ptr = Some a
  \<Longrightarrow> ptr_safe ptr x"
  by (erule lift_t_ptr_safe[where g = c_guard])

lemma generic_frame_cap_ptr_set_capFMappedAddress_spec:
  "\<forall>s cte_slot.
    \<Gamma> \<turnstile> \<lbrace>s. (\<exists> cap. cslift s \<^bsup>s\<^esup>cap_ptr = Some cap \<and> cap_lift cap \<noteq> None \<and>
                     (cap_get_tag cap = scast cap_small_frame_cap \<or>
                      cap_get_tag cap = scast cap_frame_cap)) \<and>
               \<acute>cap_ptr = cap_Ptr &(cte_slot\<rightarrow>[''cap_C'']) \<and>
               cslift s cte_slot \<noteq> None\<rbrace>
       Call generic_frame_cap_ptr_set_capFMappedAddress_'proc
       {t. (\<exists>cte' cap'.
           generic_frame_cap_set_capFMappedAddress_CL (cap_lift (the (cslift s \<^bsup>s\<^esup>cap_ptr))) \<^bsup>s\<^esup>asid \<^bsup>s\<^esup>addr = Some cap' \<and>
           cte_lift cte' = option_map (cap_CL_update (K cap')) (cte_lift (the (cslift s cte_slot))) \<and>
           t_hrs_' (globals t) = hrs_mem_update (heap_update cte_slot cte')
               (t_hrs_' (globals s)))}"
  apply vcg
  apply (clarsimp simp: typ_heap_simps)
  apply (subgoal_tac "cap_lift ret__struct_cap_C \<noteq> None")
   prefer 2
   apply (clarsimp simp: generic_frame_cap_set_capFMappedAddress_CL_def split: cap_CL.splits)
  apply (clarsimp simp: typ_heap_simps)
  apply (rule_tac x="cte_C.cap_C_update (\<lambda>_. ret__struct_cap_C) y" in exI)
  apply (case_tac y)
  apply (clarsimp simp: cte_lift_def typ_heap_simps')
  done

lemma lookupPDSlot_spec:
  "\<forall>s. \<Gamma> \<turnstile>  \<lbrace>s. array_assertion (pd_' s) (2 ^ pageBits) (hrs_htd (\<acute>t_hrs))\<rbrace>
  Call lookupPDSlot_'proc
  \<lbrace>  \<acute>ret__ptr_to_struct_pde_C =  Ptr (lookupPDSlot (ptr_val (pd_' s))  (vptr_' s)) \<rbrace>"
  apply vcg
  apply (clarsimp simp: lookupPDSlot_def)
  apply (simp add: ARM_A.lookup_pd_slot_def)
  apply (subst array_assertion_shrink_right, assumption)
   apply (rule unat_le_helper, simp)
   apply (rule order_less_imp_le, rule vptr_shiftr_le_2p)
  apply (simp add: Let_def word_sle_def)
  apply (case_tac pd)
  apply (simp add: word_shift_by_2)
  done

lemma lookupPTSlot_nofail_spec:
  "\<forall>s. \<Gamma> \<turnstile>  \<lbrace>s. array_assertion (pt_' s) (2 ^ (ptBits - 2)) (hrs_htd (\<acute>t_hrs))\<rbrace>
  Call lookupPTSlot_nofail_'proc
  \<lbrace>  \<acute>ret__ptr_to_struct_pte_C =  Ptr (lookup_pt_slot_no_fail (ptr_val (pt_' s))  (vptr_' s)) \<rbrace>"
  apply vcg
  apply (clarsimp simp: )
  apply (simp add: ARM_A.lookup_pt_slot_no_fail_def)
  apply (subst array_assertion_shrink_right, assumption)
   apply (rule order_less_imp_le, rule unat_less_helper, simp)
   apply (rule order_le_less_trans, rule word_and_le1, simp add: ptBits_def pageBits_def)
  apply (simp add: Let_def word_sle_def pteBits_def)
  apply (case_tac pt)
  apply (simp add: word_shift_by_2)
  done

lemma ccorres_pre_getObject_pde:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>pde. ko_at' pde p s \<longrightarrow> P pde s))
                  {s. \<forall>pde pde'. cslift s (pde_Ptr p) = Some pde' \<and> cpde_relation pde pde'
                           \<longrightarrow> s \<in> P' pde}
                          hs (getObject p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wp getPDE_wp empty_fail_getObject | simp)+
  apply clarsimp
  apply (erule cmap_relationE1 [OF rf_sr_cpde_relation],
         erule ko_at_projectKO_opt)
  apply simp
  done


(* FIXME: move *)
(* FIXME: delete duplicates in Corres_C *)
lemma ccorres_abstract_cleanup:
  "ccorres r xf G G' hs a c \<Longrightarrow>
   ccorres r xf G ({s. s \<in> S \<longrightarrow> s \<in> G'} \<inter> S) hs a c"
   by (fastforce intro: ccorres_guard_imp)

lemma pde_case_isPageTablePDE:
  "(case pde of PageTablePDE a b c \<Rightarrow> fn a b c | _ \<Rightarrow> g)
    = (if isPageTablePDE pde then fn (pdeTable pde) (pdeParity pde) (pdeDomain pde) else g)"
  by (cases pde, simp_all add: isPageTablePDE_def)

lemma ptrFromPAddr_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
   Call ptrFromPAddr_'proc
   \<lbrace>\<acute>ret__ptr_to_void =  Ptr (ptrFromPAddr (paddr_' s))\<rbrace>"
  apply vcg
  apply (simp add: ptrFromPAddr_def pptrBaseOffset_def pptrBase_def)
  done

lemma addrFromPPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
   Call addrFromPPtr_'proc
   \<lbrace>\<acute>ret__unsigned_long = addrFromPPtr (ptr_val (pptr_' s))\<rbrace>"
  apply vcg
  apply (simp add: addrFromPPtr_def pptrBaseOffset_def pptrBase_def)
  done

lemma addrFromKPPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
   Call addrFromKPPtr_'proc
   \<lbrace>\<acute>ret__unsigned_long = addrFromKPPtr (ptr_val (pptr_' s))\<rbrace>"
  apply vcg
  apply (simp add: addrFromKPPtr_def kernelELFBaseOffset_def kernelELFPAddrBase_def
                   kernelELFBase_def pptrBase_def mask_def)
  done

abbreviation
  "lookupPTSlot_xf \<equiv> liftxf errstate lookupPTSlot_ret_C.status_C lookupPTSlot_ret_C.ptSlot_C ret__struct_lookupPTSlot_ret_C_'"

lemma lookupPTSlot_ccorres:
  "ccorres (lookup_failure_rel \<currency> (\<lambda>rv rv'. rv' = pte_Ptr rv)) lookupPTSlot_xf
       (page_directory_at' pd)
       (UNIV \<inter> \<lbrace>\<acute>pd = Ptr pd \<rbrace> \<inter> \<lbrace>\<acute>vptr = vptr  \<rbrace>)
       []
       (lookupPTSlot pd vptr)
       (Call lookupPTSlot_'proc)"
  apply (cinit lift: pd_' vptr_')
   apply (simp add: liftE_bindE pde_case_isPageTablePDE)
   apply (rule ccorres_pre_getObject_pde)
   apply csymbr
   apply csymbr
   apply (rule ccorres_abstract_cleanup)
   apply (rule_tac P="(ret__unsigned = scast pde_pde_coarse) = (isPageTablePDE pde)"
               in ccorres_gen_asm2)
   apply (rule ccorres_cond2'[where R=\<top>])
     apply (clarsimp simp: Collect_const_mem)
    apply simp
    apply (rule_tac P=\<top> and P' =UNIV in ccorres_from_vcg_throws)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def)
    apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
    apply (simp add: lookup_fault_missing_capability_lift)
    apply (simp add: mask_def)
   apply (rule ccorres_rhs_assoc)+
   apply (simp add: checkPTAt_def bind_liftE_distrib liftE_bindE
                    returnOk_liftE[symmetric])
   apply (rule ccorres_stateAssert)
   apply (rule_tac P="page_table_at' (ptrFromPAddr (pdeTable pde))
                      and ko_at' pde (lookup_pd_slot pd vptr) and K (isPageTablePDE pde)"
               and P'=UNIV
            in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: returnOk_def return_def Collect_const_mem
                         lookup_pd_slot_def word_sle_def)
   apply (frule(1) page_table_at_rf_sr, clarsimp)
   apply (erule cmap_relationE1[OF rf_sr_cpde_relation], erule ko_at_projectKO_opt)
   apply (clarsimp simp: typ_heap_simps cpde_relation_def Let_def isPageTablePDE_def
                         pde_pde_coarse_lift_def pde_pde_coarse_lift
                  split: pde.split_asm split_of_bool_asm)
    apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift; simp)
     apply (rule unat_le_helper, rule order_trans[OF word_and_le1], simp)
    apply (simp add: word_shift_by_2 lookup_pt_slot_no_fail_def)
   apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift; simp)
    apply (rule unat_le_helper, rule order_trans[OF word_and_le1], simp)
   apply (simp add: word_shift_by_2 lookup_pt_slot_no_fail_def)
  apply (clarsimp simp: Collect_const_mem h_t_valid_clift)
  apply (frule(1) page_directory_at_rf_sr, clarsimp)
  apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
   apply (simp add: pageBits_def)
  apply (clarsimp simp: cpde_relation_def pde_pde_coarse_lift_def
                        pde_pde_coarse_lift Let_def isPageTablePDE_def
                 split: ARM_H.pde.split_asm)
  done

(* FIXME: MOVE to CSpaceAcc_C *)
lemma ccorres_pre_gets_armKSASIDTable_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. armKSASIDTable (ksArchState s) = rv  \<longrightarrow> P rv s))
                  {s. \<forall>rv. s \<in> P' rv }
                          hs (gets (armKSASIDTable \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply clarsimp
  done



abbreviation
  "findPDForASID_xf \<equiv> liftxf errstate findPDForASID_ret_C.status_C findPDForASID_ret_C.pd_C ret__struct_findPDForASID_ret_C_'"



lemma ccorres_pre_getObject_asidpool:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>asidpool. ko_at' asidpool p s \<longrightarrow> P asidpool s))
                  {s. \<forall> asidpool asidpool'. cslift s (ap_Ptr p) = Some asidpool' \<and> casid_pool_relation asidpool asidpool'
                           \<longrightarrow> s \<in> P' asidpool}
                          hs (getObject p >>= (\<lambda>rv :: asidpool. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wpsimp wp: getASID_wp empty_fail_getObject)+
  apply (erule cmap_relationE1 [OF rf_sr_cpspace_asidpool_relation],
         erule ko_at_projectKO_opt)
  apply simp
  done

lemma findPDForASID_ccorres:
  "ccorres (lookup_failure_rel \<currency> (\<lambda>pdeptrc pdeptr. pdeptr = pde_Ptr pdeptrc)) findPDForASID_xf
       (valid_arch_state' and no_0_obj' and (\<lambda>_. asid \<le> mask asid_bits))
       (UNIV \<inter> \<lbrace>\<acute>asid = asid\<rbrace> )
       []
       (findPDForASID asid)
       (Call findPDForASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_')
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_assertE)
   apply (rule ccorres_assertE)
   apply (rule ccorres_liftE_Seq)
   apply (rule_tac  r'="\<lambda>asidTable rv'. rv' = option_to_ptr (asidTable (ucast (asid_high_bits_of asid)))"
               and xf'=poolPtr_' in ccorres_split_nothrow)
       apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: simpler_gets_def Kernel_C.asidLowBits_def)
       apply (simp add: ucast_asid_high_bits_is_shift)
       apply (erule rf_sr_armKSASIDTable)
       apply (drule leq_asid_bits_shift)
       apply (simp add: asid_high_bits_def mask_def)
      apply ceqv
     apply (simp add: liftME_def)
     apply (simp add: bindE_assoc)
     apply (rename_tac asidTable poolPtr)

     apply (subgoal_tac "(doE x \<leftarrow> case asidTable (ucast (asid_high_bits_of asid)) of
                                     None \<Rightarrow> throw Fault_H.lookup_failure.InvalidRoot
                                  |  Some ptr \<Rightarrow> withoutFailure $ getObject ptr;
                              (case inv asidpool.ASIDPool x (asid && mask asid_low_bits) of
                                     None \<Rightarrow> throw Fault_H.lookup_failure.InvalidRoot
                                   | Some ptr \<Rightarrow> doE haskell_assertE (ptr \<noteq> 0) [];
                                                     withoutFailure $ checkPDAt ptr;
                                                     returnOk ptr
                                                 odE)
                           odE) =
                          (if ( asidTable (ucast (asid_high_bits_of asid))=None)
                             then (doE x\<leftarrow> throw Fault_H.lookup_failure.InvalidRoot;
                                       (case inv asidpool.ASIDPool x (asid && mask asid_low_bits) of
                                     None \<Rightarrow> throw Fault_H.lookup_failure.InvalidRoot
                                   | Some ptr \<Rightarrow> doE haskell_assertE (ptr \<noteq> 0) [];
                                                     withoutFailure $ checkPDAt ptr;
                                                     returnOk ptr
                                                 odE)
                                  odE)
                             else (doE x\<leftarrow> withoutFailure $ getObject (the (asidTable (ucast (asid_high_bits_of asid))));
                                      (case inv asidpool.ASIDPool x (asid && mask asid_low_bits) of
                                     None \<Rightarrow> throw Fault_H.lookup_failure.InvalidRoot
                                   | Some ptr \<Rightarrow> doE haskell_assertE (ptr \<noteq> 0) [];
                                                     withoutFailure $ checkPDAt ptr;
                                                     returnOk ptr
                                                 odE)
                                  odE))")

      prefer 2
      apply (case_tac "asidTable (ucast (asid_high_bits_of asid))", clarsimp, clarsimp)

     apply simp
     apply (thin_tac "a = (if b then c else d)" for a b c d)

     apply (rule_tac Q="\<lambda>s. asidTable = (armKSASIDTable (ksArchState s))\<and> valid_arch_state' s \<and> no_0_obj' s \<and> (asid \<le> mask asid_bits) "
                 and Q'="\<lambda>s'. option_to_ptr (asidTable (ucast (asid_high_bits_of asid))) =
                              index (armKSASIDTable_' (globals s')) (unat (asid >> asid_low_bits))"
                 in ccorres_if_cond_throws)
        apply clarsimp
        apply (subgoal_tac "asid && mask asid_bits = asid")
         prefer 2
         apply (rule less_mask_eq)
         apply (simp add: mask_def)
        apply (simp add: rf_sr_asidTable_None [symmetric] Collect_const_mem)

       apply (rule_tac P=\<top> and P' =UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: throwError_def return_def bindE_def bind_def NonDetMonad.lift_def)
       apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
       apply (simp add: lookup_fault_lift_invalid_root)

      apply (simp add: Collect_const[symmetric] del: Collect_const)
      apply (rule ccorres_liftE_Seq)
      apply (rule ccorres_pre_getObject_asidpool)
      apply (rule ccorres_Guard_Seq)+

(*Note for Tom: apply wpc breaks here - blocks everything, cannot be interrupted *)
      apply (case_tac "inv ASIDPool rv (asid && mask asid_low_bits) = Some 0")
       apply simp
       apply (rule ccorres_fail')
      apply (rule_tac P="\<lambda>s. asidTable=armKSASIDTable (ksArchState s) \<and>
                              valid_arch_state' s \<and>  (asid \<le> mask asid_bits) "
                   and P'= "{s'. (\<exists>  ap'. cslift s' (ap_Ptr (the (asidTable (ucast (asid_high_bits_of asid)))))
                                             = Some ap' \<and> casid_pool_relation rv ap')}"
                   in ccorres_from_vcg_throws_nofail)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: ucast_asid_high_bits_is_shift)
      apply (frule_tac idx="(asid >> asid_low_bits)" in rf_asidTable, assumption,
                        simp add:  leq_asid_bits_shift)
      apply (clarsimp simp: option_to_ptr_def option_to_0_def)
      apply (clarsimp simp: typ_heap_simps)
      apply (case_tac rv, clarsimp simp: inv_def)
      apply (simp add:casid_pool_relation_def)
      apply (case_tac ap', simp)
      apply (simp add: array_relation_def)
      apply (erule_tac x="(asid && 2 ^ asid_low_bits - 1)" in allE)
      apply (simp add: word_and_le1 mask_def option_to_ptr_def option_to_0_def)
      apply (rename_tac "fun" array)
      apply (case_tac "fun (asid && 2 ^ asid_low_bits - 1)", clarsimp)
       apply (clarsimp simp: throwError_def  return_def )
       apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
       apply (simp add: lookup_fault_lift_invalid_root)
      apply (clarsimp simp: returnOk_def return_def
        checkPDAt_def in_monad stateAssert_def liftE_bindE
        get_def bind_def assert_def fail_def
        split:if_splits)
     apply vcg
    apply simp
    apply wp
   apply vcg
  apply (clarsimp simp: Collect_const_mem)
  apply (simp add: Kernel_C.asidLowBits_def word_sle_def
                   asid_shiftr_low_bits_less order_le_less_trans[OF word_and_le1]
                   arg_cong[where f="\<lambda>x. 2 ^ x", OF meta_eq_to_obj_eq, OF asid_low_bits_def])
  apply (clarsimp simp: option_to_0_def option_to_ptr_def)
  apply (clarsimp simp: typ_heap_simps split: option.split_asm)
done


lemma ccorres_pre_gets_armKSGlobalPD_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. armKSGlobalPD (ksArchState s) = rv  \<longrightarrow> P rv s))
                  (P' (ptr_val armKSGlobalPD_Ptr))
                  hs (gets (armKSGlobalPD \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (drule rf_sr_armKSGlobalPD)
  apply simp
  done

lemma invalidateTranslationASIDLocal_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>hw_asid = hw_asid \<rbrace>) []
           (doMachineOp (invalidateLocalTLB_ASID hw_asid))
           (Call invalidateTranslationASIDLocal_'proc)"
  apply cinit'
  apply (ctac (no_vcg) add: invalidateLocalTLB_ASID_ccorres)
  apply clarsimp
  done

lemma invalidateTranslationASID_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>hw_asid = hw_asid \<rbrace>) []
           (doMachineOp (invalidateLocalTLB_ASID hw_asid))
           (Call invalidateTranslationASID_'proc)"
  apply cinit'
  apply (ctac (no_vcg) add: invalidateTranslationASIDLocal_ccorres)
  apply clarsimp
  done

lemma flushSpace_ccorres:
  "ccorres dc xfdc (valid_pde_mappings' and (\<lambda>_. asid \<le> mask asid_bits)) (UNIV \<inter> {s. asid_' s = asid}) []
       (flushSpace asid) (Call flushSpace_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_')
   apply (ctac (no_vcg) add: loadHWASID_ccorres)
    apply (ctac (no_vcg) add: cleanCaches_PoU_ccorres)
     apply csymbr
     apply (simp add: case_option_If2)
     apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws2)
        apply (clarsimp simp: Collect_const_mem pde_stored_asid_def)
        apply (simp add: if_split_eq1 to_bool_def)
       apply (rule ccorres_return_void_C)
      apply csymbr
      apply (clarsimp simp: pde_stored_asid_def)
      apply (case_tac "to_bool (stored_asid_valid_CL (pde_pde_invalid_lift stored_hw_asid___struct_pde_C))")
       prefer 2
       apply clarsimp
      apply clarsimp
      apply (case_tac "pde_get_tag stored_hw_asid___struct_pde_C = scast pde_pde_invalid")
       prefer 2
       apply clarsimp
      apply clarsimp
      apply (rule ccorres_call,
             rule invalidateTranslationASID_ccorres,
             simp+)[1]
     apply vcg
    apply wp+
  apply simp
  done



(* FIXME: MOVE *)
lemma ccorres_pre_gets_armKSHWASIDTable_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. armKSHWASIDTable (ksArchState s) = rv  \<longrightarrow> P rv s))
                  {s. \<forall>rv. s \<in> P' rv }
                          hs (gets (armKSHWASIDTable \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply clarsimp
  done

(* FIXME: MOVE *)
lemma ccorres_pre_gets_armKSNextASID_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. armKSNextASID (ksArchState s) = rv  \<longrightarrow> P rv s))
                  {s. \<forall>rv. s \<in> P' rv }
                          hs (gets (armKSNextASID \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply clarsimp
  done


lemma ccorres_from_vcg_might_throw:
  "(\<forall>\<sigma>. Gamm \<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> sr} c
                 {s. \<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> sr \<and> r rv (xf s)},
                 {s. \<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> sr \<and> arrel rv (axf s)})
     \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf P P' (SKIP # hs) a c"
  apply (rule ccorresI')
  apply (drule_tac x=s in spec)
  apply (erule exec_handlers.cases, simp_all)
   apply clarsimp
   apply (erule exec_handlers.cases, simp_all)[1]
    apply (auto elim!: exec_Normal_elim_cases)[1]
   apply (drule(1) exec_abrupt[rotated])
    apply simp
   apply (clarsimp simp: unif_rrel_simps elim!: exec_Normal_elim_cases)
   apply fastforce
  apply (clarsimp simp: unif_rrel_simps)
  apply (drule hoare_sound)
  apply (clarsimp simp: cvalid_def HoarePartialDef.valid_def)
  apply fastforce
  done

lemma rf_sr_armKSASIDTable_rel:
  "(s, s') \<in> rf_sr
    \<Longrightarrow> array_relation ((=) \<circ> option_to_0) 0xFF (armKSHWASIDTable (ksArchState s))
                               (armKSHWASIDTable_' (globals s'))"
  by (clarsimp simp: rf_sr_def cstate_relation_def
                     Let_def carch_state_relation_def)

lemma rf_sr_armKSASIDTable_rel':
  "\<lbrakk> (s, s') \<in> rf_sr; valid_arch_state' s \<rbrakk>
    \<Longrightarrow> index (armKSHWASIDTable_' (globals s')) (unat x) =
         option_to_0 (armKSHWASIDTable (ksArchState s) x)
            \<and> ((option_to_0 (armKSHWASIDTable (ksArchState s) x) = 0)
                    = (armKSHWASIDTable (ksArchState s) x = None))"
  apply (rule conjI)
   apply (drule rf_sr_armKSASIDTable_rel)
   apply (clarsimp simp: array_relation_def)
   apply (rule sym, drule spec, erule mp)
   apply (rule order_trans, rule word_n1_ge)
   apply simp
  apply (clarsimp simp: option_to_0_def split: option.splits)
  apply (clarsimp simp: valid_arch_state'_def valid_asid_map'_def)
  apply (drule (1) is_inv_SomeD)
  apply (drule subsetD, fastforce)
  apply simp
  done

lemma rf_sr_armKSNextASID:
  "(s, s') \<in> rf_sr \<Longrightarrow> armKSNextASID_' (globals s') = armKSNextASID (ksArchState s)"
  by (clarsimp simp: rf_sr_def cstate_relation_def
                     Let_def carch_state_relation_def)

end

context begin interpretation Arch . (*FIXME: arch_split*)

crunch armKSNextASID[wp]: invalidateASID
    "\<lambda>s. P (armKSNextASID (ksArchState s))"
crunch armKSNextASID[wp]: invalidateHWASIDEntry
    "\<lambda>s. P (armKSNextASID (ksArchState s))"

end

context kernel_m begin

lemma findFreeHWASID_ccorres:
  "ccorres (=) ret__unsigned_char_'
       (valid_arch_state' and valid_pde_mappings') UNIV []
       (findFreeHWASID) (Call findFreeHWASID_'proc)"
  apply (cinit)
   apply csymbr
   apply (rule ccorres_pre_gets_armKSHWASIDTable_ksArchState)
   apply (rule ccorres_pre_gets_armKSNextASID_ksArchState)
   apply (simp add: whileAnno_def case_option_find_give_me_a_map
                    mapME_def
               del: Collect_const map_append)
   apply (rule ccorres_splitE_novcg)
       apply (subgoal_tac "[nextASID .e. maxBound] @ init [minBound .e. nextASID]
                               = map (\<lambda>x. nextASID + (of_nat x)) [0 ..< 256]")
        apply (rule_tac xf=hw_asid_offset_' and i=0
                     and xf_update=hw_asid_offset_'_update
                     and r'=dc and xf'=xfdc and Q=UNIV
                     and F="\<lambda>n s. hwASIDTable = armKSHWASIDTable (ksArchState s)
                                  \<and> nextASID = armKSNextASID (ksArchState s)
                                  \<and> valid_arch_state' s"
                   in ccorres_sequenceE_while_gen')
              apply (rule ccorres_from_vcg_might_throw)
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: rf_sr_armKSNextASID)
              apply (subst down_cast_same [symmetric],
                     simp add: is_down_def target_size_def source_size_def word_size)+
              apply (simp add: ucast_ucast_mask
                               ucast_ucast_add ucast_and_mask
                               ucast_of_nat_small asidInvalid_def
                               word_sless_msb_less ucast_less[THEN order_less_le_trans]
                               word_0_sle_from_less)
              apply (simp add: word_sint_msb_eq not_msb_from_less word_of_nat_less
                               trans[OF msb_nth nth_ucast] bang_big word_size
                               uint_up_ucast is_up_def source_size_def
                               target_size_def)
              apply (rule conjI, rule order_trans[OF _ uint_add_ge0], simp)
              apply (simp add: rf_sr_armKSASIDTable_rel'
                               throwError_def return_def split: if_split)
              apply (clarsimp simp: returnOk_def return_def)
              apply (uint_arith, simp add: take_bit_nat_def unsigned_of_nat)
             apply (simp add: mask_def)
             apply unat_arith
            apply (rule conseqPre, vcg)
            apply clarsimp
           apply simp
           apply (rule hoare_pre, wp)
           apply simp
          apply simp
         apply simp
        apply simp

       apply (cut_tac x=nextASID in leq_maxBound[unfolded word_le_nat_alt])
       apply (simp add: minBound_word init_def maxBound_word minus_one_norm)
       apply (simp add: upto_enum_word)
       apply (rule nth_equalityI)
        apply (simp del: upt.simps)
       apply (simp del: upt.simps)
       apply (simp add: nth_append
                 split: if_split)

      apply ceqv
     apply (rule ccorres_assert)
     apply (rule_tac A="\<lambda>s. nextASID = armKSNextASID (ksArchState s)
                             \<and> hwASIDTable = armKSHWASIDTable (ksArchState s)
                             \<and> valid_arch_state' s \<and> valid_pde_mappings' s"
                in ccorres_guard_imp2[where A'=UNIV])
      apply (simp add: split_def)
      apply (rule ccorres_symb_exec_r)
        apply (rule_tac xf'=hw_asid_' in ccorres_abstract, ceqv)
        apply (rule_tac P="rv'a = nextASID" in ccorres_gen_asm2)
        apply (simp del: Collect_const)
        apply ((rule ccorres_move_const_guard )+)?
        apply (ctac(no_vcg) add: invalidateASID_ccorres)
         apply ((rule ccorres_move_const_guard
                    | simp only: ccorres_seq_simps)+)?
         apply (ctac(no_vcg) add: invalidateTranslationASID_ccorres)
          apply (rule ccorres_split_nothrow)
              apply (rule ccorres_move_const_guard )+
              apply (rule ccorres_handlers_weaken)
              apply (rule invalidateHWASIDEntry_ccorres[OF refl])
             apply ceqv
            apply (rule_tac P="\<lambda>s. nextASID = armKSNextASID (ksArchState s)"
                        in ccorres_from_vcg_throws[where P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp del: rf_sr_upd_safe)
            apply (clarsimp simp: rf_sr_def bind_def simpler_modify_def
                                  return_def cstate_relation_def Let_def)
            apply (simp add: carch_state_relation_def carch_globals_def
                             cmachine_state_relation_def)
            apply (subst down_cast_same [symmetric],
              simp add: is_down_def target_size_def source_size_def word_size)+
            apply (clarsimp simp: maxBound_word minBound_word
                                  ucast_ucast_add minus_one_norm
                           split: if_split)
            apply (simp add: word_sint_msb_eq uint_up_ucast word_size
                             msb_nth nth_ucast bang_big is_up_def source_size_def
                             target_size_def)
            apply uint_arith
            subgoal by simp
           apply wp
          apply vcg
         apply simp
         apply wp[1]
        apply simp
        apply wp
       apply vcg
      apply (rule conseqPre, vcg)
      apply clarsimp
     apply (drule_tac x=nextASID in bspec, simp)
     apply (clarsimp simp: rf_sr_armKSNextASID
                           rf_sr_armKSASIDTable_rel'
                           valid_arch_state'_def
                           valid_asid_map'_def
                           Collect_const_mem word_sless_msb_less
                           ucast_less[THEN order_less_le_trans]
                           word_0_sle_from_less)
     apply (frule(1) is_inv_SomeD, clarsimp)
     apply (drule subsetD, erule domI)
     apply simp
    apply (fold mapME_def)
    apply (wp mapME_wp')
    apply (rule hoare_pre, wp)
    apply simp
   apply (clarsimp simp: guard_is_UNIV_def)
  apply simp
  done

lemma all_invs_but_ct_idle_or_in_cur_domain_valid_pde_mappings':
  "all_invs_but_ct_idle_or_in_cur_domain' s \<longrightarrow> valid_pde_mappings' s"
  by (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def)

lemma invs_valid_pde_mappings':
  "invs' s \<longrightarrow> valid_pde_mappings' s"
  by (clarsimp simp: invs'_def valid_state'_def)

lemmas invs_valid_pde_mappings'[rule_format, elim!]

lemma getHWASID_ccorres:
  "ccorres (=) ret__unsigned_char_'
     (all_invs_but_ct_idle_or_in_cur_domain' and (\<lambda>s. asid \<le> mask asid_bits)) (UNIV \<inter> {s. asid_' s = asid}) []
     (getHWASID asid) (Call getHWASID_'proc)"
  apply (cinit lift: asid_')
   apply (ctac(no_vcg) add: loadHWASID_ccorres)
    apply csymbr
    apply wpc
     apply (rule ccorres_cond_false)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply simp
     apply (ctac(no_vcg) add: findFreeHWASID_ccorres)
      apply (ctac(no_vcg) add: storeHWASID_ccorres)
       apply (rule ccorres_return_C, simp+)[1]
      apply wp+
     apply (strengthen all_invs_but_ct_idle_or_in_cur_domain_valid_pde_mappings')
     apply (wp findFreeHWASID_invs_no_cicd')
    apply (rule ccorres_cond_true)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: return_def pde_stored_asid_def
                   split: if_split_asm)
   apply wp
  apply (clarsimp simp: pde_stored_asid_def)
  apply (clarsimp simp: to_bool_def split: if_split)
  apply (auto simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
  done


lemma armv_contextSwitch_ccorres:
  "ccorres dc xfdc (all_invs_but_ct_idle_or_in_cur_domain' and (\<lambda>s. asid \<le> mask asid_bits))
                   (UNIV \<inter> {s. cap_pd_' s =  pde_Ptr pd} \<inter> {s. asid_' s = asid} ) []
       (armv_contextSwitch pd asid) (Call armv_contextSwitch_'proc)"
  apply (cinit lift: cap_pd_' asid_')
   apply simp
   apply (ctac(no_vcg) add: getHWASID_ccorres)
    apply (ctac (no_vcg)add: armv_contextSwitch_HWASID_ccorres)
   apply wp
  apply clarsimp
  done

(* FIXME: move *)
lemma ccorres_h_t_valid_armKSGlobalPD:
  "ccorres r xf P P' hs f (f' ;; g') \<Longrightarrow>
   ccorres r xf P P' hs f (Guard C_Guard {s'. s' \<Turnstile>\<^sub>c armKSGlobalPD_Ptr} f';; g')"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_move_c_guards[where P = \<top>])
    apply clarsimp
    apply assumption
   apply simp
  by (simp add:rf_sr_def cstate_relation_def Let_def)

lemma setVMRoot_ccorres:
  "ccorres dc xfdc (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' thread) (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr thread}) []
       (setVMRoot thread) (Call setVMRoot_'proc)"
  apply (cinit lift: tcb_')
   apply (rule ccorres_move_array_assertion_tcb_ctes)
   apply (rule ccorres_move_c_guard_tcb_ctes)
   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv)
   apply (ctac)
     apply csymbr
     apply csymbr
     apply (simp add: cap_get_tag_isCap_ArchObject2 del: Collect_const)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: cap_case_isPageDirectoryCap cong: if_cong)
      apply (rule ccorres_cond_true_seq)
      apply (rule ccorres_rhs_assoc)
      apply (simp add: throwError_def catch_def)
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_h_t_valid_armKSGlobalPD)
      apply csymbr
      apply (rule ccorres_pre_gets_armKSGlobalPD_ksArchState)
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: setCurrentPD_ccorres)
       apply (rule ccorres_split_throws)
        apply (rule ccorres_return_void_C)
       apply vcg
      apply wp
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr
     apply (rule_tac P="to_bool (capPDIsMapped_CL (cap_page_directory_cap_lift threadRoot))
                              = (capPDMappedASID (capCap rv) \<noteq> None)"
                   in ccorres_gen_asm2)
     apply (simp add: to_bool_def del: Collect_const)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: cap_case_isPageDirectoryCap cong: if_cong)
      apply (simp add: throwError_def catch_def)
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_h_t_valid_armKSGlobalPD)
      apply csymbr
      apply (rule ccorres_pre_gets_armKSGlobalPD_ksArchState)
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: setCurrentPD_ccorres)
       apply (rule ccorres_split_throws)
        apply (rule ccorres_return_void_C)
       apply vcg
      apply wp
     apply (simp add: cap_case_isPageDirectoryCap)
     apply (simp add: catch_def)
     apply csymbr
     apply csymbr
     apply csymbr
     apply csymbr
     apply (simp add: liftE_bindE)
     apply (simp add: bindE_bind_linearise bind_assoc liftE_def)

     apply (rule_tac f'=lookup_failure_rel and r'="\<lambda>pdeptrc pdeptr. pdeptr = pde_Ptr pdeptrc"
                 and xf'=find_ret_'
                 in ccorres_split_nothrow_case_sum)
          apply (ctac add: findPDForASID_ccorres)
         apply ceqv
        apply (rule_tac P="capPDBasePtr_CL (cap_page_directory_cap_lift threadRoot)
                              = capPDBasePtr (capCap rv)"
                     in ccorres_gen_asm2)
        apply (simp del: Collect_const)
        apply (rule ccorres_Cond_rhs_Seq)
         apply (simp add: whenE_def throwError_def
                          checkPDNotInASIDMap_def checkPDASIDMapMembership_def)
         apply (rule ccorres_stateAssert)
         apply (rule ccorres_pre_gets_armKSGlobalPD_ksArchState)
         apply (rule ccorres_rhs_assoc)+
         apply (rule ccorres_h_t_valid_armKSGlobalPD)
         apply csymbr
         apply (rule ccorres_add_return2)
         apply (ctac(no_vcg) add: setCurrentPD_ccorres)
          apply (rule ccorres_split_throws)
           apply (rule ccorres_return_void_C)
          apply vcg
         apply wp
        apply (simp add: whenE_def returnOk_def)
        apply (ctac (no_vcg) add: armv_contextSwitch_ccorres)
       apply (simp add: checkPDNotInASIDMap_def checkPDASIDMapMembership_def)
       apply (rule ccorres_stateAssert)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_pre_gets_armKSGlobalPD_ksArchState)
       apply (rule ccorres_h_t_valid_armKSGlobalPD)
       apply csymbr
       apply (rule ccorres_add_return2)
       apply (ctac(no_vcg) add: setCurrentPD_ccorres)
        apply (rule ccorres_split_throws)
         apply (rule ccorres_return_void_C)
        apply vcg
       apply wp
      apply simp
      apply (wp hoare_drop_imps)[1]
     apply (simp add: Collect_const_mem)
     apply (vcg exspec=findPDForASID_modifies)
    apply (simp add: getSlotCap_def)
    apply (wp getCTE_wp')
   apply (simp add: Collect_const_mem)
   apply vcg
  apply (clarsimp simp: Collect_const_mem word_sle_def)
  apply (rule conjI)
   apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
   apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp+)
   apply (auto simp: isCap_simps valid_cap'_def mask_def)[1]
  apply (clarsimp simp: size_of_def cte_level_bits_def
                        tcbVTableSlot_def tcb_cnode_index_defs
                        ccap_rights_relation_def cap_rights_to_H_def allRights_def
                        mask_def[where n="Suc 0"]
                        cte_at_tcb_at_16' addrFromPPtr_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject2
                 dest!: isCapDs)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric]
                        cap_lift_page_directory_cap cap_to_H_def
                        cap_page_directory_cap_lift_def
                 elim!: ccap_relationE split: if_split_asm)
  done

lemma setVMRootForFlush_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_'
       (invs' and (\<lambda>s. asid \<le> mask asid_bits))
       (UNIV \<inter> {s. pd_' s = pde_Ptr pd} \<inter> {s. asid_' s = asid}) []
       (setVMRootForFlush pd asid) (Call setVMRootForFlush_'proc)"
  apply (cinit lift: pd_' asid_')
   apply (rule ccorres_pre_getCurThread)
   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv
               del: Collect_const)
   apply (rule ccorres_Guard_Seq)+
   apply (ctac add: getSlotCap_h_val_ccorres)
     apply csymbr
     apply csymbr
     apply (simp add: cap_get_tag_isCap_ArchObject2
                 del: Collect_const)
     apply (rule ccorres_if_lhs)
      apply (rule_tac P="(capPDIsMapped_CL (cap_page_directory_cap_lift threadRoot) = 0)
                             = (capPDMappedASID (capCap rv) = None)
                         \<and> capPDBasePtr_CL (cap_page_directory_cap_lift threadRoot)
                             = capPDBasePtr (capCap rv)" in ccorres_gen_asm2)
      apply (rule ccorres_rhs_assoc | csymbr | simp add: Collect_True del: Collect_const)+
      apply (rule ccorres_split_throws)
       apply (rule ccorres_return_C, simp+)
      apply vcg
     apply (rule ccorres_rhs_assoc2,
            rule ccorres_rhs_assoc2,
            rule ccorres_symb_exec_r)
       apply simp
       apply (ctac (no_vcg)add: armv_contextSwitch_ccorres)
        apply (ctac add: ccorres_return_C)
       apply wp
      apply simp
      apply vcg
     apply (rule conseqPre, vcg)
     apply (simp add: Collect_const_mem)
     apply clarsimp
    apply simp
    apply (wp hoare_drop_imps)
   apply vcg
  apply (clarsimp simp: Collect_const_mem word_sle_def
                        ccap_rights_relation_def cap_rights_to_H_def
                        mask_def[where n="Suc 0"]
                        allRights_def size_of_def cte_level_bits_def
                        tcbVTableSlot_def Kernel_C.tcbVTable_def invs'_invs_no_cicd)
  apply (clarsimp simp: rf_sr_ksCurThread ptr_add_assertion_positive)
  apply (subst rf_sr_tcb_ctes_array_assertion[THEN array_assertion_shrink_right],
    assumption, simp add: tcb_at_invs', simp add: tcb_cnode_index_defs)+
  apply (clarsimp simp: rf_sr_ksCurThread ptr_val_tcb_ptr_mask' [OF tcb_at_invs'])
  apply (frule cte_at_tcb_at_16'[OF tcb_at_invs'], clarsimp simp: cte_wp_at_ctes_of)
  apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
  apply (clarsimp simp: typ_heap_simps')
  apply (case_tac "isArchObjectCap rv \<and> isPageDirectoryCap (capCap rv)")
   apply (clarsimp simp: isCap_simps(2) cap_get_tag_isCap_ArchObject[symmetric])
   apply (clarsimp simp: cap_page_directory_cap_lift cap_to_H_def
                  elim!: ccap_relationE)
   apply (simp add: to_bool_def split: if_split)
  by (auto simp: cap_get_tag_isCap_ArchObject2)



(* FIXME: move to StateRelation_C *)
definition
  "framesize_from_H sz \<equiv> case sz of
    ARM.ARMSmallPage \<Rightarrow> (scast Kernel_C.ARMSmallPage :: word32)
  | ARM.ARMLargePage \<Rightarrow> scast Kernel_C.ARMLargePage
  | ARM.ARMSection \<Rightarrow> scast Kernel_C.ARMSection
  | ARM.ARMSuperSection \<Rightarrow> scast Kernel_C.ARMSuperSection"

lemma framesize_from_to_H:
  "gen_framesize_to_H (framesize_from_H sz) = sz"
  by (simp add: gen_framesize_to_H_def framesize_from_H_def
                Kernel_C.ARMSmallPage_def Kernel_C.ARMLargePage_def
                Kernel_C.ARMSection_def Kernel_C.ARMSuperSection_def
           split: if_split vmpage_size.splits)

lemma framesize_from_H_mask:
  "framesize_from_H vmsz && mask 2 = framesize_from_H vmsz"
  by (simp add: framesize_from_H_def mask_def
                Kernel_C.ARMSmallPage_def Kernel_C.ARMLargePage_def
                Kernel_C.ARMSection_def Kernel_C.ARMSuperSection_def
           split: vmpage_size.splits)

lemma dmo_flushtype_case:
  "(doMachineOp (case t of
    ARM_H.flush_type.Clean \<Rightarrow> f
  | ARM_H.flush_type.Invalidate \<Rightarrow> g
  | ARM_H.flush_type.CleanInvalidate \<Rightarrow> h
  | ARM_H.flush_type.Unify \<Rightarrow> i)) =
  (case t of
    ARM_H.flush_type.Clean \<Rightarrow> doMachineOp f
  | ARM_H.flush_type.Invalidate \<Rightarrow> doMachineOp g
  | ARM_H.flush_type.CleanInvalidate \<Rightarrow> doMachineOp h
  | ARM_H.flush_type.Unify \<Rightarrow> doMachineOp i)"
  by (case_tac "t", simp_all)

definition
  "flushtype_relation typ label \<equiv> case typ of
    ARM_H.flush_type.Clean \<Rightarrow> (label = Kernel_C.ARMPageClean_Data \<or> label = Kernel_C.ARMPDClean_Data)
  | ARM_H.flush_type.Invalidate \<Rightarrow>(label = Kernel_C.ARMPageInvalidate_Data \<or> label = Kernel_C.ARMPDInvalidate_Data)
  | ARM_H.flush_type.CleanInvalidate \<Rightarrow> (label = Kernel_C.ARMPageCleanInvalidate_Data \<or> label = Kernel_C.ARMPDCleanInvalidate_Data)
  | ARM_H.flush_type.Unify \<Rightarrow> (label = Kernel_C.ARMPageUnify_Instruction \<or> label = Kernel_C.ARMPDUnify_Instruction)"

lemma doFlush_ccorres:
  "ccorres dc xfdc (\<lambda>s. vs \<le> ve \<and> ps \<le> ps + (ve - vs) \<and> vs && mask 5 = ps && mask 5
        \<and> unat (ve - vs) \<le> gsMaxObjectSize s)
     (\<lbrace>flushtype_relation t \<acute>invLabel___int\<rbrace> \<inter> \<lbrace>\<acute>start = vs\<rbrace> \<inter> \<lbrace>\<acute>end = ve\<rbrace> \<inter> \<lbrace>\<acute>pstart = ps\<rbrace>) []
     (doMachineOp (doFlush t vs ve ps)) (Call doFlush_'proc)"
  apply (cinit' lift: pstart_')
   apply (unfold doMachineOp_bind doFlush_def)
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_basic_srnoop)
     apply (simp only: ccorres_seq_skip)
     apply (rule_tac xf'=invLabel___int_' in ccorres_abstract, ceqv, rename_tac invlabel)
     apply (rule_tac P="flushtype_relation t invlabel" in ccorres_gen_asm2)
     apply (rule_tac xf'=start_' in ccorres_abstract, ceqv, rename_tac start')
     apply (rule_tac P="start' = vs" in ccorres_gen_asm2)
     apply (rule_tac xf'=end_' in ccorres_abstract, ceqv, rename_tac end')
     apply (rule_tac P="end' = ve" in ccorres_gen_asm2)
     apply (simp only: dmo_flushtype_case)
     apply wpc
        apply (rule ccorres_cond_true)
        apply (ctac (no_vcg) add: cleanCacheRange_RAM_ccorres)
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_true)
       apply (ctac (no_vcg) add: invalidateCacheRange_RAM_ccorres)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_cond_true)
      apply (ctac (no_vcg) add: cleanInvalidateCacheRange_RAM_ccorres)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_true)
     apply (simp add: empty_fail_cond empty_fail_cleanCacheRange_PoU empty_fail_dsb
                      empty_fail_invalidateCacheRange_I empty_fail_branchFlushRange empty_fail_isb
                      doMachineOp_bind)
     apply (rule ccorres_rhs_assoc)+
     apply (ctac (no_vcg) add: cleanCacheRange_PoU_ccorres)
      apply (ctac (no_vcg) add: dsb_ccorres)
       apply (ctac (no_vcg) add: invalidateCacheRange_I_ccorres)
        apply (ctac (no_vcg) add: branchFlushRange_ccorres)
         apply (ctac (no_vcg) add: isb_ccorres)
        apply wp+
    apply simp
   apply (clarsimp simp: Collect_const_mem)
  apply (auto simp: flushtype_relation_def
                    Kernel_C.ARMPageClean_Data_def Kernel_C.ARMPDClean_Data_def
                    Kernel_C.ARMPageInvalidate_Data_def Kernel_C.ARMPDInvalidate_Data_def
                    Kernel_C.ARMPageCleanInvalidate_Data_def Kernel_C.ARMPDCleanInvalidate_Data_def
                    Kernel_C.ARMPageUnify_Instruction_def Kernel_C.ARMPDUnify_Instruction_def
              dest: ghost_assertion_size_logic[rotated]
             split: ARM_H.flush_type.splits)
  done
end

context begin interpretation Arch . (*FIXME: arch_split*)
crunch gsMaxObjectSize[wp]: setVMRootForFlush "\<lambda>s. P (gsMaxObjectSize s)"
  (wp: crunch_wps)
end

context kernel_m begin

lemma performPageFlush_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and K (asid \<le> mask asid_bits)
              and (\<lambda>s. ps \<le> ps + (ve - vs) \<and> vs && mask 5 = ps && mask 5
                  \<and> unat (ve - vs) \<le> gsMaxObjectSize s))
       (\<lbrace>\<acute>pd = Ptr pd\<rbrace> \<inter> \<lbrace>\<acute>asid = asid\<rbrace> \<inter>
               \<lbrace>\<acute>start = vs\<rbrace> \<inter> \<lbrace>\<acute>end =  ve\<rbrace> \<inter> \<lbrace>\<acute>pstart = ps\<rbrace> \<inter> \<lbrace>flushtype_relation typ \<acute>invLabel___int \<rbrace>)
       []
       (liftE (performPageInvocation (PageFlush typ vs ve ps pd asid)))
       (Call performPageFlush_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: pd_' asid_' start_' end_' pstart_' invLabel___int_')
   apply (unfold when_def)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (rule ccorres_cond2[where R=\<top>])
        apply (simp split: if_split)
       apply (rule ccorres_rhs_assoc)+
       apply (ctac (no_vcg) add: setVMRootForFlush_ccorres)
        apply (ctac (no_vcg) add: doFlush_ccorres)
         apply (rule ccorres_cond2[where R=\<top>])
           apply (simp split: if_split bool.splits)
          apply (rule ccorres_pre_getCurThread)
          apply (ctac add: setVMRoot_ccorres)
         apply (rule ccorres_return_Skip)
        apply (simp add: cur_tcb'_def[symmetric])
        apply (rule_tac Q="\<lambda>_ s. invs' s \<and> cur_tcb' s" in hoare_post_imp)
         apply (simp add: invs'_invs_no_cicd)
        apply wp+
      apply (rule ccorres_return_Skip)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wpsimp
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: order_less_imp_le)
  done

(* FIXME: move *)
lemma register_from_H_bound[simp]:
  "unat (register_from_H v) < 20"
  by (cases v, simp_all add: "StrictC'_register_defs")

(* FIXME: move *)
lemma register_from_H_inj:
  "inj register_from_H"
  apply (rule inj_onI)
  apply (case_tac x)
  by (case_tac y, simp_all add: "StrictC'_register_defs")+

(* FIXME: move *)
lemmas register_from_H_eq_iff[simp]
    = inj_on_eq_iff [OF register_from_H_inj, simplified]

lemma setRegister_ccorres:
  "ccorres dc xfdc \<top>
       (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>reg = register_from_H reg\<rbrace>
             \<inter> {s. w_' s = val}) []
       (asUser thread (setRegister reg val))
       (Call setRegister_'proc)"
  apply (cinit' lift: thread_' reg_' w_')
   apply (simp add: asUser_def split_def)
   apply (rule ccorres_pre_threadGet)
   apply (rule ccorres_Guard)
   apply (simp add: setRegister_def simpler_modify_def exec_select_f_singleton)
   apply (rule_tac P="\<lambda>tcb. (atcbContextGet o tcbArch) tcb = uc"
                in threadSet_ccorres_lemma2)
    apply vcg
   apply (clarsimp simp: setRegister_def HaskellLib_H.runState_def
                         simpler_modify_def typ_heap_simps)
   apply (subst StateSpace.state.fold_congs[OF refl refl])
    apply (rule globals.fold_congs[OF refl refl])
    apply (rule heap_update_field_hrs, simp)
     apply (fastforce intro: typ_heap_simps)
    apply simp
   apply (erule(1) rf_sr_tcb_update_no_queue2,
               (simp add: typ_heap_simps')+)
    apply (rule ball_tcb_cte_casesI, simp+)
   apply (clarsimp simp: ctcb_relation_def ccontext_relation_def
                         atcbContextSet_def atcbContextGet_def
                         carch_tcb_relation_def
                  split: if_split)
  apply (clarsimp simp: Collect_const_mem
                        register_from_H_less)
  apply (auto intro: typ_heap_simps elim: obj_at'_weakenE)
  done

lemma wordFromMessageInfo_spec:
  defines "mil s \<equiv> seL4_MessageInfo_lift \<^bsup>s\<^esup>mi"
  shows "\<forall>s. \<Gamma> \<turnstile> {s} Call wordFromMessageInfo_'proc
                  \<lbrace>\<acute>ret__unsigned_long = (label_CL (mil s) << 12)
                                      || (capsUnwrapped_CL (mil s) << 9)
                                      || (extraCaps_CL (mil s) << 7)
                                      || length_CL (mil s)\<rbrace>"
  unfolding mil_def
  apply vcg
  apply (simp add: seL4_MessageInfo_lift_def mask_shift_simps word_sless_def word_sle_def)
  apply word_bitwise
  done

lemmas wordFromMessageInfo_spec2 = wordFromMessageInfo_spec

lemma wordFromMessageInfo_ccorres [corres]:
  "\<And>mi. ccorres (=) ret__unsigned_long_' \<top> {s. mi = message_info_to_H (mi_' s)} []
           (return (wordFromMessageInfo mi)) (Call wordFromMessageInfo_'proc)"
  apply (rule ccorres_from_spec_modifies [where P = \<top>, simplified])
     apply (rule wordFromMessageInfo_spec)
    apply (rule wordFromMessageInfo_modifies)
   apply simp
  apply simp
  apply (simp add: return_def wordFromMessageInfo_def Let_def message_info_to_H_def
    Types_H.msgLengthBits_def Types_H.msgExtraCapBits_def
    Types_H.msgMaxExtraCaps_def shiftL_nat word_bw_assocs word_bw_comms word_bw_lcs)
  done

lemma setMessageInfo_ccorres:
  "ccorres dc xfdc (tcb_at' thread)
           (UNIV \<inter> \<lbrace>mi = message_info_to_H mi'\<rbrace>) hs
           (setMessageInfo thread mi)
           (\<acute>ret__unsigned_long :== CALL wordFromMessageInfo(mi');;
            CALL setRegister(tcb_ptr_to_ctcb_ptr thread, scast Kernel_C.msgInfoRegister, \<acute>ret__unsigned_long))"
  unfolding setMessageInfo_def
  apply (rule ccorres_guard_imp2)
   apply ctac
     apply simp
     apply (ctac add: setRegister_ccorres)
    apply wp
   apply vcg
  apply (simp add: ARM_H.msgInfoRegister_def ARM.msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def Kernel_C.R1_def)
  done

lemma performPageDirectoryInvocationFlush_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and K (asid \<le> mask asid_bits)
              and (\<lambda>s. ps \<le> ps + (ve - vs) \<and> vs && mask 5 = ps && mask 5
                  \<and> unat (ve - vs) \<le> gsMaxObjectSize s))
       (\<lbrace>\<acute>pd = Ptr pd\<rbrace> \<inter> \<lbrace>\<acute>asid = asid\<rbrace> \<inter>
               \<lbrace>\<acute>start = vs\<rbrace> \<inter> \<lbrace>\<acute>end =  ve\<rbrace> \<inter> \<lbrace>\<acute>pstart = ps\<rbrace> \<inter> \<lbrace>flushtype_relation typ \<acute>invLabel___int \<rbrace>)
       []
       (liftE (performPageDirectoryInvocation (PageDirectoryFlush typ vs ve ps pd asid)))
       (Call performPDFlush_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: pd_' asid_' start_' end_' pstart_' invLabel___int_')
   apply (unfold when_def)
   apply (rule ccorres_cond_seq)
   apply (rule ccorres_cond2[where R=\<top>])
     apply (simp split: if_split)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac (no_vcg) add: setVMRootForFlush_ccorres)
     apply (ctac (no_vcg) add: doFlush_ccorres)
      apply (rule ccorres_add_return2)
      apply (rule ccorres_split_nothrow_novcg_dc)
         apply (rule ccorres_cond2[where R=\<top>])
           apply (simp split: if_split bool.splits)
          apply (rule ccorres_pre_getCurThread)
          apply (ctac add: setVMRoot_ccorres)
         apply (rule ccorres_return_Skip)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply wp
      apply (simp add: guard_is_UNIV_def)
     apply (simp add: cur_tcb'_def[symmetric])
     apply (rule_tac Q="\<lambda>_ s. invs' s \<and> cur_tcb' s" in hoare_post_imp)
      apply (simp add: invs'_invs_no_cicd)
     apply wp+
   apply (simp)
   apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: return_def)
  apply (clarsimp simp: order_less_imp_le)
  done

lemma invalidateTranslationSingleLocal_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vptr = w\<rbrace>) []
           (doMachineOp (invalidateLocalTLB_VAASID w))
           (Call invalidateTranslationSingleLocal_'proc)"
  apply cinit'
  apply (ctac (no_vcg) add: invalidateLocalTLB_VAASID_ccorres)
  apply clarsimp
  done

lemma invalidateTranslationSingle_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vptr = w\<rbrace>) []
           (doMachineOp (invalidateLocalTLB_VAASID w))
           (Call invalidateTranslationSingle_'proc)"
  apply cinit'
  apply (ctac (no_vcg) add: invalidateTranslationSingleLocal_ccorres)
  apply clarsimp
  done

lemma flushPage_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. asid \<le> mask asid_bits \<and> is_aligned vptr pageBits))
      (UNIV \<inter> {s. gen_framesize_to_H (page_size_' s) = sz
                     \<and> page_size_' s < 4}
            \<inter> {s. pd_' s = pde_Ptr pd} \<inter> {s. asid_' s = asid}
            \<inter> {s. vptr_' s = vptr}) []
      (flushPage sz pd asid vptr) (Call flushPage_'proc)"
  apply (cinit lift: page_size_' pd_' asid_' vptr_')
   apply (rule ccorres_assert)
   apply (simp del: Collect_const)
   apply (ctac(no_vcg) add: setVMRootForFlush_ccorres)
    apply (ctac(no_vcg) add: loadHWASID_ccorres)
     apply csymbr
     apply (simp add: when_def del: Collect_const)
     apply (rule ccorres_cond2[where R=\<top>])
       apply (clarsimp simp: pde_stored_asid_def to_bool_def split: if_split)
      apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply (ctac(no_vcg) add: invalidateTranslationSingle_ccorres)
       apply (rule ccorres_cond2[where R=\<top>])
         apply (simp add: from_bool_0 Collect_const_mem)
        apply (rule ccorres_pre_getCurThread)
        apply (ctac add: setVMRoot_ccorres)
       apply (rule ccorres_return_Skip)
      apply (wp | simp add: cur_tcb'_def[symmetric])+
      apply (rule_tac Q="\<lambda>_ s. invs' s \<and> cur_tcb' s" in hoare_post_imp)
       apply (simp add: invs'_invs_no_cicd)
      apply (wp | simp add: cur_tcb'_def[symmetric])+
     apply (rule ccorres_return_Skip)
    apply wp
   apply (simp only: pred_conj_def simp_thms)
   apply (strengthen invs_valid_pde_mappings')
   apply (wp hoare_drop_imps setVMRootForFlush_invs')
  apply (clarsimp simp: Collect_const_mem word_sle_def)
  apply (rule conjI, clarsimp+)
  apply (clarsimp simp: pde_stored_asid_def to_bool_def ucast_ucast_mask
                  cong: conj_cong)
  apply (drule is_aligned_neg_mask_eq)
  apply (simp add: pde_pde_invalid_lift_def pde_lift_def mask_def[where n=8]
                   word_bw_assocs mask_def[where n=pageBits])
  apply (simp add: pageBits_def mask_eq_iff_w2p word_size)
  done

end

context begin interpretation Arch . (*FIXME: arch_split*)
crunch no_0_obj'[wp]: flushPage "no_0_obj'"
end

context kernel_m begin

lemma checkMappingPPtr_pte_ccorres:
  assumes pre:
    "\<And>pte \<sigma>. \<Gamma> \<turnstile> {s. True \<and> (\<exists>pte'. cslift s (pte_Ptr pte_ptr) = Some pte' \<and> cpte_relation pte pte')
                            \<and> (\<sigma>, s) \<in> rf_sr}
           call1 ;; Cond S return_void_C Skip;; call2;; Cond T return_void_C Skip
       {s. (\<sigma>, s) \<in> rf_sr \<and> (isSmallPagePTE pte \<and> pgsz = ARMSmallPage
                                \<or> isLargePagePTE pte \<and> pgsz = ARMLargePage)
                 \<and> pteFrame pte = addrFromPPtr pptr},
       {s. (\<sigma>, s) \<in> rf_sr \<and> \<not> ((isSmallPagePTE pte \<and> pgsz = ARMSmallPage
                                \<or> isLargePagePTE pte \<and> pgsz = ARMLargePage)
                 \<and> pteFrame pte = addrFromPPtr pptr)}"
  shows
  "ccorres_underlying rf_sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel dc) xfdc
       \<top> UNIV [SKIP]
     (checkMappingPPtr pptr pgsz (Inl pte_ptr))
     (call1;; Cond S return_void_C Skip;; call2;; Cond T return_void_C Skip)"
  apply (simp add: checkMappingPPtr_def liftE_bindE)
  apply (rule ccorres_symb_exec_l[where Q'="\<lambda>_. UNIV", OF _ _ getObject_ko_at, simplified])
      apply (rule stronger_ccorres_guard_imp)
        apply (rule ccorres_from_vcg_might_throw[where P=\<top>])
        apply (rule allI)
        apply (rule conseqPost, rule conseqPre, rule_tac \<sigma>1=\<sigma> and pte1=rv in pre)
          apply clarsimp
          apply (erule CollectE, assumption)
         apply (fold_subgoals (prefix))[2]
         subgoal by (auto simp: in_monad Bex_def isSmallPagePTE_def isLargePagePTE_def
                         split: pte.split vmpage_size.split)
       apply (wp empty_fail_getObject | simp)+
      apply (erule cmap_relationE1[OF rf_sr_cpte_relation])
       apply (erule ko_at_projectKO_opt)
      apply simp
     apply (wp empty_fail_getObject | simp add: objBits_simps archObjSize_def pteBits_def)+
  done

lemma checkMappingPPtr_pde_ccorres:
  assumes pre:
    "\<And>pde \<sigma>. \<Gamma> \<turnstile> {s. True \<and> (\<exists>pde'. cslift s (pde_Ptr pde_ptr) = Some pde' \<and> cpde_relation pde pde')
                            \<and> (\<sigma>, s) \<in> rf_sr}
           call1;; Cond S return_void_C Skip;; call2;; Cond T return_void_C Skip;;
           call3;; Cond U return_void_C Skip
       {s. (\<sigma>, s) \<in> rf_sr \<and> (isSectionPDE pde \<and> pgsz = ARMSection
                                \<or> isSuperSectionPDE pde \<and> pgsz = ARMSuperSection)
                 \<and> pdeFrame pde = addrFromPPtr pptr},
       {s. (\<sigma>, s) \<in> rf_sr \<and> \<not> ((isSectionPDE pde \<and> pgsz = ARMSection
                                \<or> isSuperSectionPDE pde \<and> pgsz = ARMSuperSection)
                 \<and> pdeFrame pde = addrFromPPtr pptr)}"
  shows
  "ccorres_underlying rf_sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel dc) xfdc
       \<top> UNIV [SKIP]
     (checkMappingPPtr pptr pgsz (Inr pde_ptr))
     (call1;; Cond S return_void_C Skip;; call2;; Cond T return_void_C Skip;;
      call3;; Cond U return_void_C Skip)"
  apply (simp add: checkMappingPPtr_def liftE_bindE)
  apply (rule ccorres_symb_exec_l[where Q'="\<lambda>_. UNIV", OF _ _ getObject_ko_at, simplified])
      apply (rule stronger_ccorres_guard_imp)
        apply (rule ccorres_from_vcg_might_throw[where P=\<top>])
        apply (rule allI)
        apply (rule conseqPost, rule conseqPre, rule_tac \<sigma>1=\<sigma> and pde1=rv in pre)
          apply clarsimp
          apply (erule CollectE, assumption)
         apply (fold_subgoals (prefix))[2]
         subgoal by (auto simp: in_monad Bex_def isSectionPDE_def isSuperSectionPDE_def
                         split: pde.split vmpage_size.split)
       apply (wp empty_fail_getObject | simp)+
      apply (erule cmap_relationE1[OF rf_sr_cpde_relation])
       apply (erule ko_at_projectKO_opt)
      apply simp
     apply (wp empty_fail_getObject | simp add: objBits_simps archObjSize_def pdeBits_def)+
  done



lemma ccorres_return_void_C':
  "ccorres_underlying rf_sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel dc) xfdc (\<lambda>_. True) UNIV (SKIP # hs) (return (Inl rv)) return_void_C"
  apply (rule ccorres_from_vcg_throws)
  apply (simp add: return_def)
  apply (rule allI, rule conseqPre, vcg)
  apply auto
  done

lemma is_aligned_cache_preconds:
  "\<lbrakk>is_aligned rva n; n \<ge> 6\<rbrakk> \<Longrightarrow> rva \<le> rva + 0x3F \<and>
          addrFromPPtr rva \<le> addrFromPPtr rva + 0x3F \<and> rva && mask 5 = addrFromPPtr rva && mask 5"
  supply if_cong[cong]
  apply (drule is_aligned_weaken, simp)
  apply (rule conjI)
   apply (drule is_aligned_no_overflow, simp, unat_arith)[1]
  apply (rule conjI)
   apply (drule is_aligned_addrFromPPtr_n, simp)
   apply (drule is_aligned_no_overflow, unat_arith)
  apply (frule is_aligned_addrFromPPtr_n, simp)
  apply (drule_tac x=6 and y=5 in is_aligned_weaken, simp)+
  apply (simp add: is_aligned_mask)
  done

lemma pte_pte_invalid_new_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       \<acute>ret__struct_pte_C :== PROC pte_pte_invalid_new()
       \<lbrace> pte_lift \<acute>ret__struct_pte_C = Some (Pte_pte_large
          \<lparr> pte_pte_large_CL.address_CL = 0,
             XN_CL = 0,
             TEX_CL = 0,
              nG_CL = 0,
              S_CL = 0,
              APX_CL = 0,
              AP_CL = 0,
              C_CL = 0,
              B_CL = 0,
              reserved_CL = 0
          \<rparr>)\<rbrace>"
  apply vcg
  apply (clarsimp simp: pte_lift_def pte_get_tag_def pte_pte_large_def fupdate_def)
  done

lemma ccorres_name_pre_C:
  "(\<And>s. s \<in> P' \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P {s} hs f g)
  \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs f g"
  apply (rule ccorres_guard_imp)
    apply (rule_tac xf'=id in ccorres_abstract, rule ceqv_refl)
    apply (rule_tac P="rv' \<in> P'" in ccorres_gen_asm2)
    apply assumption
   apply simp
  apply simp
  done

lemma ccorres_flip_Guard:
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F S (Guard F1 S1 c))"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F1 S1 (Guard F S c))"
  apply (rule ccorres_name_pre_C)
  using cc
  apply (case_tac "s \<in> (S1 \<inter> S)")
   apply (clarsimp simp: ccorres_underlying_def)
   apply (erule exec_handlers.cases;
    fastforce elim!: exec_Normal_elim_cases intro: exec_handlers.intros exec.Guard)
  apply (clarsimp simp: ccorres_underlying_def)
  apply (case_tac "s \<in> S")
   apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros)
  apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros)
  done

lemma large_ptSlot_array_constraint:
  "is_aligned (ptSlot :: word32) 6 \<Longrightarrow> n \<le> limit - 240 \<and> 240 \<le> limit
    \<Longrightarrow> \<exists>i. ptSlot = (ptSlot && ~~ mask ptBits) + of_nat i * 4 \<and> i + n \<le> limit"
  apply (rule_tac x="unat ((ptSlot && mask ptBits) >> 2)" in exI)
  apply (simp add: shiftl_t2n[where n=2, symmetric, THEN trans[rotated],
                   OF mult.commute, simplified])
  apply (simp add: shiftr_shiftl1)
  apply (rule conjI, rule trans,
         rule word_plus_and_or_coroll2[symmetric, where w="mask ptBits"])
   apply (simp, rule is_aligned_neg_mask_eq[THEN sym], rule is_aligned_andI1,
          erule is_aligned_weaken, simp)
  apply (clarsimp simp add: le_diff_conv2)
  apply (erule order_trans[rotated], simp)
  apply (rule unat_le_helper)
  apply (simp add: is_aligned_mask mask_def ptBits_def pageBits_def)
  apply (word_bitwise, simp add: pteBits_def)
  done

lemma large_pdSlot_array_constraint:
  "is_aligned pd pdBits \<Longrightarrow> vmsz_aligned vptr ARMSuperSection \<Longrightarrow> n \<le> limit - 4080 \<and> 4080 \<le> limit
    \<Longrightarrow> \<exists>i. lookup_pd_slot pd vptr = pd + of_nat i * 4 \<and> i + n \<le> limit"
  apply (rule_tac x="unat (vptr >> 20)" in exI)
  apply (rule conjI)
   apply (simp add: lookup_pd_slot_def shiftl_t2n)
  apply (clarsimp simp add: le_diff_conv2)
  apply (erule order_trans[rotated], simp)
  apply (rule unat_le_helper)
  apply (simp add: is_aligned_mask mask_def pdBits_def pageBits_def
                   vmsz_aligned_def)
  apply (word_bitwise, simp?)
  done

lemma findPDForASID_page_directory_at'_simple[wp]:
  notes checkPDAt_inv[wp del]
  shows "\<lbrace>\<top>\<rbrace> findPDForASID asiv
    \<lbrace>\<lambda>rv s. page_directory_at' rv s\<rbrace>,-"
  apply (simp add:findPDForASID_def)
   apply (wp getASID_wp|simp add:checkPDAt_def | wpc)+
  apply auto?
  done

lemma array_assertion_abs_pte_16:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_table_at' (ptr_val ptPtr && ~~ mask ptBits) s
        \<and> is_aligned (ptr_val ptPtr) 6) \<and> (n s' \<le> 16 \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (ptPtr :: pte_C ptr) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (drule(1) page_table_at_rf_sr, clarsimp)
  apply (cases ptPtr, simp)
  apply (erule clift_array_assertion_imp, simp_all)
  apply (rule large_ptSlot_array_constraint, simp_all)
  done

lemmas ccorres_move_array_assertion_pte_16
    = ccorres_move_array_assertions [OF array_assertion_abs_pte_16]

lemma array_assertion_abs_pde_16:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_directory_at' pd s
        \<and> vmsz_aligned vptr ARMSuperSection) \<and> (n s' \<le> 16 \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (pde_Ptr (lookup_pd_slot pd vptr)) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (frule(1) page_directory_at_rf_sr, clarsimp)
  apply (erule clift_array_assertion_imp, simp_all)
  apply (rule large_pdSlot_array_constraint, simp_all add: page_directory_at'_def)
  done

lemmas array_assertion_abs_pde_16_const = array_assertion_abs_pde_16[where x="\<lambda>_. Suc 0",
    simplified nat.simps simp_thms]

lemmas ccorres_move_array_assertion_pde_16
    = ccorres_move_Guard_Seq [OF array_assertion_abs_pde_16]
      ccorres_move_Guard [OF array_assertion_abs_pde_16]
      ccorres_move_Guard_Seq [OF array_assertion_abs_pde_16]
      ccorres_move_Guard [OF array_assertion_abs_pde_16]
      ccorres_move_Guard_Seq [OF array_assertion_abs_pde_16_const]
      ccorres_move_Guard [OF array_assertion_abs_pde_16_const]
      ccorres_move_Guard_Seq [OF array_assertion_abs_pde_16_const]
      ccorres_move_Guard [OF array_assertion_abs_pde_16_const]

lemma unmapPage_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. 2 ^ pageBitsForSize sz \<le> gsMaxObjectSize s)
                          and (\<lambda>_. asid \<le> mask asid_bits \<and> vmsz_aligned' vptr sz
                                           \<and> vptr < pptrBase))
      (UNIV \<inter> {s. gen_framesize_to_H (page_size_' s) = sz \<and> page_size_' s < 4}
            \<inter> {s. asid_' s = asid} \<inter> {s. vptr_' s = vptr} \<inter> {s. pptr_' s = Ptr pptr}) []
      (unmapPage sz asid vptr pptr) (Call unmapPage_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: page_size_' asid_' vptr_' pptr_')
   apply (simp add: ignoreFailure_liftM ptr_add_assertion_positive Collect_True
               del: Collect_const)
   apply ccorres_remove_UNIV_guard
   apply csymbr
   apply (ctac add: findPDForASID_ccorres)
      apply (rename_tac pdPtr pd')
      apply (rule_tac P="page_directory_at' pdPtr" in ccorres_cross_over_guard)
      apply (simp add: liftE_bindE Collect_False bind_bindE_assoc
                  del: Collect_const)
      apply (rule ccorres_splitE_novcg[where r'=dc and xf'=xfdc])
          \<comment> \<open>ARMSmallPage\<close>
          apply (rule ccorres_Cond_rhs)
           apply (simp add: gen_framesize_to_H_def)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply (ctac add: lookupPTSlot_ccorres)
              apply (rename_tac pt_slot pt_slot')
              apply simp
              apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                  rule ccorres_rhs_assoc2)
              apply (rule ccorres_splitE_novcg)
                  apply simp
                  apply (rule checkMappingPPtr_pte_ccorres)
                  apply (rule conseqPre, vcg)
                  apply (clarsimp simp: typ_heap_simps')
                  apply (simp add: cpte_relation_def Let_def pte_lift_def
                                isSmallPagePTE_def pte_tag_defs
                                pte_pte_small_lift_def pte_pte_invalid_def
                         split: if_split_asm pte.split_asm)
                 apply (rule ceqv_refl)
                apply (simp add: liftE_liftM Collect_const[symmetric]
                         del: Collect_const)
                apply (rule ccorres_handlers_weaken2)
                apply csymbr
                apply (rule ccorres_split_nothrow_novcg_dc)
                   apply (rule storePTE_Basic_ccorres)
                   apply (simp add: cpte_relation_def Let_def)
                  apply csymbr
                  apply (ctac add: cleanByVA_PoU_ccorres)
                 apply wp
                apply (simp add: guard_is_UNIV_def)
               apply wp
              apply (simp add: ccHoarePost_def guard_is_UNIV_def)
             apply (simp add: throwError_def)
             apply (rule ccorres_split_throws)
              apply (rule ccorres_return_void_C')
             apply vcg
            apply (wp)
           apply simp
           apply (vcg exspec=lookupPTSlot_modifies)
          \<comment> \<open>ARMLargePage\<close>
          apply (rule ccorres_Cond_rhs)
           apply (simp add: gen_framesize_to_H_def
                            largePagePTEOffsets_def pteBits_def)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply (ctac add: lookupPTSlot_ccorres)
              apply (rename_tac ptSlot lookupPTSlot_ret)
              apply (simp add: Collect_False del: Collect_const)
              apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                  rule ccorres_rhs_assoc2)
              apply (rule ccorres_splitE_novcg, simp, rule checkMappingPPtr_pte_ccorres)
                  apply (rule conseqPre, vcg)
                  apply (clarsimp simp: typ_heap_simps')
                  subgoal by (simp add: cpte_relation_def Let_def pte_lift_def
                                    isLargePagePTE_def pte_tag_defs
                                    pte_pte_large_lift_def pte_pte_invalid_def
                             split: if_split_asm pte.split_asm)
                 apply (rule ceqv_refl)
                apply (simp add: liftE_liftM
                             mapM_discarded whileAnno_def ARMLargePageBits_def ARMSmallPageBits_def
                             Collect_False word_sle_def
                        del: Collect_const)
                apply (ccorres_remove_UNIV_guard)
                apply (rule ccorres_rhs_assoc2)
                apply (rule ccorres_split_nothrow_novcg)
                    apply (rule_tac P="is_aligned ptSlot 6" in ccorres_gen_asm)
                    apply (rule_tac F="\<lambda>_. page_table_at' (ptSlot && ~~ mask ptBits)"
                        in ccorres_mapM_x_while)
                        apply clarsimp
                        apply (rule ccorres_guard_imp2)
                         apply csymbr
                         apply (rule ccorres_move_array_assertion_pte_16)
                         apply (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_pte_16)
                         apply (rule storePTE_Basic_ccorres)
                         apply (simp add: cpte_relation_def Let_def)
                        apply clarsimp
                        apply (simp add: unat_of_nat upto_enum_word of_nat_gt_0
                                         upto_enum_step_def del: upt.simps)
                       apply (simp add: upto_enum_step_def)
                      apply (rule allI, rule conseqPre, vcg)
                      apply clarsimp
                     apply wp
                    apply (simp add: upto_enum_step_def word_bits_def)
                   apply ceqv
                  apply (rule ccorres_handlers_weaken2)
                  apply (rule ccorres_move_c_guard_pte)
                  apply csymbr
                  apply (rule ccorres_move_c_guard_pte ccorres_move_array_assertion_pte_16)+
                  apply (rule ccorres_add_return2,
                    ctac(no_vcg) add: cleanCacheRange_PoU_ccorres)
                   apply (rule ccorres_move_array_assertion_pte_16, rule ccorres_return_Skip')
                  apply wp
                 apply (rule_tac P="is_aligned ptSlot 6" in hoare_gen_asm)
                 apply (rule hoare_strengthen_post)
                  apply (rule hoare_vcg_conj_lift)
                   apply (rule_tac P="\<lambda>s. page_table_at' (ptSlot && ~~ mask ptBits) s
                         \<and> 2 ^ pageBitsForSize sz \<le> gsMaxObjectSize s"
                      in mapM_x_wp')
                   apply wp[1]
                  apply (rule mapM_x_accumulate_checks)
                   apply (simp add: storePTE_def)
                   apply (rule obj_at_setObject3)
                    apply simp
                   apply (simp add: objBits_simps archObjSize_def pteBits_def)
                  apply (simp add: typ_at_to_obj_at_arches[symmetric])
                  apply wp
                 apply clarify
                 apply (subgoal_tac "P" for P)
                  apply (frule bspec, erule hd_in_set)
                  apply (frule bspec, erule last_in_set)
                  subgoal by (simp add: upto_enum_step_def upto_enum_word take_bit_Suc
                                   hd_map last_map typ_at_to_obj_at_arches field_simps
                                  objBits_simps archObjSize_def,
                              clarsimp dest!: is_aligned_cache_preconds)
                 apply (simp add: upto_enum_step_def upto_enum_word)
                apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
                apply (simp add: hd_map last_map upto_enum_step_def objBits_simps archObjSize_def
                             upto_enum_word)
               apply wp
              apply (simp add: guard_is_UNIV_def)
             apply (simp add: throwError_def)
             apply (rule ccorres_split_throws)
              apply (rule ccorres_return_void_C')
             apply vcg
            apply (wp lookupPTSlot_inv Arch_R.lookupPTSlot_aligned lookupPTSlot_page_table_at'
                  | simp)+
           apply (vcg exspec=lookupPTSlot_modifies)
          \<comment> \<open>ARMSection\<close>
          apply (rule ccorres_Cond_rhs)
           apply (rule ccorres_rhs_assoc)+
           apply (csymbr, csymbr)
           apply (simp add: gen_framesize_to_H_def liftE_liftM
                       del: Collect_const)
           apply (simp split: if_split, rule conjI[rotated], rule impI,
                  rule ccorres_empty, rule impI)
           apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                  rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                  rule ccorres_rhs_assoc2)
           apply (rule ccorres_splitE_novcg, simp, rule checkMappingPPtr_pde_ccorres)
               apply (rule conseqPre, vcg)
               apply (clarsimp simp: typ_heap_simps')
               subgoal by (simp add: pde_pde_section_lift_def cpde_relation_def pde_lift_def
                                     Let_def pde_tag_defs isSectionPDE_def
                              split: pde.split_asm if_split_asm)
              apply (rule ceqv_refl)
             apply (simp add: Collect_False del: Collect_const)
             apply (rule ccorres_handlers_weaken2)
             apply csymbr
             apply (rule ccorres_split_nothrow_novcg_dc)
                apply (rule storePDE_Basic_ccorres)
                apply (simp add: cpde_relation_def Let_def
                              pde_lift_pde_invalid)
               apply csymbr
               apply (ctac add: cleanByVA_PoU_ccorres)
              apply wp
             apply (clarsimp simp: guard_is_UNIV_def)
            apply simp
            apply wp
           apply (simp add: guard_is_UNIV_def)
          \<comment> \<open>ARMSuperSection\<close>
          apply (rule ccorres_Cond_rhs)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply csymbr
           apply (case_tac "pd = pde_Ptr (lookup_pd_slot pdPtr vptr)")
            prefer 2
            apply (simp, rule ccorres_empty)
           apply (simp add: gen_framesize_to_H_def liftE_liftM mapM_discarded whileAnno_def
                            superSectionPDEOffsets_def pdeBits_def
                       del: Collect_const)
           apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
               rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
               rule ccorres_rhs_assoc2)
           apply (rule ccorres_splitE_novcg, simp, rule checkMappingPPtr_pde_ccorres)
               apply (rule conseqPre, vcg)
               apply (clarsimp simp: typ_heap_simps')
               subgoal by (simp add: cpde_relation_def Let_def pde_lift_def
                                     isSuperSectionPDE_def pde_tag_defs
                                     pde_pde_section_lift_def
                              split: if_split_asm pde.split_asm)
              apply (rule ceqv_refl)
             apply (simp add: Collect_False ARMSuperSectionBits_def
                              ARMSectionBits_def word_sle_def
                      del: Collect_const)
             apply (ccorres_remove_UNIV_guard)
             apply (rule ccorres_rhs_assoc2,
                 rule ccorres_split_nothrow_novcg)
                 apply (rule_tac P="is_aligned pdPtr pdBits" in ccorres_gen_asm)
                 apply (rule_tac F="\<lambda>_. page_directory_at' pdPtr" in ccorres_mapM_x_while)
                     apply clarsimp
                     apply (rule ccorres_guard_imp2)
                      apply csymbr
                      apply (rule ccorres_move_array_assertion_pde_16)
                      apply (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_pde_16)
                      apply (rule storePDE_Basic_ccorres)
                      apply (simp add: cpde_relation_def Let_def
                                    pde_lift_pde_invalid)
                     apply clarsimp
                     apply (simp add: unat_of_nat of_nat_gt_0
                                      upto_enum_step_def upto_enum_word)
                     apply (simp add: vmsz_aligned'_def vmsz_aligned_def)
                     apply (clarsimp simp: lookup_pd_slot_def Let_def
                                        mask_add_aligned field_simps)
                     apply (erule less_pptrBase_valid_pde_offset')
                      apply (simp add: vmsz_aligned'_def)
                     apply (simp add: word_le_nat_alt unat_of_nat)
                    apply (simp add: upto_enum_step_def)
                   apply (rule allI, rule conseqPre, vcg)
                   apply clarsimp
                  apply wp
                 apply (simp add: upto_enum_step_def word_bits_def)
                apply ceqv
               apply (rule ccorres_handlers_weaken2)
               apply (rule ccorres_move_c_guard_pde)
               apply csymbr
               apply (rule ccorres_move_c_guard_pde ccorres_move_array_assertion_pde_16)+
               apply (rule ccorres_add_return2)
               apply (ctac(no_vcg) add: cleanCacheRange_PoU_ccorres)
                apply (rule ccorres_move_array_assertion_pde_16, rule ccorres_return_Skip')
               apply wp
              apply (rule_tac P="is_aligned pdPtr pdBits" in hoare_gen_asm)
              apply (rule hoare_strengthen_post)
               apply (rule hoare_vcg_conj_lift)
                apply (rule_tac P="\<lambda>s. page_directory_at' pdPtr s
                      \<and> 2 ^ pageBitsForSize sz \<le> gsMaxObjectSize s"
                   in mapM_x_wp')
                apply wp[1]
               apply (rule mapM_x_accumulate_checks)
                apply (simp add: storePDE_def)
                apply (rule obj_at_setObject3)
                 apply simp
                apply (simp add: objBits_simps archObjSize_def pdeBits_def)
               apply (simp add: typ_at_to_obj_at_arches[symmetric])
               apply wp
              apply (clarsimp simp: vmsz_aligned_def vmsz_aligned'_def)
              apply (subgoal_tac "P" for P)
               apply (frule bspec, erule hd_in_set)
               apply (frule bspec, erule last_in_set)
               apply (simp add: upto_enum_step_def upto_enum_word take_bit_Suc
                                hd_map last_map typ_at_to_obj_at_arches field_simps
                                objBits_simps archObjSize_def vmsz_aligned'_def
                                pageBitsForSize_def pdBits_def pageBits_def pdeBits_def)
               apply (frule_tac x=14 and y=6 in is_aligned_weaken, clarsimp+)
               apply (drule is_aligned_lookup_pd_slot, simp)
               apply (clarsimp dest!: is_aligned_cache_preconds)
              apply (simp add: upto_enum_step_def upto_enum_word)
             apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem objBits_simps archObjSize_def)
             apply (simp add: upto_enum_step_def upto_enum_word
                              hd_map last_map)
            apply (simp, wp)
           apply (simp add: guard_is_UNIV_def)
          apply (rule ccorres_empty[where P=\<top>])
         apply ceqv
        apply (simp add: liftE_liftM)
        apply (ctac add: flushPage_ccorres)
       apply ((wp lookupPTSlot_inv mapM_storePTE_invs[unfolded swp_def]
                 mapM_storePDE_invs[unfolded swp_def]
              | wpc | simp)+)[1]
      apply (simp add: guard_is_UNIV_def)
     apply (simp add: throwError_def)
     apply (rule ccorres_split_throws)
      apply (rule ccorres_return_void_C)
     apply vcg
    apply (simp add: lookup_pd_slot_def Let_def)
    apply (wp hoare_vcg_const_imp_lift_R)
   apply (simp add: Collect_const_mem)
   apply (vcg exspec=findPDForASID_modifies)
  apply (clarsimp simp: invs_arch_state' invs_no_0_obj' invs_valid_objs'
                        is_aligned_weaken[OF _ pbfs_atleast_pageBits]
                        vmsz_aligned'_def)
  by (auto simp: invs_arch_state' invs_no_0_obj' invs_valid_objs' vmsz_aligned'_def
                        is_aligned_weaken[OF _ pbfs_atleast_pageBits]
                        pageBitsForSize_def gen_framesize_to_H_def
                        Collect_const_mem vm_page_size_defs word_sle_def
                        ccHoarePost_def typ_heap_simps pageBits_def
            dest!: page_directory_at_rf_sr
            elim!: clift_array_assertion_imp
            split: vmpage_size.splits
    | unat_arith)+

(* FIXME: move *)
lemma cap_to_H_PageCap_tag:
  "\<lbrakk> cap_to_H cap = ArchObjectCap (PageCap d p R sz A);
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_frame_cap \<or> cap_get_tag C_cap = scast cap_small_frame_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     by (simp_all add: Let_def cap_lift_def split_def split: if_splits)

lemma generic_frame_mapped_address:
  "\<lbrakk> cap_to_H a = capability.ArchObjectCap (arch_capability.PageCap d v0 v1 v2 v3);
     cap_lift (cte_C.cap_C cte') = Some a;
     cl_valid_cte \<lparr>cap_CL = a, cteMDBNode_CL = mdb_node_lift (cteMDBNode_C cte')\<rparr>;
     generic_frame_cap_set_capFMappedAddress_CL (Some a) (scast asidInvalid) 0 = Some cap';
    cap_lift (cte_C.cap_C cte'a) = Some cap'\<rbrakk>
  \<Longrightarrow> ArchObjectCap (PageCap d v0 v1 v2 None) = cap_to_H cap' \<and> c_valid_cap (cte_C.cap_C cte'a)"
  apply (cases cte')
  apply (cases cte'a)
  apply (clarsimp simp: cl_valid_cte_def)
  apply (frule (1) cap_to_H_PageCap_tag)
  apply (erule disjE)
   apply (simp add: cap_frame_cap_lift)
   apply (simp add: generic_frame_cap_set_capFMappedAddress_CL_def)
   apply (clarsimp simp: cap_to_H_def)
   apply (simp add: asidInvalid_def split: if_split)
   apply (simp add: c_valid_cap_def cl_valid_cap_def)
  apply (simp add: cap_small_frame_cap_lift)
  apply (simp add: generic_frame_cap_set_capFMappedAddress_CL_def)
  apply (clarsimp simp: cap_to_H_def)
  apply (simp add: asidInvalid_def split: if_split)
  apply (simp add: c_valid_cap_def cl_valid_cap_def)
  done

lemma updateCap_frame_mapped_addr_ccorres:
  notes option.case_cong_weak [cong]
  shows "ccorres dc xfdc
           (cte_wp_at' (\<lambda>c. ArchObjectCap cap = cteCap c) ctSlot and K (isPageCap cap))
           UNIV []
           (updateCap ctSlot (ArchObjectCap (capVPMappedAddress_update Map.empty cap)))
           (CALL generic_frame_cap_ptr_set_capFMappedAddress(cap_Ptr &(cte_Ptr ctSlot\<rightarrow>[''cap_C'']),(scast asidInvalid),0))"
  unfolding updateCap_def
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_pre_getCTE)
   apply (rule_tac P = "\<lambda>s. ctes_of s ctSlot = Some cte \<and> cteCap cte = ArchObjectCap cap \<and> isPageCap cap" and
                   P' = "UNIV"
                in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (erule (1) rf_sr_ctes_of_cliftE)
   apply (frule cap_CL_lift)
   apply (clarsimp simp: typ_heap_simps)
   apply (rule conjI)
    apply (clarsimp simp: isCap_simps)
    apply (drule cap_CL_lift)
    apply (drule (1) cap_to_H_PageCap_tag)
    apply simp
   apply (clarsimp simp: isCap_simps)
   apply (rule exI)
   apply (rule conjI, rule refl)
   apply clarsimp
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI [rotated])
   apply clarsimp
   apply (frule (1) rf_sr_ctes_of_clift)
   apply clarsimp
   apply (subgoal_tac "ccte_relation (cteCap_update (\<lambda>_. ArchObjectCap (PageCap d v0 v1 v2 None)) (cte_to_H ctel')) cte'a")
    prefer 2
    apply (clarsimp simp: ccte_relation_def)
    apply (clarsimp simp: cte_lift_def)
    apply (simp split: option.splits)
    apply clarsimp
    apply (simp add: cte_to_H_def c_valid_cte_def)
    apply (erule (4) generic_frame_mapped_address)
   apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps
     Let_def cpspace_relation_def)
   apply (rule conjI)
    apply (erule (3) cmap_relation_updI)
    subgoal by simp
   apply (erule_tac t = s' in ssubst)
   apply (simp add: heap_to_user_data_def)
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                         typ_heap_simps h_t_valid_clift_Some_iff
                         cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

(* FIXME: move *)
lemma ccap_relation_mapped_asid_0:
  "ccap_relation (ArchObjectCap (PageCap d v0 v1 v2 v3)) cap
  \<Longrightarrow> (generic_frame_cap_get_capFMappedASID_CL (cap_lift cap) \<noteq> 0 \<longrightarrow> v3 \<noteq> None) \<and>
     (generic_frame_cap_get_capFMappedASID_CL (cap_lift cap) = 0 \<longrightarrow> v3 = None)"
  apply (erule ccap_relationE)
  apply (drule sym, frule (1) cap_to_H_PageCap_tag)
  apply (rule conjI)
   apply (rule impI)
   apply (rule notI, erule notE)
   apply clarsimp
   apply (erule disjE)
    apply (clarsimp simp: cap_lift_frame_cap cap_to_H_def
                          generic_frame_cap_get_capFMappedASID_CL_def
                    split: if_split_asm)
   apply (clarsimp simp: cap_lift_small_frame_cap cap_to_H_def
                         generic_frame_cap_get_capFMappedASID_CL_def
                   split: if_split_asm)
  apply clarsimp
  apply (erule disjE)
   apply (rule ccontr)
   apply clarsimp
   apply (clarsimp simp: cap_lift_frame_cap cap_to_H_def
                         generic_frame_cap_get_capFMappedASID_CL_def
                   split: if_split_asm)
   apply (drule word_aligned_0_sum [where n=asid_low_bits])
      apply fastforce
     apply (simp add: mask_def asid_low_bits_def word_and_le1)
    apply (simp add: asid_low_bits_def word_bits_def)
   apply clarsimp
   apply (drule word_shift_zero [where m=8])
     apply (rule order_trans)
      apply (rule word_and_le1)
     apply (simp add: mask_def)
    apply (simp add: asid_low_bits_def word_bits_def)
   apply simp
  apply (rule ccontr)
  apply clarsimp
  apply (clarsimp simp: cap_lift_small_frame_cap cap_to_H_def
                        generic_frame_cap_get_capFMappedASID_CL_def
                  split: if_split_asm)
  apply (drule word_aligned_0_sum [where n=asid_low_bits])
     apply fastforce
    apply (simp add: mask_def asid_low_bits_def word_and_le1)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply clarsimp
  apply (drule word_shift_zero [where m=8])
    apply (rule order_trans)
     apply (rule word_and_le1)
    apply (simp add: mask_def)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply simp
  done

lemma ccap_relation_PageCap_generics:
  "ccap_relation (ArchObjectCap (PageCap d ptr rghts sz mapdata)) cap'
    \<Longrightarrow> (mapdata \<noteq> None \<longrightarrow>
           generic_frame_cap_get_capFMappedAddress_CL (cap_lift cap')
                    = snd (the mapdata)
         \<and> generic_frame_cap_get_capFMappedASID_CL (cap_lift cap')
                    = fst (the mapdata))
      \<and> ((generic_frame_cap_get_capFMappedASID_CL (cap_lift cap') = 0)
                    = (mapdata = None))
      \<and> vmrights_to_H (generic_frame_cap_get_capFVMRights_CL (cap_lift cap')) = rghts
      \<and> gen_framesize_to_H (generic_frame_cap_get_capFSize_CL (cap_lift cap')) = sz
      \<and> generic_frame_cap_get_capFBasePtr_CL (cap_lift cap') = ptr
      \<and> generic_frame_cap_get_capFVMRights_CL (cap_lift cap') < 4
      \<and> generic_frame_cap_get_capFSize_CL (cap_lift cap') < 4
      \<and> to_bool (generic_frame_cap_get_capFIsDevice_CL (cap_lift cap')) = d"
  apply (frule ccap_relation_mapped_asid_0)
  apply (case_tac "sz = ARMSmallPage")
   apply (frule(1) cap_get_tag_isCap_unfolded_H_cap)
   apply (clarsimp simp: cap_lift_small_frame_cap cap_to_H_def
                         generic_frame_cap_get_capFMappedAddress_CL_def
                         generic_frame_cap_get_capFVMRights_CL_def
                         generic_frame_cap_get_capFSize_CL_def
                         generic_frame_cap_get_capFMappedASID_CL_def
                         generic_frame_cap_get_capFBasePtr_CL_def
                         generic_frame_cap_get_capFIsDevice_CL_def
                  elim!: ccap_relationE)
   apply (simp add: gen_framesize_to_H_def)
   apply (simp add: vm_page_size_defs order_le_less_trans [OF word_and_le1] mask_def
             split: if_split)
   apply (clarsimp split: if_split_asm)
  apply (frule(1) cap_get_tag_isCap_unfolded_H_cap)
  apply (clarsimp simp: cap_lift_frame_cap cap_to_H_def
                        generic_frame_cap_get_capFMappedAddress_CL_def
                        generic_frame_cap_get_capFVMRights_CL_def
                        generic_frame_cap_get_capFSize_CL_def
                        generic_frame_cap_get_capFMappedASID_CL_def
                        generic_frame_cap_get_capFBasePtr_CL_def
                        generic_frame_cap_get_capFIsDevice_CL_def
                        c_valid_cap_def cl_valid_cap_def
                        option_to_0_def
                 elim!: ccap_relationE)
  apply (simp add: gen_framesize_to_H_is_framesize_to_H_if_not_ARMSmallPage)
  apply (simp add: vm_page_size_defs order_le_less_trans [OF word_and_le1] mask_def
            split: if_split)
  apply (clarsimp split: if_split_asm)
  done

lemma performPageInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) o cteCap) ctSlot and K (isPageCap cap))
       (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performPageInvocation (PageUnmap cap ctSlot)))
       (Call performPageInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: cap_' ctSlot_')
   apply csymbr
   apply (rule ccorres_guard_imp [where A=
               "invs'
                and cte_wp_at' ((=) (ArchObjectCap cap) o cteCap) ctSlot
                and K (isPageCap cap)"])
     apply wpc
      apply (rule_tac P=" ret__unsigned_long = 0" in ccorres_gen_asm)
      apply simp
      apply (rule ccorres_symb_exec_l)
         apply (rule ccorres_split_nothrow_novcg)
             apply (rule ccorres_Guard)
             apply (rule updateCap_frame_mapped_addr_ccorres)
            apply ceqv
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
          apply wp[1]
         apply (simp add: guard_is_UNIV_def)
        apply (wp getSlotCap_wp', simp)
       apply (wp getSlotCap_wp')
      apply simp
     apply (rule_tac P=" ret__unsigned_long \<noteq> 0" in ccorres_gen_asm)
     apply (simp cong: Guard_no_cong)
     apply (rule ccorres_rhs_assoc)+
     apply (csymbr)
     apply csymbr
     apply csymbr
     apply csymbr
     apply wpc
     apply (ctac (no_vcg) add: unmapPage_ccorres)
      apply (rule ccorres_lhs_assoc)
      apply (rule ccorres_split_nothrow_novcg)
          apply (rule ccorres_move_Guard [where P="cte_at' ctSlot" and P'=\<top>])
           apply (clarsimp simp: cte_wp_at_ctes_of)
           apply (drule (1) rf_sr_ctes_of_clift)
           apply (fastforce intro: typ_heap_simps)
          apply (rule ccorres_symb_exec_l)
             apply (rule updateCap_frame_mapped_addr_ccorres)
            apply (wp getSlotCap_wp', simp)
           apply (wp getSlotCap_wp')
          apply simp
         apply ceqv
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply wp[1]
      apply (simp add: guard_is_UNIV_def)
     apply (simp add: cte_wp_at_ctes_of)
     apply wp
    apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps split: if_split)
    apply (drule_tac t="cteCap cte" in sym)
    apply clarsimp
    apply (drule ccap_relation_mapped_asid_0)
    apply (frule ctes_of_valid', clarsimp)
    apply (drule valid_global_refsD_with_objSize, clarsimp)
    apply (fastforce simp: mask_def valid_cap'_def)
   apply assumption
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps split: if_split)
  apply (drule_tac t="cteCap cte" in sym)
  apply clarsimp
  apply (frule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps')
  apply (frule ccap_relation_PageCap_generics)
  apply (case_tac "v2 = ARMSmallPage")
   apply (auto simp add: cap_get_tag_isCap_ArchObject2 isCap_simps)
  done

lemma APFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4\<rbrace> Call APFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned_long = ap_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  apply vcg
  apply (simp add: vmrights_to_H_def ap_from_vm_rights_def
                   Kernel_C.VMNoAccess_def Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply clarsimp
  apply (drule word_less_cases, auto)+
  done


lemma ap_from_vm_rights_mask:
  "ap_from_vm_rights R && 3 = (ap_from_vm_rights R :: word32)"
  by (simp add: ap_from_vm_rights_def split: vmrights.splits)

definition
  "shared_bit_from_cacheable cacheable \<equiv> if cacheable = 0x1 then 0 else 1"

definition
  "tex_bits_from_cacheable cacheable \<equiv> if cacheable = 0x1 then 5 else 0"

definition
  "iwb_from_cacheable cacheable \<equiv> if cacheable = 0x1 then 1 else 0"

lemma makeUserPDE_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  \<lbrace>s. (\<acute>page_size = scast Kernel_C.ARMSection \<or> \<acute>page_size = scast Kernel_C.ARMSuperSection) \<and>
      \<acute>vm_rights < 4 \<and> vmsz_aligned' (\<acute>paddr) (gen_framesize_to_H \<acute>page_size)  \<and>
      \<acute>parity && 1 = \<acute>parity \<and> \<acute>domain && 0xF = \<acute>domain \<and> \<acute>cacheable && 1 = \<acute>cacheable \<and>
      \<acute>nonexecutable && 1 = \<acute>nonexecutable\<rbrace>
  Call makeUserPDE_'proc
  \<lbrace> pde_lift \<acute>ret__struct_pde_C = Some (Pde_pde_section \<lparr>
       pde_pde_section_CL.address_CL = \<^bsup>s\<^esup>paddr,
       size_CL = if \<^bsup>s\<^esup>page_size = scast Kernel_C.ARMSection then 0 else 1,
       nG_CL = 1,
       S_CL =  shared_bit_from_cacheable \<^bsup>s\<^esup>cacheable,
       APX_CL = 0,
       TEX_CL = tex_bits_from_cacheable \<^bsup>s\<^esup>cacheable,
       AP_CL = ap_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       P_CL = \<^bsup>s\<^esup>parity,
       Domain_CL = \<^bsup>s\<^esup>domain,
       XN_CL = \<^bsup>s\<^esup>nonexecutable,
       C_CL = 0,
       B_CL = iwb_from_cacheable  \<^bsup>s\<^esup>cacheable
    \<rparr>) \<rbrace>"
  supply if_cong[cong]
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp:ap_from_vm_rights_mask split:if_splits)
  apply (intro conjI impI allI | clarsimp )+
    apply (simp only:pde_pde_section_lift pde_pde_section_lift_def)
    apply (simp add: vmsz_aligned'_def gen_framesize_to_H_def ap_from_vm_rights_mask)
    apply (clarsimp simp: Kernel_C.ARMSection_def Kernel_C.ARMSmallPage_def
       Kernel_C.ARMLargePage_def is_aligned_neg_mask_eq )
    apply (clarsimp simp:mask_def ap_from_vm_rights_mask
      shared_bit_from_cacheable_def tex_bits_from_cacheable_def
      iwb_from_cacheable_def
      split:if_splits dest!:mask_eq1_nochoice)
   apply (simp only:pde_pde_section_lift pde_pde_section_lift_def)
   apply (simp add: vmsz_aligned'_def gen_framesize_to_H_def ap_from_vm_rights_mask)
   apply (clarsimp simp: Kernel_C.ARMSection_def Kernel_C.ARMSmallPage_def
       Kernel_C.ARMLargePage_def is_aligned_neg_mask_eq)
   apply (clarsimp simp:ap_from_vm_rights_mask mask_def
     shared_bit_from_cacheable_def tex_bits_from_cacheable_def
     iwb_from_cacheable_def
     split:if_splits dest!:mask_eq1_nochoice)
  apply (clarsimp)
  apply (intro conjI impI allI)
   apply (simp add:pde_pde_section_lift pde_pde_section_lift_def)
   apply (simp add: vmsz_aligned'_def gen_framesize_to_H_def ap_from_vm_rights_mask)
   apply (drule is_aligned_weaken[where y = 20])
    apply (clarsimp simp: Kernel_C.ARMSuperSection_def Kernel_C.ARMSmallPage_def
       Kernel_C.ARMLargePage_def is_aligned_neg_mask_eq)+
   apply (clarsimp simp:mask_def ap_from_vm_rights_mask
     shared_bit_from_cacheable_def tex_bits_from_cacheable_def
     iwb_from_cacheable_def
     split:if_splits dest!:mask_eq1_nochoice)
  apply (simp add:pde_pde_section_lift pde_pde_section_lift_def)
  apply (simp add: vmsz_aligned'_def gen_framesize_to_H_def ap_from_vm_rights_mask)
  apply (drule is_aligned_weaken[where y = 20])
   apply (clarsimp simp: Kernel_C.ARMSuperSection_def Kernel_C.ARMSmallPage_def
       Kernel_C.ARMLargePage_def is_aligned_neg_mask_eq)+
  apply (clarsimp simp:mask_def ap_from_vm_rights_mask
     shared_bit_from_cacheable_def tex_bits_from_cacheable_def
     iwb_from_cacheable_def
     split:if_splits dest!:mask_eq1_nochoice)
  done

lemma makeUserPTE_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  \<lbrace>s. (\<acute>page_size = scast Kernel_C.ARMSmallPage \<or> \<acute>page_size = scast Kernel_C.ARMLargePage) \<and>
      \<acute>vm_rights < 4 \<and> vmsz_aligned' \<acute>paddr (gen_framesize_to_H \<acute>page_size)  \<and>
      \<acute>cacheable && 1 = \<acute>cacheable \<and> \<acute>nonexecutable && 1 = \<acute>nonexecutable\<rbrace>
  Call makeUserPTE_'proc
  \<lbrace> pte_lift \<acute>ret__struct_pte_C = Some (if \<^bsup>s\<^esup>page_size = scast Kernel_C.ARMSmallPage
    then Pte_pte_small
     \<lparr> pte_pte_small_CL.address_CL = \<^bsup>s\<^esup>paddr,
       nG_CL = 1,
       S_CL = shared_bit_from_cacheable \<^bsup>s\<^esup>cacheable,
       APX_CL = 0,
       TEX_CL = tex_bits_from_cacheable \<^bsup>s\<^esup>cacheable,
       AP_CL = ap_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       C_CL = 0,
       B_CL = iwb_from_cacheable  \<^bsup>s\<^esup>cacheable,
       XN_CL = \<^bsup>s\<^esup>nonexecutable
     \<rparr>
    else Pte_pte_large
     \<lparr> pte_pte_large_CL.address_CL =  \<^bsup>s\<^esup>paddr,
       XN_CL = \<^bsup>s\<^esup>nonexecutable,
       TEX_CL = tex_bits_from_cacheable \<^bsup>s\<^esup>cacheable,
       nG_CL = 1,
       S_CL = shared_bit_from_cacheable \<^bsup>s\<^esup>cacheable,
       APX_CL = 0,
       AP_CL = ap_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       C_CL = 0,
       B_CL =  iwb_from_cacheable  \<^bsup>s\<^esup>cacheable,
       reserved_CL = 1
     \<rparr>)\<rbrace>"
  apply vcg
  apply (clarsimp simp:vmsz_aligned'_def)
  apply (intro conjI)
   apply (rule impI)
   apply (drule is_aligned_weaken[where y = 12])
    apply (clarsimp simp:gen_framesize_to_H_def pageBitsForSize_def split:if_splits)
   apply (clarsimp dest:is_aligned_neg_mask_eq)
   apply (intro conjI impI allI)
    apply (fold_subgoals (prefix))[2]
    subgoal premises prems using prems
             by ((clarsimp simp add: pte_lift_def pte_pte_small_lift_def pte_tag_defs
                  mask_def ap_from_vm_rights_mask addrFromPPtr_def
                  shared_bit_from_cacheable_def tex_bits_from_cacheable_def
                  iwb_from_cacheable_def dest!:mask_eq1_nochoice)+)
  apply (clarsimp)
  apply (drule is_aligned_weaken[where y = 16])
   apply (clarsimp simp:gen_framesize_to_H_def pageBitsForSize_def split:if_splits)
  apply (intro conjI impI allI)
 apply ((clarsimp simp add: pte_lift_def pte_pte_large_lift_def pte_tag_defs
   mask_def ap_from_vm_rights_mask addrFromPPtr_def
   shared_bit_from_cacheable_def tex_bits_from_cacheable_def
   iwb_from_cacheable_def dest!:mask_eq1_nochoice is_aligned_neg_mask_eq)+)[2]
  done

lemma vmAttributesFromWord_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. True\<rbrace> Call vmAttributesFromWord_'proc
  \<lbrace> vm_attributes_lift \<acute>ret__struct_vm_attributes_C =
      \<lparr>  armExecuteNever_CL =  (\<^bsup>s\<^esup>w >> 2) && 1,
        armParityEnabled_CL = (\<^bsup>s\<^esup>w >> 1) && 1,
        armPageCacheable_CL = \<^bsup>s\<^esup>w && 1 \<rparr>  \<rbrace>"
  by (vcg, simp add: vm_attributes_lift_def word_sless_def word_sle_def mask_def)

lemma cap_to_H_PDCap_tag:
  "\<lbrakk> cap_to_H cap = ArchObjectCap (PageDirectoryCap p A);
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_page_directory_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     apply (simp_all add: Let_def cap_lift_def split: if_splits)
  done

lemma cap_to_H_PDCap:
  "cap_to_H cap = ArchObjectCap (PageDirectoryCap p asid) \<Longrightarrow>
  \<exists>cap_CL. cap = Cap_page_directory_cap cap_CL \<and>
           to_bool (capPDIsMapped_CL cap_CL) = (asid \<noteq> None) \<and>
           (asid \<noteq> None \<longrightarrow> capPDMappedASID_CL cap_CL = the asid) \<and>
           capPDBasePtr_CL cap_CL = p"
  by (auto simp add: cap_to_H_def Let_def split: cap_CL.splits if_splits)

lemma cap_lift_PDCap_Base:
  "\<lbrakk> cap_to_H cap_cl = ArchObjectCap (PageDirectoryCap p asid);
     cap_lift cap_c = Some cap_cl \<rbrakk>
  \<Longrightarrow> p = capPDBasePtr_CL (cap_page_directory_cap_lift cap_c)"
  apply (simp add: cap_page_directory_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  done

declare mask_Suc_0[simp]

(* FIXME: move *)
lemma asid_pool_at_rf_sr:
  "\<lbrakk>ko_at' (ASIDPool pool) p s; (s, s') \<in> rf_sr\<rbrakk> \<Longrightarrow>
  \<exists>pool'. cslift s' (ap_Ptr p) = Some pool' \<and>
          casid_pool_relation (ASIDPool pool) pool'"
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
  apply (erule (1) cmap_relation_ko_atE)
  apply clarsimp
  done

(* FIXME: move *)
lemma setObjectASID_Basic_ccorres:
  "ccorres dc xfdc \<top> {s. f s = p \<and> casid_pool_relation pool (asid_pool_C.asid_pool_C (pool' s))} hs
     (setObject p pool)
     ((Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (Ptr &(ap_Ptr (f s)\<rightarrow>[''array_C''])) (pool' s)))) s)))"
  apply (rule setObject_ccorres_helper)
    apply (simp_all add: objBits_simps archObjSize_def pageBits_def)
  apply (rule conseqPre, vcg)
  apply (rule subsetI, clarsimp simp: Collect_const_mem)
  apply (rule cmap_relationE1, erule rf_sr_cpspace_asidpool_relation,
         erule ko_at_projectKO_opt)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def typ_heap_simps
                         update_asidpool_map_to_asidpools
                         update_asidpool_map_tos)
   apply (case_tac y')
   apply clarsimp
   apply (erule cmap_relation_updI,
          erule ko_at_projectKO_opt, simp+)
  apply (simp add: cready_queues_relation_def
                   carch_state_relation_def
                   cmachine_state_relation_def
                   Let_def typ_heap_simps
                   update_asidpool_map_tos)
  done

lemma performASIDPoolInvocation_ccorres:
  notes option.case_cong_weak [cong]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' (isPDCap o cteCap) ctSlot and asid_pool_at' poolPtr
        and K (asid \<le> mask asid_bits))
       (UNIV \<inter> \<lbrace>\<acute>poolPtr = Ptr poolPtr\<rbrace> \<inter> \<lbrace>\<acute>asid = asid\<rbrace> \<inter> \<lbrace>\<acute>pdCapSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performASIDPoolInvocation (Assign asid poolPtr ctSlot)))
       (Call performASIDPoolInvocation_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: poolPtr_' asid_' pdCapSlot_')
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_symb_exec_l)
         apply (rule_tac P="ko_at' (ASIDPool pool) poolPtr" in ccorres_cross_over_guard)
         apply (rule ccorres_rhs_assoc2)
         apply (rule_tac ccorres_split_nothrow [where r'=dc and xf'=xfdc])
             apply (simp add: updateCap_def)
             apply (rule_tac A="cte_wp_at' ((=) oldcap o cteCap) ctSlot
                                and K (isPDCap oldcap \<and> asid \<le> mask asid_bits)"
                         and A'=UNIV in ccorres_guard_imp2)
              apply (rule ccorres_pre_getCTE)
              apply (rule_tac P="cte_wp_at' ((=) oldcap o cteCap) ctSlot
                                 and K (isPDCap oldcap \<and> asid \<le> mask asid_bits)
                                 and cte_wp_at' ((=) rv) ctSlot"
                          and P'=UNIV in ccorres_from_vcg)
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: cte_wp_at_ctes_of)
              apply (erule (1) rf_sr_ctes_of_cliftE)
              apply (clarsimp simp: typ_heap_simps)
              apply (rule conjI)
               apply (clarsimp simp: isPDCap_def)
               apply (drule cap_CL_lift)
               apply (drule (1) cap_to_H_PDCap_tag)
               apply simp
              apply (clarsimp simp: typ_heap_simps' isPDCap_def)
              apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
              apply (erule bexI [rotated])
              apply clarsimp
              apply (frule (1) rf_sr_ctes_of_clift)
              apply clarsimp
              apply (clarsimp simp: rf_sr_def cstate_relation_def typ_heap_simps
                              Let_def cpspace_relation_def)
              apply (rule conjI)
               apply (erule (2) cmap_relation_updI)
                apply (clarsimp simp: ccte_relation_def)
                apply (clarsimp simp: cte_lift_def)
                apply (simp split: option.splits)
                apply clarsimp
                apply (case_tac cte')
                apply clarsimp
                apply (rule conjI)
                 apply (clarsimp simp: cap_lift_def Let_def cap_tag_defs)
                apply clarsimp
                apply (simp add: cte_to_H_def c_valid_cte_def)
                apply (simp add: cap_page_directory_cap_lift)
                apply (simp (no_asm) add: cap_to_H_def)
                apply (simp add: asid_bits_def le_mask_imp_and_mask word_bits_def)
                apply (erule (1) cap_lift_PDCap_Base)
               apply simp
              apply (erule_tac t = s' in ssubst)
              apply (simp add: heap_to_user_data_def)
              apply (rule conjI)
               apply (erule (1) setCTE_tcb_case)
              apply (simp add: carch_state_relation_def cmachine_state_relation_def
                               typ_heap_simps h_t_valid_clift_Some_iff
                               cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
             apply (clarsimp simp: cte_wp_at_ctes_of)
            apply ceqv
           apply (rule ccorres_move_c_guard_cte)
           apply (rule ccorres_symb_exec_r)
             apply (rule ccorres_Guard_Seq[where F=ArrayBounds])?
             apply (rule ccorres_move_c_guard_ap)
             apply (simp only: Kernel_C.asidLowBits_def word_sle_def)
             apply (rule ccorres_Guard_Seq)+
             apply (rule ccorres_add_return2)
             apply (rule ccorres_split_nothrow_novcg)
                 apply (rule setObjectASID_Basic_ccorres)
                apply ceqv
               apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: return_def)
              apply wp
             apply (simp add: guard_is_UNIV_def)
            apply (vcg)
           apply (rule conseqPre, vcg)
           apply clarsimp
          apply wp
         apply vcg
        apply (wp getASID_wp)
        apply simp
       apply wp
       apply (simp add: inv_def)
       apply (wp getASID_wp)
      apply simp
      apply (rule empty_fail_getObject)
      apply simp
     apply wp
    apply (wp getSlotCap_wp')
   apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI)
   apply (clarsimp dest!: asid_pool_at'_ko simp: obj_at'_def)
  apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
  apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap_ArchObject2
                        isPDCap_def isCap_simps
                        order_le_less_trans[OF word_and_le1] asid_low_bits_def
                 dest!: ccte_relation_ccap_relation)
  apply (simp add: casid_pool_relation_def mask_def)
  apply (rule array_relation_update)
     apply (drule (1) asid_pool_at_rf_sr)
     apply (clarsimp simp: typ_heap_simps)
     apply (case_tac pool')
     apply (simp add: casid_pool_relation_def)
    apply simp
   apply (simp add: option_to_ptr_def option_to_0_def)
   apply (erule(1) rf_sr_ctes_of_cliftE, simp(no_asm_simp))
   apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_lift_PDCap_Base)
  apply (simp add: asid_low_bits_def)
  done

lemma flushTable_ccorres:
  "ccorres dc xfdc (invs' and cur_tcb' and (\<lambda>_. asid \<le> mask asid_bits))
      (UNIV \<inter> {s. pd_' s = pde_Ptr pd} \<inter> {s. asid_' s = asid}
            \<inter> {s. vptr_' s = vptr} \<inter> {s. pt_' s = pte_Ptr pt}) []
      (flushTable pd asid vptr) (Call flushTable_'proc)"
  apply (cinit lift: pd_' asid_' vptr_' pt_')

   apply (rule ccorres_assert)
   apply (simp add: objBits_simps archObjSize_def
                    ARMSmallPageBits_def word_sle_def
               del: Collect_const)
   apply (ctac (no_vcg) add: setVMRootForFlush_ccorres)
    apply (ctac (no_vcg) add: loadHWASID_ccorres)
     apply csymbr
     apply (simp add: when_def del: Collect_const)
     apply (rule ccorres_cond2[where R=\<top>])
       apply (clarsimp simp: pde_stored_asid_def to_bool_def split: if_split)
      apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+

      apply csymbr
        apply (simp add: word_sle_def mapM_discarded whileAnno_def Collect_False
                    del: Collect_const)
        apply (ctac (no_vcg) add: invalidateTranslationASID_ccorres)
       apply (rule_tac R=\<top> in ccorres_cond2)
         apply (clarsimp simp: from_bool_0 Collect_const_mem)
        apply (rule ccorres_pre_getCurThread)
        apply (ctac (no_vcg) add: setVMRoot_ccorres)
       apply (rule ccorres_return_Skip)
      apply (wp static_imp_wp)
       apply clarsimp
       apply (rule_tac Q="\<lambda>_ s. invs' s \<and> cur_tcb' s" in hoare_post_imp)
        apply (simp add: invs'_invs_no_cicd cur_tcb'_def)
       apply (wp mapM_x_wp_inv getPTE_wp | wpc)+
     apply (rule ccorres_return_Skip)
    apply wp
   apply clarsimp
   apply (strengthen invs_valid_pde_mappings')
   apply (wp setVMRootForFlush_invs' hoare_drop_imps)
  apply (clarsimp simp:Collect_const_mem)
  apply (simp add: pde_pde_invalid_lift_def
         pde_lift_def pde_stored_asid_def to_bool_def)
  done

lemma performPageTableInvocationMap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (cte_at' ctSlot and (\<lambda>_. valid_pde_mapping_offset' (pdSlot && mask pdBits)))
       (UNIV \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace> \<inter> \<lbrace>cpde_relation pde \<acute>pde\<rbrace> \<inter> \<lbrace>\<acute>pdSlot = Ptr pdSlot\<rbrace>)
       []
       (liftE (performPageTableInvocation (PageTableMap cap ctSlot pde pdSlot)))
       (Call performPageTableInvocationMap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: cap_' ctSlot_' pde_' pdSlot_')
   apply (ctac (no_vcg))
     apply (rule ccorres_split_nothrow_novcg)
         apply simp
         apply (erule storePDE_Basic_ccorres)
        apply ceqv
       apply (rule ccorres_symb_exec_r)
         apply (rule ccorres_add_return2)
         apply (rule ccorres_split_nothrow_novcg)
             apply simp
             apply (rule ccorres_call)
                apply (rule cleanByVA_PoU_ccorres)
               apply (rule refl)
              apply (simp add: xfdc_def)
             apply simp
            apply ceqv
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
          apply wp
         apply (simp add: guard_is_UNIV_def)
        apply vcg
       apply (rule conseqPre, vcg)
       apply clarsimp
      apply wp
     apply (simp add: guard_is_UNIV_def)
    apply wp
   apply simp
  apply simp
  done

end

end
