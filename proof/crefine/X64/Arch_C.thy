(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_C
imports Recycle_C
begin

unbundle l4v_word_context

context begin interpretation Arch . (*FIXME: arch-split*)

crunch unmapPageTable, unmapPageDirectory, unmapPDPT
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (wp: crunch_wps simp: crunch_simps)

end

context kernel_m begin

lemma storePTE_def':
  "storePTE slot pte = setObject slot pte"
  unfolding storePTE_def
  by (simp add: tailM_def headM_def)

lemma storePDE_def':
  "storePDE slot pde = setObject slot pde"
  unfolding storePDE_def
  by (simp add: tailM_def headM_def)

lemma storePDPTE_def':
  "storePDPTE slot pdpte = setObject slot pdpte"
  unfolding storePDPTE_def
  by (simp add: tailM_def headM_def)

lemma storePML4E_def':
  "storePML4E slot pml4e = setObject slot pml4e"
  unfolding storePML4E_def
  by (simp add: tailM_def headM_def)

lemma objBits_InvalidPTE:
  "objBits X64_H.InvalidPTE = word_size_bits"
  apply (simp add: objBits_simps archObjSize_def word_size_bits_def)
  done

lemma performPageTableInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) \<circ> cteCap) ctSlot
              and (\<lambda>_. isPageTableCap cap))
       (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performPageTableInvocation (PageTableUnmap cap ctSlot)))
       (Call performX86PageTableInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (rule ccorres_gen_asm)
  apply (cinit lift: cap_' ctSlot_')
   apply csymbr
   apply (simp del: Collect_const)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (subgoal_tac "capPTMappedAddress cap
                           = (\<lambda>cp. if to_bool (capPTIsMapped_CL cp)
                              then Some (capPTMappedASID_CL cp, capPTMappedAddress_CL cp)
                              else None) (cap_page_table_cap_lift capa)")
       apply (rule ccorres_Cond_rhs)
        apply (simp add: to_bool_def)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (ctac add: unmapPageTable_ccorres)
          apply csymbr
          apply (simp add: storePTE_def' swp_def)
          apply clarsimp
          apply (simp only: bit_simps_corres[symmetric])
          apply (ctac add: clearMemory_setObject_PTE_ccorres)
         apply wp
        apply (simp del: Collect_const)
        apply (vcg exspec=unmapPageTable_modifies)
       apply simp
       apply (rule ccorres_return_Skip')
      apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
      apply (clarsimp simp: cap_lift_page_table_cap cap_to_H_def
                            cap_page_table_cap_lift_def
                     elim!: ccap_relationE cong: if_cong)
     apply (simp add: liftM_def getSlotCap_def updateCap_def
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule ccorres_getCTE)+
     apply (rule_tac P="cte_wp_at' ((=) rv) ctSlot
                          and (\<lambda>_. rv = rva \<and> isArchCap isPageTableCap (cteCap rv))"
                in ccorres_from_vcg_throws [where P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: cte_wp_at_ctes_of cap_get_tag_isCap_ArchObject)
     apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
     apply (frule ccte_relation_ccap_relation)
     apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap_ArchObject)
     apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
     apply (erule rev_bexI)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           typ_heap_simps')
     apply (rule conjI)
      apply (clarsimp simp: cpspace_relation_def typ_heap_simps')
      apply (subst setCTE_tcb_case, assumption+)
      apply (clarsimp dest!: ksPSpace_update_eq_ExD)
      apply (erule cmap_relation_updI, assumption)
       apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
       apply (clarsimp simp: ccte_relation_def c_valid_cte_def
                      elim!: ccap_relationE)
       apply (subst cteCap_update_cte_to_H)
         apply (clarsimp simp: map_option_Some_eq2)
         apply (rule trans, rule sym, rule option.sel, rule sym, erule arg_cong)
        apply (erule iffD1[OF cap_page_table_cap_lift])
       apply (clarsimp simp: map_option_Some_eq2 cap_get_tag_isCap_ArchObject[symmetric]
                             cap_lift_page_table_cap cap_to_H_def
                             cap_page_table_cap_lift_def)
      apply simp
     apply (clarsimp simp: carch_state_relation_def cmachine_state_relation_def
                           fpu_null_state_heap_update_tag_disj_simps
                           global_ioport_bitmap_heap_update_tag_disj_simps
                           cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    dest!: ksPSpace_update_eq_ExD)
    apply (simp add: cte_wp_at_ctes_of)
    apply (wp mapM_x_wp' | wpc | simp)+
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric] cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (drule_tac t="cteCap cte" in sym)
  apply (frule valid_global_refsD_with_objSize, clarsimp)
  apply (clarsimp simp: cap_lift_page_table_cap cap_to_H_def
                        cap_page_table_cap_lift_def isCap_simps
                        valid_cap'_def get_capSizeBits_CL_def
                        bit_simps capAligned_def
                        to_bool_def mask_def page_table_at'_def
                        capRange_def Int_commute asid_bits_def
                 elim!: ccap_relationE cong: if_cong)
  apply (drule spec[where x=0])
  apply (auto simp add: word_and_le1)
  done

lemma clearMemory_setObject_PDE_ccorres:
  "ccorres dc xfdc (page_directory_at' ptr
                and (\<lambda>s. 2 ^ pdBits \<le> gsMaxObjectSize s)
                and (\<lambda>_. is_aligned ptr pdBits \<and> ptr \<noteq> 0 \<and> pstart = addrFromPPtr ptr))
            (UNIV \<inter> {s. ptr___ptr_to_void_' s = Ptr ptr} \<inter> {s. bits_' s = of_nat pdBits}) []
       (mapM_x (\<lambda>a. setObject a X64_H.InvalidPDE)
                       [ptr , ptr + 2 ^ objBits X64_H.InvalidPDE .e. ptr + 2 ^ pdBits - 1])
       (Call clearMemory_'proc)"
  apply (rule ccorres_gen_asm)+
  apply (cinit' lift: ptr___ptr_to_void_' bits_')
   apply (rule_tac P="page_directory_at' ptr and (\<lambda>s. 2 ^ pdBits \<le> gsMaxObjectSize s)"
               in ccorres_from_vcg_nofail[where P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (subst ghost_assertion_size_logic[unfolded o_def])
     apply (simp add: bit_simps)
    apply simp
   apply (clarsimp simp: replicateHider_def[symmetric] bit_simps)
   apply (frule is_aligned_no_overflow', simp)
   apply (intro conjI)
      apply (erule is_aligned_weaken, simp)
     apply (clarsimp simp: is_aligned_def)
    apply (erule (1) page_directory_at_rf_sr_dom_s[unfolded pdBits_def bit_simps, simplified])
   apply (clarsimp simp add: bit_simps
                      cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (simp add: upto_enum_step_def objBits_simps bit_simps add.commute[where b=ptr]
                    linorder_not_less[symmetric] archObjSize_def
                    upto_enum_word split_def)
  apply (erule mapM_x_store_memset_ccorres_assist
                      [unfolded split_def, OF _ _ _ _ _ _ subset_refl],
         simp_all add: shiftl_t2n hd_map objBits_simps archObjSize_def bit_simps)[1]
   apply (rule cmap_relationE1, erule rf_sr_cpde_relation, erule ko_at_projectKO_opt)
   apply (subst coerce_memset_to_heap_update_pde)
   apply (clarsimp simp: rf_sr_def Let_def cstate_relation_def typ_heap_simps)
   apply (rule conjI)
    apply (simp add: cpspace_relation_def typ_heap_simps update_pde_map_tos
                     update_pde_map_to_pdes carray_map_relation_upd_triv)
    apply (rule cmap_relation_updI, simp_all)[1]
    subgoal by (simp add: cpde_relation_def Let_def pde_lift_def pde_get_tag_def pde_tag_defs
                   split: if_splits pde.split_asm)
   apply (simp add: carch_state_relation_def cmachine_state_relation_def
                    fpu_null_state_heap_update_tag_disj_simps
                    global_ioport_bitmap_heap_update_tag_disj_simps
                    update_pde_map_tos)
  apply simp
  done

lemma performPageDirectoryInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) \<circ> cteCap) ctSlot
              and (\<lambda>_. isPageDirectoryCap cap))
       (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performPageDirectoryInvocation (PageDirectoryUnmap cap ctSlot)))
       (Call performX64PageDirectoryInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (rule ccorres_gen_asm)
  apply (cinit lift: cap_' ctSlot_')
   apply csymbr
   apply (simp del: Collect_const)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (subgoal_tac "capPDMappedAddress cap
                           = (\<lambda>cp. if to_bool (capPDIsMapped_CL cp)
                              then Some (capPDMappedASID_CL cp, capPDMappedAddress_CL cp)
                              else None) (cap_page_directory_cap_lift capa)")
       apply (rule ccorres_Cond_rhs)
        apply (simp add: to_bool_def)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (ctac add: unmapPageDirectory_ccorres)
          apply csymbr
          apply (simp add: storePDE_def' swp_def)
          apply clarsimp
          apply (simp only: bit_simps_corres[symmetric])
          apply (ctac add: clearMemory_setObject_PDE_ccorres)
         apply wp
        apply (simp del: Collect_const)
        apply (vcg exspec=unmapPageDirectory_modifies)
       apply simp
       apply (rule ccorres_return_Skip')
      apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
      apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                            cap_page_directory_cap_lift_def
                     elim!: ccap_relationE cong: if_cong)
     apply (simp add: liftM_def getSlotCap_def updateCap_def
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule ccorres_getCTE)+
     apply (rule_tac P="cte_wp_at' ((=) rv) ctSlot
                          and (\<lambda>_. rv = rva \<and> isArchCap isPageDirectoryCap (cteCap rv))"
                in ccorres_from_vcg_throws [where P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: cte_wp_at_ctes_of cap_get_tag_isCap_ArchObject)
     apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
     apply (frule ccte_relation_ccap_relation)
     apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap_ArchObject)
     apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
     apply (erule rev_bexI)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           typ_heap_simps')
     apply (rule conjI)
      apply (clarsimp simp: cpspace_relation_def typ_heap_simps')
      apply (subst setCTE_tcb_case, assumption+)
      apply (clarsimp dest!: ksPSpace_update_eq_ExD)
      apply (erule cmap_relation_updI, assumption)
       apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
       apply (clarsimp simp: ccte_relation_def c_valid_cte_def
                      elim!: ccap_relationE)
       apply (subst cteCap_update_cte_to_H)
         apply (clarsimp simp: map_option_Some_eq2)
         apply (rule trans, rule sym, rule option.sel, rule sym, erule arg_cong)
        apply (erule iffD1[OF cap_page_directory_cap_lift])
       apply (clarsimp simp: map_option_Some_eq2 cap_get_tag_isCap_ArchObject[symmetric]
                             cap_lift_page_directory_cap cap_to_H_def
                             cap_page_directory_cap_lift_def)
      apply simp
     apply (clarsimp simp: carch_state_relation_def cmachine_state_relation_def
                           fpu_null_state_heap_update_tag_disj_simps
                           global_ioport_bitmap_heap_update_tag_disj_simps
                           cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    dest!: ksPSpace_update_eq_ExD)
    apply (simp add: cte_wp_at_ctes_of)
    apply (wp mapM_x_wp' | wpc | simp)+
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric] cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (drule_tac t="cteCap cte" in sym)
  apply (frule valid_global_refsD_with_objSize, clarsimp)
  apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                        cap_page_directory_cap_lift_def isCap_simps
                        valid_cap'_def get_capSizeBits_CL_def
                        bit_simps capAligned_def
                        to_bool_def mask_def page_directory_at'_def
                        capRange_def Int_commute asid_bits_def
                 elim!: ccap_relationE cong: if_cong)
  apply (drule spec[where x=0])
  apply (auto simp add: word_and_le1)
  done

lemma clearMemory_setObject_PDPTE_ccorres:
  "ccorres dc xfdc (pd_pointer_table_at' ptr
                and (\<lambda>s. 2 ^ pdptBits \<le> gsMaxObjectSize s)
                and (\<lambda>_. is_aligned ptr pdptBits \<and> ptr \<noteq> 0 \<and> pstart = addrFromPPtr ptr))
            (UNIV \<inter> {s. ptr___ptr_to_void_' s = Ptr ptr} \<inter> {s. bits_' s = of_nat pdptBits}) []
       (mapM_x (\<lambda>a. setObject a X64_H.InvalidPDPTE)
                       [ptr , ptr + 2 ^ objBits X64_H.InvalidPDPTE .e. ptr + 2 ^ pdptBits - 1])
       (Call clearMemory_'proc)"
  apply (rule ccorres_gen_asm)+
  apply (cinit' lift: ptr___ptr_to_void_' bits_')
   apply (rule_tac P="pd_pointer_table_at' ptr and (\<lambda>s. 2 ^ pdptBits \<le> gsMaxObjectSize s)"
               in ccorres_from_vcg_nofail[where P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (subst ghost_assertion_size_logic[unfolded o_def])
     apply (simp add: bit_simps)
    apply simp
   apply (clarsimp simp: replicateHider_def[symmetric] bit_simps)
   apply (frule is_aligned_no_overflow', simp)
   apply (intro conjI)
      apply (erule is_aligned_weaken, simp)
     apply (clarsimp simp: is_aligned_def)
    apply (erule (1) pd_pointer_table_at_rf_sr_dom_s[unfolded pdptBits_def bit_simps, simplified])
   apply (clarsimp simp add: bit_simps
                      cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (simp add: upto_enum_step_def objBits_simps bit_simps add.commute[where b=ptr]
                    linorder_not_less[symmetric] archObjSize_def
                    upto_enum_word split_def)
  apply (erule mapM_x_store_memset_ccorres_assist
                      [unfolded split_def, OF _ _ _ _ _ _ subset_refl],
         simp_all add: shiftl_t2n hd_map objBits_simps archObjSize_def bit_simps)[1]
   apply (rule cmap_relationE1, erule rf_sr_cpdpte_relation, erule ko_at_projectKO_opt)
   apply (subst coerce_memset_to_heap_update_pdpte)
   apply (clarsimp simp: rf_sr_def Let_def cstate_relation_def typ_heap_simps)
   apply (rule conjI)
    apply (simp add: cpspace_relation_def typ_heap_simps update_pdpte_map_tos
                     update_pdpte_map_to_pdptes carray_map_relation_upd_triv)
    apply (rule cmap_relation_updI, simp_all)[1]
    subgoal by (simp add: cpdpte_relation_def Let_def pdpte_lift_def pdpte_get_tag_def pdpte_tag_defs
                   split: if_splits pdpte.split_asm)
   apply (simp add: carch_state_relation_def cmachine_state_relation_def
                    fpu_null_state_heap_update_tag_disj_simps
                    global_ioport_bitmap_heap_update_tag_disj_simps
                    update_pdpte_map_tos)
  apply simp
  done

lemma performPDPTInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) \<circ> cteCap) ctSlot
              and (\<lambda>_. isPDPointerTableCap cap))
       (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performPDPTInvocation (PDPTUnmap cap ctSlot)))
       (Call performX64PDPTInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (rule ccorres_gen_asm)
  apply (cinit lift: cap_' ctSlot_')
   apply csymbr
   apply (simp del: Collect_const)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (subgoal_tac "capPDPTMappedAddress cap
                           = (\<lambda>cp. if to_bool (capPDPTIsMapped_CL cp)
                              then Some (capPDPTMappedASID_CL cp, capPDPTMappedAddress_CL cp)
                              else None) (cap_pdpt_cap_lift capa)")
       apply (rule ccorres_Cond_rhs)
        apply (simp add: to_bool_def)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (ctac add: unmapPDPointerTable_ccorres)
          apply csymbr
          apply (simp add: storePDPTE_def' swp_def)
          apply clarsimp
          apply (simp only: bit_simps_corres[symmetric])
          apply (ctac add: clearMemory_setObject_PDPTE_ccorres)
         apply wp
        apply (simp del: Collect_const)
        apply (vcg exspec=unmapPDPT_modifies)
       apply simp
       apply (rule ccorres_return_Skip')
      apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
      apply (clarsimp simp: cap_lift_pdpt_cap cap_to_H_def
                            cap_pdpt_cap_lift_def
                     elim!: ccap_relationE cong: if_cong)
     apply (simp add: liftM_def getSlotCap_def updateCap_def
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule ccorres_getCTE)+
     apply (rule_tac P="cte_wp_at' ((=) rv) ctSlot
                          and (\<lambda>_. rv = rva \<and> isArchCap isPDPointerTableCap (cteCap rv))"
                in ccorres_from_vcg_throws [where P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: cte_wp_at_ctes_of cap_get_tag_isCap_ArchObject)
     apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
     apply (frule ccte_relation_ccap_relation)
     apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap_ArchObject)
     apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
     apply (erule rev_bexI)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           typ_heap_simps')
     apply (rule conjI)
      apply (clarsimp simp: cpspace_relation_def typ_heap_simps')
      apply (subst setCTE_tcb_case, assumption+)
      apply (clarsimp dest!: ksPSpace_update_eq_ExD)
      apply (erule cmap_relation_updI, assumption)
       apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
       apply (clarsimp simp: ccte_relation_def c_valid_cte_def
                      elim!: ccap_relationE)
       apply (subst cteCap_update_cte_to_H)
         apply (clarsimp simp: map_option_Some_eq2)
         apply (rule trans, rule sym, rule option.sel, rule sym, erule arg_cong)
        apply (erule iffD1[OF cap_pdpt_cap_lift])
       apply (clarsimp simp: map_option_Some_eq2 cap_get_tag_isCap_ArchObject[symmetric]
                             cap_lift_pdpt_cap cap_to_H_def
                             cap_pdpt_cap_lift_def)
      apply simp
     apply (clarsimp simp: carch_state_relation_def cmachine_state_relation_def
                           fpu_null_state_heap_update_tag_disj_simps
                           global_ioport_bitmap_heap_update_tag_disj_simps
                           cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    dest!: ksPSpace_update_eq_ExD)
    apply (simp add: cte_wp_at_ctes_of)
    apply (wp mapM_x_wp' | wpc | simp)+
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric] cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (drule_tac t="cteCap cte" in sym)
  apply (frule valid_global_refsD_with_objSize, clarsimp)
  apply (clarsimp simp: cap_lift_pdpt_cap cap_to_H_def
                        cap_pdpt_cap_lift_def isCap_simps
                        valid_cap'_def get_capSizeBits_CL_def
                        bit_simps capAligned_def
                        to_bool_def mask_def pd_pointer_table_at'_def
                        capRange_def Int_commute asid_bits_def
                 elim!: ccap_relationE cong: if_cong)
  apply (drule spec[where x=0])
  apply (auto simp add: word_and_le1)
  done

lemma cap_case_PML4Cap2:
  "(case cap of ArchObjectCap (PML4Cap pd mapdata)
                   \<Rightarrow> f pd mapdata | _ \<Rightarrow> g)
   = (if isArchObjectCap cap \<and> isPML4Cap (capCap cap)
      then f (capPML4BasePtr (capCap cap)) (capPML4MappedASID (capCap cap))
      else g)"
  by (simp add: isCap_simps
         split: capability.split arch_capability.split)

lemma ap_eq_D:
  "x \<lparr>array_C := arr'\<rparr> = asid_pool_C.asid_pool_C arr \<Longrightarrow> arr' = arr"
  by (cases x) simp

declare Kernel_C.asid_pool_C_size [simp del]

lemma createObjects_asidpool_ccorres:
  shows "ccorres dc xfdc
   ((\<lambda>s. \<exists>p. cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap isdev frame pageBits idx ) p s)
    and pspace_aligned' and pspace_distinct' and valid_objs'
    and ret_zero frame (2 ^ pageBits)
    and valid_global_refs' and pspace_no_overlap' frame pageBits)
   ({s. region_actually_is_bytes frame (2^pageBits) s})
   hs
   (placeNewObject frame (makeObject::asidpool) 0)
   (CALL memzero(Ptr frame, (2 ^ pageBits));;
   (global_htd_update (\<lambda>_. ptr_retyp (ap_Ptr frame))))"
proof -
  have helper: "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> is_aligned frame pageBits \<and> frame \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' frame pageBits \<sigma>
  \<and> ret_zero frame (2 ^ pageBits) \<sigma>
  \<and> region_actually_is_bytes frame (2 ^ pageBits) x
  \<and> {frame ..+ 2 ^ pageBits} \<inter> kernel_data_refs = {}
 \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr (KOArch (KOASIDPool makeObject))) (new_cap_addrs (Suc 0) frame (KOArch (KOASIDPool makeObject))) (ksPSpace \<sigma>)\<rparr>,
   x\<lparr>globals := globals x
                 \<lparr>t_hrs_' := hrs_htd_update (ptr_retyps_gen 1 (ap_Ptr frame) False)
                       (hrs_mem_update
                         (heap_update_list frame (replicate (2 ^ pageBits) 0))
                         (t_hrs_' (globals x)))\<rparr>\<rparr>) \<in> rf_sr"
    (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
        (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
  proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "ap_Ptr frame"

  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr" and al: "is_aligned frame pageBits" and ptr0: "frame \<noteq> 0"
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' frame pageBits \<sigma>"
    and zro: "ret_zero frame (2 ^ pageBits) \<sigma>"
    and actually: "region_actually_is_bytes frame (2 ^ pageBits) x"
    and kdr: "{frame ..+ 2 ^ pageBits} \<inter> kernel_data_refs = {}"
    by simp_all

  note empty = region_actually_is_bytes[OF actually]

  have relrl:
    "casid_pool_relation makeObject (from_bytes (replicate (size_of TYPE(asid_pool_C)) 0))"
    unfolding casid_pool_relation_def
    apply (clarsimp simp: makeObject_asidpool split: asid_pool_C.splits)
    apply (clarsimp simp: array_relation_def option_to_ptr_def asid_map_relation_def)
    apply (rename_tac words i)
    apply (subgoal_tac "asid_map_C.words_C (words.[unat i]).[0] = 0")
    apply (clarsimp simp: asid_map_lift_def asid_map_get_tag_def asid_map_tag_defs)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps asid_pool_C_tag_def
                     size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine)
    apply (simp add: padup_def align_td_array')
    apply (subst (asm) size_td_array)
    apply simp
    apply (simp add: size_td_array ti_typ_pad_combine_def ti_typ_combine_def
                     Let_def empty_typ_info_def update_ti_adjust_ti
                del: replicate_numeral Kernel_C.pde_C_size)
    apply (simp add: typ_info_array array_tag_def
                del: replicate_numeral)
    apply (drule ap_eq_D)
    apply (clarsimp simp del: replicate_numeral)
    apply (subst update_ti_t_array_tag_n_rep)
      apply (simp del: replicate_numeral)
     apply simp
    apply (simp del: replicate_numeral)
    apply (subst index_fold_update)
       apply simp
      apply auto[1]
     apply (simp add: asid_low_bits_def word_le_nat_alt)
    apply (simp split: if_split)
    apply (rule conjI[rotated], simp add: asid_low_bits_def word_le_nat_alt)
    apply (simp add: asid_map_C_typ_info asid_map_C_tag_def
                     final_pad_def Let_def size_td_lt_ti_typ_pad_combine
                     padup_def align_td_array' size_td_array)
    apply (simp add: ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def
                     update_ti_adjust_ti size_td_array typ_info_array array_tag_def
                     update_ti_t_array_tag_n_rep update_ti_t_machine_word_0s)
    done

  define ko where "ko \<equiv> KOArch (KOASIDPool makeObject)"

  have rc :"range_cover frame (objBitsKO ko) (objBitsKO ko) (Suc 0)"
    by (simp add:objBits_simps ko_def archObjSize_def al range_cover_full)

  have rc' :"range_cover frame (objBitsKO ko) (objBitsKO ko) (2 ^ 0)"
    by (simp add:objBits_simps ko_def archObjSize_def al range_cover_full range_cover_rel)

  have pno': "pspace_no_overlap' frame (objBitsKO ko) \<sigma>"
    by (simp add:objBits_simps pno ko_def archObjSize_def al)

  have al': "is_aligned frame (objBitsKO (ko::kernel_object))"
    by (simp add:objBits_simps ko_def archObjSize_def al)

  (* s/obj/obj'/ *)
  have szo: "size_of TYPE(asid_pool_C) = 2 ^ objBitsKO ko"
    by (simp add: size_of_def objBits_simps ko_def archObjSize_def pageBits_def)
  have szko: "objBitsKO ko = pageBits"
    by (simp add: objBits_simps ko_def archObjSize_def)
  hence sz: "objBitsKO ko \<le> pageBits" by simp
  have szo': "2 ^ pageBits = 2 ^ (pageBits - objBitsKO ko) * size_of TYPE(asid_pool_C)" using szko
    apply (subst szo)
    apply (simp add: power_add [symmetric])
    done

  have [simp]: "(2::nat) ^ (pageBits - objBitsKO ko) * 2 ^ objBitsKO ko = 2 ^ pageBits"
     by (clarsimp simp:pageBits_def objBits_simps ko_def archObjSize_def)

  have ptr_retyp:
    "hrs_htd_update (ptr_retyps (2 ^ (pageBits - objBitsKO ko)) (ap_Ptr frame)) = hrs_htd_update (ptr_retyp (ap_Ptr frame))"
    apply (simp add: szko hrs_htd_update_def)
    done

  note rl' = cslift_ptr_retyp_memset_other_inst [OF _ rc' _ szo,
     simplified, OF empty[folded szko] szo[symmetric], unfolded szko]

  have szb: "pageBits < word_bits" by simp
  have mko: "\<And>dev d f. makeObjectKO dev d (Inl (KOArch (KOASIDPool f))) = Some ko"
    by (simp add: ko_def makeObjectKO_def)


  note rl = projectKO_opt_retyp_other [OF rc pal pno' ko_def]

  note cterl = retype_ctes_helper
                 [OF pal pdst pno' al' le_refl
                     range_cover_sz'[where 'a=machine_word_len,
                                     folded word_bits_def, OF rc]
                     mko rc, simplified]

  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

  have guard:
    "\<forall>n<2 ^ (pageBits - objBitsKO ko). c_guard (CTypesDefs.ptr_add ?ptr (of_nat n))"
    apply (rule retype_guard_helper[where m=3])
        apply (rule range_cover_rel[OF rc])
         apply fastforce
        apply simp
       apply (clarsimp simp:objBits_simps ko_def archObjSize_def)
      apply (simp add:ptr0)
     apply (simp add:szo)
   apply (simp add:align_of_def objBits_simps pageBits_def ko_def archObjSize_def)+
   done

  have cslift_ptr_retyp_helper:
   "\<forall>x::asid_pool_C ptr\<in>dom (cslift x). is_aligned (ptr_val x) (objBitsKO ko)
   \<Longrightarrow> clift (hrs_htd_update (ptr_retyps_gen 1 (ap_Ptr frame) False)
           (hrs_mem_update (heap_update_list frame (replicate ((2::nat) ^ pageBits) (0::word8)))
             (t_hrs_' (globals x)))) =
   (\<lambda>y::asid_pool_C ptr.
       if y \<in> (CTypesDefs.ptr_add (ap_Ptr frame) \<circ> of_nat) ` {k::nat. k < (2::nat) ^ (pageBits - objBitsKO ko)}
       then Some (from_bytes (replicate (size_of TYPE(asid_pool_C)) (0::word8))) else cslift x y)"
    using guard
    apply (subst clift_ptr_retyps_gen_memset_same, simp_all add: szo szko)
    apply (simp add: szo empty szko)
    done

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>)) ?ks'"
    unfolding cpspace_relation_def
    apply -
    supply image_cong_simp [cong del]
    apply (clarsimp simp: rl' cterl[unfolded ko_def] tag_disj_via_td_name
                 foldr_upd_app_if [folded data_map_insert_def] cte_C_size tcb_C_size)
    apply (subst cslift_ptr_retyp_helper[simplified])
     apply (erule pspace_aligned_to_C [OF pal])
      apply (simp add: projectKOs ko_def)
     apply (simp add: ko_def projectKOs objBits_simps archObjSize_def)
    apply (simp add: ptr_add_to_new_cap_addrs [OF szo] ht_rl)
    apply (simp add: rl[unfolded ko_def] projectKO_opt_retyp_same ko_def projectKOs cong: if_cong)
    apply (simp add:objBits_simps archObjSize_def)
    apply (erule cmap_relation_retype)
    apply (rule relrl)
    done

  thus ?thesis using rf empty kdr zro
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name
                     ko_def[symmetric])
    apply (simp add: carch_state_relation_def cmachine_state_relation_def
                     fpu_null_state_relation_def)
    apply (simp add: rl' cterl tag_disj_via_td_name h_t_valid_clift_Some_iff tcb_C_size)
    apply (clarsimp simp: hrs_htd_update ptr_retyps_htd_safe_neg szo szko
                          kernel_data_refs_domain_eq_rotate
                          cvariable_array_ptr_retyps[OF szo]
                          foldr_upd_app_if [folded data_map_insert_def]
                          zero_ranges_ptr_retyps
                          rl empty projectKOs)
    done
  qed

  have [simp]:
    "of_nat pageBits < (4::word32) = False" by (simp add: pageBits_def)

  show ?thesis
  apply (rule ccorres_from_vcg_nofail2, rule allI)
  apply (rule conseqPre)
   apply vcg
  apply (clarsimp simp: cte_wp_at_ctes_of split: if_split_asm)
  apply (frule(1) ctes_of_valid', clarsimp)
  apply (subst ghost_assertion_size_logic[unfolded o_def, rotated], assumption)
   apply (drule(1) valid_global_refsD_with_objSize)
   apply (simp add: X64SmallPageBits_def pageBits_def)
  apply (erule valid_untyped_capE)
  apply (subst simpler_placeNewObject_def)
      apply ((simp add: word_bits_conv objBits_simps archObjSize_def
                        capAligned_def)+)[4]
  apply (simp add: simpler_modify_def rf_sr_htd_safe)
  apply (subgoal_tac "{frame ..+ 2 ^ pageBits} \<inter> kernel_data_refs = {}")
   prefer 2
   apply (drule(1) valid_global_refsD')
   apply (clarsimp simp: Int_commute pageBits_def X64SmallPageBits_def
                         intvl_range_conv[where bits=pageBits, unfolded pageBits_def word_bits_def,
                                          simplified])
  apply (intro conjI impI)
       apply (erule is_aligned_no_wrap')
       apply (clarsimp simp: X64SmallPageBits_def pageBits_def)
      apply (erule is_aligned_weaken, simp add:pageBits_def)
     apply (simp add: is_aligned_def X64SmallPageBits_def bit_simps)
    apply (simp add: region_actually_is_bytes_dom_s pageBits_def X64SmallPageBits_def)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         size_of_def pageBits_def
                         ptr_retyp_htd_safe_neg)
  apply clarsimp
  apply (cut_tac helper[rule_format])
   prefer 2
   apply fastforce
  apply (subst data_map_insert_def[symmetric])
  apply (erule iffD1[OF rf_sr_upd, rotated -1])
   apply simp_all
  apply (simp add: hrs_htd_update_def hrs_mem_update_def split_def)
  apply (simp add: pageBits_def X64SmallPageBits_def ptr_retyps_gen_def
              del: replicate_numeral)
  done
qed

lemma cmap_relation_ccap_relation:
  "\<lbrakk>cmap_relation (ctes_of s) (cslift s') cte_Ptr ccte_relation;ctes_of s p = Some cte; cteCap cte = cap\<rbrakk>
    \<Longrightarrow> ccap_relation cap
    (h_val (hrs_mem (t_hrs_' (globals s'))) (cap_Ptr &(cte_Ptr p\<rightarrow>[''cap_C''])))"
  apply (erule(1) cmap_relationE1)
  apply (clarsimp simp add: typ_heap_simps' ccte_relation_ccap_relation)
  done

lemma ccorres_move_Guard_Seq_strong:
  "\<lbrakk>\<forall>s s'. (s, s') \<in> sr \<and> P s \<and> P' s' \<longrightarrow> G' s';
    ccorres_underlying sr \<Gamma> r xf arrel axf A C' hs a (c;;d) \<rbrakk>
  \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (A and P) {s. P' s \<and> (G' s \<longrightarrow> s \<in> C')} hs a
    (Guard F (Collect G') c;;
     d)"
  apply (rule ccorres_guard_imp2, erule ccorres_move_Guard_Seq)
   apply assumption
  apply auto
  done

lemma ghost_assertion_data_get_gs_clear_region:
  "gs_get_assn proc (gs_clear_region addr n gs) = gs_get_assn proc gs"
  by (clarsimp simp: ghost_assertion_data_get_def gs_clear_region_def)

lemma ghost_assertion_size_logic_flex:
  "unat (sz :: machine_word) \<le> gsMaxObjectSize s
    \<Longrightarrow> (s, \<sigma>') \<in> rf_sr
    \<Longrightarrow> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' (globals \<sigma>'))
        = gs_get_assn cap_get_capSizeBits_'proc gs
    \<Longrightarrow> gs_get_assn cap_get_capSizeBits_'proc gs = 0 \<or>
            sz \<le> gs_get_assn cap_get_capSizeBits_'proc gs"
  by (metis ghost_assertion_size_logic)

lemma canonical_pspace_strg:
  "valid_pspace' s \<longrightarrow> pspace_canonical' s"
  by (simp add: valid_pspace'_def)

lemma performASIDControlInvocation_ccorres:
notes replicate_numeral[simp del]
shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
             (invs'
               and ct_active'
               and sch_act_simple
               and cte_wp_at' (\<lambda>cte. cteCap cte = capability.UntypedCap isdev frame pageBits idx) parent
               and (\<lambda>s. descendants_of' parent (ctes_of s) = {})
               and ex_cte_cap_to' parent
               and (\<lambda>_. base \<le> mask asid_bits \<and> is_aligned base asid_low_bits))
             (UNIV \<inter> {s. frame_' s = Ptr frame}
                   \<inter> {s. slot_' s = cte_Ptr slot}
                   \<inter> {s. parent_' s = cte_Ptr parent}
                   \<inter> {s. asid_base_' s = base}) []
       (liftE (performASIDControlInvocation (MakePool frame slot parent base)))
       (Call performASIDControlInvocation_'proc)"
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: frame_' slot_' parent_' asid_base_')
   apply (rule_tac P="is_aligned frame pageBits \<and> canonical_address frame \<and> frame \<in> kernel_mappings" in ccorres_gen_asm)
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_split_nothrow[where c="Seq c c'" for c c'])
       apply (fold pageBits_def)[1]
       apply (simp add: hrs_htd_update)
       apply (rule deleteObjects_ccorres)
      apply ceqv
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_abstract_cleanup)
      apply (rule ccorres_symb_exec_l)
        apply (rename_tac pcap)
        apply (rule_tac P = "pcap = (capability.UntypedCap isdev frame pageBits idx)"
                 in ccorres_gen_asm)
        apply (simp add: hrs_htd_update del:fun_upd_apply)
        apply (rule ccorres_split_nothrow)

            apply (rule_tac cap'="UntypedCap isdev frame pageBits idx" in updateFreeIndex_ccorres)
            apply (rule allI, rule conseqPre, vcg)
            apply (rule subsetI, clarsimp simp: typ_heap_simps' pageBits_def isCap_simps)
            apply (frule ccte_relation_ccap_relation, clarsimp)
            apply (frule cap_get_tag_isCap_unfolded_H_cap)
            apply (clarsimp simp: isCap_simps cap_lift_untyped_cap
                                  cap_to_H_simps cap_untyped_cap_lift_def
                                  ccap_relation_def modify_map_def
                                  fun_eq_iff
                          dest!: word_unat.Rep_inverse' split: if_split)
            apply (rule exI, strengthen refl)
            apply (case_tac cte', simp add: cap_lift_untyped_cap max_free_index_def mask_def)
            apply (simp add: mex_def meq_def del: split_paired_Ex)
            apply blast
           apply ceqv
          apply ccorres_remove_UNIV_guard
          apply csymbr
          apply (rule ccorres_Guard_Seq[where F=ShiftError])+
          apply (simp del: Collect_const, simp add: framesize_to_H_def)
          apply (ctac (c_lines 2) add:createObjects_asidpool_ccorres[where idx="max_free_index pageBits"]
                              pre del: ccorres_Guard_Seq)
            apply csymbr
             apply (ctac (no_vcg) add: cteInsert_ccorres)
              apply (simp add: ccorres_seq_skip del: fun_upd_apply)
              apply (rule ccorres_assert)
              apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: gets_def modify_def return_def put_def get_def bind_def
                             asid_shiftr_low_bits_less
                   simp del: fun_upd_apply Collect_const)
              apply (clarsimp simp: word_sle_def word_sless_def Kernel_C.asidLowBits_def simp del: fun_upd_apply)
              apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def cmachine_state_relation_def  simp del: fun_upd_apply)
              apply (clarsimp simp: carch_state_relation_def carch_globals_def simp del: fun_upd_apply)
              apply (simp add: asid_high_bits_of_def fun_upd_def[symmetric]
                          del: fun_upd_apply)
              apply (erule array_relation_update)
                apply (simp add: unat_ucast)
                apply (subst Divides.mod_less, simp)
                 apply (drule leq_asid_bits_shift)
                 apply (simp add: asid_high_bits_def mask_def word_le_nat_alt)
                apply simp
               apply (clarsimp simp: option_to_ptr_def option_to_0_def)
              apply (clarsimp simp: asid_high_bits_def)
             apply wp+
            apply (strengthen valid_pspace_mdb' vp_strgs' valid_pspace_valid_objs' canonical_pspace_strg)
            apply (clarsimp simp: is_simple_cap'_def isCap_simps conj_comms placeNewObject_def2)
            apply (wp createObjects_valid_pspace'[where ty="Inl (KOArch (KOASIDPool f))" and sz = pageBits for f]
                      createObjects_cte_wp_at'[where sz = pageBits]
                   | simp add:makeObjectKO_def objBits_simps archObjSize_def range_cover_full
                   | simp add: bit_simps untypedBits_defs)+
            apply (clarsimp simp:valid_cap'_def capAligned_def)
            apply (wp createObject_typ_at')
           apply clarsimp
           apply vcg
          apply (clarsimp simp:conj_comms objBits_simps archObjSize_def |
                 strengthen valid_pspace_mdb' vp_strgs' invs_valid_pspace'
                 valid_pspace_valid_objs' invs_valid_global'
                 invs_urz)+
          apply (wp updateFreeIndex_forward_invs'
                    updateFreeIndex_caps_no_overlap''[where sz=pageBits]
                    updateFreeIndex_pspace_no_overlap'[where sz=pageBits]
                    updateFreeIndex_caps_overlap_reserved
                    updateFreeIndex_cte_wp_at
                    )
          apply (strengthen exI[where x=parent])
          apply (wp updateFreeIndex_cte_wp_at)
         apply clarsimp
         apply vcg
        apply wp
       apply clarsimp
       apply (wp getSlotCap_wp)
      apply clarsimp
     apply (rule_tac Q'="\<lambda>_. cte_wp_at' ((=) (UntypedCap isdev frame pageBits idx) o cteCap) parent
                           and (\<lambda>s. descendants_range_in' {frame..frame + (2::machine_word) ^ pageBits - (1::machine_word)} parent (ctes_of s))
                           and pspace_no_overlap' frame pageBits
                           and invs'
                           and ct_active'"
                 in hoare_post_imp)
     apply (clarsimp simp: cte_wp_at_ctes_of invs_valid_objs' range_cover_full word_bits_conv
            pageBits_def max_free_index_def asid_low_bits_def)
     apply (case_tac cte,clarsimp simp:invs_valid_pspace')
     apply (frule(1) ctes_of_valid_cap'[OF _ invs_valid_objs'])
     apply (clarsimp simp:valid_cap'_def asid_low_bits_def invs_urz)
     apply (strengthen descendants_range_in_subseteq'[mk_strg I E] refl)
     apply (simp add: untypedBits_defs word_size_bits_def asid_wf_def)
     apply (intro context_conjI)
         apply (simp add:is_aligned_def)
        apply (rule le_m1_iff_lt[THEN iffD1,THEN iffD1])
         apply (simp add:asid_bits_def)
        apply (simp add:mask_def)
       apply simp
      apply (rule descendants_range_caps_no_overlapI'[where d=isdev and cref = parent])
        apply simp
        apply (fastforce simp:cte_wp_at_ctes_of is_aligned_neg_mask_eq)
       apply (clarsimp simp:is_aligned_neg_mask_eq)
     apply (clarsimp dest!: upto_intvl_eq)
    apply (wp deleteObjects_cte_wp_at'[where d=isdev and idx = idx and p = parent]
              deleteObjects_descendants[where d=isdev and p = parent and idx = idx]
              deleteObjects_invs'[where d=isdev and p = parent and idx = idx]
              Detype_R.deleteObjects_descendants[where p = parent and idx = idx]
              deleteObjects_ct_active'[where d=isdev and cref = parent and idx = idx])
   apply clarsimp
   apply vcg
  apply (clarsimp simp: conj_comms invs_valid_pspace')
  apply (frule cte_wp_at_valid_objs_valid_cap', fastforce)
  apply (clarsimp simp: valid_cap'_def capAligned_def cte_wp_at_ctes_of untypedBits_defs
                        descendants_range'_def2 empty_descendants_range_in')
  apply (intro conjI; (rule refl)?)
        apply clarsimp
        apply (drule(1) cte_cap_in_untyped_range[where ptr = frame])
             apply (fastforce simp: cte_wp_at_ctes_of)
            apply assumption+
         apply fastforce
        apply simp
       apply assumption
      apply simp
     apply simp
    apply (erule empty_descendants_range_in')
   apply (fastforce)
  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
  apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap dest!: ccte_relation_ccap_relation)
  apply (clarsimp simp: is_aligned_mask max_free_index_def pageBits_def)
  apply (rule conjI, rule UNIV_I)?
  apply clarsimp?
  apply (erule_tac s = sa in rf_sr_ctes_of_cliftE)
   apply assumption
  apply (frule_tac s = sa in rf_sr_cte_relation)
   apply simp+
  apply (clarsimp simp:typ_heap_simps' region_is_bytes'_def[where sz=0])
  apply (frule ccte_relation_ccap_relation)
  apply (clarsimp simp: cap_get_tag_isCap hrs_htd_update)
  apply (clarsimp simp: hrs_htd_update_def split_def
                         pageBits_def
                   split: if_split)
  apply (clarsimp simp: X64SmallPageBits_def word_sle_def is_aligned_mask[symmetric]
                        ghost_assertion_data_get_gs_clear_region)
  apply (subst ghost_assertion_size_logic_flex[unfolded o_def, rotated])
     apply assumption
    apply (simp add: ghost_assertion_data_get_gs_clear_region[unfolded o_def])
   apply (drule valid_global_refsD_with_objSize, clarsimp)+
   apply (clarsimp simp: isCap_simps dest!: ccte_relation_ccap_relation)
  apply (cut_tac ptr=frame and bits=12
                   and htd="typ_region_bytes frame 12 (hrs_htd (t_hrs_' (globals s')))"
                          in typ_region_bytes_actually_is_bytes)
   apply (simp add: hrs_htd_update)
  apply (clarsimp simp: region_actually_is_bytes'_def[where len=0])
  apply (intro conjI)
         apply (clarsimp elim!:is_aligned_weaken)
        apply (clarsimp simp: vm_page_size_defs)
       apply (simp add:is_aligned_def)
      apply (erule is_aligned_no_wrap',simp)
     apply (simp add: hrs_htd_def)
    apply (clarsimp simp: framesize_to_H_def pageBits_def)
   apply (drule region_actually_is_bytes_dom_s[OF _ order_refl])
   apply (simp add: hrs_htd_def split_def)
  apply (clarsimp simp: ccap_relation_def)
  apply (clarsimp simp: cap_asid_pool_cap_lift)
  apply (clarsimp simp: cap_to_H_def)
  apply (clarsimp simp: asid_bits_def)
  apply (drule word_le_mask_eq, simp)
  apply (simp add: asid_bits_def sign_extend_canonical_address)
  done

lemmas performX64MMUInvocations
    = ccorres_invocationCatch_Inr performInvocation_def
      X64_H.performInvocation_def performX64MMUInvocation_def
      liftE_bind_return_bindE_returnOk

lemma slotcap_in_mem_PML4:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); (s, s') \<in> rf_sr \<rbrakk>
       \<Longrightarrow> \<exists>v. cslift s' (cte_Ptr slot) = Some v
           \<and> (cap_get_tag (cte_C.cap_C v) = scast cap_pml4_cap)
              = (isArchObjectCap cap \<and> isPML4Cap (capCap cap))
           \<and> ccap_relation cap (cte_C.cap_C v)"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
  apply (clarsimp dest!: ccte_relation_ccap_relation)
  apply (simp add: cap_get_tag_isCap_ArchObject2)
  done

declare if_split [split del]

lemma isValidNativeRoot_spec:
  "\<forall>s.
    \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> True}
            Call isValidNativeRoot_'proc
         {t. \<forall>cap. ccap_relation cap (cap_' s) \<longrightarrow> ret__unsigned_long_' t = from_bool (isArchObjectCap cap \<and> isPML4Cap (capCap cap) \<and>
                                        capPML4MappedASID (capCap cap) \<noteq> None)}"
  apply (vcg, clarsimp)
  apply (rule conjI, clarsimp simp: case_bool_If split: if_split)
   apply (rule conjI; clarsimp simp: cap_pml4_cap_lift)
   apply (erule ccap_relationE, clarsimp simp: cap_to_H_def isCap_simps to_bool_def
                                        split: if_split_asm)
   apply (erule ccap_relationE, clarsimp simp: isCap_simps cap_to_H_def)
  by (clarsimp simp: from_bool_def case_bool_If isCap_simps
              dest!: cap_get_tag_isCap_unfolded_H_cap
              split: if_split)

definition
  get_capMappedASID_CL :: "cap_CL option \<Rightarrow> machine_word"
where
  "get_capMappedASID_CL \<equiv> \<lambda>cap. case cap of
     Some (Cap_pml4_cap c) \<Rightarrow> capPML4MappedASID_CL c
   | Some (Cap_pdpt_cap c) \<Rightarrow> capPDPTMappedASID_CL c
   | Some (Cap_page_directory_cap c) \<Rightarrow> capPDMappedASID_CL c"

lemma cap_get_capMappedASID_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_pml4_cap \<or> cap_get_tag \<acute>cap = scast cap_pdpt_cap
               \<or> cap_get_tag \<acute>cap = scast cap_page_directory_cap\<rbrace>
       \<acute>ret__unsigned_long :== PROC cap_get_capMappedASID(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = (get_capMappedASID_CL (cap_lift \<^bsup>s\<^esup>cap))\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capMappedASID_CL_def)
  apply (intro conjI impI;
         clarsimp simp: cap_lifts
                        cap_lift_asid_control_cap
                        cap_lift_irq_control_cap cap_lift_null_cap
                        Kernel_C.asidLowBits_def asid_low_bits_def
                        word_sle_def Let_def mask_def
                        isZombieTCB_C_def ZombieTCB_C_def
                        cap_lift_domain_cap cap_get_tag_scast
                        objBits_defs wordRadix_def
                        c_valid_cap_def cl_valid_cap_def
                 dest!: sym [where t = "ucast (cap_get_tag cap)" for cap])
  apply (auto simp: cap_pml4_cap_lift[symmetric] cap_pdpt_cap_lift[symmetric]
                    cap_page_directory_cap_lift[symmetric])
  done

lemma addrFromPPtr_mask_middle_pml4ShiftBits:
  "\<lbrakk>is_aligned p pageBits; p \<in> kernel_mappings\<rbrakk> \<Longrightarrow>
   addrFromPPtr p && (mask pml4ShiftBits << pageBits) = addrFromPPtr p"
  apply (clarsimp simp: mask_shiftl_decompose kernel_mappings_def)
  apply (subst word_bw_assocs[symmetric])
  apply (subst is_aligned_neg_mask_eq)
   apply (rule aligned_already_mask)
   apply (erule is_aligned_addrFromPPtr)
  apply (clarsimp simp: addrFromPPtr_def X64.pptrBase_def pptr_base_def bit_simps)
  apply (clarsimp simp: mask_def)
  apply (word_bitwise, clarsimp)
  done

lemma decodeX64PageTableInvocation_ccorres:
  "\<lbrakk>interpret_excaps extraCaps' = excaps_map extraCaps; isPageTableCap cp\<rbrakk> \<Longrightarrow>
   ccorres
       (intr_and_se_rel \<currency> dc)
       (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and valid_cap' (ArchObjectCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       hs
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86PageTableInvocation_'proc)"
   (is "_ \<Longrightarrow> _ \<Longrightarrow> ccorres _ _ ?pre _ _ _ _")
  supply Collect_const[simp del] if_cong[cong]
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_' current_extra_caps_' cap_' buffer_'
                simp: decodeX64MMUInvocation_def invocation_eq_use_types decodeX64PageTableInvocation_def)
   apply (simp add: Let_def isCap_simps if_to_top_of_bind
               cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_split_throws)
     apply (simp add: liftE_bindE bind_assoc)
     apply (rule ccorres_symb_exec_l[OF _ getCTE_inv _ empty_fail_getCTE])
      apply (rule ccorres_rhs_assoc)+
      apply (ctac add: isFinalCapability_ccorres)
        apply (simp add: unlessE_def if_to_top_of_bind if_to_top_of_bindE ccorres_seq_cond_raise)
        apply (rule ccorres_cond2'[where R=\<top>])
          apply (clarsimp simp: from_bool_0)
         apply (simp add: throwError_bind invocationCatch_def)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (simp add: returnOk_bind bindE_assoc performX64MMUInvocations)
        apply (ctac add: setThreadState_ccorres)
          apply (ctac add: performPageTableInvocationUnmap_ccorres)
             apply (rule ccorres_alternative2)
             apply (rule ccorres_return_CE, simp+)[1]
            apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
           apply wp
          apply simp
          apply (vcg exspec=performX86PageTableInvocationUnmap_modifies)
         apply (wp sts_invs_minor')
        apply simp
        apply (vcg exspec=setThreadState_modifies)
       apply (wp hoare_drop_imps isFinalCapability_inv)
      apply simp
      apply (vcg exspec=isFinalCapability_modifies)
     apply (wp getCTE_wp)
    apply (vcg exspec=performX86PageTableInvocationUnmap_modifies exspec=isFinalCapability_modifies)
   apply simp
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (simp split: invocation_label.split arch_invocation_label.split
                   add: throwError_bind invocationCatch_def)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply simp
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: word_less_nat_alt throwError_bind invocationCatch_def)
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_equals_throwError)
     apply (simp add: throwError_bind split: list.split)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply csymbr
   apply (simp add: interpret_excaps_test_null excaps_map_def)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: list_case_If2 split_def
                    word_less_nat_alt length_ineq_not_Nil Let_def
                    whenE_bindE_throwError_to_if if_to_top_of_bind)
   apply csymbr
   apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
      apply vcg
     apply clarsimp
     apply (frule cap_get_tag_isCap_unfolded_H_cap)
     apply (clarsimp simp: cap_lift_page_table_cap cap_page_table_cap_lift_def
                           cap_to_H_def
                    elim!: ccap_relationE split: if_split)
     apply (simp add: to_bool_def)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: cap_case_PML4Cap2 split_def)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply csymbr
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply csymbr
       apply (rule ccorres_add_return)
       apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_pml4_cap)
                                          = (isArchObjectCap rv \<and> isPML4Cap (capCap rv)))
                                     \<and> (ccap_relation rv rv')) (fst (extraCaps ! 0))"
                and xf'=vspaceCap_' in ccorres_split_nothrow)
           apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
           apply (drule(1) slotcap_in_mem_PML4)
           apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
           apply (clarsimp simp: typ_heap_simps' mask_def)
           apply (rename_tac rv' t t')
          apply (simp add: word_sless_def word_sle_def)
          apply ceqv
         apply csymbr
         apply clarsimp
         apply (rule ccorres_Cond_rhs_Seq)
          apply ccorres_rewrite
          apply (clarsimp simp: from_bool_0)
          apply (rule_tac P="isArchObjectCap (fst (extraCaps ! 0)) \<and>
                             isPML4Cap (capCap (fst (extraCaps ! 0)))"
                          in ccorres_cases)
           apply (clarsimp simp: hd_conv_nth throwError_bind invocationCatch_def cong: if_cong)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply (clarsimp simp: hd_conv_nth throwError_bind invocationCatch_def cong: if_cong)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: hd_conv_nth)
         apply csymbr
         apply csymbr
         apply csymbr
         apply (simp add: case_option_If2 if_to_top_of_bind if_to_top_of_bindE hd_conv_nth)
         apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
            apply vcg
           apply (fastforce simp: user_vtop_def X64.pptrUserTop_def bit_simps
                                  word_le_nat_alt mask_def hd_conv_nth
                                  length_ineq_not_Nil)
          apply (simp add: throwError_bind invocationCatch_def)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: lookupError_injection invocationCatch_use_injection_handler
                          injection_bindE[OF refl refl] injection_handler_If
                          injection_handler_throwError injection_liftE[OF refl]
                          injection_handler_returnOk bindE_assoc cap_pml4_cap_lift get_capMappedASID_CL_def
                    cong: if_cong)
         apply csymbr
         apply (ctac add: ccorres_injection_handler_csum1 [OF ccorres_injection_handler_csum1,
                                                           OF findVSpaceForASID_ccorres])
            apply (simp add: Collect_False if_to_top_of_bindE)
            apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
               apply vcg
              apply (clarsimp simp: isCap_simps get_capPtr_CL_def)
              apply (frule cap_get_tag_isCap_unfolded_H_cap)
              apply (erule_tac v="rv'" in ccap_relationE, clarsimp simp: cap_to_H_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (simp add: bindE_assoc,
                   simp add: liftE_bindE)
            apply (ctac add: ccorres_injection_handler_csum1 [OF ccorres_injection_handler_csum1,
                                                              OF lookupPDSlot_ccorres])
            apply (rename_tac pd_slot lookup_pd_res)
               apply (rule ccorres_pre_getObject_pde)
               apply (rename_tac pde)
               apply (rule ccorres_cond_false_seq)
               apply ccorres_rewrite
               apply clarsimp
               apply (rename_tac pml4_mapped_asid)
               apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
               apply (rule_tac xf'=ret__int_' and R="ko_at' pde pd_slot" and R'=UNIV and
                               val="from_bool (pde \<noteq> InvalidPDE)"
                               in ccorres_symb_exec_r_known_rv)
                  apply vcg
                  apply (clarsimp simp: from_bool_0)
                  apply (erule cmap_relationE1[OF rf_sr_cpde_relation], erule ko_at_projectKO_opt)
                  apply (clarsimp simp: typ_heap_simps from_bool_eq_if)
                  apply (auto simp: cpde_relation_def Let_def pde_pde_pt_lift_def
                                    pde_pde_pt_lift pde_tag_defs pde_pde_large_lift_def
                                    pde_lift_def case_bool_If
                             split: pde.split_asm if_splits)[1]
                 apply ceqv
                apply clarsimp
                apply (rule ccorres_Cond_rhs_Seq)
                 apply (clarsimp simp: throwError_bind invocationCatch_def
                                       injection_handler_throwError)
                 apply ccorres_rewrite
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (clarsimp simp: syscall_error_to_H_cases)
                apply (clarsimp simp: injection_handler_returnOk)
                apply (simp add: injection_handler_returnOk performX64MMUInvocations bindE_assoc)
                apply csymbr
                apply csymbr
                apply csymbr
                apply csymbr
                apply csymbr
                apply csymbr
                apply (ctac add: setThreadState_ccorres)
                  apply (ctac add: performPageTableInvocationMap_ccorres)
                     apply (rule ccorres_alternative2)
                     apply (rule ccorres_return_CE, simp+)[1]
                    apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                   apply wpsimp+
                  apply (vcg exspec=performX86PageTableInvocationMap_modifies)
                 apply wpsimp+
                apply (vcg exspec=setThreadState_modifies)
               apply (simp add: get_capPtr_CL_def)
              apply (rule_tac s=pml4_mapped_asid and
                              t="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                              in subst,
                     fastforce)
               apply vcg
              apply (rename_tac lookup_pd_ret)
              apply clarsimp
              apply (rule_tac P'="{s. errstate s = lookup_pd_ret}" in ccorres_from_vcg_split_throws[where P=\<top>])
               apply vcg
              apply (rule conseqPre, vcg)
              apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                    syscall_error_to_H_cases exception_defs)
              apply (erule lookup_failure_rel_fault_lift[rotated])
              apply (clarsimp simp: exception_defs)
             apply clarsimp
             apply (wp injection_wp[OF refl] hoare_drop_imps)
            apply (clarsimp simp: get_capPtr_CL_def)
            apply (rename_tac pml4_mapped_asid)
            apply (rule_tac s=pml4_mapped_asid and
                            t="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                            in subst,
                   fastforce)
            apply (vcg exspec=lookupPDSlot_modifies)
           apply clarsimp
           apply (rule_tac P'="{s. errstate s = find_ret}" in ccorres_from_vcg_split_throws[where P=\<top>])
            apply vcg
           apply simp
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                 syscall_error_to_H_cases exception_defs)
           apply (erule lookup_failure_rel_fault_lift[rotated])
           apply (simp add: exception_defs)
          apply simp
          apply (wp injection_wp[OF refl] hoare_drop_imps)
         apply simp
         apply (vcg exspec=findVSpaceForASID_modifies)
        apply simp
        apply (rule_tac Q'="\<lambda>a b. invs' b \<and> valid_cap' (fst (extraCaps ! 0)) b \<and> tcb_at' thread b \<and>
                                 sch_act_wf (ksSchedulerAction b) b \<and> cte_wp_at' (\<lambda>_. True) slot b"
                                 in hoare_strengthen_post)
         apply wp
        apply (fastforce simp: isCap_simps invs_valid_objs' valid_cap'_def valid_tcb_state'_def
                               invs_arch_state' invs_no_0_obj')
       apply vcg
      apply wp
     apply simp
     apply (vcg exspec=getSyscallArg_modifies)
    apply wpsimp+
  apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: cte_wp_at_ctes_of excaps_map_def
                        word_sle_def word_sless_def bit_simps)
  (* X64PageTableUnmap *)
  apply (rule conjI)
   apply (auto simp: ct_in_state'_def isCap_simps valid_tcb_state'_def
              elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
  (* X64PageTableMap *)
  apply (rule conjI)
   apply (clarsimp simp: isCap_simps)
   apply (subgoal_tac "s \<turnstile>' fst (extraCaps ! 0)")
    apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt
                          linorder_not_less)
    apply (clarsimp | drule length_le_helper)+
    apply (clarsimp simp: valid_cap'_def neq_Nil_conv
                          mask_add_aligned page_directory_at'_def
                          word_le_nat_alt[symmetric] bit_simps)
    apply (auto simp: ct_in_state'_def pred_tcb_at' mask_def valid_tcb_state'_def
               elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
   apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def
                         slotcap_in_mem_def)
   apply (auto dest: ctes_of_valid')[1]
  (* X64PageTableUnmap *)
  apply (rule conjI)
   apply (fastforce simp: rf_sr_ksCurThread
                          mask_eq_iff_w2p word_size
                          ct_in_state'_def st_tcb_at'_def
                          word_sle_def word_sless_def
                          typ_heap_simps' bit_simps)
  (* X64PageTableMap *)
  apply (drule_tac t="cteCap ctea" in sym, simp)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject isCap_simps
                        word_sle_def word_sless_def
                        word_less_nat_alt)
  apply (frule length_ineq_not_Nil)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(14))
  apply (clarsimp simp: cap_lift_page_directory_cap hd_conv_nth
                        cap_lift_page_table_cap bit_simps
                        cap_page_directory_cap_lift_def
                        typ_heap_simps' shiftl_t2n[where n=3] field_simps
                 elim!: ccap_relationE)
  apply (clarsimp simp: neq_Nil_conv[where xs=extraCaps]
                        excaps_in_mem_def slotcap_in_mem_def
                 dest!: sym[where s="ArchObjectCap cp" for cp])
  apply (cut_tac p="snd (hd extraCaps)" in ctes_of_valid', simp, clarsimp)
  apply (rule conjI[rotated], clarsimp simp: cap_tag_defs)
  apply (clarsimp simp: valid_cap_simps' rf_sr_ksCurThread)
  apply (rule context_conjI)
   subgoal by (clarsimp simp: get_capMappedASID_CL_def dest!: cap_to_H_PML4Cap)
  apply clarsimp
  apply (rule conjI, clarsimp simp: mask_def)
  apply clarsimp
  apply (rule conjI, clarsimp, rule conjI, clarsimp simp: pde_tag_defs, clarsimp)
   apply (rule conjI[rotated])
    apply (fastforce dest!: cap_lift_page_table_cap
                     intro!: is_aligned_addrFromPPtr[simplified bit_simps, simplified]
                     simp: vmsz_aligned_def cap_to_H_simps cap_page_table_cap_lift_def bit_simps capAligned_def)
   apply clarsimp
   apply (rule conjI)
    (* ccap_relation *)
    apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_page_table_cap_lift[THEN iffD1]
                          cap_to_H_simps asid_wf_def3[simplified asid_bits_def, simplified])
    apply (rule conjI[rotated],
           fastforce simp: sign_extend_canonical_address le_def[symmetric] mask_def word_bw_assocs
                           le_user_vtop_canonical_address[simplified user_vtop_def X64.pptrUserTop_def word_le_nat_alt])
    subgoal by (clarsimp dest!: cap_lift_page_table_cap simp: cap_page_table_cap_lift_def)
   (* cpde_relation *)
   apply (rule conjI, clarsimp simp: cpde_relation_def)
    apply (clarsimp simp: superuser_from_vm_rights_def writable_from_vm_rights_def
                          x64CacheDisabled_def attribsFromWord_def word_and_1 nth_shiftr
                   split: if_split)
    apply (clarsimp dest!: cap_lift_page_table_cap simp: cap_to_H_simps cap_page_table_cap_lift_def)
    apply (rule addrFromPPtr_mask_middle_pml4ShiftBits[simplified pml4ShiftBits_def bit_simps, simplified])
     subgoal by (fastforce simp: valid_cap_simps' capAligned_def bit_simps)
    apply (fastforce dest!: page_table_pte_atI'[where x=0, simplified bit_simps, simplified]
                     intro!: obj_at_kernel_mappings'
                     simp: typ_at_to_obj_at_arches)
   apply (frule (1) cap_lift_PML4Cap_Base)
   subgoal by (auto simp: cap_to_H_simps cap_pml4_cap_lift_def get_capPtr_CL_def
                    dest!: cap_to_H_PML4Cap_tag cap_lift_pml4_cap)
  (* the below proof duplicates some of the sections above *)
  apply (clarsimp simp: pde_tag_defs pde_get_tag_def word_and_1)
  apply safe
    (* ccap_relation *)
    apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_page_table_cap_lift[THEN iffD1]
                          cap_to_H_simps asid_wf_def3[simplified asid_bits_def, simplified])
     apply (rule conjI[rotated],
            fastforce simp: sign_extend_canonical_address le_def[symmetric] mask_def word_bw_assocs
                            le_user_vtop_canonical_address[simplified user_vtop_def X64.pptrUserTop_def word_le_nat_alt])
     subgoal by (clarsimp dest!: cap_lift_page_table_cap simp: cap_page_table_cap_lift_def)
    (* cpde_relation *)
    apply (clarsimp simp: cpde_relation_def superuser_from_vm_rights_def writable_from_vm_rights_def
                          x64CacheDisabled_def attribsFromWord_def word_and_1 nth_shiftr
                    split: if_split)
    apply (clarsimp dest!: cap_lift_page_table_cap simp: cap_to_H_simps cap_page_table_cap_lift_def)
    apply (rule addrFromPPtr_mask_middle_pml4ShiftBits[simplified pml4ShiftBits_def bit_simps, simplified])
     subgoal by (fastforce simp: valid_cap_simps' capAligned_def bit_simps)
    apply (fastforce dest!: page_table_pte_atI'[where x=0, simplified bit_simps, simplified]
                     intro!: obj_at_kernel_mappings'
                     simp: typ_at_to_obj_at_arches)
   apply (frule (1) cap_lift_PML4Cap_Base)
   subgoal by (auto simp: cap_to_H_simps cap_pml4_cap_lift_def get_capPtr_CL_def
                    dest!: cap_to_H_PML4Cap_tag cap_lift_pml4_cap)
  apply (fastforce dest!: cap_lift_page_table_cap
                   intro!: is_aligned_addrFromPPtr[simplified bit_simps, simplified]
                   simp: vmsz_aligned_def cap_to_H_simps cap_page_table_cap_lift_def bit_simps capAligned_def)
  done

lemma checkVPAlignment_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. \<acute>sz < 3\<rbrace> Call checkVPAlignment_'proc
          {t. ret__unsigned_long_' t = from_bool
               (vmsz_aligned (w_' s) (framesize_to_H (sz_' s)))}"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: mask_eq_iff_w2p word_size)
  apply (rule conjI)
   apply (simp add: pageBitsForSize_def bit_simps split: vmpage_size.split)
  apply (simp add: vmsz_aligned_def is_aligned_mask mask_def split: if_split)
  done

definition
  "createSafeMappingEntries ptr vaddr vsz vrights attr pd = doE
     entries \<leftarrow> createMappingEntries ptr vaddr vsz vrights attr pd;
     ensureSafeMapping entries;
     returnOk entries
   odE"

lemma createSafeMappingEntries_fold:
  "(doE
     entries \<leftarrow> createMappingEntries ptr vaddr vsz vrights attr pd;
     _ \<leftarrow> ensureSafeMapping entries;
     f entries
   odE) = (createSafeMappingEntries ptr vaddr vsz vrights attr pd >>=E f)"
  by (simp add: createSafeMappingEntries_def bindE_assoc)

definition
  ptr_range_to_list :: "('a :: c_type) ptr \<Rightarrow> machine_word \<Rightarrow> 'a ptr list"
where
 "ptr_range_to_list ptr lenV \<equiv>
    map (\<lambda>x. CTypesDefs.ptr_add ptr (of_nat x)) [0 ..< unat lenV]"

definition
 "pte_range_relation xs pte_ran \<equiv>
     xs = map ptr_val (ptr_range_to_list (pte_range_C.base_C pte_ran)
                            (pte_range_C.length_C pte_ran))
          \<and> 1 \<le> pte_range_C.length_C pte_ran"

definition
 "pde_range_relation xs pde_ran \<equiv>
     xs = map ptr_val (ptr_range_to_list (pde_range_C.base_C pde_ran)
                            (pde_range_C.length_C pde_ran))
          \<and> 1 \<le> pde_range_C.length_C pde_ran"

definition
 "vm_attribs_relation attr attr' \<equiv>
       x86PATBit_CL (vm_attributes_lift attr') = from_bool (x64PAT attr)
     \<and> x86PCDBit_CL (vm_attributes_lift attr') = from_bool (x64CacheDisabled attr)
     \<and> x86PWTBit_CL (vm_attributes_lift attr') = from_bool (x64WriteThrough attr)"

lemma framesize_from_H_eqs:
  "(framesize_from_H vsz = scast Kernel_C.X86_SmallPage) = (vsz = X64SmallPage)"
  "(framesize_from_H vsz = scast Kernel_C.X86_LargePage) = (vsz = X64LargePage)"
  "(framesize_from_H vsz = scast Kernel_C.X64_HugePage) = (vsz = X64HugePage)"
  by (simp add: framesize_from_H_def vm_page_size_defs split: vmpage_size.split)+

lemma pde_get_tag_alt:
  "pde_lift v = Some pdeC
    \<Longrightarrow> pde_get_tag v = (case pdeC of Pde_pde_pt _ \<Rightarrow> scast pde_pde_pt
          | Pde_pde_large _ \<Rightarrow> scast pde_pde_large)"
  by (auto simp add: pde_lift_def Let_def split: if_split_asm)

lemma cpde_relation_pde_case:
  "cpde_relation pde cpde
     \<Longrightarrow> (case pde of InvalidPDE \<Rightarrow> P
             | PageTablePDE _ _ _ _ _ _ \<Rightarrow> Q
             | LargePagePDE _ _ _ _ _ _ _ _ _ \<Rightarrow> R)
         = (if pde_get_tag cpde = scast pde_pde_pt then
                 if (pde_pde_pt_CL.present_CL (pde_pde_pt_lift cpde) = 0) then P else Q
            else R)"
  by (clarsimp simp: cpde_relation_def Let_def pde_get_tag_alt
                     pde_tag_defs pde_pde_pt_lift_def
              split: X64_H.pde.split_asm)

lemma ccorres_pre_getObject_pte:
  "(\<And>rv. ccorresG rf_sr \<Gamma> r xf (P rv) (P' rv) hs (f rv) c) \<Longrightarrow>
   ccorresG rf_sr \<Gamma> r xf (\<lambda>s. \<forall>pte. ko_at' pte p s \<longrightarrow> P pte s)
            {s. \<forall>pte pte'. cslift s (pte_Ptr p) = Some pte' \<and> cpte_relation pte pte' \<longrightarrow> s \<in> P' pte} hs
     (getObject p >>= f) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule_tac P="ko_at' rv p" in ccorres_cross_over_guard)
      apply assumption
     apply (wp getObject_inv loadObject_default_inv
               getPTE_wp empty_fail_getObject | simp)+
  apply clarsimp
  apply (erule cmap_relationE1[OF rf_sr_cpte_relation], erule ko_at_projectKO_opt)
  apply clarsimp
  done

lemma ptr_add_uint_of_nat [simp]:
  "a  +\<^sub>p uint (of_nat b :: machine_word) = a  +\<^sub>p (int b)"
  by (clarsimp simp: CTypesDefs.ptr_add_def)

declare int_unat[simp]

lemma obj_at_pte_aligned:
  "obj_at' (\<lambda>a::X64_H.pte. True) ptr s ==> is_aligned ptr word_size_bits"
  apply (drule obj_at_ko_at')
  apply (clarsimp dest!:ko_at_is_aligned'
                  simp: objBits_simps archObjSize_def bit_simps
                  elim!: is_aligned_weaken)
  done

lemma cpde_relation_invalid:
 "cpde_relation pdea pde \<Longrightarrow> (pde_get_tag pde = scast pde_pde_pt \<and> pde_pde_pt_CL.present_CL (pde_pde_pt_lift pde) = 0) = isInvalidPDE pdea"
  apply (simp add: cpde_relation_def Let_def)
  apply (simp add: pde_pde_pt_lift_def)
  apply (case_tac pdea, simp_all add: isInvalidPDE_def) [1]
   apply (clarsimp simp: pde_pde_pt_lift pde_pde_pt_lift_def)
  apply (simp add: pde_pde_pt_lift_def pde_pde_pt_lift)
  done

lemma storePTE_Basic_ccorres'':
  "ccorres dc xfdc \<top> {s. ptr_val (f s) = p \<and> cpte_relation pte pte'} hs
     (storePTE p pte)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c f s}
        (Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (f s) pte'))) s)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_gen_asm2, erule storePTE_Basic_ccorres')
  apply simp
  done

lemma pageBitsForSize_le_64: "of_nat (pageBitsForSize x) < (64::machine_word)"
  by (cases x; simp add: bit_simps)

lemma pte_sadness:
  "\<lbrakk> pte' = pte\<lparr>pte_CL.page_base_address_CL := pte_CL.page_base_address_CL pte'\<rparr>;
     f (pte_CL.page_base_address_CL pte) = pte_CL.page_base_address_CL pte \<rbrakk>
   \<Longrightarrow> pte'\<lparr>pte_CL.page_base_address_CL := f (pte_CL.page_base_address_CL pte)\<rparr> = pte"
  apply (cases pte', cases pte, simp)
  done

definition
  "isVMPTE entry \<equiv> \<exists>x y. entry = (VMPTE x, VMPTEPtr y)"

primrec (nonexhaustive)
  thePTE :: "vmpage_entry \<Rightarrow> pte" where
  "thePTE (VMPTE pte) = pte"

primrec (nonexhaustive)
  thePTEPtr :: "vmpage_entry_ptr \<Rightarrow> machine_word" where
  "thePTEPtr (VMPTEPtr p) = p"

lemma performPageInvocationMapPTE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
           and (\<lambda>_. page_entry_map_corres mapping \<and>
                  (isArchPageCap cap \<and> capVPMappedAddress (capCap cap) \<noteq> None)))
       (UNIV \<inter> {s. cpte_relation (thePTE (fst mapping)) (pte_' s)}
             \<inter> {s. ptSlot_' s = pte_Ptr (thePTEPtr (snd mapping))}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. vspace_' s = pml4e_Ptr vspace}
             \<inter> {s. isVMPTE mapping}) []
       (liftE (performPageInvocation (PageMap cap slot mapping vspace)))
       (Call performX86PageInvocationMapPTE_'proc)"
  supply pageBitsForSize_le_64 [simp]
  apply (rule ccorres_gen_asm2)+
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift:  pte_' ptSlot_' cap_' ctSlot_' vspace_')
   apply (clarsimp simp: isVMPTE_def page_entry_map_corres_def)
   apply (ctac)
     apply (rule ccorres_split_nothrow)
         apply (rule storePTE_Basic_ccorres'')
        apply ceqv
       apply csymbr
       apply csymbr
       apply (clarsimp simp: isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap,
                clarsimp simp: cap_frame_cap_lift cap_to_H_def
                        elim!: ccap_relationE
                        split: if_split_asm)
       apply (rule ccorres_split_nothrow)
           apply (rule ccorres_call[where xf'=xfdc])
              apply (ctac add: invalidatePageStructureCacheASID_ccorres)
             apply clarsimp
            apply clarsimp
           apply clarsimp
          apply ceqv
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply wp
       apply (vcg exspec=invalidatePageStructureCacheASID_modifies)
      apply wp
     apply vcg
    apply wp
   apply (rule conseqPre[where P'="UNIV" and P=UNIV, simplified])
   apply vcg
   apply (clarsimp simp: isCap_simps dest!: cap_get_tag_isCap_unfolded_H_cap)
  apply clarsimp
  done

lemma pde_align_ptBits:
  "\<lbrakk> ko_at' (X64_H.PageTablePDE x y z w u v) slot s ;valid_objs' s\<rbrakk>
  \<Longrightarrow> is_aligned (ptrFromPAddr x) ptBits"
  apply (drule ko_at_valid_objs')
    apply simp
   apply (simp add:projectKO_opts_defs injectKO_defs
    split:Structures_H.kernel_object.splits
    arch_kernel_object.splits)+
  apply (simp add:valid_obj'_def)
  apply (rule is_aligned_ptrFromPAddr_n)
   apply simp
  apply (simp add: bit_simps)
  done

lemma storePDE_Basic_ccorres'':
  "ccorres dc xfdc
     (\<lambda>_. True)
     {s. ptr_val (f s) = p \<and> cpde_relation pde pde'} hs
     (storePDE p pde)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c f s}
        (Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (f s) pde'))) s)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_gen_asm2, erule storePDE_Basic_ccorres')
  apply simp
  done

lemma pde_lift_to_large:
  "pde_lift pde = Some (Pde_pde_large pde') \<Longrightarrow> pde_pde_large_lift pde = pde'"
  by (simp add: pde_pde_large_lift_def)

lemma pde_lift_to_tag:
  "pde_lift pde = Some (Pde_pde_large pde') \<Longrightarrow> pde_get_tag pde = scast pde_pde_large"
  by (simp add: pde_lift_def Let_def split: if_split_asm)

lemmas pde_lift_section = pde_lift_to_large pde_lift_to_tag

definition
  "isVMPDE entry \<equiv> \<exists>x y. entry = (VMPDE x, VMPDEPtr y)"

primrec (nonexhaustive)
  thePDE :: "vmpage_entry \<Rightarrow> pde" where
  "thePDE (VMPDE pde) = pde"

primrec (nonexhaustive)
  thePDEPtr :: "vmpage_entry_ptr \<Rightarrow> machine_word" where
  "thePDEPtr (VMPDEPtr p) = p"

lemma performPageInvocationMapPDE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
              and (\<lambda>s. page_entry_map_corres mapping \<and>
                       isArchPageCap cap \<and> capVPMappedAddress (capCap cap) \<noteq> None))
       (UNIV \<inter> {s. cpde_relation (thePDE (fst mapping)) (pde_' s)}
             \<inter> {s. pdSlot_' s = pde_Ptr (thePDEPtr (snd mapping))}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. vspace_' s = pml4e_Ptr vspace}
             \<inter> {s. isVMPDE mapping}) []
       (liftE (performPageInvocation (PageMap cap slot mapping vspace)))
       (Call performX86PageInvocationMapPDE_'proc)"
  supply pageBitsForSize_le_64 [simp]
  apply (rule ccorres_gen_asm2)
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift:  pde_' pdSlot_' cap_' ctSlot_' vspace_')
   apply (clarsimp simp: isVMPDE_def page_entry_map_corres_def)
   apply (ctac)
     apply (rule ccorres_split_nothrow)
         apply (rule storePDE_Basic_ccorres'')
        apply ceqv
       apply csymbr
       apply csymbr
       apply (clarsimp simp: isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap,
                clarsimp simp: cap_frame_cap_lift cap_to_H_def
                        elim!: ccap_relationE
                        split: if_split_asm)
       apply (rule ccorres_split_nothrow)
           apply (rule ccorres_call[where xf'=xfdc])
              apply (ctac add: invalidatePageStructureCacheASID_ccorres)
             apply clarsimp
            apply clarsimp
           apply clarsimp
          apply ceqv
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply wp
       apply (vcg exspec=invalidatePageStructureCacheASID_modifies)
      apply wp
     apply vcg
    apply wp
   apply (rule conseqPre[where P'="UNIV" and P=UNIV, simplified])
   apply vcg
   apply (clarsimp simp: isCap_simps dest!: cap_get_tag_isCap_unfolded_H_cap)
  apply clarsimp
  done

definition
  "isVMPDPTE entry \<equiv> \<exists>x y. entry = (VMPDPTE x, VMPDPTEPtr y)"

primrec (nonexhaustive)
  thePDPTE :: "vmpage_entry \<Rightarrow> pdpte" where
  "thePDPTE (VMPDPTE pdpte) = pdpte"

primrec (nonexhaustive)
  thePDPTEPtr :: "vmpage_entry_ptr \<Rightarrow> machine_word" where
  "thePDPTEPtr (VMPDPTEPtr p) = p"

lemma storePDPTE_Basic_ccorres'':
  "ccorres dc xfdc \<top> {s. ptr_val (f s) = p \<and> cpdpte_relation pte pte'} hs
     (storePDPTE p pte)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c f s}
        (Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (f s) pte'))) s)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_gen_asm2, erule storePDPTE_Basic_ccorres')
  apply simp
  done

lemma updatePDPTE_ccorres:
  "ccorres
            (K (K \<bottom>) \<currency> dc)
            (liftxf errstate id (\<lambda>y. ()) ret__unsigned_long_')
            \<top>
            (UNIV \<inter> {s. asid_' s = asid}
                  \<inter> {s. cpdpte_relation pdpte (pdpte_' s)}
                  \<inter> {s. pdptSlot_' s = pdpte_Ptr pdptPtr}
                  \<inter> {s. vspace_' s = pml4e_Ptr vspace})
            hs
            (doE y <- liftE (storePDPTE pdptPtr pdpte);
                liftE (invalidatePageStructureCacheASID
                 (addrFromPPtr vspace) asid)
             odE)
            (Call updatePDPTE_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: asid_' pdpte_' pdptSlot_' vspace_')
   apply (clarsimp simp: bind_liftE_distrib[symmetric])
   apply (simp only: liftE_liftM ccorres_liftM_simp)
   apply (rule ccorres_split_nothrow)
       apply (rule storePDPTE_Basic_ccorres'')
      apply ceqv
     apply csymbr
     apply (rule ccorres_add_return2)
     apply (rule ccorres_split_nothrow)
         apply (rule ccorres_call[where xf'=xfdc])
            apply (ctac add: invalidatePageStructureCacheASID_ccorres)
           apply clarsimp
          apply clarsimp
         apply clarsimp
        apply ceqv
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply wp
     apply (vcg exspec=invalidatePageStructureCacheASID_modifies)
    apply wp
   apply vcg
  apply clarsimp
  done

lemma performPageInvocationMapPDPTE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (cte_at' slot and (\<lambda>s. page_entry_map_corres mapping \<and> isArchPageCap cap
                            \<and> capVPMappedAddress (capCap cap) \<noteq> None))
       (UNIV \<inter> {s. cpdpte_relation (thePDPTE (fst mapping)) (pdpte_' s)}
             \<inter> {s. pdptSlot_' s = pdpte_Ptr (thePDPTEPtr (snd mapping))}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. vspace_' s = pml4e_Ptr vspace}
             \<inter> {s. isVMPDPTE mapping}) hs
       (liftE (performPageInvocation (PageMap cap slot mapping vspace)))
       (Call performX64ModeMap_'proc)"
  supply pageBitsForSize_le_64 [simp]
  apply (rule ccorres_gen_asm2)
  apply (rule ccorres_gen_asm)
  apply (simp add: performPageInvocation_def)
  apply (cinit' lift:  pdpte_' pdptSlot_' cap_' ctSlot_' vspace_')
   apply (clarsimp simp: page_entry_map_corres_def isVMPDPTE_def)
   apply (rename_tac apdpte apdpteptr a b)
   apply (simp only: bind_liftE_distrib)
   apply (subst liftE_bindE)
   apply ctac
     apply (clarsimp simp: isCap_simps)
     apply csymbr
     apply (clarsimp simp: liftE_foo_to_fooE)
     apply (subst bindE_assoc[symmetric])
     apply (ctac add: updatePDPTE_ccorres)
        apply (rule ccorres_return_CE)
          apply clarsimp
         apply clarsimp
        apply clarsimp
       apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
       apply clarsimp
      apply wp
     apply (vcg exspec=updatePDPTE_modifies)
    apply wp
   apply (clarsimp simp: isCap_simps)
   apply (clarsimp simp: ccap_relation_PageCap_MappedASID)
   apply (frule cap_get_tag_isCap_unfolded_H_cap)
   apply clarsimp
   apply vcg
  apply clarsimp
  done

lemma performPageGetAddress_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and (\<lambda>s. ksCurThread s = thread) and ct_in_state' ((=) Restart))
      (UNIV \<inter> \<lbrace>\<acute>vbase_ptr = Ptr ptr\<rbrace> \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>) []
      (do reply \<leftarrow> performPageInvocation (PageGetAddr ptr);
          liftE (replyOnRestart thread reply isCall) od)
      (Call performPageGetAddress_'proc)"
  apply (cinit' lift: vbase_ptr_' call_' simp: performPageInvocation_def)
   apply (clarsimp simp: bind_assoc)
   apply csymbr
   apply csymbr
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=thread_' in ccorres_abstract, ceqv)
     apply (rename_tac cthread)
     apply (rule_tac P="cthread = tcb_ptr_to_ctcb_ptr thread" in ccorres_gen_asm2)
     apply (rule ccorres_Cond_rhs_Seq[rotated]; clarsimp)
      apply (simp add: replyOnRestart_def liftE_def bind_assoc)
      apply (rule getThreadState_ccorres_foo, rename_tac tstate)
      apply (rule_tac P="tstate = Restart" in ccorres_gen_asm)
      apply clarsimp
      apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
      apply (ctac (no_vcg) add: setThreadState_ccorres)
       apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
       apply clarsimp
       apply (rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply (rule hoare_TrueI[of \<top>])
     apply (rule ccorres_rhs_assoc)+
     apply (clarsimp simp: replyOnRestart_def liftE_def bind_assoc)
     apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
     apply (rule getThreadState_ccorres_foo, rename_tac tstate)
     apply (rule_tac P="tstate = Restart" in ccorres_gen_asm)
     apply (clarsimp simp: bind_assoc)
     apply (simp add: replyFromKernel_def bind_assoc)
     apply (ctac add: lookupIPCBuffer_ccorres)
       apply (ctac add: setRegister_ccorres)
         apply (simp add: setMRs_single)
         apply (ctac add: setMR_as_setRegister_ccorres[where offset=0])
           apply clarsimp
           apply csymbr
           apply (simp only: setMessageInfo_def bind_assoc)
           apply ctac
             apply simp
             apply (ctac add: setRegister_ccorres)
               apply (ctac add: setThreadState_ccorres)
                 apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
                 apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                 apply (rule allI, rule conseqPre, vcg)
                 apply (clarsimp simp: return_def)
                apply (rule hoare_TrueI[of \<top>])
               apply (vcg exspec=setThreadState_modifies)
              apply wpsimp
             apply (vcg exspec=setRegister_modifies)
            apply wpsimp
           apply clarsimp
           apply (vcg)
          apply wpsimp
         apply (clarsimp simp: msgInfoRegister_def X64.msgInfoRegister_def
                               Kernel_C.msgInfoRegister_def)
         apply (vcg exspec=setMR_modifies)
        apply wpsimp
       apply clarsimp
       apply (vcg exspec=setRegister_modifies)
      apply wpsimp
     apply clarsimp
     apply (vcg exspec=lookupIPCBuffer_modifies)
    apply clarsimp
    apply vcg
   apply clarsimp
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: invs_no_0_obj' tcb_at_invs' invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        seL4_MessageInfo_lift_def message_info_to_H_def mask_def)
  apply (cases isCall)
   apply (auto simp: X64.badgeRegister_def X64_H.badgeRegister_def Kernel_C.badgeRegister_def
                     X64.capRegister_def Kernel_C.RDI_def Kernel_C.RSI_def fromPAddr_def
                     pred_tcb_at'_def obj_at'_def ct_in_state'_def)
  done

lemma vmsz_aligned_addrFromPPtr':
  "vmsz_aligned (addrFromPPtr p) sz
       = vmsz_aligned p sz"
  apply (simp add: vmsz_aligned_def addrFromPPtr_def
                   X64.addrFromPPtr_def)
  apply (subgoal_tac "is_aligned X64.pptrBase (pageBitsForSize sz)")
   apply (rule iffI)
    apply (drule(1) aligned_add_aligned)
      apply (simp add: pageBitsForSize_def word_bits_def split: vmpage_size.split)
     apply simp
   apply (erule(1) aligned_sub_aligned)
    apply (simp add: pageBitsForSize_def word_bits_def split: vmpage_size.split)
  apply (simp add: pageBitsForSize_def X64.pptrBase_def is_aligned_def bit_simps
            split: vmpage_size.split)+
  done

lemmas vmsz_aligned_addrFromPPtr
    = vmsz_aligned_addrFromPPtr'
      vmsz_aligned_addrFromPPtr'[unfolded addrFromPPtr_def]
      vmsz_aligned_addrFromPPtr'[unfolded vmsz_aligned_def]
      vmsz_aligned_addrFromPPtr'[unfolded addrFromPPtr_def vmsz_aligned_def]

lemmas framesize_from_H_simps
    = framesize_from_H_def[split_simps vmpage_size.split]

lemma shiftr_asid_low_bits_mask_asid_high_bits:
  "(asid :: machine_word) \<le> mask asid_bits
      \<Longrightarrow> (asid >> asid_low_bits) && mask asid_high_bits = asid >> asid_low_bits"
  apply (rule iffD2 [OF mask_eq_iff_w2p])
   apply (simp add: asid_high_bits_def word_size)
  apply (rule shiftr_less_t2n)
  apply (simp add: asid_low_bits_def asid_high_bits_def mask_def)
  apply (simp add: asid_bits_def)
  done

lemma shiftr_asid_low_bits_mask_eq_0:
  "\<lbrakk> (asid :: machine_word) \<le> mask asid_bits; asid >> asid_low_bits = 0 \<rbrakk>
        \<Longrightarrow> (asid && mask asid_low_bits = 0) = (asid = 0)"
  apply (rule iffI[rotated])
   apply simp
  apply (rule asid_low_high_bits)
     apply (rule More_Word.ucast_up_inj[where 'b=machine_word_len]; simp add: asid_low_bits_of_mask_eq)
    apply (simp add: ucast_asid_high_bits_is_shift)
   apply (simp add: asid_wf_def mask_def)
  apply (rule asid_wf_0)
  done

lemma slotcap_in_mem_valid:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); valid_objs' s \<rbrakk>
            \<Longrightarrow> s \<turnstile>' cap"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) ctes_of_valid')
  done

lemma injection_handler_if_returnOk:
  "injection_handler Inl (if a then b else returnOk c)
  = (if a then (injection_handler Inl b) else returnOk c)"
  apply (clarsimp simp:whenE_def injection_handler_def)
  apply (clarsimp simp:injection_handler_def
    throwError_def return_def bind_def returnOk_def
    handleE'_def split:if_splits)
  done

lemma pbfs_less: "pageBitsForSize sz < 31"
  by (case_tac sz,simp_all add: bit_simps)

lemma cte_wp_at_eq_gsMaxObjectSize:
  "cte_wp_at' ((=) cap o cteCap) slot s
    \<Longrightarrow> valid_global_refs' s
    \<Longrightarrow> 2 ^ capBits cap \<le> gsMaxObjectSize s"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule(1) valid_global_refsD_with_objSize)
  apply (clarsimp simp: capMaster_eq_capBits_eq[OF capMasterCap_maskCapRights])
  done

lemma two_nat_power_pageBitsForSize_le:
  "(2 :: nat) ^ pageBits \<le> 2 ^ pageBitsForSize vsz"
  by (cases vsz, simp_all add: pageBits_def bit_simps)

lemma ptrFromPAddr_add_left:
  "ptrFromPAddr (x + y) = ptrFromPAddr x + y"
  unfolding ptrFromPAddr_def by simp

lemma at_least_3_args:
  "\<not>  length args < 3 \<Longrightarrow> \<exists>a b c d. args = a#b#c#d"
  apply (case_tac args; simp)
  apply (rename_tac list, case_tac list; simp)+
  done

lemma list_3_collapse:
  "\<lbrakk> length xs \<ge> 3; a = xs ! 0; b = xs ! 1; c = xs ! 2; d = drop 3 xs \<rbrakk> \<Longrightarrow> a # b # c # d = xs"
  apply (case_tac xs; simp)
  apply (rename_tac list, case_tac list; simp)+
  done

lemma createSafeMappingEntries_PTE_ccorres:
  "ccorres (syscall_error_rel \<currency> (\<lambda>rv rv'. isVMPTE rv \<and> cpte_relation (thePTE (fst rv)) (fst rv')
                                         \<and> (snd rv' = pte_Ptr (thePTEPtr (snd rv)))))
     (liftxf errstate create_mapping_pte_return_C.status_C
             (\<lambda>v. (create_mapping_pte_return_C.pte_C v,
                   create_mapping_pte_return_C.ptSlot_C v))
             ret__struct_create_mapping_pte_return_C_')
     (valid_objs' and page_map_l4_at' pml4 and
         (\<lambda>_. vsz = X64SmallPage \<and> vmsz_aligned (addrFromPPtr base) vsz
              \<and> base \<in> kernel_mappings))
     (UNIV \<inter> {s. base_' s = (addrFromPPtr base)} \<inter> {s. vaddr___unsigned_long_' s = vaddr}
           \<inter> {s. vmrights_to_H (vmRights_' s) = vrights \<and> vmRights_' s < 4 \<and> vmRights_' s \<noteq> 0}
           \<inter> {s. vm_attribs_relation attr (attr_' s)}
           \<inter> {s. vspace_' s = pml4e_Ptr pml4}) hs
     (createSafeMappingEntries (addrFromPPtr base) vaddr vsz vrights attr pml4)
     (Call createSafeMappingEntries_PTE_'proc)"
  supply Collect_const[simp del]
    apply (rule ccorres_gen_asm)
  apply (cinit lift: base_' vaddr___unsigned_long_' vmRights_' attr_' vspace_')
   apply (simp add: createSafeMappingEntries_def createMappingEntries_def
                    ensureSafeMapping_def framesize_from_H_eqs)
   apply (simp add: lookupError_injection bindE_assoc)
   apply (ctac add: ccorres_injection_handler_csum1[OF lookupPTSlot_ccorres])
      apply (simp add: Collect_False liftE_bindE)
      apply csymbr+
      apply (rule ccorres_return_CE, simp+)[1]
     apply (simp, ccorres_rewrite)
     apply (rule_tac P'="{s. lu_ret___struct_lookupPTSlot_ret_C = errstate s}" in ccorres_from_vcg_throws[where P=\<top>])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: fst_throwError_returnOk syscall_error_to_H_cases
                           syscall_error_rel_def exception_defs)
     apply (erule lookup_failure_rel_fault_lift[rotated])
     apply (simp add: exception_defs)
    apply wpsimp
   apply (clarsimp simp: isVMPTE_def)
   apply (vcg exspec=lookupPTSlot_modifies)
  apply clarsimp
  apply (clarsimp simp: cpte_relation_def Let_def vm_attribs_relation_def)
  apply (rule addrFromPPtr_mask_middle_pml4ShiftBits[simplified, simplified bit_simps])
   apply (clarsimp simp: vmsz_aligned_addrFromPPtr' vmsz_aligned_aligned_pageBits[simplified bit_simps])
  apply clarsimp
  done

lemma pde_case_isPageTablePDE:
  "(case pde of PageTablePDE _ _ _ _ _ _ \<Rightarrow> P | _ \<Rightarrow> Q)
       = (if isPageTablePDE pde then P else Q)"
  by (clarsimp simp: isPageTablePDE_def split: pde.splits)

primrec
  shiftBitsForSize :: "vmpage_size \<Rightarrow> nat"
where
  "shiftBitsForSize X64SmallPage = pml4ShiftBits"
| "shiftBitsForSize X64LargePage = pdptShiftBits"
| "shiftBitsForSize X64HugePage = pdShiftBits"

lemma shiftBits_pageBits_add[simp]:
  "shiftBitsForSize sz + pageBitsForSize sz = 51"
  by (case_tac sz; clarsimp simp: bit_simps)

lemma addrFromPPtr_mask_middle_shiftBits:
  "\<lbrakk>is_aligned p (pageBitsForSize sz); p \<in> kernel_mappings\<rbrakk> \<Longrightarrow>
   addrFromPPtr p && (mask (shiftBitsForSize sz) << (pageBitsForSize sz)) = addrFromPPtr p"
  apply (clarsimp simp: mask_shiftl_decompose kernel_mappings_def)
  apply (subst word_bw_assocs[symmetric])
  apply (subst is_aligned_neg_mask_eq)
   apply (rule aligned_already_mask)
   apply (clarsimp simp: is_aligned_addrFromPPtr_pageBitsForSize)
  apply (clarsimp simp: addrFromPPtr_def X64.pptrBase_def pptr_base_def bit_simps)
  apply (clarsimp simp: mask_def)
  apply (word_bitwise, clarsimp)
  done

lemma createSafeMappingEntries_PDE_ccorres:
  "ccorres (syscall_error_rel \<currency> (\<lambda>rv rv'. isVMPDE rv \<and> cpde_relation (thePDE (fst rv)) (fst rv')
                                         \<and> (snd rv' = pde_Ptr (thePDEPtr (snd rv)))))
     (liftxf errstate create_mapping_pde_return_C.status_C
             (\<lambda>v. (create_mapping_pde_return_C.pde_C v,
                   create_mapping_pde_return_C.pdSlot_C v))
             ret__struct_create_mapping_pde_return_C_')
     (valid_objs' and page_map_l4_at' pml4 and
         (\<lambda>_. vsz = X64LargePage \<and> vmsz_aligned (addrFromPPtr base) vsz
              \<and> base \<in> kernel_mappings))
     (UNIV \<inter> {s. base_' s = (addrFromPPtr base)} \<inter> {s. vaddr___unsigned_long_' s = vaddr}
           \<inter> {s. vmrights_to_H (vmRights_' s) = vrights \<and> vmRights_' s < 4 \<and> vmRights_' s \<noteq> 0}
           \<inter> {s. vm_attribs_relation attr (attr_' s)}
           \<inter> {s. vspace_' s = pml4e_Ptr pml4}) hs
     (createSafeMappingEntries (addrFromPPtr base) vaddr vsz vrights attr pml4)
     (Call createSafeMappingEntries_PDE_'proc)"
  supply Collect_const[simp del]
  apply (rule ccorres_gen_asm)
  apply (cinit lift: base_' vaddr___unsigned_long_' vmRights_' attr_' vspace_')
   apply (simp add: createSafeMappingEntries_def createMappingEntries_def
                    ensureSafeMapping_def framesize_from_H_eqs)
   apply (simp add: lookupError_injection bindE_assoc)
   apply (ctac add: ccorres_injection_handler_csum1[OF lookupPDSlot_ccorres])
      apply (simp add: Collect_False liftE_bindE)
      apply (rule ccorres_pre_getObject_pde)
      apply csymbr
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule_tac xf'="ret__int_'" and val="from_bool (isPageTablePDE x)"
               and R="ko_at' x rv"
               in ccorres_symb_exec_r_known_rv[where R'=UNIV])
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (erule cmap_relationE1[OF rf_sr_cpde_relation], erule ko_at_projectKO_opt)
         apply (clarsimp simp: typ_heap_simps cpde_relation_def Let_def)
         apply (case_tac x;
                fastforce simp: pde_lifts isPageTablePDE_def pde_pde_pt_lift_def)
        apply ceqv
       apply (clarsimp simp: pde_case_isPageTablePDE)
       apply (rule ccorres_Cond_rhs_Seq, clarsimp)
        apply ccorres_rewrite
        apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: fst_throwError_returnOk exception_defs syscall_error_to_H_cases syscall_error_rel_def)
       apply clarsimp
       apply csymbr+
       apply (rule ccorres_return_CE, simp+)[1]
      apply (clarsimp simp: isVMPDE_def)
      apply vcg
     apply (simp, ccorres_rewrite)
     apply (rule_tac P'="{s. lu_ret___struct_lookupPDSlot_ret_C = errstate s}" in ccorres_from_vcg_throws[where P=\<top>])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: fst_throwError_returnOk syscall_error_to_H_cases
                           syscall_error_rel_def exception_defs)
     apply (erule lookup_failure_rel_fault_lift[rotated])
     apply (simp add: exception_defs)
    apply clarsimp
    apply wpsimp
   apply (clarsimp simp: if_P_1_0_neq_0)
   apply (vcg exspec=lookupPDSlot_modifies)
  apply (clarsimp simp: vm_attribs_relation_def typ_heap_simps from_bool_eq_if'
                        is_aligned_addrFromPPtr_pageBitsForSize[where sz=X64LargePage, simplified]
                        vmsz_aligned_def
                  dest!: addrFromPPtr_mask_middle_shiftBits[where sz=X64LargePage, simplified])
  apply (clarsimp simp: bit_simps cpde_relation_def isPageTablePDE_def
                split: pde.splits)
  done

lemma createSafeMappingEntries_PDPTE_ccorres:
  "ccorres (syscall_error_rel \<currency> (\<lambda>rv rv'. isVMPDPTE rv \<and> cpdpte_relation (thePDPTE (fst rv)) (fst rv')
                                         \<and> (snd rv' = pdpte_Ptr (thePDPTEPtr (snd rv)))))
     (liftxf errstate create_mapping_pdpte_return_C.status_C
             (\<lambda>v. (create_mapping_pdpte_return_C.pdpte_C v,
                   create_mapping_pdpte_return_C.pdptSlot_C v))
             ret__struct_create_mapping_pdpte_return_C_')
     (valid_objs' and page_map_l4_at' pml4 and
         (\<lambda>_. vsz = X64HugePage \<and> vmsz_aligned (addrFromPPtr base) vsz
              \<and> base \<in> kernel_mappings))
     (UNIV \<inter> {s. base_' s = (addrFromPPtr base)} \<inter> {s. vaddr___unsigned_long_' s = vaddr}
           \<inter> {s. vmrights_to_H (vmRights_' s) = vrights \<and> vmRights_' s < 4 \<and> vmRights_' s \<noteq> 0}
           \<inter> {s. vm_attribs_relation attr (attr_' s)}
           \<inter> {s. vspace_' s = pml4e_Ptr pml4}) hs
     (createSafeMappingEntries (addrFromPPtr base) vaddr vsz vrights attr pml4)
     (Call createSafeMappingEntries_PDPTE_'proc)"
  supply Collect_const[simp del]
  apply (rule ccorres_gen_asm)
  apply (cinit lift: base_' vaddr___unsigned_long_' vmRights_' attr_' vspace_')
   apply (simp add: createSafeMappingEntries_def createMappingEntries_def
                    ensureSafeMapping_def framesize_from_H_eqs)
   apply (simp add: lookupError_injection bindE_assoc)
   apply (ctac add: ccorres_injection_handler_csum1[OF lookupPDPTSlot_ccorres])
      apply (simp add: Collect_False liftE_bindE)
      apply (rule ccorres_pre_getObject_pdpte)
      apply csymbr
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule_tac xf'="ret__int_'" and val="from_bool (isPageDirectoryPDPTE x)"
               and R="ko_at' x rv"
               in ccorres_symb_exec_r_known_rv[where R'=UNIV])
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (erule cmap_relationE1[OF rf_sr_cpdpte_relation], erule ko_at_projectKO_opt)
         apply (clarsimp simp: typ_heap_simps cpdpte_relation_def Let_def)
         apply (case_tac x;
                fastforce simp: pdpte_lifts isPageDirectoryPDPTE_def pdpte_pdpte_pd_lift_def)
        apply ceqv
       apply (clarsimp simp: pdpte_case_isPageDirectoryPDPTE)
       apply (rule ccorres_Cond_rhs_Seq, clarsimp)
        apply ccorres_rewrite
        apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: fst_throwError_returnOk exception_defs syscall_error_to_H_cases syscall_error_rel_def)
       apply clarsimp
       apply csymbr+
       apply (rule ccorres_return_CE, simp+)[1]
      apply (clarsimp simp: isVMPDPTE_def)
      apply vcg
     apply (simp, ccorres_rewrite)
     apply (rule_tac P'="{s. lu_ret___struct_lookupPDPTSlot_ret_C = errstate s}" in ccorres_from_vcg_throws[where P=\<top>])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: fst_throwError_returnOk syscall_error_to_H_cases
                           syscall_error_rel_def exception_defs)
     apply (erule lookup_failure_rel_fault_lift[rotated])
     apply (simp add: exception_defs)
    apply clarsimp
    apply wpsimp
   apply (clarsimp simp: if_P_1_0_neq_0)
   apply (vcg exspec=lookupPDPTSlot_modifies)
  apply (clarsimp simp: vm_attribs_relation_def typ_heap_simps from_bool_eq_if'
                        is_aligned_addrFromPPtr_pageBitsForSize[where sz=X64HugePage, simplified]
                        vmsz_aligned_def
                  dest!: addrFromPPtr_mask_middle_shiftBits[where sz=X64HugePage, simplified])
  apply (clarsimp simp: bit_simps cpdpte_relation_def isPageDirectoryPDPTE_def
                split: pdpte.splits)
  done

lemma ccap_relation_PML4Cap_BasePtr:
  "ccap_relation (ArchObjectCap (PML4Cap p r)) ccap
    \<Longrightarrow> capPML4BasePtr_CL (cap_pml4_cap_lift ccap) = p"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  by (drule (1) cap_lift_PML4Cap_Base, clarsimp)

lemma decodeX86ModeMapPage_ccorres:
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
            (invs' and page_map_l4_at' pml4
                   and cte_wp_at' \<top> slot and (\<lambda>s. thread = ksCurThread s)
                   and K (vmsz_aligned base vsz \<and> base \<in> kernel_mappings \<and> vsz = X64HugePage
                          \<and> isPageCap cap \<and> capVPBasePtr cap = base \<and> capVPMappedAddress cap \<noteq> None))
            (UNIV \<inter> \<lbrace>\<acute>label___unsigned_long = scast X86PageMap\<rbrace>
                  \<inter> \<lbrace>\<acute>page_size = framesize_from_H vsz\<rbrace>
                  \<inter> \<lbrace>\<acute>vroot = pml4e_Ptr pml4\<rbrace>
                  \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace>
                  \<inter> \<lbrace>\<acute>paddr = addrFromPPtr base\<rbrace>
                  \<inter> \<lbrace>vmrights_to_H \<acute>vm_rights = rights \<and> \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace>
                  \<inter> \<lbrace>vm_attribs_relation attribs \<acute>vm_attr\<rbrace>
                  \<inter> \<lbrace>\<acute>vaddr___unsigned_long = vaddr\<rbrace>
                  \<inter> \<lbrace>\<acute>cte = cte_Ptr slot\<rbrace>)
            hs
            (doE x <- injection_handler Inl
                  (createSafeMappingEntries (addrFromPPtr base) vaddr vsz rights attribs pml4);
                 invocationCatch thread isBlocking isCall Invocations_H.invocation.InvokeArchObject
                    (Inr (invocation.InvokePage (PageMap (ArchObjectCap cap) slot x pml4)))
             odE)
            (Call decodeX86ModeMapPage_'proc)"
  supply if_cong[cong] tl_drop_1[simp] Collect_const[simp del]
  apply (simp add: K_def)
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: label___unsigned_long_' page_size_' vroot_' cap_' paddr_' vm_rights_' vm_attr_'
                      vaddr___unsigned_long_' cte_'
                simp: bindE_assoc injection_handler_bindE)
   apply csymbr (* config_set(CONFIG_HUGE_PAGE) *)
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (clarsimp simp: framesize_from_H_simps, ccorres_rewrite)
   apply (rule ccorres_rhs_assoc)+
   apply csymbr
   apply (ctac add: ccorres_injection_handler_csum1 [OF createSafeMappingEntries_PDPTE_ccorres])
      apply (simp add: Collect_False performX64MMUInvocations bindE_assoc bind_assoc)
      apply (ctac add: setThreadState_ccorres)
        apply (ctac(no_vcg) add: performPageInvocationMapPDPTE_ccorres)
          apply (rule ccorres_gen_asm)
          apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
          apply (rule ccorres_alternative2)
          apply (rule ccorres_return_CE, simp+)[1]
         apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
        apply (wpsimp simp: performPageInvocation_def)
       apply (wp sts_invs_minor')
      apply simp
      apply (vcg exspec=setThreadState_modifies)
     apply (simp, ccorres_rewrite)
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply (simp add: createSafeMappingEntries_def)
    apply (wp injection_wp[OF refl] createMappingEntries_wf)
   apply (simp add: all_ex_eq_helper)
   apply (vcg exspec=createSafeMappingEntries_PDPTE_modifies)
  by (fastforce simp: invs_valid_objs' tcb_at_invs' vmsz_aligned_addrFromPPtr'
                      valid_tcb_state'_def invs_sch_act_wf' rf_sr_ksCurThread
                      arch_invocation_label_defs mask_def isCap_simps)

lemma valid_cap'_PageCap_kernel_mappings:
  "\<lbrakk>pspace_in_kernel_mappings' s; isPageCap cap; valid_cap' (ArchObjectCap cap) s\<rbrakk>
     \<Longrightarrow> capVPBasePtr cap \<in> kernel_mappings"
  apply (clarsimp simp: valid_cap'_def isCap_simps)
  apply (drule_tac x=0 in spec)
  apply (case_tac v3; fastforce simp: bit_simps typ_at_to_obj_at_arches obj_at_kernel_mappings'
                              split: if_splits)
  done

lemma ccap_relation_PageCap_MappedAddress_update:
  "\<lbrakk>cap_lift cap = Some (Cap_frame_cap (cap_frame_cap_lift cap));
    cp = PageCap f_base f_vmr mt sz f_dev f_addr;
    cap_to_H (Cap_frame_cap (cap_frame_cap_lift cap)) = ArchObjectCap cp;
    c_valid_cap cap; 0 < asid; asid_wf asid;
    cap_frame_cap_lift cap' = cap_frame_cap_lift cap
        \<lparr>capFMappedASID_CL := asid && mask 16,
           capFMappedAddress_CL := sign_extend 47 vaddr,
           capFMapType_CL := newmt\<rparr>;
    cap_lift cap' = Some (Cap_frame_cap (cap_frame_cap_lift cap
            \<lparr>capFMappedASID_CL := asid && mask 16,
               capFMappedAddress_CL := sign_extend 47 vaddr,
               capFMapType_CL := newmt\<rparr>));
    newmt = scast X86_MappingVSpace; canonical_address vaddr\<rbrakk>
    \<Longrightarrow> ccap_relation (ArchObjectCap (PageCap f_base f_vmr VMVSpaceMap sz f_dev (Some (asid, vaddr)))) cap'"
   apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_frame_cap_lift[THEN iffD1]
                         cap_to_H_simps asid_wf_def3[simplified asid_bits_def, simplified])
   apply (rule conjI, clarsimp simp: maptype_to_H_def vm_page_map_type_defs mask_def)
   apply (rule conjI,
           clarsimp simp: sign_extend_canonical_address le_def[symmetric] mask_def word_bw_assocs
                          le_user_vtop_canonical_address[simplified user_vtop_def
                          X64.pptrUserTop_def word_le_nat_alt] vm_page_map_type_defs
                          canonical_address_user_vtop[simplified user_vtop_def X64.pptrUserTop_def]
                   split: if_split)
    apply (rule conjI; word_bitwise, clarsimp)
   by (clarsimp simp: c_valid_cap_def cl_valid_cap_def vm_page_map_type_defs mask_def)

lemma framesize_to_from_H:
  "sz < 3 \<Longrightarrow> framesize_from_H (framesize_to_H sz) = sz"
   apply (clarsimp simp: framesize_to_H_def framesize_from_H_def
                Kernel_C.X86_SmallPage_def Kernel_C.X86_LargePage_def
                Kernel_C.X64_HugePage_def
           split: if_split vmpage_size.splits)
  by (word_bitwise, auto)

lemma cap_get_tag_PDPTCap:
  "ccap_relation cap cap' \<Longrightarrow>
     (cap_get_tag cap' = SCAST(32 signed \<rightarrow> 64) cap_pdpt_cap) =
     (cap = ArchObjectCap
        (PDPointerTableCap (capPDPTBasePtr_CL (cap_pdpt_cap_lift cap'))
                           (if to_bool (capPDPTIsMapped_CL (cap_pdpt_cap_lift cap'))
                            then Some (capPDPTMappedASID_CL (cap_pdpt_cap_lift cap'),
                                       capPDPTMappedAddress_CL (cap_pdpt_cap_lift cap'))
                            else None)))"
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap_unfolded_H_cap)
  done

lemma cap_get_tag_PML4Cap:
  "ccap_relation cap cap' \<Longrightarrow>
     (cap_get_tag cap' = SCAST(32 signed \<rightarrow> 64) cap_pml4_cap) =
     (cap = ArchObjectCap
        (PML4Cap (capPML4BasePtr_CL (cap_pml4_cap_lift cap'))
                          (if to_bool (capPML4IsMapped_CL (cap_pml4_cap_lift cap'))
                           then Some (capPML4MappedASID_CL (cap_pml4_cap_lift cap'))
                           else None)))"
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap_unfolded_H_cap)
  done

lemma ccap_relation_capPML4MappedASID_liftE:
  "\<lbrakk> ccap_relation c c'; cap_get_tag c' = SCAST(32 signed \<rightarrow> 64) cap_pml4_cap;
     capPML4MappedASID (capCap c) = Some y \<rbrakk>
    \<Longrightarrow> capPML4MappedASID_CL (cap_pml4_cap_lift c') = the (capPML4MappedASID (capCap c))"
  by (simp add: cap_get_tag_PML4Cap split: if_splits)

lemma ccap_relation_PageCap_generics:
  "ccap_relation (ArchObjectCap (PageCap word vmrights mt vmpage_size d map_data)) cap'
    \<Longrightarrow> (map_data \<noteq> None \<longrightarrow>
           capFMappedAddress_CL (cap_frame_cap_lift cap')
                    = snd (the map_data)
         \<and> capFMappedASID_CL (cap_frame_cap_lift cap')
                    = fst (the map_data))
      \<and> ((capFMappedASID_CL (cap_frame_cap_lift cap') = 0)
                    = (map_data = None))
      \<and> vmrights_to_H (capFVMRights_CL (cap_frame_cap_lift cap')) = vmrights
      \<and> framesize_to_H (capFSize_CL (cap_frame_cap_lift cap')) = vmpage_size
      \<and> capFBasePtr_CL (cap_frame_cap_lift cap') = word
      \<and> to_bool (capFIsDevice_CL (cap_frame_cap_lift cap')) = d
      \<and> capFSize_CL (cap_frame_cap_lift cap') < 3
      \<and> capFMapType_CL (cap_frame_cap_lift cap') < 2
      \<and> capFVMRights_CL (cap_frame_cap_lift cap') < 4
      \<and> capFVMRights_CL (cap_frame_cap_lift cap') \<noteq> 0"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (frule cap_get_tag_PageCap_frame)
  apply (frule ccap_relation_c_valid_cap)
  apply (clarsimp simp: cap_frame_cap_lift c_valid_cap_def cl_valid_cap_def split: if_split_asm)
  done

lemma throwError_invocationCatch:
  "throwError a >>= invocationCatch b c d e = throwError (Inl a)"
  by (simp add: invocationCatch_def throwError_bind)

lemma canonical_address_cap_frame_cap:
  "cap_get_tag cap = SCAST(32 signed \<rightarrow> 64) cap_frame_cap \<Longrightarrow>
     canonical_address (capFMappedAddress_CL (cap_frame_cap_lift cap))"
  apply (frule_tac cap_lift_frame_cap)
  apply (subst(asm) cap_frame_cap_lift)
  apply clarsimp
  apply (drule_tac t="cap_frame_cap_lift cap" in sym)
  apply (rule sign_extend_canonical_address[THEN iffD1])
  apply (fastforce simp: sign_extend_sign_extend_eq)
  done

lemma decodeX64FrameInvocation_ccorres:
  notes if_cong[cong] option.case_cong[cong] Collect_const[simp del]
  defines "does_not_throw args extraCaps maptype pg_sz mapdata \<equiv>
           (mapdata = None \<longrightarrow> \<not> (unat user_vtop < unat (hd args)
                                  \<or> unat user_vtop < unat (hd args + 2 ^ pageBitsForSize pg_sz)))
           \<and> (mapdata \<noteq> None \<longrightarrow>
                (fst (the mapdata) = (the (capPML4MappedASID (capCap (fst (extraCaps ! 0)))))
                 \<and> maptype = VMVSpaceMap
                 \<and> snd (the mapdata) = hd args))"
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps;
          isPageCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86FrameInvocation_'proc)"
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_' current_extra_caps_' cap_' buffer_' call_'
                simp: decodeX64MMUInvocation_def )
   apply (simp add: Let_def isCap_simps invocation_eq_use_types split_def decodeX64FrameInvocation_def
              cong: StateSpace.state.fold_congs globals.fold_congs
                    if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong)
   apply (rule ccorres_Cond_rhs[rotated])+
      apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
      apply (rule ccorres_equals_throwError)
       apply (fastforce simp: throwError_bind invocationCatch_def
                       split: invocation_label.split arch_invocation_label.split)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)

     \<comment> \<open>PageGetAddress\<close>
     apply (simp add: returnOk_bind bindE_assoc performX64MMUInvocations)
     apply (rule ccorres_rhs_assoc)+
     apply (ctac add: setThreadState_ccorres)
       apply csymbr
       apply (rule ccorres_nondet_refinement)
        apply (rule is_nondet_refinement_bindE)
         apply (rule is_nondet_refinement_refl)
        apply (simp split: if_split, rule conjI[rotated])
         apply (rule impI, rule is_nondet_refinement_refl)
        apply (rule impI, rule is_nondet_refinement_alternative1)
       apply (clarsimp simp: liftE_bindE)
       apply (rule ccorres_add_returnOk)
       apply (ctac(no_vcg) add: performPageGetAddress_ccorres)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_return_C_errorE, simp+)[1]
       apply (wpsimp wp: sts_invs_minor' ct_in_state'_set)+
     apply (vcg exspec=setThreadState_modifies)

    \<comment> \<open>PageUnmap\<close>
    apply (simp add: returnOk_bind bindE_assoc performX64MMUInvocations)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac add: setThreadState_ccorres)
      apply (ctac(no_vcg) add: performPageInvocationUnmap_ccorres)
        apply (rule ccorres_gen_asm)
        apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
        apply (rule ccorres_alternative2)
        apply (rule ccorres_return_CE, simp+)[1]
       apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
      apply (wpsimp simp: performPageInvocation_def)
     apply (wp sts_invs_minor')
    apply simp
    apply (vcg exspec=setThreadState_modifies)

   \<comment> \<open>PageMap\<close>
   apply (rename_tac word rghts maptype pg_sz mapdata call' buffer' cap excaps
                     cte length___unsigned_long invLabel)
   apply simp
   apply (rule ccorres_rhs_assoc)+
   apply csymbr+
   apply (simp add: word_less_nat_alt)
   (* throw on length < 3 *)
   apply (rule ccorres_Cond_rhs_Seq)
    apply simp
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind invocationCatch_def split: list.split)
    apply (rule ccorres_cond_true_seq)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply csymbr
   apply (simp add: interpret_excaps_test_null excaps_map_def)
   (* throw if no excaps *)
   apply (clarsimp dest!: at_least_3_args)
   apply (rule ccorres_guard_imp)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (rule ccorres_equals_throwError)
       apply (fastforce simp: throwError_bind invocationCatch_def split: list.split)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (clarsimp simp: list_case_If2)
     apply csymbr
     apply csymbr
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
       apply (rule ccorres_add_return)
       apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
         apply (rule ccorres_add_return)
         apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
           apply csymbr
           apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
           apply (rule ccorres_move_c_guard_cte)
           apply (rule_tac r'="\<lambda>rv rv'. ((cap_get_tag rv' = scast cap_pml4_cap)
                                            = (isArchObjectCap rv \<and> isPML4Cap (capCap rv)))
                                        \<and> (ccap_relation rv rv')"
                      and xf'=vspaceCap_' in ccorres_split_nothrow[where F=UNIV])
               apply (simp add: getSlotCap_def)
               apply (rule ccorres_symb_exec_l[OF _ getCTE_inv getCTE_sp[where P=\<top>] empty_fail_getCTE])
               apply (rule ccorres_from_vcg[where P'=UNIV])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: return_def cte_wp_at_ctes_of)
               apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
               apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
               apply (clarsimp simp: typ_heap_simps' mask_def split_def
                                     cap_get_tag_isCap_ArchObject2
                                     word_sle_def word_sless_def
                              dest!: ccte_relation_ccap_relation)
              apply (simp add: sless_positive)
              apply ceqv
             apply (rule ccorres_assert2)
             apply csymbr+
             apply (clarsimp simp add: split_def cap_case_PML4Cap2)
             apply (simp add: word_less_nat_alt length_ineq_not_Nil)
             apply (rule ccorres_Cond_rhs_Seq)
              apply (rule ccorres_equals_throwError)
               apply (simp add: unfold_checkMapping_return)
               apply (fastforce simp: invocationCatch_def throwError_bind hd_conv_nth from_bool_0
                                cong: conj_cong)
              apply ccorres_rewrite
              apply (rule syscall_error_throwError_ccorres_n)
              apply (clarsimp simp: syscall_error_to_H_cases)
             apply (clarsimp simp: hd_conv_nth)
             apply csymbr
             apply csymbr
             apply csymbr
             apply csymbr
             apply (clarsimp simp: whenE_def)
             apply (drule_tac t="Some y" in sym)
             (* There are two paths through the cap mapping eligibility check (target asid/address
                for mapped cap, target address for not mapped case) which do not throw;
                pull the non-throwing cases together *)
             apply (rule_tac P="does_not_throw args extraCaps maptype pg_sz mapdata" in ccorres_cases[rotated])
              (* Always throws case *)
              apply (clarsimp simp: if_to_top_of_bind if_to_top_of_bindE case_option_If2 hd_conv_nth
                              cong: conj_cong)
              apply (rule ccorres_split_throws[rotated])
               apply vcg
              apply (clarsimp simp: does_not_throw_def)
              (* is the frame cap mapped? *)
              apply (rule ccorres_Cond_rhs)
               (* frame cap is mapped: remap case *)
               apply (prop_tac "mapdata \<noteq> None", simp add: asidInvalid_def ccap_relation_mapped_asid_0)
               apply clarsimp
               apply (rule ccorres_rhs_assoc)+
               apply csymbr
               apply clarsimp
               apply (frule_tac c'=rv' in ccap_relation_capPML4MappedASID_liftE[OF _ _ sym], assumption+)
               apply (simp add: get_capMappedASID_CL_def cap_pml4_cap_lift)
               apply (prop_tac "args \<noteq> []", blast)
               apply (simp add: whenE_bindE_throwError_to_if if_to_top_of_bind)
               (* throw on mismatched ASID *)
               apply (rule ccorres_Cond_rhs_Seq)
                apply (frule ccap_relation_PageCap_generics)
                apply (drule sym[where s="Some _"])
                apply clarsimp
                apply (rule ccorres_equals_throwError[OF throwError_invocationCatch])
                apply (rule syscall_error_throwError_ccorres_n)
                apply (simp add: syscall_error_to_H_cases)
               (* throw on mismatched mapping type *)
               apply simp
               apply csymbr
               apply (frule ccap_relation_PageCap_MapType)
               apply (frule ccap_relation_PageCap_generics)
               apply ccorres_rewrite
               apply (drule sym[where s="Some _"])
               apply clarsimp
               apply (rule ccorres_Cond_rhs_Seq)
                apply (clarsimp simp: maptype_from_H_def throwError_bind invocationCatch_def
                               split: vmmap_type.split_asm)
                apply (rule syscall_error_throwError_ccorres_n)
                apply (clarsimp simp: syscall_error_to_H_cases)
               (* throw on mismatched vaddr *)
               apply simp
               apply csymbr
               apply (frule ccap_relation_PageCap_generics)
               apply (clarsimp simp: hd_conv_nth length_ineq_not_Nil)
               apply ccorres_rewrite
               apply (clarsimp simp: maptype_from_H_def throwError_bind invocationCatch_def
                              split: vmmap_type.split_asm)
                apply (clarsimp simp: X86_MappingNone_def X86_MappingVSpace_def)
               apply ccorres_rewrite
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              (* frame cap not mapped, check mapping *)
              (* disallow mappings above pptrBase *)
              apply clarsimp
              apply (prop_tac "mapdata = None")
               apply (simp add: asidInvalid_def ccap_relation_mapped_asid_0)
              apply clarsimp
              apply (rule ccorres_rhs_assoc)+
              apply csymbr
              apply (simp add: word_less_nat_alt)
              apply (rule ccorres_equals_throwError[OF throwError_invocationCatch])
              apply (frule ccap_relation_PageCap_generics)
              apply clarsimp
              apply ccorres_rewrite
              apply csymbr
              apply (simp add: user_vtop_def X64.pptrUserTop_def hd_conv_nth length_ineq_not_Nil)
              apply ccorres_rewrite
              apply (rule syscall_error_throwError_ccorres_n)
              apply (simp add: syscall_error_to_H_cases)
             (* Doesn't throw case *)
             apply (drule_tac s="Some y" in sym,
                    clarsimp simp: does_not_throw_def case_option_If2 cong: if_cong)
             apply (rule ccorres_add_return)
             (* split off map/remap check, show it's equivalent to SKIP *)
             apply (rule_tac P=\<top> and P'=UNIV in ccorres_split_nothrow)
                 apply (rule ccorres_guard_imp)
                   apply (frule ccap_relation_PageCap_generics)
                   apply (rule ccorres_Cond_rhs)
                    apply (clarsimp simp: asidInvalid_def)
                    apply (rule ccorres_rhs_assoc)+
                    apply csymbr
                    apply clarsimp
                    apply (prop_tac "capFMappedASID_CL (cap_frame_cap_lift cap)
                                     = get_capMappedASID_CL (cap_lift rv')")
                     apply (drule (2) ccap_relation_capPML4MappedASID_liftE)
                     apply (clarsimp simp: cap_lift_pml4_cap get_capMappedASID_CL_def
                                           cap_pml4_cap_lift_def)
                    apply (clarsimp, ccorres_rewrite)
                    apply (csymbr, clarsimp simp: hd_conv_nth length_ineq_not_Nil, ccorres_rewrite)
                    apply (frule ccap_relation_PageCap_MapType)
                    apply (clarsimp simp: maptype_from_H_def)
                    apply ccorres_rewrite
                    apply csymbr
                    apply (clarsimp simp: hd_conv_nth length_ineq_not_Nil)
                    apply ccorres_rewrite
                    apply (rule ccorres_return_Skip)
                   apply (rule ccorres_rhs_assoc)+
                   apply (csymbr, clarsimp, ccorres_rewrite)
                   apply csymbr
                   apply (simp add: asidInvalid_def)
                   apply (simp add: word_less_nat_alt user_vtop_def X64.pptrUserTop_def hd_conv_nth
                                    length_ineq_not_Nil)
                   apply (ccorres_rewrite)
                   apply (rule ccorres_return_Skip)
                  apply clarsimp
                 apply (clarsimp simp: asidInvalid_def)
                 apply (subgoal_tac "cap_get_tag cap = SCAST(32 signed \<rightarrow> 64) cap_frame_cap")
                  apply (frule ccap_relation_PageCap_generics)
                  apply clarsimp
                 apply (erule ccap_relation_frame_tags)
                apply ceqv
               apply csymbr
               apply (simp add: createSafeMappingEntries_fold lookupError_injection
                                invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                                injection_handler_returnOk injection_handler_If
                                injection_handler_throwError bindE_assoc
                           cong: if_cong)
               apply (rule_tac t=y and s="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                        in ssubst,
                      fastforce)
               apply (ctac add: ccorres_injection_handler_csum1[OF ccorres_injection_handler_csum1,
                                                                OF findVSpaceForASID_ccorres])
                  apply (simp add: Collect_False if_to_top_of_bindE)
                  apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                     apply vcg
                    apply (clarsimp simp: cap_lift_pml4_cap cap_to_H_def get_capPtr_CL_def
                                          cap_pml4_cap_lift_def
                                   elim!: ccap_relationE split: if_split)
                   apply (rule syscall_error_throwError_ccorres_n)
                   apply (simp add: syscall_error_to_H_cases)
                  apply csymbr
                  apply (rule ccorres_symb_exec_r)
                    apply csymbr
                    apply (simp add: bindE_assoc checkVPAlignment_def unlessE_def
                                     injection_handler_If if_to_top_of_bindE)
                    apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
                       apply vcg
                      apply (clarsimp simp add: from_bool_0 vmsz_aligned_def is_aligned_mask)
                      apply (drule ccap_relation_PageCap_Size)
                      apply (clarsimp simp: framesize_from_to_H user_vtop_def X64.pptrUserTop_def)
                     apply (simp add: injection_handler_throwError throwError_bind
                                      invocationCatch_def)
                     apply (rule syscall_error_throwError_ccorres_n)
                     apply (simp add: syscall_error_to_H_cases)
                    apply csymbr
                    apply csymbr
                    apply csymbr
                    apply csymbr
                    apply csymbr
                    apply (simp add: injection_handler_returnOk bindE_assoc)
                    apply (rule ccorres_Cond_rhs)
                     apply (rule ccorres_rhs_assoc)+
                     apply csymbr
                     apply (ctac add: ccorres_injection_handler_csum1[
                                        OF createSafeMappingEntries_PTE_ccorres])
                        apply (simp add: performX64MMUInvocations bindE_assoc)
                        apply ccorres_rewrite
                        apply (rule_tac P="\<lambda>s. thread = ksCurThread s" in ccorres_cross_over_guard)
                        apply (ctac add: setThreadState_ccorres)
                          apply (ctac(no_vcg) add: performPageInvocationMapPTE_ccorres)
                            apply (rule ccorres_gen_asm)
                            apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                            apply (rule ccorres_alternative2)
                            apply (rule ccorres_return_CE, simp+)[1]
                           apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                          apply (wpsimp simp: performPageInvocation_def)
                         apply (wp sts_invs_minor')
                        apply simp
                        apply (vcg exspec=setThreadState_modifies)
                       apply (simp, ccorres_rewrite)
                       apply (rule ccorres_return_C_errorE, simp+)[1]
                      apply (simp add: createSafeMappingEntries_def)
                      apply (wp injection_wp[OF refl] createMappingEntries_wf)
                     apply (simp add: all_ex_eq_helper)
                     apply (rule_tac Q' = "{s. ccap_relation (ArchObjectCap
                                                                (PageCap word rghts VMVSpaceMap pg_sz d
                                                                         (Some (y, a)))) cap}"
                                 and A' = "{}" in conseqPost)
                       apply (vcg exspec=createSafeMappingEntries_PTE_modifies)
                      apply (clarsimp simp: rf_sr_ksCurThread isCap_simps cap_pml4_cap_lift
                                            get_capPtr_CL_def ccap_relation_PML4Cap_BasePtr)
                     apply clarsimp
                    apply (rule ccorres_Cond_rhs)
                     apply (rule ccorres_rhs_assoc)+
                     apply csymbr
                     apply (ctac add: ccorres_injection_handler_csum1
                                        [OF createSafeMappingEntries_PDE_ccorres])
                        apply (simp add: performX64MMUInvocations bindE_assoc)
                        apply ccorres_rewrite
                        apply (rule_tac P="\<lambda>s. thread = ksCurThread s" in ccorres_cross_over_guard)
                        apply (ctac add: setThreadState_ccorres)
                          apply (ctac(no_vcg) add: performPageInvocationMapPDE_ccorres)
                            apply (rule ccorres_gen_asm)
                            apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                            apply (rule ccorres_alternative2)
                            apply (rule ccorres_return_CE, simp+)[1]
                           apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                          apply (wpsimp simp: performPageInvocation_def)
                         apply (wp sts_invs_minor')
                        apply simp
                        apply (vcg exspec=setThreadState_modifies)
                       apply (simp add: Collect_const)
                       apply (rule ccorres_split_throws)
                        apply (rule ccorres_return_C_errorE, simp+)[1]
                       apply vcg
                      apply (simp add: createSafeMappingEntries_def)
                      apply (wp injection_wp[OF refl] createMappingEntries_wf)
                     apply (simp add: all_ex_eq_helper)
                     apply (rule_tac Q' = "{s. ccap_relation (ArchObjectCap
                                                                 (PageCap word rghts VMVSpaceMap pg_sz d
                                                                               (Some (y, a)))) cap}"
                                                 and A' = "{}" in conseqPost)
                       apply (vcg exspec=createSafeMappingEntries_PDE_modifies)
                      apply (clarsimp simp: rf_sr_ksCurThread isCap_simps cap_pml4_cap_lift
                                            get_capPtr_CL_def ccap_relation_PML4Cap_BasePtr)
                     apply clarsimp
                    apply (rule ccorres_add_returnOk)
                    apply (ctac add: decodeX86ModeMapPage_ccorres)
                       apply (rule ccorres_return_CE, simp+)[1]
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                     apply wpsimp
                    apply clarsimp
                    apply (vcg exspec=decodeX86ModeMapPage_modifies)
                   apply clarsimp
                   apply vcg
                  apply (rule conseqPre, vcg, clarsimp)
                 apply simp
                 apply (rule_tac P'="{s. find_ret = errstate s}"
                                       in ccorres_from_vcg_split_throws[where P=\<top>])
                  apply vcg
                 apply (rule conseqPre, vcg)
                 apply (clarsimp simp: fst_throwError_returnOk exception_defs
                                       syscall_error_rel_def syscall_error_to_H_cases)
                 apply (erule lookup_failure_rel_fault_lift[rotated])
                 apply (simp add: exception_defs)
                apply (simp add: isCap_simps)
                apply (wp injection_wp[OF refl]
                       | wp (once) hoare_drop_imps)+
               apply (simp add: all_ex_eq_helper)
               apply (rule_tac t=y and s="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                        in ssubst, fastforce)
               apply (vcg exspec=findVSpaceForASID_modifies)
              apply (rule_tac t=y and s="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                                    in ssubst, fastforce)
              apply wp
             apply (rule_tac t=y and s="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                          in ssubst, fastforce)
             apply vcg
            apply clarsimp
            apply (wp getSlotCap_wp)
           apply clarsimp
           apply (vcg exspec=getSyscallArg_modifies)
          apply clarsimp
          apply wp
         apply clarsimp
         apply (vcg exspec=getSyscallArg_modifies)
        apply clarsimp
        apply wp
       apply clarsimp
       apply (vcg exspec=getSyscallArg_modifies)
      apply wp
      apply (clarsimp, assumption)
     apply vcg
    (* rewrite to args *)
    apply (rule_tac t="a # b # c # da" and s=args in subst, simp)
    apply (rule_tac t=a and s="hd args" in ssubst, simp)
    apply (rule_tac t=b and s="hd (tl args)" in ssubst, simp)
    apply (rule_tac t=c and s="hd (tl (tl args))" in ssubst, simp)
    apply (rule_tac t=da and s="tl (tl (tl args))" in ssubst, simp)
    apply assumption
   apply (rule_tac t="a # b # c # da" and s=args in subst, simp)
   apply (rule_tac t=a and s="hd args" in ssubst, simp)
   apply (rule_tac t=b and s="hd (tl args)" in ssubst, simp)
   apply (rule_tac t=c and s="hd (tl (tl args))" in ssubst, simp)
   apply (rule_tac t=da and s="tl (tl (tl args))" in ssubst, simp)
   apply assumption
  apply (rename_tac word rghts maptype pg_sz mapdata call' buffer' cap excaps
                    cte length___unsigned_long invLabel s s')
  apply (rule conjI)
   apply clarsimp
   apply (frule cte_wp_at_eq_gsMaxObjectSize, clarsimp)
   apply (clarsimp simp: cte_wp_at_ctes_of is_aligned_mask[symmetric] vmsz_aligned_def
                         vmsz_aligned_addrFromPPtr)
   apply (frule ctes_of_valid', clarsimp+)
   apply (drule_tac t="cteCap cte" in sym, simp)
   apply (frule valid_cap'_PageCap_kernel_mappings[OF invs_pspace_in_kernel_mappings', where cap=cp],
          fastforce simp: isCap_simps, fastforce)
   apply (subgoal_tac "extraCaps \<noteq> [] \<longrightarrow> (s \<turnstile>' fst (extraCaps ! 0))")
    apply (prop_tac "is_aligned word (pageBitsForSize pg_sz)", simp add: valid_cap'_def capAligned_def)

  (* Haskell side *)
  subgoal
    by (timeit \<open>(
             (clarsimp simp: ct_in_state'_def vmsz_aligned_def isCap_simps
                             valid_cap'_def page_map_l4_at'_def tcb_at_invs'
                             sysargs_rel_to_n linorder_not_less framesize_from_H_eqs
                             excaps_map_def valid_tcb_state'_def split_def is_aligned_addrFromPPtr
                             is_aligned_addrFromPPtr_pageBitsForSize[where sz=X64LargePage, simplified]
                             is_aligned_addrFromPPtr_pageBitsForSize[where sz=X64HugePage, simplified]
                   simp del: less_1_simp
           | rule conjI | erule pred_tcb'_weakenE disjE
           | (erule order_trans[where x=7, rotated], fastforce simp: bit_simps)
           | ((frule ccap_relation_PageCap_MappedASID)?, drule ccap_relation_PageCap_Size)
           | drule interpret_excaps_eq st_tcb_at_idle_thread'
           | solves \<open>clarsimp simp: framesize_from_H_def asid_wf_def split: vmpage_size.splits\<close>
       )+)[1]\<close>) (* 30s *)
   apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def slotcap_in_mem_def
                         linorder_not_le)
   apply (erule ctes_of_valid', clarsimp)


  (* C side *)
  apply (clarsimp simp: rf_sr_ksCurThread mask_eq_iff_w2p
                        word_size word_less_nat_alt from_bool_0 excaps_map_def cte_wp_at_ctes_of
                        n_msgRegisters_def)
  apply (frule(1) ctes_of_valid')
  apply (drule_tac t="cteCap ctea" in sym)
  apply (clarsimp simp: valid_cap'_def capAligned_def word_sless_def word_sle_def)
  apply (frule ccap_relation_PageCap_generics)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply clarsimp
  apply (frule cap_get_tag_PageCap_frame)
  supply unsigned_numeral[simp del]
  apply (clarsimp simp: word_less_nat_alt vm_attribs_relation_def attribsFromWord_def
                        framesize_from_H_eqs of_bool_nth[simplified of_bool_from_bool]
                        vm_page_size_defs neq_Nil_conv excaps_in_mem_def hd_conv_nth
                        numeral_2_eq_2 does_not_throw_def asidInvalid_def)
  apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (frule(1) slotcap_in_mem_PML4)
  apply (clarsimp simp: mask_def[where n=4] typ_heap_simps' isCap_simps)
  apply (frule(1) slotcap_in_mem_valid)
  apply (rename_tac pml4_cap b ys pml4_slot)
  apply (frule ccap_relation_PageCap_MapType)
  apply (erule_tac c="ArchObjectCap (PML4Cap a b)" for a b in ccap_relationE)
  apply (clarsimp simp: cap_lift_pml4_cap cap_pml4_cap_lift_def framesize_from_to_H
                           cap_to_H_def[split_simps cap_CL.split]
                           valid_cap'_def user_vtop_def X64.pptrUserTop_def)
  apply (prop_tac "(cap_C.words_C (cte_C.cap_C pml4_slot).[0] >> 58) && 1 \<noteq> 0")
   apply (fastforce split: if_splits)
  apply (clarsimp simp: bit_simps to_bool_def cap_frame_cap_lift typ_heap_simps' shiftl_t2n[where n=3]
                 elim!: ccap_relationE)
  apply (clarsimp simp: neq_Nil_conv[where xs=extraCaps] excaps_in_mem_def slotcap_in_mem_def
                 dest!: sym[where s="ArchObjectCap cp" for cp])
  apply (clarsimp simp: valid_cap_simps' rf_sr_ksCurThread get_capMappedASID_CL_def cap_tag_defs
                        maptype_from_H_def)
  apply (case_tac mapdata; clarsimp; prop_tac "canonical_address (args ! 0)")
     apply (rule le_user_vtop_canonical_address)
     apply (frule aligned_sum_le_user_vtop[simplified word_le_nat_alt])
     apply (simp add: word_le_nat_alt not_less user_vtop_def X64.pptrUserTop_def)
    prefer 2
    apply (frule(1) cap_to_H_PageCap_tag)
    apply (frule canonical_address_cap_frame_cap)
    apply metis
   by ((intro conjI impI,
          (rule_tac cp=cp in ccap_relation_PageCap_MappedAddress_update
           ; force simp: vm_page_map_type_defs mask_def),
          (rule_tac cp=cp in ccap_relation_PageCap_MappedAddress_update
           ; force simp: vm_page_map_type_defs mask_def),
          meson invocation_eq_use_types,
          (rule framesize_to_from_H[symmetric], fastforce simp: c_valid_cap_def cl_valid_cap_def),
          (rule_tac cp=cp in ccap_relation_PageCap_MappedAddress_update
           ; force simp: vm_page_map_type_defs mask_def))+)[2] (* 70s *)


lemma asidHighBits_handy_convs:
  "sint Kernel_C.asidHighBits = 3"
  "Kernel_C.asidHighBits \<noteq> 0x20"
  "unat Kernel_C.asidHighBits = asid_high_bits"
  by (simp add: Kernel_C.asidHighBits_def
                asid_high_bits_def)+

lemma sts_Restart_ct_active [wp]:
  "\<lbrace>\<lambda>s. thread = ksCurThread s\<rbrace> setThreadState Restart thread \<lbrace>\<lambda>_. ct_active'\<rbrace>"
  apply (clarsimp simp: ct_in_state'_def)
  apply (rule hoare_lift_Pf2 [where f=ksCurThread])
   apply (wp sts_st_tcb')
   apply (simp split: if_split)
  apply wp
  done

lemma maskCapRights_eq_Untyped [simp]:
  "(maskCapRights R cap = UntypedCap d p sz idx) = (cap = UntypedCap d p sz idx)"
  apply (cases cap)
  apply (auto simp: Let_def isCap_simps maskCapRights_def)
  apply (simp add: X64_H.maskCapRights_def isPageCap_def Let_def split: arch_capability.splits)
  done


lemma le_mask_asid_bits_helper:
  "x \<le> 2 ^ asid_high_bits - 1 \<Longrightarrow> (x::machine_word) << asid_low_bits \<le> mask asid_bits"
  apply (simp add: mask_def)
  apply (drule le2p_bits_unset_64)
   apply (simp add: asid_high_bits_def word_bits_def)
  apply (subst upper_bits_unset_is_l2p_64 [symmetric])
   apply (simp add: asid_bits_def word_bits_def)
  apply (clarsimp simp: asid_bits_def asid_low_bits_def asid_high_bits_def nth_shiftl)
  done


lemma injection_handler_liftE:
  "injection_handler a (liftE f) = liftE f"
  by (simp add:injection_handler_def)


lemma liftE_case_sum:
  "liftE f >>= case_sum (throwError \<circ> Inr) g = f >>= g"
  by (simp add:liftE_def)

lemma framesize_from_H_mask2:
  "framesize_from_H a && mask 2 = framesize_from_H a"
  apply (rule less_mask_eq)
  apply (simp add:framesize_from_H_def
    split: vmpage_size.splits)
    apply (simp add:Kernel_C.X86_SmallPage_def
      Kernel_C.X86_LargePage_def
      Kernel_C.X64_HugePage_def)+
  done

lemma injection_handler_stateAssert_relocate:
  "injection_handler Inl (stateAssert ass xs >>= f) >>=E g
    = do v \<leftarrow> stateAssert ass xs; injection_handler Inl (f ()) >>=E g od"
  by (simp add: injection_handler_def handleE'_def bind_bindE_assoc bind_assoc)

lemma makeUserPDPTEPageDirectory_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  \<lbrace>s. vmsz_aligned (\<acute>paddr) X64SmallPage\<rbrace>
  Call makeUserPDPTEPageDirectory_'proc
  \<lbrace> pdpte_lift \<acute>ret__struct_pdpte_C = Some (Pdpte_pdpte_pd \<lparr>
       pdpte_pdpte_pd_CL.xd_CL = 0,
       pdpte_pdpte_pd_CL.pd_base_address_CL = \<^bsup>s\<^esup>paddr && (mask 39 << 12),
       pdpte_pdpte_pd_CL.accessed_CL = 0,
       pdpte_pdpte_pd_CL.cache_disabled_CL = x86PCDBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pdpte_pdpte_pd_CL.write_through_CL = x86PWTBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pdpte_pdpte_pd_CL.super_user_CL = 1,
       pdpte_pdpte_pd_CL.read_write_CL = 1,
       pdpte_pdpte_pd_CL.present_CL = 1\<rparr>) \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: pdpte_pdpte_pd_lift
                        superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def mask_def)
  done

lemma ccap_relation_page_directory_mapped_asid:
  "ccap_relation (ArchObjectCap (PageDirectoryCap p (Some (asid, vspace)))) cap
    \<Longrightarrow> asid = capPDMappedASID_CL (cap_page_directory_cap_lift cap)"
  by (frule cap_get_tag_isCap_unfolded_H_cap)
     (clarsimp simp: cap_page_directory_cap_lift ccap_relation_def cap_to_H_def split: if_splits)

lemma performPageDirectoryInvocationMap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (cte_at' ctSlot)
       (UNIV \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace> \<inter> \<lbrace>cpdpte_relation pde \<acute>pdpte\<rbrace> \<inter> \<lbrace>\<acute>pdptSlot = Ptr pdSlot\<rbrace>
             \<inter> \<lbrace>\<acute>vspace = Ptr vspace\<rbrace>)
       hs
       (liftE (performPageDirectoryInvocation (PageDirectoryMap cap ctSlot pde pdSlot vspace)))
       (Call performX64PageDirectoryInvocationMap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: cap_' ctSlot_' pdpte_' pdptSlot_' vspace_')
   apply (ctac (no_vcg))
     apply (rule ccorres_split_nothrow)
         apply simp
         apply (erule storePDPTE_Basic_ccorres)
        apply ceqv
       apply (rule ccorres_cases[where P="\<exists>p a v. cap = ArchObjectCap (PageDirectoryCap p (Some (a, v)))" and H=\<top> and H'=UNIV];
              clarsimp split: capability.splits arch_capability.splits simp: ccorres_fail)
       apply csymbr
       apply csymbr
       apply (rule ccorres_add_return2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (frule ccap_relation_page_directory_mapped_asid)
           apply simp
           apply (rule ccorres_call[where xf'=xfdc, OF invalidatePageStructureCacheASID_ccorres]; simp)
          apply ceqv
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply wp
       apply (simp add: guard_is_UNIV_def)
      apply (clarsimp, wp)
     apply vcg
    apply wp
   apply (clarsimp simp: cap_get_tag_isCap_unfolded_H_cap)
  apply simp
  done

lemma decodeX64PageDirectoryInvocation_ccorres:
  "\<lbrakk>interpret_excaps extraCaps' = excaps_map extraCaps; isPageDirectoryCap cp\<rbrakk> \<Longrightarrow>
   ccorres
       (intr_and_se_rel \<currency> dc)
       (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and valid_cap' (ArchObjectCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       hs
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX64PageDirectoryInvocation_'proc)"
   (is "_ \<Longrightarrow> _ \<Longrightarrow> ccorres _ _ ?pre _ _ _ _")
  supply Collect_const[simp del] if_cong[cong]
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_' current_extra_caps_' cap_' buffer_'
                simp: decodeX64MMUInvocation_def invocation_eq_use_types decodeX64PageDirectoryInvocation_def)
   apply (simp add: Let_def isCap_simps if_to_top_of_bind
               cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_split_throws)
     apply (simp add: liftE_bindE bind_assoc)
     apply (rule ccorres_symb_exec_l[OF _ getCTE_inv _ empty_fail_getCTE])
      apply (rule ccorres_rhs_assoc)+
      apply (ctac add: isFinalCapability_ccorres)
        apply (simp add: unlessE_def if_to_top_of_bind if_to_top_of_bindE ccorres_seq_cond_raise)
        apply (rule ccorres_cond2'[where R=\<top>])
          apply (clarsimp simp: from_bool_0)
         apply (simp add: throwError_bind invocationCatch_def)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (simp add: returnOk_bind bindE_assoc performX64MMUInvocations)
        apply (ctac add: setThreadState_ccorres)
          apply (ctac add: performPageDirectoryInvocationUnmap_ccorres)
             apply (rule ccorres_alternative2)
             apply (rule ccorres_return_CE, simp+)[1]
            apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
           apply wp
          apply simp
          apply (vcg exspec=performX64PageDirectoryInvocationUnmap_modifies)
         apply (wp sts_invs_minor')
        apply simp
        apply (vcg exspec=setThreadState_modifies)
       apply (wp hoare_drop_imps isFinalCapability_inv)
      apply simp
      apply (vcg exspec=isFinalCapability_modifies)
     apply (wp getCTE_wp)
    apply (vcg exspec=performX64PageDirectoryInvocationUnmap_modifies exspec=isFinalCapability_modifies
               exspec=setThreadState_modifies)
   apply simp
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (simp split: invocation_label.split arch_invocation_label.split
                 add: throwError_bind invocationCatch_def)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply simp
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: word_less_nat_alt throwError_bind invocationCatch_def)
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_equals_throwError)
     apply (simp add: throwError_bind split: list.split)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply csymbr
   apply (simp add: interpret_excaps_test_null excaps_map_def)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: list_case_If2 split_def
                    word_less_nat_alt length_ineq_not_Nil Let_def
                    whenE_bindE_throwError_to_if if_to_top_of_bind)
   apply csymbr
   apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
      apply vcg
     apply clarsimp
     apply (frule cap_get_tag_isCap_unfolded_H_cap)
     apply (clarsimp simp: cap_lift_page_directory_cap cap_page_directory_cap_lift_def cap_to_H_def
                     elim!: ccap_relationE split: if_split)
     apply (simp add: to_bool_def)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: cap_case_PML4Cap2 split_def)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply csymbr
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply csymbr
       apply (rule ccorres_add_return)
       apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_pml4_cap)
                                          = (isArchObjectCap rv \<and> isPML4Cap (capCap rv)))
                                     \<and> (ccap_relation rv rv')) (fst (extraCaps ! 0))" and
                       xf'=vspaceCap_'
                       in ccorres_split_nothrow)
           apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
           apply (drule(1) slotcap_in_mem_PML4)
           apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
           apply (clarsimp simp: typ_heap_simps' mask_def)
          apply (rename_tac rv' t t')
          apply (simp add: word_sless_def word_sle_def)
          apply ceqv
         apply csymbr
         apply clarsimp
         apply (rule ccorres_Cond_rhs_Seq)
          apply ccorres_rewrite
          apply clarsimp
          apply (rule_tac P="isArchObjectCap (fst (extraCaps ! 0)) \<and>
                             isPML4Cap (capCap (fst (extraCaps ! 0)))"
                          in ccorres_cases)
           apply (clarsimp simp: hd_conv_nth throwError_bind invocationCatch_def from_bool_0 cong: if_cong)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply (clarsimp simp: hd_conv_nth throwError_bind invocationCatch_def from_bool_0 cong: if_cong)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: hd_conv_nth)
         apply csymbr
         apply csymbr
         apply csymbr
         apply (simp add: case_option_If2 if_to_top_of_bind if_to_top_of_bindE hd_conv_nth)
         apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
            apply vcg
           apply (fastforce simp: user_vtop_def X64.pptrUserTop_def bit_simps
                                  word_le_nat_alt mask_def hd_conv_nth length_ineq_not_Nil)
          apply (simp add: throwError_bind invocationCatch_def)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: lookupError_injection invocationCatch_use_injection_handler
                          injection_bindE[OF refl refl] injection_handler_If
                          injection_handler_throwError injection_liftE[OF refl]
                          injection_handler_returnOk bindE_assoc cap_pml4_cap_lift get_capMappedASID_CL_def
                     cong: if_cong)
         apply csymbr
         apply (ctac add: ccorres_injection_handler_csum1 [OF ccorres_injection_handler_csum1,
                                                           OF findVSpaceForASID_ccorres])
            apply (simp add: Collect_False if_to_top_of_bindE)
            apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
               apply vcg
              apply (clarsimp simp: isCap_simps get_capPtr_CL_def)
              apply (frule cap_get_tag_isCap_unfolded_H_cap)
              apply (erule_tac v="rv'" in ccap_relationE, clarsimp simp: cap_to_H_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (simp add: bindE_assoc,
                   simp add: liftE_bindE)
            apply (ctac add: ccorres_injection_handler_csum1 [OF ccorres_injection_handler_csum1,
                                                              OF lookupPDPTSlot_ccorres])
               apply (rule ccorres_pre_getObject_pdpte)
               apply (rule ccorres_cond_false_seq)
               apply (rename_tac pdpt_slot pdpt_slot_C pdpte)
               apply ccorres_rewrite
               apply clarsimp
               apply (rename_tac pml4_mapped_asid)
               apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
               apply (rule_tac xf'=ret__int_' and R="ko_at' pdpte pdpt_slot" and R'=UNIV and
                               val="from_bool (pdpte \<noteq> InvalidPDPTE)"
                               in ccorres_symb_exec_r_known_rv)
                  apply vcg
                  apply (clarsimp simp: from_bool_0)
                  apply (erule cmap_relationE1[OF rf_sr_cpdpte_relation], erule ko_at_projectKO_opt)
                  apply (clarsimp simp: typ_heap_simps from_bool_eq_if)
                  apply (auto simp: cpdpte_relation_def Let_def pdpte_pdpte_pd_lift_def
                                    pdpte_pdpte_pd_lift pdpte_tag_defs pdpte_pdpte_1g_lift_def
                                    pdpte_lift_def case_bool_If
                              split: pdpte.split_asm if_splits)[1]
                 apply ceqv
                apply clarsimp
                apply (rule ccorres_Cond_rhs_Seq)
                 apply (clarsimp simp: throwError_bind invocationCatch_def injection_handler_throwError)
                 apply ccorres_rewrite
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (clarsimp simp: syscall_error_to_H_cases)
                apply (clarsimp simp: injection_handler_returnOk)
                apply (simp add: injection_handler_returnOk performX64MMUInvocations bindE_assoc)
                apply csymbr
                apply csymbr
                apply csymbr
                apply csymbr
                apply csymbr
                apply csymbr
                apply (ctac add: setThreadState_ccorres)
                  apply (ctac add: performPageDirectoryInvocationMap_ccorres)
                     apply (rule ccorres_alternative2)
                     apply (rule ccorres_return_CE, simp+)[1]
                    apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                   apply wp+
                  apply simp
                  apply (vcg exspec=performX64PageDirectoryInvocationMap_modifies)
                 apply simp
                 apply wp
                apply simp
                apply (vcg exspec=setThreadState_modifies)
               apply (simp add: get_capPtr_CL_def)
               apply (rule_tac s=pml4_mapped_asid and
                               t="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                               in subst, fastforce)
               apply vcg
              apply (rename_tac lookup_pd_ret)
              apply clarsimp
              apply (rule_tac P'="{s. errstate s = lookup_pd_ret}" in ccorres_from_vcg_split_throws[where P=\<top>])
               apply vcg
              apply (rule conseqPre, vcg)
              apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                    syscall_error_to_H_cases exception_defs)
              apply (erule lookup_failure_rel_fault_lift[rotated])
              apply (clarsimp simp: exception_defs)
             apply clarsimp
             apply (wp injection_wp[OF refl] hoare_drop_imps)
            apply (clarsimp simp: get_capPtr_CL_def)
            apply (rename_tac pml4_mapped_asid)
            apply (rule_tac s=pml4_mapped_asid and
                            t="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                            in subst, fastforce)
            apply (vcg exspec=lookupPDPTSlot_modifies)
           apply clarsimp
           apply (rule_tac P'="{s. errstate s = find_ret}" in ccorres_from_vcg_split_throws[where P=\<top>])
            apply vcg
           apply simp
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                 syscall_error_to_H_cases exception_defs)
           apply (erule lookup_failure_rel_fault_lift[rotated])
           apply (simp add: exception_defs)
          apply simp
          apply (wp injection_wp[OF refl] hoare_drop_imps)
         apply simp
         apply (vcg exspec=findVSpaceForASID_modifies)
        apply simp
        apply (rule_tac Q'="\<lambda>a b. invs' b \<and> valid_cap' (fst (extraCaps ! 0)) b \<and> tcb_at' thread b \<and>
                                 sch_act_wf (ksSchedulerAction b) b \<and> cte_wp_at' (\<lambda>_. True) slot b"
                        in hoare_strengthen_post)
         apply wp
        apply (fastforce simp: isCap_simps invs_valid_objs' valid_cap'_def valid_tcb_state'_def
                               invs_arch_state' invs_no_0_obj')
       apply vcg
      apply wp
     apply simp
     apply (vcg exspec=getSyscallArg_modifies)
    apply simp
    apply wp
   apply simp
  apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: cte_wp_at_ctes_of excaps_map_def
                        word_sle_def word_sless_def bit_simps)
  apply (rule conjI)
   apply (auto simp: ct_in_state'_def isCap_simps valid_tcb_state'_def
              elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
  apply (rule conjI)
   apply (clarsimp simp: isCap_simps)
   apply (subgoal_tac "s \<turnstile>' fst (extraCaps ! 0)")
    apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt
                          linorder_not_less)
    apply (clarsimp | drule length_le_helper)+
    apply (clarsimp simp: valid_cap'_def neq_Nil_conv
                          mask_add_aligned pd_pointer_table_at'_def
                          word_le_nat_alt[symmetric] bit_simps)
    apply (auto simp: ct_in_state'_def pred_tcb_at' mask_def valid_tcb_state'_def
               elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
   apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def
                         slotcap_in_mem_def)
   apply (auto dest: ctes_of_valid')[1]
  apply (rule conjI)
   apply (clarsimp simp: rf_sr_ksCurThread
                         mask_eq_iff_w2p word_size
                         ct_in_state'_def st_tcb_at'_def
                         word_sle_def word_sless_def
                         typ_heap_simps' bit_simps)
  apply (drule_tac t="cteCap ctea" in sym, simp)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject isCap_simps
                        word_sle_def word_sless_def
                        word_less_nat_alt)
  apply (frule length_ineq_not_Nil)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (clarsimp simp: cap_lift_pdpt_cap hd_conv_nth
                        cap_lift_page_directory_cap bit_simps
                        cap_pdpt_cap_lift_def
                        typ_heap_simps' shiftl_t2n[where n=3] field_simps
                 elim!: ccap_relationE)
  apply (clarsimp simp: neq_Nil_conv[where xs=extraCaps]
                        excaps_in_mem_def slotcap_in_mem_def
                 dest!: sym[where s="ArchObjectCap cp" for cp])
  apply (cut_tac p="snd (hd extraCaps)" in ctes_of_valid', simp, clarsimp)
  apply (rule conjI[rotated], clarsimp simp: cap_tag_defs)
  apply (clarsimp simp: valid_cap_simps' rf_sr_ksCurThread)
  apply (rule context_conjI)
   subgoal by (clarsimp simp: get_capMappedASID_CL_def dest!: cap_to_H_PML4Cap)
  apply clarsimp
  apply (rule conjI, clarsimp simp: mask_def)
  apply clarsimp
  apply (rule conjI, clarsimp, rule conjI, clarsimp simp: pdpte_tag_defs, clarsimp)
   apply (rule conjI[rotated])
    apply (fastforce dest!: cap_lift_page_directory_cap
                     intro!: is_aligned_addrFromPPtr[simplified bit_simps, simplified]
                     simp: vmsz_aligned_def cap_to_H_simps cap_page_directory_cap_lift_def bit_simps capAligned_def)
   apply clarsimp
   (* ccap_relation *)
   apply (rule conjI)
    apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_page_directory_cap_lift[THEN iffD1]
                          cap_to_H_simps asid_wf_def3[simplified asid_bits_def, simplified])
    apply (rule conjI[rotated],
           fastforce simp: sign_extend_canonical_address le_def[symmetric] mask_def word_bw_assocs
                           le_user_vtop_canonical_address[simplified user_vtop_def X64.pptrUserTop_def word_le_nat_alt])
    subgoal by (clarsimp dest!: cap_lift_page_directory_cap simp: cap_page_directory_cap_lift_def)
   (* cpdpte_relation *)
   apply (rule conjI, clarsimp simp: cpdpte_relation_def)
    apply (clarsimp simp: superuser_from_vm_rights_def writable_from_vm_rights_def
                          x64CacheDisabled_def attribsFromWord_def word_and_1 nth_shiftr
                    split: if_split)
    apply (clarsimp dest!: cap_lift_page_directory_cap simp: cap_to_H_simps cap_page_directory_cap_lift_def)
    apply (rule addrFromPPtr_mask_middle_pml4ShiftBits[simplified pml4ShiftBits_def bit_simps, simplified])
     subgoal by (fastforce simp: valid_cap_simps' capAligned_def bit_simps)
    apply (fastforce dest!: page_directory_pde_atI'[where x=0, simplified bit_simps, simplified]
                     intro!: obj_at_kernel_mappings'
                     simp: typ_at_to_obj_at_arches)
   (* basePtr *)
   apply (frule (1) cap_lift_PML4Cap_Base)
   subgoal by (auto simp: cap_to_H_simps cap_pml4_cap_lift_def get_capPtr_CL_def
                    dest!: cap_to_H_PML4Cap_tag cap_lift_pml4_cap)
  apply (clarsimp simp: pdpte_tag_defs pdpte_get_tag_def word_and_1)
  (* proof below is duplicated from above due to difficulty of reasoning under
     so many layers of implications and assumptions
     context_conjI creates a mess, separate lemmas would be a bit unwieldy
  *)
  apply safe
    (* ccap_relation *)
     apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_page_directory_cap_lift[THEN iffD1]
                           cap_to_H_simps asid_wf_def3[simplified asid_bits_def, simplified])
     apply (rule conjI[rotated],
            fastforce simp: sign_extend_canonical_address le_def[symmetric] mask_def word_bw_assocs
                            le_user_vtop_canonical_address[simplified user_vtop_def X64.pptrUserTop_def word_le_nat_alt])
     subgoal by (clarsimp dest!: cap_lift_page_directory_cap simp: cap_page_directory_cap_lift_def)
    (* cpdpte_relation *)
    apply (clarsimp simp: cpdpte_relation_def)
    apply (clarsimp simp: superuser_from_vm_rights_def writable_from_vm_rights_def
                          x64CacheDisabled_def attribsFromWord_def word_and_1 nth_shiftr
                    split: if_split)
    apply (clarsimp dest!: cap_lift_page_directory_cap simp: cap_to_H_simps cap_page_directory_cap_lift_def)
    apply (rule addrFromPPtr_mask_middle_pml4ShiftBits[simplified pml4ShiftBits_def bit_simps, simplified])
     subgoal by (fastforce simp: valid_cap_simps' capAligned_def bit_simps)
    apply (fastforce dest!: page_directory_pde_atI'[where x=0, simplified bit_simps, simplified]
                     intro!: obj_at_kernel_mappings'
                     simp: typ_at_to_obj_at_arches)
   (* basePtr *)
   apply (frule (1) cap_lift_PML4Cap_Base)
   apply (auto simp: cap_to_H_simps cap_pml4_cap_lift_def get_capPtr_CL_def
               dest!: cap_to_H_PML4Cap_tag cap_lift_pml4_cap)[1]
  apply (fastforce dest!: cap_lift_page_directory_cap
                   intro!: is_aligned_addrFromPPtr[simplified bit_simps, simplified]
                   simp: vmsz_aligned_def cap_to_H_simps cap_page_directory_cap_lift_def bit_simps capAligned_def)
  done

lemma makeUserPML4E_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  {s}
  Call makeUserPML4E_'proc
  \<lbrace> pml4e_lift \<acute>ret__struct_pml4e_C = ( \<lparr>
       pml4e_CL.xd_CL = 0,
       pml4e_CL.pdpt_base_address_CL = \<^bsup>s\<^esup>paddr && (mask 39 << 12),
       pml4e_CL.accessed_CL = 0,
       pml4e_CL.cache_disabled_CL = x86PCDBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pml4e_CL.write_through_CL = x86PWTBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pml4e_CL.super_user_CL = 1,
       pml4e_CL.read_write_CL = 1,
       pml4e_CL.present_CL = 1\<rparr>) \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: pml4e_lift_def
                        superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def mask_def)
  done

lemma ccap_relation_pdpt_mapped_asid:
  "ccap_relation (ArchObjectCap (PDPointerTableCap p (Some (asid, vspace)))) cap
    \<Longrightarrow> asid = capPDPTMappedASID_CL (cap_pdpt_cap_lift cap)"
  by (frule cap_get_tag_isCap_unfolded_H_cap)
     (clarsimp simp: cap_pdpt_cap_lift ccap_relation_def cap_to_H_def split: if_splits)

lemma performPDPTInvocationMap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (cte_at' ctSlot)
       (UNIV \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace> \<inter> \<lbrace>cpml4e_relation pml4e \<acute>pml4e\<rbrace> \<inter> \<lbrace>\<acute>pml4Slot = Ptr pml4Slot\<rbrace>
             \<inter> \<lbrace>\<acute>vspace = Ptr vspace\<rbrace>)
       []
       (liftE (performPDPTInvocation (PDPTMap cap ctSlot pml4e pml4Slot vspace)))
       (Call performX64PDPTInvocationMap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: cap_' ctSlot_' pml4e_' pml4Slot_' vspace_')
   apply (ctac (no_vcg))
     apply (rule ccorres_split_nothrow)
         apply simp
         apply (erule storePML4E_Basic_ccorres)
        apply ceqv
       apply (rule ccorres_cases[where P="\<exists>p a v. cap = ArchObjectCap (PDPointerTableCap p (Some (a, v)))" and H=\<top> and H'=UNIV];
              clarsimp split: capability.splits arch_capability.splits simp: ccorres_fail)
       apply csymbr
       apply csymbr
       apply (rule ccorres_add_return2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (frule ccap_relation_pdpt_mapped_asid)
           apply simp
           apply (rule ccorres_call[where xf'=xfdc, OF invalidatePageStructureCacheASID_ccorres]; simp)
          apply ceqv
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply wp
       apply (simp add: guard_is_UNIV_def)
      apply (clarsimp, wp)
     apply vcg
    apply wp
   apply (clarsimp simp: cap_get_tag_isCap_unfolded_H_cap)
  apply simp
  done

lemma performPDPTInvocationMap_ccorres':
  "ccorres dc ret__unsigned_long_'
       (cte_at' ctSlot)
       (UNIV \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace>
             \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>
             \<inter> \<lbrace>cpml4e_relation pml4e \<acute>pml4e\<rbrace>
             \<inter> \<lbrace>\<acute>pml4Slot = Ptr pml4Slot\<rbrace>
             \<inter> \<lbrace>\<acute>vspace = Ptr vspace\<rbrace>)
       hs
       (performPDPTInvocation (PDPTMap cap ctSlot pml4e pml4Slot vspace))
       (Call performX64PDPTInvocationMap_'proc)"
  apply (cinit lift: cap_' ctSlot_' pml4e_' pml4Slot_' vspace_')
   apply (ctac (no_vcg))
     apply (rule ccorres_split_nothrow)
         apply simp
         apply (erule storePML4E_Basic_ccorres)
        apply ceqv
       apply (rule ccorres_cases[where P="\<exists>p a v. cap = ArchObjectCap (PDPointerTableCap p (Some (a, v)))" and H=\<top> and H'=UNIV];
              clarsimp split: capability.splits arch_capability.splits simp: ccorres_fail)
       apply csymbr
       apply csymbr
       apply (rule ccorres_add_return2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (frule ccap_relation_pdpt_mapped_asid)
           apply simp
           apply (rule ccorres_call[where xf'=xfdc, OF invalidatePageStructureCacheASID_ccorres]; simp)
          apply ceqv
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply wp
       apply (simp add: guard_is_UNIV_def)
      apply (clarsimp, wp)
     apply vcg
    apply wp
   apply (clarsimp simp: cap_get_tag_isCap_unfolded_H_cap)
  apply simp
  done

lemmas array_assertion_page_map_l4_at' =
  array_assertion_abs_pml4[where n="K 512" and x="K (1 :: machine_word)",
                           simplified, rule_format, simplified bit_simps, simplified, OF conjI]

lemma decodeX64PDPTInvocation_ccorres:
  "\<lbrakk>interpret_excaps extraCaps' = excaps_map extraCaps; isPDPointerTableCap cp\<rbrakk> \<Longrightarrow>
   ccorres
       (intr_and_se_rel \<currency> dc)
       (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and valid_cap' (ArchObjectCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       hs
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX64PDPTInvocation_'proc)"
     (is "_ \<Longrightarrow> _ \<Longrightarrow> ccorres _ _ ?pre ?cpre _ _ _")
  supply Collect_const[simp del] if_cong[cong]
         from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp] ccorres_IF_True[simp]
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_' current_extra_caps_' cap_' buffer_'
                simp: decodeX64MMUInvocation_def invocation_eq_use_types decodeX64PDPointerTableInvocation_def)
   apply (simp add: Let_def isCap_simps if_to_top_of_bind
               cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_split_throws)
     apply (simp add: liftE_bindE bind_assoc)
     apply (rule ccorres_symb_exec_l[OF _ getCTE_inv _ empty_fail_getCTE])
      apply (rule ccorres_rhs_assoc)+
      apply (ctac add: isFinalCapability_ccorres)
        apply (simp add: unlessE_def if_to_top_of_bind if_to_top_of_bindE
                         ccorres_seq_cond_raise)
        apply (rule ccorres_cond2'[where R=\<top>])
          apply clarsimp
         apply (simp add: throwError_bind invocationCatch_def)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (simp add: returnOk_bind bindE_assoc
                         performX64MMUInvocations)
        apply (ctac add: setThreadState_ccorres)
          apply (ctac add: performPDPTInvocationUnmap_ccorres)
             apply (rule ccorres_alternative2)
             apply (rule ccorres_return_CE, simp+)[1]
            apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
           apply wp
          apply simp
          apply (vcg exspec=performX64PDPTInvocationUnmap_modifies)
         apply (wp sts_invs_minor')
        apply simp
        apply (vcg exspec=setThreadState_modifies)
       apply (wp hoare_drop_imps isFinalCapability_inv)
      apply simp
      apply (vcg exspec=isFinalCapability_modifies)
     apply (wp getCTE_wp)
    apply (vcg exspec=performX64PDPTInvocationUnmap_modifies exspec=isFinalCapability_modifies
               exspec=setThreadState_modifies)
   apply simp
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (simp split: invocation_label.split arch_invocation_label.split
                   add: throwError_bind invocationCatch_def)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply simp
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: word_less_nat_alt throwError_bind invocationCatch_def)
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_equals_throwError)
     apply (simp add: throwError_bind split: list.split)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply csymbr
   apply (simp add: interpret_excaps_test_null excaps_map_def)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: list_case_If2 split_def
                    word_less_nat_alt length_ineq_not_Nil Let_def
                    whenE_bindE_throwError_to_if if_to_top_of_bind)
   apply csymbr
   apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
      apply vcg
     apply clarsimp
     apply (frule cap_get_tag_isCap_unfolded_H_cap)
     apply (clarsimp simp: cap_lift_pdpt_cap cap_pdpt_cap_lift_def
                           cap_to_H_def
                    elim!: ccap_relationE split: if_split)
     apply (simp add: to_bool_def)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: cap_case_PML4Cap2 split_def)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply csymbr
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply csymbr
       apply (rule ccorres_add_return)
       apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_pml4_cap)
                                          = (isArchObjectCap rv \<and> isPML4Cap (capCap rv)))
                                     \<and> (ccap_relation rv rv')) (fst (extraCaps ! 0))"
                and xf'=vspaceCap_' in ccorres_split_nothrow)
           apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
           apply (drule(1) slotcap_in_mem_PML4)
           apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
           apply (clarsimp simp: typ_heap_simps' mask_def)
           apply (rename_tac rv' t t')
          apply (simp add: word_sless_def word_sle_def)
          apply ceqv
         apply csymbr
         apply clarsimp
         apply (rule ccorres_Cond_rhs_Seq)
          apply ccorres_rewrite
          apply (rule_tac P="isArchObjectCap (fst (extraCaps ! 0)) \<and>
                             isPML4Cap (capCap (fst (extraCaps ! 0)))"
                          in ccorres_cases)
           apply (clarsimp simp: hd_conv_nth throwError_bind invocationCatch_def cong: if_cong)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply (clarsimp simp: hd_conv_nth throwError_bind invocationCatch_def cong: if_cong)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: hd_conv_nth)
         apply csymbr
         apply csymbr
         apply csymbr
         apply (simp add: case_option_If2 if_to_top_of_bind if_to_top_of_bindE hd_conv_nth)
         apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
            apply vcg
           apply (fastforce simp: user_vtop_def X64.pptrUserTop_def bit_simps
                                  word_le_nat_alt mask_def hd_conv_nth
                                  length_ineq_not_Nil)
          apply (simp add: throwError_bind invocationCatch_def)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: lookupError_injection invocationCatch_use_injection_handler
                          injection_bindE[OF refl refl] injection_handler_If
                          injection_handler_throwError injection_liftE[OF refl]
                          injection_handler_returnOk bindE_assoc cap_pml4_cap_lift get_capMappedASID_CL_def
                    cong: if_cong)
         apply csymbr
         apply (ctac add: ccorres_injection_handler_csum1 [OF ccorres_injection_handler_csum1,
                                                           OF findVSpaceForASID_ccorres])
            apply (simp add: Collect_False if_to_top_of_bindE)
            apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
               apply vcg
              apply (clarsimp simp: isCap_simps get_capPtr_CL_def)
              apply (frule cap_get_tag_isCap_unfolded_H_cap)
              apply (erule_tac v="rv'" in ccap_relationE, clarsimp simp: cap_to_H_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (simp add: bindE_assoc,
                   simp add: liftE_bindE)
            apply (rule ccorres_pre_getObject_pml4e)
            apply (clarsimp simp: get_capPtr_CL_def)
            apply (rename_tac pml4e pml4_mapped_asid)
            apply csymbr
            apply csymbr
            apply (rename_tac pml4e_present)
            apply (rule ccorres_abstract_cleanup)
            apply (clarsimp simp add: unlessE_def if_to_top_of_bindE injection_handler_If)
            apply (rule_tac Q'="\<lambda>s. \<exists>v. cslift s (pml4e_Ptr (lookup_pml4_slot (capPML4BasePtr (capCap (fst (extraCaps ! 0))))
                                                (args ! 0 && 0xFFFFFF8000000000))) = Some v
                             \<and> cpml4e_relation pml4e v \<and> pml4e_present = pml4e_CL.present_CL (pml4e_lift v)"
                        and Q="valid_cap' (ArchObjectCap cp)"
                        in ccorres_if_cond_throws2[rotated -1])
               apply vcg
              apply (fastforce simp: cpml4e_relation_def Let_def split: pml4e.split_asm)
             apply (simp add: injection_handler_throwError throwError_bind invocationCatch_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (simp add: injection_handler_returnOk performX64MMUInvocations bindE_assoc)
            apply csymbr
            apply csymbr
            apply csymbr
            apply csymbr
            apply csymbr
            apply csymbr
            apply (ctac add: setThreadState_ccorres)
              apply (ctac (no_vcg) add: performPDPTInvocationMap_ccorres)
                apply (rule ccorres_alternative2)
                apply (rule ccorres_return_CE, simp+)[1]
               apply (rule ccorres_inst[where P=\<top> and P'=UNIV], fastforce)
              apply wp
             apply wp
            apply (simp add: bit_simps)
            apply clarsimp
            apply (rule_tac t=pml4_mapped_asid and
                            s="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                            in ssubst, fastforce)
            apply (rule conseqPre, vcg exspec=setThreadState_modifies)
            apply (rule subset_refl)
           apply (rename_tac find_ret)
           apply clarsimp
           apply (rule_tac P'="{s. errstate s = find_ret}" in ccorres_from_vcg_split_throws[where P=\<top>])
            apply vcg
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                 syscall_error_to_H_cases exception_defs)
           apply (erule lookup_failure_rel_fault_lift[rotated])
           apply (fastforce simp: exception_defs)
          apply clarsimp
          apply (wp injection_wp[OF refl] hoare_drop_imps)
         apply (clarsimp simp: get_capPtr_CL_def)
         apply (rename_tac pml4_mapped_asid)
         apply (rule_tac t=pml4_mapped_asid and
                         s="the (capPML4MappedASID (capCap (fst (extraCaps ! 0))))"
                         in ssubst, fastforce)
         apply (vcg exspec=findVSpaceForASID_modifies)
        apply wpsimp
       apply vcg
      apply wpsimp
     apply (vcg exspec=getSyscallArg_modifies)
    apply wpsimp
   apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: cte_wp_at_ctes_of excaps_map_def
                        word_sle_def word_sless_def bit_simps)
  apply (rule conjI)
   apply (auto simp: ct_in_state'_def isCap_simps valid_tcb_state'_def
              elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
  apply (rule conjI)
   apply (clarsimp simp: isCap_simps)
   apply (subgoal_tac "s \<turnstile>' fst (extraCaps ! 0)")
    apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt
                          linorder_not_less)
    apply (clarsimp | drule length_le_helper)+
    apply (clarsimp simp: valid_cap'_def neq_Nil_conv
                          mask_add_aligned page_directory_at'_def
                          word_le_nat_alt[symmetric] bit_simps)
    apply (auto simp: ct_in_state'_def pred_tcb_at' mask_def valid_tcb_state'_def
               elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
   apply (auto simp: neq_Nil_conv excaps_in_mem_def slotcap_in_mem_def)[1]
  apply (rule conjI)
   apply (fastforce simp: rf_sr_ksCurThread
                          mask_eq_iff_w2p word_size
                          ct_in_state'_def st_tcb_at'_def
                          word_sle_def word_sless_def
                          typ_heap_simps' bit_simps)
  apply (drule_tac t="cteCap ctea" in sym, simp)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply clarsimp
  apply (rename_tac pml4_mapped_asid)
  apply (rule conjI[rotated], fastforce simp: cap_tag_defs)
  apply clarsimp
  apply (rule context_conjI)
   (* get_capMappedASID_CL *)
   apply (fastforce elim!: ccap_relationE[where c="ArchObjectCap (PML4Cap _ _)"]
                    simp: neq_Nil_conv valid_cap_simps' isCap_simps
                          get_capMappedASID_CL_def cap_pml4_cap_lift cap_to_H_simps
                    split: if_split_asm)
  apply (clarsimp simp: neq_Nil_conv[where xs=extraCaps] excaps_in_mem_def slotcap_in_mem_def
                 dest!: sym[where s="ArchObjectCap cp" for cp])
  apply (clarsimp simp: word_less_nat_alt hd_conv_nth dest!: length_ineq_not_Nil)
  apply (rule conjI, fastforce simp: mask_def)
  apply (rule conjI[rotated])
   (* array assertion and page_map_l4_at' *)
   apply (clarsimp simp: mask_def typ_heap_simps')
   apply (erule array_assertion_page_map_l4_at')
   apply (subgoal_tac "s \<turnstile>' fst (extraCaps ! 0)")
    prefer 2
    apply (fastforce simp: neq_Nil_conv excaps_in_mem_def slotcap_in_mem_def dest: ctes_of_valid')
   apply (clarsimp simp: valid_cap_simps' isCap_simps cap_lift_pml4_cap)
   apply (erule ccap_relationE[where c="ArchObjectCap (PML4Cap _ _)"])
   apply (clarsimp simp: get_capMappedASID_CL_def)
   apply (subst cap_lift_PML4Cap_Base[symmetric]; (assumption | rule sym, assumption))
  apply (clarsimp simp: rf_sr_ksCurThread)
  (* ccap_relation *)
  apply (rule conjI)
   apply (erule ccap_relationE[where c="ArchObjectCap (PDPointerTableCap _ _)"])
   apply (clarsimp simp: ccap_relation_def cap_pdpt_cap_lift isCap_simps cap_to_H_def)
   apply (rule conjI)
    (* get_capMappedASID_CL *)
    apply (fastforce simp: get_capMappedASID_CL_def mask_def
                     dest!: cap_lift_pml4_cap)
   apply (fastforce simp: word_bw_assocs sign_extend_canonical_address le_def[symmetric] mask_def
                          le_user_vtop_canonical_address[simplified user_vtop_def X64.pptrUserTop_def word_le_nat_alt])
  (* cmpl4e_relation *)
  apply (rule conjI)
   apply (clarsimp simp: cpml4e_relation_def superuser_from_vm_rights_def writable_from_vm_rights_def
                         x64CacheDisabled_def attribsFromWord_def word_and_1 nth_shiftr
                   split: if_split)
   apply (clarsimp elim!: ccap_relationE dest!: cap_lift_pdpt_cap simp: cap_to_H_simps cap_pdpt_cap_lift_def)
   (* addrFromPPtr *)
   apply (rule addrFromPPtr_mask_middle_pml4ShiftBits[simplified pml4ShiftBits_def bit_simps, simplified])
    apply (fastforce simp: valid_cap_simps' capAligned_def bit_simps)
   apply (fastforce dest!: pd_pointer_table_pdpte_atI'[where x=0, simplified bit_simps, simplified]
                    intro!: obj_at_kernel_mappings'
                    simp: valid_cap_simps' typ_at_to_obj_at_arches)
  apply (fastforce simp: mask_def typ_heap_simps')
  done

lemma decodeX64ModeMMUInvocation_ccorres:
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps; \<not> isPageCap cp; \<not> isPageTableCap cp;
     \<not> isASIDControlCap cp; \<not> isASIDPoolCap cp \<rbrakk>
   \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and valid_cap' (ArchObjectCap cp)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       hs
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86ModeMMUInvocation_'proc)"
  supply Collect_const[simp del] if_cong[cong]
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_')
   apply csymbr
   apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                   cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (clarsimp simp: decodeX64MMUInvocation_def isCap_simps throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (solves \<open>simp add: syscall_error_to_H_cases\<close>)
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call,
           rule decodeX64PDPTInvocation_ccorres;
           solves simp)
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call,
           rule decodeX64PageDirectoryInvocation_ccorres;
           solves simp)
   apply (fastforce intro: ccorres_fail simp: decodeX64MMUInvocation_def)
  apply (simp add: o_def)
  done

lemma decodeX64MMUInvocation_ccorres:
  notes Collect_const[simp del] if_cong[cong]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps \<rbrakk>
   \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86MMUInvocation_'proc)"
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_' call_')
   apply csymbr
   apply (simp add: cap_get_tag_isCap_ArchObject
                    X64_H.decodeInvocation_def
                    invocation_eq_use_types
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call,
           rule decodeX64FrameInvocation_ccorres,
           simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call,
           rule decodeX64PageTableInvocation_ccorres, simp+)[1]
   (* ASIDControlCap *)
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: decodeX64MMUInvocation_def decodeX64ASIDControlInvocation_def isCap_simps
                             throwError_bind invocationCatch_def
                      split: invocation_label.split arch_invocation_label.split)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    (* X64ASIDControlMakePool *)
    apply (clarsimp simp: decodeX64MMUInvocation_def decodeX64ASIDControlInvocation_def isCap_simps)
    apply (simp add: word_less_nat_alt list_case_If2 split_def)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     (* args malformed *)
     apply (rule ccorres_cond_true_seq | simp)+
     apply (simp add: throwError_bind invocationCatch_def)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    apply (simp add: interpret_excaps_test_null excaps_map_def)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     (* extraCaps malformed *)
     apply (rule ccorres_cond_true_seq | simp)+
     apply (simp add: throwError_bind invocationCatch_def)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    apply csymbr
    apply (simp add: interpret_excaps_test_null[OF Suc_leI])
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: length_ineq_not_Nil throwError_bind invocationCatch_def)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (subgoal_tac "1 < length extraCaps")
     prefer 2
     apply (rule neq_le_trans, simp)
     apply (fastforce simp: Suc_leI)
    apply (simp add: Let_def split_def liftE_bindE bind_assoc length_ineq_not_Nil)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply csymbr
        apply (rule ccorres_add_return,
               rule_tac xf'=untyped_' and
                        r'="(\<lambda>rv _ un.
                              (cap_get_tag un = scast cap_untyped_cap) = isUntypedCap rv \<and>
                              (isUntypedCap rv \<longrightarrow> ccap_relation rv un))
                            (fst (extraCaps ! 0))"
                        in ccorres_split_nothrow)
            apply (rule_tac P="excaps_in_mem extraCaps \<circ> ctes_of"
                            in ccorres_from_vcg[where P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (frule length_ineq_not_Nil[where xs=extraCaps])
            apply (clarsimp simp: return_def neq_Nil_conv excaps_in_mem_def
                                  slotcap_in_mem_def)
            apply (drule interpret_excaps_eq[rule_format, where n=0], simp)
            apply (simp add: mask_def[where n=4])
            apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
            apply (rule conjI, fastforce intro: typ_heap_simps)
            apply (drule ccte_relation_ccap_relation)
            apply (simp add: typ_heap_simps cap_get_tag_isCap)
           apply ceqv
          apply (rename_tac untyped')
          apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=1])
          apply (rule ccorres_move_c_guard_cte)
          apply ctac
            apply (rule ccorres_assert2)
            apply (rule ccorres_pre_gets_x86KSASIDTable_ksArchState)
            apply (rename_tac "x86KSASIDTab")
            apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                   rule ccorres_rhs_assoc2)
            apply (rule ccorres_add_return)
            apply (rule_tac r'="\<lambda>rv rv'. rv' = (case [p \<leftarrow> assocs x86KSASIDTab.
                                                      fst p < 2 ^ asid_high_bits \<and> snd p = None]
                                                of [] \<Rightarrow> 2 ^ asid_high_bits | x # xs \<Rightarrow> fst x)"
                    and xf'=i_' in ccorres_split_nothrow)
                apply (rule_tac P="\<forall>x \<in> ran x86KSASIDTab. x \<noteq> 0"
                                in ccorres_gen_asm)
                apply (rule_tac P="\<lambda>s. x86KSASIDTab = x64KSASIDTable (ksArchState s)"
                                in ccorres_from_vcg[where P'=UNIV])
                apply (clarsimp simp: return_def)
                apply (rule HoarePartial.SeqSwap)
                 apply (rule_tac I="{t. (\<sigma>, t) \<in> rf_sr \<and> i_' t \<le> 2 ^ asid_high_bits
                                        \<and> x86KSASIDTab = x64KSASIDTable (ksArchState \<sigma>)
                                        \<and> (\<forall>x < i_' t. x86KSASIDTab x \<noteq> None)
                                        \<and> ret__int_' t = from_bool (i_' t < 2 ^ asid_high_bits \<and>
                                                                    x86KSASIDTab (i_' t) \<noteq> None)}"
                                 in HoarePartial.reannotateWhileNoGuard)
                 apply (rule HoarePartial.While[OF order_refl])
                  apply (rule conseqPre, vcg)
                  apply (clarsimp simp: asidHighBits_handy_convs
                                        word_sle_def word_sless_def
                                        word_less_nat_alt[symmetric]
                                        from_bool_0)
                  apply (cut_tac P="\<lambda>y. y < i_' x + 1 = rhs y" for rhs in allI,
                         rule less_x_plus_1)
                   apply (fastforce simp: asid_high_bits_def)
                  apply (clarsimp simp: rf_sr_x86KSASIDTable
                                        asid_high_bits_word_bits
                                        option_to_ptr_def option_to_0_def
                                        order_less_imp_le
                                        linorder_not_less
                                        order_antisym[OF inc_le])
                  apply (clarsimp split: option.split if_split)
                  apply (auto simp: asid_high_bits_def word_le_nat_alt
                                    word_less_nat_alt unat_add_lem[THEN iffD1]
                                    Kernel_C_defs)[1]
                 apply (clarsimp simp: from_bool_0)
                 apply (case_tac "i_' x = 2 ^ asid_high_bits")
                  apply (clarsimp split: list.split)
                  apply (drule_tac f="\<lambda>xs. (a, b) \<in> set xs" in arg_cong)
                  apply (clarsimp simp: in_assocs_is_fun)
                  apply fastforce
                 apply (frule(1) neq_le_trans)
                 apply (subst filter_assocs_Cons)
                   apply fastforce
                  apply simp
                 apply simp
                apply (rule conseqPre, vcg)
                apply (clarsimp simp: asidHighBits_handy_convs word_sle_def
                                      word_sless_def from_bool_0
                                      rf_sr_x86KSASIDTable[where n=0, simplified])
                apply (simp add: asid_high_bits_def option_to_ptr_def option_to_0_def Kernel_C_defs
                          split: option.split if_split)
                apply fastforce
               apply ceqv
              apply (rule ccorres_Guard_Seq)+
              apply (simp add: whenE_bindE_throwError_to_if if_to_top_of_bind)
              apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
                 apply clarsimp
                 apply (rule conseqPre, vcg, rule subset_refl)
                apply (clarsimp simp: asid_high_bits_word_bits asidHighBits_handy_convs null_def)
                apply (clarsimp split: list.split)
                apply (fastforce dest!: filter_eq_ConsD)
               apply (simp add: throwError_bind invocationCatch_def)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (fastforce simp: syscall_error_to_H_cases)
              apply (rule ccorres_Guard_Seq)+
              apply (simp add: invocationCatch_use_injection_handler
                               injection_bindE[OF refl refl] injection_handler_If
                               injection_handler_returnOk bindE_assoc
                               injection_handler_throwError
                         cong: if_cong)
              apply csymbr
              apply csymbr
              apply csymbr
              apply (rule ccorres_symb_exec_r)
                apply (rule_tac xf'=ret__int_' in ccorres_abstract, ceqv)
                  apply (rule_tac P="rv'a = from_bool (\<not> (isUntypedCap (fst (hd extraCaps)) \<and>
                                                          capBlockSize (fst (hd extraCaps)) = objBits (makeObject ::asidpool)))"
                                  in ccorres_gen_asm2)
                apply (rule ccorres_symb_exec_r)
                  apply (rule_tac xf'=ret__int_' in ccorres_abstract, ceqv)
                  apply (rule_tac P="rv'b = from_bool (\<not> (isUntypedCap (fst (hd extraCaps)) \<and>
                                                          capBlockSize (fst (hd extraCaps)) = objBits (makeObject ::asidpool) \<and>
                                                          \<not> capIsDevice (fst (hd extraCaps))))"
                                  in ccorres_gen_asm2)
                  apply (clarsimp simp:  to_bool_if cond_throw_whenE bindE_assoc)
                  apply (rule ccorres_split_when_throwError_cond[where Q = \<top> and Q' = \<top>])
                     apply fastforce
                    apply (rule syscall_error_throwError_ccorres_n)
                    apply (clarsimp simp: syscall_error_rel_def shiftL_nat syscall_error_to_H_cases)
                   prefer 2
                   apply vcg
                  apply clarsimp
                  apply (ctac add: ccorres_injection_handler_csum1[OF ensureNoChildren_ccorres])
                     apply (clarsimp simp: Collect_False)
                     apply csymbr
                     apply csymbr
                     apply (ctac add: ccorres_injection_handler_csum1
                                        [OF lookupTargetSlot_ccorres,
                                         unfolded lookupTargetSlot_def])
                        apply (simp add: Collect_False split_def)
                        apply csymbr
                        apply (ctac add: ccorres_injection_handler_csum1
                                                [OF ensureEmptySlot_ccorres])
                           apply (simp add: ccorres_invocationCatch_Inr
                                            performInvocation_def
                                            X64_H.performInvocation_def
                                            performX64MMUInvocation_def)
                           apply (simp add: liftE_bindE)
                           apply ccorres_rewrite
                           apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
                           apply (ctac add: setThreadState_ccorres)
                             apply (simp only: liftE_bindE[symmetric])
                             apply (rule ccorres_seq_skip'[THEN iffD1])
                             apply (ctac (no_vcg) add: performASIDControlInvocation_ccorres
                                                       [where idx = "capFreeIndex (fst (extraCaps ! 0))"])
                               apply (rule ccorres_alternative2)
                               apply (rule ccorres_returnOk_skip)
                              apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                             apply wp
                            apply (wp sts_invs_minor' sts_Restart_ct_active)
                           apply simp
                           apply (vcg exspec=setThreadState_modifies)
                          apply ccorres_rewrite
                          apply (rule ccorres_return_C_errorE, simp+)
                         apply (wp injection_wp[OF refl])
                        apply (simp add: all_ex_eq_helper)
                        (* This manual conseqPost prevents the VCG from instantiating False *)
                        apply (rule_tac Q'=UNIV and A'="{}" in conseqPost)
                          apply (vcg exspec=ensureEmptySlot_modifies)
                         apply (frule length_ineq_not_Nil)
                         apply (clarsimp simp: null_def hd_conv_nth
                                               isCap_simps rf_sr_ksCurThread cap_get_tag_UntypedCap
                                               word_le_make_less asid_high_bits_def
                                         split: list.split)
                         apply (frule interpret_excaps_eq[rule_format, where n=0], fastforce)
                         apply (fastforce simp: interpret_excaps_test_null excaps_map_def split_def)
                        apply fastforce
                       apply ccorres_rewrite
                       apply (rule ccorres_return_C_errorE, simp+)
                      apply (wp injection_wp[OF refl] hoare_drop_imps)
                     apply (simp add: split_def all_ex_eq_helper)
                     apply (vcg exspec=lookupTargetSlot_modifies)
                    apply simp
                    apply ccorres_rewrite
                    apply (rule ccorres_return_C_errorE, simp+)
                   apply (wp injection_wp[OF refl] ensureNoChildren_wp)
                  apply (simp add: all_ex_eq_helper cap_get_tag_isCap)
                  apply (vcg exspec=ensureNoChildren_modifies)
                 apply clarsimp
                 apply vcg
                apply clarsimp
                apply (rule conseqPre, vcg, clarsimp)
               apply clarsimp
               apply vcg
              apply clarsimp
              apply (rule conseqPre, vcg, clarsimp)
             apply wp
            apply (simp add: cap_get_tag_isCap)
            apply (rule HoarePartial.SeqSwap)
             apply (rule_tac I="\<lbrace>Prop \<acute>ksCurThread \<acute>root\<rbrace>"
                         and Q="\<lbrace>Bonus \<acute>i \<longrightarrow> Prop \<acute>ksCurThread \<acute>root\<rbrace>"
                         for Prop Bonus in HoarePartial.reannotateWhileNoGuard)
             apply (rule HoarePartial.While[OF order_refl])
              apply (rule conseqPre, vcg)
              apply clarify
              apply (rule conjI)
               apply clarify
              apply (simp (no_asm))
              apply clarify
             apply clarsimp
            apply vcg
           apply simp
           apply (rule hoare_drop_imps)
           apply wp
          apply simp
          apply vcg
         apply simp
         apply wp
        apply vcg
       apply wp
      apply simp
      apply (vcg exspec=getSyscallArg_modifies)
     apply simp
     apply wp
    apply simp
    apply (vcg exspec=getSyscallArg_modifies)
   (* ASIDPoolCap case *)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: imp_conjR[symmetric] decodeX64MMUInvocation_def)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (clarsimp simp: isCap_simps decodeX64ASIDPoolInvocation_def)
     apply ccorres_rewrite
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: throwError_bind invocationCatch_def
                      split: invocation_label.split arch_invocation_label.split)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    apply (simp add: interpret_excaps_test_null excaps_map_def
                     list_case_If2 split_def)
    apply (rule ccorres_Cond_rhs_Seq)
     apply ccorres_rewrite
     apply (clarsimp simp: isCap_simps decodeX64ASIDPoolInvocation_def
                           throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    apply (clarsimp simp: isCap_simps decodeX64ASIDPoolInvocation_def split: list.split)
    apply csymbr
    apply (rule ccorres_add_return)
    apply (rule ccorres_Guard_Seq)
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_rhs_assoc2)
    apply (rule_tac R="excaps_in_mem extraCaps \<circ> ctes_of" and
                    R'="UNIV" and
                    val="from_bool (\<not> (isArchObjectCap (fst (extraCaps ! 0)) \<and>
                                       isPML4Cap (capCap (fst (extraCaps ! 0)))) \<or>
                                    capPML4MappedASID (capCap (fst (extraCaps ! 0))) \<noteq> None)" and
                    xf'=ret__int_' in ccorres_symb_exec_r_known_rv)
       apply vcg
       apply clarsimp
       apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
       apply (clarsimp simp: excaps_in_mem_def)
       apply (frule (1) slotcap_in_mem_PML4)
       apply (clarsimp simp: typ_heap_simps' from_bool_0 split: if_split)
       apply (fastforce simp: isCap_simps asidInvalid_def cap_lift_pml4_cap cap_to_H_simps
                              get_capMappedASID_CL_def c_valid_cap_def cl_valid_cap_def
                        elim!: ccap_relationE split: if_splits)
      apply ceqv
     apply (rule ccorres_Cond_rhs_Seq)
      apply ccorres_rewrite
      apply (rule_tac v="Inl (InvalidCapability 1)" in ccorres_equals_throwError)
       apply (fastforce simp: isCap_simps throwError_bind invocationCatch_def
                        split: capability.split arch_capability.split)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (fastforce simp: syscall_error_to_H_cases)
     apply (clarsimp simp: isCap_simps Kernel_C_defs liftE_bindE bind_assoc)
     apply (rule ccorres_pre_gets_x86KSASIDTable_ksArchState)
     apply csymbr
     apply (rule ccorres_Guard_Seq)+
     apply (rule ccorres_add_return)
     apply (rule_tac r'="\<lambda>_ rv'. rv' = option_to_ptr (x (ucast (asid_high_bits_of (capASIDBase cp))))
                                 \<and> x (ucast (asid_high_bits_of (capASIDBase cp))) \<noteq> Some 0"
                 and xf'=pool_' in ccorres_split_nothrow)
         apply (rule_tac P="\<lambda>s. x = x64KSASIDTable (ksArchState s)
                                \<and> valid_arch_state' s \<and> s \<turnstile>' ArchObjectCap cp"
                         in ccorres_from_vcg[where P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def valid_arch_state'_def valid_asid_table'_def)
         apply (frule cap_get_tag_isCap_ArchObject(2))
         apply (clarsimp simp: isCap_simps)
         apply (erule_tac v=cap in ccap_relationE)
         apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_simps valid_cap_simps'
                               cap_asid_pool_cap_lift_def)
         apply (subst rf_sr_x86KSASIDTable, assumption)
          apply (simp add: asid_high_bits_word_bits)
          apply (rule shiftr_less_t2n)
          apply (fastforce simp: asid_low_bits_def asid_high_bits_def asid_wf_def mask_def
                                 asid_bits_def word_le_make_less)
         apply (fastforce simp: ucast_asid_high_bits_is_shift asid_wf_def mask_def)
        apply ceqv
       apply (simp add: whenE_bindE_throwError_to_if if_to_top_of_bind cong: if_cong)
       apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
          apply vcg
         apply (simp add: option_to_0_def option_to_ptr_def split: option.split)
         apply fastforce
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: throwError_def return_def
                              syscall_error_rel_def exception_defs syscall_error_to_H_cases)
        apply (simp add: lookup_fault_lift_invalid_root)
       apply csymbr
       apply (simp add: liftME_def bindE_assoc if_to_top_of_bind)
       apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
          apply vcg
         apply (frule cap_get_tag_isCap_ArchObject(2))
         apply (clarsimp simp: isCap_simps)
         apply (erule_tac v=cap in ccap_relationE)
         apply (fastforce simp: cap_lift_asid_pool_cap cap_to_H_simps valid_cap_simps'
                                cap_asid_pool_cap_lift_def)
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (fastforce simp: syscall_error_to_H_cases)
       apply csymbr
       apply csymbr
       apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
              rule ccorres_rhs_assoc2)
       apply (simp add: bind_assoc liftE_bindE)
       apply (rule_tac xf'=i_' and r'="\<lambda>rv rv'. rv' = (case [(x, y) \<leftarrow> assocs (inv ASIDPool rv).
                                                              x \<le> 2 ^ asid_low_bits - 1 \<and> x + capASIDBase cp \<noteq> 0
                                                              \<and> y = None] of [] \<Rightarrow> 2 ^ asid_low_bits
                                                             | x # xs \<Rightarrow> fst x)"
                       in ccorres_split_nothrow)
           apply (rule ccorres_add_return2)
           apply (rule ccorres_pre_getObject_asidpool)
           apply (rule_tac P="\<forall>x \<in> ran (inv ASIDPool xa). x \<noteq> 0"
                           in ccorres_gen_asm)
           apply (rule_tac P="ko_at' xa (capASIDPool cp)"
                           in ccorres_from_vcg[where P'=UNIV])
           apply (clarsimp simp: option_to_0_def option_to_ptr_def
                                 return_def)
           apply (rule HoarePartial.SeqSwap)
            apply (rule_tac I="{t. (\<sigma>, t) \<in> rf_sr \<and> i_' t \<le> 2 ^ asid_low_bits
                                 \<and> ko_at' xa (capASIDPool cp) \<sigma>
                                 \<and> (\<exists>v. cslift t (ap_Ptr (capASIDPool cp))
                                         = Some v \<and> (\<forall>x < i_' t. capASIDBase cp + x = 0
                                                        \<or> asid_map_get_tag (index (array_C v) (unat x)) \<noteq> scast asid_map_asid_map_none )
                                        \<and> ret__int_' t = from_bool (i_' t < 2 ^ asid_low_bits
                                             \<and> (capASIDBase cp + (i_' t) = 0
                                                 \<or> asid_map_get_tag (index (array_C v) (unat (i_' t))) \<noteq> scast asid_map_asid_map_none)))}"
                         in HoarePartial.reannotateWhileNoGuard)
            apply (rule HoarePartial.While[OF order_refl])
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: asidLowBits_handy_convs
                                   word_sle_def word_sless_def from_bool_0)
             apply (subgoal_tac "capASIDBase_CL (cap_asid_pool_cap_lift cap)
                                     = capASIDBase cp")
              apply (subgoal_tac "\<And>x. (x < (i_' xb + 1))
                                        = (x < i_' xb \<or> x = i_' xb)")
               apply (clarsimp simp: inc_le typ_heap_simps asid_low_bits_def not_less field_simps
                              split: if_split bool.splits)
               apply unat_arith
              apply (rule iffI)
               apply (rule disjCI)
               apply (drule plus_one_helper)
               apply simp
              apply (subgoal_tac "i_' xb < i_' xb + 1")
               apply (erule_tac P="x < y" for x y in disjE, simp_all)[1]
              apply (rule plus_one_helper2 [OF order_refl])
              apply (rule notI, drule max_word_wrap)
              apply (fastforce simp: asid_low_bits_def)
             apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
             apply (frule cap_get_tag_isCap_unfolded_H_cap)
             apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_def
                                   cap_asid_pool_cap_lift_def
                            elim!: ccap_relationE)
            apply (clarsimp simp: from_bool_0)
            apply (erule cmap_relationE1[OF rf_sr_cpspace_asidpool_relation],
                   erule ko_at_projectKO_opt)
            apply (clarsimp simp: typ_heap_simps casid_pool_relation_def
                                    inv_ASIDPool array_relation_def
                             split: asidpool.split_asm asid_pool_C.split_asm)
            apply (case_tac "i_' xb = 2 ^ asid_low_bits")
             apply (clarsimp split: list.split)
             apply (drule_tac f="\<lambda>xs. (a, ba) \<in> set xs" in arg_cong)
             apply (clarsimp simp: in_assocs_is_fun)
             apply (drule spec, drule(1) mp)
             apply (simp add: asid_low_bits_word_bits)
             apply (drule spec, drule(1) mp)
             apply (simp add: option_to_ptr_def option_to_0_def field_simps)
             apply (clarsimp simp: asid_map_relation_def asid_map_lift_def
                            split: if_split_asm option.splits asid_map_CL.split_asm )
            apply (frule(1) neq_le_trans)
            apply (subst filter_assocs_Cons)
              apply (simp add: split_def asid_low_bits_word_bits)
              apply (rule conjI, assumption)
              apply (clarsimp simp add: field_simps)
              apply (drule spec, drule(1) mp)
              apply (simp add: asid_map_relation_def asid_map_lift_asid_map_none
                        split: option.split_asm)
             apply (simp add: asid_low_bits_word_bits)
             apply (erule allEI, rule impI, drule(1) mp)
             apply (clarsimp simp: field_simps)
             apply (drule_tac x=xa in spec)
             apply (simp add: asid_map_relation_def asid_map_lift_def
                       split: if_split_asm option.splits asid_map_CL.split_asm)
            apply simp
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: asidLowBits_handy_convs
                                 signed_shift_guard_simpler_64 asid_low_bits_def
                                 word_sless_def word_sle_def)
           apply (erule cmap_relationE1[OF rf_sr_cpspace_asidpool_relation],
                  erule ko_at_projectKO_opt)
           apply (clarsimp simp: typ_heap_simps split: if_split)
           apply (frule cap_get_tag_isCap_unfolded_H_cap)
           apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_def
                                 cap_asid_pool_cap_lift_def ucast_minus ucast_nat_def
                          elim!: ccap_relationE)
          apply ceqv
         apply (rule ccorres_Guard_Seq)+
         apply (simp add: if_to_top_of_bind)
         apply (rule ccorres_if_cond_throws[where Q=\<top> and Q'=\<top>, rotated -1])
            apply vcg
           apply (clarsimp simp: null_def split: list.split
                           dest!: filter_eq_ConsD)
           apply (simp add: asid_low_bits_def)
          apply (simp add: throwError_bind invocationCatch_def)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: returnOk_bind ccorres_invocationCatch_Inr
                          performInvocation_def
                          X64_H.performInvocation_def
                          performX64MMUInvocation_def liftE_bindE)
         apply csymbr
         apply (ctac add: setThreadState_ccorres)
           apply (simp only: liftE_bindE[symmetric])
           apply (ctac(no_vcg) add: performASIDPoolInvocation_ccorres)
             apply (rule ccorres_alternative2)
             apply (rule ccorres_return_CE, simp+)[1]
            apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
            apply simp
           apply wp
          apply simp
          apply (wp sts_invs_minor')
         apply simp
         apply (vcg exspec=setThreadState_modifies)
        apply simp
        apply (wp getASID_wp)
       apply simp
       apply (rule HoarePartial.SeqSwap)
        apply (rule_tac I="\<lbrace>\<forall>rv. Prop \<acute>ksCurThread \<acute>vspaceCapSlot rv\<rbrace>"
                    and Q="\<lbrace>\<forall>rv. Bonus \<acute>i rv \<longrightarrow> Prop \<acute>ksCurThread \<acute>vspaceCapSlot rv\<rbrace>"
                    for Prop Bonus in HoarePartial.reannotateWhileNoGuard)
        apply vcg
         apply fastforce
        apply clarsimp
       apply vcg
      apply simp
      (* HACK: rewrites to fix schematic dependency problems *)
      apply (rule_tac t=v0 and s="capASIDPool cp" in subst, fastforce)
      apply (rule_tac t=v1 and s="capASIDBase cp" in subst, fastforce)
      apply (rule_tac t=b and s="snd (extraCaps ! 0)" in subst, fastforce)
      apply (rule return_wp)
     apply vcg
    apply (rule_tac t=v0 and s="capASIDPool cp" in subst, fastforce)
    apply (rule_tac t=v1 and s="capASIDBase cp" in subst, fastforce)
    apply (rule_tac t=b and s="snd (extraCaps ! 0)" in subst, fastforce)
    apply vcg
   (* Mode stuff *)
   apply (rule ccorres_trim_returnE; simp?)
   apply (rule ccorres_call,
          rule decodeX64ModeMMUInvocation_ccorres;
          simp)
  apply (clarsimp simp: o_def)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of ct_in_state'_def
                         interpret_excaps_eq excaps_map_def)
   apply (drule_tac t="cteCap cte" in sym)
   apply (frule(1) ctes_of_valid', simp)
   apply (cases "extraCaps")
    apply simp
   apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
   apply (clarsimp simp: mask_def[where n=4] excaps_in_mem_def
                         slotcap_in_mem_def typ_at_to_obj_at_arches
                         obj_at'_weakenE[OF _ TrueI] invs_arch_state'
                         unat_lt2p[where 'a=machine_word_len, folded word_bits_def])
   apply (rule conjI)
    apply (frule invs_arch_state')
    apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def neq_Nil_conv)
    apply (frule interpret_excaps_eq[rule_format, where n=1], simp)
    apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt)
    apply (drule length_le_helper | clarsimp simp: linorder_not_less)+
    apply (rule conjI)
     apply clarsimp
    apply (clarsimp simp: tcb_at_invs' Kernel_C.asidLowBits_def)
    apply (clarsimp simp: invs_valid_objs')
    apply (rule conjI, fastforce)
    apply (clarsimp simp: ctes_of_valid' invs_valid_objs' isCap_simps)
    apply (clarsimp simp: ex_cte_cap_wp_to'_def cte_wp_at_ctes_of invs_pspace_distinct'
                          invs_sch_act_wf' invs_pspace_aligned'
                    dest!: isCapDs(1))
    apply (intro conjI)
           apply (simp add: valid_tcb_state'_def)
          apply (fastforce elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')
         apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
         apply (case_tac "tcbState obj", (simp add: runnable'_def)+)[1]
        apply simp
       apply (simp add: objBits_simps archObjSize_def)
      apply fastforce
     apply (clarsimp simp: null_def neq_Nil_conv)
     apply (drule_tac f="\<lambda>xs. (a, bb) \<in> set xs" in arg_cong)
      apply (clarsimp simp: in_assocs_is_fun)
     apply (clarsimp simp: le_mask_asid_bits_helper)
    apply (simp add: is_aligned_shiftl_self)
   apply (intro conjI impI)
     apply clarsimp
     apply (drule obj_at_valid_objs', clarsimp)
     apply (clarsimp simp: projectKOs valid_obj'_def inv_ASIDPool
                    split: asidpool.split_asm)
    apply clarsimp
    apply (drule obj_at_valid_objs', clarsimp)
    apply (clarsimp simp: projectKOs valid_obj'_def inv_ASIDPool
                    split: asidpool.split_asm)
    apply (clarsimp simp: isCap_simps Let_def valid_cap'_def
                          maskCapRights_def[where ?x1.0="ArchObjectCap cp" for cp]
                          X64_H.maskCapRights_def
                   split: arch_capability.split_asm)
    apply (clarsimp simp: null_def neq_Nil_conv mask_def field_simps
                          asid_low_bits_word_bits asidInvalid_def
                   dest!: filter_eq_ConsD)
    apply (subst is_aligned_add_less_t2n[rotated], assumption+)
       apply (simp add: asid_low_bits_def asid_bits_def)
      apply (simp add: asid_wf_def)
     apply simp
    apply (auto simp: ct_in_state'_def valid_tcb_state'_def
               dest!: st_tcb_at_idle_thread'
               elim!: pred_tcb'_weakenE)[1]
  apply (clarsimp simp: cte_wp_at_ctes_of asidHighBits_handy_convs
                        word_sle_def word_sless_def asidLowBits_handy_convs rf_sr_ksCurThread
                  cong: if_cong)
  apply (clarsimp simp: ccap_relation_isDeviceCap2 objBits_simps
                        archObjSize_def pageBits_def case_bool_If)
  apply (rule conjI)
   (* Is Asid Control Cap *)
   apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def excaps_map_def)
   apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
   apply (frule interpret_excaps_eq[rule_format, where n=1], simp)
   apply (clarsimp simp: mask_def[where n=4] slotcap_in_mem_def
                         ccap_rights_relation_def rightsFromWord_wordFromRights)
   apply (clarsimp simp: asid_high_bits_word_bits split: list.split_asm)
    apply (clarsimp simp: cap_untyped_cap_lift_def cap_lift_untyped_cap
                          cap_to_H_def[split_simps cap_CL.split]
                          hd_conv_nth length_ineq_not_Nil Kernel_C_defs
                   elim!: ccap_relationE)
   apply (clarsimp simp: to_bool_def unat_eq_of_nat
                         objBits_simps archObjSize_def pageBits_def case_bool_If
                  split: if_splits)
  apply (clarsimp simp: asid_low_bits_word_bits isCap_simps neq_Nil_conv
                        excaps_map_def excaps_in_mem_def
                        p2_gt_0[where 'a=machine_word_len, folded word_bits_def])
  apply (drule_tac t="cteCap cte" in sym, simp)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(13))
  apply (frule ctes_of_valid', clarsimp)
  apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (rule conjI)
   apply (clarsimp simp: cap_lift_asid_pool_cap cap_lift_page_directory_cap
                         cap_to_H_def valid_cap'_def
                         cap_page_directory_cap_lift_def
                         cap_asid_pool_cap_lift_def mask_def
                         asid_shiftr_low_bits_less[unfolded mask_def asid_bits_def] word_and_le1
                  elim!: ccap_relationE split: if_split_asm)
   apply (clarsimp split: list.split)
  apply (clarsimp simp: cap_lift_asid_pool_cap cap_lift_page_directory_cap
                        cap_to_H_def cap_page_directory_cap_lift_def
                 elim!: ccap_relationE split: if_split_asm)
  apply (erule rf_sr_cte_at_validD[rotated])
  apply (fastforce simp: slotcap_in_mem_def2)
  done

lemma ucast_ucast_first_port_is_ucast:
  "cap_lift y = Some (Cap_io_port_cap x) \<Longrightarrow> UCAST(16 \<rightarrow> 32) (UCAST(64 \<rightarrow> 16) (capIOPortFirstPort_CL x))
          = UCAST(64 \<rightarrow> 32) (capIOPortFirstPort_CL x)"
  by (clarsimp simp: cap_lift_def Let_def cap_tag_defs mask_def split: if_split_asm) word_bitwise

lemma ucast_ucast_last_port_is_ucast:
  "cap_lift y = Some (Cap_io_port_cap x) \<Longrightarrow> UCAST(16 \<rightarrow> 32) (UCAST(64 \<rightarrow> 16) (capIOPortLastPort_CL x))
          = UCAST(64 \<rightarrow> 32) (capIOPortLastPort_CL x)"
  by (clarsimp simp: cap_lift_def Let_def cap_tag_defs mask_def split: if_split_asm) word_bitwise

lemma ensurePortOperationAllowed_ccorres:
  "cap = IOPortCap f l \<Longrightarrow> ccorres (syscall_error_rel \<currency> dc)
            (liftxf errstate id (\<lambda>y. ()) ret__unsigned_long_')
            (\<top>)
            (UNIV \<inter> {s. ccap_relation (ArchObjectCap cap) (cap_' s)}
                  \<inter> {s. start_port_' s = ucast start}
                  \<inter> {s. size___unsigned_' s = of_nat magnitude} )
            hs
            (ensurePortOperationAllowed cap start magnitude)
            (Call ensurePortOperationAllowed_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: cap_' start_port_' size___unsigned_')
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply csymbr
   apply csymbr
   apply csymbr
   apply csymbr
   apply csymbr
   apply (rule ccorres_assertE)
   apply (rule ccorres_assertE)
   apply (frule cap_get_tag_isCap_unfolded_H_cap)
   apply (erule ccap_relationE)
   apply (clarsimp simp: cap_to_H_def Let_def cap_io_port_cap_lift_def
                         ucast_ucast_first_port_is_ucast ucast_ucast_last_port_is_ucast whenE_def
                  split: if_split_asm cap_CL.split_asm)
   apply (rule ccorres_add_returnOk)
   apply (rule ccorres_inst[where P=\<top> and P'=UNIV], rule ccorres_guard_imp)
     apply (rule ccorres_Cond_rhs_Seq)
      apply clarsimp
      apply ccorres_rewrite
      apply (rule ccorres_from_vcg_throws[where P'=UNIV and P=\<top>])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: throwError_def return_def syscall_error_rel_def syscall_error_to_H_cases
                            exception_defs)
     apply (clarsimp simp: whenE_def)
     apply (rule ccorres_return_CE)
       apply clarsimp
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply clarsimp
  apply clarsimp
  by (auto dest!: cap_get_tag_isCap_unfolded_H_cap)

lemma setMessageInfo_ksCurThread_ccorres:
  "ccorres dc xfdc (tcb_at' thread and (\<lambda>s. ksCurThread s = thread))
           (UNIV \<inter> \<lbrace>mi = message_info_to_H mi'\<rbrace>) hs
           (setMessageInfo thread mi)
           (\<acute>ret__unsigned_long :== CALL wordFromMessageInfo(mi');;
            CALL setRegister(\<acute>ksCurThread,
                             scast Kernel_C.msgInfoRegister,
                             \<acute>ret__unsigned_long))"
  unfolding setMessageInfo_def
  apply (rule ccorres_guard_imp2)
   apply ctac
     apply simp
     apply (ctac add: setRegister_ccorres)
    apply wp
   apply vcg
  apply (simp add: X64_H.msgInfoRegister_def X64.msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def Kernel_C.RSI_def rf_sr_ksCurThread)
  done

lemma invokeX86PortIn8_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (valid_objs' and ct_in_state' ((=) Restart) and pspace_aligned' and pspace_distinct' and
        (\<lambda>s. ksCurThread s = thread \<and> sch_act_wf (ksSchedulerAction s) s))
       (UNIV \<inter> \<lbrace>\<acute>invLabel = scast Kernel_C.X86IOPortIn8\<rbrace>
             \<inter> \<lbrace>\<acute>port = port\<rbrace>
             \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>)
       hs
       (doE reply \<leftarrow> performX64PortInvocation (InvokeIOPort (IOPortInvocation port IOPortIn8));
           liftE (replyOnRestart thread reply isCall) odE)
       (Call invokeX86PortIn_'proc)"
  supply if_cong[cong]
  apply (clarsimp simp: performX64PortInvocation_def portIn_def liftE_bindE bind_assoc Let_def)
  apply (cinit' lift: invLabel_' port_' call_')
   apply (clarsimp simp: n_msgRegisters_def)
   apply ccorres_rewrite
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=thread_' in ccorres_abstract, ceqv)
     apply (rename_tac cthread)
     apply (rule_tac P="cthread = tcb_ptr_to_ctcb_ptr thread" in ccorres_gen_asm2)
     apply (rule ccorres_rhs_assoc)+
     apply (ctac add: in8_ccorres)
       apply csymbr
       apply (rule ccorres_Cond_rhs_Seq[rotated]; clarsimp)
        apply (simp add: replyOnRestart_def liftE_def bind_assoc)
        apply (rule getThreadState_ccorres_foo, rename_tac tstate)
        apply (rule_tac P="tstate = Restart" in ccorres_gen_asm)
        apply clarsimp
        apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
        apply (ctac (no_vcg) add: setThreadState_ccorres)
         apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
         apply clarsimp
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply (rule hoare_TrueI[of \<top>])
       apply (rule ccorres_rhs_assoc)+
       apply (clarsimp simp: replyOnRestart_def liftE_def bind_assoc)
       apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
       apply (rule getThreadState_ccorres_foo, rename_tac tstate)
       apply (rule_tac P="tstate = Restart" in ccorres_gen_asm)
       apply (clarsimp simp: bind_assoc)
       apply (simp add: replyFromKernel_def bind_assoc)
       apply (ctac add: lookupIPCBuffer_ccorres)
         apply (ctac add: setRegister_ccorres)
           apply (simp add: setMRs_single)
           apply (ctac add: setMR_as_setRegister_ccorres[where offset=0])
             apply clarsimp
             apply csymbr
             apply (simp only: setMessageInfo_def bind_assoc)
             apply ctac
               apply simp
               apply (ctac add: setRegister_ccorres)
                 apply (ctac add: setThreadState_ccorres)
                   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
                   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                   apply (rule allI, rule conseqPre, vcg)
                   apply (clarsimp simp: return_def)
                  apply (rule hoare_TrueI[of \<top>])
                 apply (vcg exspec=setThreadState_modifies)
                apply wpsimp
               apply (vcg exspec=setRegister_modifies)
              apply wpsimp
             apply clarsimp
             apply (vcg)
            apply wpsimp
           apply (clarsimp simp: msgInfoRegister_def X64.msgInfoRegister_def
                                 Kernel_C.msgInfoRegister_def)
           apply (vcg exspec=setMR_modifies)
          apply wpsimp
         apply clarsimp
         apply (vcg exspec=setRegister_modifies)
        apply wpsimp
       apply clarsimp
       apply (vcg exspec=lookupIPCBuffer_modifies)
      apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift)
     apply (vcg exspec=in8_modifies)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  by (auto simp: ct_in_state'_def pred_tcb_at'_def obj_at'_def projectKOs
                 ThreadState_defs mask_def rf_sr_ksCurThread
                 X64_H.badgeRegister_def X64.badgeRegister_def "StrictC'_register_defs"
                 X64.capRegister_def msgRegisters_unfold message_info_to_H_def
                 msgRegisters_ccorres[where n=0, simplified n_msgRegisters_def,
                                      simplified, symmetric])

lemma invokeX86PortIn16_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (valid_objs' and ct_in_state' ((=) Restart) and pspace_aligned' and pspace_distinct' and
        (\<lambda>s. ksCurThread s = thread \<and> sch_act_wf (ksSchedulerAction s) s))
       (UNIV \<inter> \<lbrace>\<acute>invLabel = scast Kernel_C.X86IOPortIn16\<rbrace>
             \<inter> \<lbrace>\<acute>port = port\<rbrace>
             \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>)
       hs
       (doE reply \<leftarrow> performX64PortInvocation (InvokeIOPort (IOPortInvocation port IOPortIn16));
           liftE (replyOnRestart thread reply isCall) odE)
       (Call invokeX86PortIn_'proc)"
  supply if_cong[cong]
  apply (clarsimp simp: performX64PortInvocation_def portIn_def liftE_bindE bind_assoc Let_def)
  apply (cinit' lift: invLabel_' port_' call_')
   apply (clarsimp simp: n_msgRegisters_def arch_invocation_label_defs)
   apply ccorres_rewrite
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=thread_' in ccorres_abstract, ceqv)
     apply (rename_tac cthread)
     apply (rule_tac P="cthread = tcb_ptr_to_ctcb_ptr thread" in ccorres_gen_asm2)
     apply (rule ccorres_rhs_assoc)+
     apply (ctac add: in16_ccorres)
       apply csymbr
       apply (rule ccorres_Cond_rhs_Seq[rotated]; clarsimp)
        apply (simp add: replyOnRestart_def liftE_def bind_assoc)
        apply (rule getThreadState_ccorres_foo, rename_tac tstate)
        apply (rule_tac P="tstate = Restart" in ccorres_gen_asm)
        apply clarsimp
        apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
        apply (ctac (no_vcg) add: setThreadState_ccorres)
         apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
         apply clarsimp
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply (rule hoare_TrueI[of \<top>])
       apply (rule ccorres_rhs_assoc)+
       apply (clarsimp simp: replyOnRestart_def liftE_def bind_assoc)
       apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
       apply (rule getThreadState_ccorres_foo, rename_tac tstate)
       apply (rule_tac P="tstate = Restart" in ccorres_gen_asm)
       apply (clarsimp simp: bind_assoc)
       apply (simp add: replyFromKernel_def bind_assoc)
       apply (ctac add: lookupIPCBuffer_ccorres)
         apply (ctac add: setRegister_ccorres)
           apply (simp add: setMRs_single)
           apply (ctac add: setMR_as_setRegister_ccorres[where offset=0])
             apply clarsimp
             apply csymbr
             apply (simp only: setMessageInfo_def bind_assoc)
             apply ctac
               apply simp
               apply (ctac add: setRegister_ccorres)
                 apply (ctac add: setThreadState_ccorres)
                   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
                   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                   apply (rule allI, rule conseqPre, vcg)
                   apply (clarsimp simp: return_def)
                  apply (rule hoare_TrueI[of \<top>])
                 apply (vcg exspec=setThreadState_modifies)
                apply wpsimp
               apply (vcg exspec=setRegister_modifies)
              apply wpsimp
             apply clarsimp
             apply (vcg)
            apply wpsimp
           apply (clarsimp simp: msgInfoRegister_def X64.msgInfoRegister_def
                                 Kernel_C.msgInfoRegister_def)
           apply (vcg exspec=setMR_modifies)
          apply wpsimp
         apply clarsimp
         apply (vcg exspec=setRegister_modifies)
        apply wpsimp
       apply clarsimp
       apply (vcg exspec=lookupIPCBuffer_modifies)
      apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift)
     apply (vcg exspec=in16_modifies)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  by (auto simp: ct_in_state'_def pred_tcb_at'_def obj_at'_def projectKOs
                 ThreadState_defs mask_def rf_sr_ksCurThread
                 X64_H.badgeRegister_def X64.badgeRegister_def "StrictC'_register_defs"
                 X64.capRegister_def msgRegisters_unfold message_info_to_H_def
                 msgRegisters_ccorres[where n=0, simplified n_msgRegisters_def,
                                      simplified, symmetric])

lemma invokeX86PortIn32_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (valid_objs' and ct_in_state' ((=) Restart) and pspace_aligned' and pspace_distinct' and
        (\<lambda>s. ksCurThread s = thread \<and> sch_act_wf (ksSchedulerAction s) s))
       (UNIV \<inter> \<lbrace>\<acute>invLabel = scast Kernel_C.X86IOPortIn32\<rbrace>
             \<inter> \<lbrace>\<acute>port = port\<rbrace>
             \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>)
       hs
       (doE reply \<leftarrow> performX64PortInvocation (InvokeIOPort (IOPortInvocation port IOPortIn32));
           liftE (replyOnRestart thread reply isCall) odE)
       (Call invokeX86PortIn_'proc)"
  supply if_cong[cong]
  apply (clarsimp simp: performX64PortInvocation_def portIn_def liftE_bindE bind_assoc Let_def)
  apply (cinit' lift: invLabel_' port_' call_')
   apply (clarsimp simp: n_msgRegisters_def arch_invocation_label_defs)
   apply ccorres_rewrite
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=thread_' in ccorres_abstract, ceqv)
     apply (rename_tac cthread)
     apply (rule_tac P="cthread = tcb_ptr_to_ctcb_ptr thread" in ccorres_gen_asm2)
     apply (ctac add: in32_ccorres)
       apply (rule ccorres_Cond_rhs_Seq[rotated]; clarsimp)
        apply (simp add: replyOnRestart_def liftE_def bind_assoc)
        apply (rule getThreadState_ccorres_foo, rename_tac tstate)
        apply (rule_tac P="tstate = Restart" in ccorres_gen_asm)
        apply clarsimp
        apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
        apply (ctac (no_vcg) add: setThreadState_ccorres)
         apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
         apply clarsimp
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply (rule hoare_TrueI[of \<top>])
       apply (rule ccorres_rhs_assoc)+
       apply (clarsimp simp: replyOnRestart_def liftE_def bind_assoc)
       apply (rule_tac P="\<lambda>s. ksCurThread s = thread" in ccorres_cross_over_guard)
       apply (rule getThreadState_ccorres_foo, rename_tac tstate)
       apply (rule_tac P="tstate = Restart" in ccorres_gen_asm)
       apply (clarsimp simp: bind_assoc)
       apply (simp add: replyFromKernel_def bind_assoc)
       apply (ctac add: lookupIPCBuffer_ccorres)
         apply (ctac add: setRegister_ccorres)
           apply (simp add: setMRs_single)
           apply (ctac add: setMR_as_setRegister_ccorres[where offset=0])
             apply clarsimp
             apply csymbr
             apply (simp only: setMessageInfo_def bind_assoc)
             apply ctac
               apply simp
               apply (ctac add: setRegister_ccorres)
                 apply (ctac add: setThreadState_ccorres)
                   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
                   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                   apply (rule allI, rule conseqPre, vcg)
                   apply (clarsimp simp: return_def)
                  apply (rule hoare_TrueI[of \<top>])
                 apply (vcg exspec=setThreadState_modifies)
                apply wpsimp
               apply (vcg exspec=setRegister_modifies)
              apply wpsimp
             apply clarsimp
             apply (vcg)
            apply wpsimp
           apply (clarsimp simp: msgInfoRegister_def X64.msgInfoRegister_def
                                 Kernel_C.msgInfoRegister_def)
           apply (vcg exspec=setMR_modifies)
          apply wpsimp
         apply clarsimp
         apply (vcg exspec=setRegister_modifies)
        apply wpsimp
       apply clarsimp
       apply (vcg exspec=lookupIPCBuffer_modifies)
      apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift)
     apply (vcg exspec=in32_modifies)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  by (auto simp: ct_in_state'_def pred_tcb_at'_def obj_at'_def projectKOs
                 ThreadState_defs mask_def rf_sr_ksCurThread
                 X64_H.badgeRegister_def X64.badgeRegister_def "StrictC'_register_defs"
                 X64.capRegister_def msgRegisters_unfold message_info_to_H_def
                 msgRegisters_ccorres[where n=0, simplified n_msgRegisters_def,
                                      simplified, symmetric])

lemma invokeX86PortOut8_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
       invs'
       (UNIV \<inter> \<lbrace>\<acute>invLabel = scast Kernel_C.X86IOPortOut8\<rbrace>
             \<inter> \<lbrace>\<acute>port = port\<rbrace>
             \<inter> \<lbrace>\<acute>data___unsigned = ucast data\<rbrace>)
       hs
       (performX64PortInvocation (InvokeIOPort (IOPortInvocation port (IOPortOut8 data))))
       (Call invokeX86PortOut_'proc)"
  apply (cinit lift: invLabel_' port_' data___unsigned_' simp: portOut_def liftE_def return_returnOk)
   apply (clarsimp, ccorres_rewrite)
   apply (ctac (no_vcg) add: out8_ccorres)
    apply (rule ccorres_return_CE, simp+)[1]
   apply wp
  apply clarsimp
  done

lemma invokeX86PortOut16_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
       invs'
       (UNIV \<inter> \<lbrace>\<acute>invLabel = scast Kernel_C.X86IOPortOut16\<rbrace>
             \<inter> \<lbrace>\<acute>port = port\<rbrace>
             \<inter> \<lbrace>\<acute>data___unsigned = ucast data\<rbrace>)
       hs
       (performX64PortInvocation (InvokeIOPort (IOPortInvocation port (IOPortOut16 data))))
       (Call invokeX86PortOut_'proc)"
  apply (cinit lift: invLabel_' port_' data___unsigned_' simp: portOut_def liftE_def return_returnOk)
   apply (clarsimp simp:arch_invocation_label_defs, ccorres_rewrite)
   apply (ctac (no_vcg) add: out16_ccorres)
    apply (rule ccorres_return_CE, simp+)[1]
   apply wp
  apply clarsimp
  done

lemma invokeX86PortOut32_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
       invs'
       (UNIV \<inter> \<lbrace>\<acute>invLabel = scast Kernel_C.X86IOPortOut32\<rbrace>
             \<inter> \<lbrace>\<acute>port = port\<rbrace>
             \<inter> \<lbrace>\<acute>data___unsigned = ucast data\<rbrace>)
       hs
       (performX64PortInvocation (InvokeIOPort (IOPortInvocation port (IOPortOut32 data))))
       (Call invokeX86PortOut_'proc)"
  apply (cinit lift: invLabel_' port_' data___unsigned_' simp: portOut_def liftE_def return_returnOk)
   apply (clarsimp simp:arch_invocation_label_defs, ccorres_rewrite)
   apply (ctac (no_vcg) add: out32_ccorres)
    apply (rule ccorres_return_CE, simp+)[1]
   apply wp
  apply clarsimp
  done

lemma setIOPortMask_valid_mdb'[wp]:
  "\<lbrace>valid_mdb'\<rbrace> setIOPortMask f l b \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  by (wpsimp simp: setIOPortMask_def valid_mdb'_def)

lemma invokeX86PortControl_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (cintr \<currency> (\<lambda>rv rv'. rv = [])) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' src and K (f \<le> l))
       (UNIV \<inter> \<lbrace>\<acute>first_port = f\<rbrace> \<inter> \<lbrace>\<acute>last_port = l\<rbrace>
             \<inter> \<lbrace>\<acute>ioportSlot = cte_Ptr dest\<rbrace>
             \<inter> \<lbrace>\<acute>controlSlot = cte_Ptr src\<rbrace>)
       hs
       (performX64PortInvocation (InvokeIOPortControl (IOPortControlIssue f l dest src)))
       (Call invokeX86PortControl_'proc)"
  apply (clarsimp simp: isCap_simps performX64PortInvocation_def Let_def)
  apply (cinit' lift: first_port_' last_port_' ioportSlot_' controlSlot_')
   apply (clarsimp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Guard_Seq)
   apply (clarsimp simp: liftE_def bind_assoc return_returnOk)
   apply (rule ccorres_stateAssert)
   apply (ctac add: setIOPortMask_ccorres)
     apply csymbr
     apply (ctac(no_vcg) add: cteInsert_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply wp
    apply wp
   apply (vcg exspec=setIOPortMask_modifies)
  apply (clarsimp simp: is_simple_cap'_def isCap_simps invs_mdb' invs_valid_objs' invs_pspace_aligned'
                        invs_pspace_canonical' valid_cap_simps' capAligned_def word_bits_def)
  apply (rule conjI)
   apply (clarsimp simp: cap_io_port_cap_lift ccap_relation_def cap_to_H_def mask_def)
   apply word_bitwise
  apply (clarsimp simp: rf_sr_def cstate_relation_def carch_state_relation_def
                        global_ioport_bitmap_relation_def Let_def typ_heap_simps)
  done

(* FIXME X64: move to state rel? *)
abbreviation
  "x86KSAllocatedIOPorts_ptr == ioport_table_Ptr (symbol_table ''x86KSAllocatedIOPorts'')"

lemma first_last_highbits_eq_port_set:
  fixes f l :: "16 word"
  fixes arr :: "machine_word[1024]"
  shows "\<lbrakk>unat f \<le> unat l; unat (f && 0x3F) \<le> unat (l && 0x3F);
          unat (f >> 6) = unat (l >> 6);
          0 < unat (arr.[unat (l >> 6)] && mask (Suc (unat (l && 0x3F)))
                  && ~~ mask (unat (f && 0x3F)))\<rbrakk>
         \<Longrightarrow> \<exists>port::16 word.
                unat f \<le> unat port \<and> unat port \<le> unat l
              \<and> arr.[unat (port >> 6)] !! unat (port && 0x3F)"
  apply (frule word_exists_nth[OF word_neq_0_conv[THEN iffD2], OF unat_less_impl_less, simplified],
                clarsimp simp: word_size)
  apply (rule_tac x="(l && ~~ mask 6) + of_nat i" in exI)
  apply (clarsimp simp: neg_mask_test_bit mask_def[where n=6, simplified, symmetric])
  apply (frule test_bit_size, clarsimp simp: word_size less_Suc_eq_le)
  apply (frule_tac n=i in word_of_nat_less[where x=64 and 'a=16, simplified])
  apply (rule conjI)
   subgoal for i
     (* f \<le> port *)
     apply (frule_tac n=i in word_of_nat_less[where x=64 and 'a=16, simplified])
     apply (subst AND_NOT_mask_plus_AND_mask_eq[symmetric, where n=6])
     apply (subst unat_plus_simple[THEN iffD1])
      apply (clarsimp simp: AND_NOT_mask_plus_AND_mask_eq word_and_le2)
     apply (subst unat_plus_simple[THEN iffD1])
      apply (rule word_random[where x'="2^6 - 1"], rule is_aligned_no_overflow', simp)
      apply (rule word_less_sub_1, simp)
     by (simp add: unat_of_nat word_shiftr_eq_mask)
  apply (rule conjI)
   subgoal for i
     (* port \<le> l *)
     apply (subgoal_tac "(((l && ~~ mask 6) + of_nat i) >> 6) = l >> 6")
      apply (frule_tac w1="f" in word_le_split_mask[where n=6, THEN iffD1, OF word_le_nat_alt[THEN iffD2]])
      apply (erule disjE)
       apply clarsimp
      apply (rule iffD1[OF word_le_nat_alt])
      apply (rule word_le_split_mask[where n=6, THEN iffD2])
      apply clarsimp
      apply (subst mask_eqs(1)[symmetric])
      apply (simp add: mask_AND_NOT_mask)
      apply (subst and_mask_eq_iff_le_mask[THEN iffD2])
       apply (clarsimp simp add: mask_def dest!: word_less_sub_1)
      apply (clarsimp simp: word_le_nat_alt unat_of_nat)
     by (simp add: aligned_shift')
  subgoal for i
    (* arr set *)
    apply (simp add: aligned_shift')
    apply (subst mask_eqs(1)[symmetric])
    apply (simp add: mask_AND_NOT_mask)
    apply (subst and_mask_eq_iff_le_mask[THEN iffD2])
     apply (clarsimp simp add: mask_def dest!: word_less_sub_1)
    by (simp add: unat_of_nat)
  done

lemma port_set_in_first_word:
  fixes f l :: "16 word"
  fixes arr :: "machine_word[1024]"
  shows "\<lbrakk>unat f \<le> unat l; unat (f >> 6) < unat (l >> 6);
           0 < unat (arr.[unat (f >> 6)] && ~~ mask (unat (f && mask 6)))\<rbrakk>
       \<Longrightarrow> \<exists>port::16 word. unat f \<le> unat port \<and> unat port \<le> unat l \<and>
              arr.[unat (port >> 6)] !! unat (port && mask 6)"
  apply (frule word_exists_nth[OF word_neq_0_conv[THEN iffD2], OF unat_less_impl_less, simplified],
                clarsimp simp: word_size)
  apply (rule_tac x="(f && ~~ mask 6) + of_nat i" in exI)
  apply (frule test_bit_size, clarsimp simp: word_size)
  apply (frule_tac n=i in word_of_nat_less[where x=64 and 'a=16, simplified])
  apply (rule conjI)
   subgoal for i
     (* f \<le> port *)
     apply (frule_tac n=i in word_of_nat_less[where x=64 and 'a=16, simplified])
     apply (subst AND_NOT_mask_plus_AND_mask_eq[symmetric, where n=6])
     apply (subst unat_plus_simple[THEN iffD1])
      apply (clarsimp simp: AND_NOT_mask_plus_AND_mask_eq word_and_le2)
     apply (subst unat_plus_simple[THEN iffD1])
      apply (rule word_random[where x'="2^6 - 1"], rule is_aligned_no_overflow', simp)
      apply (rule word_less_sub_1, simp)
     by (simp add: unat_of_nat)
  apply (rule conjI)
   subgoal for i
     (* port \<le> l *)
     apply (subgoal_tac "(((f && ~~ mask 6) + of_nat i) >> 6) = f >> 6")
      apply (frule_tac w1="f" in word_le_split_mask[where n=6, THEN iffD1, OF word_le_nat_alt[THEN iffD2]])
      apply (erule disjE)
       apply (rule iffD1[OF word_le_nat_alt])
       apply (rule word_le_split_mask[where n=6, THEN iffD2])
       apply clarsimp
      apply clarsimp
     by (simp add: aligned_shift')
  subgoal for i
    (* arr set *)
    apply (simp add: aligned_shift')
    apply (subst mask_eqs(1)[symmetric])
    apply (simp add: mask_AND_NOT_mask)
    apply (subst and_mask_eq_iff_le_mask[THEN iffD2])
     apply (clarsimp simp add: mask_def dest!: word_less_sub_1)
    by (simp add: unat_of_nat)
  done

lemma bitmap_word_zero_no_bits_set1:
  fixes f l :: "16 word"
  fixes arr :: "machine_word[1024]"
  shows "\<lbrakk>unat (f && mask 6) \<le> unat (l && mask 6);
        unat (f >> 6) = unat (l >> 6);
        arr.[unat (l >> 6)] && mask (Suc (unat (l && mask 6))) &&
              ~~ mask (unat (f && mask 6)) = 0\<rbrakk>
   \<Longrightarrow> \<forall>port::16 word.
        unat f \<le> unat port \<and> unat port \<le> unat l \<longrightarrow>
        \<not>arr.[unat (port >> 6)] !! unat (port && mask 6)"
  apply clarsimp
  apply (drule word_not_exists_nth)
  apply (simp only: all_nat_less_eq)
  apply (cut_tac w=port in unat_and_mask_less_2p[of 6, simplified mask_def, simplified]; simp)
  apply (drule_tac x="unat (port && 0x3F)" in bspec, clarsimp)
  apply (frule_tac v1=port in word_le_split_mask[where n=6, THEN iffD1, OF word_le_nat_alt[THEN iffD2]])
  apply (frule_tac w1=port in word_le_split_mask[where n=6, THEN iffD1, OF word_le_nat_alt[THEN iffD2]])
  apply (subgoal_tac "port >> 6 = l >> 6")
   apply (clarsimp simp: word_size neg_mask_test_bit not_less not_le)
   apply (clarsimp simp: word_le_nat_alt mask_def min_def split: if_split_asm)
  apply (erule disjE; clarsimp simp:word_less_nat_alt)
  done

lemma bitmap_word_zero_no_bits_set2:
  fixes f l :: "16 word"
  fixes arr :: "machine_word[1024]"
  shows "\<lbrakk>unat f \<le> unat l; unat (f >> 6) < unat (l >> 6);
        arr.[unat (f >> 6)] && ~~ mask (unat (f && mask 6)) = 0\<rbrakk>
            \<Longrightarrow> \<forall>port::16 word. unat f \<le> unat port \<and>
                   unat port < unat (UCAST(16 \<rightarrow> 32 signed) ((f >> 6) + 1) << 6) \<longrightarrow>
        \<not>arr.[unat (port >> 6)] !! unat (port && mask 6)"
  apply (clarsimp simp: word_le_nat_alt[symmetric] word_less_nat_alt[symmetric] ucast_shiftl_6_absorb)
  apply (frule (1) word_highbits_bounded_highbits_eq)
  apply simp
  apply (frule_tac v1=port in word_le_split_mask[where n=6, THEN iffD1])
  apply (erule disjE; clarsimp)
  apply (drule word_not_exists_nth)
  apply (cut_tac w=port in unat_and_mask_less_2p[of 6]; simp)
  apply (drule_tac x="unat (port && mask 6)" in spec, clarsimp simp: neg_mask_test_bit not_le word_le_nat_alt)
  done

lemma isIOPortRangeFree_spec:
  notes ucast_mask = ucast_and_mask[where n=6, simplified mask_def, simplified]
  notes not_max_word_simps = and_not_max_word shiftr_not_max_word and_mask_not_max_word
  notes ucast_cmp_ucast = ucast_le_ucast ucast_less_ucast_weak
  notes array_assert = array_assertion_shrink_right[OF array_ptr_valid_array_assertionD]
  notes unat_arith_simps' = unat_arith_simps[where 'a=16] unat_arith_simps[where 'a="32 signed"]
  notes word_unat.Rep_inject[simp del] int_unat[simp del]
  defines "port_array s \<equiv> h_val (hrs_mem (t_hrs_' (globals s))) x86KSAllocatedIOPorts_ptr"
  shows
  "\<forall>\<sigma>. \<Gamma> \<turnstile>
    {s. s = \<sigma> \<and> first_port_' s \<le> last_port_' s \<and> s \<Turnstile>\<^sub>c x86KSAllocatedIOPorts_ptr }
      Call isIOPortRangeFree_'proc
    {t. globals t = globals \<sigma> \<and>
        ret__unsigned_long_' t = from_bool
          (\<forall>port. first_port_' \<sigma> \<le> port \<and> port \<le> last_port_' \<sigma>
                   \<longrightarrow> \<not> port_array \<sigma>.[unat (port >> wordRadix)] !! unat (port && mask wordRadix))}"
  apply (rule allI)
  subgoal for \<sigma>
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (simp add: scast_ucast_up_eq_ucast word_upcast_shiftr[symmetric] ucast_mask[symmetric]
                   word_upcast_0_sle)
  apply (subst whileAnno_subst_invariant
                 [where I="{s. globals s = globals \<sigma>
                             \<and> first_port_' \<sigma> \<le> last_port_' \<sigma>
                             \<and> \<sigma> \<Turnstile>\<^sub>c x86KSAllocatedIOPorts_ptr
                             \<and> ucast (first_port_' \<sigma> >> wordRadix) < low_word_' s
                             \<and> low_word_' s <= high_word_' s
                             \<and> high_word_' s = ucast (last_port_' \<sigma> >> wordRadix)
                             \<and> high_index_' s = ucast (last_port_' \<sigma> && mask wordRadix)
                             \<and> (\<forall>port. first_port_' \<sigma> \<le> port \<and> ucast port < low_word_' s << wordRadix
                                        \<longrightarrow> \<not> port_array \<sigma>.[unat (port >> wordRadix)]
                                                !! unat (port && mask wordRadix))}"])
  apply (simp add: port_array_def)
  apply (rule conseqPre, vcg)
    apply (all \<open>clarsimp simp: hrs_simps from_bool_0 wordRadix_def is_up is_down
                               unat_ucast_upcast uint_up_ucast sint_ucast_eq_uint up_ucast_inj_eq
                               not_max_word_simps[THEN ucast_increment]
                               ucast_cmp_ucast ucast_cmp_ucast[where 'a=16 and y="0x40", simplified]\<close>)
    subgoal for mem htd first_port last_port low_word
      (* Loop invariant is preserved. *)
      apply (frule neg_msb_le_mono[OF _ word_upcast_neg_msb], simp)
      apply (simp add: word_sless_iff_less word_sle_iff_le word_upcast_neg_msb
                       Most_significant_bit.sint_eq_uint)
      apply (frule less_le_trans[OF _ ucast_le_ucast[THEN iffD2],
                                 OF _ _ shiftr_le_mask[unfolded mask_def]]; simp)
      apply (intro conjI impI allI; (simp add: unat_arith_simps; fail)?)
       apply (drule word_exists_nth; clarsimp)
       subgoal for i
         (* Early return false. *)
         apply (rule_tac x="ucast ((low_word << 6) || of_nat i)" in exI)
         apply (match premises in L: \<open>_ < low_word\<close> and U: \<open>low_word < _\<close> (multi) and V: \<open>test_bit _ _\<close>
                  \<Rightarrow> \<open>match premises in _[thin]: _ (multi) \<Rightarrow> \<open>insert L U V\<close>\<close>)
         apply (frule test_bit_size; simp add: word_size)
         apply (rule revcut_rl[OF shiftl_shiftr_id[of 6 low_word]], simp, fastforce elim: less_trans)
         apply (rule revcut_rl[OF and_mask_eq_iff_le_mask[of low_word 10, THEN iffD2]],
                fastforce simp: mask_def elim: order.trans[where b="0x3FF", OF less_imp_le])
         apply (rule revcut_rl[OF le_mask_iff[of "of_nat i :: 32 signed word" 6, THEN iffD1]],
                fastforce intro: word_of_nat_le simp: mask_def)
         apply (frule and_mask_eq_iff_shiftr_0[where w="of_nat i", THEN iffD2])
         apply (subst mask_eq_ucast_shiftr)
          apply (simp add: word_ao_dist)
          apply (rule arg_cong2[where f=Bit_Operations.or]; rule and_mask_eq_iff_le_mask[THEN iffD2])
           apply (rule le_mask_shiftl_le_mask, simp)
           apply (erule order_trans[where y="0x3FF", OF less_imp_le], simp add: mask_def)
          apply (erule order_trans[OF less_imp_le[OF of_nat_mono_maybe], rotated]; simp add: mask_def)
         apply (simp add: unat_ucast_eq_unat_and_mask ucast_and_mask[symmetric]
                          shiftr_over_or_dist word_ao_dist unat_of_nat_eq word_and_mask_eq_le_mono)
         apply (thin_tac "test_bit _ _")
         apply (rule conjI;
                rule word_le_split_mask[where n=6, THEN iffD2, OF disjI1];
                rule ucast_less_ucast_weak[where 'b="32 signed", THEN iffD1])
         apply (simp_all add: ucast_shiftr ucast_ucast_mask word_ao_dist
                              word_and_mask_eq_le_mono[of "of_nat i"]
                              word_and_mask_eq_le_mono[of low_word]
                              shiftr_over_and_dist shiftr_over_or_dist
                              shiftr_mask2)
         done
      subgoal by uint_arith simp
      subgoal for port
        (* Continue to next loop iteration. *)
        apply (case_tac "ucast port < low_word << 6"; (simp add: unat_arith_simps; fail)?)
        apply (clarsimp simp: not_less)
        apply (subgoal_tac "low_word = ucast (port >> 6)", simp add: unat_arith_simps')
        apply (match premises in L: \<open>low_word << 6 \<le> ucast port\<close> and
                                 U: \<open>ucast port < low_word + 1 << 6\<close> and
                                 T: \<open>low_word < 0x3FF\<close>for port
                 \<Rightarrow> \<open>match premises in _[thin]: _ (multi) \<Rightarrow> \<open>insert T L U\<close>\<close>)
        apply (drule le_shiftr[where n=6 and v="ucast port"],
               drule le_shiftr[where n=6 and u="ucast port", OF word_less_sub_1])
        apply (simp add: word_minus_1_shiftr[OF shiftl_mask_is_0,
                                             OF word_shift_nonzero[where m=10,
                                                                   OF inc_le _ less_is_non_zero_p1,
                                                                   OF less_trans]]
                         shiftl_shiftr_id[OF _ less_trans]
                         shiftl_shiftr_id[OF _ le_less_trans[OF inc_le]]
                         word_upcast_shiftr)
        done
      done
   subgoal for mem htd first_port last_port low_word
     (* Invariant plus loop termination condition is sufficient to establish VCG postcondition. *)
     apply (frule neg_msb_le_mono[OF _ word_upcast_neg_msb], simp)
     apply (simp add: word_sless_iff_less word_sle_iff_le word_upcast_neg_msb
                      Most_significant_bit.sint_eq_uint)
     apply (cut_tac word_and_mask_le_2pm1[of last_port 6], simp)
     apply (cut_tac shiftr_le_mask[of last_port 6, simplified mask_def], simp)
     apply (intro conjI allI impI; (simp add: unat_arith_simps; fail)?)
       subgoal by uint_arith
      apply (drule word_exists_nth; clarsimp simp: word_size ucast_less_ucast_weak)
      subgoal for i
        (* return false. *)
        apply (rule exI[of _ "last_port && ~~ mask 6 || of_nat i"])
        apply (rule revcut_rl[OF le_mask_iff[of "of_nat i :: 16 word" 6, THEN iffD1]],
               fastforce intro: word_of_nat_le simp: mask_def)
        apply (frule and_mask_eq_iff_shiftr_0[where w="of_nat i", THEN iffD2])
        apply (simp add: shiftr_over_or_dist word_ao_dist mask_AND_NOT_mask unat_of_nat_eq)
        apply (rule conjI; rule word_le_split_mask[where n=6, THEN iffD2];
               simp add: ucast_less_ucast_weak shiftr_over_or_dist
                         word_ao_dist mask_AND_NOT_mask)
        apply (rule word_of_nat_le, rule nat_Suc_less_le_imp)
        apply (simp add: unat_arith_simps)
        done
     subgoal for port
       (* return true. *)
       apply (case_tac "ucast port < UCAST (16 \<rightarrow> 32 signed) (last_port >> 6) << 6")
        apply (fastforce simp: unat_arith_simps)
       apply (clarsimp simp: not_less ucast_le_ucast)
       apply (subgoal_tac "port >> 6 = last_port >> 6")
        prefer 2
        apply (drule ucast_mono_le[where 'a="32 signed" and 'b="16"])
         apply (rule order_less_le_trans, rule ucast_less, simp+)
        apply (drule_tac u="ucast _" and v=port and n=6 in le_shiftr)
        apply (clarsimp simp: ucast_shiftr shiftl_shiftr1)
        apply (simp add: shiftl_shiftr1 word_size shiftr_then_mask_commute[where n=6 and m=10, simplified, symmetric]
                         mask_twice ucast_and_mask)
        apply (drule_tac u=port and n=6 in le_shiftr)+
        apply (clarsimp simp add: shiftr_mask_eq' word_size)
       apply (clarsimp simp: word_not_exists_nth)
       apply (drule_tac x="unat (port && mask 6)" and v=0 in word_eqD)
       apply (simp add: word_size unat_and_mask_less_2p[where m=6, simplified])
       apply (simp add: word_less_nat_alt[symmetric])
       apply (erule notE, rule plus_one_helper2)
        apply (subst (asm) word_le_split_mask[where n=6 and v=last_port])+
        apply simp
       apply (simp add: unat_arith_simps)
       done
     done
  subgoal
    (* VCG precondition is sufficient to establish loop invariant. *)
    apply (frule word_le_split_mask[where n=6, THEN iffD1])
    apply (simp add: unat_arith_simps)
    apply (cut_tac unat_shiftr_less_2p[of 6 10 "first_port_' \<sigma>"]; simp)
    apply (cut_tac unat_and_mask_less_2p[of 6 "first_port_' \<sigma>"]; simp)
    apply (cut_tac unat_and_mask_less_2p[of 6 "last_port_' \<sigma>"]; simp)
    apply (simp add: uint_nat mask_def[where n=6] mask_def[where n=64] less_Suc_eq_le Suc_le_eq
                del: Word.of_nat_unat)
    apply (clarsimp intro!: word_less_imp_sless
                      simp: unat_ucast_no_overflow_le word_upcast_neg_msb msb_nth zero_sle_ucast_up
                            is_down unat_eq_0
          | rule conjI
          | erule (2) first_last_highbits_eq_port_set[simplified mask_def[where n=6], simplified]
          | erule (2) port_set_in_first_word[simplified mask_def[where n=6], simplified]
          | solves \<open>drule (2) bitmap_word_zero_no_bits_set1[simplified mask_def[where n=6], simplified],
                     clarsimp\<close>
          | solves \<open>drule (2) bitmap_word_zero_no_bits_set2[simplified mask_def[where n=6], simplified],
                     clarsimp\<close>
          )+
    done
  done
  done

lemma foldl_all_False:
  "(\<not> foldl (\<lambda>b x. b \<or> f x) False xs) = (\<forall>x \<in> set xs. \<not> f x)"
  apply (subst foldl_fun_or_alt)
  apply (fold orList_def)
  apply (simp add: orList_False image_subset_iff)
  done

lemma isIOPortRangeFree_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_'
     (\<lambda>_. f \<le> l)
     (UNIV \<inter> \<lbrace>\<acute>first_port = f\<rbrace> \<inter> \<lbrace>\<acute>last_port = l\<rbrace>)
     hs
     (isIOPortRangeFree f l)
     (Call isIOPortRangeFree_'proc)"
  apply (intro ccorres_from_vcg hoarep_conseq_spec_state[OF isIOPortRangeFree_spec] allI)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                        global_ioport_bitmap_relation_def2
                        isIOPortRangeFree_def gets_def get_def monad_simps in_monad
                intro!: arg_cong[where f=from_bool])
  apply (match premises in H: \<open>cioport_bitmap_to_H _ = _\<close> and O: \<open>first_port_' s \<le> last_port_' s\<close> for s
           \<Rightarrow> \<open>match premises in _[thin]: _(multi) \<Rightarrow> \<open>insert O H\<close>\<close>)
  apply (clarsimp simp: cioport_bitmap_to_H_def wordRadix_def port_mask_def foldl_all_False)
  apply (rule all_cong, drule_tac x=port in fun_cong)
  by simp

lemma decodeIOPortControlInvocation_ccorres:
  notes if_cong[cong] Collect_const[simp del]
  assumes "interpret_excaps extraCaps' = excaps_map extraCaps"
  assumes "isIOPortControlCap cp"
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeX64PortInvocation label args slot cp (map fst extraCaps)
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86PortControlInvocation_'proc)"
   (is "ccorres _ _ ?apre ?cpre _ _ _")
proof -
  from assms show ?thesis
    apply (clarsimp simp: isCap_simps decodeX64PortInvocation_def Let_def)
    apply (cinit' lift: invLabel_' length___unsigned_long_' slot_' current_extra_caps_' cap_' buffer_')
     apply (clarsimp cong: StateSpace.state.fold_congs globals.fold_congs)
     apply (rule ccorres_Cond_rhs_Seq, clarsimp simp: invocation_eq_use_types, ccorres_rewrite)
      apply (rule ccorres_equals_throwError)
       apply (fastforce simp: throwError_bind invocationCatch_def
                       split: invocation_label.splits arch_invocation_label.splits)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (clarsimp simp: syscall_error_to_H_cases)
     apply (clarsimp simp: invocation_eq_use_types)
     apply csymbr
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: word_less_nat_alt throwError_bind invocationCatch_def)
      apply (rule ccorres_cond_true_seq)
      apply (rule ccorres_equals_throwError)
       apply (simp add: throwError_bind split: list.split)
       apply fastforce
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply csymbr
     apply (simp add: interpret_excaps_test_null excaps_map_def)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: throwError_bind invocationCatch_def)
      apply (rule ccorres_equals_throwError)
       apply (fastforce simp: throwError_bind split: list.split)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply ccorres_rewrite
     apply (frule (1) unat_length_4_helper)
     apply (clarsimp simp: neq_Nil_conv)
     apply (rule ccorres_add_return,
                  ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=0])
       apply csymbr
       apply (rule ccorres_add_return,
                    ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=1])
         apply csymbr
         apply (rule ccorres_add_return,
                      ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=2])
           apply (rule ccorres_add_return,
                        ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=3])
             apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
             apply (rule ccorres_move_c_guard_cte)
             apply ctac
               apply (rule ccorres_assert2)
               apply (clarsimp simp: first_port_last_port_compare)
               apply (rule ccorres_Cond_rhs_Seq)
                apply (rule ccorres_equals_throwError)
                 apply (fastforce simp: whenE_def throwError_bind invocationCatch_def)
                apply ccorres_rewrite
                apply (rule syscall_error_throwError_ccorres_n)
                apply (clarsimp simp: syscall_error_to_H_cases)
               apply (clarsimp simp: ucast_drop_big_mask)
               apply (clarsimp simp: invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                                     injection_handler_If injection_handler_throwError
                                     injection_liftE[OF refl] injection_handler_returnOk bindE_assoc)
               apply (clarsimp simp: liftE_bindE)
               apply (ctac(no_vcg) add: isIOPortRangeFree_ccorres)
                apply clarsimp
                apply (rule ccorres_Cond_rhs_Seq)
                 apply (clarsimp simp: from_bool_0 injection_handler_throwError)
                 apply ccorres_rewrite
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (clarsimp simp: syscall_error_to_H_cases)
                apply (clarsimp simp: from_bool_neq_0 injection_handler_returnOk)
                apply (ctac add: ccorres_injection_handler_csum1
                                   [OF lookupTargetSlot_ccorres, unfolded lookupTargetSlot_def])
                   apply (simp add: Collect_False split_def)
                   apply csymbr
                   apply (ctac add: ccorres_injection_handler_csum1[OF ensureEmptySlot_ccorres])
                      apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                                       performInvocation_def bindE_assoc X64_H.performInvocation_def)
                      apply ccorres_rewrite
                      apply (rule_tac P="\<lambda>s. thread = ksCurThread s" in ccorres_cross_over_guard)
                      apply (ctac add: setThreadState_ccorres)
                        apply (ctac(no_vcg) add: invokeX86PortControl_ccorres)
                        apply clarsimp
                        apply (rule ccorres_alternative2)
                        apply (rule ccorres_return_CE, simp+)[1]
                        apply (rule ccorres_return_C_errorE, simp+)[1]
                        apply wp
                       apply (wp sts_invs_minor')
                      apply (simp add: Collect_const_mem)
                      apply (vcg exspec=setThreadState_modifies)
                     apply simp
                     apply (rule ccorres_split_throws, ccorres_rewrite)
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                     apply vcg
                    apply (wpsimp wp: injection_wp_E[OF refl])
                   apply (simp add: Collect_const_mem all_ex_eq_helper)
                   apply (vcg exspec=ensureEmptySlot_modifies)
                  apply simp
                  apply (rule ccorres_split_throws, ccorres_rewrite)
                   apply (rule ccorres_return_C_errorE, simp+)[1]
                  apply vcg
                 apply simp
                 apply (wpsimp wp: injection_wp_E[OF refl] hoare_drop_imps)
                apply (simp add: all_ex_eq_helper)
                apply (vcg exspec=lookupTargetSlot_modifies)
               apply (wpsimp wp: isIOPortRangeFree_wp)
              apply (rule_tac Q'="\<lambda>rv. invs' and valid_cap' a and st_tcb_at' runnable' thread
                                      and sch_act_simple and cte_wp_at' \<top> slot
                                      and (\<lambda>s. thread = ksCurThread s)" in hoare_strengthen_post)
               apply (wpsimp wp: getSlotCap_wp)
              apply (clarsimp simp: unat_less_2p_word_bits invs_valid_objs'
                                    valid_tcb_state'_def invs_pspace_aligned' invs_pspace_distinct'
                                    invs_sch_act_wf' st_tcb_strg'[rule_format] st_tcb_at'_def obj_at'_def
                                    projectKOs word_le_not_less
                             split: thread_state.splits)
              apply (case_tac "tcbState obj"; clarsimp)
               apply (drule invs_valid_idle',
                      clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs idle_tcb'_def)+
             apply (simp add: all_ex_eq_helper)
             apply vcg
            apply wp
           apply (simp add: all_ex_eq_helper, vcg exspec=getSyscallArg_modifies)
          apply wp
         apply (simp add: all_ex_eq_helper, vcg exspec=getSyscallArg_modifies)
        apply wp
       apply (simp add: all_ex_eq_helper, vcg exspec=getSyscallArg_modifies)
      apply (rule_tac Q'="\<lambda>rv. ?apre" in hoare_strengthen_post)
       apply wp
      apply (clarsimp simp: sysargs_rel_to_n excaps_in_mem_def slotcap_in_mem_def cte_wp_at_ctes_of
                      interpret_excaps_eq
               dest!: ct_active_runnable')
      apply (clarsimp simp: ct_in_state'_def)
     apply (rule_tac P="UNIV" in conseqPre)
      apply (simp add: all_ex_eq_helper, vcg exspec=getSyscallArg_modifies)
     apply (clarsimp simp: interpret_excaps_eq rf_sr_ksCurThread)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
    apply clarsimp
    apply (rule conjI, clarsimp simp: sysargs_rel_to_n dest!: unat_length_4_helper)
    apply (clarsimp simp: o_def)
    done
qed

lemma unat_length_2_helper:
  "\<lbrakk>unat (l::machine_word) = length args; \<not> l < 2\<rbrakk> \<Longrightarrow> \<exists>x xa xs. args = x#xa#xs"
  apply (case_tac args; clarsimp simp: unat_eq_0)
  by (case_tac list; clarsimp simp: unat_eq_1)

lemma ct_active_st_tcb_at_minor':
  assumes "ct_active' s"
  shows "st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = {} \<and> st' \<noteq> Inactive \<and> st' \<noteq> IdleThreadState) (ksCurThread s) s"
        "st_tcb_at' runnable' (ksCurThread s) s"
   using assms
   by (clarsimp simp: st_tcb_at'_def ct_in_state'_def obj_at'_def projectKOs,
              case_tac "tcbState obj"; clarsimp)+

lemma decodeIOPortInvocation_ccorres:
  notes if_cong[cong]
  assumes "interpret_excaps extraCaps' = excaps_map extraCaps"
  assumes "isIOPortCap cp"
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (decodeX64PortInvocation label args slot cp (map fst extraCaps)
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86PortInvocation_'proc)"
proof -
  from assms show ?thesis
    supply Collect_const[simp del]
    apply (clarsimp simp: isCap_simps decodeX64PortInvocation_def Let_def)
    apply (cinit' lift: invLabel_' length___unsigned_long_' slot_' current_extra_caps_' cap_' buffer_' call_')
     apply (clarsimp cong: StateSpace.state.fold_congs globals.fold_congs)
     apply csymbr
     apply (rule ccorres_Cond_rhs) (* IN invocations *)
      apply (erule ccorres_disj_division)
       \<comment> \<open>In8\<close>
       apply (clarsimp simp: invocation_eq_use_types cong: list.case_cong)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_Cond_rhs_Seq) (* length error *)
        apply (clarsimp simp: throwError_bind invocationCatch_def)
        apply ccorres_rewrite
        apply (rule syscall_error_throwError_ccorres_n)
        apply (clarsimp simp: syscall_error_to_H_cases)
       apply (case_tac args; clarsimp simp: unat_gt_0[symmetric])
       apply (rule ccorres_add_return,
                 ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=0])
         apply csymbr
         apply ccorres_rewrite
         apply (clarsimp simp: invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                               injection_handler_If injection_handler_throwError
                               injection_liftE[OF refl] injection_handler_returnOk bindE_assoc)
         apply (ctac add: ccorres_injection_handler_csum1 [OF ensurePortOperationAllowed_ccorres])
            apply (clarsimp, ccorres_rewrite)
            apply (clarsimp simp: injection_handler_returnOk ccorres_invocationCatch_Inr bindE_assoc returnOk_bind liftE_bindE)
            apply (ctac add: setThreadState_ccorres)
              apply (simp add: X64_H.performInvocation_def performInvocation_def returnOk_bind bindE_assoc)
              apply (rule ccorres_nondet_refinement)
               apply (rule is_nondet_refinement_bindE)
                apply (rule is_nondet_refinement_refl)
               apply (simp split: if_split, rule conjI[rotated])
                apply (rule impI, rule is_nondet_refinement_refl)
               apply (rule impI, rule is_nondet_refinement_alternative1)
              apply (simp add: ucast_mask_drop[where n=16, simplified mask_def, simplified])
              apply (rule ccorres_add_returnOk)
              apply (ctac (no_vcg) add:invokeX86PortIn8_ccorres)
                apply (rule ccorres_return_CE, simp+)[1]
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply wp
             apply (wpsimp wp: ct_in_state'_set sts_valid_objs')
            apply (simp add: Collect_const_mem intr_and_se_rel_def cintr_def exception_defs)
            apply (vcg exspec=setThreadState_modifies)
           apply clarsimp
           apply ccorres_rewrite
           apply (rule ccorres_return_C_errorE, simp+)[1]
          apply (wpsimp wp: injection_wp_E[where f=Inl])
         apply (vcg exspec=ensurePortOperationAllowed_modifies)
        apply wpsimp
       apply (vcg exspec=getSyscallArg_modifies)
      apply (erule ccorres_disj_division)
       \<comment> \<open>In16\<close>
       apply (clarsimp simp: invocation_eq_use_types cong: list.case_cong)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_Cond_rhs_Seq) (* length error *)
        apply (clarsimp simp: throwError_bind invocationCatch_def)
        apply ccorres_rewrite
        apply (rule syscall_error_throwError_ccorres_n)
        apply (clarsimp simp: syscall_error_to_H_cases)
       apply (case_tac args; clarsimp simp: unat_gt_0[symmetric])
       apply (rule ccorres_add_return,
                 ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=0])
         apply csymbr
         apply ccorres_rewrite
         apply (clarsimp simp: invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                               injection_handler_If injection_handler_throwError
                               injection_liftE[OF refl] injection_handler_returnOk bindE_assoc)
         apply (ctac add: ccorres_injection_handler_csum1 [OF ensurePortOperationAllowed_ccorres])
            apply (clarsimp, ccorres_rewrite)
            apply (clarsimp simp: injection_handler_returnOk ccorres_invocationCatch_Inr bindE_assoc returnOk_bind liftE_bindE)
            apply (ctac add: setThreadState_ccorres)
              apply (simp add: X64_H.performInvocation_def performInvocation_def returnOk_bind bindE_assoc)
              apply (rule ccorres_nondet_refinement)
               apply (rule is_nondet_refinement_bindE)
                apply (rule is_nondet_refinement_refl)
               apply (simp split: if_split, rule conjI[rotated])
                apply (rule impI, rule is_nondet_refinement_refl)
               apply (rule impI, rule is_nondet_refinement_alternative1)
              apply (simp add: ucast_mask_drop[where n=16, simplified mask_def, simplified])
              apply (rule ccorres_add_returnOk)
              apply (ctac (no_vcg) add:invokeX86PortIn16_ccorres)
                apply (rule ccorres_return_CE, simp+)[1]
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply wp
             apply (wpsimp wp: ct_in_state'_set sts_valid_objs')
            apply (simp add: Collect_const_mem intr_and_se_rel_def cintr_def exception_defs)
            apply (vcg exspec=setThreadState_modifies)
           apply clarsimp
           apply ccorres_rewrite
           apply (rule ccorres_return_C_errorE, simp+)[1]
          apply (wpsimp wp: injection_wp_E[where f=Inl])
         apply (vcg exspec=ensurePortOperationAllowed_modifies)
        apply wpsimp
       apply (vcg exspec=getSyscallArg_modifies)
      \<comment> \<open>In32\<close>
      apply (clarsimp simp: invocation_eq_use_types cong: list.case_cong)
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_Cond_rhs_Seq) (* length error *)
       apply (clarsimp simp: throwError_bind invocationCatch_def)
       apply ccorres_rewrite
       apply (rule syscall_error_throwError_ccorres_n)
       apply (clarsimp simp: syscall_error_to_H_cases)
      apply (case_tac args; clarsimp simp: unat_gt_0[symmetric])
      apply (rule ccorres_add_return,
                ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=0])
        apply csymbr
        apply ccorres_rewrite
        apply (clarsimp simp: invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                              injection_handler_If injection_handler_throwError
                              injection_liftE[OF refl] injection_handler_returnOk bindE_assoc)
        apply (ctac add: ccorres_injection_handler_csum1 [OF ensurePortOperationAllowed_ccorres])
           apply (clarsimp, ccorres_rewrite)
           apply (clarsimp simp: injection_handler_returnOk ccorres_invocationCatch_Inr bindE_assoc returnOk_bind liftE_bindE)
           apply (ctac add: setThreadState_ccorres)
             apply (simp add: X64_H.performInvocation_def performInvocation_def returnOk_bind bindE_assoc)
             apply (rule ccorres_nondet_refinement)
              apply (rule is_nondet_refinement_bindE)
               apply (rule is_nondet_refinement_refl)
              apply (simp split: if_split, rule conjI[rotated])
               apply (rule impI, rule is_nondet_refinement_refl)
         apply (rule impI, rule is_nondet_refinement_alternative1)
             apply (simp add: ucast_mask_drop[where n=16, simplified mask_def, simplified])
             apply (rule ccorres_add_returnOk)
             apply (ctac (no_vcg) add:invokeX86PortIn32_ccorres)
               apply (rule ccorres_return_CE, simp+)[1]
              apply (rule ccorres_return_C_errorE, simp+)[1]
             apply wp
            apply (wpsimp wp: ct_in_state'_set sts_valid_objs')
           apply (simp add: Collect_const_mem intr_and_se_rel_def cintr_def exception_defs)
           apply (vcg exspec=setThreadState_modifies)
          apply clarsimp
          apply ccorres_rewrite
          apply (rule ccorres_return_C_errorE, simp+)[1]
         apply (wpsimp wp: injection_wp_E[where f=Inl])
        apply (vcg exspec=ensurePortOperationAllowed_modifies)
       apply wpsimp
      apply (vcg exspec=getSyscallArg_modifies)
     apply clarsimp
     apply (rule ccorres_Cond_rhs) (* OUT invocations *)
      apply (erule ccorres_disj_division)
       \<comment> \<open>Out8\<close>
       apply (clarsimp simp: invocation_eq_use_types cong: list.case_cong)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_Cond_rhs_Seq) (* length error *)
        apply (rule ccorres_equals_throwError)
         apply (drule x_less_2_0_1, erule disjE;
                      clarsimp simp: throwError_bind invocationCatch_def length_Suc_0_conv
                              dest!: sym[where s="Suc 0"];
                      fastforce)
        apply ccorres_rewrite
        apply (rule syscall_error_throwError_ccorres_n)
        apply (clarsimp simp: syscall_error_to_H_cases)
       apply (frule (1) unat_length_2_helper)
       apply clarsimp
       apply (rule ccorres_add_return,
                 ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=0])
         apply csymbr
         apply (rule ccorres_add_return,
                 ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=1])
           apply csymbr
           apply ccorres_rewrite
           apply (clarsimp simp: invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                               injection_handler_If injection_handler_throwError
                               injection_liftE[OF refl] injection_handler_returnOk bindE_assoc)
           apply (rule ccorres_rhs_assoc)+
           apply (ctac add: ccorres_injection_handler_csum1 [OF ensurePortOperationAllowed_ccorres])
              apply (clarsimp, ccorres_rewrite, csymbr)
              apply (clarsimp simp: injection_handler_returnOk ccorres_invocationCatch_Inr bindE_assoc returnOk_bind liftE_bindE)
              apply (ctac add: setThreadState_ccorres)
                apply (simp add: X64_H.performInvocation_def performInvocation_def returnOk_bind bindE_assoc)
                apply (simp add: ucast_mask_drop[where n=16, simplified mask_def, simplified]
                                 ucast_mask_drop[where n=32, simplified mask_def, simplified])
                apply (ctac add: invokeX86PortOut8_ccorres)
                   apply clarsimp
                   apply (rule ccorres_alternative2)
                   apply (rule ccorres_return_CE, simp+)[1]
                  apply (rule ccorres_return_C_errorE, simp+)[1]
                 apply wp
                apply (vcg exspec=invokeX86PortOut_modifies)
               apply (wp sts_invs_minor')
              apply (vcg exspec=setThreadState_modifies)
             apply (clarsimp, ccorres_rewrite, csymbr)
             apply (rule ccorres_return_C_errorE, simp+)[1]
            apply (wpsimp wp: injection_wp_E[where f=Inl])
           apply (vcg exspec=ensurePortOperationAllowed_modifies)
          apply wpsimp
         apply (vcg exspec=getSyscallArg_modifies)
        apply wpsimp
       apply (vcg exspec=getSyscallArg_modifies)
      apply (erule ccorres_disj_division)
       \<comment> \<open>Out16\<close>
       apply (clarsimp simp: invocation_eq_use_types cong: list.case_cong)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_Cond_rhs_Seq) (* length error *)
        apply (rule ccorres_equals_throwError)
         apply (drule x_less_2_0_1, erule disjE;
                      clarsimp simp: throwError_bind invocationCatch_def length_Suc_0_conv
                              dest!: sym[where s="Suc 0"];
                      fastforce)
        apply ccorres_rewrite
        apply (rule syscall_error_throwError_ccorres_n)
        apply (clarsimp simp: syscall_error_to_H_cases)
       apply (frule (1) unat_length_2_helper)
       apply clarsimp
       apply (rule ccorres_add_return,
                 ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=0])
         apply csymbr
         apply (rule ccorres_add_return,
                 ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=1])
           apply csymbr
           apply ccorres_rewrite
           apply (clarsimp simp: invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                                 injection_handler_If injection_handler_throwError
                                 injection_liftE[OF refl] injection_handler_returnOk bindE_assoc)
           apply (rule ccorres_rhs_assoc)+
           apply (ctac add: ccorres_injection_handler_csum1 [OF ensurePortOperationAllowed_ccorres])
              apply (clarsimp, ccorres_rewrite, csymbr)
              apply (clarsimp simp: injection_handler_returnOk ccorres_invocationCatch_Inr bindE_assoc returnOk_bind liftE_bindE)
              apply (ctac add: setThreadState_ccorres)
                apply (simp add: X64_H.performInvocation_def performInvocation_def returnOk_bind bindE_assoc)
                apply (simp add: ucast_mask_drop[where n=16, simplified mask_def, simplified]
                                 ucast_mask_drop[where n=32, simplified mask_def, simplified])
                apply (ctac add: invokeX86PortOut16_ccorres)
                   apply clarsimp
                   apply (rule ccorres_alternative2)
                   apply (rule ccorres_return_CE, simp+)[1]
                  apply (rule ccorres_return_C_errorE, simp+)[1]
                 apply wp
                apply (vcg exspec=invokeX86PortOut_modifies)
               apply (wp sts_invs_minor')
              apply (vcg exspec=setThreadState_modifies)
             apply (clarsimp, ccorres_rewrite, csymbr)
             apply (rule ccorres_return_C_errorE, simp+)[1]
            apply (wpsimp wp: injection_wp_E[where f=Inl])
           apply (vcg exspec=ensurePortOperationAllowed_modifies)
          apply wpsimp
         apply (vcg exspec=getSyscallArg_modifies)
        apply wpsimp
       apply (vcg exspec=getSyscallArg_modifies)
       \<comment> \<open>Out32\<close>
      apply (clarsimp simp: invocation_eq_use_types cong: list.case_cong)
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_Cond_rhs_Seq) (* length error *)
       apply (rule ccorres_equals_throwError)
        apply (drule x_less_2_0_1, erule disjE;
                     clarsimp simp: throwError_bind invocationCatch_def length_Suc_0_conv
                             dest!: sym[where s="Suc 0"];
                     fastforce)
       apply ccorres_rewrite
       apply (rule syscall_error_throwError_ccorres_n)
       apply (clarsimp simp: syscall_error_to_H_cases)
      apply (frule (1) unat_length_2_helper)
      apply clarsimp
      apply (rule ccorres_add_return,
                ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=0])
        apply csymbr
        apply (rule ccorres_add_return,
                ctac add: getSyscallArg_ccorres_foo[where args=args and buffer=buffer and n=1])
          apply csymbr
          apply ccorres_rewrite
          apply (clarsimp simp: invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                                injection_handler_If injection_handler_throwError
                                injection_liftE[OF refl] injection_handler_returnOk bindE_assoc)
          apply (rule ccorres_rhs_assoc)+
          apply (ctac add: ccorres_injection_handler_csum1 [OF ensurePortOperationAllowed_ccorres])
             apply (clarsimp, ccorres_rewrite, csymbr)
             apply (clarsimp simp: injection_handler_returnOk ccorres_invocationCatch_Inr bindE_assoc returnOk_bind liftE_bindE)
             apply (ctac add: setThreadState_ccorres)
               apply (simp add: X64_H.performInvocation_def performInvocation_def returnOk_bind bindE_assoc)
               apply (simp add: ucast_mask_drop[where n=16, simplified mask_def, simplified]
                                ucast_mask_drop[where n=32, simplified mask_def, simplified])
               apply (ctac add: invokeX86PortOut32_ccorres)
                  apply clarsimp
                  apply (rule ccorres_alternative2)
                  apply (rule ccorres_return_CE, simp+)[1]
                 apply (rule ccorres_return_C_errorE, simp+)[1]
                apply wp
               apply (vcg exspec=invokeX86PortOut_modifies)
              apply (wp sts_invs_minor')
             apply (vcg exspec=setThreadState_modifies)
            apply (clarsimp, ccorres_rewrite, csymbr)
            apply (rule ccorres_return_C_errorE, simp+)[1]
           apply (wpsimp wp: injection_wp_E[where f=Inl])
          apply (vcg exspec=ensurePortOperationAllowed_modifies)
         apply wpsimp
        apply (vcg exspec=getSyscallArg_modifies)
       apply wpsimp
      apply (vcg exspec=getSyscallArg_modifies)
     apply (clarsimp simp: invocation_eq_use_types)
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: throwError_bind invocationCatch_def
                      split: invocation_label.splits arch_invocation_label.splits)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (clarsimp simp: syscall_error_to_H_cases)
    apply (clarsimp simp: arch_invocation_label_defs sysargs_rel_to_n valid_tcb_state'_def tcb_at_invs'
                          invs_sch_act_wf' ct_active_st_tcb_at_minor' rf_sr_ksCurThread
                          ucast_mask_drop[where n=16, simplified mask_def, simplified])
    apply (safe, simp_all add: unat_eq_0 unat_eq_1)
           apply (clarsimp dest!: unat_length_2_helper simp: syscall_error_rel_def
                                  | (thin_tac "P" for P)+, word_bitwise)+
    done
qed

lemma Mode_decodeInvocation_ccorres:
  assumes "interpret_excaps extraCaps' = excaps_map extraCaps"
  assumes "isPageCap cp \<or> isPageTableCap cp \<or> isPageDirectoryCap cp \<or> isPDPointerTableCap cp \<or> isPML4Cap cp"
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
          >>= invocationCatch thread isBlocking isCall Invocations_H.invocation.InvokeArchObject)
       (Call Mode_decodeInvocation_'proc)"
  using assms
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' slot_'
                      current_extra_caps_' cap_' buffer_' call_')
   apply csymbr
   apply (simp only: cap_get_tag_isCap_ArchObject X64_H.decodeInvocation_def)
   apply (rule ccorres_cond_true)
   apply (rule ccorres_trim_returnE[rotated 2, OF ccorres_call, OF decodeX64MMUInvocation_ccorres], simp+)[1]
  apply (clarsimp simp: o_def)
  done

lemma Arch_decodeInvocation_ccorres:
  notes if_cong[cong]
  assumes "interpret_excaps extraCaps' = excaps_map extraCaps"
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall }) []
       (Arch.decodeInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call Arch_decodeInvocation_'proc)"
  (is "ccorres ?r ?xf ?P (?P' slot_') [] ?a ?c")
proof -
  note trim_call = ccorres_trim_returnE[rotated 2, OF ccorres_call]
  from assms show ?thesis
    apply (cinit' lift: invLabel_' length___unsigned_long_' slot_' current_extra_caps_' cap_' buffer_' call_')
     apply csymbr
     apply (simp only: cap_get_tag_isCap_ArchObject X64_H.decodeInvocation_def)
     apply (rule ccorres_Cond_rhs)
      apply (subgoal_tac "\<not> isIOCap cp", simp)
       apply (rule trim_call[OF decodeX64MMUInvocation_ccorres], simp+)[1]
      apply (fastforce simp: isCap_simps isIOCap_def)
     apply (rule ccorres_Cond_rhs)
      apply (subgoal_tac "isIOCap cp", simp)
       apply (rule trim_call[OF decodeIOPortControlInvocation_ccorres], simp+)[1]
      apply (fastforce simp: isCap_simps isIOCap_def)
     apply (rule ccorres_Cond_rhs)
      apply (subgoal_tac "isIOCap cp", simp)
       apply (rule trim_call[OF decodeIOPortInvocation_ccorres], simp+)[1]
      apply (fastforce simp: isCap_simps isIOCap_def)
     apply (subgoal_tac "\<not> isIOCap cp", simp)
      apply (rule trim_call[OF Mode_decodeInvocation_ccorres])
            apply assumption
           apply (cases cp; simp add: isCap_simps)
          apply simp+
     apply (cases cp; simp add: isCap_simps isIOCap_def)
    apply (clarsimp simp: o_def excaps_in_mem_def slotcap_in_mem_def)
    apply (drule (1) bspec)
    apply (clarsimp simp: ctes_of_valid')
    done
qed

end

end
