(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Arch_C
imports Recycle_C
begin

context begin interpretation Arch . (*FIXME: arch_split*)

crunches unmapPageTable, unmapPageDirectory, unmapPDPT
  for ctes_of[wp]:  "\<lambda>s. P (ctes_of s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject setObject)

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
       (invs' and cte_wp_at' (diminished' (ArchObjectCap cap) \<circ> cteCap) ctSlot
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
          apply(simp only: dc_def[symmetric] bit_simps_corres[symmetric])
          apply (ctac add: clearMemory_setObject_PTE_ccorres)
         apply wp
        apply (simp del: Collect_const)
        apply (vcg exspec=unmapPageTable_modifies)
       apply (simp add: to_bool_def)
       apply (rule ccorres_return_Skip')
      apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
      apply (clarsimp simp: cap_lift_page_table_cap cap_to_H_def
                            cap_page_table_cap_lift_def
                     elim!: ccap_relationE cong: if_cong)
     apply (simp add: liftM_def getSlotCap_def updateCap_def
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule ccorres_getCTE)+
     apply (rule_tac P="cte_wp_at' (op = rv) ctSlot
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
                           typ_heap_simps'
                           cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    dest!: ksPSpace_update_eq_ExD)
    apply (simp add: cte_wp_at_ctes_of)
    apply (wp mapM_x_wp' | wpc | simp)+
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric] cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (frule_tac x=s in fun_cong[OF diminished_valid'])
  apply (frule valid_global_refsD_with_objSize, clarsimp)
  apply (clarsimp simp: cap_lift_page_table_cap cap_to_H_def
                        cap_page_table_cap_lift_def isCap_simps
                        valid_cap'_def get_capSizeBits_CL_def
                        bit_simps capAligned_def
                        to_bool_def mask_def page_table_at'_def
                        capRange_def Int_commute asid_bits_def
                 elim!: ccap_relationE cong: if_cong
                 dest!: diminished_capMaster)
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
   apply (simp add: upto_enum_step_def objBits_simps bit_simps
                    field_simps linorder_not_less[symmetric] archObjSize_def
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
                    typ_heap_simps update_pde_map_tos)
  apply simp
  done

lemma performPageDirectoryInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' (diminished' (ArchObjectCap cap) \<circ> cteCap) ctSlot
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
          apply(simp only: dc_def[symmetric] bit_simps_corres[symmetric])
          apply (ctac add: clearMemory_setObject_PDE_ccorres)
         apply wp
        apply (simp del: Collect_const)
        apply (vcg exspec=unmapPageDirectory_modifies)
       apply (simp add: to_bool_def)
       apply (rule ccorres_return_Skip')
      apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
      apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                            cap_page_directory_cap_lift_def
                     elim!: ccap_relationE cong: if_cong)
     apply (simp add: liftM_def getSlotCap_def updateCap_def
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule ccorres_getCTE)+
     apply (rule_tac P="cte_wp_at' (op = rv) ctSlot
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
                           typ_heap_simps'
                           cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    dest!: ksPSpace_update_eq_ExD)
    apply (simp add: cte_wp_at_ctes_of)
    apply (wp mapM_x_wp' | wpc | simp)+
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric] cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (frule_tac x=s in fun_cong[OF diminished_valid'])
  apply (frule valid_global_refsD_with_objSize, clarsimp)
  apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                        cap_page_directory_cap_lift_def isCap_simps
                        valid_cap'_def get_capSizeBits_CL_def
                        bit_simps capAligned_def
                        to_bool_def mask_def page_directory_at'_def
                        capRange_def Int_commute asid_bits_def
                 elim!: ccap_relationE cong: if_cong
                 dest!: diminished_capMaster)
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
   apply (simp add: upto_enum_step_def objBits_simps bit_simps
                    field_simps linorder_not_less[symmetric] archObjSize_def
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
                    typ_heap_simps update_pdpte_map_tos)
  apply simp
  done

lemma performPDPTInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' (diminished' (ArchObjectCap cap) \<circ> cteCap) ctSlot
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
          apply(simp only: dc_def[symmetric] bit_simps_corres[symmetric])
          apply (ctac add: clearMemory_setObject_PDPTE_ccorres)
         apply wp
        apply (simp del: Collect_const)
        apply (vcg exspec=unmapPDPT_modifies)
       apply (simp add: to_bool_def)
       apply (rule ccorres_return_Skip')
      apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
      apply (clarsimp simp: cap_lift_pdpt_cap cap_to_H_def
                            cap_pdpt_cap_lift_def
                     elim!: ccap_relationE cong: if_cong)
     apply (simp add: liftM_def getSlotCap_def updateCap_def
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule ccorres_getCTE)+
     apply (rule_tac P="cte_wp_at' (op = rv) ctSlot
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
                           typ_heap_simps'
                           cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    dest!: ksPSpace_update_eq_ExD)
    apply (simp add: cte_wp_at_ctes_of)
    apply (wp mapM_x_wp' | wpc | simp)+
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric] cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (frule_tac x=s in fun_cong[OF diminished_valid'])
  apply (frule valid_global_refsD_with_objSize, clarsimp)
  apply (clarsimp simp: cap_lift_pdpt_cap cap_to_H_def
                        cap_pdpt_cap_lift_def isCap_simps
                        valid_cap'_def get_capSizeBits_CL_def
                        bit_simps capAligned_def
                        to_bool_def mask_def pd_pointer_table_at'_def
                        capRange_def Int_commute asid_bits_def
                 elim!: ccap_relationE cong: if_cong
                 dest!: diminished_capMaster)
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

lemma cap_case_PageDirectoryCap2:
  "(case cap of ArchObjectCap (PageDirectoryCap pd mapdata)
                   \<Rightarrow> f pd mapdata | _ \<Rightarrow> g)
   = (if isArchObjectCap cap \<and> isPageDirectoryCap (capCap cap)
      then f (capPDBasePtr (capCap cap)) (capPDMappedAddress (capCap cap))
      else g)"
  by (simp add: isCap_simps
         split: capability.split arch_capability.split)

lemma ap_eq_D:
  "x \<lparr>array_C := arr'\<rparr> = asid_pool_C arr \<Longrightarrow> arr' = arr"
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
   (CALL memzero(Ptr frame, (2 ^ unat X64SmallPageBits));;
   (global_htd_update (\<lambda>_. ptr_retyp (ap_Ptr frame))))"
  sorry (*
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
    apply (clarsimp simp: array_relation_def option_to_ptr_def option_to_0_def)
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
    apply (rule conjI)
     apply (clarsimp simp: update_ti_t_ptr_0s)
    apply (clarsimp simp: asid_low_bits_def word_le_nat_alt)
    done

  def ko \<equiv> "KOArch (KOASIDPool makeObject)"

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
  have mko: "\<And>dev. makeObjectKO dev (Inl (KOArch (KOASIDPool f))) = Some ko"
    by (simp add: ko_def makeObjectKO_def)


  note rl = projectKO_opt_retyp_other [OF rc pal pno' ko_def]
  note cterl = retype_ctes_helper[OF pal pdst pno' al'
    le_refl range_cover_sz'[where 'a=32, folded word_bits_def, OF rc] mko rc,simplified]
  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

  have guard:
    "\<forall>n<2 ^ (pageBits - objBitsKO ko). c_guard (CTypesDefs.ptr_add ?ptr (of_nat n))"
    apply (rule retype_guard_helper[where m = 2])
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
    apply (simp add: carch_state_relation_def cmachine_state_relation_def)
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
      apply ((simp add:word_bits_conv objBits_simps archObjSize_def
        capAligned_def)+)[4]
  apply (simp add:simpler_modify_def rf_sr_htd_safe)
  apply (subgoal_tac "{frame ..+ 2 ^ pageBits} \<inter> kernel_data_refs = {}")
   prefer 2
   apply (drule(1) valid_global_refsD')
   apply (clarsimp simp:Int_commute pageBits_def X64SmallPageBits_def
     intvl_range_conv[where bits = pageBits,unfolded pageBits_def word_bits_def,simplified])
  apply (intro conjI impI)
       apply (erule is_aligned_no_wrap')
       apply (clarsimp simp:X64SmallPageBits_def pageBits_def)
      apply (erule is_aligned_weaken,simp add:pageBits_def)
     apply (simp add:is_aligned_def X64SmallPageBits_def)
    apply (simp add: region_actually_is_bytes_dom_s pageBits_def X64SmallPageBits_def)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         size_of_def pageBits_def
                  elim!: ptr_retyp_htd_safe_neg)
  apply clarsimp
  apply (cut_tac helper [rule_format])
   prefer 2
   apply fastforce
  apply (subst data_map_insert_def[symmetric])
  apply (erule iffD1[OF rf_sr_upd,rotated -1 ])
   apply simp_all
  apply (simp add: hrs_htd_update_def hrs_mem_update_def split_def)
  apply (simp add: pageBits_def X64SmallPageBits_def ptr_retyps_gen_def
              del:replicate_numeral)
  done
qed *)

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
   apply (rule_tac P="is_aligned frame pageBits" in ccorres_gen_asm)
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_split_nothrow[where c="Seq c c'" for c c'])
       apply (fold pageBits_def)[1]
       apply (simp add: hrs_htd_update)
       apply (rule deleteObjects_ccorres)
      apply ceqv
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_abstract_cleanup)
      apply (rule ccorres_symb_exec_l)
        apply (rule_tac P = "rva = (capability.UntypedCap isdev frame pageBits idx)" in ccorres_gen_asm)
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
  sorry (*
          apply (rule ccorres_Guard_Seq[where F=ShiftError])+
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
                apply (subst mod_less)
                 apply (drule leq_asid_bits_shift)
                 apply (simp add: asid_high_bits_def mask_def word_le_nat_alt)
                apply simp
               apply (clarsimp simp: option_to_ptr_def option_to_0_def)
              apply (clarsimp simp: asid_high_bits_def)
             apply wp+
            apply (strengthen valid_pspace_mdb' vp_strgs' valid_pspace_valid_objs')
            apply (clarsimp simp: is_simple_cap'_def isCap_simps conj_comms placeNewObject_def2)
            apply (wp createObjects_valid_pspace'[where ty="Inl (KOArch (KOASIDPool f))" and sz = pageBits]
                      createObjects_cte_wp_at'[where sz = pageBits]
                   | simp add:makeObjectKO_def objBits_simps archObjSize_def range_cover_full)+
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
     apply (rule_tac Q="\<lambda>_. cte_wp_at' (op = (UntypedCap isdev frame pageBits idx) o cteCap) parent
                           and (\<lambda>s. descendants_range_in' {frame..frame + (2::word32) ^ pageBits - (1::word32)} parent (ctes_of s))
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
     apply simp
     apply (intro conjI)
        apply (simp add:is_aligned_def)
      apply (rule descendants_range_caps_no_overlapI'[where d=isdev and cref = parent])
         apply simp
        apply (fastforce simp:cte_wp_at_ctes_of is_aligned_neg_mask_eq)
       apply (clarsimp simp:is_aligned_neg_mask_eq)
      apply (rule le_m1_iff_lt[THEN iffD1,THEN iffD1])
       apply (simp add:asid_bits_def)
      apply (simp add:mask_def)
     apply (clarsimp dest!: upto_intvl_eq)
    apply (wp deleteObjects_cte_wp_at'[where d=isdev and idx = idx and p = parent]
              deleteObjects_descendants[where d=isdev and p = parent and idx = idx]
              deleteObjects_invs'[where d=isdev and p = parent and idx = idx]
              Detype_R.deleteObjects_descendants[where p = parent and idx = idx]
              deleteObjects_ct_active'[where d=isdev and cref = parent and idx = idx])
   apply clarsimp
   apply vcg
  apply (clarsimp simp:conj_comms invs_valid_pspace')
  apply (frule cte_wp_at_valid_objs_valid_cap', fastforce)
  apply (clarsimp simp:valid_cap'_def capAligned_def cte_wp_at_ctes_of
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
  apply (clarsimp simp: is_aligned_mask max_free_index_def pageBits_def
                        gen_framesize_to_H_def)
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
                        ghost_assertion_data_get_gs_clear_region[unfolded o_def])
  apply (subst ghost_assertion_size_logic_flex[unfolded o_def, rotated])
     apply assumption
    apply (simp add: ghost_assertion_data_get_gs_clear_region[unfolded o_def])
   apply (drule valid_global_refsD_with_objSize, clarsimp)+
   apply (clarsimp simp: isCap_simps dest!: ccte_relation_ccap_relation)
  apply (cut_tac ptr=frame and bits=12
    and htd="typ_region_bytes frame 12 (hrs_htd (t_hrs_' (globals s')))" in typ_region_bytes_actually_is_bytes)
   apply (simp add: hrs_htd_update)
  apply (clarsimp simp: region_actually_is_bytes'_def[where len=0])
  apply (intro conjI)
       apply (clarsimp elim!:is_aligned_weaken)
      apply (simp add:is_aligned_def)
     apply (simp add: hrs_htd_def)
    apply (erule is_aligned_no_wrap',simp)
   apply (drule region_actually_is_bytes_dom_s[OF _ order_refl])
   apply (simp add: hrs_htd_def split_def)
  apply (clarsimp simp: ccap_relation_def)
  apply (clarsimp simp: cap_asid_pool_cap_lift)
  apply (clarsimp simp: cap_to_H_def)
  apply (simp add: is_aligned_neg_mask pageBits_def)
  apply (drule word_le_mask_eq, simp)
  apply (simp add: asid_bits_def)
  done *)

lemmas performX64MMUInvocations
    = ccorres_invocationCatch_Inr performInvocation_def
      X64_H.performInvocation_def performX64MMUInvocation_def
      liftE_bind_return_bindE_returnOk

lemma slotcap_in_mem_PML4:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); (s, s') \<in> rf_sr \<rbrakk>
       \<Longrightarrow> \<exists>v. cslift s' (cte_Ptr slot) = Some v
           \<and> (cap_get_tag (cte_C.cap_C v) = scast cap_pml4_cap)
              = (isArchObjectCap cap \<and> isPML4Cap (capCap cap))
           \<and> (isArchObjectCap cap \<and> isPML4Cap (capCap cap)
                  \<longrightarrow> ccap_relation cap (cte_C.cap_C v))"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
  apply (clarsimp dest!: ccte_relation_ccap_relation)
  apply (simp add: cap_get_tag_isCap_ArchObject2)
  done

declare if_split [split del]

lemma decodeX64PageTableInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps;
          isPageTableCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' (diminished' (ArchObjectCap cp) \<circ> cteCap) slot
              and valid_cap' (ArchObjectCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. excaps_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86PageTableInvocation_'proc)"
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_' excaps_' cap_' buffer_'
                simp: decodeX64MMUInvocation_def invocation_eq_use_types decodeX64PageTableInvocation_def)
   apply (simp add: Let_def isCap_simps if_to_top_of_bind
               del: Collect_const cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_split_throws)
     apply (simp add: liftE_bindE bind_assoc)
     apply (rule ccorres_symb_exec_l[OF _ getCTE_inv _ empty_fail_getCTE])
      apply (rule ccorres_rhs_assoc)+
      apply (ctac add: isFinalCapability_ccorres)
        apply (simp add: unlessE_def if_to_top_of_bind if_to_top_of_bindE
                         ccorres_seq_cond_raise
                    del: Collect_const)
        apply (rule ccorres_cond2'[where R=\<top>])
          apply (clarsimp simp: from_bool_0)
         apply (simp add: throwError_bind invocationCatch_def)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (simp add: returnOk_bind bindE_assoc
                         performX64MMUInvocations)
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
   apply (simp del: Collect_const)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (simp split: invocation_label.split arch_invocation_label.split
                   add: throwError_bind invocationCatch_def)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp del: Collect_const)
   apply csymbr
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: if_1_0_0 word_less_nat_alt throwError_bind invocationCatch_def)
    apply (rule ccorres_cond_true_seq)
    apply (rule ccorres_equals_throwError)
     apply (simp add: throwError_bind split: list.split)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply csymbr
   apply (simp add: if_1_0_0 interpret_excaps_test_null excaps_map_def
               del: Collect_const)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: list_case_If2 split_def
                    word_less_nat_alt length_ineq_not_Nil Let_def
                    whenE_bindE_throwError_to_if if_to_top_of_bind
               del: Collect_const)
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
   apply (simp add: cap_case_PML4Cap2 split_def del: Collect_const)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
apply csymbr
     apply (rule ccorres_add_return)
apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
apply csymbr
apply (rule ccorres_add_return)
     apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_pml4_cap)
                                          = (isArchObjectCap rv \<and> isPML4Cap (capCap rv)))
                                  \<and> (cap_get_tag rv' = scast cap_pml4_cap \<longrightarrow> ccap_relation rv rv'))
                                      (fst (extraCaps ! 0))"
                and xf'=vspaceCap_' in ccorres_split_nothrow)
         apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
         apply (drule(1) slotcap_in_mem_PML4)
         apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
         apply (clarsimp simp: typ_heap_simps' mask_def)
        apply (simp add:word_sless_def word_sle_def)
        apply ceqv
(* FIXME x64: needs isValidNativeRoot_spec for csymbr *)
  sorry (*
       apply csymbr
       apply csymbr
       apply (simp add: if_1_0_0 del: Collect_const)
       apply (rule ccorres_Cond_rhs_Seq)
        apply (simp add: throwError_bind invocationCatch_def hd_conv_nth
                   cong: conj_cong)
        apply (rule ccorres_cond_true_seq)
        apply (rule ccorres_split_throws)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply vcg
       apply (simp del: Collect_const)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply csymbr
       apply (simp add: case_option_If2 if_1_0_0 if_to_top_of_bind
                          if_to_top_of_bindE hd_conv_nth del: Collect_const)
       apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
          apply vcg
         apply (clarsimp simp: cap_lift_page_directory_cap
                               cap_to_H_def cap_page_directory_cap_lift_def
                               to_bool_def neq_Nil_conv
                        elim!: ccap_relationE split: if_split)
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply csymbr
       apply csymbr
       apply csymbr
       apply (simp add: if_to_top_of_bind del: Collect_const)
       apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
          apply vcg
         apply (simp add: kernelBase_def X64.kernelBase_def hd_conv_nth length_ineq_not_Nil)
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (simp add: lookupError_injection invocationCatch_use_injection_handler
                        injection_bindE[OF refl refl] injection_handler_If
                        injection_handler_throwError injection_liftE[OF refl]
                        injection_handler_returnOk bindE_assoc
                  cong: if_cong del: Collect_const)
       apply csymbr
       apply (ctac add: ccorres_injection_handler_csum1 [OF ccorres_injection_handler_csum1,
                                                         OF findPDForASID_ccorres])
          apply (simp add: Collect_False if_to_top_of_bindE del: Collect_const)
          apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
             apply vcg
            apply (clarsimp simp: isCap_simps)
            apply (frule cap_get_tag_isCap_unfolded_H_cap)
            apply (clarsimp simp: cap_lift_page_directory_cap
                                  cap_to_H_def cap_page_directory_cap_lift_def
                           elim!: ccap_relationE split: if_split)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply (simp add: bindE_assoc del: Collect_const,
                 simp add: liftE_bindE del: Collect_const)
          apply (rule ccorres_pre_getObject_pde)
          apply csymbr
          apply (rule ccorres_rhs_assoc2, rule ccorres_symb_exec_r)
            apply (simp add: unlessE_def if_to_top_of_bindE injection_handler_If
                        del: Collect_const)
            apply (simp add: bit_simps)
            apply (rule_tac Q'="\<lambda>s. \<exists>v. cslift s (pde_Ptr (capPDBasePtr (capCap (fst (extraCaps ! 0)))
                                                           + (args ! 0 >> 21 << 3))) = Some v
                                        \<and> cpde_relation rva v \<and> ret__unsigned_' s = pde_get_tag v"
                          in ccorres_if_cond_throws2[rotated -1, where Q=\<top>])
               apply vcg
              apply clarsimp
              apply (clarsimp simp: cpde_relation_def Let_def pde_pde_invalid_lift
                              split: pde.split_asm)
              apply (simp add: pde_pde_invalid_lift_def)
             apply (simp add: injection_handler_throwError throwError_bind invocationCatch_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (simp add: injection_handler_returnOk
                               performX64MMUInvocations bindE_assoc)
            apply csymbr
            apply csymbr
            apply csymbr
            apply csymbr
            apply csymbr
            apply csymbr
            apply (ctac add: setThreadState_ccorres)
              apply (ctac(no_vcg) add: performPageTableInvocationMap_ccorres)
                apply (rule ccorres_alternative2)
                apply (rule ccorres_return_CE, simp+)[1]
               apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
              apply wp+
            apply simp
            apply (vcg exspec=setThreadState_modifies)
           apply simp
           apply vcg
          apply (rule conseqPre, vcg, clarsimp)
         apply simp
         apply (rule_tac P'="{s. errstate s = find_ret}"
                       in ccorres_from_vcg_split_throws[where P=\<top>])
          apply vcg
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                               syscall_error_to_H_cases exception_defs false_def)
         apply (erule lookup_failure_rel_fault_lift[rotated])
         apply (simp add: exception_defs)
        apply simp
        apply (wp injection_wp[OF refl] hoare_drop_imps)
       apply simp
       apply (vcg exspec=findPDForASID_modifies)
      apply simp
      apply (wp | wp_once hoare_drop_imps)+
     apply simp
     apply vcg
    apply simp
    apply wp
   apply simp
   apply (vcg exspec=getSyscallArg_modifies)
  apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of excaps_map_def
                        if_1_0_0 word_sle_def word_sless_def bit_simps)
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
                          less_kernelBase_valid_pde_offset''
                          word_le_nat_alt[symmetric] bit_simps)
    apply (auto simp: ct_in_state'_def pred_tcb_at' mask_def valid_tcb_state'_def
               elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
   apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def
                         slotcap_in_mem_def)
   apply (auto dest: ctes_of_valid')[1]
  apply (rule conjI)
   apply (clarsimp simp: rf_sr_ksCurThread "StrictC'_thread_state_defs"
                         mask_eq_iff_w2p word_size
                         ct_in_state'_def st_tcb_at'_def
                         word_sle_def word_sless_def
                         typ_heap_simps' bit_simps)

  apply (clarsimp simp: cap_get_tag_isCap_ArchObject isCap_simps
                        word_sle_def word_sless_def
                        word_less_nat_alt)
  apply (frule length_ineq_not_Nil)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(15))
  apply (frule cap_get_tag_isCap_unfolded_H_cap(14))
  apply (clarsimp simp: cap_lift_page_directory_cap hd_conv_nth
                        cap_lift_page_table_cap bit_simps
                        cap_to_H_def cap_page_directory_cap_lift_def
                        to_bool_def cap_page_table_cap_lift_def
                        typ_heap_simps' shiftl_t2n[where n=3] field_simps
                 elim!: ccap_relationE)
  apply (clarsimp simp: neq_Nil_conv[where xs=extraCaps]
                        excaps_in_mem_def slotcap_in_mem_def
                 dest!: sym[where s="ArchObjectCap cp" for cp])
  apply (cut_tac p="snd (hd extraCaps)" in ctes_of_valid', simp, clarsimp)
  apply (clarsimp simp: valid_cap_simps')
  apply (subst array_assertion_abs_pd, erule conjI,
          simp add: unat_eq_0 unat_shiftr_le_bound bit_simps)
  apply (clarsimp simp: rf_sr_ksCurThread mask_def[where n=4]
                        "StrictC'_thread_state_defs"
                        ccap_relation_def cap_to_H_def
                        cap_lift_page_table_cap word_bw_assocs
                        shiftr_shiftl1 mask_def[where n=17])
  apply (clarsimp simp: cpde_relation_def Let_def pde_lift_pde_coarse
                        pde_pde_coarse_lift_def word_bw_assocs page_table_at'_def bit_simps)
  apply (subst is_aligned_neg_mask [OF _ order_refl]
         , erule is_aligned_addrFromPPtr_n)
   apply fastforce+
  done *)

lemma checkVPAlignment_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. \<acute>sz < 3\<rbrace> Call checkVPAlignment_'proc
          {t. ret__unsigned_long_' t = from_bool
               (vmsz_aligned' (w_' s) (framesize_to_H (sz_' s)))}"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: mask_eq_iff_w2p word_size)
  apply (rule conjI)
   apply (simp add: pageBitsForSize_def bit_simps split: vmpage_size.split)
  apply (simp add: from_bool_def vmsz_aligned'_def is_aligned_mask
                   mask_def split: if_split)
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

thm cpde_relation_def

(* FIXME x64: this is going to be annoying because
 * you cannot determine validity just from pde_get_tag *)
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

(* FIXME: move *)
lemma int_unat [simp]: "int (unat x) = uint x"
  by (clarsimp simp: unat_def)

lemma obj_at_pte_aligned:
  "obj_at' (\<lambda>a::X64_H.pte. True) ptr s ==> is_aligned ptr word_size_bits"
  apply (drule obj_at_ko_at')
  apply (clarsimp dest!:ko_at_is_aligned'
                  simp: objBits_simps archObjSize_def bit_simps
                  elim!: is_aligned_weaken)
  done

(* FIXME x64: dont know what these are for yet *)
lemma addrFromPPtr_mask_5:
  "addrFromPPtr ptr && mask (5::nat) = ptr && mask (5::nat)"
  apply (simp add:addrFromPPtr_def X64.pptrBase_def)
  apply word_bitwise
  apply (simp add:mask_def)
  done

lemma addrFromPPtr_mask_6:
  "addrFromPPtr ptr && mask (6::nat) = ptr && mask (6::nat)"
  apply (simp add:addrFromPPtr_def X64.pptrBase_def)
  apply word_bitwise
  apply (simp add:mask_def)
  done

lemma word_add_format:
  "(-1::machine_word) + b + c = b + (c - 1)"
  by simp

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

lemma hd_in_zip_set:
   "slots \<noteq> [] \<Longrightarrow> (hd slots, 0) \<in> set (zip slots [0.e.of_nat (length slots - Suc 0)::machine_word])"
   by (cases slots; simp add: upto_enum_word upto_0_to_n2 del: upt_Suc)

lemma last_in_zip_set:
  "\<lbrakk> slots \<noteq> []; length js = length slots \<rbrakk> \<Longrightarrow> (last slots, last js) \<in> set (zip slots js)"
   apply (simp add: in_set_zip last_conv_nth)
   apply (rule_tac x="length slots - 1" in exI)
   apply clarsimp
   apply (subst last_conv_nth)
    apply (cases js; simp)
   apply simp
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
           and (\<lambda>_. asid \<le> mask asid_bits \<and> page_entry_map_corres mapping))
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
sorry (*
apply (ctac add: storePTE_Basic_ccorres'')
     apply wpc
      prefer 2
      apply (simp add: isLeft_def)
     apply (simp add: split_def)
     apply (rename_tac h_pte_slots)
     apply (ctac add: pteCheckIfMapped_ccorres)
       apply csymbr
       apply (simp add: mapM_discarded whileAnno_def Collect_False del: Collect_const)
       apply (rule ccorres_Guard_Seq)
       apply (rule ccorres_basic_srnoop2, simp)
       apply csymbr
       apply (rule ccorres_abstract_cleanup)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac F="\<lambda>_. valid_pte_slots'2 mapping" and
                           Q="\<lbrace> cpte_relation (addPTEOffset (fst h_pte_slots) (if \<acute>i = 0 then 0 else \<acute>i - 1)) \<acute>pte \<and>
                                pteFrame (fst h_pte_slots) = base_address  \<rbrace>"
                   in ccorres_mapM_x_whileQ)
               apply (intro allI impI, simp add: split_def)
               apply (rule ccorres_rhs_assoc)+
               apply (rule ccorres_guard_imp2)
                apply csymbr
                apply (rule ccorres_Guard_Seq)
                apply csymbr
                apply (rule ccorres_abstract_cleanup)
                apply (rule ccorres_move_array_assertion_pte_16_2
                     | (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_pte_16_2))+
                apply (rule storePTE_Basic_ccorres'', simp)
               apply clarsimp
               apply (rename_tac h_pte slots n s s' x)
               apply (clarsimp simp: valid_pte_slots'2_def)
               apply (erule disjE)
                apply clarsimp
                apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def
                                      unat_of_nat upto_enum_word X64SmallPage_def)
                apply (case_tac h_pte; clarsimp simp: isLargePagePTE_def)
                apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
                apply (clarsimp simp: pte_lifts split del: split_of_bool)
               apply (clarsimp simp: Kernel_C.X64SmallPage_def)
               apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def
                                     upt_conv_Cons[where i=0] of_nat_gt_0
                                     unat_of_nat upto_enum_word pte_pte_small_lift_def)
               apply (case_tac h_pte; clarsimp simp: isLargePagePTE_def)
               apply (clarsimp simp: nth_Cons')
               apply (clarsimp simp: pte_lifts split: if_split)
               apply (rule conjI)
                apply (clarsimp simp: cpte_relation_def pte_pte_small_lift_def split del: split_of_bool)
                apply (rule is_aligned_neg_mask_eq)
                apply (erule is_aligned_weaken, simp)
               apply (clarsimp simp: addPTEOffset_def)
               apply (clarsimp simp: cpte_relation_def pte_pte_small_lift_def split del: split_of_bool)
               apply (clarsimp simp: gen_framesize_to_H_def X64SmallPage_def addPAddr_def fromPAddr_def)
               apply (rule is_aligned_neg_mask_eq)
               apply (erule is_aligned_add_multI[where n=12, simplified]; simp)
              apply simp
              apply (clarsimp simp: valid_pte_slots'2_def pte_range_relation_def ptr_range_to_list_def)
              apply (erule disjE; clarsimp simp: unat32_eq_of_nat word_bits_def)
             apply clarsimp
             apply vcg
             apply (clarsimp simp: valid_pte_slots'2_def)
             apply (rule conjI)
              apply (clarsimp simp: X64SmallPage_def)
             apply (rule context_conjI)
              apply (case_tac a; clarsimp simp: isLargePagePTE_def cpte_relation_def addPTEOffset_def pte_lift_small)
             apply clarsimp
             apply (rule conjI, clarsimp)
              apply (clarsimp split: if_split_asm)
               apply (case_tac a; clarsimp simp: isLargePagePTE_def)
               apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
               apply (clarsimp simp: pte_lifts split del: split_of_bool)
              apply (case_tac a; clarsimp simp: isLargePagePTE_def)
              apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
              apply (clarsimp simp: pte_lifts split del: split_of_bool)
              apply (rule context_conjI)
               apply (rule is_aligned_neg_mask_eq)
               apply (erule is_aligned_weaken, simp)
              apply simp
             apply clarsimp
             apply (rule conjI, clarsimp)
              apply (clarsimp split: if_split_asm)
               apply (case_tac a; clarsimp simp: isLargePagePTE_def)
               apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
               apply (clarsimp simp: pte_lifts split del: split_of_bool)
              apply (case_tac a; clarsimp simp: isLargePagePTE_def)
              apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
              apply (clarsimp simp: pte_lifts split del: split_of_bool)
              apply (rule is_aligned_neg_mask_eq)
              apply (erule is_aligned_weaken, simp)
             apply (clarsimp split: if_split)
             apply (rule conjI, clarsimp)
              apply unat_arith
             apply clarsimp
             apply (erule disjE)
              apply (case_tac a; clarsimp simp: isLargePagePTE_def)
              apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
              apply (clarsimp simp: pte_lifts split del: split_of_bool)
             apply (case_tac a; clarsimp simp: isLargePagePTE_def)
             apply (clarsimp simp: cpte_relation_def addPTEOffset_def pte_lift_small split del: split_of_bool)
             apply (clarsimp simp: pte_lifts split del: split_of_bool)
             apply (clarsimp simp: X64SmallPage_def gen_framesize_to_H_def addPAddr_def fromPAddr_def)
             apply (rule is_aligned_neg_mask_eq)
             apply (rule is_aligned_add_multI[where n=12, simplified], simp, simp, simp)
            apply (simp add: valid_pte_slots'2_def split_def)
            apply (rule hoare_pre, wpsimp wp: hoare_vcg_ex_lift, clarsimp)
           apply (auto simp: valid_pte_slots'2_def word_bits_def)[1]
          apply ceqv
         apply (rule_tac P="valid_pte_slots'2 mapping" in ccorres_cross_over_guard)
         apply csymbr
         apply (rule ccorres_move_c_guard_pte
                     ccorres_move_array_assertion_pte_16_2
                     ccorres_Guard_Seq
                     ccorres_rhs_assoc)+
         apply (ctac add: cleanCacheRange_PoU_ccorres)
           apply (rule ccorres_move_c_guard_pte
                       ccorres_move_array_assertion_pte_16_2
                       ccorres_rhs_assoc)+
           apply (simp add: when_def del: Collect_const)
           apply (rule ccorres_Cond_rhs_Seq)
            apply (simp add: to_bool_def)
            apply (rule ccorres_add_return2)
            apply (ctac (no_vcg) add: invalidateTLBByASID_ccorres)
             apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp:return_def)
            apply (rule wp_post_taut)
           apply (simp add: to_bool_def)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp:return_def)
          apply (wp hoare_vcg_const_imp_lift) [1]
         apply clarsimp
         apply (vcg exspec=cleanCacheRange_PoU_modifies)
        apply (clarsimp simp: to_bool_def)
        apply (rule hoare_strengthen_post)
         apply (rule_tac Q'="\<lambda>rv s. valid_pde_mappings' s
                 \<and> valid_pte_slots'2 mapping s
                 \<and> unat (last (snd (theLeft mapping)) + 7
                     - hd (snd (theLeft mapping))) \<le> gsMaxObjectSize s"
                in hoare_vcg_conj_lift)
          apply (rule mapM_x_accumulate_checks)
           apply (simp add: storePTE_def' split_def)
           apply (rule obj_at_setObject3)
            apply simp
           apply (simp add: objBits_simps archObjSize_def pteBits_def)
          apply (simp add: typ_at_to_obj_at_arches[symmetric])
          apply ((wp mapM_x_wp_inv hoare_vcg_ex_lift | simp add: split_def valid_pte_slots'2_def)+)[2]
        apply clarsimp
        apply (simp add: typ_at_to_obj_at_arches)
        apply (frule bspec, erule hd_in_zip_set)
        apply (drule bspec, erule last_in_zip_set)
         apply (clarsimp simp: valid_pte_slots'2_def)
        apply (simp add: hd_conv_nth last_conv_nth)
        apply (rule conj_assoc[where Q="a \<le> b" for a b, THEN iffD1])+
        apply (rule conjI)
    (* the inequalities first *)
         apply (clarsimp simp: valid_pte_slots'2_def
                               objBits_simps archObjSize_def hd_conv_nth pteBits_def)
         apply (clarsimp simp:pte_range_relation_def ptr_range_to_list_def ptr_add_def)
         apply (frule is_aligned_addrFromPPtr_n,simp)
         apply (cut_tac n = "sz + 3" in  power_not_zero[where 'a="machine_word_len"])
          apply simp
         apply (subst is_aligned_no_wrap', assumption, fastforce simp: field_simps)
         apply (subst add_diff_eq [symmetric], subst is_aligned_no_wrap', assumption, fastforce simp: field_simps)
         apply simp
        apply (clarsimp simp: pte_range_relation_def ptr_add_def ptr_range_to_list_def
                              addrFromPPtr_mask_6)
        apply (auto simp: valid_pte_slots'2_def upt_conv_Cons[where i=0])[1]
       apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem hd_conv_nth last_conv_nth ucast_minus)
       apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def objBits_simps
                             archObjSize_def pteBits_def)
       apply (simp add: CTypesDefs.ptr_add_def ucast_nat_def word_0_sle_from_less)
       apply (clarsimp simp: valid_pte_slots'2_def del: disjCI)
       apply (erule disjE, simp_all add: unat_arith_simps)[1]
       apply (clarsimp simp: upt_conv_Cons[where i=0])
      apply (wp valid_pte_slots_lift2 hoare_drop_imps)
     apply vcg
    apply (wp valid_pte_slots_lift2 hoare_drop_imps hoare_vcg_all_lift)
   apply (vcg)
  apply simp
  apply (rule conjI, fastforce)
  apply (rule conjI)
   apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def unat_1_0
                         valid_pte_slots'2_def isLeft_def last_map hd_map
                         ptr_add_def)
   apply (auto elim!: order_trans[rotated] simp: unat_word_ariths unat_arith_simps)[1]
  apply (rule conjI, fastforce)
  apply (clarsimp simp: isLeft_def valid_pte_slots'2_def)
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply (clarsimp simp: pte_range_relation_def hd_map_simp ptr_range_to_list_def)
  apply (rule conjI)
   apply (rule c_guard_abs_pte[rule_format])
   apply (erule conjI, simp)
   apply (erule page_table_at_pte_atD')
    apply (simp add: is_aligned_weaken)
   apply simp
  apply (clarsimp simp: unat_eq_of_nat split: if_split_asm)
   apply (case_tac a; clarsimp simp: isLargePagePTE_def)
   apply (clarsimp simp: cpte_relation_def pte_lift_small)
  apply (case_tac a; clarsimp simp: isLargePagePTE_def)
  apply (clarsimp simp: cpte_relation_def pte_lift_small)
  done *)

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

lemma vaddr_segment_nonsense3_folded:
  "is_aligned (p :: machine_word) pageBits \<Longrightarrow>
   (p + ((vaddr >> pageBits) && mask (pt_bits - word_size_bits) << word_size_bits) && ~~ mask pt_bits) = p"
  apply (rule is_aligned_add_helper[THEN conjunct2])
   apply (simp add: bit_simps mask_def)+
  apply (rule shiftl_less_t2n[where m=12 and n=3, simplified, OF and_mask_less'[where n=9, unfolded mask_def, simplified]])
   apply simp+
  done


(* FIXME : move *)
lemma of_nat_ucast:
  "is_down (ucast :: ('a :: len) word \<Rightarrow> ('b :: len) word)
    \<Longrightarrow> (of_nat n :: 'b word) = ucast (of_nat n :: 'a word)"
  apply (subst word_unat.inverse_norm)
  apply (simp add: ucast_def word_of_int[symmetric]
                   of_nat_nat[symmetric] unat_def[symmetric])
  apply (simp add: unat_of_nat)
  apply (rule nat_int.Rep_eqD)
  apply (simp only: zmod_int)
  apply (rule mod_mod_cancel)
  apply (subst zdvd_int[symmetric])
  apply (rule le_imp_power_dvd)
  apply (simp add: is_down_def target_size_def source_size_def word_size)
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
              and (\<lambda>s. asid \<le> mask asid_bits \<and> page_entry_map_corres mapping))
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
  sorry (*
   apply (rule_tac P="\<exists>s. valid_pde_slots'2 mapping s" in ccorres_gen_asm)
   apply (rule ccorres_gen_asm [where P ="snd (theRight mapping)\<noteq>[]"])
   apply (ctac)
     apply wpc
      apply (simp add: isRight_def)
     apply (simp add: split_def)
     apply (rename_tac h_pde_slots)
     apply (ctac add: pdeCheckIfMapped_ccorres)
       apply csymbr
       apply (simp add: mapM_discarded whileAnno_def Collect_False del: Collect_const)
       apply (rule ccorres_Guard_Seq)
       apply (rule ccorres_basic_srnoop2, simp)
       apply csymbr
       apply (rule ccorres_abstract_cleanup)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac F="\<lambda>_. valid_pde_slots'2 mapping" and
                           Q="\<lbrace> cpde_relation (addPDEOffset (fst h_pde_slots) (if \<acute>i = 0 then 0 else \<acute>i - 1)) \<acute>pde \<and>
                                pdeFrame (fst h_pde_slots) = base_address  \<rbrace>"
                   in ccorres_mapM_x_whileQ)
               apply (intro allI impI, simp add: split_def)
               apply (rule ccorres_rhs_assoc)+
               apply (rule ccorres_guard_imp2)
                apply csymbr
                apply (rule ccorres_Guard_Seq)
                apply csymbr
                apply (rule ccorres_abstract_cleanup)
                apply (rule ccorres_move_array_assertion_pde_16_2
                     | (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_pde_16_2))+
                apply (rule storePDE_Basic_ccorres'', simp)
               apply clarsimp
               apply (rename_tac h_pde slots n s s' x)
               apply (clarsimp simp: valid_pde_slots'2_def)
               apply (erule disjE)
                apply clarsimp
                apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def
                                      unat_of_nat upto_enum_word X64Section_def mask_def[of 2])
                apply (case_tac h_pde; clarsimp simp: isSuperSectionPDE_def)
                apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
                apply (clarsimp simp: pde_lifts split del: split_of_bool)
                apply (rule is_aligned_neg_mask_eq)
                apply (erule is_aligned_weaken, simp)
               apply (clarsimp simp: Kernel_C.X64Section_def mask_def[of 2])
               apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def
                                     upt_conv_Cons[where i=0] of_nat_gt_0
                                     unat_of_nat upto_enum_word pde_pde_section_lift_def)
               apply (case_tac h_pde; clarsimp simp: isSuperSectionPDE_def)
               apply (clarsimp simp: nth_Cons')
               apply (clarsimp simp: pde_lifts split: if_split)
               apply (rule conjI)
                apply (clarsimp simp: cpde_relation_def pde_pde_section_lift_def split del: split_of_bool)
                apply (rule is_aligned_neg_mask_eq)
                apply (erule is_aligned_weaken, simp)
               apply (clarsimp simp: addPDEOffset_def)
               apply (clarsimp simp: cpde_relation_def pde_pde_section_lift_def split del: split_of_bool)
               apply (clarsimp simp: gen_framesize_to_H_def X64LargePage_def X64Section_def X64SmallPage_def addPAddr_def fromPAddr_def)
               apply (rule is_aligned_neg_mask_eq)
               apply (drule is_aligned_add_multI[where n=21 and m=25, simplified], simp)
               apply (erule is_aligned_weaken, simp)
              apply simp
              apply (clarsimp simp: valid_pde_slots'2_def pde_range_relation_def ptr_range_to_list_def)
              apply (erule disjE; clarsimp simp: unat32_eq_of_nat word_bits_def)
             apply clarsimp
             apply vcg
             apply (clarsimp simp: valid_pde_slots'2_def)
             apply (rule conjI)
              apply (clarsimp simp: X64Section_def mask_def)
             apply (rule context_conjI)
              apply (case_tac a; clarsimp simp: isSuperSectionPDE_def cpde_relation_def addPDEOffset_def pde_lift_section)
             apply clarsimp
             apply (rule conjI, clarsimp)
              apply (clarsimp split: if_split_asm)
               apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
               apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
               apply (clarsimp simp: pde_lifts split del: split_of_bool cong: conj_cong)
               apply (rule is_aligned_neg_mask_eq)
               apply (erule is_aligned_weaken, simp)
              apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
              apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
              apply (clarsimp simp: pde_lifts split del: split_of_bool)
              apply (rule context_conjI)
               apply (rule is_aligned_neg_mask_eq)
               apply (erule is_aligned_weaken, simp)
              apply simp
             apply clarsimp
             apply (rule conjI, clarsimp)
              apply (clarsimp split: if_split_asm)
               apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
               apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
               apply (clarsimp simp: pde_lifts split del: split_of_bool)
               apply (rule is_aligned_neg_mask_eq)
               apply (erule is_aligned_weaken, simp)
              apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
              apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
              apply (clarsimp simp: pde_lifts split del: split_of_bool)
              apply (rule is_aligned_neg_mask_eq)
              apply (erule is_aligned_weaken, simp)
             apply (clarsimp split: if_split)
             apply (rule conjI, clarsimp)
              apply unat_arith
             apply clarsimp
             apply (erule disjE)
              apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
              apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
              apply (clarsimp simp: pde_lifts split del: split_of_bool)
              apply (rule is_aligned_neg_mask_eq)
              apply (erule is_aligned_weaken, simp)
             apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
             apply (clarsimp simp: cpde_relation_def addPDEOffset_def pde_lift_section split del: split_of_bool)
             apply (clarsimp simp: pde_lifts split del: split_of_bool)
             apply (clarsimp simp: X64Section_def X64LargePage_def X64SmallPage_def
                                   gen_framesize_to_H_def addPAddr_def fromPAddr_def)
             apply (rule is_aligned_neg_mask_eq)
             apply (drule is_aligned_add_multI[where n=21 and m=25, simplified], simp)
             apply (erule is_aligned_weaken, simp)
            apply (simp add: valid_pde_slots'2_def split_def)
            apply (rule hoare_pre, wpsimp wp: hoare_vcg_ex_lift, clarsimp)
           apply (auto simp: valid_pde_slots'2_def word_bits_def)[1]
          apply ceqv
         apply (rule_tac P="valid_pde_slots'2 mapping" in ccorres_cross_over_guard)
         apply csymbr
         apply (rule ccorres_move_c_guard_pde
                     ccorres_move_array_assertion_pde_16_2
                     ccorres_Guard_Seq
                     ccorres_rhs_assoc)+
         apply (ctac add: cleanCacheRange_PoU_ccorres)
           apply (rule ccorres_move_c_guard_pde
                       ccorres_move_array_assertion_pde_16_2
                       ccorres_rhs_assoc)+
           apply (simp add: when_def del: Collect_const)
           apply (rule ccorres_Cond_rhs_Seq)
            apply (simp add: to_bool_def)
            apply (rule ccorres_add_return2)
            apply (ctac (no_vcg) add: invalidateTLBByASID_ccorres)
             apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp:return_def)
            apply (rule wp_post_taut)
           apply (simp add: to_bool_def)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp:return_def)
          apply (wp hoare_vcg_const_imp_lift) [1]
         apply clarsimp
         apply (vcg exspec=cleanCacheRange_PoU_modifies)
        apply (clarsimp simp: to_bool_def)
        apply (rule hoare_strengthen_post)
         apply (rule_tac Q'="\<lambda>rv s. valid_pde_mappings' s
                 \<and> valid_pde_slots'2 mapping s
                 \<and> unat (last (snd (theRight mapping)) + 7
                     - hd (snd (theRight mapping))) \<le> gsMaxObjectSize s"
                in hoare_vcg_conj_lift)
          apply (rule mapM_x_accumulate_checks)
           apply (simp add: storePDE_def' split_def)
           apply (rule obj_at_setObject3)
            apply simp
           apply (simp add: objBits_simps archObjSize_def pdeBits_def)
          apply (simp add: typ_at_to_obj_at_arches[symmetric])
          apply ((wp mapM_x_storePDE_pde_mappings' mapM_x_wp' valid_pde_slots_lift2 | simp add: split_def)+)[2]
         apply (clarsimp simp: valid_pde_mapping'_def valid_pde_slots'2_def)
         apply (drule set_zip_helper, clarsimp)
        apply clarsimp
        apply (simp add: typ_at_to_obj_at_arches)
        apply (frule bspec, erule hd_in_zip_set)
        apply (drule bspec, erule last_in_zip_set)
         apply (clarsimp simp: valid_pde_slots'2_def)
        apply (simp add: hd_conv_nth last_conv_nth)
        apply (rule conj_assoc[where Q="a \<le> b" for a b, THEN iffD1])+
        apply (rule conjI)
    (* the inequalities first *)
         apply (clarsimp simp: valid_pde_slots'2_def
                               objBits_simps archObjSize_def hd_conv_nth pdeBits_def)
         apply (clarsimp simp:pde_range_relation_def ptr_range_to_list_def ptr_add_def)
         apply (frule is_aligned_addrFromPPtr_n,simp)
         apply (cut_tac n = "sz + 3" in  power_not_zero[where 'a="machine_word_len"])
          apply simp
         apply (subst is_aligned_no_wrap', assumption, fastforce simp: field_simps)
         apply (subst add_diff_eq [symmetric], subst is_aligned_no_wrap', assumption, fastforce simp: field_simps)
         apply simp
        apply (clarsimp simp: pde_range_relation_def ptr_add_def ptr_range_to_list_def
                              addrFromPPtr_mask_6)
        apply (auto simp: valid_pde_slots'2_def upt_conv_Cons[where i=0])[1]
       apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem hd_conv_nth last_conv_nth ucast_minus)
       apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def objBits_simps
                             archObjSize_def pdeBits_def)
       apply (simp add: CTypesDefs.ptr_add_def ucast_nat_def word_0_sle_from_less)
       apply (clarsimp simp: valid_pde_slots'2_def del: disjCI)
       apply (erule disjE, simp_all add: unat_arith_simps)[1]
       apply (clarsimp simp: upt_conv_Cons[where i=0])
      apply (wp valid_pde_slots_lift2 hoare_drop_imps)
     apply vcg
    apply (wp valid_pde_slots_lift2 hoare_drop_imps hoare_vcg_all_lift)
   apply (vcg)
  apply simp
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply (rule conjI)
   apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def unat_1_0
                         valid_pde_slots'2_def isRight_def last_map hd_map
                         ptr_add_def)
   apply (auto elim!: order_trans[rotated] simp: unat_word_ariths unat_arith_simps)[1]
  apply (clarsimp simp: isRight_def valid_pde_slots'2_def)
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply (clarsimp simp: pde_range_relation_def hd_map_simp ptr_range_to_list_def)
  apply (rule conjI)
   apply (rule c_guard_abs_pde[rule_format])
   apply (erule conjI, simp)
   apply (erule page_directory_at_pde_atD')
    apply (simp add: is_aligned_weaken)
   apply simp
  apply (clarsimp simp: unat_eq_of_nat split: if_split_asm)
   apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
   apply (clarsimp simp: cpde_relation_def pde_lift_section)
  apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
  apply (clarsimp simp: cpde_relation_def pde_lift_section)
  done *)

lemma performPageInvocationRemapPDE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
           and (\<lambda>_. asid \<le> mask asid_bits \<and> page_entry_map_corres mapping))
       (UNIV \<inter> {s. cpde_relation (thePDE (fst mapping)) (pde_' s)}
             \<inter> {s. pdSlot_' s = pde_Ptr (thePDEPtr (snd mapping))}
             \<inter> {s. asid_' s = asid}
             \<inter> {s. vspace_' s = pml4e_Ptr vspace}
             \<inter> {s. isVMPDE mapping}) []
       (liftE (performPageInvocation (PageRemap mapping asid vspace)))
       (Call performX86PageInvocationRemapPDE_'proc)"
  supply pageBitsForSize_le_64 [simp]
  apply (rule ccorres_gen_asm2)
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift:  pde_' pdSlot_' asid_' vspace_')
sorry (*
   apply (rule ccorres_gen_asm [where P ="snd (theRight mapping)\<noteq>[]"])
   apply wpc
    apply (simp add: isRight_def)
   apply (simp add: split_def)
   apply (rename_tac h_pde_slots)
   apply (ctac add: pdeCheckIfMapped_ccorres)
     apply csymbr
     apply (simp add: mapM_discarded whileAnno_def Collect_False del: Collect_const)
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_basic_srnoop2, simp)
     apply csymbr
     apply (rule ccorres_abstract_cleanup)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule_tac F="\<lambda>_. valid_pde_slots'2 mapping" and
                         Q="\<lbrace> cpde_relation (addPDEOffset (fst h_pde_slots) (if \<acute>i = 0 then 0 else \<acute>i - 1)) \<acute>pde \<and>
                              pdeFrame (fst h_pde_slots) = base_address  \<rbrace>"
                         in ccorres_mapM_x_whileQ)
             apply (intro allI impI, simp add: split_def)
             apply (rule ccorres_rhs_assoc)+
             apply (rule ccorres_guard_imp2)
              apply csymbr
              apply (rule ccorres_Guard_Seq)
              apply csymbr
              apply (rule ccorres_abstract_cleanup)
              apply (rule ccorres_move_array_assertion_pde_16_2
                      | (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_pde_16_2))+
              apply (rule storePDE_Basic_ccorres'', simp)
             apply clarsimp
             apply (rename_tac h_pde slots n s s' x)
             apply (clarsimp simp: valid_pde_slots'2_def)
             apply (erule disjE)
              apply clarsimp
              apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def
                                    unat_of_nat upto_enum_word X64Section_def mask_def[of 2])
              apply (case_tac h_pde; clarsimp simp: isSuperSectionPDE_def)
              apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
              apply (clarsimp simp: pde_lifts split del: split_of_bool)
              apply (rule is_aligned_neg_mask_eq)
              apply (erule is_aligned_weaken, simp)
             apply (clarsimp simp: Kernel_C.X64Section_def mask_def[of 2])
             apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def
                                   upt_conv_Cons[where i=0] of_nat_gt_0
                                   unat_of_nat upto_enum_word pde_pde_section_lift_def)
             apply (case_tac h_pde; clarsimp simp: isSuperSectionPDE_def)
             apply (clarsimp simp: nth_Cons')
             apply (clarsimp simp: pde_lifts split: if_split)
             apply (rule conjI)
              apply (clarsimp simp: cpde_relation_def pde_pde_section_lift_def split del: split_of_bool)
              apply (rule is_aligned_neg_mask_eq)
              apply (erule is_aligned_weaken, simp)
             apply (clarsimp simp: addPDEOffset_def)
             apply (clarsimp simp: cpde_relation_def pde_pde_section_lift_def split del: split_of_bool)
             apply (clarsimp simp: gen_framesize_to_H_def X64LargePage_def X64Section_def X64SmallPage_def addPAddr_def fromPAddr_def)
             apply (rule is_aligned_neg_mask_eq)
             apply (drule is_aligned_add_multI[where n=21 and m=25, simplified], simp)
             apply (erule is_aligned_weaken, simp)
            apply simp
            apply (clarsimp simp: valid_pde_slots'2_def pde_range_relation_def ptr_range_to_list_def)
            apply (erule disjE; clarsimp simp: unat32_eq_of_nat word_bits_def)
           apply clarsimp
           apply vcg
           apply (clarsimp simp: valid_pde_slots'2_def)
           apply (rule conjI)
            apply (clarsimp simp: X64Section_def mask_def)
           apply (rule context_conjI)
            apply (case_tac a; clarsimp simp: isSuperSectionPDE_def cpde_relation_def addPDEOffset_def pde_lift_section)
           apply clarsimp
           apply (rule conjI, clarsimp)
            apply (clarsimp split: if_split_asm)
             apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
             apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
             apply (clarsimp simp: pde_lifts split del: split_of_bool cong: conj_cong)
             apply (rule is_aligned_neg_mask_eq)
             apply (erule is_aligned_weaken, simp)
            apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
            apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
            apply (clarsimp simp: pde_lifts split del: split_of_bool)
            apply (rule context_conjI)
             apply (rule is_aligned_neg_mask_eq)
             apply (erule is_aligned_weaken, simp)
            apply simp
           apply clarsimp
           apply (rule conjI, clarsimp)
            apply (clarsimp split: if_split_asm)
             apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
             apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
             apply (clarsimp simp: pde_lifts split del: split_of_bool)
             apply (rule is_aligned_neg_mask_eq)
             apply (erule is_aligned_weaken, simp)
            apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
            apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
            apply (clarsimp simp: pde_lifts split del: split_of_bool)
            apply (rule is_aligned_neg_mask_eq)
            apply (erule is_aligned_weaken, simp)
           apply (clarsimp split: if_split)
           apply (rule conjI, clarsimp)
            apply unat_arith
           apply clarsimp
           apply (erule disjE)
            apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
            apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
            apply (clarsimp simp: pde_lifts split del: split_of_bool)
            apply (rule is_aligned_neg_mask_eq)
            apply (erule is_aligned_weaken, simp)
           apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
           apply (clarsimp simp: cpde_relation_def addPDEOffset_def pde_lift_section split del: split_of_bool)
           apply (clarsimp simp: pde_lifts split del: split_of_bool)
           apply (clarsimp simp: X64Section_def X64LargePage_def X64SmallPage_def
                                 gen_framesize_to_H_def addPAddr_def fromPAddr_def)
           apply (rule is_aligned_neg_mask_eq)
           apply (drule is_aligned_add_multI[where n=21 and m=25, simplified], simp)
           apply (erule is_aligned_weaken, simp)
          apply (simp add: valid_pde_slots'2_def split_def)
          apply (rule hoare_pre, wpsimp wp: hoare_vcg_ex_lift, clarsimp)
         apply (auto simp: valid_pde_slots'2_def word_bits_def)[1]
        apply ceqv
       apply (rule_tac P="valid_pde_slots'2 mapping" in ccorres_cross_over_guard)
       apply csymbr
       apply (rule ccorres_move_c_guard_pde
                   ccorres_move_array_assertion_pde_16_2
                   ccorres_Guard_Seq
                   ccorres_rhs_assoc)+
       apply (ctac add: cleanCacheRange_PoU_ccorres)
         apply (rule ccorres_move_c_guard_pde
                     ccorres_move_array_assertion_pde_16_2
                     ccorres_rhs_assoc)+
         apply (simp add: when_def del: Collect_const)
         apply (rule ccorres_Cond_rhs_Seq)
          apply (simp add: to_bool_def)
          apply (rule ccorres_add_return2)
          apply (ctac (no_vcg) add: invalidateTLBByASID_ccorres)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp:return_def)
          apply (rule wp_post_taut)
         apply (simp add: to_bool_def)
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp:return_def)
        apply (wp hoare_vcg_const_imp_lift) [1]
       apply clarsimp
       apply (vcg exspec=cleanCacheRange_PoU_modifies)
      apply (clarsimp simp: to_bool_def)
      apply (rule hoare_strengthen_post)
       apply (rule_tac Q'="\<lambda>rv s. valid_pde_mappings' s
                 \<and> valid_pde_slots'2 mapping s
                 \<and> unat (last (snd (theRight mapping)) + 7
                     - hd (snd (theRight mapping))) \<le> gsMaxObjectSize s"
                in hoare_vcg_conj_lift)
        apply (rule mapM_x_accumulate_checks)
         apply (simp add: storePDE_def' split_def)
         apply (rule obj_at_setObject3)
          apply simp
         apply (simp add: objBits_simps archObjSize_def pdeBits_def)
        apply (simp add: typ_at_to_obj_at_arches[symmetric])
        apply ((wp mapM_x_storePDE_pde_mappings' mapM_x_wp' valid_pde_slots_lift2 | simp add: split_def)+)[2]
       apply (clarsimp simp: valid_pde_mapping'_def valid_pde_slots'2_def)
       apply (drule set_zip_helper, clarsimp)
      apply clarsimp
      apply (simp add: typ_at_to_obj_at_arches)
      apply (frule bspec, erule hd_in_zip_set)
      apply (drule bspec, erule last_in_zip_set)
       apply (clarsimp simp: valid_pde_slots'2_def)
      apply (simp add: hd_conv_nth last_conv_nth)
      apply (rule conj_assoc[where Q="a \<le> b" for a b, THEN iffD1])+
      apply (rule conjI)
    (* the inequalities first *)
       apply (clarsimp simp: valid_pde_slots'2_def
                             objBits_simps archObjSize_def hd_conv_nth pdeBits_def)
       apply (clarsimp simp:pde_range_relation_def ptr_range_to_list_def ptr_add_def)
       apply (frule is_aligned_addrFromPPtr_n,simp)
       apply (cut_tac n = "sz + 3" in  power_not_zero[where 'a="machine_word_len"])
        apply simp
       apply (subst is_aligned_no_wrap', assumption, fastforce simp: field_simps)
       apply (subst add_diff_eq [symmetric], subst is_aligned_no_wrap', assumption, fastforce simp: field_simps)
       apply simp
      apply (clarsimp simp: pde_range_relation_def ptr_add_def ptr_range_to_list_def
                            addrFromPPtr_mask_6)
      apply (auto simp: valid_pde_slots'2_def upt_conv_Cons[where i=0])[1]
     apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem hd_conv_nth last_conv_nth ucast_minus)
     apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def objBits_simps
                           archObjSize_def pdeBits_def)
     apply (simp add: CTypesDefs.ptr_add_def ucast_nat_def word_0_sle_from_less)
     apply (clarsimp simp: valid_pde_slots'2_def del: disjCI)
     apply (erule disjE, simp_all add: unat_arith_simps)[1]
     apply (clarsimp simp: upt_conv_Cons[where i=0])
    apply (wp valid_pde_slots_lift2 hoare_drop_imps)
   apply vcg
  apply simp
  apply (rule conjI, fastforce)
  apply (rule conjI)
   apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def unat_1_0
                         valid_pde_slots'2_def isRight_def last_map hd_map
                         ptr_add_def)
   apply (auto elim!: order_trans[rotated] simp: unat_word_ariths unat_arith_simps)[1]
  apply (clarsimp simp: isRight_def valid_pde_slots'2_def)
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply (clarsimp simp: pde_range_relation_def hd_map_simp ptr_range_to_list_def)
  apply (rule conjI)
   apply (rule c_guard_abs_pde[rule_format])
   apply (erule conjI, simp)
   apply (erule page_directory_at_pde_atD')
    apply (simp add: is_aligned_weaken)
   apply simp
  apply (clarsimp simp: unat_eq_of_nat split: if_split_asm)
   apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
   apply (clarsimp simp: cpde_relation_def pde_lift_section)
  apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
  apply (clarsimp simp: cpde_relation_def pde_lift_section)
  done *)


lemma performPageInvocationRemapPTE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
           and (\<lambda>_. asid \<le> mask asid_bits \<and> page_entry_map_corres mapping))
       (UNIV \<inter> {s. cpte_relation (thePTE (fst mapping)) (pte_' s)}
             \<inter> {s. ptSlot_' s = pte_Ptr (thePTEPtr (snd mapping))}
             \<inter> {s. asid_' s = asid}
             \<inter> {s. vspace_' s = pml4e_Ptr vspace}
             \<inter> {s. isVMPTE mapping}) []
       (liftE (performPageInvocation (PageRemap mapping asid vspace)))
       (Call performX86PageInvocationRemapPTE_'proc)"
  sorry (*
  (* FIXME: almost exact copy of the MapPTE case; extract lemma *)
  supply pageBitsForSize_le_32 [simp]
  apply (rule ccorres_gen_asm2)
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift:  pte_entries_' asid_')
   apply (rule_tac P="\<exists>s. valid_pte_slots'2 mapping s" in ccorres_gen_asm)
   apply (rule ccorres_gen_asm [where P ="snd (theLeft mapping)\<noteq>[]"])
   apply wpc
    prefer 2
    apply (simp add: isLeft_def)
   apply (simp add: split_def)
   apply (rename_tac h_pte_slots)
   apply (ctac add: pteCheckIfMapped_ccorres)
     apply csymbr
     apply (simp add: mapM_discarded whileAnno_def Collect_False del: Collect_const)
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_basic_srnoop2, simp)
     apply csymbr
     apply (rule ccorres_abstract_cleanup)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule_tac F="\<lambda>_. valid_pte_slots'2 mapping" and
                         Q="\<lbrace> cpte_relation (addPTEOffset (fst h_pte_slots) (if \<acute>i = 0 then 0 else \<acute>i - 1)) \<acute>pte \<and>
                              pteFrame (fst h_pte_slots) = base_address  \<rbrace>"
                   in ccorres_mapM_x_whileQ)
             apply (intro allI impI, simp add: split_def)
             apply (rule ccorres_rhs_assoc)+
             apply (rule ccorres_guard_imp2)
              apply csymbr
              apply (rule ccorres_Guard_Seq)
              apply csymbr
              apply (rule ccorres_abstract_cleanup)
              apply (rule ccorres_move_array_assertion_pte_16_2
                     | (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_pte_16_2))+
              apply (rule storePTE_Basic_ccorres'', simp)
             apply clarsimp
             apply (rename_tac h_pte slots n s s' x)
             apply (clarsimp simp: valid_pte_slots'2_def)
             apply (erule disjE)
              apply clarsimp
              apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def
                                    unat_of_nat upto_enum_word X64SmallPage_def)
              apply (case_tac h_pte; clarsimp simp: isLargePagePTE_def)
              apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
              apply (clarsimp simp: pte_lifts split del: split_of_bool)
             apply (clarsimp simp: Kernel_C.X64SmallPage_def)
             apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def
                                   upt_conv_Cons[where i=0] of_nat_gt_0
                                   unat_of_nat upto_enum_word pte_pte_small_lift_def)
             apply (case_tac h_pte; clarsimp simp: isLargePagePTE_def)
             apply (clarsimp simp: nth_Cons')
             apply (clarsimp simp: pte_lifts split: if_split)
             apply (rule conjI)
              apply (clarsimp simp: cpte_relation_def pte_pte_small_lift_def split del: split_of_bool)
              apply (rule is_aligned_neg_mask_eq)
              apply (erule is_aligned_weaken, simp)
             apply (clarsimp simp: addPTEOffset_def)
             apply (clarsimp simp: cpte_relation_def pte_pte_small_lift_def split del: split_of_bool)
             apply (clarsimp simp: gen_framesize_to_H_def X64SmallPage_def addPAddr_def fromPAddr_def)
             apply (rule is_aligned_neg_mask_eq)
             apply (erule is_aligned_add_multI[where n=12, simplified]; simp)
            apply simp
            apply (clarsimp simp: valid_pte_slots'2_def pte_range_relation_def ptr_range_to_list_def)
            apply (erule disjE; clarsimp simp: unat32_eq_of_nat word_bits_def)
           apply clarsimp
           apply vcg
           apply (clarsimp simp: valid_pte_slots'2_def)
           apply (rule conjI)
            apply (clarsimp simp: X64SmallPage_def)
           apply (rule context_conjI)
            apply (case_tac a; clarsimp simp: isLargePagePTE_def cpte_relation_def addPTEOffset_def pte_lift_small)
           apply clarsimp
           apply (rule conjI, clarsimp)
            apply (clarsimp split: if_split_asm)
             apply (case_tac a; clarsimp simp: isLargePagePTE_def)
             apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
             apply (clarsimp simp: pte_lifts split del: split_of_bool)
            apply (case_tac a; clarsimp simp: isLargePagePTE_def)
            apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
            apply (clarsimp simp: pte_lifts split del: split_of_bool)
            apply (rule context_conjI)
             apply (rule is_aligned_neg_mask_eq)
             apply (erule is_aligned_weaken, simp)
            apply simp
           apply clarsimp
           apply (rule conjI, clarsimp)
            apply (clarsimp split: if_split_asm)
             apply (case_tac a; clarsimp simp: isLargePagePTE_def)
             apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
             apply (clarsimp simp: pte_lifts split del: split_of_bool)
            apply (case_tac a; clarsimp simp: isLargePagePTE_def)
            apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
            apply (clarsimp simp: pte_lifts split del: split_of_bool)
            apply (rule is_aligned_neg_mask_eq)
            apply (erule is_aligned_weaken, simp)
           apply (clarsimp split: if_split)
           apply (rule conjI, clarsimp)
            apply unat_arith
           apply clarsimp
           apply (erule disjE)
            apply (case_tac a; clarsimp simp: isLargePagePTE_def)
            apply (clarsimp simp: cpte_relation_def pte_lift_small split del: split_of_bool)
            apply (clarsimp simp: pte_lifts split del: split_of_bool)
           apply (case_tac a; clarsimp simp: isLargePagePTE_def)
           apply (clarsimp simp: cpte_relation_def addPTEOffset_def pte_lift_small split del: split_of_bool)
           apply (clarsimp simp: pte_lifts split del: split_of_bool)
           apply (clarsimp simp: X64SmallPage_def gen_framesize_to_H_def addPAddr_def fromPAddr_def)
           apply (rule is_aligned_neg_mask_eq)
           apply (rule is_aligned_add_multI[where n=12, simplified], simp, simp, simp)
          apply (simp add: valid_pte_slots'2_def split_def)
          apply (rule hoare_pre, wpsimp wp: hoare_vcg_ex_lift, clarsimp)
         apply (auto simp: valid_pte_slots'2_def word_bits_def)[1]
        apply ceqv
       apply (rule_tac P="valid_pte_slots'2 mapping" in ccorres_cross_over_guard)
       apply csymbr
       apply (rule ccorres_move_c_guard_pte
                   ccorres_move_array_assertion_pte_16_2
                   ccorres_Guard_Seq
                   ccorres_rhs_assoc)+
       apply (ctac add: cleanCacheRange_PoU_ccorres)
         apply (rule ccorres_move_c_guard_pte
                     ccorres_move_array_assertion_pte_16_2
                     ccorres_rhs_assoc)+
         apply (simp add: when_def del: Collect_const)
         apply (rule ccorres_Cond_rhs_Seq)
          apply (simp add: to_bool_def)
          apply (rule ccorres_add_return2)
          apply (ctac (no_vcg) add: invalidateTLBByASID_ccorres)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp:return_def)
          apply (rule wp_post_taut)
         apply (simp add: to_bool_def)
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp:return_def)
        apply (wp hoare_vcg_const_imp_lift) [1]
       apply clarsimp
       apply (vcg exspec=cleanCacheRange_PoU_modifies)
      apply (clarsimp simp: to_bool_def)
      apply (rule hoare_strengthen_post)
       apply (rule_tac Q'="\<lambda>rv s. valid_pde_mappings' s
                 \<and> valid_pte_slots'2 mapping s
                 \<and> unat (last (snd (theLeft mapping)) + 7
                     - hd (snd (theLeft mapping))) \<le> gsMaxObjectSize s"
                in hoare_vcg_conj_lift)
        apply (rule mapM_x_accumulate_checks)
         apply (simp add: storePTE_def' split_def)
         apply (rule obj_at_setObject3)
          apply simp
         apply (simp add: objBits_simps archObjSize_def pteBits_def)
        apply (simp add: typ_at_to_obj_at_arches[symmetric])
        apply ((wp mapM_x_wp_inv hoare_vcg_ex_lift | simp add: split_def valid_pte_slots'2_def)+)[2]
      apply clarsimp
      apply (simp add: typ_at_to_obj_at_arches)
      apply (frule bspec, erule hd_in_zip_set)
      apply (drule bspec, erule last_in_zip_set)
       apply (clarsimp simp: valid_pte_slots'2_def)
      apply (simp add: hd_conv_nth last_conv_nth)
      apply (rule conj_assoc[where Q="a \<le> b" for a b, THEN iffD1])+
      apply (rule conjI)
    (* the inequalities first *)
       apply (clarsimp simp: valid_pte_slots'2_def
                             objBits_simps archObjSize_def hd_conv_nth pteBits_def)
       apply (clarsimp simp:pte_range_relation_def ptr_range_to_list_def ptr_add_def)
       apply (frule is_aligned_addrFromPPtr_n,simp)
       apply (cut_tac n = "sz + 3" in  power_not_zero[where 'a="machine_word_len"])
        apply simp
       apply (subst is_aligned_no_wrap', assumption, fastforce simp: field_simps)
       apply (subst add_diff_eq [symmetric], subst is_aligned_no_wrap', assumption, fastforce simp: field_simps)
       apply simp
      apply (clarsimp simp: pte_range_relation_def ptr_add_def ptr_range_to_list_def
                            addrFromPPtr_mask_6)
      apply (auto simp: valid_pte_slots'2_def upt_conv_Cons[where i=0])[1]
     apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem hd_conv_nth last_conv_nth ucast_minus)
     apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def objBits_simps
                             archObjSize_def pteBits_def)
     apply (simp add: CTypesDefs.ptr_add_def ucast_nat_def word_0_sle_from_less)
     apply (clarsimp simp: valid_pte_slots'2_def del: disjCI)
     apply (erule disjE, simp_all add: unat_arith_simps)[1]
     apply (clarsimp simp: upt_conv_Cons[where i=0])
    apply (wp valid_pte_slots_lift2 hoare_drop_imps)
   apply vcg
  apply simp
  apply (rule conjI)
   apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def unat_1_0
                         valid_pte_slots'2_def isLeft_def last_map hd_map
                         ptr_add_def)
   apply (auto elim!: order_trans[rotated] simp: unat_word_ariths unat_arith_simps)[1]
  apply (rule conjI, fastforce)
  apply (clarsimp simp: isLeft_def valid_pte_slots'2_def)
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply (clarsimp simp: pte_range_relation_def hd_map_simp ptr_range_to_list_def)
  apply (rule conjI)
   apply (rule c_guard_abs_pte[rule_format])
   apply (erule conjI, simp)
   apply (erule page_table_at_pte_atD')
    apply (simp add: is_aligned_weaken)
   apply simp
  apply (clarsimp simp: unat_eq_of_nat split: if_split_asm)
   apply (case_tac a; clarsimp simp: isLargePagePTE_def)
   apply (clarsimp simp: cpte_relation_def pte_lift_small)
  apply (case_tac a; clarsimp simp: isLargePagePTE_def)
  apply (clarsimp simp: cpte_relation_def pte_lift_small)
  done *)

definition
  "isVMPDPTE entry \<equiv> \<exists>x y. entry = (VMPDPTE x, VMPDPTEPtr y)"

primrec (nonexhaustive)
  thePDPTE :: "vmpage_entry \<Rightarrow> pdpte" where
  "thePDPTE (VMPDPTE pdpte) = pdpte"

primrec (nonexhaustive)
  thePDPTEPtr :: "vmpage_entry_ptr \<Rightarrow> machine_word" where
  "thePDPTEPtr (VMPDPTEPtr p) = p"

lemma performPageInvocationMapPDPTE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
              and (\<lambda>s. asid \<le> mask asid_bits \<and> page_entry_map_corres mapping))
       (UNIV \<inter> {s. cpdpte_relation (thePDPTE (fst mapping)) (pdpte_' s)}
             \<inter> {s. pdptSlot_' s = pdpte_Ptr (thePDPTEPtr (snd mapping))}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. vspace_' s = pml4e_Ptr vspace}
             \<inter> {s. isVMPDPTE mapping}) []
       (liftE (performPageInvocation (PageMap cap slot mapping vspace)))
       (Call performX64ModeMapRemapPage_'proc)"
  sorry

(* FIXME x64: need to split performX64ModeMapRemapPage into two functions
              for map and remap *)
lemma performPageInvocationRemapPDPTE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
              and (\<lambda>s. asid \<le> mask asid_bits \<and> page_entry_map_corres mapping))
       (UNIV \<inter> {s. cpdpte_relation (thePDPTE (fst mapping)) (pdpte_' s)}
             \<inter> {s. pdptSlot_' s = pdpte_Ptr (thePDPTEPtr (snd mapping))}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. vspace_' s = pml4e_Ptr vspace}
             \<inter> {s. isVMPDPTE mapping}) []
       (liftE (performPageInvocation (PageRemap mapping asid vspace)))
       (Call performX64ModeMapRemapPage_'proc)"
  sorry


lemma vmsz_aligned_addrFromPPtr':
  "vmsz_aligned' (addrFromPPtr p) sz
       = vmsz_aligned' p sz"
  apply (simp add: vmsz_aligned'_def addrFromPPtr_def
                   X64.addrFromPPtr_def)
  apply (subgoal_tac "is_aligned X64.pptrBase (pageBitsForSize sz)")
   apply (rule iffI)
    apply (drule(1) aligned_add_aligned)
      apply (simp add: pageBitsForSize_def word_bits_def split: vmpage_size.split)
     apply simp
   apply (erule(1) aligned_sub_aligned)
    apply (simp add: pageBitsForSize_def word_bits_def split: vmpage_size.split)
  apply (simp add: pageBitsForSize_def X64.pptrBase_def is_aligned_def bit_simps
            split: vmpage_size.split)
  done

lemmas vmsz_aligned_addrFromPPtr
    = vmsz_aligned_addrFromPPtr'
      vmsz_aligned_addrFromPPtr'[unfolded addrFromPPtr_def]
      vmsz_aligned_addrFromPPtr'[unfolded vmsz_aligned'_def]
      vmsz_aligned_addrFromPPtr'[unfolded addrFromPPtr_def vmsz_aligned'_def]

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
     apply (rule upcast_ucast_id[where 'b=machine_word_len]; simp add: asid_low_bits_of_mask_eq)
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

lemma list_length_less:
  "(args = [] \<or> length args \<le> Suc 0) = (length args < 2)"
  by (case_tac args,simp_all)

lemma unat_less_iff64:
  "\<lbrakk>unat (a::machine_word) = b;c < 2^word_bits\<rbrakk>
   \<Longrightarrow> (a < of_nat c) = (b < c)"
  apply (rule iffI)
    apply (drule unat_less_helper)
    apply simp
  apply (simp add:unat64_eq_of_nat)
  apply (rule of_nat_mono_maybe)
   apply (simp add:word_bits_def)
  apply simp
  done

lemma injection_handler_whenE:
  "injection_handler Inl (whenE a b)
   = (if a then (injection_handler Inl b)
      else (returnOk ()))"
  apply (subst injection_handler_returnOk[symmetric])
  apply (clarsimp simp:whenE_def injection_handler_def)
  apply (fastforce simp:split:if_splits)
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

lemma at_least_2_args:
  "\<not>  length args < 2 \<Longrightarrow> \<exists>a b c. args = a#b#c"
  apply (case_tac args)
   apply simp
  apply (case_tac list)
   apply simp
  apply (case_tac lista)
   apply simp
  apply simp
  done

lemma is_aligned_no_overflow3:
 "\<lbrakk>is_aligned (a::machine_word) n; n < word_bits ;b< 2^n; c \<le> 2^ n; b< c \<rbrakk>
  \<Longrightarrow> a + b \<le> a + (c - 1)"
  apply (rule word_plus_mono_right)
   apply (simp add:minus_one_helper3)
  apply (erule is_aligned_no_wrap')
  apply (auto simp:word64_less_sub_le)
  done

definition
  to_option :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a option"
where
  "to_option f x \<equiv> if f x then Some x else None"

(* FIXME: move *)
lemma valid_objs_valid_pte': "\<lbrakk> valid_objs' s ; ko_at' (ko :: pte) p s \<rbrakk> \<Longrightarrow> valid_pte' ko s"
  by (fastforce simp add: obj_at'_def ran_def valid_obj'_def projectKOs valid_objs'_def)

lemma cte_wp_at_diminished_gsMaxObjectSize:
  "cte_wp_at' (diminished' cap o cteCap) slot s
    \<Longrightarrow> valid_global_refs' s
    \<Longrightarrow> 2 ^ capBits cap \<le> gsMaxObjectSize s"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule(1) valid_global_refsD_with_objSize)
  apply (clarsimp simp: diminished'_def capMaster_eq_capBits_eq[OF capMasterCap_maskCapRights])
  done

lemma two_nat_power_pageBitsForSize_le:
  "(2 :: nat) ^ pageBits \<le> 2 ^ pageBitsForSize vsz"
  by (cases vsz, simp_all add: pageBits_def bit_simps)

lemma unat_sub_le_strg:
  "unat v \<le> v2 \<and> x \<le> v \<and> y \<le> v \<and> y < (x :: ('a :: len) word)
    \<longrightarrow> unat (x + (- 1 - y)) \<le> v2"
  apply clarsimp
  apply (erule order_trans[rotated])
  apply (fold word_le_nat_alt)
  apply (rule order_trans[rotated], assumption)
  apply (rule order_trans[rotated], rule word_sub_le[where y="y + 1"])
   apply (erule Word.inc_le)
  apply (simp add: field_simps)
  done

(* FIXME: move *)
lemma is_aligned_pageBitsForSize_minimum:
  "\<lbrakk> is_aligned p (pageBitsForSize sz) ; n \<le> pageBits \<rbrakk> \<Longrightarrow> is_aligned p n"
  apply (cases sz; clarsimp simp: pageBits_def)
  apply (erule is_aligned_weaken, simp)+
  done

(* FIXME: move *)
lemma mask_add_aligned_right:
  "is_aligned p n \<Longrightarrow> (q + p) && mask n = q && mask n"
  by (simp add: mask_add_aligned add.commute)

lemma ptrFromPAddr_add_left:
  "ptrFromPAddr (x + y) = ptrFromPAddr x + y"
  unfolding ptrFromPAddr_def by simp

lemma decodeX64FrameInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps;
          isPageCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' (diminished' (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. excaps_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86FrameInvocation_'proc)"

  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_' excaps_' cap_' buffer_'
                simp: decodeX64MMUInvocation_def )

   apply (simp add: Let_def isCap_simps invocation_eq_use_types split_def decodeX64FrameInvocation_def
               del: Collect_const
              cong: StateSpace.state.fold_congs globals.fold_congs
                    if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong)
 sorry (*
   apply (rule ccorres_Cond_rhs[rotated])+
         apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
        apply (rule ccorres_equals_throwError)
         apply (fastforce simp: throwError_bind invocationCatch_def
                        split: invocation_label.split arch_invocation_label.split)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (simp add: returnOk_bind bindE_assoc performX64MMUInvocations)
       apply (rule ccorres_rhs_assoc)+
       apply (ctac add: setThreadState_ccorres)
         apply csymbr
         apply (ctac(no_vcg) add: performPageGetAddress_ccorres)
           apply (rule ccorres_alternative2)
           apply (rule ccorres_return_CE, simp+)[1]
          apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
         apply wp+
       apply (vcg exspec=setThreadState_modifies)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr+
      apply (simp add: ivc_label_flush_case decodeX64PageFlush_def
                       list_case_If2 if3_fold2
                  del: Collect_const
                 cong: StateSpace.state.fold_congs globals.fold_congs
                      if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong)
      apply (simp add: if_1_0_0 split_def case_option_If2 if_to_top_of_bind
                  del: Collect_const cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong)
      apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
         apply vcg


        apply (clarsimp simp:list_length_less )
        apply (drule unat_less_iff32[where c =2])
         apply (simp add:word_bits_def)
        apply simp
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply csymbr
      apply csymbr
      apply csymbr
      apply (rule ccorres_if_cond_throws2[rotated -1,where Q = \<top> and Q' = \<top>])
         apply vcg
        apply (clarsimp)
        apply (frule ccap_relation_mapped_asid_0)
        apply fastforce
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply (simp add: invocationCatch_use_injection_handler
                       injection_bindE[OF refl refl] bindE_assoc
                       injection_handler_returnOk injection_handler_whenE
                       lookupError_injection)
      apply (ctac add: ccorres_injection_handler_csum1
                            [OF ccorres_injection_handler_csum1,
                             OF findPDForASID_ccorres])
         apply (rule ccorres_if_cond_throws
           [where P = False and Q = \<top> and Q'=\<top>
           ,simplified])
           apply simp
          apply (rule ccorres_add_return)
          apply (ctac add: getSyscallArg_ccorres_foo
            [where args=args and n=0 and buffer=buffer])
            apply (rule ccorres_add_return)
            apply (ctac add: getSyscallArg_ccorres_foo
              [where args = args and n = 1 and buffer = buffer])
              apply (simp only:if_to_top_of_bindE)
              apply (rule ccorres_if_cond_throws[rotated -1,where Q = \<top> and Q' = \<top>])
                 apply vcg
                apply (clarsimp simp:hd_drop_conv_nth hd_conv_nth)
               apply (simp add:injection_handler_throwError)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply (simp only:returnOk_bindE)
              apply csymbr
              apply csymbr
              apply (rule ccorres_Guard_Seq)
              apply csymbr
              apply csymbr
              apply csymbr
              apply (rule ccorres_if_cond_throws[rotated -1,where Q = \<top> and Q' = \<top>])
                 apply vcg
                apply (clarsimp simp:hd_drop_conv_nth hd_conv_nth)
                apply (clarsimp dest!: ccap_relation_PageCap_generics)
               apply (simp add:injection_handler_throwError)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply csymbr
              apply csymbr
              apply csymbr
              apply (simp add: performX64MMUInvocations bindE_assoc)
              apply (ctac add: setThreadState_ccorres)
                apply (ctac(no_vcg) add: performPageFlush_ccorres)
                  apply (rule ccorres_alternative2)
                  apply (rule ccorres_return_CE, simp+)[1]
                 apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                apply wp
               apply simp
               apply (strengthen unat_sub_le_strg[where v="2 ^ pageBitsForSize (capVPSize cp)"])
               apply (simp add: linorder_not_less linorder_not_le order_less_imp_le)
               apply (wp sts_invs_minor')
              apply simp
              apply (vcg exspec=setThreadState_modifies)
             apply simp
             apply wp
            apply vcg
           apply wp
          apply vcg
         apply vcg
        apply simp
        apply (rule_tac P'="{s. pd___struct_findPDForASID_ret_C = errstate s}"
                    in ccorres_from_vcg_split_throws[where P=\<top>])
         apply vcg
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                              syscall_error_to_H_cases exception_defs false_def)
        apply (erule lookup_failure_rel_fault_lift[rotated])
        apply (simp add: exception_defs)
       apply (wp injection_wp[OF refl])
      apply simp
      apply (vcg exspec=findPDForASID_modifies)

(* X64PageUnmap *)
     apply (simp add: returnOk_bind bindE_assoc
                      performX64MMUInvocations)
     apply (rule ccorres_rhs_assoc)+
     apply (ctac add: setThreadState_ccorres)
       apply (ctac(no_vcg) add: performPageInvocationUnmap_ccorres)
         apply (rule ccorres_alternative2)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
       apply wp
      apply (wp sts_invs_minor')
     apply simp
     apply (vcg exspec=setThreadState_modifies)

    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (simp add: if_1_0_0 word_less_nat_alt del: Collect_const)
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: throwError_bind invocationCatch_def
                     split: list.split)
     apply (simp del: Collect_const)
     apply (rule ccorres_cond_true_seq)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply csymbr
    apply (simp add: if_1_0_0 interpret_excaps_test_null
                     excaps_map_def del: Collect_const)
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: throwError_bind invocationCatch_def
                     split: list.split)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: list_case_If2 del: Collect_const)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply csymbr
        apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
        apply (rule ccorres_move_c_guard_cte)
        apply (rule_tac r'="\<lambda>rv rv'. ((cap_get_tag rv' = scast cap_page_directory_cap)
                                             = (isArchObjectCap rv \<and> isPageDirectoryCap (capCap rv)))
                                     \<and> (cap_get_tag rv' = scast cap_page_directory_cap \<longrightarrow> ccap_relation rv rv')"
                   and xf'=pdCap_' in ccorres_split_nothrow[where F=UNIV])
            apply (simp add: getSlotCap_def del: Collect_const)
            apply (rule ccorres_symb_exec_l[OF _ getCTE_inv getCTE_sp[where P=\<top>]
                        empty_fail_getCTE])
            apply (rule ccorres_from_vcg[where P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: return_def cte_wp_at_ctes_of)
            apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
            apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
            apply (clarsimp simp: typ_heap_simps' mask_def split_def
                                  cap_get_tag_isCap_ArchObject2
                                  word_sless_def word_sle_def
                           dest!: ccte_relation_ccap_relation)
           apply (simp add:sless_positive)
           apply ceqv
          apply (rule ccorres_assert2)
          apply csymbr+
          apply (frule length_ineq_not_Nil)
          apply (simp add: split_def cap_case_PageDirectoryCap2 if_1_0_0
                      del: Collect_const)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (simp add: invocationCatch_def throwError_bind
                            hd_conv_nth
                      cong: conj_cong)
           apply (rule ccorres_cond_true_seq)
           apply (rule ccorres_split_throws)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           apply vcg
          apply (rule ccorres_rhs_assoc)+
          apply csymbr+
          apply (simp add: case_option_If2 if_to_top_of_bind if_to_top_of_bindE
                           hd_conv_nth
                      del: Collect_const cong: conj_cong)
          apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
             apply vcg
            apply (clarsimp simp: if_1_0_0)
            apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                                  to_bool_def cap_page_directory_cap_lift_def
                           elim!: ccap_relationE split: if_split)
           apply (simp add: throwError_bind invocationCatch_def)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply csymbr+
          apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
             apply vcg
            apply (clarsimp simp: if_1_0_0)
            apply (frule ccap_relation_mapped_asid_0)
            apply auto[1]
           apply (simp add: throwError_bind invocationCatch_def)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply (simp add: createSafeMappingEntries_fold)
          apply (simp add: whenE_bindE_throwError_to_if
                           invocationCatch_use_injection_handler
                           injection_bindE[OF refl refl] bindE_assoc
                           injection_handler_returnOk
                           injection_handler_If if_to_top_of_bindE
                           lookupError_injection)
          apply csymbr
          apply csymbr
          apply csymbr
          apply csymbr
          apply csymbr
          apply (ctac add: ccorres_injection_handler_csum1
                                [OF ccorres_injection_handler_csum1,
                                 OF findPDForASID_ccorres])
             apply (simp add: Collect_False del: Collect_const)
             apply csymbr
             apply (simp add: if_1_0_0 del: Collect_const)
             apply (rule ccorres_Cond_rhs_Seq)
              apply (clarsimp simp: invocationCatch_def throwError_bind
                                    injection_handler_throwError)
              apply (rule ccorres_cond_true_seq)
              apply (rule ccorres_split_throws)
               apply (rule ccorres_inst [where P=\<top> and P'=UNIV])
               apply (rule ccorres_guard_imp)
                 apply (rule ccorres_if_lhs)
                  apply (rule syscall_error_throwError_ccorres_n)
                  apply (simp add: syscall_error_to_H_cases)
                 apply (rule ccorres_inst [where P=\<top> and P'=UNIV])
                 apply (clarsimp simp: isCap_simps cap_get_tag_isCap_unfolded_H_cap)
                 apply (erule ccap_relationE)+
                 apply (drule cap_lift_PDCap_Base [rotated], erule sym)
                 apply simp
                apply simp
               apply simp
              apply vcg
             apply (rule ccorres_rhs_assoc)+
             apply csymbr+
             apply (simp add: if_1_0_0 del: Collect_const)
             apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                apply vcg
               apply clarsimp
               apply (drule ccap_relation_PageCap_generics)
               apply (erule ccap_relationE)
               apply (clarsimp simp: isCap_simps)
               apply (frule (1) cap_lift_PDCap_Base)
               apply clarsimp
               apply (drule cap_to_H_PDCap)
               apply (clarsimp simp: cap_page_directory_cap_lift)
               apply auto[1]
              apply (clarsimp simp: invocationCatch_def throwError_bind
                                    injection_handler_throwError)
              apply (rule syscall_error_throwError_ccorres_n)
              apply (simp add: syscall_error_to_H_cases)
             apply csymbr
             apply csymbr
             apply csymbr
             apply (rule ccorres_symb_exec_r)
               apply csymbr
               apply (simp add: checkVPAlignment_def unlessE_def
                                injection_handler_If if_to_top_of_bindE
                           del: Collect_const)
               apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
                  apply vcg
                 apply (clarsimp simp add: from_bool_0 vmsz_aligned'_def is_aligned_mask)
                 apply (drule ccap_relation_PageCap_generics)
                 apply simp
                apply (simp add: injection_handler_throwError throwError_bind
                                 invocationCatch_def)
                apply (rule syscall_error_throwError_ccorres_n)
                apply (simp add: syscall_error_to_H_cases)
               apply csymbr
               apply csymbr
               apply (rule ccorres_Cond_rhs)
                apply (simp add: injection_handler_returnOk del: Collect_const)
                apply (rule ccorres_rhs_assoc)+
                apply csymbr
                apply (ctac add: ccorres_injection_handler_csum1
                                     [OF createSafeMappingEntries_PTE_ccorres])
                   apply (simp add: Collect_False performX64MMUInvocations
                                    bindE_assoc
                               del: Collect_const)
                   apply (ctac add: setThreadState_ccorres)
                     apply (ctac(no_vcg) add: performPageInvocationRemapPTE_ccorres)
                       apply (rule ccorres_alternative2)
                       apply (rule ccorres_return_CE, simp+)[1]
                      apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                     apply wp
                    apply (wp sts_invs_minor' valid_pte_slots_lift2)
                   apply simp
                   apply (vcg exspec=setThreadState_modifies)
                  apply simp
                  apply (rule ccorres_split_throws)
                   apply (rule ccorres_return_C_errorE, simp+)[1]
                  apply vcg
                 apply (simp add: createSafeMappingEntries_def)
                 apply (wp injection_wp[OF refl] createMappingEntries_valid_pte_slots'2)
                apply (simp add: all_ex_eq_helper)
                apply (vcg exspec=createSafeMappingEntries_PTE_modifies)
               apply (simp add: injection_handler_returnOk)
               apply (rule ccorres_rhs_assoc)+
               apply csymbr
               apply (ctac add: ccorres_injection_handler_csum1
                                   [OF createSafeMappingEntries_PDE_ccorres])
                  apply (simp add: performX64MMUInvocations bindE_assoc)
                  apply (ctac add: setThreadState_ccorres)
                    apply (ctac(no_vcg) add: performPageInvocationRemapPDE_ccorres)
                      apply (rule ccorres_alternative2)
                      apply (rule ccorres_return_CE, simp+)[1]
                     apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                    apply wp
                   apply (wp sts_invs_minor' valid_pde_slots_lift2)
                  apply simp
                  apply (vcg exspec=setThreadState_modifies)
                 apply simp
                 apply (rule ccorres_split_throws)
                  apply (rule ccorres_return_C_errorE, simp+)[1]
                 apply vcg
                apply (simp add: createSafeMappingEntries_def)
                apply (wp injection_wp[OF refl] createMappingEntries_valid_pde_slots'2)
               apply (simp add: all_ex_eq_helper)
               apply (vcg exspec=createSafeMappingEntries_PDE_modifies)
              apply (simp add: from_bool_0)
              apply vcg
             apply (rule conseqPre, vcg, clarsimp)
            apply simp
            apply (rule_tac P'="{s. find_ret = errstate s}"
                       in ccorres_from_vcg_split_throws[where P=\<top>])
             apply vcg
            apply (rule conseqPre, vcg)
            apply (clarsimp simp: fst_throwError_returnOk exception_defs
                                  syscall_error_rel_def syscall_error_to_H_cases
                                  false_def)
            apply (erule lookup_failure_rel_fault_lift[rotated])
            apply (simp add: exception_defs)
           apply (wp injection_wp[OF refl])
           apply simp
           apply (wp hoare_drop_imps)[1]
          apply simp
          apply (vcg exspec=findPDForASID_modifies)
         apply (simp add: getSlotCap_def)
         apply (wp getCTE_wp')
        apply simp
        apply (vcg exspec=getSyscallArg_modifies)
       apply simp
       apply wp
      apply simp
      apply (vcg exspec=getSyscallArg_modifies)
     apply simp
     apply wp
    apply simp
    apply (vcg exspec=getSyscallArg_modifies)

   -- "PageMap"
   apply (rule ccorres_rhs_assoc)+
   apply csymbr+
   apply (simp add: if_1_0_0 word_less_nat_alt del: Collect_const)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind invocationCatch_def
                    split: list.split)
    apply (simp del: Collect_const)
    apply (rule ccorres_cond_true_seq)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply csymbr
   apply (simp add: if_1_0_0 interpret_excaps_test_null
                    excaps_map_def del: Collect_const)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind invocationCatch_def
                    split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: list_case_If2 del: Collect_const)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply (rule ccorres_add_return)
       apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
         apply csymbr
         apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
         apply (rule ccorres_move_c_guard_cte)
         apply (rule_tac r'="\<lambda>rv rv'. ((cap_get_tag rv' = scast cap_page_directory_cap)
                                              = (isArchObjectCap rv \<and> isPageDirectoryCap (capCap rv)))
                                      \<and> (cap_get_tag rv' = scast cap_page_directory_cap \<longrightarrow> ccap_relation rv rv')"
                    and xf'=pdCap_' in ccorres_split_nothrow[where F=UNIV])
             apply (simp add: getSlotCap_def del: Collect_const)
             apply (rule ccorres_symb_exec_l[OF _ getCTE_inv getCTE_sp[where P=\<top>]
                         empty_fail_getCTE])
             apply (rule ccorres_from_vcg[where P'=UNIV])
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: return_def cte_wp_at_ctes_of)
             apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
             apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
             apply (clarsimp simp: typ_heap_simps' mask_def split_def
                                   cap_get_tag_isCap_ArchObject2
                                   word_sle_def word_sless_def
                            dest!: ccte_relation_ccap_relation)
            apply (simp add:sless_positive)
            apply ceqv
           apply (rule ccorres_assert2)
           apply csymbr+
           apply (frule length_ineq_not_Nil)
           apply (simp add: if_1_0_0 whenE_bindE_throwError_to_if
                            if_to_top_of_bind
                       del: Collect_const)
           apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
              apply vcg
             apply (drule ccap_relation_mapped_asid_0)
             apply fastforce
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           apply csymbr+
           apply (simp add: split_def cap_case_PageDirectoryCap2 if_1_0_0
                       del: Collect_const)
           apply (rule ccorres_Cond_rhs_Seq)
            apply (simp add: invocationCatch_def throwError_bind
                             hd_conv_nth
                       cong: conj_cong)
            apply (rule ccorres_cond_true_seq)
            apply (rule ccorres_split_throws)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply vcg
           apply (rule ccorres_rhs_assoc)+
           apply csymbr+
           apply (simp add: case_option_If2 if_to_top_of_bind if_to_top_of_bindE
                            hd_conv_nth
                       del: Collect_const cong: conj_cong)
           apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
              apply vcg
             apply (clarsimp simp: if_1_0_0)
             apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                                   to_bool_def cap_page_directory_cap_lift_def
                            elim!: ccap_relationE split: if_split)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply (simp add: createSafeMappingEntries_fold
                      cong: if_cong del: Collect_const)
           apply (simp add: lookupError_injection invocationCatch_use_injection_handler
                            injection_bindE[OF refl refl] injection_handler_returnOk
                            injection_handler_If injection_handler_throwError bindE_assoc
                       del: Collect_const cong: if_cong)
           apply (ctac add: ccorres_injection_handler_csum1
                                  [OF ccorres_injection_handler_csum1,
                                   OF findPDForASID_ccorres])
              apply (simp add: Collect_False if_to_top_of_bindE del: Collect_const)
              apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                 apply vcg
                apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                                      to_bool_def cap_page_directory_cap_lift_def
                               elim!: ccap_relationE split: if_split)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply csymbr+
              apply (rule ccorres_Guard_Seq)
              apply csymbr
              apply (simp add: if_to_top_of_bindE del: Collect_const)
              apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                 apply vcg
                apply (frule ccap_relation_PageCap_generics)
                apply (clarsimp simp add: kernelBase_def X64.kernelBase_def word_le_nat_alt)
               apply (simp add: throwError_bind invocationCatch_def)?
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply csymbr
              apply (rule ccorres_symb_exec_r)
                apply csymbr
                apply (simp add: bindE_assoc checkVPAlignment_def unlessE_def
                                 injection_handler_If if_to_top_of_bindE
                            del: Collect_const)
                apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
                   apply vcg
                  apply (clarsimp simp add: from_bool_0 vmsz_aligned'_def is_aligned_mask)
                  apply (drule ccap_relation_PageCap_generics)
                  apply simp
                 apply (simp add: injection_handler_throwError throwError_bind
                                  invocationCatch_def)
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (simp add: syscall_error_to_H_cases)
                apply csymbr
                apply csymbr
                apply csymbr
                apply (simp add: injection_handler_returnOk bindE_assoc
                            del: Collect_const)
                apply (rule ccorres_Cond_rhs)
                 apply (rule ccorres_rhs_assoc)+
                 apply csymbr
                 apply (ctac add: ccorres_injection_handler_csum1
                                      [OF createSafeMappingEntries_PTE_ccorres])
                    apply (simp add: performX64MMUInvocations bindE_assoc)
                    apply (ctac add: setThreadState_ccorres)
                      apply (ctac(no_vcg) add: performPageInvocationMapPTE_ccorres)
                        apply (rule ccorres_alternative2)
                        apply (rule ccorres_return_CE, simp+)[1]
                       apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                      apply (wp sts_invs_minor' valid_pte_slots_lift2)+
                    apply simp
                    apply (vcg exspec=setThreadState_modifies)
                   apply simp
                   apply (rule ccorres_split_throws)
                    apply (rule ccorres_return_C_errorE, simp+)
                   apply vcg
                  apply (simp add: createSafeMappingEntries_def)
                  apply (wp injection_wp[OF refl] createMappingEntries_valid_pte_slots'2)
                 apply (simp add: all_ex_eq_helper)
                 apply (vcg exspec=createSafeMappingEntries_PTE_modifies)
                apply (rule ccorres_rhs_assoc)+
                apply csymbr
                apply (ctac add: ccorres_injection_handler_csum1
                                    [OF createSafeMappingEntries_PDE_ccorres])
                   apply (simp add: performX64MMUInvocations bindE_assoc)
                   apply (ctac add: setThreadState_ccorres)
                     apply (ctac(no_vcg) add: performPageInvocationMapPDE_ccorres)
                       apply (rule ccorres_alternative2)
                       apply (rule ccorres_return_CE, simp+)[1]
                      apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                     apply wp
                    apply (wp sts_invs_minor' valid_pde_slots_lift2)
                   apply simp
                   apply (vcg exspec=setThreadState_modifies)
                  apply simp
                  apply (rule ccorres_split_throws)
                   apply (rule ccorres_return_C_errorE, simp+)[1]
                  apply vcg
                 apply (simp add: createSafeMappingEntries_def)
                 apply (wp injection_wp[OF refl] createMappingEntries_valid_pde_slots'2)
                apply (simp add: all_ex_eq_helper)
                apply (vcg exspec=createSafeMappingEntries_PDE_modifies)
               apply simp
               apply vcg
              apply (rule conseqPre, vcg, clarsimp)
             apply simp
             apply (rule_tac P'="{s. find_ret = errstate s}"
                      in ccorres_from_vcg_split_throws[where P=\<top>])
              apply vcg
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: fst_throwError_returnOk exception_defs
                                   syscall_error_rel_def syscall_error_to_H_cases
                                   false_def)
             apply (erule lookup_failure_rel_fault_lift[rotated])
             apply (simp add: exception_defs)
            apply simp
            apply (wp injection_wp[OF refl]
                        | wp_once hoare_drop_imps)+
           apply (simp add: all_ex_eq_helper)
           apply (vcg exspec=findPDForASID_modifies)
          apply (simp add: getSlotCap_def)
          apply (wp getCTE_wp')
         apply (simp add: if_1_0_0 del: Collect_const)
         apply vcg
        apply simp
        apply wp
       apply simp
       apply (vcg exspec=getSyscallArg_modifies)
      apply simp
      apply wp
     apply simp
     apply (vcg exspec=getSyscallArg_modifies)
    apply simp
    apply wp
   apply simp
   apply (vcg exspec=getSyscallArg_modifies)
  apply (rule conjI)
   apply clarsimp
   apply (frule cte_wp_at_diminished_gsMaxObjectSize, clarsimp)
   apply (clarsimp simp: cte_wp_at_ctes_of
                         is_aligned_mask[symmetric] vmsz_aligned'_def
                         vmsz_aligned_addrFromPPtr)
   apply (frule ctes_of_valid', clarsimp+)
   apply (simp add: diminished_valid'[symmetric])
   apply (clarsimp simp: valid_cap'_def capAligned_def
                         mask_def[where n=asid_bits]
                         linorder_not_le simp del: less_1_simp)
   apply (subgoal_tac "extraCaps \<noteq> [] \<longrightarrow> (s \<turnstile>' fst (extraCaps ! 0))")
    (* FIXME yuck; slow, likely partly redundant and runs for ~1.5min hence timing check *)
    apply (timeit \<open>(
             (clarsimp simp: ct_in_state'_def vmsz_aligned'_def isCap_simps
                             valid_cap'_def page_directory_at'_def
                             sysargs_rel_to_n linorder_not_less
                             excaps_map_def valid_tcb_state'_def
                   simp del: less_1_simp
           | rule conjI | erule pred_tcb'_weakenE disjE
           | erule(3) is_aligned_no_overflow3[OF vmsz_aligned_addrFromPPtr(3)[THEN iffD2]]
           | drule st_tcb_at_idle_thread' interpret_excaps_eq
           | erule order_le_less_trans[rotated] order_trans[where x=127, rotated]
           | rule order_trans[where x=127, OF _ two_nat_power_pageBitsForSize_le, unfolded pageBits_def]
           | clarsimp simp: neq_Nil_conv
           | ((drule_tac p2 = v0 in is_aligned_weaken[OF vmsz_aligned_addrFromPPtr(3)[THEN iffD2],
                where y = 7,OF _ le_trans[OF  _ pbfs_atleast_pageBits]],simp add:pageBits_def)
              , drule_tac w = b in is_aligned_weaken[
                where y = 7,OF _ le_trans[OF  _ pbfs_atleast_pageBits]]
              , simp add: pageBits_def
              , simp add: mask_add_aligned, simp add: field_simps, simp add: mask_add_aligned)
           | simp add: mask_add_aligned_right[OF is_aligned_pageBitsForSize_minimum, simplified pageBits_def]
                       mask_add_aligned[OF is_aligned_pageBitsForSize_minimum, simplified pageBits_def]
                       vmsz_aligned_addrFromPPtr
           | fastforce simp add: ptrFromPAddr_add_left is_aligned_no_overflow3[rotated -1]
           )+)[1]\<close>)
   apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def slotcap_in_mem_def
                         linorder_not_le)
   apply (erule ctes_of_valid', clarsimp)
  apply (clarsimp simp: if_1_0_0 rf_sr_ksCurThread "StrictC'_thread_state_defs"
                        mask_eq_iff_w2p word_size word_less_nat_alt
                        from_bool_0 excaps_map_def cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (simp only: diminished_valid'[symmetric])
  apply (clarsimp simp: valid_cap'_def capAligned_def word_sless_def word_sle_def)
  apply (subgoal_tac "cap_get_tag cap \<in> {scast cap_small_frame_cap, scast cap_frame_cap}")
   prefer 2
   apply (clarsimp simp: cap_to_H_def cap_lift_def Let_def elim!: ccap_relationE
                   split: if_split_asm)
  apply (rule conjI)
   apply clarsimp
   apply (frule ccap_relation_PageCap_generics)
   apply clarsimp
   apply (clarsimp simp: word_less_nat_alt vm_attribs_relation_def
                         attribsFromWord_def framesize_from_H_eq_eqs
                         of_bool_nth[simplified of_bool_from_bool]
                         vm_page_size_defs neq_Nil_conv excaps_in_mem_def
                         hd_conv_nth numeral_2_eq_2)
   apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
   apply (frule(1) slotcap_in_mem_PageDirectory)
   apply (clarsimp simp: mask_def[where n=4] typ_heap_simps')
   apply (clarsimp simp: isCap_simps)
   apply (frule slotcap_in_mem_valid, clarsimp+)
   apply (erule_tac c="ArchObjectCap (PageDirectoryCap a b)" for a b in ccap_relationE)
   apply (clarsimp simp: cap_lift_page_directory_cap to_bool_def
                         cap_page_directory_cap_lift_def
                         cap_to_H_def[split_simps cap_CL.split]
                         valid_cap'_def)
   apply (drule(1) generic_frame_cap_set_capFMappedAddress_ccap_relation)
       apply (simp add: isCap_simps)
      apply (simp add: mask_def)
     apply clarsimp
    apply simp
   apply (simp add: gen_framesize_to_H_def vm_page_size_defs
                    hd_conv_nth length_ineq_not_Nil
             split: if_split)
   apply (simp add: vm_page_size_defs bit_simps split: if_split_asm)
  apply (clarsimp simp:signed_shift_guard_simpler_32 pbfs_less)
  apply (frule ccap_relation_PageCap_generics)
  apply (clarsimp simp:framesize_from_H_eq_eqs)
  apply (intro conjI impI)
      apply (clarsimp simp: word_less_nat_alt framesize_from_H_eq_eqs
                        vm_page_size_defs gen_framesize_to_H_def
                        attribsFromWord_def vm_attribs_relation_def isCap_simps
                        of_bool_nth[simplified of_bool_from_bool])
      apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
      apply (erule_tac c="ArchObjectCap (PageDirectoryCap a b)" for a b in ccap_relationE)
      apply (clarsimp simp: cap_lift_page_directory_cap to_bool_def
                            cap_page_directory_cap_lift_def
                            cap_to_H_def[split_simps cap_CL.split] valid_cap'_def)
      apply (clarsimp split:if_splits)
     apply (clarsimp simp:
       unat_less_helper isPageFlush_def isPageFlushLabel_def
       dest!:at_least_2_args | intro flushtype_relation_triv allI impI conjI)+
  done *)

(* FIXME x64: find out some handy ones for X64 *)
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

declare Word_Lemmas.from_bool_mask_simp [simp]

lemma injection_handler_liftE:
  "injection_handler a (liftE f) = liftE f"
  by (simp add:injection_handler_def)


lemma liftE_case_sum:
  "liftE f >>= case_sum (throwError \<circ> Inr) g = f >>= g"
  by (simp add:liftE_def)

lemma throwError_invocationCatch:
  "throwError a >>= invocationCatch b c d e = throwError (Inl a)"
  by (simp add:throwError_def invocationCatch_def)

lemma framesize_from_H_mask2:
  "framesize_from_H a && mask 2 = framesize_from_H a"
  apply (rule less_mask_eq)
  apply (simp add:framesize_from_H_def
    split: vmpage_size.splits)
    apply (simp add:Kernel_C.X86_SmallPage_def
      Kernel_C.X86_LargePage_def
      Kernel_C.X64_HugePage_def)+
  done

lemma rel_option_alt_def:
  "rel_option f a b = (
      (a = None \<and>  b = None)
      \<or> (\<exists>x y. a = Some x \<and>  b = Some y \<and> f x y))"
  apply (case_tac a, case_tac b, simp, simp, case_tac b, auto)
  done

lemma injection_handler_stateAssert_relocate:
  "injection_handler Inl (stateAssert ass xs >>= f) >>=E g
    = do v \<leftarrow> stateAssert ass xs; injection_handler Inl (f ()) >>=E g od"
  by (simp add: injection_handler_def handleE'_def bind_bindE_assoc bind_assoc)

(* FIXME: move to where is_aligned_ptrFromPAddr is *)
lemma is_aligned_ptrFromPAddr_pageBitsForSize:
  "is_aligned p (pageBitsForSize sz) \<Longrightarrow> is_aligned (ptrFromPAddr p) (pageBitsForSize sz)"
  by (cases sz ; simp add: is_aligned_ptrFromPAddr_n pageBits_def bit_simps)

lemma decodeX64PageDirectoryInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps;
          isPageDirectoryCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' (diminished' (ArchObjectCap cp) \<circ> cteCap) slot
              and valid_cap' (ArchObjectCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. excaps_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX64PageDirectoryInvocation_'proc)"
  sorry

lemma decodeX64PDPTInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps;
          isPDPointerTableCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' (diminished' (ArchObjectCap cp) \<circ> cteCap) slot
              and valid_cap' (ArchObjectCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. excaps_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX64PDPTInvocation_'proc)"
  sorry

lemma decodeX64MMUInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps \<rbrakk>
   \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' (diminished' (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. excaps_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeX64MMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeX86MMUInvocation_'proc)"
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_'
                      excaps_' cap_' buffer_')
   apply csymbr
   apply (simp add: cap_get_tag_isCap_ArchObject
                    X64_H.decodeInvocation_def
                    invocation_eq_use_types
               del: Collect_const
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE,simp+)
    apply (rule ccorres_call,
      rule decodeX64FrameInvocation_ccorres,
      simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call,
           rule decodeX64PageTableInvocation_ccorres, simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
 (* FIXME x64: ASID Control Invocation *)
  sorry (*
    apply (simp add: conj_disj_distribL[symmetric])
    apply (rule ccorres_call,
           rule decodeX64FrameInvocation_ccorres, simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (simp add: imp_conjR[symmetric] decodeX64MMUInvocation_def
                del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: throwError_bind invocationCatch_def
                     split: invocation_label.split arch_invocation_label.split)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: word_less_nat_alt list_case_If2 split_def
                del: Collect_const)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: if_1_0_0)
     apply (rule ccorres_cond_true_seq | simp)+
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: if_1_0_0 interpret_excaps_test_null
                     excaps_map_def
                del: Collect_const)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: if_1_0_0 | rule ccorres_cond_true_seq)+
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply csymbr
    apply (simp add: if_1_0_0 interpret_excaps_test_null[OF Suc_leI]
                del: Collect_const)
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: length_ineq_not_Nil throwError_bind
                      invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (subgoal_tac "1 < List.length extraCaps")
     prefer 2
     apply (rule neq_le_trans, simp)
     apply (simp add: Suc_leI)
    apply (simp add: Let_def split_def liftE_bindE bind_assoc
                     length_ineq_not_Nil
                del: Collect_const)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply csymbr
        apply (rule ccorres_add_return,
               rule_tac xf'=untyped_' and r'="(\<lambda>rv _ un.
                    (cap_get_tag un = scast cap_untyped_cap) = isUntypedCap rv
                        \<and> (isUntypedCap rv \<longrightarrow> ccap_relation rv un))
                    (fst (extraCaps ! 0))" in ccorres_split_nothrow)
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
            apply (rule ccorres_pre_gets_armKSASIDTable_ksArchState)
            apply (rename_tac "armKSASIDTab")
            apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                   rule ccorres_rhs_assoc2)
            apply (rule ccorres_add_return)
            apply (rule_tac r'="\<lambda>rv rv'. rv' = (case [p \<leftarrow> assocs armKSASIDTab.
                                                      fst p < 2 ^ asid_high_bits \<and> snd p = None]
                                                of [] \<Rightarrow> 2 ^ asid_high_bits | x # xs \<Rightarrow> fst x)"
                    and xf'=i_' in ccorres_split_nothrow)
                apply (rule_tac P="\<forall>x \<in> ran armKSASIDTab. x \<noteq> 0"
                             in ccorres_gen_asm)
                apply (rule_tac P="\<lambda>s. armKSASIDTab = armKSASIDTable (ksArchState s)"
                             in ccorres_from_vcg[where P'=UNIV])
                apply (clarsimp simp: return_def)
                apply (rule HoarePartial.SeqSwap)
                 apply (rule_tac I="{t. (\<sigma>, t) \<in> rf_sr \<and> i_' t \<le> 2 ^ asid_high_bits
                                        \<and> armKSASIDTab = armKSASIDTable (ksArchState \<sigma>)
                                        \<and> (\<forall>x < i_' t. armKSASIDTab x \<noteq> None)
                                        \<and> ret__int_' t = from_bool (i_' t < 2 ^ asid_high_bits
                                                  \<and> armKSASIDTab (i_' t) \<noteq> None)}"
                              in HoarePartial.reannotateWhileNoGuard)
                 apply (rule HoarePartial.While[OF order_refl])
                  apply (rule conseqPre, vcg)
                  apply (clarsimp simp: asidHighBits_handy_convs
                                        word_sle_def word_sless_def
                                        if_1_0_0 word_less_nat_alt[symmetric]
                                        from_bool_0)
                  apply (cut_tac P="\<lambda>y. y < i_' x + 1 = rhs y" for rhs in allI,
                         rule less_x_plus_1)
                   apply (clarsimp simp: max_word_def asid_high_bits_def)
                  apply (clarsimp simp: rf_sr_armKSASIDTable from_bool_def
                                        asid_high_bits_word_bits
                                        option_to_ptr_def option_to_0_def
                                        order_less_imp_le
                                        linorder_not_less
                                        order_antisym[OF inc_le])
                  apply (clarsimp simp: true_def false_def
                                 split: option.split if_split)
                  apply (simp add: asid_high_bits_def word_le_nat_alt
                                   word_less_nat_alt unat_add_lem[THEN iffD1])
                  apply auto[1]
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
                                      word_sless_def if_1_0_0 from_bool_0
                                      rf_sr_armKSASIDTable[where n=0, simplified])
                apply (simp add: asid_high_bits_def option_to_ptr_def option_to_0_def
                                 from_bool_def
                          split: option.split if_split)
                apply fastforce
               apply ceqv
              apply (rule ccorres_Guard_Seq)+
              apply (simp add: whenE_bindE_throwError_to_if if_to_top_of_bind
                          del: Collect_const)
              apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
                 apply clarsimp
                 apply (rule conseqPre, vcg, rule subset_refl)
                apply (clarsimp simp: asid_high_bits_word_bits asidHighBits_handy_convs null_def)
                apply (clarsimp split: list.split)
                apply (clarsimp dest!: filter_eq_ConsD)
               apply (simp add: throwError_bind invocationCatch_def)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply (rule ccorres_Guard_Seq)+
              apply (simp add: invocationCatch_use_injection_handler
                               injection_bindE[OF refl refl] injection_handler_If
                               injection_handler_returnOk bindE_assoc
                               injection_handler_throwError
                         cong: if_cong del: Collect_const)
              apply csymbr
              apply csymbr
              apply csymbr
              apply (rule ccorres_symb_exec_r)
                apply (rule_tac xf'=ret__int_' in ccorres_abstract, ceqv)
                  apply (rule_tac P = "rv'a = from_bool (\<not>( isUntypedCap (fst (hd extraCaps)) \<and>
                            capBlockSize (fst (hd extraCaps)) = objBits (makeObject ::asidpool)
                            ))" in ccorres_gen_asm2)
                  apply csymbr
                apply (rule ccorres_symb_exec_r)
                  apply (rule_tac xf'=ret__int_' in ccorres_abstract, ceqv)
                  apply (rule_tac P = "rv'b = from_bool (\<not>( isUntypedCap (fst (hd extraCaps)) \<and>
                                capBlockSize (fst (hd extraCaps)) = objBits (makeObject ::asidpool)
                                \<and> \<not> capIsDevice (fst (hd extraCaps))))"
                            in ccorres_gen_asm2)
                  apply (clarsimp simp: if_1_0_0 to_bool_if cond_throw_whenE bindE_assoc
                    from_bool_neq_0)
                  apply (rule ccorres_split_when_throwError_cond[where Q = \<top> and Q' = \<top>])
                     apply fastforce
                    apply (rule syscall_error_throwError_ccorres_n)
                    apply (clarsimp simp: syscall_error_rel_def shiftL_nat syscall_error_to_H_cases)
                   prefer 2
                   apply vcg
                  apply clarsimp
                  apply (ctac add: ccorres_injection_handler_csum1
                                     [OF ensureNoChildren_ccorres])
                     apply (clarsimp simp add: Collect_False del: Collect_const)
                     apply csymbr
                     apply csymbr
                     apply (ctac add: ccorres_injection_handler_csum1
                                        [OF lookupTargetSlot_ccorres,
                                         unfolded lookupTargetSlot_def])
                        apply (simp add: Collect_False split_def del: Collect_const)
                        apply csymbr
                        apply (ctac add: ccorres_injection_handler_csum1
                                           [OF ensureEmptySlot_ccorres])
                           apply (simp add: ccorres_invocationCatch_Inr
                                            performInvocation_def
                                            X64_H.performInvocation_def
                                            performX64MMUInvocation_def)
                           apply (simp add: liftE_bindE)
                           apply (ctac add: setThreadState_ccorres)
                             apply (simp only: liftE_bindE[symmetric])
                             apply (ctac(no_vcg) add: performASIDControlInvocation_ccorres
                               [where idx = "capFreeIndex (fst (extraCaps ! 0))"])
                               apply (rule ccorres_alternative2)
                               apply (rule ccorres_return_CE, simp+)[1]
                              apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                             apply wp
                            apply (wp sts_invs_minor' sts_Restart_ct_active)
                           apply simp
                           apply (vcg exspec=setThreadState_modifies)
                          apply simp
                          apply (rule ccorres_split_throws)
                           apply (rule ccorres_return_C_errorE, simp+)
                          apply vcg
                         apply simp
                         apply (wp injection_wp[OF refl])
                        apply (simp add: all_ex_eq_helper)
                        apply (vcg exspec=ensureEmptySlot_modifies)
                       apply simp
                       apply (rule ccorres_split_throws)
                        apply (rule ccorres_return_C_errorE, simp+)
                       apply vcg
                      apply (wp injection_wp[OF refl])
                     apply (simp add: split_def all_ex_eq_helper)
                     apply (vcg exspec=lookupTargetSlot_modifies)
                    apply simp
                    apply (rule ccorres_split_throws)
                     apply (rule ccorres_return_C_errorE, simp+)
                    apply vcg
                   apply simp
                   apply (wp injection_wp[OF refl] ensureNoChildren_wp)
                  apply (simp add: all_ex_eq_helper cap_get_tag_isCap)
                  apply (vcg exspec=ensureNoChildren_modifies)
                 apply simp
                 apply clarsimp
                 apply vcg
                apply clarsimp
                apply (rule conseqPre,vcg,clarsimp)
               apply clarsimp
               apply vcg
              apply clarsimp
              apply (rule conseqPre,vcg,clarsimp)
             apply (clarsimp split: list.splits
                              simp: Kernel_C.asidHighBits_def asid_high_bits_def word_0_sle_from_less)
             apply (frule interpret_excaps_eq[rule_format, where n=0],fastforce)
             apply (simp add: interpret_excaps_test_null excaps_map_def
                              list_case_If2 split_def
                         del: Collect_const)
              apply (simp add: if_1_0_0 from_bool_0 hd_conv_nth length_ineq_not_Nil
                          del: Collect_const)
              apply (clarsimp simp: eq_Nil_null[symmetric] asid_high_bits_word_bits hd_conv_nth
                ThreadState_Restart_def mask_def)
              apply wp+
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
   apply (rule ccorres_Cond_rhs) -- "ASIDPoolCap case"
    apply (simp add: imp_conjR[symmetric] decodeX64MMUInvocation_def
                del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: throwError_bind invocationCatch_def
                      split: invocation_label.split arch_invocation_label.split)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: interpret_excaps_test_null excaps_map_def
                     list_case_If2 split_def
                del: Collect_const)
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: Let_def split_def del: Collect_const)
    apply csymbr
    apply (rule ccorres_add_return)
    apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_page_directory_cap)
                                     = (isArchObjectCap rv \<and> isPageDirectoryCap (capCap rv)))
                          \<and> (cap_get_tag rv' = scast cap_page_directory_cap \<longrightarrow> ccap_relation rv rv'))
                              (fst (extraCaps ! 0))"
                    and xf'=pdCap_' in ccorres_split_nothrow[where F=UNIV])
        apply (rule_tac P="excaps_in_mem extraCaps \<circ> ctes_of"
                             in ccorres_from_vcg[where P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def neq_Nil_conv excaps_in_mem_def)
        apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
        apply (frule(1) slotcap_in_mem_PageDirectory)
        apply (clarsimp simp: typ_heap_simps' mask_def[where n=4])
       apply ceqv
      apply csymbr
      apply csymbr
      apply (simp add: cap_get_tag_isCap_ArchObject2 if_1_0_0
                       cap_case_PageDirectoryCap2
                  del: Collect_const)
      apply (rule ccorres_Cond_rhs_Seq)
       apply (simp add: hd_conv_nth cong: conj_cong)
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule ccorres_cond_true_seq)
       apply (rule ccorres_split_throws)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply vcg
      apply (simp del: Collect_const)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply (simp add: if_1_0_0 hd_conv_nth del: Collect_const)
      apply wpc
       apply (rule ccorres_cond_false_seq)
       apply (simp add: liftME_def bindE_assoc del: Collect_const)
       apply (simp add: liftE_bindE bind_assoc del: Collect_const)
       apply (rule ccorres_pre_gets_armKSASIDTable_ksArchState[unfolded o_def])
       apply csymbr
       apply (rule ccorres_Guard_Seq)+
       apply (rule ccorres_add_return)
       apply (rule_tac r'="\<lambda>_ rv'. rv' = option_to_ptr (x (ucast (asid_high_bits_of (capASIDBase cp))))
                                \<and> x (ucast (asid_high_bits_of (capASIDBase cp))) \<noteq> Some 0"
                  and xf'=pool_' in ccorres_split_nothrow)
           apply (rule_tac P="\<lambda>s. x = armKSASIDTable (ksArchState s)
                                  \<and> valid_arch_state' s \<and> s \<turnstile>' ArchObjectCap cp"
                       in  ccorres_from_vcg[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def valid_arch_state'_def
                                 valid_asid_table'_def cap_get_tag_isCap_ArchObject[symmetric])
           apply (erule_tac v=cap in ccap_relationE)
           apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_def valid_cap'_def
                                 cap_asid_pool_cap_lift_def)
           apply (subst rf_sr_armKSASIDTable, assumption)
            apply (simp add: asid_high_bits_word_bits)
            apply (rule shiftr_less_t2n)
            apply (simp add: asid_low_bits_def asid_high_bits_def asid_bits_def)
           apply (simp add: ucast_asid_high_bits_is_shift mask_def)
           apply fastforce
          apply ceqv
         apply (simp add: whenE_bindE_throwError_to_if if_to_top_of_bind
                    cong: if_cong del: Collect_const)
         apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
            apply vcg
           apply (simp add: option_to_0_def option_to_ptr_def split: option.split)
           apply clarsimp
          apply (simp add: throwError_bind invocationCatch_def)
          apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: throwError_def return_def
                                syscall_error_rel_def exception_defs
                                syscall_error_to_H_cases false_def)
          apply (simp add: lookup_fault_lift_invalid_root)
         apply csymbr
         apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
            apply vcg
           apply (clarsimp simp: option_to_0_def option_to_ptr_def
                                 cap_get_tag_isCap_ArchObject[symmetric]
                          elim!: ccap_relationE)
           apply (simp add: cap_asid_pool_cap_lift cap_to_H_def)
          apply (simp add: throwError_bind invocationCatch_def)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply csymbr
         apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                rule ccorres_rhs_assoc2)
         apply (simp add: bind_assoc del: Collect_const)
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
                                                          \<or> index (array_C v) (unat x) \<noteq> pde_Ptr 0)
                                          \<and> ret__int_' t = from_bool (i_' t < 2 ^ asid_low_bits
                                               \<and> (capASIDBase cp + (i_' t) = 0
                                                   \<or> index (array_C v) (unat (i_' t)) \<noteq> pde_Ptr 0)))}"
                           in HoarePartial.reannotateWhileNoGuard)
              apply (rule HoarePartial.While[OF order_refl])
               apply (rule conseqPre, vcg)
               apply (clarsimp simp: asidLowBits_handy_convs
                                     word_sle_def word_sless_def
                                     if_1_0_0 from_bool_0)
               apply (subgoal_tac "capASIDBase_CL (cap_asid_pool_cap_lift cap)
                                       = capASIDBase cp")
                apply (subgoal_tac "\<And>x. (x < (i_' xb + 1))
                                          = (x < i_' xb \<or> x = i_' xb)")
                 apply (clarsimp simp: inc_le from_bool_def typ_heap_simps
                                       asid_low_bits_def not_less field_simps
                                       false_def
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
                apply (clarsimp simp: max_word_def asid_low_bits_def)
               apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
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
               apply (drule_tac f="\<lambda>xs. (a, b) \<in> set xs" in arg_cong)
               apply (clarsimp simp: in_assocs_is_fun)
               apply (drule spec, drule(1) mp)
               apply (simp add: asid_low_bits_word_bits)
               apply (drule spec, drule(1) mp)
               apply (simp add: option_to_ptr_def option_to_0_def field_simps)
              apply (frule(1) neq_le_trans)
              apply (subst filter_assocs_Cons)
                apply (simp add: split_def asid_low_bits_word_bits)
                apply (rule conjI, assumption)
                apply (clarsimp simp add: field_simps)
                apply (drule spec, drule(1) mp)
                apply (simp add: option_to_ptr_def option_to_0_def
                          split: option.split_asm)
                apply (drule bspec, erule ranI, simp)
               apply (simp add: asid_low_bits_word_bits)
               apply (erule allEI, rule impI, drule(1) mp)
               apply (clarsimp simp: field_simps)
               apply (drule_tac x=xa in spec)
               apply (simp add: option_to_ptr_def option_to_0_def)
              apply simp
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: asidLowBits_handy_convs if_1_0_0
                                   signed_shift_guard_simpler_32 asid_low_bits_def
                                   word_sless_def word_sle_def)
             apply (erule cmap_relationE1[OF rf_sr_cpspace_asidpool_relation],
                    erule ko_at_projectKO_opt)
             apply (clarsimp simp: typ_heap_simps from_bool_def split: if_split)
             apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
             apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_def
                                   cap_asid_pool_cap_lift_def false_def
                                   ucast_minus ucast_nat_def
                            elim!: ccap_relationE)
            apply ceqv
           apply (rule ccorres_Guard_Seq)+
           apply (simp add: if_to_top_of_bind del: Collect_const)
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
         apply (simp del: Collect_const)
         apply (rule HoarePartial.SeqSwap)
          apply (rule_tac I="\<lbrace>\<forall>rv. Prop \<acute>ksCurThread \<acute>pdCapSlot rv\<rbrace>"
                      and Q="\<lbrace>\<forall>rv. Bonus \<acute>i rv \<longrightarrow> Prop \<acute>ksCurThread \<acute>pdCapSlot rv\<rbrace>"
                      for Prop Bonus in HoarePartial.reannotateWhileNoGuard)
          apply vcg
           apply clarsimp
          apply clarsimp
         apply vcg
        apply simp
        apply wp
       apply (simp add: if_1_0_0 cong: if_cong)
       apply vcg
      apply (rule ccorres_cond_true_seq)
      apply (simp add: throwError_bind invocationCatch_def)
      apply (rule ccorres_split_throws)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply vcg
     apply simp
     apply wp
    apply simp
    apply vcg
   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
   apply (cases cp, simp_all add: isCap_simps)[1]
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of ct_in_state'_def
                         if_1_0_0 interpret_excaps_eq excaps_map_def)
   apply (frule(1) ctes_of_valid', simp only: diminished_valid'[symmetric])
   apply (cases "extraCaps")
    apply simp
   apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
   apply (clarsimp simp: mask_def[where n=4] excaps_in_mem_def
                         slotcap_in_mem_def typ_at_to_obj_at_arches
                         obj_at'_weakenE[OF _ TrueI] invs_arch_state'
                         unat_lt2p[where 'a=32, folded word_bits_def])
   apply (rule conjI)
    apply (frule invs_arch_state')
    apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def neq_Nil_conv)
    apply (frule interpret_excaps_eq[rule_format, where n=1], simp)
    apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt)
    apply (drule length_le_helper | clarsimp simp: linorder_not_less)+
    apply (rule conjI)
     apply clarsimp
    apply (clarsimp simp: tcb_at_invs' Kernel_C.asidLowBits_def)
    apply (clarsimp simp:invs_valid_objs')
    apply (rule conjI, fastforce)
    apply (clarsimp simp: ctes_of_valid' invs_valid_objs' isCap_simps)
    apply (clarsimp simp: ex_cte_cap_wp_to'_def cte_wp_at_ctes_of
                          invs_sch_act_wf' dest!: isCapDs(1))
    apply (intro conjI)
            apply (simp add: Invariants_H.invs_queues)
           apply (simp add: valid_tcb_state'_def)
          apply (fastforce elim!: pred_tcb'_weakenE dest!:st_tcb_at_idle_thread')
         apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
         apply (case_tac "tcbState obja", (simp add: runnable'_def)+)[1]
        apply simp
       apply (simp add: objBits_simps archObjSize_def)
      apply fastforce
     apply (drule_tac f="\<lambda>xs. (a, bb) \<in> set xs" in arg_cong)
      apply (clarsimp simp: in_assocs_is_fun)
     apply (rule unat_less_helper)
     apply (clarsimp simp: asid_low_bits_def)
     apply (rule shiftl_less_t2n)
      apply (simp add: asid_bits_def minus_one_helper5)+
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
                          asid_low_bits_word_bits
                   dest!: filter_eq_ConsD)
    apply (subst is_aligned_add_less_t2n[rotated], assumption+)
       apply (simp add: asid_low_bits_def asid_bits_def)
      apply simp
     apply simp
    apply (auto simp: ct_in_state'_def valid_tcb_state'_def
               dest!: st_tcb_at_idle_thread'
               elim!: pred_tcb'_weakenE)[1]
  apply (clarsimp simp: if_1_0_0 cte_wp_at_ctes_of asidHighBits_handy_convs
                        word_sle_def word_sless_def asidLowBits_handy_convs
                        rf_sr_ksCurThread "StrictC'_thread_state_defs"
                        mask_def[where n=4]
                  cong: if_cong)
  apply (clarsimp simp: if_1_0_0 to_bool_def ccap_relation_isDeviceCap2
     objBits_simps archObjSize_def pageBits_def from_bool_def case_bool_If)
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
                         hd_conv_nth length_ineq_not_Nil
                  elim!: ccap_relationE)
   apply (clarsimp simp: if_1_0_0 to_bool_def unat_eq_of_nat
                         objBits_simps archObjSize_def pageBits_def from_bool_def case_bool_If
                  split: if_splits)
  apply (clarsimp simp: asid_low_bits_word_bits isCap_simps neq_Nil_conv
                        excaps_map_def excaps_in_mem_def
                        p2_gt_0[where 'a=32, folded word_bits_def])
  apply (frule cap_get_tag_isCap_unfolded_H_cap(13))
  apply (frule ctes_of_valid', clarsimp)
  apply (simp only: diminished_valid'[symmetric])
  apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (rule conjI)
   apply (clarsimp simp: cap_lift_asid_pool_cap cap_lift_page_directory_cap
                         cap_to_H_def to_bool_def valid_cap'_def
                         cap_page_directory_cap_lift_def
                         cap_asid_pool_cap_lift_def mask_def
                         asid_shiftr_low_bits_less[unfolded mask_def asid_bits_def] word_and_le1
                  elim!: ccap_relationE split: if_split_asm)
   apply (clarsimp split: list.split)
  apply (clarsimp simp: cap_lift_asid_pool_cap cap_lift_page_directory_cap
                        cap_to_H_def to_bool_def
                        cap_page_directory_cap_lift_def
                 elim!: ccap_relationE split: if_split_asm)
  done *)

lemma Arch_decodeInvocation_ccorres:
  notes if_cong[cong]
  assumes "interpret_excaps extraCaps' = excaps_map extraCaps"
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' (diminished' (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. excaps_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> \<lbrace>\<acute>call = from_bool isCall \<rbrace>) []
       (Arch.decodeInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call Arch_decodeInvocation_'proc)"
  (is "ccorres ?r ?xf ?P (?P' slot_') [] ?a ?c")
proof -
  from assms show ?thesis
    apply (cinit' lift: invLabel_'  length___unsigned_long_'  slot_'  excaps_'  cap_'
                        buffer_' call_')
     apply csymbr
     apply (simp only: cap_get_tag_isCap_ArchObject X64_H.decodeInvocation_def)
     apply (rule ccorres_Cond_rhs)
  sorry (* FIXME x64: needs IOPort Invocation lemma
      apply wpc
           apply (clarsimp simp: )+
      apply (rule ccorres_trim_returnE, simp+)
      apply (rule ccorres_call,
             rule decodeX64VCPUInvocation_ccorres, (simp add: isVCPUCap_def)+)[1]
     (* will not rewrite any other way, and we do not want to repeat proof for each MMU cap case
        of decodeX64MMUInvocation *)
     apply (subst not_VCPUCap_case_helper_eq, assumption)
     apply (rule ccorres_trim_returnE, simp+)
     apply (rule ccorres_call,
            rule decodeX64MMUInvocation_ccorres, simp+)[1]

    apply (clarsimp simp: cte_wp_at_ctes_of ct_in_state'_def)
    apply (frule(1) ctes_of_valid', simp only: diminished_valid'[symmetric])
    apply (clarsimp split: arch_capability.splits simp: isVCPUCap_def)
    done *)
qed

end

end
