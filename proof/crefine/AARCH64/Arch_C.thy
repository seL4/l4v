(*
 * Copyright 2024, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_C
imports Recycle_C
begin

unbundle l4v_word_context

context begin interpretation Arch . (*FIXME: arch-split*)

crunch unmapPageTable
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (wp: crunch_wps simp: crunch_simps)

end

context kernel_m begin

lemma storePTE_def':
  "storePTE slot pte = setObject slot pte"
  unfolding storePTE_def
  by (simp add: tailM_def headM_def)

lemma objBits_InvalidPTE:
  "objBits AARCH64_H.InvalidPTE = word_size_bits"
  by (simp add: objBits_simps bit_simps)

lemma objBits_InvalidPTE_pte_bits:
  "objBits AARCH64_H.InvalidPTE = pte_bits"
  by (simp add: objBits_InvalidPTE bit_simps)

lemma clearMemory_PT_setObject_PTE_ccorres:
  "ccorres dc xfdc
           (page_table_at' pt_t ptr and (\<lambda>s. 2 ^ ptBits pt_t \<le> gsMaxObjectSize s) and
            (\<lambda>_. is_aligned ptr (ptBits pt_t) \<and> ptr \<noteq> 0 \<and> pstart = addrFromPPtr ptr))
           (\<lbrace>\<acute>ptr___ptr_to_unsigned_long = Ptr ptr\<rbrace> \<inter> \<lbrace>\<acute>bits = of_nat (ptBits pt_t)\<rbrace>) []
       (do x \<leftarrow> mapM_x (\<lambda>p. setObject p InvalidPTE)
                       [ptr , ptr + 2 ^ objBits InvalidPTE .e. ptr + 2 ^ ptBits pt_t - 1];
           doMachineOp (cleanCacheRange_PoU ptr (ptr + 2 ^ ptBits pt_t - 1) pstart)
        od)
       (Call clearMemory_PT_'proc)"
  apply (rule ccorres_gen_asm)+
  apply (cinit' lift: ptr___ptr_to_unsigned_long_' bits_')
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (rule_tac P="page_table_at' pt_t ptr and (\<lambda>s. 2 ^ pt_bits pt_t \<le> gsMaxObjectSize s)"
                      in ccorres_from_vcg_nofail[where P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: unat_of_nat_pt_bits_mw)
      apply (subst ghost_assertion_size_logic[unfolded o_def])
        apply simp
       apply assumption
      apply (simp add: is_aligned_no_overflow')
      apply (intro conjI)
         apply (erule is_aligned_weaken, simp add: bit_simps)
        apply (clarsimp simp: is_aligned_def bit_simps split: if_splits)
       apply (erule (1) page_table_at_rf_sr_dom_s[simplified])
      apply (clarsimp simp: replicateHider_def[symmetric]
                      cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (simp add: objBits_simps upto_enum_step_def aligned_no_overflow_less
                       not_less[symmetric] upto_enum_word
                  split: if_split_asm cong: if_cong)
      apply (split if_split)
      apply (rule conjI; clarsimp)
      apply (fold mask_2pm1 shiftr_div_2n_w)
      apply (erule mapM_x_store_memset_ccorres_assist[OF _ _ _ _ _ _ subset_refl];
             simp add: shiftl_t2n hd_map objBits_simps)
        apply (clarsimp simp: less_Suc_eq_le nth_append split: if_split)
       apply (simp add: bit_simps mask_def split: if_split)
      apply (rule cmap_relationE1, erule rf_sr_cpte_relation, erule ko_at_projectKO_opt)
      apply (simp add: pte_bits_def word_size_bits_def)
      apply (subst coerce_memset_to_heap_update_pte)
      apply (clarsimp simp: rf_sr_def Let_def cstate_relation_def typ_heap_simps)
      apply (rule conjI)
       apply (simp add: cpspace_relation_def typ_heap_simps update_pte_map_tos
                        update_pte_map_to_ptes carray_map_relation_upd_triv)
       apply (rule cmap_relation_updI, simp_all)[1]
       apply (simp add: cpte_relation_def Let_def pte_lift_def
                        pte_get_tag_def pte_tag_defs)
       apply (simp add: carch_state_relation_def cmachine_state_relation_def
                        typ_heap_simps update_pte_map_tos)
      apply csymbr
     apply (rule ccorres_Guard)
     apply (ctac add: cleanCacheRange_PoU_ccorres)
    apply (wpsimp wp: mapM_x_wp' setObject_ksPSpace_only updateObject_default_inv)
   apply (clarsimp simp: guard_is_UNIV_def bit_simps split: if_split)
  apply clarsimp
  apply (frule is_aligned_addrFromPPtr_n, simp)
  apply (simp add: is_aligned_no_overflow' addrFromPPtr_mask_cacheLineBits)
  apply (rule conjI)
   apply (simp add: unat_mask_eq flip: mask_2pm1)
   apply (simp add: mask_eq_exp_minus_1)
  apply (simp add: bit_simps split: if_split)
  done

lemma performPageTableInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) \<circ> cteCap) ctSlot
              and (\<lambda>_. isPageTableCap cap \<and> capPTType cap = NormalPT_T))
       (\<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performPageTableInvocation (PageTableUnmap cap ctSlot)))
       (Call performPageTableInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (rule ccorres_gen_asm)
  apply (cinit lift: cap_' ctSlot_')
   apply (rename_tac cap')
   apply csymbr
   apply (simp del: Collect_const)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (subgoal_tac "capPTMappedAddress cap
                           = (\<lambda>cp. if to_bool (capPTIsMapped_CL cp)
                              then Some (capPTMappedASID_CL cp, capPTMappedAddress_CL cp)
                              else None) (cap_page_table_cap_lift cap')")
       apply (rule ccorres_Cond_rhs)
        apply (simp add: to_bool_def)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (ctac add: unmapPageTable_ccorres)
          apply (simp add: storePTE_def' swp_def)
          apply clarsimp
          apply (simp only: bit_simps_corres[symmetric])
          apply csymbr
          apply (ctac add: clearMemory_PT_setObject_PTE_ccorres[simplified objBits_InvalidPTE_pte_bits])
         apply wp
        apply (simp del: Collect_const)
        apply (vcg exspec=unmapPageTable_modifies)
       apply simp
       apply (rule ccorres_return_Skip')
      apply (simp add: cap_get_tag_isCap_ArchObject[symmetric] split: if_split)
      apply (clarsimp simp: cap_lift_page_table_cap cap_to_H_def cap_page_table_cap_lift_def
                     elim!: ccap_relationE cong: if_cong)
     apply (simp add: liftM_def getSlotCap_def updateCap_def del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule ccorres_getCTE)+
     apply (rename_tac cte cte')
     apply (rule_tac P="cte_wp_at' ((=) cte) ctSlot
                          and (\<lambda>_. cte = cte' \<and>
                                   isArchCap (\<lambda>acap. isPageTableCap acap \<and>
                                                     capPTType acap = NormalPT_T) (cteCap cte))"
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
       apply (clarsimp simp: isCap_simps)
       apply (drule cap_get_tag_isCap_unfolded_H_cap)
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (clarsimp simp: ccte_relation_def c_valid_cte_def
                      elim!: ccap_relationE)
       apply (subst cteCap_update_cte_to_H)
         apply (clarsimp simp: map_option_Some_eq2)
         apply (rule trans, rule sym, rule option.sel, rule sym, erule arg_cong)
        apply (erule iffD1[OF cap_page_table_cap_lift])
       apply (clarsimp simp: map_option_Some_eq2
                             cap_lift_page_table_cap cap_to_H_def
                             cap_page_table_cap_lift_def)
      apply simp
     apply (clarsimp simp: carch_state_relation_def cmachine_state_relation_def
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
                        wellformed_mapdata'_def
             simp flip: canonical_bit_def
                 elim!: ccap_relationE cong: if_cong)
  apply (drule spec[where x=0])
  apply auto
  done

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
    unfolding casid_pool_relation_def casid_map_relation_def
    apply (clarsimp simp: makeObject_asidpool split: asid_pool_C.splits)
    apply (clarsimp simp: array_relation_def option_to_ptr_def)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps asid_pool_C_tag_def asid_map_C_tag_def
                     size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine)
    apply (simp add: padup_def align_td_array')
    apply (subst (asm) size_td_array)
    apply (simp add: dom_def ran_def)
    apply (simp add: size_td_array ti_typ_pad_combine_def ti_typ_combine_def
                     Let_def empty_typ_info_def update_ti_adjust_ti
                del: replicate_numeral Kernel_C.pte_C_size)
    apply (simp add: typ_info_array array_tag_def
                del: replicate_numeral)
    supply replicate_numeral[simp del]
    apply (clarsimp dest!: ap_eq_D
                    simp: update_ti_t_array_tag_n_rep asid_low_bits_def word_le_nat_alt)

    apply (simp add: typ_info_simps asid_pool_C_tag_def
                     size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)

    apply (subst index_fold_update; auto simp: replicate_numeral update_ti_t_ptr_0s mask_def)
    (* casid_map relation *)
    apply (clarsimp simp: asid_map_lift_def asid_map_get_tag_def asid_map_C_tag_def)
    apply (simp add: final_pad_def padup_def align_td_array')
    apply (simp add: size_td_array ti_typ_pad_combine_def ti_typ_combine_def
                     empty_typ_info_def update_ti_adjust_ti)
    apply (simp add: typ_info_array array_tag_def)
    apply (subst update_ti_t_array_tag_n_rep[where v=0])
      apply (simp add: replicate_numeral)
     apply simp
    apply (clarsimp simp: update_ti_t_machine_word_0s replicate_numeral asid_map_tag_defs)
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
  have mko: "\<And>dev. makeObjectKO dev (Inl (KOArch (KOASIDPool f))) = Some ko"
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
   apply (simp add: pageBits_def)
  apply (erule valid_untyped_capE)
  apply (subst simpler_placeNewObject_def)
      apply ((simp add: word_bits_conv objBits_simps archObjSize_def
                        capAligned_def)+)[4]
  apply (simp add: simpler_modify_def rf_sr_htd_safe)
  apply (subgoal_tac "{frame ..+ 2 ^ pageBits} \<inter> kernel_data_refs = {}")
   prefer 2
   apply (drule(1) valid_global_refsD')
   apply (clarsimp simp: Int_commute pageBits_def
                         intvl_range_conv[where bits=pageBits, unfolded pageBits_def word_bits_def,
                                          simplified])
  apply (intro conjI impI)
       apply (erule is_aligned_no_wrap')
       apply (clarsimp simp: pageBits_def)
      apply (erule is_aligned_weaken, simp add:pageBits_def)
     apply (simp add: is_aligned_def bit_simps)
    apply (simp add: region_actually_is_bytes_dom_s pageBits_def)
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
  apply (simp add: pageBits_def ptr_retyps_gen_def
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

(* FIXME move *)
lemma ucast_x3_shiftr_asid_low_bits:
  "\<lbrakk> is_aligned base asid_low_bits ; base \<le> mask asid_bits \<rbrakk>
   \<Longrightarrow> UCAST(7 \<rightarrow> 64) (UCAST(16 \<rightarrow> 7) (UCAST(64 \<rightarrow> 16) base >> asid_low_bits)) = base >> asid_low_bits"
  apply (simp add: ucast_shiftr word_le_mask_eq asid_bits_def)
  apply (subst le_max_word_ucast_id)
   apply simp
   apply (drule_tac n=asid_low_bits in le_shiftr)
   apply (simp add: asid_low_bits_def asid_bits_def mask_def )+
  done

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
   apply (rule_tac P="is_aligned frame pageBits \<and> canonical_address frame" in ccorres_gen_asm)
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_split_nothrow[where c="Seq c c'" for c c'])
       apply (fold pageBits_def)[1]
       apply (simp add: hrs_htd_update)
       apply (rule deleteObjects_ccorres)
      apply ceqv
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_abstract_cleanup)
     apply (rule ccorres_symb_exec_l)
        apply (rule_tac P = "rv = (capability.UntypedCap isdev frame pageBits idx)" in ccorres_gen_asm)
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
          apply (ctac (c_lines 2) add: createObjects_asidpool_ccorres
                                         [where idx="max_free_index pageBits",
                                          unfolded pageBits_def, simplified]
                              pre del: ccorres_Guard_Seq)
            apply csymbr
            apply (ctac (no_vcg) add: cteInsert_ccorres)
             apply (simp add: ccorres_seq_skip del: fun_upd_apply)
             apply (rule ccorres_assert)
             apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: gets_def modify_def return_def put_def get_def bind_def
                             simp del: fun_upd_apply Collect_const)
             apply (prop_tac "base >> asid_low_bits < 0x80")
              apply (drule_tac n=asid_low_bits in le_shiftr)
              apply (fastforce simp: asid_low_bits_def asid_bits_def mask_def dest: plus_one_helper2)
             apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                   cmachine_state_relation_def
                             simp del: fun_upd_apply)
             apply (clarsimp simp: carch_state_relation_def carch_globals_def
                             simp del: fun_upd_apply)
             apply (simp add: asid_high_bits_of_def fun_upd_def[symmetric]
                         del: fun_upd_apply)
             apply (simp add: ucast_x3_shiftr_asid_low_bits)
             apply (erule array_relation_update, rule refl)
              apply (clarsimp simp: option_to_ptr_def option_to_0_def)
             apply (clarsimp simp: asid_high_bits_def mask_def)
            apply wp+
           apply (strengthen valid_pspace_mdb' vp_strgs' valid_pspace_valid_objs' valid_pspace_canonical')
           apply (clarsimp simp: is_simple_cap'_def isCap_simps conj_comms placeNewObject_def2)
           apply (wp createObjects_valid_pspace'[where ty="Inl (KOArch (KOASIDPool f))" and sz = pageBits for f]
                     createObjects_cte_wp_at'[where sz = pageBits]
                  | simp add:makeObjectKO_def objBits_simps archObjSize_def range_cover_full
                  | simp add: bit_simps untypedBits_defs)+
           apply (clarsimp simp:valid_cap'_def capAligned_def)
           apply (wp createObject_typ_at')
          apply clarsimp
          apply vcg
         apply (clarsimp simp:conj_comms objBits_simps simp flip: pageBits_def |
                strengthen valid_pspace_mdb' vp_strgs' invs_valid_pspace'
                valid_pspace_valid_objs' invs_valid_global'
                invs_urz)+
         apply (wp updateFreeIndex_forward_invs'
                   updateFreeIndex_caps_no_overlap''[where sz=pageBits]
                   updateFreeIndex_pspace_no_overlap'[where sz=pageBits]
                   updateFreeIndex_caps_overlap_reserved
                   updateFreeIndex_cte_wp_at)
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
       apply (simp add: is_aligned_def)
      apply (simp add: mask_def)
      apply (rule descendants_range_caps_no_overlapI'[where d=isdev and cref = parent])
        apply simp
       apply (fastforce simp: cte_wp_at_ctes_of)
      apply (clarsimp simp flip: add_mask_fold)
     apply (clarsimp dest!: upto_intvl_eq simp: mask_2pm1)
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
  apply (clarsimp simp: word_sle_def is_aligned_mask[symmetric]
                        ghost_assertion_data_get_gs_clear_region[unfolded o_def])
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
      apply (erule is_aligned_no_wrap', simp)
     apply (simp add:is_aligned_def)
    apply (simp add: hrs_htd_def)
   apply (drule region_actually_is_bytes_dom_s[OF _ order_refl])
   apply (simp add: hrs_htd_def split_def)
  apply (clarsimp simp: ccap_relation_def)
  apply (clarsimp simp: cap_asid_pool_cap_lift)
  apply (clarsimp simp: cap_to_H_def)
  apply (clarsimp simp: asid_bits_def)
  apply (drule word_le_mask_eq, simp)
  apply (simp add: canonical_address_mask_shift canonical_bit_def)
  done

lemmas performARMMMUInvocations
    = ccorres_invocationCatch_Inr performInvocation_def
      AARCH64_H.performInvocation_def performARMMMUInvocation_def
      liftE_bind_return_bindE_returnOk

(* FIXME AARCH64: consider using isVTableRoot *)
lemma slotcap_in_mem_PageTable:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); (s, s') \<in> rf_sr \<rbrakk>
       \<Longrightarrow> \<exists>v. cslift s' (cte_Ptr slot) = Some v
           \<and> (cap_get_tag (cte_C.cap_C v) = scast cap_page_table_cap)
              = (isArchObjectCap cap \<and> isPageTableCap (capCap cap) \<and> capPTType (capCap cap) = NormalPT_T)
           \<and> ccap_relation cap (cte_C.cap_C v)"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
  apply (clarsimp dest!: ccte_relation_ccap_relation)
  apply (simp add: cap_get_tag_isCap_ArchObject2)
  done

lemma ccap_relation_PageTableCap_IsMapped:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap p NormalPT_T m)) ccap \<rbrakk>
   \<Longrightarrow> (capPTIsMapped_CL (cap_page_table_cap_lift ccap) = 0) = (m = None)"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: cap_page_table_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  apply (simp add: to_bool_def)
  done

lemma ccap_relation_VSpaceCap_IsMapped:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap p VSRootPT_T m)) ccap \<rbrakk>
   \<Longrightarrow> (capVSIsMapped_CL (cap_vspace_cap_lift ccap) = 0) = (m = None)"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: cap_vspace_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  apply (simp add: to_bool_def)
  done

lemma ccap_relation_PageTableCap_BasePtr:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap p NormalPT_T m)) ccap \<rbrakk>
   \<Longrightarrow> capPTBasePtr_CL (cap_page_table_cap_lift ccap) = p"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: cap_page_table_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  done

lemma ccap_relation_PageTableCap_MappedASID:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap p NormalPT_T (Some (a,b))))
                   ccap \<rbrakk>
   \<Longrightarrow> capPTMappedASID_CL (cap_page_table_cap_lift ccap) = a"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: cap_page_table_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  done

lemma bind_bindE_liftE:
  "f >>= g >>=E h
   = doE a <- liftE f;
         g a >>=E h
     odE"
  by (simp add: liftE_def bindE_def lift_def bind_assoc)

lemma liftME_option_catch_bind:
  "(liftME Some m <catch> const (return None))
   = do x <- m;
        case x of Inl e \<Rightarrow> return None | Inr b \<Rightarrow> return (Some b)
     od"
  apply (clarsimp simp: const_def catch_def liftME_def bindE_def returnOk_def bind_def)
  apply (rule ext)
  apply (clarsimp simp: return_def)
  apply (case_tac "m s", clarsimp)
  apply (auto simp: split_def throwError_def return_def Nondet_Monad.lift_def
              split: prod.splits sum.splits)
  done

lemma maybeVSpaceForASID_findVSpaceForASID_ccorres:
  "ccorres
       (\<lambda>rv rv'. (case rv of None \<Rightarrow> (findVSpaceForASID_ret_C.status_C rv' \<noteq> scast EXCEPTION_NONE)
                           | Some pteptr \<Rightarrow> (findVSpaceForASID_ret_C.status_C rv' = scast EXCEPTION_NONE)
                                            \<and> pte_Ptr pteptr = (vspace_root_C rv')))
       ret__struct_findVSpaceForASID_ret_C_'
       (valid_arch_state' and (\<lambda>_. asid_wf asid))
       (\<lbrace>\<acute>asid___unsigned_long = asid\<rbrace>)
       hs
       (maybeVSpaceForASID asid)
       (Call findVSpaceForASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (clarsimp simp: maybeVSpaceForASID_def liftME_option_catch_bind)
  apply (rule ccorres_seq_skip'[THEN iffD1])
  apply (rule ccorres_guard_imp)
    apply (ctac (no_vcg) add: findVSpaceForASID_ccorres)
      apply (wpc; clarsimp)
       apply (rule ccorres_return_Skip')
      apply (rule ccorres_return_Skip')
     apply wpsimp
    apply simp_all
  apply (rule conjI; clarsimp)
  done

lemma cap_case_PageTableCap2:
  "(case cap of ArchObjectCap (PageTableCap p VSRootPT_T mapdata)
                   \<Rightarrow> f p mapdata | _ \<Rightarrow> g)
   = (if isArchObjectCap cap \<and> isPageTableCap (capCap cap) \<and> capPTType (capCap cap) = VSRootPT_T
      then f (capPTBasePtr (capCap cap)) (capPTMappedAddress (capCap cap))
      else g)"
  by (simp add: isCap_simps split: capability.split arch_capability.split pt_type.split)

lemma lookupPTSlotFromLevel_bitsLeft_less_64:
  "n \<le> maxPTLevel \<Longrightarrow> \<lbrace>\<lambda>_. True\<rbrace> lookupPTSlotFromLevel n p vptr \<lbrace>\<lambda>rv _. fst rv < 64\<rbrace>"
  apply (induct n arbitrary: p)
   apply (simp add: lookupPTSlotFromLevel.simps)
   apply (wpsimp simp: pageBits_def)
  apply (simp add: lookupPTSlotFromLevel.simps)
  apply wpsimp
      apply assumption
     apply (wpsimp wp: hoare_drop_imps)+
  apply (simp add: ptBitsLeft_def ptTranslationBits_def pageBits_def maxPTLevel_def
              split: if_splits)
  done

lemma lookupPTSlotFromLevel_bitsLeft_le_pptrBaseOffset_alignment:
  "n \<le> maxPTLevel \<Longrightarrow> \<lbrace>\<lambda>_. True\<rbrace> lookupPTSlotFromLevel n p vptr \<lbrace>\<lambda>rv _. fst rv \<le> pptrBaseOffset_alignment\<rbrace>"
  apply (induct n arbitrary: p)
   apply (simp add: lookupPTSlotFromLevel.simps)
   apply (wpsimp simp: pageBits_def pptrBaseOffset_alignment_def)
  apply (simp add: lookupPTSlotFromLevel.simps)
  apply wpsimp
      apply assumption
     apply (wpsimp wp: hoare_drop_imps)+
  apply (simp add: ptBitsLeft_def ptTranslationBits_def pageBits_def maxPTLevel_def
                   pptrBaseOffset_alignment_def
              split: if_splits)
  done

lemma lookupPTSlot_bitsLeft_less_64:
  "\<lbrace>\<top>\<rbrace> lookupPTSlot p vptr \<lbrace>\<lambda>rv _. fst rv < 64\<rbrace>"
  unfolding lookupPTSlot_def
  by (wpsimp wp: lookupPTSlotFromLevel_bitsLeft_less_64)

lemma lookupPTSlot_bitsLeft_le_pptrBaseOffset_alignment[wp]:
  "\<lbrace>\<top>\<rbrace> lookupPTSlot p vptr \<lbrace>\<lambda>rv _. fst rv \<le> pptrBaseOffset_alignment\<rbrace>"
  unfolding lookupPTSlot_def
  by (wpsimp wp: lookupPTSlotFromLevel_bitsLeft_le_pptrBaseOffset_alignment)

(* See comment in decode ARMPageTableInvocation for why "20" *)
definition
  "enoughPTBits n \<equiv> n \<noteq> pageBits \<longrightarrow> 20 \<le> n"

lemma lookupPTSlotFromLevel_enoughPTBits:
  "n \<le> maxPTLevel \<Longrightarrow> \<lbrace>\<lambda>_. True\<rbrace> lookupPTSlotFromLevel n p vptr \<lbrace>\<lambda>rv _. enoughPTBits (fst rv)\<rbrace>"
  unfolding enoughPTBits_def
  apply (induct n arbitrary: p)
   apply (simp add: lookupPTSlotFromLevel.simps)
   apply (wpsimp simp: pageBits_def)
  apply (simp add: lookupPTSlotFromLevel.simps)
  apply wpsimp
      apply assumption
     apply (wpsimp wp: hoare_drop_imps)+
  apply (simp add: ptBitsLeft_def ptTranslationBits_def pageBits_def maxPTLevel_def
              split: if_splits)
  done

lemma lookupPTSlot_enoughPTBits[wp]:
  "\<lbrace>\<top>\<rbrace> lookupPTSlot p vptr \<lbrace>\<lambda>rv _. enoughPTBits (fst rv)\<rbrace>"
  unfolding lookupPTSlot_def
  by (wpsimp wp: lookupPTSlotFromLevel_enoughPTBits)

lemma slotcap_in_mem_VSpace:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); (s, s') \<in> rf_sr \<rbrakk>
       \<Longrightarrow> \<exists>v. cslift s' (cte_Ptr slot) = Some v
           \<and> (cap_get_tag (cte_C.cap_C v) = scast cap_vspace_cap)
              = (isArchObjectCap cap \<and> isPageTableCap (capCap cap) \<and> capPTType (capCap cap) = VSRootPT_T)
           \<and> ccap_relation cap (cte_C.cap_C v)"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
  apply (clarsimp dest!: ccte_relation_ccap_relation)
  apply (simp add: cap_get_tag_isCap_ArchObject2)
  done

lemma Restart_valid[simp]:
  "valid_tcb_state' Restart s"
  by (simp add: valid_tcb_state'_def)

lemma canonical_address_mask_shift2:
  "\<lbrakk> canonical_address p; n + m = Suc canonical_bit; 0 < n \<rbrakk> \<Longrightarrow> p && (mask n << m) = p >> m << m"
  apply (prop_tac "m = Suc canonical_bit - n", arith)
  supply canonical_bit_def[simp]
  apply (simp add: canonical_address_def canonical_address_of_def)
  apply word_eqI
  apply (rule iffI; clarsimp)
  apply (rename_tac n')
  apply (prop_tac "n' < Suc canonical_bit"; fastforce)
  done

lemma capVSMappedASID_CL_masked[unfolded asid_bits_def, simplified]:
  "ccap_relation (ArchObjectCap (PageTableCap p VSRootPT_T (Some (asid, vref)))) cap
   \<Longrightarrow> capVSMappedASID_CL (cap_vspace_cap_lift cap) && mask asid_bits =
       capVSMappedASID_CL (cap_vspace_cap_lift cap)"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  apply (clarsimp simp: cap_vspace_cap_lift_def)
  apply (clarsimp simp: cap_lift_def Let_def asid_bits_def split: if_splits)
  done

lemma pptrUserTop_le_canonical_val[unfolded canonical_bit_def, simplified]:
  "x \<le> pptrUserTop \<Longrightarrow> x \<le> mask (Suc canonical_bit)"
  by (simp add: pptrUserTop_def canonical_bit_def order_trans[OF _ mask_mono] split: if_split_asm)

lemma decodeARMPageTableInvocation_ccorres:
  "\<lbrakk>interpret_excaps extraCaps' = excaps_map extraCaps;
    isPageTableCap cp; capPTType cp = NormalPT_T\<rbrakk> \<Longrightarrow>
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
       (decodeARMMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeARMPageTableInvocation_'proc)"
  supply Collect_const[simp del] if_cong[cong] option.case_cong[cong]
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_'
                simp: decodeARMMMUInvocation_def invocation_eq_use_types
                      decodeARMPageTableInvocation_def)
   apply (simp add: Let_def isCap_simps if_to_top_of_bind
               cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq)
    (* ARMPageTableUnmap *)
    apply (rule ccorres_split_throws)
     apply (simp add: liftE_bindE bind_assoc)
     apply (rule ccorres_symb_exec_l[OF _ getCTE_inv _ empty_fail_getCTE])
      apply (rule ccorres_rhs_assoc)+
      (* check cap is final *)
      apply (ctac add: isFinalCapability_ccorres)
        apply (simp add: unlessE_def if_to_top_of_bind if_to_top_of_bindE ccorres_seq_cond_raise)
        apply (rule ccorres_cond2'[where R=\<top>])
          apply (clarsimp simp: from_bool_0)
         apply (simp add: throwError_bind invocationCatch_def)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (simp add: returnOk_bind bindE_assoc performARMMMUInvocations)
        apply (ctac add: setThreadState_ccorres)
          apply (ctac add: performPageTableInvocationUnmap_ccorres)
             apply (rule ccorres_alternative2)
             apply (rule ccorres_return_CE, simp+)[1]
            apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
           apply wpsimp
          apply (vcg exspec=performPageTableInvocationUnmap_modifies)
         apply (wpsimp wp: sts_invs_minor' simp: isCap_simps)
        apply clarsimp
        apply (vcg exspec=setThreadState_modifies)
       apply clarsimp
       apply (wp (once) hoare_drop_imp, wp isFinalCapability_inv)
      apply simp
      apply (vcg exspec=isFinalCapability_modifies)
     apply (wp getCTE_wp)
    apply (vcg exspec=performPageTableInvocationUnmap_modifies exspec=isFinalCapability_modifies
               exspec=findVSpaceForASID_modifies exspec=setThreadState_modifies)

   (* we're done with unmap case *)
   apply simp
   apply (rule ccorres_Cond_rhs_Seq)
    (* neither map nor unmap, throw *)
    apply (rule ccorres_equals_throwError)
     apply (simp split: invocation_label.split arch_invocation_label.split
                   add: throwError_bind invocationCatch_def)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)

   (* ARMPageTableMap *)
   apply clarsimp
   apply csymbr
   apply clarsimp
   (* ensure we have enough extraCaps *)
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
   (* we have enough extraCaps *)
   apply (simp add: list_case_If2 split_def
                    word_less_nat_alt length_ineq_not_Nil Let_def
                    whenE_bindE_throwError_to_if if_to_top_of_bind
                    decodeARMPageTableInvocationMap_def)
   (* ensure the page table cap is mapped *)
   apply csymbr
   apply (simp add: ccap_relation_PageTableCap_IsMapped)
   apply (rule ccorres_Cond_rhs_Seq; clarsimp)
    (* not mapped *)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   (* mapped *)
   apply (simp add: checkVSpaceRoot_def cap_case_PageTableCap2 split_def)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_vspace_cap)
                                        = (isArchObjectCap rv \<and> isPageTableCap (capCap rv) \<and>
                                           capPTType (capCap rv) = VSRootPT_T))
                                      \<and> (ccap_relation rv rv')) (fst (extraCaps ! 0))"
              and xf'=vspaceRootCap_' in ccorres_split_nothrow)
         apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
         apply (drule(1) slotcap_in_mem_VSpace)
         apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
         apply (clarsimp simp: typ_heap_simps' mask_def)
        apply (rename_tac rv' t t')
        apply (simp add: word_sless_def word_sle_def)
        apply ceqv
       apply csymbr
       apply clarsimp
       apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
       apply (clarsimp simp: hd_conv_nth)
       (* is first extra cap a vspace cap? *)
       apply (rule ccorres_if_lhs[rotated]; clarsimp)
        (* if not vspace cap, clear up the C if condition calculation, then throw *)
        apply (rule ccorres_cond_true_seq)
        apply ccorres_rewrite
        apply (rule ccorres_equals_throwError)
         apply (simp split: invocation_label.split arch_invocation_label.split
                       add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       (* first extracap is a vspace cap *)
       apply (clarsimp simp: isCap_simps isValidVTableRoot_def isVTableRoot_def)
       (* ensure the vspace is mapped *)
       apply (clarsimp simp: option.case_eq_if if_to_top_of_bind if_to_top_of_bindE)
       apply (rename_tac m)
       apply (prop_tac "m = capPTMappedAddress (capCap (fst (extraCaps ! 0)))", simp)
       apply hypsubst
       apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
          apply vcg
         apply (solves \<open>clarsimp simp: from_bool_def split: bool.split\<close>)
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
          apply vcg
         apply (solves \<open>clarsimp simp: hd_conv_nth not_less length_le_helper mask_def pptrUserTop_val\<close>)
        apply (fold not_None_def)[1] (* avoid expanding capPTMappedAddress  *)
        apply clarsimp
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (simp add: lookupError_injection invocationCatch_use_injection_handler
                        injection_bindE[OF refl refl] injection_handler_If bindE_assoc
                        injection_handler_throwError injection_liftE[OF refl])
       apply (ctac add: ccorres_injection_handler_csum1[OF ccorres_injection_handler_csum1,
                                                        OF findVSpaceForASID_ccorres])
          (* ensure level 1 pt pointer supplied by user is actually a vspace root *)
          apply (simp add: Collect_False if_to_top_of_bindE)
          apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
             apply vcg
            apply (solves\<open>clarsimp simp: asidInvalid_def isCap_simps ccap_relation_vspace_base\<close>)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply (clarsimp simp: bindE_assoc)
          apply (ctac pre: ccorres_liftE_Seq add: lookupPTSlot_ccorres)
            apply (simp add: liftE_bindE)
            apply (rule ccorres_pre_getObject_pte)
            apply (rename_tac pte)
            apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
            apply clarsimp
            apply (rename_tac pte_slot ptSlot___struct_lookupPTSlot_ret_C pte)
            apply wpfix
            (* 20 in enoughPTBits is from the bitfield generator: capPTMappedAddress is a field_high
               of width 28, which leaves 20 bottom bits at 48 canonical width -- the only reason
               this works is because ptBitsLeft must be \<ge> 20 when it returns more than pageBits and
               we later mask by ptBitsLeft. *)
            apply (rule_tac P="enoughPTBits (unat (ptBitsLeft_C ptSlot___struct_lookupPTSlot_ret_C))"
                            in ccorres_gen_asm)
            (* ensure we have found a valid pte with more bits than pageBits left to look up *)
            apply (rule ccorres_rhs_assoc2)
            apply (rule_tac val="from_bool (unat (ptBitsLeft_C ptSlot___struct_lookupPTSlot_ret_C)
                                            = pageBits
                                            \<or> \<not> pte = AARCH64_H.InvalidPTE)"
                     and xf'=ret__int_' and R="ko_at' pte pte_slot" and R'=UNIV
                     in ccorres_symb_exec_r_known_rv)
               apply vcg
               apply clarsimp
               apply (simp add: from_bool_eq_if' pageBits_def)
               apply (erule cmap_relationE1[OF rf_sr_cpte_relation], erule ko_at_projectKO_opt)
               apply (clarsimp simp: typ_heap_simps from_bool_eq_if)
               apply (simp flip: word_unat.Rep_inject)
               apply (auto simp: cpte_relation_def Let_def pte_lift_def case_bool_If pte_tag_defs
                          split: pte.split_asm if_splits)[1]
              apply ceqv
             apply clarsimp
             apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                apply vcg
               apply (solves clarsimp)
              apply (rule syscall_error_throwError_ccorres_n)
              apply (simp add: syscall_error_to_H_cases)
             (* checks are done, move on to doing the mapping *)
             apply (clarsimp simp: injection_handler_returnOk injection_handler_assertE bindE_assoc)
             apply (simp add: assertE_liftE liftE_bindE)
             apply (rule ccorres_assert)
             apply (simp add: performARMMMUInvocations bindE_assoc)
             apply csymbr
             apply csymbr
             apply csymbr
             apply csymbr
             apply csymbr
             apply (rule_tac P="unat (ptBitsLeft_C ptSlot___struct_lookupPTSlot_ret_C) < 64"
                             in ccorres_gen_asm) (* bitsLeft should not exceed word bits *)
             apply ccorres_rewrite
             apply csymbr
             apply (ctac add: setThreadState_ccorres)
               apply (rule_tac A="cte_at' slot" and A'=UNIV in ccorres_guard_imp2)
                apply (ctac add: performPageTableInvocationMap_ccorres)
                   apply (rule ccorres_alternative2)
                   apply (rule ccorres_return_CE, simp+)[1]
                  apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                 apply wpsimp+
                apply (vcg exspec=performPageTableInvocationMap_modifies)
               apply clarsimp
               apply (rule conjI)
                apply (simp (no_asm) add: ccap_relation_def)
                apply (clarsimp simp: cap_get_tag_to_H map_option_Some_eq2 cap_page_table_cap_lift)
                apply (clarsimp simp: cap_to_H_def ccap_relation_PageTableCap_BasePtr
                                      ccap_relation_vspace_mapped_asid)
                apply (subst ccap_relation_vspace_mapped_asid)
                 apply assumption
                apply (simp add: capVSMappedASID_CL_masked)
                apply (simp flip: mask_2pm1)
                apply (drule at_least_2_args)
                apply (clarsimp simp: hd_conv_nth)
                apply (solves \<open>simp add: mask_shift_neg_mask_eq not_less pptrUserTop_le_canonical_val
                                         enoughPTBits_def
                                    flip: word_le_nat_alt\<close>)
               apply (clarsimp simp: cpte_relation_def pte_lift_def Let_def pte_pte_table_lift_def
                                     pte_tag_defs ccap_relation_PageTableCap_BasePtr
                               split: if_splits)
               apply (drule addrFromPPtr_canonical_in_kernel_window, simp add: word_less_nat_alt)
               apply (solves \<open>simp add: canonical_address_mask_shift2 pageBits_def canonical_bit_def\<close>)
              apply wpsimp+
             apply (vcg exspec=setThreadState_modifies)
            apply (simp add: get_capPtr_CL_def cap_get_tag_isCap_unfolded_H_cap typ_heap_simps)
            apply vcg
           apply clarsimp
           apply (wpsimp wp: lookupPTSlot_inv hoare_vcg_all_lift hoare_drop_imps lookupPTSlot_bitsLeft_less_64)
          apply (simp add: typ_heap_simps)
          (* guard against False by schematic instantiation because of simp above *)
          apply (rule conseqPre, vcg exspec=lookupPTSlot_modifies, rule order_refl)
         (* throw on failed lookup *)
         apply clarsimp
         apply ccorres_rewrite
         apply (rule_tac P'="{s. errstate s = find_ret}" in ccorres_from_vcg_throws[where P=\<top>])
         apply clarsimp
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                               syscall_error_to_H_cases exception_defs)
         apply (erule lookup_failure_rel_fault_lift[rotated])
         apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                syscall_error_to_H_cases exception_defs)
        apply clarsimp
        apply (wp injection_wp[OF refl] findVSpaceForASID_inv hoare_imp_eq_substR)
       apply clarsimp
       apply (vcg exspec=findVSpaceForASID_modifies)
      apply clarsimp
      apply wp
     apply clarsimp
     apply vcg
    apply wpsimp
   apply clarsimp
   apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: cte_wp_at_ctes_of excaps_map_def
                        word_sle_def word_sless_def bit_simps not_None_def)
  apply (rule conjI)
  subgoal
    (* ARMPageTableUnmap: Haskell preconditions *)
    by (fastforce simp: ct_in_state'_def cte_wp_at_ctes_of isCap_simps rf_sr_ksCurThread
                  elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')

  apply (rule conjI)
  subgoal for \<dots> s _ _
    (* ARMPageTableMap: Haskell preconditions *)
    apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt
                          linorder_not_less)
    apply (clarsimp | drule length_le_helper)+
    apply (prop_tac "s \<turnstile>' fst (extraCaps ! 0)")
     apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def
                           slotcap_in_mem_def dest!: ctes_of_valid')
    by (auto simp: ct_in_state'_def pred_tcb_at' mask_def valid_tcb_state'_def
                   valid_cap'_def wellformed_acap'_def wellformed_mapdata'_def
             elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]

  apply (rule conjI)
  subgoal for _ v1
    (* ARMPageTableUnmap: C preconditions *)
    by (clarsimp simp: rf_sr_ksCurThread)

  subgoal for p
    (* ARMPageTableMap: C preconditions *)
    apply (clarsimp simp: neq_Nil_conv[where xs=extraCaps]
                    dest!: sym[where s="ArchObjectCap cp" for cp])
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject isCap_simps
                          word_sle_def word_sless_def word_less_nat_alt)
    apply (frule length_ineq_not_Nil)
    apply (clarsimp simp: rf_sr_ksCurThread hd_conv_nth isValidVTableRoot_def2)
    apply (rule conjI)
     apply (clarsimp simp: ccap_relation_vspace_mapped_asid[symmetric])
    apply (clarsimp simp: from_bool_0)
    done
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

lemma framesize_from_H_eqs:
  "(framesize_from_H vsz = scast Kernel_C.ARMSmallPage) = (vsz = ARMSmallPage)"
  "(framesize_from_H vsz = scast Kernel_C.ARMLargePage) = (vsz = ARMLargePage)"
  "(framesize_from_H vsz = scast Kernel_C.ARMHugePage) = (vsz = ARMHugePage)"
  by (simp add: framesize_from_H_def vm_page_size_defs split: vmpage_size.split)+

lemma ptr_add_uint_of_nat [simp]:
  "a  +\<^sub>p uint (of_nat b :: machine_word) = a  +\<^sub>p (int b)"
  by (clarsimp simp: CTypesDefs.ptr_add_def)

declare int_unat[simp]

lemma obj_at_pte_aligned:
  "obj_at' (\<lambda>a::AARCH64_H.pte. True) ptr s ==> is_aligned ptr word_size_bits"
  apply (drule obj_at_ko_at')
  apply (clarsimp dest!:ko_at_is_aligned'
                  simp: objBits_simps bit_simps
                  elim!: is_aligned_weaken)
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

lemma pte_lift_pte_invalid_eq:
  "(pte_get_tag pte = scast pte_pte_invalid) = (pte_lift pte = Some Pte_pte_invalid)"
  by (auto simp: pte_lift_def pte_tag_defs Let_def split: if_splits)

lemma cpte_relation_InvalidPTE[simp]:
  "cpte_relation InvalidPTE pte = (pte_lift pte  = Some Pte_pte_invalid)"
  by (clarsimp simp: cpte_relation_def)

lemma cpte_relation_pte_invalid_eq:
  "cpte_relation pte pte' \<Longrightarrow> (pte_lift pte' = Some Pte_pte_invalid) = (pte = InvalidPTE)"
  by (clarsimp simp: cpte_relation_def Let_def split: if_splits pte.splits)

lemma performPageInvocationMap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
           and (\<lambda>_. (isFrameCap acap \<and>
                     case_option False wellformed_mapdata' (capFMappedAddress acap))))
       ({s. asid___unsigned_long_' s = fst (the (capFMappedAddress acap))} \<inter>
        {s. cpte_relation (fst mapping) (pte_' s)} \<inter>
        {s. ccap_relation (ArchObjectCap acap) (cap_' s)} \<inter>
        {s. ctSlot_' s = cte_Ptr slot} \<inter>
        {s. ptSlot_' s = pte_Ptr (snd mapping)}) []
       (liftE (performPageInvocation (PageMap acap slot mapping)))
       (Call performPageInvocationMap_'proc)"
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (clarsimp split: option.splits)
  apply (cinit lift:  pte_' cap_' ctSlot_' ptSlot_')
   apply wpc (* split mapping *)
   apply (rename_tac m_pte m_slot)
   apply (rule ccorres_pre_getObject_pte)
   apply (rename_tac oldPTE)
   apply (rule_tac xf'=tlbflush_required_' and
                   val="from_bool (oldPTE \<noteq> InvalidPTE)" and
                   R="\<top>" and
                   R'="{s. \<exists>old_pte. cslift s (pte_Ptr m_slot) = Some old_pte \<and>
                                     cpte_relation oldPTE old_pte}" in
                   ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg, clarsimp)
      apply (clarsimp simp: typ_heap_simps from_bool_0 pte_lift_pte_invalid_eq
                            cpte_relation_pte_invalid_eq)
     apply ceqv
    apply (rule ccorres_move_c_guard_cte)
    apply ctac (* updateCap *)
      apply (rule ccorres_split_nothrow)
          apply clarsimp
          apply (rule storePTE_Basic_ccorres, simp)
         apply ceqv
        apply csymbr
        apply (ctac add: cleanByVA_PoU_ccorres)
          apply (clarsimp simp: when_def if_to_top_of_bind simp del: Collect_const)
          apply (rule ccorres_cond_seq)
          apply (rule ccorres_cond[where R=\<top>], clarsimp)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply (ctac (no_vcg) add: invalidateTLBByASIDVA_ccorres)
            apply (rule ccorres_rel_imp, rule ccorres_return_C[where xf=ret__unsigned_long_']; simp)
           apply wp
          apply ccorres_rewrite
          apply (clarsimp cong: ccorres_prog_only_cong)
          apply (rule ccorres_rel_imp, rule ccorres_return_C[where xf=ret__unsigned_long_']; simp)
         apply wpsimp
        apply (wpsimp wp: hoare_drop_imp)
        apply (vcg exspec=cleanByVA_PoU_modifies)
       apply (wp hoare_drop_imp)
      apply vcg
     apply wpsimp
    apply vcg
   apply clarsimp
   apply vcg
  apply (fastforce simp: wellformed_mapdata'_def typ_heap_simps isCap_simps cap_get_tag_isCap
                         ccap_relation_FrameCap_MappedAddress)
  done

lemma performPageGetAddress_ccorres:
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and (\<lambda>s. ksCurThread s = thread) and ct_in_state' ((=) Restart))
      (\<lbrace>\<acute>base_ptr = ptr\<rbrace> \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>) []
      (do reply \<leftarrow> performPageInvocation (PageGetAddr ptr);
          liftE (replyOnRestart thread reply isCall) od)
      (Call performPageGetAddress_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: base_ptr_' call_' simp: performPageInvocation_def)
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
         apply (clarsimp simp: msgInfoRegister_def AARCH64.msgInfoRegister_def
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
   apply (auto simp: AARCH64.badgeRegister_def AARCH64_H.badgeRegister_def Kernel_C.badgeRegister_def
                     fromPAddr_def ThreadState_defs Kernel_C.X0_def Kernel_C.X1_def
                     pred_tcb_at'_def obj_at'_def ct_in_state'_def)
  done

lemma vmsz_aligned_addrFromPPtr':
  "vmsz_aligned (addrFromPPtr p) sz
       = vmsz_aligned p sz"
  apply (simp add: vmsz_aligned_def AARCH64.addrFromPPtr_def pptrBaseOffset_def paddrBase_def)
  apply (subgoal_tac "is_aligned AARCH64.pptrBase (pageBitsForSize sz)")
   apply (rule iffI)
    apply (drule(1) aligned_add_aligned)
      apply (simp add: pageBitsForSize_def word_bits_def split: vmpage_size.split)
     apply simp
   apply (erule(1) aligned_sub_aligned)
    apply (simp add: pageBitsForSize_def word_bits_def bit_simps split: vmpage_size.split)
  apply (simp add: pageBitsForSize_def AARCH64.pptrBase_def is_aligned_def bit_simps
                   canonical_bit_def
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
  by (cases vsz; simp add: bit_simps)

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

lemma pde_case_isPageTablePDE:
  "(case pte of PageTablePTE _ \<Rightarrow> P | _ \<Rightarrow> Q)
       = (if isPageTablePTE pte then P else Q)"
  by (clarsimp simp: isPageTablePTE_def split: pte.splits)

lemma framesize_to_from_H:
  "sz < 3 \<Longrightarrow> framesize_from_H (framesize_to_H sz) = sz"
   apply (clarsimp simp: framesize_to_H_def framesize_from_H_def framesize_defs
           split: if_split vmpage_size.splits)
  by (word_bitwise, auto)

lemma ccap_relation_FrameCap_generics:
  "ccap_relation (ArchObjectCap (FrameCap word vmrights vmpage_size d map_data)) cap'
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
      \<and> capFVMRights_CL (cap_frame_cap_lift cap') < 4"
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
  apply (rule canonical_address_and_maskI)
  apply fastforce
  done

lemma of_nat_pageBitsForSize_eq:
  "(x = of_nat (pageBitsForSize sz)) = (unat x = pageBitsForSize sz)" for x::machine_word
  by (auto simp: of_nat_pageBitsForSize)

lemma ccap_relation_FrameCap_IsMapped:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.FrameCap p r sz d m)) ccap \<rbrakk>
   \<Longrightarrow> (capFMappedASID_CL (cap_frame_cap_lift ccap) = 0) = (m = None)"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: cap_frame_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  done

lemma cte_wp_at'_frame_at':
  "\<lbrakk> cte_wp_at'
       ((=) (capability.ArchObjectCap (arch_capability.FrameCap p v1 sz d m)) \<circ> cteCap) slot s;
     valid_objs' s \<rbrakk>
   \<Longrightarrow> frame_at' p sz d s"
  apply (drule (1) cte_wp_at_valid_objs_valid_cap')
  apply clarsimp
  apply (drule_tac t="cteCap _" in sym)
  apply (clarsimp simp: valid_cap'_def)
  done

lemma canonical_address_frame_at':
  "\<lbrakk>frame_at' p sz d s; pspace_canonical' s\<rbrakk> \<Longrightarrow> canonical_address p"
  apply (clarsimp simp: frame_at'_def)
  apply (drule_tac x=0 in spec, clarsimp simp: bit_simps typ_at_to_obj_at_arches)
  apply (cases sz
         ; auto simp: bit_simps split: if_splits
                dest!: device_data_at_ko user_data_at_ko intro!: obj_at'_is_canonical)
  done

definition flushtype_relation :: "flush_type \<Rightarrow> machine_word \<Rightarrow> bool" where
  "flushtype_relation typ label \<equiv> case typ of
     Clean \<Rightarrow>
       label \<in> scast ` {Kernel_C.ARMPageClean_Data, Kernel_C.ARMVSpaceClean_Data}
   | Invalidate \<Rightarrow>
       label \<in> scast ` {Kernel_C.ARMPageInvalidate_Data, Kernel_C.ARMVSpaceInvalidate_Data}
   | CleanInvalidate \<Rightarrow>
       label \<in> scast ` {Kernel_C.ARMPageCleanInvalidate_Data, Kernel_C.ARMVSpaceCleanInvalidate_Data}
   | Unify \<Rightarrow>
       label \<in> scast ` {Kernel_C.ARMPageUnify_Instruction, Kernel_C.ARMVSpaceUnify_Instruction}"

lemma doFlush_ccorres:
  "ccorres dc xfdc (\<lambda>s. vs \<le> ve \<and> ps \<le> ps + (ve - vs) \<and> vs && mask cacheLineBits = ps && mask cacheLineBits
        \<and> ptrFromPAddr ps \<le> ptrFromPAddr ps + (ve - vs)
        \<and> unat (ve - vs) \<le> gsMaxObjectSize s)
     (\<lbrace>flushtype_relation t \<acute>invLabel\<rbrace> \<inter> \<lbrace>\<acute>start = vs\<rbrace> \<inter> \<lbrace>\<acute>end = ve\<rbrace> \<inter> \<lbrace>\<acute>pstart = ps\<rbrace>) []
     (doMachineOp (doFlush t vs ve ps)) (Call doFlush_'proc)"
  apply (cases t; clarsimp simp: doFlush_def doMachineOp_bind)
     apply (cinit' lift: pstart_')
      apply (rule ccorres_cond_true)
      apply (ctac (no_vcg) add: cleanCacheRange_RAM_ccorres)
     apply (clarsimp simp: flushtype_relation_def)
    apply (cinit' lift: pstart_')
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_true)
     apply (ctac (no_vcg) add: invalidateCacheRange_RAM_ccorres)
    apply (fastforce simp: flushtype_relation_def
                           sel4_arch_invocation_label_defs arch_invocation_label_defs)
   apply (cinit' lift: pstart_')
    apply (rule ccorres_cond_false)
    apply (rule ccorres_cond_false)
    apply (rule ccorres_cond_true)
    apply (ctac (no_vcg) add: cleanInvalidateCacheRange_RAM_ccorres)
   apply (fastforce simp: flushtype_relation_def
                          sel4_arch_invocation_label_defs arch_invocation_label_defs)
  apply (simp add: doMachineOp_bind empty_fail_bind bind_assoc)
  apply (cinit' lift: pstart_')
   apply (rule ccorres_cond_false)
   apply (rule ccorres_cond_false)
   apply (rule ccorres_cond_false)
   apply (rule ccorres_cond_true)
   apply (rule ccorres_rhs_assoc)+
   apply (ctac (no_vcg) add: cleanCacheRange_PoU_ccorres)
    apply (ctac (no_vcg) add: dsb_ccorres)
     apply (ctac (no_vcg) add: invalidateCacheRange_I_ccorres)
      apply (ctac (no_vcg) add: isb_ccorres)
     apply wp+
   apply (fastforce simp: flushtype_relation_def
                          sel4_arch_invocation_label_defs arch_invocation_label_defs)
  done

(* The precondition is slightly different here to ARM/ARM_HYP, because we're flushing on kernel
   virtual addresses instead of user virtual addresses (hence also no VM root switching). *)
lemma performPageFlush_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (\<lambda>s. pstart \<le> pstart + (end - start) \<and>
            ptrFromPAddr pstart \<le> ptrFromPAddr pstart + (end - start) \<and>
            unat (end - start) \<le> gsMaxObjectSize s)
       (\<lbrace>\<acute>start = start\<rbrace> \<inter> \<lbrace>\<acute>end =  end\<rbrace> \<inter> \<lbrace>\<acute>pstart = pstart\<rbrace> \<inter>
        \<lbrace>flushtype_relation typ \<acute>invLabel \<rbrace>)
       []
       (liftE (performPageInvocation (PageFlush typ start end pstart pt asid)))
       (Call performPageFlush_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: start_' end_' pstart_' invLabel_')
   apply (unfold when_def)
   apply csymbr (* config_set(CONFIG_ARM_HYPERVISOR_SUPPORT) *)
   apply ccorres_rewrite
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply csymbr
      apply csymbr
      apply (rule ccorres_cond2[where R=\<top>])
        apply (simp split: if_split)
       apply (ctac (no_vcg) add: doFlush_ccorres)
      apply (rule ccorres_return_Skip)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wpsimp
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: order_less_imp_le)
  done

lemma ivc_label_flush_case:
  "label = ArchInvocationLabel ARMPageUnify_Instruction \<or>
   label = ArchInvocationLabel ARMPageCleanInvalidate_Data \<or>
   label = ArchInvocationLabel ARMPageInvalidate_Data \<or>
   label = ArchInvocationLabel ARMPageClean_Data
    \<Longrightarrow> (case label of
     ArchInvocationLabel ARMPageMap \<Rightarrow> A
  |  ArchInvocationLabel ARMPageUnmap \<Rightarrow> B
  |  ArchInvocationLabel ARMPageUnify_Instruction \<Rightarrow> C
  |  ArchInvocationLabel ARMPageCleanInvalidate_Data \<Rightarrow> C
  |  ArchInvocationLabel ARMPageInvalidate_Data \<Rightarrow> C
  |  ArchInvocationLabel ARMPageClean_Data \<Rightarrow> C
  |  ArchInvocationLabel ARMPageGetAddress \<Rightarrow> D
  |  _  \<Rightarrow> E)
  = C"
  by (auto split: invocation_label.split arch_invocation_label.split)

lemma isPageFlushLabel_disj:
  "(label = ArchInvocationLabel ARMPageUnify_Instruction \<or>
    label = ArchInvocationLabel ARMPageCleanInvalidate_Data \<or>
    label = ArchInvocationLabel ARMPageInvalidate_Data \<or>
    label = ArchInvocationLabel ARMPageClean_Data) =
  isPageFlushLabel label"
  by (auto simp: isPageFlushLabel_def split: invocation_label.split arch_invocation_label.split)

lemma flushtype_relation_triv:
  "isPageFlushLabel (invocation_type label) \<or> isVSpaceFlushLabel (invocation_type label)
   \<Longrightarrow> flushtype_relation (labelToFlushType label) label"
  by (clarsimp simp: labelToFlushType_def flushtype_relation_def invocation_eq_use_types
                     isPageFlushLabel_def isVSpaceFlushLabel_def
               split: flush_type.splits invocation_label.splits arch_invocation_label.splits)

lemma vmAttributesFromWord_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. True\<rbrace> Call vmAttributesFromWord_'proc
  \<lbrace> vm_attributes_lift \<acute>ret__struct_vm_attributes_C =
      \<lparr> armExecuteNever_CL =  (\<^bsup>s\<^esup>w >> 2) && 1,
        armParityEnabled_CL = (\<^bsup>s\<^esup>w >> 1) && 1,
        armPageCacheable_CL = \<^bsup>s\<^esup>w && 1 \<rparr>  \<rbrace>"
  by (vcg, simp add: vm_attributes_lift_def word_sless_def word_sle_def mask_def)

lemma maskVMRights_spec: (* FIXME AARCH64: replace the one in CSpace_C -- preconditions mess up csymbr *)
  "\<forall>s. \<Gamma> \<turnstile> {s}
  Call maskVMRights_'proc
  \<lbrace> \<^bsup>s\<^esup>vm_rights && mask 2 = \<^bsup>s\<^esup>vm_rights
    \<longrightarrow> vmrights_to_H \<acute>ret__unsigned_long =
        maskVMRights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) (cap_rights_to_H (seL4_CapRights_lift \<^bsup>s\<^esup>cap_rights_mask)) \<and>
       \<acute>ret__unsigned_long && mask 2 = \<acute>ret__unsigned_long \<and>
       \<acute>ret__unsigned_long \<noteq> 2 \<rbrace>"
  apply (rule HoarePartial.ProcNoRec1)
   apply (simp add: maskVMRights_impl)
   apply (unfold maskVMRights_body_def)
   apply vcg
   apply (clarsimp simp: vmrights_defs vmrights_to_H_def maskVMRights_def mask_def
                         cap_rights_to_H_def to_bool_def
                   split: bool.split)
  apply (simp add: maskVMRights_impl dom_def)
  done

lemma checkVSpaceRoot_def2:
  "checkVSpaceRoot cap n =
   (if isValidVTableRoot cap
    then returnOk (capPTBasePtr (capCap cap), fst (the (capPTMappedAddress (capCap cap))))
    else throwError (InvalidCapability n))"
  unfolding checkVSpaceRoot_def isValidVTableRoot_def2
  by (clarsimp split: capability.splits arch_capability.splits pt_type.splits option.splits)

lemma frame_at'_is_aligned_addrFromPPtr:
  "\<lbrakk> frame_at' p sz dev s; pspace_aligned' s \<rbrakk> \<Longrightarrow> is_aligned (addrFromPPtr p) pageBits"
  apply (clarsimp simp: frame_at'_def)
  apply (erule_tac x=0 in allE)
  apply (erule impE)
   apply (clarsimp simp: bit_simps pageBitsForSize_def split: vmpage_size.splits)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def objBits_simps koTypeOf_eq_UserDataT
                  split: if_splits)
  apply (simp split: kernel_object.splits)
  done

lemma cap_frame_cap_lift_asid_upd_idem:
  "cap_get_tag cap = scast cap_frame_cap \<Longrightarrow>
   cap_frame_cap_lift cap\<lparr>capFMappedASID_CL := capFMappedASID_CL (cap_frame_cap_lift cap) && mask 16\<rparr> =
   cap_frame_cap_lift cap"
  by (clarsimp simp: cap_frame_cap_lift_def cap_lift_def Let_def cap_tag_defs)

lemma cpte_relation_makeUserPTE:
  "\<lbrakk> vm_attributes_lift v =
       \<lparr>armExecuteNever_CL = (attrs >> 2) && 1, armParityEnabled_CL = (attrs >> Suc 0) && 1,
        armPageCacheable_CL = attrs && 1\<rparr>;
     let uxn = uxn_from_vmattributes (vm_attributes_to_H v);
         ap = ap_from_vm_rights rights;
         attridx = attridx_from_vmattributes (vm_attributes_to_H v)
     in if framesize_from_H sz = scast Kernel_C.ARMSmallPage
        then pte_lift cpte =
               Some (Pte_pte_4k_page \<lparr>pte_pte_4k_page_CL.UXN_CL = uxn, page_base_address_CL = p,
                                      nG_CL = 0, AF_CL = 1, SH_CL = 0, AP_CL = ap,
                                      AttrIndx_CL = attridx\<rparr>)
        else pte_lift cpte =
               Some (Pte_pte_page \<lparr>pte_pte_page_CL.UXN_CL = uxn, page_base_address_CL = p,
                                   nG_CL = 0, AF_CL = 1, SH_CL = 0, AP_CL = ap,
                                   AttrIndx_CL = attridx\<rparr>)\<rbrakk>
   \<Longrightarrow> cpte_relation (makeUserPTE p rights (attribsFromWord attrs) sz) cpte"
  apply (clarsimp simp: cpte_relation_def Let_def makeUserPTE_def vm_attributes_to_H_def
                        uxn_from_vmattributes_def framesize_from_H_eqs
                  split: if_splits)
   apply (clarsimp simp: pte_lift_def Let_def attribsFromWord_def
                   simp flip: of_bool_nth to_bool_and_1)+
  done

lemma ccap_relation_decodePageMap[unfolded asid_bits_def canonical_bit_def, simplified]:
  "\<lbrakk> ccap_relation (ArchObjectCap (FrameCap p R sz dev m)) cap;
     cap_get_tag cap = scast cap_frame_cap;
     0 < asid; asid_wf asid; canonical_address vref;
     cap_frame_cap_lift ccap =
       cap_frame_cap_lift cap\<lparr>capFMappedASID_CL := asid && mask asid_bits,
                              capFMappedAddress_CL := vref && mask (Suc canonical_bit)\<rparr>;
     cap_get_tag ccap = scast cap_frame_cap  \<rbrakk>
   \<Longrightarrow> ccap_relation (ArchObjectCap (FrameCap p R sz dev (Some (asid, vref)))) ccap"
  apply (simp (no_asm) add: ccap_relation_def map_option_Some_eq2 c_valid_cap_def)
  apply (simp (no_asm_simp) add: cap_frame_cap_lift[THEN iffD1])
  apply (simp add: cap_to_H_def ccap_relation_FrameCap_generics asid_wf_def asid_bits_def
                   and_mask_eq_iff_le_mask[symmetric] cl_valid_cap_def canonical_bit_def
                   canonical_address_and_maskD)
  apply (rule conjI, clarsimp)
  apply (clarsimp simp: ccap_relation_def c_valid_cap_def cap_frame_cap_lift[THEN iffD1]
                        cl_valid_cap_def)
  done

lemmas canonical_address_C_pptrUserTop =
  canonical_address_pptrUserTop_mask[unfolded pptrUserTop_val word_le_nat_alt, simplified]

lemma capFMappedAddress_CL_canonical:
  "\<lbrakk> capFMappedAddress_CL (cap_frame_cap_lift cap) = p; cap_get_tag cap = scast cap_frame_cap \<rbrakk> \<Longrightarrow>
   canonical_address p"
  by (drule sym, simp add: canonical_address_cap_frame_cap)

lemma decodeARMFrameInvocation_ccorres:
  notes if_cong[cong] Collect_const[simp del]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps; isFrameCap cp \<rbrakk>
   \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       ({s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (decodeARMMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeARMFrameInvocation_'proc)"
  (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ccorres _ _ ?P _ _ _ _")
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_' call_'
                simp: decodeARMMMUInvocation_def)
   apply (simp add: Let_def isCap_simps invocation_eq_use_types split_def decodeARMFrameInvocation_def
              cong: StateSpace.state.fold_congs globals.fold_congs
                    if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong)
   apply (rule ccorres_Cond_rhs[rotated])+
       apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
       apply clarsimp
       apply (rule ccorres_equals_throwError)
        apply (fastforce simp: throwError_bind invocationCatch_def
                        split: invocation_label.split arch_invocation_label.split)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)

      \<comment> \<open>PageGetAddress\<close>
      apply (rule ccorres_guard_imp2[where A="?P" and A'=UNIV])
       apply (simp add: returnOk_bind bindE_assoc performARMMMUInvocations)
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
      apply (fastforce simp: ct_in_state'_def valid_tcb_state'_def rf_sr_ksCurThread
                             ccap_relation_FrameCap_BasePtr ccap_relation_frame_tags
                      elim!: pred_tcb'_weakenE
                      dest!: st_tcb_at_idle_thread')

     \<comment> \<open>Flush\<close>
     apply (rule ccorres_guard_imp2[where A="?P" and A'=UNIV])
      apply (rule ccorres_rhs_assoc)+
      apply csymbr+
      apply (simp add: ivc_label_flush_case decodeARMFrameInvocationFlush_def
                       list_case_If2 if3_fold2
                 cong: StateSpace.state.fold_congs globals.fold_congs
                       if_cong invocation_label.case_cong arch_invocation_label.case_cong
                       list.case_cong)
      apply (simp add: split_def case_option_If2 if_to_top_of_bind
                  cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong)
      apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
         apply vcg
        apply (clarsimp simp:list_length_less )
        apply (drule unat_less_iff[where c=2])
         apply (simp add:word_bits_def)
        apply simp
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply csymbr
      apply (rule ccorres_if_cond_throws2[rotated -1,where Q = \<top> and Q' = \<top>])
         apply vcg
        apply clarsimp
        apply (frule ccap_relation_mapped_asid_0)
        apply fastforce
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply csymbr
      apply csymbr
      apply csymbr
      apply csymbr
      apply (simp add: invocationCatch_use_injection_handler
                       injection_bindE[OF refl refl] bindE_assoc
                       injection_handler_returnOk injection_handler_whenE
                       lookupError_injection)
      apply (ctac add: ccorres_injection_handler_csum1
                            [OF ccorres_injection_handler_csum1, OF findVSpaceForASID_ccorres])
         apply (rule ccorres_if_cond_throws[where P = False and Q = \<top> and Q'=\<top>, simplified])
           apply simp
          apply (rule ccorres_add_return)
          apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
            apply (rule ccorres_add_return)
            apply (ctac add: getSyscallArg_ccorres_foo
                               [where args = args and n = 1 and buffer = buffer])
              apply (simp only:if_to_top_of_bindE whenE_def)
              apply (rule ccorres_if_cond_throws[rotated -1, where Q = \<top> and Q' = \<top>])
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
              apply (rule ccorres_if_cond_throws[rotated -1,where Q = \<top> and Q' = \<top>])
                 apply vcg
                apply (clarsimp simp:hd_drop_conv_nth hd_conv_nth)
                apply (clarsimp dest!: ccap_relation_FrameCap_generics)
               apply (simp add:injection_handler_throwError)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply csymbr
              apply csymbr
              apply csymbr
              apply (rule ccorres_if_cond_throws[rotated -1,where Q = \<top> and Q' = \<top>])
                 apply vcg
                apply (clarsimp simp: hd_drop_conv_nth hd_conv_nth paddrBase_def paddrTop_def
                                      pptrBaseOffset_def pptrTop_def pptrBase_def fromPAddr_def)
                apply (clarsimp dest!: ccap_relation_FrameCap_generics)
               apply (simp add:injection_handler_throwError)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply (simp add: performARMMMUInvocations bindE_assoc)
              apply simp
              apply (ctac add: setThreadState_ccorres)
                apply (ctac(no_vcg) add: performPageFlush_ccorres)
                  apply (rule ccorres_gen_asm)
                  apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                  apply (rule ccorres_alternative2)
                  apply (rule ccorres_return_CE, simp+)[1]
                 apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                apply (wpsimp simp: performPageInvocation_def)
               apply simp
               apply (strengthen unat_sub_le_strg[where v="2 ^ pageBitsForSize (capFSize cp)"])
               apply (simp add: linorder_not_less linorder_not_le order_less_imp_le)
               apply (wp sts_invs_minor')
              apply simp
              apply (vcg exspec=setThreadState_modifies)
             apply wp
            apply simp
            apply vcg
           apply wp
          apply vcg
         apply vcg
        apply clarsimp
        apply (rule_tac P'="{s. find_ret = errstate s}" in ccorres_from_vcg_split_throws[where P=\<top>])
         apply vcg
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                              syscall_error_to_H_cases exception_defs)
        apply (erule lookup_failure_rel_fault_lift[rotated])
        apply (simp add: exception_defs)
       apply (wp injection_wp[OF refl])
      apply simp
      apply (vcg exspec=findVSpaceForASID_modifies)
     apply (clarsimp simp: ct_in_state'_def valid_tcb_state'_def rf_sr_ksCurThread isCap_simps
                           ccap_relation_FrameCap_BasePtr ccap_relation_frame_tags
                           sysargs_rel_to_n ccap_relation_FrameCap_MappedASID)
     apply (frule cte_wp_at_eq_gsMaxObjectSize, fastforce)
     apply (frule cte_wp_cteCap_valid, fastforce)
     apply (clarsimp simp: valid_cap'_def capAligned_def wellformed_mapdata'_def
                     cong: option.case_cong)
     apply (rule conjI; clarsimp)
       (* Haskell side *)
       apply (fastforce simp: not_less not_le paddrBase_def ptrFromPAddr_add_left
                              is_aligned_no_overflow3
                              is_aligned_no_overflow3[OF vmsz_aligned_addrFromPPtr(3)[THEN iffD2]])
     (* C side *)
     apply (prop_tac "2 \<le> length args", clarsimp simp: not_less word_le_nat_alt)
     apply (drule at_least_2_args[simplified not_less])
     apply (solves \<open>clarsimp simp: ccap_relation_capFMappedASID_CL_0 ccap_relation_FrameCap_MappedASID
                                   pageBitsForSize_le_64 ccap_relation_FrameCap_MappedAddress
                                   isPageFlushLabel_disj  ccap_relation_FrameCap_Size
                                   framesize_from_H_bounded flushtype_relation_triv
                             split: option.splits\<close>)

    \<comment> \<open>PageUnmap\<close>
    apply (rule ccorres_guard_imp2[where A="?P" and A'=UNIV])
     apply (simp add: returnOk_bind bindE_assoc performARMMMUInvocations)
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
    apply clarsimp (* needed *)
    apply (fastforce simp: ct_in_state'_def valid_tcb_state'_def rf_sr_ksCurThread isCap_simps
                           cte_wp_at_ctes_of
                     elim!: pred_tcb'_weakenE)

  \<comment> \<open>PageMap\<close>
  apply (rule ccorres_guard_imp2[where A="?P" and A'=UNIV])
   apply (rename_tac word rights pg_sz maptype mapdata call' buffer' cap excaps cte
                     length___unsigned_long invLabel)
   apply clarsimp
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
   apply (prop_tac "args \<noteq> []", fastforce dest: at_least_3_args)
   apply csymbr
   apply (simp add: interpret_excaps_test_null excaps_map_def)
   (* throw if no excaps *)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind invocationCatch_def split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (clarsimp simp: list_case_If2 decodeARMFrameInvocationMap_def)
   apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
        apply csymbr
        apply (rule ccorres_add_return)
        apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_vspace_cap) = isVTableRoot rv)
                                         \<and> (ccap_relation rv rv')) (fst (extraCaps ! 0))"
                 and xf'=vspaceRootCap_' in ccorres_split_nothrow)
            apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
            apply (drule(1) slotcap_in_mem_VSpace)
            apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
            apply (clarsimp simp: typ_heap_simps' mask_def isVTableRoot_ex isCap_simps)
            apply (thin_tac _)+
            apply fastforce
           apply (rename_tac rv' t t')
           apply (simp add: word_sless_def word_sle_def)
           apply ceqv
          apply (clarsimp simp add: split_def cap_case_PageTableCap2 hd_conv_nth option.case_eq_if)
          apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
          apply csymbr
          apply csymbr
          apply csymbr
          apply (rule ccorres_add_return)
          apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
           apply (clarsimp simp: assertE_liftE liftE_bindE bind_assoc cong: if_weak_cong)
           apply (rule ccorres_assert2)
           (* checkVSpaceRoot and isValidNativeRoot_'proc *)
           apply csymbr
           apply csymbr
           apply csymbr
           apply (erule allE, erule (1) impE)
           apply (simp add: checkVSpaceRoot_def2 if_to_top_of_bind if_to_top_of_bindE from_bool_0)
           apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top> and PT'=UNIV])
               apply (vcg, clarsimp)
              apply (solves simp)
             apply (simp add: throwError_bind invocationCatch_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply csymbr
            apply csymbr
            apply csymbr
            apply csymbr
            (* findVSpaceForASID *)
            apply (simp add: invocationCatch_use_injection_handler
                             injection_bindE[OF refl refl] bindE_assoc
                             injection_handler_returnOk injection_handler_throwError
                             injection_handler_If if_to_top_of_bindE
                             lookupError_injection injection_liftE
                        cong: if_cong)
            apply (ctac add: ccorres_injection_handler_csum1
                                  [OF ccorres_injection_handler_csum1, OF findVSpaceForASID_ccorres])
               apply (rule ccorres_if_cond_throws[rotated -1, where P=False and Q=\<top> and Q'=\<top> and
                                                                    R'=UNIV and PT'=UNIV, simplified])
                 apply (vcg, clarsimp)
                apply (solves simp)
               (* base ptr equality *)
               apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                  apply vcg
                 apply (clarsimp simp: ccap_relation_vspace_base isValidVTableRoot_def2)
                apply (simp add: throwError_bind invocationCatch_def)
                apply (rule syscall_error_throwError_ccorres_n)
                apply (simp add: syscall_error_to_H_cases)
               (* check vaddr alignment *)
               apply csymbr
               apply (clarsimp simp: checkVPAlignment_def unlessE_def injection_handler_If
                                     injection_handler_returnOk injection_handler_throwError
                                     if_to_top_of_bind if_to_top_of_bindE
                               cong: if_cong)
               apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
                  apply vcg
                 apply (solves \<open>clarsimp simp: vmsz_aligned_def from_bool_0 is_aligned_mask
                                              ccap_relation_FrameCap_Size framesize_from_to_H\<close>)
                apply (rule syscall_error_throwError_ccorres_n)
                apply (simp add: syscall_error_to_H_cases)
               (* mapdata = None / capFMappedASID = asidInvalid*)
               apply csymbr
               apply csymbr
               apply (simp only: if_swap[where P="x = None" for x])
               apply (rule ccorres_cond_seq)
               apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                 apply (solves \<open>clarsimp simp: ccap_relation_FrameCap_IsMapped asidInvalid_def\<close>)
                apply (fold not_None_def)[1]
                apply (rule ccorres_cond_seq)
                (* asids not equal? *)
                apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                  apply (solves \<open>clarsimp simp: isValidVTableRoot_def2 not_None_def
                                                ccap_relation_vspace_mapped_asid[symmetric]
                                                ccap_relation_FrameCap_MappedASID\<close>)
                 apply ccorres_rewrite
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (simp add: syscall_error_to_H_cases)
                apply (rule ccorres_rhs_assoc)+
                apply csymbr
                apply (rule ccorres_cond_seq)
                (* base addresses not equal? *)
                apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                  apply (solves \<open>clarsimp simp: ccap_relation_FrameCap_MappedAddress not_None_def\<close>)
                 apply ccorres_rewrite
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (simp add: syscall_error_to_H_cases)
                apply (clarsimp simp: liftE_bindE)
                apply csymbr
                apply csymbr
                apply csymbr
                apply csymbr
                apply (ctac add: lookupPTSlot_ccorres)
                  apply (rename_tac lookupPTSlot_ret)
                  apply csymbr
                  apply (rule ccorres_cond_seq)
                  apply (simp only: if_swap[where P="x = pageBitsForSize y" for x y])
                  apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                    apply (clarsimp simp: ccap_relation_FrameCap_Size framesize_from_to_H)
                    apply (rule unat_eq_of_nat)
                    apply (rule less_trans, rule pageBitsForSize_64, simp)
                   apply clarsimp
                   apply ccorres_rewrite
                   apply wpfix
                   apply (rule_tac P="\<lambda>s. unat (ptBitsLeft_C lookupPTSlot_ret) < 64" and
                                   P'=UNIV in ccorres_from_vcg_throws)
                   apply (clarsimp simp: throwError_def return_def)
                   apply (rule conseqPre, vcg, clarsimp)
                   apply (clarsimp simp: exception_defs syscall_error_rel_def
                                         syscall_error_to_H_cases and_mask_eq_iff_le_mask
                                         lookup_fault_missing_capability_lift_def
                                         lookup_fault_lift_def lookup_fault_tag_defs)
                   apply (solves \<open>clarsimp simp: mask_def word_le_nat_alt\<close>)
                  apply (clarsimp simp: performARMMMUInvocations)
                  apply (ctac add: setThreadState_ccorres)
                    apply csymbr
                    apply (ctac (no_vcg) add: performPageInvocationMap_ccorres)
                      apply (rule ccorres_gen_asm)
                      apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                      apply (rule ccorres_alternative2)
                      apply (rule ccorres_return_CE, simp+)[1]
                     apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                    apply (wpsimp simp: performPageInvocation_def)
                   apply (wp sts_invs_minor')
                  apply clarsimp
                  apply (vcg exspec=setThreadState_modifies)
                 apply (wpsimp wp: hoare_drop_imp lookupPTSlot_bitsLeft_less_64 lookupPTSlot_inv)
                apply (clarsimp simp: ccap_relation_frame_tags ccap_relation_FrameCap_Size
                                      ccap_relation_FrameCap_BasePtr)
                apply (vcg exspec=lookupPTSlot_modifies)
               (* mapdata \<noteq> None --> remap case *)
               apply (rule ccorres_rhs_assoc)
               apply csymbr
               apply clarsimp (* simplifies Guard to True*)
               apply ccorres_rewrite (* removes Guard \<lbrace>True\<rbrace> *)
               apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                  apply vcg
                 apply (solves \<open>clarsimp simp: pptrUserTop_val ccap_relation_FrameCap_Size
                                               framesize_from_to_H word_less_nat_alt field_simps\<close>)
                apply (rule syscall_error_throwError_ccorres_n)
                apply (simp add: syscall_error_to_H_cases)
               apply (clarsimp simp: liftE_bindE)
               apply csymbr
               apply csymbr
               apply csymbr
               apply csymbr
               apply (ctac add: lookupPTSlot_ccorres)
                 apply (rename_tac lookupPTSlot_ret)
                 apply csymbr
                 apply (rule ccorres_cond_seq)
                 apply (simp only: if_swap[where P="x = pageBitsForSize y" for x y])
                 apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                   apply (clarsimp simp: ccap_relation_FrameCap_Size framesize_from_to_H)
                   apply (rule unat_eq_of_nat)
                   apply (rule less_trans, rule pageBitsForSize_64, simp)
                  apply clarsimp
                  apply ccorres_rewrite
                  apply wpfix
                  apply (rule_tac P="\<lambda>s. unat (ptBitsLeft_C lookupPTSlot_ret) < 64" and
                                  P'=UNIV in ccorres_from_vcg_throws)
                  apply (clarsimp simp: throwError_def return_def)
                  apply (rule conseqPre, vcg, clarsimp)
                  apply (clarsimp simp: exception_defs syscall_error_rel_def
                                        syscall_error_to_H_cases and_mask_eq_iff_le_mask
                                        lookup_fault_missing_capability_lift_def
                                        lookup_fault_lift_def lookup_fault_tag_defs)
                  apply (solves \<open>clarsimp simp: mask_def word_le_nat_alt\<close>)
                 apply (clarsimp simp: performARMMMUInvocations)
                 apply (ctac add: setThreadState_ccorres)
                   apply csymbr
                   apply (ctac (no_vcg) add: performPageInvocationMap_ccorres)
                     apply (rule ccorres_gen_asm)
                     apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                     apply (rule ccorres_alternative2)
                     apply (rule ccorres_return_CE, simp+)[1]
                    apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                   apply (wpsimp simp: performPageInvocation_def)
                  apply (wp sts_invs_minor')
                 apply clarsimp
                 apply (vcg exspec=setThreadState_modifies)
                apply (wpsimp wp: hoare_drop_imp lookupPTSlot_bitsLeft_less_64 lookupPTSlot_inv)
               apply clarsimp
               apply (vcg exspec=lookupPTSlot_modifies)
              apply ccorres_rewrite
              apply clarsimp
              apply (rename_tac fault)
              apply (rule_tac P'="{s. errstate s = find_ret}" in ccorres_from_vcg_throws[where P=\<top>])
              apply (clarsimp simp: throwError_def return_def)
              apply (rule conseqPre, vcg, clarsimp)
              apply (clarsimp simp: exception_defs syscall_error_rel_def syscall_error_to_H_cases)
              apply (case_tac fault; clarsimp)
             apply clarsimp
             apply (wpsimp wp: injection_handler_wp)
             apply (wp (once) hoare_drop_imps) (* drop rv = capPTBasePtr (capCap (fst (extraCaps ! 0))) *)
             apply (wpsimp wp: hoare_vcg_const_imp_lift)
            apply (clarsimp simp: ccap_relation_frame_tags ccap_relation_FrameCap_Size
                                  ccap_relation_FrameCap_BasePtr)
            apply (vcg exspec=findVSpaceForASID_modifies)
           apply wp
          apply (vcg exspec=getSyscallArg_modifies)
         apply wp
        apply vcg
       apply clarsimp (* removes vaddr from post condition *)
       apply wp
      apply (vcg exspec=getSyscallArg_modifies)
     apply wp
    apply (vcg exspec=getSyscallArg_modifies)
   apply (clarsimp simp: rf_sr_ksCurThread)
   apply (frule cte_wp_at_eq_gsMaxObjectSize, fastforce)
   apply (clarsimp simp: cte_wp_at_ctes_of is_aligned_mask[symmetric] vmsz_aligned_def
                         vmsz_aligned_addrFromPPtr isCap_simps sysargs_rel_to_n not_less)
   apply (frule ctes_of_valid', fastforce)
   apply (drule sym[where t="cteCap cap" for cap])
   apply (clarsimp simp: valid_cap'_def capAligned_def isValidVTableRoot_def2)
   apply (rule conjI)
    (* Haskell side of PageMap *)
    apply (clarsimp dest!: at_least_3_args[simplified not_less])
    apply (prop_tac "s \<turnstile>' fst (extraCaps ! 0)")
     apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def
                           slotcap_in_mem_def dest!: ctes_of_valid')
    apply (clarsimp simp: valid_cap'_def capAligned_def wellformed_mapdata'_def)
    apply (prop_tac "7 \<le> gsMaxObjectSize s")
     subgoal for _ _ v2
       by (cases v2; clarsimp simp: bit_simps')
    subgoal
      by (auto simp: ct_in_state'_def pred_tcb_at' valid_tcb_state'_def mask_2pm1[symmetric]
                     valid_cap'_def wellformed_acap'_def wellformed_mapdata'_def
                     mask_pptrUserTop_user_region
               elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')
   (* length___unsigned_long <-> length args *)
   apply (rule conjI, solves \<open>clarsimp simp: word_less_nat_alt\<close>)
   (* C side of PageMap *)
   apply (frule ccap_relation_frame_tags)
   apply (clarsimp dest!: at_least_3_args[simplified not_less])
   apply (prop_tac "s \<turnstile>' fst (extraCaps ! 0)")
    apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def
                          slotcap_in_mem_def dest!: ctes_of_valid')
   apply (solves
          \<open>clarsimp simp: ccap_relation_vspace_mapped_asid[symmetric] valid_cap'_def capAligned_def
                          wellformed_mapdata'_def  ccap_relation_FrameCap_generics
                          addrFromPPtr_canonical_in_kernel_window frame_at'_is_aligned_addrFromPPtr
                          is_aligned_addrFromPPtr invs_pspace_aligned'
                          isVTableRoot_def ccap_relation_FrameCap_Size framesize_from_H_bounded
                          framesize_from_to_H and_mask_eq_iff_le_mask le_mask_iff_lt_2n[THEN iffD1]
                          cpte_relation_makeUserPTE ccap_relation_decodePageMap
                          canonical_address_C_pptrUserTop capFMappedAddress_CL_canonical\<close>)
   (* PageMap done *)

  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

(* adapted from X64 *)
lemma asidHighBits_handy_convs:
  "sint Kernel_C.asidHighBits = 7"
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
  apply (simp add: AARCH64_H.maskCapRights_def isFrameCap_def Let_def split: arch_capability.splits)
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
    apply (simp add: framesize_defs)+
  done

lemma performVSpaceFlush_ccorres:
  "ccorres (\<lambda>_ rv'. rv' = scast EXCEPTION_NONE) ret__unsigned_long_'
       (\<lambda>s. pstart \<le> pstart + (end - start) \<and>
            ptrFromPAddr pstart \<le> ptrFromPAddr pstart + (end - start) \<and>
            unat (end - start) \<le> gsMaxObjectSize s)
       (\<lbrace>\<acute>start = start\<rbrace> \<inter> \<lbrace>\<acute>end =  end\<rbrace> \<inter> \<lbrace>\<acute>pstart = pstart\<rbrace> \<inter>
        \<lbrace>flushtype_relation typ \<acute>invLabel \<rbrace>)
       []
       (performVSpaceInvocation (VSpaceFlush typ start end pstart vs asid))
       (Call performVSpaceFlush_'proc)"
  apply (cinit lift: start_' end_' pstart_' invLabel_')
   apply csymbr (* config_set(CONFIG_ARM_HYPERVISOR_SUPPORT) *)
   apply ccorres_rewrite
   apply (unfold when_def)
   apply (rule ccorres_rhs_assoc)+
   apply csymbr
   apply csymbr
   apply csymbr
   apply csymbr
   apply (rule ccorres_add_return2)
   apply (rule ccorres_split_nothrow_novcg)
       apply (rule ccorres_cond2[where R=\<top>])
         apply (simp split: if_split)
        apply (rule ccorres_call[where xf'=xfdc])
           apply (rule doFlush_ccorres)
          apply simp
         apply simp
        apply simp
       apply (rule ccorres_return_Skip)
      apply ceqv
     apply (rule ccorres_return_C[where xf=ret__unsigned_long_']; simp)
    apply wp
   apply (clarsimp simp: guard_is_UNIV_def)
  apply clarsimp
  done

lemma isVSpaceFlushLabel_disj:
  "(label = ArchInvocationLabel ARMVSpaceUnify_Instruction \<or>
    label = ArchInvocationLabel ARMVSpaceCleanInvalidate_Data \<or>
    label = ArchInvocationLabel ARMVSpaceInvalidate_Data \<or>
    label = ArchInvocationLabel ARMVSpaceClean_Data) =
  isVSpaceFlushLabel label"
  by (auto simp: isVSpaceFlushLabel_def split: invocation_label.split arch_invocation_label.split)

lemma flush_range_le:
  fixes start :: "'a::len word"
  assumes "pageBase start n = pageBase end n"
  assumes "start \<le> end"
  assumes "w && mask n = start && mask n"
  assumes "n < LENGTH('a)"
  shows "w \<le> w + (end - start)" "unat (end - start) \<le> 2 ^ n"
proof -
  have q: "w && mask n \<le> (w && mask n) + (end - start)"
    using assms
    apply (subst AND_NOT_mask_plus_AND_mask_eq[where w = start,symmetric,where n=n])
    apply (simp add: page_base_def)
    apply (drule word_le_minus_mono_left[where x= "start && ~~ mask n"])
     apply (rule word_and_le2)
    apply simp
    done

  have a: "unat (w && mask n) + unat (end - start) = unat ((w && mask n) + (end - start))"
    apply (rule unat_plus_simple[THEN iffD1,symmetric])
    apply (rule q)
    done

  have b: "end + (start && mask n) - start = end - (start && ~~ mask n)"
    by (simp add:mask_out_sub_mask)
  have c: "unat (w && mask n) + unat (end - start) < 2 ^ n"
    using assms a
    apply (simp add:field_simps)
    apply (rule unat_less_helper)
    apply simp
    apply (rule_tac P =" \<lambda>x. x < y" for y in ssubst[OF b])
    apply (subst AND_NOT_mask_plus_AND_mask_eq[where w = "end",symmetric,where n=n])
    apply (simp add: pageBase_def)
    apply (rule and_mask_less')
    apply simp
    done

  show "w \<le> w + (end - start)"
    using assms
    by - (rule word_plus_mono_right_split, rule c, simp)

  show "unat (end - start) \<le> 2 ^ n"
    using q c
    by (simp add: olen_add_eqv)
qed

lemmas flush_range_le1 = flush_range_le(2)[OF _ _ refl]

lemma ptrFromPAddr_and_mask_eq:
  "n \<le> pptrBaseOffset_alignment \<Longrightarrow> ptrFromPAddr p && mask n = p && mask n"
  apply (simp add: ptrFromPAddr_def pptrBaseOffset_def paddrBase_def pptrBaseOffset_alignment_def
                   pptrBase_def)
  apply word_bitwise
  apply clarsimp
  done

lemma decodeARMVSpaceRootInvocation_ccorres:
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps;
     isPageTableCap cp; capPTType cp = VSRootPT_T \<rbrakk> \<Longrightarrow>
   ccorres
       (intr_and_se_rel \<currency> dc)
       (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and valid_cap' (ArchObjectCap cp)
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       ({s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       hs
       (decodeARMMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeARMVSpaceRootInvocation_'proc)"
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_' current_extra_caps_' cap_' buffer_')
   apply (simp add: Let_def isCap_simps invocation_eq_use_types decodeARMMMUInvocation_def
                    decodeARMVSpaceInvocation_def
               del: Collect_const
              cong: StateSpace.state.fold_congs globals.fold_congs
                    if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong)
   apply (rule ccorres_Cond_rhs[rotated])
    apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
    apply (clarsimp simp: isVSpaceFlushLabel_disj)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_rhs_assoc)+
   apply (simp add: isVSpaceFlushLabel_disj decodeARMFrameInvocationFlush_def
                    list_case_If2 if3_fold2
              cong: StateSpace.state.fold_congs globals.fold_congs
                    if_cong invocation_label.case_cong arch_invocation_label.case_cong
                    list.case_cong
              del: Collect_const)
   apply (simp add: case_option_If2 if_to_top_of_bind del: Collect_const
               cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong)
   apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
      apply vcg
     apply (clarsimp simp: word_less_nat_alt list_length_less)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo
                        [where args = args and n = 1 and buffer = buffer])
       apply (simp only:if_to_top_of_bindE whenE_def)
       apply (simp add: case_option_If2 if_to_top_of_bind del: Collect_const
                   cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong)
       apply (rule ccorres_if_cond_throws[rotated -1, where Q = \<top> and Q' = \<top>])
          apply vcg
         apply (clarsimp simp:hd_drop_conv_nth hd_conv_nth)
        apply (rule ccorres_equals_throwError)
         apply (fastforce simp: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (rule ccorres_if_cond_throws[rotated -1, where Q = \<top> and Q' = \<top>])
          apply vcg
         apply (clarsimp simp: hd_drop_conv_nth hd_conv_nth pptrUserTop_val)
        apply (rule ccorres_equals_throwError)
         apply (fastforce simp: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply csymbr
       apply (erule allE, erule (1) impE)
       apply (clarsimp simp: checkVSpaceRoot_def isValidVTableRoot_def isVTableRoot_def
                             case_option_If2 if_to_top_of_bindE if_to_top_of_bind
                       simp del: Collect_const)
       apply (rule ccorres_if_cond_throws2[rotated -1, where Q = \<top> and Q' = \<top>])
          apply vcg
         apply (clarsimp simp: from_bool_def split: bool.split)
        apply (rule ccorres_equals_throwError)
         apply (fastforce simp: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply clarsimp
       apply (simp add: lookupError_injection invocationCatch_use_injection_handler
                        injection_bindE[OF refl refl] injection_handler_If bindE_assoc
                        injection_handler_throwError injection_liftE[OF refl])
       apply wpfix
       apply (ctac add: ccorres_injection_handler_csum1[OF ccorres_injection_handler_csum1,
                                                           OF findVSpaceForASID_ccorres])
          prefer 2 (* throw exception *)
          apply ccorres_rewrite
          apply (rule_tac P'="{s. errstate s = find_ret}" in ccorres_from_vcg_throws[where P=\<top>])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                syscall_error_to_H_cases exception_defs)
          apply (erule lookup_failure_rel_fault_lift[rotated])
          apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                 syscall_error_to_H_cases exception_defs)
         (* findVSpace succeeded *)
         apply ccorres_rewrite
         apply (clarsimp simp: if_to_top_of_bindE if_to_top_of_bind
                         simp del: Collect_const)
         apply (rule ccorres_if_cond_throws[rotated -1, where Q = \<top> and Q' = \<top>])
            apply vcg
           apply (clarsimp simp: ccap_relation_vspace_base)
          apply (rule ccorres_equals_throwError)
           apply (fastforce simp: throwError_bind invocationCatch_def injection_handler_def handleE'_def)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (clarsimp simp: injection_handler_bindE injection_handler_liftE bindE_assoc)
         apply (clarsimp simp: lookupFrame_def liftE_bindE bind_assoc split_def)
         apply (ctac add: lookupPTSlot_ccorres)
           apply (rule ccorres_split_nothrow, rule getObject_pte_ccorres)
               apply clarsimp
              apply ceqv
             apply (rename_tac pte pte')
             apply csymbr
             apply (clarsimp simp: if_to_top_of_bind
                             simp del: Collect_const)
             apply (rule ccorres_if_cond_throws2[rotated -1, where Q = \<top> and Q' = \<top>])
                apply (vcg exspec=setThreadState_modifies)
               apply (clarsimp simp: cpte_relation_def Let_def isPagePTE_def pte_lifts
                                     pte_pte_4k_page_lift_def pte_pte_page_lift_def
                               split: pte.splits if_splits)
              apply (clarsimp simp: injection_handler_returnOk ccorres_invocationCatch_Inr)
              apply (ctac (no_vcg) add: setThreadState_ccorres)
               apply (clarsimp simp: performInvocation_def AARCH64_H.performInvocation_def
                                     performARMMMUInvocation_def performVSpaceInvocation_def
                                     liftE_bindE)
               apply (rule ccorres_alternative2)
               apply (rule ccorres_return_CE; simp)
              apply wp
             apply (clarsimp simp: injection_handler_bindE injection_handler_liftE injection_handler_If
                                   injection_handler_returnOk bindE_assoc injection_handler_throwError
                                   checkValidMappingSize_def
                             cong: if_cong
                             simp del: Collect_const)
             apply (rule ccorres_assert)
             apply (clarsimp simp: liftE_bindE simp del: Collect_const)
             apply (rule ccorres_stateAssert)
             apply (clarsimp simp: if_to_top_of_bindE cong: if_cong simp del: Collect_const)
             apply (rule ccorres_move_const_guard)+
             apply (rule ccorres_if_cond_throws[rotated -1, where Q = \<top> and Q' = \<top>])
                apply vcg
               apply (clarsimp simp: pageBase_def shiftr_shiftl1 hd_conv_nth)
              apply (rule_tac P="unat (ptBitsLeft_C resolve_ret) < 0x40" in ccorres_gen_asm)
              apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: throwError_def return_def exception_defs syscall_error_rel_def
                                    syscall_error_to_H_def syscall_error_type_defs hd_conv_nth
                                    pageBase_def shiftr_shiftl1 mask_def word_less_nat_alt)
             apply (clarsimp simp: ccorres_invocationCatch_Inr performInvocation_def bindE_assoc
                                   AARCH64_H.performInvocation_def performARMMMUInvocation_def
                                   liftE_bindE
                             simp del: Collect_const)
             apply csymbr
             apply (erule allE, erule (1) impE, erule (1) impE)
             apply csymbr
             apply (rule ccorres_move_const_guard)+
             apply csymbr
             apply (ctac (no_vcg) add: setThreadState_ccorres)
              apply (rule_tac A="\<lambda>s. unat (ptBitsLeft_C resolve_ret) < 0x40 \<and>
                                     unat (ptBitsLeft_C resolve_ret) \<le> pptrBaseOffset_alignment \<and>
                                     2 ^ unat (ptBitsLeft_C resolve_ret) \<le> gsMaxObjectSize s" and
                              A'=UNIV in
                              ccorres_guard_imp)
                apply (ctac (no_vcg) add: performVSpaceFlush_ccorres)
                 apply (rule ccorres_alternative2)
                 apply (rule ccorres_return_CE; simp)
                apply wp
               apply (clarsimp cong: conj_cong simp flip: is_aligned_mask simp: fromPAddr_def)
               apply (rule conjI)
                apply (erule flush_range_le; simp add: linorder_not_le)
                 apply (erule word_less_sub_1)
                apply (simp add: mask_add_aligned mask_twice)
               apply (rule conjI)
                apply (erule flush_range_le; simp add: linorder_not_le)
                 apply (erule word_less_sub_1)
                apply (simp add: ptrFromPAddr_and_mask_eq mask_add_aligned mask_twice)
               apply (erule order_trans[rotated])
               apply (rule flush_range_le1; simp add: not_le)
               apply (erule word_less_sub_1)
              apply (clarsimp simp: hd_conv_nth mask_def flushtype_relation_triv)
             apply wp
            apply (clarsimp simp: word_less_nat_alt)
            apply wpfix
            apply (wp getPTE_wp)
           apply vcg
          apply (wp hoare_vcg_all_lift hoare_drop_imps lookupPTSlot_inv lookupPTSlot_bitsLeft_less_64)
         apply (vcg exspec=lookupPTSlot_modifies)
        apply (wp injection_handler_wp hoare_drop_imps)
       apply (vcg exspec=findVSpaceForASID_modifies)
      apply wp
     apply (vcg exspec=getSyscallArg_modifies)
    apply wp
   apply (vcg exspec=getSyscallArg_modifies)
  apply (simp only: isVSpaceFlushLabel_disj)
  apply (clarsimp simp: sysargs_rel_to_n valid_cap'_def capAligned_def valid_tcb_state'_def)
  apply (rule conjI; clarsimp simp: wellformed_mapdata'_def)
   apply fastforce
  apply (clarsimp simp: isValidVTableRoot_def ccap_relation_vspace_mapped_asid[symmetric])
  apply (clarsimp simp: word_less_nat_alt hd_conv_nth wellformed_mapdata'_def rf_sr_ksCurThread
                        cap_get_tag_isCap_unfolded_H_cap
                  dest!: at_least_2_args)
  done

lemma injection_handler_stateAssert_relocate:
  "injection_handler Inl (stateAssert ass xs >>= f) >>=E g
    = do v \<leftarrow> stateAssert ass xs; injection_handler Inl (f ()) >>=E g od"
  by (simp add: injection_handler_def handleE'_def bind_bindE_assoc bind_assoc)

lemma decodeARMMMUInvocation_ccorres:
  notes Collect_const[simp del] if_cong[cong]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps; \<not> isVCPUCap cp \<rbrakk>
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
       (decodeARMMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeARMMMUInvocation_'proc)"
  supply ccorres_prog_only_cong[cong]
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_' call_')
   apply csymbr
   apply (simp add: cap_get_tag_isCap_ArchObject
                    AARCH64_H.decodeInvocation_def
                    invocation_eq_use_types
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    (* PageTableCap, VSRootPT_T *)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeARMVSpaceRootInvocation_ccorres]; solves simp)
   apply (rule ccorres_Cond_rhs)
    (* PageTableCap, NormalPT_T *)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeARMPageTableInvocation_ccorres]; solves simp)
   apply (rule ccorres_Cond_rhs)
    (* FrameCap *)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeARMFrameInvocation_ccorres]; solves simp)
   (* ASIDControlCap *)
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: decodeARMMMUInvocation_def decodeARMASIDControlInvocation_def isCap_simps
                             throwError_bind invocationCatch_def
                      split: invocation_label.split arch_invocation_label.split)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    (* ARMASIDControlMakePool *)
    apply (simp add: decodeARMMMUInvocation_def decodeARMASIDControlInvocation_def isCap_simps)
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
    apply (prop_tac "1 < length extraCaps")
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
            apply (rule ccorres_pre_gets_armKSASIDTable_ksArchState)
            apply (rename_tac asid_table)
            apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                   rule ccorres_rhs_assoc2)
            apply (rule ccorres_add_return)
            apply (rule_tac r'="\<lambda>rv rv'. rv' = (case [p \<leftarrow> assocs asid_table.
                                                      fst p < 2 ^ asid_high_bits \<and> snd p = None]
                                                of [] \<Rightarrow> 2 ^ asid_high_bits | x # xs \<Rightarrow> fst x)"
                    and xf'=i_' in ccorres_split_nothrow)
                apply (rule_tac P="\<forall>x \<in> ran asid_table. x \<noteq> 0"
                                in ccorres_gen_asm)
                apply (rule_tac P="\<lambda>s. asid_table = armKSASIDTable (ksArchState s)"
                                in ccorres_from_vcg[where P'=UNIV])
                apply (clarsimp simp: return_def)
                apply (rule HoarePartial.SeqSwap)
                 (* i_' = i___unsigned_long_' *)
                 apply (rule_tac I="{t. (\<sigma>, t) \<in> rf_sr \<and> i_' t \<le> 2 ^ asid_high_bits
                                        \<and> asid_table = armKSASIDTable (ksArchState \<sigma>)
                                        \<and> (\<forall>x < i_' t. asid_table x \<noteq> None)
                                        \<and> ret__int_' t = from_bool (i_' t < 2 ^ asid_high_bits \<and>
                                                                    asid_table (i_' t) \<noteq> None)}"
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
                  apply (clarsimp simp: rf_sr_armKSASIDTable
                                        asid_high_bits_word_bits
                                        option_to_ptr_def option_to_0_def
                                        order_less_imp_le
                                        linorder_not_less
                                        order_antisym[OF inc_le])
                  apply (clarsimp split: option.split if_split)
                  apply (rule conjI; clarsimp simp: Kernel_C_defs asid_high_bits_def word_less_nat_alt
                                                    from_bool_0 unat_add_lem[THEN iffD1])
                   apply (drule_tac n="i_' x + 1" in rf_sr_armKSASIDTable)
                    apply (simp add: asid_high_bits_def mask_def word_le_nat_alt)
                   apply (clarsimp simp: option_to_ptr_def option_to_0_def split: option.splits)
                  apply (drule_tac n="i_' x + 1" in rf_sr_armKSASIDTable)
                   apply (simp add: asid_high_bits_def mask_def word_le_nat_alt)
                  apply (clarsimp simp: option_to_ptr_def option_to_0_def ran_def split: option.splits)
                  apply blast
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
                                      rf_sr_armKSASIDTable[where n=0, simplified])
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
                                            AARCH64_H.performInvocation_def
                                            performARMMMUInvocation_def)
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
                         apply (clarsimp simp: null_def ThreadState_defs mask_def hd_conv_nth
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
    apply (simp add: imp_conjR[symmetric] decodeARMMMUInvocation_def)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (clarsimp simp: isCap_simps decodeARMASIDPoolInvocation_def)
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
     apply (clarsimp simp: isCap_simps decodeARMASIDPoolInvocation_def
                           throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    apply (simp add: isCap_simps decodeARMASIDPoolInvocation_def split: list.split)
    apply (intro allI impI)
    apply csymbr
    apply (rule ccorres_add_return)
    apply (rule ccorres_Guard_Seq)
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_rhs_assoc2)
    apply (rule_tac R="excaps_in_mem extraCaps \<circ> ctes_of" and
                    R'="UNIV" and
                    val="from_bool (\<not>isVTableRoot (fst (extraCaps ! 0)) \<or>
                                    capPTMappedAddress (capCap (fst (extraCaps ! 0))) \<noteq> None)" and
                    xf'=ret__int_' in ccorres_symb_exec_r_known_rv)
       apply vcg
       apply clarsimp
       apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
       apply (clarsimp simp: excaps_in_mem_def)
       apply (frule (1) slotcap_in_mem_VSpace)
       apply (clarsimp simp: typ_heap_simps' from_bool_0 isVTableRoot_cap_eq)
       apply (fastforce simp: isCap_simps ccap_relation_VSpaceCap_IsMapped split: if_splits)
      apply ceqv
     apply (rule ccorres_Cond_rhs_Seq)
      apply ccorres_rewrite
      apply (rule_tac v="Inl (InvalidCapability 1)" in ccorres_equals_throwError)
       apply (fastforce simp: isCap_simps throwError_bind invocationCatch_def isVTableRoot_def
                        split: capability.split arch_capability.split option.splits pt_type.splits)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (fastforce simp: syscall_error_to_H_cases)
     apply (simp add: isCap_simps isVTableRoot_ex, elim exE conjE)
     apply (simp add: isCap_simps Kernel_C_defs liftE_bindE bind_assoc isVTableRoot_def)
     apply (rule ccorres_pre_gets_armKSASIDTable_ksArchState)
     apply csymbr
     apply (rule ccorres_Guard_Seq)+
     apply (rule ccorres_add_return)
     apply (rule_tac r'="\<lambda>_ rv'. rv' = option_to_ptr (x (ucast (asid_high_bits_of (ucast (capASIDBase cp)))))
                                 \<and> x (ucast (asid_high_bits_of (ucast (capASIDBase cp)))) \<noteq> Some 0"
                 and xf'=pool_' in ccorres_split_nothrow)
         apply (rule_tac P="\<lambda>s. x = armKSASIDTable (ksArchState s)
                                \<and> valid_arch_state' s \<and> s \<turnstile>' ArchObjectCap cp"
                         in ccorres_from_vcg[where P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def valid_arch_state'_def valid_asid_table'_def)
         apply (frule cap_get_tag_isCap_ArchObject(2))
         apply (clarsimp simp: isCap_simps)
         apply (erule_tac v=cap in ccap_relationE)
         apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_simps valid_cap_simps'
                               cap_asid_pool_cap_lift_def)
         apply (subst rf_sr_armKSASIDTable, assumption)
          apply (rule leq_asid_bits_shift, simp)
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
           apply (rename_tac pool)
           apply (rule_tac P="ko_at' pool (capASIDPool cp)"
                           in ccorres_from_vcg[where P'=UNIV])
           apply (clarsimp simp: option_to_0_def option_to_ptr_def
                                 return_def)
           apply (rule HoarePartial.SeqSwap)
            apply (rule_tac I="{t. (\<sigma>, t) \<in> rf_sr \<and> i_' t \<le> 2 ^ asid_low_bits
                                 \<and> ko_at' pool (capASIDPool cp) \<sigma>
                                 \<and> (\<exists>v. cslift t (ap_Ptr (capASIDPool cp)) = Some v \<and>
                                          (\<forall>x < i_' t. capASIDBase cp + x = 0 \<or>
                                                asid_map_get_tag (index (array_C v) (unat x)) =
                                                  scast asid_map_asid_map_vspace) \<and>
                                         ret__int_' t = from_bool (i_' t < 2 ^ asid_low_bits \<and>
                                         (capASIDBase cp + (i_' t) = 0 \<or>
                                           asid_map_get_tag (index (array_C v) (unat (i_' t))) =
                                             scast asid_map_asid_map_vspace)))}"
                         in HoarePartial.reannotateWhileNoGuard)
            apply (rule HoarePartial.While[OF order_refl])
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: asidLowBits_handy_convs word_sle_def word_sless_def from_bool_0)
             apply (rename_tac s v)
             apply (subgoal_tac "capASIDBase_CL (cap_asid_pool_cap_lift cap)
                                     = capASIDBase cp")
              apply (subgoal_tac "\<And>x. (x < (i_' s + 1))
                                        = (x < i_' s \<or> x = i_' s)")
               apply (clarsimp simp: typ_heap_simps ccap_relation_capASIDBase)
               apply (clarsimp simp: inc_le asid_low_bits_def not_less split: if_split)
              apply unat_arith
             apply (solves \<open>simp add: ccap_relation_capASIDBase\<close>)
            apply (clarsimp simp: from_bool_0)
            apply (rename_tac s v)
            apply (erule cmap_relationE1[OF rf_sr_cpspace_asidpool_relation],
                   erule ko_at_projectKO_opt)
            apply (clarsimp simp: typ_heap_simps casid_pool_relation_def
                                    inv_ASIDPool array_relation_def
                             split: asidpool.split_asm asid_pool_C.split_asm)
            apply (case_tac "i_' s = 2 ^ asid_low_bits")
             apply (clarsimp split: list.split)
             apply (rename_tac a b xs)
             apply (drule_tac f="\<lambda>xs. (a, b) \<in> set xs" in arg_cong)
             apply (clarsimp simp: in_assocs_is_fun mask_def)
             apply (drule spec, drule(1) mp)
             apply (simp add: asid_low_bits_word_bits)
             apply (drule spec, drule(1) mp)
             apply (simp add: option_to_ptr_def option_to_0_def field_simps)
            apply (frule(1) neq_le_trans)
            apply (subst filter_assocs_Cons)
              apply (simp add: split_def asid_low_bits_word_bits)
              apply (rule conjI, assumption)
              apply (clarsimp simp add: field_simps)
              apply (erule_tac x="i_' s" in allE, erule impE,
                     solves \<open>clarsimp simp: le_mask_iff_lt_2n[THEN iffD1] asid_low_bits_def\<close>)
              apply (fastforce simp: casid_map_relation_def asid_map_lift_def)
             apply (simp add: asid_low_bits_word_bits)
             apply (erule allEI, rule impI, erule(1) impE)
             apply (clarsimp simp: field_simps)
             apply (rename_tac x')
             apply (drule_tac x=x' in spec)
             apply (simp add: le_mask_iff_lt_2n[THEN iffD1] asid_low_bits_def
                         split: if_split_asm option.splits)
            apply simp
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: asidLowBits_handy_convs
                                 signed_shift_guard_simpler_64 asid_low_bits_def
                                 word_sless_def word_sle_def)
           apply (erule cmap_relationE1[OF rf_sr_cpspace_asidpool_relation],
                  erule ko_at_projectKO_opt)
           apply (clarsimp simp: typ_heap_simps ccap_relation_capASIDBase split: if_split)
          apply ceqv
         apply (simp add: assertE_liftE liftE_bindE bind_assoc)
         apply (simp add: if_to_top_of_bind asid_low_bits_def)
         apply ccorres_rewrite
         apply (rule ccorres_if_cond_throws[where Q=\<top> and Q'=\<top>, rotated -1])
            apply vcg
           apply (clarsimp simp: null_def asid_low_bits_def split: list.split
                           dest!: filter_eq_ConsD)
          apply (simp add: throwError_bind invocationCatch_def)
          apply (rule syscall_error_throwError_ccorres_n)
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: returnOk_bind ccorres_invocationCatch_Inr
                          performInvocation_def
                          AARCH64_H.performInvocation_def liftE_bindE)
         apply csymbr
         apply (ctac add: setThreadState_ccorres)
           apply (simp add: performARMMMUInvocation_def bindE_assoc flip: liftE_liftE returnOk_liftE)
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
       apply (rule conseqPre, vcg, rule subset_refl)
      apply simp
      (* HACK: rewrites to fix schematic dependency problems *)
      apply (rule_tac t=v0 and s="capASIDPool cp" in subst, fastforce)
      apply (rule_tac t=v1 and s="capASIDBase cp" in subst, fastforce)
      apply (rule_tac t=b and s="snd (extraCaps ! 0)" in subst, fastforce)
      apply (rule return_wp)
     apply (rule conseqPre, vcg)
     apply (rule_tac t=v0 and s="capASIDPool cp" in subst, fastforce)
     apply (rule_tac t=v1 and s="capASIDBase cp" in subst, fastforce)
     apply (rule_tac t=b and s="snd (extraCaps ! 0)" in subst, fastforce)
     apply (rule subset_refl)
    apply (rule_tac t=b and s="snd (extraCaps ! 0)" in subst, fastforce)
    apply (rule conseqPre, vcg, rule subset_refl)
   (* Can't reach *)
   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
   apply (cases cp; simp add: isCap_simps)
   apply (rename_tac pt_t m)
   apply (case_tac pt_t; simp)
  apply clarsimp
  apply (rule conjI) (* PTCap VSRoot *)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (drule_tac t="cteCap cte" in sym)
   apply (frule(1) ctes_of_valid', simp)
  apply (rule conjI) (* not PTCap VSRoot *)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (drule_tac t="cteCap cte" in sym)
   apply (frule(1) ctes_of_valid', simp)
   apply (rule conjI, clarsimp, simp) (* PTCap NormalPT_T *)
   apply clarsimp
   apply (rule conjI, clarsimp, simp) (* FrameCap *)
   apply clarsimp
   apply (rule conjI, clarsimp simp: isCap_simps) (* ASIDControlCap *)
    apply (clarsimp simp: cte_wp_at_ctes_of ct_in_state'_def
                          interpret_excaps_eq excaps_map_def)
    apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt not_le)
    apply (rule conjI; clarsimp)
    apply (frule invs_arch_state')
    apply (rule conjI, clarsimp simp: valid_arch_state'_def valid_asid_table'_def)
    apply (clarsimp simp: neq_Nil_conv excaps_map_def valid_tcb_state'_def invs_sch_act_wf'
                          unat_lt2p[where 'a=machine_word_len, folded word_bits_def])
    apply (frule interpret_excaps_eq[rule_format, where n=1], simp)
    apply (rule conjI; clarsimp)+
    apply (rule conjI, erule ctes_of_valid', clarsimp)
    apply (intro conjI)
            apply fastforce
           apply fastforce
          apply fastforce
         apply (fastforce elim!: pred_tcb'_weakenE)
        apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
        apply (case_tac "tcbState obj", (simp add: runnable'_def)+)[1]
       apply (clarsimp simp: excaps_in_mem_def slotcap_in_mem_def)
       apply (rule sym, simp add: objBits_simps)
      apply (simp add: ex_cte_cap_wp_to'_def cte_wp_at_ctes_of)
      apply clarsimp
      apply (rule exI)+
      apply (rule conjI; assumption)
     apply (clarsimp simp: null_def neq_Nil_conv)
     apply (drule_tac f="\<lambda>xs. (a, bb) \<in> set xs" in arg_cong)
     apply (clarsimp simp: in_assocs_is_fun)
     apply (clarsimp simp: le_mask_asid_bits_helper)
    apply (simp add: is_aligned_shiftl_self)
   (* ARMASIDPoolAssign *)
   apply (clarsimp simp: isCap_simps valid_tcb_state'_def invs_sch_act_wf')
   apply (frule invs_arch_state', clarsimp)
   apply (intro conjI)
         apply fastforce
        apply fastforce
       apply fastforce
      apply (fastforce simp: ct_in_state'_def elim!: pred_tcb'_weakenE)
     apply (fastforce simp: ct_in_state'_def elim!: pred_tcb'_weakenE)
    apply (cases extraCaps; simp)
    apply (clarsimp simp: excaps_in_mem_def slotcap_in_mem_def isPTCap'_def)
   apply (simp add: valid_cap'_def)
   apply (clarsimp simp: null_def neq_Nil_conv mask_def field_simps
                         asid_low_bits_word_bits asidInvalid_def asid_wf_def
                  dest!: filter_eq_ConsD)
   apply (subst is_aligned_add_less_t2n[rotated]; assumption?)
     apply (simp add: asid_low_bits_def asid_bits_def)
     apply (clarsimp simp: asid_wf_def valid_cap'_def asid_bits_def mask_def word_le_nat_alt
                           word_less_nat_alt)
    apply (simp add: asid_bits_def asid_low_bits_def)
   apply (rule TrueI)
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_ctes_of asidHighBits_handy_convs
                        word_sle_def word_sless_def asidLowBits_handy_convs
                        rf_sr_ksCurThread ThreadState_defs mask_def[where n=4]
                  cong: if_cong)
  apply (clarsimp simp: ccap_relation_isDeviceCap2 objBits_simps pageBits_def case_bool_If)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def excaps_map_def)
   apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
   apply (frule interpret_excaps_eq[rule_format, where n=1], simp)
   apply (clarsimp simp: mask_def[where n=4] slotcap_in_mem_def
                         ccap_rights_relation_def rightsFromWord_wordFromRights)
   apply (clarsimp simp: asid_high_bits_word_bits Kernel_C.asidHighBits_def split: list.split_asm)
    apply (clarsimp simp: cap_untyped_cap_lift_def cap_lift_untyped_cap
                          cap_to_H_def[split_simps cap_CL.split]
                          hd_conv_nth length_ineq_not_Nil Kernel_C_defs
                   elim!: ccap_relationE)
   apply (clarsimp simp: to_bool_def unat_eq_of_nat objBits_simps pageBits_def case_bool_If
                  split: if_splits)
  apply (clarsimp simp: asid_low_bits_word_bits isCap_simps neq_Nil_conv
                        excaps_map_def excaps_in_mem_def from_bool_0
                        p2_gt_0[where 'a=machine_word_len, folded word_bits_def])
  apply (drule_tac t="cteCap cte" in sym, simp)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(13)) (* ASIDPoolCap *)
  apply (frule ctes_of_valid', clarsimp)
  apply (clarsimp simp: valid_cap'_def capAligned_def
                        ccap_relation_capASIDPool ccap_relation_capASIDBase)
  apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (elim conjE)
  apply (frule (1) slotcap_in_mem_VSpace)
  apply (clarsimp simp: typ_heap_simps isVTableRoot_ex isCap_simps asid_wf_table_guard inv_ASIDPool)
  apply (prop_tac "asid_low_bits < LENGTH(machine_word_len)", simp add: asid_low_bits_def)
  apply (simp add: le_mask_iff_lt_2n[THEN iffD1, symmetric])
  apply (clarsimp simp: asid_low_bits_def mask_def cong: list.case_cong split: list.split)
  done

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
  apply (simp add: AARCH64.msgInfoRegister_def C_register_defs rf_sr_ksCurThread
                   AARCH64_H.msgInfoRegister_def)
  done

lemma foldl_all_False:
  "(\<not> foldl (\<lambda>b x. b \<or> f x) False xs) = (\<forall>x \<in> set xs. \<not> f x)"
  apply (subst foldl_fun_or_alt)
  apply (fold orList_def)
  apply (simp add: orList_False image_subset_iff)
  done

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

lemma vcpu_reg_saved_when_disabled_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
           Call vcpu_reg_saved_when_disabled_'proc
           \<lbrace> \<acute>ret__unsigned_long = from_bool (\<^bsup>s\<^esup>field \<in> {scast seL4_VCPUReg_SCTLR,
                                                          scast seL4_VCPUReg_CNTV_CVAL,
                                                          scast seL4_VCPUReg_CNTVOFF,
                                                          scast seL4_VCPUReg_CNTKCTL_EL1,
                                                          scast seL4_VCPUReg_CNTV_CTL,
                                                          scast seL4_VCPUReg_CPACR}) \<rbrace>"
  by vcg clarsimp

lemma vcpuRegSavedWhenDisabled_spec[simp]:
  "vcpuRegSavedWhenDisabled reg = (reg = VCPURegSCTLR \<or> reg = VCPURegCNTV_CVAL \<or>
                                   reg = VCPURegCNTVOFF \<or> reg = VCPURegCNTKCTL_EL1 \<or>
                                   reg = VCPURegCNTV_CTL \<or> reg = VCPURegCPACR)"
  by (simp add: vcpuRegSavedWhenDisabled_def split: vcpureg.splits)

lemma writeVCPUReg_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres dc xfdc
      (vcpu_at' vcpuptr and no_0_obj')
      (UNIV \<inter> \<lbrace>\<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace>
            \<inter> \<lbrace>\<acute>field = of_nat (fromEnum reg) \<rbrace>
            \<inter> \<lbrace>\<acute>value = val\<rbrace>) hs
    (writeVCPUReg vcpuptr reg val) (Call writeVCPUReg_'proc)"
  apply (cinit lift: vcpu_' field_' value_')
   apply clarsimp
   apply (rule ccorres_pre_getCurVCPU, rename_tac cvcpuopt)
   (* abstract out check for "is vcpuptr the current vcpu" in terms of cvcpuopt *)
   apply (rule_tac C'="{s. cvcpuopt \<noteq> None \<and> (cvcpuopt \<noteq> None \<longrightarrow> fst (the cvcpuopt) = vcpuptr) }"
            and Q="\<lambda>s. vcpuptr \<noteq> 0 \<and> (armHSCurVCPU \<circ> ksArchState) s = cvcpuopt"
            and Q'=UNIV in ccorres_rewrite_cond_sr)
    subgoal by (fastforce dest: rf_sr_ksArchState_armHSCurVCPU simp: cur_vcpu_relation_def
                        split: option.splits)
   apply (rule ccorres_Cond_rhs)
    \<comment> \<open>vcpuptr is current vcpu\<close>
    apply clarsimp
    apply (rename_tac curvcpuactive)
    apply csymbr
    apply (rule_tac C'="{s. (reg = VCPURegSCTLR \<or> reg = VCPURegCNTV_CVAL \<or> reg = VCPURegCNTVOFF \<or>
                             reg = VCPURegCNTKCTL_EL1 \<or> reg = VCPURegCNTV_CTL \<or> reg = VCPURegCPACR) \<and> \<not>curvcpuactive }"
                            and Q="\<lambda>s. (armHSCurVCPU \<circ> ksArchState) s = Some (vcpuptr, curvcpuactive)"
                            and Q'=UNIV in ccorres_rewrite_cond_sr)
     subgoal by (clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU
                          simp: cur_vcpu_relation_def from_bool_0 vcpureg_eq_use_types
                          split: option.splits)
     (* unification choking on schematics with pairs *)
    apply (rule_tac A="vcpu_at' vcpuptr" and A'=UNIV in ccorres_guard_imp)
      apply (rule ccorres_Cond_rhs, clarsimp)
       apply (ctac (no_vcg) add: vcpu_write_reg_ccorres)
      apply (simp (no_asm_simp))
      apply (ctac (no_vcg) add: vcpu_hw_write_reg_ccorres)
     apply fastforce
    apply fastforce
   \<comment> \<open>no current vcpu\<close>
   apply clarsimp
   apply wpc
   apply (rename_tac cur b, prop_tac "\<not>cur", fastforce)
   apply simp
   apply (ctac (no_vcg) add: vcpu_write_reg_ccorres)
  apply fastforce
  done

lemma readVCPUReg_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres ((=)) ret__unsigned_long_'
      (vcpu_at' vcpuptr and no_0_obj')
      (UNIV \<inter> \<lbrace>\<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace> \<inter> \<lbrace>\<acute>field = of_nat (fromEnum reg) \<rbrace>) hs
    (readVCPUReg vcpuptr reg) (Call readVCPUReg_'proc)"
  apply (cinit lift: vcpu_' field_')
   apply clarsimp
   apply (rule ccorres_pre_getCurVCPU, rename_tac cvcpuopt)
   (* abstract out check for "is vcpuptr the current vcpu" in terms of cvcpuopt *)
   apply (rule_tac C'="{s. cvcpuopt \<noteq> None \<and> (cvcpuopt \<noteq> None \<longrightarrow> fst (the cvcpuopt) = vcpuptr) }"
            and Q="\<lambda>s. vcpuptr \<noteq> 0 \<and> (armHSCurVCPU \<circ> ksArchState) s = cvcpuopt"
            and Q'=UNIV in ccorres_rewrite_cond_sr)
    subgoal by (fastforce dest: rf_sr_ksArchState_armHSCurVCPU simp: cur_vcpu_relation_def
                          split: option.splits)
   apply (rule ccorres_Cond_rhs)
    \<comment> \<open>vcpuptr is current vcpu\<close>
    apply clarsimp
    apply (rename_tac curvcpuactive)
    apply csymbr
    apply (rule_tac C'="{s. (reg = VCPURegSCTLR \<or> reg = VCPURegCNTV_CVAL \<or> reg = VCPURegCNTVOFF \<or>
                             reg = VCPURegCNTKCTL_EL1 \<or> reg = VCPURegCNTV_CTL \<or> reg = VCPURegCPACR) \<and> \<not>curvcpuactive }"
                            and Q="\<lambda>s. (armHSCurVCPU \<circ> ksArchState) s = Some (vcpuptr, curvcpuactive)"
                            and Q'=UNIV in ccorres_rewrite_cond_sr)
     subgoal by (clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU
                          simp: cur_vcpu_relation_def from_bool_0 vcpureg_eq_use_types
                          split: option.splits)
    (* unification choking on schematics with pairs *)
    apply (rule_tac A="vcpu_at' vcpuptr" and A'=UNIV in ccorres_guard_imp)
      apply (rule ccorres_Cond_rhs, clarsimp)
       apply (rule ccorres_add_return2)
       apply (ctac (no_vcg) add: vcpu_read_reg_ccorres)
        apply (fastforce intro!: ccorres_return_C)
       apply wp
      apply (simp (no_asm_simp))
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: vcpu_hw_read_reg_ccorres)
       apply (fastforce intro!: ccorres_return_C)
      apply wp
     apply fastforce
    apply fastforce
   \<comment> \<open>no current vcpu\<close>
   apply clarsimp
   apply wpc
   apply (rename_tac cur b, prop_tac "\<not>cur", fastforce)
   apply simp
   apply (rule ccorres_add_return2)
   apply (ctac (no_vcg) add: vcpu_read_reg_ccorres)
    apply (fastforce intro!: ccorres_return_C)
   apply wp
  apply fastforce
  done

crunch readVCPUReg
  for st_tcb_at'[wp]: "\<lambda>s. Q (st_tcb_at' P t s)"
  and pspace_aligned'[wp]: "pspace_aligned'"
  and pspace_distinct'[wp]: "pspace_distinct'"
  (wp: crunch_wps simp: crunch_simps)

lemma invokeVCPUReadReg_ccorres: (* styled after invokeTCB_ReadRegisters_ccorres *)
  notes Collect_const[simp del]
  shows
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_in_state' ((=) Restart)
         and vcpu_at' vcpuptr)
       (UNIV \<inter> \<lbrace>\<acute>vcpu = Ptr vcpuptr \<rbrace>
             \<inter> \<lbrace>\<acute>field = of_nat (fromEnum reg) \<rbrace>
             \<inter> \<lbrace>\<acute>call = from_bool isCall \<rbrace>)
       hs
       (do reply \<leftarrow> invokeVCPUReadReg vcpuptr reg;
           liftE (replyOnRestart thread reply isCall) od)
       (Call invokeVCPUReadReg_'proc)"
  apply (cinit' lift: vcpu_' field_' call_' simp: invokeVCPUReadReg_def)
   apply (clarsimp simp: bind_assoc)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=thread_' in ccorres_abstract, ceqv)
     apply (rename_tac cthread,
      rule_tac P="cthread = tcb_ptr_to_ctcb_ptr thread" in ccorres_gen_asm2)
     apply (rule ccorres_pre_getCurThread, rename_tac curthread)
     apply (rule_tac P="curthread = thread" in ccorres_gen_asm)
     apply clarsimp
     apply (ctac add: readVCPUReg_ccorres)
       apply (rule ccorres_Cond_rhs_Seq[rotated]; clarsimp)

        \<comment> \<open>if we are not part of a call\<close>
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

       \<comment> \<open>now if we are part of a call\<close>
       apply (rule ccorres_rhs_assoc)+
       apply (rename_tac rval)
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
             (* setMessageInfo_ccorres does not fire here, no idea why *)
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
           apply (clarsimp simp: msgInfoRegister_def AARCH64.msgInfoRegister_def Kernel_C.msgInfoRegister_def Kernel_C.X1_def)
           apply (vcg exspec=setMR_modifies)
          apply wpsimp
         apply clarsimp
         apply (vcg exspec=setRegister_modifies)
        apply wpsimp
       apply clarsimp
       apply (vcg exspec=lookupIPCBuffer_modifies)
      apply clarsimp
      apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_all_lift hoare_vcg_imp_lift)
     apply clarsimp
     apply (vcg exspec=readVCPUReg_modifies)
    apply vcg
   apply clarsimp
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: invs_no_0_obj' tcb_at_invs' invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold ThreadState_defs
                        seL4_MessageInfo_lift_def message_info_to_H_def mask_def)
  apply (cases isCall; clarsimp)
   apply (rule conjI, clarsimp simp: ct_in_state'_def st_tcb_at'_def comp_def)
    apply (fastforce simp: obj_at'_def)
   apply (clarsimp simp: AARCH64.badgeRegister_def AARCH64_H.badgeRegister_def C_register_defs)
   apply (simp add: rf_sr_def cstate_relation_def Let_def)
  apply (rule conjI, fastforce simp: pred_tcb_at'_def obj_at'_def ct_in_state'_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  done

lemma liftE_invokeVCPUWriteReg_empty_return:
  "liftE (invokeVCPUWriteReg vcpu reg val) >>=E (\<lambda>rv. m rv)
    = liftE (invokeVCPUWriteReg vcpu reg val) >>=E (\<lambda>_. m [])"
  unfolding invokeVCPUWriteReg_def
  by (clarsimp simp: liftE_bindE bind_assoc)

lemma invokeVCPUWriteReg_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and vcpu_at' vcpuptr)
       (UNIV \<inter> \<lbrace>\<acute>vcpu = Ptr vcpuptr \<rbrace>
             \<inter> \<lbrace>\<acute>field = of_nat (fromEnum reg) \<rbrace>
             \<inter> \<lbrace>\<acute>value = val \<rbrace>)
       hs
       (liftE (invokeVCPUWriteReg vcpuptr reg val))
       (Call invokeVCPUWriteReg_'proc)"
  apply (cinit' lift: vcpu_' field_' value_'
                simp: invokeVCPUWriteReg_def gets_bind_ign liftE_liftM)
   apply clarsimp
   apply (ctac (no_vcg) add: writeVCPUReg_ccorres)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: return_def)
  by (wpsimp simp: invs_no_0_obj')+

lemma decodeVCPUWriteReg_ccorres:
  notes if_cong[cong] Collect_const[simp del]
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and sysargs_rel args buffer
              and (valid_cap' (ArchObjectCap cp)) and K (isVCPUCap cp))
       (UNIV \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) hs
       (decodeVCPUWriteReg args cp
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeVCPUWriteReg_'proc)"
  apply (rule ccorres_grab_asm)
  apply (cinit' lift: length___unsigned_long_' cap_' buffer_' simp: decodeVCPUWriteReg_def Let_def)
   apply (rule ccorres_Cond_rhs_Seq ; clarsimp)
    apply (rule_tac ccorres_gen_asm[where P="length args < 2"])
    apply clarsimp
    apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule_tac ccorres_gen_asm[where P="Suc 0 < length args"])
   apply clarsimp
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply (clarsimp simp: fromEnum_maxBound_vcpureg_def seL4_VCPUReg_Num_def hd_conv_nth[symmetric])
       apply (rule ccorres_Cond_rhs_Seq)
        apply (simp add: word_le_nat_alt throwError_bind invocationCatch_def invocation_eq_use_types
                   cong: StateSpace.state.fold_congs globals.fold_congs)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (clarsimp simp: word_le_nat_alt)
       apply (simp add: returnOk_bind bindE_assoc
                        performARMMMUInvocations performARMVCPUInvocation_def)
       \<comment> \<open>we want the second alternative - nothing to return to user\<close>
       apply (subst liftE_invokeVCPUWriteReg_empty_return, clarsimp)
       apply (ctac add: setThreadState_ccorres)
         apply csymbr
         apply (ctac add: invokeVCPUWriteReg_ccorres)
            apply (rule ccorres_alternative2)
            apply (rule ccorres_return_CE, simp+)[1]
           apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
          apply wp
         apply (vcg exspec=invokeVCPUWriteReg_modifies)
        apply (wpsimp wp: sts_invs_minor' ct_in_state'_set)+
       apply (vcg exspec=setThreadState_modifies)
      apply clarsimp
      apply (rule return_inv) (* force getting rid of schematic, wp does wrong thing here *)
     apply (vcg exspec=getSyscallArg_modifies)
    apply (rule return_inv)
   apply (vcg exspec=getSyscallArg_modifies)

  apply (clarsimp simp: word_less_nat_alt word_le_nat_alt conj_commute
                        invs_no_0_obj' tcb_at_invs' invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        valid_tcb_state'_def ThreadState_defs mask_def)
  apply (rule conjI; clarsimp) \<comment> \<open>not enough args\<close>
   apply (clarsimp simp: isCap_simps cap_get_tag_isCap capVCPUPtr_eq)
   apply (subst from_to_enum; clarsimp simp: fromEnum_maxBound_vcpureg_def)
  \<comment> \<open>enough args\<close>
  apply (clarsimp simp: isCap_simps cap_get_tag_isCap capVCPUPtr_eq valid_cap'_def)
  apply (subgoal_tac "args \<noteq> []")
   prefer 2 subgoal by (cases args; clarsimp, unat_arith?)
  by (fastforce simp: sysargs_rel_to_n ct_in_state'_def st_tcb_at'_def comp_def
                    elim: obj_at'_weakenE)

lemma liftE_invokeVCPUInjectIRQ_empty_return:
  "liftE (invokeVCPUInjectIRQ vcpu reg val) >>=E (\<lambda>rv. m rv)
    = liftE (invokeVCPUInjectIRQ vcpu reg val) >>=E (\<lambda>_. m [])"
  unfolding invokeVCPUInjectIRQ_def
  by (clarsimp simp: liftE_bindE bind_assoc)

lemma invokeVCPUInjectIRQ_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and vcpu_at' vcpuptr and K (idx < max_armKSGICVCPUNumListRegs))
       (UNIV \<inter> \<lbrace>\<acute>vcpu = Ptr vcpuptr \<rbrace>
             \<inter> \<lbrace>\<acute>index = of_nat idx \<rbrace>
             \<inter> \<lbrace> virq_to_H \<acute>virq = virq \<rbrace>)
       hs
       (liftE (invokeVCPUInjectIRQ vcpuptr idx virq))
       (Call invokeVCPUInjectIRQ_'proc)"
  apply (rule ccorres_grab_asm)
  apply (cinit' lift: vcpu_' index_' virq_')
   supply not_None_eq[simp del]
   apply (simp add: invokeVCPUInjectIRQ_def gets_bind_ign liftE_liftM)
   apply clarsimp
   apply (rule_tac P="vcpuptr \<noteq> 0" in ccorres_gen_asm)
   apply (rule ccorres_pre_getCurVCPU, rename_tac hsCurVCPU)
     apply (rule_tac Q="\<lambda>s. hsCurVCPU = (armHSCurVCPU \<circ> ksArchState) s"
              and Q'=UNIV
              and C'="{s. hsCurVCPU \<noteq> None \<and> fst (the hsCurVCPU) = vcpuptr}"
              in ccorres_rewrite_cond_sr_Seq)
    apply (clarsimp)
    apply (frule rf_sr_ksArchState_armHSCurVCPU)
    apply (clarsimp simp: cur_vcpu_relation_def split_def split: option.splits)
   apply (rule ccorres_Cond_rhs_Seq)
    apply clarsimp
    apply (ctac (no_vcg) add: set_gic_vcpu_ctrl_lr_ccorres)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg, clarsimp simp: return_def)
    apply (rule wp_post_taut)
   apply (simp only:)
   apply (clarsimp simp: bind_assoc)
   apply (rule ccorres_move_const_guards)
   apply (rule ccorres_move_c_guard_vcpu)
   apply (ctac (no_vcg) add: vgicUpdateLR_ccorres)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg, clarsimp simp: return_def)
    apply wpsimp+
  apply (clarsimp simp: unat_of_nat_eq word_of_nat_less max_armKSGICVCPUNumListRegs_val)
  apply (rule conjI)
   apply (clarsimp elim: typ_at'_no_0_objD invs_no_0_obj')
  apply (subst scast_eq_ucast; simp?)
  apply (rule not_msb_from_less)
  apply (clarsimp simp: word_less_nat_alt unat_of_nat_eq word_of_nat_less)
  done

(* Note: only works for virqEOIIRQEN = 1 because that is the only type we are using *)
lemma virq_virq_pending_EN_new_spec:
  shows
  "\<forall>s. \<Gamma> \<turnstile> {s}
       Call virq_virq_pending_new_'proc
       \<lbrace> virqEOIIRQEN_' s = 1 \<longrightarrow> virq_to_H \<acute>ret__struct_virq_C = makeVIRQ (virqGroup_' s) (virqPriority_' s) (virqIRQ_' s) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  (* unfold config to match up with bitfield gen shifts *)
  apply (clarsimp simp: virq_to_H_def make_virq_def virq_virq_pending_def
                        Kernel_Config.config_ARM_GIC_V3_def virq_type_shift_def
                        eoiirqen_shift_def mask_def)
  by (simp add: bit.disj_commute  bit.disj_assoc bit.disj_ac)

lemma virq_virq_active_eq_is_virq_active:
  "(of_nat (virq_type virq) = (scast virq_virq_active :: machine_word)) = is_virq_active virq"
  apply (simp add: is_virq_active_def virq_virq_active_def)
  apply (rule iffI; clarsimp?)
  apply (clarsimp simp: virq_type_def)
  done

lemma virq_get_tag_eq_of_nat_virq_type:
  "virq_get_tag virq = of_nat (virq_type (virq_to_H virq))"
  (* config unfolding to match bitfield shift in virq_get_tag with virq_type_shift in virq_type *)
  by (simp add: virq_to_H_def virq_type_def virq_get_tag_def virq_type_shift_def mask_def
                Kernel_Config.config_ARM_GIC_V3_def)

lemma decodeVCPUInjectIRQ_ccorres:
  notes if_cong[cong] Collect_const[simp del]
  (* csymbr will use this instead now *)
  notes virq_virq_pending_new_spec = virq_virq_pending_EN_new_spec
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and sysargs_rel args buffer
              and (valid_cap' (ArchObjectCap cp))
              and K (isVCPUCap cp))
       (UNIV \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             ) hs
       (decodeVCPUInjectIRQ args cp
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeVCPUInjectIRQ_'proc)"
  apply (rule ccorres_grab_asm)
  apply (cinit' lift: length___unsigned_long_' cap_' buffer_'
                simp: decodeVCPUInjectIRQ_def Let_def shiftL_nat )
   apply csymbr
   apply csymbr
   apply clarsimp
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_gen_asm[where P="\<not> 0 < length args"])
    apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule_tac ccorres_gen_asm[where P="0 < length args"])
   apply (prop_tac "args \<noteq> []")
    apply fastforce
   apply clarsimp
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply csymbr
     apply csymbr
     apply csymbr
     apply csymbr
     apply clarsimp
     apply (rule ccorres_Cond_rhs_Seq)
      apply ccorres_rewrite
      apply (simp add: rangeCheck_def not_le[symmetric])
      apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
                 cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply clarsimp
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: rangeCheck_def not_le[symmetric])
      apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
                 cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply clarsimp
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: rangeCheck_def not_le[symmetric])
      apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
                 cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)

     apply (simp add: returnOk_bind bindE_assoc
                      performARMMMUInvocations performARMVCPUInvocation_def)
     apply (clarsimp simp: rangeCheck_def not_le[symmetric]
                           liftE_liftM[symmetric] liftE_bindE_assoc)

     (* symbolically execute the gets on LHS *)
     apply (rule_tac ccorres_pre_gets_armKSGICVCPUNumListRegs_ksArchState,
            rename_tac nregs)

     apply (rule_tac P="nregs < max_armKSGICVCPUNumListRegs" in ccorres_gen_asm)
     apply (rule_tac P="nregs < max_armKSGICVCPUNumListRegs" in ccorres_cross_over_guard_no_st)

     (* unfortunately directly looking at \<acute>gic_vcpu_num_list_regs means we need to abstract the
        IF condition, and because of 32/64-bit casting we need to know < max_armKSGICVCPUNumListRegs *)
     apply (rule_tac Q="\<lambda>s. valid_arch_state' s \<and> nregs = armKSGICVCPUNumListRegs (ksArchState s)"
                 and Q'=UNIV
                 and C'="{s. of_nat nregs \<le> (args ! 0 >> 32) && 0xFF}"
               in ccorres_rewrite_cond_sr_Seq)
      apply (clarsimp simp: not_le[symmetric] word_le_nat_alt unat_of_nat_eq)
      apply (simp add: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                       valid_arch_state'_def
                       unat_of_nat64' unat_of_nat32')

     apply (rule ccorres_Cond_rhs_Seq)
      apply (prop_tac "(of_nat nregs \<le> (args ! 0 >> 32) && 0xFF)")
       apply (simp add: word_le_nat_alt not_le)

      apply (simp add: rangeCheck_def not_le[symmetric])
      apply (simp add: throwError_bind invocationCatch_def
                 cong: StateSpace.state.fold_congs globals.fold_congs)

    (* can't use syscall_error_throwError_ccorres_n, since one of the globals updates reads a global
       var itself: gic_vcpu_num_list_regs_', need to split off up to the first return_C else
       vcg barfs *)
      apply (rule ccorres_split_throws)
       apply (rule_tac P="\<lambda>s. valid_arch_state' s \<and> nregs = armKSGICVCPUNumListRegs (ksArchState s)"
                   and P'="UNIV" in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre)
        apply (vcg exspec=invokeVCPUInjectIRQ_modifies)
       apply (clarsimp split: prod.splits
                        simp: throwError_def return_def EXCEPTION_SYSCALL_ERROR_def
                              EXCEPTION_NONE_def syscall_error_rel_def syscall_error_to_H_def
                              syscall_error_type_defs)
       apply (simp add: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)
      apply (simp add: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                       valid_arch_state'_def not_le
                       unat_of_nat64' unat_of_nat32')
      apply vcg

     apply (prop_tac "\<not> (of_nat nregs \<le> (args ! 0 >> 32) && 0xFF)")
      apply (simp add: word_le_nat_alt not_le)
     apply clarsimp
     apply (rule ccorres_move_const_guard)
     apply (rule ccorres_move_c_guard_vcpu)
     apply (simp add: liftM_def)
     apply (clarsimp simp: rangeCheck_def not_le[symmetric]
                           liftE_liftM[symmetric] liftE_bindE_assoc)

     apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
     apply csymbr
     apply (rule ccorres_abstract_cleanup)

     apply (rule_tac P="ret__unsigned_longlong =
                          of_nat (virq_type (vgicLR (vcpuVGIC vcpu)
                                            (unat ((args ! 0 >> 32) && 0xFF))))"
                     in ccorres_gen_asm2)
     apply clarsimp
     apply (rule ccorres_Cond_rhs_Seq)
      apply (prop_tac "isVIRQActive (vgicLR (vcpuVGIC vcpu) (unat ((args ! 0 >> 32) && 0xFF)))")
       apply (clarsimp simp add: virq_virq_active_eq_is_virq_active)
      apply (simp add: rangeCheck_def not_le[symmetric])
      apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
                 cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)

     apply (prop_tac "\<not>is_virq_active (vgicLR (vcpuVGIC vcpu) (unat ((args ! 0 >> 32) && 0xFF)))")
      apply (clarsimp simp add: virq_virq_active_eq_is_virq_active)
     apply clarsimp
     apply (simp add: returnOk_bind bindE_assoc not_le
                      performARMMMUInvocations performARMVCPUInvocation_def)
     apply csymbr
     apply (subst liftE_invokeVCPUInjectIRQ_empty_return)
     apply clarsimp

     \<comment> \<open>we want the second alternative - nothing to return to user\<close>
     apply (ctac add: setThreadState_ccorres)
       apply (ctac add: invokeVCPUInjectIRQ_ccorres)
          apply (rule ccorres_alternative2)
          apply (rule ccorres_return_CE, simp+)[1]
         apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
        apply wp
       apply clarsimp
       apply (vcg exspec=invokeVCPUInjectIRQ_modifies)
      apply (wpsimp wp: sts_invs_minor' ct_in_state'_set)+
     apply (vcg exspec=setThreadState_modifies)
    (* wp does wrong thing, have to clarsimp to use return_wp instead of getting asm schematic*)
    apply clarsimp
    apply (rule return_wp)
   apply clarsimp
   apply (vcg exspec=getSyscallArg_modifies)

  apply (clarsimp simp: word_less_nat_alt word_le_nat_alt conj_commute
                        invs_no_0_obj' tcb_at_invs' invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        valid_tcb_state'_def ThreadState_defs mask_def)

  apply (frule invs_arch_state')
  apply (clarsimp simp: valid_arch_state'_def max_armKSGICVCPUNumListRegs_val
                        rf_sr_armKSGICVCPUNumListRegs isCap_simps cap_get_tag_isCap capVCPUPtr_eq
                        sysargs_rel_to_n word_le_nat_alt linorder_not_less valid_cap'_def not_le)

  apply (prop_tac "armKSGICVCPUNumListRegs (ksArchState s) < 2 ^ LENGTH(machine_word_len)")
   apply (erule order_less_trans; simp)

  apply (safe; clarsimp?)
       apply (simp add: unat_eq_zero)
      apply (erule order_less_le_trans)
      apply (simp add: unat_of_nat_eq)
     apply (fastforce simp: sysargs_rel_to_n ct_in_state'_def st_tcb_at'_def comp_def
                      elim: obj_at'_weakenE)
    apply (fastforce simp: sysargs_rel_to_n ct_in_state'_def st_tcb_at'_def comp_def
                      elim: obj_at'_weakenE)
  apply (simp add: unat_of_nat_eq)
  apply (clarsimp simp: typ_heap_simps' cvcpu_relation_def cvgic_relation_def)
  apply (subgoal_tac "unat ((args ! 0 >> 32) && 0xFF) < max_armKSGICVCPUNumListRegs")
   apply (simp add: virq_get_tag_eq_of_nat_virq_type)
  apply (fastforce simp: unat_of_nat_eq max_armKSGICVCPUNumListRegs_val)
  done

lemma decodeVCPUReadReg_ccorres:
  notes if_cong[cong] Collect_const[simp del]
  shows
  "\<lbrakk> isVCPUCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and sysargs_rel args buffer
              and (valid_cap' (ArchObjectCap cp)))
       (UNIV \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> \<lbrace>\<acute>call = from_bool isCall \<rbrace>) hs
       (decodeVCPUReadReg args cp
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeVCPUReadReg_'proc)"
  apply (cinit' lift: length___unsigned_long_' cap_' buffer_' call_')
   apply (clarsimp simp: decodeVCPUReadReg_def Let_def)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule_tac P="args \<noteq> []" in ccorres_gen_asm)
   apply clarsimp
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (clarsimp simp: fromEnum_maxBound_vcpureg_def seL4_VCPUReg_Num_def hd_conv_nth[symmetric])
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: word_le_nat_alt throwError_bind invocationCatch_def invocation_eq_use_types
                 cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (clarsimp simp: word_le_nat_alt)
     (* unpack invocationCatch and resolve non-determinism (copied from use of
        invokeTCB_ReadRegisters_ccorres after unsuccessful attempts at abstraction) *)
     apply (simp add: Collect_const returnOk_def uncurry_def)
     apply (simp (no_asm) add: ccorres_invocationCatch_Inr split_def
                               performInvocation_def liftE_bindE bind_assoc)
     apply (ctac add: setThreadState_ccorres)
       apply (rule ccorres_nondet_refinement)
        apply (rule is_nondet_refinement_bindE)
         apply (rule is_nondet_refinement_refl)
        apply (simp split: if_split)
        apply (rule conjI[rotated], rule impI, rule is_nondet_refinement_refl)
        apply (rule impI)
        apply (rule is_nondet_refinement_alternative1)
       apply csymbr
       (* drill down to invoke level *)
       apply (clarsimp simp: AARCH64_H.performInvocation_def performARMVCPUInvocation_def)
       apply (clarsimp simp: liftE_bindE)
       apply (rule ccorres_add_returnOk)
       apply (ctac (no_vcg) add: invokeVCPUReadReg_ccorres)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_return_C_errorE, simp+)[1]
       apply (wpsimp wp: sts_invs_minor' ct_in_state'_set)+
     apply (vcg exspec=setThreadState_modifies)
    apply wp
   apply (vcg exspec=getSyscallArg_modifies)

  apply (clarsimp simp: word_le_nat_alt conj_commute
                        invs_no_0_obj' tcb_at_invs' invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        valid_tcb_state'_def ThreadState_defs mask_def)

  apply (rule conjI; clarsimp) \<comment> \<open>no args\<close>
   subgoal by (clarsimp simp: isCap_simps cap_get_tag_isCap capVCPUPtr_eq)
               (subst from_to_enum; clarsimp simp: fromEnum_maxBound_vcpureg_def)
  \<comment> \<open>at least one arg\<close>
  apply (clarsimp simp: isCap_simps cap_get_tag_isCap capVCPUPtr_eq valid_cap'_def)
  apply (subgoal_tac "args \<noteq> []")
    prefer 2 apply (cases args; clarsimp, unat_arith?)
  apply (fastforce simp: sysargs_rel_to_n ct_in_state'_def st_tcb_at'_def comp_def
                    elim: obj_at'_weakenE)
  done

lemma invokeVCPUSetTCB_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and tcb_at' tptr and vcpu_at' vcpuptr)
       (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tptr \<rbrace>
             \<inter> \<lbrace>\<acute>vcpu = Ptr vcpuptr \<rbrace>) hs
       (liftE (associateVCPUTCB vcpuptr tptr))
       (Call invokeVCPUSetTCB_'proc)"
  apply (cinit' lift:  tcb_' vcpu_' simp: gets_bind_ign liftE_liftM)
   apply clarsimp
   apply (rule ccorres_add_return2)
   apply (ctac (no_vcg) add: associateVCPUTCB_ccorres)
    apply (clarsimp simp: return_def)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: return_def)
  by (wpsimp simp: invs_no_0_obj')+

lemma liftE_associateVCPUTCB_empty_return:
  "liftE (associateVCPUTCB vcpu val) >>=E (\<lambda>rv. m rv)
    = liftE (associateVCPUTCB vcpu val) >>=E (\<lambda>_. m [])"
  unfolding associateVCPUTCB_def
  by (clarsimp simp: liftE_bindE bind_assoc)

lemma decodeVCPUSetTCB_ccorres:
  notes if_cong[cong] Collect_const[simp del]
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (valid_cap' (ArchObjectCap cp))
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and K (isVCPUCap cp \<and> interpret_excaps extraCaps' = excaps_map extraCaps))
       (UNIV \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             ) hs
       (decodeVCPUSetTCB cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeVCPUSetTCB_'proc)"
  apply (rule ccorres_grab_asm)
  apply (cinit' lift: cap_' current_extra_caps_'
                simp: decodeVCPUSetTCB_def Let_def)
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq ; clarsimp)
    apply (rule ccorres_split_throws)
     apply (subgoal_tac "null extraCaps")
      prefer 2 subgoal by (clarsimp simp: interpret_excaps_test_null excaps_map_def null_def)
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply vcg
   apply (subgoal_tac "extraCaps \<noteq> []")
     prefer 2 subgoal by (clarsimp simp: idButNot_def interpret_excaps_test_null
                                          excaps_map_def neq_Nil_conv)
   apply (clarsimp simp: null_def bindE)
   (* lookup first slot in extracaps and its type *)
   apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
   apply (rule ccorres_move_c_guard_cte)
   apply ctac
     apply (rule ccorres_assert2)
     apply clarsimp
     apply csymbr
     apply (simp add: cap_case_TCBCap2 unlessE_def if_to_top_of_bind if_to_top_of_bindE
                      ccorres_seq_cond_raise)
     apply (rule ccorres_cond2'[where R=\<top>])
       apply (cases extraCaps ; clarsimp simp add: cap_get_tag_isCap cnode_cap_case_if)
      apply (simp add: throwError_bind invocationCatch_def)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply clarsimp
     apply (simp add: returnOk_bind bindE_assoc
                        performARMMMUInvocations performARMVCPUInvocation_def)
       \<comment> \<open>we want the second alternative - nothing to return to user\<close>
       apply (subst liftE_associateVCPUTCB_empty_return, clarsimp)
     apply (ctac add: setThreadState_ccorres)
       apply csymbr
       apply csymbr
       apply (ctac add: invokeVCPUSetTCB_ccorres)
          apply (rule ccorres_alternative2)
          apply (rule ccorres_return_CE, simp+)[1]
         apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
        apply wp
       apply (vcg exspec=invokeVCPUSetTCB_modifies)
      apply (wpsimp wp: sts_invs_minor' ct_in_state'_set)+
     apply (vcg exspec=setThreadState_modifies)
    apply (wpsimp | wp (once) hoare_drop_imps)+
   apply vcg

  apply (clarsimp simp: word_less_nat_alt word_le_nat_alt conj_commute
                        invs_no_0_obj' tcb_at_invs' invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        invs_pspace_aligned' invs_pspace_distinct'
                        valid_tcb_state'_def ThreadState_defs mask_def)
  apply (clarsimp simp: idButNot_def interpret_excaps_test_null
                        excaps_map_def neq_Nil_conv)
  apply (rule conjI; clarsimp)
   apply (drule interpret_excaps_eq)
   apply (clarsimp simp: excaps_in_mem_def slotcap_in_mem_def isCap_simps ctes_of_cte_at)
   apply (rule conjI)
    apply (fastforce simp: ct_in_state'_def st_tcb_at'_def comp_def elim: obj_at'_weakenE)
   apply (rule conjI)
    apply (fastforce simp: ct_in_state'_def st_tcb_at'_def comp_def
                     elim: obj_at'_weakenE dest!: interpret_excaps_eq)
   apply (frule ctes_of_valid'; simp add: invs_valid_objs' valid_cap'_def)
  apply (fastforce simp: isCap_simps valid_cap'_def valid_tcb_state'_def excaps_map_def
                          cap_get_tag_ThreadCap capVCPUPtr_eq isVCPUCap_def cap_get_tag_isCap
                  dest!: interpret_excaps_eq)[1]
done

lemma invokeVCPUAckVPPI_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and vcpu_at' vcpuptr)
       (UNIV \<inter> \<lbrace>\<acute>vcpu = Ptr vcpuptr \<rbrace>
             \<inter> \<lbrace> unat \<acute>vppi = fromEnum vppi \<rbrace>)
       hs
       (liftE (invokeVCPUAckVPPI vcpuptr vppi))
       (Call invokeVCPUAckVPPI_'proc)"
  apply (cinit' lift: vcpu_' vppi_' simp: liftE_liftM)
   apply (simp add: invokeVCPUAckVPPI_def)
   apply (rule ccorres_move_const_guards)
   apply (rule ccorres_move_c_guard_vcpu)
   apply (ctac (no_vcg) add: vcpuVPPIMasked_update_ccorres[
                               where v=False, simplified from_bool_vals])
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wpsimp+
  apply (case_tac vppi, simp add: fromEnum_def enum_vppievent_irq flip: word_unat.Rep_inject)
  done

lemma unat_of_nat_fromEnum_vppievent_irq[simp]:
  "unat (of_nat (fromEnum (vppi :: vppievent_irq)) :: machine_word) = fromEnum vppi"
  by (cases vppi, clarsimp simp: fromEnum_def enum_vppievent_irq)

lemma liftE_invokeVCPUAckVPPI_empty_return:
  "liftE (invokeVCPUAckVPPI vcpu val) >>=E (\<lambda>rv. m rv)
    = liftE (invokeVCPUAckVPPI vcpu val) >>=E (\<lambda>_. m [])"
  unfolding invokeVCPUAckVPPI_def
  by (clarsimp simp: liftE_bindE bind_assoc)

lemma decodeVCPUAckVPPI_ccorres:
  notes if_cong[cong] Collect_const[simp del]
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and sysargs_rel args buffer
              and (valid_cap' (ArchObjectCap cp))
              and K (isVCPUCap cp))
       (UNIV \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             ) hs
       (decodeVCPUAckVPPI args cp
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeVCPUAckVPPI_'proc)"
proof -

  have ucast_scast_invalid[simp]:
    "UCAST(32 signed \<rightarrow> 32) VPPIEventIRQ_invalid = SCAST(32 signed \<rightarrow> 32) VPPIEventIRQ_invalid"
    by (simp flip: word_unat.Rep_inject add: VPPIEventIRQ_invalid_def)

  have irqVPPIEventIndex_not_invalid:
    "\<And>vppi. irqVPPIEventIndex (UCAST(machine_word_len \<rightarrow> irq_len) (args ! 0)) = Some vppi
            \<Longrightarrow> of_nat (fromEnum vppi) \<noteq> SCAST(32 signed \<rightarrow> machine_word_len) VPPIEventIRQ_invalid"
    by (clarsimp simp: irqVPPIEventIndex_def VPPIEventIRQ_invalid_def IRQ_def
                       fromEnum_def enum_vppievent_irq
                 split: if_splits)

  show ?thesis
    apply (rule ccorres_grab_asm)
    apply (cinit' lift: length___unsigned_long_' cap_' buffer_')
     apply (clarsimp simp: decodeVCPUAckVPPI_def)
     apply (csymbr, rename_tac cp')
     apply csymbr
     apply (rule ccorres_Cond_rhs_Seq ; clarsimp)
      apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
                  cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (simp add: syscall_error_to_H_cases)
     apply (rule_tac ccorres_gen_asm[where P="args \<noteq> []"], simp add: Let_def)
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
       apply csymbr
       (* isolate checkIRQ for ctac by using injection_handler *)
       apply (fold checkIRQ_def[simplified])
       apply (simp add: invocationCatch_use_injection_handler)
       apply (simp add: split_def invocationCatch_use_injection_handler
                                      injection_handler_bindE bindE_assoc)
       apply (ctac add: ccorres_injection_handler_csum1[OF Arch_checkIRQ_ccorres]; clarsimp)
          apply ccorres_rewrite
          apply (prop_tac "toEnum (unat (args ! 0)) = UCAST(machine_word_len \<rightarrow> irq_len) (args ! 0)")
           apply (solves \<open>simp add: Kernel_C_maxIRQ maxIRQ_ucast_toEnum_eq_irq\<close>)
          apply csymbr
          apply clarsimp
          (* simplify outcome of irqVPPIEventIndex_'proc *)
          apply (rule_tac Q=\<top> and Q'=UNIV
                   and C'="{s. irqVPPIEventIndex (UCAST(machine_word_len \<rightarrow> irq_len) (args ! 0)) = None}"
                   in ccorres_rewrite_cond_sr_Seq)
           apply (prop_tac "\<not> msb VPPIEventIRQ_invalid")
            apply (solves \<open>simp add: VPPIEventIRQ_invalid_def\<close>)
           apply (solves \<open>clarsimp simp: irqVPPIEventIndex_not_invalid split: option.splits,
                          simp add: scast_eq_ucast\<close>)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (clarsimp simp: irqVPPIEventIndex_not_invalid; ccorres_rewrite)
           apply (simp add: throwError_bind invocationCatch_def whenE_def injection_handler_throwError)
           apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
                      cong: StateSpace.state.fold_congs globals.fold_congs)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (solves \<open>simp add: syscall_error_to_H_cases\<close>)

          apply (clarsimp simp: irqVPPIEventIndex_not_invalid; ccorres_rewrite)
          apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr bindE_assoc)
          apply (ctac add: setThreadState_ccorres)
            apply (simp add: injection_handler_returnOk ccorres_invocationCatch_Inr
                             performInvocation_def AARCH64_H.performInvocation_def
                             performARMVCPUInvocation_def bindE_assoc)
            \<comment> \<open>we want the second alternative - nothing to return to user\<close>
            apply (subst liftE_invokeVCPUAckVPPI_empty_return, clarsimp)
            apply (ctac add: invokeVCPUAckVPPI_ccorres)
               apply (rule ccorres_alternative2)
               apply (rule ccorres_return_CE, simp+)[1]
              apply (rule ccorres_return_C_errorE; solves simp)
             apply wpsimp+
            apply (vcg exspec=invokeVCPUAckVPPI_modifies)
           apply (wpsimp wp: sts_invs_minor' ct_in_state'_set)
          apply clarsimp
          apply (vcg exspec=setThreadState_modifies)
         apply (ccorres_rewrite)
         apply (rule ccorres_return_C_errorE, simp+)[1]
        apply (wpsimp wp: injection_wp_E[OF refl] checkIRQ_ret_good)
       apply clarsimp
       apply (vcg exspec=Arch_checkIRQ_modifies)
      apply wpsimp
     apply (vcg exspec=getSyscallArg_modifies)

    apply (clarsimp simp: cap_get_tag_isCap)
    apply (cases args; clarsimp simp: unat_eq_0)
    apply (rule conjI)
     (* Haskell side *)
     apply (clarsimp simp: excaps_in_mem_def slotcap_in_mem_def isCap_simps ctes_of_cte_at)
     apply (clarsimp simp: word_le_nat_alt conj_commute
                           invs_no_0_obj' tcb_at_invs' invs_valid_objs' invs_sch_act_wf'
                           rf_sr_ksCurThread msgRegisters_unfold
                           valid_tcb_state'_def mask_def invs_pspace_aligned' invs_pspace_distinct'
                           valid_cap'_def ct_in_state'_def sysargs_rel_to_n st_tcb_at'_def comp_def
                           runnable'_eq)
     apply (fastforce elim: obj_at'_weakenE)
    (* C side *)
    apply (clarsimp simp: word_le_nat_alt rf_sr_ksCurThread msgRegisters_unfold
                          Kernel_C_maxIRQ and_mask_eq_iff_le_mask capVCPUPtr_eq)
    apply (rule conjI; clarsimp)
    using maxIRQ_less_2p_irq_len
    apply (simp add: mask_def)
    done
qed

lemma decodeARMVCPUInvocation_ccorres:
  notes if_cong[cong] Collect_const[simp del]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps ; isVCPUCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs'
              and (valid_cap' (ArchObjectCap cp)))
       (UNIV
             \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> \<lbrace>\<acute>call = from_bool isCall \<rbrace>) []
       (decodeARMVCPUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeARMVCPUInvocation_'proc)"
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' slot_' current_extra_caps_'
                       cap_' buffer_' call_')
   apply (clarsimp simp: decodeARMVCPUInvocation_def)

   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocation_eq_use_types)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeVCPUSetTCB_ccorres]; simp)

   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocation_eq_use_types)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeVCPUReadReg_ccorres]; simp)

   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocation_eq_use_types)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeVCPUWriteReg_ccorres]; simp)

   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocation_eq_use_types)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeVCPUInjectIRQ_ccorres]; simp)

   apply (rule ccorres_Cond_rhs)
    apply (simp add: invocation_eq_use_types)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeVCPUAckVPPI_ccorres]; simp)

   \<comment> \<open>unknown (arch) invocation labels all throw IllegalOperation in line with the Haskell\<close>
    apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (intro allI, rule conseqPre, vcg)
   subgoal
    apply (clarsimp simp: invocation_eq_use_types
                    split: invocation_label.splits arch_invocation_label.splits)
    apply (safe
           ; simp add: invocation_eq_use_types throwError_invocationCatch fst_throwError_returnOk
                       exception_defs syscall_error_rel_def syscall_error_to_H_cases)
    done
  \<comment> \<open>preconditions imply calculated preconditions\<close>
  apply auto
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
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (Arch.decodeInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call Arch_decodeInvocation_'proc)"
  (is "ccorres ?r ?xf ?P (?P' slot_') [] ?a ?c")
proof -
  note trim_call = ccorres_trim_returnE[rotated 2, OF ccorres_call]

  have not_VCPUCap_case_helper_eq:
    "\<And>P Q. \<not> isVCPUCap cp \<Longrightarrow> (case cp of arch_capability.VCPUCap x \<Rightarrow> P cp | _ \<Rightarrow> Q cp) = Q cp"
    by (clarsimp simp: isVCPUCap_def split: arch_capability.splits)

  from assms show ?thesis
    apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' slot_'
                        current_extra_caps_' cap_' buffer_' call_')
     apply csymbr
     apply (simp only: cap_get_tag_isCap_ArchObject AARCH64_H.decodeInvocation_def)
     apply (rule ccorres_Cond_rhs)
      apply wpc
           apply (clarsimp simp: isVCPUCap_def)+
      apply (rule ccorres_trim_returnE, simp+)
      apply (rule ccorres_call,
             rule decodeARMVCPUInvocation_ccorres, (simp add: isVCPUCap_def)+)[1]
     (* will not rewrite any other way, and we do not want to repeat proof for each MMU cap case
        of decodeARMMMUInvocation *)
     apply (subst not_VCPUCap_case_helper_eq, assumption)
     apply (rule ccorres_trim_returnE, simp+)
     apply (rule ccorres_call,
            rule decodeARMMMUInvocation_ccorres, simp+)[1]
    apply (clarsimp simp: cte_wp_at_ctes_of ct_in_state'_def)
    apply (drule_tac t="cteCap cte" in sym, simp)
    apply (frule(1) ctes_of_valid', simp)
    apply (clarsimp split: arch_capability.splits simp: isVCPUCap_def)
    done
qed

end

end
