(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_C
imports Recycle_C
begin

unbundle l4v_word_context

context begin interpretation Arch . (*FIXME: arch_split*)

crunches unmapPageTable
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (wp: crunch_wps simp: crunch_simps)

end

context kernel_m begin

lemma storePTE_def':
  "storePTE slot pte = setObject slot pte"
  unfolding storePTE_def
  by (simp add: tailM_def headM_def)

lemma objBits_InvalidPTE:
  "objBits RISCV64_H.InvalidPTE = word_size_bits"
  by (simp add: objBits_simps bit_simps)

lemma objBits_InvalidPTE_pte_bits:
  "objBits RISCV64_H.InvalidPTE = pte_bits"
  by (simp add: objBits_InvalidPTE bit_simps)

lemma canonical_user_less_pptrBase:
  "canonical_user < RISCV64.pptrBase"
  by (clarsimp simp: canonical_user_def RISCV64.pptrBase_def)
     (simp add: canonical_bit_def mask_2pm1)

lemma user_region_less_pptrBase:
  "p \<in> user_region \<Longrightarrow> p < RISCV64.pptrBase"
  by (simp add: user_region_def order_le_less_trans[OF _ canonical_user_less_pptrBase])

lemma performPageTableInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) \<circ> cteCap) ctSlot
              and (\<lambda>_. isPageTableCap cap))
       (\<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performPageTableInvocation (PageTableUnmap cap ctSlot)))
       (Call performPageTableInvocationUnmap_'proc)"
using [[goals_limit=20]]
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
          apply (simp add: storePTE_def' swp_def)
          apply clarsimp
          apply(simp only: bit_simps_corres[symmetric])
          apply (ctac add: clearMemory_setObject_PTE_ccorres[simplified objBits_InvalidPTE_pte_bits])
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
                           cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                           refill_buffer_relation_def typ_heap_simps
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
                        bit_simps capAligned_def mask_def page_table_at'_def
                        capRange_def Int_commute asid_bits_def
                        wellformed_mapdata'_def
             simp flip: canonical_bit_def
                 elim!: ccap_relationE cong: if_cong)
  apply (drule spec[where x=0])
  apply (auto simp add: word_and_le1 user_region_less_pptrBase)
  done

lemma ap_eq_D:
  "x \<lparr>array_C := arr'\<rparr> = asid_pool_C.asid_pool_C arr \<Longrightarrow> arr' = arr"
  by (cases x) simp

declare Kernel_C.asid_pool_C_size [simp del]

lemma createObjects_asidpool_ccorres:
  shows "ccorres dc xfdc
   ((\<lambda>s. \<exists>p. cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap isdev frame pageBits idx ) p s)
    and pspace_aligned' and pspace_distinct' and pspace_bounded' and valid_objs'
    and ret_zero frame (2 ^ pageBits)
    and valid_global_refs' and pspace_no_overlap' frame pageBits)
   ({s. region_actually_is_bytes frame (2^pageBits) s})
   hs
   (placeNewObject frame (makeObject::asidpool) 0)
   (CALL memzero(Ptr frame, (2 ^ pageBits));;
   (global_htd_update (\<lambda>_. ptr_retyp (ap_Ptr frame))))"
proof -
  have helper: "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> is_aligned frame pageBits \<and> frame \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma> \<and> pspace_bounded' \<sigma>
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
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>" and pbound: "pspace_bounded' \<sigma>"
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
    apply (clarsimp simp: array_relation_def option_to_ptr_def)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps asid_pool_C_tag_def
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
    apply (subst index_fold_update; auto simp: replicate_numeral update_ti_t_ptr_0s)
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
  have mko: "\<And>dev us d. makeObjectKO dev us d (Inl (KOArch (KOASIDPool f))) = Some ko"
    by (simp add: ko_def makeObjectKO_def)


  note rl = projectKO_opt_retyp_other [OF rc pal pno' ko_def]

  note cterl = retype_ctes_helper
                 [OF pal pdst pbound pno' al' le_refl
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
                     refill_buffer_relation_def Let_def)
    apply (simp add: rl' cterl tag_disj_via_td_name h_t_valid_clift_Some_iff tcb_C_size)
    apply (clarsimp simp: hrs_htd_update ptr_retyps_htd_safe_neg szo szko
                          kernel_data_refs_domain_eq_rotate
                          cvariable_array_ptr_retyps[OF szo]
                          foldr_upd_app_if [folded data_map_insert_def]
                          zero_ranges_ptr_retyps
                          rl empty)
    apply blast
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

lemma canonical_pspace_strg:
  "valid_pspace' s \<longrightarrow> pspace_canonical' s"
  by (simp add: valid_pspace'_def)

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
                             simp del: fun_upd_apply Collect_const)
             apply (prop_tac "base >> asid_low_bits < 0x80")
              apply (drule_tac n=asid_low_bits in le_shiftr)
              apply (fastforce simp: asid_low_bits_def asid_bits_def mask_def dest: plus_one_helper2)
             apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                   cmachine_state_relation_def
                             simp del: fun_upd_apply)
             apply (clarsimp simp: carch_state_relation_def carch_globals_def riscvKSGlobalPT_def
                             simp del: fun_upd_apply)
             apply (simp add: asid_high_bits_of_def fun_upd_def[symmetric]
                         del: fun_upd_apply)
             apply (simp add: ucast_x3_shiftr_asid_low_bits)
             apply (erule array_relation_update, rule refl)
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
                   updateFreeIndex_cte_wp_at)
         apply (strengthen exI[where x=parent])
         apply (wp updateFreeIndex_cte_wp_at)
        apply clarsimp
        apply vcg
       apply wp
      apply clarsimp
      apply (wp getSlotCap_wp)
     apply clarsimp
    apply (rule_tac Q="\<lambda>_. cte_wp_at' ((=) (UntypedCap isdev frame pageBits idx) o cteCap) parent
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
       apply fastforce
      apply (rule descendants_range_caps_no_overlapI'[where d=isdev and cref = parent])
        apply simp
       apply (fastforce simp: cte_wp_at_ctes_of is_aligned_neg_mask_eq)
      apply (clarsimp simp: is_aligned_neg_mask_eq simp flip: add_mask_fold)
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
                        descendants_range'_def2 empty_descendants_range_in'
                        kernel_mappings_canonical)
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
  apply (clarsimp simp: RISCV_4K_Page_def word_sle_def is_aligned_mask[symmetric]
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
       apply (simp add:is_aligned_def)
      apply (erule is_aligned_no_wrap',simp)
     apply (simp add: hrs_htd_def)
    apply (clarsimp simp: framesize_to_H_def pageBits_def framesize_defs)
   apply (drule region_actually_is_bytes_dom_s[OF _ order_refl])
   apply (simp add: hrs_htd_def split_def)
  apply (clarsimp simp: ccap_relation_def)
  apply (clarsimp simp: cap_asid_pool_cap_lift)
  apply (clarsimp simp: cap_to_H_def)
  apply (clarsimp simp: asid_bits_def)
  apply (drule word_le_mask_eq, simp)
  apply (simp add: asid_bits_def sign_extend_canonical_address kernel_mappings_canonical)
  done

lemmas performRISCV64MMUInvocations
    = ccorres_invocationCatch_Inr performInvocation_def
      RISCV64_H.performInvocation_def performRISCVMMUInvocation_def
      liftE_bind_return_bindE_returnOk

lemma slotcap_in_mem_PageTable:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); (s, s') \<in> rf_sr \<rbrakk>
       \<Longrightarrow> \<exists>v. cslift s' (cte_Ptr slot) = Some v
           \<and> (cap_get_tag (cte_C.cap_C v) = scast cap_page_table_cap)
              = (isArchObjectCap cap \<and> isPageTableCap (capCap cap))
           \<and> ccap_relation cap (cte_C.cap_C v)"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
  apply (clarsimp dest!: ccte_relation_ccap_relation)
  apply (simp add: cap_get_tag_isCap_ArchObject2)
  done

declare if_split [split del]

lemma ccap_relation_PageTableCap_IsMapped:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap p m)) ccap \<rbrakk>
   \<Longrightarrow> (capPTIsMapped_CL (cap_page_table_cap_lift ccap) = 0) = (m = None)"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: cap_page_table_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  apply (simp add: to_bool_def)
  done

lemma ccap_relation_PageTableCap_BasePtr:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap p m)) ccap \<rbrakk>
   \<Longrightarrow> capPTBasePtr_CL (cap_page_table_cap_lift ccap) = p"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: cap_page_table_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  done

lemma ccap_relation_PageTableCap_MappedASID:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap p (Some (a,b)))) ccap \<rbrakk>
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
  by (simp add: liftE_def bindE_def bind_assoc)

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
  "(case cap of ArchObjectCap (PageTableCap pd mapdata)
                   \<Rightarrow> f pd mapdata | _ \<Rightarrow> g)
   = (if isArchObjectCap cap \<and> isPageTableCap (capCap cap)
      then f (capPTBasePtr (capCap cap)) (capPTMappedAddress (capCap cap))
      else g)"
  by (simp add: isCap_simps
         split: capability.split arch_capability.split)

lemma lookupPTSlotFromLevel_bitsLeft_less_64:
  "n \<le> maxPTLevel \<Longrightarrow> \<lbrace>\<lambda>_. True\<rbrace> lookupPTSlotFromLevel n p vptr \<lbrace>\<lambda>rv _. fst rv < 64\<rbrace>"
  apply (induct n arbitrary: p)
   apply (simp add: lookupPTSlotFromLevel.simps)
   apply (wpsimp simp: pageBits_def)
  apply (simp add: lookupPTSlotFromLevel.simps)
  apply wpsimp
      apply assumption
     apply (wpsimp wp: hoare_drop_imps)+
  apply (simp add: ptBitsLeft_def ptTranslationBits_def pageBits_def maxPTLevel_def)
  done

lemma lookupPTSlot_bitsLeft_less_64:
  "\<lbrace>\<top>\<rbrace> lookupPTSlot p vptr \<lbrace>\<lambda>rv _. fst rv < 64\<rbrace>"
  unfolding lookupPTSlot_def
  by (rule lookupPTSlotFromLevel_bitsLeft_less_64, simp)

(* FIXME move *)
lemma addrFromPPtr_in_user_region:
  "p \<in> kernel_mappings \<Longrightarrow> addrFromPPtr p \<in> user_region"
  supply if_cong[cong]
  apply (simp add: kernel_mappings_def addrFromPPtr_def pptrBaseOffset_def paddrBase_def
                   user_region_def pptr_base_def RISCV64.pptrBase_def canonical_user_def)
  apply (clarsimp simp: canonical_bit_def mask_def)
  apply (subst diff_minus_eq_add[symmetric])
  apply (cut_tac n=p in max_word_max)
  apply unat_arith
  apply simp
  done

lemma page_table_at'_kernel_mappings:
  "\<lbrakk>page_table_at' p s; pspace_in_kernel_mappings' s\<rbrakk> \<Longrightarrow> p \<in> kernel_mappings"
  apply (clarsimp simp: page_table_at'_def)
  apply (drule_tac x=0 in spec, clarsimp simp: bit_simps typ_at_to_obj_at_arches)
  apply (erule (1) obj_at_kernel_mappings')
  done

lemma decodeRISCVPageTableInvocation_ccorres:
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
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       hs
       (decodeRISCVMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall canDonate InvokeArchObject)
       (Call decodeRISCVPageTableInvocation_'proc)"
   (is "_ \<Longrightarrow> _ \<Longrightarrow> ccorres _ _ ?pre ?pre' _ _ _")
  supply Collect_const[simp del] if_cong[cong] option.case_cong[cong]
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_'
                simp: decodeRISCVMMUInvocation_def invocation_eq_use_types
                      decodeRISCVPageTableInvocation_def)
   apply (simp add: Let_def isCap_simps if_to_top_of_bind
               cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq)
    (* RISCVPageTableUnmap *)
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
        (* check if PT cap is mapped *)
        apply clarsimp
        apply csymbr
        apply (clarsimp simp: ccap_relation_PageTableCap_IsMapped)
        apply (simp add: option.case_eq_if)
        apply (simp add: unlessE_def if_to_top_of_bind if_to_top_of_bindE ccorres_seq_cond_raise)
        apply (rule ccorres_cond2'[where R=\<top>], solves clarsimp)
         prefer 2
         (* not mapped, perform unmap *)
         apply (simp add: returnOk_bind bindE_assoc performRISCV64MMUInvocations)
         apply (ctac add: setThreadState_ccorres)
           apply (ctac add: performPageTableInvocationUnmap_ccorres)
              apply (rule ccorres_alternative2)
              apply (rule ccorres_return_CE, simp+)[1]
             apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
            apply wpsimp
           apply (vcg exspec=performPageTableInvocationUnmap_modifies)
          apply (wpsimp wp: sts_invs_minor' simp: isCap_simps)
         apply simp
         apply (vcg exspec=setThreadState_modifies)
        apply (simp add: split_def)
        (* mapped, check it isn't a top-level PT *)
        apply (rule_tac P="v1 \<noteq> None" in ccorres_gen_asm)
        apply (rule ccorres_rhs_assoc)+
        apply clarsimp
        apply csymbr
        apply csymbr
        (* pull out maybeVSpaceForASID to bind at front *)
        apply (simp only: bind_bindE_liftE)
        apply (simp add: invocationCatch_use_injection_handler injection_handler_bindE
                         bindE_assoc injection_liftE)
        apply (simp add: liftE_bindE)
        apply (rule ccorres_split_nothrow)
            apply wpfix
            apply (rule ccorres_call[where xf'=find_ret_'])
               apply (rule maybeVSpaceForASID_findVSpaceForASID_ccorres; simp)
              apply simp+
           apply ceqv
          apply csymbr
          apply csymbr
          apply clarsimp
          (* check this isn't a top-level page table *)
          apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE ccorres_seq_cond_raise
                           injection_handler_If)
          apply (clarsimp simp: ccap_relation_PageTableCap_BasePtr)
          apply (rule ccorres_cond2[where R=\<top>], (fastforce split: option.splits))
           (* it is a top level page table, throw *)
           apply (clarsimp simp: injection_handler_throwError)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          (* not top level, perform unmap *)
          apply (simp add: injection_handler_returnOk)
          apply (simp add: performRISCV64MMUInvocations bindE_assoc)
          apply (ctac add: setThreadState_ccorres)
            apply (ctac add: performPageTableInvocationUnmap_ccorres)
               apply (rule ccorres_alternative2)
               apply (rule ccorres_return_CE, simp+)[1]
              apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
             apply wp
            apply simp
            apply (vcg exspec=performPageTableInvocationUnmap_modifies)
           apply (wp sts_invs_minor')
          apply simp
          apply (vcg exspec=setThreadState_modifies)
         apply clarsimp
         apply (wp hoare_drop_imps)
        apply clarsimp
        apply (vcg exspec=findVSpaceForASID_modifies)
       apply clarsimp
       apply (wp (once) hoare_drop_imp, wp isFinalCapability_inv)
      apply simp
      apply (vcg exspec=isFinalCapability_modifies)
     apply (wp getCTE_wp)
    apply (vcg exspec=performPageTableInvocationUnmap_modifies exspec=isFinalCapability_modifies
               exspec=findVSpaceForASID_modifies exspec=setThreadState_modifies)
   apply simp
   (* we're done with unmap case *)
   apply (rule ccorres_Cond_rhs_Seq)
    (* neither map nor unmap, throw *)
    apply (rule ccorres_equals_throwError)
     apply (simp split: invocation_label.split arch_invocation_label.split
                   add: throwError_bind invocationCatch_def)
     apply fastforce
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply simp

  (* RISCVPageTableMap *)
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
                    decodeRISCVPageTableInvocationMap_def)
   apply (prop_tac "tl args \<noteq> []")
    apply (cases args; simp)
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
   apply (simp add: cap_case_PageTableCap2 split_def)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_page_table_cap)
                                        = (isArchObjectCap rv \<and> isPageTableCap (capCap rv)))
                                      \<and> (ccap_relation rv rv')) (fst (extraCaps ! 0))"
              and xf'=lvl1ptCap_' in ccorres_split_nothrow)
         apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
         apply (drule(1) slotcap_in_mem_PageTable)
         apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
         apply (clarsimp simp: typ_heap_simps' mask_def)
        apply (rename_tac rv' t t')
        apply (simp add: word_sless_def word_sle_def)
        apply ceqv
     apply csymbr
     apply clarsimp
       apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
       apply (clarsimp simp: hd_conv_nth)
       (* is first extra cap a page table cap? *)
       apply (rule ccorres_if_lhs[rotated]; clarsimp)
        (* it not PT cap, clear up the C if condition calculation, then throw *)
        apply (rule ccorres_rhs_assoc2)
        apply (rule_tac val=1 and xf'=ret__int_' and R=\<top> and R'=UNIV in ccorres_symb_exec_r_known_rv_UNIV)
           apply vcg
           apply clarsimp
          apply ceqv
         apply clarsimp
         apply ccorres_rewrite
         apply (rule ccorres_equals_throwError)
          apply (simp split: invocation_label.split arch_invocation_label.split
                        add: throwError_bind invocationCatch_def)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (solves \<open>simp add: guard_is_UNIV_def\<close>)
       (* first extracap is a page table *)
       apply csymbr
       apply clarsimp
       apply ccorres_rewrite
       (* ensure the pt is mapped *)
       apply (rule ccorres_rhs_assoc)
       apply csymbr
       apply (simp add: option.case_eq_if)
       apply (simp add: if_to_top_of_bind if_to_top_of_bindE)
       apply csymbr
       apply clarsimp
       apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
          apply vcg
         apply (solves \<open>clarsimp simp: asidInvalid_def isCap_simps
                                       ccap_relation_PageTableCap_IsMapped\<close>)
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
     apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
        apply vcg
       apply (solves \<open>clarsimp simp: isCap_simps hd_conv_nth RISCV64.pptrUserTop_def'
                                     pptrUserTop_def' not_less length_le_helper\<close>)
        apply (fold not_None_def) (* avoid expanding capPTMappedAddress  *)
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
            apply (solves\<open>clarsimp simp: asidInvalid_def isCap_simps ccap_relation_PageTableCap_BasePtr\<close>)
           apply (rule syscall_error_throwError_ccorres_n)
           apply (simp add: syscall_error_to_H_cases)
          apply (clarsimp simp: bindE_assoc)
          apply (ctac pre: ccorres_liftE_Seq add: lookupPTSlot_ccorres)
            apply (simp add: liftE_bindE)
            apply (rule ccorres_pre_getObject_pte)
            apply (rename_tac pte)
            apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
            apply clarsimp
            (* ensure we have found a valid pte with more bits than pageBits left to look up *)
            apply wpfix
            apply (rule ccorres_rhs_assoc2)
            apply (rule_tac val="from_bool (unat (ptBitsLeft_C lu_ret___struct_lookupPTSlot_ret_C)
                                            = pageBits
                                            \<or> \<not> pte = RISCV64_H.InvalidPTE)"
                     and xf'=ret__int_' and R="ko_at' pte b" and R'=UNIV
                     in ccorres_symb_exec_r_known_rv)
               apply vcg
               apply clarsimp
               apply (simp add: from_bool_eq_if' pageBits_def)
               apply (erule cmap_relationE1[OF rf_sr_cpte_relation], erule ko_at_projectKO_opt)
               apply (clarsimp simp: typ_heap_simps from_bool_eq_if)
               apply (simp flip: word_unat.Rep_inject)
               apply (auto simp: cpte_relation_def Let_def pte_lift_def case_bool_If
                          split: pte.split_asm if_splits)[1]
              apply ceqv
             apply clarsimp
             apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                apply vcg
               apply (solves clarsimp)
              apply (rule syscall_error_throwError_ccorres_n)
              apply (simp add: syscall_error_to_H_cases)
             (* checks are done, move on to doing the mapping *)
             apply (clarsimp simp: injection_handler_returnOk)
             apply (simp add: performRISCV64MMUInvocations bindE_assoc)
             apply csymbr
             apply csymbr
             apply csymbr
             apply csymbr
             apply csymbr
             apply csymbr
             apply (rule_tac P="unat (ptBitsLeft_C lu_ret___struct_lookupPTSlot_ret_C) < 64"
                      in ccorres_gen_asm) (* bitsLeft should not exceed word bits *)
             apply ccorres_rewrite
             apply (clarsimp simp: ccap_relation_PageTableCap_BasePtr
                                   ccap_relation_PageTableCap_MappedASID)
             apply csymbr
             apply (ctac add: setThreadState_ccorres)
               apply (ctac add: performPageTableInvocationMap_ccorres)
                  apply (rule ccorres_alternative2)
                  apply (rule ccorres_return_CE, simp+)[1]
                 apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                apply wpsimp+
               apply (vcg exspec=performPageTableInvocationMap_modifies)
              apply wpsimp+
             apply (vcg exspec=setThreadState_modifies)
            apply (simp add: get_capPtr_CL_def)
            apply vcg
           apply (rename_tac lookup_pt_ret)
           apply clarsimp
           apply (wpsimp wp: lookupPTSlot_inv hoare_drop_imps lookupPTSlot_bitsLeft_less_64)
          apply clarsimp
          apply (vcg exspec=lookupPTSlot_modifies)
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
        apply (wp injection_wp[OF refl] findVSpaceForASID_inv hoare_drop_imps)
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
  subgoal for _ v1
    (* RISCVPageTableUnmap: Haskell preconditions *)
    apply (drule_tac s="capability.ArchObjectCap _" in sym)
    apply (clarsimp simp: ct_in_state'_def isCap_simps valid_tcb_state'_def)
    apply (case_tac v1; clarsimp) (* is PT mapped *)
     apply (auto simp: ct_in_state'_def isCap_simps valid_tcb_state'_def valid_cap'_def
                       wellformed_mapdata'_def sch_act_wf_def sch_act_simple_def
                elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')
    done
  apply (rule conjI)
  subgoal for \<dots> s _ _
    (* RISCVPageTableMap: Haskell preconditions *)
    apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt
                          linorder_not_less)
    apply (clarsimp | drule length_le_helper)+
    apply (prop_tac "s \<turnstile>' fst (extraCaps ! 0)")
     apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def
                           slotcap_in_mem_def dest!: ctes_of_valid')
    by (auto simp: ct_in_state'_def pred_tcb_at' mask_def valid_tcb_state'_def
                   valid_cap'_def wellformed_acap'_def wellformed_mapdata'_def
                   sch_act_wf_def sch_act_simple_def
             elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]

  apply (rule conjI)
  subgoal for _ v1
    (* RISCVPageTableUnmap: C preconditions *)
    apply (drule_tac t="cteCap _" in sym)
    apply (clarsimp simp: rf_sr_ksCurThread ThreadState_defs mask_eq_iff_w2p word_size
                          ct_in_state'_def st_tcb_at'_def word_sle_def word_sless_def
                          typ_heap_simps' bit_simps)
    apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
    apply clarsimp
    apply (case_tac v1; clarsimp)
    apply (drule_tac s="capability.ArchObjectCap _" in sym)
    apply (solves \<open>clarsimp simp: ccap_relation_PageTableCap_MappedASID\<close>)
    done

  subgoal for p
    (* RISCVPageTableMap: C preconditions *)
    apply (prop_tac "SCAST(32 signed \<rightarrow> 64) ThreadState_Restart && mask 4 =
             SCAST(32 signed \<rightarrow> 64) ThreadState_Restart")
     apply (solves \<open>clarsimp simp: ThreadState_defs mask_def\<close>)
    apply (clarsimp cong: imp_cong conj_cong)
    apply (clarsimp simp: neq_Nil_conv[where xs=extraCaps]
                          excaps_in_mem_def slotcap_in_mem_def
                   dest!: sym[where s="ArchObjectCap cp" for cp])
    apply (cut_tac p="snd (hd extraCaps)" in ctes_of_valid', simp, clarsimp)
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject isCap_simps
                          word_sle_def word_sless_def
                          word_less_nat_alt)
    apply (frule length_ineq_not_Nil)
    apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
    apply (clarsimp simp: asidInvalid_def valid_cap_simps' rf_sr_ksCurThread hd_conv_nth
                          cap_get_tag_isCap_unfolded_H_cap)
    apply (clarsimp simp: typ_heap_simps')
    apply (clarsimp simp: ccap_relation_PageTableCap_BasePtr ccap_relation_PageTableCap_IsMapped
                          ccap_relation_PageTableCap_MappedASID)
    apply (rule conjI)
     (* ccap relation between caps with new mapping info *) (* FIXME RAF CLEANUP *)
     apply (fold mask_2pm1)
     apply (subst ccap_relation_def)
     apply (clarsimp simp: map_option_Some_eq2 cap_page_table_cap_lift[THEN iffD1]
                           cap_to_H_simps)
     (* base pointer *)
     apply (clarsimp simp: ccap_relation_PageTableCap_BasePtr ccap_relation_PageTableCap_IsMapped)
     (* wellformed ASID *)
     apply (clarsimp simp: wellformed_mapdata'_def
                           asid_wf_eq_mask_eq[simplified asid_bits_def, simplified])
     (* masked args ! 0 idempotent under sign extension *)
     apply (clarsimp simp: not_le)
     apply (subst sign_extend_less_mask_idem[rotated], solves \<open>simp (no_asm) add: word_size\<close>)
      apply (rule word_and_le)
      apply (simp add: mask_def)
      apply (rule less_imp_le)
      apply (erule order.strict_trans, simp)
     apply (rule refl)
    (* pte relation *)
    apply (clarsimp simp: cpte_relation_def Let_def)
    (* this boils down to showing that the page table's address >> 12 can fit into C PPN field *)
    apply (prop_tac "canonical_address p")
     apply (erule canonical_address_page_table_at', fastforce)
    apply (prop_tac "p \<in> kernel_mappings")
     apply (erule page_table_at'_kernel_mappings, fastforce)
    apply (drule_tac p=p in addrFromPPtr_in_user_region)
    apply (prop_tac "addrFromPPtr p >> 12 \<le> mask 44")
     apply (clarsimp simp: user_region_def canonical_user_def canonical_bit_def)
     apply (erule leq_mask_shift[OF le_smaller_mask])
     apply simp
    apply (erule word_le_mask_eq)
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

definition
 "vm_attribs_relation attr attr' \<equiv>
       riscvExecuteNever_CL (vm_attributes_lift attr') = from_bool (riscvExecuteNever attr)"

lemma framesize_from_H_eqs:
  "(framesize_from_H vsz = scast Kernel_C.RISCV_4K_Page) = (vsz = RISCVSmallPage)"
  "(framesize_from_H vsz = scast Kernel_C.RISCV_Mega_Page) = (vsz = RISCVLargePage)"
  "(framesize_from_H vsz = scast Kernel_C.RISCV_Giga_Page) = (vsz = RISCVHugePage)"
  by (simp add: framesize_from_H_def vm_page_size_defs split: vmpage_size.split)+

lemma ccorres_pre_getObject_pte:
  "(\<And>rv. ccorresG rf_sr \<Gamma> r xf (P rv) (P' rv) hs (f rv) c) \<Longrightarrow>
   ccorresG rf_sr \<Gamma> r xf (\<lambda>s. \<forall>pte. ko_at' pte p s \<longrightarrow> P pte s)
            {s. \<forall>pte pte'. cslift s (pte_Ptr p) = Some pte' \<and> cpte_relation pte pte' \<longrightarrow> s \<in> P' pte} hs
     (getObject p >>= f) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule_tac P="ko_at' rv p" in ccorres_cross_over_guard)
      apply assumption
     apply (wpsimp wp: getObject_inv getPTE_wp empty_fail_getObject)+
  apply (erule cmap_relationE1[OF rf_sr_cpte_relation], erule ko_at_projectKO_opt)
  apply clarsimp
  done

lemma ptr_add_uint_of_nat [simp]:
  "a  +\<^sub>p uint (of_nat b :: machine_word) = a  +\<^sub>p (int b)"
  by (clarsimp simp: CTypesDefs.ptr_add_def)

declare int_unat[simp]

lemma obj_at_pte_aligned:
  "obj_at' (\<lambda>a::RISCV64_H.pte. True) ptr s ==> is_aligned ptr word_size_bits"
  apply (drule obj_at_ko_at')
  apply (clarsimp dest!:ko_at_is_aligned'
                  simp: objBits_simps archObjSize_def bit_simps
                  elim!: is_aligned_weaken)
  done

lemma addrFromPPtr_mask_6:
  "addrFromPPtr ptr && mask (6::nat) = ptr && mask (6::nat)"
  apply (simp add: addrFromPPtr_def RISCV64.pptrBase_def pptrBaseOffset_def canonical_bit_def
                   paddrBase_def)
  apply word_bitwise
  apply (simp add:mask_def)
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


lemma updatePTE_ccorres:
  "ccorres (\<lambda>_ rv'. rv' = scast EXCEPTION_NONE) ret__unsigned_long_'
     \<top>
     (\<lbrace> cpte_relation pte \<acute>pte \<rbrace>
      \<inter> \<lbrace> \<acute>base = pte_Ptr p \<rbrace>)
     hs
          (do y <- storePTE p pte;
              doMachineOp sfence
           od)
     (Call updatePTE_'proc)"
  apply (cinit' lift: pte_' base_')
   apply (rule ccorres_split_nothrow)
       apply (rule storePTE_Basic_ccorres'')
      apply ceqv
     apply (rule ccorres_add_return2)
     apply (ctac add: sfence_ccorres)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply wpsimp
     apply (vcg exspec=sfence_modifies)
    apply wpsimp
   apply vcg
  apply clarsimp
  done

lemma performPageInvocationMapPTE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
           and (\<lambda>_. (isArchFrameCap cap \<and> capFMappedAddress (capCap cap) \<noteq> None)))
       (UNIV \<inter> {s. cpte_relation (fst mapping) (pte_' s)}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. base_' s = pte_Ptr (snd mapping)}) []
       (liftE (performPageInvocation (PageMap cap slot mapping)))
       (Call performPageInvocationMapPTE_'proc)"
  supply pageBitsForSize_le_64 [simp]
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift:  pte_' cap_' ctSlot_' base_')
   apply clarsimp
   apply wpc (* split mapping *)
   apply ctac
     apply (subst bind_assoc[symmetric])
     apply (rule ccorres_split_nothrow)
         apply (rule ccorres_call[OF updatePTE_ccorres, where xf'=ret__unsigned_long_'], simp+)
        apply ceqv
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply wpsimp
     apply (clarsimp, vcg exspec=sfence_modifies exspec=updatePTE_modifies)
    apply wpsimp
   apply (clarsimp, vcg)
  apply clarsimp
  done

lemma performPageGetAddress_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      (invs' and (\<lambda>s. ksCurThread s = thread) and ct_in_state' ((=) Restart)
       and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s))
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
      apply (rule hoare_post_taut[of \<top>])
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
                apply (rule hoare_post_taut[of \<top>])
               apply (vcg exspec=setThreadState_modifies)
              apply wpsimp
             apply (vcg exspec=setRegister_modifies)
            apply wpsimp
           apply clarsimp
           apply (vcg)
          apply wpsimp
         apply (clarsimp simp: msgInfoRegister_def RISCV64.msgInfoRegister_def
                               Kernel_C.msgInfoRegister_def Kernel_C.a1_def)
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
  apply (clarsimp simp: invs_no_0_obj' invs_queues invs_valid_objs'
                        rf_sr_ksCurThread msgRegisters_unfold
                        seL4_MessageInfo_lift_def message_info_to_H_def mask_def)
  apply (cases isCall)
   apply (auto simp: RISCV64.badgeRegister_def RISCV64_H.badgeRegister_def Kernel_C.badgeRegister_def
                     Kernel_C.a0_def fromPAddr_def ThreadState_defs
                     pred_tcb_at'_def obj_at'_def ct_in_state'_def)
  done

lemma vmsz_aligned_addrFromPPtr':
  "vmsz_aligned (addrFromPPtr p) sz
       = vmsz_aligned p sz"
  apply (simp add: vmsz_aligned_def RISCV64.addrFromPPtr_def pptrBaseOffset_def paddrBase_def)
  apply (subgoal_tac "is_aligned RISCV64.pptrBase (pageBitsForSize sz)")
   apply (rule iffI)
    apply (drule(1) aligned_add_aligned)
      apply (simp add: pageBitsForSize_def word_bits_def split: vmpage_size.split)
     apply simp
   apply (erule(1) aligned_sub_aligned)
    apply (simp add: pageBitsForSize_def word_bits_def bit_simps split: vmpage_size.split)
  apply (simp add: pageBitsForSize_def RISCV64.pptrBase_def is_aligned_def bit_simps
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

lemma pde_case_isPageTablePDE:
  "(case pte of PageTablePTE _ _ \<Rightarrow> P | _ \<Rightarrow> Q)
       = (if isPageTablePTE pte then P else Q)"
  by (clarsimp simp: isPageTablePTE_def split: pte.splits)

lemma valid_cap'_FrameCap_kernel_mappings:
  "\<lbrakk>pspace_in_kernel_mappings' s; isFrameCap cap; valid_cap' (ArchObjectCap cap) s\<rbrakk>
     \<Longrightarrow> capFBasePtr cap \<in> kernel_mappings"
  apply (clarsimp simp: valid_cap'_def isCap_simps frame_at'_def)
  apply (drule_tac x=0 in spec)
  apply (prop_tac "(0::machine_word) < 2 ^ (pageBitsForSize v2 - pageBits)")
   apply (clarsimp simp: bit_simps pageBitsForSize_def split: vmpage_size.split)
  apply (case_tac v4; (fastforce simp: bit_simps typ_at_to_obj_at_arches obj_at_kernel_mappings'
                              split: if_splits)?)
  done

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
      \<and> capFVMRights_CL (cap_frame_cap_lift cap') < 4
      \<and> capFVMRights_CL (cap_frame_cap_lift cap') \<noteq> 0"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (frule cap_get_tag_PageCap_frame)
  apply (frule ccap_relation_c_valid_cap)
  apply (clarsimp simp: cap_frame_cap_lift c_valid_cap_def cl_valid_cap_def split: if_split_asm)
  done

lemma throwError_invocationCatch:
  "throwError a >>= invocationCatch b c d e f = throwError (Inl a)"
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

(* FIXME move *)
lemma and_1_0_not_bit_0:
  "(w && 1 = 0) = (\<not> (w::'a::len word) !! 0)"
  using to_bool_and_1[simplified to_bool_def, where x=w]
  by auto

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

lemma frame_at'_kernel_mappings:
  "\<lbrakk>frame_at' p sz d s; pspace_in_kernel_mappings' s\<rbrakk> \<Longrightarrow> p \<in> kernel_mappings"
  apply (clarsimp simp: frame_at'_def)
  apply (drule_tac x=0 in spec, clarsimp simp: bit_simps)
  apply (cases sz
         ; auto simp: bit_simps split: if_splits
                dest!: device_data_at_ko user_data_at_ko intro!: obj_at_kernel_mappings')
  done

lemma decodeRISCVFrameInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp] Collect_const[simp del]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps; isFrameCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs' and cur_tcb')
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (decodeRISCVMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall canDonate InvokeArchObject)
       (Call decodeRISCVFrameInvocation_'proc)"
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_' call_'
                simp: decodeRISCVMMUInvocation_def)
   apply (simp add: Let_def isCap_simps invocation_eq_use_types split_def decodeRISCVFrameInvocation_def
               del: Collect_const
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
     apply (simp add: returnOk_bind bindE_assoc performRISCV64MMUInvocations)
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
    apply (simp add: returnOk_bind bindE_assoc
                     performRISCV64MMUInvocations)
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
   supply Collect_const[simp del]
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
   apply csymbr
   apply (simp add: interpret_excaps_test_null excaps_map_def)
   (* throw if no excaps *)
   apply (clarsimp dest!: at_least_3_args)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind invocationCatch_def split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (clarsimp simp: list_case_If2 decodeRISCVFrameInvocationMap_def)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply (rule ccorres_add_return)
       apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
         apply csymbr
         apply (rule ccorres_add_return)
         apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_page_table_cap)
                                            = (isArchObjectCap rv \<and> isPageTableCap (capCap rv)))
                                          \<and> (ccap_relation rv rv')) (fst (extraCaps ! 0))"
                  and xf'=lvl1ptCap_' in ccorres_split_nothrow)
             apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
             apply (drule(1) slotcap_in_mem_PageTable)
             apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
             apply (clarsimp simp: typ_heap_simps' mask_def)
            apply (rename_tac rv' t t')
            apply (simp add: word_sless_def word_sle_def)
            apply ceqv
           apply (clarsimp simp add: split_def cap_case_PageTableCap2 hd_conv_nth option.case_eq_if)
           apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
           (* symb exec until ret__int init *)
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           (* is first extra cap a page table cap? *)
           apply (rule ccorres_if_lhs[rotated]; clarsimp)
            (* it not PT cap, clear up the C if condition calculation, then throw *)
            apply (rule ccorres_rhs_assoc2)
            apply (rule_tac val=1 and xf'=ret__int_' and R=\<top> and R'=UNIV in ccorres_symb_exec_r_known_rv_UNIV)
               apply vcg
               apply clarsimp
              apply ceqv
             apply clarsimp
             apply ccorres_rewrite
             apply (rule ccorres_equals_throwError)
              apply (simp split: invocation_label.split arch_invocation_label.split
                            add: throwError_bind invocationCatch_def)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            apply (solves \<open>simp add: guard_is_UNIV_def\<close>)
           (* first extracap is a page table cap *)
           apply csymbr
           apply clarsimp
           apply ccorres_rewrite
           (* ensure the pt is mapped *)
           apply (rule ccorres_rhs_assoc)
           apply csymbr
           apply (simp add: option.case_eq_if)
           apply csymbr
           apply clarsimp
           apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
              apply vcg
             apply (solves \<open>clarsimp simp: asidInvalid_def isCap_simps
                                       ccap_relation_PageTableCap_IsMapped\<close>)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           apply csymbr
           apply csymbr
           apply csymbr
           apply csymbr
           apply (fold not_None_def) (* avoid expanding capPTMappedAddress  *)
           apply (simp add: lookupError_injection invocationCatch_use_injection_handler
                            injection_bindE[OF refl refl] injection_handler_If bindE_assoc
                            injection_handler_throwError injection_liftE[OF refl])
           apply (ctac add: ccorres_injection_handler_csum1[OF ccorres_injection_handler_csum1,
                                                            OF findVSpaceForASID_ccorres])
              (* ensure level 1 pt pointer supplied by user is actually a vspace root *)
              apply (simp add: Collect_False if_to_top_of_bindE)
              apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                 apply vcg
                apply (solves\<open>clarsimp simp: asidInvalid_def isCap_simps ccap_relation_PageTableCap_BasePtr\<close>)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply (clarsimp simp: bindE_assoc)
              (* check vaddr is valid *)
              apply csymbr
              apply clarsimp
              apply ccorres_rewrite
              apply csymbr
              apply (clarsimp simp: ccap_relation_FrameCap_Size framesize_from_to_H)
              apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                 apply vcg
                apply (solves \<open>clarsimp simp: pptrUserTop_def' p_assoc_help\<close>)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              (* check vaddr alignment *)
              apply (clarsimp simp: checkVPAlignment_def unlessE_def injection_handler_If
                                    injection_handler_returnOk injection_handler_throwError)
              apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
              apply csymbr
              apply (clarsimp simp: framesize_from_to_H)
              apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
                 apply vcg
                apply (solves \<open>clarsimp simp: vmsz_aligned_def from_bool_0 is_aligned_mask\<close>)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)

              (* lookup pt slot *)
              apply (ctac pre: ccorres_liftE_Seq add: lookupPTSlot_ccorres)
                (* ensure remaining page bits match page bits for size *)
                apply csymbr

                apply clarsimp
                apply (rename_tac ptSlot ptSlot_ret)
                apply wpfix
                apply (rule_tac P="unat (ptBitsLeft_C ptSlot_ret) < 64" in ccorres_gen_asm)
                apply (rule ccorres_if_lhs[rotated])
                 (* throwing a lookup fault, branch condition on C side is true *)
                 apply (prop_tac "ptBitsLeft_C ptSlot_ret
                                  \<noteq> of_nat (pageBitsForSize (framesize_to_H (
                                      framesize_from_H pg_sz)))")
                  apply (clarsimp simp: of_nat_pageBitsForSize_eq[symmetric] framesize_from_to_H)
                 apply simp
                 apply ccorres_rewrite
                 (* throwing a lookup fault is more complicated for some reason, due to
                    lookup_fault_missing_capability_new_'proc *)
                 apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
                 apply (rule allI, rule conseqPre, vcg)
                 apply (clarsimp simp: throwError_def return_def bindE_def Nondet_Monad.lift_def
                                       exception_defs lookup_fault_lift_invalid_root)
                 apply (clarsimp simp: syscall_error_rel_def exception_defs syscall_error_to_H_def
                                       syscall_error_type_defs)
                 apply (simp add: lookup_fault_missing_capability_lift)
                 apply (subst word_le_mask_eq)
                  apply (simp add: mask_def word_le_nat_alt)
                 apply (rule refl)
                apply clarsimp
                apply (clarsimp simp: of_nat_pageBitsForSize_eq framesize_from_to_H)
                apply ccorres_rewrite
                apply csymbr
                apply csymbr
                (* split on whether frame is mapped; error checking happens on both branches
                   followed by performPageInvocationMapPTE; since there are only two branches and
                   they consist mostly of error checking, we will take on that duplication *)
                apply clarsimp
                apply (clarsimp simp: asidInvalid_def ccap_relation_FrameCap_IsMapped)
                apply (rule ccorres_if_lhs)

                 (* frame not mapped *)
                 apply clarsimp
                 apply ccorres_rewrite
                 apply (clarsimp simp: checkSlot_def injection_handler_bindE injection_liftE
                                       bindE_assoc unlessE_def injection_handler_If
                                       injection_handler_throwError injection_handler_returnOk)
                 apply (simp add: liftE_bindE)

                 (* fetch pte *)
                 apply (rule ccorres_pre_getObject_pte)
                 apply (rename_tac pte)
                 apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
                 apply (rule ccorres_rhs_assoc)
                 apply (rule_tac val="from_bool (pte \<noteq> RISCV64_H.InvalidPTE)"
                           and xf'=ret__unsigned_longlong_' and R="ko_at' pte ptSlot" and R'=UNIV
                           in ccorres_symb_exec_r_known_rv)
                    apply vcg
                    apply clarsimp
                    apply (erule cmap_relationE1[OF rf_sr_cpte_relation], erule ko_at_projectKO_opt)
                    apply (clarsimp simp: typ_heap_simps from_bool_eq_if from_bool_0)
                    apply (fastforce simp: cpte_relation_def Let_def pte_lift_def case_bool_If
                               split: pte.split_asm if_splits)
                   apply ceqv
                  apply clarsimp
                  (* throw if pte not invalid *)
                  apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
                     apply vcg
                    apply (solves clarsimp)
                   apply (rule syscall_error_throwError_ccorres_n)
                   apply (simp add: syscall_error_to_H_cases)

                  (* checks handled, perform frame map *)
                  apply (simp add: performRISCV64MMUInvocations bindE_assoc)
                  apply csymbr

                  (* FIXME RISCV extract return/maskVMRights_'proc ccorres, similar to isPTEPageTable_corres *)
                  apply (rule_tac xf'=vmRights___unsigned_long_'
                           and val="vmRightsToBits (maskVMRights rights (rightsFromWord b))"
                           and R=\<top> and R'=UNIV
                           in ccorres_symb_exec_r_known_rv) (* maskVMRights_'proc *)
                     apply vcg
                     apply clarsimp
                     apply (drule ccap_relation_FrameCap_generics)
                     apply clarsimp
                     apply (subst word_le_mask_eq)
                      apply (clarsimp simp: mask_def)
                      apply (solves unat_arith)
                     apply simp
                     apply clarsimp
                     apply (drule_tac s="vmrights_to_H _" in sym)
                     apply simp
                     apply (subst vmRightsToBits_vmrights_to_H)
                       apply (simp add: and_mask_eq_iff_le_mask)
                       apply (simp add: mask_def)
                       apply (solves unat_arith)
                      apply assumption
                     apply (rule refl)
                    apply ceqv

                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply clarsimp
                   apply csymbr
                   apply (ctac add: setThreadState_ccorres)
                     apply (ctac (no_vcg) add: performPageInvocationMapPTE_ccorres)
                       apply (rule ccorres_gen_asm)
                       apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                       apply (rule ccorres_alternative2)
                       apply (rule ccorres_return_CE, simp+)[1]
                      apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                     apply (wpsimp simp: performPageInvocation_def)
                    apply (wp sts_invs_minor')
                   apply clarsimp
                   apply (vcg exspec=setThreadState_modifies)
                  apply clarsimp
                  apply vcg
                 apply clarsimp
                 apply vcg

                (* frame is mapped, we're doing a remap *)
                apply (simp add: asidInvalid_def)
                apply clarsimp
                apply ccorres_rewrite
                (* ensure frame cap asid matches vspace asid *)
                apply (rule ccorres_rhs_assoc)+
                apply wpfix
                apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                   apply vcg
                  apply (clarsimp simp: isCap_simps not_None_def ccap_relation_FrameCap_MappedAddress
                                        ccap_relation_PageTableCap_MappedASID
                                        ccap_relation_FrameCap_MappedASID)
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (simp add: syscall_error_to_H_cases)
                (* ensure mapped address of frame matches *)
                apply csymbr
                apply csymbr
                apply (clarsimp simp: ccap_relation_FrameCap_MappedAddress)
                apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                   apply vcg
                  apply (solves clarsimp)
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (simp add: syscall_error_to_H_cases)

                (* ensure lookupPTSlot returned a slot with a PTE *)
                (* This check is redundant and should be removed; see VER-1288 *)
                apply (clarsimp simp: bindE_assoc checkSlot_def injection_handler_bindE
                                      injection_liftE unlessE_def injection_handler_If
                                      injection_handler_throwError injection_handler_returnOk)
                apply (simp add: liftE_bindE)
                apply (rule ccorres_pre_getObject_pte)
                apply (rename_tac ptSlot_ret_pte)
                apply (rule ccorres_add_return)
                apply (rule_tac xf'=ret__unsigned_long_' in ccorres_split_nothrow_call)
                       apply (rule_tac pte=ptSlot_ret_pte and ptePtr=ptSlot in isPTEPageTable_corres)
                      apply simp+
                   apply ceqv

                  apply clarsimp
                  apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)

                  apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
                     apply vcg
                    apply (solves clarsimp)
                   apply (rule syscall_error_throwError_ccorres_n)
                   apply (simp add: syscall_error_to_H_cases)

                  (* checks handled, perform frame remap *)
                  apply (simp add: performRISCV64MMUInvocations bindE_assoc)
                  apply csymbr

                  (* FIXME RISCV extract return/maskVMRights_'proc ccorres, similar to isPTEPageTable_corres *)
                  apply (rule_tac xf'=vmRights___unsigned_long_'
                           and val="vmRightsToBits (maskVMRights rights (rightsFromWord b))"
                           and R=\<top> and R'=UNIV
                           in ccorres_symb_exec_r_known_rv) (* maskVMRights_'proc *)
                     apply vcg
                     apply clarsimp
                     apply (drule ccap_relation_FrameCap_generics)
                     apply clarsimp
                     apply (subst word_le_mask_eq)
                      apply (clarsimp simp: mask_def)
                      apply (solves unat_arith)
                     apply simp
                     apply clarsimp
                     apply (drule_tac s="vmrights_to_H _" in sym)
                     apply simp
                     apply (subst vmRightsToBits_vmrights_to_H)
                       apply (simp add: and_mask_eq_iff_le_mask)
                       apply (simp add: mask_def)
                       apply (solves unat_arith)
                      apply assumption
                     apply (rule refl)
                    apply ceqv

                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply csymbr
                   apply clarsimp
                   apply csymbr
                   apply (ctac add: setThreadState_ccorres)
                     apply (ctac (no_vcg) add: performPageInvocationMapPTE_ccorres)
                       apply (rule ccorres_gen_asm)
                       apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                       apply (rule ccorres_alternative2)
                       apply (rule ccorres_return_CE, simp+)[1]
                      apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                     apply (wpsimp simp: performPageInvocation_def)
                    apply clarsimp
                    apply (wpsimp wp: sts_invs_minor')
                   apply clarsimp
                   apply (vcg exspec=setThreadState_modifies)
                  apply clarsimp
                  apply vcg
                 apply clarsimp
                 apply wpsimp
                apply clarsimp
                apply vcg
               (* wp goal for lookupPTSlot *)
               apply clarsimp
               apply (wpsimp wp: hoare_drop_imps lookupPTSlot_inv hoare_vcg_all_lift lookupPTSlot_bitsLeft_less_64)
              apply clarsimp
              apply (vcg exspec=lookupPTSlot_modifies)
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
            apply (wp injection_wp[OF refl] findVSpaceForASID_inv hoare_drop_imps)
           apply clarsimp
           apply (vcg exspec=findVSpaceForASID_modifies)
          apply clarsimp
          apply wp
         apply clarsimp
         apply vcg
        apply wpsimp
       apply clarsimp
       apply (vcg exspec=getSyscallArg_modifies)
      apply clarsimp
      apply wpsimp
     apply (vcg exspec=getSyscallArg_modifies)
    apply clarsimp
    apply wpsimp
    (* rewrite to args *)
    apply (rule_tac t="a # b # c # d" and s=args in subst, simp)
    apply (rule_tac t=a and s="hd args" in ssubst, simp)
    apply (rule_tac t=b and s="hd (tl args)" in ssubst, simp)
    apply (rule_tac t=c and s="hd (tl (tl args))" in ssubst, simp)
    apply (rule_tac t=d and s="tl (tl (tl args))" in ssubst, simp)
    apply assumption
   (* rewrite to args on for C side *)
   apply (rule conseqPre)
    apply (vcg exspec=getSyscallArg_modifies)
   apply (rule_tac t="a # b # c # d" and s=args in subst, simp)
   apply (rule_tac t=a and s="hd args" in ssubst, simp)
   apply (rule_tac t=b and s="hd (tl args)" in ssubst, simp)
   apply (rule_tac t=c and s="hd (tl (tl args))" in ssubst, simp)
   apply (rule_tac t=d and s="tl (tl (tl args))" in ssubst, simp)
   apply (rule subset_refl)

  apply (clarsimp)
  apply (frule cte_wp_at_eq_gsMaxObjectSize, fastforce)
  apply (clarsimp simp: ccap_relation_FrameCap_BasePtr ccap_relation_frame_tags)

  apply (prop_tac "SCAST(32 signed \<rightarrow> 64) ThreadState_Restart && mask 4
                   = SCAST(32 signed \<rightarrow> 64) ThreadState_Restart")
  apply (solves \<open>clarsimp simp: ThreadState_defs mask_def\<close>)

  apply (rule conjI)
   (* RISCVPageMap, Haskell side *)
   apply (clarsimp simp: not_None_def)
   apply (clarsimp simp: cte_wp_at_ctes_of is_aligned_mask[symmetric] vmsz_aligned_def
                         vmsz_aligned_addrFromPPtr)
   apply (frule ctes_of_valid', clarsimp+)
   apply (drule_tac t="cteCap cte" in sym, simp)
   apply (frule valid_cap'_FrameCap_kernel_mappings[OF invs_pspace_in_kernel_mappings', where cap=cp],
          fastforce simp: isCap_simps, fastforce)

   apply (clarsimp simp: isCap_simps sysargs_rel_to_n not_less)
   apply (rule conjI)
    apply (solves \<open>simp flip: Suc_length_not_empty[OF refl]\<close>)

   apply clarsimp
   apply (prop_tac "s \<turnstile>' fst (extraCaps ! 0)")
    apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def
                          slotcap_in_mem_def dest!: ctes_of_valid')
   apply clarsimp
   apply (rule conjI, fastforce)
   apply (clarsimp simp: valid_cap'_def wellformed_mapdata'_def)
   apply (rule conjI, fastforce simp: cur_tcb'_def)+
   apply (prop_tac "7 \<le> gsMaxObjectSize s")
   subgoal for _ _ v2
     by (cases v2; clarsimp simp: bit_simps')
  subgoal
    by (auto simp: ct_in_state'_def pred_tcb_at' mask_def valid_tcb_state'_def
                   valid_cap'_def wellformed_acap'_def wellformed_mapdata'_def
                   sch_act_wf_def sch_act_simple_def
             elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')

  (* RISCVPageUnMap, Haskell side *)
  apply (rule conjI)
  subgoal
    by (auto simp: isCap_simps comp_def ct_in_state'_def pred_tcb_at' mask_def valid_tcb_state'_def
                   valid_cap'_def wellformed_acap'_def wellformed_mapdata'_def
                   sch_act_wf_def sch_act_simple_def
             elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')

  (* C side of precondition satisfaction *)
  (* General idea for discharging this: we have some ccap relations between Haskell and C side,
     and the C side only ever used the C ones to perform the operations. Apart from a bit of
     extra noise, the gist of it is that after those operations, the new cap and new PTE should
     also be related. So we rewrite all the C accessors into the Haskell accessors,
     and then tackle the cap relation and pte relation at the end. *)
  subgoal for p rights sz d _ cap
    supply framesize_from_to_H[simp]
    apply (clarsimp simp: not_le rf_sr_ksCurThread isCap_simps)
    apply (prop_tac "SCAST(32 signed \<rightarrow> 64) ThreadState_Restart && mask 4 =
             SCAST(32 signed \<rightarrow> 64) ThreadState_Restart")
     apply (solves \<open>clarsimp\<close>)
    apply (rule conjI, solves \<open>simp add: word_less_nat_alt\<close>)  (* size args < 3 *)

    (* get a hold of our valid caps and resolve the C heap *)
    apply (clarsimp simp: neq_Nil_conv[where xs=extraCaps]
                          excaps_in_mem_def slotcap_in_mem_def
                   dest!: sym[where s="ArchObjectCap cp" for cp])
    apply (cut_tac p="snd (hd extraCaps)" in ctes_of_valid', simp, clarsimp)
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject isCap_simps
                          word_sle_def word_sless_def
                          word_less_nat_alt)
    apply (frule length_ineq_not_Nil)
    apply (frule cap_get_tag_isCap_unfolded_H_cap, simp)
    apply (clarsimp simp: asidInvalid_def valid_cap_simps' rf_sr_ksCurThread hd_conv_nth
                          cap_get_tag_isCap_unfolded_H_cap)
    apply (clarsimp simp: typ_heap_simps')
    (* clean up page table cap side *)
    apply (clarsimp simp: ccap_relation_PageTableCap_BasePtr ccap_relation_PageTableCap_IsMapped
                        ccap_relation_PageTableCap_MappedASID)
    (* clean up frame cap side *)
    apply (clarsimp simp: attribsFromWord_def ccap_relation_FrameCap_Size)
    apply (prop_tac "vmrights_to_H (capFVMRights_CL (cap_frame_cap_lift cap)) = rights")
     apply (drule ccap_relation_FrameCap_generics)
     apply (solves clarsimp)
    apply (clarsimp simp: and_1_0_not_bit_0)
    (* storing the page address again in the PPN bitfield does not lose info  *)
    apply (prop_tac "(addrFromPPtr p >> 12) AND mask 44 = (addrFromPPtr p >> 12)")
    subgoal
      apply (frule cte_wp_at'_frame_at', fastforce)
      apply (prop_tac "canonical_address p")
       apply (erule canonical_address_frame_at', fastforce)
      apply (prop_tac "p \<in> kernel_mappings")
       apply (erule frame_at'_kernel_mappings, fastforce)
      apply (drule_tac p=p in addrFromPPtr_in_user_region)
      apply (prop_tac "addrFromPPtr p >> 12 \<le> mask 44")
       apply (clarsimp simp: user_region_def canonical_user_def canonical_bit_def)
       apply (erule leq_mask_shift[OF le_smaller_mask])
       apply simp
      apply (erule word_le_mask_eq)
      done
    (* storing the ASID doesn't lose info *)
    apply (prop_tac "a AND mask 16 = a")
    subgoal by (clarsimp simp: wellformed_mapdata'_def asid_wf_def asid_bits_def word_le_mask_eq)
    apply simp

    (* clean up rights back-and-forth *)
    apply (cut_tac framesize_from_H_bounded[of sz, simplified word_less_nat_alt])
    apply (clarsimp simp: framesize_to_from_H)
    apply (prop_tac "unat (vmRightsToBits (maskVMRights rights (rightsFromWord (args ! Suc 0)))) < 4
                     \<and> vmRightsToBits (maskVMRights rights (rightsFromWord (args ! Suc 0))) \<noteq> 0")
    subgoal
      using vmRightsToBits_bounded
      by (simp add: vmRightsToBits_not_0 word_less_nat_alt)
    apply clarsimp

    (* idempotency of vaddr sign-extension *)
    apply (fold canonical_bit_def)
    apply (prop_tac "sign_extend canonical_bit (args ! 0) = args ! 0")
    subgoal
      apply (simp add: canonical_bit_def)
      apply (subst sign_extend_less_mask_idem[rotated], solves \<open>simp (no_asm) add: word_size\<close>)
       apply (simp (no_asm) add: mask_def)
       apply (simp only: vmsz_aligned_def)
       apply (drule (2) word_aligned_add_no_wrap_bounded)
       apply unat_arith
      apply (rule refl)
      done
    apply clarsimp

  (* now all we have left are cpte relations and ccap relations *)
  apply (intro conjI impI allI)
  (* runs for around 1 minute, can be improved by rules specific to the two relations rather
     than unfolding *)
             apply (match conclusion in \<open>cpte_relation _ _\<close> \<Rightarrow>
                      \<open>solves \<open>simp (no_asm) add: cpte_relation_def,
                               clarsimp simp: Let_def makeUserPTE_def attribsFromWord_def
                                              pageBits_def word_and_1
                                        split: pte.splits if_splits\<close>\<close>
                    | match conclusion in \<open>ccap_relation _ _\<close> \<Rightarrow>
                        \<open>solves \<open>simp (no_asm) add: ccap_relation_def,
                                 clarsimp simp: cap_frame_cap_lift[THEN iffD1]
                                                cap_to_H_simps wellformed_mapdata'_def,
                                 clarsimp simp flip: word_neq_0_conv
                                          dest!: ccap_relation_FrameCap_generics
                                          simp: c_valid_cap_def cap_frame_cap_lift[THEN iffD1],
                                 clarsimp simp: cl_valid_cap_def\<close>\<close>)+
    done
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
  apply (simp add: RISCV64_H.maskCapRights_def isFrameCap_def Let_def split: arch_capability.splits)
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

lemma injection_handler_stateAssert_relocate:
  "injection_handler Inl (stateAssert ass xs >>= f) >>=E g
    = do v \<leftarrow> stateAssert ass xs; injection_handler Inl (f ()) >>=E g od"
  by (simp add: injection_handler_def handleE'_def bind_bindE_assoc bind_assoc)

lemma decodeRISCVMMUInvocation_ccorres:
  notes Collect_const[simp del] if_cong[cong]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps \<rbrakk>
   \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs' and cur_tcb'
              and (\<lambda>s.  sch_act_wf (ksSchedulerAction s) s))
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (decodeRISCVMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall canDonate InvokeArchObject)
       (Call decodeRISCVMMUInvocation_'proc)"
  supply ccorres_prog_only_cong[cong]
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_' call_')
   apply csymbr
   apply (simp add: cap_get_tag_isCap_ArchObject
                    RISCV64_H.decodeInvocation_def
                    invocation_eq_use_types
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    (* PageTableCap *)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeRISCVPageTableInvocation_ccorres]; solves simp)
   apply (rule ccorres_Cond_rhs)
    (* FrameCap *)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call[OF decodeRISCVFrameInvocation_ccorres]; solves simp)
   (* ASIDControlCap *)
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule ccorres_equals_throwError)
      apply (fastforce simp: decodeRISCVMMUInvocation_def decodeRISCVASIDControlInvocation_def isCap_simps
                             throwError_bind invocationCatch_def
                      split: invocation_label.split arch_invocation_label.split)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    (* RISCV64ASIDControlMakePool *)
    apply (simp add: decodeRISCVMMUInvocation_def decodeRISCVASIDControlInvocation_def isCap_simps)
    apply (simp add: word_less_nat_alt list_case_If2 split_def tl_drop_1)
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
            apply (rule ccorres_pre_gets_riscvKSASIDTable_ksArchState)
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
                apply (rule_tac P="\<lambda>s. asid_table = riscvKSASIDTable (ksArchState s)"
                                in ccorres_from_vcg[where P'=UNIV])
                apply (clarsimp simp: return_def)
                apply (rule HoarePartial.SeqSwap)
                 apply (rule_tac I="{t. (\<sigma>, t) \<in> rf_sr \<and> i_' t \<le> 2 ^ asid_high_bits
                                        \<and> asid_table = riscvKSASIDTable (ksArchState \<sigma>)
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
                  apply (clarsimp simp: rf_sr_riscvKSASIDTable
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
                                      rf_sr_riscvKSASIDTable[where n=0, simplified])
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
                                            RISCV64_H.performInvocation_def
                                            performRISCVMMUInvocation_def)
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
    apply (simp add: imp_conjR[symmetric] decodeRISCVMMUInvocation_def)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_Cond_rhs_Seq)
     apply (clarsimp simp: isCap_simps decodeRISCVASIDPoolInvocation_def)
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
     apply (clarsimp simp: isCap_simps decodeRISCVASIDPoolInvocation_def
                           throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (fastforce simp: syscall_error_to_H_cases)
    apply (simp add: isCap_simps decodeRISCVASIDPoolInvocation_def split: list.split)
    apply (intro allI impI)
    apply csymbr
    apply (rule ccorres_add_return)
    apply (rule ccorres_Guard_Seq)
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_rhs_assoc2)
    apply (rule_tac R="excaps_in_mem extraCaps \<circ> ctes_of" and
                    R'="UNIV" and
                    val="from_bool (\<not> (isArchObjectCap (fst (extraCaps ! 0)) \<and>
                                       isPageTableCap (capCap (fst (extraCaps ! 0)))) \<or>
                                    capPTMappedAddress (capCap (fst (extraCaps ! 0))) \<noteq> None)" and
                    xf'=ret__int_' in ccorres_symb_exec_r_known_rv)
       apply vcg
       apply clarsimp
       apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
       apply (clarsimp simp: excaps_in_mem_def)
       apply (frule (1) slotcap_in_mem_PageTable)
       apply (clarsimp simp: typ_heap_simps' from_bool_0 split: if_split)
       apply (case_tac a; clarsimp simp: isCap_simps cap_get_tag_isCap_unfolded_H_cap cap_tag_defs)
       apply (intro conjI impI
              ; solves \<open>clarsimp simp: isCap_simps asidInvalid_def cap_lift_page_table_cap cap_to_H_simps
                                       c_valid_cap_def cl_valid_cap_def
                                       ccap_relation_PageTableCap_IsMapped\<close>)
      apply ceqv
     apply (rule ccorres_Cond_rhs_Seq)
      apply ccorres_rewrite
      apply (rule_tac v="Inl (InvalidCapability 1)" in ccorres_equals_throwError)
       apply (fastforce simp: isCap_simps throwError_bind invocationCatch_def
                        split: capability.split arch_capability.split)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (fastforce simp: syscall_error_to_H_cases)
     apply (simp add: isCap_simps, elim exE conjE)
     apply (simp add: isCap_simps Kernel_C_defs liftE_bindE bind_assoc)
     apply (rule ccorres_pre_gets_riscvKSASIDTable_ksArchState)
     apply csymbr
     apply (rule ccorres_Guard_Seq)+
     apply (rule ccorres_add_return)
     apply (rule_tac r'="\<lambda>_ rv'. rv' = option_to_ptr (asidTable (ucast (asid_high_bits_of (ucast (capASIDBase cp)))))
                                 \<and> asidTable (ucast (asid_high_bits_of (ucast (capASIDBase cp)))) \<noteq> Some 0"
                 and xf'=pool_' in ccorres_split_nothrow)
         apply (rule_tac P="\<lambda>s. asidTable = riscvKSASIDTable (ksArchState s)
                                \<and> valid_arch_state' s \<and> s \<turnstile>' ArchObjectCap cp"
                         in ccorres_from_vcg[where P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def valid_arch_state'_def valid_asid_table'_def)
         apply (frule cap_get_tag_isCap_ArchObject(2))
         apply (clarsimp simp: isCap_simps)
         apply (erule_tac v=cap in ccap_relationE)
         apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_simps valid_cap_simps'
                               cap_asid_pool_cap_lift_def)
         apply (subst rf_sr_riscvKSASIDTable, assumption)
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
           apply (rule_tac P="\<forall>x \<in> ran (inv ASIDPool x). x \<noteq> 0"
                           in ccorres_gen_asm2)
           apply (rule_tac P="ko_at' x (capASIDPool cp)"
                           in ccorres_from_vcg[where P'=UNIV])
           apply (clarsimp simp: option_to_0_def option_to_ptr_def
                                 return_def)
           apply (rule HoarePartial.SeqSwap)
            apply (rule_tac I="{t. (\<sigma>, t) \<in> rf_sr \<and> i_' t \<le> 2 ^ asid_low_bits
                                 \<and> ko_at' x (capASIDPool cp) \<sigma>
                                 \<and> (\<exists>v. cslift t (ap_Ptr (capASIDPool cp))
                                         = Some v \<and> (\<forall>x < i_' t. capASIDBase cp + x = 0
                                                        \<or> index (array_C v) (unat x) \<noteq> NULL)
                                        \<and> ret__int_' t = from_bool (i_' t < 2 ^ asid_low_bits
                                             \<and> (capASIDBase cp + (i_' t) = 0
                                                 \<or> index (array_C v) (unat (i_' t)) \<noteq> NULL)))}"
                         in HoarePartial.reannotateWhileNoGuard)
            apply (rule HoarePartial.While[OF order_refl])
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: asidLowBits_handy_convs
                                   word_sle_def word_sless_def from_bool_0)
             apply (rename_tac s' asid_pool)
             apply (subgoal_tac "capASIDBase_CL (cap_asid_pool_cap_lift cap)
                                     = capASIDBase cp")
              apply (subgoal_tac "\<And>x. (x < (i_' s' + 1))
                                        = (x < i_' s' \<or> x = i_' s')")
               apply (clarsimp simp: inc_le typ_heap_simps asid_low_bits_def not_less field_simps
                              split: if_split bool.splits)
               apply unat_arith
              apply (rule iffI)
               apply (rule disjCI)
               apply (drule plus_one_helper)
               apply simp
              apply (subgoal_tac "i_' s' < i_' s' + 1")
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
            apply (case_tac "i_' xa = 2 ^ asid_low_bits")
             apply (clarsimp split: list.split)
             apply (drule_tac f="\<lambda>xs. (a, ba) \<in> set xs" in arg_cong)
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
              apply fastforce
             apply (simp add: asid_low_bits_word_bits)
             apply (erule allEI, rule impI, erule(1) impE)
             apply (clarsimp simp: field_simps)
             apply (rename_tac x')
             apply (drule_tac x=x' in spec)
             apply (simp split: if_split_asm option.splits )
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
                          RISCV64_H.performInvocation_def liftE_bindE)
         apply csymbr
         apply (ctac add: setThreadState_ccorres)
           apply (simp add: performRISCVMMUInvocation_def bindE_assoc flip: liftE_liftE returnOk_liftE)
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
  apply clarsimp
  apply (rule conjI) (* PTCap *)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (drule_tac t="cteCap cte" in sym)
   apply (frule(1) ctes_of_valid', simp)
  apply (rule conjI) (* not PTCap *)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (drule_tac t="cteCap cte" in sym)
   apply (frule(1) ctes_of_valid', simp)
   apply (rule conjI, clarsimp, simp) (* FrameCap *)
   apply clarsimp
   apply (rule conjI, clarsimp simp: isCap_simps) (* ASIDControlCap *)
    apply (clarsimp simp: cte_wp_at_ctes_of ct_in_state'_def
                          interpret_excaps_eq excaps_map_def)
    apply (clarsimp simp: sysargs_rel_to_n word_less_nat_alt not_le)
    apply (rule conjI; clarsimp)
    apply (frule invs_arch_state')
    apply (rule conjI, clarsimp simp: valid_arch_state'_def valid_asid_table'_def)
    apply (clarsimp simp: neq_Nil_conv excaps_map_def valid_tcb_state'_def invs_queues
                          unat_lt2p[where 'a=machine_word_len, folded word_bits_def])
    apply (frule interpret_excaps_eq[rule_format, where n=1], simp)
    apply (rule conjI; clarsimp)+
    apply (rule conjI, erule ctes_of_valid', clarsimp)
    apply (intro conjI)
          apply fastforce
         apply (fastforce elim!: pred_tcb'_weakenE)
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
   (* RISCVASIDPoolAssign *)
   apply (clarsimp simp: isCap_simps valid_tcb_state'_def invs_queues)
   apply (frule invs_arch_state', clarsimp)
   apply (intro conjI)
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
    apply (simp add: objBits_simps valid_cap'_def)
   apply simp
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
   apply (clarsimp simp: unat_eq_of_nat objBits_simps pageBits_def case_bool_If
                  split: if_splits)
  apply (clarsimp simp: asid_low_bits_word_bits isCap_simps neq_Nil_conv
                        excaps_map_def excaps_in_mem_def
                        p2_gt_0[where 'a=machine_word_len, folded word_bits_def])
  apply (drule_tac t="cteCap cte" in sym, simp)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(15))
  apply (frule ctes_of_valid', clarsimp)
  apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
  apply (rule conjI)
   apply (clarsimp simp: cap_lift_asid_pool_cap cap_lift_page_table_cap
                         cap_to_H_def valid_cap'_def
                         cap_page_table_cap_lift_def inv_ASIDPool
                         cap_asid_pool_cap_lift_def mask_def
                         asid_shiftr_low_bits_less[unfolded mask_def asid_bits_def] word_and_le1
                  elim!: ccap_relationE split: if_split_asm asidpool.splits)
   apply (clarsimp split: list.split)
   apply (clarsimp simp: casid_pool_relation_def)
   apply (case_tac asidpool', simp)
  apply (clarsimp simp: cap_lift_asid_pool_cap cap_lift_page_table_cap
                        cap_to_H_def cap_page_table_cap_lift_def
                 elim!: ccap_relationE split: if_split_asm)
  apply (erule rf_sr_cte_at_validD[rotated])
  apply (fastforce simp: slotcap_in_mem_def2)
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
  apply (simp add: RISCV64.msgInfoRegister_def C_register_defs rf_sr_ksCurThread
                   RISCV64_H.msgInfoRegister_def)
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
   by (clarsimp simp: st_tcb_at'_def ct_in_state'_def obj_at'_def,
              case_tac "tcbState obj"; clarsimp)+

lemma Arch_decodeInvocation_ccorres:
  notes if_cong[cong]
  assumes "interpret_excaps extraCaps' = excaps_map extraCaps"
  shows
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs' and cur_tcb'
              and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s))
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> {s. call_' s = from_bool isCall}) []
       (Arch.decodeInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall canDonate InvokeArchObject)
       (Call Arch_decodeInvocation_'proc)"
proof -
  note trim_call = ccorres_trim_returnE[rotated 2, OF ccorres_call]
  from assms show ?thesis
    apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' slot_'
                        current_extra_caps_' cap_' buffer_' call_')
     apply (simp only: cap_get_tag_isCap_ArchObject RISCV64_H.decodeInvocation_def)
       apply (rule trim_call[OF decodeRISCVMMUInvocation_ccorres], simp+)[1]
    apply (clarsimp simp: o_def excaps_in_mem_def slotcap_in_mem_def)
    done
qed

end

end
