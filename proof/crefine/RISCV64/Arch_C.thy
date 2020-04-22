(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_C
imports Recycle_C
begin

context begin interpretation Arch . (*FIXME: arch_split*)

crunches unmapPageTable
  for ctes_of[wp]:  "\<lambda>s. P (ctes_of s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (wp: crunch_wps simp: crunch_simps)

end

context kernel_m begin

lemma storePTE_def':
  "storePTE slot pte = setObject slot pte"
  unfolding storePTE_def
  by (simp add: tailM_def headM_def)

lemma objBits_InvalidPTE:
  "objBits RISCV64_H.InvalidPTE = word_size_bits"
  by (simp add: objBits_simps archObjSize_def word_size_bits_def bit_simps)

(* FIXME RISCV: should this be the real objBits_InvalidPTE? *)
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
          apply(simp only: dc_def[symmetric] bit_simps_corres[symmetric])
          apply (ctac add: clearMemory_setObject_PTE_ccorres[simplified objBits_InvalidPTE_pte_bits])
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
  apply (auto simp add: word_and_le1 user_region_less_pptrBase)
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
    unfolding casid_pool_relation_def
    apply (clarsimp simp: makeObject_asidpool split: asid_pool_C.splits)
    apply (clarsimp simp: array_relation_def option_to_ptr_def)
    apply (rename_tac words i)
    sorry (* FIXME RISCV
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
                del: replicate_numeral Kernel_C.pte_C_size)
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
    apply (simp add: 
                     final_pad_def Let_def size_td_lt_ti_typ_pad_combine
                     padup_def align_td_array' size_td_array)
    apply (simp add: ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def
                     update_ti_adjust_ti size_td_array typ_info_array array_tag_def
                     update_ti_t_array_tag_n_rep update_ti_t_machine_word_0s)
    done
    *)

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
                  elim!: ptr_retyp_htd_safe_neg)
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
  sorry (* FIXME RISCV anyone's guess if lemma statement is still good
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
  apply (clarsimp simp: RISCV64SmallPageBits_def word_sle_def is_aligned_mask[symmetric]
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
  *)

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

(* FIXME RISCV REMOVE unclear what of this needs to be adapted
lemma isValidNativeRoot_spec:
  "\<forall>s.
    \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> True}
            Call isValidNativeRoot_'proc
         {t. \<forall>cap. ccap_relation cap (cap_' s) \<longrightarrow> ret__unsigned_long_' t = from_bool (isArchObjectCap cap \<and> isPML4Cap (capCap cap) \<and>
                                        capPML4MappedASID (capCap cap) \<noteq> None)}"
  apply (vcg, clarsimp)
  apply (rule conjI, clarsimp simp: from_bool_def case_bool_If if_1_0_0
                             split: if_split)
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
  apply (subst word_bool_alg.conj.assoc[symmetric])
  apply (subst is_aligned_neg_mask_eq)
   apply (rule aligned_already_mask)
   apply (erule is_aligned_addrFromPPtr)
  apply (clarsimp simp: addrFromPPtr_def RISCV64.pptrBase_def pptr_base_def bit_simps)
  apply (clarsimp simp: mask_def)
  apply (word_bitwise, clarsimp)
  done
*)

lemma ccap_relation_PageTableCap_IsMapped:
  "\<lbrakk> ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap p m)) ccap \<rbrakk>
   \<Longrightarrow> (capPTIsMapped_CL (cap_page_table_cap_lift ccap) = 0) = (m = None)"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: cap_page_table_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  apply (simp add: to_bool_def)
  done

(* FIXME RISCV: on other architectures, C uses invLabel_' instead of label___unsigned_long,
                and excaps_' instead of extraCaps___struct_extra_caps_C_' *)
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
             \<inter> {s. extraCaps___struct_extra_caps_C_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer})
       hs
       (decodeRISCVMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeRISCVPageTableInvocation_'proc)"
   (is "_ \<Longrightarrow> _ \<Longrightarrow> ccorres _ _ ?pre _ _ _ _")
  supply Collect_const[simp del] if_cong[cong]
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_'
                      extraCaps___struct_extra_caps_C_' cap_' buffer_'
                simp: decodeRISCVMMUInvocation_def invocation_eq_use_types
                      decodeRISCVPageTableInvocation_def)
   apply (simp add: Let_def isCap_simps if_to_top_of_bind
               cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs_Seq)
    (* unmap *)
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

        apply clarsimp
        apply csymbr
        apply clarsimp

        apply (rule_tac P="v1 = None" in ccorres_cases
               ; clarsimp simp: ccap_relation_PageTableCap_IsMapped
               ; ccorres_rewrite)
         (* not mapped, perform unmap *)
         apply (simp add: returnOk_bind bindE_assoc performRISCV64MMUInvocations)
         apply (ctac add: setThreadState_ccorres)
           apply (ctac add: performPageTableInvocationUnmap_ccorres)
              apply (rule ccorres_alternative2)
              apply (rule ccorres_return_CE, simp+)[1]
             apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
            apply wpsimp
           apply (vcg exspec=performPageTableInvocationUnmap_modifies)
          apply (wp sts_invs_minor')
         apply simp
         apply (vcg exspec=setThreadState_modifies)
        (* mapped, check it isn't a top-level PT *)
        apply (rule ccorres_rhs_assoc)+
        apply clarsimp
        apply csymbr
        apply csymbr
        apply (simp add: invocationCatch_use_injection_handler bindE_assoc)
        (* FIXME RISCV: the dynamic here with maybeVSpaceForASID, bind, bindE and the injection
                        handler is somewhat convoluted *)
  sorry (* FIXME RISCV
        apply (ctac add: setThreadState_ccorres)
          apply (ctac add: performPageTableInvocationUnmap_ccorres)
             apply (rule ccorres_alternative2)
             apply (rule ccorres_return_CE, simp+)[1]
            apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
           apply wp
          apply simp
          apply (vcg exspec=performRISCVPageTableInvocationUnmap_modifies)
         apply (wp sts_invs_minor')
        apply simp
        apply (vcg exspec=setThreadState_modifies)
       apply (wp hoare_drop_imps isFinalCapability_inv)
      apply simp
      apply (vcg exspec=isFinalCapability_modifies)
     apply (wp getCTE_wp)
    apply (vcg exspec=performRISCVPageTableInvocationUnmap_modifies exspec=isFinalCapability_modifies)
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
           apply (rule syscall_error_throwError_ccorres_n[simplified dc_def id_def o_def])
           apply (simp add: syscall_error_to_H_cases)
          apply (clarsimp simp: hd_conv_nth throwError_bind invocationCatch_def cong: if_cong)
          apply (rule syscall_error_throwError_ccorres_n[simplified dc_def id_def o_def])
          apply (simp add: syscall_error_to_H_cases)
         apply (simp add: hd_conv_nth)
         apply csymbr
         apply csymbr
         apply csymbr
         apply (simp add: case_option_If2 if_to_top_of_bind if_to_top_of_bindE hd_conv_nth)
         apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
            apply vcg
           apply (fastforce simp: user_vtop_def RISCV64.pptrUserTop_def bit_simps
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
                                    pde_lift_def from_bool_def case_bool_If
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
                apply (simp add: injection_handler_returnOk performRISCV64MMUInvocations bindE_assoc)
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
                  apply (vcg exspec=performRISCVPageTableInvocationMap_modifies)
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
                                    syscall_error_to_H_cases exception_defs false_def)
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
                                 syscall_error_to_H_cases exception_defs false_def)
           apply (erule lookup_failure_rel_fault_lift[rotated])
           apply (simp add: exception_defs)
          apply simp
          apply (wp injection_wp[OF refl] hoare_drop_imps)
         apply simp
         apply (vcg exspec=findVSpaceForASID_modifies)
        apply simp
        apply (rule_tac Q="\<lambda>a b. invs' b \<and> valid_cap' (fst (extraCaps ! 0)) b \<and> tcb_at' thread b \<and>
                                 sch_act_wf (ksSchedulerAction b) b \<and> cte_wp_at' (\<lambda>_. True) slot b"
                                 in hoare_strengthen_post)
         apply wp
        apply (clarsimp simp: isCap_simps invs_valid_objs' valid_cap'_def valid_tcb_state'_def
                              invs_arch_state' invs_no_0_obj')
       apply vcg
      apply wp
     apply simp
     apply (vcg exspec=getSyscallArg_modifies)
    apply wpsimp+
  apply (vcg exspec=getSyscallArg_modifies)
  apply (clarsimp simp: cte_wp_at_ctes_of excaps_map_def
                        word_sle_def word_sless_def bit_simps)
  (* RISCV64PageTableUnmap *)
  apply (rule conjI)
   apply (auto simp: ct_in_state'_def isCap_simps valid_tcb_state'_def
              elim!: pred_tcb'_weakenE dest!: st_tcb_at_idle_thread')[1]
  (* RISCV64PageTableMap *)
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
  (* RISCV64PageTableUnmap *)
  apply (rule conjI)
   apply (fastforce simp: rf_sr_ksCurThread "StrictC'_thread_state_defs"
                          mask_eq_iff_w2p word_size
                          ct_in_state'_def st_tcb_at'_def
                          word_sle_def word_sless_def
                          typ_heap_simps' bit_simps)
  (* RISCV64PageTableMap *)
  apply (drule_tac t="cteCap ctea" in sym, simp)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject isCap_simps
                        word_sle_def word_sless_def
                        word_less_nat_alt)
  apply (frule length_ineq_not_Nil)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(14))
  apply (clarsimp simp: cap_lift_page_directory_cap hd_conv_nth
                        cap_lift_page_table_cap bit_simps
                        cap_page_directory_cap_lift_def
                        to_bool_def
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
   apply (rule conjI, clarsimp simp: ThreadState_Restart_def mask_def)
   apply (rule conjI)
    (* ccap_relation *)
    apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_page_table_cap_lift[THEN iffD1]
                          cap_to_H_simps asid_wf_def3[simplified asid_bits_def, simplified])
    apply (rule conjI[rotated],
           fastforce simp: sign_extend_canonical_address le_def[symmetric] mask_def word_bw_assocs
                           le_user_vtop_canonical_address[simplified user_vtop_def RISCV64.pptrUserTop_def word_le_nat_alt])
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
     apply (clarsimp simp: ThreadState_Restart_def mask_def)
    (* ccap_relation *)
    apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_page_table_cap_lift[THEN iffD1]
                          cap_to_H_simps asid_wf_def3[simplified asid_bits_def, simplified])
     apply (rule conjI[rotated],
            fastforce simp: sign_extend_canonical_address le_def[symmetric] mask_def word_bw_assocs
                            le_user_vtop_canonical_address[simplified user_vtop_def RISCV64.pptrUserTop_def word_le_nat_alt])
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
  *)

lemma checkVPAlignment_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. \<acute>sz < 3\<rbrace> Call checkVPAlignment_'proc
          {t. ret__unsigned_long_' t = from_bool
               (vmsz_aligned (w_' s) (framesize_to_H (sz_' s)))}"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: mask_eq_iff_w2p word_size)
  apply (rule conjI)
   apply (simp add: pageBitsForSize_def bit_simps split: vmpage_size.split)
  apply (simp add: from_bool_def vmsz_aligned_def is_aligned_mask
                   mask_def split: if_split)
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

(* FIXME RISCV useful?
lemma pde_get_tag_alt:
  "pde_lift v = Some pdeC
    \<Longrightarrow> pde_get_tag v = (case pdeC of Pde_pde_pt _ \<Rightarrow> scast pde_pde_pt
          | Pde_pde_large _ \<Rightarrow> scast pde_pde_large)"
  by (auto simp add: pde_lift_def Let_def split: if_split_asm)

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
              split: RISCV64_H.pde.split_asm)
*)

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
  "obj_at' (\<lambda>a::RISCV64_H.pte. True) ptr s ==> is_aligned ptr word_size_bits"
  apply (drule obj_at_ko_at')
  apply (clarsimp dest!:ko_at_is_aligned'
                  simp: objBits_simps archObjSize_def bit_simps
                  elim!: is_aligned_weaken)
  done

(* FIXME RISCV: dont know what these are for yet *)
lemma addrFromPPtr_mask_5:
  "addrFromPPtr ptr && mask (5::nat) = ptr && mask (5::nat)"
  apply (simp add: addrFromPPtr_def RISCV64.pptrBase_def baseOffset_def canonical_bit_def
                   pAddr_base_def)
  apply word_bitwise
  apply (simp add:mask_def)
  done

lemma addrFromPPtr_mask_6:
  "addrFromPPtr ptr && mask (6::nat) = ptr && mask (6::nat)"
  apply (simp add: addrFromPPtr_def RISCV64.pptrBase_def baseOffset_def canonical_bit_def
                   pAddr_base_def)
  apply word_bitwise
  apply (simp add:mask_def)
  done

(* FIXME RISCV adapt?
lemma cpde_relation_invalid:
 "cpde_relation pdea pde \<Longrightarrow> (pde_get_tag pde = scast pde_pde_pt \<and> pde_pde_pt_CL.present_CL (pde_pde_pt_lift pde) = 0) = isInvalidPDE pdea"
  apply (simp add: cpde_relation_def Let_def)
  apply (simp add: pde_pde_pt_lift_def)
  apply (case_tac pdea, simp_all add: isInvalidPDE_def) [1]
   apply (clarsimp simp: pde_pde_pt_lift pde_pde_pt_lift_def)
  apply (simp add: pde_pde_pt_lift_def pde_pde_pt_lift)
  done
*)

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

(* FIXME RISCV: reformulate if needed
lemma pte_sadness:
  "\<lbrakk> pte' = pte\<lparr>pte_CL.page_base_address_CL := pte_CL.page_base_address_CL pte'\<rparr>;
     f (pte_CL.page_base_address_CL pte) = pte_CL.page_base_address_CL pte \<rbrakk>
   \<Longrightarrow> pte'\<lparr>pte_CL.page_base_address_CL := f (pte_CL.page_base_address_CL pte)\<rparr> = pte"
  apply (cases pte', cases pte, simp)
  done
*)

(* FIXME RISCV: needed?
definition
  "isVMPTE entry \<equiv> \<exists>x y. entry = (VMPTE x, VMPTEPtr y)"

primrec (nonexhaustive)
  thePTE :: "vmpage_entry \<Rightarrow> pte" where
  "thePTE (VMPTE pte) = pte"

primrec (nonexhaustive)
  thePTEPtr :: "vmpage_entry_ptr \<Rightarrow> machine_word" where
  "thePTEPtr (VMPTEPtr p) = p"
*)

lemma performPageInvocationMapPTE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 7 \<le> gsMaxObjectSize s)
           and (\<lambda>_. (isArchFrameCap cap \<and> capFMappedAddress (capCap cap) \<noteq> None)))
       (UNIV \<inter> {s. cpte_relation (fst mapping) (pte_' s)}
             \<inter> {s. ptSlot_' s = pte_Ptr (snd mapping)}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. base_' s = pte_Ptr (snd mapping)}) []
       (liftE (performPageInvocation (PageMap cap slot mapping)))
       (Call performPageInvocationMapPTE_'proc)"
  supply pageBitsForSize_le_64 [simp]
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift:  pte_' ptSlot_' cap_' ctSlot_' base_')
   apply clarsimp
   apply wpc (* split mapping *)
   apply ctac
     apply (rule ccorres_add_return2)
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

(* FIXME RISCV adapt?
lemma pde_align_ptBits:
  "\<lbrakk> ko_at' (RISCV64_H.PageTablePDE x y z w u v) slot s ;valid_objs' s\<rbrakk>
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
*)

lemma vaddr_segment_nonsense3_folded:
  "is_aligned (p :: machine_word) pageBits \<Longrightarrow>
   (p + ((vaddr >> pageBits) && mask (pt_bits - word_size_bits) << word_size_bits) && ~~ mask pt_bits) = p"
  apply (rule is_aligned_add_helper[THEN conjunct2])
   apply (simp add: bit_simps mask_def)+
  apply (rule shiftl_less_t2n[where m=12 and n=3, simplified, OF and_mask_less'[where n=9, unfolded mask_def, simplified]])
   apply simp+
  done

lemma vmsz_aligned_addrFromPPtr':
  "vmsz_aligned (addrFromPPtr p) sz
       = vmsz_aligned p sz"
  apply (simp add: vmsz_aligned_def RISCV64.addrFromPPtr_def baseOffset_def pAddr_base_def)
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

(* FIXME RISCV: adapt?
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
*)

lemma slotcap_in_mem_valid:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); valid_objs' s \<rbrakk>
            \<Longrightarrow> s \<turnstile>' cap"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) ctes_of_valid')
  done

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

definition
  to_option :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a option"
where
  "to_option f x \<equiv> if f x then Some x else None"

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
  "(case pte of PageTablePTE _ _ _ \<Rightarrow> P | _ \<Rightarrow> Q)
       = (if isPageTablePTE pte then P else Q)"
  by (clarsimp simp: isPageTablePTE_def split: pte.splits)

lemma ccap_relation_PageTableCap_BasePtr:
  "ccap_relation (ArchObjectCap (PageTableCap p r)) ccap
    \<Longrightarrow> capPTBasePtr_CL (cap_page_table_cap_lift ccap) = p"
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  by (drule (1) cap_lift_PTCap_Base, clarsimp)

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

(* FIXME RISCV: adapt
lemma ccap_relation_PageCap_MappedAddress_update:
  "\<lbrakk>cap_lift cap = Some (Cap_frame_cap (cap_frame_cap_lift cap));
    cp = FrameCap f_base f_vmr sz f_dev f_addr;
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
    newmt = scast RISCV_MappingVSpace; canonical_address vaddr\<rbrakk>
    \<Longrightarrow> ccap_relation (ArchObjectCap (PageCap f_base f_vmr VMVSpaceMap sz f_dev (Some (asid, vaddr)))) cap'"
   apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 cap_frame_cap_lift[THEN iffD1]
                         cap_to_H_simps asid_wf_def3[simplified asid_bits_def, simplified])
   apply (rule conjI, clarsimp simp: maptype_to_H_def vm_page_map_type_defs mask_def)
   apply (rule conjI,
           clarsimp simp: sign_extend_canonical_address le_def[symmetric] mask_def word_bw_assocs
                          le_user_vtop_canonical_address[simplified user_vtop_def
                          RISCV64.pptrUserTop_def word_le_nat_alt] vm_page_map_type_defs
                          canonical_address_user_vtop[simplified user_vtop_def RISCV64.pptrUserTop_def]
                   split: if_split)
    apply (rule conjI; word_bitwise, clarsimp)
   by (clarsimp simp: c_valid_cap_def cl_valid_cap_def vm_page_map_type_defs mask_def)
*)

lemma framesize_to_from_H:
  "sz < 3 \<Longrightarrow> framesize_from_H (framesize_to_H sz) = sz"
   apply (clarsimp simp: framesize_to_H_def framesize_from_H_def framesize_defs
           split: if_split vmpage_size.splits)
  by (word_bitwise, auto)

(* FIXME RISCV: adapt to PageTable?
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

lemma ccap_relation_capPML4MappedASID_liftE:
  "\<lbrakk> ccap_relation c c'; cap_get_tag c' = SCAST(32 signed \<rightarrow> 64) cap_pml4_cap;
     capPML4MappedASID (capCap c) = Some y \<rbrakk>
    \<Longrightarrow> capPML4MappedASID_CL (cap_pml4_cap_lift c') = the (capPML4MappedASID (capCap c))"
  by (simp add: cap_get_tag_PML4Cap split: if_splits)
*)

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

(* FIXME RISCV: on other architectures, C uses invLabel_' instead of label___unsigned_long,
                and excaps_' instead of extraCaps___struct_extra_caps_C_' *)
lemma decodeRISCVFrameInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp] Collect_const[simp del]
(* FIXME RISCV: adapt?
  defines "does_not_throw args extraCaps maptype pg_sz mapdata \<equiv>
           (mapdata = None \<longrightarrow> \<not> (unat user_vtop < unat (hd args)
                                  \<or> unat user_vtop < unat (hd args + 2 ^ pageBitsForSize pg_sz)))
           \<and> (mapdata \<noteq> None \<longrightarrow>
                (fst (the mapdata) = (the (capPML4MappedASID (capCap (fst (extraCaps ! 0)))))
                 \<and> maptype = VMVSpaceMap
                 \<and> snd (the mapdata) = hd args))"
*)
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps; isFrameCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. extraCaps___struct_extra_caps_C_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeRISCVMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeRISCVFrameInvocation_'proc)"
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_'
                      extraCaps___struct_extra_caps_C_' cap_' buffer_'
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
       apply (ctac(no_vcg) add: performPageGetAddress_ccorres)
         apply (rule ccorres_alternative2)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
       apply wp+
     apply (vcg exspec=setThreadState_modifies)
    apply (rule ccorres_rhs_assoc)+

    \<comment> \<open>PageUnmap\<close>
    apply (simp add: returnOk_bind bindE_assoc
                     performRISCV64MMUInvocations)
    apply (ctac add: setThreadState_ccorres)
      apply (ctac(no_vcg) add: performPageInvocationUnmap_ccorres)
        apply (rule ccorres_alternative2)
        apply (rule ccorres_return_CE, simp+)[1]
       apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
      apply wp
     apply (wp sts_invs_minor')
    apply simp
    apply (vcg exspec=setThreadState_modifies)

   \<comment> \<open>PageMap\<close>
   supply Collect_const[simp del]
   apply (rename_tac word rights pg_sz maptype mapdata buffera cap excaps cte
                     length___unsigned_long invLabel)
   apply (clarsimp simp: decodeRISCVFrameInvocationMap_def)
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
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
       apply (rule ccorres_add_return)
       apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
         apply (rule ccorres_add_return)
         apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=2 and buffer=buffer])
           apply csymbr
           apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
           apply (rule ccorres_move_c_guard_cte)
           apply (rule_tac r'="\<lambda>rv rv'. ((cap_get_tag rv' = scast cap_page_table_cap)
                                            = (isArchObjectCap rv \<and> isPageTableCap (capCap rv)))
                                        \<and> (ccap_relation rv rv')"
                      and xf'=lvl1ptCap_' in ccorres_split_nothrow[where F=UNIV])
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
  sorry (* FIXME RISCV different csymbr coming up with different variables, diverges here
             apply csymbr+
             apply (simp add: if_P_then_t_else_f_eq_f_simps)
             apply (clarsimp simp add: split_def cap_case_PML4Cap2)
             apply (simp add: word_less_nat_alt length_ineq_not_Nil)
             apply (rule ccorres_Cond_rhs_Seq)
              apply (rule ccorres_equals_throwError)
               apply (simp add: unfold_checkMapping_return)
               apply (xfastforce simp: invocationCatch_def throwError_bind hd_conv_nth from_bool_0
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
                apply (rule syscall_error_throwError_ccorres_n[simplified id_def o_def dc_def])
                apply (clarsimp simp: syscall_error_to_H_cases)
               (* throw on mismatched vaddr *)
               apply simp
               apply csymbr
               apply (frule ccap_relation_PageCap_generics)
               apply (clarsimp simp: hd_conv_nth length_ineq_not_Nil)
               apply ccorres_rewrite
               apply (clarsimp simp: maptype_from_H_def throwError_bind invocationCatch_def
                              split: vmmap_type.split_asm)
                apply (clarsimp simp: RISCV_MappingNone_def RISCV_MappingVSpace_def)
               apply ccorres_rewrite
               apply (fold dc_def id_def)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              (* frame cap not mapped, check mapping *)
              (* disallow mappings above kernelBase *)
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
              apply (simp add: user_vtop_def RISCV64.pptrUserTop_def hd_conv_nth length_ineq_not_Nil)
              apply ccorres_rewrite
              apply (rule syscall_error_throwError_ccorres_n[unfolded id_def dc_def])
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
                   apply (simp add: word_less_nat_alt user_vtop_def RISCV64.pptrUserTop_def hd_conv_nth
                                    length_ineq_not_Nil)
                   apply (ccorres_rewrite)
                   apply (fold dc_def)
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
                    apply (clarsimp simp: cap_lift_pml4_cap cap_to_H_def get_capPtr_CL_def to_bool_def
                                          cap_pml4_cap_lift_def
                                   elim!: ccap_relationE split: if_split)
                   apply (rule syscall_error_throwError_ccorres_n[simplified id_def o_def dc_def])
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
                      apply (clarsimp simp: framesize_from_to_H user_vtop_def RISCV64.pptrUserTop_def)
                     apply (simp add: injection_handler_throwError throwError_bind
                                      invocationCatch_def)
                     apply (rule syscall_error_throwError_ccorres_n[simplified id_def o_def dc_def])
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
                        apply (simp add: performRISCV64MMUInvocations bindE_assoc)
                        apply ccorres_rewrite
                        apply (rule_tac P="\<lambda>s. thread = ksCurThread s" in ccorres_cross_over_guard)
                        apply (ctac add: setThreadState_ccorres)
                          apply (ctac(no_vcg) add: performPageInvocationMapPTE_ccorres)
                            apply (rule ccorres_alternative2)
                            apply (rule ccorres_return_CE, simp+)[1]
                           apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                          apply (wp sts_invs_minor')+
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
                      apply (clarsimp simp: ThreadState_Restart_def mask_def rf_sr_ksCurThread
                                            isCap_simps cap_pml4_cap_lift
                                            get_capPtr_CL_def ccap_relation_PML4Cap_BasePtr)
                     apply clarsimp
                    apply (rule ccorres_Cond_rhs)
                     apply (rule ccorres_rhs_assoc)+
                     apply csymbr
                     apply (ctac add: ccorres_injection_handler_csum1
                                        [OF createSafeMappingEntries_PDE_ccorres])
                        apply (simp add: performRISCV64MMUInvocations bindE_assoc)
                        apply ccorres_rewrite
                        apply (rule_tac P="\<lambda>s. thread = ksCurThread s" in ccorres_cross_over_guard)
                        apply (ctac add: setThreadState_ccorres)
                          apply (ctac(no_vcg) add: performPageInvocationMapPDE_ccorres)
                            apply (rule ccorres_alternative2)
                            apply (rule ccorres_return_CE, simp+)[1]
                           apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                          apply wp
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
                      apply (clarsimp simp: ThreadState_Restart_def mask_def rf_sr_ksCurThread
                                            isCap_simps cap_pml4_cap_lift
                                            get_capPtr_CL_def ccap_relation_PML4Cap_BasePtr)
                     apply clarsimp
                    apply (rule ccorres_add_returnOk)
                    apply (ctac add: decodeRISCVModeMapPage_ccorres)
                       apply (rule ccorres_return_CE, simp+)[1]
                      apply (rule ccorres_return_C_errorE, simp+)[1]
                     apply wpsimp
                    apply clarsimp
                    apply (vcg exspec=decodeRISCVModeMapPage_modifies)
                   apply clarsimp
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
  apply (rename_tac word rghts maptype pg_sz mapdata buffera cap excaps cte length___unsigned_long
                    invLabel s s')
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
                             is_aligned_addrFromPPtr_pageBitsForSize[where sz=RISCV64LargePage, simplified]
                             is_aligned_addrFromPPtr_pageBitsForSize[where sz=RISCV64HugePage, simplified]
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
  apply (clarsimp simp: rf_sr_ksCurThread "StrictC'_thread_state_defs" mask_eq_iff_w2p
                        word_size word_less_nat_alt from_bool_0 excaps_map_def cte_wp_at_ctes_of
                        n_msgRegisters_def)
  apply (frule(1) ctes_of_valid')
  apply (drule_tac t="cteCap ctea" in sym)
  apply (clarsimp simp: valid_cap'_def capAligned_def word_sless_def word_sle_def)
  apply (frule ccap_relation_PageCap_generics)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply clarsimp
  apply (frule cap_get_tag_PageCap_frame)
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
  apply (clarsimp simp: cap_lift_pml4_cap to_bool_def cap_pml4_cap_lift_def framesize_from_to_H
                           cap_to_H_def[split_simps cap_CL.split]
                           valid_cap'_def user_vtop_def RISCV64.pptrUserTop_def)
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
     apply (simp add: word_le_nat_alt not_less user_vtop_def RISCV64.pptrUserTop_def)
    prefer 2
    apply (frule(1) cap_to_H_PageCap_tag)
    apply (frule canonical_address_cap_frame_cap)
    apply metis
   apply ((intro conjI impI,
          (rule_tac cp=cp in ccap_relation_PageCap_MappedAddress_update
           ; force simp: vm_page_map_type_defs mask_def),
          (rule_tac cp=cp in ccap_relation_PageCap_MappedAddress_update
           ; force simp: vm_page_map_type_defs mask_def),
          meson invocation_eq_use_types,
          (rule framesize_to_from_H[symmetric], fastforce simp: c_valid_cap_def cl_valid_cap_def),
          (rule_tac cp=cp in ccap_relation_PageCap_MappedAddress_update
           ; force simp: vm_page_map_type_defs mask_def))+)[2] (* 70s *)
  done
  *)

(* FIXME RISCV64: adapted from x64 *)
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

declare Word_Lemmas.from_bool_mask_simp [simp]

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

(* FIXME RISCV: adapt?
lemma ccap_relation_page_directory_mapped_asid:
  "ccap_relation (ArchObjectCap (PageDirectoryCap p (Some (asid, vspace)))) cap
    \<Longrightarrow> asid = capPDMappedASID_CL (cap_page_directory_cap_lift cap)"
  by (frule cap_get_tag_isCap_unfolded_H_cap)
     (clarsimp simp: cap_page_directory_cap_lift ccap_relation_def cap_to_H_def split: if_splits)
*)

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
              and sysargs_rel args buffer and valid_objs')
       (UNIV \<inter> {s. label___unsigned_long_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. extraCaps___struct_extra_caps_C_' s = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeRISCVMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeRISCVMMUInvocation_'proc)"
thm decodeRISCVMMUInvocation_body_def
  apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' cte_'
                      extraCaps___struct_extra_caps_C_' cap_' buffer_')
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
     apply (rule syscall_error_throwError_ccorres_n[simplified id_def o_def])
     apply (fastforce simp: syscall_error_to_H_cases)
    (* RISCV64ASIDControlMakePool *)
    apply (clarsimp simp: decodeRISCVMMUInvocation_def decodeRISCVASIDControlInvocation_def isCap_simps)
    apply (simp add: word_less_nat_alt list_case_If2 split_def)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     (* args malformed *)
     apply (rule ccorres_cond_true_seq | simp)+
     apply (simp add: throwError_bind invocationCatch_def)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n[simplified id_def o_def])
     apply (fastforce simp: syscall_error_to_H_cases)
    apply (simp add: interpret_excaps_test_null excaps_map_def)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     (* extraCaps malformed *)
     apply (rule ccorres_cond_true_seq | simp)+
     apply (simp add: throwError_bind invocationCatch_def)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n[simplified id_def o_def])
     apply (fastforce simp: syscall_error_to_H_cases)
    apply csymbr
    apply (simp add: interpret_excaps_test_null[OF Suc_leI])
    apply (rule ccorres_Cond_rhs_Seq)
     apply (simp add: length_ineq_not_Nil throwError_bind invocationCatch_def)
     apply ccorres_rewrite
     apply (rule syscall_error_throwError_ccorres_n[simplified id_def o_def])
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
                   apply (fastforce simp: max_word_def asid_high_bits_def)
                  apply (clarsimp simp: rf_sr_riscvKSASIDTable from_bool_def
                                        asid_high_bits_word_bits
                                        option_to_ptr_def option_to_0_def
                                        order_less_imp_le
                                        linorder_not_less
                                        order_antisym[OF inc_le])
                  apply (clarsimp simp: true_def false_def
                                 split: option.split if_split)
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
                apply (simp add: asid_high_bits_def option_to_ptr_def option_to_0_def
                                 from_bool_def Kernel_C_defs
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
               apply (rule syscall_error_throwError_ccorres_n[simplified id_def o_def])
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
                    apply (rule syscall_error_throwError_ccorres_n[simplified id_def])
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
                         apply (clarsimp simp: null_def ThreadState_Restart_def mask_def hd_conv_nth
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
     apply (rule syscall_error_throwError_ccorres_n[simplified dc_def id_def o_def])
     apply (fastforce simp: syscall_error_to_H_cases)
    apply (clarsimp simp: isCap_simps decodeRISCVASIDPoolInvocation_def split: list.split)
    apply csymbr
    apply (rule ccorres_add_return)
    apply (rule ccorres_Guard_Seq)
    (* FIXME RISCV: there appears to be a missing check in the C here, we do not know that
                    the extra cap is a page table cap; this is waiting on C update
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_rhs_assoc2)
    *)
    apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
           rule ccorres_rhs_assoc2)
(*
apply (rule ccorres_split_nothrow)
*)
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
       apply (case_tac a; clarsimp simp: isCap_simps cap_get_tag_isCap_unfolded_H_cap
                                         cap_tag_defs true_def)
       apply (intro conjI impI
              ; solves \<open>clarsimp simp: isCap_simps asidInvalid_def cap_lift_page_table_cap cap_to_H_simps
                                       true_def c_valid_cap_def cl_valid_cap_def
                                       ccap_relation_PageTableCap_IsMapped\<close>)
      apply ceqv
     apply (rule ccorres_Cond_rhs_Seq)
      apply ccorres_rewrite
      apply (rule_tac v="Inl (InvalidCapability 1)" in ccorres_equals_throwError)
       apply (fastforce simp: isCap_simps throwError_bind invocationCatch_def
                        split: capability.split arch_capability.split)
      apply (rule syscall_error_throwError_ccorres_n)
      apply (fastforce simp: syscall_error_to_H_cases)
     apply (clarsimp simp: isCap_simps Kernel_C_defs liftE_bindE bind_assoc)
     apply (rule ccorres_pre_gets_riscvKSASIDTable_ksArchState)
     apply csymbr
     apply (rule ccorres_Guard_Seq)+
     apply (rule ccorres_add_return)
     apply (rule_tac r'="\<lambda>_ rv'. rv' = option_to_ptr (x (ucast (asid_high_bits_of (ucast (capASIDBase cp)))))
                                 \<and> x (ucast (asid_high_bits_of (ucast (capASIDBase cp)))) \<noteq> Some 0"
                 and xf'=pool_' in ccorres_split_nothrow)
         apply (rule_tac P="\<lambda>s. x = riscvKSASIDTable (ksArchState s)
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
                              syscall_error_rel_def exception_defs
                              syscall_error_to_H_cases false_def)
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
  sorry (* FIXME RISCV TODO vcg goal with loop in it, needs more thinking
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
               apply (clarsimp simp: inc_le from_bool_def typ_heap_simps
                                     asid_low_bits_def not_less field_simps
                                     false_def
                              split: if_split bool.splits)
               apply xunat_arith
              apply (rule iffI)
               apply (rule disjCI)
               apply (drule plus_one_helper)
               apply simp
              apply (subgoal_tac "i_' xb < i_' xb + 1")
               apply (erule_tac P="x < y" for x y in disjE, simp_all)[1]
              apply (rule plus_one_helper2 [OF order_refl])
              apply (rule notI, drule max_word_wrap)
              apply (fastforce simp: max_word_def asid_low_bits_def)
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
           apply (clarsimp simp: typ_heap_simps from_bool_def split: if_split)
           apply (frule cap_get_tag_isCap_unfolded_H_cap)
           apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_def
                                 cap_asid_pool_cap_lift_def false_def
                                 ucast_minus ucast_nat_def
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
                          RISCV64_H.performInvocation_def
                          performRISCV64MMUInvocation_def liftE_bindE)
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
   apply (rule ccorres_trim_returnE; simp)
   apply (rule ccorres_call,
          rule decodeRISCV64ModeMMUInvocation_ccorres;
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
    apply (clarsimp simp: ex_cte_cap_wp_to'_def cte_wp_at_ctes_of
                          invs_sch_act_wf' dest!: isCapDs(1))
    apply (intro conjI)
            apply (simp add: Invariants_H.invs_queues)
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
                          RISCV64_H.maskCapRights_def
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
                        word_sle_def word_sless_def asidLowBits_handy_convs
                        rf_sr_ksCurThread "StrictC'_thread_state_defs"
                        mask_def[where n=4]
                  cong: if_cong)
  apply (clarsimp simp: to_bool_def ccap_relation_isDeviceCap2 objBits_simps
                        archObjSize_def pageBits_def from_bool_def case_bool_If)
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
                         objBits_simps archObjSize_def pageBits_def from_bool_def case_bool_If
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
  apply (erule rf_sr_cte_at_validD[rotated])
  apply (fastforce simp: slotcap_in_mem_def2)
  done
  *)

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
   by (clarsimp simp: st_tcb_at'_def ct_in_state'_def obj_at'_def projectKOs,
              case_tac "tcbState obj"; clarsimp)+

(* FIXME RISCV: on other architectures, C uses invLabel_' instead of label___unsigned_long,
                and excaps_' instead of extraCaps___struct_extra_caps_C_' *)
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
             \<inter> {s. extraCaps___struct_extra_caps_C_' s = extraCaps'}
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
    apply (cinit' lift: label___unsigned_long_' length___unsigned_long_' slot_'
                        extraCaps___struct_extra_caps_C_' cap_' buffer_' call_')
     apply (simp only: cap_get_tag_isCap_ArchObject RISCV64_H.decodeInvocation_def)
       apply (rule trim_call[OF decodeRISCVMMUInvocation_ccorres], simp+)[1]
    apply (clarsimp simp: o_def excaps_in_mem_def slotcap_in_mem_def)
    done
qed

end

end
