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

context begin interpretation Arch . (*FIXME: arch_split*)
crunch ctes_of[wp]: unmapPageTable "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: crunch_simps)

crunch gsMaxObjectSize[wp]: unmapPageTable "\<lambda>s. P (gsMaxObjectSize s)"

crunch inv[wp]: pteCheckIfMapped "P"

crunch inv[wp]: pdeCheckIfMapped "P"
end

context kernel_m begin

lemma storePTE_def':
  "storePTE slot pte = setObject slot pte"
  unfolding storePTE_def
  apply (simp add: tailM_def headM_def)
  apply (case_tac pte)
    by (auto simp add: wordsFromPTE_def)+

lemma storePDE_def':
  "storePDE slot pde = setObject slot pde"
  unfolding storePDE_def
  apply (simp add: tailM_def headM_def)
  apply (case_tac pde)
    by (auto simp add: wordsFromPDE_def)+

lemma objBits_InvalidPTE:
  "objBits ARM_HYP_H.InvalidPTE = pteBits"
  apply (simp add: objBits_simps archObjSize_def)
  done

lemma performPageTableInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) \<circ> cteCap) ctSlot
              and (\<lambda>_. isPageTableCap cap))
       (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performPageTableInvocation (PageTableUnmap cap ctSlot)))
       (Call performPageTableInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (rule ccorres_gen_asm)
  apply (cinit lift: cap_' ctSlot_')
   apply csymbr
   apply (simp add: del: Collect_const)
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
          apply (ctac add: clearMemory_PT_setObject_PTE_ccorres[unfolded objBits_InvalidPTE, simplified])
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
                           typ_heap_simps'
                           cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    dest!: ksPSpace_update_eq_ExD)
    apply (simp add: cte_wp_at_ctes_of)
    apply (wp mapM_x_wp' | wpc | simp)+
   apply (simp add: guard_is_UNIV_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric] cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (frule valid_global_refsD_with_objSize, clarsimp)
  apply (clarsimp simp: cap_lift_page_table_cap cap_to_H_def
                        cap_page_table_cap_lift_def isCap_simps
                        valid_cap'_def get_capSizeBits_CL_def
                        table_bits_defs capAligned_def
                        to_bool_def mask_def page_table_at'_def
                        capRange_def Int_commute asid_bits_def
                 elim!: ccap_relationE cong: if_cong)
  apply (drule spec[where x=0], clarsimp)
  done

lemma cap_case_PageDirectoryCap2:
  "(case cap of ArchObjectCap (PageDirectoryCap pd mapdata)
                   \<Rightarrow> f pd mapdata | _ \<Rightarrow> g)
   = (if isArchObjectCap cap \<and> isPageDirectoryCap (capCap cap)
      then f (capPDBasePtr (capCap cap)) (capPDMappedASID (capCap cap))
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
   (CALL memzero(Ptr frame, (2 ^ unat ARMSmallPageBits));;
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
   apply (simp add: ARMSmallPageBits_def pageBits_def)
  apply (erule valid_untyped_capE)
  apply (subst simpler_placeNewObject_def)
      apply ((simp add:word_bits_conv objBits_simps archObjSize_def
        capAligned_def)+)[4]
  apply (simp add:simpler_modify_def rf_sr_htd_safe)
  apply (subgoal_tac "{frame ..+ 2 ^ pageBits} \<inter> kernel_data_refs = {}")
   prefer 2
   apply (drule(1) valid_global_refsD')
   apply (clarsimp simp:Int_commute pageBits_def ARMSmallPageBits_def
     intvl_range_conv[where bits = pageBits,unfolded pageBits_def word_bits_def,simplified])
  apply (intro conjI impI)
       apply (erule is_aligned_no_wrap')
       apply (clarsimp simp:ARMSmallPageBits_def pageBits_def)
      apply (erule is_aligned_weaken,simp add:pageBits_def)
     apply (simp add:is_aligned_def ARMSmallPageBits_def)
    apply (simp add: region_actually_is_bytes_dom_s pageBits_def ARMSmallPageBits_def)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         size_of_def pageBits_def
                         ptr_retyp_htd_safe_neg)
  apply clarsimp
  apply (cut_tac helper [rule_format])
   prefer 2
   apply fastforce
  apply (subst data_map_insert_def[symmetric])
  apply (erule iffD1[OF rf_sr_upd,rotated -1 ])
   apply simp_all
  apply (simp add: hrs_htd_update_def hrs_mem_update_def split_def)
  apply (simp add: pageBits_def ARMSmallPageBits_def ptr_retyps_gen_def
              del:replicate_numeral)
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
  "unat (sz :: word32) \<le> gsMaxObjectSize s
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
                apply (subst Divides.mod_less, simp)
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
     apply (rule_tac Q="\<lambda>_. cte_wp_at' ((=) (UntypedCap isdev frame pageBits idx) o cteCap) parent
                           and (\<lambda>s. descendants_range_in' {frame..frame + (2::word32) ^ pageBits - (1::word32)} parent (ctes_of s))
                           and pspace_no_overlap' frame pageBits
                           and invs'
                           and ct_active'"
                 in hoare_post_imp)
     apply (clarsimp simp: cte_wp_at_ctes_of invs_valid_objs' range_cover_full word_bits_conv
                           pageBits_def max_free_index_def asid_low_bits_def untypedBits_defs)
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
  apply (clarsimp simp: ARMSmallPageBits_def word_sle_def is_aligned_mask[symmetric]
                        ghost_assertion_data_get_gs_clear_region)
  apply (subst ghost_assertion_size_logic_flex[unfolded o_def, rotated])
     apply assumption
    apply (simp add: ghost_assertion_data_get_gs_clear_region)
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
  apply (drule word_le_mask_eq)
  apply (simp add: asid_bits_def)
  done

lemmas performARMMMUInvocations
    = ccorres_invocationCatch_Inr performInvocation_def
      ARM_HYP_H.performInvocation_def performARMMMUInvocation_def
      liftE_bind_return_bindE_returnOk

lemma slotcap_in_mem_PageDirectory:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); (s, s') \<in> rf_sr \<rbrakk>
       \<Longrightarrow> \<exists>v. cslift s' (cte_Ptr slot) = Some v
           \<and> (cap_get_tag (cte_C.cap_C v) = scast cap_page_directory_cap)
              = (isArchObjectCap cap \<and> isPageDirectoryCap (capCap cap))
           \<and> (isArchObjectCap cap \<and> isPageDirectoryCap (capCap cap)
                  \<longrightarrow> ccap_relation cap (cte_C.cap_C v))"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
  apply (clarsimp dest!: ccte_relation_ccap_relation)
  apply (simp add: cap_get_tag_isCap_ArchObject2)
  done

lemma decodeARMPageTableInvocation_ccorres:
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps;
          isPageTableCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
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
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeARMMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeARMPageTableInvocation_'proc)"
  supply if_cong[cong]
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_' current_extra_caps_' cap_' buffer_'
                simp: decodeARMMMUInvocation_def invocation_eq_use_types)
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
                         performARMMMUInvocations)
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
       apply (wp hoare_drop_imps isFinalCapability_inv)
      apply simp
      apply (vcg exspec=isFinalCapability_modifies)
     apply (wp getCTE_wp)
    apply (vcg exspec=performPageTableInvocationUnmap_modifies exspec=isFinalCapability_modifies)
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
   apply (simp add: cap_case_PageDirectoryCap2 split_def del: Collect_const)
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
     apply (rule ccorres_add_return)
     apply (rule_tac r'="(\<lambda>rv _ rv'. ((cap_get_tag rv' = scast cap_page_directory_cap)
                                          = (isArchObjectCap rv \<and> isPageDirectoryCap (capCap rv)))
                                  \<and> (cap_get_tag rv' = scast cap_page_directory_cap \<longrightarrow> ccap_relation rv rv'))
                                      (fst (extraCaps ! 0))"
                and xf'=pdCap_' in ccorres_split_nothrow)
         apply (rule ccorres_from_vcg[where P="excaps_in_mem extraCaps \<circ> ctes_of" and P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: excaps_in_mem_def return_def neq_Nil_conv)
         apply (drule(1) slotcap_in_mem_PageDirectory)
         apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
         apply (clarsimp simp: typ_heap_simps' mask_def)
        apply (simp add:word_sless_def word_sle_def)
        apply ceqv
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
       apply csymbr
       apply (simp add: if_to_top_of_bind del: Collect_const)
       apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
          apply vcg
         apply (simp add: pptrBase_def ARM_HYP.pptrBase_def hd_conv_nth length_ineq_not_Nil)
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
            apply (simp add: table_bits_defs)
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
                               performARMMMUInvocations bindE_assoc)
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
                               syscall_error_to_H_cases exception_defs)
         apply (erule lookup_failure_rel_fault_lift[rotated])
         apply (simp add: exception_defs)
        apply simp
        apply (wp injection_wp[OF refl] hoare_drop_imps)
       apply simp
       apply (vcg exspec=findPDForASID_modifies)
      apply simp
      apply (wp | wp (once) hoare_drop_imps)+
     apply simp
     apply vcg
    apply simp
    apply wp
   apply simp
   apply (vcg exspec=getSyscallArg_modifies)
  apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of excaps_map_def
                        if_1_0_0 word_sle_def word_sless_def table_bits_defs)
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
                          less_pptrBase_valid_pde_offset''
                          word_le_nat_alt[symmetric] table_bits_defs)
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
                         typ_heap_simps' table_bits_defs)

  apply (clarsimp simp: cap_get_tag_isCap_ArchObject isCap_simps
                        word_sle_def word_sless_def
                        word_less_nat_alt)
  apply (frule length_ineq_not_Nil)
  apply (drule_tac t="cteCap ctea" in sym, simp)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(14))
  apply (clarsimp simp: cap_lift_page_directory_cap hd_conv_nth
                        cap_lift_page_table_cap table_bits_defs
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
          simp add: unat_eq_0 unat_shiftr_le_bound table_bits_defs)
  apply (clarsimp simp: rf_sr_ksCurThread mask_def[where n=4]
                        "StrictC'_thread_state_defs"
                        ccap_relation_def cap_to_H_def
                        cap_lift_page_table_cap word_bw_assocs
                        shiftr_shiftl1 mask_def[where n=17])
  apply (clarsimp simp: cpde_relation_def Let_def pde_lift_pde_coarse
                        pde_pde_coarse_lift_def word_bw_assocs page_table_at'_def table_bits_defs)
  apply (subst is_aligned_neg_mask_eq, erule is_aligned_addrFromPPtr_n)
   apply fastforce+
  done

lemma checkVPAlignment_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. \<acute>sz < 4\<rbrace> Call checkVPAlignment_'proc
          {t. ret__unsigned_long_' t = from_bool
               (vmsz_aligned' (w_' s) (gen_framesize_to_H (sz_' s)))}"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: mask_eq_iff_w2p word_size)
  apply (rule conjI)
   apply (simp add: pageBitsForSize_def split: vmpage_size.split)
  apply (simp add: vmsz_aligned'_def is_aligned_mask mask_def
            split: if_split)
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
  ptr_range_to_list :: "('a :: c_type) ptr \<Rightarrow> word32 \<Rightarrow> 'a ptr list"
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
       armPageCacheable_CL (vm_attributes_lift attr') = from_bool (armPageCacheable attr)
       \<comment> \<open>armParityEnabled_CL / armParityEnabled is not used on ARM with hypervisor
          Note: Slight divergence between the generated vmAttributesFromWord in C which maps
                across all the attributes, and the Haskell which explicitly sets the parity
                enabled attribute to False.
                In C, the complete set of attributes are passed around, then subsequently parity
                attribute is ignored when constructing PTE/PDEs.
         \<close>
     \<and> armExecuteNever_CL (vm_attributes_lift attr') = from_bool (armExecuteNever attr)"

lemma framesize_from_H_eqs:
  "(framesize_from_H vsz = scast Kernel_C.ARMSmallPage) = (vsz = ARMSmallPage)"
  "(framesize_from_H vsz = scast Kernel_C.ARMLargePage) = (vsz = ARMLargePage)"
  "(framesize_from_H vsz = scast Kernel_C.ARMSection) = (vsz = ARMSection)"
  "(framesize_from_H vsz = scast Kernel_C.ARMSuperSection) = (vsz = ARMSuperSection)"
  by (simp add: framesize_from_H_def vm_page_size_defs split: vmpage_size.split)+

lemma pde_get_tag_alt:
  "pde_lift v = Some pdeC
    \<Longrightarrow> pde_get_tag v = (case pdeC of Pde_pde_invalid _ \<Rightarrow> scast pde_pde_invalid
          | Pde_pde_coarse _ \<Rightarrow> scast pde_pde_coarse
          | Pde_pde_section _ \<Rightarrow> scast pde_pde_section)"
  by (auto simp add: pde_lift_def Let_def split: if_split_asm)

lemma cpde_relation_pde_case:
  "cpde_relation pde cpde
     \<Longrightarrow> (case pde of InvalidPDE \<Rightarrow> P
             | PageTablePDE _ \<Rightarrow> Q
             | SectionPDE _ _ _ _ \<Rightarrow> R
             | SuperSectionPDE _ _ _ _ \<Rightarrow> S)
         = (if pde_get_tag cpde = scast pde_pde_invalid then P
            else if (pde_get_tag cpde = scast pde_pde_coarse)
                     \<or> (pde_get_tag cpde \<noteq> scast pde_pde_section) then Q
            else if  pde_pde_section_CL.contiguous_hint_CL (pde_pde_section_lift cpde) = 0
                 then R else S)"
  by (clarsimp simp: cpde_relation_def Let_def pde_get_tag_alt
                     pde_tag_defs pde_pde_section_lift_def memattr_from_cacheable_def
              split: ARM_HYP_H.pde.split_asm)

lemma pde_pde_section_size_0_1:
  "pde_get_tag pde = scast pde_pde_section
     \<Longrightarrow> pde_pde_section_CL.contiguous_hint_CL (pde_pde_section_lift pde) = 0
            \<or> pde_pde_section_CL.contiguous_hint_CL (pde_pde_section_lift pde) = 1"
  apply (simp add: pde_pde_section_lift_def pde_lift_pde_section)
  apply (rule x_less_2_0_1)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply simp
  done

lemma createSafeMappingEntries_PDE_ccorres:
  "ccorres (syscall_error_rel \<currency> (\<lambda>rv rv'. isRight rv \<and> cpde_relation (fst (theRight rv)) (fst rv')
                                         \<and> pde_range_relation (snd (theRight rv)) (snd rv')))
     (liftxf errstate create_mappings_pde_return_C.status_C
             (\<lambda>v. (create_mappings_pde_return_C.pde_C v,
                   create_mappings_pde_return_C.pde_entries_C v))
             ret__struct_create_mappings_pde_return_C_')
     (page_directory_at' pd and (\<lambda>_. vmsz_aligned' vaddr vsz \<and> vmsz_aligned' base vsz
                        \<and> is_aligned pd pdBits))
     (UNIV \<inter> {s. base_' s = base} \<inter> {s. vaddr_' s = vaddr}
           \<inter> {s. frameSize_' s = framesize_from_H vsz
                   \<and> (vsz = ARMSection \<or> vsz = ARMSuperSection)}
           \<inter> {s. vmrights_to_H (vmRights_' s) = vrights \<and> vmRights_' s < 4}
           \<inter> {s. vm_attribs_relation attr (attr_' s)}
           \<inter> {s. pd_' s = pde_Ptr pd}) []
     (createSafeMappingEntries base vaddr vsz vrights attr pd)
     (Call createSafeMappingEntries_PDE_'proc)"
  apply (rule ccorres_gen_asm)
  apply (subgoal_tac "vsz = ARMSuperSection
                       \<longrightarrow> lookup_pd_slot pd vaddr \<le> lookup_pd_slot pd vaddr + 0x3C")
   prefer 2
   apply (clarsimp simp: vmsz_aligned'_def)
   apply (rule is_aligned_no_wrap'[where sz=6], simp_all add: word_bits_def)[1]
   apply (simp add: lookup_pd_slot_def Let_def)
   apply (erule aligned_add_aligned,
          simp_all add: table_bits_defs word_bits_def)[1]
   apply (intro is_aligned_shiftl is_aligned_shiftr)
   apply (simp add: table_bits_defs)
   apply (erule is_aligned_weaken, simp)
  apply (cinit lift: base_' vaddr_' frameSize_' vmRights_' attr_' pd_')
   apply (simp add: createSafeMappingEntries_def createMappingEntries_def
                    ensureSafeMapping_def framesize_from_H_eqs
               del: Collect_const)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: mapME_x_def sequenceE_x_def bindE_assoc
                del: Collect_const)
    apply (simp add: liftE_bindE)
    apply (rule ccorres_pre_getObject_pde)
    apply (rule_tac P'="{s. \<exists>v. cslift s (pde_Ptr (lookup_pd_slot pd vaddr)) = Some v
                                 \<and> cpde_relation x v
                                 \<and> array_assertion (pde_Ptr pd) (2 ^ (pdBits - pdeBits)) (hrs_htd (t_hrs_' (globals s)))}"
               in ccorres_from_vcg_might_throw[where P=\<top>])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: if_1_0_0)
    apply (clarsimp simp: typ_heap_simps vm_attribs_relation_def
                          from_bool_mask_simp[unfolded mask_def, simplified] table_bits_defs)
    apply (rule conjI)
     apply (simp add: gen_framesize_to_H_def vm_page_size_defs)
    apply (clarsimp simp: pde_get_tag_alt cpde_relation_pde_case
                          pde_tag_defs fst_throwError_returnOk
                          pde_range_relation_def ptr_range_to_list_def
                          exception_defs isRight_def
                          syscall_error_rel_def syscall_error_to_H_cases)
    apply (clarsimp simp: cpde_relation_def)
   apply (rule ccorres_Cond_rhs)
    apply (simp del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_rhs_assoc2)
    apply (rule ccorres_symb_exec_r)
      apply (rule ccorres_Guard_Seq)+
      apply csymbr
      apply csymbr
      apply csymbr
      apply csymbr
      apply csymbr
      apply (simp add: mapME_x_sequenceE bindE_assoc)
      apply (simp add:ARMSuperSectionBits_def word_0_sle_from_less
         ARMSectionBits_def)
      apply (ccorres_remove_UNIV_guard)
      apply csymbr
      apply (rule ccorres_rhs_assoc2,rule ccorres_splitE)
          apply (simp only:whileAnno_def)
          apply (ccorres_remove_UNIV_guard)
          apply (rule_tac r'=dc and xf'=xfdc and F="\<lambda>_. page_directory_at' pd"
                    and Q="{s. pde_range_C.base_C (pde_entries_C
                                                   ret___struct_create_mappings_pde_return_C)
                                   = Ptr (lookup_pd_slot pd vaddr)}"
                     in ccorres_sequenceE_while)
               apply (simp add: liftE_bindE)
               apply (rule ccorres_guard_imp2)
                apply (rule_tac r'="\<lambda>rv rv'. rv' = from_bool (isPageTablePDE rv \<or> isSectionPDE rv)"
                           and xf'=ret__int_' in ccorres_split_nothrow_novcg)
                    apply (rule ccorres_add_return2, rule ccorres_pre_getObject_pde)
                    apply (rule_tac P'="{s. let ptr = (pde_range_C.base_C (pde_entries_C
                                                       ret___struct_create_mappings_pde_return_C))
                                  in \<exists>v. cslift s (CTypesDefs.ptr_add ptr (uint (i_' s))) = Some v
                                   \<and> cpde_relation x v
                                   \<and> (i_' s = 0 \<or> array_assertion ptr (Suc (unat (i_' s)))
                                      (hrs_htd (t_hrs_' (globals s))))}"
                             in ccorres_from_vcg_nofail[where P=\<top>])
                    apply (rule allI, rule conseqPre, vcg)
                    apply (clarsimp simp: if_1_0_0 return_def typ_heap_simps Let_def)
                    apply (simp add: isPageTablePDE_def isSectionPDE_def
                                     cpde_relation_pde_case)
                    apply (intro impI conjI disjCI2, simp_all add: array_assertion_shrink_right)[1]
                    apply (clarsimp simp: pde_tag_defs  split: if_split bool.split)
                    apply (frule pde_pde_section_size_0_1[simplified pde_tag_defs, simplified], simp)
                   apply ceqv
                  apply (simp add: from_bool_0 del: Collect_const)
                  apply (rule ccorres_from_vcg_might_throw[where P=\<top> and P'=UNIV])
                  apply (rule allI, rule conseqPre, vcg)
                  apply (clarsimp simp: isPageTablePDE_def isSectionPDE_def
                                        fst_throwError_returnOk
                                 split: ARM_HYP_H.pde.split)
                  apply (auto simp: exception_defs syscall_error_rel_def
                                    syscall_error_to_H_cases)[1]
                 apply wp
                apply (simp add: guard_is_UNIV_def)
               apply (clarsimp simp: upto_enum_step_def)
               apply (frule_tac n3="Suc o unat o i_'" in array_assertion_abs_pde_16_const[where pd=pd and vptr=vaddr,
                   simplified imp_conjL, THEN spec, THEN spec, THEN mp])
               apply (simp add: upto_enum_word unat_of_nat vmsz_aligned_def
                                superSectionPDEOffsets_def table_bits_defs
                                vmsz_aligned'_def split: if_split_asm)
                apply (clarsimp simp add: typ_heap_simps' add.commute)
                apply (simp add: upto_enum_step_def upto_enum_word)
               apply (clarsimp simp add: typ_heap_simps' add.commute)
               apply (simp add: upto_enum_step_def upto_enum_word)
              apply simp
             apply (rule conseqPre, vcg)
             apply clarsimp
            apply simp
            apply (wp getPDE_wp | wpc)+
            apply simp
           apply (simp add: upto_enum_step_def word_bits_def split: if_split)
          apply clarsimp
         apply ceqv
        apply csymbr
        apply (rule ccorres_return_CE, simp+)[1]
       apply wp
      apply (simp add: ccHoarePost_def isRight_def xfdc_def)
      apply (rule HoarePartial.SeqSwap)
       apply (rule_tac Q="\<lbrace>Bonus \<acute>i \<longrightarrow> Prop \<acute>ret___struct_create_mappings_pde_return_C\<rbrace>"
                   and I="\<lbrace>Prop \<acute>ret___struct_create_mappings_pde_return_C\<rbrace>"
                 for Bonus Prop
                 in HoarePartial.reannotateWhileNoGuard)
       apply (rule HoarePartial.While[OF order_refl])
        apply (rule conseqPre, vcg)
        apply clarsimp
       apply clarsimp
      apply vcg
     apply (clarsimp simp: pde_range_relation_def)
     apply vcg
    apply (rule conseqPre, vcg, clarsimp)
   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
   apply simp
  apply (clarsimp simp: vmsz_aligned'_def gen_framesize_to_H_def vm_page_size_defs
                        vm_attribs_relation_def
                        from_bool_mask_simp[unfolded mask_def, simplified]
                        ptr_range_to_list_def upto_enum_step_def upto_enum_word
                  cong: if_cong)
  apply (frule(1) page_directory_at_rf_sr, clarsimp)
  apply (frule array_ptr_valid_array_assertionD[OF h_t_valid_clift])
  apply (clarsimp simp:ARMSuperSectionBits_def
    ARMSectionBits_def word_0_sle_from_less
    table_bits_defs)
  apply (rule conjI)
   apply (simp add: cpde_relation_def)
  apply (simp add: superSectionPDEOffsets_def table_bits_defs upto_enum_step_def
                   upto_enum_def comp_def del: upt_Suc split: if_split)
  done

lemma pte_case_isLargePagePTE:
  "(case pte of LargePagePTE _ _ _ _ \<Rightarrow> P | _ \<Rightarrow> Q)
       = (if isLargePagePTE pte then P else Q)"
  by (simp add: isLargePagePTE_def split: ARM_HYP_H.pte.split)

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

lemma lookupPTSlot_le_0x3C:
  "\<lbrace>valid_objs' and K (vmsz_aligned' vptr ARMLargePage)\<rbrace>
      lookupPTSlot pd vptr \<lbrace>\<lambda>rv s. rv \<le> rv + 0x3C\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (simp add: lookupPTSlot_def cong: pde.case_cong)
  apply (rule hoare_pre)
   apply (wp getPDE_wp | wpc)+
  apply clarsimp
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: projectKOs)
  apply (clarsimp simp: valid_obj'_def table_bits_defs vmsz_aligned'_def
                        lookup_pt_slot_no_fail_def)
  apply (subgoal_tac "is_aligned (ptrFromPAddr x) 9")
   apply (rule is_aligned_no_wrap' [where sz=7])
    apply (erule aligned_add_aligned)
      apply clarsimp
      apply (rule is_aligned_andI1)
      apply clarsimp
    apply simp
   apply simp
  apply (rule is_aligned_ptrFromPAddr_n[rotated], simp)
  apply (erule is_aligned_weaken)
  apply (simp add: pteBits_def)
  done

lemma createSafeMappingEntries_PTE_ccorres:
  "ccorres (syscall_error_rel \<currency> (\<lambda>rv rv'. isLeft rv \<and> cpte_relation (fst (theLeft rv)) (fst rv')
                                         \<and> pte_range_relation (snd (theLeft rv)) (snd rv')))
     (liftxf errstate create_mappings_pte_return_C.status_C
             (\<lambda>v. (create_mappings_pte_return_C.pte_C v,
                   create_mappings_pte_return_C.pte_entries_C v))
             ret__struct_create_mappings_pte_return_C_')
     (valid_objs' and page_directory_at' pd
          and (\<lambda>_. vmsz_aligned' vaddr vsz \<and> vmsz_aligned' base vsz
                        \<and> is_aligned pd pdBits))
     (UNIV \<inter> {s. base_' s = base} \<inter> {s. vaddr_' s = vaddr}
           \<inter> {s. frameSize_' s = framesize_from_H vsz
                   \<and> (vsz = ARMSmallPage \<or> vsz = ARMLargePage)}
           \<inter> {s. vmrights_to_H (vmRights_' s) = vrights \<and> vmRights_' s < 4}
           \<inter> {s. vm_attribs_relation attr (attr_' s)}
           \<inter> {s. pd_' s = pde_Ptr pd}) []
     (createSafeMappingEntries base vaddr vsz vrights attr pd)
     (Call createSafeMappingEntries_PTE_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: base_' vaddr_' frameSize_' vmRights_' attr_' pd_')
   apply (simp add: createSafeMappingEntries_def createMappingEntries_def
                    ensureSafeMapping_def framesize_from_H_eqs
               del: Collect_const)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: bindE_assoc mapME_x_def sequenceE_x_def
                     pte_case_isLargePagePTE)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply csymbr
    apply csymbr
    apply (rule ccorres_rhs_assoc2)
    apply (rule ccorres_symb_exec_r)
      apply (simp only: lookupError_injection)
      apply (ctac add: ccorres_injection_handler_csum1
                         [OF lookupPTSlot_ccorres])
         apply (simp add: Collect_False liftE_bindE del: Collect_const)
         apply csymbr
         apply (rule ccorres_pre_getObject_pte)
         apply (rule ccorres_add_return)

         (* group C side calculation of whether pte is a large page pte : \<not>invalid and CN bit set *)
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_rhs_assoc2)
         apply (rule_tac xf'="ret__int_'"
                      and r'="\<lambda>_ rv'. rv' = from_bool (isLargePagePTE rva)"
                      in ccorres_split_nothrow[where F=UNIV])
             apply (rule_tac P="ko_at' rva rv" in ccorres_from_vcg[where P'=UNIV])
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: return_def)
             apply (drule obj_at_ko_at', clarsimp)
             apply (erule cmap_relationE1[OF rf_sr_cpte_relation], erule ko_at_projectKO_opt)
             apply (clarsimp simp: typ_heap_simps cpte_relation_def Let_def)
             apply (case_tac rva
                    ; fastforce simp: pte_lifts isLargePagePTE_def pte_pte_small_lift_def)
            apply ceqv
           apply (clarsimp simp del: Collect_const)
           (* the if/IF condition is now the same on both sides *)
           apply (simp add: pte_case_isLargePagePTE if_to_top_of_bindE del: Collect_const)
           apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
              apply vcg
             apply simp
            apply simp
            apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: fst_throwError_returnOk
                                  exception_defs syscall_error_to_H_cases
                                  syscall_error_rel_def)
          apply simp
           apply csymbr
           apply (rule ccorres_return_CE, simp+)[1]
          apply (simp only: pred_conj_def simp_thms)
          apply wp
         apply (simp add: isLeft_def)
         apply vcg
        apply simp
        apply (rule_tac P'="{s. lu_ret___struct_lookupPTSlot_ret_C = errstate s}"
                   in ccorres_from_vcg_split_throws [where P=\<top>])
         apply vcg
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: fst_throwError_returnOk syscall_error_to_H_cases
                              syscall_error_rel_def exception_defs)
        apply (erule lookup_failure_rel_fault_lift[rotated])
        apply (simp add: exception_defs)
       apply simp
       apply wp
      apply simp
      apply (vcg exspec=lookupPTSlot_modifies)
     apply simp
     apply vcg
    apply (rule conseqPre, vcg, clarsimp)

   apply (rule ccorres_Cond_rhs)
    apply (simp add: ARMLargePageBits_def ARMSmallPageBits_def word_0_sle_from_less)
    apply ccorres_rewrite
    apply (rule ccorres_rhs_assoc)+
    apply (simp add: lookupError_injection bindE_assoc del: Collect_const)
    apply csymbr
    apply csymbr
    apply csymbr
    apply csymbr

    apply (rule ccorres_rhs_assoc2)
    apply (rule ccorres_symb_exec_r)
      apply (ctac add: ccorres_injection_handler_csum1
                             [OF lookupPTSlot_ccorres])
         apply (simp add: Collect_False del: Collect_const)
         apply csymbr
         apply (simp add: mapME_x_sequenceE bindE_assoc
                     del: Collect_const)
         apply (rule_tac P="\<not> rv + 0x3C < rv" in ccorres_gen_asm) (* FIXME ARMHYP 3C? *)
         apply (rule_tac P="is_aligned rv 7" in ccorres_gen_asm)
         apply clarsimp
         apply (rule ccorres_rhs_assoc2, rule ccorres_splitE)
             apply (simp only: whileAnno_def)
             apply (rule_tac xf'=xfdc and r'=dc and F="\<lambda>_. page_table_at' (rv && ~~ mask ptBits)"
                        and Q="{s. pte_range_C.base_C (pte_entries_C
                                     (ret___struct_create_mappings_pte_return_C_' s))
                                       = Ptr rv}"
                       in ccorres_sequenceE_while)
                  apply (clarsimp simp: liftE_bindE)
                  apply (clarsimp simp: largePagePTEOffsets_def[simplified pteBits_def])
                  apply (rule ccorres_symb_exec_l'[OF _ _ hoare_vcg_conj_lift[OF getObject_obj_at' getObject_inv, simplified]])
                       apply (rule ccorres_from_vcg_might_throw)
                       apply (rule allI, rule conseqPre, vcg)
                       apply clarsimp
                       apply (simp add: upto_enum_step_def upto_enum_word)
                       apply (clarsimp simp: fst_throwError_returnOk
                                             inr_rrel_def syscall_error_rel_def
                                             syscall_error_to_H_cases exception_defs pte_lifts
                                      split: pte.split)
                       apply (subst array_assertion_abs_pte_16[rule_format], erule conjI,
                         clarsimp simp: unat_of_nat)+

                       apply (drule obj_at_ko_at', clarsimp)
                       apply (erule cmap_relationE1[OF rf_sr_cpte_relation],
                              erule ko_at_projectKO_opt)
                       apply (auto simp: typ_heap_simps cpte_relation_def
                                         Let_def pte_lift_def pte_tag_defs table_bits_defs
                                         add.commute pte_lifts if_1_0_0 pte_pte_small_lift_def
                                  intro: typ_heap_simps split: if_split_asm)[1]

                      apply (wp getObject_inv loadObject_default_inv | simp)+
                    apply (simp add: objBits_simps archObjSize_def table_bits_defs)
                   apply (simp add: loadObject_default_inv)
                  apply (simp add: empty_fail_getObject)
                 apply (simp add: upto_enum_step_def upto_enum_word
                           split: if_split)
                apply (rule conseqPre, vcg)
                apply (clarsimp simp: pte_tag_defs if_1_0_0)
               apply (wp getPTE_wp | simp | wpc)+
              apply (simp add: upto_enum_step_def upto_enum_word
                               word_bits_def
                        split: if_split)
             apply simp
            apply (rule ceqv_refl)
           apply csymbr
           apply (rule ccorres_return_CE, simp+)[1]
          apply wp
         apply (simp add: isLeft_def ccHoarePost_def xfdc_def
                          upto_enum_step_def)
         apply (rule HoarePartial.SeqSwap)
          apply (rule_tac Q="\<lbrace>Bonus \<acute>i \<longrightarrow> Prop \<acute>ret___struct_create_mappings_pte_return_C\<rbrace>"
                      and I="\<lbrace>Prop \<acute>ret___struct_create_mappings_pte_return_C\<rbrace>"
                      for Bonus Prop
                       in HoarePartial.reannotateWhileNoGuard)
          apply (rule HoarePartial.While[OF order_refl])
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: pte_tag_defs if_1_0_0)
          apply clarsimp
         apply vcg
        apply simp
        apply (rule_tac P'="{s. lu_ret___struct_lookupPTSlot_ret_C = errstate s}"
                   in ccorres_from_vcg_split_throws [where P=\<top>])
         apply vcg
        apply (rule conseqPre, vcg)
        apply (clarsimp simp: fst_throwError_returnOk syscall_error_rel_def
                              syscall_error_to_H_cases exception_defs)
        apply (erule lookup_failure_rel_fault_lift[rotated])
        apply (simp add: exception_defs)
       apply (wp injection_wp[OF refl])
       apply (simp add: linorder_not_less ptBits_eq)
       apply (wp lookupPTSlot_le_0x3C lookupPTSlot_page_table_at' Arch_R.lookupPTSlot_aligned)
      apply simp
      apply (vcg exspec=lookupPTSlot_modifies)
     apply simp
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
   apply simp
  apply (clarsimp simp: gen_framesize_to_H_def vm_page_size_defs
                        vm_attribs_relation_def
                        from_bool_mask_simp[unfolded mask_def, simplified])
  apply (clarsimp simp: typ_heap_simps pte_range_relation_def
                        ptr_range_to_list_def upto_enum_word)
  apply (simp add: cpte_relation_def pte_tag_defs table_bits_defs largePagePTEOffsets_def)
  apply (auto simp: vmsz_aligned'_def upto_enum_step_def upto_enum_def)[1]
  done

lemma ptr_add_uint_of_nat [simp]:
  "a  +\<^sub>p uint (of_nat b :: word32) = a  +\<^sub>p (int b)"
  by (clarsimp simp: CTypesDefs.ptr_add_def)


declare int_unat[simp]

definition
 "valid_pte_slots'2 slots \<equiv>
    \<lambda>s. case slots of Inl (pte,xs) \<Rightarrow> (\<exists>sz. sz \<le> 4 \<and> length xs = 2^sz \<and> is_aligned (hd xs) (sz+3)
        \<and> (page_table_at' (hd xs && ~~ mask ptBits) s)
        \<and> (sz = 0 \<or> sz = 4)
        \<and> (if sz = 0 then is_aligned (pteFrame pte) (pageBitsForSize ARMSmallPage) \<and> \<not>isLargePagePTE pte
                     else is_aligned (pteFrame pte) (pageBitsForSize ARMLargePage) \<and> isLargePagePTE pte))
        \<and> pte \<noteq> InvalidPTE
     | Inr _ => True"

lemma valid_pte_slots_lift2:
  "\<lbrakk> \<And>pt. \<lbrace> page_table_at' pt \<rbrace> f \<lbrace> \<lambda>_. page_table_at' pt \<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace> valid_pte_slots'2 slots \<rbrace> f \<lbrace> \<lambda>_. valid_pte_slots'2 slots \<rbrace>"
  apply (cases slots, simp_all add: valid_pte_slots'2_def hoare_post_taut)
  apply clarsimp
  apply (wp hoare_vcg_ex_lift hoare_vcg_conj_lift | assumption)+
  done

definition
 "valid_pde_slots'2 slots \<equiv> \<lambda>s. case slots of Inl _ \<Rightarrow> True
     | Inr (pde, xs) \<Rightarrow> (\<forall>x \<in> set xs. valid_pde_mapping_offset' (x && mask pdBits))
                       \<and> page_directory_at' (hd xs && ~~ mask pdBits) s
                       \<and> (case pde of InvalidPDE \<Rightarrow> False | PageTablePDE _ \<Rightarrow> False | _ \<Rightarrow> True)
                       \<and> (\<exists>sz. sz \<le> 4 \<and> length xs = 2^sz \<and> is_aligned (hd xs) (sz+3)
                          \<and> (sz = 0 \<or> sz = 4)
                          \<and> (if sz = 0 then is_aligned (pdeFrame pde) (pageBitsForSize ARMSection) \<and> \<not>isSuperSectionPDE pde
                                       else is_aligned (pdeFrame pde) (pageBitsForSize ARMSuperSection) \<and> isSuperSectionPDE pde))"


lemma valid_pde_slots_lift2:
  "\<lbrakk> \<And>pd. \<lbrace> page_directory_at' pd \<rbrace> f \<lbrace> \<lambda>_. page_directory_at' pd \<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace> valid_pde_slots'2 slots \<rbrace> f \<lbrace> \<lambda>_. valid_pde_slots'2 slots \<rbrace>"
  apply (cases slots, simp_all add: valid_pde_slots'2_def hoare_post_taut)
  apply clarsimp
  apply (wp hoare_vcg_ex_lift hoare_vcg_conj_lift | assumption)+
  done

lemma obj_at_pte_aligned:
  "obj_at' (\<lambda>a::ARM_HYP_H.pte. True) ptr s ==> is_aligned ptr 2"
  apply (drule obj_at_ko_at')
  apply (clarsimp dest!:ko_at_is_aligned'
                  simp: objBits_simps archObjSize_def table_bits_defs
                  elim!: is_aligned_weaken)
  done

lemma pteCheckIfMapped_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_' \<top>
    (UNIV \<inter> {s. pte___ptr_to_struct_pte_C_' s = Ptr slot}) []
    (pteCheckIfMapped slot)
    (Call pteCheckIfMapped_'proc)"
  apply (cinit lift: pte___ptr_to_struct_pte_C_')
   apply (rule ccorres_pre_getObject_pte)
   apply (rule_tac P'="{s. \<exists>pte'. cslift s (pte_Ptr slot) = Some pte' \<and> cpte_relation rv pte'}"
     in ccorres_from_vcg_throws[where P="\<lambda>s. True"])
   apply simp_all
  apply clarsimp
  apply (rule conseqPre, vcg)
  apply (clarsimp simp: typ_heap_simps' return_def)
  apply (case_tac rv, simp_all add: isInvalidPTE_def pte_tag_defs pte_pte_invalid_def
                                    cpte_relation_def pte_get_tag_def pte_lift_def Let_def
                             split: if_split_asm)
  done

lemma cpde_relation_invalid:
 "cpde_relation pdea pde \<Longrightarrow> (pde_get_tag pde = scast pde_pde_invalid) = isInvalidPDE pdea"
  apply (simp add: cpde_relation_def Let_def)
  apply (simp add: pde_pde_invalid_lift)
  apply (case_tac pdea, simp_all add: isInvalidPDE_def) [1]
   apply clarsimp
  apply (simp add: pde_pde_invalid_lift_def)
  done

lemma pdeCheckIfMapped_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_' \<top>
    (UNIV \<inter> {s. pde___ptr_to_struct_pde_C_' s = Ptr slot}) []
    (pdeCheckIfMapped slot)
    (Call pdeCheckIfMapped_'proc)"
  apply (cinit lift: pde___ptr_to_struct_pde_C_')
   apply (rule ccorres_pre_getObject_pde)
   apply (rule_tac P'="{s. \<exists>pde'. cslift s (pde_Ptr slot) = Some pde' \<and> cpde_relation pd pde'}"
     in ccorres_from_vcg_throws[where P="\<lambda>s. True"])
   apply simp_all
  apply clarsimp
  apply (rule conseqPre, vcg)
  apply (clarsimp simp: typ_heap_simps' return_def)
  apply (case_tac pd, simp_all add: cpde_relation_invalid isInvalidPDE_def
                             split: if_split)
  done


lemma array_assertion_abs_pte_16_mv_aligned:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_table_at' (ptr_val ptPtr && ~~ mask ptBits) s)
        \<and> (n s' \<le> 16 \<and> (x s' \<noteq> k \<longrightarrow> is_aligned (ptr_val ptPtr) 7 \<and> n s' \<noteq> 0))
    \<longrightarrow> (x s' = k \<or> array_assertion (ptPtr :: pte_C ptr) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  by (metis array_assertion_abs_pte_16)

(* FIXME: 16_2 is a terrible name, on ARM HYP it might be 16_3 except the "2" doesn't seem to
          mean anything *)
lemmas ccorres_move_array_assertion_pte_16_2
    = ccorres_move_array_assertions[OF array_assertion_abs_pte_16_mv_aligned]

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

lemma pageBitsForSize_le_32: "of_nat (pageBitsForSize x) < (32::machine_word)"
  by (cases x; simp)

lemma pte_sadness:
  "\<lbrakk> pte' = pte\<lparr>pte_pte_small_CL.address_CL := pte_pte_small_CL.address_CL pte'\<rparr>;
     f (pte_pte_small_CL.address_CL pte) = pte_pte_small_CL.address_CL pte \<rbrakk>
   \<Longrightarrow> pte'\<lparr>pte_pte_small_CL.address_CL := f (pte_pte_small_CL.address_CL pte)\<rparr> = pte"
  apply (cases pte', cases pte, simp)
  done

lemma pte_lift_to_small:
  "pte_lift pte = Some (Pte_pte_small pte') \<Longrightarrow> pte_pte_small_lift pte = pte'"
  by (simp add: pte_pte_small_lift_def)

lemma pte_lift_to_tag:
  "pte_lift pte = Some (Pte_pte_small pte') \<Longrightarrow> pte_get_tag pte = scast pte_pte_small"
  by (simp add: pte_lift_def Let_def split: if_split_asm)

lemmas pte_lift_small = pte_lift_to_small pte_lift_to_tag

(* 16 entries for a large page, each 8 bytes = 128 bytes total *)
lemma performPageInvocationMapPTE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 127 \<le> gsMaxObjectSize s)
           and valid_pte_slots'2 mapping and (\<lambda>_. asid \<le> mask asid_bits))
       (UNIV \<inter> {s. cpte_relation (fst (theLeft mapping)) (pte_' s)}
             \<inter> {s. pte_range_relation (snd (theLeft mapping)) (pte_entries_' s)}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. asid_' s = asid}
             \<inter> {s. isLeft mapping}) []
       (liftE (performPageInvocation (PageMap asid cap slot mapping)))
       (Call performPageInvocationMapPTE_'proc)"
  supply pageBitsForSize_le_32 [simp]
  apply (rule ccorres_gen_asm2)
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift:  pte_entries_' cap_' ctSlot_' asid_')
   apply (rule_tac P="\<exists>s. valid_pte_slots'2 mapping s" in ccorres_gen_asm)
   apply (rule ccorres_gen_asm [where P ="snd (theLeft mapping)\<noteq>[]"])
   apply (ctac)
     apply wpc
      prefer 2
      apply (simp add: isLeft_def)
     apply (simp add: split_def bind_assoc)
     apply (rename_tac h_pte_slots)
     apply (ctac add: pteCheckIfMapped_ccorres)
       apply csymbr
       apply (simp add: mapM_discarded whileAnno_def Collect_False del: Collect_const)
       apply (rule ccorres_Guard_Seq)
       apply (rule ccorres_basic_srnoop2, simp)
       apply csymbr
       apply (rule ccorres_abstract_cleanup)
       apply csymbr
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac F="\<lambda>_. valid_pte_slots'2 mapping" and
                           Q="\<lbrace> cpte_relation (addPTEOffset (fst h_pte_slots) (if \<acute>i = 0 then 0 else \<acute>i - 1)) \<acute>pte \<and>
                                pteFrame (fst h_pte_slots) = ret__unsigned  \<rbrace>"
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
                                      unat_of_nat upto_enum_word ARMSmallPage_def)
                apply (case_tac h_pte; clarsimp simp: isLargePagePTE_def)
                apply (clarsimp simp: cpte_relation_def pte_lift_small)
                apply (clarsimp simp: pte_lifts split del: split_of_bool)
               apply (clarsimp simp: Kernel_C.ARMSmallPage_def)
               apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def
                                     upt_conv_Cons[where i=0] of_nat_gt_0
                                     unat_of_nat upto_enum_word pte_pte_small_lift_def)
               apply (case_tac h_pte; clarsimp simp: isLargePagePTE_def)
               apply (clarsimp simp: nth_Cons')
               apply (clarsimp simp: pte_lifts split: if_split)
               apply (rule conjI)
                apply (clarsimp simp: cpte_relation_def pte_pte_small_lift_def
                                split del: split_of_bool)
               apply (clarsimp simp: addPTEOffset_def)
               apply (clarsimp simp: cpte_relation_def pte_pte_small_lift_def
                               split del: split_of_bool)
               apply (clarsimp simp: gen_framesize_to_H_def ARMSmallPage_def addPAddr_def fromPAddr_def
                               split del: split_of_bool)
               apply (rule is_aligned_neg_mask_eq)
               apply (erule is_aligned_add_multI[where n=12, simplified]; simp)
              apply simp
              apply (clarsimp simp: valid_pte_slots'2_def pte_range_relation_def ptr_range_to_list_def)
              apply (erule disjE; clarsimp simp: unat32_eq_of_nat word_bits_def)
             apply clarsimp
             apply vcg
             apply (clarsimp simp: valid_pte_slots'2_def)
             apply (rule conjI)
              apply (clarsimp simp: ARMSmallPage_def)
             apply (rule context_conjI)
              apply (case_tac a; clarsimp simp: isLargePagePTE_def cpte_relation_def addPTEOffset_def pte_lift_small)
             apply clarsimp
             apply (rule conjI, clarsimp)
              apply (clarsimp split: if_split_asm)
               apply (case_tac a; clarsimp simp: isLargePagePTE_def)
               apply (clarsimp simp: cpte_relation_def pte_lift_small
                               split del: split_of_bool)
               apply (clarsimp simp: pte_lifts split del: split_of_bool)
              apply (case_tac a; clarsimp simp: isLargePagePTE_def)
              apply (clarsimp simp: cpte_relation_def pte_lift_small
                              split del: split_of_bool)
              apply (clarsimp simp: pte_lifts split del: split_of_bool)
             apply clarsimp
             apply (rule conjI, clarsimp)
              apply (clarsimp split: if_split_asm)
               apply (case_tac a; clarsimp simp: isLargePagePTE_def)
               apply (clarsimp simp: cpte_relation_def pte_lift_small
                               split del: split_of_bool)
               apply (clarsimp simp: pte_lifts split del: split_of_bool)
              apply (case_tac a; clarsimp simp: isLargePagePTE_def)
              apply (clarsimp simp: cpte_relation_def pte_lift_small
                              split del: split_of_bool)
              apply (clarsimp simp: pte_lifts split del: split_of_bool)
             apply (clarsimp split: if_split)
             apply (rule conjI, clarsimp)
              apply unat_arith
             apply clarsimp
             apply (erule disjE)
              apply (case_tac a; clarsimp simp: isLargePagePTE_def)
              apply (clarsimp simp: cpte_relation_def pte_lift_small
                              split del: split_of_bool)
              apply (clarsimp simp: pte_lifts split del: split_of_bool)
             apply (case_tac a; clarsimp simp: isLargePagePTE_def)
             apply (clarsimp simp: cpte_relation_def addPTEOffset_def pte_lift_small
                             split del: split_of_bool)
             apply (clarsimp simp: pte_lifts split del: split_of_bool)
             apply (clarsimp simp: ARMSmallPage_def gen_framesize_to_H_def addPAddr_def fromPAddr_def)
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
            apply (ctac (no_vcg) add: invalidateTLBByASID_ccorres)
             apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp:return_def)
            apply (rule wp_post_taut)
           apply simp
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
           apply (simp add: objBits_simps archObjSize_def pteBits_def pte_bits_def)
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
         apply (clarsimp simp: valid_pte_slots'2_def objBits_simps archObjSize_def hd_conv_nth
                               pteBits_def pte_bits_def)
         apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def ptr_add_def)
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
                             archObjSize_def pteBits_def pte_bits_def)
       apply (simp add: CTypesDefs.ptr_add_def ucast_nat_def word_0_sle_from_less)
       apply (clarsimp simp: valid_pte_slots'2_def del: disjCI)
       apply (erule disjE, simp_all add: unat_arith_simps)[1]
       apply (clarsimp simp: upt_conv_Cons[where i=0])
      apply (wp valid_pte_slots_lift2 hoare_drop_imps)
     apply vcg
    apply (wp valid_pte_slots_lift2 hoare_drop_imps hoare_vcg_all_lift)
   apply (vcg)
  apply simp
  apply (strengthen refl[where t=True] UNIV_I, simp)?
  apply (rule conjI, fastforce)
  apply (rule conjI)
   apply (clarsimp simp: pte_range_relation_def ptr_range_to_list_def unat_1_0
                         valid_pte_slots'2_def isLeft_def last_map hd_map
                         ptr_add_def)
   apply (auto elim!: order_trans[rotated] simp: unat_word_ariths unat_arith_simps)[1]
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
  done

lemma pde_align_ptBits:
  "\<lbrakk> ko_at' (ARM_HYP_H.PageTablePDE x) slot s ;valid_objs' s\<rbrakk>
  \<Longrightarrow> is_aligned (ptrFromPAddr x) ptBits"
  apply (drule ko_at_valid_objs')
    apply simp
   apply (simp add:projectKO_opts_defs injectKO_defs
    split:Structures_H.kernel_object.splits
    arch_kernel_object.splits)+
  apply (simp add:valid_obj'_def)
  apply (rule is_aligned_ptrFromPAddr_n)
   apply simp
  apply (simp add: table_bits_defs)
  done

lemma createMappingEntries_valid_pte_slots'2:
  "\<lbrace>K (vmsz_aligned' vptr sz \<and> vmsz_aligned' base sz) and valid_objs'\<rbrace>
     createMappingEntries base vptr sz vm_rights attrib pt
   \<lbrace>\<lambda>rv. valid_pte_slots'2 rv\<rbrace>,-"
  apply (simp add: createMappingEntries_def valid_pde_slots'2_def)
  apply (cases sz, simp_all)
     apply (wp | simp)+
      apply (simp add:lookupPTSlot_def)
      apply (wp getPDE_wp|wpc|simp add: checkPTAt_def valid_pte_slots'2_def)+
     apply (clarsimp simp:valid_pte_slots'2_def lookup_pt_slot_no_fail_def)
     apply (rule_tac x = 0 in exI)
     apply (clarsimp simp: ptBits_eq)
     apply (subst vaddr_segment_nonsense3_folded)
      apply (simp add: page_table_at'_def table_bits_defs)
     apply (simp add: isLargePagePTE_def)
     apply (rule conjI)
      apply (rule aligned_add_aligned[where n = 3])
        apply (drule pde_align_ptBits)
         apply simp
        apply (erule is_aligned_weaken)
        apply (simp add: table_bits_defs)
       apply (simp add: is_aligned_shiftl table_bits_defs)
      apply (simp)
     apply (simp add: vmsz_aligned'_def)
    apply (simp add:lookupPTSlot_def)
    apply (wp getPDE_wp|wpc|simp add: valid_pte_slots'2_def checkPTAt_def)+
    apply (clarsimp simp:valid_pte_slots'2_def lookup_pt_slot_no_fail_def)
    apply (rule_tac x = 4 in exI)
    apply (clarsimp simp:upto_enum_step_def split:if_splits)
    apply (clarsimp simp: largePagePTEOffsets_def length_upto_enum_step table_bits_defs)
    apply (clarsimp simp:upto_enum_step_def upto_enum_def hd_map_simp comp_def)
    apply (clarsimp simp: vmsz_aligned'_def)
    apply (subst vaddr_segment_nonsense5[simplified table_bits_defs])
     apply (erule (1) pde_align_ptBits[simplified table_bits_defs])
    apply (simp add: isLargePagePTE_def)
    apply (erule(1) aligned_add_aligned[OF pde_align_ptBits])
     apply (rule is_aligned_shiftl[OF aligned_already_mask],simp)
     apply (rule is_aligned_shiftr)
     apply simp
    apply (simp add: table_bits_defs)
   apply (wp | simp add:valid_pte_slots'2_def)+
  done

(* replay of proof in Arch_R with stronger validity result *)
lemma createMappingEntries_valid_pde_slots'2:
  "\<lbrace>page_directory_at' pd and K (vmsz_aligned' vptr sz \<and> vptr < pptrBase \<and> vmsz_aligned' base sz)\<rbrace>
     createMappingEntries base vptr sz vm_rights attrib pd
   \<lbrace>\<lambda>rv. valid_pde_slots'2 rv\<rbrace>,-"
  apply (simp add: createMappingEntries_def valid_pde_slots'2_def)
  apply (cases sz, simp_all)
     apply wpsimp+
   apply (clarsimp simp: page_directory_at'_def
                         lookup_pd_slot_eq[simplified pd_bits_def pde_bits_def])
   apply (clarsimp simp: lookup_pd_slot_def Let_def mask_add_aligned table_bits_defs)
   apply (rule conjI, erule less_pptrBase_valid_pde_offset'')
   apply (rule conjI, subst vaddr_segment_nonsense6, assumption, blast)
   apply (rule_tac x= 0 in exI)
   apply (simp add: isSuperSectionPDE_def)
   apply (rule conjI)
    apply (erule aligned_add_aligned[OF is_aligned_weaken is_aligned_shiftl, where n=3])
      apply (simp add: pdBits_def)
     apply (simp add: vmsz_aligned'_def)
    apply simp
   apply (simp add: vmsz_aligned'_def)
  apply (rule hoare_pre, wp)
  apply (clarsimp simp: vmsz_aligned'_def page_directory_at'_def lookup_pd_slot_def)
  apply (rule conjI)
   subgoal \<comment> \<open>valid_pde_mapping_offset'\<close>
     apply (clarsimp simp: superSectionPDEOffsets_def length_upto_enum_step table_bits_defs)
     apply (clarsimp simp: upto_enum_step_def upto_enum_def comp_def)
     apply (clarsimp simp: linorder_not_less field_simps mask_add_aligned)
     apply (erule less_pptrBase_valid_pde_offset'[simplified table_bits_defs], simp+)
     apply (rule word_of_nat_le, simp)
     done
  apply (rule conjI)
   subgoal \<comment> \<open>pde_at'\<close>
     apply (clarsimp simp: superSectionPDEOffsets_def length_upto_enum_step table_bits_defs)
     apply (clarsimp simp:upto_enum_step_def upto_enum_def hd_map_simp comp_def)
     apply (simp add: vaddr_segment_nonsense6)
     done
  apply (rule_tac x = 4 in exI)
  apply (clarsimp simp: superSectionPDEOffsets_def length_upto_enum_step table_bits_defs)
  apply (clarsimp simp:upto_enum_step_def upto_enum_def hd_map_simp comp_def isSuperSectionPDE_def)
  apply (erule aligned_add_aligned)
   apply (rule is_aligned_shiftl, simp)
   apply (rule is_aligned_shiftr)
   apply simp
  apply simp
  done

lemma mapM_x_storePDE_pde_mappings':
"\<lbrakk>valid_pde_slots'2 (Inr (a, b)) s; b \<noteq> []\<rbrakk> \<Longrightarrow> \<lbrace>valid_pde_mappings'\<rbrace>
          mapM_x (\<lambda>b. storePDE b a) b \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (wp mapM_x_wp')
  apply (auto simp: valid_pde_slots'2_def valid_pde_mapping'_def)
  done

lemma array_assertion_abs_pde_16_no_lookup:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_directory_at' (ptr_val ptr && ~~ mask pdBits) s)
        \<and> (n s' \<le> 16 \<and> (x s' \<noteq> k \<longrightarrow> n s' \<noteq> 0 \<and> is_aligned (ptr_val ptr) 7))
    \<longrightarrow> (x s' = k \<or> array_assertion (ptr :: pde_C ptr) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (frule(1) page_directory_at_rf_sr, clarsimp)
  apply (erule clift_array_assertion_imp, simp_all)
  apply (rule_tac x="unat ((ptr_val ptr && mask pdBits) >> 3)" in exI)
  apply (simp add: shiftl_t2n[where n=3, symmetric, THEN trans[rotated],
                   OF mult.commute, simplified])
  apply (cases ptr, simp add: shiftr_shiftl1)
  apply (rule conjI, rule trans,
         rule word_plus_and_or_coroll2[symmetric, where w="mask pdBits"])
   apply (simp, rule is_aligned_neg_mask_eq[THEN sym], rule is_aligned_andI1,
          erule is_aligned_weaken, simp)
  apply (rule order_trans, erule add_mono[OF order_refl], simp)
  apply (rule unat_le_helper)
  apply (simp add: is_aligned_mask mask_def table_bits_defs)
  apply (word_bitwise, simp?)
  done

lemmas ccorres_move_array_assertion_pde_16_2
    = ccorres_move_array_assertions[OF array_assertion_abs_pde_16_no_lookup]

lemma storePDE_Basic_ccorres'':
  "ccorres dc xfdc
     (\<lambda>_. valid_pde_mapping_offset' (p && mask pdBits))
     {s. ptr_val (f s) = p \<and> cpde_relation pde pde'} hs
     (storePDE p pde)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c f s}
        (Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (f s) pde'))) s)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_gen_asm2, erule storePDE_Basic_ccorres')
  apply simp
  done

lemma pde_lift_to_section:
  "pde_lift pde = Some (Pde_pde_section pde') \<Longrightarrow> pde_pde_section_lift pde = pde'"
  by (simp add: pde_pde_section_lift_def)

lemma pde_lift_to_tag:
  "pde_lift pde = Some (Pde_pde_section pde') \<Longrightarrow> pde_get_tag pde = scast pde_pde_section"
  by (simp add: pde_lift_def Let_def split: if_split_asm)

lemmas pde_lift_section = pde_lift_to_section pde_lift_to_tag

lemma performPageInvocationMapPDE_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_at' slot and (\<lambda>s. 127 \<le> gsMaxObjectSize s)
              and valid_pde_slots'2 mapping and (\<lambda>s. asid \<le> mask asid_bits))
       (UNIV \<inter> {s. cpde_relation (fst (theRight mapping)) (pde_' s)}
             \<inter> {s. pde_range_relation (snd (theRight mapping)) (pde_entries_' s)}
             \<inter> {s. ccap_relation cap (cap_' s)}
             \<inter> {s. ctSlot_' s = cte_Ptr slot}
             \<inter> {s. asid_' s = asid}
             \<inter> {s. isRight mapping}) []
       (liftE (performPageInvocation (PageMap asid cap slot mapping)))
       (Call performPageInvocationMapPDE_'proc)"
  supply pageBitsForSize_le_32 [simp]
  apply (rule ccorres_gen_asm2)
  apply (rule ccorres_gen_asm)
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift:  pde_entries_' cap_' ctSlot_' asid_')
   apply (rule_tac P="\<exists>s. valid_pde_slots'2 mapping s" in ccorres_gen_asm)
   apply (rule ccorres_gen_asm [where P ="snd (theRight mapping)\<noteq>[]"])
   apply (ctac)
     apply wpc
      apply (simp add: isRight_def)
     apply (simp add: split_def bind_assoc)
     apply (rename_tac h_pde_slots)
     apply (ctac add: pdeCheckIfMapped_ccorres)
       apply csymbr
       apply (simp add: mapM_discarded whileAnno_def Collect_False del: Collect_const)
       apply (rule ccorres_Guard_Seq)
       apply (rule ccorres_basic_srnoop2, simp)
       apply csymbr
       apply (rule ccorres_abstract_cleanup)
       apply csymbr
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac F="\<lambda>_. valid_pde_slots'2 mapping" and
                           Q="\<lbrace> cpde_relation (addPDEOffset (fst h_pde_slots) (if \<acute>i = 0 then 0 else \<acute>i - 1)) \<acute>pde \<and>
                                pdeFrame (fst h_pde_slots) = ret__unsigned \<rbrace>"
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
                                      unat_of_nat upto_enum_word ARMSection_def mask_def[of 2])
                apply (case_tac h_pde; clarsimp simp: isSuperSectionPDE_def)
                apply (clarsimp simp: cpde_relation_def pde_lift_section)
                apply (clarsimp simp: pde_lifts)
               apply (clarsimp simp: Kernel_C.ARMSection_def mask_def[of 2])
               apply (clarsimp simp: pde_range_relation_def ptr_range_to_list_def
                                     upt_conv_Cons[where i=0] of_nat_gt_0
                                     unat_of_nat upto_enum_word pde_pde_section_lift_def)
               apply (case_tac h_pde; clarsimp simp: isSuperSectionPDE_def)
               apply (clarsimp simp: nth_Cons')
               apply (clarsimp simp: pde_lifts split: if_split)
               apply (rule conjI)
                apply (clarsimp simp: cpde_relation_def pde_pde_section_lift_def
                                split del: split_of_bool)
               apply (clarsimp simp: addPDEOffset_def)
               apply (clarsimp simp: cpde_relation_def pde_pde_section_lift_def
                               split del: split_of_bool)
               apply (clarsimp simp: gen_framesize_to_H_def ARMLargePage_def ARMSection_def
                                     ARMSmallPage_def addPAddr_def fromPAddr_def)
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
              apply (clarsimp simp: ARMSection_def mask_def)
             apply (rule context_conjI)
              apply (case_tac a; clarsimp simp: isSuperSectionPDE_def cpde_relation_def addPDEOffset_def pde_lift_section)
             apply clarsimp
             apply (rule conjI, clarsimp)
              apply (clarsimp split: if_split_asm)
               apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
               apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
               apply (clarsimp simp: pde_lifts split del: split_of_bool cong: conj_cong)
              apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
              apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
              apply (clarsimp simp: pde_lifts split del: split_of_bool)
             apply clarsimp
             apply (rule conjI, clarsimp)
              apply (clarsimp split: if_split_asm)
               apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
               apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
               apply (clarsimp simp: pde_lifts split del: split_of_bool)
              apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
              apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
              apply (clarsimp simp: pde_lifts split del: split_of_bool)
             apply (clarsimp split: if_split)
             apply (rule conjI, clarsimp)
              apply unat_arith
             apply clarsimp
             apply (erule disjE)
              apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
              apply (clarsimp simp: cpde_relation_def pde_lift_section split del: split_of_bool)
              apply (clarsimp simp: pde_lifts split del: split_of_bool)
             apply (case_tac a; clarsimp simp: isSuperSectionPDE_def)
             apply (clarsimp simp: cpde_relation_def addPDEOffset_def pde_lift_section split del: split_of_bool)
             apply (clarsimp simp: pde_lifts split del: split_of_bool)
             apply (clarsimp simp: ARMSection_def ARMLargePage_def ARMSmallPage_def
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
            apply (ctac (no_vcg) add: invalidateTLBByASID_ccorres)
             apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp:return_def)
            apply (rule wp_post_taut)
           apply simp
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
           apply (simp add: objBits_simps archObjSize_def pdeBits_def pde_bits_def)
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
                               objBits_simps archObjSize_def hd_conv_nth pdeBits_def pde_bits_def)
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
                             archObjSize_def pdeBits_def pde_bits_def)
       apply (simp add: CTypesDefs.ptr_add_def ucast_nat_def word_0_sle_from_less)
       apply (clarsimp simp: valid_pde_slots'2_def del: disjCI)
       apply (erule disjE, simp_all add: unat_arith_simps)[1]
       apply (clarsimp simp: upt_conv_Cons[where i=0])
      apply (wp valid_pde_slots_lift2 hoare_drop_imps)
     apply vcg
    apply (wp valid_pde_slots_lift2 hoare_drop_imps hoare_vcg_all_lift)
   apply vcg
  apply simp
  apply (strengthen refl[where t=True] UNIV_I, simp)?
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
         apply (clarsimp simp: msgInfoRegister_def ARM_HYP.msgInfoRegister_def
                               Kernel_C.msgInfoRegister_def Kernel_C.R1_def)
         apply (vcg exspec=setMR_modifies)
        apply wpsimp
       apply clarsimp
       apply (vcg exspec=setRegister_modifies)
      apply wpsimp
     apply (clarsimp simp: ThreadState_Running_def)
     apply (vcg exspec=lookupIPCBuffer_modifies)
    apply clarsimp
    apply vcg
   apply clarsimp
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: invs_no_0_obj' tcb_at_invs' invs_queues invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        seL4_MessageInfo_lift_def message_info_to_H_def mask_def)
  apply (cases isCall)
   apply (auto simp: ARM_HYP.badgeRegister_def ARM_HYP_H.badgeRegister_def Kernel_C.badgeRegister_def
                     Kernel_C.R0_def fromPAddr_def ThreadState_Running_def
                     pred_tcb_at'_def obj_at'_def projectKOs ct_in_state'_def)
  done

lemma vmsz_aligned_addrFromPPtr':
  "vmsz_aligned' (addrFromPPtr p) sz = vmsz_aligned' p sz"
  apply (simp add: vmsz_aligned'_def)
  apply (rule iffI)
   apply (simp add: addrFromPPtr_def is_aligned_mask)
   apply (prop_tac "pptrBaseOffset AND mask (pageBitsForSize sz) = 0")
    apply (rule mask_zero[OF is_aligned_weaken[OF pptrBaseOffset_aligned]], simp)
   apply (simp flip: mask_eqs(8))
  apply (erule is_aligned_addrFromPPtr_n)
  apply (cases sz; clarsimp)
  done

lemmas vmsz_aligned_addrFromPPtr
    = vmsz_aligned_addrFromPPtr'
      vmsz_aligned_addrFromPPtr'[unfolded addrFromPPtr_def]
      vmsz_aligned_addrFromPPtr'[unfolded vmsz_aligned'_def]
      vmsz_aligned_addrFromPPtr'[unfolded addrFromPPtr_def vmsz_aligned'_def]

lemma gen_framesize_to_H_eq_from_H':
  "v < 4 \<Longrightarrow> (v' = gen_framesize_to_H v) = (framesize_from_H v' = v)"
  apply (simp add: gen_framesize_to_H_def framesize_from_H_eqs
            split: if_split)
  apply (clarsimp simp: framesize_from_H_eqs[symmetric] vm_page_size_defs)
  apply unat_arith
  done

lemma gen_framesize_to_H_eq_from_H:
  assumes v: "v < 4" shows
  "(v' = gen_framesize_to_H v) = (framesize_from_H v' = v)"
  "(gen_framesize_to_H v = v') = (v = framesize_from_H v')"
  using gen_framesize_to_H_eq_from_H'[OF v, where v'=v']
  by auto

lemmas framesize_from_H_simps
    = framesize_from_H_def[split_simps vmpage_size.split]

lemma framesize_from_H_eq_eq:
  "(framesize_from_H v = v') = (v' < 4 \<and> gen_framesize_to_H v' = v)"
  apply (rule iffI)
   apply (clarsimp simp: framesize_from_to_H)
   apply (simp add: framesize_from_H_def vm_page_size_defs split: vmpage_size.split)
  apply (clarsimp simp: gen_framesize_to_H_eq_from_H)
  apply (simp add: gen_framesize_to_H_def framesize_from_H_def split: if_split)
  apply (clarsimp simp: vm_page_size_defs)
  apply unat_arith
  done

lemmas framesize_from_H_eq_eqs = framesize_from_H_eq_eq trans [OF eq_commute framesize_from_H_eq_eq]

lemma generic_frame_cap_set_capFMappedAddress_ccap_relation:
  "\<lbrakk> cap_lift c'' = generic_frame_cap_set_capFMappedAddress_CL (cap_lift c') asid addr;
     ccap_relation c c'; isArchPageCap c; asid \<le> mask asid_bits; asid \<noteq> 0;
     vmsz_aligned' addr (gen_framesize_to_H (generic_frame_cap_get_capFSize_CL (cap_lift c')))
      \<rbrakk>
        \<Longrightarrow> ccap_relation (capCap_update (capVPMappedAddress_update (\<lambda>_. Some (asid, addr))) c) c''"
  apply (clarsimp simp: isCap_simps)
  apply (erule ccap_relationE)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.split_asm if_split_asm)
     apply (simp_all add: ccap_relation_def generic_frame_cap_set_capFMappedAddress_CL_def
                          cap_to_H_def c_valid_cap_def cl_valid_cap_def
                          generic_frame_cap_get_capFSize_CL_def
                          shiftr_asid_low_bits_mask_asid_high_bits
                          and_not_mask[symmetric] shiftr_asid_low_bits_mask_eq_0
                   split: if_split)
     apply (fastforce simp: vmsz_aligned'_def gen_framesize_to_H_def word_plus_and_or_coroll2
                            pageBitsForSize_def is_aligned_neg_mask_weaken
                            is_aligned_neg_mask_eq field_simps
                     split: if_split_asm vmpage_size.splits)+
  done

lemma slotcap_in_mem_valid:
  "\<lbrakk> slotcap_in_mem cap slot (ctes_of s); valid_objs' s \<rbrakk>
            \<Longrightarrow> s \<turnstile>' cap"
  apply (clarsimp simp: slotcap_in_mem_def)
  apply (erule(1) ctes_of_valid')
  done

lemma ivc_label_flush_case:
  "label = ArchInvocationLabel arch_invocation_label.ARMPageUnify_Instruction \<or>
   label = ArchInvocationLabel arch_invocation_label.ARMPageCleanInvalidate_Data \<or>
   label = ArchInvocationLabel arch_invocation_label.ARMPageInvalidate_Data \<or>
   label = ArchInvocationLabel arch_invocation_label.ARMPageClean_Data
    \<Longrightarrow> (case label of
     ArchInvocationLabel arch_invocation_label.ARMPageMap \<Rightarrow> A
  |  ArchInvocationLabel arch_invocation_label.ARMPageUnmap \<Rightarrow> B
  |  ArchInvocationLabel arch_invocation_label.ARMPageUnify_Instruction \<Rightarrow> C
  |  ArchInvocationLabel arch_invocation_label.ARMPageCleanInvalidate_Data \<Rightarrow> C
  |  ArchInvocationLabel arch_invocation_label.ARMPageInvalidate_Data \<Rightarrow> C
  |  ArchInvocationLabel arch_invocation_label.ARMPageClean_Data \<Rightarrow> C
  |  ArchInvocationLabel arch_invocation_label.ARMPageGetAddress \<Rightarrow> D
  |  _  \<Rightarrow> E)
  = C"
  by (auto split: invocation_label.split arch_invocation_label.split)


lemma injection_handler_whenE:
  "injection_handler Inl (whenE a b)
   = (if a then (injection_handler Inl b)
      else (returnOk ()))"
  apply (subst injection_handler_returnOk[symmetric])
  apply (clarsimp simp: whenE_def injection_handler_def cong: if_cong)
  apply (fastforce split: if_splits)
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
  by (case_tac sz,simp_all)

lemma flushtype_relation_triv:
  "isPageFlushLabel (invocation_type label) \<or>
   isPDFlushLabel (invocation_type label)
  ==> flushtype_relation (labelToFlushType label) (ucast label)"
  by (clarsimp simp: labelToFlushType_def flushtype_relation_def
    invocation_eq_use_types ARM_HYP_H.isPageFlushLabel_def
    ARM_HYP_H.isPDFlushLabel_def
    split: flush_type.splits invocation_label.splits arch_invocation_label.splits)

lemma setVMRootForFlush_ccorres2:
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_'
       (invs' and (\<lambda>s. asid \<le> mask asid_bits))
       (UNIV \<inter> {s. pd_' s = pde_Ptr pd} \<inter> {s. asid_' s = asid}) hs
       (setVMRootForFlush pd asid) (Call setVMRootForFlush_'proc)"
  apply (cinit lift: pd_' asid_')
   apply (rule ccorres_pre_getCurThread)
   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv
               del: Collect_const)
   apply (rule ccorres_Guard_Seq)+
   apply (ctac add: getSlotCap_h_val_ccorres)
     apply csymbr
     apply csymbr
     apply (simp add: cap_get_tag_isCap_ArchObject2 if_1_0_0
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
       apply (ctac (no_vcg) add: armv_contextSwitch_ccorres)
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
  apply (clarsimp simp: Collect_const_mem if_1_0_0 word_sle_def
                        ccap_rights_relation_def cap_rights_to_H_def
                        mask_def[where n="Suc 0"] allRights_def size_of_def cte_level_bits_def
                        tcbVTableSlot_def Kernel_C.tcbVTable_def invs'_invs_no_cicd)
  apply (clarsimp simp: rf_sr_ksCurThread ptr_val_tcb_ptr_mask' [OF tcb_at_invs'])
  apply (frule cte_at_tcb_at_16'[OF tcb_at_invs'], clarsimp simp: cte_wp_at_ctes_of)
  apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
  apply (clarsimp simp: typ_heap_simps' ptr_add_assertion_positive)
  apply (clarsimp simp: tcb_cnode_index_defs
                        rf_sr_tcb_ctes_array_assertion2[OF _ tcb_at_invs',
                            THEN array_assertion_shrink_right])
  apply (case_tac "isArchObjectCap rv \<and> isPageDirectoryCap (capCap rv)")
   apply (clarsimp simp: isCap_simps(2) cap_get_tag_isCap_ArchObject[symmetric])
   apply (clarsimp simp: cap_page_directory_cap_lift cap_to_H_def
                  elim!: ccap_relationE)
   apply (simp add: to_bool_def split: if_split)
  apply (auto simp: cap_get_tag_isCap_ArchObject2)
  done


definition
  to_option :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a option"
where
  "to_option f x \<equiv> if f x then Some x else None"

definition
  resolve_ret_rel :: "(vmpage_size \<times> 32 word) option \<Rightarrow> resolve_ret_C \<Rightarrow> bool"
where
  "resolve_ret_rel \<equiv>
     \<lambda>x y. rel_option (\<lambda>rv rv'. resolve_ret_C.frameSize_C rv' = framesize_from_H (fst rv)
                              \<and> snd rv = resolve_ret_C.frameBase_C rv')
                      x (to_option (to_bool \<circ> resolve_ret_C.valid_C) y)"


lemma resolve_ret_rel_None[simp]:
  "resolve_ret_rel None y = (valid_C y = scast false)"
  by (clarsimp simp: resolve_ret_rel_def to_option_def to_bool_def split: if_splits)

lemma resolve_ret_rel_Some:
  "\<lbrakk>valid_C y = scast true;  frameSize_C y = framesize_from_H (fst x); snd x = frameBase_C y\<rbrakk>
   \<Longrightarrow> resolve_ret_rel (Some x) y"
  by (clarsimp simp: resolve_ret_rel_def to_option_def)

lemma pte_get_tag_exhaust:
  "pte_get_tag pte = 0 \<or> pte_get_tag pte = 1 \<or>  pte_get_tag pte = 2 \<or>  pte_get_tag pte = 3"
  apply (simp add: pte_get_tag_def mask_def)
  apply word_bitwise
  apply fastforce
  done

lemma pte_get_tag_alt:
  "pte_lift v = Some pteC
    \<Longrightarrow> pte_get_tag v = (case pteC of
            Pte_pte_small _ \<Rightarrow> scast pte_pte_small
          | Pte_pte_invalid \<Rightarrow> scast pte_pte_invalid)"
  by (auto simp add: pte_lift_def Let_def split: if_split_asm)

lemma c_page_sizes_noteq:
  "Kernel_C.ARMSmallPage \<noteq> Kernel_C.ARMLargePage"
  "Kernel_C.ARMLargePage \<noteq> Kernel_C.ARMSmallPage"
  by (simp_all add: ARMSmallPage_def ARMLargePage_def)

lemma c_section_sizes_noteq:
  "Kernel_C.ARMSection \<noteq> Kernel_C.ARMSuperSection"
  "Kernel_C.ARMSuperSection \<noteq> Kernel_C.ARMSection"
  by (simp_all add: ARMSection_def ARMSuperSection_def)

lemma c_pages_noteq:
  "pte_pte_invalid \<noteq> pte_pte_small"
  "pte_pte_small \<noteq> pte_pte_invalid"
  by (simp_all add: pte_pte_small_def pte_pte_invalid_def)

lemma cpte_relation_get_tag_simps:
  "cpte_relation ARM_HYP_H.InvalidPTE cpte \<Longrightarrow> pte_get_tag cpte = scast pte_pte_invalid"
  "cpte_relation (ARM_HYP_H.SmallPagePTE w x y z) cpte \<Longrightarrow> pte_get_tag cpte = scast pte_pte_small"
  "cpte_relation (ARM_HYP_H.LargePagePTE w x y z) cpte \<Longrightarrow> pte_get_tag cpte = scast pte_pte_small"
  by (clarsimp simp: cpte_relation_def pte_get_tag_alt)+

(* Note: needs valid_objs' on ARM Hypervisor since the cpte_relation says nothing about alignment
         of the page addresses - therefore the only way to ensure that a C large page is aligned
         is to appeal to validity of the PTE on the Haskell side *)
lemma resolveVAddr_ccorres:
  "ccorres resolve_ret_rel ret__struct_resolve_ret_C_'
           (page_directory_at' pd and valid_objs')
           (UNIV \<inter> {s. pd_' s = pde_Ptr pd} \<inter> {s. vaddr_' s = vaddr}) hs
     (resolveVAddr pd vaddr) (Call resolveVAddr_'proc)"
  apply (cinit lift: pd_' vaddr_')
   apply clarsimp
   apply (rule ccorres_pre_getObject_pde)
   apply csymbr+
   apply (rule ccorres_abstract_cleanup)
   apply (rule_tac P="(ret__unsigned = scast pde_pde_coarse) = (isPageTablePDE rv)"
               in ccorres_gen_asm2)
   apply (rule_tac P="isPageTablePDE rv" in ccorres_cases)
    apply (clarsimp simp: pde_tag_defs)
    apply wpc
       apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
       apply (clarsimp simp: isPageTablePDE_def split: pde.splits)
      prefer 2
      apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
      apply (clarsimp simp: isPageTablePDE_def split: pde.splits)
     prefer 2
     apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
     apply (clarsimp simp: isPageTablePDE_def split: pde.splits)
    apply (rename_tac word1)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply (rule ccorres_abstract_cleanup)
    apply (rule_tac P="(ret__unsigned = word1)" in ccorres_gen_asm2)
    apply (rule ccorres_stateAssert)
    apply clarsimp
    apply (rule_tac val="Ptr (ptrFromPAddr word1)" and R=\<top>
                  in ccorres_symb_exec_r_known_rv_UNIV[where xf'=ret__ptr_to_void_' and R'=UNIV])
       apply (vcg, clarsimp)
      apply ceqv
     apply (rule ccorres_pre_getObject_pte)
     apply (rule_tac P="page_table_at' (ptrFromPAddr word1)" in ccorres_cross_over_guard)
     apply (rule_tac P = "\<lambda>s. valid_pte' rv s"
                 and P'="{s. \<exists>v. cslift s (pte_Ptr (lookup_pt_slot_no_fail (ptrFromPAddr word1) vaddr)) = Some v
                                    \<and> cpte_relation rv v
                                    \<and> array_assertion (pte_Ptr (ptrFromPAddr word1))
                                        (2 ^ (ptBits - 3)) (hrs_htd (t_hrs_' (globals s)))}"
                  in ccorres_from_vcg_might_throw)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: pteBits_def pt_bits_def pte_bits_def typ_heap_simps' gen_framesize_to_H_def
                           c_page_sizes_noteq)
     subgoal for word1 pte \<sigma> x cpte _ tag

       apply (subgoal_tac "scast Kernel_C.ARMLargePage && mask 2 = (scast Kernel_C.ARMLargePage :: machine_word)")
        prefer 2
        apply (simp add: mask_def ARMLargePage_def)
       \<comment> \<open>reduce to resolve_ret_rel goals first\<close>
       apply (clarsimp simp: fst_return pte_get_tag_alt pt_bits_def pte_bits_def
                      split: pte.splits)
       apply (safe ; clarsimp simp: cpte_relation_get_tag_simps c_pages_noteq)
       (* 4 subgoals *)
       apply (fastforce simp: cpte_relation_def pte_pte_small_lift_def pte_lift_def Let_def mask_def
                              valid_mapping'_def framesize_from_H_simps page_base_def
                        split: if_splits intro!: resolve_ret_rel_Some
                        dest!: is_aligned_neg_mask_eq)+
       done
    apply (rule guard_is_UNIVI)
    apply (clarsimp simp: typ_heap_simps)
    apply (auto simp: ptBits_def' pageBits_def pt_bits_def pte_bits_def
               dest!: page_table_at_rf_sr
               elim: clift_array_assertion_imp)[1]
   apply (rule_tac P'="{s. \<exists>v. cslift s (pde_Ptr (lookup_pd_slot pd vaddr)) = Some v
                                \<and> cpde_relation rv v
                                \<and> ret__unsigned = pde_get_tag v}"
              in ccorres_from_vcg_might_throw[where P=\<top>])
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (clarsimp simp: isPageTablePDE_def pde_get_tag_alt pde_tag_defs cpde_relation_def
                          fst_return typ_heap_simps framesize_from_H_simps
                          pde_pde_section_lift_def
                   intro: resolve_ret_rel_Some
                   split: pde.splits)
     subgoal
       apply (fastforce simp: cpte_relation_def pte_pte_small_lift_def pte_lift_def Let_def mask_def
                              valid_mapping'_def framesize_from_H_simps
                        split: if_splits intro!: resolve_ret_rel_Some
                        dest!: is_aligned_neg_mask_eq)+
       done
     subgoal
       apply (rule conjI; clarsimp simp: ARMSuperSection_def mask_def)
       apply (rule conjI)
        apply (clarsimp simp: gen_framesize_to_H_def split: if_splits)
       apply (rule resolve_ret_rel_Some;
              clarsimp simp: framesize_from_H_simps ARMSuperSection_def)
       apply (clarsimp simp: page_base_def gen_framesize_to_H_def ARMSmallPage_def ARMLargePage_def
                             ARMSection_def mask_def)
       done
  apply clarsimp
  apply (rule conjI, fastforce elim: valid_objs_valid_pte') \<comment> \<open>valid_pte'\<close>
  apply (frule(1) page_directory_at_rf_sr)
  apply (clarsimp simp: isPageTablePDE_def pde_get_tag_alt pde_tag_defs cpde_relation_def
                        typ_heap_simps pde_pde_coarse_lift_def
                        clift_array_assertion_imp table_bits_defs Let_def
                 split: pde.splits)
  done

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
  by (cases vsz, simp_all add: pageBits_def)


lemma ptrFromPAddr_add_left:
  "ptrFromPAddr (x + y) = ptrFromPAddr x + y"
  unfolding ptrFromPAddr_def by simp

lemma cap_get_tag_PageDirectoryCap:
  "ccap_relation cap cap' \<Longrightarrow>
     (cap_get_tag cap' = SCAST(32 signed \<rightarrow> 32) cap_page_directory_cap) =
     (cap = ArchObjectCap
        (PageDirectoryCap (capPDBasePtr_CL (cap_page_directory_cap_lift cap'))
                          (if to_bool (capPDIsMapped_CL (cap_page_directory_cap_lift cap'))
                           then Some (capPDMappedASID_CL (cap_page_directory_cap_lift cap'))
                           else None)))"
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap_unfolded_H_cap)
  done

lemma ccap_relation_capPDMappedASID_liftE:
  "\<lbrakk> ccap_relation c c'; cap_get_tag c' = SCAST(32 signed \<rightarrow> 32) cap_page_directory_cap;
     capPDMappedASID (capCap c) = Some y \<rbrakk>
    \<Longrightarrow> capPDMappedASID_CL (cap_page_directory_cap_lift c') = the (capPDMappedASID (capCap c))"
  by (simp add: cap_get_tag_PageDirectoryCap split: if_splits)

lemma throwError_invocationCatch:
  "throwError a >>= invocationCatch b c d e = throwError (Inl a)"
  by (simp add: invocationCatch_def throwError_bind)

lemma decodeARMFrameInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  defines "does_not_throw args extraCaps pg_sz mapdata \<equiv>
           (mapdata = None \<longrightarrow> \<not> (ARM_HYP.pptrBase \<le> hd args + 2 ^ pageBitsForSize pg_sz - 1)) \<and>
           (mapdata \<noteq> None \<longrightarrow> (fst (the mapdata) = (the (capPDMappedASID (capCap (fst (extraCaps ! 0)))))
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
       (decodeARMMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeARMFrameInvocation_'proc)"
  supply if_cong[cong] option.case_cong[cong]
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_' current_extra_caps_' cap_' buffer_' call_'
                simp: decodeARMMMUInvocation_def decodeARMPageFlush_def)

   apply (simp add: Let_def isCap_simps invocation_eq_use_types split_def
               del: Collect_const
              cong: StateSpace.state.fold_congs globals.fold_congs
                    if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong)

   apply (rule ccorres_Cond_rhs[rotated])+
       apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
       apply (rule ccorres_equals_throwError)
        apply (fastforce simp: throwError_bind invocationCatch_def
                        split: invocation_label.split arch_invocation_label.split)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
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
     apply (rule ccorres_rhs_assoc)+
     apply csymbr+
     apply (simp add: ivc_label_flush_case decodeARMPageFlush_def
                      list_case_If2 if3_fold2
                 del: Collect_const
                cong: StateSpace.state.fold_congs globals.fold_congs
                      if_cong invocation_label.case_cong arch_invocation_label.case_cong
                      list.case_cong)
     apply (simp add: split_def case_option_If2 if_to_top_of_bind
                 del: Collect_const cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong)
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
             apply csymbr
             (* can't csymbr the IF calculation because of the function calls, but we can show
                it's the same as the condition on the Haskell side*)
             apply (rule ccorres_rhs_assoc2)
             apply (rule_tac xf'=ret__int_' and R'=UNIV and R=\<top> and
                             val="from_bool (
                                    addrFromPPtr v0 + hd args < physBase \<or>
                                    ARM_HYP_H.fromPAddr paddrTop
                                      < hd (drop (Suc 0) args) - hd args +
                                        ARM_HYP_H.fromPAddr (addrFromPPtr v0 + hd args))"
                             in ccorres_symb_exec_r_known_rv)
                apply (rule conseqPre, vcg)
                apply (clarsimp dest!: ccap_relation_PageCap_generics)
                apply (clarsimp simp: hd_drop_conv_nth hd_conv_nth)
                (* sync up preprocessor-defined number sources coming from C *)
                apply (clarsimp simp: fromPAddr_def paddrTop_def pptrBase_def pptrTop_def
                                      pptrBaseOffset_def add.commute from_bool_eq_if')
               apply ceqv

              apply (rule ccorres_if_cond_throws[rotated -1,where Q = \<top> and Q' = \<top>])
                 apply vcg
                apply (solves clarsimp)
               apply (simp add:injection_handler_throwError)
               apply (rule syscall_error_throwError_ccorres_n)
               apply (simp add: syscall_error_to_H_cases)
              apply (simp add: performARMMMUInvocations bindE_assoc)
              apply (ctac add: setThreadState_ccorres)
                apply (ctac(no_vcg) add: performPageFlush_ccorres)
                  apply (rule ccorres_gen_asm)
                  apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                  apply (rule ccorres_alternative2)
                  apply (rule ccorres_return_CE, simp+)[1]
                 apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                apply (wpsimp simp: performPageInvocation_def)
               apply simp
               apply (strengthen unat_sub_le_strg[where v="2 ^ pageBitsForSize (capVPSize cp)"])
               apply (simp add: linorder_not_less linorder_not_le order_less_imp_le)
               apply (wp sts_invs_minor')
              apply simp
              apply (vcg exspec=setThreadState_modifies)
             apply simp
             apply vcg
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
                             syscall_error_to_H_cases exception_defs)
       apply (erule lookup_failure_rel_fault_lift[rotated])
       apply (simp add: exception_defs)
      apply (wp injection_wp[OF refl])
     apply simp
      apply (vcg exspec=findPDForASID_modifies)

\<comment> \<open>ARMPageUnmap\<close>
    apply (simp add: returnOk_bind bindE_assoc
                          performARMMMUInvocations)
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

\<comment> \<open>ARMPageMap\<close>
   supply Collect_const[simp del]
   apply (rename_tac word rghts pg_sz mapdata call' buffer' cap excaps cte length___unsigned_long invLabel)
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
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_equals_throwError)
     apply (fastforce simp: throwError_bind invocationCatch_def split: list.split)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: list_case_If2 length_ineq_not_Nil linorder_class.not_less)
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
                                      \<and> (cap_get_tag rv' = scast cap_page_directory_cap
                                         \<longrightarrow> ccap_relation rv rv')"
                  and xf'=pdCap_' in ccorres_split_nothrow[where F=UNIV])
             apply (simp add: getSlotCap_def del: Collect_const)
             apply (rule ccorres_symb_exec_l[OF _ getCTE_inv getCTE_sp[where P=\<top>] empty_fail_getCTE])
             apply (rule ccorres_from_vcg[where P'=UNIV])
             apply (rule allI, rule conseqPre, vcg)
             apply (clarsimp simp: return_def cte_wp_at_ctes_of)
             apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
             apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
             apply (clarsimp simp: typ_heap_simps' split_def cap_get_tag_isCap_ArchObject2
                            dest!: ccte_relation_ccap_relation)
            apply ceqv
           apply (rule ccorres_assert2)
           apply csymbr+
           apply (simp add: whenE_bindE_throwError_to_if if_to_top_of_bind hd_conv_nth)
           (* throw if pdCap not a page directory cap *)
           apply (rule ccorres_Cond_rhs_Seq)
            apply simp
            apply (rule ccorres_equals_throwError)
             apply (fastforce simp: throwError_bind invocationCatch_def isCap_simps
                             split: list.split capability.split arch_capability.split)
            apply (rule ccorres_cond_true_seq)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           (* throw if pdCap is not mapped *)
           apply (clarsimp simp: cap_case_PageDirectoryCap2)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr+
           apply (rule ssubst[OF case_option_If2,
                              where P="\<lambda>tm. ccorres _ _ _ _ _ (bindE tm _ >>= _) _"])
           apply (simp add: if_to_top_of_bind if_to_top_of_bindE hd_conv_nth cong: conj_cong)
           apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
              apply vcg
             apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                                   to_bool_def cap_page_directory_cap_lift_def
                            elim!: ccap_relationE split: if_split)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           apply csymbr+
           apply (clarsimp simp: whenE_def)
           apply (drule_tac t="Some y" in sym)
           (* There are two paths through the cap mapping eligibility check (target asid/address for
              mapped cap, target address for not mapped case) which do not throw;
              pull the non-throwing cases together *)
           apply (rule_tac P="does_not_throw args extraCaps pg_sz mapdata" in ccorres_cases[rotated])
            (* Always throws case *)
            apply (clarsimp simp: if_to_top_of_bind if_to_top_of_bindE case_option_If2 hd_conv_nth
                            cong: conj_cong)
            apply (rule ccorres_split_throws[rotated])
             apply vcg
            apply (clarsimp simp: does_not_throw_def)
            (* is the frame cap mapped? *)
            apply (rule ccorres_Cond_rhs)
             (* frame cap is mapped: remap case *)
             apply (prop_tac "mapdata \<noteq> None", simp add: ccap_relation_mapped_asid_0)
             apply clarsimp
             apply (rule ccorres_rhs_assoc)+
             apply csymbr
             apply clarsimp
             apply (frule(2) ccap_relation_capPDMappedASID_liftE[OF _ _ sym])
             apply (frule length_ineq_not_Nil)
             apply (simp add: whenE_bindE_throwError_to_if if_to_top_of_bind)
             (* throw on mismatched ASID *)
             apply (rule ccorres_Cond_rhs_Seq)
              apply (frule ccap_relation_PageCap_generics)
              apply (drule sym[where s="Some _"])
              apply clarsimp
              apply (rule ccorres_equals_throwError[OF throwError_invocationCatch])
              apply (rule syscall_error_throwError_ccorres_n)
              apply (simp add: syscall_error_to_H_cases)
             (* throw on mismatched vaddr *)
             apply simp
             apply csymbr
             apply (frule ccap_relation_PageCap_generics)
             apply (clarsimp simp: hd_conv_nth length_ineq_not_Nil)
             apply ccorres_rewrite
             apply (rule ccorres_equals_throwError)
              apply (frule ccap_relation_PageCap_generics)
              apply (drule sym[where s="Some _"])
              apply clarsimp
              apply (rule throwError_invocationCatch)
             apply (rule syscall_error_throwError_ccorres_n)
             apply (simp add: syscall_error_to_H_cases)
            (* frame cap not mapped, check mapping *)
            (* disallow mappings above pptrBase *)
            apply clarsimp
            apply (prop_tac "mapdata = None")
             apply (simp add: ccap_relation_mapped_asid_0)
            apply clarsimp
            apply (rule ccorres_rhs_assoc)+
            apply csymbr
            apply (rule ccorres_equals_throwError[OF throwError_invocationCatch])
            apply (frule ccap_relation_PageCap_generics)
            apply clarsimp
            apply ccorres_rewrite
            apply csymbr
            apply (simp add: ARM_HYP.pptrBase_def ARM_HYP.pptrBase_def hd_conv_nth length_ineq_not_Nil)
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
                  apply (rule ccorres_rhs_assoc)+
                  apply (csymbr, clarsimp)
                  apply (prop_tac "generic_frame_cap_get_capFMappedASID_CL (cap_lift cap)
                                   = capPDMappedASID_CL (cap_page_directory_cap_lift rv')")
                   apply (drule (2) ccap_relation_capPDMappedASID_liftE)
                   apply clarsimp
                  apply (clarsimp, ccorres_rewrite)
                  apply (csymbr, clarsimp simp: hd_conv_nth length_ineq_not_Nil, ccorres_rewrite)
                  apply (rule ccorres_return_Skip)
                 apply (rule ccorres_rhs_assoc)+
                 apply (csymbr, clarsimp, ccorres_rewrite)
                 apply (csymbr,
                        simp add: ARM_HYP.pptrBase_def ARM_HYP.pptrBase_def
                                  hd_conv_nth length_ineq_not_Nil,
                        ccorres_rewrite)
                 apply (rule ccorres_return_Skip, clarsimp)
               apply clarsimp
               apply (subgoal_tac "cap_get_tag cap = SCAST(32 signed \<rightarrow> 32) cap_frame_cap
                                   \<or> cap_get_tag cap = SCAST(32 signed \<rightarrow> 32) cap_small_frame_cap",
                      force)
               apply (erule ccap_relation_frame_tags)
              apply ceqv
             apply csymbr
             apply (simp add: createSafeMappingEntries_fold lookupError_injection
                              invocationCatch_use_injection_handler injection_bindE[OF refl refl]
                              injection_handler_returnOk injection_handler_If
                              injection_handler_throwError bindE_assoc
                         cong: if_cong)
             (* throw on no pd for asid *)
             apply (ctac add: ccorres_injection_handler_csum1[OF ccorres_injection_handler_csum1,
                                                              OF findPDForASID_ccorres])
                apply (simp add: Collect_False if_to_top_of_bindE)
                (* throw on mismatched pd *)
                apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
                   apply vcg
                  apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                                        cap_page_directory_cap_lift_def
                                 elim!: ccap_relationE split: if_split)
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (simp add: syscall_error_to_H_cases)
                apply csymbr
                apply (rule ccorres_symb_exec_r)
                  apply csymbr
                  apply (simp add: bindE_assoc checkVPAlignment_def unlessE_def
                                   injection_handler_If if_to_top_of_bindE)
                  (* throw on vaddr has incorrect alignment *)
                  apply (rule ccorres_if_cond_throws2[rotated -1, where Q=\<top> and Q'=\<top>])
                     apply vcg
                    apply (clarsimp simp add: from_bool_0 vmsz_aligned'_def is_aligned_mask)
                    apply (drule ccap_relation_PageCap_generics)
                    apply (simp add: hd_conv_nth length_ineq_not_Nil)
                   apply (simp add: injection_handler_throwError throwError_bind
                                    invocationCatch_def)
                   apply (rule syscall_error_throwError_ccorres_n)
                   apply (simp add: syscall_error_to_H_cases)
                  apply csymbr+
                  apply (simp add: injection_handler_returnOk bindE_assoc)
                  (* return perform page invocation map
                     pte if frameSize is small or large, otherwise pde *)
                  apply (rule ccorres_Cond_rhs)
                   apply (rule ccorres_rhs_assoc)+
                   apply csymbr
                   (* throw on pte not free *)
                   apply (ctac add: ccorres_injection_handler_csum1[
                                      OF createSafeMappingEntries_PTE_ccorres])
                      apply (simp add: performARMMMUInvocations bindE_assoc)
                      apply ccorres_rewrite
                      apply (ctac add: setThreadState_ccorres)
                        apply (ctac(no_vcg) add: performPageInvocationMapPTE_ccorres)
                          apply (rule ccorres_gen_asm)
                          apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                          apply (rule ccorres_alternative2)
                          apply (rule ccorres_return_CE; simp)
                         apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                        apply (wpsimp simp: performPageInvocation_def)
                       apply (wp sts_invs_minor' valid_pte_slots_lift2)
                      apply (simp, vcg exspec=setThreadState_modifies)
                     apply (simp, rule ccorres_split_throws)
                      apply ccorres_rewrite
                      apply (rule ccorres_return_C_errorE, simp+)
                     apply vcg
                    apply (simp add: createSafeMappingEntries_def)
                    apply (wp injection_wp[OF refl] createMappingEntries_valid_pte_slots'2)
                   apply (simp add: all_ex_eq_helper)
                   apply (vcg exspec=createSafeMappingEntries_PTE_modifies)
                  apply (rule ccorres_rhs_assoc)+
                  apply csymbr
                  (* throw on pde not free *)
                  apply (ctac add: ccorres_injection_handler_csum1[
                                     OF createSafeMappingEntries_PDE_ccorres])
                     apply (simp add: performARMMMUInvocations bindE_assoc)
                     apply ccorres_rewrite
                     apply (ctac add: setThreadState_ccorres)
                       apply (ctac(no_vcg) add: performPageInvocationMapPDE_ccorres)
                         apply (rule ccorres_gen_asm)
                         apply (erule ssubst[OF if_P, where P="\<lambda>x. ccorres _ _ _ _ _ x _"])
                         apply (rule ccorres_alternative2)
                         apply (rule ccorres_return_CE; simp)
                        apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                       apply (wpsimp simp: performPageInvocation_def)
                      apply (wp sts_invs_minor' valid_pde_slots_lift2)
                     apply (simp, vcg exspec=setThreadState_modifies)
                    apply (simp, ccorres_rewrite, rule ccorres_return_C_errorE; simp)
                   apply (simp add: createSafeMappingEntries_def,
                                    wp injection_wp[OF refl] createMappingEntries_valid_pde_slots'2)
                  apply (simp add: all_ex_eq_helper, vcg exspec=createSafeMappingEntries_PDE_modifies)
                 apply (simp, vcg)
                apply (rule conseqPre, vcg, clarsimp)
               apply (simp, ccorres_rewrite)
               apply (rule_tac P'="{s. find_ret = errstate s}" in ccorres_from_vcg_throws[where P=\<top>])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: fst_throwError_returnOk exception_defs syscall_error_rel_def
                                     syscall_error_to_H_cases)
               apply (erule lookup_failure_rel_fault_lift[rotated], simp add: exception_defs)
              apply simp
              apply (wp injection_wp[OF refl] | wp (once) hoare_drop_imps)+
             apply (simp add: all_ex_eq_helper, vcg exspec=findPDForASID_modifies)
            apply (simp add: getSlotCap_def)
            apply (prop_tac "y = the (capPDMappedASID (capCap (fst (extraCaps ! 0))))", fastforce)
            apply (drule_tac t="Some y" in sym)
            apply (simp, rule return_inv)
           apply simp
           apply (prop_tac "y = the(capPDMappedASID (capCap (fst (extraCaps ! 0))))"; clarsimp)
           apply vcg
          apply (simp, wp (once) hoare_drop_imps, wpsimp)
         apply (clarsimp, vcg)
        apply (wpsimp, (simp, vcg exspec=getSyscallArg_modifies))+
  apply (rename_tac word rghts pg_sz mapdata call' buffer' cap excaps cte length___unsigned_long invLabel s s')
  apply (rule conjI)
   apply (clarsimp, frule cte_wp_at_eq_gsMaxObjectSize, clarsimp)
   apply (clarsimp simp: cte_wp_at_ctes_of is_aligned_mask[symmetric] vmsz_aligned'_def
                         vmsz_aligned_addrFromPPtr)
   apply (frule ctes_of_valid', clarsimp+)
   apply (drule_tac t="cteCap cte" in sym, simp)
   apply (clarsimp simp: valid_cap'_def capAligned_def mask_def[where n=asid_bits] linorder_not_le)
   apply (prop_tac "extraCaps \<noteq> [] \<longrightarrow> (s \<turnstile>' fst (extraCaps ! 0))")
    apply (clarsimp simp: neq_Nil_conv excaps_in_mem_def slotcap_in_mem_def linorder_not_le)
    apply (erule ctes_of_valid', clarsimp)
   (* Haskell side *)
   subgoal
     supply_local_method simplify_and_expand =
           (clarsimp simp: ct_in_state'_def vmsz_aligned'_def isCap_simps valid_cap'_def
                           valid_tcb_state'_def page_directory_at'_def sysargs_rel_to_n
                           linorder_not_less excaps_map_def
                 simp del: less_1_simp
            | rule conjI
            | erule pred_tcb'_weakenE disjE
            | drule st_tcb_at_idle_thread' interpret_excaps_eq)+

     apply (local_method simplify_and_expand,
            (erule order_le_less_trans[rotated] order_trans[where x=127, rotated]
             | rule order_trans[where x=127, OF _ two_nat_power_pageBitsForSize_le,
                                unfolded pageBits_def])+, simp)+
       apply (clarsimp simp: does_not_throw_def not_le word_aligned_add_no_wrap_bounded
                      split: option.splits)
      apply (clarsimp simp: neq_Nil_conv dest!: interpret_excaps_eq)
     apply (local_method simplify_and_expand,
            clarsimp simp: neq_Nil_conv,
            (solves \<open>rule word_plus_mono_right[OF word_less_sub_1], simp,
                       subst (asm) vmsz_aligned_addrFromPPtr(3)[symmetric],
                       erule is_aligned_no_wrap', clarsimp\<close>),
            intro conjI,
            (solves \<open>frule vmsz_aligned_addrFromPPtr(3)[THEN iffD2],
                       (subst mask_add_aligned mask_add_aligned_right, erule is_aligned_weaken,
                        rule order_trans[OF _ pbfs_atleast_pageBits[simplified pageBits_def]], simp)+,
                       simp\<close>),
            fastforce simp add: ptrFromPAddr_add_left is_aligned_no_overflow3[rotated -1])+
     apply (local_method simplify_and_expand)+
     done

  (* C side *)
  apply (clarsimp simp: rf_sr_ksCurThread "StrictC'_thread_state_defs" mask_eq_iff_w2p
                        word_size word_less_nat_alt from_bool_0 excaps_map_def cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (drule_tac t="cteCap ctea" in sym)
  apply (clarsimp simp: valid_cap'_def capAligned_def word_sless_def word_sle_def)
  apply (prop_tac "cap_get_tag cap \<in> {scast cap_small_frame_cap, scast cap_frame_cap}")
   apply (clarsimp simp: cap_to_H_def cap_lift_def Let_def elim!: ccap_relationE split: if_split_asm)
  apply (rule conjI)
   apply (frule ccap_relation_PageCap_generics)
   apply (clarsimp simp: word_less_nat_alt vm_attribs_relation_def attribsFromWord_def
                         framesize_from_H_eq_eqs of_bool_nth[simplified of_bool_from_bool]
                         vm_page_size_defs neq_Nil_conv excaps_in_mem_def hd_conv_nth
                         length_ineq_not_Nil numeral_2_eq_2 does_not_throw_def
                         ARM_HYP.pptrBase_def
                   simp del: unsigned_numeral)
   apply (frule interpret_excaps_eq[rule_format, where n=0], simp)
   apply (frule(1) slotcap_in_mem_PageDirectory)
   apply (clarsimp simp: mask_def[where n=4] typ_heap_simps' isCap_simps)
   apply (frule slotcap_in_mem_valid, clarsimp+)
   apply (erule_tac c="ArchObjectCap (PageDirectoryCap a b)" for a b in ccap_relationE)
   supply from_bool_odd_eq_and[simp]
   apply (case_tac mapdata
          ; (clarsimp simp: cap_lift_page_directory_cap to_bool_def cap_page_directory_cap_lift_def
                            cap_to_H_def[split_simps cap_CL.split] valid_cap'_def,
             (drule(1) generic_frame_cap_set_capFMappedAddress_ccap_relation
              ; simp add: isCap_simps mask_def),
             (simp add: gen_framesize_to_H_def vm_page_size_defs hd_conv_nth length_ineq_not_Nil
                 split: if_split_asm)))
  apply (frule ccap_relation_PageCap_generics)
  apply (clarsimp simp: signed_shift_guard_simpler_32 pbfs_less framesize_from_H_eq_eqs)
  apply (intro conjI impI)
     apply (clarsimp simp: unat_less_helper isPageFlush_def isPageFlushLabel_def dest!: at_least_2_args
            | intro flushtype_relation_triv allI impI conjI)+
  done

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
  apply (simp add: ARM_HYP_H.maskCapRights_def isPageCap_def Let_def split: arch_capability.splits)
  done


lemma isPDFlush_fold:
 "(label = ArchInvocationLabel arch_invocation_label.ARMPDUnify_Instruction \<or>
 label =   ArchInvocationLabel arch_invocation_label.ARMPDCleanInvalidate_Data \<or>
 label =   ArchInvocationLabel arch_invocation_label.ARMPDInvalidate_Data \<or>
 label =   ArchInvocationLabel arch_invocation_label.ARMPDClean_Data) = isPDFlushLabel label"
  by (simp_all add:isPDFlushLabel_def split:invocation_label.splits arch_invocation_label.splits)

lemma injection_handler_liftE:
  "injection_handler a (liftE f) = liftE f"
  by (simp add:injection_handler_def)

lemma pageBase_spec:
"\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>size && mask 2 = \<acute>size\<rbrace>
  Call pageBase_'proc
  \<lbrace> \<acute>ret__unsigned_long = \<^bsup>s\<^esup>vaddr && ~~ (2 ^ pageBitsForSize (gen_framesize_to_H \<^bsup>s\<^esup>size) - 1)\<rbrace>"
  apply vcg
  apply (simp add:pageBitsForSize_def split:vmpage_size.splits)
  done

lemma liftE_case_sum:
  "liftE f >>= case_sum (throwError \<circ> Inr) g = f >>= g"
  by (simp add:liftE_def)

crunch inv': resolveVAddr "P"
  (wp: crunch_wps simp: crunch_simps)


lemma flush_range_le:
  assumes assms:"page_base start a = page_base end a"
        "start \<le> end" "w && mask (pageBitsForSize a) = start && mask (pageBitsForSize a)"
  shows "w \<le> w + (end - start)" "unat (end - start) \<le> 2 ^ pageBitsForSize a"
proof -
  have q: "w && mask (pageBitsForSize a) \<le> (w && mask (pageBitsForSize a)) + (end - start)"
    using assms
    apply (subst AND_NOT_mask_plus_AND_mask_eq
      [where w = start,symmetric,where n = "pageBitsForSize a"])
    apply (simp add: page_base_def)
    apply (drule word_le_minus_mono_left[where x= "start && ~~ mask (pageBitsForSize a)"])
     apply (rule word_and_le2)
    apply (simp(no_asm_use), simp)
    done
  have a: "unat (w && mask (pageBitsForSize a)) + unat (end - start)
    = unat ((w && mask (pageBitsForSize a)) + (end - start))"
    apply (rule unat_plus_simple[THEN iffD1,symmetric])
    apply (rule q)
    done
  have b: "end + (start && mask (pageBitsForSize a)) - start
     = end - (start && ~~ mask (pageBitsForSize a))"
    by (simp add:mask_out_sub_mask)
  have c: "unat (w && mask (pageBitsForSize a)) + unat (end - start) < 2 ^ pageBitsForSize a"
    using assms a
    apply (simp add:field_simps)
    apply (rule unat_less_helper)
    apply simp
    apply (rule_tac P =" \<lambda>x. x < y" for y in ssubst[OF b])
    apply (subst AND_NOT_mask_plus_AND_mask_eq
      [where w = "end",symmetric,where n = "pageBitsForSize a"])
    apply (simp add:page_base_def)
    apply (rule and_mask_less')
    apply simp
    done

  show "w \<le> w + (end - start)"
    using assms
    apply -
    apply (rule machine_word_plus_mono_right_split, rule c)
    apply (simp add:pbfs_less_wb')
    done

  show "unat (end - start) \<le> 2 ^ pageBitsForSize a"
    using q c
    by (simp add: olen_add_eqv)
qed

lemmas flush_range_le1 = flush_range_le(2)[OF _ _ refl]

lemma resolveVAddr_ret:
  "\<lbrace>valid_objs' and P \<rbrace> resolveVAddr p start
  \<lbrace>\<lambda>r s. P s \<and> (r \<noteq> None \<longrightarrow> is_aligned (snd (the r)) (pageBitsForSize (fst (the r))))
  \<rbrace>"
  apply (simp add:resolveVAddr_def)
  apply (wp getPDE_wp getPTE_wp|wpc|simp)+
  apply (intro conjI impI allI)
     apply clarsimp
     apply (drule obj_at_valid_objs', clarsimp)+
     apply (clarsimp simp: projectKOs valid_obj'_def valid_mapping'_def page_base_def)
    apply (drule obj_at_valid_objs', clarsimp)+
    apply (clarsimp simp: projectKOs valid_obj'_def valid_mapping'_def)
   apply (drule obj_at_valid_objs', clarsimp)+
   apply (clarsimp simp: projectKOs valid_obj'_def valid_mapping'_def)
  apply (drule obj_at_valid_objs', clarsimp)+
  apply (clarsimp simp: projectKOs valid_obj'_def valid_mapping'_def page_base_def)
  done

lemma framesize_from_H_mask2:
  "framesize_from_H a && mask 2 = framesize_from_H a"
  apply (rule less_mask_eq)
  apply (simp add:framesize_from_H_def
    split: vmpage_size.splits)
    apply (simp add:Kernel_C.ARMSmallPage_def
      Kernel_C.ARMLargePage_def
      Kernel_C.ARMSection_def
      Kernel_C.ARMSuperSection_def)+
  done

lemma injection_handler_stateAssert_relocate:
  "injection_handler Inl (stateAssert ass xs >>= f) >>=E g
    = do v \<leftarrow> stateAssert ass xs; injection_handler Inl (f ()) >>=E g od"
  by (simp add: injection_handler_def handleE'_def bind_bindE_assoc bind_assoc)

lemma decodeARMPageDirectoryInvocation_ccorres:
  notes if_cong[cong] tl_drop_1[simp]
  shows
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps;
          isPageDirectoryCap cp \<rbrakk>
     \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and (\<lambda>s. ksCurThread s = thread) and ct_active' and sch_act_simple
              and (excaps_in_mem extraCaps \<circ> ctes_of)
              and cte_wp_at' ((=) (ArchObjectCap cp) \<circ> cteCap) slot
              and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
              and sysargs_rel args buffer)
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. cte_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}) []
       (decodeARMMMUInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call decodeARMPageDirectoryInvocation_'proc)"
  apply (clarsimp simp only: isCap_simps)
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_' current_extra_caps_' cap_' buffer_'
                simp: decodeARMMMUInvocation_def invocation_eq_use_types)
   apply (simp add: Let_def isCap_simps if_to_top_of_bind
               del: Collect_const cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: list_case_If2 if3_fold2 isPDFlush_fold
                del: Collect_const
                cong: StateSpace.state.fold_congs globals.fold_congs if_cong list.case_cong)
    apply (simp add: split_def if_to_top_of_bind
                del: Collect_const cong: if_cong)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr+
    apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
       apply vcg
      apply (clarsimp simp:list_length_less )
      apply (drule unat_less_iff[where c =2])
       apply (simp add:word_bits_def)
      apply simp
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (rule ccorres_add_return)
    apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
      apply (rule ccorres_add_return)
      apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
        apply (simp add: invocationCatch_use_injection_handler
                         injection_bindE[OF refl refl] bindE_assoc
                         injection_handler_returnOk injection_handler_whenE
                         lookupError_injection)
        apply (simp add:if_to_top_of_bindE)
        apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
           apply vcg
          apply (clarsimp simp: hd_conv_nth length_ineq_not_Nil)
         apply (simp add:injection_handler_throwError)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
           apply vcg
          apply (clarsimp simp: hd_conv_nth length_ineq_not_Nil pptrBase_def ARM_HYP.pptrBase_def)
         apply (simp add:injection_handler_throwError)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add: syscall_error_to_H_cases)
        apply (simp add:case_option_If2[unfolded if_swap[symmetric]])
        apply (simp only: injection_handler_if_returnOk)
        apply csymbr
        apply csymbr
        apply (rule ccorres_cond_false_seq)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply (simp add:if_to_top_of_bind if_to_top_of_bindE)
        apply (rule ccorres_if_cond_throws[rotated -1,where Q=\<top> and Q'=\<top>])
           apply vcg
          apply (clarsimp simp: cap_page_directory_cap_lift_def
                                cap_to_H_def to_bool_def Let_def
                         dest!: cap_lift_page_directory_cap
                         elim!: ccap_relationE
                         split: cap_CL.splits if_splits)
         apply (simp add:injection_handler_throwError)
         apply (rule syscall_error_throwError_ccorres_n)
         apply (simp add:syscall_error_to_H_cases)
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (ctac add: ccorres_injection_handler_csum1
                            [OF ccorres_injection_handler_csum1,
                             OF findPDForASID_ccorres])
           apply (rule ccorres_cond_false_seq)
           apply simp
           apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
              apply vcg
             apply (clarsimp simp: isCap_simps)
             apply (frule cap_get_tag_isCap_unfolded_H_cap)
             apply (clarsimp simp: cap_lift_page_directory_cap
                                   cap_to_H_def cap_page_directory_cap_lift_def
                            elim!: ccap_relationE split: if_split)
            apply (simp add: injection_handler_throwError)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add:syscall_error_to_H_cases)
           apply (simp add:injection_handler_liftE liftE_bindE)
           apply (rule ccorres_rhs_assoc2)+
           apply (rule ccorres_rhs_assoc)+
           apply (simp add:hd_conv_nth)
           apply (rule ccorres_split_nothrow)
               apply (rule_tac xf'= "resolve_ret_'" in ccorres_call)
                  apply (rule resolveVAddr_ccorres)
                 apply simp
                apply simp
               apply simp
              apply ceqv
             apply (simp add: injection_handler_If
                              injection_handler_returnOk if_to_top_of_bind if_to_top_of_bindE)
             apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
                apply vcg
               apply (clarsimp simp: resolve_ret_rel_def to_bool_def to_option_def
                                     rel_option_alt_def not_le
                              split: option.splits if_splits)
              apply (simp add: invocationCatch_def ARM_HYP_H.performInvocation_def
                               performInvocation_def performARMMMUInvocation_def)
              apply (simp add: performPageDirectoryInvocation_def
                               liftE_case_sum liftE_bindE liftE_alternative)
              apply (ctac add: setThreadState_ccorres)
                apply (rule ccorres_alternative2)
                apply (simp add:returnOk_liftE[symmetric])
                apply (rule ccorres_return_CE,simp+)[1]
               apply wp
              apply (vcg exspec=setThreadState_modifies)
             apply csymbr
             apply csymbr
             apply (simp add: injection_handler_whenE
                              injection_bindE[OF refl refl] bindE_assoc
                              if_to_top_of_bindE injection_handler_throwError
                              injection_handler_returnOk injection_handler_stateAssert_relocate
                              checkValidMappingSize_def)
             apply (rule ccorres_stateAssert)
             apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws[rotated -1])
                apply vcg
               apply (clarsimp simp: page_base_def resolve_ret_rel_def rel_option_alt_def
                                     to_option_def mask_def[unfolded shiftl_1,symmetric]
                               split: option.splits if_splits)
               apply (simp add: framesize_from_to_H)
              apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: throwError_def return_def syscall_error_rel_def exception_defs
                                    syscall_error_to_H_cases)
              apply (clarsimp simp: page_base_def resolve_ret_rel_def rel_option_alt_def to_option_def
                                    mask_def[unfolded shiftl_1,symmetric]
                              split: option.splits if_splits)
              apply (cut_tac sz = a in pbfs_less_wb')
              apply (clarsimp simp add:framesize_from_to_H word_bits_def framesize_from_H_mask)
              apply (rule word_of_nat_less)
              apply (simp add:pbfs_less_wb')
             apply (simp add:performARMMMUInvocations)
             apply csymbr
             apply (rule ccorres_Guard_Seq)
             apply csymbr
             apply (ctac add: setThreadState_ccorres)
               apply (simp add:bindE_assoc)
               apply (ctac add: performPageDirectoryInvocationFlush_ccorres)
                  apply (rule ccorres_alternative2)
                  apply (simp add:returnOk_liftE[symmetric])
                  apply (rule ccorres_return_CE,simp+)[1]
                 apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp)
                apply (rule hoareE_TrueI[where P = \<top>])
               apply simp
               apply (vcg exspec=performPDFlush_modifies)
              apply (wp sts_invs_minor' sts_Restart_ct_active)
              apply simp
             apply simp
             apply (vcg exspec=setThreadState_modifies)
            apply (rule_tac P = "(the v1 \<le> mask asid_bits)" in hoare_gen_asm)
            apply simp
            apply (rule hoare_post_imp[OF _ resolveVAddr_ret
              [where P = "sch_act_simple and invs' and tcb_at' thread and
                st_tcb_at'
                (\<lambda>st'. tcb_st_refs_of' st' = {} \<and>
                st' \<noteq> Structures_H.thread_state.Inactive \<and> st' \<noteq> Structures_H.thread_state.IdleThreadState)
                thread and (\<lambda>s. thread \<noteq> ksIdleThread s
                   \<and> (obj_at' tcbQueued thread s \<longrightarrow> st_tcb_at' runnable' thread s))"]])
            apply (clarsimp simp: invs_valid_objs' invs_sch_act_wf'
              valid_tcb_state'_def invs_queues)

           \<comment> \<open>cache flush constraints\<close>
           subgoal for _ _ _ _ _ _ sz p
             using pbfs_atleast_pageBits[simplified pageBits_def, of sz]
             apply (intro conjI)
                apply (erule flush_range_le)
                 apply (simp add:linorder_not_le)
                 apply (erule word_less_sub_1)
                apply (simp add:mask_add_aligned mask_twice)
               apply (fastforce simp: mask_twice
                                      mask_add_aligned[OF is_aligned_pageBitsForSize_minimum,
                                                       simplified pageBits_def])
              apply (simp add: ptrFromPAddr_add_left)
              apply (erule flush_range_le)
               apply (simp add:linorder_not_le)
               apply (erule word_less_sub_1)
              apply (fastforce simp: mask_add_aligned is_aligned_ptrFromPAddr_pageBitsForSize)
             apply (erule order_trans[rotated])
             apply (erule flush_range_le1, simp add: linorder_not_le)
             apply (erule word_less_sub_1)
             done

           apply simp
           apply (vcg exspec=resolveVAddr_modifies)
          apply (rule_tac P'="{s. errstate s = find_ret}"
            in ccorres_from_vcg_split_throws[where P=\<top>])
            apply vcg
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: throwError_def return_def syscall_error_rel_def
                                 syscall_error_to_H_cases exception_defs)
           apply (erule lookup_failure_rel_fault_lift[rotated])
           apply (simp add: exception_defs)
          apply simp
          apply (wp injection_wp[OF refl] hoare_drop_imps)
         apply simp
         apply (vcg exspec=findPDForASID_modifies)
        apply simp
        apply (wp | wp (once) hoare_drop_imps)+
       apply simp
       apply vcg
      apply simp
      apply wp
     apply simp
     apply (vcg exspec=getSyscallArg_modifies)
    apply (simp add:isPDFlush_fold throwError_invocationCatch)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (clarsimp simp: syscall_error_to_H_cases)
   apply (clarsimp simp: ex_cte_cap_wp_to'_def invs_arch_state'
                         invs_valid_objs' invs_sch_act_wf' tcb_at_invs')
  apply (clarsimp simp: isCap_simps cte_wp_at_ctes_of invs_no_0_obj')
  apply (frule ctes_of_valid', clarsimp)
  apply (drule_tac t="cteCap cte" in sym, simp)
  apply (intro conjI)
         apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt mask_def
                               linorder_not_less linorder_not_le valid_cap_simps')
         apply (clarsimp dest!:ct_active_runnable')
         apply (simp add:ct_in_state'_def)
         apply (erule pred_tcb'_weakenE)
          apply (case_tac st,simp+)
        apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt mask_def
                              linorder_not_less linorder_not_le valid_cap_simps')
        apply (clarsimp dest!:ct_active_runnable')
        apply (simp add:ct_in_state'_def)
        apply (erule pred_tcb'_weakenE)
        apply (case_tac st,simp+)
       apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt mask_def
                             linorder_not_less linorder_not_le valid_cap_simps')
       apply (clarsimp dest!:ct_active_runnable')
       apply (simp add:ct_in_state'_def)
       apply (erule pred_tcb'_weakenE)
       apply (case_tac st,simp+)
      apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt mask_def
                            linorder_not_less linorder_not_le valid_cap_simps')
      apply (clarsimp dest!:ct_active_runnable')
      apply (simp add:ct_in_state'_def)
      apply (erule pred_tcb'_weakenE)
      apply (case_tac st,simp+)
     apply (frule cap_get_tag_isCap_unfolded_H_cap(15))
     apply (clarsimp simp: cap_lift_page_directory_cap hd_conv_nth
                           cap_lift_page_table_cap typ_heap_simps'
                           cap_to_H_def cap_page_directory_cap_lift_def
                           to_bool_def cap_page_table_cap_lift_def
                           typ_heap_simps' shiftl_t2n[where n=2] field_simps
                    elim!: ccap_relationE)
     apply (intro conjI impI allI)
      apply (clarsimp simp: ThreadState_Restart_def less_mask_eq rf_sr_ksCurThread
                            resolve_ret_rel_def framesize_from_to_H framesize_from_H_mask2
                            to_option_def rel_option_alt_def to_bool_def typ_heap_simps'
                     split: option.splits if_splits
             | fastforce simp: mask_def
             | rule flushtype_relation_triv, simp add: isPageFlush_def isPDFlushLabel_def
             | rule word_of_nat_less, simp add: pbfs_less)+
    apply (frule cap_get_tag_isCap_unfolded_H_cap(15))
    apply (clarsimp simp: cap_lift_page_directory_cap hd_conv_nth
                          cap_lift_page_table_cap
                          cap_to_H_def cap_page_directory_cap_lift_def
                          cap_page_table_cap_lift_def
                          typ_heap_simps' shiftl_t2n[where n=2] field_simps
                   elim!: ccap_relationE)
    apply (intro conjI impI allI)
     apply (clarsimp simp: ThreadState_Restart_def less_mask_eq rf_sr_ksCurThread
                           resolve_ret_rel_def framesize_from_to_H framesize_from_H_mask2
                           to_option_def rel_option_alt_def to_bool_def typ_heap_simps'
                    split: option.splits if_splits
            | fastforce simp: mask_def
            | rule flushtype_relation_triv, simp add: isPageFlush_def isPDFlushLabel_def
            | rule word_of_nat_less, simp add: pbfs_less)+
   apply (frule cap_get_tag_isCap_unfolded_H_cap(15))
   apply (clarsimp simp: cap_lift_page_directory_cap hd_conv_nth
                         cap_lift_page_table_cap
                         cap_to_H_def cap_page_directory_cap_lift_def
                         cap_page_table_cap_lift_def
                         typ_heap_simps' shiftl_t2n[where n=2] field_simps
                  elim!: ccap_relationE)
   apply (intro conjI impI allI)
    apply (clarsimp simp: ThreadState_Restart_def less_mask_eq rf_sr_ksCurThread
                          resolve_ret_rel_def framesize_from_to_H framesize_from_H_mask2
                          to_option_def rel_option_alt_def to_bool_def typ_heap_simps'
                   split: option.splits if_splits
           | fastforce simp: mask_def
           | rule flushtype_relation_triv, simp add: isPageFlush_def isPDFlushLabel_def
           | rule word_of_nat_less, simp add: pbfs_less)+ (* slow 20 secs *)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(15))
  apply (clarsimp simp: cap_lift_page_directory_cap hd_conv_nth
                        cap_lift_page_table_cap
                        cap_to_H_def cap_page_directory_cap_lift_def
                        to_bool_def cap_page_table_cap_lift_def
                        typ_heap_simps' shiftl_t2n[where n=2] field_simps
                 elim!: ccap_relationE)
  apply (intro conjI impI allI)
  by (clarsimp simp: ThreadState_Restart_def less_mask_eq rf_sr_ksCurThread
                     resolve_ret_rel_def framesize_from_to_H framesize_from_H_mask2
                     to_option_def rel_option_alt_def typ_heap_simps'
              split: option.splits if_splits
      | fastforce simp: mask_def
      | rule flushtype_relation_triv, simp add: isPageFlush_def isPDFlushLabel_def
      | rule word_of_nat_less, simp add: pbfs_less)+

lemma decodeARMMMUInvocation_ccorres:
  "\<lbrakk> interpret_excaps extraCaps' = excaps_map extraCaps ; \<not> isVCPUCap cp \<rbrakk>
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
  supply if_cong[cong]
  apply (cinit' lift: invLabel_' length___unsigned_long_' cte_'
                      current_extra_caps_' cap_' buffer_' call_')
   apply csymbr
   apply (simp add: cap_get_tag_isCap_ArchObject
                    ARM_HYP_H.decodeInvocation_def
                    invocation_eq_use_types
               del: Collect_const
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE,simp+)
    apply (rule ccorres_call,
      rule decodeARMPageDirectoryInvocation_ccorres,
      simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (rule ccorres_call,
           rule decodeARMPageTableInvocation_ccorres, simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_trim_returnE, simp+)
    apply (simp add: conj_disj_distribL[symmetric])
    apply (rule ccorres_call,
           rule decodeARMFrameInvocation_ccorres, simp+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (simp add: imp_conjR[symmetric] decodeARMMMUInvocation_def
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
                   apply (clarsimp simp: asid_high_bits_def)
                  apply (clarsimp simp: rf_sr_armKSASIDTable
                                        asid_high_bits_word_bits
                                        option_to_ptr_def option_to_0_def
                                        order_less_imp_le
                                        linorder_not_less
                                        order_antisym[OF inc_le])
                  apply (clarsimp split: option.split if_split)
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
                                            ARM_HYP_H.performInvocation_def
                                            performARMMMUInvocation_def)
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
                      apply (wp injection_wp[OF refl] hoare_drop_imps)
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
   apply (rule ccorres_Cond_rhs) \<comment> \<open>ASIDPoolCap case\<close>
    apply (simp add: imp_conjR[symmetric] decodeARMMMUInvocation_def
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
                                syscall_error_to_H_cases)
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
                apply (clarsimp simp: asid_low_bits_def)
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
             apply (clarsimp simp: typ_heap_simps split: if_split)
             apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
             apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_def
                                   cap_asid_pool_cap_lift_def ucast_minus ucast_nat_def
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
                            ARM_HYP_H.performInvocation_def
                            performARMMMUInvocation_def liftE_bindE)
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
   apply (drule_tac t="cteCap ctea" in sym)
   apply (frule(1) ctes_of_valid', simp)
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
         apply (rename_tac obj)
         apply (case_tac "tcbState obj", (simp add: runnable'_def)+)[1]
        apply simp
       apply (simp add: objBits_simps archObjSize_def)
      apply fastforce
     apply (drule_tac f="\<lambda>xs. (a, bb) \<in> set xs" in arg_cong)
      apply (clarsimp simp: in_assocs_is_fun)
     apply (rule unat_less_helper)
     apply (clarsimp simp: asid_low_bits_def)
     apply (rule shiftl_less_t2n)
      apply (simp add: asid_bits_def word_leq_minus_one_le)+
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
                          ARM_HYP_H.maskCapRights_def
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
  apply (clarsimp simp: cte_wp_at_ctes_of asidHighBits_handy_convs
                        word_sle_def word_sless_def asidLowBits_handy_convs
                        rf_sr_ksCurThread "StrictC'_thread_state_defs"
                        mask_def[where n=4]
                  cong: if_cong)
  apply (clarsimp simp: ccap_relation_isDeviceCap2 objBits_simps archObjSize_def pageBits_def)
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
   apply (clarsimp simp: to_bool_def unat_eq_of_nat objBits_simps archObjSize_def pageBits_def
                  split: if_splits)
  apply (clarsimp simp: asid_low_bits_word_bits isCap_simps neq_Nil_conv
                        excaps_map_def excaps_in_mem_def
                        p2_gt_0[where 'a=32, folded word_bits_def])
  apply (drule_tac t="cteCap ctea" in sym, simp)
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
                        cap_to_H_def cap_page_directory_cap_lift_def to_bool_def
                 elim!: ccap_relationE split: if_split_asm)
  done

lemma vcpu_reg_saved_when_disabled_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
           Call vcpu_reg_saved_when_disabled_'proc
           \<lbrace> \<acute>ret__unsigned_long = from_bool (\<^bsup>s\<^esup>field = scast seL4_VCPUReg_SCTLR) \<rbrace>"
  by vcg clarsimp


lemma vcpuRegSavedWhenDisabled_spec[simp]:
  "vcpuRegSavedWhenDisabled reg = (reg = VCPURegSCTLR)"
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
    apply (rule_tac C'="{s. reg = VCPURegSCTLR \<and> \<not>curvcpuactive }"
                            and Q="\<lambda>s. (armHSCurVCPU \<circ> ksArchState) s = Some (vcpuptr, curvcpuactive)"
                            and Q'=UNIV in ccorres_rewrite_cond_sr)
     subgoal by (clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU
                          simp: cur_vcpu_relation_def from_bool_0 vcpureg_eq_use_types(1)
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
    apply (rule_tac C'="{s. reg = VCPURegSCTLR \<and> \<not>curvcpuactive }"
                            and Q="\<lambda>s. (armHSCurVCPU \<circ> ksArchState) s = Some (vcpuptr, curvcpuactive)"
                            and Q'=UNIV in ccorres_rewrite_cond_sr)
     subgoal by (clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU
                          simp: cur_vcpu_relation_def from_bool_0 vcpureg_eq_use_types(1)
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
        apply (rule hoare_post_taut[of \<top>])

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
                  apply (rule hoare_post_taut[of \<top>])
                 apply (vcg exspec=setThreadState_modifies)
                apply wpsimp
               apply (vcg exspec=setRegister_modifies)
              apply wpsimp
             apply clarsimp
             apply (vcg)
            apply wpsimp
           apply (clarsimp simp: msgInfoRegister_def  ARM_HYP.msgInfoRegister_def Kernel_C.msgInfoRegister_def Kernel_C.R1_def)
           apply (vcg exspec=setMR_modifies)
          apply wpsimp
         apply clarsimp
         apply (vcg exspec=setRegister_modifies)
        apply wpsimp
       apply (clarsimp simp: ThreadState_Running_def)
       apply (vcg exspec=lookupIPCBuffer_modifies)
      apply clarsimp
      apply (wpsimp wp: hoare_vcg_const_imp_lift hoare_vcg_all_lift hoare_vcg_imp_lift)
     apply clarsimp
     apply (vcg exspec=readVCPUReg_modifies)
    apply vcg
   apply clarsimp
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply (clarsimp simp: invs_no_0_obj' tcb_at_invs' invs_queues invs_valid_objs' invs_sch_act_wf'
                         rf_sr_ksCurThread msgRegisters_unfold
                         seL4_MessageInfo_lift_def message_info_to_H_def mask_def)
  apply (cases isCall; clarsimp)
   apply (rule conjI, clarsimp simp: ct_in_state'_def st_tcb_at'_def comp_def)
    apply (fastforce simp: obj_at'_def projectKOs)
   apply (clarsimp simp: Kernel_C.badgeRegister_def ARM_HYP.badgeRegister_def ARM_HYP_H.badgeRegister_def Kernel_C.R0_def)
   apply (simp add: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: ThreadState_Running_def)
  apply (rule conjI, clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs ct_in_state'_def)
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
                        invs_no_0_obj' tcb_at_invs' invs_queues invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        valid_tcb_state'_def ThreadState_Restart_def mask_def)
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
       (invs' and vcpu_at' vcpuptr and K (idx < 64))
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
  apply (clarsimp simp: unat_of_nat_eq word_of_nat_less)
  done

(* Note: only works for virqEOIIRQEN = 1 because that is the only type we are using *)
lemma virq_virq_pending_EN_new_spec:
  shows
  "\<forall>s. \<Gamma> \<turnstile> {s}
       Call virq_virq_pending_new_'proc
       \<lbrace> virqEOIIRQEN_' s = 1 \<longrightarrow> virq_to_H \<acute>ret__struct_virq_C = makeVIRQ (virqGroup_' s) (virqPriority_' s) (virqIRQ_' s) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: virq_to_H_def makeVIRQ_def virq_virq_pending_def)
  by (simp add: bit.disj_commute  bit.disj_assoc bit.disj_ac)

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
    apply (rule ccorres_gen_asm[where P="\<not> Suc 0 < length args"])
    apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
               cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule_tac ccorres_gen_asm[where P="Suc 0 < length args"])
   apply clarsimp
   apply (rule ccorres_add_return)
   apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=0 and buffer=buffer])
   apply csymbr
     apply (rule ccorres_add_return)
     apply (ctac add: getSyscallArg_ccorres_foo[where args=args and n=1 and buffer=buffer])
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply (rule ccorres_Cond_rhs_Seq)
       apply clarsimp
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

       (* unfortunately directly looking at \<acute>gic_vcpu_num_list_regs means we need to abstract the IF condition*)
       apply (rule_tac Q="\<lambda>s. nregs = armKSGICVCPUNumListRegs (ksArchState s)" and Q'=UNIV
                   and C'="{s. of_nat nregs \<le> args ! Suc 0 && 0xFF}"
                 in ccorres_rewrite_cond_sr_Seq)
        apply (clarsimp simp: not_le[symmetric] word_le_nat_alt unat_of_nat_eq)
        apply (simp add: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)

       apply (rule ccorres_Cond_rhs_Seq)
        apply (subgoal_tac "(of_nat nregs \<le> args ! Suc 0 && 0xFF)")
         prefer 2
  subgoal by (simp add: word_le_nat_alt not_le)

        apply (simp add: rangeCheck_def not_le[symmetric])
        apply (simp add: throwError_bind invocationCatch_def
                   cong: StateSpace.state.fold_congs globals.fold_congs)

    (* can't use syscall_error_throwError_ccorres_n, since one of the globals updates reads a global
       var itself: gic_vcpu_num_list_regs_', need to split off up to the first return_C else
       vcg barfs *)
        apply (rule ccorres_split_throws)
         apply (rule_tac P="\<lambda>s. nregs = armKSGICVCPUNumListRegs (ksArchState s)"
                     and P'="UNIV" in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre)
          apply (vcg exspec=invokeVCPUInjectIRQ_modifies)
         apply (clarsimp split: prod.splits
                          simp: throwError_def return_def EXCEPTION_SYSCALL_ERROR_def
                                EXCEPTION_NONE_def syscall_error_rel_def syscall_error_to_H_def
                                syscall_error_type_defs)
         apply (simp add: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)
        apply vcg

       apply (subgoal_tac "\<not> (of_nat nregs \<le> args ! Suc 0 && 0xFF)")
        prefer 2
  subgoal by (simp add: word_le_nat_alt not_le)
       apply clarsimp
       apply (rule ccorres_move_const_guard)
       apply (rule ccorres_move_c_guard_vcpu)
       apply (simp add: liftM_def)
       apply (clarsimp simp: rangeCheck_def not_le[symmetric]
                             liftE_liftM[symmetric] liftE_bindE_assoc)

       apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
       apply csymbr
       apply (rule ccorres_abstract_cleanup)
       apply (simp add: virq_virq_active_def)
       apply (rule_tac
                P="ret__unsigned = (vgicLR (vcpuVGIC vcpu) (unat (args ! Suc 0 && 0xFF))
                                     && vgic_irq_mask) >> 28"
                in ccorres_gen_asm2)
       apply clarsimp
       apply (rule ccorres_Cond_rhs_Seq)
        apply (subgoal_tac "vgicLR (vcpuVGIC vcpu) (unat (args ! Suc 0 && 0xFF)) && vgic_irq_mask =
                          vgic_irq_active")
         prefer 2
  subgoal
           apply (clarsimp simp: vgic_irq_active_def vgic_irq_mask_def shiftr_over_and_dist)
           apply (drule shiftr_and_eq_shiftl)
           apply simp
           done

        apply (simp add: rangeCheck_def not_le[symmetric])
        apply (simp add: throwError_bind invocationCatch_def invocation_eq_use_types
                   cong: StateSpace.state.fold_congs globals.fold_congs)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)

       apply (subgoal_tac "vgicLR (vcpuVGIC vcpu) (unat (args ! Suc 0 && 0xFF)) && vgic_irq_mask \<noteq>
                          vgic_irq_active")
               prefer 2
  subgoal by (clarsimp simp: vgic_irq_active_def)

       apply clarsimp
       apply (simp add: returnOk_bind bindE_assoc
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
  apply (rule return_inv)
  apply clarsimp
  apply (vcg exspec=getSyscallArg_modifies)

  apply (clarsimp simp: word_less_nat_alt word_le_nat_alt conj_commute
                        invs_no_0_obj' tcb_at_invs' invs_queues invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        valid_tcb_state'_def ThreadState_Restart_def mask_def)

  apply (frule invs_arch_state')
  apply (clarsimp simp: valid_arch_state'_def max_armKSGICVCPUNumListRegs_def rf_sr_armKSGICVCPUNumListRegs)
  apply (clarsimp simp: isCap_simps cap_get_tag_isCap capVCPUPtr_eq)
  apply (clarsimp simp: sysargs_rel_to_n word_le_nat_alt linorder_not_less)
  apply (clarsimp simp: valid_cap'_def)
  apply (clarsimp simp: not_le word_le_nat_alt)

  apply (subgoal_tac "armKSGICVCPUNumListRegs (ksArchState s) < 2 ^ LENGTH(machine_word_len)")
  prefer 2 subgoal by (erule order_le_less_trans; simp)

  apply (safe; clarsimp?)
    apply (subgoal_tac "armKSGICVCPUNumListRegs (ksArchState s) < 2 ^ LENGTH(machine_word_len)")
     prefer 2 subgoal by (erule order_le_less_trans; simp)
    apply (erule order_less_le_trans)
    apply (simp add: unat_of_nat_eq)
  apply (fastforce simp: sysargs_rel_to_n ct_in_state'_def st_tcb_at'_def comp_def
                    elim: obj_at'_weakenE)
  apply (fastforce simp: sysargs_rel_to_n ct_in_state'_def st_tcb_at'_def comp_def
                    elim: obj_at'_weakenE)

  apply (subgoal_tac "armKSGICVCPUNumListRegs (ksArchState s) < 2 ^ LENGTH(machine_word_len)")
  prefer 2 subgoal by (erule order_le_less_trans; simp)
  apply (erule order_less_le_trans)
  apply (simp add: unat_of_nat_eq)
  apply (clarsimp simp: typ_heap_simps')
  apply (simp add: virq_get_tag_def mask_def vgic_irq_mask_def shiftr_over_and_dist)
  apply (simp add: cvcpu_relation_def cvgic_relation_def virq_to_H_def)
  apply (clarsimp simp: cvcpu_relation_def cvgic_relation_def virq_get_tag_def vgic_irq_mask_def
                        shiftr_over_and_dist mask_def )
  apply (subgoal_tac "unat ((args ! Suc 0) && 0xFF) \<le> 63")
  apply (rule sym)
  apply simp
  apply (subgoal_tac "gic_vcpu_num_list_regs_' (globals s') \<le> 63")
  apply (simp add: word_le_nat_alt)
  apply (simp add: rf_sr_armKSGICVCPUNumListRegs)
  apply (simp add: word_le_nat_alt)
  apply (clarsimp simp: valid_arch_state'_def max_armKSGICVCPUNumListRegs_def dest!: invs_arch_state')
  apply (clarsimp simp: rf_sr_armKSGICVCPUNumListRegs)
  apply (subst unat_of_nat_eq)
  apply (erule order_le_less_trans, simp+)
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
       apply (clarsimp simp: ARM_HYP_H.performInvocation_def performARMVCPUInvocation_def)
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
                        invs_no_0_obj' tcb_at_invs' invs_queues invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        valid_tcb_state'_def ThreadState_Restart_def mask_def)

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
                        invs_no_0_obj' tcb_at_invs' invs_queues invs_valid_objs' invs_sch_act_wf'
                        rf_sr_ksCurThread msgRegisters_unfold
                        valid_tcb_state'_def ThreadState_Restart_def mask_def)
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
    "\<And>vppi. irqVPPIEventIndex (UCAST(32 \<rightarrow> 10) (args ! 0)) = Some vppi
            \<Longrightarrow> of_nat (fromEnum vppi) \<noteq> SCAST(32 signed \<rightarrow> 32) VPPIEventIRQ_invalid"
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
          apply (prop_tac "toEnum (unat (args ! 0)) = UCAST(32 \<rightarrow> 10) (args ! 0)")
           apply (fastforce simp: Kernel_C.maxIRQ_def word_le_nat_alt ucast_nat_def)
          apply csymbr
          apply clarsimp
          (* simplify outcome of irqVPPIEventIndex_'proc *)
          apply (rule_tac Q=\<top> and Q'=UNIV
                   and C'="{s. irqVPPIEventIndex (UCAST(32 \<rightarrow> 10) (args ! 0)) = None}"
                   in ccorres_rewrite_cond_sr_Seq)
           apply (solves \<open>clarsimp simp: irqVPPIEventIndex_not_invalid split: option.splits\<close>)

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
                             performInvocation_def ARM_HYP_H.performInvocation_def
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
                           invs_no_0_obj' tcb_at_invs' invs_queues invs_valid_objs' invs_sch_act_wf'
                           rf_sr_ksCurThread msgRegisters_unfold
                           valid_tcb_state'_def ThreadState_Restart_def mask_def
                           valid_cap'_def ct_in_state'_def sysargs_rel_to_n st_tcb_at'_def comp_def
                           runnable'_eq)
     apply (fastforce elim: obj_at'_weakenE)
    (* C side *)
    apply (clarsimp simp: word_le_nat_alt conj_commute
                          invs_no_0_obj' tcb_at_invs' invs_queues invs_valid_objs' invs_sch_act_wf'
                          rf_sr_ksCurThread msgRegisters_unfold
                          valid_tcb_state'_def ThreadState_Restart_def Kernel_C.maxIRQ_def
                          and_mask_eq_iff_le_mask capVCPUPtr_eq)
    apply (clarsimp simp:  mask_def)
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
       (UNIV \<comment> \<open>whoever wrote the C code decided to name this arbitrarily differently from other functions\<close>
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
       (UNIV \<inter> {s. invLabel_' s = label}
             \<inter> {s. unat (length___unsigned_long_' s) = length args}
             \<inter> {s. slot_' s = cte_Ptr slot}
             \<inter> {s. current_extra_caps_' (globals s) = extraCaps'}
             \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
             \<inter> {s. buffer_' s = option_to_ptr buffer}
             \<inter> \<lbrace>\<acute>call = from_bool isCall \<rbrace>) []
       (Arch.decodeInvocation label args cptr slot cp extraCaps
              >>= invocationCatch thread isBlocking isCall InvokeArchObject)
       (Call Arch_decodeInvocation_'proc)"
  (is "ccorres ?r ?xf ?P (?P' slot_') [] ?a ?c")
proof -

  have not_VCPUCap_case_helper_eq:
    "\<And>P Q. \<not> isVCPUCap cp \<Longrightarrow> (case cp of arch_capability.VCPUCap x \<Rightarrow> P cp | _ \<Rightarrow> Q cp) = Q cp"
    by (clarsimp simp: isVCPUCap_def split: arch_capability.splits)

  from assms show ?thesis
    apply (cinit' lift: invLabel_'  length___unsigned_long_'  slot_'  current_extra_caps_'  cap_'
                        buffer_' call_')
     apply csymbr
     apply (simp only: cap_get_tag_isCap_ArchObject ARM_HYP_H.decodeInvocation_def)
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
