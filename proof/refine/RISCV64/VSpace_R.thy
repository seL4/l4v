(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   RISCV64 VSpace refinement
*)

theory VSpace_R
imports TcbAcc_R
begin

context Arch begin global_naming RISCV64 (*FIXME: arch-split*)

(*FIXME: move to ainvs*)
lemmas store_pte_typ_ats[wp] = store_pte_typ_ats abs_atyp_at_lifts[OF store_pte_typ_at]

end

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  "vspace_at_asid' vs asid \<equiv> \<lambda>s. \<exists>ap pool.
             riscvKSASIDTable (ksArchState s) (ucast (asid_high_bits_of (ucast asid))) = Some ap \<and>
             ko_at' (ASIDPool pool) ap s \<and> pool (ucast (asid_low_bits_of (ucast asid))) = Some vs \<and>
             page_table_at' vs s"

lemma findVSpaceForASID_vs_at_wp:
  "\<lbrace>\<lambda>s. \<forall>pm. asid \<noteq> 0 \<and> asid_wf asid \<and> vspace_at_asid' pm asid s \<longrightarrow> P pm s\<rbrace>
    findVSpaceForASID asid
   \<lbrace>P\<rbrace>,-"
  apply (simp add: findVSpaceForASID_def assertE_def checkPTAt_def
                   asidRange_def mask_2pm1[symmetric]
                   le_mask_asidBits_asid_wf
             cong: option.case_cong split del: if_split)
  apply (wpsimp wp: getASID_wp)
  apply (erule allE; erule mp; clarsimp simp: vspace_at_asid'_def page_table_at'_def)
  apply (case_tac ko; simp)
  apply (subst (asm) inv_f_f, rule inj_onI, simp)
  apply (rule conjI, fastforce)
  apply (simp add: asid_low_bits_of_def ucast_ucast_a is_down ucast_ucast_mask asid_low_bits_def)
  by fastforce

crunch findVSpaceForASID, haskell_fail
  for inv[wp]: "P"
  (simp: const_def crunch_simps wp: crunch_wps ignore_del: getObject)

lemma asidBits_asid_bits[simp]:
  "asidBits = asid_bits"
  by (simp add: bit_simps' asid_bits_def asidBits_def)

lemma no_fail_read_stval[wp, intro!, simp]:
  "no_fail \<top> read_stval"
  by (simp add: read_stval_def)

lemma handleVMFault_corres:
  "corres (fr \<oplus> dc) (tcb_at thread) (tcb_at' thread)
          (handle_vm_fault thread fault) (handleVMFault thread fault)"
  unfolding handleVMFault_def handle_vm_fault_def
  by (corres | corres_cases_both)+

lemma no_fail_setVSpaceRoot[wp, intro!, simp]:
  "no_fail \<top> (setVSpaceRoot v a)"
  by (simp add: setVSpaceRoot_def)

lemma setVMRoot_corres [corres]:
  assumes "t' = t"
  shows "corres dc (tcb_at t and valid_vspace_objs and valid_asid_table and
                    pspace_aligned and pspace_distinct and
                    valid_objs and valid_global_arch_objs)
                   (no_0_obj')
                   (set_vm_root t) (setVMRoot t')"
proof -
  have global:
    "(\<And>s. P s \<Longrightarrow> valid_global_arch_objs s) \<Longrightarrow>
     corres dc
            P
            Q
            (do global_pt <- gets global_pt;
                do_machine_op (setVSpaceRoot (RISCV64.addrFromKPPtr global_pt) 0)
             od)
            (do globalPT <- gets (riscvKSGlobalPT \<circ> ksArchState);
                doMachineOp (setVSpaceRoot (addrFromKPPtr globalPT) 0)
             od)" for P Q
    by corres

  show ?thesis
  unfolding set_vm_root_def setVMRoot_def catchFailure_def withoutFailure_def throw_def
  apply (rule corres_cross_over_guard[where Q="no_0_obj' and pspace_distinct' and pspace_aligned'"])
   apply (clarsimp simp add: pspace_distinct_cross pspace_aligned_cross state_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="(=) \<circ> cte_map" and P=\<top> and P'=\<top>])
       apply (simp add: getThreadVSpaceRoot_def locateSlotTCB_def locateSlotBasic_def
                        tcbVTableSlot_def cte_map_def objBits_def cte_level_bits_def
                        objBitsKO_def tcb_cnode_index_def to_bl_1 assms cteSizeBits_def)
      apply (rule_tac  R="\<lambda>thread_root. valid_vspace_objs and valid_asid_table and
                                        pspace_aligned and pspace_distinct and
                                        valid_objs and valid_global_arch_objs and
                                        cte_wp_at ((=) thread_root) thread_root_slot and
                                        tcb_at (fst thread_root_slot) and
                                        K (snd thread_root_slot = tcb_cnode_index 1)"
                    and R'="\<lambda>thread_root. no_0_obj'"
                in corres_split[OF getSlotCap_corres])
         apply simp
        apply simp
        apply (rename_tac cap cap')
        apply (rule_tac Q="no_0_obj' and (\<lambda>_. isValidVTableRoot cap' \<or> cap' = NullCap)"
                        in corres_cross_over_guard)
         apply clarsimp
         apply (drule (1) tcb_cap_wp_at[where ref="tcb_cnode_index 1" and
                                              Q="\<lambda>cap. is_valid_vtable_root cap \<or> cap=Structures_A.NullCap"])
           apply (simp add: tcb_cap_cases_def)
          apply clarsimp
         apply (clarsimp simp: cte_wp_at_caps_of_state)
         apply (erule disjE; simp?)
         apply (clarsimp simp: is_valid_vtable_root_def split: cap.splits arch_cap.splits option.splits)
         apply (simp add: isValidVTableRoot_def)
        apply (rule corres_guard_imp)
          apply (rule_tac P="valid_vspace_objs and valid_asid_table and pspace_aligned and
                             pspace_distinct and valid_objs and valid_global_arch_objs and
                             cte_wp_at ((=) cap) thread_root_slot" in corres_assert_gen_asm2)
          prefer 3
          apply assumption
         apply (case_tac cap; clarsimp simp: isCap_simps catch_throwError intro!: global)
         apply (rename_tac acap acap')
         apply (case_tac acap; clarsimp simp: isCap_simps catch_throwError intro!: global)
         apply (rename_tac m)
         apply (case_tac m; clarsimp simp: isCap_simps catch_throwError intro!: global)
         apply (corres simp: lookup_failure_map_def wp: hoare_vcg_if_lift_ER)
          apply (frule (1) cte_wp_at_valid_objs_valid_cap)
          apply (clarsimp simp: valid_cap_def mask_def wellformed_mapdata_def)
         apply (wpsimp wp: get_cap_wp simp: getThreadVSpaceRoot_def)+
   apply (auto dest!: tcb_at_cte_at_1)
  done
qed


lemma get_asid_pool_corres_inv'[corres]:
  assumes "p' = p"
  shows "corres (\<lambda>p. (\<lambda>p'. p = p' o ucast) \<circ> inv ASIDPool)
                (asid_pool_at p and pspace_aligned and pspace_distinct) \<top>
                (get_asid_pool p) (getObject p')"
  apply (rule corres_rel_imp)
   apply (rule getObject_ASIDPool_corres[OF assms])
  apply simp
  done

lemma dMo_no_0_obj'[wp]:
  "doMachineOp f \<lbrace>no_0_obj'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (simp add: no_0_obj'_def)

lemma dMo_riscvKSASIDTable_inv[wp]:
  "doMachineOp f \<lbrace>\<lambda>s. P (riscvKSASIDTable (ksArchState s))\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma dMo_valid_arch_state'[wp]:
  "\<lbrace>\<lambda>s. P (valid_arch_state' s)\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (valid_arch_state' s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

crunch deleteASID
 for no_0_obj'[wp]: "no_0_obj'"
  (simp: crunch_simps wp: crunch_wps getObject_inv)

lemma asid_high_bits_of_ucast_ucast[simp]:
  "asid_high_bits_of (ucast (ucast asid :: machine_word)) = asid_high_bits_of asid"
  by (simp add: ucast_down_ucast_id is_down)

lemma no_fail_hwAIDFlush[intro!, wp, simp]:
  "no_fail \<top> (hwASIDFlush a)"
  by (simp add: hwASIDFlush_def)

lemma hwASIDFlush_corres[corres]:
  "corres dc \<top> \<top> (do_machine_op (hwASIDFlush x)) (doMachineOp (hwASIDFlush x))"
  by (corresKsimp corres: corres_machine_op)

lemma deleteASID_corres[corres]:
  assumes "asid' = ucast asid" "pm' = pm"
  shows "corres dc invs no_0_obj'
                (delete_asid asid pm) (deleteASID asid' pm')"
  unfolding delete_asid_def deleteASID_def using assms
  apply simp
  apply (corres simp: liftM_def mask_asid_low_bits_ucast_ucast asid_low_bits_of_def
                      ucast_ucast_a is_down
         | corres_cases_both)+
             (* side condition of setObject_ASIDPool_corres needs manual work *)
             apply (rule ext)
             apply (clarsimp simp: ucast_ucast_a is_down asid_low_bits_of_def
                                   mask_asid_low_bits_ucast_ucast inv_def)
             apply (word_bitwise, clarsimp)
            (* continue rest of corres proof: *)
            apply (corres corres: getCurThread_corres)
           apply (wp set_asid_pool_vs_lookup_unmap'
                     set_asid_pool_vspace_objs_unmap_single getASID_wp
                  | strengthen valid_arch_state_asid_table valid_arch_state_global_arch_objs
                  | simp flip: cur_tcb_def)+
   apply (fastforce dest: valid_asid_tableD invs_valid_asid_table)
  apply simp
  done

lemma valid_arch_state_unmap_strg':
  "valid_arch_state' s \<longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState :=
                        riscvKSASIDTable_update (\<lambda>_. (riscvKSASIDTable (ksArchState s))(ptr := None))
                         (ksArchState s)\<rparr>)"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def)
  apply (auto simp: ran_def split: if_split_asm)
  done

lemma is_aligned_asid_low_bits_of_zero:
  "is_aligned asid asid_low_bits \<longleftrightarrow> asid_low_bits_of asid = 0"
  apply (simp add: is_aligned_mask word_eq_iff word_size asid_bits_defs asid_bits_of_defs nth_ucast)
  apply (intro iffI allI; drule_tac x=n in spec; fastforce)
  done

lemma mask_is_asid_low_bits_of[simp]:
  "(ucast asid :: machine_word) && mask asid_low_bits = ucast (asid_low_bits_of asid)"
  by (word_eqI_solve simp: asid_low_bits_of_def asid_low_bits_def)

lemma deleteASIDPool_corres:
  assumes "base' = ucast base" "ptr' = ptr"
  shows "corres dc (invs and K (is_aligned base asid_low_bits) and asid_pool_at ptr)
                   (no_0_obj')
                   (delete_asid_pool base ptr) (deleteASIDPool base' ptr)"
  using assms
  apply (simp add: delete_asid_pool_def deleteASIDPool_def)
  apply (rule corres_assume_pre)
  apply (simp add: is_aligned_asid_low_bits_of_zero cong: corres_weak_cong)
  apply (thin_tac P for P)+
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_asid])
      apply (rule corres_when)
       apply simp
      apply (simp add: liftM_def)
      apply (rule corres_split[OF getObject_ASIDPool_corres[OF refl]])
        apply (rule corres_split)
           apply (rule corres_modify [where P=\<top> and P'=\<top>])
           apply (simp add: state_relation_def arch_state_relation_def)
           apply (rule ext)
           apply clarsimp
           apply (erule notE)
           apply (rule word_eqI[rule_format])
           apply (rename_tac x n)
           apply (drule_tac x1="ucast x" in bang_eq [THEN iffD1])
           apply (erule_tac x=n in allE)
           apply (simp add: word_size nth_ucast)
          apply (rule corres_split[OF getCurThread_corres])
            apply (rule setVMRoot_corres, simp)
           apply (wp getASID_wp)+
   apply (clarsimp simp: invs_psp_aligned invs_distinct invs_arch_state
                         invs_cur[unfolded cur_tcb_def]
                         valid_arch_state_global_arch_objs invs_valid_objs
                   simp del: fun_upd_apply)
   apply (rule conjI)
    apply (rule valid_vspace_objs_unmap_strg[THEN mp])
    apply clarsimp
   apply (drule invs_arch_state)
   apply (drule valid_arch_state_asid_table)
   apply (auto simp: valid_asid_table_def ran_def inj_on_def)[1]
  apply clarsimp
  done

crunch unmapPageTable, unmapPage, setVMRoot, setMessageInfo, setMRs, performPageTableInvocation,
         performASIDPoolInvocation, performPageInvocation
  for typ_at' [wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: crunch_wps getASID_wp simp: crunch_simps)

end

sublocale Arch < unmapPageTable: typ_at_all_props' "unmapPageTable asid vaddr pt"
  by typ_at_props'

sublocale Arch < unmapPage: typ_at_all_props' "unmapPage magnitude asid vptr ptr"
  by typ_at_props'

sublocale Arch < setVMRoot: typ_at_all_props' "setVMRoot tcb"
  by typ_at_props'

sublocale Arch < setMessageInfo: typ_at_all_props' "setMessageInfo thread info"
  by typ_at_props'

sublocale Arch < setMRs: typ_at_all_props' "setMRs thread buffer messageData"
  by typ_at_props'

sublocale Arch < performPageTableInvocation: typ_at_all_props' "performPageTableInvocation iv"
  by typ_at_props'

sublocale Arch < performASIDPoolInvocation: typ_at_all_props' "performASIDPoolInvocation iv"
  by typ_at_props'

sublocale Arch < performPageInvocation: typ_at_all_props' "performPageInvocation iv"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch-split*)

lemma getObject_PTE_corres'':
  assumes "p' = p"
  shows "corres pte_relation' (pte_at p and pspace_aligned and pspace_distinct) \<top>
                              (get_pte p) (getObject p')"
  using assms getObject_PTE_corres by simp

crunch unmapPageTable, unmapPage
  for aligned'[wp]: "pspace_aligned'"
  and distinct'[wp]: "pspace_distinct'"
  and ctes [wp]: "\<lambda>s. P (ctes_of s)"
  (simp: crunch_simps
   wp: crunch_wps getObject_inv)

crunch storePTE
  for no_0_obj'[wp]: no_0_obj'
  and valid_arch'[wp]: valid_arch_state'
  and cur_tcb'[wp]: cur_tcb'

lemma no_fail_sfence[intro!,simp,wp]:
  "no_fail \<top> sfence"
  by (simp add: sfence_def)

lemma unmapPageTable_corres:
  assumes "asid' = ucast asid" "vptr' = vptr" "pt' = pt"
  shows "corres dc
          (invs and (\<lambda>s.  vspace_for_asid asid s \<noteq> Some pt) and K (0 < asid \<and> vptr \<in> user_region))
          no_0_obj'
          (unmap_page_table asid vptr pt)
          (unmapPageTable asid' vptr' pt')"
  apply (clarsimp simp: assms unmap_page_table_def unmapPageTable_def ignoreFailure_def const_def)
  apply (corres corres: lookupPTFromLevel_corres wp: pt_lookup_from_level_wp)
   apply (clarsimp simp: invs_distinct invs_psp_aligned invs_vspace_objs invs_valid_asid_table
                         pte_at_eq)
   apply (rule_tac x=asid in exI)
   apply (rule_tac x=0 in exI)
   apply (simp add: vspace_for_asid_vs_lookup)
  apply simp
  done

lemma corres_split_strengthen_ftE:
  "\<lbrakk> corres (ftr \<oplus> r') P P' f j;
      \<And>rv rv'. r' rv rv' \<Longrightarrow> corres (ftr' \<oplus> r) (R rv) (R' rv') (g rv) (k rv');
      \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-; \<lbrace>Q'\<rbrace> j \<lbrace>R'\<rbrace>,- \<rbrakk>
    \<Longrightarrow> corres (dc \<oplus> r) (P and Q) (P' and Q') (f >>=E (\<lambda>rv. g rv)) (j >>=E (\<lambda>rv'. k rv'))"
  apply (rule_tac r'=r' in corres_splitEE)
     apply (erule corres_rel_imp)
     apply (case_tac x, auto)[1]
    apply (rule corres_rel_imp, assumption)
    apply (case_tac x, auto)[1]
   apply (simp add: validE_R_def)+
  done

lemma checkMappingPPtr_corres:
  "pte_relation' pte pte' \<Longrightarrow> corres (dc \<oplus> dc) \<top> \<top>
      (whenE (RISCV64_A.is_PagePTE pte \<longrightarrow> pptr_from_pte pte \<noteq> pptr) (throwError ExceptionTypes_A.InvalidRoot))
      (checkMappingPPtr pptr pte')"
  apply (simp add: liftE_bindE checkMappingPPtr_def)
  apply (cases pte; simp add: pptr_from_pte_def addr_from_ppn_def)
  apply (auto simp: whenE_def corres_returnOk)
  done

crunch checkMappingPPtr
 for inv[wp]: "P"
  (wp: crunch_wps simp: crunch_simps)

lemmas liftE_get_pte_corres = getObject_PTE_corres[THEN corres_liftE_rel_sum[THEN iffD2]]

lemma unmapPage_corres:
  assumes "sz' = sz" "asid' = ucast asid" "vptr' = vptr" "pptr' = pptr"
  shows "corres dc (invs and K (valid_unmap sz (asid,vptr) \<and> vptr \<in> user_region))
                   (no_0_obj')
                   (unmap_page sz asid vptr pptr)
                   (unmapPage sz' asid' vptr' pptr')"
  apply (clarsimp simp: assms unmap_page_def unmapPage_def ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>"])
       apply (rule corres_split_strengthen_ftE[where ftr'=dc])
          apply (rule findVSpaceForASID_corres[OF refl])
         apply (rule corres_splitEE)
            apply simp
            apply (rule lookupPTSlot_corres)
           apply (clarsimp simp: unlessE_whenE)
           apply datatype_schem
           apply (rule whenE_throwError_corres_initial, simp, simp)
           apply (rule corres_splitEE)
              apply (rule corres_rel_imp)
               apply (rule liftE_get_pte_corres, simp)
              apply fastforce
             apply (rule corres_splitEE[OF checkMappingPPtr_corres]; assumption?)
               apply (simp add: liftE_bindE)
               apply (rule corres_split[OF storePTE_corres], rule refl)
                  apply simp
                 apply simp
                 apply (rule corres_machine_op, rule corres_Id, rule refl; simp)
                apply wpsimp+
   apply (clarsimp simp: invs_psp_aligned invs_distinct invs_vspace_objs valid_unmap_def
                         invs_valid_asid_table)
   apply (rule conjI)
    apply (rule_tac x=asid in exI)
    apply (rule_tac x=0 in exI)
    apply (simp add: vspace_for_asid_vs_lookup)
   apply clarsimp
   apply (frule (1) pt_lookup_slot_vs_lookup_slotI)
   apply (fastforce dest!: vs_lookup_slot_pte_at)
  apply simp
  done

definition
  "mapping_map \<equiv> \<lambda>(pte, r) (pte', r'). pte_relation' pte pte' \<and> r' = r"

definition
  "page_invocation_map pgi pgi' \<equiv> case pgi of
    RISCV64_A.PageMap c slot m \<Rightarrow>
      \<exists>c' m'. pgi' = PageMap c' (cte_map slot) m' \<and>
              cap_relation (Structures_A.ArchObjectCap c) c' \<and>
              mapping_map m m'
  | RISCV64_A.PageUnmap c ptr \<Rightarrow>
      \<exists>c'. pgi' = PageUnmap c' (cte_map ptr) \<and>
      acap_relation c c'
  | RISCV64_A.PageGetAddr ptr \<Rightarrow>
      pgi' = PageGetAddr ptr"

definition
  "valid_page_inv' pgi \<equiv>
  case pgi of
    PageMap cap ptr m \<Rightarrow>
      cte_wp_at' (is_arch_update' cap) ptr and valid_cap' cap
  | PageUnmap cap ptr \<Rightarrow>
      K (isFrameCap cap) and
      cte_wp_at' (is_arch_update' (ArchObjectCap cap)) ptr and valid_cap' (ArchObjectCap cap)
  | PageGetAddr ptr \<Rightarrow> \<top>"

lemma message_info_to_data_eqv:
  "wordFromMessageInfo (message_info_map mi) = message_info_to_data mi"
  apply (cases mi)
  apply (simp add: wordFromMessageInfo_def msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def shiftL_nat)
  done

lemma message_info_from_data_eqv:
  "message_info_map (data_to_message_info rv) = messageInfoFromWord rv"
  using shiftr_mask_eq[where 'a=64 and n=12]
  by (auto simp: data_to_message_info_def messageInfoFromWord_def Let_def not_less
                 msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def mask_def
                 shiftL_nat msgMaxLength_def msgLabelBits_def)

lemma setMessageInfo_corres:
 "mi' = message_info_map mi \<Longrightarrow>
  corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
            (set_message_info t mi) (setMessageInfo t mi')"
  apply (simp add: setMessageInfo_def set_message_info_def)
  apply (subgoal_tac "wordFromMessageInfo (message_info_map mi) =
                      message_info_to_data mi")
   apply (simp add: asUser_setRegister_corres msg_info_register_def
                    msgInfoRegister_def)
  apply (simp add: message_info_to_data_eqv)
  done

lemma set_mi_invs'[wp]: "\<lbrace>invs' and tcb_at' t\<rbrace> setMessageInfo t a \<lbrace>\<lambda>x. invs'\<rbrace>"
  by (simp add: setMessageInfo_def) wp

lemma set_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' receiver \<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: setMRs_def)
  apply (wp dmo_invs' no_irq_mapM no_irq_storeWord crunch_wps|
         simp add: zipWithM_x_mapM split_def)+
  done

crunch unmapPage
  for cte_at'[wp]: "cte_at' p"
  (wp: crunch_wps simp: crunch_simps)

lemma performPageInvocation_corres:
  assumes "page_invocation_map pgi pgi'"
  shows "corres (=) (invs and valid_page_inv pgi) (no_0_obj' and valid_page_inv' pgi')
                    (perform_page_invocation pgi) (performPageInvocation pgi')"
  apply (rule corres_cross_over_guard [where Q="no_0_obj' and valid_page_inv' pgi' and
                                                pspace_aligned' and pspace_distinct'"])
   apply (fastforce intro!: pspace_aligned_cross pspace_distinct_cross)
  using assms
  unfolding perform_page_invocation_def performPageInvocation_def page_invocation_map_def
  apply (cases pgi; clarsimp simp: valid_page_inv_def mapping_map_def)
    apply (simp add: bind_assoc[symmetric])
    apply (rule corres_underlying_split[where r'=dc, OF _ corres_return_eq_same[OF refl]
                                             hoare_TrueI hoare_TrueI])
    apply (simp add: bind_assoc)
    apply (rule corres_guard_imp)
      apply (simp add: perform_pg_inv_map_def)
      apply (corres corres: updateCap_same_master)
     apply (clarsimp simp: invs_valid_objs invs_distinct invs_psp_aligned)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def is_cap_simps)
     apply (clarsimp simp: same_ref_def)
     apply (erule (3) vs_lookup_slot_pte_at)
    apply (clarsimp simp: valid_page_inv'_def cte_wp_at_ctes_of)
   apply (simp add: bind_assoc[symmetric])
   apply (rule corres_underlying_split[where r'=dc, OF _ corres_return_eq_same[OF refl]
                                               hoare_TrueI hoare_TrueI])
   apply (simp add: bind_assoc)
   apply (clarsimp simp: perform_pg_inv_unmap_def liftM_def)
   apply (rename_tac cap a b cap')
   apply (rule_tac F="RISCV64_A.is_FrameCap cap" in corres_req; clarsimp)
   apply (clarsimp simp: RISCV64_A.is_FrameCap_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split[where r'=dc])
        apply (rename_tac m)
        apply (rule option_corres[where P=\<top> and P'=\<top>])
          prefer 3
          apply (case_tac m; simp add: mdata_map_def)
         apply clarsimp
        apply clarsimp
        apply datatype_schem
        apply (fold dc_def)[1]
        apply (rule unmapPage_corres; simp)
       apply (rule corres_split[OF getSlotCap_corres[OF refl]])
         apply (rule_tac F="is_frame_cap old_cap" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: update_map_data_def is_cap_simps)
        apply (wpsimp wp: get_cap_wp)+
      apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct)
    apply (clarsimp simp: cte_wp_at_caps_of_state wellformed_pte_def
                          cap_master_cap_simps is_cap_simps update_map_data_def mdata_map_def
                          wellformed_mapdata_def valid_arch_cap_def)
   apply (clarsimp simp: valid_page_inv'_def cte_wp_at_ctes_of)
  apply (clarsimp simp: perform_pg_inv_get_addr_def fromPAddr_def)
  done

definition
  "page_table_invocation_map pti pti' \<equiv>
  case pti of
     RISCV64_A.PageTableMap cap ptr pte pt_slot \<Rightarrow>
       \<exists>cap' pte'. pti' = PageTableMap cap' (cte_map ptr) pte' pt_slot \<and>
                   cap_relation (Structures_A.ArchObjectCap cap) cap' \<and>
                   pte_relation' pte pte'
   | RISCV64_A.PageTableUnmap cap ptr \<Rightarrow>
       \<exists>cap'. pti' = PageTableUnmap cap' (cte_map ptr) \<and> acap_relation cap cap'"

definition
  "valid_pti' pti \<equiv>
   case pti of
     PageTableMap cap slot pte pteSlot \<Rightarrow>
       cte_wp_at' (is_arch_update' cap) slot and valid_cap' cap
   | PageTableUnmap cap slot \<Rightarrow>
       cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot and valid_cap' (ArchObjectCap cap)
         and K (isPageTableCap cap)"

(* extend with arch rules *)
lemmas store_pte_typ_ats[wp] = store_pte_typ_ats abs_atyp_at_lifts[OF store_pte_typ_at]

lemma clear_page_table_corres:
  "corres dc (pspace_aligned and pspace_distinct and pt_at p)
             \<top>
    (mapM_x (swp store_pte RISCV64_A.InvalidPTE) [p , p + 2^pte_bits .e. p + 2 ^ pt_bits - 1])
    (mapM_x (swp storePTE RISCV64_H.InvalidPTE) [p , p + 2^pte_bits .e. p + 2 ^ pt_bits - 1])"
  apply (rule_tac F="is_aligned p ptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 2^pte_bits"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="(=)"
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pte_at x s \<and> pspace_aligned s \<and> pspace_distinct s"
               and Q'="\<lambda>_. \<top>"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule storePTE_corres)
        apply (simp add:pte_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_table_pte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

lemma performPageTableInvocation_corres:
  "page_table_invocation_map pti pti' \<Longrightarrow>
   corres dc
          (invs and valid_pti pti) (no_0_obj' and valid_pti' pti')
          (perform_page_table_invocation pti)
          (performPageTableInvocation pti')"
  apply (rule corres_cross_over_guard [where Q="no_0_obj' and valid_pti' pti' and
                                                pspace_aligned' and pspace_distinct'"])
   apply (fastforce intro!: pspace_aligned_cross pspace_distinct_cross)
  apply (simp add: perform_page_table_invocation_def performPageTableInvocation_def
                   page_table_invocation_map_def)
  apply (cases pti)
   apply (rename_tac cap slot pte pte_slot)
   apply (clarsimp simp:  perform_pt_inv_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pti_def valid_pti'_def
                  split: arch_cap.splits capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (corres corres: updateCap_same_master)
    apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                          invs_valid_objs invs_psp_aligned invs_distinct)
    apply (case_tac cap; simp add: is_cap_simps cap_master_cap_simps)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
  apply (clarsimp simp: perform_pt_inv_unmap_def)
  apply (rename_tac acap a b acap')
  apply (rule_tac F="RISCV64_A.is_PageTableCap acap" in corres_req; clarsimp)
   apply (clarsimp simp: valid_pti_def)
  apply (clarsimp simp: RISCV64_A.is_PageTableCap_def split_def cong: option.case_cong)
  apply (simp add: case_option_If2 split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_if3)
         apply (fastforce simp: acap_map_data_def mdata_map_def is_PageTableCap_def)
        apply (rule corres_split[OF unmapPageTable_corres])
             apply (clarsimp simp: mdata_map_def)
            apply (clarsimp simp: mdata_map_def)
           apply (rule refl)
          apply (rule clear_page_table_corres)
         apply wp+
       apply (rule corres_trivial, simp)
      apply (simp add: liftM_def)
      apply (rule corres_split[OF getSlotCap_corres[OF refl]])
        apply (rule_tac F="is_pt_cap x" in corres_gen_asm)
        apply (rule updateCap_same_master)
        apply (clarsimp simp: is_cap_simps update_map_data_def)
       apply (wpsimp wp: get_cap_wp mapM_x_wp' hoare_vcg_all_lift hoare_vcg_imp_lift'
                     simp: wellformed_pte_def)+
   apply (clarsimp simp: valid_pti_def valid_arch_cap_def cte_wp_at_caps_of_state
                         invs_valid_objs invs_psp_aligned invs_distinct
                         cap_master_cap_simps is_cap_simps update_map_data_def
                         wellformed_mapdata_def)
  apply (clarsimp simp: valid_pti'_def cte_wp_at_ctes_of)
  done

definition
  "asid_pool_invocation_map ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow> Assign (ucast asid) p (cte_map slot)"

definition
  "valid_apinv' ap \<equiv>
    case ap of Assign asid p slot \<Rightarrow>
      cte_wp_at' (isArchCap isPageTableCap o cteCap) slot and K (0 < asid \<and> asid_wf asid)"

crunch copy_global_mappings
  for aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  (wp: crunch_wps)

lemma performASIDPoolInvocation_corres:
  assumes "ap' = asid_pool_invocation_map ap"
  shows "corres dc (valid_objs and pspace_aligned and pspace_distinct and valid_arch_state and valid_apinv ap)
                   (no_0_obj' and valid_apinv' ap')
                   (perform_asid_pool_invocation ap)
                   (performASIDPoolInvocation ap')"
  apply (rule corres_cross_over_guard [where Q="no_0_obj' and valid_apinv' ap' and
                                                pspace_aligned' and pspace_distinct'"])
   apply (fastforce intro!: pspace_aligned_cross pspace_distinct_cross)
  using assms
  apply (clarsimp simp: perform_asid_pool_invocation_def performASIDPoolInvocation_def)
  apply (cases ap, simp add: asid_pool_invocation_map_def)
  (* The fastforce is needed for the side conditions of setObject_ASIDPool_corres used at the end.
     Guarded by "match" to not slow down the rest too much. *)
  apply (corres' \<open>match conclusion in "f' = inv f x \<circ> g" for f' f x g \<Rightarrow>
                   \<open>fastforce simp: inv_def is_cap_simps ucast_up_inj\<close>\<close>
                 corres: getSlotCap_corres corres_assert_gen_asm_l updateCap_same_master
                 simp: update_map_data_def cap.is_ArchObjectCap_def arch_cap.is_PageTableCap_def
                       liftM_def store_asid_pool_entry_def)
    apply (wpsimp wp: set_cap_typ_at hoare_drop_imps get_cap_wp
           | strengthen valid_arch_state_global_arch_objs)+
   apply (clarsimp simp: valid_apinv_def cte_wp_at_caps_of_state is_cap_simps cap_master_cap_simps
                         update_map_data_def in_omonad)
   apply (drule (1) caps_of_state_valid_cap)
   apply (simp add: valid_cap_def obj_at_def)
  apply (fastforce simp: valid_apinv'_def cte_wp_at_ctes_of)
  done

crunch setVMRoot
  for obj_at[wp]: "\<lambda>s. P (obj_at' P' t s)"
  (simp: crunch_simps wp: crunch_wps)

crunch doMachineOp
  for arch[wp]: "\<lambda>s. P (ksArchState s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  and cur'[wp]: "\<lambda>s. P (ksCurThread s)"
  and cteCaps_of[wp]: "\<lambda>s. P (cteCaps_of s)"
  and dmo_global_refs'[wp]: "\<lambda>s. P (global_refs' s)"
  and ksPSpace[wp]: "\<lambda>s. P (ksPSpace s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"

crunch sfence, setVSpaceRoot
  for irq_masks[wp]: "\<lambda>s. P (irq_masks s)"

lemma dmo_sfence_invs'[wp]:
  "doMachineOp sfence \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs')
  apply (clarsimp simp: in_monad sfence_def machine_op_lift_def machine_rest_lift_def select_f_def)
  done

lemma dmo_setVSpaceRoot_invs'[wp]:
  "doMachineOp (setVSpaceRoot r a) \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs')
  apply (clarsimp simp: setVSpaceRoot_def machine_op_lift_def machine_rest_lift_def in_monad select_f_def)
  done

lemma dmo_setVSpaceRoot_irq_masks[wp]:
  "doMachineOp (setVSpaceRoot r a) \<lbrace>\<lambda>s. P (irq_masks (ksMachineState s))\<rbrace>"
  unfolding doMachineOp_def
  apply wpsimp
  apply (drule use_valid, rule setVSpaceRoot_irq_masks; assumption)
  done

lemma dmo_setVSpaceRoot_memory[wp]:
  "doMachineOp (setVSpaceRoot r a) \<lbrace>\<lambda>s. P (underlying_memory (ksMachineState s))\<rbrace>"
  unfolding doMachineOp_def
  apply wpsimp
  apply (drule use_valid, rule setVSpaceRoot_underlying_memory_inv; assumption)
  done

lemma setVMRoot_invs [wp]:
  "setVMRoot p \<lbrace>invs'\<rbrace>"
  unfolding setVMRoot_def getThreadVSpaceRoot_def
  by (wpsimp wp: whenE_wp findVSpaceForASID_vs_at_wp hoare_drop_imps hoare_vcg_ex_lift
                 hoare_vcg_all_lift)

crunch setVMRoot
 for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps
       loadObject_default_def)

crunch deleteASIDPool
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv mapM_wp' crunch_wps)

lemma lookupPTSlot_inv:
  "lookupPTSlot pt vptr \<lbrace>P\<rbrace>"
  unfolding lookupPTSlot_def by (wp lookupPTSlotFromLevel_inv)

crunch deleteASID
 for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def updateObject_default_def
   wp: getObject_inv)

lemma storePTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps)
     apply (auto simp: updateObject_default_def in_monad live'_def hyp_live'_def)
  done

method valid_idle'_setObject uses simp =
  simp add: valid_idle'_def, rule hoare_lift_Pf [where f="ksIdleThread"]; wpsimp?;
  (wpsimp wp: obj_at_setObject2[where P="idle_tcb'", simplified] hoare_drop_imp
        simp: simp
   | clarsimp dest!: updateObject_default_result)+

lemma setObject_asidpool_replies_of'[wp]:
  "setObject c (asidpool::asidpool) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_asidpool_tcbs_of'[wp]:
  "setObject c (asidpool::asidpool) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_pte_replies_of'[wp]:
  "setObject c (pte::pte) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma storePTE_tcbs_of'[wp]:
  "storePTE c (pte::pte) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  unfolding storePTE_def
  by setObject_easy_cases

crunch storePTE
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"

lemma storePTE_invs[wp]:
  "storePTE p pte \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift sym_heap_sched_pointers_lift
           | simp add: cteCaps_of_def o_def)+
  apply (clarsimp simp: valid_arch_obj'_def)
  done

lemma setASIDPool_valid_objs [wp]:
  "setObject p (ap::asidpool) \<lbrace>valid_objs'\<rbrace>"
  apply (wp setObject_valid_objs'[where P=\<top>])
   apply (clarsimp simp: updateObject_default_def in_monad valid_obj'_def valid_arch_obj'_def)
  apply simp
  done

lemma setASIDPool_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps)
     apply (auto simp: updateObject_default_def in_monad pageBits_def live'_def hyp_live'_def)
  done

lemma setASIDPool_invs [wp]:
  "setObject p (ap::asidpool) \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_pspace'_def valid_dom_schedule'_def)
  apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
            valid_arch_state_lift' valid_irq_node_lift
            cur_tcb_lift valid_irq_handlers_lift''
            untyped_ranges_zero_lift updateObject_default_inv sym_heap_sched_pointers_lift
          | simp add: cteCaps_of_def
          | rule setObject_ksPSpace_only)+
  apply (clarsimp simp:  o_def)
  done

crunch unmapPageTable
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas storePTE_Invalid_invs = storePTE_invs[where pte=InvalidPTE, simplified]

crunch unmapPageTable
  for invs'[wp]: "invs'"
  (ignore: doMachineOp
       wp: storePTE_Invalid_invs mapM_wp' crunch_wps
     simp: crunch_simps)

lemma perform_pti_invs [wp]:
  "\<lbrace>invs' and valid_pti' pti\<rbrace> performPageTableInvocation pti \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPageTableInvocation_def getSlotCap_def valid_pti'_def
                 split: page_table_invocation.splits)
  apply (intro conjI allI impI;
           wpsimp wp: arch_update_updateCap_invs getCTE_wp' mapM_x_wp'
                      hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (auto simp: cte_wp_at_ctes_of is_arch_update'_def isCap_simps valid_cap'_def capAligned_def)
  done

crunch unmapPage
  for cte_wp_at': "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps lookupPTSlotFromLevel_inv simp: crunch_simps)

lemma unmapPage_invs' [wp]:
  "unmapPage sz asid vptr pptr \<lbrace>invs'\<rbrace>"
  unfolding unmapPage_def
  by (wpsimp wp: lookupPTSlot_inv hoare_drop_imp hoare_vcg_all_lift)

lemma perform_page_invs [wp]:
  "\<lbrace>invs' and valid_page_inv' pt\<rbrace> performPageInvocation pt \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: performPageInvocation_def)
  apply (cases pt)
     apply clarsimp
     apply ((wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                        arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
                  simp: valid_page_inv'_def is_arch_update'_def cur_tcb'_asrt_def cur_tcb'_def
             | (auto simp: is_arch_update'_def)[1])+)[3]
  apply (clarsimp simp: cte_wp_at_ctes_of valid_page_inv'_def)
  apply (clarsimp simp: is_arch_update'_def isCap_simps valid_cap'_def capAligned_def
                  split: option.splits)
  done

lemma updateCap_ko_at_ap_inv'[wp]:
  "\<lbrace>\<lambda>s. P (ko_at' (ko::asidpool) p s )\<rbrace> updateCap a b \<lbrace>\<lambda>rv s. P ( ko_at' ko p s)\<rbrace>"
  by (wpsimp simp: updateCap_def setCTE_def wp: setObject_distinct_types_preserves_obj_at')

lemma storePTE_asid_pool_obj_at'[wp]:
  "storePTE p pte \<lbrace>\<lambda>s. P (obj_at' (P'::asidpool \<Rightarrow> bool) t s)\<rbrace>"
  apply (simp add: storePTE_def)
  apply (clarsimp simp: setObject_def in_monad split_def
                        valid_def lookupAround2_char1
                        obj_at'_def ps_clear_upd
             split del: if_split)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

crunch copyGlobalMappings
  for asid_pool_obj_at'[wp]: "\<lambda>s. P (obj_at' (P'::asidpool \<Rightarrow> bool) p s)"
  and invs'[wp]: invs'
  (ignore: storePTE wp: crunch_wps)

lemma perform_aci_invs [wp]:
  "\<lbrace>invs' and valid_apinv' api\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performASIDPoolInvocation_def split: asidpool_invocation.splits)
  apply (wpsimp wp: arch_update_updateCap_invs getASID_wp getSlotCap_wp hoare_vcg_all_lift
            hoare_vcg_imp_lift')
  apply (clarsimp simp: valid_apinv'_def cte_wp_at_ctes_of)
  apply (case_tac cte, clarsimp)
  apply (drule ctes_of_valid_cap', fastforce)
  apply (clarsimp simp: valid_cap'_def capAligned_def is_arch_update'_def isCap_simps
                        wellformed_mapdata'_def)
  done

lemma lookupIPCBuffer_valid_ipc_buffer [wp]:
  "\<lbrace>valid_objs'\<rbrace> lookupIPCBuffer b t \<lbrace>case_option \<top> valid_ipc_buffer_ptr'\<rbrace>"
  unfolding lookupIPCBuffer_def RISCV64_H.lookupIPCBuffer_def
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  apply (simp add: Let_def getSlotCap_def getThreadBufferSlot_def
                   locateSlot_conv threadGet_getObject)
  apply (wp getCTE_wp getObject_tcb_wp | wpc)+
  apply (clarsimp simp del: imp_disjL)
  apply (drule obj_at_ko_at')
  apply (clarsimp simp del: imp_disjL)
  apply (rule_tac x = ko in exI)
  apply (frule ko_at_cte_ipcbuffer[simplified cteSizeBits_def])
  apply (clarsimp simp: cte_wp_at_ctes_of shiftl_t2n' simp del: imp_disjL)
  apply (rename_tac d ref rghts sz mapdata)
  apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
  apply (frule (1) ko_at_valid_objs')
   apply (clarsimp simp: projectKO_opts_defs split: kernel_object.split_asm)
  apply (clarsimp simp: valid_obj'_def valid_tcb'_def
                        isCap_simps cte_level_bits_def field_simps)
  apply (drule bspec [OF _ ranI [where a = "0x40"]])
   apply simp
  apply (clarsimp simp: valid_cap'_def valid_arch_cap'_def frame_at'_def)
  apply (rule conjI)
   apply (rule aligned_add_aligned)
     apply (clarsimp simp: capAligned_def)

     apply assumption
    apply (erule is_aligned_andI1)
   apply (case_tac rghts; simp add: msg_align_bits pageBits_def)
  apply (clarsimp simp: capAligned_def)
  apply (drule_tac x = "(tcbIPCBuffer ko && mask (pageBitsForSize rghts)) >> pageBits" in spec)
  apply (simp add: shiftr_shiftl1)
  apply (subst (asm) mask_out_add_aligned)
   apply (erule is_aligned_weaken [OF _ pbfs_atleast_pageBits])
  apply (erule mp)
  apply (rule shiftr_less_t2n)
  apply (clarsimp simp: pbfs_atleast_pageBits)
  apply (rule and_mask_less')
  apply (case_tac rghts; simp add: pageBits_def ptTranslationBits_def)
  done

lemma replyFromKernel_corres:
  "\<lbrakk>t = t'; r = r'\<rbrakk> \<Longrightarrow>
   corres dc (tcb_at t and invs) invs' (reply_from_kernel t r) (replyFromKernel t' r')"
  apply (case_tac r)
  apply (clarsimp simp: replyFromKernel_def reply_from_kernel_def
                        badge_register_def badgeRegister_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF lookupIPCBuffer_corres])
      apply (rule corres_split[OF asUser_setRegister_corres])
        apply (rule corres_split_eqr[OF setMRs_corres], simp)
          apply (rule setMessageInfo_corres)
          apply (wp hoare_case_option_wp hoare_valid_ipc_buffer_ptr_typ_at'
                 | fastforce)+
  done

end

end
