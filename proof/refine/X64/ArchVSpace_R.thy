(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   X64 VSpace refinement
*)

theory ArchVSpace_R
imports VSpace_R
begin
context Arch begin global_naming X64 (*FIXME: arch-split*)

end

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  "vspace_at_asid' vs asid \<equiv> \<lambda>s. \<exists>ap pool.
             x64KSASIDTable (ksArchState s) (ucast (asid_high_bits_of asid)) = Some ap \<and>
             ko_at' (ASIDPool pool) ap s \<and> pool (asidLowBitsOf asid) = Some vs \<and>
             page_map_l4_at' vs s"

crunch checkPDAt
  for inv[wp]: P

lemma findVSpaceForASID_vs_at_wp:
  "\<lbrace>\<lambda>s. \<forall>pm. asid \<noteq> 0 \<and> asid_wf asid \<and> (page_map_l4_at' pm s \<longrightarrow> vspace_at_asid' pm asid s) \<longrightarrow> P pm s\<rbrace>
    findVSpaceForASID asid
   \<lbrace>P\<rbrace>,-"
  supply inj_ASIDPool[simp del]
  apply (simp add: findVSpaceForASID_def assertE_def checkPML4At_def
                   asidRange_def mask_2pm1[symmetric]
                   le_mask_asidBits_asid_wf
             cong: option.case_cong split del: if_split)
  apply (wpsimp wp: getASID_wp)
  apply (erule allE; erule mp; clarsimp simp: vspace_at_asid'_def page_map_l4_at'_def)
  apply (case_tac ko; simp)
  apply (subst (asm) inv_f_f, rule inj_onI, simp)
  by fastforce

crunch findVSpaceForASID, haskell_fail
  for inv[wp]: "P"
  (simp: const_def crunch_simps wp: loadObject_default_inv crunch_wps ignore_del: getObject)

lemma dmo_invs_no_cicd_lift': (* FIXME X64: move up *)
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  assumes "\<And>P p. f \<lbrace>\<lambda>s. P (underlying_memory s p)\<rbrace>"
  shows "doMachineOp f \<lbrace>all_invs_but_ct_idle_or_in_cur_domain'\<rbrace>"
  apply (wp dmo_invs_no_cicd' assms)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid,
         rule assms, rule refl)
  apply simp
  done

lemma dmo_invs_lift': (* FIXME X64: move up *)
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  assumes "\<And>P p. f \<lbrace>\<lambda>s. P (underlying_memory s p)\<rbrace>"
  shows "doMachineOp f \<lbrace>invs'\<rbrace>"
  apply (wp dmo_invs' assms)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid,
         rule assms, rule refl)
  apply simp
  done

lemma dmo_invalidateTranslationSingleASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateTranslationSingleASID a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_invalidateTranslationSingleASID no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: invalidateTranslationSingleASID_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_invalidateASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateASID a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_invalidateASID no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: invalidateASID_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_invalidateLocalPageStructureCacheASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateLocalPageStructureCacheASID vspace asid) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wpsimp wp: dmo_invs' invalidateLocalPageStructureCacheASID_irq_masks)
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: invalidateLocalPageStructureCacheASID_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmos_invs_no_cicd'[wp]:
  "doMachineOp enableFpu \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp disableFpu \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp (writeFpuState val) \<lbrace>invs_no_cicd'\<rbrace>"
  "doMachineOp readFpuState \<lbrace>invs_no_cicd'\<rbrace>"
  by (wp dmo_invs_no_cicd_lift')+

lemma dmos_invs'[wp]:
  "doMachineOp enableFpu \<lbrace>invs'\<rbrace>"
  "doMachineOp disableFpu \<lbrace>invs'\<rbrace>"
  "doMachineOp (writeFpuState val) \<lbrace>invs'\<rbrace>"
  "doMachineOp readFpuState \<lbrace>invs'\<rbrace>"
  by (wp dmo_invs_lift')+

lemma pspace_relation_pml4:
  assumes p: "pspace_relation (kheap a) (ksPSpace c)"
  assumes pa: "pspace_aligned a"
  assumes pad: "pspace_aligned' c" "pspace_distinct' c"
  assumes t: "page_map_l4_at p a"
  shows "page_map_l4_at' p c"
  using assms is_aligned_pml4 [OF t pa]
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                        if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: page_map_l4_at'_def bit_simps
                        typ_at_to_obj_at_arches)
  apply (drule_tac x="ucast y" in spec, clarsimp)
  apply (simp add: ucast_ucast_mask iffD2 [OF mask_eq_iff_w2p] word_size)
  apply (clarsimp simp add: pml4e_relation_def)
  apply (drule(2) aligned_distinct_pml4e_atI')
  apply (erule obj_at'_weakenE)
  apply simp
  done

lemma find_vspace_for_asid_eq_helper:
  "\<lbrakk> vspace_at_asid asid pm s; valid_vspace_objs s;
         asid \<noteq> 0; pspace_aligned s \<rbrakk>
    \<Longrightarrow> find_vspace_for_asid asid s = returnOk pm s
             \<and> page_map_l4_at pm s \<and> is_aligned pm pml4Bits"
  apply (clarsimp simp: vspace_at_asid_def valid_vspace_objs_def)
  apply (frule spec, drule mp, erule exI)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def
                 elim!: vs_lookupE)
  apply (erule rtranclE)
   apply simp
  apply (clarsimp dest!: vs_lookup1D)
  apply (erule rtranclE)
   defer
   apply (drule vs_lookup1_trans_is_append')
   apply (clarsimp dest!: vs_lookup1D)
  apply (clarsimp dest!: vs_lookup1D)
  apply (drule spec, drule mp, rule exI,
         rule vs_lookupI[unfolded vs_asid_refs_def])
    apply (rule image_eqI[OF refl])
    apply (erule graph_ofI)
   apply clarsimp
   apply (rule rtrancl.intros(1))
  apply (clarsimp simp: vs_refs_def graph_of_def
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  apply (drule bspec, erule ranI)
  apply clarsimp
  apply (drule ucast_up_inj, simp)
  apply (simp add: find_vspace_for_asid_def bind_assoc
                   word_neq_0_conv[symmetric] liftE_bindE)
  apply (simp add: exec_gets liftE_bindE bind_assoc
                   get_asid_pool_def get_object_def)
  apply (clarsimp simp: returnOk_def get_pml4e_def
                        get_pml4_def get_object_def
                        bind_assoc)
  apply (frule(1) pspace_alignedD[where p=pm])
  apply (simp add: bit_simps)
  done

lemma asidBits_asid_bits[simp]:
  "asidBits = asid_bits"
  by (simp add: asid_bits_def asidBits_def
                asidHighBits_def asid_low_bits_def)

lemma handleVMFault_corres:
  "corres (fr \<oplus> dc) (tcb_at thread and pspace_aligned and pspace_distinct) \<top>
          (handle_vm_fault thread fault) (handleVMFault thread fault)"
  apply (simp add: X64_H.handleVMFault_def handle_vm_fault_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply simp
       apply (rule corres_machine_op [where r="(=)"])
       apply (rule corres_Id, rule refl, simp)
       apply (rule no_fail_getFaultAddress)
      apply (rule corres_split_eqrE)
         apply simp
         apply (rule asUser_getRegister_corres)
        apply (cases fault; simp)
       apply (simp, wp as_user_typ_at)
      apply (simp, wp asUser_typ_ats)
     apply wpsimp+
  done

lemma set_current_cr3_corres [corres]:
  "cr3_relation c c' \<Longrightarrow> corres dc \<top> \<top> (set_current_cr3 c) (setCurrentUserCR3 c')"
  apply (clarsimp simp add: set_current_cr3_def setCurrentUserCR3_def cr3_relation_def)
  apply (rule corres_modify')
   apply (clarsimp simp: state_relation_def arch_state_relation_def cr3_relation_def)
  apply simp
  done

lemma get_current_cr3_corres [corres]:
  "corres cr3_relation \<top> \<top> (get_current_cr3) (getCurrentUserCR3)"
  apply (simp add: getCurrentUserCR3_def get_current_cr3_def)
  by (clarsimp simp: state_relation_def arch_state_relation_def)

lemma setVMRoot_corres [corres]:
  assumes "t' = t"
  shows "corres dc (tcb_at t and valid_arch_state and valid_objs
                      and unique_table_refs o caps_of_state and valid_vs_lookup
                      and valid_global_objs and pspace_aligned and pspace_distinct
                      and valid_vspace_objs)
                   (pspace_aligned' and pspace_distinct'
                      and valid_arch_state' and tcb_at' t' and no_0_obj')
                   (set_vm_root t) (setVMRoot t')"
proof -
  have P: "corres dc \<top> \<top>
        (do global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
            set_current_vspace_root (X64.addrFromKPPtr global_pml4) 0
         od)
        (do globalPML4 \<leftarrow> gets (x64KSSKIMPML4 \<circ> ksArchState);
            X64_H.setCurrentUserVSpaceRoot (addrFromKPPtr globalPML4) 0
         od)"
    apply (simp add: X64_H.setCurrentUserVSpaceRoot_def set_current_vspace_root_def
                     make_cr3_def makeCR3_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr)
         apply (subst corres_gets)
         apply (clarsimp simp: state_relation_def arch_state_relation_def)
        apply (rule set_current_cr3_corres,
               simp add: cr3_relation_def cr3_addr_mask_def addrFromKPPtr_def bit_simps)
       apply (wp | simp)+
    done
  have Q: "\<And>P P'. corres dc P P'
        (throwError ExceptionTypes_A.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
                  set_current_vspace_root (X64.addrFromKPPtr global_pml4) 0
               od))
        (throwError Fault_H.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do globalPML4 \<leftarrow> gets (x64KSSKIMPML4 \<circ> ksArchState);
                  setCurrentUserVSpaceRoot (addrFromKPPtr globalPML4) 0
               od))"
    apply (rule corres_guard_imp)
      apply (rule corres_split_catch [where f=lfr])
         apply (subst corres_throwError, simp add: lookup_failure_map_def)
        apply (simp, rule P)
       apply (wp | simp)+
    done
  show ?thesis
    unfolding set_vm_root_def setVMRoot_def getThreadVSpaceRoot_def locateSlot_conv
              catchFailure_def withoutFailure_def throw_def
              make_cr3_def makeCR3_def
    apply (rule corres_guard_imp)
      apply (rule corres_underlying_split [where r'="(=) \<circ> cte_map"])
         apply (simp add: tcbVTableSlot_def cte_map_def objBits_def cte_level_bits_def
                          objBitsKO_def tcb_cnode_index_def to_bl_1 assms)
        apply (rule_tac R="\<lambda>thread_root. valid_arch_state and
                                         valid_vspace_objs and valid_vs_lookup and
                                         unique_table_refs o caps_of_state and
                                         valid_global_objs and valid_objs and
                                         pspace_aligned and pspace_distinct and
                                         cte_wp_at ((=) thread_root) thread_root_slot"
                    and R'="\<lambda>thread_root. pspace_aligned' and pspace_distinct' and no_0_obj'"
                 in corres_split[OF getSlotCap_corres])
           apply simp
          apply (case_tac rv; simp add: isCap_simps Q[simplified])
          apply (rename_tac arch_cap)
          apply (case_tac arch_cap; simp add: isCap_simps Q[simplified])
          apply (rename_tac pm_ptr pm_mapped)
          apply (case_tac pm_mapped; simp add: Q[simplified])
          apply (clarsimp simp: cap_asid_def)
          apply (rule corres_guard_imp)
            apply (rule corres_split_catch [where f=lfr, OF _ P wp_post_tautE wp_post_tautE])
            apply (rule corres_split_eqrE[OF findVSpaceForASID_corres[OF refl]])
              apply (rule whenE_throwError_corres; simp add: lookup_failure_map_def)
              apply (simp only: liftE_bindE)
              apply (rule corres_underlying_split[OF get_current_cr3_corres])
                apply (rule corres_whenE[OF _ _ dc_simp])
                 apply (case_tac cur_cr3; case_tac curCR3; clarsimp simp: cr3_relation_def cr3_addr_mask_def)
                apply (rule iffD2[OF corres_liftE_rel_sum, OF set_current_cr3_corres])
                apply (simp add: cr3_relation_def cr3_addr_mask_def)
               apply wp
              apply wpsimp
             apply simp
             apply wp
            apply simp
            apply wp
           apply clarsimp
           apply (frule (1) cte_wp_at_valid_objs_valid_cap)
           apply (clarsimp simp: valid_cap_def mask_def word_neq_0_conv asid_wf_def asid_bits_def)
          apply (fastforce simp: valid_cap_def mask_def word_neq_0_conv)
         apply wpsimp
         apply (wpsimp wp: get_cap_wp)
        apply wp
       apply wp
      apply wp
    using tcb_at_cte_at_1 by auto
qed


lemma get_asid_pool_corres_inv':
  assumes "p' = p"
  shows "corres (\<lambda>p. (\<lambda>p'. p = p' o ucast) \<circ> inv ASIDPool)
                (asid_pool_at p) (pspace_aligned' and pspace_distinct')
                (get_asid_pool p) (getObject p')"
  apply (rule corres_rel_imp)
   apply (rule getObject_ASIDPool_corres'[OF assms])
  apply simp
  done

lemma dMo_no_0_obj'[wp]:
  "\<lbrace>no_0_obj'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. no_0_obj'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (simp add: no_0_obj'_def)

lemma hwASIDInvalidate_corres:
  assumes "pm' = pm" "asid' = asid"
  shows "corres dc \<top> \<top> (hw_asid_invalidate asid pm) (hwASIDInvalidate asid' pm')"
  using assms
  apply (simp add: hw_asid_invalidate_def hwASIDInvalidate_def)
  apply (rule corres_machine_op)
  apply (rule corres_Id; simp)
  done

crunch hwASIDInvalidate
  for aligned'[wp]: pspace_aligned'
crunch hwASIDInvalidate
  for distinct'[wp]: pspace_distinct'
crunch hwASIDInvalidate
  for cur'[wp]: cur_tcb'

lemma dMo_x64KSASIDTable_inv[wp]:
  "\<lbrace>\<lambda>s. P (x64KSASIDTable (ksArchState s))\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (x64KSASIDTable (ksArchState s))\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma dMo_valid_arch_state'[wp]:
  "\<lbrace>\<lambda>s. P (valid_arch_state' s)\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (valid_arch_state' s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma invalidateASID_valid_arch_state [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> hwASIDInvalidate x y \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  unfolding hwASIDInvalidate_def
  by wpsimp

crunch deleteASID
  for no_0_obj'[wp]: "no_0_obj'"
  (simp: crunch_simps wp: crunch_wps getObject_inv loadObject_default_inv)


lemma deleteASID_corres [corres]:
  assumes "asid' = asid" "pm' = pm"
  notes set_asid_pool_def[simp del]
  shows "corres dc
          (invs and K (asid_wf asid \<and> asid \<noteq> 0))
          (pspace_aligned' and pspace_distinct' and no_0_obj'
              and valid_arch_state' and cur_tcb')
          (delete_asid asid pm) (deleteASID asid' pm')"
  using assms
  apply (simp add: delete_asid_def deleteASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_asid])
      apply (case_tac "asid_table (asid_high_bits_of asid)", simp)
      apply clarsimp
      apply (rule_tac P="\<lambda>s. asid_high_bits_of asid \<in> dom (asidTable o ucast) \<longrightarrow>
                             asid_pool_at (the ((asidTable o ucast) (asid_high_bits_of asid))) s" and
                      P'="pspace_aligned' and pspace_distinct'" and
                      Q="invs and K (asid_wf asid \<and> asid \<noteq> 0) and
                         (\<lambda>s. x64_asid_table (arch_state s) = asidTable \<circ> ucast)" in
                      corres_split)
         apply (simp add: dom_def)
         apply (rule get_asid_pool_corres_inv'[OF refl])
        apply (rule corres_when, simp add: mask_asid_low_bits_ucast_ucast asid_low_bits_of_def)
        apply (rule corres_split)
           apply (rule hwASIDInvalidate_corres[where pm=pm]; simp)
          apply (rule_tac P="asid_pool_at (the (asidTable (ucast (asid_high_bits_of asid))))"
                      and P'="pspace_aligned' and pspace_distinct'"
                       in corres_split)
             apply (simp del: fun_upd_apply)
             apply (rule setObject_ASIDPool_corres')
             apply (simp add: inv_def mask_asid_low_bits_ucast_ucast)
             apply (rule ext)
             apply (clarsimp simp: o_def)
            apply (rule corres_split[OF getCurThread_corres])
              apply simp
              apply (rule setVMRoot_corres[OF refl])
             apply wp+
           apply (thin_tac "x = f o g" for x f g)
           apply (simp del: fun_upd_apply)
           apply (fold cur_tcb_def)
           apply (wp set_asid_pool_vs_lookup_unmap'
                     set_asid_pool_vspace_objs_unmap_single)+
          apply simp
          apply (fold cur_tcb'_def)
          apply (wp | clarsimp simp: o_def)+
       apply (subgoal_tac "vspace_at_asid asid pm s")
        apply (auto simp: obj_at_def a_type_def graph_of_def
                   split: if_split_asm)[1]
       apply (simp add: vspace_at_asid_def)
       apply (rule vs_lookupI)
        apply (simp add: vs_asid_refs_def)
        apply (rule image_eqI[OF refl])
        apply (erule graph_ofI)
       apply (rule r_into_rtrancl)
       apply simp
       apply (erule vs_lookup1I [OF _ _ refl])
       apply (simp add: vs_refs_def)
       apply (rule image_eqI[rotated], erule graph_ofI)
       apply (simp add: mask_asid_low_bits_ucast_ucast)
      \<comment> \<open>rewrite assumption so that the goal can refer to the C variable instead of the abstract's.\<close>
      apply (drule Some_to_the)
      apply (wpsimp wp: getASID_wp)+
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                  dest!: invs_arch_state)
   apply blast
  apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def)
  done

lemma valid_arch_state_unmap_strg':
  "valid_arch_state' s \<longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState :=
                        x64KSASIDTable_update (\<lambda>_. (x64KSASIDTable (ksArchState s))(ptr := None))
                         (ksArchState s)\<rparr>)"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def)
  apply (auto simp: ran_def split: if_split_asm)
  done

crunch hwASIDInvalidate
  for x64KSASIDTable_inv[wp]: "\<lambda>s. P (x64KSASIDTable (ksArchState s))"

lemma deleteASIDPool_corres:
  assumes "base' = base" "ptr' = ptr"
  shows "corres dc (invs and K (is_aligned base asid_low_bits)
                         and asid_pool_at ptr)
                   (pspace_aligned' and pspace_distinct' and no_0_obj'
                         and valid_arch_state' and cur_tcb')
                   (delete_asid_pool base ptr) (deleteASIDPool base ptr)"
  using assms
  apply (simp add: delete_asid_pool_def deleteASIDPool_def)
  apply (rule corres_assume_pre, simp add: is_aligned_asid_low_bits_of_zero cong: corres_weak_cong)
  apply (thin_tac P for P)+
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_asid])
      apply (rule corres_when)
       apply simp
      apply (simp add: liftM_def)
      apply (rule corres_split[OF getObject_ASIDPool_corres'[OF refl]])
        apply (rule corres_split)
           apply (rule corres_mapM [where r=dc and r'=dc], simp, simp)
               prefer 5
               apply (rule order_refl)
              apply (rule_tac P="invs and ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) ptr
                                      and [VSRef (ucast (asid_high_bits_of base)) None] \<rhd> ptr
                                      and K (is_aligned base asid_low_bits)"
                          and P'="pspace_aligned' and pspace_distinct' and no_0_obj'"
                       in corres_guard_imp)
                apply (rule corres_when)
                 apply (clarsimp simp: ucast_ucast_low_bits)
                apply (simp add: ucast_ucast_low_bits)
                apply (rule_tac pm="the (inv ASIDPool x xa)"
                         in hwASIDInvalidate_corres[OF refl refl])
               apply simp
              apply simp
             apply clarsimp
             apply ((wp|clarsimp simp: o_def)+)[3]
          apply (rule corres_split)
             apply (rule corres_modify [where P=\<top> and P'=\<top>])
             apply (simp add: state_relation_def arch_state_relation_def)
             apply (rule ext)
             apply clarsimp
             apply (erule notE)
             apply (rule word_eqI[rule_format])
             apply (drule_tac x1="ucast xa" in bang_eq [THEN iffD1])
             apply (erule_tac x=n in allE)
             apply (simp add: word_size nth_ucast)
            apply (rule corres_split)
               apply (rule getCurThread_corres)
              apply (simp only:)
              apply (rule setVMRoot_corres[OF refl])
             apply wp+
         apply (rule_tac Q'="\<lambda>_ s. rv = x64_asid_table (arch_state s)"
                  in hoare_post_add)
         apply (drule sym, simp only: )
         apply (drule sym, simp only: )
         apply (thin_tac "P" for P)+
         apply (simp only: pred_conj_def cong: conj_cong)
         apply simp
         apply (fold cur_tcb_def)
         apply (strengthen valid_arch_state_unmap_strg
                           valid_vspace_objs_unmap_strg
                           valid_vs_lookup_unmap_strg)
         apply (wp mapM_wp')+
         apply simp
        apply (rule_tac Q'="\<lambda>_ s. rv' = x64KSASIDTable (ksArchState s)"
                 in hoare_post_add)
        apply (simp only: pred_conj_def cong: conj_cong)
        apply simp
        apply (strengthen valid_arch_state_unmap_strg')
        apply (fold cur_tcb'_def)
        apply (wp mapM_wp')+
        apply (clarsimp simp: cur_tcb'_def)
       apply (simp add: o_def pred_conj_def)
       apply wp
      apply (wp getASID_wp)+
   apply (clarsimp simp: conj_comms)
   apply (auto simp: vs_lookup_def intro: vs_asid_refsI)[1]
  apply clarsimp
  done

crunch findVSpaceForASID
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps loadObject_default_def)

crunch setVMRoot
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps)

lemmas setVMRoot_typ_ats [wp] = typ_at_lifts [OF setVMRoot_typ_at']

crunch flushTable
  for no_0_obj'[wp]: "no_0_obj'"
  (wp: crunch_wps simp: crunch_simps)

lemma getObject_PTE_corres'':
  assumes "p' = p"
  shows "corres pte_relation' (pte_at p) (pspace_aligned' and pspace_distinct')
                              (get_pte p) (getObject p')"
  using assms getObject_PTE_corres' by simp

lemma flushTable_corres:
  assumes "pm' = pm" "vptr' = vptr" "pt' = pt" "asid' = asid"
  shows "corres dc (pspace_aligned and valid_objs and valid_arch_state
                      and cur_tcb and vspace_at_asid asid pm and valid_asid_map
                      and valid_vspace_objs and pspace_aligned and pspace_distinct
                      and valid_vs_lookup and valid_global_objs
                      and unique_table_refs o caps_of_state and page_table_at pt
                      and K (is_aligned vptr pd_shift_bits \<and> asid \<noteq> 0))
                   (pspace_aligned' and pspace_distinct' and no_0_obj'
                      and valid_arch_state' and cur_tcb')
                   (flush_table pm vptr pt asid)
                   (flushTable pm' vptr' pt' asid')"
  proof -
    have b: "ptTranslationBits + pageBits = pd_shift_bits"
      by (simp add: bit_simps)
    show ?thesis
      using assms
      apply (simp add: flush_table_def flushTable_def)
      apply (rule corres_assume_pre)
      apply (simp add: b is_aligned_mask[symmetric] cong: corres_weak_cong)
      apply (subst get_pt_mapM_x_lower)
        apply (solves \<open>wpsimp simp: upto_enum_def\<close>)+
      apply (subst get_pt_get_pte)
       apply (clarsimp elim!: is_aligned_pt)
      apply (thin_tac "P" for P)+
      apply (rule subst[of "0x1FF" "-1::9 word"], simp)
      apply (rule corres_mapM_x[OF _ _ _ _ subset_refl])
         apply (frule zip_map_rel[where f=ucast and g=id, simplified])
          apply (simp add: upto_enum_def bit_simps take_bit_nat_eq_self unsigned_of_nat)
         apply (rule corres_guard_imp)
           apply (rule corres_split[OF getObject_PTE_corres''])
              apply (simp add: bit_simps objBits_simps archObjSize_def)
             apply (case_tac rv; case_tac rv'; simp)
             apply (rule corres_machine_op)
             apply (subgoal_tac "ucast x = y"; simp)
             apply (rule corres_rel_imp[OF corres_underlying_trivial]; simp)
             apply (wpsimp simp: invalidateTranslationSingleASID_def)
            apply (wpsimp)+
          apply (rule page_table_pte_atI; simp add: bit_simps ucast_less[where 'b=9, simplified])
         apply simp
        apply (wpsimp wp: hoare_drop_imps)
       apply (wpsimp wp: hoare_drop_imps)
      apply (simp add: bit_simps)
      done
  qed

crunch flushTable
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (simp: assertE_def when_def wp: crunch_wps)

lemmas flushTable_typ_ats' [wp] = typ_at_lifts [OF flushTable_typ_at']

lemmas findVSpaceForASID_typ_ats' [wp] = typ_at_lifts [OF findVSpaceForASID_inv]

crunch findVSpaceForASID
  for inv[wp]: P
  (simp: assertE_def whenE_def loadObject_default_def
   wp: crunch_wps getObject_inv)

crunch unmapPageTable, unmapPageDirectory, unmapPDPT
  for aligned'[wp]: "pspace_aligned'"
  and distinct'[wp]: "pspace_distinct'"
  (simp: crunch_simps
     wp: crunch_wps getObject_inv loadObject_default_inv)


crunch storePDE, storePTE, storePDPTE, storePML4E
  for no_0_obj'[wp]: no_0_obj'
  and valid_arch'[wp]: valid_arch_state'
  and cur_tcb'[wp]: cur_tcb'

lemma getCurrentUserCR3_inv[wp]: "\<lbrace>P\<rbrace> getCurrentUserCR3 \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getCurrentUserCR3_def)

lemma invalidatePageStructureCacheASID_corres' [corres]:
  assumes "vspace' = vspace" "asid' = asid"
  shows
  "corres dc \<top> \<top>
     (invalidate_page_structure_cache_asid vspace asid)
     (X64_H.invalidatePageStructureCacheASID vspace' asid')"
  by (corresKsimp simp: invalidate_page_structure_cache_asid_def
                       X64_H.invalidatePageStructureCacheASID_def
                       invalidateLocalPageStructureCacheASID_def
                       assms ucast_id
               corres: corres_machine_op
                   wp: no_fail_machine_op_lift)

lemmas invalidatePageStructureCacheASID_corres =
  invalidatePageStructureCacheASID_corres'[OF refl refl]

crunch lookupPTSlot
  for inv[wp]: "P"
  (wp: loadObject_default_inv)

lemma unmapPageTable_corres:
  assumes "asid' = asid" "vptr' = vptr" "pt' = pt"
  notes liftE_get_pde_corres = getObject_PDE_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and page_table_at pt and
           K (0 < asid \<and> is_aligned vptr pd_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid_wf asid))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_page_table asid vptr pt)
          (unmapPageTable asid' vptr' pt')"
  apply (clarsimp simp: assms unmap_page_table_def unmapPageTable_def ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>", OF _ corres_return_trivial])
      apply (rule corres_split_eqrE[OF findVSpaceForASID_corres[OF refl]])
        apply (rule corres_split_eqrE[OF lookupPDSlot_corres])
          apply (rule corres_splitEE[OF liftE_get_pde_corres])
            apply (rule corres_splitEE[where r'=dc])
               apply (case_tac "\<exists>addr x xa. pde = X64_A.PageTablePDE addr x xa";
                      fastforce intro!: corres_returnOkTT
                                simp: lookup_failure_map_def pde_relation_def
                                split: X64_A.pde.splits)
              apply simp
              apply (rule corres_split[OF flushTable_corres[OF refl refl refl refl]])
                apply (rule corres_split[OF storePDE_corres'])
                   apply simp
                  apply (rule invalidatePageStructureCacheASID_corres)
                 apply ((wpsimp wp: hoare_if get_pde_wp getPDE_wp)+)[8]
         apply ((wpsimp wp: lookup_pd_slot_wp hoare_vcg_all_liftE_R | wp (once) hoare_drop_imps)+)[2]
       apply ((wp find_vspace_for_asid_wp)+)[4]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def
                         word_neq_0_conv[symmetric])
   apply (frule (3) find_vspace_for_asid_eq_helper; fastforce simp: vspace_at_asid_def)
  apply simp
  done

crunch unmapPage
  for aligned'[wp]: pspace_aligned'
  (wp: crunch_wps simp: crunch_simps)

crunch unmapPage
  for distinct'[wp]: pspace_distinct'
  (wp: crunch_wps simp: crunch_simps)

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
  "page_entry_map m m' \<Longrightarrow> corres (dc \<oplus> dc) \<top> \<top>
      (unlessE (check_mapping_pptr pptr m) $ throwError ExceptionTypes_A.InvalidRoot)
      (checkMappingPPtr pptr m')"
  apply (simp add: liftE_bindE check_mapping_pptr_def
                   checkMappingPPtr_def)
  apply (cases m, simp_all add: liftE_bindE)
    apply (clarsimp simp: page_entry_map_def)
    apply (case_tac x1; auto simp: unlessE_def corres_returnOk)
   apply (clarsimp simp: page_entry_map_def)
   apply (case_tac x2; auto simp: unlessE_def corres_returnOk)
  apply (clarsimp simp: page_entry_map_def)
  apply (case_tac x3; auto simp: unlessE_def corres_returnOk)
  done

crunch checkMappingPPtr
  for inv[wp]: "P"
  (wp: crunch_wps loadObject_default_inv simp: crunch_simps)

lemma set_pt_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> set_pt p pt \<lbrace>\<lambda>x s. P (vs_lookup s)\<rbrace>"
  apply (simp add: set_object_def set_arch_obj_simps)
  apply (wpsimp wp: get_object_wp simp: a_type_simps obj_at_def)
  apply (erule rsubst [where P=P])
  by (rule order_antisym; rule vs_lookup_sub;
      clarsimp simp: obj_at_def vs_refs_def split: if_splits)

lemmas liftE_get_pde_corres = getObject_PDE_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
lemmas liftE_get_pte_corres = getObject_PTE_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
lemmas liftE_get_pdpte_corres = getObject_PDPTE_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]

lemma unmapPage_corres:
  assumes "sz' = sz" "asid' = asid" "vptr' = vptr" "pptr' = pptr"
  shows "corres dc (invs and
                     K (valid_unmap sz (asid,vptr) \<and> vptr < pptr_base \<and> asid_wf asid
                          \<and> canonical_address vptr))
                   (valid_objs' and valid_arch_state' and pspace_aligned' and
                     pspace_distinct' and no_0_obj' and cur_tcb')
                   (unmap_page sz asid vptr pptr)
                   (unmapPage sz' asid' vptr' pptr')"
  apply (clarsimp simp: assms unmap_page_def unmapPage_def ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>", OF _ corres_return_trivial])
      apply (rule corres_split_strengthen_ftE[where ftr'=dc])
         apply (rule findVSpaceForASID_corres[OF refl])
        apply (rule corres_splitEE)
           apply (rule_tac F = "vptr < pptr_base" in corres_gen_asm)
           apply (rule_tac P="\<exists>\<rhd> vspace and page_map_l4_at vspace and vspace_at_asid asid vspace
                              and (\<exists>\<rhd> vspace)
                              and valid_arch_state and valid_vspace_objs
                              and equal_kernel_mappings
                              and pspace_aligned and valid_global_objs and
                              K (valid_unmap sz (asid,vptr) \<and> canonical_address vptr )" and
                           P'="pspace_aligned' and pspace_distinct'" in corres_inst)
           apply clarsimp
           apply (rename_tac vspace)
           apply (cases sz, simp_all)[1]
             apply (rule corres_guard_imp)
               apply (rule_tac F = "vptr < pptr_base" in corres_gen_asm)
               apply (rule corres_split_strengthen_ftE[OF lookupPTSlot_corres])
                 apply simp
                 apply (rule corres_splitEE[OF liftE_get_pte_corres])
                   apply simp
                   apply (rule corres_split_norE[OF checkMappingPPtr_corres, where r=dc, simplified])
                      apply (simp add: page_entry_map_def)
                     apply simp
                     apply (rule storePTE_corres')
                     apply (((wpsimp  wp: hoare_vcg_all_liftE_R get_pte_wp getPTE_wp lookup_pt_slot_wp
                                    simp: unlessE_def is_aligned_pml4 if_apply_def2
                               split_del: if_split
                                simp_del: dc_simp)+
                             | wp (once) hoare_drop_imps)+)[9]
            apply (rule corres_guard_imp)
              apply (rule corres_split_strengthen_ftE[OF lookupPDSlot_corres])
                apply (simp del: dc_simp)
                apply (rule corres_splitEE[OF liftE_get_pde_corres])
                  apply (rule corres_split_norE[OF checkMappingPPtr_corres, where r=dc, simplified])
                     apply (simp add: page_entry_map_def)
                    apply simp
                    apply (rule storePDE_corres')
                    apply (((wpsimp  wp: hoare_vcg_all_liftE_R get_pde_wp getPDE_wp lookup_pd_slot_wp
                                   simp: unlessE_def is_aligned_pml4 if_apply_def2
                              split_del: if_split
                               simp_del: dc_simp)+
                           | wp (once) hoare_drop_imps)+)[9]
           apply (rule corres_guard_imp)
             apply (rule corres_split_strengthen_ftE[OF lookupPDPTSlot_corres])
               apply (simp del: dc_simp)
               apply (rule corres_splitEE[OF liftE_get_pdpte_corres])
                 apply (rule corres_split_norE[OF checkMappingPPtr_corres, where r=dc, simplified])
                    apply (simp add: page_entry_map_def)
                   apply simp
                   apply (rule storePDPTE_corres')
                   apply (((wpsimp  wp: hoare_vcg_all_liftE_R get_pdpte_wp getPDPTE_wp
                                        lookup_pdpt_slot_wp
                                  simp: unlessE_def is_aligned_pml4 if_apply_def2
                             split_del: if_split
                              simp_del: dc_simp)+
                           | wp (once) hoare_drop_imps)+)
          apply (rule corres_machine_op, rule corres_Id, rule refl, simp)
          apply (rule no_fail_invalidateTranslationSingleASID)
         apply wpsimp+
   apply (rule conjI[OF disjI1], clarsimp)
   apply (clarsimp simp: invs_vspace_objs invs_psp_aligned valid_unmap_def invs_arch_state
                         invs_equal_kernel_mappings)
  apply (clarsimp)
  done

definition
  "page_directory_invocation_map pdi pdi' \<equiv> case pdi of
   X64_A.PageDirectoryMap cap cte pdpte pdpt_slot pml4  \<Rightarrow>
      \<exists>cap' pdpte'. pdi' = PageDirectoryMap cap' (cte_map cte) pdpte' pdpt_slot pml4
            \<and> cap_relation cap cap' \<and> pdpte_relation' pdpte pdpte'
 | X64_A.PageDirectoryUnmap cap ptr \<Rightarrow>
      \<exists>cap'. pdi' = PageDirectoryUnmap cap' (cte_map ptr) \<and> cap_relation cap (ArchObjectCap cap')"

definition
  "page_invocation_map pgi pgi' \<equiv> case pgi of
    X64_A.PageMap c slot m vs \<Rightarrow>
      \<exists>c' m'. pgi' = PageMap c' (cte_map slot) m' vs \<and>
              cap_relation c c' \<and>
              mapping_map m m'
  | X64_A.PageUnmap c ptr \<Rightarrow>
      \<exists>c'. pgi' = PageUnmap c' (cte_map ptr) \<and>
         acap_relation c c'
  | X64_A.PageGetAddr ptr \<Rightarrow>
      pgi' = PageGetAddr ptr"

definition
  "valid_page_inv' pgi \<equiv> case pgi of
    PageMap cap ptr m vs \<Rightarrow>
      cte_wp_at' (is_arch_update' cap) ptr and valid_slots' m and valid_cap' cap
      and K (page_entry_map_corres m)
  | PageUnmap cap ptr \<Rightarrow>
      \<lambda>s. \<exists>r mt R sz d m. cap = PageCap r R mt sz d m \<and>
          cte_wp_at' (is_arch_update' (ArchObjectCap cap)) ptr s \<and>
          s \<turnstile>' (ArchObjectCap cap)
  | PageGetAddr ptr \<Rightarrow> \<top>"

crunch unmapPage
  for ctes[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: crunch_simps)

lemma updateCap_valid_slots'[wp]:
  "\<lbrace>valid_slots' x2\<rbrace> updateCap cte cte' \<lbrace>\<lambda>_ s. valid_slots' x2 s \<rbrace>"
  apply (case_tac x2, case_tac a)
    by (wpsimp simp: valid_slots'_def wp: hoare_vcg_ball_lift)+


crunch do_machine_op, store_pte, store_pde, store_pdpte
  for unique_table_refs[wp]: "\<lambda>s. (unique_table_refs (caps_of_state s))"

lemma set_cap_valid_slots_inv[wp]:
  "\<lbrace>valid_slots m\<rbrace> set_cap t st \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  apply (cases m; simp)
  apply (case_tac a; simp)
    by  (clarsimp simp: valid_slots_def, wp hoare_vcg_ball_lift set_cap.vs_lookup set_cap_typ_ats)+

lemma set_cap_same_refs_inv[wp]:
  "\<lbrace>\<lambda>s. same_refs m cap s\<rbrace> set_cap t st \<lbrace>\<lambda>rv s. same_refs m cap s\<rbrace>"
  by (cases m, (clarsimp simp: same_refs_def, wp)+)

definition
  "valid_page_map_inv cap ptr m vs \<equiv> (\<lambda>s. caps_of_state s ptr = Some cap) and same_refs m cap and
  valid_slots m and
  valid_cap cap and
  K (is_pg_cap cap \<and> empty_refs m) and
  (\<lambda>s. \<exists>sl. cte_wp_at (parent_for_refs m) sl s)"

lemma set_cap_valid_page_map_inv:
  "\<lbrace>valid_page_inv (X64_A.page_invocation.PageMap cap slot m vs)\<rbrace> set_cap cap slot \<lbrace>\<lambda>rv. valid_page_map_inv cap slot m vs\<rbrace>"
  apply (simp add: valid_page_inv_def valid_page_map_inv_def)
  apply (wp set_cap_cte_wp_at_cases hoare_vcg_ex_lift| simp)+
  apply clarsimp
  apply (rule conjI, fastforce simp: cte_wp_at_def)
  apply (rule_tac x=a in exI, rule_tac x=b in exI)
  apply (subgoal_tac "(a,b) \<noteq> slot")
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_def parent_for_refs_def)
  apply (auto simp: is_pt_cap_def is_pg_cap_def is_pd_cap_def is_pdpt_cap_def split: vm_page_entry.splits)
  done

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

lemma set_mi_tcb' [wp]:
  "\<lbrace> tcb_at' t \<rbrace> setMessageInfo receiver msg \<lbrace>\<lambda>rv. tcb_at' t\<rbrace>"
  by (simp add: setMessageInfo_def) wp


lemma setMRs_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def, wp crunch_wps)

lemmas setMRs_typ_at_lifts[wp] = typ_at_lifts [OF setMRs_typ_at']

lemma set_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' receiver \<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: setMRs_def)
  apply (wp dmo_invs' no_irq_mapM no_irq_storeWord crunch_wps|
         simp add: zipWithM_x_mapM split_def)+
  done

lemma same_refs_vs_cap_ref_eq:
  assumes "valid_slots entries s"
  assumes "same_refs entries cap s"
  assumes "same_refs entries cap' s"
  shows "vs_cap_ref cap = vs_cap_ref cap'"
  using assms
  apply (cases entries; clarsimp simp: same_refs_def valid_slots_def)
  apply (all \<open>rename_tac pte slots; case_tac slots; clarsimp\<close>)
  apply (case_tac pte; clarsimp)
  done

lemma performPageInvocation_corres:
  assumes "page_invocation_map pgi pgi'"
  notes mapping_map_simps = mapping_map_def page_entry_map_def attr_mask_def attr_mask'_def page_entry_ptr_map_def
  shows "corres (=) (invs and valid_page_inv pgi)
            (invs' and valid_page_inv' pgi')
            (perform_page_invocation pgi) (performPageInvocation pgi')"
proof -
  have pull_out_P:
    "\<And>P s Q c p. P s \<and> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> Q s c) \<longrightarrow> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> P s \<and> Q s c)"
   by blast
  show ?thesis
  using assms
  apply (cases pgi)
    apply (rename_tac cap prod entry vspace)

    \<comment> \<open>PageMap\<close>
    apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def
                          page_invocation_map_def)
    apply (rule corres_guard_imp)
      apply (rule_tac R="\<lambda>_. invs and (valid_page_map_inv cap (a,b) (aa,ba) vspace)
                         and (\<lambda>s. caps_of_state s (a,b) = Some cap)"
               and R'="\<lambda>_. invs' and valid_slots' (ab,bb) and pspace_aligned'
                       and pspace_distinct' and K (page_entry_map_corres (ab,bb))" in corres_split)
         apply (erule updateCap_same_master)
        apply (simp, rule corres_gen_asm2)
        apply (case_tac aa)
          apply clarsimp
          apply (frule (1) mapping_map_pte, clarsimp)
          apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def
                                neq_Nil_conv valid_page_map_inv_def)
          apply (rule corres_name_pre)
          apply (clarsimp simp: mapM_Cons bind_assoc split del: if_split)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF storePTE_corres'])
               apply simp
              apply (rule corres_split[where r'="(=)"])
                 apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                 apply (case_tac m; clarsimp)
                 apply (rule corres_fail[where P=\<top> and P'=\<top>])
                 apply (simp add: same_refs_def)
                apply (rule corres_underlying_split[where r'=dc, OF _ corres_return_eq_same[OF refl]
                                                          hoare_TrueI hoare_TrueI])
                apply simp
                apply (rule invalidatePageStructureCacheASID_corres)
               apply (wpsimp simp: invs_psp_aligned)+
         apply (frule (1) mapping_map_pde, clarsimp)
         apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def
                               neq_Nil_conv valid_page_map_inv_def)
         apply (rule corres_name_pre)
         apply (clarsimp simp: mapM_Cons bind_assoc split del: if_split)
         apply (rule corres_guard_imp)
           apply (rule corres_split[OF storePDE_corres'])
              apply simp
             apply (rule corres_split[where r'="(=)"])
                apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                apply (case_tac m; clarsimp)
                apply (rule corres_fail[where P=\<top> and P'=\<top>])
                apply (simp add: same_refs_def)
               apply simp
               apply (rule corres_underlying_split[where r'=dc, OF _ corres_return_eq_same[OF refl]
                                                         hoare_TrueI hoare_TrueI])
               apply (rule invalidatePageStructureCacheASID_corres)
              apply (wpsimp simp: invs_psp_aligned)+
        apply (frule (1) mapping_map_pdpte, clarsimp)
        apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def
                              neq_Nil_conv valid_page_map_inv_def)
        apply (rule corres_name_pre)
        apply (clarsimp simp: mapM_Cons bind_assoc split del: if_split)
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF storePDPTE_corres'])
             apply simp
            apply (rule corres_split[where r'="(=)"])
               apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
               apply (case_tac m; clarsimp)
               apply (rule corres_fail[where P=\<top> and P'=\<top>])
               apply (simp add: same_refs_def)
              apply simp
              apply (rule corres_underlying_split[where r'=dc, OF _ corres_return_eq_same[OF refl]
                                                        hoare_TrueI hoare_TrueI])
              apply (rule invalidatePageStructureCacheASID_corres)
             apply (wpsimp simp: invs_psp_aligned)+
       apply (wp arch_update_cap_invs_map set_cap_valid_page_map_inv)
      apply (wp arch_update_updateCap_invs)
     apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct valid_page_inv_def
                           cte_wp_at_caps_of_state is_arch_update_def is_cap_simps)
     apply (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)
     apply (auto simp: cte_wp_at_ctes_of valid_page_inv'_def)[1]
     apply (erule (3) subst[OF same_refs_vs_cap_ref_eq, rotated 2])
    apply (clarsimp simp: invs_pspace_aligned' invs_pspace_distinct' valid_page_inv'_def cte_wp_at'_def)

    \<comment> \<open>PageUnmap\<close>
   apply (clarsimp simp: performPageInvocation_def perform_page_invocation_def
                         page_invocation_map_def)
   apply (rule corres_assume_pre)
   apply (clarsimp simp: valid_page_inv_def valid_page_inv'_def isCap_simps is_page_cap_def
                   cong: option.case_cong prod.case_cong)
   apply (case_tac m)
    apply (simp add: split_def)+
   apply (case_tac maptyp; simp)
    apply (rule corres_fail, clarsimp simp: valid_cap_def)
   apply (simp add: perform_page_invocation_unmap_def performPageInvocationUnmap_def split_def)
    apply (rule corres_guard_imp)
     apply (rule corres_underlying_split[where r'=dc, OF _ corres_return_eq_same[OF refl]
                                               hoare_TrueI hoare_TrueI])
     apply (rule corres_split)
        apply (rule unmapPage_corres[OF refl refl refl refl])
       apply (rule corres_split[where r'=acap_relation])
          apply simp
          apply (rule corres_rel_imp)
           apply (rule get_cap_corres_all_rights_P[where P=is_arch_cap], rule refl)
          apply (clarsimp simp: is_cap_simps)
         apply (rule_tac F="is_page_cap cap" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_page_cap_def update_map_data_def)
        apply (wp get_cap_wp getSlotCap_wp)+
      apply (simp add: cte_wp_at_caps_of_state)
      apply (strengthen pull_out_P)+
      apply wp
     apply (simp add: cte_wp_at_ctes_of)
     apply wp
    apply (clarsimp simp: valid_unmap_def cte_wp_at_caps_of_state)
    apply (clarsimp simp: is_cap_simps split: cap.splits arch_cap.splits)
    apply (clarsimp simp: cap_rights_update_def is_page_cap_def cap_master_cap_simps
                          update_map_data_def acap_rights_update_def)
    apply (clarsimp simp add: wellformed_mapdata_def valid_cap_def mask_def)
    apply auto[1]
   apply (auto simp: cte_wp_at_ctes_of)[1]

    \<comment> \<open>PageGetAddr\<close>
  apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def
                        page_invocation_map_def fromPAddr_def)
  done
qed

definition
  "page_table_invocation_map pti pti' \<equiv> case pti of
     X64_A.PageTableMap cap ptr pde pd_slot vspace \<Rightarrow>
    \<exists>cap' pde'. pti' = PageTableMap cap' (cte_map ptr) pde' pd_slot vspace \<and>
                cap_relation cap cap' \<and>
                pde_relation' pde pde'
   | X64_A.PageTableUnmap cap ptr \<Rightarrow>
    \<exists>cap'. pti' = PageTableUnmap cap' (cte_map ptr) \<and>
           cap_relation cap (ArchObjectCap cap')"

definition
  "valid_pti' pti \<equiv> case pti of
     PageTableMap cap slot pde pdeSlot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pde' pde and K (case cap of ArchObjectCap (PageTableCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PageTableUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageTableCap cap)"

lemma clear_page_table_corres:
  "corres dc (pspace_aligned and page_table_at p)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pte X64_A.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])
    (mapM_x (swp storePTE X64_H.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])"
  apply (rule_tac F="is_aligned p ptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="(=)"
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pte_at x s \<and> pspace_aligned s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule storePTE_corres')
        apply (simp add:pte_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_table_pte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

lemma clear_page_directory_corres:
  "corres dc (pspace_aligned and page_directory_at p)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pde X64_A.InvalidPDE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])
    (mapM_x (swp storePDE X64_H.InvalidPDE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])"
  apply (rule_tac F="is_aligned p pdBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="(=)"
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pde_at x s \<and> pspace_aligned s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule storePDE_corres')
        apply (simp add:pde_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_directory_pde_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

lemma clear_pdpt_corres:
  "corres dc (pspace_aligned and pd_pointer_table_at p)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pdpte X64_A.InvalidPDPTE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])
    (mapM_x (swp storePDPTE X64_H.InvalidPDPTE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])"
  apply (rule_tac F="is_aligned p pdptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="(=)"
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pdpte_at x s \<and> pspace_aligned s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule storePDPTE_corres')
        apply (simp add:pde_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule pd_pointer_table_pdpte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

crunch invalidatePageStructureCacheASID, unmapPageTable, unmapPageDirectory, unmapPDPT
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps hoare_vcg_all_liftE_R)

lemmas unmapPageTable_typ_ats[wp] = typ_at_lifts[OF unmapPageTable_typ_at']
lemmas unmapPageDirectory_typ_ats[wp] = typ_at_lifts[OF unmapPageDirectory_typ_at']
lemmas unmapPDPT_typ_ats[wp] = typ_at_lifts[OF unmapPDPT_typ_at']

lemma performPageTableInvocation_corres:
  "page_table_invocation_map pti pti' \<Longrightarrow>
   corres dc
          (invs and valid_pti pti)
          (invs' and valid_pti' pti')
          (perform_page_table_invocation pti)
          (performPageTableInvocation pti')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_page_table_invocation_def performPageTableInvocation_def)
  apply (cases pti)
   apply (rename_tac cap slot pde pd_slot vspace)
   apply (clarsimp simp: page_table_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pti_def valid_pti'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF updateCap_same_master])
        apply assumption
       apply (rule corres_split[OF storePDE_corres'])
          apply simp
         apply (rule corres_split[where r'="(=)" and P="\<top>" and P'="\<top>"])
            apply (case_tac cap; clarsimp simp add: is_pt_cap_def)
            apply (solves \<open>clarsimp split: option.splits\<close>)
           apply simp
           apply (rule invalidatePageStructureCacheASID_corres)
          apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
   apply auto[1]
  apply (clarsimp simp: split:X64_H.pde.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: page_table_invocation_map_def)
  apply (rule_tac F="is_pt_cap cap" in corres_req)
   apply (clarsimp simp: valid_pti_def)
  apply (clarsimp simp: is_pt_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_if[OF refl])
        apply (rule corres_split[OF unmapPageTable_corres[OF refl refl refl]])
          apply (rule clear_page_table_corres[simplified bit_simps bitSimps, simplified])
         apply wp+
       apply (rule corres_trivial, simp)
      apply (simp add: liftM_def)
      apply (rule corres_split[OF get_cap_corres])
        apply (rule_tac F="is_pt_cap x" in corres_gen_asm)
        apply (rule updateCap_same_master)
        apply (clarsimp simp: is_pt_cap_def update_map_data_def)
       apply (wp get_cap_wp)
      apply wp
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
                     wellformed_mapdata_def
              split: option.split_asm)[1]
  apply (auto simp: valid_pti'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "valid_pdi' pdi \<equiv> case pdi of
     PageDirectoryMap cap slot pdpte pdptSlot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pdpte' pdpte and K (case cap of ArchObjectCap (PageDirectoryCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PageDirectoryUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageDirectoryCap cap)"

lemma flush_all_corres [corres]:
  assumes "vspace' = vspace" "asid' = asid"
  shows "corres dc \<top> \<top> (flush_all vspace asid) (flushAll vspace' asid')"
  apply (simp add: assms flush_all_def flushAll_def ucast_id)
  apply (rule corres_rel_imp[OF _ dc_simp])
  apply (rule corres_machine_op)
  apply (rule corres_underlying_trivial[OF no_fail_invalidateASID])
  done

lemma unmapPageDirectory_corres:
  assumes "asid' = asid" "vptr' = vptr" "pd' = pd"
  notes liftE_get_pdpte_corres = getObject_PDPTE_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and page_directory_at pd and
           K (0 < asid \<and> is_aligned vptr pdpt_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid_wf asid))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_pd asid vptr pd)
          (unmapPageDirectory asid' vptr' pd')"
  apply (clarsimp simp: assms unmap_pd_def unmapPageDirectory_def flushPD_def
                        ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>", OF _ corres_return_trivial])
      apply (rule corres_split_eqrE[OF findVSpaceForASID_corres[OF refl]])
        apply (rule corres_split_eqrE[OF lookupPDPTSlot_corres])
          apply (rule corres_splitEE[OF liftE_get_pdpte_corres])
            apply (rule corres_splitEE[where r'=dc])
               apply (case_tac "\<exists>addr x xa. pdpte = X64_A.PageDirectoryPDPTE addr x xa";
                      fastforce intro!: corres_returnOkTT
                                simp: lookup_failure_map_def pdpte_relation_def
                                split: X64_A.pdpte.splits)
              apply simp
              apply (rule corres_split_nor[OF flush_all_corres[OF refl refl]])
                apply (rule corres_split[OF storePDPTE_corres'
                                            invalidatePageStructureCacheASID_corres])
                  apply ((wpsimp wp: get_pdpte_wp simp: pdpte_at_def)+)[8]
          apply (wpsimp wp: hoare_drop_imps)
         apply ((wp lookup_pdpt_slot_wp find_vspace_for_asid_wp)+)[6]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def
                         word_neq_0_conv[symmetric])
   apply (frule (3) find_vspace_for_asid_eq_helper;
          fastforce simp: vspace_at_asid_def pdpte_at_def)
  apply simp
  done

crunch unmap_pd, unmap_pdpt
  for valid_objs[wp]: "valid_objs"
  and pspace_aligned[wp]: "pspace_aligned"
  and pspace_distinct[wp]: "pspace_distinct"

lemma performPageDirectoryInvocation_corres:
  "page_directory_invocation_map pdi pdi' \<Longrightarrow>
   corres dc
          (invs and valid_pdi pdi)
          (invs' and valid_pdi' pdi')
          (perform_page_directory_invocation pdi)
          (performPageDirectoryInvocation pdi')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_page_directory_invocation_def performPageDirectoryInvocation_def)
  apply (cases pdi)
   apply (rename_tac cap slot pdpte pdpt_slot vspace)
   apply (clarsimp simp: page_directory_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pdi_def valid_pdi'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF updateCap_same_master])
        apply assumption
       apply (rule corres_split[OF storePDPTE_corres'])
          apply simp
         apply (rule corres_split[where r'="(=)" and P="\<top>" and P'="\<top>"])
            apply (case_tac cap; clarsimp simp add: is_pd_cap_def)
            apply (solves \<open>clarsimp split: option.splits\<close>)
           apply simp
           apply (rule invalidatePageStructureCacheASID_corres)
          apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pdi'_def)
   apply auto[1]
  apply (clarsimp split:X64_H.pdpte.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: page_directory_invocation_map_def)
  apply (rule_tac F="is_pd_cap cap" in corres_req)
   apply (clarsimp simp: valid_pdi_def)
  apply (clarsimp simp: is_pd_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_if[OF refl])
        apply (rule corres_split[OF unmapPageDirectory_corres[OF refl refl refl]])
          apply (rule clear_page_directory_corres[simplified bit_simps bitSimps, simplified])
         apply wp+
       apply (rule corres_trivial, simp)
      apply (simp add: liftM_def)
      apply (rule corres_split[OF get_cap_corres])
        apply (rule_tac F="is_pd_cap x" in corres_gen_asm)
        apply (rule updateCap_same_master)
        apply (clarsimp simp: is_pd_cap_def update_map_data_def)
       apply (wp get_cap_wp)
      apply wp
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pdi_def cte_wp_at_caps_of_state
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
                     wellformed_mapdata_def vmsz_aligned_def
              split: option.split_asm)[1]
   apply (auto simp: valid_pdi'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "valid_pdpti' pdi \<equiv> case pdi of
     PDPTMap cap slot pml4e pml4Slot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pml4e' pml4e and K (case cap of ArchObjectCap (PDPointerTableCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PDPTUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPDPointerTableCap cap)"

lemma unmapPDPT_corres:
  assumes "asid' = asid" "vptr' = vptr" "pd' = pd"
  notes liftE_get_pml4e_corres = get_pml4e_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and pd_pointer_table_at pd and
           K (0 < asid \<and> is_aligned vptr pml4_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid_wf asid))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_pdpt asid vptr pd)
          (unmapPDPT asid vptr pd)"
  apply (clarsimp simp: assms unmap_pdpt_def unmapPDPT_def flushPDPT_def
                        invalidatePageStructureCacheASID_def
                        ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>", OF _ corres_return_trivial])
      apply (rule corres_split_eqrE[OF findVSpaceForASID_corres[OF refl]])
        apply (rule corres_splitEE[OF liftE_get_pml4e_corres])
          apply (rule corres_splitEE[where r'=dc])
             apply (case_tac "\<exists>addr a b. rv = X64_A.PDPointerTablePML4E addr a b";
                    fastforce intro!: corres_returnOkTT
                              simp: lookup_failure_map_def pml4e_relation_def
                              split: X64_A.pml4e.splits)
            apply simp
            apply (rule corres_split_nor[OF flush_all_corres[OF refl refl]])
              apply (rule store_pml4e_corres'[OF refl], simp)
             apply ((wpsimp wp: get_pml4e_wp simp: pml4e_at_def)+)[5]
        apply (wpsimp wp: hoare_drop_imps)
       apply ((wp find_vspace_for_asid_wp)+)[4]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def
                         word_neq_0_conv[symmetric])
   apply (frule (3) find_vspace_for_asid_eq_helper)
   apply (rule conjI[OF page_map_l4_pml4e_at_lookupI]; simp)
   apply (clarsimp simp: obj_at_def a_type_simps lookup_pml4_slot_def)
   apply (fastforce intro!: is_aligned_add is_aligned_shiftl_self
                    elim: is_aligned_weaken simp: bit_simps)
  apply simp
  done

definition
  "pdpt_invocation_map pdpti pdpti' \<equiv> case pdpti of
   X64_A.PDPTMap cap cte pml4e pml4_slot vspace  \<Rightarrow>
      \<exists>cap' pml4e'. pdpti' = PDPTMap cap' (cte_map cte) pml4e' pml4_slot vspace
            \<and> cap_relation cap cap' \<and> pml4e_relation' pml4e pml4e'
 | X64_A.PDPTUnmap cap ptr \<Rightarrow>
      \<exists>cap'. pdpti' = PDPTUnmap cap' (cte_map ptr) \<and> cap_relation cap (ArchObjectCap cap')"

lemma performPDPTInvocation_corres:
  "pdpt_invocation_map pdpti pdpti' \<Longrightarrow>
   corres dc
          (invs and valid_pdpti pdpti)
          (invs' and valid_pdpti' pdpti')
          (perform_pdpt_invocation pdpti)
          (performPDPTInvocation pdpti')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_pdpt_invocation_def performPDPTInvocation_def)
  apply (cases pdpti)
   apply (rename_tac cap slot pml4e pml4_slot vspace)
   apply (clarsimp simp: pdpt_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pdpti_def valid_pdpti'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF updateCap_same_master])
        apply assumption
       apply (rule corres_split)
          apply (rule store_pml4e_corres'; simp)
         apply (rule corres_split[where r'="(=)" and P="\<top>" and P'="\<top>"])
            apply (case_tac cap; clarsimp simp add: is_pdpt_cap_def)
            apply (solves \<open>clarsimp split: option.splits\<close>)
           apply simp
           apply (rule invalidatePageStructureCacheASID_corres)
          apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pdpti'_def)
   apply auto[1]
  apply (clarsimp split:X64_H.pml4e.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: pdpt_invocation_map_def)
  apply (rule_tac F="is_pdpt_cap cap" in corres_req)
   apply (clarsimp simp: valid_pdpti_def)
  apply (clarsimp simp: is_pdpt_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_if[OF refl])
        apply (rule corres_split[OF unmapPDPT_corres[OF refl refl refl]])
          apply (rule clear_pdpt_corres[simplified bit_simps bitSimps, simplified])
         apply wp+
       apply (rule corres_trivial, simp)
      apply (simp add: liftM_def)
      apply (rule corres_split[OF get_cap_corres])
        apply (rule_tac F="is_pdpt_cap x" in corres_gen_asm)
        apply (rule updateCap_same_master)
        apply (clarsimp simp: is_pdpt_cap_def update_map_data_def)
       apply (wp get_cap_wp)
      apply wp
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pdpti_def cte_wp_at_caps_of_state
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
                     wellformed_mapdata_def vmsz_aligned_def
              split: option.split_asm)[1]
  apply (auto simp: valid_pdpti'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "asid_pool_invocation_map ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow> Assign asid p (cte_map slot)"

definition
  "isPML4Cap' cap \<equiv> \<exists>p asid. cap = (ArchObjectCap (PML4Cap p asid))"

definition
  "valid_apinv' ap \<equiv> case ap of Assign asid p slot \<Rightarrow>
    asid_pool_at' p and cte_wp_at' (isPML4Cap' o cteCap) slot and K
    (0 < asid \<and> asid_wf asid)"

lemma performASIDPoolInvocation_corres:
  assumes "ap' = asid_pool_invocation_map ap"
  shows "corres dc (valid_objs and pspace_aligned and pspace_distinct and valid_apinv ap)
                   (pspace_aligned' and pspace_distinct' and valid_apinv' ap')
                   (perform_asid_pool_invocation ap)
                   (performASIDPoolInvocation ap')"
  proof -
    { fix rv p asid asid'
      assume "rv = cap.ArchObjectCap (arch_cap.PML4Cap p asid)"
      hence "(case rv of cap.ArchObjectCap (arch_cap.PML4Cap p asid)
                 \<Rightarrow> cap.ArchObjectCap (arch_cap.PML4Cap p asid'))
               = cap.ArchObjectCap (arch_cap.PML4Cap p asid')"
      by simp
    } note helper = this
    show ?thesis
      using assms
      apply (clarsimp simp: perform_asid_pool_invocation_def performASIDPoolInvocation_def)
      apply (cases ap, simp add: asid_pool_invocation_map_def)
      apply (rename_tac word1 word2 prod)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF getSlotCap_corres[OF refl] _ get_cap_wp getSlotCap_wp])
        apply (rule_tac F="\<exists>p asid. rv = Structures_A.ArchObjectCap (X64_A.PML4Cap p asid)"
                 in corres_gen_asm; elim exE)
        apply (simp cong: corres_weak_cong)
        apply (rule subst[OF helper], assumption)
        apply (rule corres_split[OF updateCap_same_master])
           apply simp
          unfolding store_asid_pool_entry_def
          apply (rule corres_split[where r'="\<lambda>pool pool'. pool = pool' \<circ> ucast"])
             apply (simp cong: corres_weak_cong)
             apply (rule corres_rel_imp)
              apply (rule getObject_ASIDPool_corres'[OF refl])
             apply simp
            apply (simp only: return_bind cong: corres_weak_cong)
            apply (rule setObject_ASIDPool_corres')
            apply (rule ext; clarsimp simp: inv_def mask_asid_low_bits_ucast_ucast)
           apply (wp getASID_wp)+
         apply (wpsimp wp: set_cap_typ_at hoare_drop_imps)
        apply (wpsimp wp: hoare_drop_imps)
       by (auto simp: valid_apinv_def cte_wp_at_def is_pml4_cap_def
                      is_cap_simps cap_master_cap_def obj_at_def a_type_simps
                      valid_apinv'_def cte_wp_at'_def)
  qed

lemma setCurrentUserCR3_obj_at [wp]:
  "\<lbrace>\<lambda>s. P (obj_at' P' t s)\<rbrace> setCurrentUserCR3 c \<lbrace>\<lambda>rv s. P (obj_at' P' t s)\<rbrace>"
  apply (simp add: setCurrentUserCR3_def)
  apply (wp doMachineOp_obj_at|wpc|simp)+
  done

lemmas getCurrentUserCR3_obj_at [wp]
  = getCurrentUserCR3_inv[of "\<lambda>s. P (obj_at' P' t s)" for P P' t]

crunch setVMRoot
  for obj_at[wp]: "\<lambda>s. P (obj_at' P' t s)"
  (simp: crunch_simps)

crunch doMachineOp
  for it[wp]:  "\<lambda>s. P (ksIdleThread s)"
  and arch[wp]: "\<lambda>s. P (ksArchState s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"

lemma setCurrentUserCR3_invs' [wp]:
  "\<lbrace>invs' and K (valid_cr3' c)\<rbrace> setCurrentUserCR3 c \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding setCurrentUserCR3_def
  apply wpsimp
  by (clarsimp simp: invs'_def valid_state'_def valid_global_refs'_def global_refs'_def
                     valid_arch_state'_def valid_machine_state'_def ct_not_inQ_def
                     ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma setCurrentUserCR3_invs_no_cicd' [wp]:
  "\<lbrace>invs_no_cicd' and K (valid_cr3' c)\<rbrace> setCurrentUserCR3 c \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  unfolding setCurrentUserCR3_def
  apply wpsimp
  by (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def
                     valid_global_refs'_def global_refs'_def
                     valid_arch_state'_def valid_machine_state'_def ct_not_inQ_def
                     ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma valid_cr3'_makeCR3:
  "asid_wf asid \<Longrightarrow> valid_cr3' (makeCR3 addr asid)"
  apply (clarsimp simp: valid_cr3'_def makeCR3_def bit_simps
                        is_aligned_andI2[OF is_aligned_shift])
  apply (rule order.trans[OF word_and_le1])
  apply (simp add: mask_def asid_bits_def)
  done

lemma getCurrentUserCR3_wp:
  "\<lbrace> \<lambda>s. Q (x64KSCurrentUserCR3 (ksArchState s)) s \<rbrace> getCurrentUserCR3 \<lbrace> Q \<rbrace>"
  by (wpsimp simp: getCurrentUserCR3_def)

lemma setVMRoot_invs [wp]:
  "\<lbrace>invs'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def setCurrentUserVSpaceRoot_def)
  apply (wp whenE_wp getCurrentUserCR3_wp findVSpaceForASID_vs_at_wp
         | wpcw
         | clarsimp simp: if_apply_def2 asid_wf_0
         | strengthen valid_cr3'_makeCR3)+
  done

lemma setVMRoot_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def setCurrentUserVSpaceRoot_def)
  apply (wp whenE_wp getCurrentUserCR3_wp findVSpaceForASID_vs_at_wp
         | wpcw
         | clarsimp simp: if_apply_def2 asid_wf_0
         | strengthen valid_cr3'_makeCR3)+
  done

crunch setVMRoot
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps
       loadObject_default_def)

crunch findVSpaceForASID
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv)

crunch deleteASIDPool
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv mapM_wp')

crunch lookupPTSlot
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv)

crunch storePTE
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle')

crunch storePDE
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle')

crunch storePDPTE
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle')

crunch storePML4E
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle')

crunch flushTable
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def
   wp: setObject_idle' hoare_drop_imps mapM_x_wp')

crunch deleteASID
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def updateObject_default_def
   wp: getObject_inv)

crunch performPageTableInvocation
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch performPageDirectoryInvocation
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch performPDPTInvocation
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch performPageInvocation
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma performASIDPoolInvocation_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wpsimp simp: performASIDPoolInvocation_def
               wp: getASID_wp hoare_vcg_imp_lift[where P'=\<bottom>, simplified])

lemmas performPageTableInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageTableInvocation_typ_at']

lemmas performPageDirectoryInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageDirectoryInvocation_typ_at']

lemmas performPDPTInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPDPTInvocation_typ_at']

lemmas performPageInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageInvocation_typ_at']

lemmas performASIDPoolInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performASIDPoolInvocation_typ_at']

lemma storePDE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePDE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePTE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePDPTE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePDPTE p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePDPTE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePML4E_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePML4E p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePML4E_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setASID_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma dmo_ct[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> doMachineOp m \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  done

lemma storePDE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma storePDPTE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePDPTE p pde \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma storePML4E_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePML4E p pde \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

crunch storePDE, storePDPTE, storePML4E
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def ignore_del: setObject)

lemma storePDE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePDE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePDE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

lemma storePDPTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePDPTE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePDPTE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

lemma storePML4E_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePML4E ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePML4E_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

crunch storePDE, storePDPTE, storePML4E
  for norqL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and norqL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: updateObject_default_def)

lemma storePDE_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: storePDE_def)
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma storePDE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs live'_def hyp_live'_def)
  done

lemma setObject_pde_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma storePDPTE_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: storePDPTE_def)
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma storePDPTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs live'_def hyp_live'_def)
  done

lemma setObject_pdpte_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pdpte::pdpte) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma storePML4E_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: storePML4E_def)
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma storePML4E_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs live'_def hyp_live'_def)
  done

lemma setObject_pml4e_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pml4e::pml4e) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

crunch storePDE, storePDPTE, storePML4E
  for ksInterruptState [wp]: "\<lambda>s. P (ksInterruptState s)"

lemma storePDE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

method valid_idle'_setObject uses simp =
  simp add: valid_idle'_def, rule hoare_lift_Pf [where f="ksIdleThread"]; wpsimp?;
  (wpsimp wp: obj_at_setObject2[where P="idle_tcb'", simplified] hoare_drop_imp
        simp: simp
   | clarsimp dest!: updateObject_default_result)+

lemma storePDE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by (valid_idle'_setObject simp: storePDE_def)

lemma storePDPTE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePDPTE p pde \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePDPTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePDPTE p pde \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by (valid_idle'_setObject simp: storePDPTE_def)

lemma storePML4E_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePML4E p pde \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePML4E_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePML4E p pde \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by (valid_idle'_setObject simp: storePML4E_def)

crunch storePDE, storePDPTE, storePML4E
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"
  and cur'[wp]: "\<lambda>s. P (ksCurThread s)"

lemma storePDE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePDE pde p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

lemma storePDPTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePDPTE pde p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

lemma storePML4E_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePML4E pde p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

crunch storePDE, storePDPTE, storePML4E
  for no_0_obj'[wp]: no_0_obj'

lemma storePDE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePDE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma storePDPTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePDPTE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePDPTE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma storePML4E_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePML4E p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePML4E_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

crunch storePDE, storePDPTE, storePML4E
  for pspace_domain_valid[wp]: "pspace_domain_valid"

lemma storePDE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePDE p pde \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePDE_nosch])
  apply (simp add: storePDE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PDE_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad comp_def)+
  done

lemma setObject_pde_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pde) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pde_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pde) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePDE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
by (simp add: storePDE_def) wp

lemma storePDE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePDE_def) wp

lemma storePDE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePDE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePDE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pte_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma setObject_pde_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma storePDPTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePDPTE_nosch])
  apply (simp add: storePDPTE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PDPTE_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad comp_def)+
  done

lemma setObject_pdpte_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pdpte) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pdpte_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pdpte) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePDPTE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
by (simp add: storePDPTE_def) wp

lemma storePDPTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePDPTE_def) wp

lemma storePDPTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePDPTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePDPTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pdpte_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pdpte::pdpte) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma storePML4E_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePML4E_nosch])
  apply (simp add: storePML4E_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PML4E_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad comp_def)+
  done

lemma setObject_pml4e_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pml4e) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pml4e_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pml4e) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePML4E_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
by (simp add: storePML4E_def) wp

lemma storePML4E_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePML4E_def) wp

lemma storePML4E_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePML4E_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePML4E_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pml4e_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pml4e::pml4e) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

crunch storePTE, storePDE, storePDPTE, storePML4E
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and pspace_canonical'[wp]: "pspace_canonical'"
  and pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"

crunch storePTE, storePDE, storePDPTE, storePML4E
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv)

lemma storePTE_tcbs_of'[wp]:
  "storePTE c (pte::pte) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  unfolding storePTE_def
  by setObject_easy_cases

lemma storePDE_tcbs_of'[wp]:
  "storePDE c (pde::pde) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  unfolding storePDE_def
  by setObject_easy_cases

lemma storePDPTE_tcbs_of'[wp]:
  "storePDPTE c (pdpte::pdpte) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  unfolding storePDPTE_def
  by setObject_easy_cases

lemma storePML4E_tcbs_of'[wp]:
  "storePML4E c (pml4e::pml4e) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  unfolding storePML4E_def
  by setObject_easy_cases

lemma storePDE_invs[wp]:
  "\<lbrace>invs' and valid_pde' pde\<rbrace>
      storePDE p pde
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift valid_bitmaps_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma storePDPTE_invs[wp]:
  "\<lbrace>invs' and valid_pdpte' pde\<rbrace>
      storePDPTE p pde
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift valid_bitmaps_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma storePML4E_invs[wp]:
  "\<lbrace>invs' and valid_pml4e' pde\<rbrace>
      storePML4E p pde
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift valid_bitmaps_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma storePTE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

crunch storePTE
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: updateObject_default_def ignore_del: setObject)

crunch storePTE
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def)

lemma storePTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePTE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePTE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

crunch storePTE
  for norqL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (simp: updateObject_default_def)

crunch storePTE
  for norqL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: updateObject_default_def)

lemma storePTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs live'_def hyp_live'_def)
  done

lemma setObject_pte_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

crunch storePTE
  for ksInt'[wp]: "\<lambda>s. P (ksInterruptState s)"

lemma storePTE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by (valid_idle'_setObject simp: storePTE_def)

crunch storePTE
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"

crunch storePTE
  for cur'[wp]: "\<lambda>s. P (ksCurThread s)"

lemma storePTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePTE pte p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

lemma storePTE_valid_objs [wp]:
  "\<lbrace>valid_objs' and valid_pte' pte\<rbrace> storePTE p pte \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: storePTE_def doMachineOp_def split_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps|wpc|simp)+
   apply (rule setObject_valid_objs')
   prefer 2
   apply assumption
  apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: valid_obj'_def)
  done

lemma storePTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePTE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePTE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

crunch storePTE
  for pspace_domain_valid[wp]: "pspace_domain_valid"

lemma storePTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePTE_nosch])
  apply (simp add: storePTE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_pte_ct)
  apply (rule obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad comp_def)+
  done

lemma setObject_pte_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pte_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePTE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  by (simp add: storePTE_def) wp

lemma storePTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  by (simp add: storePTE_def) wp


lemma storePTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma storePTE_invs [wp]:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> storePTE p pte \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift valid_bitmaps_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma setASIDPool_valid_objs [wp]:
  "\<lbrace>valid_objs' and valid_asid_pool' ap\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_valid_objs')
   prefer 2
   apply assumption
  apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: valid_obj'_def)
  done

lemma setASIDPool_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma setASIDPool_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (wp setObject_nosch updateObject_default_inv|simp)+

lemma setASIDPool_ksQ [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace>
     setObject ptr (ap::asidpool)
   \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def)
  apply (wp setObject_ko_wp_at
            | simp add: objBits_simps archObjSize_def)+
   apply (simp add: pageBits_def)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  done

lemma setASIDPool_qsL1 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_qsL2 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs pageBits_def
                       live'_def hyp_live'_def)
  done

lemma setASIDPool_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma setASIDPool_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma setASIDPool_it' [wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksIdleThread s)\<rbrace>"
  by (wp setObject_it updateObject_default_inv|simp)+

lemma setASIDPool_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by valid_idle'_setObject

lemma setASIDPool_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF setObject_ksInterrupt])
    apply (simp, rule updateObject_default_inv)
   apply (rule hoare_use_eq [where f=ksMachineState, OF setObject_ksMachine])
    apply (simp, rule updateObject_default_inv)
   apply wp
  apply assumption
  done


lemma setASIDPool_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma setASIDPool_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF setObject_nosch])
   apply (simp add: updateObject_default_def | wp)+
  apply (rule hoare_weaken_pre)
   apply (wps setObject_ASID_ct)
  apply (rule obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad comp_def)+
  done

lemma setObject_asidpool_cur'[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def)
  apply (wp | wpc | simp add: updateObject_default_def)+
  done

lemma setObject_asidpool_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_asidpool_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setObject_asidpool_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma setObject_asidpool_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
      apply (wp hoare_vcg_disj_lift)+
  done

lemma setObject_ap_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma setObject_asidpool_tcbs_of'[wp]:
  "setObject c (asidpool::asidpool) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setASIDPool_invs [wp]:
  "\<lbrace>invs' and valid_asid_pool' ap\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
             updateObject_default_inv valid_bitmaps_lift
           | simp add: cteCaps_of_def
           | rule setObject_ksPSpace_only)+
  apply (clarsimp simp add: setObject_def o_def)
  done

crunch unmapPageTable
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch unmapPageDirectory
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch unmapPDPT
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas storePDE_Invalid_invs = storePDE_invs[where pde=InvalidPDE, simplified]
lemmas storePDPTE_Invalid_invs = storePDPTE_invs[where pde=InvalidPDPTE, simplified]
lemmas storePML4E_Invalid_invs = storePML4E_invs[where pde=InvalidPML4E, simplified]

crunch unmapPageTable, unmapPageDirectory, unmapPDPT
  for invs'[wp]: "invs'"
  (ignore: storePDE storePDPTE storePML4E doMachineOp
       wp: storePDE_Invalid_invs storePDPTE_Invalid_invs storePML4E_Invalid_invs mapM_wp'
           crunch_wps
     simp: crunch_simps)

lemma perform_pti_invs [wp]:
  "\<lbrace>invs' and valid_pti' pti\<rbrace> performPageTableInvocation pti \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPageTableInvocation_def getSlotCap_def
                 split: page_table_invocation.splits)
  apply (intro conjI allI impI)
   apply (rule hoare_pre)
    apply (wp arch_update_updateCap_invs getCTE_wp
              hoare_vcg_ex_lift  mapM_x_wp'
                | wpc | simp add: o_def
                | (simp only: imp_conv_disj, rule hoare_vcg_disj_lift))+
   apply (clarsimp simp: valid_pti'_def cte_wp_at_ctes_of
                         is_arch_update'_def isCap_simps valid_cap'_def
                         capAligned_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: arch_update_updateCap_invs valid_pde_lift' hoare_vcg_all_lift hoare_vcg_ex_lift
             | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
  done

lemma perform_pdi_invs [wp]:
  "\<lbrace>invs' and valid_pdi' pdi\<rbrace> performPageDirectoryInvocation pdi \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPageDirectoryInvocation_def getSlotCap_def
                 split: page_directory_invocation.splits)
  apply (intro conjI allI impI)
   apply (rule hoare_pre)
    apply (wp arch_update_updateCap_invs getCTE_wp
              hoare_vcg_ex_lift  mapM_x_wp'
                | wpc | simp add: o_def
                | (simp only: imp_conv_disj, rule hoare_vcg_disj_lift))+
   apply (clarsimp simp: valid_pdi'_def cte_wp_at_ctes_of
                         is_arch_update'_def isCap_simps valid_cap'_def
                         capAligned_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: arch_update_updateCap_invs valid_pdpte_lift' hoare_vcg_all_lift hoare_vcg_ex_lift
             | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pdi'_def)
  done

lemma perform_pdpti_invs [wp]:
  "\<lbrace>invs' and valid_pdpti' pdpti\<rbrace> performPDPTInvocation pdpti \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPDPTInvocation_def getSlotCap_def
                 split: pdptinvocation.splits)
  apply (intro conjI allI impI)
   apply (rule hoare_pre)
    apply (wp arch_update_updateCap_invs getCTE_wp
              hoare_vcg_ex_lift  mapM_x_wp'
                | wpc | simp add: o_def
                | (simp only: imp_conv_disj, rule hoare_vcg_disj_lift))+
   apply (clarsimp simp: valid_pdpti'_def cte_wp_at_ctes_of
                         is_arch_update'_def isCap_simps valid_cap'_def
                         capAligned_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: arch_update_updateCap_invs hoare_vcg_all_lift hoare_vcg_ex_lift
             | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pdpti'_def)
  done

crunch unmapPage
  for cte_wp_at': "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas unmapPage_typ_ats [wp] = typ_at_lifts [OF unmapPage_typ_at']

crunch lookupPTSlot
  for inv: P
  (wp: crunch_wps simp: crunch_simps)

lemma unmapPage_invs' [wp]:
  "\<lbrace>invs'\<rbrace> unmapPage sz asid vptr pptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: unmapPage_def)
  apply (rule hoare_pre)
   apply (wp lookupPTSlot_inv
             hoare_vcg_const_imp_lift
         |wpc
         |simp)+
  done

crunch pteCheckIfMapped, pdeCheckIfMapped
  for invs'[wp]: "invs'"
  and valid_pte'[wp]: "valid_pte' pte"
  and valid_pde'[wp]: "valid_pde' pde"

lemma perform_page_invs [wp]:
  notes no_irq[wp]
  shows "\<lbrace>invs' and valid_page_inv' pt\<rbrace> performPageInvocation pt \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: performPageInvocation_def)
  apply (cases pt)
     apply clarsimp
     apply ((wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                       arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
                  simp: valid_page_inv'_def valid_slots'_def is_arch_update'_def
                 split: vmpage_entry.splits
             | (auto simp: is_arch_update'_def)[1])+)[3]
  apply (wp arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
         | wpc
         | clarsimp simp: performPageInvocationUnmap_def)+
   apply (rename_tac acap word a b)
   apply (rule_tac Q'="\<lambda>_. invs' and cte_wp_at' (\<lambda>cte. \<exists>r R mt sz d m. cteCap cte =
                                       ArchObjectCap (PageCap r R mt sz d m)) word"
               in hoare_strengthen_post)
    apply (wp unmapPage_cte_wp_at')
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (case_tac cte)
   apply clarsimp
   apply (frule ctes_of_valid_cap')
    apply (auto simp: valid_page_inv'_def valid_slots'_def cte_wp_at_ctes_of)[1]
   apply (simp add: is_arch_update'_def isCap_simps)
   apply (simp add: valid_cap'_def capAligned_def)
  apply (clarsimp simp: cte_wp_at_ctes_of valid_page_inv'_def)
  apply (simp add: is_arch_update'_def isCap_simps)
  apply (case_tac cte)
  apply clarsimp+
  done

lemma setObject_cte_obj_at_ap':
  shows
  "\<lbrace>\<lambda>s. P' (obj_at' (P :: asidpool \<Rightarrow> bool) p s)\<rbrace>
  setObject c (cte::cte)
  \<lbrace>\<lambda>_ s. P' (obj_at' P p s)\<rbrace>"
  apply (clarsimp simp: setObject_def in_monad split_def
                        valid_def lookupAround2_char1
                        obj_at'_def ps_clear_upd projectKOs
             split del: if_split)
  apply (clarsimp elim!: rsubst[where P=P'])
  apply (clarsimp simp: updateObject_cte in_monad objBits_simps
                        tcbCTableSlot_def tcbVTableSlot_def
                        typeError_def
                 split: if_split_asm
                        Structures_H.kernel_object.split_asm)
  done

lemma updateCap_ko_at_ap_inv'[wp]:
  "\<lbrace>\<lambda>s. P (ko_at' (ko::asidpool) p s )\<rbrace> updateCap a b \<lbrace>\<lambda>rv s. P ( ko_at' ko p s)\<rbrace>"
  by (wpsimp simp: updateCap_def setCTE_def wp: setObject_cte_obj_at_ap')

lemma perform_aci_invs [wp]:
  "\<lbrace>invs' and valid_apinv' api\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performASIDPoolInvocation_def split: asidpool_invocation.splits)
  apply (wp arch_update_updateCap_invs getASID_wp getSlotCap_wp hoare_vcg_all_lift
            hoare_vcg_imp_lift
          | simp add: o_def)+
  apply (clarsimp simp: valid_apinv'_def cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply (clarsimp split: if_splits)
  apply (drule ctes_of_valid_cap', fastforce)
  apply (clarsimp simp: isPML4Cap'_def valid_cap'_def capAligned_def is_arch_update'_def isCap_simps)
  apply (drule ko_at_valid_objs', fastforce, clarsimp simp: projectKOs)
  apply (clarsimp simp: valid_obj'_def ran_def mask_asid_low_bits_ucast_ucast
                 split: if_split_asm)
  apply (case_tac x, clarsimp simp: inv_def)
  apply (clarsimp simp: page_map_l4_at'_def, drule_tac x=0 in spec)
  apply (auto simp: bit_simps asid_bits_defs asid_bits_of_defs ucast_ucast_mask mask_def word_and_le1)
  done

lemma capMaster_isPML4Cap':
  "capMasterCap cap' = capMasterCap cap \<Longrightarrow> isPML4Cap' cap' = isPML4Cap' cap"
  by (simp add: capMasterCap_def arch_capMasterCap_def isPML4Cap'_def
           split: capability.splits arch_capability.splits)

lemma isPML4Cap'_PML4 :
  "isPML4Cap' (ArchObjectCap (PML4Cap r m))"
  by (simp add: isPML4Cap'_def)


end

lemma cteCaps_of_ctes_of_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P (cteCaps_of s) \<rbrace> f \<lbrace>\<lambda>_ s. P (cteCaps_of s)\<rbrace>"
  unfolding cteCaps_of_def .

end
