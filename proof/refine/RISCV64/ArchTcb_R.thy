(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTcb_R
imports Tcb_R
begin

context Arch begin arch_global_naming

named_theorems Tcb_R_assms

lemma activateIdleThread_corres[Tcb_R_assms]:
 "corres dc (st_tcb_at idle t) (st_tcb_at' idle' t)
    (arch_activate_idle_thread t) (activateIdleThread t)"
  by (simp add: arch_activate_idle_thread_def activateIdleThread_def)

crunch arch_post_modify_registers
  for pspace_aligned[Tcb_R_assms, wp]: pspace_aligned
  and pspace_distinct[Tcb_R_assms, wp]: pspace_distinct
  (wp: crunch_wps simp: crunch_simps)

lemma asUser_postModifyRegisters_corres[Tcb_R_assms]:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) (tcb_at' t and tcb_at' ct)
     (arch_post_modify_registers ct t)
     (asUser t $ postModifyRegisters ct t)"
  apply (rule corres_guard_imp)
    apply (clarsimp simp: arch_post_modify_registers_def postModifyRegisters_def when_def)
    apply safe
    apply (subst submonad_asUser.return)
    apply (corres corres: corres_stateAssert_assume)
    apply simp+
  done

(* formulation of threadSet_state_hyp_refs_of' varies based on whether VCPU is present;
   use this as interface, but keep original lemma name for use outside of Arch *)
lemma threadSet_state_hyp_refs_of'_interface[Tcb_R_assms]:
  "\<lbrakk> \<And>tcb. tcb_hyp_refs' (tcbArch (F tcb)) = tcb_hyp_refs' (tcbArch tcb) \<rbrakk>
   \<Longrightarrow> threadSet F t \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace> "
  by (wpsimp simp: threadSet_state_hyp_refs_of')

lemma sameObject_corres2[Tcb_R_assms]:
  "\<lbrakk> cap_relation c c'; cap_relation d d' \<rbrakk>
   \<Longrightarrow> same_object_as c d = sameObjectAs c' d'"
  apply (frule(1) same_region_as_relation[symmetric, where c=c and c'=d])
  apply (case_tac c; simp add: global.sameObjectAs_def same_object_as_def
                               isCap_simps is_cap_simps bits_of_def)
  apply (case_tac d; case_tac c'; simp)
  apply (case_tac d'; simp)
  apply (clarsimp simp add: RISCV64_H.sameObjectAs_def Let_def)
  apply (intro conjI impI)
   subgoal by (fastforce simp: add_mask_fold sameRegionAs_def isCap_simps
                         split: arch_cap.splits)
  by (fastforce simp: global.sameRegionAs_def isCap_simps split: arch_cap.splits)

lemma untyped_derived_eq_from_sameObjectAs[Tcb_R_assms]:
  "sameObjectAs cap cap2 \<Longrightarrow> untyped_derived_eq cap cap2"
  by (clarsimp simp: untyped_derived_eq_def sameObjectAs_def2 gen_isCap_Master)

lemma isValidVTableRootD:
  "isValidVTableRoot cap
   \<Longrightarrow> isArchObjectCap cap \<and> isPageTableCap (capCap cap)
      \<and> capPTMappedAddress (capCap cap) \<noteq> None"
  by (simp add: isValidVTableRoot_def isCap_simps
         split: capability.split_asm arch_capability.split_asm
                option.split_asm)

crunch prepare_thread_delete, arch_finalise_cap
  for pspace_aligned[Tcb_R_assms, wp]: "pspace_aligned :: det_ext state \<Rightarrow> _"
  and pspace_distinct[Tcb_R_assms, wp]: "pspace_distinct :: det_ext state \<Rightarrow> _"
  (simp: crunch_simps preemption_point_def wp: crunch_wps OR_choiceE_weak_wp)

lemma is_valid_vtable_root_simp:
  "is_valid_vtable_root cap =
   (\<exists>r asid. cap = cap.ArchObjectCap (arch_cap.PageTableCap r (Some asid)))"
  by (simp add: is_valid_vtable_root_def
           split: cap.splits arch_cap.splits option.splits)

(* FIXME: move after checked_insert_tcb_invs in ArchTcb_AI, and consolidate redundancy there *)
lemma checked_insert_tcb_invs_gen[Tcb_R_assms]:
  "\<lbrace>invs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
    and K (is_cnode_or_valid_arch new_cap) and valid_cap new_cap
    and tcb_cap_valid new_cap (target, ref)
    and cte_wp_at \<top> src_slot
    and no_cap_to_obj_dr_emp new_cap\<rbrace>
   check_cap_at new_cap src_slot
    (check_cap_at (Structures_A.ThreadCap target) slot
     (cap_insert new_cap src_slot (target, ref)))
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp wp: checked_insert_tcb_invs)
  apply (strengthen use_no_cap_to_obj_asid_strg)
  apply (clarsimp dest!: is_cnode_or_valid_arch_cap_asid)
  done

lemma is_valid_vtable_root_is_cnode_or_valid_arch[Tcb_R_assms]:
  "is_valid_vtable_root cap \<Longrightarrow> is_cnode_or_valid_arch cap"
  by (clarsimp simp: is_cnode_or_valid_arch_def is_valid_vtable_root_simp is_cap_simps)

lemma is_cnode_cap_is_cnode_or_valid_arch[Tcb_R_assms]:
  "is_cnode_cap cap \<Longrightarrow> is_cnode_or_valid_arch cap"
  by (clarsimp simp: is_cnode_or_valid_arch_def)

lemma valid_ipc_buffer_cap_is_nondevice_page_cap[Tcb_R_assms]:
  "\<lbrakk>valid_ipc_buffer_cap cap buf; is_arch_cap cap\<rbrakk> \<Longrightarrow> is_nondevice_page_cap cap"
  by (clarsimp simp: is_cap_simps valid_ipc_buffer_cap_def)

lemma cte_at_tcb_at_2p_cteSizeBits[Tcb_R_assms]:
  "tcb_at' t s \<Longrightarrow> cte_at' (t + 2 ^ cteSizeBits) s"
  by (simp add: cte_at'_obj_at' tcb_cte_cases_def cteSizeBits_def)

(* arch_capBadge may involve SMC caps on some architectures, but not page tables *)
lemma isValidVTableRootD_arch[Tcb_R_assms]:
  "isValidVTableRoot cap \<Longrightarrow> isArchObjectCap cap \<and> arch_capBadge (capCap cap) = None"
  by (drule isValidVTableRootD; clarsimp simp: arch_capBadge_def isCap_simps)

(* FIXME FPU: when the FPU being enabled is properly configurable for the proofs then this shouldn't
              need to unfold config_HAVE_FPU. *)
lemma postSetFlags_corres[Tcb_R_assms, corres]:
  "flags = word_to_tcb_flags flags' \<Longrightarrow>
   corres dc (cur_tcb and pspace_aligned and pspace_distinct and valid_cur_fpu) \<top>
     (arch_post_set_flags  t flags) (postSetFlags t flags')"
  unfolding arch_post_set_flags_def postSetFlags_def
  by (corres simp: Kernel_Config.config_HAVE_FPU_def cur_tcb_def)

lemma postSetFlags_invs'[Tcb_R_assms, wp]:
  "postSetFlags t flags \<lbrace>invs'\<rbrace>"
  unfolding postSetFlags_def
  by wpsimp

lemma copyregsets_map_only[simp]:
  "copyregsets_map v = RISCVNoExtraRegisters"
  by (cases "copyregsets_map v", simp)

(* there are no extra registers on any architecture so far, and while it is theoretically possible
   in the design spec, the abstract invariant proof assumes this *)
lemma decodeTransfer_def'[Tcb_R_assms]:
  "decodeTransfer w = returnOk (copyregsets_map ArchDefaultExtraRegisters)"
  by (simp add: decodeTransfer_def)

lemma checkValidIPCBuffer_corres[Tcb_R_assms]:
  "cap_relation cap cap' \<Longrightarrow>
   corres (ser \<oplus> dc) \<top> \<top>
     (check_valid_ipc_buffer vptr cap)
     (checkValidIPCBuffer vptr cap')"
  apply (simp add: check_valid_ipc_buffer_def
                   checkValidIPCBuffer_def
                   unlessE_def Let_def
            split: cap_relation_split_asm arch_cap.split_asm bool.splits)
  apply (simp add: capTransferDataSize_def msgMaxLength_def
                   msg_max_length_def msgMaxExtraCaps_def
                   cap_transfer_data_size_def word_size ipcBufferSizeBits_def
                   msgLengthBits_def msgExtraCapBits_def msg_align_bits msgAlignBits_def
                   msg_max_extra_caps_def is_aligned_mask whenE_def split:vmpage_size.splits)
  apply (auto simp add: returnOk_def)
  done

lemma checkValidIPCBuffer_ArchObject_wp[Tcb_R_assms]:
  "\<lbrace>\<lambda>s. isArchObjectCap cap \<and> capBadge cap = None \<and> is_aligned p msg_align_bits \<longrightarrow> P s\<rbrace>
   checkValidIPCBuffer p cap
   \<lbrace>\<lambda>rv s. P s\<rbrace>,-"
  apply (simp add: checkValidIPCBuffer_def
                   whenE_def unlessE_def
             cong: capability.case_cong
                   arch_capability.case_cong
            split del: if_split)
  apply (wpsimp wp: whenE_throwError_wp msgAlignBits_def
         | clarsimp simp: ipcBufferSizeBits_def isCap_simps is_aligned_mask msg_align_bits)+
  done

crunch checkValidIPCBuffer
  for inv[Tcb_R_assms, wp]: "P"
  (simp: crunch_simps)

lemma isValidVTableRoot_eq[Tcb_R_assms]:
  "cap_relation cap cap' \<Longrightarrow> isValidVTableRoot cap' = is_valid_vtable_root cap"
  apply (cases cap; simp add: isValidVTableRoot_def is_valid_vtable_root_simp)
  apply (rename_tac acap, case_tac acap; simp)
  apply (auto split: option.split simp: mdata_map_def)
  done

end (* Arch *)

interpretation Tcb_R?: Tcb_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Tcb_R_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Tcb_R_2_assms

lemma checkCapAt_cteInsert_corres':
  "cap_relation new_cap newCap \<Longrightarrow>
   corres dc (einvs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
               and cte_at slot and K (is_cnode_or_valid_arch new_cap)
               and cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                                \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and>
                                    vspace_asid c = vspace_asid new_cap) src_slot)
             (invs' and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) (cte_map (target, ref))
               and valid_cap' newCap)
     (check_cap_at new_cap src_slot
      (check_cap_at (cap.ThreadCap target) slot
       (cap_insert new_cap src_slot (target, ref))))
     (checkCapAt newCap (cte_map src_slot)
      (checkCapAt (ThreadCap target) (cte_map slot)
       (assertDerived (cte_map src_slot) newCap (cteInsert newCap (cte_map src_slot) (cte_map (target, ref))))))"
  (is "_ \<Longrightarrow> corres dc ?P ?P' _ _")
  apply (rule corres_guard_imp)
  apply (rule_tac P="?P" and P'="?P'" in checkCapAt_corres, assumption)
      apply (rule checkCapAt_weak_corres, simp)
      apply (unfold assertDerived_def)[1]
      apply (rule corres_stateAssert_implied [where P'=\<top>])
       apply simp
       apply (erule cteInsert_corres [OF _ refl refl])
      apply clarsimp
      apply (drule cte_wp_at_norm [where p=src_slot])
      apply (case_tac src_slot)
      apply (clarsimp simp: state_relation_def)
      apply (drule (1) pspace_relation_cte_wp_at)
        apply fastforce
       apply fastforce
      apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (erule (2) is_derived_eq [THEN iffD1])
       apply (erule cte_wp_at_weakenE, rule TrueI)
      apply assumption
     apply clarsimp
     apply (rule conjI, fastforce)+
     apply (cases src_slot)
     apply (clarsimp simp: cte_wp_at_caps_of_state invs_arch_state)
     apply (rule conjI)
      apply (frule same_object_as_cap_master)
      apply (clarsimp simp: cap_master_cap_simps is_cnode_or_valid_arch_def
                            is_cap_simps is_valid_vtable_root_def
                     dest!: cap_master_cap_eqDs)
     apply (erule(1) checked_insert_is_derived)
      apply simp
     apply simp
    apply fastforce
   apply (fastforce dest: is_cnode_or_valid_arch_cap_asid simp: cte_wp_at_caps_of_state)
  apply clarsimp
  apply fastforce
  done

lemma checkCapAt_cteInsert_corres[Tcb_R_2_assms]:
  "cap_relation new_cap newCap \<Longrightarrow>
   corres dc (einvs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
               and cte_at slot and K (is_cnode_or_valid_arch new_cap)
               and cte_wp_at \<top> src_slot
               and no_cap_to_obj_dr_emp new_cap
               and (\<lambda>s. s \<turnstile> new_cap))
             (invs' and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) (cte_map (target, ref))
               and valid_cap' newCap)
     (check_cap_at new_cap src_slot
      (check_cap_at (cap.ThreadCap target) slot
       (cap_insert new_cap src_slot (target, ref))))
     (checkCapAt newCap (cte_map src_slot)
      (checkCapAt (ThreadCap target) (cte_map slot)
       (assertDerived (cte_map src_slot) newCap (cteInsert newCap (cte_map src_slot) (cte_map (target, ref))))))"
  apply (corres corres: checkCapAt_cteInsert_corres')
   apply (strengthen use_no_cap_to_obj_asid_strg)
   apply (fastforce dest: is_cnode_or_valid_arch_cap_asid)
  apply fastforce
  done

end (* Arch *)

interpretation Tcb_R_2?: Tcb_R_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Tcb_R_2_assms)?)?)
qed

end
