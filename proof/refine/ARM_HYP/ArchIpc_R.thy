(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpc_R
imports Ipc_R
begin

context Arch begin arch_global_naming

named_theorems Ipc_R_assms

declare word32_minus_one_le[simp]

lemma max_ipc_size_le_2_msg_align_bits[Ipc_R_assms]:
  "max_ipc_words * word_size \<le> 2 ^ msg_align_bits"
  by (simp add: max_ipc_words word_size_def msg_align_bits)

lemma maskCapRights_vsCapRef[simp]:
  "vsCapRef (maskCapRights msk cap) = vsCapRef cap"
  unfolding vsCapRef_def
  apply (cases cap, simp_all add: global.maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: ARM_HYP_H.maskCapRights_def isCap_simps Let_def)
  done

lemma vsCapRef_generic:
  "\<not> isArchObjectCap cap \<Longrightarrow> vsCapRef cap = None"
  by (clarsimp simp add: vsCapRef_def gen_isCap_simps split: capability.splits)

lemma is_derived'_Untyped[Ipc_R_assms]:
  "\<lbrakk>isUntypedCap cap'\<rbrakk>
   \<Longrightarrow> is_derived' m src cap' cap
      = (isUntypedCap cap \<and> badge_derived' cap' cap \<and> descendants_of' src m = {})"
  by (clarsimp simp add: ARM_HYP.is_derived'_def gen_isCap_simps)
     (cases cap; clarsimp simp: badge_derived'_def capMasterCap_def vsCapRef_generic isCap_simps)

lemma is_derived'_Reply[Ipc_R_assms]:
  "\<lbrakk>isReplyCap cap'\<rbrakk>
   \<Longrightarrow> is_derived' m src cap' cap
      = (isReplyCap cap \<and> capTCBPtr cap = capTCBPtr cap' \<and> capReplyMaster cap \<and> \<not> capReplyMaster cap')"
  by (clarsimp simp add: ARM_HYP.is_derived'_def gen_isCap_simps)
     (cases cap; clarsimp simp: badge_derived'_def capMasterCap_def vsCapRef_generic isCap_simps)

lemma arch_maskCapRights_not_null[Ipc_R_assms, simp]:
  "Arch.maskCapRights r acap \<noteq> NullCap"
  by (case_tac acap; simp add: ARM_HYP_H.maskCapRights_def isCap_simps)

lemma capASID_gen_cap[Ipc_R_assms]:
  "\<not> isArchObjectCap cap \<Longrightarrow> capASID cap = None"
  by (cases cap; simp add: isCap_simps split: arch_capability.split option.split)

lemma cap_asid_base'_gen_cap[Ipc_R_assms]:
  "\<not> isArchObjectCap cap \<Longrightarrow> cap_asid_base' cap = None"
  by (cases cap; simp add: isCap_simps split: arch_capability.split option.split)

lemma cap_vptr'_gen_cap[Ipc_R_assms]:
  "\<not> isArchObjectCap cap \<Longrightarrow> cap_vptr' cap = None"
  by (cases cap; simp add: isCap_simps split: arch_capability.split option.split)

lemmas transferCapsToSlots_pspace_in_kernel_mappings'[Ipc_R_assms, wp] =
  pspace_in_kernel_mappings'_inv[where f="transferCapsToSlots _ _ _ _ _ _"]

crunch makeArchFaultMessage
  for sch_act[Ipc_R_assms, wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma is_derived'_IRQHandlerCap[Ipc_R_assms]:
  "\<lbrakk>isIRQHandlerCap cap'\<rbrakk> \<Longrightarrow> is_derived' (ctes_of (s::kernel_state)) src cap' cap =
   (isIRQHandlerCap cap \<and> badge_derived' cap' cap)"
  by (clarsimp simp add: ARM_HYP.is_derived'_def gen_isCap_simps)
     (cases cap; clarsimp simp: badge_derived'_def capMasterCap_def vsCapRef_generic isCap_simps)

(* variant of storeWord_um_inv which does not expose architecture-specific information *)
lemma storeWord_um_inv'[Ipc_R_assms]:
  "\<lbrace>\<lambda>s. underlying_memory s = um\<rbrace>
   storeWord a v
   \<lbrace>\<lambda>_ s. is_aligned a word_size_bits
          \<and> x \<in> set [a .e. (a+word_size-1)] \<or> underlying_memory s x = um x\<rbrace>"
  apply (rule hoare_post_imp[OF _ storeWord_um_inv[where x=x]])
  apply (clarsimp simp add: word_size_bits_def word_size_def)
  apply (frule is_aligned_no_overflow_mask)
  apply (subst add.commute) (* want "\<le> a + _" *)
  apply (erule disjE, clarsimp simp: mask_def)
  apply (simp (no_asm) add: word_le_nat_alt)
  apply (auto simp add: unat_plus_simple[THEN iffD1] word_plus_mono_right2 mask_def)
  done

lemma isArchObjectCap_maskCapRights[Ipc_R_assms]:
  "isArchObjectCap (Arch.maskCapRights R acap)"
  by (cases acap; simp add: ARM_HYP_H.maskCapRights_def isCap_simps)

lemma isPageCap_maskCapRights[simp]:
  "isArchCap isPageCap (global.maskCapRights R c) = isArchCap isPageCap c"
  apply (case_tac c; simp add: gen_isCap_simps isArchCap_def global.maskCapRights_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability; simp add: isCap_simps ARM_HYP_H.maskCapRights_def)
  done

lemma arch_updateCapData_ordering[Ipc_R_assms]:
  "\<lbrakk> (x, arch_capBadge acap) \<in> capBadge_ordering P; Arch.updateCapData p d acap \<noteq> NullCap \<rbrakk>
   \<Longrightarrow> (x, capBadge (Arch.updateCapData p d acap)) \<in> capBadge_ordering P"
  by (cases acap; simp add: ARM_HYP_H.updateCapData_def)

lemma ArchUpdateCapData_noReply[Ipc_R_assms]:
  "Arch.updateCapData p d acap \<noteq> capability.ReplyCap x y z"
  by (cases acap; simp add: ARM_HYP_H.updateCapData_def)

lemma ArchUpdateCapData_noIRQControl[Ipc_R_assms]:
  "Arch.updateCapData p d acap \<noteq> IRQControlCap"
  by (cases acap; simp add: ARM_HYP_H.updateCapData_def)

lemma updateCapData_vsCapRef[simp]:
  "vsCapRef (updateCapData pr D c) = vsCapRef c"
  by (rule ccontr,
      clarsimp simp: isCap_simps global.updateCapData_def Let_def
                     ARM_HYP_H.updateCapData_def
                     vsCapRef_def
          split del: if_split
              split: if_split_asm arch_capability.splits)

lemma isPageCap_updateCapData[simp]:
  "isArchCap isPageCap (updateCapData pr D c) = isArchCap isPageCap c"
  apply (case_tac c; simp add: global.updateCapData_def isCap_simps isArchCap_def)
   apply (rename_tac arch_capability)
   apply (case_tac arch_capability; simp add: ARM_HYP_H.updateCapData_def isCap_simps isArchCap_def)
  apply (clarsimp split:capability.splits simp:Let_def)
  done

lemma badgeRegister_badge_register[Ipc_R_assms]:
  "badgeRegister = badge_register"
  by (simp add: badge_register_def badgeRegister_def)

lemmas copyMRs__pspace_in_kernel_mappings'[Ipc_R_assms, wp] =
  pspace_in_kernel_mappings'_inv[where f="copyMRs _ _ _ _ _"]

lemma makeArchFaultMessage_corres[Ipc_R_assms]:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (make_arch_fault_msg f t)
          (makeArchFaultMessage (arch_fault_map f) t)"
  apply (cases f; clarsimp simp: makeArchFaultMessage_def ucast_nat_def split: arch_fault.split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF asUser_getRestartPC_corres])
      apply (rule corres_trivial, simp)
     apply (wp+, auto)
  done

lemma syscallMessage_def'[Ipc_R_assms]:
  "FaultHandler_H.syscallMessage \<equiv> MachineExports.syscallMessage"
  by (simp add: syscallMessage_def)

lemma exceptionMessage_def'[Ipc_R_assms]:
  "FaultHandler_H.exceptionMessage \<equiv> MachineExports.exceptionMessage"
  by (simp add: exceptionMessage_def)

lemma makeArchFaultMessage_inv[Ipc_R_assms, wp]:
  "makeArchFaultMessage ft t \<lbrace>P\<rbrace>"
  unfolding makeArchFaultMessage_def
  by (wpsimp wp: asUser_inv getRestartPC_inv split: arch_fault.split)

lemma lookupIPCBuffer_valid_ipc_buffer[Ipc_R_assms, wp]:
  "\<lbrace>valid_objs'\<rbrace> VSpace_H.lookupIPCBuffer b s \<lbrace>case_option \<top> valid_ipc_buffer_ptr'\<rbrace>"
  unfolding lookupIPCBuffer_def
  supply tcb_cte_cases_simps(1)[simp del] (* avoid duplicate simp rule warning *)
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  apply (simp add: Let_def getSlotCap_def getThreadBufferSlot_def
                   locateSlot_conv threadGet_def comp_def)
  apply (wp getCTE_wp getObject_tcb_wp | wpc)+
  apply (clarsimp simp del: imp_disjL)
  apply (drule obj_at_ko_at')
  apply (clarsimp simp del: imp_disjL)
  apply (rule_tac x = ko in exI)
  apply (frule ko_at_cte_ipcbuffer[simplified cteSizeBits_def])
  apply (clarsimp simp: cte_wp_at_ctes_of shiftl_t2n' simp del: imp_disjL)
  apply (rename_tac ref rg sz d m)
  apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
  apply (frule (1) ko_at_valid_objs')
   apply (clarsimp simp: projectKO_opts_defs split: kernel_object.split_asm)
  apply (clarsimp simp add: valid_obj'_def valid_tcb'_def
                            isCap_simps cte_level_bits_def field_simps)
  apply (drule bspec [OF _ ranI [where a = "4 << cteSizeBits"]])
   apply (simp add: cteSizeBits_def)
  apply (clarsimp simp add: valid_cap'_def)
  apply (rule conjI)
   apply (rule aligned_add_aligned)
     apply (clarsimp simp add: capAligned_def)
     apply assumption
    apply (erule is_aligned_andI1)
   apply (rule order_trans[rotated])
    apply (rule pbfs_atleast_pageBits)
   apply (simp add: msg_align_bits pageBits_def)
  apply (clarsimp simp: capAligned_def)
  apply (drule_tac x = "(tcbIPCBuffer ko && mask (pageBitsForSize d))  >> pageBits" in spec)
  apply (subst(asm) mult.commute mult.left_commute, subst(asm) shiftl_t2n[symmetric])
  apply (simp add: shiftr_shiftl1 )
  apply (subst (asm) mask_out_add_aligned)
   apply (erule is_aligned_weaken [OF _ pbfs_atleast_pageBits])
  apply (erule mp)
  apply (rule shiftr_less_t2n)
  apply (clarsimp simp: pbfs_atleast_pageBits)
  apply (rule and_mask_less')
  apply (simp add: word_bits_conv pbfs_less_wb'[unfolded word_bits_conv])
  done

(* Used in CRefine *)
lemma lookupIPCBuffer_Some_0:
  "\<lbrace>\<top>\<rbrace> lookupIPCBuffer w t \<lbrace>\<lambda>rv s. rv \<noteq> Some 0\<rbrace>"
  by (wpsimp simp: lookupIPCBuffer_def Let_def getThreadBufferSlot_def locateSlot_conv)

lemma arch_getSanitiseRegisterInfo_corres[Ipc_R_assms]:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (arch_get_sanitise_register_info t)
          (getSanitiseRegisterInfo t)"
  unfolding arch_get_sanitise_register_info_def getSanitiseRegisterInfo_def
  by (fold archThreadGet_def, corres)

crunch getSanitiseRegisterInfo
  for tcb_at'[wp]: "tcb_at' t"

crunch arch_get_sanitise_register_info
  for pspace_distinct[Ipc_R_assms, wp]: pspace_distinct
  and pspace_aligned[Ipc_R_assms, wp]: pspace_aligned

lemma sanitiseRegister_sanitise_register[Ipc_R_assms]:
  "sanitiseRegister = sanitise_register"
  by (rule ext)+
     (clarsimp simp add: sanitiseRegister_def sanitise_register_def cong: register.case_cong)

lemma handleArchFaultReply_corres[Ipc_R_assms]:
  "corres (=) \<top> \<top>
          (handle_arch_fault_reply ft t label msg) (handleArchFaultReply (arch_fault_map ft) t label msg)"
  by (clarsimp simp: handle_arch_fault_reply_def handleArchFaultReply_def
               split: arch_fault.split)

crunch getSanitiseRegisterInfo, handleArchFaultReply, handle_arch_fault_reply
  for inv[Ipc_R_assms, wp]: P

lemma ctes_of_mdbNext_parentOf[Ipc_R_assms]:
  "\<lbrakk> ctes_of s' \<turnstile> cte_map cptr \<rightarrow> cte_map slot;
     ctes_of s' (cte_map cptr) = Some (CTE (capability.ReplyCap t master rights) n);
     ctes_of s' (mdbNext (cteMDBNode cte)) = Some (CTE (capability.ReplyCap t master' rights') n');
     ctes_of s' \<turnstile> cte_map slot \<leadsto> mdbNext (cteMDBNode cte)\<rbrakk>
   \<Longrightarrow> ctes_of s' \<turnstile> cte_map cptr parentOf mdbNext (cteMDBNode cte)"
  by (clarsimp simp add: parentOf_def isMDBParentOf_CTE sameRegionAs_def2 isCap_simps)
     (erule subtree.cases; clarsimp simp: parentOf_def isMDBParentOf_CTE)

crunch debugPrint
  for inv[Ipc_R_assms, wp]: P
  and (no_fail) no_fail[Ipc_R_assms, intro!, wp, simp]

crunch setThreadState, asUser
  for valid_pde_mappings'[wp]: valid_pde_mappings'
  (simp: crunch_simps wp: hoare_drop_imps)

end (* Arch *)

interpretation Ipc_R?: Ipc_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Ipc_R_assms)?)?)
qed

context Arch begin arch_global_naming

lemma is_derived_mask'[simp]:
  "is_derived' m p (maskCapRights R c) = is_derived' m p c"
  by (rule ext, simp add: is_derived'_def badge_derived'_def)

lemma dmo_addressTranslateS1_valid_machine_state'[wp]:
  "doMachineOp (addressTranslateS1 pc) \<lbrace>valid_machine_state'\<rbrace>"
  by (wpsimp simp: valid_machine_state'_def
                      pointerInUserData_def
                      pointerInDeviceData_def
                wp: dmo_lift' hoare_vcg_all_lift
                    addressTranslateS1_underlying_memory
                    hoare_vcg_disj_lift)

sublocale setExtraBadge: typ_at_props' "setExtraBadge buffer badge n"
  by typ_at_props'
sublocale transferCaps: typ_at_props' "transferCaps info caps endpoint receiver receiveBuffer"
  by typ_at_props'
sublocale copyMRs: typ_at_props' "copyMRs s sb r rb n"
  by typ_at_props'
sublocale doNormalTransfer: typ_at_props' "doNormalTransfer s sb e b g r rb"
  by typ_at_props'
sublocale doIPCTransfer: typ_at_props' "doIPCTransfer s e b g r"
  by typ_at_props'
sublocale handleFaultReply: typ_at_props' "handleFaultReply x t l m"
  by typ_at_props'
sublocale sendFaultIPC: typ_at_props' "sendFaultIPC tptr fault"
  by typ_at_props'
sublocale receiveIPC: typ_at_props' "receiveIPC t cap b"
  by typ_at_props'
sublocale receiveSignal: typ_at_props' "receiveSignal t cap b"
  by typ_at_props'

end (* Arch *)

end
