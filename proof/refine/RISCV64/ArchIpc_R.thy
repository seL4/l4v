(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpc_R
imports Ipc_R
begin

context Arch begin arch_global_naming

named_theorems Ipc_R_assms

declare word64_minus_one_le[simp]

lemma max_ipc_size_le_2_msg_align_bits[Ipc_R_assms]:
  "max_ipc_words * word_size \<le> 2 ^ msg_align_bits"
  by (simp add: max_ipc_words word_size_def msg_align_bits)

lemma maskCapRights_vs_cap_ref'[simp]:
  "vs_cap_ref' (maskCapRights msk cap) = vs_cap_ref' cap"
  unfolding vs_cap_ref'_def
  apply (cases cap, simp_all add: global.maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: RISCV64_H.maskCapRights_def isCap_simps Let_def)
  done

lemma is_derived'_Untyped[Ipc_R_assms]:
  "\<lbrakk>isUntypedCap cap'\<rbrakk>
   \<Longrightarrow> is_derived' m src cap' cap
      = (isUntypedCap cap \<and> badge_derived' cap' cap \<and> descendants_of' src m = {})"
  by (clarsimp simp add: RISCV64.is_derived'_def gen_isCap_simps)
     (cases cap; clarsimp simp: badge_derived'_def capMasterCap_def)

lemma arch_maskCapRights_not_null[Ipc_R_assms, simp]:
  "Arch.maskCapRights r acap \<noteq> NullCap"
  by (case_tac acap; simp add: RISCV64_H.maskCapRights_def isCap_simps)

lemma capASID_gen_cap[Ipc_R_assms]:
  "\<not> isArchObjectCap cap \<Longrightarrow> capASID cap = None"
  by (cases cap; simp add: isCap_simps split: arch_capability.split option.split)

lemma cap_asid_base'_gen_cap[Ipc_R_assms]:
  "\<not> isArchObjectCap cap \<Longrightarrow> cap_asid_base' cap = None"
  by (cases cap; simp add: isCap_simps split: arch_capability.split option.split)

lemma cap_vptr'_gen_cap[Ipc_R_assms]:
  "\<not> isArchObjectCap cap \<Longrightarrow> cap_vptr' cap = None"
  by (cases cap; simp add: isCap_simps split: arch_capability.split option.split)

crunch transferCapsToSlots
  for pspace_in_kernel_mappings'[Ipc_R_assms, wp]: pspace_in_kernel_mappings'

crunch makeArchFaultMessage
  for sch_act[Ipc_R_assms, wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma is_derived'_IRQHandlerCap[Ipc_R_assms]:
  "\<lbrakk>isIRQHandlerCap cap'\<rbrakk> \<Longrightarrow> is_derived' (ctes_of (s::kernel_state)) src cap' cap =
   (isIRQHandlerCap cap \<and> badge_derived' cap' cap)"
  by (clarsimp simp add: RISCV64.is_derived'_def gen_isCap_simps)
     (cases cap; clarsimp simp: badge_derived'_def capMasterCap_def)

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
  by (cases acap; simp add: RISCV64_H.maskCapRights_def isCap_simps)

lemma isFrameCap_maskCapRights[simp]:
  "isArchCap isFrameCap (global.maskCapRights R c) = isArchCap isFrameCap c"
  apply (case_tac c; simp add: gen_isCap_simps isArchCap_def global.maskCapRights_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability; simp add: isCap_simps RISCV64_H.maskCapRights_def)
  done

lemma arch_updateCapData_ordering[Ipc_R_assms]:
  "\<lbrakk> (x, arch_capBadge acap) \<in> capBadge_ordering P; Arch.updateCapData p d acap \<noteq> NullCap \<rbrakk>
   \<Longrightarrow> (x, capBadge (Arch.updateCapData p d acap)) \<in> capBadge_ordering P"
  by (cases acap; simp add: RISCV64_H.updateCapData_def)

lemma ArchUpdateCapData_noIRQControl[Ipc_R_assms]:
  "Arch.updateCapData p d acap \<noteq> IRQControlCap"
  by (cases acap; simp add: RISCV64_H.updateCapData_def)

lemma updateCapData_vs_cap_ref'[simp]:
  "vs_cap_ref' (updateCapData pr D c) = vs_cap_ref' c"
  by (rule ccontr,
      clarsimp simp: isCap_simps global.updateCapData_def Let_def
                     RISCV64_H.updateCapData_def
                     vs_cap_ref'_def
          split del: if_split
              split: if_split_asm arch_capability.splits)

lemma isFrameCap_updateCapData[simp]:
  "isArchCap isFrameCap (updateCapData pr D c) = isArchCap isFrameCap c"
  apply (case_tac c; simp add: global.updateCapData_def isCap_simps isArchCap_def)
   apply (rename_tac arch_capability)
   apply (case_tac arch_capability; simp add: RISCV64_H.updateCapData_def isCap_simps isArchCap_def)
  apply (clarsimp split:capability.splits simp:Let_def)
  done

lemma badgeRegister_badge_register[Ipc_R_assms]:
  "badgeRegister = badge_register"
  by (simp add: badge_register_def badgeRegister_def)

crunch copyMRs
  for pspace_in_kernel_mappings'[Ipc_R_assms, wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps simp: crunch_simps)

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

(* Used in CRefine *)
lemma lookupIPCBuffer_Some_0:
  "\<lbrace>\<top>\<rbrace> lookupIPCBuffer w t \<lbrace>\<lambda>rv s. rv \<noteq> Some 0\<rbrace>"
  by (wpsimp simp: lookupIPCBuffer_def Let_def getThreadBufferSlot_def locateSlot_conv)

lemma arch_getSanitiseRegisterInfo_corres[Ipc_R_assms]:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (arch_get_sanitise_register_info t)
          (getSanitiseRegisterInfo t)"
  unfolding arch_get_sanitise_register_info_def getSanitiseRegisterInfo_def
  by corres

crunch getSanitiseRegisterInfo
  for tcb_at'[wp]: "tcb_at' t"

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

crunch debugPrint
  for inv[Ipc_R_assms, wp]: P
  and (no_fail) no_fail[Ipc_R_assms, intro!, wp, simp]

lemmas [Ipc_R_assms] =
  lookupIPCBuffer_valid_ipc_buffer

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

end (* Arch *)

end
