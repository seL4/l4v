(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CLevityCatch
imports
  "CBaseRefine.Include_C"
  ArchMove_C
  "CLib.LemmaBucket_C"
  "Lib.LemmaBucket"
begin

context begin interpretation Arch . (*FIXME: arch_split*)

(* Short-hand for  unfolding cumbersome machine constants *)

(* works much better *)
lemmas typ_heap_simps' = typ_heap_simps c_guard_clift

(* Rule previously in the simpset, now not. *)
declare ptr_add_def' [simp]

(* Levity: moved from Ipc_C (20090419 09:44:31) *) (* and remove from Syscall_C *)
lemma empty_fail_doMachineOp[intro!]:
  "empty_fail m \<Longrightarrow> empty_fail (doMachineOp m)"
  by (rule ef_dmo')

(* Levity: moved from Ipc_C (20090419 09:44:31) *) (* why isn't this in Kernel_C? *)
lemmas C_register_defs =
  Kernel_C.RAX_def Kernel_C.RBX_def Kernel_C.RCX_def Kernel_C.RDX_def
  Kernel_C.RSI_def Kernel_C.RDI_def Kernel_C.RBP_def
  Kernel_C.R8_def Kernel_C.R9_def Kernel_C.R10_def Kernel_C.R11_def
  Kernel_C.R12_def Kernel_C.R13_def Kernel_C.R14_def Kernel_C.R15_def
  Kernel_C.RSP_def Kernel_C.FLAGS_def Kernel_C.NextIP_def
  Kernel_C.FaultIP_def Kernel_C.Error_def Kernel_C.CS_def
  Kernel_C.SS_def Kernel_C.FS_BASE_def Kernel_C.GS_BASE_def

(* Levity: moved from Retype_C (20090419 09:44:41) *)
lemma no_overlap_new_cap_addrs_disjoint:
  "\<lbrakk> range_cover ptr sz (objBitsKO ko) n;
     pspace_aligned' s;
     pspace_no_overlap' ptr sz s \<rbrakk> \<Longrightarrow>
   set (new_cap_addrs n ptr ko) \<inter> dom (ksPSpace s) = {}"
  apply (erule disjoint_subset [OF new_cap_addrs_subset, where sz1=sz])
  apply (clarsimp simp: Word_Lib.ptr_add_def field_simps)
  apply (rule pspace_no_overlap_disjoint')
  apply auto
  done

declare empty_fail_doMachineOp [simp]

lemma empty_fail_loadWordUser[intro!, simp]:
  "empty_fail (loadWordUser x)"
  by (simp add: loadWordUser_def ef_loadWord)

lemma empty_fail_getMRs[iff]:
  "empty_fail (getMRs t buf mi)"
  by (auto simp add: getMRs_def split: option.split)

lemma empty_fail_getExtraCPtrs [intro!, simp]:
  "empty_fail (getExtraCPtrs sendBuffer info)"
  apply (simp add: getExtraCPtrs_def)
  apply (cases info, simp)
  apply (cases sendBuffer, simp_all)
  done

lemma empty_fail_loadCapTransfer [intro!, simp]:
  "empty_fail (loadCapTransfer a)"
  by (simp add: loadCapTransfer_def capTransferFromWords_def)

lemma empty_fail_emptyOnFailure [intro!, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (emptyOnFailure m)"
  by (auto simp: emptyOnFailure_def catch_def split: sum.splits)

lemma empty_fail_unifyFailure [intro!, simp]:
  "empty_fail m \<Longrightarrow> empty_fail (unifyFailure m)"
  by (auto simp: unifyFailure_def catch_def rethrowFailure_def
                 handleE'_def throwError_def
           split: sum.splits)


lemma empty_fail_getReceiveSlots:
  "empty_fail (getReceiveSlots r rbuf)"
proof -
  note
    empty_fail_assertE[iff]
    empty_fail_resolveAddressBits[iff]
  show ?thesis
  apply (clarsimp simp: getReceiveSlots_def loadCapTransfer_def split_def
                 split: option.split)
  apply (rule empty_fail_bind)
   apply (simp add: capTransferFromWords_def)
  apply (simp add: emptyOnFailure_def unifyFailure_def)
  apply (intro empty_fail_catch empty_fail_bindE empty_fail_rethrowFailure,
         simp_all add: empty_fail_whenEs)
   apply (simp_all add: lookupCap_def split_def lookupCapAndSlot_def
                        lookupSlotForThread_def liftME_def
                        getThreadCSpaceRoot_def locateSlot_conv bindE_assoc
                        lookupSlotForCNodeOp_def lookupErrorOnFailure_def
                  cong: if_cong)
   apply (intro empty_fail_bindE,
          simp_all add: getSlotCap_def)
  apply (intro empty_fail_If empty_fail_bindE empty_fail_rethrowFailure impI,
         simp_all add: empty_fail_whenEs rangeCheck_def)
  done
qed

lemma exec_Basic_Guard_UNIV:
  "Semantic.exec \<Gamma> (Basic f;; Guard F UNIV (Basic g)) x y =
   Semantic.exec \<Gamma> (Basic (g o f)) x y"
  apply (rule iffI)
   apply (elim exec_elim_cases, simp_all, clarsimp)[1]
   apply (simp add: o_def, rule exec.Basic)
  apply (elim exec_elim_cases)
  apply simp_all
  apply (rule exec_Seq' exec.Basic exec.Guard | simp)+
  done

end

definition
  "option_to_ptr \<equiv> Ptr o option_to_0"

lemma option_to_ptr_simps [simp]:
  "option_to_ptr None = NULL"
  "option_to_ptr (Some x) = Ptr x"
  by (auto simp: option_to_ptr_def split: option.split)

(* FIXME MOVE *)
lemma option_to_ptr_NULL_eq:
  "\<lbrakk> option_to_ptr p = p' \<rbrakk> \<Longrightarrow> (p' = NULL) = (p = None \<or> p = Some 0)"
  unfolding option_to_ptr_def option_to_0_def
  by (clarsimp split: option.splits)

lemma option_to_ptr_not_0:
  "\<lbrakk> p \<noteq> 0 ; option_to_ptr v = Ptr p \<rbrakk> \<Longrightarrow> v = Some p"
  by (clarsimp simp: option_to_ptr_def option_to_0_def split: option.splits)

end
