(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CLevityCatch
imports
  "CBaseRefine.Include_C"
  ArchMove_C
  "CParser.LemmaBucket_C"
  "Lib.LemmaBucket"
  Boolean_C
begin

context begin interpretation Arch . (*FIXME: arch_split*)

(* Rule previously in the simpset, now not. *)
declare ptr_add_def' [simp]

(* works much better *)
lemmas typ_heap_simps' = typ_heap_simps c_guard_clift

lemmas asUser_return = submonad.return [OF submonad_asUser]

lemmas asUser_bind_distrib =
  submonad_bind [OF submonad_asUser submonad_asUser submonad_asUser]

lemma ntfnQueue_head_mask_4 :
  "ntfnQueue_head_CL (notification_lift ko') && ~~ mask 4 = ntfnQueue_head_CL (notification_lift ko')"
  unfolding notification_lift_def
  by (clarsimp simp: mask_def word_bw_assocs)

(* Levity: moved from Ipc_C (20090419 09:44:31) *) (* and remove from Syscall_C *)
lemma empty_fail_doMachineOp[intro!]:
  "empty_fail m \<Longrightarrow> empty_fail (doMachineOp m)"
  by (rule ef_dmo')

(* Levity: moved from Ipc_C (20090419 09:44:31) *) (* why isn't this in Kernel_C? *)
lemmas C_register_defs =
  Kernel_C.R0_def Kernel_C.R1_def Kernel_C.R2_def Kernel_C.R3_def
  Kernel_C.R4_def Kernel_C.R5_def Kernel_C.R6_def Kernel_C.R7_def
  Kernel_C.R8_def Kernel_C.R9_def Kernel_C.R10_def Kernel_C.R11_def
  Kernel_C.R12_def Kernel_C.SP_def Kernel_C.LR_def Kernel_C.NextIP_def
  Kernel_C.CPSR_def Kernel_C.TLS_BASE_def Kernel_C.TPIDRURW_def Kernel_C.TPIDRURO_def
  Kernel_C.FaultIP_def

(* Levity: moved from Retype_C (20090419 09:44:41) *)
lemma no_overlap_new_cap_addrs_disjoint:
  "\<lbrakk> range_cover ptr sz (objBitsKO ko) n;
     pspace_aligned' s;
     pspace_no_overlap' ptr sz s \<rbrakk> \<Longrightarrow>
   set (new_cap_addrs n ptr ko) \<inter> dom (ksPSpace s) = {}"
  apply (erule disjoint_subset [OF new_cap_addrs_subset, where sz1=sz])
  apply (clarsimp simp: More_Word_Operations.ptr_add_def field_simps)
  apply (rule pspace_no_overlap_disjoint')
  apply auto
  done

declare empty_fail_doMachineOp [simp]

lemma asUser_get_registers:
  "\<lbrace>tcb_at' target\<rbrace>
     asUser target (mapM getRegister xs)
   \<lbrace>\<lambda>rv s. obj_at' (\<lambda>tcb. map ((user_regs \<circ> atcbContextGet \<circ> tcbArch) tcb) xs = rv) target s\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_empty asUser_return)
   apply wp
   apply simp
  apply (simp add: mapM_Cons asUser_bind_distrib asUser_return empty_fail_cond)
  apply wp
   apply simp
   apply (rule hoare_strengthen_post)
    apply (erule hoare_vcg_conj_lift)
    apply (rule asUser_inv)
    apply (simp add: getRegister_def)
    apply (wp mapM_wp')
   apply clarsimp
   apply (erule(1) obj_at_conj')
  apply (wp)
   apply (simp add: asUser_def split_def threadGet_def)
   apply (wp getObject_tcb_wp)
  apply (clarsimp simp: getRegister_def simpler_gets_def
                        obj_at'_def)
  done

(* only exists in Haskell, only used for C refinement *)
crunch writeTTBR0Ptr
  for (empty_fail) empty_fail[wp,simp]

end

schematic_goal sz8_helper:
  "((-1) << 8 :: addr) = ?v"
  by (simp add: shiftl_t2n)

lemmas reset_name_seq_bound_helper2
    = reset_name_seq_bound_helper[where sz=8 and v="v :: addr" for v,
          simplified sz8_helper word_bits_def[symmetric],
          THEN name_seq_bound_helper]

end
