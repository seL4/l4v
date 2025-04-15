(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Author: Gerwin Klein

   Assumptions and lemmas on machine operations.
*)

theory Machine_C
imports Ctac_lemmas_C
begin

(* FIXME x64: add all machine operations as required *)
locale kernel_m = kernel +
assumes getFaultAddr_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp getFaultAddress)
           (Call getFaultAddr_'proc)"

assumes resetTimer_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp resetTimer)
           (Call resetTimer_'proc)"

assumes ioapicMapPinToVector_ccorres:
  "ccorres dc xfdc \<top>
     (UNIV \<inter> \<lbrace>\<acute>ioapic___unsigned_long = ioapic\<rbrace>
           \<inter> \<lbrace>\<acute>pin___unsigned_long = pin\<rbrace>
           \<inter> \<lbrace>\<acute>level___unsigned_long = level\<rbrace>
           \<inter> \<lbrace>\<acute>polarity = polarity\<rbrace>
           \<inter> \<lbrace>\<acute>vector___unsigned_long = vector\<rbrace>)
     []
     (doMachineOp (ioapicMapPinToVector ioapic pin level polarity vector))
     (Call ioapic_map_pin_to_vector_'proc)"

(* FIXME: x64: Currently don't verify FPU lazy state switching (VER-951) *)
assumes nativeThreadUsingFPU_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_'
     (tcb_at' thread)
     (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>)
     []
     (doMachineOp (nativeThreadUsingFPU thread))
     (Call nativeThreadUsingFPU_'proc)"

assumes switchFpuOwner_ccorres:
  "ccorres dc xfdc \<top>
     (UNIV \<inter> \<lbrace>\<acute>new_owner = Ptr new_owner\<rbrace>
           \<inter> \<lbrace>\<acute>cpu = cpu\<rbrace>)
     []
     (doMachineOp (switchFpuOwner new_owner cpu))
     (Call switchFpuOwner_'proc)"

(* FIXME x64: double-check this, assumption is ccorres holds regardless of in_kernel *)
(* FIXME x64: accessor function relation was complicated on ARM, testing if you don't
              need it to be that way *)
assumes getActiveIRQ_ccorres:
"\<And>in_kernel.
   ccorres (\<lambda>(a::8 word option) c::64 word.
     case a of None \<Rightarrow> c = (0xFF::64 word)
     | Some (x::8 word) \<Rightarrow> c = ucast x \<and> c \<noteq> (0xFF::64 word))
     ret__unsigned_long_'
     \<top> UNIV hs
 (doMachineOp (getActiveIRQ in_kernel)) (Call getActiveIRQ_'proc)"

(* This is not very correct, however our current implementation of Hardware in haskell is stateless *)
assumes isIRQPending_ccorres:
  "\<And>in_kernel.
     ccorres (\<lambda>rv rv'. rv' = from_bool (rv \<noteq> None)) ret__unsigned_long_'
      \<top> UNIV []
      (doMachineOp (getActiveIRQ in_kernel)) (Call isIRQPending_'proc)"

assumes getActiveIRQ_Normal:
  "\<Gamma> \<turnstile> \<langle>Call getActiveIRQ_'proc, Normal s\<rangle> \<Rightarrow> s' \<Longrightarrow> isNormal s'"

assumes maskInterrupt_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>disable = from_bool m\<rbrace> \<inter> \<lbrace>\<acute>irq = ucast irq\<rbrace>) []
           (doMachineOp (maskInterrupt m irq))
           (Call maskInterrupt_'proc)"

assumes invalidateTranslationSingleASID_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>asid = asid\<rbrace> \<inter> \<lbrace>\<acute>vptr = vptr\<rbrace>) []
           (doMachineOp (invalidateTranslationSingleASID vptr asid))
           (Call invalidateTranslationSingleASID_'proc)"

assumes invalidateASID_ccorres:
  "ccorres dc xfdc \<top> (UNIV \<inter> \<lbrace>\<acute>vspace = pml4e_Ptr vspace\<rbrace> \<inter> \<lbrace>\<acute>asid = asid\<rbrace>) []
           (doMachineOp (invalidateASID vspace asid)) (Call invalidateASID_'proc)"

assumes invalidateLocalPageStructureCacheASID_ccorres:
  "ccorres dc xfdc \<top> (UNIV \<inter> \<lbrace>\<acute>root = vspace\<rbrace> \<inter> \<lbrace>\<acute>asid = asid\<rbrace>) []
           (doMachineOp (invalidateLocalPageStructureCacheASID vspace asid))
           (Call invalidateLocalPageStructureCacheASID_'proc)"


(* FPU-related machine ops *)

assumes saveFpuState_ccorres:
  "ccorres dc xfdc (tcb_at' t) (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t \<rbrace>) []
     (saveFpuState t) (Call saveFpuState_'proc)"

assumes loadFpuState_ccorres:
  "ccorres dc xfdc (tcb_at' t) (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr t \<rbrace>) []
     (loadFpuState t) (Call loadFpuState_'proc)"

assumes enableFpu_ccorres:
  "ccorres dc xfdc \<top> UNIV []
     (doMachineOp enableFpu) (Call enableFpu_'proc)"

assumes disableFpu_ccorres:
  "ccorres dc xfdc \<top> UNIV []
     (doMachineOp disableFpu) (Call disableFpu_'proc)"


(* The following are fastpath specific assumptions.
   We might want to move them somewhere else. *)

(*
  @{text slowpath} is an assembly stub that switches execution
  from the fastpath to the slowpath. Its contract is equivalence
  to the toplevel slowpath function @{term callKernel} for the
  @{text SyscallEvent} case.
*)
assumes slowpath_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> ct_in_state' ((=) Running) s)
     ({s. syscall_' s = syscall_from_H ev})
     [SKIP]
     (callKernel (SyscallEvent ev)) (Call slowpath_'proc)"

(*
  @{text slowpath} does not return, but uses the regular
  slowpath kernel exit instead.
*)
assumes slowpath_noreturn_spec:
  "\<Gamma> \<turnstile> UNIV Call slowpath_'proc {},UNIV"

(*
  @{text fastpath_restore} updates badge and msgInfo registers
  and returns to the user.
*)
assumes fastpath_restore_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. t = ksCurThread s)
     ({s. badge_' s = bdg} \<inter> {s. msgInfo_' s = msginfo}
           \<inter> {s. cur_thread_' s = tcb_ptr_to_ctcb_ptr t})
     [SKIP]
     (asUser t (zipWithM_x setRegister
               [X64_H.badgeRegister, X64_H.msgInfoRegister]
               [bdg, msginfo]))
     (Call fastpath_restore_'proc)"

assumes ackInterrupt_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
           (doMachineOp (ackInterrupt irq))
           (Call ackInterrupt_'proc)"

assumes in8_ccorres:
  "ccorres (\<lambda>ar cr. ar = ucast cr) ret__unsigned_char_'
        \<top>
        (UNIV \<inter> {s. port_' s = port}) []
           (doMachineOp (in8 port))
           (Call in8_'proc)"

assumes in16_ccorres:
  "ccorres (\<lambda>ar cr. ar = ucast cr) ret__unsigned_short_'
        \<top>
        (UNIV \<inter> {s. port_' s = port}) []
           (doMachineOp (in16 port))
           (Call in16_'proc)"

assumes in32_ccorres:
  "ccorres (\<lambda>ar cr. ar = ucast cr) ret__unsigned_'
        \<top>
        (UNIV \<inter> {s. port_' s = port}) []
           (doMachineOp (in32 port))
           (Call in32_'proc)"

assumes out8_ccorres:
  "ccorres dc xfdc
         \<top>
        (UNIV \<inter> {s. port_' s = port} \<inter> {s. value___unsigned_char_' s = ucast dat}) []
           (doMachineOp (out8 port dat))
           (Call out8_'proc)"

assumes out16_ccorres:
  "ccorres dc xfdc
         \<top>
        (UNIV \<inter> {s. port_' s = port} \<inter> {s. value___unsigned_short_' s = ucast dat16}) []
           (doMachineOp (out16 port dat16))
           (Call out16_'proc)"

assumes out32_ccorres:
  "ccorres dc xfdc
         \<top>
        (UNIV \<inter> {s. port_' s = port} \<inter> {s. value___unsigned_' s = ucast dat32}) []
           (doMachineOp (out32 port dat32))
           (Call out32_'proc)"

context kernel_m begin

lemma wrap_config_set_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call wrap_config_set_'proc \<lbrace>\<acute>ret__int = x_' s\<rbrace>"
  by (rule allI, rule conseqPre, vcg) clarsimp

lemma index_xf_for_sequence:
  "\<forall>s f. index_' (index_'_update f s) = f (index_' s)
          \<and> globals (index_'_update f s) = globals s"
  by simp

lemma dmo_if:
  "(doMachineOp (if a then b else c)) = (if a then (doMachineOp b) else (doMachineOp c))"
  by (simp split: if_split)

end

end
