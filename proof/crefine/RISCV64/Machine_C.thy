(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Author: Rafal Kolanski

   Assumptions and lemmas on machine operations.
*)

theory Machine_C
imports Ctac_lemmas_C
begin

locale kernel_m = kernel +

assumes setVSpaceRoot_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>addr = pt\<rbrace> \<inter> \<lbrace>\<acute>asid___unsigned_long = asid\<rbrace>) []
           (doMachineOp (RISCV64.setVSpaceRoot pt asid))
           (Call setVSpaceRoot_'proc)"

assumes hwASIDFlush_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>asid___unsigned_long = asid\<rbrace>) []
           (doMachineOp (RISCV64.hwASIDFlush asid))
           (Call hwASIDFlush_'proc)"

assumes read_sbadaddr_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp RISCV64.read_sbadaddr)
           (Call read_sbadaddr_'proc)"

assumes sfence_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp RISCV64.sfence)
           (Call sfence_'proc)"

assumes maskInterrupt_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>disable = from_bool m\<rbrace> \<inter> \<lbrace>\<acute>irq = ucast irq\<rbrace>) []
           (doMachineOp (maskInterrupt m irq))
           (Call maskInterrupt_'proc)"

assumes getActiveIRQ_ccorres:
"\<And>in_kernel.
   ccorres (\<lambda>(a::irq option) c::64 word.
     case a of None \<Rightarrow> c = ucast irqInvalid
     | Some (x::irq) \<Rightarrow> c = ucast x \<and> c \<noteq> ucast irqInvalid)
     ret__unsigned_long_'
     \<top> UNIV hs
 (doMachineOp (getActiveIRQ in_kernel)) (Call getActiveIRQ_'proc)"

assumes ackInterrupt_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
           (doMachineOp (ackInterrupt irq))
           (Call ackInterrupt_'proc)"

assumes setIRQTrigger_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>irq = ucast irq\<rbrace> \<inter> \<lbrace>\<acute>trigger = from_bool trigger\<rbrace>) []
           (doMachineOp (RISCV64.setIRQTrigger irq trigger))
           (Call setIRQTrigger_'proc)"

assumes resetTimer_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp resetTimer)
           (Call resetTimer_'proc)"

(* This is not very correct, however our current implementation of Hardware in haskell is stateless *)
assumes isIRQPending_ccorres:
  "\<And>in_kernel.
     ccorres (\<lambda>rv rv'. rv' = from_bool (rv \<noteq> None)) ret__unsigned_long_'
      \<top> UNIV []
      (doMachineOp (getActiveIRQ in_kernel)) (Call isIRQPending_'proc)"

assumes getActiveIRQ_Normal:
  "\<Gamma> \<turnstile> \<langle>Call getActiveIRQ_'proc, Normal s\<rangle> \<Rightarrow> s' \<Longrightarrow> isNormal s'"

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
               [RISCV64_H.badgeRegister, RISCV64_H.msgInfoRegister]
               [bdg, msginfo]))
     (Call fastpath_restore_'proc)"

context kernel_m begin

lemma index_xf_for_sequence:
  "\<forall>s f. index_' (index_'_update f s) = f (index_' s)
          \<and> globals (index_'_update f s) = globals s"
  by simp

lemma dmo_if:
  "(doMachineOp (if a then b else c)) = (if a then (doMachineOp b) else (doMachineOp c))"
  by (simp split: if_split)

end

end
