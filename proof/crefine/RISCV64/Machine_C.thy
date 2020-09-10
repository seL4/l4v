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
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>addr___unsigned_long = pt\<rbrace> \<inter> \<lbrace>\<acute>asid___unsigned_long = asid\<rbrace>) []
           (doMachineOp (RISCV64.setVSpaceRoot pt asid))
           (Call setVSpaceRoot_'proc)"

assumes hwASIDFlush_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>asid___unsigned_long = asid\<rbrace>) []
           (doMachineOp (RISCV64.hwASIDFlush asid))
           (Call hwASIDFlush_'proc)"

assumes read_stval_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp RISCV64.read_stval)
           (Call read_stval_'proc)"

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

assumes plic_complete_claim_ccorres:
  "ccorres dc xfdc \<top> \<lbrace>\<acute>irq = ucast irq\<rbrace> []
           (doMachineOp (plic_complete_claim irq))
           (Call plic_complete_claim_'proc)"

assumes setIRQTrigger_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>irq = ucast irq\<rbrace> \<inter> \<lbrace>\<acute>edge_triggered = from_bool trigger\<rbrace>) []
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

(* Count leading and trailing zeros. *)

(* FIXME: move *)
lemma word_ctz_max:
  "word_ctz w \<le> size w"
  sorry

(* FIXME move *)
lemma scast_of_nat_small:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> scast (of_nat x :: 'a :: len word) = (of_nat x :: 'b :: len word)"
  apply (rule sym, subst word_unat.inverse_norm)
  apply (simp add: scast_def word_of_int[symmetric]
                   of_nat_nat[symmetric] unat_def[symmetric])
  apply (simp add: int_eq_sint unat_of_nat)
  done

(* FIXME move *)
lemmas casts_of_nat_small = ucast_of_nat_small scast_of_nat_small

(* FIXME: move *)
lemma hoarep_Seq_nothrow:
  assumes c: "hoarep \<Gamma> \<Theta> F P c Q {}"
  assumes d: "hoarep \<Gamma> \<Theta> F Q d R A"
  shows "hoarep \<Gamma> \<Theta> F P (Seq c d) R A"
  by (rule hoarep.Seq[OF HoarePartialDef.conseqPrePost[OF c] d]; simp)

definition clz32_step where
  "clz32_step i \<equiv> \<acute>mask___unsigned :== \<acute>mask___unsigned >> unat ((1::32 sword) << unat i);;
                 \<acute>bits :== SCAST(32 signed \<rightarrow> 32) (if \<acute>mask___unsigned < \<acute>x___unsigned then 1 else 0) << unat i;;
                 Guard ShiftError \<lbrace>\<acute>bits < SCAST(32 signed \<rightarrow> 32) 0x20\<rbrace> (\<acute>x___unsigned :== \<acute>x___unsigned >> unat \<acute>bits);;
                 \<acute>count :== \<acute>count - \<acute>bits"

(* FIXME: figure out what this should be *)
definition clz32_invariant where
  "clz32_invariant i s \<equiv> {s'. undefined ''clz32_invariant'' i s s'}"

lemma clz32_step:
  "\<Gamma> \<turnstile> (clz32_invariant (i+1) s) clz32_step i (clz32_invariant i s)"
  unfolding clz32_step_def
  apply (vcg, clarsimp simp: clz32_invariant_def)
  sorry

lemma clz32_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call clz32_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_clz (x___unsigned_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold clz32_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="clz32_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
  apply (rule HoarePartial.SeqSwap[OF clz32_step], simp)+
  apply (rule conseqPre, vcg)
  apply (all \<open>clarsimp simp: clz32_invariant_def\<close>)
  sorry

definition clz64_step where
  "clz64_step i \<equiv> \<acute>mask___unsigned_longlong :== \<acute>mask___unsigned_longlong >> unat ((1::32 sword) << unat i);;
                   \<acute>bits :== SCAST(32 signed \<rightarrow> 32) (if \<acute>mask___unsigned_longlong < \<acute>x___unsigned_longlong then 1 else 0) << unat i;;
                   Guard ShiftError \<lbrace>\<acute>bits < SCAST(32 signed \<rightarrow> 32) 0x40\<rbrace> (\<acute>x___unsigned_longlong :== \<acute>x___unsigned_longlong >> unat \<acute>bits);;
                   \<acute>count :== \<acute>count - \<acute>bits"

(* FIXME: figure out what this should be *)
definition clz64_invariant where
  "clz64_invariant i s \<equiv> {s'. undefined ''clz64_invariant'' i s s'}"

lemma clz64_step:
  "\<Gamma> \<turnstile> (clz64_invariant (i+1) s) clz64_step i (clz64_invariant i s)"
  unfolding clz64_step_def
  apply (vcg, clarsimp simp: clz64_invariant_def)
  sorry

lemma clz64_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call clz64_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_clz (x___unsigned_longlong_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold clz64_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="clz64_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
  apply (rule HoarePartial.SeqSwap[OF clz64_step], simp)+
  apply (rule conseqPre, vcg)
  apply (all \<open>clarsimp simp: clz64_invariant_def\<close>)
  sorry

definition ctz32_step where
  "ctz32_step i \<equiv> \<acute>mask___unsigned :== \<acute>mask___unsigned >> unat ((1::32 sword) << unat i);;
                   \<acute>bits :== SCAST(32 signed \<rightarrow> 32) (if \<acute>x___unsigned && \<acute>mask___unsigned = SCAST(32 signed \<rightarrow> 32) 0 then 1 else 0) << unat i;;
                   Guard ShiftError \<lbrace>\<acute>bits < SCAST(32 signed \<rightarrow> 32) 0x20\<rbrace> (\<acute>x___unsigned :== \<acute>x___unsigned >> unat \<acute>bits);;
                   \<acute>count :== \<acute>count + \<acute>bits"

(* FIXME: figure out what this should be *)
definition ctz32_invariant where
  "ctz32_invariant i s \<equiv> {s'. undefined ''ctz32_invariant'' i s s'}"

lemma ctz32_step:
  "\<Gamma> \<turnstile> (ctz32_invariant (i+1) s) ctz32_step i (ctz32_invariant i s)"
  unfolding ctz32_step_def
  apply (vcg, clarsimp simp: ctz32_invariant_def)
  sorry

lemma ctz32_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call ctz32_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_ctz (x___unsigned_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold ctz32_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="ctz32_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
  apply (rule HoarePartial.SeqSwap[OF ctz32_step], simp)+
  apply (rule conseqPre, vcg)
  apply (all \<open>clarsimp simp: ctz32_invariant_def\<close>)
  sorry

definition ctz64_step where
  "ctz64_step i \<equiv> \<acute>mask___unsigned_longlong :== \<acute>mask___unsigned_longlong >> unat ((1::32 sword) << unat i);;
                   \<acute>bits :== SCAST(32 signed \<rightarrow> 32) (if \<acute>x___unsigned_longlong && \<acute>mask___unsigned_longlong = SCAST(32 signed \<rightarrow> 64) 0 then 1 else 0) << unat i;;
                   Guard ShiftError \<lbrace>\<acute>bits < SCAST(32 signed \<rightarrow> 32) 0x40\<rbrace> (\<acute>x___unsigned_longlong :== \<acute>x___unsigned_longlong >> unat \<acute>bits);;
                   \<acute>count :== \<acute>count + \<acute>bits"

(* FIXME: figure out what this should be *)
definition ctz64_invariant where
  "ctz64_invariant i s \<equiv> {s'. undefined ''ctz64_invariant'' i s s'}"

lemma ctz64_step:
  "\<Gamma> \<turnstile> (ctz64_invariant (i+1) s) ctz64_step i (ctz64_invariant i s)"
  unfolding ctz64_step_def
  apply (vcg, clarsimp simp: ctz64_invariant_def)
  sorry

lemma ctz64_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call ctz64_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_ctz (x___unsigned_longlong_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold ctz64_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="ctz64_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
  apply (rule HoarePartial.SeqSwap[OF ctz64_step], simp)+
  apply (rule conseqPre, vcg)
  apply (all \<open>clarsimp simp: ctz64_invariant_def\<close>)
  sorry

(* The library implementations would allow us to weaken the preconditions to allow zero inputs,
   but we keep the stronger preconditions to preserve older proofs that use these specs. *)
lemma clzl_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0}
   Call clzl_'proc
   \<lbrace>\<acute>ret__long = of_nat (word_clz (x___unsigned_long_' s))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  by (clarsimp simp: casts_of_nat_small[OF word_clz_max[THEN le_less_trans]] word_size)

lemma ctzl_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0}
   Call ctzl_'proc
   \<lbrace>\<acute>ret__long = of_nat (word_ctz (x___unsigned_long_' s))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  by (clarsimp simp: casts_of_nat_small[OF word_ctz_max[THEN le_less_trans]] word_size)

end
end
