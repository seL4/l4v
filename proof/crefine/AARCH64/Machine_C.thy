(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Assumptions and lemmas on machine operations.
*)

theory Machine_C
imports Ctac_lemmas_C
begin

(* FIXME: somewhere automation has failed, resulting in virq_C arrays not being in packed_type! *)
instance virq_C :: array_inner_packed
  apply intro_classes
  by (simp add: size_of_def)

locale kernel_m = kernel +

(* timer and IRQ common machine ops (function names exist on other platforms *)

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

assumes getActiveIRQ_ccorres:
  "\<And>in_kernel.
   ccorres
     (\<lambda>irq c_irq.
        case irq of None \<Rightarrow> c_irq = irqInvalid
                  | Some x \<Rightarrow> c_irq = ucast x \<and> c_irq \<noteq> irqInvalid)
     ret__unsigned_long_' \<top> UNIV hs
     (doMachineOp (getActiveIRQ in_kernel)) (Call getActiveIRQ_'proc)"

assumes setIRQTrigger_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>irq = ucast irq\<rbrace> \<inter> \<lbrace>\<acute>trigger = from_bool trigger\<rbrace>) []
           (doMachineOp (AARCH64.setIRQTrigger irq trigger))
           (Call setIRQTrigger_'proc)"

assumes ackInterrupt_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>irq = ucast irq\<rbrace>) hs
           (doMachineOp (ackInterrupt irq))
           (Call ackInterrupt_'proc)"

assumes maskInterrupt_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>disable = from_bool m\<rbrace> \<inter> \<lbrace>\<acute>irq = ucast irq\<rbrace>) []
           (doMachineOp (maskInterrupt m irq))
           (Call maskInterrupt_'proc)"

(* This is a simplification until complete FPU handling is added at a future date *)
assumes fpuThreadDelete_ccorres:
  "ccorres dc xfdc (tcb_at' thread) (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
     (fpuThreadDelete thread)
     (Call fpuThreadDelete_'proc)"

assumes setVSpaceRoot_ccorres:
  "ccorres dc xfdc
           \<top> (\<lbrace> base_address_CL (ttbr_lift \<acute>ttbr) = pt\<rbrace> \<inter> \<lbrace> asid_CL (ttbr_lift \<acute>ttbr) = asid\<rbrace>) []
           (doMachineOp (AARCH64.setVSpaceRoot pt asid))
           (Call setCurrentUserVSpaceRoot_'proc)"

(* AArch64-specific machine ops (function names don't exist on other architectures) *)

assumes getFAR_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp getFAR)
           (Call getFAR_'proc)"

assumes getESR_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp getESR)
           (Call getESR_'proc)"

assumes setHCR_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>reg = r \<rbrace>) []
           (doMachineOp (setHCR r))
           (Call setHCR_'proc)"

assumes getSCTLR_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp getSCTLR)
           (Call getSCTLR_'proc)"

assumes setSCTLR_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>sctlr = sctlr \<rbrace>) []
           (doMachineOp (setSCTLR sctlr))
           (Call setSCTLR_'proc)"

assumes isb_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp isb)
           (Call isb_'proc)"

assumes dsb_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp dsb)
           (Call dsb_'proc)"

assumes dsb_preserves_kernel_bytes:
 "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call dsb_'proc
      {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
          \<and> (\<forall>x. snd (hrs_htd (t_hrs_' (globals s)) x) 0 \<noteq> None
                 \<longrightarrow> hrs_mem (t_hrs_' (globals t)) x = hrs_mem (t_hrs_' (globals s)) x)}"

assumes enableFpuEL01_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp enableFpuEL01)
           (Call enableFpuEL01_'proc)"

assumes check_export_arch_timer_ccorres:
    "ccorres dc xfdc \<top> UNIV []
           (doMachineOp check_export_arch_timer)
           (Call check_export_arch_timer_'proc)"

assumes read_cntpct_ccorres:
    "ccorres (=) ret__unsigned_longlong_' \<top> UNIV []
           (doMachineOp read_cntpct)
           (Call read_cntpct_'proc)"

(* TLB and Cache ops *)

assumes addressTranslateS1_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top> (\<lbrace>\<acute>vaddr___unsigned_long = vaddr \<rbrace>) []
           (doMachineOp (addressTranslateS1 vaddr))
           (Call addressTranslateS1_'proc)"

assumes invalidateTranslationASID_ccorres:
  "\<And>hw_asid. ccorres dc xfdc \<top> (\<lbrace>\<acute>hw_asid___unsigned_char = ucast hw_asid\<rbrace>) []
                     (doMachineOp (invalidateTranslationASID hw_asid))
                     (Call invalidateTranslationASID_'proc)"

assumes invalidateTranslationSingle_ccorres:
  "\<And>vptr. ccorres dc xfdc \<top> (\<lbrace>\<acute>vptr = vptr\<rbrace>) []
                     (doMachineOp (invalidateTranslationSingle vptr))
                     (Call invalidateTranslationSingle_'proc)"

assumes cleanByVA_PoU_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vaddr = w1\<rbrace> \<inter> \<lbrace>\<acute>paddr = w2\<rbrace>) []
           (doMachineOp (cleanByVA_PoU w1 w2))
           (Call cleanByVA_PoU_'proc)"

assumes cleanCacheRange_RAM_ccorres:
  "ccorres dc xfdc (\<lambda>s. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                        \<and> w1 && mask cacheLineBits  = w3 && mask cacheLineBits
                        \<and> unat (w2 - w1) \<le> gsMaxObjectSize s)
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (cleanCacheRange_RAM w1 w2 w3))
           (Call cleanCacheRange_RAM_'proc)"

assumes cleanCacheRange_PoU_ccorres:
  "ccorres dc xfdc (\<lambda>s. unat (w2 - w1) \<le> gsMaxObjectSize s
                        \<and> w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                        \<and> w1 && mask cacheLineBits = w3 && mask cacheLineBits)
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (cleanCacheRange_PoU w1 w2 w3))
           (Call cleanCacheRange_PoU_'proc)"

assumes cleanInvalidateCacheRange_RAM_ccorres:
  "ccorres dc xfdc (\<lambda>s. unat (w2 - w1) \<le> gsMaxObjectSize s
                        \<and> w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                        \<and> w1 && mask cacheLineBits = w3 && mask cacheLineBits)
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (cleanInvalidateCacheRange_RAM w1 w2 w3))
           (Call cleanInvalidateCacheRange_RAM_'proc)"

assumes invalidateCacheRange_RAM_ccorres:
  "ccorres dc xfdc ((\<lambda>s. unat (w2 - w1) \<le> gsMaxObjectSize s)
                    and (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                      \<and> w1 && mask cacheLineBits = w3 && mask cacheLineBits))
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (invalidateCacheRange_RAM w1 w2 w3))
           (Call invalidateCacheRange_RAM_'proc)"

assumes invalidateCacheRange_I_ccorres:
  "ccorres dc xfdc (\<lambda>_. w1 \<le> w2 \<and> w3 \<le> w3 + (w2 - w1)
                        \<and> w1 && mask cacheLineBits = w3 && mask cacheLineBits)
                   (\<lbrace>\<acute>start = w1\<rbrace> \<inter> \<lbrace>\<acute>end = w2\<rbrace> \<inter> \<lbrace>\<acute>pstart = w3\<rbrace>) []
           (doMachineOp (invalidateCacheRange_I w1 w2 w3))
           (Call invalidateCacheRange_I_'proc)"

assumes cleanCacheRange_RAM_preserves_kernel_bytes:
 "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call cleanCacheRange_RAM_'proc
      {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
          \<and> (\<forall>x. snd (hrs_htd (t_hrs_' (globals s)) x) 0 \<noteq> None
                 \<longrightarrow> hrs_mem (t_hrs_' (globals t)) x = hrs_mem (t_hrs_' (globals s)) x)}"

assumes cleanCacheRange_PoU_preserves_kernel_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call cleanCacheRange_PoU_'proc
       {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
           \<and> (\<forall>x. snd (hrs_htd (t_hrs_' (globals s)) x) 0 \<noteq> None
                  \<longrightarrow> hrs_mem (t_hrs_' (globals t)) x = hrs_mem (t_hrs_' (globals s)) x)}"


(* Hypervisor-related machine ops *)

(* ARM Hypervisor hardware register getters and setters *)

assumes get_gic_vcpu_ctrl_hcr_ccorres:
  "ccorres (=) ret__unsigned_' \<top> UNIV []
           (doMachineOp get_gic_vcpu_ctrl_hcr) (Call get_gic_vcpu_ctrl_hcr_'proc)"
assumes get_gic_vcpu_ctrl_vmcr_ccorres:
  "ccorres (=) ret__unsigned_' \<top> UNIV []
           (doMachineOp get_gic_vcpu_ctrl_vmcr) (Call get_gic_vcpu_ctrl_vmcr_'proc)"
assumes get_gic_vcpu_ctrl_apr_ccorres:
  "ccorres (=) ret__unsigned_' \<top> UNIV []
           (doMachineOp get_gic_vcpu_ctrl_apr) (Call get_gic_vcpu_ctrl_apr_'proc)"
assumes get_gic_vcpu_ctrl_vtr_ccorres:
  "ccorres (=) ret__unsigned_' \<top> UNIV []
           (doMachineOp get_gic_vcpu_ctrl_vtr) (Call get_gic_vcpu_ctrl_vtr_'proc)"
assumes get_gic_vcpu_ctrl_eisr0_ccorres:
  "ccorres (=) ret__unsigned_' \<top> UNIV []
           (doMachineOp get_gic_vcpu_ctrl_eisr0) (Call get_gic_vcpu_ctrl_eisr0_'proc)"
assumes get_gic_vcpu_ctrl_eisr1_ccorres:
  "ccorres (=) ret__unsigned_' \<top> UNIV []
           (doMachineOp get_gic_vcpu_ctrl_eisr1) (Call get_gic_vcpu_ctrl_eisr1_'proc)"
assumes get_gic_vcpu_ctrl_misr_ccorres:
  "ccorres (=) ret__unsigned_' \<top> UNIV []
           (doMachineOp get_gic_vcpu_ctrl_misr) (Call get_gic_vcpu_ctrl_misr_'proc)"

assumes set_gic_vcpu_ctrl_hcr_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>hcr = v \<rbrace>) []
     (doMachineOp (set_gic_vcpu_ctrl_hcr v)) (Call set_gic_vcpu_ctrl_hcr_'proc)"
assumes set_gic_vcpu_ctrl_vmcr_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>vmcr = v \<rbrace>) []
     (doMachineOp (set_gic_vcpu_ctrl_vmcr v)) (Call set_gic_vcpu_ctrl_vmcr_'proc)"
assumes set_gic_vcpu_ctrl_apr_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>apr = v \<rbrace>) []
     (doMachineOp (set_gic_vcpu_ctrl_apr v)) (Call set_gic_vcpu_ctrl_apr_'proc)"

assumes set_gic_vcpu_ctrl_lr_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>num = scast n \<rbrace> \<inter> \<lbrace>virq_to_H \<acute>lr = lr \<rbrace>) []
     (doMachineOp (set_gic_vcpu_ctrl_lr n lr)) (Call set_gic_vcpu_ctrl_lr_'proc)"

assumes get_gic_vcpu_ctrl_lr_ccorres:
  "ccorres (\<lambda>v virq. virq = virq_C (FCP (\<lambda>_. v))) ret__struct_virq_C_' \<top> (\<lbrace>\<acute>num = scast n \<rbrace>) hs
           (doMachineOp (get_gic_vcpu_ctrl_lr n)) (Call get_gic_vcpu_ctrl_lr_'proc)"

(* Lazy FPU switching is not in current verification scope. We abstract this by acting as if
   FPU is always enabled. When the FPU switching implementation is updated, this assumption
   should be removed. *)
assumes isFpuEnable_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp isFpuEnable)
           (Call isFpuEnable_'proc)"

(* ARM Hypervisor banked register save/restoring *)

assumes vcpu_hw_read_reg_ccorres:
  "\<And>r. ccorres (=) ret__unsigned_long_'
         \<top> (\<lbrace> unat \<acute>reg_index = fromEnum r \<rbrace>) hs
         (doMachineOp (readVCPUHardwareReg r))
         (Call vcpu_hw_read_reg_'proc)"

assumes vcpu_hw_write_reg_ccorres:
  "\<And>r v. ccorres dc xfdc
           \<top> (\<lbrace> unat \<acute>reg_index = fromEnum r \<rbrace> \<inter> \<lbrace> \<acute>reg = v \<rbrace>) hs
           (doMachineOp (writeVCPUHardwareReg r v))
           (Call vcpu_hw_write_reg_'proc)"

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
               [AARCH64_H.badgeRegister, AARCH64_H.msgInfoRegister]
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

(* FIXME AARCH64 clzl and ctzl use builtin compiler versions, while clz32/64 and ctz32/64 are
   software implementations that are provided BUT NOT USED, hence this whole chunk except for
   clzl_spec and ctzl_spec can be removed. *)

definition clz32_step where
  "clz32_step i \<equiv>
    \<acute>mask___unsigned :== \<acute>mask___unsigned >> unat ((1::32 sword) << unat i);;
    \<acute>bits___unsigned :== SCAST(32 signed \<rightarrow> 32) (if \<acute>mask___unsigned < \<acute>x___unsigned then 1 else 0) << unat i;;
    Guard ShiftError \<lbrace>\<acute>bits___unsigned < SCAST(32 signed \<rightarrow> 32) 0x20\<rbrace>
      (\<acute>x___unsigned :== \<acute>x___unsigned >> unat \<acute>bits___unsigned);;
    \<acute>count :== \<acute>count - \<acute>bits___unsigned"

definition clz32_invariant where
  "clz32_invariant i s \<equiv> {s'.
   mask___unsigned_' s' \<ge> x___unsigned_' s'
   \<and> of_nat (word_clz (x___unsigned_' s')) + count_' s' = of_nat (word_clz (x___unsigned_' s)) + 32
   \<and> mask___unsigned_' s' = mask (2 ^ unat i)}"

lemma clz32_step:
  "unat (i :: 32 sword) < 5 \<Longrightarrow>
   \<Gamma> \<turnstile> (clz32_invariant (i+1) s) clz32_step i (clz32_invariant i s)"
  unfolding clz32_step_def
  apply (vcg, clarsimp simp: clz32_invariant_def)
  \<comment> \<open>Introduce some trivial but useful facts so that most later goals are solved with simp\<close>
  apply (prop_tac "i \<noteq> -1", clarsimp simp: unat_minus_one_word)
  apply (frule unat_Suc2)
  apply (prop_tac "(2 :: nat) ^ unat i < (32 :: nat)",
         clarsimp simp: power_strict_increasing_iff[where b=2 and y=5, simplified])
  apply (prop_tac "(2 :: nat) ^ unat (i + 1) \<le> (32 :: nat)",
         clarsimp simp: unat_Suc2 power_increasing_iff[where b=2 and y=4, simplified])
  apply (intro conjI impI; clarsimp)
       apply (clarsimp simp: word_less_nat_alt)
      apply (erule le_shiftr)
     apply (clarsimp simp: word_size shiftr_mask2 word_clz_shiftr)
    apply (clarsimp simp: shiftr_mask2)
   apply fastforce
  apply (clarsimp simp: shiftr_mask2)
  done

lemma clz32_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call clz32_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_clz (x___unsigned_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold clz32_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="clz32_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
   apply (rule HoarePartial.SeqSwap[OF clz32_step], simp, simp)+
   apply (rule conseqPre, vcg)
   apply (all \<open>clarsimp simp: clz32_invariant_def mask_def word_less_max_simp\<close>)
  by (fastforce simp: word_le_1)

definition clz64_step where
  "clz64_step i \<equiv>
    \<acute>mask___unsigned_longlong :== \<acute>mask___unsigned_longlong >> unat ((1::32 sword) << unat i);;
    \<acute>bits___unsigned :== SCAST(32 signed \<rightarrow> 32) (if \<acute>mask___unsigned_longlong < \<acute>x___unsigned_longlong then 1 else 0) << unat i;;
    Guard ShiftError \<lbrace>\<acute>bits___unsigned < SCAST(32 signed \<rightarrow> 32) 0x40\<rbrace>
      (\<acute>x___unsigned_longlong :== \<acute>x___unsigned_longlong >> unat \<acute>bits___unsigned);;
    \<acute>count :== \<acute>count - \<acute>bits___unsigned"

definition clz64_invariant where
  "clz64_invariant i s \<equiv> {s'.
   mask___unsigned_longlong_' s' \<ge> x___unsigned_longlong_' s'
   \<and> of_nat (word_clz (x___unsigned_longlong_' s')) + count_' s' = of_nat (word_clz (x___unsigned_longlong_' s)) + 64
   \<and> mask___unsigned_longlong_' s' = mask (2 ^ unat i)}"

lemma clz64_step:
  "unat (i :: 32 sword) < 6 \<Longrightarrow>
   \<Gamma> \<turnstile> (clz64_invariant (i+1) s) clz64_step i (clz64_invariant i s)"
  unfolding clz64_step_def
  apply (vcg, clarsimp simp: clz64_invariant_def)
  \<comment> \<open>Introduce some trivial but useful facts so that most later goals are solved with simp\<close>
  apply (prop_tac "i \<noteq> -1", clarsimp simp: unat_minus_one_word)
  apply (frule unat_Suc2)
  apply (prop_tac "(2 :: nat) ^ unat i < (64 :: nat)",
         clarsimp simp: power_strict_increasing_iff[where b=2 and y=6, simplified])
  apply (prop_tac "(2 :: nat) ^ unat (i + 1) \<le> (64 :: nat)",
         clarsimp simp: unat_Suc2 power_increasing_iff[where b=2 and y=5, simplified])
  apply (intro conjI impI; clarsimp)
       apply (clarsimp simp: word_less_nat_alt)
      apply (erule le_shiftr)
     apply (clarsimp simp: word_size shiftr_mask2 word_clz_shiftr)
    apply (clarsimp simp: shiftr_mask2)
   apply fastforce
  apply (clarsimp simp: shiftr_mask2)
  done

lemma clz64_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call clz64_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_clz (x___unsigned_longlong_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold clz64_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="clz64_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
   apply (rule HoarePartial.SeqSwap[OF clz64_step], simp, simp)+
   apply (rule conseqPre, vcg)
   apply (all \<open>clarsimp simp: clz64_invariant_def mask_def word_less_max_simp\<close>)
  apply (clarsimp simp: word_le_1)
  apply (erule disjE; clarsimp)
  apply (subst add.commute)
  apply (subst ucast_increment[symmetric])
   apply (simp add: not_max_word_iff_less)
   apply (rule word_of_nat_less)
   apply (rule le_less_trans[OF word_clz_max])
   apply (simp add: word_size unat_max_word)
  apply clarsimp
  done

definition ctz32_step where
  "ctz32_step i \<equiv> \<acute>mask___unsigned :== \<acute>mask___unsigned >> unat ((1::32 sword) << unat i);;
                   \<acute>bits___unsigned :== SCAST(32 signed \<rightarrow> 32) (if \<acute>x___unsigned && \<acute>mask___unsigned = SCAST(32 signed \<rightarrow> 32) 0 then 1 else 0) << unat i;;
                   Guard ShiftError \<lbrace>\<acute>bits___unsigned < SCAST(32 signed \<rightarrow> 32) 0x20\<rbrace> (\<acute>x___unsigned :== \<acute>x___unsigned >> unat \<acute>bits___unsigned);;
                   \<acute>count :== \<acute>count + \<acute>bits___unsigned"

definition ctz32_invariant where
  "ctz32_invariant (i :: 32 sword) s \<equiv> {s'.
     (x___unsigned_' s' \<noteq> 0 \<longrightarrow> (of_nat (word_ctz (x___unsigned_' s')) + count_' s' = of_nat (word_ctz (x___unsigned_' s))
   \<and> (word_ctz (x___unsigned_' s') < 2 ^ unat i)))
   \<and> (x___unsigned_' s' = 0 \<longrightarrow> (count_' s' + (0x1 << (unat i)) = 33 \<and> x___unsigned_' s = 0))
   \<and> mask___unsigned_' s' = mask (2 ^ unat i)}"

lemma ctz32_step:
  "unat (i :: 32 sword) < 5 \<Longrightarrow>
   \<Gamma> \<turnstile> (ctz32_invariant (i+1) s) ctz32_step i (ctz32_invariant i s)"
  supply word_neq_0_conv [simp del]
  unfolding ctz32_step_def
  apply (vcg, clarsimp simp: ctz32_invariant_def)
  apply (prop_tac "i \<noteq> -1", clarsimp simp: unat_minus_one_word)
  apply (frule unat_Suc2)
  apply (prop_tac "(2 :: nat) ^ unat i < (32 :: nat)",
         clarsimp simp: power_strict_increasing_iff[where b=2 and y=5, simplified])
  apply (prop_tac "(2 :: nat) ^ unat (i + 1) \<le> (32 :: nat)",
         clarsimp simp: unat_Suc2 power_increasing_iff[where b=2 and y=4, simplified])
  apply (intro conjI; intro impI)
   apply (intro conjI)
      apply (clarsimp simp: word_less_nat_alt)
     apply (intro impI)
     apply (subgoal_tac "x___unsigned_' x \<noteq> 0")
      apply (intro conjI, clarsimp)
       apply (subst word_ctz_shiftr, clarsimp, clarsimp)
        apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
        apply (clarsimp simp: shiftr_mask2 is_aligned_mask[symmetric])
       apply (subst of_nat_diff)
        apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
        apply (clarsimp simp: shiftr_mask2)
       apply fastforce
      apply (subst word_ctz_shiftr, clarsimp, clarsimp)
       apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
       apply (clarsimp simp: shiftr_mask2 is_aligned_mask[symmetric])
      apply (fastforce elim: is_aligned_weaken)
     apply fastforce
    apply (intro impI conjI; clarsimp simp: shiftr_mask2)
     apply (subgoal_tac "x___unsigned_' x = 0", clarsimp)
      apply (subst add.commute, simp)
     apply (fastforce simp: shiftr_mask2 word_neq_0_conv and_mask_eq_iff_shiftr_0[symmetric])
    apply (simp add: and_mask_eq_iff_shiftr_0[symmetric])
   apply (clarsimp simp: shiftr_mask2)
  by (fastforce simp: shiftr_mask2 intro: word_ctz_bound_above)

lemma ctz32_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call ctz32_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_ctz (x___unsigned_' s))\<rbrace>"
  supply word_neq_0_conv [simp del]
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold ctz32_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="ctz32_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
   apply (rule HoarePartial.SeqSwap[OF ctz32_step], simp, simp)+
   apply (rule conseqPre, vcg)
   apply (clarsimp simp: ctz32_invariant_def)
   apply (clarsimp simp: mask_def)
   apply (subgoal_tac "word_ctz (x___unsigned_' s) \<le> size (x___unsigned_' s)")
    apply (clarsimp simp: word_size)
  using word_ctz_len_word_and_mask_zero apply force
   apply (rule word_ctz_max)
  apply (clarsimp simp: ctz32_invariant_def)
  apply (case_tac "x___unsigned_' x = 0"; clarsimp)
  done

definition ctz64_step where
  "ctz64_step i \<equiv> \<acute>mask___unsigned_longlong :== \<acute>mask___unsigned_longlong >> unat ((1::32 sword) << unat i);;
                   \<acute>bits___unsigned :== SCAST(32 signed \<rightarrow> 32) (if \<acute>x___unsigned_longlong && \<acute>mask___unsigned_longlong = SCAST(32 signed \<rightarrow> 64) 0 then 1 else 0) << unat i;;
                   Guard ShiftError \<lbrace>\<acute>bits___unsigned < SCAST(32 signed \<rightarrow> 32) 0x40\<rbrace> (\<acute>x___unsigned_longlong :== \<acute>x___unsigned_longlong >> unat \<acute>bits___unsigned);;
                   \<acute>count :== \<acute>count + \<acute>bits___unsigned"

definition ctz64_invariant where
  "ctz64_invariant i s \<equiv> {s'.
     (x___unsigned_longlong_' s' \<noteq> 0 \<longrightarrow> (of_nat (word_ctz (x___unsigned_longlong_' s')) + count_' s' = of_nat (word_ctz (x___unsigned_longlong_' s))
   \<and> (word_ctz (x___unsigned_longlong_' s') < 2 ^ unat i)))
   \<and> (x___unsigned_longlong_' s' = 0 \<longrightarrow> (count_' s' + (0x1 << (unat i)) = 65 \<and> x___unsigned_longlong_' s = 0))
   \<and> mask___unsigned_longlong_' s' = mask (2 ^ unat i)}"

lemma ctz64_step:
  "unat (i :: 32 sword) < 6 \<Longrightarrow>
   \<Gamma> \<turnstile> (ctz64_invariant (i+1) s) ctz64_step i (ctz64_invariant i s)"
supply word_neq_0_conv [simp del]
  unfolding ctz64_step_def
  apply (vcg, clarsimp simp: ctz64_invariant_def)
  apply (prop_tac "i \<noteq> -1", clarsimp simp: unat_minus_one_word)
  apply (frule unat_Suc2)
  apply (prop_tac "(2 :: nat) ^ unat i < (64 :: nat)",
         clarsimp simp: power_strict_increasing_iff[where b=2 and y=6, simplified])
  apply (prop_tac "(2 :: nat) ^ unat (i + 1) \<le> (64 :: nat)",
         clarsimp simp: unat_Suc2 power_increasing_iff[where b=2 and y=5, simplified])
  apply (intro conjI; intro impI)
   apply (intro conjI)
      apply (clarsimp simp: word_less_nat_alt)
     apply (intro impI)
     apply (subgoal_tac "x___unsigned_longlong_' x \<noteq> 0")
      apply (intro conjI, clarsimp)
       apply (subst word_ctz_shiftr, clarsimp, clarsimp)
        apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
        apply (clarsimp simp: shiftr_mask2 is_aligned_mask[symmetric])
       apply (subst of_nat_diff)
        apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
        apply (clarsimp simp: shiftr_mask2)
     apply fastforce
      apply (subst word_ctz_shiftr, clarsimp, clarsimp)
       apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
       apply (clarsimp simp: shiftr_mask2 is_aligned_mask[symmetric])
      apply (fastforce elim: is_aligned_weaken)
     apply fastforce
    apply (intro impI conjI; clarsimp simp: shiftr_mask2)
     apply (subgoal_tac "x___unsigned_longlong_' x = 0", clarsimp)
      apply (subst add.commute, simp)
     apply (fastforce simp: shiftr_mask2 word_neq_0_conv and_mask_eq_iff_shiftr_0[symmetric])
    apply (simp add: and_mask_eq_iff_shiftr_0[symmetric])
   apply (clarsimp simp: shiftr_mask2)
  by (fastforce simp: shiftr_mask2 intro: word_ctz_bound_above)

lemma ctz64_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call ctz64_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_ctz (x___unsigned_longlong_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold ctz64_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="ctz64_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
   apply (rule HoarePartial.SeqSwap[OF ctz64_step], simp, simp)+
   apply (rule conseqPre, vcg)
   apply (clarsimp simp: ctz64_invariant_def)
   apply (clarsimp simp: mask_def)
   apply (subgoal_tac "word_ctz (x___unsigned_longlong_' s) \<le> size (x___unsigned_longlong_' s)")
    apply (clarsimp simp: word_size)
    apply (erule le_neq_trans, clarsimp)
    using word_ctz_len_word_and_mask_zero[where 'a=64] apply force
   apply (rule word_ctz_max)
  apply (clarsimp simp: ctz64_invariant_def)
  apply (case_tac "x___unsigned_longlong_' x = 0"; clarsimp)
  done

(* On AArch64, clzl and ctzl use compiler builtins and hence these are rephrasings of
   Kernel_C.clzl_spec.clzl_spec and Kernel_C.ctzl_spec.ctzl_spec to omit "symbol_table" *)

lemma clzl_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0} Call clzl_'proc
       \<lbrace>\<acute>ret__long = of_nat (word_clz (x___unsigned_long_' s))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply clarsimp
  apply (rule_tac x="ret__long_'_update f x" for f in exI)
  apply (simp add: mex_def meq_def)
  done

lemma ctzl_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0} Call ctzl_'proc
       \<lbrace>\<acute>ret__long = of_nat (word_ctz (x___unsigned_long_' s))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply clarsimp
  apply (rule_tac x="ret__long_'_update f x" for f in exI)
  apply (simp add: mex_def meq_def)
  done

(* FIXME AARCH64 there are a whole lot of cache op lemmas on ARM_HYP, e.g.
     cleanCaches_PoU_ccorres, branchFlushRange_ccorres, invalidateCacheRange_I_ccorres,
     invalidateCacheRange_RAM_ccorres, cleanCacheRange_PoU_ccorres, etc.
     We'll probably need some of these. *)

end
end
