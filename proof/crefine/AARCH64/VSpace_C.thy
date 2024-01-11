(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory VSpace_C
imports TcbAcc_C CSpace_C PSpace_C TcbQueue_C
begin

unbundle l4v_word_context

autocorres
  [ skip_heap_abs, skip_word_abs,
    scope = handleVMFault,
    scope_depth = 0,
    c_locale = kernel_all_substitute
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

context begin interpretation Arch . (*FIXME: arch_split*)

lemma ccorres_name_pre_C:
  "(\<And>s. s \<in> P' \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P {s} hs f g)
   \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs f g"
  apply (rule ccorres_guard_imp)
    apply (rule_tac xf'=id in ccorres_abstract, rule ceqv_refl)
    apply (rule_tac P="rv' \<in> P'" in ccorres_gen_asm2)
    apply assumption
   apply simp
  apply simp
  done

lemma ccorres_flip_Guard:
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F S (Guard F' S' c))"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F' S' (Guard F S c))"
  apply (rule ccorres_name_pre_C)
  using cc
  apply (case_tac "s \<in> (S' \<inter> S)")
   apply (clarsimp simp: ccorres_underlying_def)
   apply (erule exec_handlers.cases;
    fastforce elim!: exec_Normal_elim_cases intro: exec_handlers.intros exec.Guard)
  apply (clarsimp simp: ccorres_underlying_def)
  apply (case_tac "s \<in> S")
   apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros)
  apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros)
  done

end

context kernel_m begin

lemma pageBitsForSize_le:
  "pageBitsForSize x \<le> 30"
  by (simp add: pageBitsForSize_def bit_simps split: vmpage_size.splits)

lemma unat_of_nat_pageBitsForSize[simp]:
  "unat (of_nat (pageBitsForSize x)::machine_word) = pageBitsForSize x"
  apply (subst unat_of_nat64)
   apply (rule order_le_less_trans, rule pageBitsForSize_le)
   apply (simp add: word_bits_def)
  apply simp
  done

(* FIXME AARCH64 checkVPAlignment has gone missing in C, it is used in decodeRISCVFrameInvocation
   for RISCVPageMap, and on ARM_HYP for decodeARMFrameInvocation/ARMPageMap
   For AARCH64 it does the calculation inline via a macro: IS_PAGE_ALIGNED(vaddr, frameSize)
   TODO: re-introduce checkVPAlignment in C
lemma checkVPAlignment_ccorres:
  "ccorres (\<lambda>a c. if to_bool c then a = Inr () else a = Inl AlignmentError) ret__unsigned_long_'
           \<top>
           (\<lbrace>sz = framesize_to_H \<acute>sz \<and> \<acute>sz < 3\<rbrace> \<inter> \<lbrace>\<acute>w = w\<rbrace>)
           []
           (checkVPAlignment sz w)
           (Call checkVPAlignment_'proc)"
  apply (cinit lift: sz_' w_')
   apply (csymbr)
   apply clarsimp
   apply (rule ccorres_Guard [where A=\<top> and C'=UNIV])
   apply (simp split: if_split)
   apply (rule conjI)
    apply (clarsimp simp: mask_def unlessE_def returnOk_def)
    apply (rule ccorres_guard_imp)
      apply (rule ccorres_return_C)
        apply simp
       apply simp
      apply simp
     apply simp
    apply (simp split: if_split)
   apply (clarsimp simp: mask_def unlessE_def throwError_def split: if_split)
   apply (rule ccorres_guard_imp)
     apply (rule ccorres_return_C)
       apply simp
      apply simp
     apply simp
    apply simp
   apply (simp split: if_split)
  apply (clarsimp split: if_split)
  apply (simp add: word_less_nat_alt)
  apply (rule order_le_less_trans, rule pageBitsForSize_le)
  apply simp
  done *)

lemma rf_asidTable:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; valid_arch_state' \<sigma>; idx \<le> mask asid_high_bits \<rbrakk>
     \<Longrightarrow> case armKSASIDTable (ksArchState \<sigma>)
                idx of
        None \<Rightarrow>
            index (armKSASIDTable_' (globals x)) (unat idx) =
               NULL
             | Some v \<Rightarrow>
                 index (armKSASIDTable_' (globals x)) (unat idx) = Ptr v \<and>
                 index (armKSASIDTable_' (globals x)) (unat idx) \<noteq> NULL"
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                             carch_state_relation_def
                             array_relation_def)
  apply (drule_tac x=idx in spec)+
  apply (clarsimp simp: mask_def split: option.split)
  apply (drule sym, simp)
  apply (simp add: option_to_ptr_def option_to_0_def)
  apply (fastforce simp: invs'_def valid_state'_def valid_arch_state'_def
                         valid_asid_table'_def ran_def)
  done

lemma getKSASIDTable_ccorres_stuff:
  "\<lbrakk> invs' \<sigma>; (\<sigma>, x) \<in> rf_sr; idx' = unat idx;
             idx < 2 ^ asid_high_bits \<rbrakk>
     \<Longrightarrow> case armKSASIDTable (ksArchState \<sigma>)
                idx of
        None \<Rightarrow>
            index (armKSASIDTable_' (globals x))
                idx' =
               NULL
             | Some v \<Rightarrow>
                 index (armKSASIDTable_' (globals x))
                  idx' = Ptr v \<and>
                 index (armKSASIDTable_' (globals x))
                  idx' \<noteq> NULL"
  apply (drule rf_asidTable [where idx=idx])
    apply fastforce
   apply (simp add: mask_def)
   apply (simp add: word_le_minus_one_leq)
  apply (clarsimp split: option.splits)
  done

lemma asidLowBits_handy_convs:
  "sint Kernel_C.asidLowBits = 9"
  "Kernel_C.asidLowBits \<noteq> 0x20"
  "unat Kernel_C.asidLowBits = asid_low_bits"
  by (simp add: Kernel_C.asidLowBits_def asid_low_bits_def)+

lemma rf_sr_armKSASIDTable:
  "\<lbrakk> (s, s') \<in> rf_sr; n \<le> mask asid_high_bits \<rbrakk>
   \<Longrightarrow> index (armKSASIDTable_' (globals s')) (unat n)
      = option_to_ptr (armKSASIDTable (ksArchState s) n)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                     carch_state_relation_def array_relation_def)

lemma asid_high_bits_word_bits:
  "asid_high_bits < word_bits"
  by (simp add: asid_high_bits_def word_bits_def)

lemma array_relation_update:
  "\<lbrakk> array_relation R bnd table (arr :: 'a['b :: finite]);
               x' = unat (x :: ('td :: len) word); R v v';
               unat bnd < card (UNIV :: 'b set) \<rbrakk>
     \<Longrightarrow> array_relation R bnd (table (x := v))
               (Arrays.update arr x' v')"
  by (simp add: array_relation_def word_le_nat_alt split: if_split)

definition vm_fault_type_from_H :: "vmfault_type \<Rightarrow> machine_word" where
  "vm_fault_type_from_H fault \<equiv>
    case fault of
      vmfault_type.ARMDataAbort \<Rightarrow> scast Kernel_C.ARMDataAbort
    | vmfault_type.ARMPrefetchAbort \<Rightarrow> scast Kernel_C.ARMPrefetchAbort"

lemmas vm_fault_defs_C =
         Kernel_C.ARMDataAbort_def
         Kernel_C.ARMPrefetchAbort_def

(* FIXME: automate this *)
lemma seL4_Fault_VMFault_new'_spec:
  "\<lbrace> \<lambda>s. s = \<sigma> \<rbrace> seL4_Fault_VMFault_new' addr FSR i
   \<lbrace> \<lambda>r s. s = \<sigma>
            \<and> seL4_Fault_VMFault_lift r = \<lparr>address_CL = addr, FSR_CL = FSR && mask 32, instructionFault_CL = i && mask 1\<rparr>
            \<and> seL4_Fault_get_tag r = scast seL4_Fault_VMFault \<rbrace>"
  apply (rule hoare_weaken_pre, rule hoare_strengthen_post)
    apply (rule autocorres_transfer_spec_no_modifies
                  [where cs="undefined\<lparr>globals := \<sigma>, address_' := addr,
                                       FSR_' := FSR, instructionFault_' := i\<rparr>",
                   OF seL4_Fault_VMFault_new'_def seL4_Fault_VMFault_new_spec
                      seL4_Fault_VMFault_new_modifies])
      by auto

lemma no_fail_seL4_Fault_VMFault_new':
  "no_fail \<top> (seL4_Fault_VMFault_new' addr fault i)"
  apply (rule terminates_spec_no_fail'[OF seL4_Fault_VMFault_new'_def seL4_Fault_VMFault_new_spec])
  apply clarsimp
  apply terminates_trivial
  done

(* FIXME AARCH64 this doesn't make much sense currently with hyp, but was a helper used by
     handleVMFault_ccorres, so possibly could still have that role once updated *)
lemma returnVMFault_corres:
  "\<lbrakk> addr = addr'; i = i' && mask 1; fault = fault' && mask 32 \<rbrakk> \<Longrightarrow>
   corres_underlying
     {(x, y). cstate_relation x y} True True
     (lift_rv id (\<lambda>y. ()) (\<lambda>e. e) (\<lambda>_ _. False)
                 (\<lambda>e f e'. f = SCAST(32 signed \<rightarrow> 64) EXCEPTION_FAULT \<and>
                           (\<exists>vf. e = ArchFault (VMFault (address_CL vf) [instructionFault_CL vf, FSR_CL vf])
                                       \<and> errfault e' = Some (SeL4_Fault_VMFault vf))))
     \<top> \<top>
     (throwError (Fault_H.fault.ArchFault (VMFault addr [i, fault])))
     (do f <- seL4_Fault_VMFault_new' addr' fault' i';
         _ <- modify (current_fault_'_update (\<lambda>_. f));
         e <- gets errglobals;
         return (scast EXCEPTION_FAULT, e)
      od)"
  apply (rule corres_symb_exec_r)
     apply (rename_tac vmf)
     apply (rule_tac F="seL4_Fault_VMFault_lift vmf = \<lparr>address_CL = addr, FSR_CL = fault && mask 32, instructionFault_CL = i && mask 1\<rparr>
                         \<and> seL4_Fault_get_tag vmf = scast seL4_Fault_VMFault"
              in corres_gen_asm2)
     apply (rule lift_rv_throwError;
            clarsimp simp: exception_defs seL4_Fault_VMFault_lift)
    apply (wpsimp wp: valid_spec_to_wp'[OF seL4_Fault_VMFault_new'_spec]
                      no_fail_seL4_Fault_VMFault_new'
                simp: mask_twice)+
  done

lemma handleVMFault_ccorres:
  "ccorres ((\<lambda>f ex v. ex = scast EXCEPTION_FAULT
                      \<and> (\<exists>vf. f = ArchFault (VMFault (address_CL vf)
                                             [instructionFault_CL vf, FSR_CL vf])
                          \<and> errfault v = Some (SeL4_Fault_VMFault vf))) \<currency> \<bottom>\<bottom>)
           (liftxf errstate id (K ()) ret__unsigned_long_')
           \<top>
           (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
            \<inter> \<lbrace>\<acute>vm_faultType = vm_fault_type_from_H vm_fault\<rbrace>)
           []
           (handleVMFault thread vm_fault)
           (Call handleVMFault_'proc)"
  (* FIXME: make this a real ac_init *)
  apply (rule corres_to_ccorres_rv_spec_errglobals[OF _ _ refl],
         rule handleVMFault'_ac_corres[simplified o_def])
    prefer 3 apply simp
   apply (simp add: handleVMFault_def handleVMFault'_def liftE_bindE condition_const
                    ucast_ucast_mask bind_assoc)
   (* FIXME AARCH64 left in as a guideline of how this autocorres-based proof handles machine ops
   apply (rule corres_split[OF read_stval_ccorres[ac]])
      apply terminates_trivial
     apply (drule sym, clarsimp)   *)
     apply (corres_cases; simp add: vm_fault_type_from_H_def vm_fault_defs_C bind_assoc)
      sorry
      (* FIXME AARCH64 the rest looks analogous
          to ARM_HYP's handleVMFault_ccorres except for it being an autocorres-style proof now;
          original riscv proof, could be helpful for last step of both cases:
          apply (rule returnVMFault_corres;
                 clarsimp simp: exception_defs mask_twice lift_rv_def mask_def vmFaultTypeFSR_def)+
     apply wpsimp+
  done  *)

lemma unat_asidLowBits[simp]:
  "unat Kernel_C.asidLowBits = asidLowBits"
  by (simp add: asidLowBits_def Kernel_C.asidLowBits_def asid_low_bits_def)

lemma asid_wf_eq_mask_eq:
  "asid_wf asid = (asid && mask asid_bits = asid)"
  by (simp add: asid_wf_def and_mask_eq_iff_le_mask)

lemma leq_asid_bits_shift:
  "asid_wf x \<Longrightarrow> (x::machine_word) >> asid_low_bits \<le> mask asid_high_bits"
  unfolding asid_wf_def
  apply (rule word_leI)
  apply (simp add: nth_shiftr word_size)
  apply (rule ccontr)
  apply (clarsimp simp: linorder_not_less asid_high_bits_def asid_low_bits_def)
  apply (simp add: mask_def)
  apply (simp add: upper_bits_unset_is_l2p_64 [symmetric])
  apply (simp add: asid_bits_def word_bits_def)
  apply (erule_tac x="asid_low_bits+n" in allE) (*asid_low_bits*)
  apply (simp add: linorder_not_less asid_low_bits_def)
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done

lemma ucast_asid_high_bits_is_shift:
  "asid_wf asid \<Longrightarrow> ucast (asid_high_bits_of (ucast asid)) = asid >> asid_low_bits"
  unfolding asid_wf_def
  apply (simp add: mask_def upper_bits_unset_is_l2p_64[symmetric])
  apply (simp add: asid_high_bits_of_def mask_2pm1[symmetric] ucast_ucast_mask)
  using shiftr_mask_eq[where n=asid_low_bits and x=asid, simplified]
  apply (simp add: asid_low_bits_def word_size asid_bits_def word_bits_def mask_def)
  apply word_bitwise
  apply simp
  done

lemma rf_sr_asidTable_None:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; asid_wf asid; valid_arch_state' \<sigma>  \<rbrakk> \<Longrightarrow>
  (index (armKSASIDTable_' (globals x)) (unat (asid >> asid_low_bits)) = ap_Ptr 0) =
  (armKSASIDTable (ksArchState \<sigma>) (ucast (asid_high_bits_of (ucast asid))) = None)"
  apply (simp add: ucast_asid_high_bits_is_shift)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)
  apply (simp add: array_relation_def option_to_0_def)
  apply (erule_tac x="asid >> asid_low_bits" in allE)
  apply (erule impE)
   apply (simp add: leq_asid_bits_shift flip: mask_2pm1)
  apply (drule sym [where t="index a b" for a b])
  apply (simp add: option_to_0_def option_to_ptr_def split: option.splits)
  apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def ran_def)
  done

lemma clift_ptr_safe:
  "clift (h, x) ptr = Some a
   \<Longrightarrow> ptr_safe ptr x"
  by (erule lift_t_ptr_safe[where g = c_guard])

lemma clift_ptr_safe2:
  "clift htd ptr = Some a
   \<Longrightarrow> ptr_safe ptr (hrs_htd htd)"
  by (cases htd, simp add: hrs_htd_def clift_ptr_safe)

lemma ptTranslationBits_mask_le: "(x::machine_word) && 0x1FF < 0x200"
  by (word_bitwise)

lemma ptrFromPAddr_spec:
  "\<forall>s. \<Gamma> \<turnstile>  {s}
  Call ptrFromPAddr_'proc
  \<lbrace>  \<acute>ret__ptr_to_void =  Ptr (ptrFromPAddr (paddr_' s) ) \<rbrace>"
  apply vcg
  apply (simp add: AARCH64.ptrFromPAddr_def AARCH64.pptrBase_def pptrBaseOffset_def paddrBase_def)
  done

lemma addrFromPPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile>  {s}
  Call addrFromPPtr_'proc
  \<lbrace>  \<acute>ret__unsigned_long =  (addrFromPPtr (ptr_val (pptr_' s)) ) \<rbrace>"
  apply vcg
  apply (simp add: addrFromPPtr_def AARCH64.pptrBase_def pptrBaseOffset_def paddrBase_def)
  done

lemma addrFromKPPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
   Call addrFromKPPtr_'proc
   \<lbrace>\<acute>ret__unsigned_long = addrFromKPPtr (ptr_val (pptr_' s))\<rbrace>"
  apply vcg
  apply (simp add: addrFromKPPtr_def kernelELFBaseOffset_def kernelELFPAddrBase_def
                   kernelELFBase_def pptrBase_def mask_def)
  done

(* FIXME: move *)
lemma corres_symb_exec_unknown_r:
  assumes "\<And>rv. corres_underlying sr nf nf' r P P' a (c rv)"
  shows "corres_underlying sr nf nf' r P P' a (unknown >>= c)"
  apply (simp add: unknown_def)
  apply (rule corres_symb_exec_r[OF assms]; wp select_inv no_fail_select)
  done

lemma isPageTablePTE_def2:
  "isPageTablePTE pte = (\<exists>ppn. pte = PageTablePTE ppn)"
  by (simp add: isPageTablePTE_def split: pte.splits)

(* FIXME AARCH64 no longer present on this arch, but be wary of analogues
lemma getPPtrFromHWPTE_spec':
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>pte___ptr_to_struct_pte_C \<rbrace>
           Call getPPtrFromHWPTE_'proc
           \<lbrace> \<acute>ret__ptr_to_struct_pte_C =
               pte_Ptr (ptrFromPAddr (pte_CL.ppn_CL (pte_lift
                            (the (clift \<^bsup>s\<^esup>t_hrs \<^bsup>s\<^esup>pte___ptr_to_struct_pte_C))) << pageBits)) \<rbrace>"
  by vcg (simp add: bit_simps)

lemma getPPtrFromHWPTE_corres:
  "ccorres (\<lambda>_ ptr. ptr = pte_Ptr (getPPtrFromHWPTE pte))
     ret__ptr_to_struct_pte_C_'
     (ko_at' pte ptePtr and K (isPageTablePTE pte))
     \<lbrace> \<acute>pte___ptr_to_struct_pte_C = pte_Ptr ptePtr \<rbrace>
     hs
     (return ())
     (Call getPPtrFromHWPTE_'proc)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: return_def rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
  apply (drule (1) cmap_relation_ko_atD)
  apply (clarsimp simp: typ_heap_simps getPPtrFromHWPTE_def cpte_relation_def Let_def
                        isPageTablePTE_def2 bit_simps)
  done

lemma isPTEPageTable_spec':
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>pte___ptr_to_struct_pte_C \<rbrace>
           Call isPTEPageTable_'proc
           \<lbrace> \<forall>cpte pte. clift \<^bsup>s\<^esup>t_hrs \<^bsup>s\<^esup>pte___ptr_to_struct_pte_C = Some cpte \<longrightarrow>
                        cpte_relation pte cpte \<longrightarrow>
             \<acute>ret__unsigned_long = from_bool (isPageTablePTE pte) \<rbrace>"
  by vcg
     (auto simp: cpte_relation_def isPageTablePTE_def2 Let_def
                 readable_from_vm_rights_def writable_from_vm_rights_def bit_simps
           split: bool.split if_split pte.splits vmrights.splits)

lemma readable_from_vm_rights0:
  "(readable_from_vm_rights vm = (0::machine_word)) = (vm = VMKernelOnly)"
  by (auto simp add: readable_from_vm_rights_def split: vmrights.splits)

lemma isPTEPageTable_corres:
  "ccorres (\<lambda>_ isPTE. isPTE = from_bool (isPageTablePTE pte))
     ret__unsigned_long_'
     (ko_at' pte ptePtr)
     \<lbrace> \<acute>pte___ptr_to_struct_pte_C = pte_Ptr ptePtr \<rbrace>
     hs
     (return ())
     (Call isPTEPageTable_'proc)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre)
  apply vcg
  apply (clarsimp simp: return_def)
  apply (drule rf_sr_cpte_relation)
  apply (drule (1) cmap_relation_ko_atD)
  apply (clarsimp simp: typ_heap_simps)
  apply (cases pte; simp add: readable_from_vm_rights0 isPageTablePTE_def
                              cpte_relation_def writable_from_vm_rights_def)
  done *)

lemma ccorres_checkPTAt:
  "ccorres_underlying srel Ga rrel xf arrel axf P P' hs (a ()) c \<Longrightarrow>
   ccorres_underlying srel Ga rrel xf arrel axf
                      (\<lambda>s. (\<exists>pt_t. page_table_at' pt_t pt s) \<longrightarrow> P s) P' hs (checkPTAt pt >>= a) c"
  unfolding checkPTAt_def by (rule ccorres_stateAssert)

lemma pteAtIndex_ko[wp]:
  "\<lbrace>\<top>\<rbrace> pteAtIndex level pt vptr \<lbrace>\<lambda>pte. ko_at' pte (ptSlotIndex level pt vptr)\<rbrace>"
  unfolding pteAtIndex_def by (wpsimp wp: getPTE_wp)

lemma ptBitsLeft_bound:
  "level \<le> maxPTLevel \<Longrightarrow> ptBitsLeft level \<le> canonical_bit"
  by (simp add: ptBitsLeft_def bit_simps maxPTLevel_def canonical_bit_def split: if_splits)

lemma unat_of_nat_ptBitsLeft[simp]:
  "level \<le> maxPTLevel \<Longrightarrow> unat (of_nat (ptBitsLeft level)::machine_word) = ptBitsLeft level"
  apply (subst unat_of_nat64)
   apply (rule order_le_less_trans, erule ptBitsLeft_bound)
   apply (simp add: word_bits_def canonical_bit_def)
  apply simp
  done

(* FIXME AARCH64 this is a helper for lookupPTSlotFromLevel_ccorres, should be true, but ensure it
   actually helps *)
lemma pte_at'_ptSlotIndex:
  "\<lbrakk> page_table_at' pt_t pt s; levelType level = pt_t \<rbrakk> \<Longrightarrow> pte_at' (ptSlotIndex level pt vptr) s"
  apply (simp add: ptSlotIndex_def ptIndex_def)
  apply (drule page_table_pte_atI'[where i="ucast (vptr >> ptBitsLeft level) && mask (ptTranslationBits pt_t)"])
   (* proving the first subgoal looks like it would enable proving the second *)
   prefer 2
   apply (simp add: ucast_ucast_mask split: if_splits)
  apply (simp add: ucast_ucast_mask bit_simps)
  apply (simp add: Kernel_Config.config_ARM_PA_SIZE_BITS_40_def ptBitsLeft_def
                   ptTranslationBits_def pageBits_def maxPTLevel_def word_bool_le_funs
              split: if_splits)
  done

lemmas unat_and_mask_le_ptTrans = unat_and_mask_le[OF AARCH64.ptTranslationBits_le_machine_word]

lemma lookupPTSlotFromLevel_ccorres:
  (* these are copied out of lookupPTSlot_ccorres with "_'proc" removed, and schematic preconditions
     set, and main goal has pdSlot_upd folded for brevity *)
  (* FIXME AARCH64 style/indentation once this works *)
  defines
    "ptSlot_upd \<equiv>
       Guard ShiftError \<lbrace>ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C < 0x40\<rbrace>
          (Guard MemorySafety
            \<lbrace>(\<acute>vptr >> unat (ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C)) && 0x1FF = 0 \<or>
             array_assertion \<acute>pt
              (unat ((\<acute>vptr >> unat (ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C)) && 0x1FF))
              (hrs_htd \<acute>t_hrs)\<rbrace>
            (\<acute>ret___struct_lookupPTSlot_ret_C :==
               ptSlot_C_update
                (\<lambda>_. \<acute>pt +\<^sub>p
                     uint ((\<acute>vptr >> unat (ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C)) && 0x1FF))
                \<acute>ret___struct_lookupPTSlot_ret_C))"
  shows (* FIXME AARCH64 note for induction maxPTLevel is changed to level *)
    "
       ccorres (\<lambda>(bitsLeft, ptSlot) cr. bitsLeft = unat (ptBitsLeft_C cr) \<and> ptSlot_C cr = pte_Ptr ptSlot)
        ret__struct_lookupPTSlot_ret_C_'
     (page_table_at' VSRootPT_T pt)
     (\<lbrace> ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C = of_nat (ptBitsLeft level) \<rbrace>
      \<inter> \<lbrace> \<acute>level = of_nat level \<rbrace> \<inter> \<lbrace> \<acute>pt = Ptr pt \<rbrace> \<inter> \<lbrace> \<acute>vptr = vptr \<rbrace>)
     (SKIP # hs)
        (lookupPTSlotFromLevel level pt vptr)
        (ptSlot_upd;;
         \<acute>ret__unsigned_long :== CALL pte_pte_table_ptr_get_present(ptSlot_C
                     \<acute>ret___struct_lookupPTSlot_ret_C);;
         WHILE \<acute>ret__unsigned_long \<noteq> 0 \<and> 0 < \<acute>level DO
           \<acute>level :== \<acute>level - 1;;
           \<acute>ret___struct_lookupPTSlot_ret_C :==
             ptBitsLeft_C_update (\<lambda>_. ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C - 9)
              \<acute>ret___struct_lookupPTSlot_ret_C;;
           \<acute>ret__unsigned_longlong :== CALL pte_pte_table_ptr_get_pt_base_address(ptSlot_C
                                   \<acute>ret___struct_lookupPTSlot_ret_C);;
           \<acute>ret__ptr_to_void :== CALL ptrFromPAddr(UCAST(64 \<rightarrow> 64) \<acute>ret__unsigned_longlong);;
           \<acute>pt :== PTR_COERCE(unit \<rightarrow> pte_C) \<acute>ret__ptr_to_void;;
           ptSlot_upd;;
           \<acute>ret__unsigned_long :== CALL pte_pte_table_ptr_get_present(ptSlot_C
                       \<acute>ret___struct_lookupPTSlot_ret_C)
         OD;;
         return_C ret__struct_lookupPTSlot_ret_C_'_update ret___struct_lookupPTSlot_ret_C_')
    "
  (* FIXME AARCH64 old version:
  shows
    "ccorres (\<lambda>(bitsLeft,ptSlot) cr. bitsLeft = unat (ptBitsLeft_C cr) \<and> ptSlot_C cr = Ptr ptSlot)
     ret__struct_lookupPTSlot_ret_C_'
     (page_table_at' pt and (\<lambda>_. level \<le> maxPTLevel))
     (\<lbrace> ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C = of_nat (ptTranslationBits * level + ptBits) \<rbrace>
      \<inter> \<lbrace> \<acute>level = of_nat level \<rbrace> \<inter> \<lbrace> \<acute>pt = Ptr pt \<rbrace> \<inter> \<lbrace> \<acute>vptr = vptr \<rbrace>)
     (SKIP#hs)
     (lookupPTSlotFromLevel level pt vptr)
     (ptSlot_upd;;
      \<acute>ret__unsigned_long :== CALL pte_pte_table_ptr_get_present(ptSlot_C \<acute>ret___struct_lookupPTSlot_ret_C);;
      WHILE \<acute>ret__unsigned_long \<noteq> 0 \<and> 0 < \<acute>level DO
        \<acute>level :== \<acute>level - 1;;
        \<acute>ret___struct_lookupPTSlot_ret_C :==
             ptBitsLeft_C_update (\<lambda>_. ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C - 9)
                                 \<acute>ret___struct_lookupPTSlot_ret_C;;
         \<acute>pt :== CALL getPPtrFromHWPTE(ptSlot_C \<acute>ret___struct_lookupPTSlot_ret_C);;
         ptSlot_upd;;
         \<acute>ret__unsigned_long :== CALL isPTEPageTable(ptSlot_C \<acute>ret___struct_lookupPTSlot_ret_C)
      OD;;
      return_C ret__struct_lookupPTSlot_ret_C_'_update ret___struct_lookupPTSlot_ret_C_')"  *)
proof (induct level arbitrary: pt)
  note unat_and_mask_le_ptTrans[simp] neq_0_unat[simp]

  (* FIXME AARCH64 these need to be re-done depending on what's needed below
  have misc_simps[simp]:
    "pageBits = pt_bits"
    "of_nat pageBits = of_nat pt_bits"
    "pt_bits - 3 = ptTranslationBits"
    "unat (of_nat pt_bits::machine_word) = pt_bits"
    "\<And>x::machine_word. x * 8 = x << pte_bits"
    "0x1FF = (mask ptTranslationBits :: machine_word)"
    by (auto simp: bit_simps mask_def shiftl_t2n)
  *)

  case 0
  show ?case
    apply (simp only: ptSlot_upd_def lookupPTSlotFromLevel.simps(1))
    apply (cinitlift pt_' vptr_', simp only:)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_move_array_assertion_vspace)
     apply (rule ccorres_symb_exec_r2)
       apply (rule ccorres_symb_exec_r2)
         apply (simp add: whileAnno_def)
         apply (rule ccorres_expand_while_iff_Seq[THEN iffD1])
         sorry (* FIXME AARCH64
         apply (rule ccorres_cond_false[where R="\<top>" and
                       R'="\<lbrace> \<acute>level = 0  \<and>
                             ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C = of_nat ptBits \<and>
                             ptSlot_C \<acute>ret___struct_lookupPTSlot_ret_C =
                             pte_Ptr pt +\<^sub>p uint ((vptr >> ptBits) && mask ptTranslationBits) \<rbrace>"])
         apply (rule ccorres_guard_imp)
           apply (rule ccorres_return_C)
             apply clarsimp
            apply clarsimp
           apply clarsimp
          apply (rule TrueI)
         apply (clarsimp simp: bit_simps pt_slot_offset_def pt_index_def pt_bits_left_def shiftl_t2n)
        apply vcg
       apply clarsimp
       apply (vcg spec=modifies)
      apply clarsimp
      apply vcg
     apply (vcg spec=modifies)
    apply clarsimp
    apply (drule pte_at'_ptSlotIndex[where level=0 and vptr=vptr])
    apply (clarsimp simp: pt_slot_offset_def pt_index_def pt_bits_left_def c_guard_abs_pte)
    apply (clarsimp simp: bit_simps)
    done *)

  case (Suc level)
  (* FIXME AARCH64 these need to be re-done depending on what's needed below
  have [simp]:
    "Suc level \<le> maxPTLevel \<Longrightarrow>
     unat (of_nat ptTranslationBits +
           of_nat ptTranslationBits * of_nat level +
           of_nat pt_bits :: machine_word) =
     ptTranslationBits + ptTranslationBits * level + pt_bits"
    by (simp add: bit_simps word_less_nat_alt maxPTLevel_def unat_word_ariths unat_of_nat_eq)
  *)

  show ?case
    sorry (* FIXME AARCH64
    apply (simp only: lookupPTSlotFromLevel.simps)
    apply (subst ptSlot_upd_def)
    \<comment> \<open>cinitlift will not fully eliminate pt and vptr,
        so we double the precondition to remember the connection\<close>
    apply (rule ccorres_guard_imp[where Q=Q and A=Q and
                                        Q'="A' \<inter> \<lbrace>\<acute>pt = pte_Ptr pt\<rbrace> \<inter> \<lbrace>\<acute>vptr = vptr\<rbrace>" and
                                        A'=A' for Q A']; simp)
    apply (cinitlift pt_' vptr_', simp only:) \<comment> \<open>Warns about ptSlot_upd, which is fine\<close>
    apply (rename_tac vptrC ptC)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_gen_asm[where P="Suc level \<le> maxPTLevel"])
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_move_array_assertion_pt)
     apply (rule ccorres_symb_exec_r2)
       apply (rule_tac G'="\<lbrace> ptSlot_C \<acute>ret___struct_lookupPTSlot_ret_C =
                                pte_Ptr (ptSlotIndex (Suc level) pt  vptr) \<and>
                             ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C =
                                of_nat (ptBitsLeft (Suc level)) \<and>
                             \<acute>level = of_nat (Suc level) \<and>
                             \<acute>vptr = vptr \<and>
                             \<acute>pt = ptC \<and>
                             hrs_htd \<acute>t_hrs,c_guard \<Turnstile>\<^sub>t pte_Ptr (ptSlotIndex (Suc level) pt vptr)
                            \<rbrace>"
                       in ccorres_symb_exec_l')
          apply (rename_tac pte)
          apply (rule ccorres_add_return)
          apply (rule ccorres_guard_imp)
            apply (rule_tac xf'=ret__unsigned_long_' in ccorres_split_nothrow_call)
                   apply (rule_tac pte=pte in isPTEPageTable_corres)
                  apply simp
                 apply simp
                apply simp
               apply (simp only: ptSlot_upd_def)
               apply ceqv
              apply (rename_tac from_bl)
              apply (fold ptSlot_upd_def)
              apply (unfold whileAnno_def)[1]
              apply (rule ccorres_expand_while_iff_Seq[THEN iffD1])
              apply (rule_tac R="\<top>" and
                              R'="\<lbrace>\<acute>ret__unsigned_long = from_bl \<and> \<acute>level =  of_nat (Suc level)\<rbrace>"
                              in ccorres_cond_strong)
                apply (clarsimp simp: maxPTLevel_def word_less_nat_alt unat_word_ariths
                                      unat_of_nat_eq)
               apply (rule ccorres_rhs_assoc)+
               apply (rule ccorres_symb_exec_r2)
                 apply (rule ccorres_symb_exec_r2)
                   apply (rule ccorres_add_return)
                   apply (rule_tac xf'="pt_'" in ccorres_split_nothrow_call)
                          apply (rule_tac pte=pte in getPPtrFromHWPTE_corres)
                         apply simp
                        apply simp
                       apply simp
                      apply ceqv \<comment> \<open>Warns about ptSlot_upd, which is fine\<close>
                     apply (rule ccorres_checkPTAt)
                     apply simp
                     apply (rule ccorres_rhs_assoc2)+
                     apply (rule Suc[unfolded whileAnno_def])
                    apply simp
                    apply wp
                   apply simp
                   apply (vcg exspec=getPPtrFromHWPTE_spec')
                  apply vcg
                 apply (vcg spec=modifies)
                apply vcg
               apply (vcg spec=modifies)
              apply (rule ccorres_return_C; simp)
             apply simp
             apply wp
            prefer 2
            apply assumption
           prefer 4
           apply (wp hoare_drop_imps)
          apply simp
          apply (vcg exspec=isPTEPageTable_spec')
         apply clarsimp
         apply (clarsimp simp: ptBitsLeft_def bit_simps)
        apply (wpsimp simp: pteAtIndex_def)
       apply (wpsimp simp: pteAtIndex_def wp: empty_fail_getObject)
      apply vcg
     apply (vcg spec=modifies)
    apply clarsimp
    apply (drule pte_at'_ptSlotIndex[where vptr=vptr and level="Suc level"])
    apply (simp add: c_guard_abs_pte)
    apply (simp add: ptSlotIndex_def ptIndex_def ptBitsLeft_def)
    apply (simp add: bit_simps word_less_nat_alt maxPTLevel_def unat_word_ariths unat_of_nat_eq)
    done *)
qed

lemma lookupPTSlot_ccorres:
  "ccorres (\<lambda>(bitsLeft,ptSlot) cr. bitsLeft = unat (ptBitsLeft_C cr) \<and> ptSlot_C cr = Ptr ptSlot)
     ret__struct_lookupPTSlot_ret_C_'
     (page_table_at' VSRootPT_T pt)
     (\<lbrace>\<acute>vptr = vptr \<rbrace> \<inter> \<lbrace>\<acute>vspace = Ptr pt \<rbrace>)
     hs
     (lookupPTSlot pt vptr)
     (Call lookupPTSlot_'proc)"
  apply (cinit lift: vspace_')
   apply (rule ccorres_symb_exec_r2)
     apply (rule ccorres_symb_exec_r2)
       apply (rule ccorres_symb_exec_r2)
         apply (rule ccorres_rhs_assoc2)+
         apply (rule lookupPTSlotFromLevel_ccorres)
        apply vcg
       apply (vcg spec=modifies)
      apply vcg
     apply (vcg spec=modifies)
    apply vcg
   apply (vcg spec=modifies)
  apply (simp add: bit_simps maxPTLevel_def ptBitsLeft_def split: if_split)
  (* FIXME AARCH64 abstraction violation, we need to know \<not>config_ARM_PA_SIZE_BITS_40 here.
     Make a lemma similar to the one for numDomains where maxPTLevel is some automatically
     generated numeral, since the number of PT levels in C is a #define, hence a numeral *)
  apply (simp add: Kernel_Config.config_ARM_PA_SIZE_BITS_40_def)
  done

abbreviation
  "findVSpaceForASID_xf \<equiv>
     liftxf errstate findVSpaceForASID_ret_C.status_C
            findVSpaceForASID_ret_C.vspace_root_C
            ret__struct_findVSpaceForASID_ret_C_'"

lemma ccorres_pre_getObject_asidpool:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>asidpool. ko_at' asidpool p s \<longrightarrow> P asidpool s))
                  {s. \<forall> asidpool asidpool'. cslift s (ap_Ptr p) = Some asidpool' \<and> casid_pool_relation asidpool asidpool'
                           \<longrightarrow> s \<in> P' asidpool}
                          hs (getObject p >>= (\<lambda>rv :: asidpool. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wpsimp wp: getASID_wp empty_fail_getObject)+
  apply (erule cmap_relationE1 [OF rf_sr_cpspace_asidpool_relation],
         erule ko_at_projectKO_opt)
  apply simp
  done

lemma asid_wf_table_guard[unfolded asid_high_bits_def, simplified]:
  "asid_wf asid \<Longrightarrow> asid >> asid_low_bits < 2^asid_high_bits"
  apply (simp add: asid_wf_def)
  apply (simp add: mask_def asid_bits_def asid_low_bits_def asid_high_bits_def)
  apply word_bitwise
  done

lemma asidLowBits_guard0[simp]:
  "0 <=s Kernel_C.asidLowBits"
  by (simp add: Kernel_C.asidLowBits_def)

lemma asidLowBits_shift_guard[unfolded word_bits_def, simplified, simp]:
  "Kernel_C.asidLowBits <s of_nat word_bits"
  by (simp add: Kernel_C.asidLowBits_def word_bits_def)

lemma asidPool_table_guard[simplified, simp]:
  "p && 2^asid_low_bits - 1 < 2^LENGTH(asid_low_len)" for p :: machine_word
  apply (fold mask_2pm1)
  apply (rule le_less_trans)
  apply (rule word_and_mask_le_2pm1)
  apply (simp add: asid_low_bits_def)
  done

lemma findVSpaceForASID_ccorres:
  "ccorres
       (lookup_failure_rel \<currency> (\<lambda>pteptrc pteptr. pteptr = pte_Ptr pteptrc))
       findVSpaceForASID_xf
       (valid_arch_state' and (\<lambda>_. asid_wf asid))
       (\<lbrace>\<acute>asid___unsigned_long = asid\<rbrace>)
       []
       (findVSpaceForASID asid)
       (Call findVSpaceForASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid___unsigned_long_')
   sorry (* FIXME AARCH64 new: asid map
   apply (rule ccorres_assertE)+
   apply (rule ccorres_liftE_Seq)
   apply (simp add: liftME_def bindE_assoc)
   apply (rule ccorres_pre_gets_armKSASIDTable_ksArchState')
   apply (case_tac "asidTable (ucast (asid_high_bits_of (ucast asid)))")
    (* Case where the first look-up fails *)
    apply clarsimp
    apply (rule_tac P="valid_arch_state' and _" and P'=UNIV in ccorres_from_vcg_throws)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def bindE_def Nondet_Monad.lift_def
                          EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def
                          lookup_fault_lift_invalid_root asid_wf_table_guard)
    apply (frule rf_sr_asidTable_None[where asid=asid, THEN iffD2],
           simp add: asid_wf_eq_mask_eq, assumption, assumption)
    apply (solves \<open>simp\<close>)
   (* Case where the first look-up succeeds *)
   apply clarsimp
   apply (rule ccorres_liftE_Seq)
   apply (rule ccorres_guard_imp)
     apply (rule ccorres_pre_getObject_asidpool)
     apply (rename_tac asidPool)
     apply (case_tac "inv ASIDPool asidPool (asid && mask asid_low_bits) = Some 0")
      apply (solves \<open>clarsimp simp: ccorres_fail'\<close>)
     apply (rule_tac P="\<lambda>s. asidTable=armKSASIDTable (ksArchState s) \<and>
                            valid_arch_state' s \<and> asid_wf asid"
                 and P'="{s'. (\<exists>ap'. cslift s' (ap_Ptr (the (asidTable (ucast (asid_high_bits_of (ucast asid))))))
                                               = Some ap' \<and> casid_pool_relation asidPool ap')}"
                  in ccorres_from_vcg_throws_nofail)
     apply (rule allI, rule conseqPre, vcg)
     apply (simp add: asid_wf_table_guard)
     apply (clarsimp simp: ucast_asid_high_bits_is_shift)
     apply (frule_tac idx="asid >> asid_low_bits" in rf_asidTable, assumption,
                      simp add: leq_asid_bits_shift)
     apply (clarsimp simp: typ_heap_simps)
     apply (case_tac asidPool, clarsimp simp: inv_def)
     apply (simp add: casid_pool_relation_def)
     apply (case_tac ap', simp)
     apply (clarsimp simp: array_relation_def)
     apply (erule_tac x="asid && 2 ^ asid_low_bits - 1" in allE)
     apply (simp add: word_and_le1 mask_def option_to_ptr_def option_to_0_def asid_low_bits_of_p2m1_eq)
     apply (rename_tac "fun" array)
     apply (case_tac "fun (asid && 2 ^ asid_low_bits - 1)", clarsimp)
      apply (clarsimp simp: throwError_def return_def EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
      apply (solves \<open>simp add: lookup_fault_lift_invalid_root Kernel_C.asidLowBits_def\<close>)
     apply (clarsimp simp add: asid_low_bits_def asid_bits_def)
     apply (fastforce simp: returnOk_def return_def
                            checkPTAt_def in_monad stateAssert_def liftE_bindE
                            get_def bind_def assert_def fail_def
                      split: if_splits)
    apply simp+
  done *)

lemma ccorres_pre_gets_armKSGlobalUserVSpace_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. armKSGlobalUserVSpace (ksArchState s) = rv  \<longrightarrow> P rv s))
                  (P' (ptr_val armKSGlobalUserVSpace_Ptr))
                  hs (gets (armKSGlobalUserVSpace \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp[1]
      apply (rule gets_sp)
     apply (clarsimp simp: empty_fail_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (drule rf_sr_armKSGlobalUserVSpace)
  apply simp
  done

(* FIXME move *)
lemma ccorres_from_vcg_might_throw:
  "(\<forall>\<sigma>. Gamm \<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> sr} c
                 {s. \<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> sr \<and> r rv (xf s)},
                 {s. \<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> sr \<and> arrel rv (axf s)})
     \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf P P' (SKIP # hs) a c"
  apply (rule ccorresI')
  apply (drule_tac x=s in spec)
  apply (erule exec_handlers.cases, simp_all)
   apply clarsimp
   apply (erule exec_handlers.cases, simp_all)[1]
    apply (auto elim!: exec_Normal_elim_cases)[1]
   apply (drule(1) exec_abrupt[rotated])
    apply simp
   apply (clarsimp simp: unif_rrel_simps elim!: exec_Normal_elim_cases)
   apply fastforce
  apply (clarsimp simp: unif_rrel_simps)
  apply (drule hoare_sound)
  apply (clarsimp simp: cvalid_def HoarePartialDef.valid_def)
  apply fastforce
  done

end

context kernel_m begin

(* FIXME: move *)
lemma ccorres_h_t_valid_armKSGlobalUserVSpace:
  "ccorres r xf P P' hs f (f' ;; g') \<Longrightarrow>
   ccorres r xf P P' hs f (Guard C_Guard {s'. s' \<Turnstile>\<^sub>c armKSGlobalUserVSpace_Ptr} f';; g')"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_move_c_guards[where P = \<top>])
    apply clarsimp
    apply assumption
   apply simp
  by (clarsimp simp add: rf_sr_def cstate_relation_def Let_def)

(* MOVE copied from CSpace_RAB_C *)
lemma ccorres_gen_asm_state:
  assumes rl: "\<And>s. P s \<Longrightarrow> ccorres r xf G G' hs a c"
  shows "ccorres r xf (G and P) G' hs a c"
proof (rule ccorres_guard_imp2)
  show "ccorres r xf (G and (\<lambda>_. \<exists>s. P s)) G' hs a c"
    apply (rule ccorres_gen_asm)
    apply (erule exE)
    apply (erule rl)
    done
next
  fix s s'
  assume "(s, s') \<in> rf_sr" and "(G and P) s" and "s' \<in> G'"
  thus "(G and (\<lambda>_. \<exists>s. P s)) s \<and> s' \<in> G'"
    by fastforce
qed

(* FIXME shadows two other identical versions in other files *)
lemma ccorres_abstract_known:
  "\<lbrakk> \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' g (g' rv'); ccorres rvr xf P P' hs f (g' val) \<rbrakk>
     \<Longrightarrow> ccorres rvr xf P (P' \<inter> {s. xf' s = val}) hs f g"
  apply (rule ccorres_guard_imp2)
   apply (rule_tac xf'=xf' in ccorres_abstract)
    apply assumption
   apply (rule_tac P="rv' = val" in ccorres_gen_asm2)
   apply simp
  apply simp
  done

lemma isValidVTableRoot_def2:
  "isValidVTableRoot cap =
   (\<exists>pt asid vref. cap = ArchObjectCap (PageTableCap pt VSRootPT_T (Some (asid,vref))))"
  unfolding isValidVTableRoot_def
  by (auto simp: isVTableRoot_def
           split: capability.splits arch_capability.splits option.splits pt_type.splits)

lemma setVMRoot_ccorres:
  "ccorres dc xfdc
      (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' thread)
      ({s. tcb_' s = tcb_ptr_to_ctcb_ptr thread}) hs
      (setVMRoot thread) (Call setVMRoot_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: tcb_')
   apply (rule ccorres_move_array_assertion_tcb_ctes)
   apply (rule ccorres_move_c_guard_tcb_ctes)
   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv bit_simps asid_bits_def)
   apply (ctac, rename_tac vRootCap vRootCap')
     apply (rule ccorres_assert2)
     sorry (* FIXME AARCH64 missing spec rule for isValidNativeRoot
     apply (csymbr, rename_tac vRootTag)
     apply (simp add: cap_get_tag_isCap_ArchObject2)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (subst will_throw_and_catch)
       apply (simp split: capability.split arch_capability.split option.split)
       apply (fastforce simp: isCap_simps)
      apply (rule ccorres_pre_gets_riscvKSGlobalPT_ksArchState)
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_h_t_valid_riscvKSGlobalPT)
      apply csymbr
      apply ccorres_rewrite
      apply (subst bind_return_unit)
      apply (ctac (no_vcg) add: setVSpaceRoot_ccorres)
       apply (rule ccorres_return_void_C)
      apply (rule hoare_post_taut[where P=\<top>])
     apply (simp add: catch_def bindE_bind_linearise bind_assoc liftE_def)
     apply csymbr
     apply csymbr
     apply csymbr
     apply csymbr
     apply simp
     apply ((wpc; (solves \<open>clarsimp simp: isCap_simps isValidVTableRoot_def\<close>)?), simp)+
     apply (simp add: catch_def bindE_bind_linearise bind_assoc liftE_def)
     apply (rule_tac f'=lookup_failure_rel
                 and r'="\<lambda>pte_ptr pte_ptr'. pte_ptr' = pte_Ptr pte_ptr"
                 and xf'=find_ret_'
              in ccorres_split_nothrow_case_sum)
          apply (ctac add: findVSpaceForASID_ccorres)
         apply ceqv
        apply (rename_tac vspace vspace')
        apply (rule_tac P="capPTBasePtr_CL (cap_page_table_cap_lift vRootCap')
                              = capPTBasePtr (capCap vRootCap)"
                     in ccorres_gen_asm2)
        apply simp
        apply (rule ccorres_Cond_rhs_Seq)
         apply (simp add: whenE_def throwError_def, ccorres_rewrite)
         apply (rule ccorres_rhs_assoc)
         apply (rule ccorres_h_t_valid_riscvKSGlobalPT)
         apply csymbr
         apply (rule ccorres_pre_gets_riscvKSGlobalPT_ksArchState)
         apply (rule ccorres_add_return2)
         apply (ctac (no_vcg) add: setVSpaceRoot_ccorres)
          apply (rule ccorres_return_void_C)
         apply (rule hoare_post_taut[where P=\<top>])
        apply (simp add: whenE_def returnOk_def)
        apply (csymbr)
        apply (ctac (no_vcg) add: setVSpaceRoot_ccorres)
       apply (rule ccorres_cond_true_seq, simp, ccorres_rewrite)
       apply (rule ccorres_rhs_assoc)
       apply (rule ccorres_h_t_valid_riscvKSGlobalPT)
       apply csymbr
       apply (rule ccorres_pre_gets_riscvKSGlobalPT_ksArchState)
       apply (rule ccorres_add_return2)
       apply (ctac (no_vcg) add: setVSpaceRoot_ccorres)
        apply (rule ccorres_return_void_C)
       apply (rule hoare_post_taut[where P=\<top>])
      apply (simp, rule wp_post_tautE)
     apply clarsimp
     apply (vcg)
    apply (simp add: isCap_simps)
    apply (wpsimp wp: getSlotCap_wp)
   apply vcg
  apply (clarsimp simp: Collect_const_mem)
  apply (rule conjI)
   apply (frule cte_at_tcb_at_32', drule cte_at_cte_wp_atD)
   apply (clarsimp simp: cte_level_bits_def tcbVTableSlot_def)
   apply (rule_tac x="cteCap cte" in exI)
   apply (rule conjI, erule cte_wp_at_weakenE', simp)
   apply (clarsimp simp: invs_cicd_no_0_obj' invs_cicd_arch_state' isCap_simps)
   apply (frule cte_wp_at_valid_objs_valid_cap'; clarsimp simp: invs_cicd_valid_objs')
   apply (clarsimp simp: valid_cap'_def wellformed_mapdata'_def isValidVTableRoot_def2)
  apply (clarsimp simp: tcb_cnode_index_defs cte_level_bits_def tcbVTableSlot_def)
  apply (clarsimp simp: isCap_simps isValidVTableRoot_def2)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject2)
  by (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric]
                     cap_lift_page_table_cap cap_to_H_def
                     cap_page_table_cap_lift_def isCap_simps isZombieTCB_C_def Let_def
              elim!: ccap_relationE
              split: if_split_asm cap_CL.splits) *)

lemma ccorres_seq_IF_False:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (IF False THEN x ELSE y FI ;; c) = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (y ;; c)"
  by simp

(* FIXME AARCH64: needed? *)
lemma ptrFromPAddr_mask6_simp[simp]:
  "ptrFromPAddr ps && mask 6 = ps && mask 6"
  unfolding ptrFromPAddr_def pptrBase_def pptrBaseOffset_def AARCH64.pptrBase_def canonical_bit_def
             paddrBase_def
  by (subst add.commute, subst mask_add_aligned ; simp add: is_aligned_def)

(* FIXME: move *)
lemma register_from_H_bound[simp]:
  "unat (register_from_H v) < 37"
  by (cases v, simp_all add: "StrictC'_register_defs")

(* FIXME: move *)
lemma register_from_H_inj:
  "inj register_from_H"
  apply (rule inj_onI)
  apply (case_tac x)
  by (case_tac y, simp_all add: "StrictC'_register_defs")+

(* FIXME: move *)
lemmas register_from_H_eq_iff[simp]
    = inj_on_eq_iff [OF register_from_H_inj, simplified]

lemma setRegister_ccorres:
  "ccorres dc xfdc \<top>
       (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>reg = register_from_H reg\<rbrace>
        \<inter> {s. w_' s = val}) []
       (asUser thread (setRegister reg val))
       (Call setRegister_'proc)"
  apply (cinit' lift: thread_' reg_' w_')
   apply (simp add: asUser_def split_def)
   apply (rule ccorres_pre_threadGet)
   apply (rule ccorres_Guard)
   apply (simp add: setRegister_def simpler_modify_def exec_select_f_singleton)
   apply (rule_tac P="\<lambda>tcb. (atcbContextGet o tcbArch) tcb = uc"
                in threadSet_ccorres_lemma2)
    apply vcg
   apply (clarsimp simp: setRegister_def HaskellLib_H.runState_def
                         simpler_modify_def typ_heap_simps)
   apply (subst StateSpace.state.fold_congs[OF refl refl])
    apply (rule globals.fold_congs[OF refl refl])
    apply (rule heap_update_field_hrs, simp)
     apply (fastforce intro: typ_heap_simps)
    apply simp
   apply (erule(1) rf_sr_tcb_update_no_queue2,
               (simp add: typ_heap_simps')+)
    apply (rule ball_tcb_cte_casesI, simp+)
   apply (clarsimp simp: ctcb_relation_def ccontext_relation_def cregs_relation_def
                         atcbContextSet_def atcbContextGet_def
                         carch_tcb_relation_def
                  split: if_split)
  apply (clarsimp simp: Collect_const_mem register_from_H_sless
                        register_from_H_less)
  apply (auto intro: typ_heap_simps elim: obj_at'_weakenE)
  done

lemma msgRegisters_ccorres:
  "n < unat n_msgRegisters \<Longrightarrow>
  register_from_H (AARCH64_H.msgRegisters ! n) = (index kernel_all_substitute.msgRegisters n)"
  apply (simp add: kernel_all_substitute.msgRegisters_def msgRegisters_unfold fupdate_def)
  apply (simp add: Arrays.update_def n_msgRegisters_def nth_Cons' split: if_split)
  done

(* usually when we call setMR directly, we mean to only set a registers, which will
   fit in actual registers *)
lemma setMR_as_setRegister_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = of_nat offset + 1) ret__unsigned_'
      (tcb_at' thread and K (TCB_H.msgRegisters ! offset = reg \<and> offset < length msgRegisters))
      (\<lbrace>\<acute>reg___unsigned_long = val\<rbrace>
       \<inter> \<lbrace>\<acute>offset = of_nat offset\<rbrace>
       \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
    (asUser thread (setRegister reg val))
    (Call setMR_'proc)"
  apply (rule ccorres_grab_asm)
  apply (cinit' lift:  reg___unsigned_long_' offset_' receiver_')
   apply (clarsimp simp: n_msgRegisters_def length_of_msgRegisters)
   apply (rule ccorres_cond_false)
   apply (rule ccorres_move_const_guards)
   apply (rule ccorres_add_return2)
   apply (ctac add: setRegister_ccorres)
     apply (rule ccorres_from_vcg_throws[where P'=UNIV and P=\<top>])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply (rule hoare_post_taut[of \<top>])
   apply (vcg exspec=setRegister_modifies)
  apply (clarsimp simp: n_msgRegisters_def length_of_msgRegisters not_le conj_commute)
  apply (subst msgRegisters_ccorres[symmetric])
   apply (clarsimp simp: n_msgRegisters_def length_of_msgRegisters unat_of_nat_eq)
  apply (clarsimp simp: word_less_nat_alt word_le_nat_alt unat_of_nat_eq not_le[symmetric])
  done

lemma wordFromMessageInfo_spec:
  defines "mil s \<equiv> seL4_MessageInfo_lift (mi_' s)"
  shows "\<forall>s. \<Gamma> \<turnstile> {s} Call wordFromMessageInfo_'proc
                  \<lbrace>\<acute>ret__unsigned_long = (label_CL (mil s) << 12)
                                      || (capsUnwrapped_CL (mil s) << 9)
                                      || (extraCaps_CL (mil s) << 7)
                                      || length_CL (mil s)\<rbrace>"
  unfolding mil_def
  apply vcg
  apply (simp del: scast_id add: seL4_MessageInfo_lift_def mask_shift_simps)
  apply word_bitwise
  done

lemma wordFromMessageInfo_ccorres [corres]:
  "ccorres (=) ret__unsigned_long_'
           \<top> {s. mi = message_info_to_H (mi_' s)} []
           (return (wordFromMessageInfo mi)) (Call wordFromMessageInfo_'proc)"
  apply (rule ccorres_from_spec_modifies [where P = \<top>, simplified])
     apply (rule wordFromMessageInfo_spec)
    apply (rule wordFromMessageInfo_modifies)
   apply simp
  apply clarsimp
  apply (simp add: return_def wordFromMessageInfo_def Let_def message_info_to_H_def
                   msgLengthBits_def msgExtraCapBits_def
                   msgMaxExtraCaps_def shiftL_nat word_bw_assocs word_bw_comms word_bw_lcs)
  done

(* FIXME move *)
lemma register_from_H_eq:
  "(r = r') = (register_from_H r = register_from_H r')"
  apply (case_tac r, simp_all add: C_register_defs)
                   by (case_tac r', simp_all add: C_register_defs)+

lemma setMessageInfo_ccorres:
  "ccorres dc xfdc (tcb_at' thread)
           (\<lbrace>mi = message_info_to_H mi'\<rbrace>) hs
           (setMessageInfo thread mi)
           (\<acute>ret__unsigned_long :== CALL wordFromMessageInfo(mi');;
            CALL setRegister(tcb_ptr_to_ctcb_ptr thread,
                             scast Kernel_C.msgInfoRegister,
                             \<acute>ret__unsigned_long))"
  unfolding setMessageInfo_def
  apply (rule ccorres_guard_imp2)
   apply ctac
     apply simp
     apply (ctac add: setRegister_ccorres)
    apply wp
   apply vcg
  apply (simp add: AARCH64_H.msgInfoRegister_def AARCH64.msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def C_register_defs)
  done

lemma ccorres_pre_getObject_pte:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>pte. ko_at' pte p s \<longrightarrow> P pte s))
                  {s. \<forall>pte pte'. cslift s (pte_Ptr p) = Some pte' \<and> cpte_relation pte pte'
                           \<longrightarrow> s \<in> P' pte}
                          hs (getObject p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wp getPTE_wp empty_fail_getObject | simp)+
  apply clarsimp
  apply (erule cmap_relationE1 [OF rf_sr_cpte_relation],
         erule ko_at_projectKO_opt)
  apply simp
  done

lemmas unfold_checkMapping_return
    = from_bool_0[where 'a=machine_word_len, folded exception_defs]
      to_bool_def

(* FIXME AARCH64 this rule was a helper for unmapPage_ccorres, but now doesn't match, need to
     understand the changed conditions in the unmapPage_ccorres proof to re-state this lemma
lemma checkMappingPPtr_pte_ccorres:
  assumes pre:
    "\<And>pte \<sigma>. \<Gamma> \<turnstile> {s. True \<and> (\<exists>pte'. cslift s (pte_Ptr pte_ptr) = Some pte' \<and> cpte_relation pte pte')
                            \<and> (\<sigma>, s) \<in> rf_sr}
           call1 ;; Cond S return_void_C Skip
       {s. (\<sigma>, s) \<in> rf_sr \<and> (isPagePTE pte) \<and> pteBaseAddress pte << ptBits NormalPT_T = addrFromPPtr pptr},
       {s. (\<sigma>, s) \<in> rf_sr \<and> \<not> ((isPagePTE pte) \<and> pteBaseAddress pte << ptBits NormalPT_T = addrFromPPtr pptr)}"
  shows
  "ccorres_underlying rf_sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel dc) xfdc
       \<top> UNIV (SKIP # hs)
     (doE
         pte \<leftarrow> withoutFailure $ getObject pte_ptr;
         checkMappingPPtr pptr pte
      odE)
     (call1;; Cond S return_void_C Skip)"
  apply (simp add: checkMappingPPtr_def liftE_bindE)
  apply (rule ccorres_symb_exec_l[where Q'="\<lambda>_. UNIV", OF _ _ getObject_ko_at, simplified])
      apply (rule stronger_ccorres_guard_imp)
        apply (rule ccorres_from_vcg_might_throw[where P=\<top>])
        apply (rule allI)
        apply (rule conseqPost, rule conseqPre, rule_tac \<sigma>1=\<sigma> and pte1=rv in pre)
          apply clarsimp
          apply (erule CollectE, assumption)
         apply (clarsimp simp: Bex_def isPagePTE_def in_monad)

         apply (clarsimp simp: Bex_def isPagePTE_def in_monad split: pte.splits)
         apply (fastforce simp: Bex_def isPagePTE_def in_monad split: pte.splits)
       apply (wp empty_fail_getObject | simp)+
      apply (erule cmap_relationE1[OF rf_sr_cpte_relation])
       apply (erule ko_at_projectKO_opt)
      apply simp
     apply (wp empty_fail_getObject | simp add: objBits_simps bit_simps)+
  done *)

lemma ccorres_return_void_C':
  "ccorres_underlying rf_sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel dc) xfdc (\<lambda>_. True) UNIV (SKIP # hs) (return (Inl rv)) return_void_C"
  apply (rule ccorres_from_vcg_throws)
  apply (simp add: return_def)
  apply (rule allI, rule conseqPre, vcg)
  apply auto
  done

lemma findVSpaceForASID_page_table_at'_simple[wp]:
  notes checkPTAt_inv[wp del]
  shows "\<lbrace>\<top>\<rbrace> findVSpaceForASID asid \<lbrace> page_table_at' VSRootPT_T \<rbrace>,-"
  apply (simp add: findVSpaceForASID_def)
   apply (wpsimp wp: getASID_wp simp: checkPTAt_def)
  sorry (* FIXME AARCH64 the wp rule is probably too weak (only gives us existence of pt_t
  done *)

lemmas ccorres_name_ksCurThread = ccorres_pre_getCurThread[where f="\<lambda>_. f'" for f',
    unfolded getCurThread_def, simplified gets_bind_ign]

lemma of_nat_pageBitsForSize:
  "unat x = pageBitsForSize sz \<Longrightarrow> x = of_nat (pageBitsForSize sz)" for x::machine_word
  by (drule sym, simp)

lemma checkMappingPPtr_def2:
  "checkMappingPPtr p pte =
   (if isPagePTE pte \<and> ptrFromPAddr (pteBaseAddress pte) = p
    then returnOk()
    else throw InvalidRoot)"
  unfolding checkMappingPPtr_def
  apply (cases pte; simp add: isPagePTE_def unlessE_def cong: if_cong split: if_splits)
  apply auto
  done

(* FIXME AARCH64 is this necessary, or can we work with the bitfield gen spec rule that only gives
   the tag? *)
lemma pte_pte_invalid_new_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       \<acute>ret__struct_pte_C :== PROC pte_pte_invalid_new()
       \<lbrace> pte_lift \<acute>ret__struct_pte_C = Some Pte_pte_invalid \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: pte_pte_invalid_new_body_def pte_pte_invalid_new_impl
                        pte_lift_def Let_def pte_get_tag_def pte_tag_defs)
  done

lemma unmapPage_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>_. asid_wf asid))
      (\<lbrace> framesize_to_H \<acute>page_size = sz \<and> \<acute>page_size < 3 \<rbrace> \<inter>
       \<lbrace> \<acute>asid___unsigned_long = asid \<rbrace> \<inter> \<lbrace> \<acute>vptr = vptr \<rbrace> \<inter> \<lbrace> \<acute>pptr___unsigned_long = pptr \<rbrace>)
      hs
      (unmapPage sz asid vptr pptr) (Call unmapPage_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: page_size_' asid___unsigned_long_' vptr_' pptr___unsigned_long_')
   apply (simp add: ignoreFailure_liftM)
   apply (ctac add: findVSpaceForASID_ccorres)
      apply (rename_tac vspace find_ret)
      apply (rule ccorres_liftE_Seq)
      apply (simp add: Collect_False del: Collect_const)
      apply (ctac add: lookupPTSlot_ccorres)
        apply csymbr
        apply (simp (no_asm) add: split_def del: Collect_const)
        apply (rule ccorres_split_unless_throwError_cond[where Q=\<top> and Q'=\<top>])
           apply (clarsimp simp: of_nat_pageBitsForSize split: if_split)
          apply (simp add: throwError_def)
          apply (rule ccorres_return_void_C)
         apply simp
         apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
         apply (subst bindE_assoc[symmetric])
         apply (rule ccorres_splitE_novcg)
             apply (simp only: inl_rrel_inl_rrel)
             sorry (* FIXME AARCH64 conditions changed somewhere above, the code differs from the
                        third early return clause (also features cleanByVA_PoU, invalidateTLBByASIDVA
             apply (rule checkMappingPPtr_pte_ccorres[simplified])
             apply (rule conseqPre, vcg exspec=isPTEPageTable_spec')
             apply (clarsimp simp: cpte_relation_def Let_def pte_lift_def isPagePTE_def
                                   typ_heap_simps isPageTablePTE_def bit_simps
                            split: if_split_asm pte.split_asm)
            apply (rule ceqv_refl)
           apply (simp add: unfold_checkMapping_return liftE_bindE
                       del: Collect_const)
           apply csymbr
           apply (rule ccorres_split_nothrow_novcg)
               apply (simp add: ptr_add_assertion_def split_def)
               apply ccorres_rewrite
               apply (rule storePTE_Basic_ccorres)
               apply (simp add: cpte_relation_def Let_def)
              apply ceqv
             apply (rule ccorres_liftE)
             apply (rule ccorres_call)
                apply (rule ccorres_rel_imp)
                 apply (rule sfence_ccorres, simp, simp)
              apply (simp add: xfdc_def)
             apply simp
            apply wp
           apply (simp add: guard_is_UNIV_def)
          apply wp
         apply (simp add: guard_is_UNIV_def)
        apply vcg
       apply wpsimp
      apply (vcg exspec=lookupPTSlot_modifies)
     apply ccorres_rewrite
     apply (simp add: throwError_def)
     apply (rule ccorres_return_void_C)
    apply wp
   apply (vcg exspec=findVSpaceForASID_modifies)
  apply clarsimp
  done *)

(* FIXME: move *)
lemma cap_to_H_PageCap_tag:
  "\<lbrakk> cap_to_H cap = ArchObjectCap (FrameCap p R sz d A);
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_frame_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     by (simp_all add: Let_def cap_lift_def split_def split: if_splits)

lemma ccap_relation_mapped_asid_0:
  "\<lbrakk>ccap_relation (ArchObjectCap (FrameCap d v0 v1 v2 v3)) cap\<rbrakk>
  \<Longrightarrow> (capFMappedASID_CL (cap_frame_cap_lift cap) \<noteq> 0 \<longrightarrow> v3 \<noteq> None) \<and>
      (capFMappedASID_CL (cap_frame_cap_lift cap) = 0 \<longrightarrow> v3 = None)"
  apply (frule cap_get_tag_PageCap_frame)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply simp
  done

lemma framesize_from_H_bounded:
  "framesize_from_H x < 3"
  by (clarsimp simp: framesize_from_H_def framesize_defs
               split: vmpage_size.split)

lemma cap_to_H_Frame_unfold:
  "cap_to_H capC = ArchObjectCap (FrameCap p R sz d m) \<Longrightarrow>
   \<exists>asid_C sz_C vmrights_C device_C mappedAddr_C.
   capC = Cap_frame_cap \<lparr>capFMappedASID_CL = asid_C, capFBasePtr_CL = p, capFSize_CL = sz_C,
           capFMappedAddress_CL = mappedAddr_C, capFVMRights_CL = vmrights_C,
           capFIsDevice_CL = device_C \<rparr> \<and>
   sz = framesize_to_H sz_C \<and>
   d = to_bool device_C \<and>
   R = vmrights_to_H vmrights_C \<and>
   m = (if asid_C = 0 then None else Some (asid_C, mappedAddr_C))"
  supply if_cong[cong]
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits)
   apply (simp split: if_split_asm)
  apply (rename_tac fcap, case_tac fcap, simp)
  done

(* FIXME AARCH64 change C code in this function to use a get/set pattern for the cap instead of
   going via cap_frame_cap_ptr_set_capFMappedASID etc *)
lemma performPageInvocationUnmap_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) o cteCap) ctSlot  and K (isFrameCap cap))
       (\<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       hs
       (liftE (performPageInvocation (PageUnmap cap ctSlot)))
       (Call performPageInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp K_def)
  apply (rule ccorres_gen_asm)
  apply (clarsimp simp: isCap_simps)
  apply (cinit' lift: cap_' ctSlot_' simp: performPageInvocation_def)
   apply (rename_tac ctSlotC capC)
   apply csymbr
   apply (simp only: )
   apply (frule ccap_relation_mapped_asid_0)
   apply (rule_tac R'="\<lbrace> cap_get_tag capC = SCAST(32 signed \<rightarrow> 64) cap_frame_cap \<rbrace>"
                   in ccorres_split_nothrow)
       apply (rule ccorres_Cond_rhs)
        (* ASID present, unmap *)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply clarsimp
        apply (frule cap_get_tag_isCap_unfolded_H_cap)
(*        apply (clarsimp simp: asidInvalid_def) *)
        apply (rule ccorres_call[where xf'=xfdc])
           apply datatype_schem
           apply (rule unmapPage_ccorres)
          apply simp
         apply simp
        apply simp
       apply (simp add: asidInvalid_def)
       apply (rule ccorres_return_Skip)
      apply ceqv
     apply (simp add: liftM_def)
     apply (rule_tac Q="\<lambda>slotCap.  cte_wp_at' ((=) slotCap o cteCap) ctSlot and (\<lambda>_. isArchFrameCap slotCap)" and
                     Q'="\<lambda>slotCap slotCap_C. UNIV"
                     in ccorres_split_nothrow)
         sorry (* FIXME AARCH64 once again expecting Basic, but have a CALL
         apply (ctac add: getSlotCap_h_val_ccorres)
        apply ceqv
       apply (rename_tac slotCap slotCap_C)
       apply (rule ccorres_gen_asm)
       apply (rule ccorres_guard_imp)
         apply csymbr
         apply csymbr
         apply (rule ccorres_move_c_guard_cte)
         apply (ctac add: ccorres_updateCap)
           apply (rule ccorres_rel_imp[where xf'=ret__unsigned_long_' and
                                             r'="\<lambda>_ x. x = SCAST(32 signed \<rightarrow> 64) EXCEPTION_NONE"])
            apply (rule ccorres_return_C; simp)
           apply simp
          apply wp
         apply vcg
        apply (clarsimp simp: cte_wp_at_ctes_of)
       apply (clarsimp simp: cap_get_tag_isCap asidInvalid_def)
       apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 c_valid_cap_def)
       apply (clarsimp simp: cap_frame_cap_lift)
       apply (rename_tac slotCap_CL)
       apply (clarsimp simp: isCap_simps)
       apply (simp (no_asm) add: cap_to_H_def cap_frame_cap_lift_def)
       apply simp
       apply (drule cap_to_H_Frame_unfold)+
       apply (clarsimp simp: cl_valid_cap_def)
      apply wp
      apply (wpsimp simp: getSlotCap_def wp: getCTE_wp)
     apply vcg
    apply simp
    apply (wpsimp wp: hoare_drop_imps hoare_vcg_ex_lift unmapPage_cte_wp_at')
   apply (rule conseqPre, vcg exspec=unmapPage_modifies)
   apply clarsimp
  apply (clarsimp simp: asidInvalid_def cap_get_tag_isCap cte_wp_at_ctes_of)
  apply (rename_tac p R sz d m cap' s s' cte)
  apply (frule ctes_of_valid', fastforce)
  apply (drule_tac t="cteCap cte" in sym)
  apply (clarsimp simp: valid_cap'_def)
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (drule cap_to_H_Frame_unfold)
  apply (clarsimp simp: cap_frame_cap_lift_def
                        c_valid_cap_def cl_valid_cap_def wellformed_mapdata'_def)
  done *)

(* FIXME AARCH64 incorporate whichever of these are needed (from RISCV64 and ARM_HYP), remove rest

lemma RISCVGetWriteFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace> Call ArmGetWriteFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned_long = writable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  supply if_cong[cong]
  apply vcg
  apply (simp add: vmrights_to_H_def writable_from_vm_rights_def Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply (drule word_less_cases, auto)+
  done

lemma RISCVGetReadFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace> Call RISCVGetReadFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned_long = readable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  supply if_cong[cong]
  apply vcg
  apply (simp add: vmrights_to_H_def readable_from_vm_rights_def Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply (drule word_less_cases, auto)+
  done

lemma writable_from_vm_rights_mask:
  "(writable_from_vm_rights R) && 1 = (writable_from_vm_rights R :: machine_word)"
  by (simp add: writable_from_vm_rights_def split: vmrights.splits)

lemma readable_from_vm_rights_mask:
  "(readable_from_vm_rights R) && 1 = (readable_from_vm_rights R :: machine_word)"
  by (simp add: readable_from_vm_rights_def split: vmrights.splits)

lemma user_from_vm_rights_mask:
  "user_from_vm_rights R && 1 = (user_from_vm_rights R :: machine_word)"
  by (simp add: user_from_vm_rights_def split: vmrights.splits)

lemma HAPFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4\<rbrace> Call HAPFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned_long = hap_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  apply vcg
  apply (simp add: vmrights_to_H_def hap_from_vm_rights_def
                   Kernel_C.VMNoAccess_def Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply clarsimp
  apply (drule word_less_cases, auto)+
  done

lemma hap_from_vm_rights_mask:
  "hap_from_vm_rights R && 3 = (hap_from_vm_rights R :: word32)"
  by (simp add: hap_from_vm_rights_def split: vmrights.splits)

*)

lemma APFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 2 \<rbrace> Call APFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned_long = ap_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  apply vcg
  apply (simp add: vmrights_to_H_def ap_from_vm_rights_def
                   Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply clarsimp
  apply (drule word_less_cases, auto)+
  done

lemma armExecuteNever_CL_limit:
  "armExecuteNever_CL (vm_attributes_lift attrs) \<le> 1"
  by (simp add: vm_attributes_lift_def word_and_le1)

lemmas vm_attributes_helpers =
  armExecuteNever_CL_limit word_le_1_and_idem from_to_bool_le_1_idem

(* FIXME AARCH64 rename/cleanup/generalise to not mention 12, maybe also not 36 (these are from
   the bitfield generator *)
lemma makeUserPagePTE_spec_helper:
  "\<lbrakk> canonical_address p; is_aligned p pageBits \<rbrakk> \<Longrightarrow> p && (mask 36 << 12) = p"
  apply (simp add: word_and_mask_shiftl pageBits_def canonical_address_range canonical_bit_def)
  apply word_eqI
  apply (clarsimp simp: le_def)
  apply (rule iffI, clarsimp)
  apply (subst add_diff_inverse_nat; fastforce)
  done

lemma makeUserPagePTE_spec:
  "\<forall>s. \<Gamma> \<turnstile>
   \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 2 \<and> canonical_address \<acute>paddr \<and> is_aligned \<acute>paddr pageBits \<rbrace>
   Call makeUserPagePTE_'proc
   \<lbrace> let uxn = uxn_from_vmattributes (vm_attributes_to_H \<^bsup>s\<^esup>attributes);
         ap = ap_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights);
         attridx = attridx_from_vmattributes (vm_attributes_to_H \<^bsup>s\<^esup>attributes);
         nG = 0 \<comment> \<open>hyp 0, non-hyp 1\<close>
     in
       if \<^bsup>s\<^esup>page_size = scast Kernel_C.ARMSmallPage
       then
         pte_lift \<acute>ret__struct_pte_C = Some (Pte_pte_4k_page \<lparr>
           pte_pte_4k_page_CL.UXN_CL = uxn,
           page_base_address_CL = \<^bsup>s\<^esup>paddr,
           nG_CL = nG,
           AF_CL = 1,
           SH_CL = 0,
           AP_CL = ap,
           AttrIndx_CL = attridx
           \<rparr>)
       else
         pte_lift \<acute>ret__struct_pte_C = Some (Pte_pte_page \<lparr>
           pte_pte_page_CL.UXN_CL = uxn,
           page_base_address_CL = \<^bsup>s\<^esup>paddr,
           nG_CL = nG,
           AF_CL = 1,
           SH_CL = 0,
           AP_CL = ap,
           AttrIndx_CL = attridx
           \<rparr>) \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: Let_def)
  (* these simps don't want to be combined *)
  apply (clarsimp simp: pte_pte_page_lift pte_pte_4k_page_lift makeUserPagePTE_spec_helper)
  apply (clarsimp simp: uxn_from_vmattributes_def vm_attributes_to_H_def Let_def vm_attributes_helpers
                         attridx_from_vmattributes_def S2_NORMAL_def S2_DEVICE_nGnRnE_def mask_def
                         ap_from_vm_rights_def vmrights_to_H_def
                  split: if_split vmrights.split)
  apply (simp add: to_bool_def)
  done

lemma cap_to_H_PTCap:
  "cap_to_H cap = ArchObjectCap (PageTableCap p NormalPT_T asid) \<Longrightarrow>
   \<exists>cap_CL. cap = Cap_page_table_cap cap_CL \<and>
            to_bool (capPTIsMapped_CL cap_CL) = (asid \<noteq> None) \<and>
            (asid \<noteq> None \<longrightarrow> capPTMappedASID_CL cap_CL = fst (the asid) \<and>
                            capPTMappedAddress_CL cap_CL = snd (the asid)) \<and>
            cap_page_table_cap_CL.capPTBasePtr_CL cap_CL = p"
  by (auto simp add: cap_to_H_def Let_def split: cap_CL.splits if_splits)

(* FIXME AARCH64 might not be needed *)
lemma cap_to_H_VSCap:
  "cap_to_H cap = ArchObjectCap (PageTableCap p VSRootPT_T asid) \<Longrightarrow>
   \<exists>cap_CL. cap = Cap_vspace_cap cap_CL \<and>
            to_bool (capVSIsMapped_CL cap_CL) = (asid \<noteq> None) \<and>
            (asid \<noteq> None \<longrightarrow> capVSMappedASID_CL cap_CL = fst (the asid)) \<and>
            cap_vspace_cap_CL.capVSBasePtr_CL cap_CL = p"
  by (auto simp add: cap_to_H_def Let_def split: cap_CL.splits if_splits)

lemma cap_lift_PTCap_Base:
  "\<lbrakk> cap_to_H cap_cl = ArchObjectCap (PageTableCap p NormalPT_T asid);
     cap_lift cap_c = Some cap_cl \<rbrakk>
  \<Longrightarrow> p = cap_page_table_cap_CL.capPTBasePtr_CL (cap_page_table_cap_lift cap_c)"
  apply (simp add: cap_page_table_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  done

declare mask_Suc_0[simp]

(* FIXME: move *)
lemma setCTE_asidpool':
  "\<lbrace> ko_at' (ASIDPool pool) p \<rbrace> setCTE c p' \<lbrace>\<lambda>_. ko_at' (ASIDPool pool) p\<rbrace>"
  apply (clarsimp simp: setCTE_def)
  apply (simp add: setObject_def split_def)
  apply (rule hoare_seq_ext [OF _ hoare_gets_sp])
  apply (clarsimp simp: valid_def in_monad)
  apply (frule updateObject_type)
  apply (clarsimp simp: obj_at'_def)
  apply (rule conjI)
   apply (clarsimp simp: lookupAround2_char1)
   apply (clarsimp split: if_split)
   apply (case_tac obj', auto)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, auto)[1]
   apply (simp add: updateObject_cte)
   apply (clarsimp simp: updateObject_cte typeError_def magnitudeCheck_def in_monad
                   split: kernel_object.splits if_splits option.splits)
  apply (clarsimp simp: ps_clear_upd lookupAround2_char1)
  done

lemmas udpateCap_asidpool' = updateCap_ko_at_ap_inv'

(* FIXME: move *)
lemma asid_pool_at_rf_sr:
  "\<lbrakk>ko_at' (ASIDPool pool) p s; (s, s') \<in> rf_sr\<rbrakk> \<Longrightarrow>
  \<exists>pool'. cslift s' (ap_Ptr p) = Some pool' \<and>
          casid_pool_relation (ASIDPool pool) pool'"
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
  apply (erule (1) cmap_relation_ko_atE)
  apply clarsimp
  done

(* FIXME: move *)
lemma asid_pool_at_ko:
  "asid_pool_at' p s \<Longrightarrow> \<exists>pool. ko_at' (ASIDPool pool) p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  apply (case_tac ko, auto)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  apply (rename_tac asidpool)
  apply (case_tac asidpool, auto)[1]
  done

(* FIXME: move *)
lemma asid_pool_at_c_guard:
  "\<lbrakk>asid_pool_at' p s; (s, s') \<in> rf_sr\<rbrakk> \<Longrightarrow> c_guard (ap_Ptr p)"
  by (fastforce intro: typ_heap_simps dest!: asid_pool_at_ko asid_pool_at_rf_sr)

(* FIXME: move *)
lemma setObjectASID_Basic_ccorres:
  "ccorres dc xfdc \<top> {s. f s = p \<and> casid_pool_relation pool (asid_pool_C.asid_pool_C (pool' s))} hs
     (setObject p pool)
     ((Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (Ptr &(ap_Ptr (f s)\<rightarrow>[''array_C''])) (pool' s)))) s)))"
  apply (rule setObject_ccorres_helper)
    apply (simp_all add: objBits_simps pageBits_def)
  apply (rule conseqPre, vcg)
  apply (rule subsetI, clarsimp simp: Collect_const_mem)
  apply (rule cmap_relationE1, erule rf_sr_cpspace_asidpool_relation,
         erule ko_at_projectKO_opt)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def typ_heap_simps
                         update_asidpool_map_to_asidpools
                         update_asidpool_map_tos)
   apply (case_tac y')
   apply clarsimp
   apply (erule cmap_relation_updI,
          erule ko_at_projectKO_opt, simp+)
  apply (simp add: cready_queues_relation_def
                   carch_state_relation_def
                   cmachine_state_relation_def
                   Let_def typ_heap_simps
                   update_asidpool_map_tos)
  done

lemma getObject_ap_inv [wp]: "\<lbrace>P\<rbrace> (getObject addr :: asidpool kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule getObject_inv)
  apply simp
  apply (rule loadObject_default_inv)
  done

lemma getObject_ko_at_ap [wp]:
  "\<lbrace>\<top>\<rbrace> getObject p \<lbrace>\<lambda>rv::asidpool. ko_at' rv p\<rbrace>"
  by (rule getObject_ko_at | simp add: objBits_simps bit_simps)+

(* FIXME AARCH64 no pspace_canonical
lemma canonical_address_page_table_at':
  "\<lbrakk>page_table_at' p s; pspace_canonical' s\<rbrakk> \<Longrightarrow> canonical_address p"
  apply (clarsimp simp: page_table_at'_def)
  apply (drule_tac x=0 in spec, clarsimp simp: bit_simps typ_at_to_obj_at_arches)
  apply (erule (1) obj_at'_is_canonical)
  done  *)

(* FIXME AARCH64 assuming the only array use of page tables are root PTs (vspace)
   these might need to be renamed or gain comments to explain why it's only root PTs *)
lemma page_table_at'_array_assertion:
  assumes "(s,s') \<in> rf_sr"
  assumes "page_table_at' VSRootPT_T pt s"
  assumes "gsPTTypes (ksArchState s) pt = Some VSRootPT_T"
  assumes "n \<le> 2^(ptTranslationBits  VSRootPT_T)" "0 < n"
  shows "array_assertion (pte_Ptr pt) n (hrs_htd (t_hrs_' (globals s')))"
  using assms
  by (fastforce intro: array_assertion_abs_vspace[where x="\<lambda>_. (1::nat)", simplified, rule_format])

(* FIXME AARCH64 probably not needed for this arch, because no copy global mappings *)
lemma page_table_at'_array_assertion_weak[unfolded ptTranslationBits_def, simplified]:
  assumes "(s,s') \<in> rf_sr"
  assumes "page_table_at' VSRootPT_T pt s"
  assumes "gsPTTypes (ksArchState s) pt = Some VSRootPT_T"
  assumes "n < 2^(ptTranslationBits VSRootPT_T - 1)"
  shows "array_assertion (pte_Ptr pt) ((unat (2^(ptTranslationBits VSRootPT_T - 1) + of_nat n::machine_word)))
                         (hrs_htd (t_hrs_' (globals s')))"
  using assms
  sorry (* FIXME AARCH64 re-examine this lemma, it might no longer make sense with vspaces
  by (fastforce intro: page_table_at'_array_assertion
                simp: unat_add_simple ptTranslationBits_def word_bits_def unat_of_nat) *)

(* FIXME AARCH64 probably not needed for this arch, because no copy global mappings *)
lemma page_table_at'_array_assertion_strong[unfolded ptTranslationBits_def, simplified]:
  assumes "(s,s') \<in> rf_sr"
  assumes "page_table_at' VSRootPT_T pt s"
  assumes "gsPTTypes (ksArchState s) pt = Some VSRootPT_T"
  assumes "n < 2^(ptTranslationBits VSRootPT_T - 1)"
  shows "array_assertion (pte_Ptr pt) (Suc (unat (2^(ptTranslationBits VSRootPT_T - 1) + of_nat n::machine_word)))
                         (hrs_htd (t_hrs_' (globals s')))"
  using assms
  sorry (* FIXME AARCH64 re-examine this lemma, it might no longer make sense with vspaces
  by (fastforce intro: page_table_at'_array_assertion
                simp: unat_add_simple ptTranslationBits_def word_bits_def unat_of_nat) *)

(* FIXME AARCH64 cte arg is named vspaceCapSlot on all other arches
   TODO: rename in the C, it's not a cte it's a slot
   TODO: change the C to use get/set pattern instead of cap_vspace_cap_ptr_set_capMappedASID etc
   see also performPageInvocationUnmap *)
lemma performASIDPoolInvocation_ccorres:
  notes option.case_cong_weak[cong]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' (isPTCap' o cteCap) ctSlot and asid_pool_at' poolPtr
        and K (asid_wf asid))
       (\<lbrace>\<acute>poolPtr = Ptr poolPtr\<rbrace> \<inter> \<lbrace>\<acute>asid___unsigned_long = asid\<rbrace> \<inter> \<lbrace>\<acute>cte = Ptr ctSlot\<rbrace>)
       []
       (liftE (performASIDPoolInvocation (Assign asid poolPtr ctSlot)))
       (Call performASIDPoolInvocation_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp K_def)
  apply (rule ccorres_gen_asm)
  apply (cinit lift: poolPtr_' asid___unsigned_long_' cte_')
   apply (rule_tac Q="\<lambda>slotCap.  valid_arch_state' and valid_objs' and
                                 cte_wp_at' ((=) slotCap o cteCap) ctSlot and
                                 (\<lambda>_. isPTCap' slotCap \<and> capPTBasePtr (capCap slotCap) \<noteq> 0)" and
                  Q'="\<lambda>slotCap slotCap_C. UNIV"
                  in ccorres_split_nothrow)
       sorry (* FIXME AARCH64 this rule expects a Basic assignment, but we have
                  CALL cap_vspace_cap_ptr_set_capMappedASID_'proc
       apply (ctac add: getSlotCap_h_val_ccorres)
      apply ceqv
     apply (rule ccorres_gen_asm)
     apply (rule ccorres_guard_imp)
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply csymbr
       apply (ctac add: ccorres_updateCap)
         apply (ctac (no_vcg) add: copyGlobalMappings_ccorres)
          apply (simp add: liftM_def)
          apply (rule ccorres_pre_getObject_asidpool)
          apply (rule ccorres_move_c_guard_ap)
          apply (rule ccorres_add_return2)
          apply (ctac add: setObjectASID_Basic_ccorres)
            apply (rule ccorres_rel_imp[where xf'=ret__unsigned_long_' and
                                              r'="\<lambda>_ x. x = SCAST(32 signed \<rightarrow> 64) EXCEPTION_NONE"])
             apply (rule ccorres_return_C; simp)
            apply simp
           apply wp
          apply simp
          apply vcg
         apply (rule hoare_strengthen_post[where Q="\<lambda>_. \<top>"], wp)
         apply (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def)
        apply wp
       apply simp
       apply vcg
      apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (drule (1) ctes_of_valid')
      apply (clarsimp simp: valid_cap'_def isPTCap'_def)
     apply (clarsimp simp: isPTCap'_def cap_get_tag_isCap_unfolded_H_cap asidInvalid_def)
     apply (clarsimp split: if_split)
     apply (erule ccap_relationE)
     apply (rename_tac cap_CL)
     apply (drule_tac t="cap_to_H cap_CL" in sym)
     apply (clarsimp simp: cap_lift_PTCap_Base[symmetric])
     apply (frule cap_to_H_PTCap, clarsimp)
     apply (rule conjI; clarsimp)
      apply (clarsimp simp: cap_page_table_cap_lift)
      apply (clarsimp simp: ccap_relation_def cap_to_H_def)
      apply (simp (no_asm) add: cap_page_table_cap_lift_def)
      apply (clarsimp simp: asid_wf_eq_mask_eq asid_bits_def)
      apply (simp add: c_valid_cap_def cl_valid_cap_def)
     apply (erule notE[where P="casid_pool_relation a b" for a b])
     apply (clarsimp simp: typ_heap_simps simp flip: fun_upd_def)
     apply (clarsimp simp: casid_pool_relation_def
                     split: asidpool.splits asid_pool_C.splits)
     apply (rule conjI)
      apply (rule array_relation_update)
         apply (simp add: inv_def)
        apply (simp add: mask_2pm1)
       apply simp
      apply (simp add: asid_low_bits_def)
     apply (clarsimp simp: word_and_le1 inv_def ran_def split: if_splits)
    apply wp
    apply (wpsimp simp: getSlotCap_def wp: getCTE_wp)
   apply simp
   apply vcg
  apply (clarsimp simp: cte_wp_at_ctes_of isPTCap'_def)
  apply (drule ctes_of_valid', fastforce)
  apply (clarsimp simp: valid_cap'_def isPTCap'_def)
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply clarsimp
  apply (drule page_table_pte_atI'[where x=0, simplified])
  apply (erule no_0_typ_at', fastforce)
  done *)

lemma pte_case_isInvalidPTE:
  "(case pte of InvalidPTE \<Rightarrow> P | _ \<Rightarrow> Q)
   = (if isInvalidPTE pte then P else Q)"
  by (cases pte, simp_all add: isInvalidPTE_def)

lemma ccap_relation_vspace_mapped_asid:
  "ccap_relation (ArchObjectCap (PageTableCap p VSRootPT_T (Some (asid, vspace)))) cap
    \<Longrightarrow> asid = capVSMappedASID_CL (cap_vspace_cap_lift cap)"
  by (frule cap_get_tag_isCap_unfolded_H_cap)
     (clarsimp simp: cap_vspace_cap_lift ccap_relation_def cap_to_H_def split: if_splits)

(* FIXME AARCH64 potentially unused *)
lemma ccap_relation_page_table_mapped_asid:
  "ccap_relation (ArchObjectCap (PageTableCap p NormalPT_T (Some (asid, vspace)))) cap
    \<Longrightarrow> asid = capPTMappedASID_CL (cap_page_table_cap_lift cap)"
  by (frule cap_get_tag_isCap_unfolded_H_cap)
     (clarsimp simp: cap_page_table_cap_lift ccap_relation_def cap_to_H_def split: if_splits)

lemma performPageTableInvocationMap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (cte_at' ctSlot)
       (\<lbrace>ccap_relation cap \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>
        \<inter> \<lbrace>cpte_relation pte \<acute>pte\<rbrace> \<inter> \<lbrace>\<acute>ptSlot = Ptr ptSlot\<rbrace>)
       []
       (liftE (performPageTableInvocation (PageTableMap cap ctSlot pte ptSlot)))
       (Call performPageTableInvocationMap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: cap_' ctSlot_' pte_' ptSlot_')
   apply (ctac (no_vcg))
     apply (rule ccorres_split_nothrow)
         apply simp
         apply (erule storePTE_Basic_ccorres)
        apply ceqv
       sorry (* FIXME AARCH64 not clear whether we are looking at a PT, a VS, or need to handle both
       apply (rule ccorres_cases[where P="\<exists>p a v. cap = ArchObjectCap (PageTableCap p (Some (a, v)))"
                                   and H=\<top> and H'=UNIV];
              clarsimp split: capability.splits arch_capability.splits simp: ccorres_fail)
        apply (rule ccorres_add_return2)
        apply (ctac (no_vcg) add: sfence_ccorres)
         apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: return_def)
        apply wpsimp
       apply (rule ccorres_guard_imp)
         apply (rule ccorres_add_return2)
         apply (ctac (no_vcg) add: sfence_ccorres)
          apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: return_def)
         apply (wpsimp | vcg)+
  done *)



(* FIXME AARCH64 VCPU/HYP related block (everything from VSpace_C on ARM_HYP) adapted to AARCH64
   some of these might be needed earlier *)

(* FIXME AARCH64 move, potentially to a VCPU theory
   if we try move most of the VCPU lemmas into a VCPU theory, some might need items in this or later
   theories, meaning we'd need a VCPU low (maybe put into ArchAcc?) and VCPU high theory
 *)
(* When updating fields (or fields of fields) inside VCPUs, typ_heap_simps can resolve the
   hrs_mem_update of a field into a specific C vcpu update when on its own. Then if we can
   show that specific C vcpu is related to the Haskell one, there is no need to unfold
   rf_sr anymore. *)
lemma vcpu_hrs_mem_update_helper:
  "\<lbrakk> (s, s') \<in> rf_sr; ko_at' (vcpu'::vcpu) vcpuptr s;
     hrs_mem_update (f s') (t_hrs_' (globals s'))
     = hrs_mem_update (heap_update (vcpu_Ptr vcpuptr) cvcpu) (t_hrs_' (globals s'));
     cvcpu_relation vcpu cvcpu \<rbrakk>
   \<Longrightarrow> (s\<lparr>ksPSpace := (ksPSpace s)(vcpuptr \<mapsto> KOArch (KOVCPU vcpu))\<rparr>,
       globals_update (t_hrs_'_update (hrs_mem_update (f s'))) s') \<in> rf_sr"
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                        cmachine_state_relation_def update_vcpu_map_to_vcpu
                        cpspace_relation_def update_vcpu_map_tos)
  apply (frule (1) cmap_relation_ko_atD)
  apply (clarsimp simp: typ_heap_simps')
  apply (erule cmap_relation_upd_relI)
      apply (erule (3) ko_at_projectKO_opt)
  apply simp
  done

(* FIXME AARCH64 move *)
lemmas setObject_ccorres_helper_vcpu =
         setObject_ccorres_helper[where 'a=vcpu, simplified objBits_simps vcpuBits_def, simplified]

lemma vcpuUpdate_ccorres:
  (* We depend on the simplifier and typ_heap_simps to resolve what the updated VCPU on the C side
     looks like for specific updates f and heap_upd, and need to ensure they maintain the VCPU
     relation. *)
  assumes update_rel:
    "\<And>s s' vcpu cvcpu.
     \<lbrakk> (s, s') \<in> rf_sr; ko_at' vcpu vcpuptr s; cslift s' (vcpu_Ptr vcpuptr) = Some cvcpu;
       cvcpu_relation vcpu cvcpu \<rbrakk>
     \<Longrightarrow> \<exists>cvcpu'.
          hrs_mem_update (heap_upd s') (t_hrs_' (globals s'))
          = hrs_mem_update (heap_update (vcpu_Ptr vcpuptr) cvcpu') (t_hrs_' (globals s'))
          \<and> cvcpu_relation (f vcpu) cvcpu'"
  shows "ccorres dc xfdc \<top> UNIV hs
                 (vcpuUpdate vcpuptr f)
                 (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update (heap_upd s))) s))"
  apply (rule ccorres_guard_imp)
    apply (simp add: vcpuUpdate_def)
    apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
    apply (rule_tac P="ko_at' vcpu vcpuptr" in setObject_ccorres_helper_vcpu[where P'=UNIV])
    apply (rule conseqPre, vcg)
    apply clarsimp
    apply (frule (1) cmap_relation_ko_atD[OF cmap_relation_vcpu])
    apply clarsimp
    apply (frule (3) update_rel)
    apply clarsimp
    apply (rule vcpu_hrs_mem_update_helper)
       apply (fastforce dest!: vcpu_at_ko simp: obj_at'_ko_at'_prop)+
  done

method vcpuUpdate_ccorres
  \<open>ccorres of vcpuUpdate and a Basic heap update on vcpu fields\<close> =
  rule vcpuUpdate_ccorres,
  rule exI,
  rule conjI, \<comment> \<open>need to resolve schematic cvcpu before showing it's in the relation\<close>
  solves \<open>simp add: typ_heap_simps'\<close>, \<comment> \<open>calculate updated vcpu object\<close>
  \<comment> \<open>unfold VCPU and VGIC relations (will solve for simple relations)\<close>
  simp add: cvcpu_relation_regs_def cvgic_relation_def cvcpu_vppi_masked_relation_def

lemma vcpuUpdate_vcpuRegs_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
     (vcpuUpdate vcpuptr (\<lambda>vcpu. vcpuRegs_update (\<lambda>_. (vcpuRegs vcpu)(r := v)) vcpu))
     (Basic_heap_update
       (\<lambda>_. vcpuregs_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''regs_C'']))
       (\<lambda>s. Arrays.update (h_val (hrs_mem (t_hrs_' (globals s)))
                          (vcpuregs_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''regs_C'']))) (fromEnum r) v))"
  apply vcpuUpdate_ccorres
      using maxBound_is_bound[where 'a=vcpureg, simplified fromEnum_maxBound_vcpureg_def]
      apply (clarsimp simp: fromEnum_eq_iff less_eq_Suc_le split: if_split)
  done

(* FIXME AARCH64 consider moving this inline *)
lemma vgicUpdate_HCR_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
     (vgicUpdate vcpuptr (vgicHCR_update (\<lambda>_. hcr)))
     (Basic_heap_update
        (\<lambda>_. PTR(32 word) &(vgic_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''vgic_C''])\<rightarrow>[''hcr_C''])) (\<lambda>_. hcr))"
  by (simp add: vgicUpdate_def)
     vcpuUpdate_ccorres

(* FIXME AARCH64 consider moving this inline *)
lemma vgicUpdate_virtTimer_pcount_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
        (vcpuUpdate vcpuptr (vcpuVTimer_update (\<lambda>_. VirtTimer pcount)))
        (Basic_heap_update
          (\<lambda>_. PTR(64 word) &(PTR(vTimer_C) &(vcpu_Ptr vcpuptr\<rightarrow>[''virtTimer_C''])\<rightarrow>[''last_pcount_C'']))
          (\<lambda>_. pcount))"
  by vcpuUpdate_ccorres

(* FIXME AARCH64 consider moving this inline *)
lemma vgicUpdate_APR_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
        (vgicUpdate vcpuptr (vgicAPR_update (\<lambda>_. hcr)))
        (Basic_heap_update
          (\<lambda>_. PTR(32 word) &(vgic_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''vgic_C''])\<rightarrow>[''apr_C''])) (\<lambda>_. hcr))"
  by (simp add: vgicUpdate_def)
     vcpuUpdate_ccorres

(* FIXME AARCH64 consider moving this inline *)
lemma vgicUpdate_VMCR_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
        (vgicUpdate vcpuptr (vgicVMCR_update (\<lambda>_. hcr)))
        (Basic_heap_update
          (\<lambda>_. PTR(32 word) &(vgic_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''vgic_C''])\<rightarrow>[''vmcr_C''])) (\<lambda>_. hcr))"
  by (simp add: vgicUpdate_def)
     vcpuUpdate_ccorres

lemma vppievent_irq_noteq_fromEnum_mono:
  "vppi \<noteq> (k :: vppievent_irq) \<Longrightarrow> fromEnum vppi \<noteq> fromEnum k"
  apply (cases vppi, clarsimp)
  apply (cases k, clarsimp)
  done

lemma vcpuVPPIMasked_update_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
     (vcpuUpdate vcpuptr (\<lambda>vcpu. vcpuVPPIMasked_update (\<lambda>_. (vcpuVPPIMasked vcpu)(k := v)) vcpu))
     ((Basic_heap_update
       (\<lambda>s. vcpu_vppi_masked_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''vppi_masked_C'']))
       (\<lambda>s. Arrays.update (h_val (hrs_mem (t_hrs_' (globals s)))
                          (vcpu_vppi_masked_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''vppi_masked_C''])))
                          (fromEnum k) (from_bool v))))"
  apply vcpuUpdate_ccorres
  using maxBound_is_bound[where 'a=vppievent_irq, simplified fromEnum_maxBound_vppievent_irq_def]
  apply (split if_split)
  apply (rule allI)
  apply (rule conjI)
   apply clarsimp
  apply (rule impI)
  apply (subst Arrays.index_update2, simp)
   apply (rule vppievent_irq_noteq_fromEnum_mono)
   apply simp
  apply blast
  done

lemma vcpu_write_reg_ccorres:
  "ccorres dc xfdc
       (vcpu_at' vcpuptr)
       (\<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace> \<inter> \<lbrace> \<acute>reg = of_nat (fromEnum reg) \<rbrace> \<inter> \<lbrace> \<acute>value = v \<rbrace>) hs
     (vcpuWriteReg vcpuptr reg v)
     (Call vcpu_write_reg_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: vcpu_' reg_' value_')
   apply (rule ccorres_assert)
   apply clarsimp
   apply (rule ccorres_cond_false_seq, simp)
   apply (rule ccorres_move_const_guards)
   apply ccorres_rewrite
   apply (rule ccorres_move_c_guard_vcpu, rule vcpuUpdate_vcpuRegs_ccorres)
  using maxBound_is_bound[of reg, simplified fromEnum_maxBound_vcpureg_def]
  apply (clarsimp simp: seL4_VCPUReg_Num_def not_le word_less_nat_alt)
  done

lemma vcpu_save_reg_ccorres:
  "ccorres dc xfdc (vcpu_at' vcpuptr) (\<lbrace>unat \<acute>reg = fromEnum r\<rbrace> \<inter> \<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace>) hs
     (vcpuSaveReg vcpuptr r) (Call vcpu_save_reg_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: reg_' vcpu_')
   apply (rule ccorres_assert2)
   apply (rule ccorres_cond_false_seq, simp)
   apply (ctac add: vcpu_hw_read_reg_ccorres)
     apply (rule ccorres_move_const_guard ccorres_move_c_guard_vcpu)+
     apply (simp del: fun_upd_apply)
     apply (ctac add: vcpuUpdate_vcpuRegs_ccorres)
    apply wpsimp
   apply (vcg exspec=vcpu_hw_read_reg_modifies)
  apply (fastforce dest: maxBound_is_bound'
                   simp: fromEnum_maxBound_vcpureg_def seL4_VCPUReg_Num_def unat_arith_simps)
  done

lemma vcpu_restore_reg_ccorres:
  "ccorres dc xfdc
     (vcpu_at' vcpuptr) (\<lbrace>unat \<acute>reg = fromEnum r\<rbrace> \<inter> \<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace>) hs
     (vcpuRestoreReg vcpuptr r) (Call vcpu_restore_reg_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: reg_' vcpu_')
   apply (rule ccorres_assert2)
   apply (rule ccorres_cond_false_seq, simp)
   apply (rule ccorres_move_const_guard ccorres_move_c_guard_vcpu)+
   apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
   apply (ctac add: vcpu_hw_write_reg_ccorres)
  apply (frule maxBound_is_bound')
  apply (clarsimp simp: word_le_nat_alt word_less_nat_alt
                        fromEnum_maxBound_vcpureg_def seL4_VCPUReg_Num_def)
  apply (frule cmap_relation_vcpu)
  apply (clarsimp simp: typ_heap_simps cvcpu_relation_def cvcpu_regs_relation_def)
  done

lemma ccorres_dc_from_rrel:
  "ccorres r xf P P' hs a c \<Longrightarrow> ccorres dc xf' P P' hs a c"
  unfolding ccorres_underlying_def
  by (fastforce simp: unif_rrel_def split: xstate.splits)

lemma vcpu_restore_reg_range_ccorres:
  "ccorres dc xfdc
     (vcpu_at' vcpuptr and K (fromEnum (start::vcpureg) \<le> fromEnum end))
     (\<lbrace>unat \<acute>start = fromEnum start\<rbrace> \<inter> \<lbrace>unat \<acute>end = fromEnum end\<rbrace>
       \<inter> \<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace>) hs
     (vcpuRestoreRegRange vcpuptr start end) (Call vcpu_restore_reg_range_'proc)"
  using maxBound_is_bound[of start, simplified fromEnum_maxBound_vcpureg_def]
        length_upto_enum_le_maxBound[of start "end", simplified fromEnum_maxBound_vcpureg_def]
  apply -
  apply (rule ccorres_grab_asm)
  apply (cinit lift: start_' end_' vcpu_' simp: whileAnno_def)
   apply csymbr
   apply (rule ccorres_dc_from_rrel)
   apply (rule ccorres_mapM_x_while'[where i="fromEnum start" and F="\<lambda>n s. vcpu_at' vcpuptr s"])
       apply clarsimp
       apply (rule ccorres_guard_imp)
         apply (ctac add: vcpu_restore_reg_ccorres)
        apply assumption
       subgoal
         apply (clarsimp simp: fromEnum_upto_nth dest!: less_length_upto_enum_maxBoundD)
         by (subst unat_add_lem'; clarsimp simp: fromEnum_maxBound_vcpureg_def unat_of_nat_eq)
      subgoal
        apply (simp add: word_less_nat_alt word_le_nat_alt)
        apply (subst unat_add_lem'; clarsimp simp: unat_of_nat_eq)
        apply (fastforce simp add: upto_enum_red split: if_splits)
        done
     apply (rule allI, rule conseqPre, vcg exspec=vcpu_restore_reg_modifies)
     apply fastforce
    apply wpsimp
   apply (fastforce simp: word_bits_def)
  apply (clarsimp simp: Collect_const_mem)
  apply (subst unat_eq_of_nat[symmetric]; clarsimp)
  done

lemma vcpu_save_reg_range_ccorres:
  "ccorres dc xfdc
     (vcpu_at' vcpuptr and K (fromEnum start \<le> fromEnum end))
     (\<lbrace>unat \<acute>start = fromEnum start\<rbrace> \<inter> \<lbrace>unat \<acute>end = fromEnum end\<rbrace>
       \<inter> \<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace>) hs
     (vcpuSaveRegRange vcpuptr start end) (Call vcpu_save_reg_range_'proc)"
  using maxBound_is_bound[of start, simplified fromEnum_maxBound_vcpureg_def]
        length_upto_enum_le_maxBound[of start "end", simplified fromEnum_maxBound_vcpureg_def]
  apply -
  apply (rule ccorres_grab_asm)
  apply (cinit lift: start_' end_' vcpu_' simp: whileAnno_def)
   apply csymbr
   apply (rule ccorres_dc_from_rrel)
   apply (rule ccorres_mapM_x_while'[where i="fromEnum start" and F="\<lambda>n s. vcpu_at' vcpuptr s"])
       apply clarsimp
       apply (rule ccorres_guard_imp)
         apply (ctac add: vcpu_save_reg_ccorres)
        apply assumption
       subgoal
         apply (clarsimp simp: fromEnum_upto_nth dest!: less_length_upto_enum_maxBoundD)
         by (subst unat_add_lem'; clarsimp simp: fromEnum_maxBound_vcpureg_def unat_of_nat_eq)
      subgoal
        apply (simp add: word_less_nat_alt word_le_nat_alt)
        apply (subst unat_add_lem'; clarsimp simp: unat_of_nat_eq)
        apply (fastforce simp add: upto_enum_red split: if_splits)
        done
     apply (rule allI, rule conseqPre, vcg exspec=vcpu_save_reg_modifies)
     apply fastforce
    apply wpsimp
    apply (fastforce simp: word_bits_def)
  apply (clarsimp simp: Collect_const_mem)
  apply (subst unat_eq_of_nat[symmetric]; clarsimp)
  done

lemma vcpu_read_reg_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top>
       (\<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace> \<inter> \<lbrace> \<acute>reg = of_nat (fromEnum reg) \<rbrace>) hs
     (vcpuReadReg vcpuptr reg)
     (Call vcpu_read_reg_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: vcpu_' reg_')
   apply (rule ccorres_assert)
   apply clarsimp
   apply (rule ccorres_cond_false_seq, simp)
   apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
   apply (rule ccorres_move_const_guards)
   apply ccorres_rewrite
   apply (rule ccorres_move_c_guard_vcpu)
   apply (rule ccorres_return_C; clarsimp)
  apply (clarsimp simp: vcpu_at_ko'_eq)

  using maxBound_is_bound[of reg, simplified fromEnum_maxBound_vcpureg_def]
  apply (clarsimp simp: seL4_VCPUReg_Num_def not_le word_less_nat_alt)
  apply (fastforce elim: allE[where x=reg]
                   simp: cvcpu_relation_def cvcpu_regs_relation_def typ_heap_simps' )
  done

lemma irqVPPIEventIndex_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>irq && mask LENGTH(irq_len) = \<acute>irq \<rbrace>
       Call irqVPPIEventIndex_'proc
       \<lbrace> \<acute>ret__unsigned_long
         = case_option (ucast VPPIEventIRQ_invalid) (of_nat \<circ> fromEnum) (irqVPPIEventIndex (ucast \<^bsup>s\<^esup>irq)) \<rbrace>"
  apply vcg
  apply (clarsimp simp: irqVPPIEventIndex_def IRQ_def irqVTimerEvent_def
                        Kernel_C.VPPIEventIRQ_VTimer_def
                  split: if_splits)
  apply (auto dest!: word_unat.Rep_inject[THEN iffD2]
              simp: VPPIEventIRQ_invalid_def unat_ucast_eq_unat_and_mask and_mask_eq_iff_le_mask
                    fromEnum_def enum_vppievent_irq mask_def word_le_nat_alt word_less_nat_alt
              simp flip: word_unat.Rep_inject)
  done

lemma vcpuWriteReg_obj_at'_vcpuVPPIMasked:
  "vcpuWriteReg vcpuptr r v
   \<lbrace>\<lambda>s. obj_at' (\<lambda>vcpu. P (vcpuVPPIMasked vcpu))  vcpuptr s \<rbrace>"
  apply (simp add: vcpuWriteReg_def vcpuUpdate_def obj_at'_real_def)
  apply (wp setObject_ko_wp_at[where n="objBits (undefined :: vcpu)"], simp)
      apply (simp add: objBits_simps vcpuBits_def)+
    apply (wpsimp wp: getVCPU_wp)+
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def)
  done

lemma isIRQActive_ccorres:
  "ccorres (\<lambda>rv rv'. rv' = from_bool rv) ret__unsigned_long_'
        (\<lambda>s. irq \<le> scast Kernel_C.maxIRQ) ({s. irq_' s = ucast irq}) []
        (isIRQActive irq) (Call isIRQActive_'proc)"
  apply (cinit lift: irq_')
   apply (simp add: getIRQState_def getInterruptState_def)
   apply (rule_tac P="irq \<le> ucast Kernel_C.maxIRQ \<and> unat irq \<le> (unat maxIRQ)" in ccorres_gen_asm)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: simpler_gets_def word_sless_msb_less maxIRQ_def
                         word_less_nat_alt)
   apply (clarsimp simp: order_le_less_trans unat_less_helper Kernel_C.IRQInactive_def
                         Kernel_C.maxIRQ_def word_0_sle_from_less[OF order_less_le_trans, OF ucast_less])
   apply (clarsimp simp: rf_sr_def cstate_relation_def Kernel_C.maxIRQ_def
                         Let_def cinterrupt_relation_def)
   apply (drule spec, drule(1) mp)
   apply (case_tac "intStateIRQTable (ksInterruptState \<sigma>) irq")
      apply (simp add: irq_state_defs Kernel_C.maxIRQ_def word_le_nat_alt maxIRQ_def)+
  done

lemma restore_virt_timer_ccorres:
  "ccorres dc xfdc
     (vcpu_at' vcpuptr)
     (\<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace>) hs
     (restoreVirtTimer vcpuptr) (Call restore_virt_timer_'proc)"
  apply (cinit lift: vcpu_')
   apply (ctac (no_vcg) add: vcpu_restore_reg_ccorres)
    apply (ctac (no_vcg) add: vcpu_restore_reg_ccorres)
    sorry (* FIXME AARCH64 code changed, needs re-examination
    apply csymbr
    apply (ctac (no_vcg) add: vcpu_read_reg_ccorres)
     apply csymbr
     apply csymbr
     apply clarsimp
     apply (ctac (no_vcg) add: set_cntv_cval_64_ccorres)
      apply csymbr
      apply (ctac (no_vcg) add: read_cntpct_ccorres)
       apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
       apply (rule_tac val="current_cntpct - vtimerLastPCount (vcpuVTimer vcpu)"
                and R'=UNIV and R="ko_at' vcpu vcpuptr"
                and xf'=pcount_delta_'
                in ccorres_symb_exec_r_known_rv)
          apply (rule conseqPre, vcg)
          apply (fastforce dest: vcpu_at_rf_sr simp: typ_heap_simps' cvcpu_relation_def)
         apply ceqv
        apply (ctac (no_vcg) add: vcpu_read_reg_ccorres)
         apply csymbr
         apply (ctac (no_vcg) add: vcpu_read_reg_ccorres)
          apply csymbr
          apply csymbr
          apply csymbr
          apply clarsimp
          apply (ctac (no_vcg) add: vcpu_write_reg_ccorres)
           apply (ctac (no_vcg) add: vcpu_write_reg_ccorres)
            apply (ctac (no_vcg) add: set_cntv_off_64_ccorres)
             apply (ctac (no_vcg) add: isIRQActive_ccorres)
              apply (clarsimp simp: when_def simp del: Collect_const)
              apply (rule ccorres_split_nothrow[where xf'=xfdc and r'=dc])
                  apply (rule ccorres_cond[where R=\<top>], simp add: Collect_const_mem)
                   apply csymbr
                   apply clarsimp
                   apply (rule ccorres_move_const_guards)
                   apply (rule ccorres_move_c_guard_vcpu)
                   apply (clarsimp simp: irqVPPIEventIndex_def IRQ_def irqVTimerEvent_def
                                         fromEnum_def enum_vppievent_irq)
                   apply (rule ccorres_call)
                      apply (rule_tac P="obj_at' (\<lambda>vcpu'. vcpuVPPIMasked vcpu' vppievent_irq.VPPIEventIRQ_VTimer
                                                           = vcpuVPPIMasked vcpu vppievent_irq.VPPIEventIRQ_VTimer) vcpuptr" in ccorres_cross_over_guard)
                      apply (rule maskInterrupt_ccorres, simp)
                    apply simp
                   apply simp
                  apply (rule ccorres_return_Skip)
                 apply ceqv
                apply (ctac (no_vcg) add: vcpu_restore_reg_ccorres)
               apply wpsimp
              apply clarsimp
              apply (vcg exspec=maskInterrupt_modifies)
             apply wpsimp+
             (* ignore rv of isIRQActive *)
             apply (wp (once) hoare_drop_imp[where f="isIRQActive irq" for irq])
              apply (wpsimp simp: isIRQActive_def liftM_bind
                            wp: vcpuWriteReg_obj_at'_vcpuVPPIMasked)+
       apply (clarsimp simp: Collect_const_mem)
       apply vcg
     apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')+

  apply (clarsimp simp: IRQ_def Collect_const_mem irqVPPIEventIndex_def)
  apply (simp add: vcpureg_eq_use_types[where reg=VCPURegCNTV_CVALhigh, simplified, symmetric]
                   vcpureg_eq_use_types[where reg=VCPURegCNTV_CVALlow, simplified, symmetric]
                   vcpureg_eq_use_types[where reg=VCPURegCNTV_CTL, simplified, symmetric]
                   vcpureg_eq_use_types[where reg=VCPURegCNTVOFFhigh, simplified, symmetric]
                   vcpureg_eq_use_types[where reg=VCPURegCNTVOFFlow, simplified, symmetric])
  apply (clarsimp simp: irqVTimerEvent_def Kernel_C.maxIRQ_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule vcpu_at_ko)
   apply normalise_obj_at'
   apply (simp add: fromEnum_def enum_vppievent_irq)

  (* remaining C side *)
  apply (clarsimp simp: and_mask_eq_iff_le_mask)
  apply (clarsimp simp: mask_def)
  apply normalise_obj_at'
  apply (drule (1) vcpu_at_rf_sr)
  apply (clarsimp simp: typ_heap_simps cvcpu_relation_def cvcpu_vppi_masked_relation_def)
  apply (erule_tac x="vppievent_irq.VPPIEventIRQ_VTimer" in allE)+
  apply (fastforce simp: fromEnum_def enum_vppievent_irq)
  done *)

lemma vcpuUpdate_vTimer_pcount_ccorres:
  "ccorres dc xfdc (vcpu_at' vcpuptr) UNIV hs
        (vcpuUpdate vcpuptr (vcpuVTimer_update (\<lambda>_. VirtTimer v)))
        (Guard C_Guard {s. s \<Turnstile>\<^sub>c vcpu_Ptr vcpuptr}
          (Basic_heap_update
            (\<lambda>_. PTR(64 word) &(PTR(vTimer_C) &(vcpu_Ptr vcpuptr\<rightarrow>[''virtTimer_C''])\<rightarrow>[''last_pcount_C''])) (\<lambda>_. v)))"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_move_c_guard_vcpu)
    apply vcpuUpdate_ccorres
    apply simp+
  done

lemma save_virt_timer_ccorres:
  "ccorres dc xfdc
     (vcpu_at' vcpuptr)
     (\<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace>) hs
     (saveVirtTimer vcpuptr) (Call save_virt_timer_'proc)"
  apply (cinit lift: vcpu_')
   apply (ctac (no_vcg) add: vcpu_save_reg_ccorres)
    apply (ctac (no_vcg) add: vcpu_hw_write_reg_ccorres)
     apply (ctac (no_vcg) add: vcpu_save_reg_ccorres)
      apply (ctac (no_vcg) add: vcpu_save_reg_ccorres)
       apply (ctac (no_vcg) add: vcpu_save_reg_ccorres)
        apply (ctac (no_vcg) add: check_export_arch_timer_ccorres)
         apply (ctac (no_vcg) add: read_cntpct_ccorres)
          apply clarsimp
          apply (rule vcpuUpdate_vTimer_pcount_ccorres)
         apply wpsimp+
  apply (simp add: vcpureg_eq_use_types[where reg=VCPURegCNTV_CVAL, simplified, symmetric]
                   vcpureg_eq_use_types[where reg=VCPURegCNTV_CTL, simplified, symmetric]
                   vcpureg_eq_use_types[where reg=VCPURegCNTVOFF, simplified, symmetric]
                   vcpureg_eq_use_types[where reg=VCPURegCNTKCTL_EL1, simplified, symmetric])
  done

lemma armv_vcpu_save_ccorres:
  "ccorres dc xfdc
     (vcpu_at' vcpuptr)
     (\<lbrace> \<acute>vcpu = vcpu_Ptr vcpuptr \<rbrace> \<inter> \<lbrace> \<acute>active = from_bool act \<rbrace>) hs
     (armvVCPUSave vcpuptr act) (Call armv_vcpu_save_'proc)"
  apply (cinit lift: vcpu_' active_')
   apply (ctac (no_vcg) add: vcpu_save_reg_range_ccorres)
  apply wpsimp
  apply (clarsimp split: if_splits simp: seL4_VCPUReg_defs fromEnum_def enum_vcpureg)
  done

lemma vcpu_disable_ccorres:
  "ccorres dc xfdc
     (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj' and valid_arch_state'
       and (case v of None \<Rightarrow> \<top> | Some new \<Rightarrow> vcpu_at' new))
     ({s. vcpu_' s = option_to_ptr v}) hs
     (vcpuDisable v) (Call vcpu_disable_'proc)"
  supply if_cong[cong] option.case_cong[cong] empty_fail_cond[simp]
  apply (cinit lift: vcpu_')
   apply (ctac (no_vcg) add: dsb_ccorres)
    apply (rule ccorres_split_nothrow_novcg)
        apply wpc
         (* v=None *)
         apply simp
         apply ccorres_rewrite
         apply (rule ccorres_return_Skip)
        (* v=Some x2 *)
        apply (rule ccorres_cond_true)
        apply (rule ccorres_rhs_assoc)+
        apply (ctac (no_vcg) add: get_gic_vcpu_ctrl_hcr_ccorres)
         apply (rule ccorres_split_nothrow_novcg[of _ _ dc xfdc])
             apply (rule ccorres_move_const_guard ccorres_move_c_guard_vcpu, simp)
             apply clarsimp
             apply (ctac (no_vcg) add: vgicUpdate_HCR_ccorres)
            apply ceqv
           apply (ctac (no_vcg) add: vcpu_save_reg_ccorres)
            apply (ctac (no_vcg) add: vcpu_save_reg_ccorres)
             apply (ctac (no_vcg) pre: ccorres_call[where r=dc and xf'=xfdc] add: isb_ccorres)
               apply (wpsimp simp: guard_is_UNIV_def)+
         apply (clarsimp split: if_splits simp: seL4_VCPUReg_CPACR_def fromEnum_def enum_vcpureg)
        apply wpsimp
       apply ceqv
      apply (clarsimp simp: doMachineOp_bind bind_assoc)
      apply (ctac (no_vcg) add: set_gic_vcpu_ctrl_hcr_ccorres)
       apply (ctac (no_vcg) add: isb_ccorres)
        apply (ctac (no_vcg) add: setSCTLR_ccorres)
         apply (ctac (no_vcg) add: isb_ccorres)
          apply (ctac (no_vcg) add: setHCR_ccorres)
           apply (ctac (no_vcg) add: isb_ccorres)
            apply (ctac (no_vcg) add: enableFpuEL01_ccorres)
             apply (wpc; ccorres_rewrite)
              apply (rule ccorres_return_Skip)
             apply (rename_tac vcpu_ptr)
             apply (rule_tac P="the v \<noteq> 0" in ccorres_gen_asm)
             apply ccorres_rewrite
             apply (ctac (no_vcg) add: save_virt_timer_ccorres)
              apply (ctac (no_vcg) add: maskInterrupt_ccorres)
             apply (wpsimp wp: hoare_vcg_all_lift)+
    apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem hcrNative_def sctlrDefault_def
                          irqVTimerEvent_def IRQ_def)
   apply (wpsimp wp: hoare_vcg_all_lift)+
  apply (clarsimp simp: Collect_const_mem ko_at'_not_NULL dest!: vcpu_at_ko split: option.splits)
  done

lemma vcpu_enable_ccorres:
  "ccorres dc xfdc
     (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj'
       and valid_arch_state' and vcpu_at' v)
     ({s. vcpu_' s = vcpu_Ptr v}) hs
     (vcpuEnable v) (Call vcpu_enable_'proc)"
  supply empty_fail_cond[simp]
  apply (cinit lift: vcpu_')
   apply (ctac (no_vcg) add: vcpu_restore_reg_ccorres)+
    apply (rule ccorres_pre_getObject_vcpu, rename_tac vcpu)
    apply (clarsimp simp: doMachineOp_bind bind_assoc)
    apply (ctac (no_vcg) add: setHCR_ccorres)
     apply (ctac  (no_vcg) add: isb_ccorres)
      apply (rule_tac P="ko_at' vcpu v" in ccorres_cross_over_guard)
      apply (ctac pre: ccorres_move_c_guard_vcpu add: set_gic_vcpu_ctrl_hcr_ccorres)
        apply wpsimp+
        apply (ctac (no_vcg) add: vcpu_restore_reg_ccorres)
         apply (ctac (no_vcg) add: restore_virt_timer_ccorres)
        apply wpsimp
       apply simp
       apply wpsimp
      apply (vcg exspec=set_gic_vcpu_ctrl_hcr_modifies)
     apply wpsimp+
   apply (rule_tac Q="\<lambda>_. vcpu_at' v" in hoare_post_imp, fastforce)
   apply wpsimp
  apply (clarsimp simp: typ_heap_simps' Collect_const_mem cvcpu_relation_def
                        cvcpu_regs_relation_def Let_def cvgic_relation_def hcrVCPU_def
         | rule conjI | simp)+
   apply (drule (1) vcpu_at_rf_sr)
   apply (clarsimp simp: typ_heap_simps' cvcpu_relation_def cvgic_relation_def)
  apply (clarsimp split: if_splits simp: seL4_VCPUReg_CPACR_def fromEnum_def enum_vcpureg)
  done

lemma vcpu_restore_ccorres:
  notes upt_Suc[simp del] Collect_const[simp del]
  shows
  "ccorres dc xfdc
       (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj' and valid_arch_state'
        and vcpu_at' vcpuPtr)
       ({s. vcpu_' s = vcpu_Ptr vcpuPtr}) hs
     (vcpuRestore vcpuPtr) (Call vcpu_restore_'proc)"
  supply empty_fail_cond[simp]
  apply (cinit lift: vcpu_' simp: whileAnno_def)
   apply (simp add: doMachineOp_bind uncurry_def split_def doMachineOp_mapM_x)+
   apply (clarsimp simp: bind_assoc)
   apply (ctac (no_vcg) add: set_gic_vcpu_ctrl_hcr_ccorres)
    apply (ctac (no_vcg) add: isb_ccorres)
     apply (rule ccorres_pre_getObject_vcpu)
     apply (rule ccorres_move_c_guard_vcpu, rename_tac vcpu)
     apply (rule ccorres_pre_gets_armKSGICVCPUNumListRegs_ksArchState, rename_tac lr_num)
     apply (ctac (no_vcg) add: set_gic_vcpu_ctrl_vmcr_ccorres)
      apply (rule_tac P="ko_at' vcpu vcpuPtr" in ccorres_cross_over_guard)
      apply (ctac (no_vcg) add: set_gic_vcpu_ctrl_apr_ccorres)
       apply (rule_tac xf'=lr_num_' and R="\<lambda>s. lr_num = (armKSGICVCPUNumListRegs \<circ> ksArchState) s"
                   and val="of_nat lr_num" in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
          apply vcg
          apply (fastforce intro!: rf_sr_armKSGICVCPUNumListRegs)
         apply ceqv
        apply (rule ccorres_rhs_assoc2)
        apply (rule ccorres_split_nothrow_novcg)
            (* the loop *)
            apply (rule_tac P="lr_num \<le> 63" in ccorres_gen_asm)
            apply (rule_tac F="\<lambda>_ s. lr_num \<le> 63 \<and> ko_at' vcpu vcpuPtr s" in ccorres_mapM_x_while)
                apply (intro allI impI)
                apply clarsimp
                apply (rule ccorres_guard_imp2)
                 apply (rule_tac P="\<lambda>s. lr_num \<le> 63" in ccorres_cross_over_guard)
                 apply (rule ccorres_Guard)
                 apply (rule_tac val="of_nat n" in ccorres_abstract_known[where xf'=i_'], ceqv)
                 apply (rule_tac P="n \<le> 63" in ccorres_gen_asm)
                 apply (rule ccorres_move_c_guard_vcpu)
                 apply (ctac (no_vcg) add: set_gic_vcpu_ctrl_lr_ccorres)
                apply (clarsimp simp: virq_to_H_def ko_at_vcpu_at'D upt_Suc)
                apply (rule conjI)
                 apply (subst scast_eq_ucast; (rule refl)?)
                 apply (fastforce intro!: not_msb_from_less simp: word_less_nat_alt unat_of_nat)
                apply (frule (1) vcpu_at_rf_sr)
                apply (clarsimp simp: typ_heap_simps cvcpu_relation_regs_def cvgic_relation_def virq_to_H_def unat_of_nat)
                apply (simp add: word_less_nat_alt upt_Suc)
                subgoal (* FIXME extract into separate lemma *)
                  by (fastforce simp: word_less_nat_alt unat_of_nat_eq elim: order_less_le_trans)
               apply clarsimp
               apply (simp add: upt_Suc)
              apply vcg
              apply (fastforce simp: word_less_nat_alt unat_of_nat_eq word_bits_def elim: order_less_le_trans)
             apply wpsimp
            apply (simp add: upt_Suc word_bits_def)
           apply ceqv
          apply (ctac add: vcpu_restore_reg_range_ccorres)
            apply (ctac add: vcpu_enable_ccorres)
           apply wpsimp
          apply (vcg exspec=vcpu_restore_reg_range_modifies)
         apply (wpsimp wp: crunch_wps)
        apply (wpsimp simp: guard_is_UNIV_def upt_Suc ko_at_vcpu_at'D  wp: mapM_x_wp_inv
               | rule UNIV_I
               | wp hoare_vcg_imp_lift hoare_vcg_all_lift hoare_vcg_disj_lift)+
        apply (fastforce simp: fromEnum_def enum_vcpureg seL4_VCPUReg_defs)
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (wpsimp simp: vcpu_at_ko'_eq wp: hoare_vcg_imp_lift')+
  apply (rule conjI)
   apply (fastforce simp: invs_no_cicd'_def valid_arch_state'_def max_armKSGICVCPUNumListRegs_def)
  apply (rule conjI)
   apply (fastforce simp: fromEnum_def enum_vcpureg)
  apply (fastforce dest!: vcpu_at_rf_sr
                   simp: typ_heap_simps' cvcpu_relation_def cvgic_relation_def)
  done

(* FIXME AARCH64 unused
lemma ccorres_pre_getsNumListRegs:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. (armKSGICVCPUNumListRegs \<circ> ksArchState) s = rv \<longrightarrow> P rv s))
                  {s. \<forall>rv num'. gic_vcpu_num_list_regs_' (globals s) = num'
                                 \<longrightarrow> s \<in> P' rv }
                          hs (gets (armKSGICVCPUNumListRegs \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l)
       defer
       apply wp
      apply (rule hoare_gets_sp)
     apply (clarsimp simp: empty_fail_def getCurThread_def simpler_gets_def)
    apply assumption
   apply clarsimp
   defer
   apply (rule ccorres_guard_imp)
     apply (rule cc)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: rf_sr_ksArchState_armHSCurVCPU)
  done  *)

lemma ccorres_gets_armKSGICVCPUNumListRegs:
  "ccorres ((=) \<circ> of_nat) lr_num_' \<top> UNIV hs
           (gets (armKSGICVCPUNumListRegs \<circ> ksArchState)) (\<acute>lr_num :== \<acute>gic_vcpu_num_list_regs)"
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre, vcg)
  apply (clarsimp simp: simpler_gets_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)
  done

lemma vgicUpdateLR_ccorres:
  "ccorres dc xfdc (\<top> and K (n \<le> 63 \<and> n' = n \<and> virq_to_H v' = v)) UNIV hs
     (vgicUpdateLR vcpuptr n v)
     (Basic_heap_update
       (\<lambda>_. vgic_lr_C_Ptr &(vgic_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''vgic_C''])\<rightarrow>[''lr_C'']))
       (\<lambda>s. Arrays.update
              (h_val (hrs_mem (t_hrs_' (globals s)))
              (vgic_lr_C_Ptr &(vgic_C_Ptr &(vcpu_Ptr vcpuptr\<rightarrow>[''vgic_C''])\<rightarrow>[''lr_C''])))
              n' v'))"
  apply (rule ccorres_grab_asm)
  apply (simp add: vgicUpdateLR_def vgicUpdate_def)
  apply vcpuUpdate_ccorres
  supply from_bool_eq_if[simp] from_bool_eq_if'[simp] from_bool_0[simp]
  apply (fastforce simp: virq_to_H_def cvcpu_vppi_masked_relation_def split: if_split)
  done

lemma vcpu_save_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres dc xfdc
      (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj' and valid_arch_state'
        and case_option \<top> (vcpu_at' \<circ> fst) v)
      ({s. vcpu_' s = case_option NULL (vcpu_Ptr \<circ> fst) v}
       \<inter> {s. active_' s = case_option 0 (from_bool \<circ> snd) v}) hs
    (vcpuSave v) (Call vcpu_save_'proc)"
  supply if_cong[cong] option.case_cong[cong]
  apply (cinit lift: vcpu_' active_' simp: whileAnno_def)
   apply wpc
    (* v = None *)
    apply (rule ccorres_fail)
   (* v = Some (vcpuPtr, active) *)
   apply wpc
   apply (rename_tac vcpuPtr act)
   apply (ctac (no_vcg) add: dsb_ccorres)
    apply (rule ccorres_split_nothrow_novcg)
        apply (rule_tac R=\<top> in ccorres_when)
         apply clarsimp
        apply (rule ccorres_rhs_assoc)+
        apply (ctac (no_vcg) add: vcpu_save_reg_ccorres)
         apply (ctac (no_vcg) add: get_gic_vcpu_ctrl_hcr_ccorres)
          apply (rule ccorres_move_c_guard_vcpu)
          apply (clarsimp)
          apply (ctac (no_vcg) add: vgicUpdate_HCR_ccorres)
            apply (rule ccorres_call[where xf'=xfdc], rule save_virt_timer_ccorres)
              apply wpsimp+
       apply ceqv
      apply (ctac (no_vcg) add: get_gic_vcpu_ctrl_vmcr_ccorres)
       apply clarsimp
       apply (rule ccorres_move_c_guard_vcpu)
       apply (ctac (no_vcg) add: vgicUpdate_VMCR_ccorres)
         apply (ctac (no_vcg) add: get_gic_vcpu_ctrl_apr_ccorres)
          apply (rule ccorres_move_c_guard_vcpu)
          apply clarsimp
          apply (ctac (no_vcg) add: vgicUpdate_APR_ccorres)
            apply (ctac (no_vcg) add: ccorres_gets_armKSGICVCPUNumListRegs)
              apply (rename_tac lr_num lr_num')
              apply (rule ccorres_rhs_assoc2)
              apply (rule ccorres_split_nothrow_novcg)
                  (* the loop *)
                  apply (rule_tac P="lr_num \<le> 63" in ccorres_gen_asm)
                  apply (rule_tac F="\<lambda>_ s. lr_num \<le> 63 \<and> vcpu_at' vcpuPtr s" in ccorres_mapM_x_while)
                      apply (intro allI impI)
                      apply clarsimp
                      apply (rule ccorres_guard_imp2)
                       apply (rule_tac P="\<lambda>s. lr_num \<le> 63" in ccorres_cross_over_guard)
                       apply (ctac (no_vcg) add: get_gic_vcpu_ctrl_lr_ccorres)
                        apply (rule ccorres_Guard)
                        apply (rule_tac val="of_nat n" in ccorres_abstract_known[where xf'=i_'], ceqv)
                        apply (rule_tac P="n \<le> 63" in ccorres_gen_asm)
                        apply (rule ccorres_move_c_guard_vcpu)
                        apply (clarsimp simp: unat_of_nat_eq)
                        apply (ctac (no_vcg) add: vgicUpdateLR_ccorres)
                       apply (wpsimp simp: virq_to_H_def)+
                      apply (subst scast_eq_ucast; (rule refl)?)
                       apply (fastforce intro!: not_msb_from_less simp: word_less_nat_alt unat_of_nat)
                      apply (fastforce intro: word_of_nat_less)
                     apply (fastforce simp: word_less_nat_alt unat_of_nat)
                    apply clarsimp
                    apply (rule conseqPre, vcg exspec=get_gic_vcpu_ctrl_lr_modifies)
                    apply fastforce
                   apply wpsimp
                  apply (fastforce simp: word_bits_def)
                 apply ceqv
                apply (ctac (no_vcg) add: armv_vcpu_save_ccorres)
               apply (wpsimp simp: guard_is_UNIV_def wp: mapM_x_wp_inv)+
  apply (simp add: invs_no_cicd'_def valid_arch_state'_def max_armKSGICVCPUNumListRegs_def)
  done

lemma vcpu_switch_ccorres_None:
   "ccorres dc xfdc
             (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj'
                     and valid_arch_state')
             ({s. new_' s = NULL}) hs
             (vcpuSwitch None) (Call vcpu_switch_'proc)"
  apply (cinit lift: new_')
  (* v = None *)
   apply ccorres_rewrite
   apply (simp add: when_def)
   apply (rule ccorres_pre_getCurVCPU)
   apply wpc
    (* v = None & CurVCPU = None *)
    apply (rule ccorres_cond_false)
    apply (rule ccorres_return_Skip)
   (* v = None & CurVCPU \<noteq> None *)
   apply ccorres_rewrite
   apply wpc
   apply (rename_tac ccurv cactive)
   apply simp
   apply (rule ccorres_cond_true)
   apply (rule_tac R="\<lambda>s. armHSCurVCPU (ksArchState s) = Some (ccurv, cactive)" in ccorres_cond)
     apply (clarsimp simp: cur_vcpu_relation_def dest!: rf_sr_ksArchState_armHSCurVCPU)
    apply (ctac add: vcpu_disable_ccorres)
      apply (rule_tac v=x2 in armHSCurVCPU_update_active_ccorres)
       apply simp
      apply simp
     apply wp
     apply clarsimp
     apply assumption
    apply clarsimp
    apply (vcg exspec=vcpu_disable_modifies)
   apply (rule ccorres_return_Skip)
  apply (clarsimp, rule conjI)
   apply (fastforce dest: invs_cicd_arch_state' simp: valid_arch_state'_def vcpu_at_is_vcpu' ko_wp_at'_def split: option.splits)
  by (auto dest!: rf_sr_ksArchState_armHSCurVCPU simp: cur_vcpu_relation_def)+

lemma vcpu_switch_ccorres_Some:
  "ccorres dc xfdc
    (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj'
                     and valid_arch_state' and vcpu_at' v)
    ({s. new_' s = vcpu_Ptr v}) hs
        (vcpuSwitch (Some v)) (Call vcpu_switch_'proc)"
  supply if_cong[cong] option.case_cong[cong]
  apply (cinit lift: new_')
    (* v \<noteq> None *)
   apply simp
   apply (rule ccorres_pre_getCurVCPU)
   apply wpc
    (* v \<noteq> None & CurVCPU = None *)
    apply (rule ccorres_cond_true)
    apply (rule ccorres_cond_true)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_cond_false_seq)
    apply ccorres_rewrite
    apply (ctac add: vcpu_restore_ccorres)
      apply (rule_tac curv="Some (v, True)" in armHSCurVCPU_update_ccorres)
     apply wp
    apply clarsimp
    apply (vcg exspec=vcpu_restore_modifies)
    (* v \<noteq> None & CurVCPU \<noteq> None *)
   apply wpc
   apply (rename_tac ccurv cactive)
   apply (rule_tac R="\<lambda>s. (armHSCurVCPU \<circ> ksArchState) s = Some (ccurv, cactive)" in ccorres_cond)
     apply (clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU
                     simp: Collect_const_mem cur_vcpu_relation_def
                     split: option.splits)
    (* new \<noteq> CurVCPU or equivalently v \<noteq> ccurv *)
    apply (rule ccorres_cond_true)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_cond_true_seq)
    apply (ctac add: vcpu_save_ccorres)
      apply (ctac add: vcpu_restore_ccorres)
        apply (rule_tac curv="Some (v, True)" in armHSCurVCPU_update_ccorres)
       apply wp
      apply clarsimp
      apply (vcg exspec=vcpu_restore_modifies)
     apply (wpsimp wp: hoare_vcg_conj_lift vcpuSave_invs_no_cicd' vcpuSave_typ_at')
    apply clarsimp
    apply (vcg exspec=vcpu_save_modifies)
    (* new = CurVCPU or equivalently v = ccurv *)
   apply (unfold when_def)
   apply (rule_tac R="\<lambda>s. (ccurv = v) \<and> (armHSCurVCPU \<circ> ksArchState) s = Some (ccurv, cactive)"
            in ccorres_cond)
     apply (clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU
                     simp: Collect_const_mem cur_vcpu_relation_def from_bool_def
                     split: option.splits bool.splits)
    (* ccactive = false *)
    apply (rule ccorres_rhs_assoc)
    apply (ctac (no_vcg) add: isb_ccorres)
     apply (ctac (no_vcg) add: vcpu_enable_ccorres)
      apply (rule_tac v="(v, cactive)" in armHSCurVCPU_update_active_ccorres)
       apply simp
      apply simp
     apply wp
    apply (wpsimp wp: hoare_vcg_conj_lift vcpuSave_invs_no_cicd' vcpuSave_typ_at')
   (* ccactive =true *)
   apply (rule ccorres_return_Skip)
  (* last goal *)
  apply simp
  apply (rule conjI
         | clarsimp dest!: rf_sr_ksArchState_armHSCurVCPU
                     simp: Collect_const_mem cur_vcpu_relation_def
         | fastforce dest: invs_cicd_arch_state'  split: option.splits
                     simp: valid_arch_state'_def vcpu_at_is_vcpu' ko_wp_at'_def Collect_const_mem)+
  done

lemma vcpu_switch_ccorres:
  "ccorres dc xfdc
    (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj'
                     and valid_arch_state'
          and (case v of None \<Rightarrow> \<top> | Some new \<Rightarrow> vcpu_at' new))
    ({s. new_' s = option_to_ptr v \<comment> \<open>(case v of None \<Rightarrow> NULL | Some new \<Rightarrow> vcpu_Ptr new)\<close> }) hs
        (vcpuSwitch v) (Call vcpu_switch_'proc)"
  by (cases v; clarsimp simp: vcpu_switch_ccorres_None[simplified] vcpu_switch_ccorres_Some[simplified])


lemma invs_no_cicd_sym_hyp'[elim!]:
  "invs_no_cicd' s \<Longrightarrow> sym_refs (state_hyp_refs_of' s)"
  by (simp add: invs_no_cicd'_def valid_state'_def)

(* FIXME AARCH64 the above was above setVMRoot_ccorres on ARM_HYP, so things might be needed earlier *)

end

end
