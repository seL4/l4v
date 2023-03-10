(*
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

lemma unat_of_nat_pageBitsForSize [simp]:
  "unat (of_nat (pageBitsForSize x)::machine_word) = pageBitsForSize x"
  apply (subst unat_of_nat64)
   apply (rule order_le_less_trans, rule pageBitsForSize_le)
   apply (simp add: word_bits_def)
  apply simp
  done

lemma checkVPAlignment_ccorres:
  "ccorres (\<lambda>a c. if to_bool c then a = Inr () else a = Inl AlignmentError) ret__unsigned_long_'
           \<top>
           (UNIV \<inter> \<lbrace>sz = framesize_to_H \<acute>sz \<and> \<acute>sz < 3\<rbrace> \<inter> \<lbrace>\<acute>w = w\<rbrace>)
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
    apply (simp split: if_split add: to_bool_def)
   apply (clarsimp simp: mask_def unlessE_def throwError_def split: if_split)
   apply (rule ccorres_guard_imp)
     apply (rule ccorres_return_C)
       apply simp
      apply simp
     apply simp
    apply simp
   apply (simp split: if_split add: to_bool_def)
  apply (clarsimp split: if_split)
  apply (simp add: word_less_nat_alt)
  apply (rule order_le_less_trans, rule pageBitsForSize_le)
  apply simp
  done

lemma rf_asidTable:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; valid_arch_state' \<sigma>; idx \<le> mask asid_high_bits \<rbrakk>
     \<Longrightarrow> case riscvKSASIDTable (ksArchState \<sigma>)
                idx of
        None \<Rightarrow>
            index (riscvKSASIDTable_' (globals x)) (unat idx) =
               NULL
             | Some v \<Rightarrow>
                 index (riscvKSASIDTable_' (globals x)) (unat idx) = Ptr v \<and>
                 index (riscvKSASIDTable_' (globals x)) (unat idx) \<noteq> NULL"
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                             carch_state_relation_def
                             array_relation_def)
  apply (drule_tac x=idx in spec)+
  apply (clarsimp simp: mask_def split: option.split)
  apply (drule sym, simp)
  apply (simp add: option_to_ptr_def option_to_0_def)
  apply (clarsimp simp: invs'_def valid_state'_def valid_arch_state'_def
                        valid_asid_table'_def ran_def)
  done

lemma getKSASIDTable_ccorres_stuff:
  "\<lbrakk> invs' \<sigma>; (\<sigma>, x) \<in> rf_sr; idx' = unat idx;
             idx < 2 ^ asid_high_bits \<rbrakk>
     \<Longrightarrow> case riscvKSASIDTable (ksArchState \<sigma>)
                idx of
        None \<Rightarrow>
            index (riscvKSASIDTable_' (globals x))
                idx' =
               NULL
             | Some v \<Rightarrow>
                 index (riscvKSASIDTable_' (globals x))
                  idx' = Ptr v \<and>
                 index (riscvKSASIDTable_' (globals x))
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

lemma rf_sr_riscvKSASIDTable:
  "\<lbrakk> (s, s') \<in> rf_sr; n \<le> 2 ^ asid_high_bits - 1 \<rbrakk>
       \<Longrightarrow> index (riscvKSASIDTable_' (globals s')) (unat n)
               = option_to_ptr (riscvKSASIDTable (ksArchState s) n)"
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

definition
  vm_fault_type_from_H :: "vmfault_type \<Rightarrow> machine_word"
where
  "vm_fault_type_from_H fault \<equiv>
    case fault of
      vmfault_type.RISCVInstructionAccessFault \<Rightarrow> scast Kernel_C.RISCVInstructionAccessFault
    | vmfault_type.RISCVLoadAccessFault \<Rightarrow> scast Kernel_C.RISCVLoadAccessFault
    | vmfault_type.RISCVStoreAccessFault \<Rightarrow> scast Kernel_C.RISCVStoreAccessFault
    | vmfault_type.RISCVInstructionPageFault \<Rightarrow> scast Kernel_C.RISCVInstructionPageFault
    | vmfault_type.RISCVLoadPageFault \<Rightarrow> scast Kernel_C.RISCVLoadPageFault
    | vmfault_type.RISCVStorePageFault \<Rightarrow> scast Kernel_C.RISCVStorePageFault"

lemmas vm_fault_defs_C =
         Kernel_C.RISCVInstructionAccessFault_def
         Kernel_C.RISCVLoadAccessFault_def
         Kernel_C.RISCVStoreAccessFault_def
         Kernel_C.RISCVInstructionPageFault_def
         Kernel_C.RISCVLoadPageFault_def
         Kernel_C.RISCVStorePageFault_def

(* FIXME: automate this *)
lemma seL4_Fault_VMFault_new'_spec:
  "\<lbrace> \<lambda>s. s = \<sigma> \<rbrace> seL4_Fault_VMFault_new' addr FSR i
   \<lbrace> \<lambda>r s. s = \<sigma>
            \<and> seL4_Fault_VMFault_lift r = \<lparr>address_CL = addr, FSR_CL = FSR && mask 5, instructionFault_CL = i && mask 1\<rparr>
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

lemma returnVMFault_corres:
  "\<lbrakk> addr = addr'; i = i' && mask 1; fault = fault' && mask 5 \<rbrakk> \<Longrightarrow>
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
     apply (rule_tac F="seL4_Fault_VMFault_lift vmf = \<lparr>address_CL = addr, FSR_CL = fault && mask 5, instructionFault_CL = i && mask 1\<rparr>
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
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
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
   apply (rule corres_split[OF read_stval_ccorres[ac]])
      apply terminates_trivial
     apply (drule sym, clarsimp)
     apply (wpc; simp add: vm_fault_type_from_H_def vm_fault_defs_C
                           true_def false_def bind_assoc)
          apply (rule returnVMFault_corres;
                 clarsimp simp: exception_defs mask_twice lift_rv_def mask_def vmFaultTypeFSR_def)+
     apply wpsimp+
  done

lemma unat_asidLowBits [simp]:
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
  apply (erule_tac x="9+n" in allE) (*asid_low_bits*)
  apply (simp add: linorder_not_less)
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done

lemma ucast_asid_high_bits_is_shift:
  "asid_wf asid \<Longrightarrow> ucast (asid_high_bits_of (ucast asid)) = asid >> asid_low_bits"
  unfolding asid_wf_def
  apply (simp add: mask_def upper_bits_unset_is_l2p_64 [symmetric])
  apply (simp add: asid_high_bits_of_def mask_2pm1[symmetric] ucast_ucast_mask)
  using shiftr_mask_eq[where n=9 and x=asid, simplified]
  apply (simp add: asid_low_bits_def word_size asid_bits_def word_bits_def mask_def)
  apply word_bitwise
  apply simp
  done

lemma rf_sr_asidTable_None:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; asid_wf asid; valid_arch_state' \<sigma>  \<rbrakk> \<Longrightarrow>
  (index (riscvKSASIDTable_' (globals x)) (unat (asid >> asid_low_bits)) = ap_Ptr 0) =
  (riscvKSASIDTable (ksArchState \<sigma>) (ucast (asid_high_bits_of (ucast asid))) = None)"
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
  apply (simp add: RISCV64.ptrFromPAddr_def RISCV64.pptrBase_def pptrBaseOffset_def paddrBase_def
                   canonical_bit_def)
  done

lemma addrFromPPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile>  {s}
  Call addrFromPPtr_'proc
  \<lbrace>  \<acute>ret__unsigned_long =  (addrFromPPtr (ptr_val (pptr_' s)) ) \<rbrace>"
  apply vcg
  apply (simp add: addrFromPPtr_def RISCV64.pptrBase_def pptrBaseOffset_def paddrBase_def
                   canonical_bit_def)
  done

lemma corres_symb_exec_unknown_r:
  assumes "\<And>rv. corres_underlying sr nf nf' r P P' a (c rv)"
  shows "corres_underlying sr nf nf' r P P' a (unknown >>= c)"
  apply (simp add: unknown_def)
  apply (rule corres_symb_exec_r[OF assms]; wp select_inv no_fail_select)
  done

lemma isPageTablePTE_def2:
  "isPageTablePTE pte = (\<exists>ppn global. pte = PageTablePTE ppn global)"
  by (simp add: isPageTablePTE_def split: pte.splits)

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
     (auto simp: from_bool_def cpte_relation_def isPageTablePTE_def2 Let_def
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
  apply (cases pte; simp add: readable_from_vm_rights0 isPageTablePTE_def from_bool_def
                              cpte_relation_def writable_from_vm_rights_def)
  done

lemma ccorres_checkPTAt:
  "ccorres_underlying srel Ga rrel xf arrel axf P P' hs (a ()) c \<Longrightarrow>
   ccorres_underlying srel Ga rrel xf arrel axf
                      (\<lambda>s. page_table_at' pt s \<longrightarrow> P s) P' hs (checkPTAt pt >>= a) c"
  unfolding checkPTAt_def by (rule ccorres_stateAssert)

lemma pteAtIndex_ko[wp]:
  "\<lbrace>\<top>\<rbrace> pteAtIndex level pt vptr \<lbrace>\<lambda>pte. ko_at' pte (ptSlotIndex level pt vptr)\<rbrace>"
  unfolding pteAtIndex_def by (wpsimp wp: getPTE_wp)

lemma ptBitsLeft_bound:
  "level \<le> maxPTLevel \<Longrightarrow> ptBitsLeft level \<le> canonical_bit"
  by (simp add: ptBitsLeft_def bit_simps maxPTLevel_def canonical_bit_def)

lemma unat_of_nat_ptBitsLeft [simp]:
  "level \<le> maxPTLevel \<Longrightarrow> unat (of_nat (ptBitsLeft level)::machine_word) = ptBitsLeft level"
  apply (subst unat_of_nat64)
   apply (rule order_le_less_trans, erule ptBitsLeft_bound)
   apply (simp add: word_bits_def canonical_bit_def)
  apply simp
  done

lemma pte_at'_ptSlotIndex:
  "page_table_at' pt s \<Longrightarrow> pte_at' (ptSlotIndex level pt vptr) s"
  apply (simp add: ptSlotIndex_def ptIndex_def)
  apply (drule page_table_pte_atI'[where x="ucast (vptr >> ptBitsLeft level)"])
  apply (simp add: ucast_ucast_mask bit_simps)
  done

lemma ptTranslationBits_word_bits:
  "ptTranslationBits < LENGTH(machine_word_len)"
  by (simp add: bit_simps)

lemmas unat_and_mask_le_ptTrans = unat_and_mask_le[OF ptTranslationBits_word_bits]

lemma lookupPTSlotFromLevel_ccorres:
  defines
    "ptSlot_upd \<equiv>
       Guard ShiftError \<lbrace>ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C < 0x40\<rbrace>
         (Guard MemorySafety
           \<lbrace> (\<acute>vptr >> unat (ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C)) && 0x1FF = 0 \<or>
             array_assertion \<acute>pt (unat ((\<acute>vptr >> unat (ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C)) && 0x1FF))
                             (hrs_htd \<acute>t_hrs) \<rbrace>
           (\<acute>ret___struct_lookupPTSlot_ret_C :==
              ptSlot_C_update
                (\<lambda>_. \<acute>pt +\<^sub>p uint ((\<acute>vptr >> unat (ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C)) && 0x1FF))
                \<acute>ret___struct_lookupPTSlot_ret_C))"
  shows
    "ccorres (\<lambda>(bitsLeft,ptSlot) cr. bitsLeft = unat (ptBitsLeft_C cr) \<and> ptSlot_C cr = Ptr ptSlot)
     ret__struct_lookupPTSlot_ret_C_'
     (page_table_at' pt and (\<lambda>_. level \<le> maxPTLevel))
     (\<lbrace> ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C = of_nat (ptTranslationBits * level + ptBits) \<rbrace>
      \<inter> \<lbrace> \<acute>level = of_nat level \<rbrace> \<inter> \<lbrace> \<acute>pt = Ptr pt \<rbrace> \<inter> \<lbrace> \<acute>vptr = vptr \<rbrace>)
     (SKIP#hs)
     (lookupPTSlotFromLevel level pt vptr)
     (ptSlot_upd;;
      \<acute>ret__unsigned_long :== CALL isPTEPageTable(ptSlot_C \<acute>ret___struct_lookupPTSlot_ret_C);;
      WHILE \<acute>ret__unsigned_long \<noteq> 0 \<and> 0 < \<acute>level DO
        \<acute>level :== \<acute>level - 1;;
        \<acute>ret___struct_lookupPTSlot_ret_C :==
             ptBitsLeft_C_update (\<lambda>_. ptBitsLeft_C \<acute>ret___struct_lookupPTSlot_ret_C - 9)
                                 \<acute>ret___struct_lookupPTSlot_ret_C;;
         \<acute>pt :== CALL getPPtrFromHWPTE(ptSlot_C \<acute>ret___struct_lookupPTSlot_ret_C);;
         ptSlot_upd;;
         \<acute>ret__unsigned_long :== CALL isPTEPageTable(ptSlot_C \<acute>ret___struct_lookupPTSlot_ret_C)
      OD;;
      return_C ret__struct_lookupPTSlot_ret_C_'_update ret___struct_lookupPTSlot_ret_C_')"
proof (induct level arbitrary: pt)
  note unat_and_mask_le_ptTrans[simp] neq_0_unat[simp]

  have misc_simps[simp]:
    "pageBits = pt_bits"
    "of_nat pageBits = of_nat pt_bits"
    "pt_bits - 3 = ptTranslationBits"
    "unat (of_nat pt_bits::machine_word) = pt_bits"
    "\<And>x::machine_word. x * 8 = x << pte_bits"
    "0x1FF = (mask ptTranslationBits :: machine_word)"
    by (auto simp: bit_simps mask_def shiftl_t2n)

  case 0
  show ?case
    apply (simp only: ptSlot_upd_def lookupPTSlotFromLevel.simps(1))
    apply (cinitlift pt_' vptr_', simp only:)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_Guard_Seq)
     apply (rule ccorres_move_array_assertion_pt)
     apply (rule ccorres_symb_exec_r2)
       apply (rule ccorres_symb_exec_r2)
         apply (simp add: whileAnno_def)
         apply (rule ccorres_expand_while_iff_Seq[THEN iffD1])
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
    done

  case (Suc level)
  have [simp]:
    "Suc level \<le> maxPTLevel \<Longrightarrow>
     unat (of_nat ptTranslationBits +
           of_nat ptTranslationBits * of_nat level +
           of_nat pt_bits :: machine_word) =
     ptTranslationBits + ptTranslationBits * level + pt_bits"
    by (simp add: bit_simps word_less_nat_alt maxPTLevel_def unat_word_ariths unat_of_nat_eq)

  show ?case
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
    done
qed


lemma lookupPTSlot_ccorres:
  "ccorres (\<lambda>(bitsLeft,ptSlot) cr. bitsLeft = unat (ptBitsLeft_C cr) \<and> ptSlot_C cr = Ptr ptSlot)
     ret__struct_lookupPTSlot_ret_C_'
     (page_table_at' pt)
     (\<lbrace>\<acute>vptr = vptr  \<rbrace> \<inter> \<lbrace>\<acute>lvl1pt = Ptr pt \<rbrace>)
     hs
     (lookupPTSlot pt vptr)
     (Call lookupPTSlot_'proc)"
  apply (cinit lift: lvl1pt_')
   apply (rename_tac lvl1pt)
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
  apply (simp add: bit_simps maxPTLevel_def)
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
       (UNIV \<inter> \<lbrace>\<acute>asid___unsigned_long = asid\<rbrace> )
       []
       (findVSpaceForASID asid)
       (Call findVSpaceForASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid___unsigned_long_')
   apply (rule ccorres_assertE)+
   apply (rule ccorres_liftE_Seq)
   apply (simp add: liftME_def bindE_assoc)
   apply (rule ccorres_pre_gets_riscvKSASIDTable_ksArchState')
   apply (case_tac "asidTable (ucast (asid_high_bits_of (ucast asid)))")
    (* Case where the first look-up fails *)
    apply clarsimp
    apply (rule_tac P="valid_arch_state' and _" and P'=UNIV in ccorres_from_vcg_throws)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def bindE_def NonDetMonad.lift_def
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
     apply (rule_tac P="\<lambda>s. asidTable=riscvKSASIDTable (ksArchState s) \<and>
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
  done

lemma ccorres_pre_gets_riscvKSGlobalPT_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. riscvKSGlobalPT (ksArchState s) = rv  \<longrightarrow> P rv s))
                  (P' (ptr_val riscvKSGlobalPT_Ptr))
                  hs (gets (riscvKSGlobalPT \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply (drule rf_sr_riscvKSGlobalPT)
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
lemma ccorres_h_t_valid_riscvKSGlobalPT:
  "ccorres r xf P P' hs f (f' ;; g') \<Longrightarrow>
   ccorres r xf P P' hs f (Guard C_Guard {s'. s' \<Turnstile>\<^sub>c riscvKSGlobalPT_Ptr} f';; g')"
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

lemma addrFromKPPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
   Call addrFromKPPtr_'proc
   \<lbrace>\<acute>ret__unsigned_long = addrFromKPPtr (ptr_val (pptr_' s))\<rbrace>"
  apply vcg
  apply (simp add: addrFromKPPtr_def kernelELFBaseOffset_def
                   kernelELFBase_def kernelELFPAddrBase_def mask_def)
  done

lemma isValidVTableRoot_def2:
  "isValidVTableRoot cap =
   (\<exists>pt asid vref. cap = ArchObjectCap (PageTableCap pt (Some (asid,vref))))"
  unfolding isValidVTableRoot_def
  by (auto split: capability.splits arch_capability.splits option.splits)

lemma setVMRoot_ccorres:
  "ccorres dc xfdc
      (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' thread)
      (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr thread}) hs
      (setVMRoot thread) (Call setVMRoot_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: tcb_')
   apply (rule ccorres_move_array_assertion_tcb_ctes)
   apply (rule ccorres_move_c_guard_tcb_ctes)
   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv bit_simps asid_bits_def)
   apply (ctac, rename_tac vRootCap vRootCap')
     apply (rule ccorres_assert2)
     apply (csymbr, rename_tac vRootTag)
     apply (simp add: cap_get_tag_isCap_ArchObject2)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (subst will_throw_and_catch)
       apply (simp split: capability.split arch_capability.split option.split)
       apply (fastforce simp: isCap_simps)
      apply (rule ccorres_pre_gets_riscvKSGlobalPT_ksArchState[unfolded o_def])
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_h_t_valid_riscvKSGlobalPT)
      apply csymbr
      apply ccorres_rewrite
      apply (subst bind_return_unit)
      apply (ctac (no_vcg) add: setVSpaceRoot_ccorres)
       apply (simp flip: dc_def)
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
         apply (simp add: whenE_def throwError_def dc_def[symmetric], ccorres_rewrite)
         apply (rule ccorres_rhs_assoc)
         apply (rule ccorres_h_t_valid_riscvKSGlobalPT)
         apply csymbr
         apply (rule ccorres_pre_gets_riscvKSGlobalPT_ksArchState[unfolded comp_def])
         apply (rule ccorres_add_return2)
         apply (ctac (no_vcg) add: setVSpaceRoot_ccorres)
          apply (rule ccorres_return_void_C)
         apply (rule hoare_post_taut[where P=\<top>])
        apply (simp add: whenE_def returnOk_def flip: dc_def)
        apply (csymbr)
        apply (ctac (no_vcg) add: setVSpaceRoot_ccorres)
       apply (rule ccorres_cond_true_seq, simp add: dc_def[symmetric], ccorres_rewrite)
       apply (rule ccorres_rhs_assoc)
       apply (rule ccorres_h_t_valid_riscvKSGlobalPT)
       apply csymbr
       apply (rule ccorres_pre_gets_riscvKSGlobalPT_ksArchState[unfolded comp_def])
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
                        cap_page_table_cap_lift_def isCap_simps
                        to_bool_def mask_def isZombieTCB_C_def Let_def
                 elim!: ccap_relationE
                 split: if_split_asm cap_CL.splits)

lemma ccorres_seq_IF_False:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (IF False THEN x ELSE y FI ;; c) = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (y ;; c)"
  by simp

(* FIXME x64: needed? *)
lemma ptrFromPAddr_mask6_simp[simp]:
  "ptrFromPAddr ps && mask 6 = ps && mask 6"
  unfolding ptrFromPAddr_def pptrBase_def pptrBaseOffset_def RISCV64.pptrBase_def canonical_bit_def
             paddrBase_def
  by (subst add.commute, subst mask_add_aligned ; simp add: is_aligned_def)

(* FIXME: move *)
lemma register_from_H_bound[simp]:
  "unat (register_from_H v) < 35"
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
       (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>reg = register_from_H reg\<rbrace>
             \<inter> {s. w_' s = val}) []
       (asUser thread (setRegister reg val))
       (Call setRegister_'proc)"
  apply (cinit' lift: thread_' reg_' w_')
   apply (simp add: asUser_def dc_def[symmetric] split_def split del: if_split)
   apply (rule ccorres_pre_threadGet)
   apply (rule ccorres_Guard)
   apply (simp add: setRegister_def simpler_modify_def exec_select_f_singleton)
   apply (rule_tac P="\<lambda>tcb. (atcbContextGet o tcbArch) tcb = rv"
                in threadSet_ccorres_lemma2 [unfolded dc_def])
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
  register_from_H (RISCV64_H.msgRegisters ! n) = (index kernel_all_substitute.msgRegisters n)"
  apply (simp add: kernel_all_substitute.msgRegisters_def msgRegisters_unfold fupdate_def)
  apply (simp add: Arrays.update_def n_msgRegisters_def nth_Cons' split: if_split)
  done

(* usually when we call setMR directly, we mean to only set a registers, which will
   fit in actual registers *)
lemma setMR_as_setRegister_ccorres:
  notes dc_simp[simp del]
  shows
  "ccorres (\<lambda>rv rv'. rv' = of_nat offset + 1) ret__unsigned_'
      (tcb_at' thread and K (TCB_H.msgRegisters ! offset = reg \<and> offset < length msgRegisters))
      (UNIV \<inter> \<lbrace>\<acute>reg___unsigned_long = val\<rbrace>
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
     apply (clarsimp simp: dc_def return_def)
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
           (UNIV \<inter> \<lbrace>mi = message_info_to_H mi'\<rbrace>) hs
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
  apply (simp add: RISCV64_H.msgInfoRegister_def RISCV64.msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def Kernel_C.a1_def)
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

lemma checkMappingPPtr_pte_ccorres:
  assumes pre:
    "\<And>pte \<sigma>. \<Gamma> \<turnstile> {s. True \<and> (\<exists>pte'. cslift s (pte_Ptr pte_ptr) = Some pte' \<and> cpte_relation pte pte')
                            \<and> (\<sigma>, s) \<in> rf_sr}
           call1 ;; Cond S return_void_C Skip
       {s. (\<sigma>, s) \<in> rf_sr \<and> (isPagePTE pte) \<and> ptePPN pte << ptBits = addrFromPPtr pptr},
       {s. (\<sigma>, s) \<in> rf_sr \<and> \<not> ((isPagePTE pte) \<and> ptePPN pte << ptBits = addrFromPPtr pptr)}"
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
         apply (clarsimp simp: Bex_def isPagePTE_def in_monad split: pte.splits)
         apply (fastforce simp: Bex_def isPagePTE_def in_monad split: pte.splits)
       apply (wp empty_fail_getObject | simp)+
      apply (erule cmap_relationE1[OF rf_sr_cpte_relation])
       apply (erule ko_at_projectKO_opt)
      apply simp
     apply (wp empty_fail_getObject | simp add: objBits_simps bit_simps)+
  done

lemma ccorres_return_void_C':
  "ccorres_underlying rf_sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel dc) xfdc (\<lambda>_. True) UNIV (SKIP # hs) (return (Inl rv)) return_void_C"
  apply (rule ccorres_from_vcg_throws)
  apply (simp add: return_def)
  apply (rule allI, rule conseqPre, vcg)
  apply auto
  done

lemma multiple_add_less_nat:
  "a < (c :: nat) \<Longrightarrow> x dvd a \<Longrightarrow> x dvd c \<Longrightarrow> b < x
    \<Longrightarrow> a + b < c"
  apply (subgoal_tac "b < c - a")
   apply simp
  apply (erule order_less_le_trans)
  apply (rule dvd_imp_le)
   apply simp
  apply simp
  done

lemma findVSpaceForASID_page_table_at'_simple[wp]:
  notes checkPTAt_inv[wp del]
  shows "\<lbrace>\<top>\<rbrace> findVSpaceForASID asid
    \<lbrace>\<lambda>rv s. page_table_at' rv s\<rbrace>,-"
  apply (simp add: findVSpaceForASID_def)
   apply (wpsimp wp: getASID_wp simp: checkPTAt_def)
  done

lemmas ccorres_name_ksCurThread = ccorres_pre_getCurThread[where f="\<lambda>_. f'" for f',
    unfolded getCurThread_def, simplified gets_bind_ign]

lemma of_nat_pageBitsForSize:
  "unat x = pageBitsForSize sz \<Longrightarrow> x = of_nat (pageBitsForSize sz)" for x::machine_word
  by (drule sym, simp)

lemma checkMappingPPtr_def2:
  "checkMappingPPtr p pte =
   (if isPagePTE pte \<and> ptrFromPAddr (ptePPN pte << ptBits) = p
    then returnOk()
    else throw InvalidRoot)"
  unfolding checkMappingPPtr_def
  by (cases pte; simp add: isPagePTE_def unlessE_def cong: if_cong)

lemma pte_pte_invalid_new_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. True\<rbrace>
           Call pte_pte_invalid_new_'proc
           \<lbrace> pte_lift \<acute>ret__struct_pte_C = \<lparr>
               pte_CL.ppn_CL = 0,
               pte_CL.sw_CL = 0,
               pte_CL.dirty_CL = 0,
               pte_CL.accessed_CL = 0,
               pte_CL.global_CL = 0,
               pte_CL.user_CL = 0,
               pte_CL.execute_CL = 0,
               pte_CL.write_CL = 0,
               pte_CL.read_CL = 0,
               pte_CL.valid_CL = 0\<rparr>
           \<rbrace>"
  by (rule allI, rule conseqPre, vcg) (clarsimp simp: pte_lift_def fupdate_def)

lemma unmapPage_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>_. asid_wf asid))
      (\<lbrace> framesize_to_H \<acute>page_size = sz \<and> \<acute>page_size < 3 \<rbrace> \<inter>
       \<lbrace> \<acute>asid___unsigned_long = asid \<rbrace> \<inter> \<lbrace> \<acute>vptr = vptr \<rbrace> \<inter> \<lbrace> \<acute>pptr___unsigned_long = pptr \<rbrace>)
      hs
      (unmapPage sz asid vptr pptr) (Call unmapPage_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: page_size_' asid___unsigned_long_' vptr_' pptr___unsigned_long_')
   apply (simp add: ignoreFailure_liftM)
   apply (fold dc_def)
   apply (ctac add: findVSpaceForASID_ccorres)
      apply (rename_tac vspace find_ret)
      apply (rule ccorres_liftE_Seq)
      apply (simp add: Collect_False del: Collect_const)
      apply (ctac add: lookupPTSlot_ccorres)
        apply csymbr
        apply (simp (no_asm) add: split_def del: Collect_const)
        apply (rule ccorres_split_unless_throwError_cond[where Q=\<top> and Q'=\<top>])
           apply (clarsimp simp: of_nat_pageBitsForSize split: if_split)
          apply (simp add: throwError_def flip: dc_def)
          apply (rule ccorres_return_void_C)
         apply (simp add: dc_def[symmetric])
         apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
         apply (subst bindE_assoc[symmetric])
         apply (rule ccorres_splitE_novcg)
             apply (simp only: inl_rrel_inl_rrel)
             apply (rule checkMappingPPtr_pte_ccorres[simplified])
             apply (rule conseqPre, vcg exspec=isPTEPageTable_spec')
             apply (clarsimp simp: cpte_relation_def Let_def pte_lift_def isPagePTE_def
                                   typ_heap_simps isPageTablePTE_def bit_simps from_bool_def
                            split: if_split_asm pte.split_asm)
            apply (rule ceqv_refl)
           apply (simp add: unfold_checkMapping_return liftE_bindE
                            Collect_const[symmetric] dc_def[symmetric]
                       del: Collect_const)
           apply csymbr
           apply (rule ccorres_split_nothrow_novcg)
               apply (simp add: dc_def[symmetric] ptr_add_assertion_def split_def)
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
     apply (simp add: throwError_def flip: dc_def)
     apply (rule ccorres_return_void_C)
    apply wp
   apply (vcg exspec=findVSpaceForASID_modifies)
  apply clarsimp
  done

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
           capFVMRights_CL = vmrights_C, capFIsDevice_CL = device_C,
           capFMappedAddress_CL = mappedAddr_C\<rparr> \<and>
   sz = framesize_to_H sz_C \<and>
   d = to_bool device_C \<and>
   R = vmrights_to_H vmrights_C \<and>
   m = (if asid_C = 0 then None else Some (asid_C, mappedAddr_C))"
  supply if_cong[cong]
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits)
   apply (simp split: if_split_asm)
  apply (rename_tac fcap, case_tac fcap, simp)
  done

lemma performPageInvocationUnmap_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) o cteCap) ctSlot  and K (isFrameCap cap))
       (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
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
        apply (clarsimp simp: asidInvalid_def)
        apply (rule ccorres_call[where xf'=xfdc])
           apply datatype_schem
           apply (rule unmapPage_ccorres)
          apply simp
         apply simp
        apply simp
       apply (simp add: asidInvalid_def flip: dc_def)
       apply (rule ccorres_return_Skip)
      apply ceqv
     apply (simp add: liftM_def)
     apply (rule_tac Q="\<lambda>slotCap.  cte_wp_at' ((=) slotCap o cteCap) ctSlot and (\<lambda>_. isArchFrameCap slotCap)" and
                     Q'="\<lambda>slotCap slotCap_C. UNIV"
                     in ccorres_split_nothrow)
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
  done

lemma RISCVGetWriteFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace> Call RISCVGetWriteFromVMRights_'proc
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

lemma makeUserPTE_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace>
  Call makeUserPTE_'proc
  \<lbrace> if \<^bsup>s\<^esup>executable = 0 \<and> vmrights_to_H \<^bsup>s\<^esup>vm_rights = VMKernelOnly
    then
      pte_lift \<acute>ret__struct_pte_C = \<lparr>
        pte_CL.ppn_CL = 0,
        pte_CL.sw_CL = 0,
        pte_CL.dirty_CL = 0,
        pte_CL.accessed_CL = 0,
        pte_CL.global_CL = 0,
        pte_CL.user_CL = 0,
        pte_CL.execute_CL = 0,
        pte_CL.write_CL = 0,
        pte_CL.read_CL = 0,
        pte_CL.valid_CL = 0\<rparr>
    else
      pte_lift \<acute>ret__struct_pte_C = \<lparr>
        pte_CL.ppn_CL = (\<^bsup>s\<^esup>paddr >> 12) && mask 44,
        pte_CL.sw_CL = 0,
        pte_CL.dirty_CL = 1,
        pte_CL.accessed_CL = 1,
        pte_CL.global_CL = 0,
        pte_CL.user_CL = 1,
        pte_CL.execute_CL = \<^bsup>s\<^esup>executable && mask 1,
        pte_CL.write_CL = writable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
        pte_CL.read_CL = readable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
        pte_CL.valid_CL = 1\<rparr> \<rbrace>"
  supply if_cong[cong]
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: mask_def user_from_vm_rights_mask writable_from_vm_rights_mask
                        readable_from_vm_rights_mask)
  apply (rule conjI; clarsimp simp: readable_from_vm_rights_def writable_from_vm_rights_def
                              split: if_split vmrights.splits)
  done

lemma vmAttributesFromWord_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. True\<rbrace> Call vmAttributesFromWord_'proc
  \<lbrace> vm_attributes_lift \<acute>ret__struct_vm_attributes_C =
      \<lparr>  riscvExecuteNever_CL = \<^bsup>s\<^esup>w && 1 \<rparr>  \<rbrace>"
  by (vcg, simp add: vm_attributes_lift_def word_sless_def word_sle_def mask_def)

lemma cap_to_H_PTCap_tag:
  "\<lbrakk> cap_to_H cap = ArchObjectCap (PageTableCap p A);
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_page_table_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     apply (simp_all add: Let_def cap_lift_def split: if_splits)
  done

lemma cap_to_H_PTCap:
  "cap_to_H cap = ArchObjectCap (PageTableCap p asid) \<Longrightarrow>
  \<exists>cap_CL. cap = Cap_page_table_cap cap_CL \<and>
           to_bool (capPTIsMapped_CL cap_CL) = (asid \<noteq> None) \<and>
           (asid \<noteq> None \<longrightarrow> capPTMappedASID_CL cap_CL = fst (the asid) \<and>
                            capPTMappedAddress_CL cap_CL = snd (the asid)) \<and>
           capPTBasePtr_CL cap_CL = p"
  by (auto simp add: cap_to_H_def Let_def split: cap_CL.splits if_splits)

lemma cap_lift_PTCap_Base:
  "\<lbrakk> cap_to_H cap_cl = ArchObjectCap (PageTableCap p asid);
     cap_lift cap_c = Some cap_cl \<rbrakk>
  \<Longrightarrow> p = capPTBasePtr_CL (cap_page_table_cap_lift cap_c)"
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

lemma canonical_address_page_table_at':
  "\<lbrakk>page_table_at' p s; pspace_canonical' s\<rbrakk> \<Longrightarrow> canonical_address p"
  apply (clarsimp simp: page_table_at'_def)
  apply (drule_tac x=0 in spec, clarsimp simp: bit_simps typ_at_to_obj_at_arches)
  apply (erule (1) obj_at'_is_canonical)
  done

lemma page_table_at'_array_assertion:
  assumes "(s,s') \<in> rf_sr"
  assumes "page_table_at' pt s"
  assumes "n \<le> 2^ptTranslationBits" "0 < n"
  shows "array_assertion (pte_Ptr pt) n (hrs_htd (t_hrs_' (globals s')))"
  using assms
  by (fastforce simp: bit_simps
                intro: array_assertion_abs_pt[where x="\<lambda>_. (1::nat)", simplified, rule_format])

lemma page_table_at'_array_assertion_weak[unfolded ptTranslationBits_def, simplified]:
  assumes "(s,s') \<in> rf_sr"
  assumes "page_table_at' pt s"
  assumes "n < 2^(ptTranslationBits-1)"
  shows "array_assertion (pte_Ptr pt) ((unat (2^(ptTranslationBits-1) + of_nat n::machine_word)))
                         (hrs_htd (t_hrs_' (globals s')))"
  using assms
  by (fastforce intro: page_table_at'_array_assertion
                simp: unat_add_simple ptTranslationBits_def word_bits_def unat_of_nat)

lemma page_table_at'_array_assertion_strong[unfolded ptTranslationBits_def, simplified]:
  assumes "(s,s') \<in> rf_sr"
  assumes "page_table_at' pt s"
  assumes "n < 2^(ptTranslationBits-1)"
  shows "array_assertion (pte_Ptr pt) (Suc (unat (2^(ptTranslationBits-1) + of_nat n::machine_word)))
                         (hrs_htd (t_hrs_' (globals s')))"
  using assms
  by (fastforce intro: page_table_at'_array_assertion
                simp: unat_add_simple ptTranslationBits_def word_bits_def unat_of_nat)

lemma copyGlobalMappings_ccorres:
  "ccorres dc xfdc
           (page_table_at' pt and valid_arch_state')
           (UNIV \<inter> {s. newLvl1pt_' s = Ptr pt}) []
           (copyGlobalMappings pt) (Call copyGlobalMappings_'proc)"
proof -
  have ptIndex_maxPTLevel_pptrBase:
    "ptIndex maxPTLevel RISCV64.pptrBase = 0x100"
    by (simp add: ptIndex_def maxPTLevel_def ptBitsLeft_def pageBits_def ptTranslationBits_def
                  RISCV64.pptrBase_def canonical_bit_def mask_def)
  let ?enum = "\<lambda>n. [0x100.e.0x1FF::machine_word] ! n << 3"
  have enum_rewrite:
    "\<And>n. n < 256 \<Longrightarrow> ?enum n = 0x800 + of_nat n * 8"
    by (auto simp: upto_enum_word_nth word_shiftl_add_distrib shiftl_t2n)
  show ?thesis
    apply (cinit lift: newLvl1pt_' simp: ptIndex_maxPTLevel_pptrBase ptTranslationBits_def)
     apply (rule ccorres_pre_gets_riscvKSGlobalPT_ksArchState, rename_tac globalPT)
     apply (rule ccorres_rel_imp[where r=dc, OF _ dc_simp])
     apply (clarsimp simp: whileAnno_def objBits_simps bit_simps RISCV64.pptrBase_def mask_def)
     apply (rule ccorres_h_t_valid_riscvKSGlobalPT)
     apply csymbr
     apply csymbr
     apply clarsimp
     apply (rule_tac F="\<lambda>n s. globalPT = riscvKSGlobalPT (ksArchState s) \<and> page_table_at' pt s \<and>
                              page_table_at' globalPT s"
                 and i="0x100"
              in ccorres_mapM_x_while'
            ; clarsimp simp: word_bits_def)
       apply (rule ccorres_guard_imp2)
        apply (rule ccorres_pre_getObject_pte, rename_tac pte)
        apply (simp add: storePTE_def)
        apply (rule_tac P="\<lambda>s. page_table_at' pt s \<and>
                               page_table_at' (riscvKSGlobalPT (ksArchState s)) s \<and>
                               ko_at' pte (riscvKSGlobalPT (ksArchState s) + ?enum n) s"
                    and P'="\<lbrace>\<acute>i = 0x100 + of_nat n \<rbrace>"
                 in setObject_ccorres_helper)
          apply (rule conseqPre, vcg, clarsimp)
          apply (prop_tac "(0x100::machine_word) + of_nat n \<noteq> 0")
           apply unat_arith
           apply (simp add: unat_of_nat)
          apply clarsimp
          apply (frule (2) page_table_at'_array_assertion_weak)
          apply (frule (2) page_table_at'_array_assertion_strong)
          apply (frule rf_sr_riscvKSGlobalPT, clarsimp)
          apply (frule (2) page_table_at'_array_assertion_weak[where pt="symbol_table s" for s])
          apply (frule (2) page_table_at'_array_assertion_strong[where pt="symbol_table s" for s])
          apply simp
          apply (rule cmap_relationE1[OF rf_sr_cpte_relation], assumption,
                 erule_tac ko=ko' in ko_at_projectKO_opt)
          apply (rule cmap_relationE1[OF rf_sr_cpte_relation], assumption,
                 erule_tac ko=pte in ko_at_projectKO_opt)
          apply (clarsimp simp: enum_rewrite typ_heap_simps' heap_access_Array_element)
          apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
          apply (clarsimp simp: typ_heap_simps update_pte_map_tos)
          apply (rule conjI)
           apply (clarsimp simp: cpspace_relation_def typ_heap_simps
                                 update_pte_map_tos update_pte_map_to_ptes
                                 carray_map_relation_upd_triv)
           subgoal by (erule (2) cmap_relation_updI; simp)
          subgoal by (clarsimp simp: carch_state_relation_def cmachine_state_relation_def)
         apply simp
        apply (simp add: objBits_simps)
       apply clarsimp
      apply (rule conseqPre, vcg, clarsimp)
     apply wp
    apply (clarsimp simp: valid_arch_state'_def valid_global_pts'_def riscvKSGlobalPT_def)
    apply (erule_tac x=maxPTLevel in allE, force)
    done
qed

lemma performASIDPoolInvocation_ccorres:
  notes option.case_cong_weak [cong]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' (isPTCap' o cteCap) ctSlot and asid_pool_at' poolPtr
        and K (asid_wf asid))
       (UNIV \<inter> \<lbrace>\<acute>poolPtr = Ptr poolPtr\<rbrace> \<inter> \<lbrace>\<acute>asid___unsigned_long = asid\<rbrace> \<inter> \<lbrace>\<acute>vspaceCapSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performASIDPoolInvocation (Assign asid poolPtr ctSlot)))
       (Call performASIDPoolInvocation_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp K_def)
  apply (rule ccorres_gen_asm)
  apply (cinit lift: poolPtr_' asid___unsigned_long_' vspaceCapSlot_')
   apply (rule_tac Q="\<lambda>slotCap.  valid_arch_state' and valid_objs' and
                                 cte_wp_at' ((=) slotCap o cteCap) ctSlot and
                                 (\<lambda>_. isPTCap' slotCap \<and> capPTBasePtr (capCap slotCap) \<noteq> 0)" and
                  Q'="\<lambda>slotCap slotCap_C. UNIV"
                  in ccorres_split_nothrow)
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
  done

lemma pte_case_isInvalidPTE:
  "(case pte of InvalidPTE \<Rightarrow> P | _ \<Rightarrow> Q)
     = (if isInvalidPTE pte then P else Q)"
  by (cases pte, simp_all add: isInvalidPTE_def)

lemma ccap_relation_page_table_mapped_asid:
  "ccap_relation (ArchObjectCap (PageTableCap p (Some (asid, vspace)))) cap
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
  done

end

end
