(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory VSpace_C
imports TcbAcc_C CSpace_C PSpace_C TcbQueue_C
begin

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

local_setup
  \<open>AutoCorresModifiesProofs.new_modifies_rules "../c/build/$L4V_ARCH/kernel_all.c_pp"\<close>

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

lemma vspace_at_asid_cross_over:
  "\<lbrakk> vspace_at_asid' pm asid s; asid \<le> mask asid_bits;
          (s, s') \<in> rf_sr\<rbrakk>
      \<Longrightarrow> \<exists>apptr ap. index (riscvKSASIDTable_' (globals s')) (unat (asid >> asid_low_bits))
                     = (ap_Ptr apptr) \<and> cslift s' (ap_Ptr apptr) = Some (asid_pool_C.asid_pool_C ap)
                  \<and> is_aligned pm ptBits
                  \<and> array_assertion (pt_Ptr pm) 512 (hrs_htd (t_hrs_' (globals s')))"
  apply (clarsimp simp: vspace_at_asid'_def)
  sorry (* FIXME RISCV unclear if useful in current form
  apply (subgoal_tac "asid >> asid_low_bits \<le> 2 ^ asid_high_bits - 1")
   prefer 2
   apply (simp add: asid_high_bits_word_bits)
   apply (rule shiftr_less_t2n)
   apply (simp add: mask_def)
   apply (simp add: asid_low_bits_def asid_high_bits_def asid_bits_def)
  apply (simp add: rf_sr_x86KSASIDTable)
  apply (subgoal_tac "ucast (asid_high_bits_of asid) = asid >> asid_low_bits")
   prefer 2
   apply (simp add: asid_high_bits_of_def ucast_ucast_mask asid_high_bits_def[symmetric])
   apply (subst mask_eq_iff_w2p, simp add: asid_high_bits_def word_size)
   apply (rule shiftr_less_t2n)
   apply (simp add: mask_def, simp add: asid_bits_def asid_low_bits_def asid_high_bits_def)
  apply (simp add: option_to_ptr_def option_to_0_def)
  apply (rule cmap_relationE1 [OF rf_sr_cpspace_asidpool_relation],
         assumption, erule ko_at_projectKO_opt)
  apply (clarsimp simp: casid_pool_relation_def array_relation_def
                 split: asid_pool_C.split_asm)
  apply (apply_conjunct \<open>solves \<open>simp add: page_map_l4_at'_def\<close>\<close>)
  apply (drule spec, drule mp, rule word_and_mask_le_2pm1[of asid])
  using page_map_l4_at'_array_assertion
  by (simp add: asid_map_relation_def bit_simps asid_bits_defs asid_bits_of_defs ucast_ucast_mask
         split: option.splits asid_map_CL.splits)
  *)

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
   apply (rule corres_split[OF _ read_sbadaddr_ccorres[ac]], drule sym, clarsimp)
      apply (wpc; simp add: vm_fault_type_from_H_def vm_fault_defs_C
                            true_def false_def bind_assoc)
           apply (rule returnVMFault_corres;
                  clarsimp simp: exception_defs mask_twice lift_rv_def mask_def vmFaultTypeFSR_def)+
     apply (wpsimp simp: mask_def | terminates_trivial)+
  done

lemma unat_asidLowBits [simp]:
  "unat Kernel_C.asidLowBits = asidLowBits"
  by (simp add: asidLowBits_def Kernel_C.asidLowBits_def asid_low_bits_def)

(* FIXME RISCV: this is more complex than expected due to typ asid being 64 word and not matching
   the 16 word that asid_high_bits_of etc. require
   When we need to use this lemma, we also get a 64-bit asid, so the entire cast chain
   looks something like 64\<rightarrow>16\<rightarrow>7\<rightarrow>64

   this lemma was only used once, in findVSpaceForASID_ccorres
*)
lemma rf_sr_asidTable_None:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; (asid :: asid) && mask asid_bits = asid; valid_arch_state' \<sigma>  \<rbrakk> \<Longrightarrow>
  (index (riscvKSASIDTable_' (globals x)) (unat (asid >> asid_low_bits)) = ap_Ptr 0) =
  (riscvKSASIDTable (ksArchState \<sigma>) (ucast (asid_high_bits_of (ucast asid))) = None)"
  apply (simp add: asid_high_bits_of_def ucast_ucast_mask2 is_down)
  sorry (* FIXME RISCV: not clear if this is useful, and the chain of casting is painful
  apply (subgoal_tac "(UCAST(64 \<rightarrow> 16) asid >> asid_low_bits) && mask 7 = UCAST(64 \<rightarrow> 16) asid >> asid_low_bits")(*asid_high_bits*)
   prefer 2
   apply (rule word_eqI)
   apply (subst (asm) bang_eq)
   apply (simp add: word_size nth_shiftr asid_bits_def asid_low_bits_def)
   apply (case_tac "n < 7", simp) (*asid_high_bits*)
   apply (clarsimp simp: linorder_not_less)
   apply (erule_tac x="n+9" in allE) (*asid_low_bits*)
   apply simp
   subgoal sorry
  (* FIXME RISCV: this is due to typ asid being 64 word and not matching the 16 word that
     asid_high_bits_of etc. require *)
  apply (simp add: ucast_ucast_mask2 is_down)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)
  apply (simp add: array_relation_def option_to_0_def)
  apply (erule_tac x="ucast (UCAST(64 \<rightarrow> 16) asid >> asid_low_bits)" in allE)
  apply (erule impE)
   prefer 2
   apply (drule sym [where t="index a b" for a b])
   apply (simp add: option_to_0_def option_to_ptr_def split: option.splits)
   apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def ran_def)
  apply (simp add: and_mask_eq_iff_le_mask)
  apply (simp add: asid_high_bits_def mask_def word_le_nat_alt)
  done
  *)

lemma leq_asid_bits_shift:
  "x \<le> mask asid_bits \<Longrightarrow> (x::machine_word) >> asid_low_bits \<le> mask asid_high_bits"
  apply (rule word_leI)
  apply (simp add: nth_shiftr word_size)
  apply (rule ccontr)
  apply (clarsimp simp: linorder_not_less asid_high_bits_def asid_low_bits_def)
  apply (simp add: mask_def)
  apply (simp add: upper_bits_unset_is_l2p_64 [symmetric])
  apply (simp add: asid_bits_def word_bits_def)
  apply (erule_tac x="n+9" in allE) (*asid_low_bits*)
  apply (simp add: linorder_not_less)
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done

lemma ucast_asid_high_bits_is_shift:
  "asid \<le> mask asid_bits \<Longrightarrow> ucast (asid_high_bits_of asid) = (asid >> asid_low_bits)"
  apply (simp add: mask_def upper_bits_unset_is_l2p_64 [symmetric])
  apply (simp add: asid_high_bits_of_def mask_2pm1[symmetric] ucast_ucast_mask)
  using shiftr_mask_eq[where n=9 and x=asid, simplified]
  apply (simp add: asid_low_bits_def word_size)
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
  apply (simp add: RISCV64.ptrFromPAddr_def RISCV64.pptrBase_def baseOffset_def pAddr_base_def
                   canonical_bit_def)
  done

lemma addrFromPPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile>  {s}
  Call addrFromPPtr_'proc
  \<lbrace>  \<acute>ret__unsigned_long =  (addrFromPPtr (ptr_val (pptr_' s)) ) \<rbrace>"
  apply vcg
  apply (simp add: addrFromPPtr_def RISCV64.pptrBase_def baseOffset_def pAddr_base_def
                   canonical_bit_def)
  done

lemma corres_symb_exec_unknown_r:
  assumes "\<And>rv. corres_underlying sr nf nf' r P P' a (c rv)"
  shows "corres_underlying sr nf nf' r P P' a (unknown >>= c)"
  apply (simp add: unknown_def)
  apply (rule corres_symb_exec_r[OF assms]; wp select_inv non_fail_select)
  done

(* FIXME RISCV: we may need PT versions of these, keeping these for now
lemma lookupPML4Slot'_spec:
  "\<lbrace> \<lambda>s. s = \<sigma> \<and> array_assertion pm (2 ^ ptTranslationBits) (hrs_htd (t_hrs_' s)) \<rbrace>
    lookupPML4Slot' pm vptr
   \<lbrace> \<lambda>r s. s = \<sigma> \<and> r = pml4e_Ptr (lookupPML4Slot (ptr_val pm) vptr) \<rbrace>"
  apply (rule hoare_weaken_pre, rule hoare_strengthen_post)
    apply (rule autocorres_transfer_spec_no_modifies
                  [where cs="undefined\<lparr>globals := \<sigma>, pml4_' := pm, vptr_' := vptr\<rparr>"
                     and P="\<lambda>s. array_assertion (pml4_' s) (2 ^ ptTranslationBits) (hrs_htd (t_hrs_' (globals s)))",
                   OF lookupPML4Slot'_def lookupPML4Slot_spec lookupPML4Slot_modifies])
       by auto

lemma no_fail_lookupPML4Slot':
  "no_fail (\<lambda>s. array_assertion pm (2 ^ ptTranslationBits) (hrs_htd (t_hrs_' s))) (lookupPML4Slot' pm vptr)"
  apply (rule terminates_spec_no_fail[OF lookupPML4Slot'_def lookupPML4Slot_spec]; clarsimp)
  apply terminates_trivial
  done

lemmas corres_symb_exec_lookupPML4Slot' =
  valid_spec_to_corres_gen_symb_exec_r[OF lookupPML4Slot'_spec no_fail_lookupPML4Slot']

(* FIXME: automate this. *)
lemma pml4e_ptr_get_present'_spec:
  "\<lbrace> \<lambda>s. s = \<sigma> \<and> s \<Turnstile>\<^sub>g pml4e_ptr \<rbrace>
    pml4e_ptr_get_present' pml4e_ptr
   \<lbrace> \<lambda>r s. s = \<sigma> \<and> r = pml4e_CL.present_CL (pml4e_lift (the (gslift s pml4e_ptr))) \<rbrace>"
  apply (rule hoare_weaken_pre, rule hoare_strengthen_post)
    apply (rule autocorres_transfer_spec_no_modifies
                  [where cs="undefined\<lparr>globals := \<sigma>, pml4e_ptr_' := pml4e_ptr\<rparr>"
                     and P="\<lambda>s. s \<Turnstile>\<^sub>c pml4e_ptr_' s",
                   OF pml4e_ptr_get_present'_def pml4e_ptr_get_present_spec
                      pml4e_ptr_get_present_modifies])
      by (auto dest: spec[where x="undefined\<lparr>globals := \<sigma>\<rparr>"])

lemma pml4e_ptr_get_present'_no_fail:
  "no_fail (\<lambda>s. s \<Turnstile>\<^sub>g pml4e_ptr) (pml4e_ptr_get_present' pml4e_ptr)"
  apply (rule terminates_spec_no_fail[OF pml4e_ptr_get_present'_def pml4e_ptr_get_present_spec]; clarsimp)
  apply terminates_trivial
  done

lemmas corres_symb_exec_pml4e_ptr_get_present' =
  valid_spec_to_corres_symb_exec_r[OF pml4e_ptr_get_present'_spec pml4e_ptr_get_present'_no_fail]
*)

(* FIXME RISCV: ptrFromPAddr' does not appear to be defined anywhere, yet it exists on X64
                This is potentially useful if we can figure out what it is
lemma ptrFromPAddr'_spec:
  "\<lbrace> \<lambda>s. s = \<sigma> \<rbrace>
    ptrFromPAddr' paddr
   \<lbrace> \<lambda>r s. s = \<sigma> \<and> r = Ptr (ptrFromPAddr paddr) \<rbrace>"
  apply (rule hoare_weaken_pre, rule hoare_strengthen_post)
    apply (rule autocorres_transfer_spec_no_modifies
                  [where cs="undefined\<lparr>globals := \<sigma>, paddr_' := paddr\<rparr>" and P=\<top>,
                   OF ptrFromPAddr'_def ptrFromPAddr_spec ptrFromPAddr_modifies])
      by (auto dest: spec[where x="undefined\<lparr>globals := \<sigma>\<rparr>"])

lemma ptrFromPAddr'_no_fail:
  "no_fail \<top> (ptrFromPAddr' paddr)"
  apply (rule terminates_spec_no_fail'[OF ptrFromPAddr'_def ptrFromPAddr_spec]; clarsimp)
  apply terminates_trivial
  done

lemmas corres_symb_exec_ptrFromPAddr' =
  valid_spec_to_corres_gen_symb_exec_r'[OF ptrFromPAddr'_spec ptrFromPAddr'_no_fail]

(* Move near rf_sr_cpml4e_relation. *)
lemma cstate_relation_cpml4e_relation:
  "cstate_relation s s' \<Longrightarrow>
    cmap_relation (map_to_pml4es (ksPSpace s)) (gslift s') pml4e_Ptr cpml4e_relation"
  by (clarsimp simp: cstate_relation_def Let_def cpspace_relation_def)
*)

(* FIXME RISCV: this is a first stab at a formulation *)
lemma lookupPTSlot_ccorres:
  "ccorres (\<lambda>(bitsLeft,ptSlot) cr. bitsLeft = unat (ptBitsLeft_C cr) \<and> (ptSlot_C cr) = Ptr ptSlot)
     ret___struct_lookupPTSlot_ret_C_'
     (page_table_at' pt)
     (\<lbrace>\<acute>lvl1pt = Ptr pt \<rbrace> \<inter> \<lbrace>\<acute>vptr = vptr  \<rbrace>)
     hs
     (lookupPTSlot pt vptr)
     (Call lookupPTSlot_'proc)"
  apply (cinit lift: lvl1pt_' vptr_')
   apply (rename_tac vptr' root_pt)
   sorry (* FIXME RISCV: this one is completely different from before and involves a loop
   apply (simp add: liftE_bindE pde_case_isPageTablePDE)
   apply (ctac add: lookupPDSlot_ccorres)
      apply (rename_tac pde_ptr lookup_ret, case_tac lookup_ret, clarsimp)
      apply (rule ccorres_pre_getObject_pde, rename_tac pde)
      apply (csymbr, rename_tac page_size, rule ccorres_abstract_cleanup)
      apply (rule ccorres_rhs_assoc2)
      apply (rule_tac ccorres_symb_exec_r)
        apply (rule ccorres_if_lhs)
         apply (rule ccorres_cond_false)
         apply (simp add: bind_liftE_distrib liftE_bindE returnOk_liftE[symmetric])
         apply (rule ccorres_stateAssert)
         apply (rule_tac P="page_table_at' (ptrFromPAddr (pdeTable pde))
                              and ko_at' pde pde_ptr
                              and K (isPageTablePDE pde)"
                     and P'=UNIV
                  in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: returnOk_def return_def, rename_tac s s')
         apply (frule (1) page_table_at_rf_sr, clarsimp, rename_tac pt')
         apply (rule cmap_relationE1[OF rf_sr_cpde_relation], assumption,
                erule ko_at_projectKO_opt, rename_tac pdpte')
         apply (clarsimp simp: typ_heap_simps cpde_relation_def Let_def isPageTablePDE_def
                        split: pde.splits,
                rename_tac pt_ptr ac cd wt xd rights)
         apply (rule context_conjI, simp add: pde_lift_def Let_def split: if_splits, intro imp_ignore)
         apply (clarsimp simp: pde_lift_def pde_pde_pt_lift_def Let_def pde_tag_defs)
         apply (subst array_ptr_valid_array_assertionI[OF h_t_valid_clift], assumption, simp)
          apply (rule unat_le_helper[OF order_trans[OF word_and_le1]], simp)
         apply (simp add: lookup_pt_slot_no_fail_def getPTIndex_def mask_def bit_simps shiftl_t2n)
        apply (rule ccorres_cond_true)
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: throwError_def return_def syscall_error_rel_def)
        apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
        apply (simp add: lookup_fault_missing_capability_lift mask_def bit_simps)
       apply vcg
      apply (rule conseqPre, vcg, clarsimp)
     apply (ccorres_rewrite, rename_tac lookupPDSlot_errstate)
     apply (rule_tac P=\<top> and P'="{s. lookupPDSlot_errstate = errstate s}"
              in ccorres_from_vcg_throws)
     apply (rule allI, rule conseqPre, vcg, clarsimp simp: throwError_def return_def)
    apply (clarsimp, wp)
   apply (vcg exspec=lookupPDSlot_modifies)
  apply clarsimp
  apply (frule h_t_valid_clift; simp)
  apply (strengthen imp_ignore[where A="Ex P" for P])
  apply (clarsimp simp: cpde_relation_def isPageTablePDE_def Let_def
                        pde_lift_def pde_pde_pt_lift_def pde_tag_defs
                 split: X64_H.pde.splits if_splits)
  done
  *)

abbreviation
  "findVSpaceForASID_xf \<equiv> liftxf errstate findVSpaceForASID_ret_C.status_C findVSpaceForASID_ret_C.vspace_root_C ret__struct_findVSpaceForASID_ret_C_'"

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

(* FIXME: move *)
lemma ccorres_from_vcg_throws_nofail:
  "\<forall>\<sigma>. \<Gamma>\<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> srel} c {},
  {s. \<not>snd (a \<sigma>) \<longrightarrow> (\<exists>(rv, \<sigma>')\<in>fst (a \<sigma>). (\<sigma>', s) \<in> srel \<and> arrel rv (axf s))} \<Longrightarrow>
  ccorres_underlying srel \<Gamma> r xf arrel axf P P' (SKIP # hs) a c"
  apply (rule ccorresI')
  apply (drule_tac x = s in spec)
  apply (drule hoare_sound)
  apply (simp add: HoarePartialDef.valid_def cvalid_def)
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (drule spec, drule spec, drule (1) mp)
    apply (clarsimp dest!: exec_handlers_SkipD
                     simp: split_def unif_rrel_simps elim!: bexI [rotated])
   apply clarsimp
   apply (drule spec, drule spec, drule (1) mp)
   apply clarsimp
  apply simp
  done

lemma findVSpaceForASID_ccorres:
  "ccorres
       (lookup_failure_rel \<currency> (\<lambda>pteptrc pteptr. pteptr = pte_Ptr pteeptrc))
       findVSpaceForASID_xf
       (valid_arch_state' and no_0_obj' and (\<lambda>_. asid_wf asid))
       (UNIV \<inter> \<lbrace>\<acute>asid = asid\<rbrace> )
       []
       (findVSpaceForASID asid)
       (Call findVSpaceForASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_')
   apply (rule ccorres_assertE)+
   apply (rule ccorres_liftE_Seq)
   apply (simp add: liftME_def bindE_assoc)
   apply (rule ccorres_pre_gets_riscvKSASIDTable_ksArchState')
   apply (case_tac "asidTable (ucast (asid_high_bits_of (ucast asid)))")
    (* Case where the first look-up fails *)
    apply clarsimp
    sorry (* FIXME RISCV: proof will be somewhat different
    apply (rule_tac P="valid_arch_state' and _" and P'=UNIV in ccorres_from_vcg_throws)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def bindE_def NonDetMonad.lift_def
                          EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def
                          lookup_fault_lift_invalid_root Kernel_C.asidLowBits_def)
    apply (frule rf_sr_asidTable_None[where asid=asid, THEN iffD2])
           simp add: asid_wf_def3, assumption, assumption)
    apply (fastforce simp: asid_map_asid_map_none_def asid_map_asid_map_vspace_def asid_wf_def2
                           Kernel_C.asidLowBits_def asid_shiftr_low_bits_less)
  (* Case where the first look-up succeeds *)
   apply clarsimp
   apply (rule ccorres_liftE_Seq)
   apply (rule ccorres_guard_imp)
     apply (rule ccorres_pre_getObject_asidpool)
     apply (rename_tac asidPool)
     apply (case_tac "inv ASIDPool asidPool (ucast (asid_low_bits_of asid)) = Some 0")
      apply (clarsimp simp: ccorres_fail')
     apply (rule_tac P="\<lambda>s. asidTable=x64KSASIDTable (ksArchState s) \<and>
                            valid_arch_state' s \<and> (asid_wf asid)"
                 and P'="{s'. (\<exists>ap'. cslift s' (ap_Ptr (the (asidTable (ucast (asid_high_bits_of asid)))))
                                               = Some ap' \<and> casid_pool_relation asidPool ap')}"
                  in ccorres_from_vcg_throws_nofail)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: ucast_asid_high_bits_is_shift asid_wf_def2)
     apply (frule_tac idx="(asid >> asid_low_bits)" in rf_asidTable, assumption,
                      simp add: leq_asid_bits_shift)
     apply (clarsimp simp: typ_heap_simps)
     apply (case_tac asidPool, clarsimp simp: inv_def)
     apply (simp add: casid_pool_relation_def)
     apply (case_tac ap', simp)
     apply (simp add: array_relation_def)
     apply (erule_tac x="(asid && 2 ^ asid_low_bits - 1)" in allE)
     apply (simp add: word_and_le1 mask_def option_to_ptr_def option_to_0_def
                      asid_shiftr_low_bits_less asid_low_bits_of_p2m1_eq)
     apply (rename_tac "fun" array)
     apply (case_tac "fun (asid && 2 ^ asid_low_bits - 1)", clarsimp)
      apply (clarsimp simp: throwError_def return_def EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
      apply (simp add: lookup_fault_lift_invalid_root Kernel_C.asidLowBits_def)
      apply (rule conjI)
       apply (simp add: asid_low_bits_def asid_bits_def)
       apply word_bitwise
      apply (clarsimp simp: asid_map_relation_def asid_map_lift_def
                             asid_map_asid_map_none_def asid_map_asid_map_vspace_def)
     apply (clarsimp simp: Kernel_C.asidLowBits_def)
     apply (rule conjI)
      apply (simp add: asid_low_bits_def asid_bits_def)
      apply word_bitwise
     apply clarsimp
     apply (subgoal_tac "asid_map_get_tag (array.[unat (asid && 2 ^ asid_low_bits - 1)]) =
                         SCAST(32 signed \<rightarrow> 64) asid_map_asid_map_vspace")
      prefer 2
      apply (rule classical)
      apply (fastforce simp: asid_map_relation_def asid_map_lift_def split: if_splits)
     apply (fastforce simp: returnOk_def return_def
                            checkPML4At_def in_monad stateAssert_def liftE_bindE
                            get_def bind_def assert_def fail_def
                            asid_map_relation_def asid_map_lift_def
                            asid_map_asid_map_none_def asid_map_asid_map_vspace_def
                            asid_map_asid_map_vspace_lift_def
                      split: if_splits)
    apply (simp add: mask_2pm1)+
  done
  *)

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
    by (clarsimp elim!: exI)
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

lemma setObject_modify:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk> obj_at' (P :: 'a \<Rightarrow> bool) p s; updateObject v = updateObject_default v;
         (1 :: machine_word) < 2 ^ objBits v \<rbrakk>
    \<Longrightarrow> setObject p v s
      = modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))) s"
  apply (clarsimp simp: setObject_def split_def exec_gets
                        obj_at'_def projectKOs lookupAround2_known1
                        assert_opt_def updateObject_default_def
                        bind_assoc)
  apply (simp add: projectKO_def alignCheck_assert)
  apply (simp add: project_inject objBits_def)
  apply (clarsimp simp only: objBitsT_koTypeOf[symmetric] koTypeOf_injectKO)
  apply (frule(2) in_magnitude_check[where s'=s])
  apply (simp add: magnitudeCheck_assert in_monad)
  apply (simp add: simpler_modify_def)
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

lemma kpptr_to_paddr_spec:
  "\<forall>s. \<Gamma> \<turnstile>  {s}
  Call kpptr_to_paddr_'proc
  \<lbrace> \<acute>ret__unsigned_long = RISCV64_H.addrFromKPPtr (ptr_val (pptr_' s)) \<rbrace>"
  apply vcg
  apply (simp add: RISCV64_H.addrFromKPPtr_def RISCV64.addrFromKPPtr_def RISCV64.kernelBaseOffset_def
                   RISCV64.kernelELFBase_def RISCV64.paddrLoad_def)
  done

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
   sorry (* FIXME RISCV: many changes from X64
   apply (ctac, rename_tac vRootCap vRootCap')
     apply (csymbr, rename_tac vRootTag)
     apply csymbr
     apply (simp add: cap_get_tag_isCap_ArchObject2)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: throwError_def catch_def dc_def[symmetric])
      apply (rule ccorres_cond_true_seq, ccorres_rewrite)
      apply (rule ccorres_rhs_assoc)
      apply (rule ccorres_h_t_valid_x64KSSKIMPML4)
      apply csymbr
      apply (rule ccorres_pre_gets_x64KSSKIMPML4_ksArchState[unfolded comp_def])
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: setCurrentUserVSpaceRoot_ccorres)
       apply (rule ccorres_return_void_C)
      apply (rule hoare_post_taut[where P=\<top>])
     apply (rule ccorres_rhs_assoc)
     apply (csymbr, rename_tac is_mapped)
     apply csymbr
     apply (rule_tac P="to_bool (capPML4IsMapped_CL (cap_pml4_cap_lift vRootCap'))
                              = (capPML4MappedASID (capCap vRootCap) \<noteq> None)"
                  in ccorres_gen_asm2)
     apply (clarsimp simp: to_bool_def dc_def[symmetric])
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: throwError_def catch_def dc_def[symmetric], ccorres_rewrite)
      apply (rule ccorres_rhs_assoc)
      apply (rule ccorres_h_t_valid_x64KSSKIMPML4)
      apply csymbr
      apply (rule ccorres_pre_gets_x64KSSKIMPML4_ksArchState[unfolded comp_def])
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: setCurrentUserVSpaceRoot_ccorres)
       apply (rule ccorres_return_void_C)
      apply (rule hoare_post_taut[where P=\<top>])
     apply (simp add: catch_def bindE_bind_linearise bind_assoc liftE_def)
     apply (csymbr, rename_tac pml4_ptr, csymbr)
     apply (csymbr, rename_tac asid', csymbr)
     apply (rule_tac f'=lookup_failure_rel
                 and r'="\<lambda>pml4_ptr pml4_ptr'. pml4_ptr' = pml4e_Ptr pml4_ptr"
                 and xf'=find_ret_'
              in ccorres_split_nothrow_case_sum)
          apply (ctac add: findVSpaceForASID_ccorres)
         apply ceqv
        apply (rename_tac vspace vspace')
        apply (rule_tac P="capPML4BasePtr_CL (cap_pml4_cap_lift vRootCap')
                              = capPML4BasePtr (capCap vRootCap)"
                     in ccorres_gen_asm2)
        apply simp
        apply (rule ccorres_Cond_rhs_Seq)
         apply (simp add: whenE_def throwError_def dc_def[symmetric], ccorres_rewrite)
         apply (rule ccorres_rhs_assoc)
         apply (rule ccorres_h_t_valid_x64KSSKIMPML4)
         apply csymbr
         apply (rule ccorres_pre_gets_x64KSSKIMPML4_ksArchState[unfolded comp_def])
         apply (rule ccorres_add_return2)
         apply (ctac (no_vcg) add: setCurrentUserVSpaceRoot_ccorres)
          apply (rule ccorres_return_void_C)
         apply (rule hoare_post_taut[where P=\<top>])
        apply (simp add: whenE_def returnOk_def)
        apply (csymbr, rename_tac base_addr)
        apply (rule ccorres_symb_exec_r)
          apply (ctac add: getCurrentUserCR3_ccorres, rename_tac currentCR3 currentCR3')
            apply (rule ccorres_if_bind, rule ccorres_if_lhs; simp add: dc_def[symmetric])
             apply (rule ccorres_cond_true)
             apply (ctac add: setCurrentUserCR3_ccorres)
            apply (rule ccorres_cond_false)
            apply (rule ccorres_return_Skip)
           apply (simp, rule hoare_post_taut[where P=\<top>])
          apply vcg
         apply vcg
        apply (rule conseqPre, vcg, clarsimp)
       apply (rule ccorres_cond_true_seq, simp add: dc_def[symmetric], ccorres_rewrite)
       apply (rule ccorres_rhs_assoc)
       apply (rule ccorres_h_t_valid_x64KSSKIMPML4)
       apply csymbr
       apply (rule ccorres_pre_gets_x64KSSKIMPML4_ksArchState[unfolded comp_def])
       apply (rule ccorres_add_return2)
       apply (ctac (no_vcg) add: setCurrentUserVSpaceRoot_ccorres)
        apply (rule ccorres_return_void_C)
       apply (rule hoare_post_taut[where P=\<top>])
      apply (simp add: asid_wf_0, rule wp_post_tautE)
     apply (vcg exspec=findVSpaceForASID_modifies)
    apply (wpsimp wp: getSlotCap_wp)
   apply vcg
  apply (clarsimp simp: Collect_const_mem)
  apply (rule conjI)
   apply (frule cte_at_tcb_at_32', drule cte_at_cte_wp_atD)
   apply (clarsimp simp: cte_level_bits_def tcbVTableSlot_def)
   apply (rule_tac x="cteCap cte" in exI)
   apply (rule conjI, erule cte_wp_at_weakenE', simp)
   apply (clarsimp simp: invs_cicd_no_0_obj' invs_cicd_arch_state')
   apply (frule cte_wp_at_valid_objs_valid_cap'; clarsimp simp: invs_cicd_valid_objs')
   apply (clarsimp simp: isCap_simps valid_cap'_def mask_def asid_wf_def)
  apply (clarsimp simp: tcb_cnode_index_defs cte_level_bits_def tcbVTableSlot_def
                        cte_at_tcb_at_32' to_bool_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject2
                 dest!: isCapDs)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric]
                        cap_lift_pml4_cap cap_to_H_def
                        cap_pml4_cap_lift_def
                        to_bool_def mask_def
                        ccr3_relation_defs Let_def
                        cr3_lift_def word_bw_assocs
                 elim!: ccap_relationE
                 split: if_split_asm X64_H.cr3.splits)
  apply (rename_tac t t')
  apply (rule conjI; clarsimp)
   apply (drule_tac t="cr3_C.words_C (ret__struct_cr3_C_' t').[0]" in sym)
   apply (simp add: word_bw_assocs)
  apply (frule (1) word_combine_masks[where m="0x7FFFFFFFFF000" and m'="0xFFF"]; simp add: word_ao_dist2[symmetric])
  apply (frule (1) word_combine_masks[where m="0x7FFFFFFFFFFFF" and m'="0x7FF8000000000000"]; simp)
  apply (match premises in H: \<open>cr3_C.words_C _.[0] && _ = 0\<close> \<Rightarrow> \<open>insert H; word_bitwise\<close>)
  done
  *)

lemma ccorres_seq_IF_False:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (IF False THEN x ELSE y FI ;; c) = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (y ;; c)"
  by simp

(* FIXME x64: needed? *)
lemma ptrFromPAddr_mask6_simp[simp]:
  "ptrFromPAddr ps && mask 6 = ps && mask 6"
  unfolding ptrFromPAddr_def pptrBase_def baseOffset_def RISCV64.pptrBase_def canonical_bit_def
             pAddr_base_def
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
  apply (simp add: Arrays.update_def n_msgRegisters_def fcp_beta nth_Cons' split: if_split)
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
  apply (simp add: seL4_MessageInfo_lift_def mask_shift_simps)
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

lemma performPageGetAddress_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
      \<top>
      (UNIV \<inter> {s. vbase_ptr_' s = Ptr ptr}) []
      (liftE (performPageInvocation (PageGetAddr ptr)))
      (Call performPageGetAddress_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: vbase_ptr_')
   apply csymbr
   apply (rule ccorres_pre_getCurThread)
   apply (clarsimp simp: setMRs_def zipWithM_x_mapM_x mapM_x_Nil length_of_msgRegisters
                         zip_singleton msgRegisters_unfold mapM_x_singleton)
   apply (ctac add: setRegister_ccorres)
     apply csymbr
     apply (rule ccorres_add_return2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc])
         apply (unfold setMessageInfo_def)
         apply ctac
           apply (simp only: fun_app_def)
           apply (ctac add: setRegister_ccorres)
          apply wp
         apply vcg
        apply ceqv
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
      apply wp
     apply (simp add: guard_is_UNIV_def)
    apply wp
   apply vcg
  apply (auto simp: RISCV64_H.fromPAddr_def message_info_to_H_def mask_def
                    RISCV64_H.msgInfoRegister_def RISCV64.msgInfoRegister_def
                    Kernel_C.msgInfoRegister_def
                    word_sle_def word_sless_def Kernel_C.a1_def
                    kernel_all_global_addresses.msgRegisters_def fupdate_def)
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
       \<top> UNIV [SKIP]
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
     apply (wp empty_fail_getObject | simp add: objBits_simps archObjSize_def bit_simps)+
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

(* FIXME RISCV: REMOVE; left in as guide for proving unmapPage_ccorres as RISCV has no modes
lemma modeUnmapPage_ccorres:
  "ccorres
       (\<lambda>rv rv'. case rv of Inl _ \<Rightarrow> rv' = scast false | Inr _ \<Rightarrow> rv' = scast true)
       ret__unsigned_long_'
       (page_map_l4_at' pmPtr)
       (UNIV \<inter> {s. page_size_' s = scast X64_HugePage}
             \<inter> {s. vroot_' s = pml4e_Ptr pmPtr}
             \<inter> {s. vaddr___unsigned_long_' s = vptr}
             \<inter> {s. pptr_' s = Ptr pptr})
       hs
       (doE p <- lookupPDPTSlot pmPtr vptr;
            pdpte <- liftE (getObject p);
            y <- checkMappingPPtr pptr (vmpage_entry.VMPDPTE pdpte);
            liftE (storePDPTE p X64_H.InvalidPDPTE)
        odE)
       (Call modeUnmapPage_'proc)"
  apply (cinit' lift: page_size_' vroot_' vaddr___unsigned_long_' pptr_')
   apply ccorres_rewrite
   apply (rule ccorres_rhs_assoc)+
   apply csymbr
   apply (ctac add: lookupPDPTSlot_ccorres)
      apply ccorres_rewrite
      apply csymbr
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
             rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
      apply (simp only: bindE_assoc[symmetric])
      apply (rule ccorres_splitE_novcg)
          apply (clarsimp simp: inl_rrel_def)
          apply (rule checkMappingPPtr_pdpte_ccorres[simplified inl_rrel_def])
          apply (rule conseqPre, vcg)
          apply (clarsimp simp: typ_heap_simps')
          apply (intro conjI impI)
              apply (auto simp: pdpte_pdpte_1g_lift_def pdpte_lift_def cpdpte_relation_def
                                isHugePagePDPTE_def pdpteFrame_def
                         split: if_split_asm pdpte.split_asm pdpte.split)[5]
          apply (case_tac pdpte; fastforce)
         apply ceqv
        apply csymbr
        apply (rule ccorres_add_returnOk)
        apply (rule ccorres_liftE_Seq)
        apply (rule ccorres_split_nothrow)
            apply (rule storePDPTE_Basic_ccorres)
            apply (simp add: cpdpte_relation_def Let_def)
           apply ceqv
          apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (fastforce simp: returnOk_def return_def)
         apply wp
        apply vcg
       apply wp
      apply (simp add: guard_is_UNIV_def)
     apply ccorres_rewrite
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def return_def)
    apply wp
   apply (vcg exspec=lookupPDPTSlot_modifies)
  apply clarsimp
  done
  *)

lemmas ccorres_name_ksCurThread = ccorres_pre_getCurThread[where f="\<lambda>_. f'" for f',
    unfolded getCurThread_def, simplified gets_bind_ign]

lemma unmapPage_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. 2 ^ pageBitsForSize sz \<le> gsMaxObjectSize s)
                          and (\<lambda>_. asid_wf asid \<and> vmsz_aligned vptr sz
                                           \<and> vptr < pptrBase))
      (UNIV \<inter> {s. framesize_to_H (page_size_' s) = sz \<and> page_size_' s < 3}
            \<inter> {s. asid_' s = asid} \<inter> {s. vptr_' s = vptr} \<inter> {s. pptr_' s = Ptr pptr}) []
      (unmapPage sz asid vptr pptr) (Call unmapPage_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: page_size_' asid_' vptr_' pptr_')
   apply (simp add: ignoreFailure_liftM Collect_True
               del: Collect_const)
   apply (fold dc_def)
   apply (ctac add: findVSpaceForASID_ccorres)
  sorry (* FIXME RISCV: only one case for riscv, clearing a pte in a page table
      apply (rename_tac pmPtr pm')
      apply (rule_tac P="page_map_l4_at' pmPtr" in ccorres_cross_over_guard)
      apply (simp add: liftE_bindE Collect_False bind_bindE_assoc
                  del: Collect_const)
      apply (rule ccorres_splitE_novcg[where r'=dc and xf'=xfdc])
          \<comment> \<open>X64SmallPage\<close>
          apply (rule ccorres_Cond_rhs)
           apply (simp add: framesize_to_H_def dc_def[symmetric])
           apply (rule ccorres_rhs_assoc)+
           apply (ctac add: lookupPTSlot_ccorres)
              apply (rename_tac pt_slot pt_slot')
              apply (simp add: dc_def[symmetric])
              apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                     rule ccorres_rhs_assoc2)
              apply (simp only: bindE_assoc[symmetric])
              apply (rule ccorres_splitE_novcg)
                  apply (simp only: inl_rrel_inl_rrel)
                  apply (rule checkMappingPPtr_pte_ccorres[simplified])
                  apply (rule conseqPre, vcg)
                  apply (clarsimp simp: typ_heap_simps')
                  apply (clarsimp simp: cpte_relation_def Let_def pte_lift_def
                                        isSmallPagePTE_def if_1_0_0
                                 split: if_split_asm pte.split_asm)
                 apply (rule ceqv_refl)
                apply (simp add: unfold_checkMapping_return liftE_liftM
                                 Collect_const[symmetric] dc_def[symmetric]
                            del: Collect_const)
                apply (rule ccorres_handlers_weaken2)
                apply csymbr
                apply (simp add: dc_def[symmetric])
                apply (rule storePTE_Basic_ccorres)
                apply (simp add: cpte_relation_def Let_def)
               apply wp
              apply (simp add: guard_is_UNIV_def)
             apply (simp add: throwError_def)
             apply (rule ccorres_split_throws)
              apply (rule ccorres_return_void_C')
             apply vcg
            apply (wp)
           apply simp
           apply (vcg exspec=lookupPTSlot_modifies)
          \<comment> \<open>X64LargePage\<close>
          apply (rule ccorres_Cond_rhs)
           apply (simp add: framesize_to_H_def dc_def[symmetric]
                       del: Collect_const)
           apply (rule ccorres_rhs_assoc)+
           apply (ctac add: lookupPDSlot_ccorres)
              apply (rename_tac pd_slot pd_slot')
              apply (simp add: dc_def[symmetric])
              apply csymbr
              apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                     rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
              apply (simp only: bindE_assoc[symmetric])
              apply (rule ccorres_splitE_novcg)
                  apply (simp only: inl_rrel_inl_rrel)
                  apply (rule checkMappingPPtr_pde_ccorres[simplified])
                  apply (rule conseqPre, vcg)
                  apply (clarsimp simp: typ_heap_simps')
                  apply (clarsimp simp: cpde_relation_def Let_def pde_lift_def pde_pde_large_lift_def
                                        isLargePagePDE_def pde_get_tag_def pde_tag_defs
                                 split: if_split_asm pde.split_asm)
                 apply (rule ceqv_refl)
                apply (simp add: unfold_checkMapping_return liftE_liftM
                                 Collect_const[symmetric] dc_def[symmetric]
                            del: Collect_const)
                apply (rule ccorres_handlers_weaken2)
                apply csymbr
                apply (simp add: dc_def[symmetric])
                apply (rule storePDE_Basic_ccorres)
                apply (simp add: cpde_relation_def Let_def)
               apply wp
              apply (simp add: guard_is_UNIV_def)
             apply (simp add: throwError_def)
             apply (rule ccorres_split_throws)
              apply (rule ccorres_return_void_C')
             apply vcg
            apply (wp)
           apply simp
           apply (vcg exspec=lookupPDSlot_modifies)
          \<comment> \<open>X64HugePage\<close>
          apply (simp add: framesize_to_H_def dc_def[symmetric])
          apply (rule ccorres_add_return2)
          apply (ctac add: modeUnmapPage_ccorres)
            apply (rule ccorres_from_vcg_might_throw[where P="\<top>" and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: true_def false_def return_def inl_rrel_def split: sum.split_asm)
           apply wp
          apply (vcg exspec=modeUnmapPage_modifies)
         apply ceqv
        apply (rule ccorres_name_ksCurThread)
        apply (rule_tac val="tcb_ptr_to_ctcb_ptr rv" and xf'="\<lambda>s. ksCurThread_' (globals s)"
                        in ccorres_abstract_known, ceqv)
        apply clarsimp
        apply ccorres_rewrite
        apply (clarsimp simp: liftE_liftM)
        apply (ctac add: invalidateTranslationSingleASID_ccorres[simplified dc_def])
       apply clarsimp
      apply clarsimp
      apply (clarsimp simp: guard_is_UNIV_def conj_comms tcb_cnode_index_defs)
     apply (simp add: throwError_def)
     apply (rule ccorres_split_throws)
      apply (rule ccorres_return_void_C[unfolded dc_def])
     apply vcg
    apply wpsimp
   apply (simp add: Collect_const_mem)
   apply (vcg exspec=findVSpaceForASID_modifies)
  by (auto simp: invs_arch_state' invs_no_0_obj' invs_valid_objs' vmsz_aligned_def
                 is_aligned_weaken[OF _ pbfs_atleast_pageBits] pageBitsForSize_def
                 Collect_const_mem vm_page_size_defs word_sle_def
                 ccHoarePost_def typ_heap_simps bit_simps
            dest!: page_directory_at_rf_sr
            elim!: clift_array_assertion_imp
            split: vmpage_size.splits
            elim: is_aligned_weaken
      | unat_arith)+
  *)

(* FIXME: move *)
lemma cap_to_H_PageCap_tag:
  "\<lbrakk> cap_to_H cap = ArchObjectCap (FrameCap p R sz d A);
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_frame_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     by (simp_all add: Let_def cap_lift_def split_def split: if_splits)

(* FIXME RISCV: used by performPageInvocationUnmap_ccorres* to set the frame cap on all platforms
                unfortunately on riscv the code is different for no apparent reason:
    ctSlot->cap = cap_frame_cap_set_capFMappedAddress(ctSlot->cap, 0);
    ctSlot->cap = cap_frame_cap_set_capFMappedASID(ctSlot->cap, asidInvalid);
as compared to X64:
    cap_frame_cap_ptr_set_capFMappedAddress(&ctSlot->cap, 0);
    cap_frame_cap_ptr_set_capFMappedASID(&ctSlot->cap, asidInvalid);
    cap_frame_cap_ptr_set_capFMapType(&ctSlot->cap, X86_MappingNone);
and ARM:
    generic_frame_cap_ptr_set_capFMappedAddress(&ctSlot->cap, asidInvalid, 0);

    this is an argument for changing the C if this proof ends up too difficult

lemma updateCap_frame_mapped_addr_ccorres:
  notes option.case_cong_weak [cong]
  shows "ccorres dc xfdc
           (cte_wp_at' (\<lambda>c. ArchObjectCap cap = cteCap c) ctSlot and K (isFrameCap cap))
           UNIV []
           (updateCap ctSlot (ArchObjectCap (capFMappedAddress_update Map.empty cap)))
           (Guard C_Guard {s. s \<Turnstile>\<^sub>c cte_Ptr ctSlot}
              (CALL cap_frame_cap_ptr_set_capFMappedAddress(cap_Ptr &(cte_Ptr ctSlot\<rightarrow>[''cap_C'']), 0));;
            Guard C_Guard {s. s \<Turnstile>\<^sub>c cte_Ptr ctSlot}
              (CALL cap_frame_cap_ptr_set_capFMappedASID(cap_Ptr &(cte_Ptr ctSlot\<rightarrow>[''cap_C'']), scast asidInvalid)))"
  unfolding updateCap_def
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_pre_getCTE)
   apply (rule_tac P = "\<lambda>s. ctes_of s ctSlot = Some cte
                             \<and> cteCap cte = ArchObjectCap cap \<and> isPageCap cap" and
                   P' = "UNIV"
                in ccorres_from_vcg)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (erule (1) rf_sr_ctes_of_cliftE)
   apply (frule cap_CL_lift)
   apply (clarsimp simp: typ_heap_simps)
   apply (rule context_conjI)
    apply (clarsimp simp: isCap_simps)
    apply (drule cap_CL_lift)
    apply (drule (1) cap_to_H_PageCap_tag)
    apply simp
   apply (clarsimp simp: isCap_simps typ_heap_simps)
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI [rotated])
   apply clarsimp
   apply (frule (1) rf_sr_ctes_of_clift)
   apply clarsimp
   prefer 2 apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: packed_heap_update_collapse_hrs)
  apply (subgoal_tac "ccte_relation (cteCap_update (\<lambda>_. ArchObjectCap (PageCap v0 v1 VMNoMap v3 d None))
                                                   (cte_to_H ctel'))
                                    (cte_C.cap_C_update (\<lambda>_. capb) cte')")
   apply (clarsimp simp: rf_sr_def cstate_relation_def typ_heap_simps Let_def cpspace_relation_def)
   apply (rule conjI)
    apply (erule (3) cmap_relation_updI)
    subgoal by simp
   apply (erule_tac t=s' in ssubst)
   apply (simp add: heap_to_user_data_def)
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                         typ_heap_simps h_t_valid_clift_Some_iff
                         cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                         fpu_null_state_heap_update_tag_disj_simps)
  apply (clarsimp simp: ccte_relation_def)
  apply (clarsimp simp: cte_lift_def)
  apply (simp split: option.splits)
  apply (clarsimp simp: cte_to_H_def c_valid_cte_def)
  apply (rule conjI, simp add: cap_frame_cap_lift)
  apply (clarsimp simp: cap_frame_cap_lift_def)
  apply (clarsimp simp: c_valid_cap_def cl_valid_cap_def
                        cap_frame_cap_lift cap_to_H_def maptype_to_H_def
                        X86_MappingNone_def asidInvalid_def)
  done
  *)

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

lemma performPageInvocationUnmap_ccorres:
  notes Collect_const[simp del]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' ((=) (ArchObjectCap cap) o cteCap) ctSlot  and K (isFrameCap cap))
       (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>cte = Ptr ctSlot\<rbrace>)
       hs
       (liftE (performPageInvocation (PageUnmap cap ctSlot)))
       (Call performPageInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp K_def)
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: cap_' cte_' simp: performPageInvocation_def)
   apply csymbr
   apply (clarsimp simp: isCap_simps)
   apply (frule ccap_relation_mapped_asid_0)
   apply (rule ccorres_Cond_rhs_Seq)
    (* ASID present, unmap *)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply csymbr
    apply csymbr
    apply clarsimp
    apply (frule cap_get_tag_isCap_unfolded_H_cap)
    apply (clarsimp simp: asidInvalid_def)
    sorry (* FIXME RISCV: quite different from X64, see performPageInvocationUnmap_ccorres' there
     apply (ctac (no_vcg) add: unmapPage_ccorres)

     apply (ctac add: performPageInvocationUnmap_ccorres'[simplified K_def, simplified])

    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule ccorres_rhs_assoc)
     apply (drule_tac s=cap in sym, simp) (* schematic ugliness *)
     apply ccorres_rewrite
     apply (rule ccorres_add_return2)
     apply (ctac add: performPageInvocationUnmap_ccorres'[simplified K_def, simplified])
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply wp
     apply (vcg exspec=performX86PageInvocationUnmap_modifies)
    apply (clarsimp simp: asidInvalid_def)
    apply (clarsimp simp: maptype_from_H_def split: vmmap_type.splits)
    apply(rule ccorres_fail)
   apply (clarsimp simp: asidInvalid_def)
   apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: return_def)
  by (clarsimp simp: o_def isCap_simps cap_get_tag_isCap_unfolded_H_cap)
  *)


lemma RISCVGetWriteFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace> Call RISCVGetWriteFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned_long = writable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  apply vcg
  apply (simp add: vmrights_to_H_def writable_from_vm_rights_def Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply (drule word_less_cases, auto)+
  done

lemma RISCVGetReadFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace> Call RISCVGetReadFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned_long = readable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  apply vcg
  apply (simp add: vmrights_to_H_def readable_from_vm_rights_def Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply (drule word_less_cases, auto)+
  done

lemma RISCVGetUserFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace> Call RISCVGetUserFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned_long = user_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  apply vcg
  apply (simp add: vmrights_to_H_def user_from_vm_rights_def Kernel_C.VMKernelOnly_def
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
  \<lbrace> pte_lift \<acute>ret__struct_pte_C = \<lparr>
       pte_CL.ppn_CL = (\<^bsup>s\<^esup>paddr >> 12) && mask 44,
       pte_CL.sw_CL = 0,
       pte_CL.dirty_CL = 1,
       pte_CL.accessed_CL = 1,
       pte_CL.global_CL = 0,
       pte_CL.user_CL = user_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pte_CL.execute_CL = \<^bsup>s\<^esup>executable && mask 1,
       pte_CL.write_CL = writable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pte_CL.read_CL = readable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pte_CL.valid_CL = 1\<rparr> \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: mask_def user_from_vm_rights_mask writable_from_vm_rights_mask
                        readable_from_vm_rights_mask)
  done

(* FIXME RISCV: useful? strange that the vm_attributes are so limited, so the C code could be wrong *)
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
           (asid \<noteq> None \<longrightarrow> capPTMappedASID_CL cap_CL = fst (the asid)) \<and>
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
  apply (rule hoare_seq_ext [OF _ hoare_gets_post])
  apply (clarsimp simp: valid_def in_monad)
  apply (frule updateObject_type)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (rule conjI)
   apply (clarsimp simp: lookupAround2_char1)
   apply (clarsimp split: if_split)
   apply (case_tac obj', auto)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, auto)[1]
   apply (simp add: updateObject_cte)
   apply (clarsimp simp: updateObject_cte typeError_def magnitudeCheck_def in_monad
                   split: kernel_object.splits if_splits option.splits)
  apply (clarsimp simp: ps_clear_upd' lookupAround2_char1)
  done

(* FIXME: move *)
lemma udpateCap_asidpool':
  "\<lbrace> ko_at' (ASIDPool pool) p \<rbrace> updateCap c p' \<lbrace>\<lambda>_. ko_at' (ASIDPool pool) p\<rbrace>"
  apply (simp add: updateCap_def)
  apply (wp setCTE_asidpool')
  done

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
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
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
    apply (simp_all add: objBits_simps archObjSize_def pageBits_def)
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
  by (rule getObject_ko_at | simp add: objBits_simps archObjSize_def bit_simps)+

lemma canonical_address_page_table_at':
  "\<lbrakk>page_table_at' p s; pspace_canonical' s\<rbrakk> \<Longrightarrow> canonical_address p"
  apply (clarsimp simp: page_table_at'_def)
  apply (drule_tac x=0 in spec, clarsimp simp: bit_simps typ_at_to_obj_at_arches)
  apply (erule (1) obj_at'_is_canonical)
  done

(* FIXME RISCV move *)
definition
  "isPTCap' cap \<equiv> \<exists>p asid. cap = (ArchObjectCap (PageTableCap p asid))"

lemma performASIDPoolInvocation_ccorres:
  notes option.case_cong_weak [cong]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' (isPTCap' o cteCap) ctSlot and asid_pool_at' poolPtr
        and K (asid \<le> mask asid_bits \<and> asid \<noteq> ucast asidInvalid))
       (UNIV \<inter> \<lbrace>\<acute>poolPtr = Ptr poolPtr\<rbrace> \<inter> \<lbrace>\<acute>asid = asid\<rbrace> \<inter> \<lbrace>\<acute>vspaceCapSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performASIDPoolInvocation (Assign asid poolPtr ctSlot)))
       (Call performASIDPoolInvocation_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: poolPtr_' asid_' vspaceCapSlot_')
  sorry (* FIXME RISCV
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_rhs_assoc2)
      apply (rule_tac ccorres_split_nothrow [where r'=dc and xf'=xfdc])
          apply (simp add: updateCap_def)
          apply (rule_tac A="cte_wp_at' ((=) rv o cteCap) ctSlot
                             and K (isPML4Cap' rv \<and> asid \<le> mask asid_bits \<and> asid \<noteq> ucast asidInvalid)"
                      and A'=UNIV in ccorres_guard_imp2)
           apply (rule ccorres_pre_getCTE)
           apply (rule_tac P="cte_wp_at' ((=) rv o cteCap) ctSlot
                              and K (isPML4Cap' rv \<and> asid \<le> mask asid_bits \<and> asid \<noteq> ucast asidInvalid)
                              and cte_wp_at' ((=) rva) ctSlot"
                       and P'=UNIV in ccorres_from_vcg)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: cte_wp_at_ctes_of)
           apply (erule (1) rf_sr_ctes_of_cliftE)
           apply (clarsimp simp: typ_heap_simps)
           apply (rule conjI)
            apply (clarsimp simp: isPML4Cap'_def)
            apply (drule cap_CL_lift)
            apply (drule (1) cap_to_H_PML4Cap_tag)
            apply simp
           apply (clarsimp simp: typ_heap_simps' isPML4Cap'_def)
           apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
           apply (erule bexI [rotated])
           apply clarsimp
           apply (frule (1) rf_sr_ctes_of_clift)
           apply clarsimp
           apply (clarsimp simp: rf_sr_def cstate_relation_def typ_heap_simps
                                 Let_def cpspace_relation_def)
           apply (rule conjI)
            apply (erule (2) cmap_relation_updI)
             apply (clarsimp simp: ccte_relation_def)
             apply (clarsimp simp: cte_lift_def)
             apply (simp split: option.splits)
             apply clarsimp
             apply (case_tac cte')
             apply clarsimp
             apply (rule conjI)
              apply (clarsimp simp: cap_lift_def Let_def cap_tag_defs)
             apply clarsimp
             apply (simp add: cte_to_H_def c_valid_cte_def)
             apply (simp add: cap_pml4_cap_lift)
             apply (simp (no_asm) add: cap_to_H_def)
             apply (simp add: to_bool_def asid_bits_def le_mask_imp_and_mask word_bits_def)
             apply (clarsimp simp: c_valid_cap_def cl_valid_cap_def)
             apply (erule (1) cap_lift_PML4Cap_Base)
            apply simp
           apply (erule_tac t = s' in ssubst)
           apply (simp add: heap_to_user_data_def)
           apply (rule conjI)
            apply (erule (1) setCTE_tcb_case)
           apply (simp add: carch_state_relation_def cmachine_state_relation_def
                            cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                            fpu_null_state_heap_update_tag_disj_simps
                            global_ioport_bitmap_heap_update_tag_disj_simps
                            packed_heap_update_collapse_hrs)
          apply (clarsimp simp: cte_wp_at_ctes_of)
         apply ceqv
        apply (rule ccorres_symb_exec_l)
           apply (rule_tac P="ko_at' (ASIDPool pool) poolPtr" in ccorres_cross_over_guard)
           apply (rule ccorres_move_c_guard_cte)
           apply (rule ccorres_symb_exec_r)
             apply csymbr
             apply (rule ccorres_abstract_cleanup)
             apply (rule ccorres_Guard_Seq[where F=ArrayBounds])?
             apply (rule ccorres_move_c_guard_ap)
             apply (simp only: Kernel_C.asidLowBits_def word_sle_def)
             apply (rule ccorres_Guard_Seq)+
             apply (rule ccorres_add_return2)
             apply (rule ccorres_split_nothrow_novcg)
                 apply (rule setObjectASID_Basic_ccorres)
                apply ceqv
               apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: return_def)
              apply wp
             apply (simp add: guard_is_UNIV_def)
            apply (vcg)
           apply (rule conseqPre, vcg)
           apply clarsimp
          apply (wpsimp wp: liftM_wp)
         apply (wpsimp wp: getASID_wp simp: o_def inv_def)
        apply (clarsimp simp: empty_fail_getObject)
       apply (wpsimp wp: udpateCap_asidpool' hoare_vcg_all_lift hoare_vcg_imp_lift')
      apply vcg
     apply wp
     apply simp
    apply (wp getSlotCap_wp')
   apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI)
   apply (clarsimp dest!: asid_pool_at_ko simp: obj_at'_def inv_def)
  apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
  apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap_ArchObject2
                        isPML4Cap'_def isCap_simps
                        order_le_less_trans[OF word_and_le1] asid_low_bits_def
                 dest!: ccte_relation_ccap_relation)
  apply (simp add: casid_pool_relation_def mask_def)
  apply (rule array_relation_update)
     apply (drule (1) asid_pool_at_rf_sr)
     apply (clarsimp simp: typ_heap_simps)
     apply (case_tac pool')
     apply (simp add: casid_pool_relation_def)
    apply (simp add: asid_low_bits_of_mask_eq mask_def asid_low_bits_def)
   apply (clarsimp simp: asid_map_relation_def asid_map_asid_map_vspace_lift
                         asid_map_asid_map_none_def asid_map_asid_map_vspace_def
                         asid_map_lifts[simplified asid_map_asid_map_vspace_def, simplified]
                         cap_pml4_cap_lift
                   split: if_splits)
   apply (drule_tac s=sa in cmap_relation_cte)
   apply (erule_tac y=ctea in cmap_relationE1, assumption)
   apply (clarsimp simp: ccte_relation_def ccap_relation_def map_option_Some_eq2)
   apply (clarsimp simp: cap_pml4_cap_lift_def dest!: cap_to_H_PML4Cap)
   apply (simp add: sign_extend_canonical_address)
   apply (drule_tac cte=cte in ctes_of_valid'[OF _ invs_valid_objs'], assumption)
   apply (clarsimp simp: valid_cap'_def canonical_address_page_map_l4_at'[OF _ invs_pspace_canonical'])
  apply (simp add: asid_low_bits_def)
  done
  *)

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
