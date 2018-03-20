(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory VSpace_C
imports TcbAcc_C CSpace_C PSpace_C TcbQueue_C
begin

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
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F S (Guard F1 S1 c))"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F1 S1 (Guard F S c))"
  apply (rule ccorres_name_pre_C)
  using cc
  apply (case_tac "s \<in> (S1 \<inter> S)")
   apply (clarsimp simp: ccorres_underlying_def)
   apply (erule exec_handlers.cases;
    fastforce elim!: exec_Normal_elim_cases intro: exec_handlers.intros exec.Guard)
  apply (clarsimp simp: ccorres_underlying_def)
  apply (case_tac "s \<in> S")
   apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros)
  apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros)
  done

(* FIXME: move *)
lemma empty_fail_findVSpaceForASID[iff]:
  "empty_fail (findVSpaceForASID asid)"
  apply (simp add: findVSpaceForASID_def liftME_def)
  apply (intro empty_fail_bindE, simp_all split: option.split)
     apply (simp add: assertE_def split: if_split)
    apply (simp add: assertE_def split: if_split)
   apply (simp add: empty_fail_getObject)
  apply (simp add: assertE_def liftE_bindE checkPML4At_def split: if_split)
  done

(* FIXME: move *)
lemma empty_fail_findVSpaceForASIDAssert[iff]:
  "empty_fail (findVSpaceForASIDAssert asid)"
  apply (simp add: findVSpaceForASIDAssert_def catch_def
                   checkPML4At_def)
  apply (intro empty_fail_bind, simp_all split: sum.split)
  done

(* FIXME: move *)
lemma mask_AND_less_0:
  "\<lbrakk>x && mask n = 0; m \<le> n\<rbrakk> \<Longrightarrow> x && mask m = 0"
  apply (case_tac "len_of TYPE('a) \<le> n")
   apply (clarsimp simp: ge_mask_eq)
  apply (erule is_aligned_AND_less_0)
  apply (clarsimp simp: mask_2pm1 two_power_increasing)
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
proof -
  note [split del] = if_split
  show ?thesis
  apply (cinit lift: sz_' w_')
  sorry (* FIXME x64: csymbr not unifying with pageBitsForSize_spec
                      also need to check pageBitsForSize_modifies, it can apparently modify everything
   apply (csymbr) thm pageBitsForSize_modifies
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
  done *)
qed


lemma rf_asidTable:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; valid_arch_state' \<sigma>; idx \<le> mask asid_high_bits \<rbrakk>
     \<Longrightarrow> case x64KSASIDTable (ksArchState \<sigma>)
                idx of
        None \<Rightarrow>
            index (x86KSASIDTable_' (globals x)) (unat idx) =
               NULL
             | Some v \<Rightarrow>
                 index (x86KSASIDTable_' (globals x)) (unat idx) = Ptr v \<and>
                 index (x86KSASIDTable_' (globals x)) (unat idx) \<noteq> NULL"
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
     \<Longrightarrow> case x64KSASIDTable (ksArchState \<sigma>)
                idx of
        None \<Rightarrow>
            index (x86KSASIDTable_' (globals x))
                idx' =
               NULL
             | Some v \<Rightarrow>
                 index (x86KSASIDTable_' (globals x))
                  idx' = Ptr v \<and>
                 index (x86KSASIDTable_' (globals x))
                  idx' \<noteq> NULL"
  apply (drule rf_asidTable [where idx=idx])
    apply fastforce
   apply (simp add: mask_def)
   apply (simp add: minus_one_helper3)
  apply (clarsimp split: option.splits)
  done

lemma asidLowBits_handy_convs:
  "sint Kernel_C.asidLowBits = 9"
  "Kernel_C.asidLowBits \<noteq> 0x20"
  "unat Kernel_C.asidLowBits = asid_low_bits"
  by (simp add: Kernel_C.asidLowBits_def asid_low_bits_def)+

lemma rf_sr_x86KSASIDTable:
  "\<lbrakk> (s, s') \<in> rf_sr; n \<le> 2 ^ asid_high_bits - 1 \<rbrakk>
       \<Longrightarrow> index (x86KSASIDTable_' (globals s')) (unat n)
               = option_to_ptr (x64KSASIDTable (ksArchState s) n)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                     carch_state_relation_def array_relation_def)

lemma asid_high_bits_word_bits:
  "asid_high_bits < word_bits"
  by (simp add: asid_high_bits_def word_bits_def)

(* FIXME x64: update for new asid map carch_state_relation *)
(*
lemma rf_sr_asid_map_pd_:
  "(s, s') \<in> rf_sr \<Longrightarrow>
   asid_map_pd_to_hwasids (x64KSASIDMap (ksArchState s))
       = set_option \<circ> (pde_stored_asid \<circ>\<^sub>m cslift s' \<circ>\<^sub>m pd_pointer_to_asid_slot)"
  by (simp add: rf_sr_def cstate_relation_def Let_def
                carch_state_relation_def)
*)
(* FIXME x64: need to fix up asid_map_lift conclusion *)
lemma vspace_at_asid_cross_over:
  "\<lbrakk> vspace_at_asid' pm asid s; asid \<le> mask asid_bits;
          (s, s') \<in> rf_sr\<rbrakk>
      \<Longrightarrow> \<exists>apptr ap. index (x86KSASIDTable_' (globals s')) (unat (asid >> asid_low_bits))
                     = (ap_Ptr apptr) \<and> cslift s' (ap_Ptr apptr) = Some (asid_pool_C ap)
                  (*\<and> asid_map_lift (index ap (unat (asid && 2 ^ asid_low_bits - 1))) = pml4e_Ptr pm*)
                  \<and> is_aligned pm pml4Bits
                  \<and> array_assertion (pml4e_Ptr pm) 512 (hrs_htd (t_hrs_' (globals s')))"
  apply (clarsimp simp: vspace_at_asid'_def)
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
  (*
  apply (drule spec, drule sym [OF mp])
   apply (rule_tac y=asid in word_and_le1)
  apply (frule(1) page_directory_at_rf_sr)
  apply (clarsimp simp: mask_2pm1[symmetric] option_to_ptr_def option_to_0_def
                        page_directory_at'_def typ_at_to_obj_at_arches)
  apply (drule_tac x="pd_asid_slot" in spec,
         simp add: pd_asid_slot_def pt_index_bits_def' pageBits_def)
  apply (drule obj_at_ko_at'[where 'a=pde], clarsimp)
  apply (rule cmap_relationE1 [OF rf_sr_cpde_relation],
         assumption, erule ko_at_projectKO_opt)
  apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
  apply (clarsimp simp: valid_pde_mappings'_def)
  apply (elim allE, drule(1) mp)
  apply (simp add: valid_pde_mapping'_def valid_pde_mapping_offset'_def
                   pd_asid_slot_def mask_add_aligned table_bits_defs)
  apply (simp add: mask_def)
  apply (clarsimp simp add: cpde_relation_def Let_def)
  by (simp add: pde_lift_def Let_def split: if_split_asm) *)
  sorry

lemma findVSpaceForASIDAssert_pd_at_wp2:
  "\<lbrace>\<lambda>s. \<forall>pd. vspace_at_asid' pd asid s \<longrightarrow> P pd s\<rbrace> findVSpaceForASIDAssert asid \<lbrace>P\<rbrace>"
  apply (simp add: findVSpaceForASIDAssert_def const_def
                    checkPML4At_def)
  apply (wpsimp wp: findVSpaceForASID_vs_at_wp)
  done

lemma asid_shiftr_low_bits_less:
  "(asid :: machine_word) \<le> mask asid_bits \<Longrightarrow> asid >> asid_low_bits < 0x8"
  apply (rule_tac y="2 ^ 3" in order_less_le_trans)
   apply (rule shiftr_less_t2n)
   apply (simp add: le_mask_iff_lt_2n[THEN iffD1] asid_bits_def asid_low_bits_def)
  apply simp
  done

lemma array_relation_update:
  "\<lbrakk> array_relation R bnd table (arr :: 'a['b :: finite]);
               x' = unat (x :: ('td :: len) word); R v v';
               unat bnd < card (UNIV :: 'b set) \<rbrakk>
     \<Longrightarrow> array_relation R bnd (table (x := v))
               (Arrays.update arr x' v')"
  by (simp add: array_relation_def word_le_nat_alt split: if_split)

(* FIXME x64: this function doesn't exist in x64, related to
              the maintenance of the asid map. Since the asid map
              is contentious (gerwin advocates getting rid of it)
              it is commented out now *)
(*
lemma invalidateASID_ccorres:
  "ccorres dc xfdc ((\<lambda>_. asid \<le> mask asid_bits))
                   (UNIV \<inter> {s. asid_' s = asid}) []
     (invalidateASID asid) (Call invalidateASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_')
   apply (rule ccorres_Guard_Seq)+
   apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_findVSpaceForASIDAssert])
     apply (rename_tac pd)
     apply (rule_tac P="\<lambda>s. vspace_at_asid' pd asid s \<and> valid_pde_mappings' s
                               \<and> pd \<notin> ran (option_map snd o x64KSASIDMap (ksArchState s)
                                                     |` (- {asid}))
                               \<and> option_map snd (x64KSASIDMap (ksArchState s) asid) \<in> {None, Some pd}"
                   in ccorres_from_vcg[where P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: Collect_const_mem word_sle_def word_sless_def
                           asidLowBits_handy_convs simpler_gets_def
                           simpler_modify_def bind_def)
     apply (frule(2) vspace_at_asid_cross_over)
     apply (clarsimp simp: typ_heap_simps)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           cpspace_relation_def
                           ptr_add_assertion_positive
                           array_assertion_shrink_right)
     apply (clarsimp simp: typ_heap_simps cmachine_state_relation_def
                           carch_state_relation_def vspace_at_asid'_def carch_globals_def
                           fun_upd_def[symmetric] order_le_less_trans[OF word_and_le1]
                           arg_cong[where f="\<lambda>x. 2 ^ x", OF meta_eq_to_obj_eq, OF asid_low_bits_def])
     apply (intro conjI)
      apply (erule iffD1 [OF cmap_relation_cong, rotated -1], simp_all)[1]
      apply (simp split: if_split_asm)
      apply (clarsimp simp: cpde_relation_def Let_def
                            pde_lift_pde_invalid
                      cong: X64_H.pde.case_cong)
     apply (subst asid_map_pd_to_hwasids_clear, assumption)
      subgoal by clarsimp
     apply (rule ext, simp add: pd_pointer_to_asid_slot_def map_comp_def split: if_split)
     subgoal by (clarsimp simp: pde_stored_asid_def false_def mask_def[where n="Suc 0"])
    apply wp[1]
   apply (wp findVSpaceForASIDAssert_pd_at_wp2)
  apply (clarsimp simp: asidLowBits_handy_convs word_sle_def word_sless_def
                        asid_shiftr_low_bits_less)
  done *)

(* FIXME x64: waiting on vm_fault_type enum for x64 *)
definition
  "vm_fault_type_from_H fault \<equiv>
  case fault of
    vmfault_type.X64DataFault \<Rightarrow> (scast Kernel_C.X86DataFault) :: machine_word
  | vmfault_type.X64InstructionFault \<Rightarrow> scast Kernel_C.X86InstructionFault"

lemma mask_64_id [simp]:
  "(x::machine_word) && mask 64 = x"
  using uint_lt2p [of x] by (simp add: mask_eq_iff)

(* FIXME x64 *)
lemma handleVMFault_ccorres:
  "ccorres ((\<lambda>a ex v. ex = scast EXCEPTION_FAULT \<and> (\<exists>vf.
                      a = ArchFault (VMFault (seL4_Fault_VMFault_CL.address_CL vf) [instructionFault_CL vf, FSR_CL vf]) \<and>
                      errfault v = Some (SeL4_Fault_VMFault vf))) \<currency>
           (\<lambda>_. \<bottom>))
           (liftxf errstate id (K ()) ret__unsigned_long_')
           \<top>
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>vm_faultType = vm_fault_type_from_H vm_fault\<rbrace>)
          []
           (handleVMFault thread vm_fault)
           (Call handleVMFault_'proc)"
  apply (cinit lift: thread_' vm_faultType_')
   apply (ctac (no_vcg) add: getFaultAddr_ccorres pre: ccorres_liftE_Seq)
  sorry (* getRegister returns word but gets truncated here
    apply (ctac (no_vcg) add: getRegister_ccorres pre: ccorres_liftE_Seq)

   apply (ctac add: getFaultAddr_ccorres)
   apply wpc
    apply (simp add: vm_fault_type_from_H_def)
    apply (simp add: ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (ctac (no_vcg) add: getHDFAR_ccorres pre: ccorres_liftE_Seq)
     apply (ctac (no_vcg) add: addressTranslateS1CPR_ccorres pre: ccorres_liftE_Seq)
      apply csymbr
      apply (ctac (no_vcg) add: getHSR_ccorres pre: ccorres_liftE_Seq)
       apply csymbr
       apply (clarsimp simp: pageBits_def)
       apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
       apply (clarsimp simp add: throwError_def return_def)
       apply (rule conseqPre)
        apply vcg
       apply (clarsimp simp: errstate_def EXCEPTION_FAULT_def EXCEPTION_NONE_def)
       apply (wpsimp simp: seL4_Fault_VMFault_lift false_def mask_def)+
  apply (simp add: vm_fault_type_from_H_def Kernel_C.ARMDataAbort_def Kernel_C.ARMPrefetchAbort_def)
   apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff)
   apply (rule ccorres_rhs_assoc)+
   apply csymbr
   apply csymbr
   apply (ctac (no_vcg) pre: ccorres_liftE_Seq)
    apply (ctac (no_vcg) add: addressTranslateS1CPR_ccorres pre: ccorres_liftE_Seq)
     apply csymbr
     apply (ctac (no_vcg) add: getHSR_ccorres pre: ccorres_liftE_Seq)
      apply csymbr
      apply (clarsimp simp: pageBits_def)
      apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
      apply (clarsimp simp add: throwError_def return_def)
      apply (rule conseqPre)
       apply vcg
      apply (clarsimp simp: errstate_def EXCEPTION_FAULT_def EXCEPTION_NONE_def)
      apply (wpsimp simp: seL4_Fault_VMFault_lift true_def mask_def)+
  done *)

lemma unat_asidLowBits [simp]:
  "unat Kernel_C.asidLowBits = asidLowBits"
  by (simp add: asidLowBits_def Kernel_C.asidLowBits_def asid_low_bits_def)

lemma rf_sr_asidTable_None:
  "\<lbrakk> (\<sigma>, x) \<in> rf_sr; asid && mask asid_bits = asid; valid_arch_state' \<sigma>  \<rbrakk> \<Longrightarrow>
  (index (x86KSASIDTable_' (globals x)) (unat (asid >> asid_low_bits)) = ap_Ptr 0) =
  (x64KSASIDTable (ksArchState \<sigma>) (ucast (asid_high_bits_of asid)) = None)"
  apply (simp add: asid_high_bits_of_def ucast_ucast_mask)
  apply (subgoal_tac "(asid >> asid_low_bits) && mask 3 = asid >> asid_low_bits")(*asid_high_bits*)
   prefer 2
   apply (rule word_eqI)
   apply (subst (asm) bang_eq)
   apply (simp add: word_size nth_shiftr asid_bits_def asid_low_bits_def)
   apply (case_tac "n < 3", simp) (*asid_high_bits*)
   apply (clarsimp simp: linorder_not_less)
   apply (erule_tac x="n+9" in allE) (*asid_low_bits*)
   apply simp
  apply simp
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)
  apply (simp add: array_relation_def option_to_0_def)
  apply (erule_tac x="asid >> asid_low_bits" in allE)
  apply (erule impE)
   prefer 2
   apply (drule sym [where t="index a b" for a b])
   apply (simp add: option_to_0_def option_to_ptr_def split: option.splits)
   apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def ran_def)
  apply (simp add: and_mask_eq_iff_le_mask)
  apply (simp add: asid_high_bits_def mask_def)
  done

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
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_eqI[rule_format])
  apply (simp add: word_size nth_shiftr nth_ucast asid_low_bits_def asid_bits_def word_bits_def)
  apply (erule_tac x="n+9" in allE)(*asid_low_bits*)
  apply simp
  apply (case_tac "n < 3", simp) (*asid_high_bits*)
  apply (simp add: linorder_not_less)
  apply (rule notI)
  apply (frule test_bit_size)
  apply (simp add: word_size)
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


(* FIXME x64: lookupPML4Slot returns a struct, postcondition needs fixing *)
lemma lookupPML4Slot_spec:
  "\<forall>s. \<Gamma> \<turnstile>  \<lbrace>s. array_assertion (pml4_' s) (2 ^ ptTranslationBits) (hrs_htd (\<acute>t_hrs))\<rbrace>
  Call lookupPML4Slot_'proc
  \<lbrace>  \<acute>ret__ptr_to_struct_pml4e_C =  Ptr (lookupPML4Slot (ptr_val (pml4_' s))  (vptr_' s)) \<rbrace>"
  apply vcg
  apply clarsimp
  apply (clarsimp simp: lookup_pml4_slot_def)
  apply (simp add: bit_simps)
  apply (subst array_assertion_shrink_right, assumption)
   apply (rule unat_le_helper, clarsimp simp: ptTranslationBits_mask_le order_less_imp_le)
  apply (simp add: Let_def word_sle_def bit_simps getPML4Index_def mask_def)
  apply (case_tac pml4)
  apply (simp add: shiftl_t2n )
  oops

lemma ccorres_pre_getObject_pml4e:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>pml4e. ko_at' pml4e p s \<longrightarrow> P pml4e s))
                  {s. \<forall>pml4e pml4e'. cslift s (pml4e_Ptr p) = Some pml4e' \<and> cpml4e_relation pml4e pml4e'
                           \<longrightarrow> s \<in> P' pml4e}
                          hs (getObject p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wp getPML4E_wp empty_fail_getObject | simp)+
  apply clarsimp
  apply (erule cmap_relationE1 [OF rf_sr_cpml4e_relation],
         erule ko_at_projectKO_opt)
  apply simp
  done

lemma ccorres_pre_getObject_pde:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>pde. ko_at' pde p s \<longrightarrow> P pde s))
                  {s. \<forall>pde pde'. cslift s (pde_Ptr p) = Some pde' \<and> cpde_relation pde pde'
                           \<longrightarrow> s \<in> P' pde}
                          hs (getObject p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wp getPDE_wp empty_fail_getObject | simp)+
  apply clarsimp
  apply (erule cmap_relationE1 [OF rf_sr_cpde_relation],
         erule ko_at_projectKO_opt)
  apply simp
  done

(* FIXME: move *)
(* FIXME: delete duplicates in Corres_C *)
lemma ccorres_abstract_cleanup:
  "ccorres r xf G G' hs a c \<Longrightarrow>
   ccorres r xf G ({s. s \<in> S \<longrightarrow> s \<in> G'} \<inter> S) hs a c"
   by (fastforce intro: ccorres_guard_imp)

lemma ptrFromPAddr_spec:
  "\<forall>s. \<Gamma> \<turnstile>  {s}
  Call ptrFromPAddr_'proc
  \<lbrace>  \<acute>ret__ptr_to_void =  Ptr (ptrFromPAddr (paddr_' s) ) \<rbrace>"
  apply vcg
  apply (simp add: X64.ptrFromPAddr_def X64.pptrBase_def)
  done

lemma addrFromPPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile>  {s}
  Call addrFromPPtr_'proc
  \<lbrace>  \<acute>ret__unsigned_long =  (addrFromPPtr (ptr_val (pptr_' s)) ) \<rbrace>"
  apply vcg
  apply (simp add: addrFromPPtr_def X64.pptrBase_def)
  done

abbreviation
  "lookupPDPTSlot_xf \<equiv> liftxf errstate lookupPDPTSlot_ret_C.status_C lookupPDPTSlot_ret_C.pdptSlot_C ret__struct_lookupPDPTSlot_ret_C_'"

lemma lookupPDPTSlot_ccorres:
  "ccorres (lookup_failure_rel \<currency> (\<lambda>rv rv'. rv' = pdpte_Ptr rv)) lookupPDPTSlot_xf
       (page_map_l4_at' pm)
       (UNIV \<inter> \<lbrace>\<acute>pml4 = Ptr pm \<rbrace> \<inter> \<lbrace>\<acute>vptr = vptr  \<rbrace>)
       []
       (lookupPDPTSlot pm vptr)
       (Call lookupPDPTSlot_'proc)"
  apply (cinit lift: pml4_' vptr_')
   apply (simp add: liftE_bindE)
   apply (rule ccorres_pre_getObject_pml4e)
  sorry (*
   apply csymbr
   apply csymbr
   apply (rule ccorres_abstract_cleanup)
   apply (rule_tac P="(ret__unsigned = scast pde_pde_coarse) = (isPageTablePDE rv)"
               in ccorres_gen_asm2)
   apply (rule ccorres_cond2'[where R=\<top>])
     apply (clarsimp simp: Collect_const_mem)
    apply simp
    apply (rule_tac P=\<top> and P' =UNIV in ccorres_from_vcg_throws)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def)
    apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
    apply (simp add: lookup_fault_missing_capability_lift)
    apply (simp add: mask_def)
   apply (rule ccorres_rhs_assoc)+
   apply (simp add: checkPTAt_def bind_liftE_distrib liftE_bindE
                    returnOk_liftE[symmetric])
   apply (rule ccorres_stateAssert)
   apply (rule_tac P="page_table_at' (ptrFromPAddr (pdeTable rv))
         and ko_at' rv (lookup_pd_slot pd vptr)
         and K (isPageTablePDE rv)" and P'=UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: returnOk_def return_def Collect_const_mem
                         lookup_pd_slot_def word_sle_def)
   apply (frule(1) page_table_at_rf_sr, clarsimp)
   apply (erule cmap_relationE1[OF rf_sr_cpde_relation], erule ko_at_projectKO_opt)
   apply (clarsimp simp: typ_heap_simps cpde_relation_def Let_def isPageTablePDE_def
                         pde_pde_coarse_lift_def pde_pde_coarse_lift
                  split: pde.split_asm)
   apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
    apply (rule unat_le_helper, rule order_trans[OF word_and_le1], simp)
   apply (simp add: word_shift_by_2 lookup_pt_slot_no_fail_def)
   apply (simp add: table_bits_defs mask_def shiftl_t2n)
  apply (clarsimp simp: Collect_const_mem h_t_valid_clift)
  apply (frule(1) page_directory_at_rf_sr, clarsimp)
  apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
   apply (simp add: table_bits_defs)
  apply (clarsimp simp: cpde_relation_def pde_pde_coarse_lift_def
                        pde_pde_coarse_lift Let_def isPageTablePDE_def
                 split: X64_H.pde.split_asm)
  done *)

lemma ccorres_pre_getObject_pdpte:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>pdpte. ko_at' pdpte p s \<longrightarrow> P pdpte s))
                  {s. \<forall>pdpte pdpte'. cslift s (pdpte_Ptr p) = Some pdpte' \<and> cpdpte_relation pdpte pdpte'
                           \<longrightarrow> s \<in> P' pdpte}
                          hs (getObject p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wp getPDPTE_wp empty_fail_getObject | simp)+
  apply clarsimp
  apply (erule cmap_relationE1 [OF rf_sr_cpdpte_relation],
         erule ko_at_projectKO_opt)
  apply simp
  done

abbreviation
  "lookupPDSlot_xf \<equiv> liftxf errstate lookupPDSlot_ret_C.status_C lookupPDSlot_ret_C.pdSlot_C ret__struct_lookupPDSlot_ret_C_'"

lemma pdpte_case_isPageDirectoryPDPTE:
  "(case pdpte of PageDirectoryPDPTE p _ _ _ _ _ \<Rightarrow> fn p | _ \<Rightarrow> g)
    = (if isPageDirectoryPDPTE pdpte then fn (pdpteTable pdpte) else g)"
  by (cases pdpte, simp_all add: isPageDirectoryPDPTE_def)

lemma lookupPDSlot_ccorres:
  "ccorres (lookup_failure_rel \<currency> (\<lambda>rv rv'. rv' = pde_Ptr rv)) lookupPDSlot_xf
       (page_map_l4_at' pm)
       (UNIV \<inter> \<lbrace>\<acute>pml4 = Ptr pm \<rbrace> \<inter> \<lbrace>\<acute>vptr = vptr  \<rbrace>)
       []
       (lookupPDSlot pm vptr)
       (Call lookupPDSlot_'proc)"
  apply (cinit lift: pml4_' vptr_')
   apply (simp add: liftE_bindE pdpte_case_isPageDirectoryPDPTE)
   apply (ctac add: lookupPDPTSlot_ccorres)
      apply (rule ccorres_pre_getObject_pdpte)
      apply (simp del: Collect_const)
      apply (ccorres_rewrite)
  sorry (* FIXME x64: bitfield gen bug, not generating enough spec rules
      apply csymbr



   apply csymbr
   apply csymbr
   apply (rule ccorres_abstract_cleanup)
   apply (rule_tac P="(ret__unsigned = scast pde_pde_coarse) = (isPageTablePDE rv)"
               in ccorres_gen_asm2)
   apply (rule ccorres_cond2'[where R=\<top>])
     apply (clarsimp simp: Collect_const_mem)
    apply simp
    apply (rule_tac P=\<top> and P' =UNIV in ccorres_from_vcg_throws)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def)
    apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
    apply (simp add: lookup_fault_missing_capability_lift)
    apply (simp add: mask_def)
   apply (rule ccorres_rhs_assoc)+
   apply (simp add: checkPTAt_def bind_liftE_distrib liftE_bindE
                    returnOk_liftE[symmetric])
   apply (rule ccorres_stateAssert)
   apply (rule_tac P="page_table_at' (ptrFromPAddr (pdeTable rv))
         and ko_at' rv (lookup_pd_slot pd vptr)
         and K (isPageTablePDE rv)" and P'=UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: returnOk_def return_def Collect_const_mem
                         lookup_pd_slot_def word_sle_def)
   apply (frule(1) page_table_at_rf_sr, clarsimp)
   apply (erule cmap_relationE1[OF rf_sr_cpde_relation], erule ko_at_projectKO_opt)
   apply (clarsimp simp: typ_heap_simps cpde_relation_def Let_def isPageTablePDE_def
                         pde_pde_coarse_lift_def pde_pde_coarse_lift
                  split: pde.split_asm)
   apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
    apply (rule unat_le_helper, rule order_trans[OF word_and_le1], simp)
   apply (simp add: word_shift_by_2 lookup_pt_slot_no_fail_def)
   apply (simp add: table_bits_defs mask_def shiftl_t2n)
  apply (clarsimp simp: Collect_const_mem h_t_valid_clift)
  apply (frule(1) page_directory_at_rf_sr, clarsimp)
  apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
   apply (simp add: table_bits_defs)
  apply (clarsimp simp: cpde_relation_def pde_pde_coarse_lift_def
                        pde_pde_coarse_lift Let_def isPageTablePDE_def
                 split: X64_H.pde.split_asm)
  done *)


abbreviation
  "lookupPTSlot_xf \<equiv> liftxf errstate lookupPTSlot_ret_C.status_C lookupPTSlot_ret_C.ptSlot_C ret__struct_lookupPTSlot_ret_C_'"

lemma lookupPTSlot_ccorres:
  "ccorres (lookup_failure_rel \<currency> (\<lambda>rv rv'. rv' = pte_Ptr rv)) lookupPTSlot_xf
       (page_map_l4_at' pm)
       (UNIV \<inter> \<lbrace>\<acute>vspace = Ptr pm \<rbrace> \<inter> \<lbrace>\<acute>vptr = vptr  \<rbrace>)
       []
       (lookupPTSlot pm vptr)
       (Call lookupPTSlot_'proc)"
  apply (cinit lift: vspace_' vptr_')
   apply (simp add: liftE_bindE)
   apply (ctac add: lookupPDSlot_ccorres)
   apply (rule ccorres_pre_getObject_pde)
      apply simp
      apply csymbr
      apply (rule ccorres_abstract_cleanup)
      apply (rule ccorres_rhs_assoc2)
      apply (rule_tac xf'=ret__int_' and
                      val="from_bool (isPageTablePDE rva)"
                 in ccorres_symb_exec_r_known_rv_UNIV)
apply vcg
apply (clarsimp simp: pde_pde_pt_def)
  sorry (*
thm pde_pde_pt_ptr_get_present_spec
term rf_sr
   apply csymbr
   apply (rule ccorres_abstract_cleanup)
   apply (rule_tac P="(ret__unsigned = scast pde_pde_coarse) = (isPageTablePDE rv)"
               in ccorres_gen_asm2)
   apply (rule ccorres_cond2'[where R=\<top>])
     apply (clarsimp simp: Collect_const_mem)
    apply simp
    apply (rule_tac P=\<top> and P' =UNIV in ccorres_from_vcg_throws)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def)
    apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
    apply (simp add: lookup_fault_missing_capability_lift)
    apply (simp add: mask_def)
   apply (rule ccorres_rhs_assoc)+
   apply (simp add: checkPTAt_def bind_liftE_distrib liftE_bindE
                    returnOk_liftE[symmetric])
   apply (rule ccorres_stateAssert)
   apply (rule_tac P="page_table_at' (ptrFromPAddr (pdeTable rv))
         and ko_at' rv (lookup_pd_slot pd vptr)
         and K (isPageTablePDE rv)" and P'=UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: returnOk_def return_def Collect_const_mem
                         lookup_pd_slot_def word_sle_def)
   apply (frule(1) page_table_at_rf_sr, clarsimp)
   apply (erule cmap_relationE1[OF rf_sr_cpde_relation], erule ko_at_projectKO_opt)
   apply (clarsimp simp: typ_heap_simps cpde_relation_def Let_def isPageTablePDE_def
                         pde_pde_coarse_lift_def pde_pde_coarse_lift
                  split: pde.split_asm)
   apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
    apply (rule unat_le_helper, rule order_trans[OF word_and_le1], simp)
   apply (simp add: word_shift_by_2 lookup_pt_slot_no_fail_def)
   apply (simp add: table_bits_defs mask_def shiftl_t2n)
  apply (clarsimp simp: Collect_const_mem h_t_valid_clift)
  apply (frule(1) page_directory_at_rf_sr, clarsimp)
  apply (subst array_ptr_valid_array_assertionI, erule h_t_valid_clift, simp+)
   apply (simp add: table_bits_defs)
  apply (clarsimp simp: cpde_relation_def pde_pde_coarse_lift_def
                        pde_pde_coarse_lift Let_def isPageTablePDE_def
                 split: X64_H.pde.split_asm)
  done *)


lemma cap_case_isPML4Cap:
  "(case cap of capability.ArchObjectCap (arch_capability.PML4Cap pm ( Some asid))  \<Rightarrow> fn pm asid
                | _ => g)
    = (if ( if (isArchObjectCap cap) then if (isPML4Cap (capCap cap)) then capPML4MappedASID (capCap cap) \<noteq> None else False else False)
                then fn (capPML4BasePtr (capCap cap)) (the ( capPML4MappedASID (capCap cap))) else g)"
  apply (cases cap; simp add: isArchObjectCap_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability, simp_all add: isPML4Cap_def)
  apply (rename_tac option)
  apply (case_tac option; simp)
  done

(* FIXME: MOVE to CSpaceAcc_C *)
lemma ccorres_pre_gets_x86KSASIDTable_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. x64KSASIDTable (ksArchState s) = rv  \<longrightarrow> P rv s))
                  {s. \<forall>rv. s \<in> P' rv }
                          hs (gets (x64KSASIDTable \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply clarsimp
  done

(* FIXME: MOVE to CSpaceAcc_C *)
lemma ccorres_pre_gets_x86KSASIDTable_ksArchState':
  assumes cc: "\<And>rv. ccorres r xf (P and (\<lambda>s. rv = (x64KSASIDTable \<circ> ksArchState) s)) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  P
                  {s. \<forall>rv. s \<in> P' rv }
                          hs (gets (x64KSASIDTable \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply clarsimp
  done

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
  "ccorres (lookup_failure_rel \<currency> (\<lambda>pml4eptrc pml4eptr. pml4eptr = pml4e_Ptr pml4eptrc)) findVSpaceForASID_xf
       (valid_arch_state' and no_0_obj' and (\<lambda>_. asid \<le> mask asid_bits))
       (UNIV \<inter> \<lbrace>\<acute>asid = asid\<rbrace> )
       []
       (findVSpaceForASID asid)
       (Call findVSpaceForASID_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: asid_')
   apply (rule ccorres_assertE)+
   apply (rule ccorres_liftE_Seq)
   apply (simp add: liftME_def bindE_assoc)
   apply (rule ccorres_pre_gets_x86KSASIDTable_ksArchState')
   apply (case_tac "asidTable (ucast (asid_high_bits_of asid))")
    (* Case where the first look-up fails *)
    apply clarsimp
    apply (rule_tac P="valid_arch_state' and _" and P'=UNIV in ccorres_from_vcg_throws)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: throwError_def return_def bindE_def NonDetMonad.lift_def
                          EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def lookup_fault_lift_invalid_root)
    apply (frule rf_sr_asidTable_None[THEN iffD2],
                 fastforce intro: le_mask_imp_and_mask, assumption, assumption)
    apply (fastforce simp: asid_map_asid_map_none_def asid_map_asid_map_vspace_def
                           Kernel_C.asidLowBits_def asid_shiftr_low_bits_less)
  (* Case where the first look-up succeeds *)
  apply clarsimp
  apply (rule ccorres_liftE_Seq)
  apply (rule ccorres_guard_imp)
     apply (rule ccorres_pre_getObject_asidpool)
     apply (rename_tac asidPool)
     apply (case_tac "inv ASIDPool asidPool (asid && mask asid_low_bits) = Some 0")
      apply (fastforce simp: ccorres_fail')
     apply (rule_tac P="\<lambda>s. asidTable=x64KSASIDTable (ksArchState s) \<and>
                            valid_arch_state' s \<and> (asid \<le> mask asid_bits)"
                 and P'="{s'. (\<exists>ap'. cslift s' (ap_Ptr (the (asidTable (ucast (asid_high_bits_of asid)))))
                                               = Some ap' \<and> casid_pool_relation asidPool ap')}"
                  in ccorres_from_vcg_throws_nofail)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: ucast_asid_high_bits_is_shift)
     apply (frule_tac idx="(asid >> asid_low_bits)" in rf_asidTable, assumption,
                      simp add: leq_asid_bits_shift)
     apply (clarsimp simp: typ_heap_simps)
     apply (case_tac asidPool, clarsimp simp: inv_def)
     apply (simp add: casid_pool_relation_def)
     apply (case_tac ap', simp)
     apply (simp add: array_relation_def)
     apply (erule_tac x="(asid && 2 ^ asid_low_bits - 1)" in allE)
     apply (simp add: word_and_le1 mask_def option_to_ptr_def option_to_0_def asid_shiftr_low_bits_less)
     apply (rename_tac "fun" array)
     apply (case_tac "fun (asid && 2 ^ asid_low_bits - 1)", clarsimp)
      apply (clarsimp simp: throwError_def return_def EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def)
      apply (simp add: lookup_fault_lift_invalid_root Kernel_C.asidLowBits_def)
      apply (rule conjI)
       apply (simp add: asid_low_bits_def asid_bits_def)
       apply word_bitwise
      apply (fastforce simp: asid_map_relation_def asid_map_lift_def
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
    apply simp+
  done

(* FIXME x64: there is no USGlobalPML4 in x64, do we need this?
lemma ccorres_pre_gets_armUSGlobalPD_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. armUSGlobalPD (ksArchState s) = rv  \<longrightarrow> P rv s))
                  (P' (ptr_val ((Ptr ::(32 word \<Rightarrow> (pde_C[2048]) ptr)) (symbol_table ''armUSGlobalPD''))))
                          hs (gets (armUSGlobalPD \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply (drule rf_sr_armUSGlobalPD)
  apply simp
  done *)

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

context begin interpretation Arch . (*FIXME: arch_split*)

lemma scast_ucast_down_same:
  "(scast :: word32 \<Rightarrow> word8) = (ucast :: word32 \<Rightarrow> word8)"
  apply (rule down_cast_same [symmetric])
  apply (simp add: is_down_def target_size_def source_size_def word_size)
  done

end

context kernel_m begin


(* FIXME: move *)
(* FIXME x64: needed?
lemma ccorres_h_t_valid_armUSGlobalPD:
  "ccorres r xf P P' hs f (f' ;; g') \<Longrightarrow>
   ccorres r xf P P' hs f
    (Guard C_Guard {s'. s' \<Turnstile>\<^sub>c (Ptr::(32 word \<Rightarrow> (pde_C[2048]) ptr)) (symbol_table ''armUSGlobalPD'')} f';;
    g')"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_move_c_guards[where P = \<top>])
    apply clarsimp
    apply assumption
   apply simp
  by (simp add:rf_sr_def cstate_relation_def Let_def) *)

lemma ccorres_pre_gets_x64KSCurrentCR3_ksArchState:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>rv. x64KSCurrentCR3 (ksArchState s) = rv  \<longrightarrow> P rv s))
                  {s. \<forall>rv. s \<in> P' rv }
                          hs (gets (x64KSCurrentCR3 \<circ> ksArchState) >>= (\<lambda>rv. f rv)) c"
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
  apply clarsimp
  done

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

(* FIXME move *)
lemma fromIntegral_simp_nat[simp]: "(fromIntegral :: nat \<Rightarrow> nat) = id"
  by (simp add: fromIntegral_def fromInteger_nat toInteger_nat)

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

lemma setVMRoot_ccorres:
  "ccorres dc xfdc
      (all_invs_but_ct_idle_or_in_cur_domain' and tcb_at' thread)
      (UNIV \<inter> {s. tcb_' s = tcb_ptr_to_ctcb_ptr thread}) []
        (setVMRoot thread) (Call setVMRoot_'proc)"
  apply (cinit lift: tcb_')
  sorry (* FIXME x64: waiting for bit size changes, and subsequent changes to Ctac_lemmas_C
   apply (rule ccorres_move_array_assertion_tcb_ctes)
   apply (rule ccorres_move_c_guard_tcb_ctes)
   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv)
   apply (ctac)
     apply csymbr
     apply csymbr
     apply (simp add: if_1_0_0 cap_get_tag_isCap_ArchObject2 del: Collect_const)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: cap_case_isPageDirectoryCap cong: if_cong)
      apply (rule ccorres_cond_true_seq)
      apply (rule ccorres_rhs_assoc)
      apply (simp add: throwError_def catch_def dc_def[symmetric])
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_h_t_valid_armUSGlobalPD)
      apply csymbr
      apply (rule ccorres_pre_gets_armUSGlobalPD_ksArchState[unfolded comp_def])
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: setCurrentPD_ccorres)
       apply (rule ccorres_split_throws)
        apply (rule ccorres_return_void_C)
       apply vcg
      apply wp
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr
     apply (rule_tac P="to_bool (capPDIsMapped_CL (cap_page_directory_cap_lift threadRoot))
                              = (capPDMappedASID (capCap rv) \<noteq> None)"
                   in ccorres_gen_asm2)
     apply (simp add: if_1_0_0 to_bool_def del: Collect_const)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: cap_case_isPageDirectoryCap cong: if_cong)
      apply (simp add: throwError_def catch_def)
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_h_t_valid_armUSGlobalPD)
      apply csymbr
      apply (rule ccorres_pre_gets_armUSGlobalPD_ksArchState[unfolded comp_def])
      apply (rule ccorres_add_return2)
      apply (ctac (no_vcg) add: setCurrentPD_ccorres)
       apply (rule ccorres_split_throws)
        apply (rule ccorres_return_void_C [unfolded dc_def])
       apply vcg
      apply wp
     apply (simp add: cap_case_isPageDirectoryCap)
     apply (simp add: catch_def)
     apply csymbr
     apply csymbr
     apply csymbr
     apply (simp add: liftE_bindE)
     apply (simp add: bindE_bind_linearise bind_assoc liftE_def)
     apply (rule_tac f'=lookup_failure_rel and r'="\<lambda>pdeptrc pdeptr. pdeptr = pde_Ptr pdeptrc"
                 and xf'=find_ret_'
                 in ccorres_split_nothrow_case_sum)
          apply (ctac add: findVSpaceForASID_ccorres)
         apply ceqv
        apply (rule_tac P="capPDBasePtr_CL (cap_page_directory_cap_lift threadRoot)
                              = capPDBasePtr (capCap rv)"
                     in ccorres_gen_asm2)
        apply (simp del: Collect_const)
        apply (rule ccorres_Cond_rhs_Seq)
         apply (simp add: whenE_def throwError_def
                          checkPML4NotInASIDMap_def checkPML4ASIDMapMembership_def)
         apply (rule ccorres_stateAssert)
         apply (rule ccorres_pre_gets_armUSGlobalPD_ksArchState[unfolded o_def])
         apply (rule ccorres_rhs_assoc)+
         apply (rule ccorres_h_t_valid_armUSGlobalPD)
         apply csymbr
         apply (rule ccorres_add_return2)
         apply (ctac(no_vcg) add: setCurrentPD_ccorres)
          apply (rule ccorres_split_throws)
           apply (rule ccorres_return_void_C[unfolded dc_def])
          apply vcg
         apply wp
        apply (simp add: whenE_def returnOk_def)
        apply (ctac (no_vcg) add: armv_contextSwitch_ccorres[unfolded dc_def])
         apply (rule ccorres_move_c_guard_tcb)
         apply (rule ccorres_symb_exec_l3)
            apply (rename_tac tcb)
            apply (rule_tac P="ko_at' tcb thread" in ccorres_cross_over_guard)
            apply (ctac add: vcpu_switch_ccorres[unfolded dc_def]) (* c *)
           apply wp
          apply (wp getObject_tcb_wp)
         apply simp
        apply clarsimp
        apply (wp hoare_drop_imp hoare_vcg_ex_lift armv_contextSwitch_invs_no_cicd' valid_case_option_post_wp')
       apply (simp add: checkPML4NotInASIDMap_def checkPML4ASIDMapMembership_def)
       apply (rule ccorres_stateAssert)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_pre_gets_armUSGlobalPD_ksArchState[unfolded o_def])
       apply (rule ccorres_h_t_valid_armUSGlobalPD)
       apply csymbr
       apply (rule ccorres_add_return2)
       apply (ctac(no_vcg) add: setCurrentPD_ccorres)
        apply (rule ccorres_split_throws)
         apply (rule ccorres_return_void_C[unfolded dc_def])
        apply vcg
       apply wp
      apply simp
      apply (wp hoare_drop_imps)[1]
     apply (simp add: Collect_const_mem)
     apply (vcg exspec=findVSpaceForASID_modifies)
    apply (simp add: getSlotCap_def)
    apply (wp getCTE_wp')
   apply (clarsimp simp add:  if_1_0_0 simp del: Collect_const)
   apply vcg
  apply (clarsimp simp: Collect_const_mem word_sle_def)
  apply (rule conjI)
   apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
   apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp+)
   apply (auto simp: isCap_simps valid_cap'_def mask_def dest!: tcb_ko_at')[1]
   apply (rule_tac x=ta in exI, auto split: option.splits)[1]
   apply (frule (2) sym_refs_tcb_vcpu', clarsimp)
   apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def projectKOs)
  apply (clarsimp simp: ptr_val_tcb_ptr_mask'
                        size_of_def cte_level_bits_def
                        tcbVTableSlot_def tcb_cnode_index_defs
                        ccap_rights_relation_def cap_rights_to_H_def
                        to_bool_def true_def allRights_def
                        mask_def[where n="Suc 0"]
                        cte_at_tcb_at_16' addrFromPPtr_def)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject2
                 dest!: isCapDs)
  apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric]
                        cap_lift_page_directory_cap cap_to_H_def
                        cap_page_directory_cap_lift_def
                        to_bool_def
                 elim!: ccap_relationE split: if_split_asm)
  apply (rename_tac s'')
  apply (drule_tac s=s'' in obj_at_cslift_tcb, assumption)
  apply (clarsimp simp: typ_heap_simps)
  apply (clarsimp simp: ctcb_relation_def carch_tcb_relation_def)
  done *)

(* FIXME: move *)
lemma invs'_invs_no_cicd:
  "invs' s \<Longrightarrow> all_invs_but_ct_idle_or_in_cur_domain' s"
by (clarsimp simp add: invs'_def all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def newKernelState_def)

lemma ccorres_seq_IF_False:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (IF False THEN x ELSE y FI ;; c) = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (y ;; c)"
  by simp

(* FIXME x64: needed? *)
lemma ptrFromPAddr_mask6_simp[simp]:
  "ptrFromPAddr ps && mask 6 = ps && mask 6"
  unfolding ptrFromPAddr_def X64.pptrBase_def
  by (subst add.commute, subst mask_add_aligned ; simp add: is_aligned_def)

(* FIXME: move *)
lemma register_from_H_bound[simp]:
  "unat (register_from_H v) < 23"
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

(* FIXME x64: haskell msg registers are wrong, see VER-830 *)
lemma msgRegisters_ccorres:
  "n < unat n_msgRegisters \<Longrightarrow>
  register_from_H (X64_H.msgRegisters ! n) = (index kernel_all_substitute.msgRegisters n)"
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

(* FIXME x64: what stops padding bits not being 1 in bitfield struct *)
lemma wordFromMessageInfo_spec:
  defines "mil s \<equiv> seL4_MessageInfo_lift \<^bsup>s\<^esup>mi"
  shows "\<forall>s. \<Gamma> \<turnstile> {s} Call wordFromMessageInfo_'proc
                  \<lbrace>\<acute>ret__unsigned_long = (label_CL (mil s) << 12)
                                      || (capsUnwrapped_CL (mil s) << 9)
                                      || (extraCaps_CL (mil s) << 7)
                                      || length_CL (mil s)\<rbrace>"
  unfolding mil_def
  apply vcg
  apply (simp add: seL4_MessageInfo_lift_def mask_shift_simps word_sless_def word_sle_def)
thm wordFromMessageInfo_body_def
  apply word_bitwise
  sorry

lemmas wordFromMessageInfo_spec2 = wordFromMessageInfo_spec

lemma wordFromMessageInfo_ccorres [corres]:
  "\<And>mi. ccorres (op =) ret__unsigned_long_' \<top> {s. mi = message_info_to_H (mi_' s)} []
           (return (wordFromMessageInfo mi)) (Call wordFromMessageInfo_'proc)"
  apply (rule ccorres_from_spec_modifies [where P = \<top>, simplified])
     apply (rule wordFromMessageInfo_spec)
    apply (rule wordFromMessageInfo_modifies)
   apply simp
  apply simp
  apply (simp add: return_def wordFromMessageInfo_def Let_def message_info_to_H_def
    Types_H.msgLengthBits_def Types_H.msgExtraCapBits_def
    Types_H.msgMaxExtraCaps_def shiftL_nat word_bw_assocs word_bw_comms word_bw_lcs)
  done

(* FIXME move *)
lemma unat_register_from_H_range:
  "unat (register_from_H r) < 23"
  by (case_tac r, simp_all add: C_register_defs)

(* FIXME move *)
lemma register_from_H_eq:
  "(r = r') = (register_from_H r = register_from_H r')"
  apply (case_tac r, simp_all add: C_register_defs)
                   by (case_tac r', simp_all add: C_register_defs)+

(* FIXME x64: this will break with msgRegister changes *)
lemma setMessageInfo_ccorres:
  "ccorres dc xfdc (tcb_at' thread)
           (UNIV \<inter> \<lbrace>mi = message_info_to_H mi'\<rbrace>) hs
           (setMessageInfo thread mi)
           (\<acute>ret__unsigned_long :== CALL wordFromMessageInfo(mi');;
            CALL setRegister(tcb_ptr_to_ctcb_ptr thread, scast Kernel_C.msgInfoRegister, \<acute>ret__unsigned_long))"
  unfolding setMessageInfo_def
  apply (rule ccorres_guard_imp2)
   apply ctac
     apply simp
     apply (ctac add: setRegister_ccorres)
    apply wp
   apply vcg
  apply (simp add: X64_H.msgInfoRegister_def X64.msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def Kernel_C.RSI_def)
  done

(* FIXME x64: msgRegister changes *)
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
   apply (clarsimp simp add: setMRs_def zipWithM_x_mapM_x mapM_x_Nil length_of_msgRegisters zip_singleton msgRegisters_unfold mapM_x_singleton)
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
  apply (auto simp: X64_H.fromPAddr_def message_info_to_H_def mask_def X64_H.msgInfoRegister_def
                    X64.msgInfoRegister_def Kernel_C.msgInfoRegister_def Kernel_C.RSI_def
                    word_sle_def word_sless_def Kernel_C.RDI_def
                    kernel_all_global_addresses.msgRegisters_def fupdate_def Arrays.update_def
                    fcp_beta)
  done

lemma ignoreFailure_liftM:
  "ignoreFailure = liftM (\<lambda>v. ())"
  apply (rule ext)+
  apply (simp add: ignoreFailure_def liftM_def
                   catch_def)
  apply (rule bind_apply_cong[OF refl])
  apply (simp split: sum.split)
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

(* FIXME x64: this may need revising, check proof of unmapPage_ccorres *)
lemma checkMappingPPtr_pte_ccorres:
  assumes pre:
    "\<And>pte \<sigma>. \<Gamma> \<turnstile> {s. True \<and> (\<exists>pte'. cslift s (pte_Ptr pte_ptr) = Some pte' \<and> cpte_relation pte pte')
                            \<and> (\<sigma>, s) \<in> rf_sr}
           call1 ;; Cond S return_void_C Skip
       {s. (\<sigma>, s) \<in> rf_sr \<and> (isSmallPagePTE pte) \<and> pteFrame pte = addrFromPPtr pptr},
       {s. (\<sigma>, s) \<in> rf_sr \<and> \<not> ((isSmallPagePTE pte) \<and> pteFrame pte = addrFromPPtr pptr)}"
  shows
  "ccorres_underlying rf_sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel dc) xfdc
       \<top> UNIV [SKIP]
     (doE
         pte \<leftarrow> withoutFailure $ getObject pte_ptr;
         checkMappingPPtr pptr (VMPTE pte)
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
         apply (fold_subgoals (prefix))[2]
         subgoal by (auto simp: in_monad Bex_def isSmallPagePTE_def
                         split: pte.split vmpage_size.split)
       apply (wp empty_fail_getObject | simp)+
      apply (erule cmap_relationE1[OF rf_sr_cpte_relation])
       apply (erule ko_at_projectKO_opt)
      apply simp
     apply (wp empty_fail_getObject | simp add: objBits_simps archObjSize_def bit_simps)+
  done

(* FIXME x64: this may need revising *)
lemma checkMappingPPtr_pde_ccorres:
  assumes pre:
    "\<And>pde \<sigma>. \<Gamma> \<turnstile> {s. True \<and> (\<exists>pde'. cslift s (pde_Ptr pde_ptr) = Some pde' \<and> cpde_relation pde pde')
                            \<and> (\<sigma>, s) \<in> rf_sr}
           call1;; Cond S return_void_C Skip
       {s. (\<sigma>, s) \<in> rf_sr \<and> (isLargePagePDE pde) \<and> pdeFrame pde = addrFromPPtr pptr},
       {s. (\<sigma>, s) \<in> rf_sr \<and> \<not> ((isLargePagePDE pde) \<and> pdeFrame pde = addrFromPPtr pptr)}"
  shows
  "ccorres_underlying rf_sr \<Gamma> (inr_rrel dc) xfdc (inl_rrel dc) xfdc
       \<top> UNIV [SKIP]
     (doE
         pde \<leftarrow> withoutFailure $ getObject pde_ptr;
         checkMappingPPtr pptr (VMPDE pde)
      odE)
     (call1;; Cond S return_void_C Skip)"
  apply (simp add: checkMappingPPtr_def liftE_bindE)
  apply (rule ccorres_symb_exec_l[where Q'="\<lambda>_. UNIV", OF _ _ getObject_ko_at, simplified])
      apply (rule stronger_ccorres_guard_imp)
        apply (rule ccorres_from_vcg_might_throw[where P=\<top>])
        apply (rule allI)
        apply (rule conseqPost, rule conseqPre, rule_tac \<sigma>1=\<sigma> and pde1=rv in pre)
          apply clarsimp
          apply (erule CollectE, assumption)
         apply (fold_subgoals (prefix))[2]
         subgoal by (auto simp: in_monad Bex_def isLargePagePDE_def
                         split: pde.split vmpage_size.split)
       apply (wp empty_fail_getObject | simp)+
      apply (erule cmap_relationE1[OF rf_sr_cpde_relation])
       apply (erule ko_at_projectKO_opt)
      apply simp
     apply (wp empty_fail_getObject | simp add: objBits_simps archObjSize_def bit_simps)+
  done

lemma checkMappingPPtr_pdpte_ccorres:
  assumes pre:
    "\<And>pdpte \<sigma>. \<Gamma> \<turnstile> {s. True \<and> (\<exists>pdpte'. cslift s (pdpte_Ptr pdpte_ptr) = Some pdpte' \<and> cpdpte_relation pdpte pdpte')
                            \<and> (\<sigma>, s) \<in> rf_sr}
           call1;;
           Cond S (return_C ret__unsigned_long_'_update (\<lambda>s. SCAST(32 signed \<rightarrow> 64) false)) Skip
       {s. (\<sigma>, s) \<in> rf_sr \<and> (isHugePagePDPTE pdpte) \<and> pdpteFrame pdpte = addrFromPPtr pptr},
       {s. (\<sigma>, s) \<in> rf_sr \<and> \<not> ((isHugePagePDPTE pdpte) \<and> pdpteFrame pdpte = addrFromPPtr pptr)
                          \<and> ret__unsigned_long_' s = scast false }"
  shows
  "ccorres_underlying rf_sr \<Gamma>
     (inr_rrel dc) xfdc
     (inl_rrel (\<lambda>rv rv'. rv' = scast false)) ret__unsigned_long_'
     \<top> UNIV (SKIP # hs)
     (doE
        pdpte \<leftarrow> liftE (getObject pdpte_ptr);
        checkMappingPPtr pptr (VMPDPTE pdpte)
     odE)
     (call1;;
      Cond S (return_C ret__unsigned_long_'_update (\<lambda>s. SCAST(32 signed \<rightarrow> 64) false)) Skip)"
  apply (simp add: checkMappingPPtr_def liftE_bindE)
  apply (rule ccorres_symb_exec_l[where Q'="\<lambda>_. UNIV", OF _ _ getObject_ko_at, simplified])
      apply (rule stronger_ccorres_guard_imp)
        apply (rule ccorres_from_vcg_might_throw[where P=\<top>])
        apply (rule allI)
        apply (rule conseqPost, rule conseqPre, rule_tac \<sigma>1=\<sigma> and pdpte1=rv in pre)
          apply clarsimp
          apply (erule CollectE, assumption)
         apply (clarsimp split: pdpte.split_asm
                          simp: isHugePagePDPTE_def throwError_def returnOk_def return_def
                                EXCEPTION_NONE_def EXCEPTION_LOOKUP_FAULT_def
                                lookup_fault_lift_invalid_root)+
      apply (erule cmap_relationE1[OF rf_sr_cpdpte_relation])
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

lemma makeUserPTEInvalid_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       \<acute>ret__struct_pte_C :== PROC makeUserPTEInvalid()
       \<lbrace> pte_lift \<acute>ret__struct_pte_C = \<lparr>
            pte_CL.xd_CL = 0, pte_CL.page_base_address_CL = 0,
            pte_CL.global_CL = 0, pte_CL.pat_CL = 0,
            pte_CL.dirty_CL = 0, pte_CL.accessed_CL = 0,
            pte_CL.cache_disabled_CL = 0, pte_CL.write_through_CL = 0,
            pte_CL.super_user_CL = 0, pte_CL.read_write_CL = 0,
            pte_CL.present_CL = 0 \<rparr> \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: makeUserPTEInvalid_body_def makeUserPTEInvalid_impl
                        pte_lift_def Let_def)
  done

lemma makeUserPDEInvalid_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       \<acute>ret__struct_pde_C :== PROC makeUserPDEInvalid()
       \<lbrace> pde_lift \<acute>ret__struct_pde_C = Some (Pde_pde_pt \<lparr>
            pde_pde_pt_CL.xd_CL = 0,
            pde_pde_pt_CL.pt_base_address_CL = 0,
            pde_pde_pt_CL.accessed_CL = 0,
            pde_pde_pt_CL.cache_disabled_CL = 0,
            pde_pde_pt_CL.write_through_CL = 0,
            pde_pde_pt_CL.super_user_CL = 0,
            pde_pde_pt_CL.read_write_CL = 0,
            pde_pde_pt_CL.present_CL = 0 \<rparr>) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: makeUserPDEInvalid_body_def makeUserPDEInvalid_impl
                        pde_lift_def Let_def pde_get_tag_def pde_tag_defs pde_pde_pt_lift_def)
  done

lemma makeUserPDPTEInvalid_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       \<acute>ret__struct_pdpte_C :== PROC makeUserPDPTEInvalid()
       \<lbrace> pdpte_lift \<acute>ret__struct_pdpte_C = Some (Pdpte_pdpte_pd \<lparr>
            pdpte_pdpte_pd_CL.xd_CL = 0,
            pdpte_pdpte_pd_CL.pd_base_address_CL = 0,
            pdpte_pdpte_pd_CL.accessed_CL = 0,
            pdpte_pdpte_pd_CL.cache_disabled_CL = 0,
            pdpte_pdpte_pd_CL.write_through_CL = 0,
            pdpte_pdpte_pd_CL.super_user_CL = 0,
            pdpte_pdpte_pd_CL.read_write_CL = 0,
            pdpte_pdpte_pd_CL.present_CL = 0 \<rparr>) \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: makeUserPDPTEInvalid_body_def makeUserPDPTEInvalid_impl
                        pdpte_lift_def Let_def pdpte_get_tag_def pdpte_tag_defs
                        pdpte_pdpte_pd_lift_def)
  done

lemma makeUserPML4EInvalid_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       \<acute>ret__struct_pml4e_C :== PROC makeUserPML4EInvalid()
       \<lbrace> pml4e_lift \<acute>ret__struct_pml4e_C = \<lparr>
            pml4e_CL.xd_CL = 0,
            pml4e_CL.pdpt_base_address_CL = 0,
            pml4e_CL.accessed_CL = 0,
            pml4e_CL.cache_disabled_CL = 0,
            pml4e_CL.write_through_CL = 0,
            pml4e_CL.super_user_CL = 0,
            pml4e_CL.read_write_CL = 0,
            pml4e_CL.present_CL = 0 \<rparr> \<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1) (* force vcg to unfold non-recursive procedure *)
  apply vcg
  apply (clarsimp simp: makeUserPML4EInvalid_body_def makeUserPML4EInvalid_impl
                        pml4e_lift_def Let_def pml4e_lift_def)
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

(* FIXME x64
(* 7 = log2 (pte size * 16), where pte size is 8
   496 = number of entries in pt - 16, where number of entries is 512 *)
lemma large_ptSlot_array_constraint:
  "is_aligned (ptSlot :: word32) 7 \<Longrightarrow> n \<le> limit - 496 \<and> 496 \<le> limit
    \<Longrightarrow> \<exists>i. ptSlot = (ptSlot && ~~ mask ptBits) + of_nat i * 8 \<and> i + n \<le> limit"
  apply (rule_tac x="unat ((ptSlot && mask ptBits) >> 3)" in exI)
  apply (simp add: shiftl_t2n[where n=3, symmetric, THEN trans[rotated],
                   OF mult.commute, simplified])
  apply (simp add: shiftr_shiftl1)
  apply (rule conjI, rule trans,
         rule word_plus_and_or_coroll2[symmetric, where w="mask ptBits"])
   apply (simp, rule aligned_neg_mask[THEN sym], rule is_aligned_andI1,
          erule is_aligned_weaken, simp)
  apply (clarsimp simp add: le_diff_conv2)
  apply (erule order_trans[rotated], simp)
  apply (rule unat_le_helper)
  apply (simp add: is_aligned_mask mask_def table_bits_defs)
  apply (word_bitwise, simp?)
  done
*)

(* FIXME x64
(* pde size is 8
   2032 = number of entries in pd - 16, where number of entries is 2048 *)
lemma large_pdSlot_array_constraint:
  "is_aligned pd pdBits \<Longrightarrow> vmsz_aligned vptr ARMSuperSection \<Longrightarrow> n \<le> limit - 2032 \<and> 2032 \<le> limit
    \<Longrightarrow> \<exists>i. lookup_pd_slot pd vptr = pd + of_nat i * 8 \<and> i + n \<le> limit"
  apply (rule_tac x="unat (vptr >> 21)" in exI)
  apply (rule conjI)
   apply (simp add: lookup_pd_slot_def shiftl_t2n table_bits_defs)
  apply (clarsimp simp add: le_diff_conv2)
  apply (erule order_trans[rotated], simp)
  apply (rule unat_le_helper)
  apply (simp add: is_aligned_mask mask_def table_bits_defs
                   vmsz_aligned_def)
  apply (word_bitwise, simp?)
  done *)

lemma findVSpaceForASID_page_map_l4_at'_simple[wp]:
  notes checkPML4At_inv[wp del]
  shows "\<lbrace>\<top>\<rbrace> findVSpaceForASID asiv
    \<lbrace>\<lambda>rv s. page_map_l4_at' rv s\<rbrace>,-"
  apply (simp add:findVSpaceForASID_def)
   apply (wpsimp wp:getASID_wp simp:checkPML4At_def)
  done

(* FIXME x64: redo as required
lemma array_assertion_abs_pte_16:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_table_at' (ptr_val ptPtr && ~~ mask ptBits) s
        \<and> is_aligned (ptr_val ptPtr) 7) \<and> (n s' \<le> 16 \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (ptPtr :: pte_C ptr) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (drule(1) page_table_at_rf_sr, clarsimp)
  apply (cases ptPtr, simp)
  apply (erule clift_array_assertion_imp, simp_all)
  apply (rule large_ptSlot_array_constraint, simp_all)
  done

lemmas ccorres_move_array_assertion_pte_16
    = ccorres_move_array_assertions [OF array_assertion_abs_pte_16]

lemma array_assertion_abs_pde_16:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (page_directory_at' pd s
        \<and> vmsz_aligned vptr ARMSuperSection) \<and> (n s' \<le> 16 \<and> (x s' \<noteq> 0 \<longrightarrow> n s' \<noteq> 0))
    \<longrightarrow> (x s' = 0 \<or> array_assertion (pde_Ptr (lookup_pd_slot pd vptr)) (n s') (hrs_htd (t_hrs_' (globals s'))))"
  apply (intro allI impI disjCI2, clarsimp)
  apply (frule(1) page_directory_at_rf_sr, clarsimp)
  apply (erule clift_array_assertion_imp, simp_all)
  apply (rule large_pdSlot_array_constraint, simp_all add: page_directory_at'_def)
  done

lemmas array_assertion_abs_pde_16_const = array_assertion_abs_pde_16[where x="\<lambda>_. Suc 0",
    simplified nat.simps simp_thms]

lemmas ccorres_move_array_assertion_pde_16
    = ccorres_move_Guard_Seq [OF array_assertion_abs_pde_16]
      ccorres_move_Guard [OF array_assertion_abs_pde_16]
      ccorres_move_Guard_Seq [OF array_assertion_abs_pde_16]
      ccorres_move_Guard [OF array_assertion_abs_pde_16]
      ccorres_move_Guard_Seq [OF array_assertion_abs_pde_16_const]
      ccorres_move_Guard [OF array_assertion_abs_pde_16_const]
      ccorres_move_Guard_Seq [OF array_assertion_abs_pde_16_const]
      ccorres_move_Guard [OF array_assertion_abs_pde_16_const]
*)

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
          (* FIXME(sproul): clean this up *)
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

lemmas ccorres_name_ksCurThread = ccorres_pre_getCurThread[where f="\<lambda>_. f'" for f',
    unfolded getCurThread_def, simplified gets_bind_ign]

lemma unmapPage_ccorres:
  "ccorres dc xfdc (invs' and (\<lambda>s. 2 ^ pageBitsForSize sz \<le> gsMaxObjectSize s)
                          and (\<lambda>_. asid \<le> mask asid_bits \<and> vmsz_aligned' vptr sz
                                           \<and> vptr < pptrBase))
      (UNIV \<inter> {s. framesize_to_H (page_size_' s) = sz \<and> page_size_' s < 3}
            \<inter> {s. asid_' s = asid} \<inter> {s. vptr_' s = vptr} \<inter> {s. pptr_' s = Ptr pptr}) []
      (unmapPage sz asid vptr pptr) (Call unmapPage_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: page_size_' asid_' vptr_' pptr_')
   apply (simp add: ignoreFailure_liftM Collect_True
               del: Collect_const)
   apply (ctac add: findVSpaceForASID_ccorres)
      apply (rename_tac pmPtr pm')
      apply (rule_tac P="page_map_l4_at' pmPtr" in ccorres_cross_over_guard)
      apply (simp add: liftE_bindE Collect_False bind_bindE_assoc
                  del: Collect_const)
      apply (rule ccorres_splitE_novcg[where r'=dc and xf'=xfdc])
          -- "X64SmallPage"
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
          -- "X64LargePage"
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
                                        isLargePagePDE_def if_1_0_0 pde_get_tag_def pde_tag_defs
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
          -- "X64HugePage"
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
        apply (rule ccorres_move_array_assertion_tcb_ctes ccorres_move_c_guard_tcb_ctes)+
        apply (rule ccorres_symb_exec_r)
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV and xf'=ret__int_' and val=1])
             apply vcg
             apply clarsimp
            apply ceqv
           apply ccorres_rewrite
           apply (clarsimp simp: liftE_liftM)
           apply (ctac add: invalidateTranslationSingleASID_ccorres[simplified dc_def])
          apply vcg
         apply clarsimp
         apply vcg
        apply (rule conseqPre, vcg)
        apply clarsimp
       apply (wpsimp simp: cur_tcb'_def[symmetric])
      apply (clarsimp simp: guard_is_UNIV_def conj_comms tcb_cnode_index_defs)
     apply (simp add: throwError_def)
     apply (rule ccorres_split_throws)
      apply (rule ccorres_return_void_C[unfolded dc_def])
     apply vcg
    apply wpsimp
   apply (simp add: Collect_const_mem)
   apply (vcg exspec=findVSpaceForASID_modifies)
  by (auto simp: invs_arch_state' invs_no_0_obj' invs_valid_objs' vmsz_aligned'_def
                 is_aligned_weaken[OF _ pbfs_atleast_pageBits] pageBitsForSize_def
                 Collect_const_mem vm_page_size_defs word_sle_def
                 ccHoarePost_def typ_heap_simps bit_simps
            dest!: page_directory_at_rf_sr
            elim!: clift_array_assertion_imp
            split: vmpage_size.splits
            elim: is_aligned_weaken
      | unat_arith)+

(* FIXME: move *)
lemma cap_to_H_PageCap_tag:
  "\<lbrakk> cap_to_H cap = ArchObjectCap (PageCap p R sz mt d A);
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_frame_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     by (simp_all add: Let_def cap_lift_def split_def split: if_splits)

(* FIXME x64: we now call 3 functions rather than just generic_frame_cap_ptr_set...
              so this will need to be redone whilst proving performPageInvocation_ccorres *)
lemma updateCap_frame_mapped_addr_ccorres:
  notes option.case_cong_weak [cong]
  shows "ccorres dc xfdc
           (cte_wp_at' (\<lambda>c. ArchObjectCap cap = cteCap c) ctSlot and K (isPageCap cap))
           UNIV []
           (updateCap ctSlot (ArchObjectCap (capVPMappedAddress_update empty cap)))
           (CALL cap_frame_cap_ptr_set_capFMappedAddress(cap_Ptr &(cte_Ptr ctSlot\<rightarrow>[''cap_C'']),0);;
            CALL cap_frame_cap_ptr_set_capFMappedASID(cap_Ptr &(cte_Ptr ctSlot \<rightarrow>[''cap_C'']), (scast asidInvalid)))"
  unfolding updateCap_def
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_pre_getCTE)
   apply (rule_tac P = "\<lambda>s. ctes_of s ctSlot = Some cte
                             \<and> cteCap cte = ArchObjectCap cap \<and> isPageCap cap" and
                   P' = "UNIV"
                in ccorres_from_vcg)
  sorry (*
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (erule (1) rf_sr_ctes_of_cliftE)
   apply (frule cap_CL_lift)
   apply (clarsimp simp: typ_heap_simps)
   apply (rule conjI)
    apply (clarsimp simp: isCap_simps)
    apply (drule cap_CL_lift)
    apply (drule (1) cap_to_H_PageCap_tag)
    apply simp
   apply (clarsimp simp: isCap_simps)
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI [rotated])
   apply clarsimp
   apply (frule (1) rf_sr_ctes_of_clift)
   apply clarsimp
   apply (subgoal_tac "ccte_relation (cteCap_update (\<lambda>_. ArchObjectCap (PageCap v0 v1 v2 v3 d None)) (cte_to_H ctel')) (cte_C.cap_C_update (\<lambda>_. capa) cte')")
    prefer 2
    apply (clarsimp simp: ccte_relation_def)
    apply (clarsimp simp: cte_lift_def)
    apply (simp split: option.splits)
    apply clarsimp
    apply (simp add: cte_to_H_def c_valid_cte_def)
    apply (rule conjI, simp add: cap_lift_frame_cap)
    apply (clarsimp)
    apply (erule (4) generic_frame_mapped_address)
   apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps
     Let_def cpspace_relation_def)
   apply (rule conjI)
    apply (erule (3) cmap_relation_updI)
    subgoal by simp
   apply (erule_tac t = s' in ssubst)
   apply (simp add: heap_to_user_data_def)
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                         typ_heap_simps h_t_valid_clift_Some_iff
                         cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done *)

(* FIXME: move *)
lemma diminished_PageCap:
  "diminished' (ArchObjectCap (PageCap p R mt sz d a)) cap \<Longrightarrow>
  \<exists>R'. cap = ArchObjectCap (PageCap p R' mt sz d a)"
  apply (clarsimp simp: diminished'_def)
  apply (clarsimp simp: maskCapRights_def Let_def)
  apply (cases cap, simp_all add: isCap_simps)
  apply (simp add: X64_H.maskCapRights_def)
  apply (simp add: isPageCap_def split: arch_capability.splits)
  done

(* FIXME: move *)
lemma aligend_mask_disjoint:
  "\<lbrakk>is_aligned (a :: machine_word) n; b \<le> mask n; n < word_bits\<rbrakk> \<Longrightarrow> a && b = 0"
  apply (rule word_eqI)
  apply (clarsimp simp: is_aligned_nth word_size mask_def simp del: word_less_sub_le)
  apply (drule le2p_bits_unset_64[OF word_less_sub_1])
  apply (case_tac "na < n")
   apply simp
  apply (simp add: linorder_not_less word_bits_def)
  done

(* FIXME: move *)
lemma word_aligend_0_sum:
  "\<lbrakk> a + b = 0; is_aligned (a :: machine_word) n; b \<le> mask n; n < word_bits \<rbrakk> \<Longrightarrow> a = 0 \<and> b = 0"
  by (simp add: word_plus_and_or_coroll aligend_mask_disjoint word_or_zero)

(* FIXME: move *)
lemma getSlotCap_wp':
  "\<lbrace>\<lambda>s. \<forall>cap. cte_wp_at' (\<lambda>c. cteCap c = cap) p s \<longrightarrow> Q cap s\<rbrace> getSlotCap p \<lbrace>Q\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma vmsz_aligned_aligned_pageBits:
  "vmsz_aligned' ptr sz \<Longrightarrow> is_aligned ptr pageBits"
  apply (simp add: vmsz_aligned'_def)
  apply (erule is_aligned_weaken)
  apply (simp add: pageBits_def pageBitsForSize_def
            split: vmpage_size.split)
  done

(*
lemma ccap_relation_PageCap_generics:
  "ccap_relation (ArchObjectCap (PageCap d ptr rghts sz mapdata)) cap'
    \<Longrightarrow> (mapdata \<noteq> None \<longrightarrow>
           generic_frame_cap_get_capFMappedAddress_CL (cap_lift cap')
                    = snd (the mapdata)
         \<and> generic_frame_cap_get_capFMappedASID_CL (cap_lift cap')
                    = fst (the mapdata))
      \<and> ((generic_frame_cap_get_capFMappedASID_CL (cap_lift cap') = 0)
                    = (mapdata = None))
      \<and> vmrights_to_H (generic_frame_cap_get_capFVMRights_CL (cap_lift cap')) = rghts
      \<and> gen_framesize_to_H (generic_frame_cap_get_capFSize_CL (cap_lift cap')) = sz
      \<and> generic_frame_cap_get_capFBasePtr_CL (cap_lift cap') = ptr
      \<and> generic_frame_cap_get_capFVMRights_CL (cap_lift cap') < 4
      \<and> generic_frame_cap_get_capFSize_CL (cap_lift cap') < 4
      \<and> to_bool (generic_frame_cap_get_capFIsDevice_CL (cap_lift cap')) = d"
  apply (frule ccap_relation_mapped_asid_0)
  apply (case_tac "sz = ARMSmallPage")
   apply (frule(1) cap_get_tag_isCap_unfolded_H_cap)
   apply (clarsimp simp: cap_lift_small_frame_cap cap_to_H_def
                         generic_frame_cap_get_capFMappedAddress_CL_def
                         generic_frame_cap_get_capFVMRights_CL_def
                         generic_frame_cap_get_capFSize_CL_def
                         generic_frame_cap_get_capFMappedASID_CL_def
                         generic_frame_cap_get_capFBasePtr_CL_def
                         generic_frame_cap_get_capFIsDevice_CL_def
                  elim!: ccap_relationE)
   apply (simp add: gen_framesize_to_H_def)
   apply (simp add: vm_page_size_defs order_le_less_trans [OF word_and_le1] mask_def
             split: if_split)
   apply (clarsimp split: if_split_asm)
  apply (frule(1) cap_get_tag_isCap_unfolded_H_cap)
  apply (clarsimp simp: cap_lift_frame_cap cap_to_H_def
                        generic_frame_cap_get_capFMappedAddress_CL_def
                        generic_frame_cap_get_capFVMRights_CL_def
                        generic_frame_cap_get_capFSize_CL_def
                        generic_frame_cap_get_capFMappedASID_CL_def
                        generic_frame_cap_get_capFBasePtr_CL_def
                        generic_frame_cap_get_capFIsDevice_CL_def
                        c_valid_cap_def cl_valid_cap_def
                        option_to_0_def
                 elim!: ccap_relationE)
  apply (simp add: gen_framesize_to_H_is_framesize_to_H_if_not_ARMSmallPage)
  apply (simp add: vm_page_size_defs order_le_less_trans [OF word_and_le1] mask_def
            split: if_split)
  apply (clarsimp split: if_split_asm)
  done
*)

lemma performPageInvocationUnmap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' (diminished' (ArchObjectCap cap) o cteCap) ctSlot and K (isPageCap cap))
       (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap cap) \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performPageInvocation (PageUnmap cap ctSlot)))
       (Call performX86PageInvocationUnmap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: cap_' ctSlot_')
   apply clarsimp
   apply csymbr
   apply (rule ccorres_guard_imp [where A=
               "invs'
                and cte_wp_at' (diminished' (ArchObjectCap cap) o cteCap) ctSlot
                and K (isPageCap cap)"])

     apply wpc
  sorry (* FIXME x64: need to figure out if we put maptype check into haskell or change c
      apply (rule_tac P=" ret__unsigned_long = 0" in ccorres_gen_asm)
      apply simp
      apply (rule ccorres_symb_exec_l)
         apply (subst bind_return [symmetric])
         apply (rule ccorres_split_nothrow_novcg)
             apply (rule ccorres_Guard)
             apply (rule updateCap_frame_mapped_addr_ccorres)
            apply ceqv
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
          apply wp[1]
         apply (simp add: guard_is_UNIV_def)
        apply (wp getSlotCap_wp', simp)
       apply (wp getSlotCap_wp')
      apply simp
     apply (rule_tac P=" ret__unsigned_long \<noteq> 0" in ccorres_gen_asm)
     apply (simp cong: Guard_no_cong)
     apply (rule ccorres_rhs_assoc)+
     apply (csymbr)
     apply csymbr
     apply csymbr
     apply csymbr
     apply wpc
     apply (ctac (no_vcg) add: unmapPage_ccorres)
      apply (rule ccorres_add_return2)
      apply (rule ccorres_split_nothrow_novcg)
          apply (rule ccorres_move_Guard [where P="cte_at' ctSlot" and P'=\<top>])
           apply (clarsimp simp: cte_wp_at_ctes_of)
           apply (drule (1) rf_sr_ctes_of_clift)
           apply (fastforce intro: typ_heap_simps)
          apply (rule ccorres_symb_exec_l)
             apply (rule updateCap_frame_mapped_addr_ccorres)
            apply (wp getSlotCap_wp', simp)
           apply (wp getSlotCap_wp')
          apply simp
         apply ceqv
        apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: return_def)
       apply wp[1]
      apply (simp add: guard_is_UNIV_def)
     apply (simp add: cte_wp_at_ctes_of)
     apply wp
    apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps split: if_split)
    apply (drule diminished_PageCap)
    apply clarsimp
    apply (drule ccap_relation_mapped_asid_0)
    apply (frule ctes_of_valid', clarsimp)
    apply (drule valid_global_refsD_with_objSize, clarsimp)
    apply (clarsimp simp: mask_def valid_cap'_def
                          vmsz_aligned_aligned_pageBits)
   apply assumption
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps split: if_split)
  apply (drule diminished_PageCap)
  apply clarsimp
  apply (frule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps')
  apply (frule ccap_relation_PageCap_generics)
  apply (case_tac "v2 = ARMSmallPage")
   apply (auto simp add: cap_get_tag_isCap_ArchObject2 isCap_simps)
  done *)

lemma SuperUserFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace> Call SuperUserFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned = superuser_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  apply vcg
  apply (simp add: vmrights_to_H_def superuser_from_vm_rights_def Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply clarsimp
  apply (drule word_less_cases, auto)+
  done


lemma superuser_from_vm_rights_mask:
  "ucast ((superuser_from_vm_rights R) :: 32 word) && 1 = (superuser_from_vm_rights R :: machine_word)"
  by (simp add: superuser_from_vm_rights_def split: vmrights.splits)

lemma WritableFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0\<rbrace> Call WritableFromVMRights_'proc
  \<lbrace> \<acute>ret__unsigned = writable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) \<rbrace>"
  apply vcg
  apply (simp add: vmrights_to_H_def writable_from_vm_rights_def Kernel_C.VMKernelOnly_def
                   Kernel_C.VMReadOnly_def Kernel_C.VMReadWrite_def)
  apply clarsimp
  apply (drule word_less_cases, auto)+
  done

lemma writable_from_vm_rights_mask:
  "ucast ((writable_from_vm_rights R) :: 32 word) && 1 = (writable_from_vm_rights R :: machine_word)"
  by (simp add: writable_from_vm_rights_def split: vmrights.splits)

lemma mask_eq1_nochoice:
  "(x:: word32) && 1 = x \<Longrightarrow> x = 0 \<or> x = 1"
  apply (simp add:mask_eq_iff[where n = 1,unfolded mask_def,simplified])
  apply (drule word_2p_lem[where n = 1 and w = x,symmetric,simplified,THEN iffD1,rotated])
   apply (simp add:word_size)
  apply word_bitwise
  apply clarsimp
  done

lemma makeUserPTE_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0 \<and> vmsz_aligned' (\<acute>paddr) X64SmallPage \<rbrace>
  Call makeUserPTE_'proc
  \<lbrace> pte_lift \<acute>ret__struct_pte_C = \<lparr>
       pte_CL.xd_CL = 0,
       pte_CL.page_base_address_CL = \<^bsup>s\<^esup>paddr,
       pte_CL.global_CL = 0,
       pte_CL.pat_CL = x86PATBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pte_CL.dirty_CL = 0,
       pte_CL.accessed_CL = 0,
       pte_CL.cache_disabled_CL = x86PCDBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pte_CL.write_through_CL = x86PWTBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pte_CL.super_user_CL = superuser_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pte_CL.read_write_CL = writable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pte_CL.present_CL = 1\<rparr> \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp split: if_splits)
  apply (rule conjI[rotated])
   apply (clarsimp simp: superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def mask_def
                  split: if_splits)
  apply (clarsimp simp: superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def vmsz_aligned'_def bit_simps
                 split: if_splits)
  sorry (* FIXME x64: canonical address magic
  apply (intro conjI impI allI | clarsimp )+
    apply (simp only: pte_lift_def)
    apply (simp add: vmsz_aligned'_def superuser_from_vm_rights_mask)
    apply (clarsimp simp: Kernel_C.ARMSection_def Kernel_C.ARMSmallPage_def
       Kernel_C.ARMLargePage_def)
    apply (fastforce simp:mask_def hap_from_vm_rights_mask  memattr_from_cacheable_def
      split:if_splits dest!:mask_eq1_nochoice intro: is_aligned_neg_mask)
   apply (simp only: pde_pde_section_lift pde_pde_section_lift_def)
   apply (simp add: vmsz_aligned'_def gen_framesize_to_H_def hap_from_vm_rights_mask)
   apply (clarsimp simp: Kernel_C.ARMSection_def Kernel_C.ARMSmallPage_def
       Kernel_C.ARMLargePage_def is_aligned_neg_mask_eq)
    apply (fastforce simp:mask_def hap_from_vm_rights_mask  memattr_from_cacheable_def
      split:if_splits dest!:mask_eq1_nochoice intro: is_aligned_neg_mask)
  apply (clarsimp)
  apply (intro conjI impI allI)
   apply (simp add:pde_pde_section_lift pde_pde_section_lift_def)
   apply (simp add: vmsz_aligned'_def gen_framesize_to_H_def hap_from_vm_rights_mask)
   apply (drule is_aligned_weaken[where y = 21])
    apply (clarsimp simp: Kernel_C.ARMSuperSection_def Kernel_C.ARMSmallPage_def
       Kernel_C.ARMLargePage_def is_aligned_neg_mask_eq)+
   apply (fastforce simp:mask_def hap_from_vm_rights_mask  memattr_from_cacheable_def
     split:if_splits dest!:mask_eq1_nochoice intro: is_aligned_neg_mask)
  apply (simp add:pde_pde_section_lift pde_pde_section_lift_def)
  apply (simp add: vmsz_aligned'_def gen_framesize_to_H_def hap_from_vm_rights_mask)
  apply (drule is_aligned_weaken[where y = 21])
   apply (clarsimp simp: Kernel_C.ARMSuperSection_def Kernel_C.ARMSmallPage_def
       Kernel_C.ARMLargePage_def is_aligned_neg_mask_eq)+
   apply (fastforce simp:mask_def hap_from_vm_rights_mask  memattr_from_cacheable_def
     split:if_splits dest!:mask_eq1_nochoice intro: is_aligned_neg_mask)
  done *)

lemma makeUserPDELargePage_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0 \<and> vmsz_aligned' (\<acute>paddr) X64LargePage \<rbrace>
  Call makeUserPDELargePage_'proc
  \<lbrace> pde_lift \<acute>ret__struct_pde_C = Some (Pde_pde_large \<lparr>
       pde_pde_large_CL.xd_CL = 0,
       pde_pde_large_CL.page_base_address_CL = \<^bsup>s\<^esup>paddr,
       pde_pde_large_CL.pat_CL = x86PATBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pde_pde_large_CL.global_CL = 0,
       pde_pde_large_CL.dirty_CL = 0,
       pde_pde_large_CL.accessed_CL = 0,
       pde_pde_large_CL.cache_disabled_CL = x86PCDBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pde_pde_large_CL.write_through_CL = x86PWTBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pde_pde_large_CL.super_user_CL = superuser_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pde_pde_large_CL.read_write_CL = writable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pde_pde_large_CL.present_CL = 1\<rparr>) \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp:vmsz_aligned'_def)
  apply (clarsimp simp: pde_pde_large_lift split: if_splits)
  apply (rule conjI[rotated])
   apply (clarsimp simp: superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def mask_def
                  split: if_splits)
  apply (clarsimp simp: superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def bit_simps word_and_mask_shiftl
                 split: if_splits)
  sorry (*
  apply (intro conjI)
   apply (rule impI)
   apply (drule is_aligned_weaken[where y = 12])
    apply (clarsimp simp:gen_framesize_to_H_def pageBitsForSize_def split:if_splits)
   apply (clarsimp dest:is_aligned_neg_mask_eq)
   apply (intro conjI impI allI)
    apply (fold_subgoals (prefix))[2]
    subgoal premises prems using prems
             by ((clarsimp simp add: pte_lift_def pte_pte_small_lift_def pte_tag_defs
                  mask_def hap_from_vm_rights_mask addrFromPPtr_def
                  memattr_from_cacheable_def
                  iwb_from_cacheable_def dest!:mask_eq1_nochoice)+)
  apply clarsimp
  apply (drule is_aligned_weaken[where y = 16])
  apply (clarsimp simp: gen_framesize_to_H_def pageBitsForSize_def split: if_splits)
  apply (intro conjI impI allI
         ; clarsimp simp: pte_lift_def pte_pte_small_lift_def pte_tag_defs)
   apply (fastforce simp:mask_def hap_from_vm_rights_mask  memattr_from_cacheable_def
     split:if_splits dest!:mask_eq1_nochoice intro: is_aligned_neg_mask)+
  done *)

lemma makeUserPDEPageTable_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  \<lbrace>s. vmsz_aligned' (\<acute>paddr) X64LargePage \<rbrace>
  Call makeUserPDEPageTable_'proc
  \<lbrace> pde_lift \<acute>ret__struct_pde_C = Some (Pde_pde_pt \<lparr>
       pde_pde_pt_CL.xd_CL = 0,
       pde_pde_pt_CL.pt_base_address_CL = \<^bsup>s\<^esup>paddr,
       pde_pde_pt_CL.accessed_CL = 0,
       pde_pde_pt_CL.cache_disabled_CL = x86PCDBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pde_pde_pt_CL.write_through_CL = x86PWTBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pde_pde_pt_CL.super_user_CL = 1,
       pde_pde_pt_CL.read_write_CL = 1,
       pde_pde_pt_CL.present_CL = 1\<rparr>) \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp:vmsz_aligned'_def)
  apply (clarsimp simp: pde_pde_pt_lift split: if_splits)
  apply (rule conjI[rotated])
   apply (clarsimp simp: superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def mask_def
                  split: if_splits)
  apply (clarsimp simp: superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def bit_simps word_and_mask_shiftl
                 split: if_splits)
  sorry

lemma makeUserPDPTEHugePage_spec:
  "\<forall>s. \<Gamma> \<turnstile>
  \<lbrace>s. \<acute>vm_rights < 4 \<and> \<acute>vm_rights \<noteq> 0 \<and> vmsz_aligned' (\<acute>paddr) X64HugePage \<rbrace>
  Call makeUserPDPTEHugePage_'proc
  \<lbrace> pdpte_lift \<acute>ret__struct_pdpte_C = Some (Pdpte_pdpte_1g \<lparr>
       pdpte_pdpte_1g_CL.xd_CL = 0,
       pdpte_pdpte_1g_CL.page_base_address_CL = \<^bsup>s\<^esup>paddr,
       pdpte_pdpte_1g_CL.pat_CL = 0,
       pdpte_pdpte_1g_CL.global_CL = 0,
       pdpte_pdpte_1g_CL.dirty_CL = 0,
       pdpte_pdpte_1g_CL.accessed_CL = 0,
       pdpte_pdpte_1g_CL.cache_disabled_CL = x86PCDBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pdpte_pdpte_1g_CL.write_through_CL = x86PWTBit_CL (vm_attributes_lift \<^bsup>s\<^esup>vm_attr),
       pdpte_pdpte_1g_CL.super_user_CL = superuser_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pdpte_pdpte_1g_CL.read_write_CL = writable_from_vm_rights (vmrights_to_H \<^bsup>s\<^esup>vm_rights),
       pdpte_pdpte_1g_CL.present_CL = 1\<rparr>) \<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp:vmsz_aligned'_def)
  apply (clarsimp simp: pdpte_pdpte_1g_lift split: if_splits)
  apply (rule conjI[rotated])
   apply (clarsimp simp: superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def mask_def
                  split: if_splits)
  apply (clarsimp simp: superuser_from_vm_rights_mask writable_from_vm_rights_mask
                        vm_attributes_lift_def bit_simps word_and_mask_shiftl
                 split: if_splits)
  sorry

lemma vmAttributesFromWord_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. True\<rbrace> Call vmAttributesFromWord_'proc
  \<lbrace> vm_attributes_lift \<acute>ret__struct_vm_attributes_C =
      \<lparr>  x86PATBit_CL =  (\<^bsup>s\<^esup>w >> 2) && 1,
        x86PCDBit_CL = (\<^bsup>s\<^esup>w >> 1) && 1,
        x86PWTBit_CL = \<^bsup>s\<^esup>w && 1 \<rparr>  \<rbrace>"
  by (vcg, simp add: vm_attributes_lift_def word_sless_def word_sle_def mask_def)

lemma cap_to_H_PML4Cap_tag:
  "\<lbrakk> cap_to_H cap = ArchObjectCap (PML4Cap p A);
     cap_lift C_cap = Some cap \<rbrakk> \<Longrightarrow>
    cap_get_tag C_cap = scast cap_pml4_cap"
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     apply (simp_all add: Let_def cap_lift_def split: if_splits)
  done

lemma cap_to_H_PML4Cap:
  "cap_to_H cap = ArchObjectCap (PML4Cap p asid) \<Longrightarrow>
  \<exists>cap_CL. cap = Cap_pml4_cap cap_CL \<and>
           to_bool (capPML4IsMapped_CL cap_CL) = (asid \<noteq> None) \<and>
           (asid \<noteq> None \<longrightarrow> capPML4MappedASID_CL cap_CL = the asid) \<and>
           capPML4BasePtr_CL cap_CL = p"
  by (auto simp add: cap_to_H_def Let_def split: cap_CL.splits if_splits)

lemma cap_lift_PML4Cap_Base:
  "\<lbrakk> cap_to_H cap_cl = ArchObjectCap (PML4Cap p asid);
     cap_lift cap_c = Some cap_cl \<rbrakk>
  \<Longrightarrow> p = capPML4BasePtr_CL (cap_pml4_cap_lift cap_c)"
  apply (simp add: cap_pml4_cap_lift_def)
  apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_splits)
  done

(* FIXME: move *)
lemma word_le_mask_eq:
  "\<lbrakk> x \<le> mask n; n < word_bits \<rbrakk> \<Longrightarrow> x && mask n = (x::machine_word)"
  by (rule le_mask_imp_and_mask)

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
  "ccorres dc xfdc \<top> {s. f s = p \<and> casid_pool_relation pool (asid_pool_C (pool' s))} hs
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

lemma canonical_address_page_map_l4_at':
  "\<lbrakk>page_map_l4_at' p s; pspace_canonical' s\<rbrakk> \<Longrightarrow>
     canonical_address p"
  apply (clarsimp simp: page_map_l4_at'_def)
  apply (drule_tac x=0 in spec, clarsimp simp: bit_simps typ_at_to_obj_at_arches)
  apply (erule (1) obj_at'_is_canonical)
  done

lemma sign_extend_canonical_address:
  "(x = sign_extend 47 x) = canonical_address x"
  by (fastforce simp: sign_extended_iff_sign_extend canonical_address_sign_extended)

lemma performASIDPoolInvocation_ccorres:
  notes option.case_cong_weak [cong]
  shows
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (invs' and cte_wp_at' (isPML4Cap' o cteCap) ctSlot and asid_pool_at' poolPtr
        and K (asid \<le> mask asid_bits))
       (UNIV \<inter> \<lbrace>\<acute>poolPtr = Ptr poolPtr\<rbrace> \<inter> \<lbrace>\<acute>asid = asid\<rbrace> \<inter> \<lbrace>\<acute>vspaceCapSlot = Ptr ctSlot\<rbrace>)
       []
       (liftE (performASIDPoolInvocation (Assign asid poolPtr ctSlot)))
       (Call performASIDPoolInvocation_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (cinit lift: poolPtr_' asid_' vspaceCapSlot_')
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_rhs_assoc2)
      apply (rule_tac ccorres_split_nothrow [where r'=dc and xf'=xfdc])
          apply (simp add: updateCap_def)
          apply (rule_tac A="cte_wp_at' (op = rv o cteCap) ctSlot
                             and K (isPML4Cap' rv \<and> asid \<le> mask asid_bits)"
                      and A'=UNIV in ccorres_guard_imp2)
           apply (rule ccorres_pre_getCTE)
           apply (rule_tac P="cte_wp_at' (op = rv o cteCap) ctSlot
                              and K (isPML4Cap' rv \<and> asid \<le> mask asid_bits)
                              and cte_wp_at' (op = rva) ctSlot"
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
             apply (erule (1) cap_lift_PML4Cap_Base)
            apply simp
           apply (erule_tac t = s' in ssubst)
           apply (simp add: heap_to_user_data_def)
           apply (rule conjI)
            apply (erule (1) setCTE_tcb_case)
           apply (simp add: carch_state_relation_def cmachine_state_relation_def
                            typ_heap_simps h_t_valid_clift_Some_iff
                            cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
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
    apply simp
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

lemma pte_case_isInvalidPTE:
  "(case pte of InvalidPTE \<Rightarrow> P | _ \<Rightarrow> Q)
     = (if isInvalidPTE pte then P else Q)"
  by (cases pte, simp_all add: isInvalidPTE_def)

(* FIXME x64: cap condition is a bit gross, do we put a check in the C or fiddle with args
              e.g. add asid to args so you don't have to get it out of the cap and tehrefore
                   dont have to assume that it is a page table cap *)
lemma performPageTableInvocationMap_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
       (cte_at' ctSlot and K (case cap of capability.ArchObjectCap (arch_capability.PageTableCap x None) \<Rightarrow> False
       | capability.ArchObjectCap (arch_capability.PageTableCap x (Some (asid, vs))) \<Rightarrow> True
       | capability.ArchObjectCap _ \<Rightarrow> False | _ \<Rightarrow> False))
       (UNIV \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace> \<inter> \<lbrace>\<acute>ctSlot = Ptr ctSlot\<rbrace> \<inter> \<lbrace>cpde_relation pde \<acute>pde\<rbrace> \<inter> \<lbrace>\<acute>pdSlot = Ptr pdSlot\<rbrace>
             \<inter> \<lbrace>\<acute>root___ptr_to_struct_pml4e_C = Ptr vspace\<rbrace>)
       []
       (liftE (performPageTableInvocation (PageTableMap cap ctSlot pde pdSlot vspace)))
       (Call performX86PageTableInvocationMap_'proc)"
  apply (simp only: liftE_liftM ccorres_liftM_simp)
  apply (simp add: K_def, rule ccorres_gen_asm,
           clarsimp split: capability.splits arch_capability.splits option.splits)
  apply (cinit lift: cap_' ctSlot_' pde_' pdSlot_' root___ptr_to_struct_pml4e_C_')
   apply (ctac (no_vcg))
     apply (rule ccorres_split_nothrow_novcg)
         apply simp
         apply (erule storePDE_Basic_ccorres)
        apply ceqv
apply csymbr
         apply (rule ccorres_add_return2)
apply csymbr
         apply (rule ccorres_split_nothrow_novcg)
             apply simp
thm valid_pti'_def
             apply (rule ccorres_call)
  sorry (*
                subgoal sorry (* need invalidatePageStructureCacheASID_ccorres *)
               apply (rule refl)
              apply (simp add: xfdc_def)
             apply simp
            apply ceqv
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def)
          apply wp
         apply (simp add: guard_is_UNIV_def)
        apply vcg
       apply (rule conseqPre, vcg)
       apply clarsimp
      apply wp
     apply (simp add: guard_is_UNIV_def)
    apply wp
   apply simp
  apply simp
  done *)

end

end
