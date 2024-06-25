(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CSpace_All
imports CSpace_RAB_C CSpace_C
begin

context kernel_m
begin




abbreviation
  "lookupCapAndSlot_xf \<equiv> liftxf errstate lookupCapAndSlot_ret_C.status_C
                             (\<lambda> x . (lookupCapAndSlot_ret_C.cap_C x, lookupCapAndSlot_ret_C.slot_C x))
                             ret__struct_lookupCapAndSlot_ret_C_'"




(* FIXME: move *)
lemma ccorres_return_into_rel:
  "ccorres (r \<circ> f) xf G G' hs a c
  \<Longrightarrow> ccorres r xf G G' hs (a >>= (\<lambda>rv. return (f rv))) c"
  by (simp add: liftM_def[symmetric])

lemma lookupCap_ccorres':
  "ccorres (lookup_failure_rel \<currency> ccap_relation) lookupCap_xf
   (valid_pspace' and tcb_at' a)
   (UNIV \<inter> {s. cPtr_' s = b} \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr a}) []
  (lookupCap a b) (Call lookupCap_'proc)"
  apply (cinit lift: cPtr_' thread_' simp: lookupCapAndSlot_def liftME_def bindE_assoc)

   apply (ctac (no_vcg) add: lookupSlotForThread_ccorres')
     \<comment> \<open>case where lu_ret.status is EXCEPTION_NONE\<close>
     apply (simp  add: split_beta cong:call_ignore_cong)
     apply csymbr  \<comment> \<open>call status_C_update\<close>
     apply (simp add: Collect_const[symmetric] lookupSlot_raw_rel_def liftE_def
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (ctac )
       apply (rule ccorres_return_CE [unfolded returnOk_def, simplified], simp+)[1]
      apply wp
     apply vcg
    \<comment> \<open>case where lu_ret.status is *not* EXCEPTION_NONE\<close>
    apply simp
    apply (rule ccorres_split_throws)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr \<comment> \<open>call cap_null_cap_new_'proc\<close>
     apply csymbr
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply vcg
   apply (wp | simp)+

  \<comment> \<open>last subgoal\<close>
  apply (clarsimp simp: valid_pspace_valid_objs')
  apply (intro impI conjI allI)
    apply (simp add: lookupSlot_raw_rel_def)
    apply (rule_tac y="ret___struct_lookupCap_ret_C_' s" for s
                    in arg_cong, fastforce)
   apply simp
  apply (case_tac err, simp+) [1]
done

lemma lookupCap_ccorres:
  "ccorres (lookup_failure_rel \<currency> ccap_relation) lookupCap_xf
   (\<lambda>s. invs' s \<and> (tcb_at' a s))
   (UNIV \<inter> {s. cPtr_' s = b} \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr a}) []
  (lookupCap a b) (Call lookupCap_'proc)"
  apply (rule ccorres_guard_imp2, rule lookupCap_ccorres')
  apply fastforce
  done


lemma lookupCapAndSlot_ccorres :
  "ccorres
   (lookup_failure_rel \<currency> (\<lambda>(c,s) (c',s'). ccap_relation c c' \<and> s'= Ptr s)) lookupCapAndSlot_xf
   (\<lambda>s. invs' s \<and> tcb_at' thread s)
   (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>cPtr = cPtr\<rbrace> ) []
  (lookupCapAndSlot thread cPtr)
  (Call lookupCapAndSlot_'proc)"
  apply (cinit lift: thread_' cPtr_')

   apply (ctac (no_vcg))
     \<comment> \<open>case where lu_ret.status is EXCEPTION_NONE\<close>
     apply (simp  add: split_beta cong:call_ignore_cong)
     apply csymbr  \<comment> \<open>call status_C_update\<close>
     apply csymbr  \<comment> \<open>call slot_C_update\<close>
     apply (simp add: Collect_const[symmetric] lookupSlot_raw_rel_def liftE_bindE
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule_tac P="cte_at' rv" and P'=UNIV in ccorres_from_vcg_throws)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: Bex_def in_monad getSlotCap_def in_getCTE2 cte_wp_at_ctes_of)
     apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
     apply (simp add: ccte_relation_ccap_relation typ_heap_simps')
    \<comment> \<open>case where lu_ret.status is *not* EXCEPTION_NONE\<close>
    apply simp
    apply (rule ccorres_split_throws)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr+
     apply (rule ccorres_return_C_errorE, simp+)[1]

    apply vcg
   apply (wp | simp)+

  \<comment> \<open>last subgoal\<close>
  apply clarsimp
  apply (rule conjI, fastforce)
  apply clarsimp
  apply (case_tac err, simp+) [1]
done


lemma lookupErrorOnFailure_ccorres:
  "ccorres (f \<currency> r) xf P P' hs a c
    \<Longrightarrow> ccorres ((\<lambda>x y z. \<exists>w. x = FailedLookup isSource w \<and> f w y z) \<currency> r)
             xf P P' hs
             (lookupErrorOnFailure isSource a) c"
  apply (simp add: lookupError_injection injection_handler_liftM)
  apply (erule ccorres_rel_imp)
  apply (auto split: sum.split)
  done


lemma lookup_failure_rel_fault_lift:
  " \<lbrakk> st \<noteq> scast EXCEPTION_NONE;
      lookup_failure_rel err st (errstate t)\<rbrakk>
     \<Longrightarrow> \<exists>v. lookup_fault_lift (current_lookup_fault_' (globals t)) = Some v \<and> lookup_fault_to_H v = err"
  apply (case_tac err, clarsimp+)
  done

lemma le_64_mask_eq:
  "(bits::machine_word) \<le> 64 \<Longrightarrow> bits && mask 7 = bits"
  apply (rule less_mask_eq, simp)
  apply (erule le_less_trans, simp)
  done

lemma lookupSlotForCNodeOp_ccorres':
  "ccorres
   (syscall_error_rel \<currency>  (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  valid_pspace' s \<and> s  \<turnstile>' croot \<and> depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. to_bool (isSource_' s) = isSource}  \<inter>
            {s. ccap_relation croot (root___struct_cap_C_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) []
  (lookupSlotForCNodeOp isSource croot capptr depth)
  (Call lookupSlotForCNodeOp_'proc)"
  apply (cinit lift: capptr_' isSource_' root___struct_cap_C_' depth_')
   apply csymbr \<comment> \<open>slot_C_update\<close>
   apply csymbr \<comment> \<open>cap_get_capType\<close>

   apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws2)
      \<comment> \<open>correspondance of Haskell and C conditions\<close>
      apply (clarsimp simp: Collect_const_mem cap_get_tag_isCap)

     \<comment> \<open>case where root is *not* a CNode => throw InvalidRoot\<close>
     apply simp
     apply (rule_tac P=\<top> and P' =UNIV in ccorres_from_vcg_throws)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def)
     apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
     apply (drule_tac  lookup_fault_lift_invalid_root)
     apply clarsimp
     apply (subst syscall_error_to_H_cases(6), simp+)[1]

    \<comment> \<open>case where root is a CNode\<close>
    apply (simp add: rangeCheck_def)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule_tac P="depth < 2 ^ word_bits" in ccorres_gen_asm)
     apply (drule unat_of_nat64)
     apply (simp add: unlessE_def fromIntegral_def integral_inv)
     apply (rule ccorres_cond_true_seq)
     apply (rule ccorres_split_throws)
      apply (rule_tac P= \<top> and P' =UNIV in ccorres_from_vcg_throws)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def
                            word_sle_def syscall_error_to_H_cases
                            word_size exception_defs)
     apply vcg
    apply csymbr
    apply (rule_tac Q="\<lambda>s. depth < 2 ^ word_bits" and Q'=\<top> in ccorres_split_unless_throwError_cond)
       \<comment> \<open>correspondance of Haskell and C conditions\<close>
       apply (clarsimp simp: Collect_const_mem fromIntegral_def integral_inv)
       apply (simp add: word_size unat_of_nat64 word_less_nat_alt
                        word_less_1[symmetric] linorder_not_le)

      \<comment> \<open>case of RangeError\<close>
      apply (rule_tac P= \<top> and P' =UNIV in ccorres_from_vcg_throws)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def)
      apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
      apply (subst syscall_error_to_H_cases(4), simp+)[1]
      apply (simp add: word_size word_sle_def)

     \<comment> \<open>case where there is *no* RangeError\<close>
     apply (rule_tac xf'=lookupSlot_xf in  ccorres_rel_imp)
      apply (rule_tac r="\<lambda>w w'. w'= Ptr w"
          and f="\<lambda> st fl es. fl = scast EXCEPTION_SYSCALL_ERROR \<and>
                           syscall_error_to_H (errsyscall es) (errlookup_fault es) = Some (FailedLookup isSource st)"
          in lookupErrorOnFailure_ccorres)
      apply (ctac (no_vcg))  \<comment> \<open>resolveAddressBits\<close>
        \<comment> \<open>case where resolveAddressBits results in EXCEPTION_NONE\<close>
        apply clarsimp
      apply (rule_tac A=\<top> and A'=UNIV in ccorres_guard_imp2)
         apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws2)
            \<comment> \<open>correspondance of Haskell and C conditions\<close>
            apply (clarsimp simp: Collect_const_mem unat_gt_0)
           \<comment> \<open>case where bits are remaining\<close>
           apply (rule_tac P= \<top> and P' =UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: throwError_def return_def)
         apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
         apply (subst syscall_error_to_H_cases(6), simp+)[1]
           apply (simp add: lookup_fault_depth_mismatch_lift)
           apply (erule le_64_mask_eq)

          \<comment> \<open>case where *no* bits are remaining\<close>
          apply csymbr \<comment> \<open>slot_C_update\<close>
        apply csymbr \<comment> \<open>status_C_update\<close>
        apply (rule ccorres_return_CE, simp+)[1]

       apply vcg

        \<comment> \<open>guard_imp subgoal\<close>
        apply clarsimp

       \<comment> \<open>case where resolveAddressBits does *not* results in EXCEPTION_NONE\<close>
       apply clarsimp
     apply (rule_tac P= \<top> and P' ="\<lbrace>\<exists>v. (lookup_fault_lift (\<acute>current_lookup_fault)) = Some v
                                              \<and> lookup_fault_to_H v = err \<rbrace>"
                       in ccorres_from_vcg_throws)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def return_def)
     apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
     apply (subst syscall_error_to_H_cases(6), simp+)[1]
      apply wp

     \<comment> \<open>rel_imp\<close>
     apply clarsimp
     apply (case_tac x, clarsimp)
      apply (simp add: syscall_error_rel_def errstate_def)
     apply (clarsimp simp: word_bits_def word_size fromIntegral_def
                           integral_inv)

    apply vcg
   apply vcg

  \<comment> \<open>last subgoal\<close>
  apply (clarsimp simp: word_size fromIntegral_def integral_inv)
  apply (case_tac "cap_get_tag root___struct_cap_C = scast cap_cnode_cap")
   prefer 2 apply clarsimp
  apply (clarsimp simp: unat_of_nat64 word_sle_def)
  apply (simp add: Collect_const_mem lookup_failure_rel_fault_lift)
  done


lemma lookupSlotForCNodeOp_ccorres:
  "ccorres
   (syscall_error_rel \<currency>  (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  invs' s \<and> s  \<turnstile>' croot \<and> depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. to_bool (isSource_' s) = isSource}  \<inter>
            {s. ccap_relation croot (root___struct_cap_C_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) []
  (lookupSlotForCNodeOp isSource croot capptr depth)
  (Call lookupSlotForCNodeOp_'proc)"
  apply (rule ccorres_guard_imp2, rule lookupSlotForCNodeOp_ccorres')
  apply fastforce
  done

lemma lookupSourceSlot_ccorres':
  "ccorres
   (syscall_error_rel \<currency> (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  valid_pspace' s \<and> s  \<turnstile>' croot \<and>  depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. ccap_relation croot (root___struct_cap_C_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) []
  (lookupSourceSlot croot capptr depth)
  (Call lookupSourceSlot_'proc)"
  apply (cinit lift: capptr_' root___struct_cap_C_' depth_')
   apply (rule ccorres_trim_returnE)
     apply simp
    apply simp
   apply (ctac add: lookupSlotForCNodeOp_ccorres')
  apply clarsimp
  done

lemma lookupSourceSlot_ccorres:
  "ccorres
   (syscall_error_rel \<currency> (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  invs' s \<and> s  \<turnstile>' croot \<and>  depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. ccap_relation croot (root___struct_cap_C_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) []
  (lookupSourceSlot croot capptr depth)
  (Call lookupSourceSlot_'proc)"
  apply (rule ccorres_guard_imp2, rule lookupSourceSlot_ccorres')
  apply fastforce
  done

lemma lookupTargetSlot_ccorres':
  "ccorres
   (syscall_error_rel \<currency>  (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  valid_pspace' s \<and> s  \<turnstile>' croot \<and>  depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. ccap_relation croot (root___struct_cap_C_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) []
  (lookupTargetSlot croot capptr depth)
  (Call lookupTargetSlot_'proc)"
  apply (cinit lift: capptr_' root___struct_cap_C_' depth_')
   apply (rule ccorres_trim_returnE)
     apply simp
    apply simp
   apply (ctac add: lookupSlotForCNodeOp_ccorres')
  apply clarsimp
  done

lemma lookupTargetSlot_ccorres:
  "ccorres
   (syscall_error_rel \<currency>  (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  invs' s \<and> s  \<turnstile>' croot \<and>  depth < 2 ^ word_bits)
  (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. ccap_relation croot (root___struct_cap_C_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) []
  (lookupTargetSlot croot capptr depth)
  (Call lookupTargetSlot_'proc)"
  apply (rule ccorres_guard_imp2, rule lookupTargetSlot_ccorres')
  apply fastforce
  done

lemma lookupPivotSlot_ccorres:
  "ccorres
   (syscall_error_rel \<currency>  (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  invs' s \<and> s  \<turnstile>' croot \<and>  depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. ccap_relation croot (root___struct_cap_C_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) []
  (lookupPivotSlot croot capptr depth)
  (Call lookupPivotSlot_'proc)"
  apply (cinit lift: capptr_' root___struct_cap_C_' depth_')
   apply (rule ccorres_trim_returnE)
     apply simp
    apply simp
   apply (ctac add: lookupSlotForCNodeOp_ccorres)
  apply clarsimp
  done

end
end
