(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
  "ccorres (\<lambda>rv rv'. r (f rv) rv') xf G G' hs a c
  \<Longrightarrow> ccorres r xf G G' hs (a >>= (\<lambda>rv. return (f rv))) c"
  by (simp add: liftM_def[symmetric] o_def)

lemma lookupCap_ccorres':
  "ccorres (lookup_failure_rel \<currency> ccap_relation) lookupCap_xf 
   (valid_pspace' and tcb_at' a)
   (UNIV \<inter> {s. cPtr_' s = b} \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr a}) [] 
  (lookupCap a b) (Call lookupCap_'proc)"
  apply (cinit lift: cPtr_' thread_' simp: lookupCapAndSlot_def liftME_def bindE_assoc)

   apply (ctac (no_vcg) add: lookupSlotForThread_ccorres')
     --"case where lu_ret.status is EXCEPTION_NONE" 
     apply (simp  add: split_beta cong:call_ignore_cong)
     apply csymbr  --"call status_C_update"
     apply (simp add: Collect_const[symmetric] lookupSlot_raw_rel_def liftE_def
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (ctac )
       apply (rule ccorres_return_CE [unfolded returnOk_def, simplified], simp+)[1]
      apply wp
     apply vcg
    --"case where lu_ret.status is *not* EXCEPTION_NONE" 
    apply simp
    apply (rule ccorres_split_throws)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr -- "call cap_null_cap_new_'proc"
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply vcg 
   apply (wp | simp)+

  -- "last subgoal"
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
     --"case where lu_ret.status is EXCEPTION_NONE" 
     apply (simp  add: split_beta cong:call_ignore_cong)
     apply csymbr  --"call status_C_update"
     apply csymbr  --"call slot_C_update"
     apply (simp add: Collect_const[symmetric] lookupSlot_raw_rel_def liftE_bindE
                 del: Collect_const)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule_tac P="cte_at' rv" and P'=UNIV in ccorres_from_vcg_throws)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: Bex_def in_monad getSlotCap_def in_getCTE2 cte_wp_at_ctes_of)
     apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
     apply (simp add: ccte_relation_ccap_relation typ_heap_simps')
    --"case where lu_ret.status is *not* EXCEPTION_NONE" 
    apply simp
    apply (rule ccorres_split_throws)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr+
     apply (rule ccorres_return_C_errorE, simp+)[1]

    apply vcg 
   apply (wp | simp)+

  -- "last subgoal"
  apply clarsimp
  apply (rule conjI, fastforce)
  apply clarsimp
  apply (case_tac err, simp+) [1]
done


(* FIXME: move *)
lemma injection_handler_liftM:
  "injection_handler f
    = liftM (\<lambda>v. case v of Inl ex \<Rightarrow> Inl (f ex) | Inr rv \<Rightarrow> Inr rv)"
  apply (intro ext, simp add: injection_handler_def liftM_def
                              handleE'_def)
  apply (rule bind_apply_cong, rule refl)
  apply (simp add: throwError_def split: sum.split)
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

lemma lookupSlotForCNodeOp_ccorres':
  "ccorres 
   (syscall_error_rel \<currency>  (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  valid_pspace' s \<and> s  \<turnstile>' croot \<and> depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. to_bool (isSource_' s) = isSource}  \<inter> 
            {s. ccap_relation croot (root_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) [] 
  (lookupSlotForCNodeOp isSource croot capptr depth)
  (Call lookupSlotForCNodeOp_'proc)"                              
  apply (cinit lift: capptr_' isSource_' root_' depth_')
   apply csymbr -- "slot_C_update"
   apply csymbr -- "cap_get_capType"

   apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws2)
      -- "correspondance of Haskell and C conditions"
      apply (clarsimp simp: Collect_const_mem cap_get_tag_isCap)

     -- "case where root is *not* a CNode => throw InvalidRoot"
     apply simp
     apply (rule_tac P=\<top> and P' =UNIV in ccorres_from_vcg_throws)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def)
     apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
     apply (drule_tac  lookup_fault_lift_invalid_root)
     apply clarsimp
     apply (subst syscall_error_to_H_cases(6), simp+)[1]

    -- " case where root is a CNode"
    apply (simp add: rangeCheck_def)
    apply csymbr
    apply (rule ccorres_Cond_rhs_Seq)
     apply (rule_tac P="depth < 2 ^ word_bits" in ccorres_gen_asm)
     apply (drule unat_of_nat32)
     apply (simp add: if_1_0_0 unlessE_def fromIntegral_def integral_inv)
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
       -- "correspondance of Haskell and C conditions"
       apply (clarsimp simp: Collect_const_mem fromIntegral_def integral_inv
                             if_1_0_0)
       apply (simp add: word_size unat_of_nat32 word_less_nat_alt
                        word_less_1[symmetric] linorder_not_le)
      
      -- "case of RangeError"
      apply (rule_tac P= \<top> and P' =UNIV in ccorres_from_vcg_throws)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: throwError_def  return_def syscall_error_rel_def)
      apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
      apply (subst syscall_error_to_H_cases(4), simp+)[1] 
      apply (simp add: word_size word_sle_def)

     -- "case where there is *no* RangeError"
     apply (rule_tac xf'=lookupSlot_xf in  ccorres_rel_imp)
      apply (rule_tac r="\<lambda>w w'. w'= Ptr w"
          and f="\<lambda> st fl es. fl = scast EXCEPTION_SYSCALL_ERROR \<and> 
                           syscall_error_to_H (errsyscall es) (errlookup_fault es) = Some (FailedLookup isSource st)"
          in lookupErrorOnFailure_ccorres) 
      apply (ctac (no_vcg))  -- "resolveAddressBits"
        -- " case where resolveAddressBits results in EXCEPTION_NONE"
        apply clarsimp
      apply (rule_tac A=\<top> and A'=UNIV in ccorres_guard_imp2)
         apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_if_cond_throws2)
            -- "correspondance of Haskell and C conditions"
            apply (clarsimp simp: Collect_const_mem unat_gt_0)
           -- " case where bits are remaining"
           apply (rule_tac P= \<top> and P' =UNIV in ccorres_from_vcg_throws)
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: throwError_def return_def)
         apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
         apply (subst syscall_error_to_H_cases(6), simp+)[1]
           apply (simp add: lookup_fault_depth_mismatch_lift)
           apply (erule le_32_mask_eq)

          -- " case where *no* bits are remaining"
          apply csymbr -- "slot_C_update"
        apply csymbr -- "status_C_update"
        apply (rule ccorres_return_CE, simp+)[1]
          
       apply vcg

        -- "guard_imp subgoal"
        apply clarsimp

       -- " case where resolveAddressBits does *not* results in EXCEPTION_NONE"
       apply clarsimp
     apply (rule_tac P= \<top> and P' ="\<lbrace>\<exists>v. (lookup_fault_lift (\<acute>current_lookup_fault)) = Some v
                                              \<and> lookup_fault_to_H v = err \<rbrace>"
                       in ccorres_from_vcg_throws)
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def return_def)
     apply (clarsimp simp: EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
     apply (subst syscall_error_to_H_cases(6), simp+)[1]
      apply wp

     -- "rel_imp"
     apply clarsimp
     apply (case_tac x, clarsimp)
      apply (simp add: syscall_error_rel_def errstate_def) 
     apply (clarsimp simp: word_bits_def word_size fromIntegral_def
                           integral_inv)

    apply vcg
   apply vcg

  -- "last subgoal"
  apply (clarsimp simp: if_1_0_0  to_bool_def true_def word_size
                        fromIntegral_def integral_inv)
  apply (case_tac "cap_get_tag root = scast cap_cnode_cap")
   prefer 2 apply clarsimp
  apply (clarsimp simp: unat_of_nat32 word_sle_def)
  apply (simp add: Collect_const_mem lookup_failure_rel_fault_lift)
  done


lemma lookupSlotForCNodeOp_ccorres:
  "ccorres 
   (syscall_error_rel \<currency>  (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  invs' s \<and> s  \<turnstile>' croot \<and> depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. to_bool (isSource_' s) = isSource}  \<inter> 
            {s. ccap_relation croot (root_' s)} \<inter>
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
            {s. ccap_relation croot (root_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) [] 
  (lookupSourceSlot croot capptr depth)
  (Call lookupSourceSlot_'proc)"
  apply (cinit lift: capptr_' root_' depth_')
   apply (rule ccorres_trim_returnE)
     apply simp
    apply simp
   apply (ctac add: lookupSlotForCNodeOp_ccorres') 
  apply (clarsimp simp: to_bool_def true_def false_def)
  done

lemma lookupSourceSlot_ccorres:
  "ccorres 
   (syscall_error_rel \<currency> (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  invs' s \<and> s  \<turnstile>' croot \<and>  depth < 2 ^ word_bits)
   (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. ccap_relation croot (root_' s)} \<inter>
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
            {s. ccap_relation croot (root_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) [] 
  (lookupTargetSlot croot capptr depth)
  (Call lookupTargetSlot_'proc)"  
  apply (cinit lift: capptr_' root_' depth_')
   apply (rule ccorres_trim_returnE)
     apply simp
    apply simp
   apply (ctac add: lookupSlotForCNodeOp_ccorres') 
  apply (clarsimp simp: to_bool_def true_def false_def)
  done

lemma lookupTargetSlot_ccorres:
  "ccorres 
   (syscall_error_rel \<currency>  (\<lambda>w w'. w'= Ptr w \<and> depth \<le> word_bits)) lookupSlot_xf
   (\<lambda>s.  invs' s \<and> s  \<turnstile>' croot \<and>  depth < 2 ^ word_bits)
  (UNIV \<inter> {s. capptr_' s = capptr} \<inter>
            {s. ccap_relation croot (root_' s)} \<inter>
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
            {s. ccap_relation croot (root_' s)} \<inter>
            {s. depth_' s = of_nat depth} ) [] 
  (lookupPivotSlot croot capptr depth)
  (Call lookupPivotSlot_'proc)"
  apply (cinit lift: capptr_' root_' depth_')
   apply (rule ccorres_trim_returnE)
     apply simp
    apply simp
   apply (ctac add: lookupSlotForCNodeOp_ccorres) 
  apply (clarsimp simp: to_bool_def true_def false_def)
  done

end
end
