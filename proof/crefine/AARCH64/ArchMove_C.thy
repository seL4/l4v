(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch specific lemmas that should be moved into theory files before CRefine *)

theory ArchMove_C
imports Move_C
begin


lemma ps_clear_is_aligned_ksPSpace_None:
  "\<lbrakk>ps_clear p n s; is_aligned p n; 0<d; d \<le> mask n\<rbrakk>
   \<Longrightarrow> ksPSpace s (p + d) = None"
  apply (simp add: ps_clear_def add_diff_eq[symmetric] mask_2pm1[symmetric])
  apply (drule equals0D[where a="p + d"])
  apply (simp add: dom_def word_gt_0)
  apply (drule mp)
   apply (rule word_plus_mono_right)
    apply simp
   apply (simp add: mask_2pm1)
   apply (erule is_aligned_no_overflow')
  apply (drule mp)
   apply (case_tac "(0::machine_word)<2^n")
    apply (frule le_m1_iff_lt[of "(2::machine_word)^n" d, THEN iffD1])
    apply (simp add: mask_2pm1[symmetric])
    apply (erule (1) is_aligned_no_wrap')
   apply (simp add: is_aligned_mask mask_2pm1 not_less word_bits_def
                    power_overflow)
  by assumption

lemma ps_clear_is_aligned_ctes_None:
  assumes "ps_clear p tcbBlockSizeBits s"
      and "is_aligned p tcbBlockSizeBits"
  shows "ksPSpace s (p + 2*2^cteSizeBits) = None"
    and "ksPSpace s (p + 3*2^cteSizeBits) = None"
    and "ksPSpace s (p + 4*2^cteSizeBits) = None"
  by (auto intro: assms ps_clear_is_aligned_ksPSpace_None
            simp: objBits_defs mask_def)+

lemma word_shift_by_3:
  "x * 8 = (x::'a::len word) << 3"
  by (simp add: shiftl_t2n)

lemma unat_mask_3_less_8:
  "unat (p && mask 3 :: word64) < 8"
  apply (rule unat_less_helper)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply (simp add: mask_def)
  done

lemma ucast_le_ucast_6_64:
  "(ucast x \<le> (ucast y :: word64)) = (x \<le> (y :: 6 word))"
  by (simp add: ucast_le_ucast)

definition
  user_word_at :: "machine_word \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "user_word_at x p \<equiv> \<lambda>s. is_aligned p 3
       \<and> pointerInUserData p s
       \<and> x = word_rcat (map (underlying_memory (ksMachineState s))
                                [p + 7, p + 6, p + 5, p + 4, p + 3, p + 2, p + 1, p])"
definition
  device_word_at :: "machine_word \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "device_word_at x p \<equiv> \<lambda>s. is_aligned p 3
       \<and> pointerInDeviceData p s
       \<and> x = word_rcat (map (underlying_memory (ksMachineState s))
                                [p + 7, p + 6, p + 5, p + 4, p + 3, p + 2, p + 1, p])"

(* FIXME: move to GenericLib *)
lemmas unat64_eq_of_nat = unat_eq_of_nat[where 'a=64, folded word_bits_def]

context begin interpretation Arch .

crunch inv'[wp]: archThreadGet P

(* FIXME MOVE near thm tg_sp' *)
lemma atg_sp':
  "\<lbrace>P\<rbrace> archThreadGet f p \<lbrace>\<lambda>t. obj_at' (\<lambda>t'. f (tcbArch t') = t) p and P\<rbrace>"
  including no_pre
  apply (simp add: archThreadGet_def)
  apply wp
  apply (rule hoare_strengthen_post)
   apply (rule getObject_tcb_sp)
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply simp
  done

(* FIXME: MOVE to EmptyFail *)
lemma empty_fail_archThreadGet [intro!, wp, simp]:
  "empty_fail (archThreadGet f p)"
  by (fastforce simp: archThreadGet_def getObject_def split_def)

lemma valid_untyped':
  notes usableUntypedRange.simps[simp del]
  assumes pspace_distinct': "pspace_distinct' s" and
           pspace_aligned': "pspace_aligned' s" and
                        al: "is_aligned ptr bits"
  shows "valid_untyped' d ptr bits idx s =
         (\<forall>p ko. ksPSpace s p = Some ko \<longrightarrow>
                 obj_range' p ko \<inter> {ptr..ptr + 2 ^ bits - 1} \<noteq> {} \<longrightarrow>
                 obj_range' p ko \<subseteq> {ptr..ptr + 2 ^ bits - 1} \<and>
                 obj_range' p ko \<inter>
                   usableUntypedRange (UntypedCap d ptr bits idx) = {})"
  apply (simp add: valid_untyped'_def)
  apply (simp add: ko_wp_at'_def)
  apply (rule arg_cong[where f=All])
  apply (rule ext)
  apply (rule arg_cong[where f=All])
  apply (rule ext)
  apply (case_tac "ksPSpace s ptr' = Some ko", simp_all)
  apply (frule pspace_alignedD'[OF _ pspace_aligned'])
  apply (frule pspace_distinctD'[OF _ pspace_distinct'])
  apply (simp add: ptr_range_mask_range)
  apply (frule aligned_ranges_subset_or_disjoint[OF al])
  apply (simp only: ptr_range_mask_range)
  apply (fold obj_range'_def)
  apply (rule iffI)
   apply auto[1]
  apply (rule conjI)
   apply (rule ccontr, simp)
   apply (simp add: Set.psubset_eq)
   apply (erule conjE)
   apply (case_tac "obj_range' ptr' ko \<inter> mask_range ptr bits \<noteq> {}", simp)
   apply (cut_tac is_aligned_no_overflow[OF al])
   apply (clarsimp simp add: obj_range'_def mask_def add_diff_eq)
  apply (clarsimp simp add: usableUntypedRange.simps Int_commute)
  apply (case_tac "obj_range' ptr' ko \<inter> mask_range ptr bits \<noteq> {}", simp+)
  apply (cut_tac is_aligned_no_overflow[OF al])
  apply (clarsimp simp add: obj_range'_def mask_def add_diff_eq)
  apply (frule is_aligned_no_overflow)
  by (metis al intvl_range_conv' le_m1_iff_lt less_is_non_zero_p1
               nat_le_linear power_overflow sub_wrap add_0
               add_0_right word_add_increasing word_less_1 word_less_sub_1)

lemma more_pageBits_inner_beauty:
  fixes x :: "9 word"
  fixes p :: machine_word
  assumes x: "x \<noteq> ucast (p && mask pageBits >> 3)"
  shows "(p && ~~ mask pageBits) + (ucast x * 8) \<noteq> p"
  apply clarsimp
  apply (simp add: word_shift_by_3)
  apply (subst (asm) word_plus_and_or_coroll)
   apply (word_eqI_solve dest: test_bit_size simp: pageBits_def)
  apply (insert x)
  apply (erule notE)
  apply word_eqI
  apply (erule_tac x="3+n" in allE)
  apply (clarsimp simp: word_size pageBits_def)
  done

(* FIXME x64: figure out where these are needed and adjust appropriately *)
lemma mask_pageBits_inner_beauty:
  "is_aligned p 3 \<Longrightarrow>
  (p && ~~ mask pageBits) + (ucast ((ucast (p && mask pageBits >> 3)):: 9 word) * 8) = (p::machine_word)"
  apply (simp add: is_aligned_nth word_shift_by_3)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size word_ops_nth_size nth_ucast nth_shiftr nth_shiftl)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size word_ops_nth_size nth_ucast nth_shiftr nth_shiftl
                        pageBits_def)
  apply (rule iffI)
   apply (erule disjE)
    apply clarsimp
   apply clarsimp
  apply simp
  apply clarsimp
  apply (rule context_conjI)
   apply (rule leI)
   apply clarsimp
  apply simp
  apply arith
  done

lemmas mask_64_id[simp] = mask_len_id[where 'a=64, folded word_bits_def]
                          mask_len_id[where 'a=64, simplified]

lemma prio_ucast_shiftr_wordRadix_helper: (* FIXME generalise *)
  "(ucast (p::priority) >> wordRadix :: machine_word) < 4"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_ucast_shiftr_wordRadix_helper': (* FIXME generalise *)
  "(ucast (p::priority) >> wordRadix :: machine_word) \<le> 3"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_unat_shiftr_wordRadix_helper': (* FIXME generalise *)
  "unat ((p::priority) >> wordRadix) \<le> 3"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_ucast_shiftr_wordRadix_helper2: (* FIXME possibly unused *)
  "(ucast (p::priority) >> wordRadix :: machine_word) < 0x20"
  by (rule order_less_trans[OF prio_ucast_shiftr_wordRadix_helper]; simp)

lemma prio_ucast_shiftr_wordRadix_helper3:
  "(ucast (p::priority) >> wordRadix :: machine_word) < 0x40"
  by (rule order_less_trans[OF prio_ucast_shiftr_wordRadix_helper]; simp)

lemma unat_ucast_prio_L1_cmask_simp:
  "unat (ucast (p::priority) && 0x3F :: machine_word) = unat (p && 0x3F)"
  using unat_ucast_prio_mask_simp[where m=6]
  by (simp add: mask_def)

lemmas setEndpoint_obj_at_tcb' = setEndpoint_obj_at'_tcb

(* FIXME: Move to Schedule_R.thy. Make Arch_switchToThread_obj_at a specialisation of this *)
lemma Arch_switchToThread_obj_at_pre:
  "\<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>
   Arch.switchToThread t
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: AARCH64_H.switchToThread_def)
  apply (wp asUser_obj_at_notQ doMachineOp_obj_at hoare_drop_imps|wpc)+
  done

lemma loadWordUser_submonad_fn:
  "loadWordUser p = submonad_fn ksMachineState (ksMachineState_update \<circ> K)
                                (pointerInUserData p) (loadWord p)"
  by (simp add: loadWordUser_def submonad_doMachineOp.fn_is_sm submonad_fn_def)

lemma storeWordUser_submonad_fn:
  "storeWordUser p v = submonad_fn ksMachineState (ksMachineState_update \<circ> K)
                                   (pointerInUserData p) (storeWord p v)"
  by (simp add: storeWordUser_def submonad_doMachineOp.fn_is_sm submonad_fn_def)

lemma threadGet_tcbFault_loadWordUser_comm:
  "do x \<leftarrow> threadGet tcbFault t; y \<leftarrow> loadWordUser p; n x y od =
   do y \<leftarrow> loadWordUser p; x \<leftarrow> threadGet tcbFault t; n x y od"
  apply (rule submonad_comm [OF tcbFault_submonad_args _
                                threadGet_tcbFault_submonad_fn
                                loadWordUser_submonad_fn])
       apply (simp add: submonad_args_def pointerInUserData_def)
      apply (simp add: thread_replace_def Let_def)
     apply simp
    apply (clarsimp simp: thread_replace_def Let_def typ_at'_def ko_wp_at'_def
                          ps_clear_upd ps_clear_upd_None pointerInUserData_def
                   split: option.split kernel_object.split)
   apply (simp add: get_def empty_fail_def)
  apply simp
  done

lemma threadGet_tcbFault_storeWordUser_comm:
  "do x \<leftarrow> threadGet tcbFault t; y \<leftarrow> storeWordUser p v; n x y od =
   do y \<leftarrow> storeWordUser p v; x \<leftarrow> threadGet tcbFault t; n x y od"
  apply (rule submonad_comm [OF tcbFault_submonad_args _
                                threadGet_tcbFault_submonad_fn
                                storeWordUser_submonad_fn])
       apply (simp add: submonad_args_def pointerInUserData_def)
      apply (simp add: thread_replace_def Let_def)
     apply simp
    apply (clarsimp simp: thread_replace_def Let_def typ_at'_def ko_wp_at'_def
                          ps_clear_upd ps_clear_upd_None pointerInUserData_def
                   split: option.split kernel_object.split)
   apply (simp add: get_def empty_fail_def)
  apply simp
  done

lemma asUser_getRegister_discarded:
  "(asUser t (getRegister r)) >>= (\<lambda>_. n) =
   stateAssert (tcb_at' t) [] >>= (\<lambda>_. n)"
  apply (rule ext)
  apply (clarsimp simp: submonad_asUser.fn_is_sm submonad_fn_def
                        submonad_asUser.args assert_def select_f_def
                        gets_def get_def modify_def put_def
                        getRegister_def bind_def split_def
                        return_def fail_def stateAssert_def)
  done

lemma [wp]: (* FIXME AARCH64 *)
  "\<lbrace>valid_queues'\<rbrace> updateASIDPoolEntry param_a param_b \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  sorry
lemma [wp]: (* FIXME AARCH64 *)
  "\<lbrace>valid_pspace'\<rbrace> vcpuUpdate param_a param_b \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  sorry

crunches Arch.switchToThread
  for valid_queues'[wp]: valid_queues'
  (simp: crunch_simps wp: hoare_drop_imps crunch_wps)
crunches switchToIdleThread
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

lemma [wp]: (* FIXME AARCH64 *)
  "\<lbrace>valid_pspace'\<rbrace> updateASIDPoolEntry param_a param_b \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  sorry

crunches switchToIdleThread, switchToThread
  for valid_pspace'[wp]: valid_pspace'
  (simp: whenE_def crunch_simps wp: crunch_wps hoare_drop_imps)

lemma getMessageInfo_less_4:
  "\<lbrace>\<top>\<rbrace> getMessageInfo t \<lbrace>\<lambda>rv s. msgExtraCaps rv < 4\<rbrace>"
  including no_pre
  apply (simp add: getMessageInfo_def)
  apply wp
  apply (rule hoare_strengthen_post, rule hoare_vcg_prop)
  apply (simp add: messageInfoFromWord_def Let_def
                   Types_H.msgExtraCapBits_def)
  apply (rule word_leq_minus_one_le, simp)
  apply simp
  apply (rule word_and_le1)
  done

lemma getMessageInfo_msgLength':
  "\<lbrace>\<top>\<rbrace> getMessageInfo t \<lbrace>\<lambda>rv s. msgLength rv \<le> 0x78\<rbrace>"
  including no_pre
  apply (simp add: getMessageInfo_def)
  apply wp
  apply (rule hoare_strengthen_post, rule hoare_vcg_prop)
  apply (simp add: messageInfoFromWord_def Let_def msgMaxLength_def not_less
                   Types_H.msgExtraCapBits_def split: if_split )
  done

definition
  "isPTCap' cap \<equiv> \<exists>p pt_t asid. cap = (ArchObjectCap (PageTableCap p pt_t asid))"

lemma asid_shiftr_low_bits_less[simplified]:
  "(asid :: machine_word) \<le> mask asid_bits \<Longrightarrow> asid >> asid_low_bits < 2^LENGTH(asid_high_len)"
  apply (rule_tac y="2 ^ 7" in order_less_le_trans)
   apply (rule shiftr_less_t2n)
   apply (simp add: le_mask_iff_lt_2n[THEN iffD1] asid_bits_def asid_low_bits_def)
  apply simp
  done

lemma getActiveIRQ_neq_Some0xFF':
  "\<lbrace>\<top>\<rbrace> getActiveIRQ in_kernel \<lbrace>\<lambda>rv s. rv \<noteq> Some 0xFF\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wpsimp
  done

lemma getActiveIRQ_neq_Some0x3FF:
  "\<lbrace>\<top>\<rbrace> doMachineOp (getActiveIRQ in_kernel) \<lbrace>\<lambda>rv s. rv \<noteq> Some 0xFF\<rbrace>"
  apply (wpsimp simp: doMachineOp_def split_def)
  apply (auto dest: use_valid intro: getActiveIRQ_neq_Some0xFF')
  done

(* We don't have access to n_msgRegisters from C here, but the number of msg registers in C should
   be equivalent to what we have in the abstract/design specs. We want a number for this definition
   that automatically updates if the number of registers changes, and we sanity check it later
   in msgRegisters_size_sanity *)
definition size_msgRegisters :: nat where
  size_msgRegisters_pre_def: "size_msgRegisters \<equiv> size (AARCH64.msgRegisters)"

schematic_goal size_msgRegisters_def:
  "size_msgRegisters = numeral ?x"
  unfolding size_msgRegisters_pre_def AARCH64.msgRegisters_def
  by (simp add: upto_enum_red fromEnum_def enum_register del: Suc_eq_numeral)
     (simp only: Suc_eq_plus1_left, simp del: One_nat_def)

lemma length_msgRegisters[simplified size_msgRegisters_def]:
  "length AARCH64_H.msgRegisters = size_msgRegisters"
  by (simp add: size_msgRegisters_pre_def AARCH64_H.msgRegisters_def)

lemma empty_fail_loadWordUser[intro!, simp]:
  "empty_fail (loadWordUser x)"
  by (fastforce simp: loadWordUser_def ef_dmo')

lemma empty_fail_getMRs[iff]:
  "empty_fail (getMRs t buf mi)"
  by (auto simp add: getMRs_def split: option.split)

lemma empty_fail_getReceiveSlots:
  "empty_fail (getReceiveSlots r rbuf)"
proof -
  note
    empty_fail_resolveAddressBits[wp]
    empty_fail_rethrowFailure[wp]
    empty_fail_rethrowFailure[wp]
  show ?thesis
  unfolding getReceiveSlots_def loadCapTransfer_def lookupCap_def lookupCapAndSlot_def
  by (wpsimp simp: emptyOnFailure_def unifyFailure_def lookupSlotForThread_def
                   capTransferFromWords_def getThreadCSpaceRoot_def locateSlot_conv bindE_assoc
                   lookupSlotForCNodeOp_def lookupErrorOnFailure_def rangeCheck_def)
qed

lemma user_getreg_rv:
  "\<lbrace>obj_at' (\<lambda>tcb. P ((user_regs o atcbContextGet o tcbArch) tcb r)) t\<rbrace>
   asUser t (getRegister r)
   \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply (clarsimp simp: obj_at'_def getRegister_def in_monad atcbContextGet_def)
  done

crunches insertNewCap, Arch_createNewCaps, threadSet, Arch.createObject, setThreadState,
         updateFreeIndex, preemptionPoint
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  (wp: crunch_wps setObject_ksPSpace_only
   simp: unless_def updateObject_default_def crunch_simps
   ignore_del: preemptionPoint)

end

end
