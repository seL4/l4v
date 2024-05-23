(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch specific lemmas that should be moved into theory files before CRefine *)

theory ArchMove_C
imports Move_C
begin

lemma aligned_no_overflow_less: (* FIXME AARCH64: move to Word_Lib *)
  "\<lbrakk> is_aligned p n; p + 2 ^ n \<noteq> 0 \<rbrakk> \<Longrightarrow> p < p + 2 ^ n"
  by (erule word_leq_minus_one_le) (erule is_aligned_no_overflow)

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

(* FIXME AARCH64: this is very specific and rather ugly, is it possible to generalise? *)
lemma size_64_less_64:
  "size (r::64) < (64::nat)"
  apply (induct r rule: bit0.plus_induct, simp)
  apply (frule bit0.Suc_size)
  apply (case_tac "x = 64 - 1"; clarsimp)
  apply (prop_tac "size x \<noteq> size (64 - 1 :: 64)")
   apply (subst bit0.size_inj, simp)
  apply simp
  done

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

(* used in StoreWord_C *)
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

crunches Arch.switchToThread
  for valid_queues'[wp]: valid_queues'
  (simp: crunch_simps wp: hoare_drop_imps crunch_wps getASID_wp)
crunches switchToIdleThread
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

crunches vcpuUpdate
  for pspace_canonical'[wp]: pspace_canonical'

lemma vcpuUpdate_valid_pspace'[wp]:
  "(\<And>vcpu. vcpuTCBPtr (f vcpu) = vcpuTCBPtr vcpu) \<Longrightarrow>
   vcpuUpdate vr f \<lbrace>valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def valid_mdb'_def
  by wpsimp

lemma updateASIDPoolEntry_valid_pspace'[wp]:
  "updateASIDPoolEntry p f \<lbrace>valid_pspace'\<rbrace>"
  unfolding updateASIDPoolEntry_def valid_pspace'_def getPoolPtr_def
  by (wpsimp wp: getASID_wp)

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

(* FIXME AARCH64 vcpu-related items adapted from ARM_HYP's ArchMove_C, possibly not all are useful *)

lemma vcpu_at_ko:
  "vcpu_at' p s \<Longrightarrow> \<exists>vcpu. ko_at' (vcpu::vcpu) p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  done

lemma vcpu_at_ko'_eq:
  "(\<exists>vcpu :: vcpu. ko_at' vcpu p s) = vcpu_at' p s"
  apply (rule iffI)
   apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  apply (case_tac ko, auto)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  done

lemmas vcpu_at_ko' = vcpu_at_ko'_eq[THEN iffD2]

lemma sym_refs_tcb_vcpu':
  "\<lbrakk> ko_at' (tcb::tcb) t s; atcbVCPUPtr (tcbArch tcb) = Some v; sym_refs (state_hyp_refs_of' s) \<rbrakk> \<Longrightarrow>
  \<exists>vcpu. ko_at' vcpu v s \<and> vcpuTCBPtr vcpu = Some t"
  apply (drule (1) hyp_sym_refs_obj_atD')
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (case_tac ko; simp add: tcb_vcpu_refs'_def)
  apply (rename_tac koa)
  apply (case_tac koa; clarsimp simp: refs_of_ao_def vcpu_tcb_refs'_def)
  done


lemma ko_at'_tcb_vcpu_not_NULL:
  "\<lbrakk> ko_at' (tcb::tcb) t s ; valid_objs' s ; no_0_obj' s ; atcbVCPUPtr (tcbArch tcb) = Some p \<rbrakk>
   \<Longrightarrow> 0 < p"
  \<comment> \<open>when C pointer is NULL, need this to show atcbVCPUPtr is None\<close>
  unfolding valid_pspace'_def
  by (fastforce simp: valid_tcb'_def valid_arch_tcb'_def word_gt_0 typ_at'_no_0_objD
                dest: valid_objs_valid_tcb')

lemma ko_at_vcpu_at'D:
  "ko_at' (vcpu :: vcpu) vcpuptr s \<Longrightarrow> vcpu_at' vcpuptr s"
  by (fastforce simp: typ_at_to_obj_at_arches elim: obj_at'_weakenE)

(* FIXME: change the original to be predicated! *)
crunch pred_tcb_at'2[wp]: doMachineOp "\<lambda>s. P (pred_tcb_at' a b p s)"
  (simp: crunch_simps)

crunch valid_queues'[wp]: readVCPUReg "\<lambda>s. valid_queues s"

crunch valid_objs'[wp]: readVCPUReg "\<lambda>s. valid_objs' s"

crunch sch_act_wf'[wp]: readVCPUReg "\<lambda>s. P (sch_act_wf (ksSchedulerAction s) s)"

crunch ko_at'[wp]: readVCPUReg "\<lambda>s. P (ko_at' a p s)"

crunch obj_at'[wp]: readVCPUReg "\<lambda>s. P (obj_at' a p s)"

crunch ksCurThread[wp]: readVCPUReg "\<lambda>s. P (ksCurThread s)"

(* schematic_goal leads to Suc (Suc ..) form only *)
lemma fromEnum_maxBound_vcpureg_def:
  "fromEnum (maxBound :: vcpureg) = 23"
  by (clarsimp simp: fromEnum_def maxBound_def enum_vcpureg)

lemma unat_of_nat_mword_fromEnum_vcpureg[simp]:
  "unat ((of_nat (fromEnum e)) :: machine_word) = fromEnum (e :: vcpureg)"
  apply (subst unat_of_nat_eq, clarsimp)
   apply (rule order_le_less_trans[OF maxBound_is_bound])
   apply (clarsimp simp: fromEnum_maxBound_vcpureg_def)+
  done

lemma unat_of_nat_mword_length_upto_vcpureg[simp]:
  "unat ((of_nat (length [(start :: vcpureg) .e. end])) :: machine_word) = length [start .e. end]"
  apply (subst unat_of_nat_eq ; clarsimp)
  apply (rule order_le_less_trans[OF length_upto_enum_le_maxBound])
  apply (simp add: fromEnum_maxBound_vcpureg_def)
  done

lemma fromEnum_maxBound_vppievent_irq_def:
  "fromEnum (maxBound :: vppievent_irq) = 0"
  by (clarsimp simp: fromEnum_def maxBound_def enum_vppievent_irq)

(* when creating a new object, the entire slot including starting address should be free *)
(* FIXME move *)
lemma ps_clear_entire_slotI:
  "({p..p + 2 ^ n - 1}) \<inter> dom (ksPSpace s) = {} \<Longrightarrow> ps_clear p n s"
  by (fastforce simp: ps_clear_def mask_def field_simps)

lemma ps_clear_ksPSpace_upd_same[simp]:
  "ps_clear p n (s\<lparr>ksPSpace := (ksPSpace s)(p \<mapsto> v)\<rparr>) = ps_clear p n s"
  by (fastforce simp: ps_clear_def)

lemma getObject_vcpu_prop:
  "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(vcpu :: vcpu) s. P vcpu\<rbrace>"
  apply (rule obj_at_getObject)
  apply (clarsimp simp: loadObject_default_def in_monad)
  done

(* FIXME would be interesting to generalise these kinds of lemmas to other KOs *)
lemma setObject_sets_object_vcpu:
  "\<lbrace> vcpu_at' v \<rbrace> setObject v (vcpu::vcpu) \<lbrace> \<lambda>_. ko_at' vcpu v \<rbrace>"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: setObject_def updateObject_default_def bind_assoc)
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift simp: alignError_def)
  apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: obj_at'_def objBitsKO_def archObjSize_def dest!: vcpu_at_ko')
  apply (fastforce simp: fun_upd_apply)
  done

(* FIXME would be interesting to generalise these kinds of lemmas to other KOs *)
lemma placeNewObject_creates_object_vcpu:
  "\<lbrace> \<top> \<rbrace> placeNewObject v (vcpu::vcpu) 0 \<lbrace> \<lambda>_. ko_at' vcpu v \<rbrace>"
  supply fun_upd_apply[simp del] haskell_assert_inv[wp del]
  apply (clarsimp simp: placeNewObject_def placeNewObject'_def split_def alignError_def)
  apply (wpsimp wp: assert_wp hoare_vcg_imp_lift' hoare_vcg_ex_lift)
  apply (clarsimp simp: is_aligned_mask[symmetric] objBitsKO_def archObjSize_def)
  apply (case_tac "is_aligned v vcpuBits"; clarsimp)
  apply (rule conjI; clarsimp)
   apply (subst (asm) lookupAround2_None1)
   apply (clarsimp simp: obj_at'_def objBitsKO_def archObjSize_def fun_upd_apply)
   apply (fastforce intro: ps_clear_entire_slotI simp add: field_simps fun_upd_apply)
  apply (subst (asm) lookupAround2_char1)
  apply (clarsimp simp: obj_at'_def objBitsKO_def archObjSize_def fun_upd_apply)
  apply (fastforce intro: ps_clear_entire_slotI simp add: field_simps)
  done

(* FIXME would be interesting to generalise these kinds of lemmas to other KOs *)
lemma placeNewObject_object_at_vcpu:
  "\<lbrace> \<top> \<rbrace> placeNewObject v (vcpu::vcpu) 0 \<lbrace> \<lambda>_. vcpu_at' v \<rbrace>"
  by (rule hoare_post_imp[OF _ placeNewObject_creates_object_vcpu])
     (fastforce simp: ko_at_vcpu_at'D)

lemma case_option_both[simp]: (* FIXME AARCH64: move to Lib, remove duplicates *)
  "(case f of None \<Rightarrow> P | _ \<Rightarrow> P) = P"
  by (auto split: option.splits)

lemma if_case_opt_same_branches: (* FIXME AARCH64: move to Lib, remove duplicates *)
  "cond \<longrightarrow> Option.is_none opt \<Longrightarrow>
   (if cond then case opt of None \<Rightarrow> f | Some x \<Rightarrow> g x else f) = f"
  by (cases cond; cases opt; clarsimp)

(* FIXME AARCH64: move these up to Refine or AInvs *)
lemma haskell_assertE_wp[wp]:
  "\<lbrace>\<lambda>s. F \<longrightarrow> Q () s\<rbrace> haskell_assertE F L \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding haskell_assertE_def
  by (rule assertE_wp)

(* FIXME AARCH64: this needs to exist before VSpace_R.haskell_assertE_inv, so that the crunch there
                  does not make it [wp] *)
lemma haskell_assertE_inv:
  "haskell_assertE F L \<lbrace>P\<rbrace>"
  unfolding haskell_assertE_def
  by wpsimp

lemma cte_wp_cteCap_valid:
  "\<lbrakk> cte_wp_at' ((=) cap \<circ> cteCap) slot s; valid_objs' s \<rbrakk> \<Longrightarrow> valid_cap' cap s"
  by (clarsimp simp: cte_wp_at_ctes_of ctes_of_valid')

lemma not_VSRootPT_T_eq:
  "(pt_t \<noteq> VSRootPT_T) = (pt_t = NormalPT_T)"
  by (cases pt_t; simp)

lemma unat_of_nat_pt_bits_mw:
  "unat (of_nat (pt_bits pt_t)::machine_word) = pt_bits pt_t"
  by (rule unat_of_nat_eq) (simp add: bit_simps split: if_split)

lemma unat_mask_pt_bits_shift_neq_0[simp]:
  "0 < unat (mask (pt_bits pt_t) >> pte_bits :: machine_word)"
  by (simp add: bit_simps mask_def split: if_split)

lemma pptrBaseOffset_alignment_pt_bits[simp, intro!]:
  "pt_bits pt_t \<le> pptrBaseOffset_alignment"
  by (simp add: bit_simps pptrBaseOffset_alignment_def split: if_split)

lemma canonical_address_mask_shift:
  "\<lbrakk> canonical_address p; is_aligned p m'; m \<le> m'; n + m = Suc canonical_bit; 0 < n \<rbrakk> \<Longrightarrow>
   p && (mask n << m) = p"
  apply (prop_tac "m = Suc canonical_bit - n", arith)
  apply (simp add: canonical_address_def canonical_address_of_def canonical_bit_def)
  apply word_eqI
  apply (rule iffI; clarsimp)
  apply (rename_tac n')
  apply (prop_tac "n' < 48", fastforce)
  apply fastforce
  done

schematic_goal pptrUserTop_val:
  "pptrUserTop = numeral ?n"
  by (simp add: pptrUserTop_def mask_def Kernel_Config.config_ARM_PA_SIZE_BITS_40_def
           del: word_eq_numeral_iff_iszero)

lemma user_region_canonical:
  "p \<in> user_region \<Longrightarrow> canonical_address p"
  apply (simp add: canonical_address_range user_region_def canonical_user_def)
  apply (erule order_trans)
  apply (rule mask_mono)
  apply (simp add: ipa_size_def canonical_bit_def split: if_split)
  done

lemma pptrUserTop_eq_mask_ipa_size:
  "pptrUserTop = mask ipa_size"
  by (simp add: pptrUserTop_def ipa_size_def)

lemma mask_pptrUserTop_user_region:
  "\<lbrakk> is_aligned v n; v + mask n \<le> pptrUserTop \<rbrakk> \<Longrightarrow> v \<in> user_region"
  apply (simp add: user_region_def canonical_user_def pptrUserTop_eq_mask_ipa_size
                   word_and_or_mask_aligned)
  apply (simp flip: and_mask_eq_iff_le_mask)
  apply word_eqI_solve
  done

lemma canonical_address_pptrUserTop_mask:
  "\<lbrakk> p + 2^n - 1 \<le> pptrUserTop; is_aligned p n \<rbrakk> \<Longrightarrow> canonical_address p"
  apply (rule user_region_canonical)
  apply (erule mask_pptrUserTop_user_region)
  apply (simp add: mask_def field_simps)
  done

lemma isVTableRoot_ex:
  "isVTableRoot cap = (\<exists>p m. cap = ArchObjectCap (PageTableCap p VSRootPT_T m))"
  by (simp add: isVTableRoot_def split: capability.splits arch_capability.splits pt_type.splits)

lemma isVTableRoot_cap_eq:
  "isVTableRoot cap =
     (isArchObjectCap cap \<and> isPageTableCap (capCap cap) \<and> capPTType (capCap cap) = VSRootPT_T)"
  by (auto simp: isCap_simps isVTableRoot_ex)

(* FIXME AARCH64: try to make the 48 less magic *)
lemma canonical_address_and_maskD:
  "canonical_address p \<Longrightarrow> p && mask 48 = p"
  apply (simp add: word_and_mask_shiftl pageBits_def canonical_address_range canonical_bit_def)
  apply word_eqI
  apply fastforce
  done

(* FIXME AARCH64: try to make the 48 less magic *)
lemma canonical_address_and_maskI:
  "p && mask 48 = p \<Longrightarrow> canonical_address p"
  by (simp add: word_and_mask_shiftl pageBits_def canonical_address_range canonical_bit_def
                and_mask_eq_iff_le_mask)


lemma addrFromPPtr_canonical_in_kernel_window:
  "\<lbrakk> pptrBase \<le> p; p < pptrTop \<rbrakk> \<Longrightarrow> canonical_address (addrFromPPtr p)"
  apply (simp add: addrFromPPtr_def pptrBaseOffset_def paddrBase_def canonical_address_mask_eq
                   canonical_bit_def pptrBase_def pageBits_def pptrTop_def)
  by word_bitwise clarsimp

lemma levelType_0[simp]:
  "levelType 0 = NormalPT_T"
  by (simp add: levelType_def maxPTLevel_def split: if_splits)

lemma levelType_maxPTLevel[simp]:
  "levelType maxPTLevel = VSRootPT_T"
  by (simp add: levelType_def)

(* FIXME AARCH64: move; could be simp *)
lemma pt_bits_minus_pte_bits:
  "pt_bits pt_t - pte_bits = ptTranslationBits pt_t"
  by (simp add: bit_simps)

(* FIXME AARCH64: move; could be simp *)
lemma ptTranslationBits_plus_pte_bits:
  "ptTranslationBits pt_t + pte_bits = pt_bits pt_t"
  by (simp add: bit_simps)

lemma page_table_pte_at':
  "page_table_at' pt_t p s \<Longrightarrow> pte_at' p s"
  apply (clarsimp simp: page_table_at'_def)
  apply (erule_tac x=0 in allE)
  apply simp
  done

lemma pte_at_ko':
  "pte_at' p s \<Longrightarrow> \<exists>pte. ko_at' (pte::pte) p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  done

lemma getObject_asidpool_inv[wp]:
  "\<lbrace>P\<rbrace> getObject l \<lbrace>\<lambda>rv :: asidpool. P\<rbrace>"
  apply (rule getObject_inv)
  apply simp
  apply (rule loadObject_default_inv)
  done

lemma asid_pool_at_ko'_eq:
  "(\<exists>ap :: asidpool. ko_at' ap p s) = asid_pool_at' p s"
  apply (rule iffI)
   apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  apply (case_tac ko, auto)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  done

lemma asid_pool_at_ko':
  "asid_pool_at' p s \<Longrightarrow> \<exists>pool. ko_at' (ASIDPool pool) p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def)
  apply (case_tac ko, auto)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  apply (rename_tac asidpool)
  apply (case_tac asidpool, auto)[1]
  done

(* FIXME AARCH64: move; also add vmid_bits_val to relevant bit defs *)
value_type vmid_bits = "size (0::vmid)"

(* end of move to Refine/AInvs *)

end

end
