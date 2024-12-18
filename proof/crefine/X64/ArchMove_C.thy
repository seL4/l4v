(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
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

context Arch begin arch_global_naming

lemma ps_clear_is_aligned_ctes_None:
  assumes "ps_clear p tcbBlockSizeBits s"
      and "is_aligned p tcbBlockSizeBits"
  shows "ksPSpace s (p + 2*2^cteSizeBits) = None"
    and "ksPSpace s (p + 3*2^cteSizeBits) = None"
    and "ksPSpace s (p + 4*2^cteSizeBits) = None"
  by (auto intro: assms ps_clear_is_aligned_ksPSpace_None
            simp: objBits_defs mask_def)+

(* FIXME X64: use earlier or replace with earlier def? *)
definition
  port_mask :: "16 word \<Rightarrow> 16 word \<Rightarrow> machine_word"
where
  "port_mask start end =
     mask (unat (end && mask wordRadix)) && ~~ mask (unat (start && mask wordRadix))"

lemma unat_ucast_prio_L1_cmask_simp:
  "unat (ucast (p::priority) && 0x3F :: machine_word) = unat (p && 0x3F)"
  using unat_ucast_prio_mask_simp[where m=6]
  by (simp add: mask_def)

lemma ucast_shiftl_6_absorb:
  fixes f l :: "16 word"
  assumes "f \<le> l"
  assumes "f >> 6 < l >> 6"
  shows "UCAST(16\<rightarrow>32 signed) ((f >> 6) + 1) << 6 = UCAST(16 \<rightarrow> 32 signed) (((f >> 6) + 1) << 6)"
  using assms
  by (word_bitwise, auto)

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

lemmas setEndpoint_obj_at_tcb' = setEndpoint_obj_at'_tcb

(* FIXME: Move to Schedule_R.thy. Make Arch_switchToThread_obj_at a specialisation of this *)
lemma Arch_switchToThread_obj_at_pre:
  "\<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>
   Arch.switchToThread t
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: X64_H.switchToThread_def)
  apply (wp asUser_obj_at_notQ doMachineOp_obj_at hoare_drop_imps|wpc)+
  done

crunch setThreadState
  for pspace_canonical'[wp]: pspace_canonical'

lemma word_shift_by_3:
  "x * 8 = (x::'a::len word) << 3"
  by (simp add: shiftl_t2n)

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

lemma ucast_le_ucast_8_32:
  "(ucast x \<le> (ucast y :: word32)) = (x \<le> (y :: word8))"
  by (simp add: word_le_nat_alt is_up_8_32 unat_ucast_upcast)

lemma asid_shiftr_low_bits_less:
  "(asid :: machine_word) \<le> mask asid_bits \<Longrightarrow> asid >> asid_low_bits < 0x8"
  apply (rule_tac y="2 ^ 3" in order_less_le_trans)
   apply (rule shiftr_less_t2n)
   apply (simp add: le_mask_iff_lt_2n[THEN iffD1] asid_bits_def asid_low_bits_def)
  apply simp
  done

lemma addToBitmap_sets_L1Bitmap_same_dom:
  "\<lbrace>\<lambda>s. p \<le> maxPriority \<and> d' = d \<rbrace> addToBitmap d' p
       \<lbrace>\<lambda>rv s. ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrace>"
  unfolding addToBitmap_def bitmap_fun_defs
  apply wpsimp
  apply (clarsimp simp: maxPriority_def numPriorities_def word_or_zero le_def
                        prioToL1Index_max[simplified wordRadix_def, simplified])
  done

lemma vmsz_aligned_aligned_pageBits:
  "vmsz_aligned ptr sz \<Longrightarrow> is_aligned ptr pageBits"
  apply (simp add: vmsz_aligned_def)
  apply (erule is_aligned_weaken)
  apply (simp add: pageBits_def pageBitsForSize_def
            split: vmpage_size.split)
  done

lemma empty_fail_findVSpaceForASID[iff]:
  "empty_fail (findVSpaceForASID asid)"
  unfolding findVSpaceForASID_def checkPML4At_def
  by (wpsimp wp: empty_fail_getObject)

crunch archThreadGet
  for inv'[wp]: P

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

(* FIXME: move to ainvs? *)
lemma sign_extend_canonical_address:
  "(x = sign_extend 47 x) = canonical_address x"
  by (fastforce simp: sign_extended_iff_sign_extend canonical_address_sign_extended)

crunch switchToIdleThread
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

lemma setCurrentUserCR3_valid_arch_state'[wp]:
  "\<lbrace>valid_arch_state' and K (valid_cr3' c)\<rbrace> setCurrentUserCR3 c \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (wpsimp simp: setCurrentUserCR3_def valid_arch_state'_def)

lemma setVMRoot_valid_arch_state':
  "\<lbrace>valid_arch_state'\<rbrace> setVMRoot t \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def setCurrentUserVSpaceRoot_def)
  apply (wp whenE_wp getCurrentUserCR3_wp findVSpaceForASID_vs_at_wp
         | wpcw
         | clarsimp simp: if_apply_def2 asid_wf_0
         | strengthen valid_cr3'_makeCR3)+
  done

crunch switchToThread
  for valid_arch_state'[wp]: valid_arch_state'
  (wp: crunch_wps simp: crunch_simps)

lemma mab_gt_2 [simp]:
  "2 \<le> msg_align_bits" by (simp add: msg_align_bits)

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
  apply (simp add: ef_loadWord)
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
  apply (simp add: ef_storeWord)
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

(* FIXME x64: check *)
lemma addrFromPPtr_mask:
  "n \<le> 39
    \<Longrightarrow> addrFromPPtr ptr && mask n = ptr && mask n"
  apply (simp add: addrFromPPtr_def X64.pptrBase_def)
  apply word_bitwise
  apply simp
  done

lemma asUser_get_registers:
  "\<lbrace>tcb_at' target\<rbrace>
     asUser target (mapM getRegister xs)
   \<lbrace>\<lambda>rv s. obj_at' (\<lambda>tcb. map ((user_regs o atcbContextGet o tcbArch) tcb) xs = rv) target s\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_empty asUser_return)
   apply wp
   apply simp
  apply (simp add: mapM_Cons asUser_bind_distrib asUser_return empty_fail_cond)
  apply wp
   apply simp
   apply (rule hoare_strengthen_post)
    apply (erule hoare_vcg_conj_lift)
    apply (rule asUser_inv)
    apply (simp add: getRegister_def)
    apply (wp mapM_wp')
   apply clarsimp
   apply (erule(1) obj_at_conj')
  apply (wp)
   apply (simp add: asUser_def split_def threadGet_def)
   apply (wp getObject_tcb_wp)
  apply (clarsimp simp: getRegister_def simpler_gets_def
                        obj_at'_def)
  done

(* FIXME: move to where is_aligned_ptrFromPAddr is *)
lemma is_aligned_ptrFromPAddr_pageBitsForSize:
  "is_aligned p (pageBitsForSize sz) \<Longrightarrow> is_aligned (ptrFromPAddr p) (pageBitsForSize sz)"
  by (cases sz ; simp add: is_aligned_ptrFromPAddr_n bit_simps)

lemma is_aligned_pageBitsForSize_minimum:
  "\<lbrakk> is_aligned p (pageBitsForSize sz) ; n \<le> pageBits \<rbrakk> \<Longrightarrow> is_aligned p n"
  apply (cases sz; clarsimp simp: pageBits_def)
  apply (erule is_aligned_weaken, simp)+
  done

lemma valid_objs_valid_pte': "\<lbrakk> valid_objs' s ; ko_at' (ko :: pte) p s \<rbrakk> \<Longrightarrow> valid_pte' ko s"
  by (fastforce simp add: obj_at'_def ran_def valid_obj'_def projectKOs valid_objs'_def)

lemma obj_at_kernel_mappings':
  "\<lbrakk>pspace_in_kernel_mappings' s; obj_at' P p s\<rbrakk> \<Longrightarrow>
   p \<in> kernel_mappings"
  by (clarsimp simp: pspace_in_kernel_mappings'_def obj_at'_def dom_def)

(* FIXME: move to Wellformed, turn valid_asid_pool' into an abbreviation >>>*)
primrec
  wf_asid_pool' :: "asidpool \<Rightarrow> bool"
where
  "wf_asid_pool' (ASIDPool pool) =
   (dom pool \<subseteq> {0 .. 2^asid_low_bits - 1} \<and>
    0 \<notin> ran pool \<and> (\<forall>x \<in> ran pool. is_aligned x pml4_bits))"

lemma valid_eq_wf_asid_pool'[simp]:
  "valid_asid_pool' pool = (\<lambda>s. wf_asid_pool' pool)"
  by (case_tac pool) simp

declare valid_asid_pool'.simps[simp del]
(*<<<*)

(* FIXME: change the original to be predicated! *)
crunch doMachineOp
  for pred_tcb_at'2[wp]: "\<lambda>s. P (pred_tcb_at' a b p s)"
  (simp: crunch_simps)

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
  apply simp
  apply (frule aligned_ranges_subset_or_disjoint[OF al])
  apply (simp only: add_mask_fold)
  apply (fold obj_range'_def)
  apply (rule iffI)
   apply auto[1]
  apply (rule conjI)
   apply (rule ccontr, simp)
   apply (simp add: Set.psubset_eq)
   apply (erule conjE)
   apply (case_tac "obj_range' ptr' ko \<inter> mask_range ptr bits \<noteq> {}", simp)
   apply (cut_tac is_aligned_no_overflow[OF al])
   apply (auto simp add: obj_range'_def add_mask_fold)[1]
  apply (clarsimp simp add: usableUntypedRange.simps Int_commute)
  apply (case_tac "obj_range' ptr' ko \<inter> mask_range ptr bits \<noteq> {}", simp)
  apply (cut_tac is_aligned_no_overflow[OF al])
  apply (clarsimp simp add: obj_range'_def)
  apply (frule is_aligned_no_overflow)
  apply (simp add: mask_def add_diff_eq)
  by (metis al intvl_range_conv' le_m1_iff_lt less_is_non_zero_p1
               nat_le_linear power_overflow sub_wrap add_0
               add_0_right word_add_increasing word_less_1 word_less_sub_1)

(* We don't have access to n_msgRegisters from C here, but the number of msg registers in C should
   be equivalent to what we have in the abstract/design specs. We want a number for this definition
   that automatically updates if the number of registers changes, and we sanity check it later
   in msgRegisters_size_sanity *)
definition size_msgRegisters :: nat where
  size_msgRegisters_pre_def: "size_msgRegisters \<equiv> size (X64.msgRegisters)"

schematic_goal size_msgRegisters_def:
  "size_msgRegisters = numeral ?x"
  unfolding size_msgRegisters_pre_def X64.msgRegisters_def
  by (simp add: upto_enum_red fromEnum_def enum_register del: Suc_eq_numeral)
     (simp only: Suc_eq_plus1_left, simp del: One_nat_def)

lemma length_msgRegisters[simplified size_msgRegisters_def]:
  "length X64_H.msgRegisters = size_msgRegisters"
  by (simp add: size_msgRegisters_pre_def X64_H.msgRegisters_def)

lemma empty_fail_loadWordUser[intro!, simp]:
  "empty_fail (loadWordUser x)"
  by (fastforce simp: loadWordUser_def ef_loadWord ef_dmo')

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

crunch insertNewCap, Arch_createNewCaps, threadSet, Arch.createObject, setThreadState,
         updateFreeIndex, preemptionPoint
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  (wp: crunch_wps setObject_ksPSpace_only
   simp: unless_def updateObject_default_def crunch_simps
   ignore_del: preemptionPoint)

lemma cap_case_isPML4Cap:
  "(case cap of ArchObjectCap (PML4Cap pm (Some asid)) \<Rightarrow> fn pm asid | _ => g)
    = (if (if isArchObjectCap cap then if isPML4Cap (capCap cap) then capPML4MappedASID (capCap cap) \<noteq> None else False else False)
          then fn (capPML4BasePtr (capCap cap)) (the (capPML4MappedASID (capCap cap))) else g)"
  apply (cases cap; simp add: isArchObjectCap_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability, simp_all add: isPML4Cap_def)
  apply (rename_tac option)
  apply (case_tac option; simp)
  done

end

(* these will need to be requalified when moved *)
arch_requalify_facts
  empty_fail_loadWordUser

lemmas [intro!, simp] = empty_fail_loadWordUser

end
