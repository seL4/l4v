(*
 * Copyright 2023, Proofcraft Pty Ltd
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
  apply (simp add: dom_def word_gt_0 del: word_neq_0_conv)
  apply (drule mp)
   apply (rule word_plus_mono_right)
    apply simp
   apply (simp add: mask_2pm1)
   apply (erule is_aligned_no_overflow')
  apply (drule mp)
   apply (case_tac "(0::word32)<2^n")
    apply (frule le_m1_iff_lt[of "(2::word32)^n" d, THEN iffD1])
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

(* FIXME: Move to Schedule_R.thy. Make Arch_switchToThread_obj_at a specialisation of this *)
lemma Arch_switchToThread_obj_at_pre:
  "\<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>
   Arch.switchToThread t
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: ARM_H.switchToThread_def)
  apply (wp doMachineOp_obj_at setVMRoot_obj_at hoare_drop_imps|wpc)+
  done

context begin interpretation Arch .

lemma asid_pool_at'_ko:
  "asid_pool_at' p s \<Longrightarrow> \<exists>pool. ko_at' (ASIDPool pool) p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko, auto)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  apply (rename_tac asidpool)
  apply (case_tac asidpool, auto)[1]
  done

lemma setCTE_asidpool':
  "\<lbrace> ko_at' (ASIDPool pool) p \<rbrace> setCTE c p' \<lbrace>\<lambda>_. ko_at' (ASIDPool pool) p\<rbrace>"
  apply (clarsimp simp: setCTE_def)
  apply (simp add: setObject_def split_def)
  apply (rule bind_wp [OF _ hoare_gets_sp])
  apply (clarsimp simp: valid_def in_monad)
  apply (frule updateObject_type)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (rule conjI)
   apply (clarsimp simp: lookupAround2_char1)
   apply (case_tac obj', auto)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, auto)[1]
   apply (simp add: updateObject_cte)
   apply (clarsimp simp: updateObject_cte typeError_def magnitudeCheck_def in_monad
                   split: kernel_object.splits if_splits option.splits)
  apply (clarsimp simp: ps_clear_upd lookupAround2_char1)
  done

lemma empty_fail_findPDForASID[iff]:
  "empty_fail (findPDForASID asid)"
  unfolding findPDForASID_def checkPDAt_def
  by (wpsimp wp: empty_fail_getObject)

lemma empty_fail_findPDForASIDAssert[iff]:
  "empty_fail (findPDForASIDAssert asid)"
  unfolding findPDForASIDAssert_def checkPDAt_def checkPDUniqueToASID_def checkPDASIDMapMembership_def
  by (wpsimp wp: empty_fail_getObject)

crunch switchToIdleThread
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

crunch switchToThread
  for valid_arch_state'[wp]: valid_arch_state'

lemma mab_gt_2 [simp]:
  "2 \<le> msg_align_bits" by (simp add: msg_align_bits)

(* this one is specialised to a PDE for a supersection *)
lemma vaddr_segment_nonsense6:
  "is_aligned (p :: word32) pdBits \<Longrightarrow>
   (p + (vaddr >> 20 << 2) && ~~ mask pdBits) = p"
  apply (rule is_aligned_add_helper[THEN conjunct2])
   apply (erule is_aligned_weaken, simp)
  apply (simp add: pdBits_def pdeBits_def)
  apply (rule shiftl_less_t2n[where m=14 and n=2 and 'a=machine_word_len, simplified])
  apply (rule shiftr_less_t2n'[where m=12 and n=20 and 'a=machine_word_len, simplified])
  done

(* FIXME: move to Wellformed, turn valid_asid_pool' into an abbreviation >>>*)
primrec
  wf_asid_pool' :: "asidpool \<Rightarrow> bool"
where
  "wf_asid_pool' (ASIDPool pool) =
   (dom pool \<subseteq> {0 .. 2^asid_low_bits - 1} \<and>
    0 \<notin> ran pool \<and> (\<forall>x \<in> ran pool. is_aligned x pdBits))"

lemma valid_eq_wf_asid_pool'[simp]:
  "valid_asid_pool' pool = (\<lambda>s. wf_asid_pool' pool)"
  by (case_tac pool) simp
declare valid_asid_pool'.simps[simp del]
(*<<<*)

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
  apply (fold obj_range'_def)
  apply (rule iffI)
   apply auto[1]
  apply (rule conjI)
   apply (rule ccontr, simp)
   apply (simp add: Set.psubset_eq)
   apply (erule conjE)
   apply (case_tac "obj_range' ptr' ko \<inter> {ptr..ptr + 2 ^ bits - 1} \<noteq> {}", simp)
   apply (cut_tac is_aligned_no_overflow[OF al])
   apply (auto simp add: obj_range'_def)[1]
  apply (clarsimp simp add: usableUntypedRange.simps Int_commute)
  apply (case_tac "obj_range' ptr' ko \<inter> {ptr..ptr + 2 ^ bits - 1} \<noteq> {}", simp+)
  apply (cut_tac is_aligned_no_overflow[OF al])
  apply (clarsimp simp add: obj_range'_def)
  apply (frule is_aligned_no_overflow)
  by (metis al intvl_range_conv' le_m1_iff_lt less_is_non_zero_p1
               nat_le_linear power_overflow sub_wrap add_0
               add_0_right word_add_increasing word_less_1 word_less_sub_1)

(* We don't have access to n_msgRegisters from C here, but the number of msg registers in C should
   be equivalent to what we have in the abstract/design specs. We want a number for this definition
   that automatically updates if the number of registers changes, and we sanity check it later
   in msgRegisters_size_sanity *)
definition size_msgRegisters :: nat where
  size_msgRegisters_pre_def: "size_msgRegisters \<equiv> size (ARM.msgRegisters)"

schematic_goal size_msgRegisters_def:
  "size_msgRegisters = numeral ?x"
  unfolding size_msgRegisters_pre_def ARM.msgRegisters_def
  by (simp add: upto_enum_red fromEnum_def enum_register del: Suc_eq_numeral)
     (simp only: Suc_eq_plus1_left, simp del: One_nat_def)

lemma length_msgRegisters[simplified size_msgRegisters_def]:
  "length ARM_H.msgRegisters = size_msgRegisters"
  by (simp add: size_msgRegisters_pre_def ARM_H.msgRegisters_def)

lemma cap_case_isPageDirectoryCap:
  "(case cap of capability.ArchObjectCap (arch_capability.PageDirectoryCap pd ( Some asid))  \<Rightarrow> fn pd asid
                | _ => g)
    = (if ( if (isArchObjectCap cap) then if (isPageDirectoryCap (capCap cap)) then capPDMappedASID (capCap cap) \<noteq> None else False else False)
                then fn (capPDBasePtr (capCap cap)) (the ( capPDMappedASID (capCap cap))) else g)"
  apply (cases cap; simp add: isArchObjectCap_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability, simp_all add: isPageDirectoryCap_def)
  apply (rename_tac option)
  apply (case_tac option; simp)
  done

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
  "\<lbrace>obj_at' (\<lambda>tcb. P ((user_regs \<circ> atcbContextGet \<circ> tcbArch) tcb r)) t\<rbrace>
   asUser t (getRegister r)
   \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply (clarsimp simp: obj_at'_def projectKOs getRegister_def in_monad atcbContextGet_def)
  done

crunch insertNewCap, Arch_createNewCaps, threadSet, Arch.createObject, setThreadState,
         updateFreeIndex, preemptionPoint
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  (wp: crunch_wps setObject_ksPSpace_only
   simp: unless_def updateObject_default_def crunch_simps
   ignore_del: preemptionPoint)

lemma addrFromPPtr_mask[simplified ARM.pageBitsForSize_simps]:
  "n \<le> pageBitsForSize ARMSuperSection
   \<Longrightarrow> addrFromPPtr ptr && mask n = ptr && mask n"
  apply (simp add: addrFromPPtr_def)
  apply (prop_tac "pptrBaseOffset AND mask n = 0")
   apply (rule mask_zero[OF is_aligned_weaken[OF pptrBaseOffset_aligned]], simp)
  apply (simp flip: mask_eqs(8))
  done

(* this could be done as
   lemmas addrFromPPtr_mask_5 = addrFromPPtr_mask[where n=5, simplified]
   but that wouldn't give a sanity check of the n \<le> ... assumption  disappearing *)
lemma addrFromPPtr_mask_5:
  "addrFromPPtr ptr && mask 5 = ptr && mask 5"
  by (rule addrFromPPtr_mask[where n=5, simplified])

end

end
