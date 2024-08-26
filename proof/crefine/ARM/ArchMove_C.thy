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

lemma addrFromPPtr_mask_cacheLineBits:
  "addrFromPPtr ptr && mask cacheLineBits = ptr && mask cacheLineBits"
  apply (simp add: addrFromPPtr_def physMappingOffset_def kernelBase_addr_def ARM.physBase_def)
  apply word_bitwise
  apply (simp add: mask_def cacheLineBits_def)
  done

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
  apply (rule hoare_seq_ext [OF _ hoare_gets_post])
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
  apply (clarsimp simp: ps_clear_upd' lookupAround2_char1)
  done

lemma empty_fail_findPDForASID[iff]:
  "empty_fail (findPDForASID asid)"
  apply (simp add: findPDForASID_def liftME_def)
  apply (intro empty_fail_bindE, simp_all split: option.split)
     apply (simp add: assertE_def split: if_split)
    apply (simp add: assertE_def split: if_split)
   apply (simp add: empty_fail_getObject)
  apply (simp add: assertE_def liftE_bindE checkPDAt_def split: if_split)
  done

lemma empty_fail_findPDForASIDAssert[iff]:
  "empty_fail (findPDForASIDAssert asid)"
  apply (simp add: findPDForASIDAssert_def catch_def
                   checkPDAt_def checkPDUniqueToASID_def
                   checkPDASIDMapMembership_def)
  apply (intro empty_fail_bind, simp_all split: sum.split)
  done

crunches Arch.switchToThread
  for valid_queues'[wp]: valid_queues'
  (simp: crunch_simps ignore: clearExMonitor)
crunches switchToIdleThread
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
crunches switchToIdleThread, switchToThread
  for valid_pspace'[wp]: valid_pspace'
  (simp: crunch_simps)
crunches switchToThread
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

end

end
