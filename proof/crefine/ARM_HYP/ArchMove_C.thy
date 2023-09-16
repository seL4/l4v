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

(* FIXME move: need a theory on top of CSpec that arches can share *)
(* word size corresponding to a C int (e.g. 32 bit signed on x64 and ARM *)
type_synonym int_sword = "machine_word_len signed word"

(* FIXME: rewrite using 'unat_shiftr_shiftl_mask_zero *)
(* this one is specialised to a PDE for a supersection *)
lemma vaddr_segment_nonsense6:
  "is_aligned (p :: word32) 14 \<Longrightarrow>
   (p + (vaddr >> 21 << 3) && ~~ mask 14) = p"
  apply (rule is_aligned_add_helper[THEN conjunct2])
   apply (erule is_aligned_weaken, simp)
  apply simp
  apply (rule shiftl_less_t2n[where m=14 and n=3 and 'a=machine_word_len, simplified])
  apply (rule shiftr_less_t2n'[where m=11 and n=21 and 'a=machine_word_len, simplified])
  done

(* Short-hand for  unfolding cumbersome machine constants *)
(* FIXME MOVE these should be in refine, and the _eq forms should NOT be declared [simp]! *)
(* FIXME YUCK where did you come from *)
declare ptBits_eq[simp del] (* used everywhere in CRefine, breaks clarsimp-normal form of rules *)
declare pdBits_eq[simp del] (* used everywhere in CRefine, breaks clarsimp-normal form of rules *)
declare pteBits_eq[simp del] (* used everywhere in CRefine, breaks clarsimp-normal form of rules *)
declare pdeBits_eq[simp del] (* used everywhere in CRefine, breaks clarsimp-normal form of rules *)
declare vcpuBits_eq[simp del] (* used everywhere in CRefine, breaks clarsimp-normal form of rules *)

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

lemma unat_ucast_prio_L1_cmask_simp:
  "unat (ucast (p::priority) && 0x1F :: machine_word) = unat (p && 0x1F)"
  using unat_ucast_prio_mask_simp[where m=5]
  by (simp add: mask_def)

lemma machine_word_and_1F_less_20:
  "(w :: machine_word) && 0x1F < 0x20"
  by (rule word_and_less', simp)

lemma prio_ucast_shiftr_wordRadix_helper: (* FIXME generalise *)
  "(ucast (p::priority) >> wordRadix :: machine_word) < 8"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_ucast_shiftr_wordRadix_helper': (* FIXME generalise *)
  "(ucast (p::priority) >> wordRadix :: machine_word) \<le> 7"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_unat_shiftr_wordRadix_helper': (* FIXME generalise *)
  "unat ((p::priority) >> wordRadix) \<le> 7"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_ucast_shiftr_wordRadix_helper2:
  "(ucast (p::priority) >> wordRadix :: machine_word) < 0x20"
  by (rule order_less_trans[OF prio_ucast_shiftr_wordRadix_helper]; simp)

(* FIXME: Move to Schedule_R.thy. Make Arch_switchToThread_obj_at a specialisation of this *)
lemma Arch_switchToThread_obj_at_pre:
  "\<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>
   Arch.switchToThread t
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: ARM_HYP_H.switchToThread_def)
  apply (wp doMachineOp_obj_at setVMRoot_obj_at'_no_vcpu hoare_drop_imps | wpc)+
  done

(* FIXME: This is cheating since ucast from 10 to 16 will never give us 0xFFFF.
          However type of 10 word is from irq oracle so it is the oracle that matters not this lemma.
   (Xin) *)
lemma ucast_not_helper_cheating:
  fixes a:: "10 word"
  assumes a: "ucast a \<noteq> (0xFFFF :: word16)"
  shows "ucast a \<noteq> (0xFFFF::32 signed word)"
  by (word_bitwise,simp)

lemma ucast_helper_not_maxword:
  "UCAST(10 \<rightarrow> 32) x \<noteq> 0xFFFF"
  apply (subgoal_tac "UCAST(10 \<rightarrow> 32) x \<le> UCAST(10 \<rightarrow> 32) max_word")
   apply (rule notI)
   defer
  apply (rule ucast_up_mono_le)
    apply simp
   apply simp
  by (simp add: mask_def)

lemmas ucast_helper_simps_32 =
  ucast_helper_not_maxword arg_cong[where f="UCAST(16 \<rightarrow> 32)", OF minus_one_norm]

lemma addToBitmap_sets_L1Bitmap_same_dom:
  "\<lbrace>\<lambda>s. p \<le> maxPriority \<and> d' = d \<rbrace> addToBitmap d' p
       \<lbrace>\<lambda>rv s. ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrace>"
  unfolding addToBitmap_def bitmap_fun_defs
  apply wpsimp
  by (metis nth_0 of_nat_numeral prioToL1Index_bit_set word_neq_0_conv word_or_zero)

context begin interpretation Arch .

lemma setCTE_asidpool':
  "\<lbrace> ko_at' (ASIDPool pool) p \<rbrace> setCTE c p' \<lbrace>\<lambda>_. ko_at' (ASIDPool pool) p\<rbrace>"
  apply (clarsimp simp: setCTE_def)
  apply (simp add: setObject_def split_def)
  apply (rule hoare_seq_ext [OF _ hoare_gets_sp])
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

lemma udpateCap_asidpool':
  "\<lbrace> ko_at' (ASIDPool pool) p \<rbrace> updateCap c p' \<lbrace>\<lambda>_. ko_at' (ASIDPool pool) p\<rbrace>"
  apply (simp add: updateCap_def)
  apply (wp setCTE_asidpool')
  done

lemma asid_pool_at_ko:
  "asid_pool_at' p s \<Longrightarrow> \<exists>pool. ko_at' (ASIDPool pool) p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko, auto)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  apply (rename_tac asidpool)
  apply (case_tac asidpool, auto)[1]
  done

lemma dmo_invalidateCacheRange_RAM_invs'[wp]:
  "valid invs' (doMachineOp (invalidateCacheRange_RAM vs ve ps)) (\<lambda>rv. invs')"
  apply (wp dmo_invs' no_irq no_irq_invalidateCacheRange_RAM)
  apply (clarsimp simp: disj_commute[of "pointerInUserData p s" for p s])
  apply (erule use_valid)
   apply (wp, simp)
  done

lemma empty_fail_findPDForASID[iff]:
  "empty_fail (findPDForASID asid)"
  unfolding findPDForASID_def checkPDAt_def
  by (wpsimp wp: empty_fail_getObject)

lemma empty_fail_findPDForASIDAssert[iff]:
  "empty_fail (findPDForASIDAssert asid)"
  unfolding findPDForASIDAssert_def checkPDAt_def checkPDUniqueToASID_def checkPDASIDMapMembership_def
  by (wpsimp wp: empty_fail_getObject)

lemma vcpu_at_ko:
  "vcpu_at' p s \<Longrightarrow> \<exists>vcpu. ko_at' (vcpu::vcpu) p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object, auto)[1]
  done

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

lemma mab_gt_2 [simp]:
  "2 \<le> msg_align_bits" by (simp add: msg_align_bits)

lemmas pt_bits_def' = pt_bits_def[simplified pte_bits_def, simplified]
lemmas pd_bits_def' = pd_bits_def[simplified pde_bits_def, simplified]
lemmas page_bits_def' = page_bits_def[simplified pageBits_def, simplified]
lemmas ptBits_def' = ptBits_def[simplified pteBits_def, simplified]
lemmas pdBits_def' = pdBits_def[simplified pdeBits_def, simplified]
lemmas pt_index_bits_def' = pt_index_bits_def[simplified pt_bits_def pte_bits_def, simplified]
lemmas vcpuBits_def' = vcpuBits_def[simplified pageBits_def, simplified]
lemmas vcpu_bits_def' = vcpu_bits_def[simplified pageBits_def, simplified]

lemmas table_bits_defs = pt_bits_def' pte_bits_def pd_bits_def' pde_bits_def
                         pageBits_def page_bits_def'
                         pteBits_def pdeBits_def
                         pt_index_bits_def'
                         ptBits_def' pdBits_def'

lemmas machine_bits_defs = table_bits_defs
                            vcpuBits_def' vcpu_bits_def'

(* FIXME: move to where is_aligned_ptrFromPAddr is *)
lemma is_aligned_ptrFromPAddr_pageBitsForSize:
  "is_aligned p (pageBitsForSize sz) \<Longrightarrow> is_aligned (ptrFromPAddr p) (pageBitsForSize sz)"
  by (cases sz ; simp add: is_aligned_ptrFromPAddr_n pageBits_def)

(* FIXME: generalise, move to Word_Lib, and/or rewrite using
   'leq_high_bits_shiftr_low_bits_leq_bits' *)
lemma le_mask_asid_bits_helper:
  "x \<le> 2 ^ asid_high_bits - 1 \<Longrightarrow> (x::word32) << asid_low_bits \<le> mask asid_bits"
  apply (simp add: mask_def)
  apply (drule le2p_bits_unset_32)
   apply (simp add: asid_high_bits_def word_bits_def)
  apply (subst upper_bits_unset_is_l2p_32 [symmetric])
   apply (simp add: asid_bits_def word_bits_def)
  apply (clarsimp simp: asid_bits_def asid_low_bits_def asid_high_bits_def nth_shiftl)
  done

lemma valid_objs_valid_pte': "\<lbrakk> valid_objs' s ; ko_at' (ko :: pte) p s \<rbrakk> \<Longrightarrow> valid_pte' ko s"
  by (fastforce simp add: obj_at'_def ran_def valid_obj'_def projectKOs valid_objs'_def)

lemma is_aligned_pageBitsForSize_minimum:
  "\<lbrakk> is_aligned p (pageBitsForSize sz) ; n \<le> pageBits \<rbrakk> \<Longrightarrow> is_aligned p n"
  apply (cases sz; clarsimp simp: pageBits_def)
  apply (erule is_aligned_weaken, simp)+
  done

(* FIXME: generalise, move to Word_Lib, and/or rewrite using 'shift_then_mask_eq_shift_low_bits' *)
lemma shiftr_asid_low_bits_mask_asid_high_bits:
  "(asid :: word32) \<le> mask asid_bits
      \<Longrightarrow> (asid >> asid_low_bits) && mask asid_high_bits = asid >> asid_low_bits"
  apply (rule iffD2 [OF mask_eq_iff_w2p])
   apply (simp add: asid_high_bits_def word_size)
  apply (rule shiftr_less_t2n)
  apply (simp add: asid_low_bits_def asid_high_bits_def mask_def)
  apply (simp add: asid_bits_def)
  done

lemma ucast_asid_high_bits_is_shift:
  "asid \<le> mask asid_bits
   \<Longrightarrow> ucast (asid_high_bits_of asid) = (asid >> asid_low_bits)"
  unfolding asid_bits_def asid_low_bits_def asid_high_bits_of_def
  by (rule ucast_ucast_eq_mask_shift, simp)

(* FIXME: generalise, move to Word_Lib, and/or rewrite using 'leq_low_bits_iff_zero' *)
lemma shiftr_asid_low_bits_mask_eq_0:
  "\<lbrakk> (asid :: word32) \<le> mask asid_bits; asid >> asid_low_bits = 0 \<rbrakk>
        \<Longrightarrow> (asid && mask asid_low_bits = 0) = (asid = 0)"
  apply (rule iffI[rotated])
   apply simp
  apply (rule asid_low_high_bits)
     apply simp
    apply (simp add: ucast_asid_high_bits_is_shift)
   apply (simp add: mask_def)
  apply simp
  done

(* FIXME: consider generalising and moving to Word_Lemmas *)
lemma vaddr_segment_nonsense3_folded:
  "is_aligned (p :: word32) pageBits \<Longrightarrow>
   (p + ((vaddr >> pageBits) && mask (pt_bits - pte_bits) << pte_bits) && ~~ mask pt_bits) = p"
  apply (rule is_aligned_add_helper[THEN conjunct2])
   apply (simp add: vspace_bits_defs mask_def)+
  apply (rule shiftl_less_t2n[where m=12 and n=3, simplified, OF and_mask_less'[where n=9, unfolded mask_def, simplified]])
   apply simp+
  done

(* FIXME: ARMHYP move, to SR_Lemmas? *)
lemma isPTE_exclusion:
  "isInvalidPTE pte   \<Longrightarrow> \<not> (isSmallPagePTE pte) \<and> \<not> (isLargePagePTE pte)"
  "isLargePagePTE pte \<Longrightarrow> \<not> (isInvalidPTE pte)   \<and> \<not> (isSmallPagePTE pte)"
  "isSmallPagePTE pte \<Longrightarrow> \<not> (isInvalidPTE pte)   \<and> \<not> (isLargePagePTE pte)"
  by (cases pte ;  clarsimp simp: isInvalidPTE_def isSmallPagePTE_def isLargePagePTE_def)+

lemma length_superSectionPDEOffsets_simp [simp]:
  "length superSectionPDEOffsets = 16"
  by (simp add: length_superSectionPDEOffsets)

lemma length_largePagePTEOffsets_simp [simp]:
  "length largePagePTEOffsets = 16"
  by (simp add: length_largePagePTEOffsets)

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

(* FIXME: rewrite using ucast_ucast_mask_shift *)
lemma ucast_ucast_mask_pageBits_shift:
  "ucast (ucast (p && mask pageBits >> 2) :: 10 word) = p && mask pageBits >> 2"
  apply (rule word_eqI)
  apply (auto simp: word_size nth_ucast nth_shiftr pageBits_def)
  done

(* FIXME: rewrite using unat_ucast_mask_shift *)
lemma unat_ucast_mask_pageBits_shift:
  "unat (ucast (p && mask pageBits >> 2) :: 10 word) = unat ((p::word32) && mask pageBits >> 2)"
  apply (simp only: unat_ucast)
  apply (rule Divides.mod_less, simp)
  apply (rule unat_less_power)
   apply (simp add: word_bits_def)
  apply (rule shiftr_less_t2n)
  apply (rule order_le_less_trans [OF word_and_le1])
  apply (simp add: pageBits_def mask_def)
  done

(* FIXME: rewrite using mask_shift_sum *)
lemma mask_pageBits_shift_sum:
  "unat n = unat (p && mask 2) \<Longrightarrow>
  (p && ~~ mask pageBits) + (p && mask pageBits >> 2) * 4 + n = (p::word32)"
  apply (clarsimp simp: word_shift_by_2)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size pageBits_def nth_shiftl nth_shiftr word_ops_nth_size)
   apply arith
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size pageBits_def nth_shiftl nth_shiftr word_ops_nth_size)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size pageBits_def nth_shiftl nth_shiftr word_ops_nth_size)
  apply (auto simp: linorder_not_less SucSucMinus)
  done

lemma vcpu_at_ko'_eq:
  "(\<exists>vcpu :: vcpu. ko_at' vcpu p s) = vcpu_at' p s"
  apply (rule iffI)
   apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
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
  apply (case_tac ko; simp add: tcb_vcpu_refs'_def projectKOs)
  apply (rename_tac koa)
  apply (case_tac koa; clarsimp simp: refs_of_a_def vcpu_tcb_refs'_def)
  done


lemma ko_at'_tcb_vcpu_not_NULL:
  "\<lbrakk> ko_at' (tcb::tcb) t s ; valid_objs' s ; no_0_obj' s ; atcbVCPUPtr (tcbArch tcb) = Some p \<rbrakk>
   \<Longrightarrow> 0 < p"
  \<comment> \<open>when C pointer is NULL, need this to show atcbVCPUPtr is None\<close>
  unfolding valid_pspace'_def
  supply word_neq_0_conv[simp del]
  by (fastforce simp: valid_tcb'_def valid_arch_tcb'_def word_gt_0 typ_at'_no_0_objD
                dest: valid_objs_valid_tcb')


(* FIXME move *)
lemma setVMRoot_valid_queues':
  "\<lbrace> valid_queues' \<rbrace> setVMRoot a \<lbrace> \<lambda>_. valid_queues' \<rbrace>"
  by (rule valid_queues_lift'; wp)

lemma vcpuEnable_valid_pspace' [wp]:
  "\<lbrace> valid_pspace' \<rbrace> vcpuEnable a \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  by (wpsimp simp: valid_pspace'_def valid_mdb'_def)

lemma vcpuSave_valid_pspace' [wp]:
  "\<lbrace> valid_pspace' \<rbrace> vcpuSave a \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  by (wpsimp simp: valid_pspace'_def valid_mdb'_def)

lemma vcpuRestore_valid_pspace' [wp]:
  "\<lbrace> valid_pspace' \<rbrace> vcpuRestore a \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  by (wpsimp simp: valid_pspace'_def valid_mdb'_def)

lemma vcpuSwitch_valid_pspace' [wp]:
  "\<lbrace> valid_pspace' \<rbrace> vcpuSwitch a \<lbrace>\<lambda>_. valid_pspace' \<rbrace>"
  by (wpsimp simp: valid_pspace'_def valid_mdb'_def)

lemma ko_at_vcpu_at'D:
  "ko_at' (vcpu :: vcpu) vcpuptr s \<Longrightarrow> vcpu_at' vcpuptr s"
  by (fastforce simp: typ_at_to_obj_at_arches elim: obj_at'_weakenE)


(* FIXME: change the original to be predicated! *)
crunch ko_at'2[wp]: doMachineOp "\<lambda>s. P (ko_at' p t s)"
  (simp: crunch_simps)

(* FIXME: change the original to be predicated! *)
crunch pred_tcb_at'2[wp]: doMachineOp "\<lambda>s. P (pred_tcb_at' a b p s)"
  (simp: crunch_simps)

crunch valid_queues'[wp]: readVCPUReg "\<lambda>s. valid_queues s"

crunch valid_objs'[wp]: readVCPUReg "\<lambda>s. valid_objs' s"

crunch sch_act_wf'[wp]: readVCPUReg "\<lambda>s. P (sch_act_wf (ksSchedulerAction s) s)"

crunch ko_at'[wp]: readVCPUReg "\<lambda>s. P (ko_at' a p s)"

crunch obj_at'[wp]: readVCPUReg "\<lambda>s. P (obj_at' a p s)"

crunch pred_tcb_at'[wp]: readVCPUReg "\<lambda>s. P (pred_tcb_at' a b p s)"

crunch ksCurThread[wp]: readVCPUReg "\<lambda>s. P (ksCurThread s)"

lemma fromEnum_maxBound_vcpureg_def:
  "fromEnum (maxBound :: vcpureg) = 41"
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
  by (fastforce simp: ps_clear_def)

lemma ps_clear_ksPSpace_upd_same[simp]:
  "ps_clear p n (s\<lparr>ksPSpace := (ksPSpace s)(p \<mapsto> v)\<rparr>) = ps_clear p n s"
  by (fastforce simp: ps_clear_def)

lemma getObject_vcpu_prop:
  "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(vcpu :: vcpu) s. P vcpu\<rbrace>"
  apply (rule obj_at_getObject)
  apply (clarsimp simp: loadObject_default_def in_monad projectKOs)
  done

(* FIXME would be interesting to generalise these kinds of lemmas to other KOs *)
lemma setObject_sets_object_vcpu:
  "\<lbrace> vcpu_at' v \<rbrace> setObject v (vcpu::vcpu) \<lbrace> \<lambda>_. ko_at' vcpu v \<rbrace>"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: setObject_def updateObject_default_def bind_assoc)
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift simp: alignError_def)
  apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def archObjSize_def dest!: vcpu_at_ko')
  apply (fastforce simp: fun_upd_apply)
  done

(* FIXME would be interesting to generalise these kinds of lemmas to other KOs *)
lemma placeNewObject_creates_object_vcpu:
  "\<lbrace> \<top> \<rbrace> placeNewObject v (vcpu::vcpu) 0 \<lbrace> \<lambda>_. ko_at' vcpu v \<rbrace>"
  supply fun_upd_apply[simp del] word_neq_0_conv[simp del] haskell_assert_inv[wp del]
  apply (clarsimp simp: placeNewObject_def placeNewObject'_def split_def alignError_def)
  apply (wpsimp wp: assert_wp hoare_vcg_imp_lift' hoare_vcg_ex_lift)
  apply (clarsimp simp: is_aligned_mask[symmetric] objBitsKO_def archObjSize_def)
  apply (case_tac "is_aligned v vcpuBits"; clarsimp)
  apply (rule conjI; clarsimp)
   apply (subst (asm) lookupAround2_None1)
   apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def archObjSize_def fun_upd_apply)
   apply (fastforce intro: ps_clear_entire_slotI simp add: field_simps fun_upd_apply)
  apply (subst (asm) lookupAround2_char1)
  apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def archObjSize_def fun_upd_apply)
  apply (fastforce intro: ps_clear_entire_slotI simp add: field_simps)
  done

(* FIXME would be interesting to generalise these kinds of lemmas to other KOs *)
lemma placeNewObject_object_at_vcpu:
  "\<lbrace> \<top> \<rbrace> placeNewObject v (vcpu::vcpu) 0 \<lbrace> \<lambda>_. vcpu_at' v \<rbrace>"
  by (rule hoare_post_imp[OF _ placeNewObject_creates_object_vcpu])
     (fastforce simp: ko_at_vcpu_at'D)

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
  size_msgRegisters_pre_def: "size_msgRegisters \<equiv> size (ARM_HYP.msgRegisters)"

schematic_goal size_msgRegisters_def:
  "size_msgRegisters = numeral ?x"
  unfolding size_msgRegisters_pre_def ARM_HYP.msgRegisters_def
  by (simp add: upto_enum_red fromEnum_def enum_register del: Suc_eq_numeral)
     (simp only: Suc_eq_plus1_left, simp del: One_nat_def)

lemma length_msgRegisters[simplified size_msgRegisters_def]:
  "length ARM_HYP_H.msgRegisters = size_msgRegisters"
  by (simp add: size_msgRegisters_pre_def ARM_HYP_H.msgRegisters_def)

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
  "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb r)) t\<rbrace> asUser t (getRegister r) \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply (clarsimp simp: obj_at'_def projectKOs getRegister_def in_monad atcbContextGet_def)
  done

crunches insertNewCap, Arch_createNewCaps, threadSet, Arch.createObject, setThreadState,
         updateFreeIndex, preemptionPoint
  for gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  (wp: crunch_wps setObject_ksPSpace_only
   simp: unless_def updateObject_default_def crunch_simps
   ignore_del: preemptionPoint)

(* this could be done as
   lemmas addrFromPPtr_mask_6 = addrFromPPtr_mask[where n=6, simplified]
   but that wouldn't give a sanity check of the n \<le> ... assumption  disappearing *)
lemma addrFromPPtr_mask_6:
  "addrFromPPtr ptr && mask 6 = ptr && mask 6"
  by (rule addrFromPPtr_mask[where n=6, simplified])

lemma ptrFromPAddr_mask_6:
  "ptrFromPAddr ps && mask 6 = ps && mask 6"
  by (rule ptrFromPAddr_mask[where n=6, simplified])

end

end
