(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific proofs about untyped invocations. *)

theory ArchUntyped_R
imports Untyped_R
begin

context Arch begin arch_global_naming

named_theorems Untyped_R_assms

lemma APIType_map2_CapTable[Untyped_R_assms, simp]:
  "(APIType_map2 ty = Structures_A.CapTableObject)
   = (ty = Inr (APIObjectType ArchTypes_H.CapTableObject))"
  by (simp add: APIType_map2_def
         split: sum.split X64_H.object_type.split
                apiobject_type.split
                kernel_object.split arch_kernel_object.splits)

lemmas is_frame_type_defs = is_frame_type_def isFrameType_def arch_is_frame_type_def

lemma is_frame_type_isFrameType_eq[Untyped_R_assms, simp]:
  "(is_frame_type (APIType_map2 (Inr (toEnum (unat arg0))))) =
   (isFrameType (toEnum (unat arg0)))"
  by (simp add: APIType_map2_def is_frame_type_defs split: apiobject_type.splits object_type.splits)+

(* object_type enum (arch-specific) is extension of apiobject_type enum (generic) *)
lemma nth_enum_object_type_gen_eq[Untyped_R_assms]:
  assumes "n < length (enum :: apiobject_type list)"
  shows "((enum :: object_type list) ! n) = APIObjectType ((enum :: apiobject_type list) ! n)"
proof -
  have take_nth_eq:
    "\<And>n k xs. n < k \<Longrightarrow> (xs ! n) = (take k xs ! n)"
    by simp

  show ?thesis using assms
    unfolding enum_apiobject_type enum_object_type
    by (subst take_nth_eq[where n=n], assumption)
       (simp flip: nth_map[where f=APIObjectType])
qed

lemma length_enum_apiobject_less_enum_object_type[Untyped_R_assms]:
  "length (enum :: apiobject_type list) < length (enum :: object_type list)"
  unfolding enum_apiobject_type enum_object_type
  by simp

crunch freeMemory (* FIXME arch-split: clearMemory is already handled in ArchRetype_AI *)
  for irq_masks_inv[wp, Untyped_R_assms]: "\<lambda>s. P (irq_masks s)"
  (wp: crunch_wps)

crunch updateFreeIndex, deleteGhost
  for valid_irq_states'[Untyped_R_assms, wp]: "valid_irq_states'"
  and ksInterruptState[Untyped_R_assms, wp]: "\<lambda>s. P (ksInterruptState s)"
  and gsMaxObjectSize[Untyped_R_assms, wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and ksIdleThread[Untyped_R_assms, wp]: "\<lambda>s. P (ksIdleThread s)"
  and ksCurDomain[Untyped_R_assms, wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksCurThread[Untyped_R_assms, wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: crunch_wps)

lemma arch_data_to_obj_type_invalid[Untyped_R_assms]:
  "\<lbrakk> n \<ge> length (enum :: object_type list) \<rbrakk>
   \<Longrightarrow> arch_data_to_obj_type (n - length (enum :: apiobject_type list)) = None"
  by (auto simp: enum_apiobject_type_length enum_object_type arch_data_to_obj_type_def)

lemma arch_data_to_obj_type_valid[Untyped_R_assms]:
  "\<lbrakk> n < length (enum :: object_type list); length (enum :: apiobject_type list) \<le> n \<rbrakk>
   \<Longrightarrow> arch_data_to_obj_type (n - length (enum :: apiobject_type list)) \<noteq> None"
  by (simp add: enum_apiobject_type_length enum_object_type arch_data_to_obj_type_def)
     arith

lemma APIType_map2_arch_data_to_obj_type[Untyped_R_assms]:
  defines [simp]: "object_types \<equiv> enum :: object_type list"
  defines [simp]: "apiobject_types \<equiv> enum :: apiobject_type list"
  shows
    "\<lbrakk>n < length object_types; length apiobject_types \<le> n\<rbrakk>
     \<Longrightarrow> (APIType_map2 (Inr (object_types ! n)))
        = ArchObject (the (arch_data_to_obj_type (n - length apiobject_types)))"
  supply if_split[split del]
  apply (simp add: arch_data_to_obj_type_def APIType_map2_def enum_apiobject_type_length
                   enum_object_type)
  apply (subst nth_drop_sub[symmetric], (simp add: enum_apiobject_type_length)+)
  apply (clarsimp split: if_split)
  apply arith
  done

lemma obj_bits_api_APIType_map2[Untyped_R_assms]:
  "obj_bits_api (APIType_map2 (Inr x)) y = getObjectSize x y"
  apply (clarsimp simp:obj_bits_api_def APIType_map2_def getObjectSize_def simp del: objSize_eq_capBits)
  apply (case_tac x)
        apply (simp_all add:arch_kobj_size_def default_arch_object_def pageBits_def ptBits_def)
    apply (rename_tac apiobject_type)
    apply (case_tac apiobject_type)
        apply (simp_all add: apiGetObjectSize_def slot_bits_def objBits_simps' bit_simps)
  done

lemma length_nat_to_cref[Untyped_R_assms]:
  "bits < word_bits \<Longrightarrow> length (nat_to_cref bits x) = bits"
  by (simp add: nat_to_cref_def word_bits_conv)

lemma ctes_of_ko_arch[Untyped_R_assms]:
  "\<lbrakk> valid_cap' cap s; isArchObjectCap cap \<rbrakk> \<Longrightarrow>
   \<forall>ptr\<in>capRange cap. \<exists>optr ko. ksPSpace s optr = Some ko \<and> ptr \<in> obj_range' optr ko"
  apply (case_tac cap; simp add: gen_isCap_simps capRange_def)
   \<comment> \<open>Arch cases\<close>
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability)
          \<comment> \<open>ASID case\<close>
          apply (clarsimp simp: valid_cap'_def  typ_at'_def ko_wp_at'_def)
          apply (intro exI conjI, assumption)
          apply (clarsimp simp: obj_range'_def archObjSize_def objBitsKO_def)
          apply (case_tac ko; simp)
          apply (rename_tac arch_kernel_object)
          apply (case_tac arch_kernel_object;
              simp add: archObjSize_def asid_low_bits_def mask_def add_ac bit_simps)
         apply simp
        \<comment> \<open>IOPort case\<close>
        apply clarsimp
       \<comment> \<open>IOPortControl case\<close>
       apply clarsimp
      \<comment> \<open>Page case\<close>
      apply (rename_tac word vmrights vmpage_size option)
      apply (clarsimp simp: valid_cap'_def typ_at'_def ko_wp_at'_def capAligned_def)
      apply (frule_tac ptr = ptr and sz = "pageBits" in nasty_range [where 'a=machine_word_len, folded word_bits_def])
         apply assumption
        apply (simp add: pbfs_atleast_pageBits)+
      apply (clarsimp,drule_tac x = idx in spec,clarsimp)
      apply (intro exI conjI,assumption)
      apply (clarsimp simp: obj_range'_def)
      apply (case_tac ko, simp_all split: if_splits,
            (simp add: objBitsKO_def archObjSize_def field_simps mask_def shiftl_t2n)+)[1]
     \<comment> \<open>PT case\<close>
     apply (rename_tac word option)
     apply (clarsimp simp: valid_cap'_def obj_at'_def bit_simps
                           page_table_at'_def typ_at'_def ko_wp_at'_def ptBits_def)
     apply (frule_tac ptr=ptr and sz=3 in
                    nasty_range[where 'a=machine_word_len and bz="ptBits", folded word_bits_def,
                                simplified ptBits_def word_bits_def bit_simps, simplified])
       apply simp
      apply simp
     apply clarsimp
     apply (drule_tac x=idx in spec)
     apply clarsimp
     apply (intro exI conjI,assumption)
     apply (clarsimp simp: obj_range'_def)
     apply (case_tac ko; simp)
     apply (rename_tac arch_kernel_object)
     apply (case_tac arch_kernel_object; simp)
     apply (simp add: objBitsKO_def archObjSize_def field_simps mask_def shiftl_t2n)
    \<comment> \<open>PD case\<close>
    apply (clarsimp simp: valid_cap'_def obj_at'_def pdBits_def bit_simps
                        page_directory_at'_def typ_at'_def ko_wp_at'_def)
    apply (frule_tac ptr=ptr and sz=3 in
                   nasty_range[where 'a=machine_word_len and bz="pdBits", folded word_bits_def,
                               simplified pdBits_def word_bits_def bit_simps, simplified])
      apply simp
     apply simp
    apply clarsimp
    apply (drule_tac x="idx" in spec)
    apply clarsimp
    apply (intro exI conjI, assumption)
    apply (clarsimp simp: obj_range'_def objBitsKO_def field_simps)
    apply (case_tac ko; simp)
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object; simp)
    apply (simp add: field_simps archObjSize_def shiftl_t2n mask_def)
   \<comment> \<open>PDPT case\<close>
   apply (clarsimp simp: valid_cap'_def obj_at'_def pdptBits_def bit_simps
                        pd_pointer_table_at'_def typ_at'_def ko_wp_at'_def)
   apply (frule_tac ptr=ptr and sz=3 in
                   nasty_range[where 'a=machine_word_len and bz="pdptBits", folded word_bits_def,
                               simplified pdptBits_def word_bits_def bit_simps, simplified])
     apply simp
    apply simp
   apply clarsimp
   apply (drule_tac x="idx" in spec)
   apply clarsimp
   apply (intro exI conjI, assumption)
   apply (clarsimp simp: obj_range'_def objBitsKO_def field_simps)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp)
   apply (simp add: field_simps archObjSize_def shiftl_t2n mask_def)
  \<comment> \<open>PML4 case\<close>
  apply (clarsimp simp: valid_cap'_def obj_at'_def pml4Bits_def bit_simps
                        page_map_l4_at'_def typ_at'_def ko_wp_at'_def)
  apply (frule_tac ptr=ptr and sz=3 in
                   nasty_range[where 'a=machine_word_len and bz="pml4Bits", folded word_bits_def,
                               simplified pml4Bits_def word_bits_def bit_simps, simplified])
    apply simp
   apply simp
  apply clarsimp
  apply (drule_tac x="idx" in spec)
  apply clarsimp
  apply (intro exI conjI, assumption)
  apply (clarsimp simp: obj_range'_def objBitsKO_def field_simps)
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object; simp)
  apply (simp add: field_simps archObjSize_def shiftl_t2n mask_def)
  done

lemma irq_nodes_global[Untyped_R_assms]:
  "irq_node' s + (ucast (irq :: irq) << cteSizeBits) \<in> global_refs' s"
  by (simp add: global_refs'_def cteSizeBits_def shiftl_t2n)

lemma untyped_inc_mdbD[Untyped_R_assms]:
  "\<lbrakk> sameRegionAs cap cap'; isUntypedCap cap;
     ctes p = Some (CTE cap node); ctes p' = Some (CTE cap' node');
     untyped_inc' ctes; untyped_mdb' ctes; no_loops ctes \<rbrakk>
   \<Longrightarrow> ctes \<turnstile> p \<rightarrow> p' \<or> p = p'
      \<or> (isUntypedCap cap' \<and> untypedRange cap \<subseteq> untypedRange cap'
         \<and> sameRegionAs cap' cap \<and> ctes \<turnstile> p' \<rightarrow> p)"
  apply (subgoal_tac "untypedRange cap \<subseteq> untypedRange cap' \<longrightarrow> sameRegionAs cap' cap")
   apply (cases "isUntypedCap cap'")
    apply (drule (4) untyped_incD'[where p=p and p'=p'])
    apply (erule sameRegionAsE, simp_all add: untypedCapRange)[1]
       apply (cases "untypedRange cap = untypedRange cap'")
        apply (clarsimp simp: descendants_of'_D) (* loops if combined with next clarsimp *)
        apply (clarsimp simp: descendants_of'_def isCap_simps)+
   apply (erule sameRegionAsE; simp?)
     apply (drule (1) untyped_mdbD')
         apply (fastforce simp: untypedCapRange descendants_of'_def isCap_simps)+
  apply (clarsimp simp: sameRegionAs_def3 untypedCapRange del: disjCI)
  apply (rule disjI1)
  apply (erule disjE) (* fastforce won't work with gen_isCap_simps *)
   apply (fastforce elim!: subset_trans[OF _ untypedRange_in_capRange]
                    intro: untypedRange_not_emptyD
                    simp: untypedCapRange)
  apply (clarsimp simp: isCap_simps)
  done

lemma mdb_chunked_arch_assms_non_arch[Untyped_R_assms]:
  "\<not> isArchObjectCap cap \<Longrightarrow> mdb_chunked_arch_assms cap"
  by (simp add: mdb_chunked_arch_assms_def isCap_simps)

lemma sameRegionAs_def_untyped[Untyped_R_assms]:
  "\<lbrakk> isUntypedCap cap \<rbrakk>
   \<Longrightarrow> sameRegionAs cap cap' = (capRange cap' \<noteq> {} \<and> capRange cap' \<subseteq> capRange cap)"
  by (clarsimp simp add: sameRegionAs_def3 isCap_simps)

lemma createNewCaps_range_helper[Untyped_R_assms]:
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits tp us) n \<and> 0 < n\<rbrace>
   createNewCaps tp ptr n us d
   \<lbrace>\<lambda>rv s. \<exists>capfn.
              rv = map capfn (map (\<lambda>p. ptr_add ptr (p * 2 ^ (APIType_capBits tp us))) [0 ..< n])
              \<and> (\<forall>p. capClass (capfn p) = PhysicalClass
                     \<and> capUntypedPtr (capfn p) = p
                     \<and> capBits (capfn p) = (APIType_capBits tp us))\<rbrace>"
  apply (simp add: createNewCaps_def toAPIType_def Arch_createNewCaps_def
               split del: if_split cong: option.case_cong)
  apply (rule hoare_grab_asm)+
  apply (frule range_cover.range_cover_n_less)
  apply (frule range_cover.unat_of_nat_n)
  apply (cases tp, simp_all split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)
            \<comment>\<open>Untyped\<close>
            apply (rule hoare_pre, wp)
            apply (frule range_cover_not_zero[rotated -1],simp)
            apply (clarsimp simp: APIType_capBits_gen_def objBits_simps ptr_add_def o_def)
            apply (subst upto_enum_red')
             apply unat_arith
            apply (clarsimp simp: o_def fromIntegral_def toInteger_nat fromInteger_nat)
            apply fastforce
           \<comment>\<open>TCB\<close>
           apply (rule hoare_pre, wp createObjects_ret2)
            apply (wpsimp simp: curDomain_def)
           apply (clarsimp simp: APIType_capBits_gen_def word_bits_def objBits_simps ptr_add_def o_def)
           apply (fastforce simp: objBitsKO_def objBits_def)
          \<comment>\<open>other APIObjectType\<close>
          apply ((rule hoare_pre, wp createObjects_ret2,
                  clarsimp simp: APIType_capBits_gen_def word_bits_def objBits_simps ptr_add_def o_def,
                  fastforce simp: objBitsKO_def objBits_def)+)[3]
       \<comment>\<open>Arch objects\<close>
       by (wp createObjects_ret2
           | clarsimp simp: APIType_capBits_def objBits_if_dev word_bits_def
                 split del: if_split
           | simp add: objBits_simps
           | (rule exI, (fastforce simp: bit_simps)))+

fun isDeviceCap :: "capability \<Rightarrow> bool" where
  "isDeviceCap (UntypedCap d _ _ _) = d"
| "isDeviceCap (ArchObjectCap (PageCap _ _ _ _ d _)) = d"
| "isDeviceCap _ = False"

lemma deleteObjects_caps_no_overlap'':
  "\<lbrace>\<lambda>s. invs' s \<and> ct_active' s \<and> sch_act_simple s \<and>
        cte_wp_at' (\<lambda>c. cteCap c = capability.UntypedCap d ptr sz idx) slot s \<and>
        caps_no_overlap'' ptr sz s \<and>
        descendants_range' (capability.UntypedCap d ptr sz idx) slot (ctes_of s)\<rbrace>
   deleteObjects ptr sz
   \<lbrace>\<lambda>rv s. caps_no_overlap'' ptr sz s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp split:if_splits)
  apply (clarsimp simp:caps_no_overlap''_def2 deleteObjects_def2 capAligned_def valid_cap'_def
    dest!:ctes_of_valid_cap')
  apply (wp deleteObjects_null_filter[where idx = idx and p = slot])
  apply (clarsimp simp:cte_wp_at_ctes_of invs_def)
  apply (case_tac cte)
  apply clarsimp
  apply (frule ctes_of_valid_cap')
   apply (simp add:invs_valid_objs')
  apply (simp add:valid_cap'_def capAligned_def)
  done

(* trivial on this architecture *)
defs archOverlap_def:
  "archOverlap \<equiv> \<lambda>_ _. False"

(* trivial on this architecture *)
lemma archNoOverlap[Untyped_R_assms]:
  notes Int_atLeastAtMost[simp del]
  shows
  "corres dc (\<lambda>s. \<exists>cref. cte_wp_at (\<lambda>cap. is_untyped_cap cap
                                          \<and> Collect R \<subseteq> usable_untyped_range cap) cref s
                         \<and> valid_objs s \<and> pspace_aligned s)
             \<top>
             (return ()) (stateAssert (\<lambda>s. \<not> archOverlap s R) [])"
  by (simp add: archOverlap_def)

lemma word_size_bits_le_untyped_min_bits[Untyped_R_assms]:
  "word_size_bits \<le> untyped_min_bits"
  by (simp add: word_size_bits_def untyped_min_bits_def)

lemma minUntypedSizeBits_le_resetChunkBits[Untyped_R_assms]:
  "minUntypedSizeBits \<le> resetChunkBits"
  by (simp add: minUntypedSizeBits_def Kernel_Config.resetChunkBits_def)

lemma maxUntypedSizeBits_less_word_bits[Untyped_R_assms]:
  "maxUntypedSizeBits < word_bits"
  by (simp add: maxUntypedSizeBits_def word_bits_def)

(* FIXME arch-split: candidate for Kernel_Config lemmas *)
lemma word_size_bits_le_resetChunkBits[Untyped_R_assms]:
  "word_size_bits \<le> resetChunkBits"
  by (simp add: word_size_bits_def Kernel_Config.resetChunkBits_def)

lemma resetChunkBits_le_word_bits[Untyped_R_assms]:
  "resetChunkBits < word_bits"
  by (simp add: Kernel_Config.resetChunkBits_def word_bits_def)

lemma APIType_capBits_lower_bound[Untyped_R_assms]:
  "\<lbrakk>tp = APIObjectType ArchTypes_H.apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> us\<rbrakk>
   \<Longrightarrow> minUntypedSizeBits \<le> APIType_capBits tp us"
  by (simp add: APIType_capBits_def objBits_simps' bit_simps minUntypedSizeBits_def
           split: object_type.split apiobject_type.split)

lemma dmo_freeMemory_clear_um[Untyped_R_assms]:
  "\<lbrakk>word_size_bits \<le> sz; sz \<le> word_bits; is_aligned ptr sz\<rbrakk>
   \<Longrightarrow> (do_machine_op (freeMemory ptr sz) :: (det_state, unit) nondet_monad)
      = modify (clear_um {ptr..ptr + 2 ^ sz - 1})"
  apply (simp add: freeMemory_def)
  apply (subst mapM_storeWord_clear_um; simp?)
  apply (subst intvl_range_conv[symmetric, where 'a=machine_word_len, folded word_bits_def];
         simp)
  done

crunch createObject
  for nosch[Untyped_R_assms, wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and ksInterruptState[Untyped_R_assms, wp]: "\<lambda>s. P (ksInterruptState s)"

end (* Arch *)

interpretation Untyped_R?: Untyped_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Untyped_R_assms)?)?)
qed

locale Arch_mdb_insert_again_all = mdb_insert_again_all + Arch
begin

lemma valid_badges_n':
  "valid_badges n'"
  using valid_badges same_region parent
  apply (clarsimp simp: valid_badges_def valid_arch_badges_def)
  apply (simp add: n'_direct_eq)
  apply (drule n'_badged)+
  apply (clarsimp split: if_split_asm)
   apply (drule (1) no_next_region)
   apply simp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply simp
  done

end (* Arch_mdb_insert_again_all *)

context mdb_insert_again_all begin

(* extract arch-dependent assumptions of mdb_insert_again_all proved in Arch_mdb_insert_again_all
   (faster than interpreting Arch) *)
lemmas gen_assms =
  Arch_mdb_insert_again_all.valid_badges_n'[unfolded Arch_mdb_insert_again_all_def,
                                            OF mdb_insert_again_all_axioms]

sublocale mdb_insert_again_all_gen
  by (unfold_locales, fact gen_assms)

(* re-bind names *)
lemmas valid_badges_n' = valid_badges_n'
lemmas valid_n' = valid_n'

end (* mdb_insert_again_all *)

context invokeUntyped_proofs begin

(* use Untyped_R interpretation to instantiate invokeUntyped_proofs_gen *)
sublocale invokeUntyped_proofs_gen
  by (unfold_locales;
      fact cte_wp_at_caps_descendants_range_inI' descendants_range_ex_cte')

(* re-bind names *)
lemmas descendants_range = descendants_range
lemmas ex_cte_no_overlap' = ex_cte_no_overlap'
lemmas cref_inv = cref_inv
lemmas slots_invD = slots_invD

end (* invokeUntyped_proofs *)

context Arch begin arch_global_naming

named_theorems Untyped_R_2_assms

lemmas [Untyped_R_2_assms] =
  mdb_insert_again_all.valid_n'
  invokeUntyped_proofs.descendants_range
  invokeUntyped_proofs.ex_cte_no_overlap'
  invokeUntyped_proofs.cref_inv
  invokeUntyped_proofs.slots_invD

end (* Arch *)

interpretation Untyped_R_2?: Untyped_R_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Untyped_R_2_assms)?)?)
qed

end
