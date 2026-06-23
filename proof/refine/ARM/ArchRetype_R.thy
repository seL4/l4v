(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Retype refinement - architecture specific *)

theory ArchRetype_R
imports Retype_R
begin

context Arch begin arch_global_naming

named_theorems Retype_R_assms

lemma toAPIType_Some[Retype_R_assms, simp]:
  "(toAPIType ty = Some x) = (ty = APIObjectType x)"
  by (cases ty; auto simp: toAPIType_def)

definition APIType_map2 :: "kernel_object + ARM_H.object_type \<Rightarrow> Structures_A.apiobject_type"
  where
  APIType_map2_raw_def:
  "APIType_map2 ty \<equiv> case ty of
      Inr (APIObjectType api) \<Rightarrow> APIType_map2_gen api
    | Inr PageTableObject \<Rightarrow> ArchObject PageTableObj
    | Inr PageDirectoryObject \<Rightarrow> ArchObject PageDirectoryObj
    | Inr LargePageObject \<Rightarrow> ArchObject LargePageObj
    | Inr SectionObject \<Rightarrow> ArchObject SectionObj
    | Inr SuperSectionObject \<Rightarrow> ArchObject SuperSectionObj
    | Inl (KOArch (KOASIDPool _)) \<Rightarrow> ArchObject ASIDPoolObj
    | _ \<Rightarrow> ArchObject SmallPageObj"

(* inside of Arch, we don't need to isolate generic component *)
lemmas APIType_map2_def = APIType_map2_raw_def[simplified APIType_map2_gen_def]

lemma APIType_map2_Untyped[Retype_R_assms, simp]:
  "(APIType_map2 tp = Structures_A.Untyped) = (tp = Inr (APIObjectType ArchTypes_H.Untyped))"
  by (simp add: APIType_map2_def
         split: sum.split object_type.split kernel_object.split arch_kernel_object.splits
                apiobject_type.split)

lemma APIType_map2_TCBObject[Retype_R_assms, simp]:
  "(APIType_map2 tp = Structures_A.TCBObject) = (tp = Inr (APIObjectType ArchTypes_H.TCBObject))"
  by (simp add: APIType_map2_def
         split: sum.split object_type.split kernel_object.split arch_kernel_object.splits
                apiobject_type.split)

lemma APIType_map2_generic[Retype_R_assms, simp]:
  "APIType_map2 (Inr (APIObjectType api)) = APIType_map2_gen api"
  by (simp add: APIType_map2_raw_def)

definition APIType_capBits :: "ARM_H.object_type \<Rightarrow> nat \<Rightarrow> nat" where
  APIType_capBits_raw_def:
  "APIType_capBits ty us \<equiv> case ty of
      APIObjectType api \<Rightarrow> APIType_capBits_gen api us
    | SmallPageObject \<Rightarrow> pageBitsForSize ARMSmallPage
    | LargePageObject \<Rightarrow> pageBitsForSize ARMLargePage
    | SectionObject \<Rightarrow> pageBitsForSize ARMSection
    | SuperSectionObject \<Rightarrow> pageBitsForSize ARMSuperSection
    | PageTableObject \<Rightarrow> 10
    | PageDirectoryObject \<Rightarrow> 14"

(* inside of Arch, we don't need to isolate generic component *)
lemmas APIType_capBits_def = APIType_capBits_raw_def[simplified APIType_capBits_gen_def]

lemma APIType_capBits_generic[Retype_R_assms, simp]:
  "APIType_capBits (APIObjectType api) us = APIType_capBits_gen api us"
  by (simp add: APIType_capBits_raw_def)

definition makeObjectKO :: "bool \<Rightarrow> domain \<Rightarrow> (kernel_object + ARM_H.object_type) \<rightharpoonup> kernel_object"
  where
  makeObjectKO_raw_def:
  "makeObjectKO dev d ty \<equiv> case ty of
      Inl KOUserData \<Rightarrow> Some KOUserData
    | Inl (KOArch (KOASIDPool _)) \<Rightarrow> Some (KOArch (KOASIDPool makeObject))
    | Inr (APIObjectType api) \<Rightarrow> makeObjectKO_gen d api
    | Inr PageTableObject \<Rightarrow> Some (KOArch (KOPTE makeObject))
    | Inr PageDirectoryObject \<Rightarrow> Some (KOArch (KOPDE makeObject))
    | Inr SmallPageObject \<Rightarrow> Some (if dev then KOUserDataDevice else KOUserData)
    | Inr LargePageObject \<Rightarrow> Some(if dev then KOUserDataDevice else KOUserData)
    | Inr SectionObject \<Rightarrow> Some (if dev then KOUserDataDevice else KOUserData)
    | Inr SuperSectionObject \<Rightarrow> Some (if dev then KOUserDataDevice else KOUserData)
    | _ \<Rightarrow> None"

(* inside of Arch, we don't need to isolate generic component *)
lemmas makeObjectKO_def = makeObjectKO_raw_def[simplified makeObjectKO_gen_def]

lemma makeObjectKO_generic[Retype_R_assms, simp]:
  "makeObjectKO dev d (Inr (APIObjectType api)) = makeObjectKO_gen d api"
  by (simp add: makeObjectKO_raw_def)

text \<open>makeObject etc. lemmas\<close>

lemma valid_arch_tcb'_newArchTCB[Retype_R_assms, simp]:
  "valid_arch_tcb' newArchTCB s"
  unfolding valid_arch_tcb'_def newArchTCB_def
  by simp

lemma valid_obj_makeObject_pte[simp]:
  "valid_obj' (KOArch (KOPTE makeObject)) s"
  unfolding valid_obj'_def by (simp add: makeObject_pte)

lemma valid_obj_makeObject_pde[simp]:
  "valid_obj' (KOArch (KOPDE makeObject)) s"
  unfolding valid_obj'_def by (simp add: makeObject_pde)

lemma valid_obj_makeObject_asid_pool[simp]:
  "valid_obj' (KOArch (KOASIDPool makeObject)) s"
  unfolding valid_obj'_def
  by (simp add: makeObject_asidpool Let_def ran_def dom_def)

text \<open>On the abstract side\<close>

text \<open>Lemmas for createNewObjects etc.\<close>

lemma makeObjectKO_eq[Retype_R_assms]:
  assumes x: "makeObjectKO dev d tp = Some v"
  shows
  "(v = KOCTE cte) =
       (tp = Inr (APIObjectType ArchTypes_H.CapTableObject) \<and> cte = makeObject)"
  "(v = KOTCB tcb) =
       (tp = Inr (APIObjectType ArchTypes_H.TCBObject) \<and> tcb = (tcbDomain_update (\<lambda>_. d) makeObject))"
  using x
  by (simp add: makeObjectKO_def eq_commute
         split: apiobject_type.split_asm sum.split_asm kernel_object.split_asm
                ARM_H.object_type.split_asm arch_kernel_object.split_asm)+

lemma objBits_le_obj_bits_api[Retype_R_assms]:
  "makeObjectKO dev d ty = Some ko \<Longrightarrow> objBitsKO ko \<le> obj_bits_api (APIType_map2 ty) us"
  apply (case_tac ty)
    apply (auto simp: default_arch_object_def vspace_bits_defs
                      makeObjectKO_def objBits_simps' APIType_map2_def obj_bits_api_def slot_bits_def
               split: Structures_H.kernel_object.splits arch_kernel_object.splits object_type.splits
                      Structures_H.kernel_object.splits arch_kernel_object.splits apiobject_type.splits)
  done

lemma obj_relation_retype_other_obj[Retype_R_assms]:
  "\<lbrakk> is_other_obj_relation_type (a_type ko); other_obj_relation ko ko' \<rbrakk>
   \<Longrightarrow> obj_relation_retype ko ko'"
  apply (simp add: obj_relation_retype_def)
  apply (subgoal_tac "objBitsKO ko' = obj_bits ko")
   apply (clarsimp simp: is_other_obj_relation_type other_obj_relation_not_aobj)
  apply (fastforce simp: other_obj_relation_def objBits_simps'
                  split: Structures_A.kernel_object.split_asm
                         Structures_H.kernel_object.split_asm
                         Structures_H.kernel_object.split
                         arch_kernel_obj.split_asm arch_kernel_object.split)
  done

definition update_gs :: "Structures_A.apiobject_type \<Rightarrow> nat \<Rightarrow> machine_word set
                         \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
  where
  "update_gs ty us ptrs \<equiv> case ty of
       Structures_A.CapTableObject \<Rightarrow> gsCNodes_update
         (\<lambda>cns x. if x \<in> ptrs then Some us else cns x)
     | ArchObject SmallPageObj \<Rightarrow> gsUserPages_update
         (\<lambda>ups x. if x \<in> ptrs then Some ARMSmallPage else ups x)
     | ArchObject LargePageObj \<Rightarrow> gsUserPages_update
         (\<lambda>ups x. if x \<in> ptrs then Some ARMLargePage else ups x)
     | ArchObject SectionObj \<Rightarrow> gsUserPages_update
         (\<lambda>ups x. if x \<in> ptrs then Some ARMSection else ups x)
     | ArchObject SuperSectionObj \<Rightarrow> gsUserPages_update
         (\<lambda>ups x. if x \<in> ptrs then Some ARMSuperSection else ups x)
     | _ \<Rightarrow> id"

lemma ksPSpace_update_gs_eq[Retype_R_assms, simp]:
  "ksPSpace (update_gs ty us ptrs s) = ksPSpace s"
  by (simp add: update_gs_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)

lemma ksMachineState_update_gs[simp]:
  "ksMachineState (update_gs tp us addrs s) = ksMachineState s"
  by (simp add: update_gs_def
         split: aobject_type.splits Structures_A.apiobject_type.splits)

lemma ksReadyQueues_update_gs[simp]:
  "ksReadyQueues (update_gs tp us addrs s) = ksReadyQueues s"
  by (simp add: update_gs_def
         split: aobject_type.splits Structures_A.apiobject_type.splits)

lemma update_gs_ksMachineState_update_swap:
  "update_gs tp us addrs (ksMachineState_update f s) =
   ksMachineState_update f (update_gs tp us addrs s)"
  by (simp add: update_gs_def
         split: aobject_type.splits Structures_A.apiobject_type.splits)

lemma update_gs_id[Retype_R_assms]:
  "tp \<in> no_gs_types \<Longrightarrow> update_gs tp us addrs = id"
  by (simp add: no_gs_types_def update_gs_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)

lemma no_gs_types_CapTableObject[Retype_R_assms]:
  "Structures_A.apiobject_type.CapTableObject \<notin> no_gs_types"
  by (simp add: no_gs_types_def)

lemma update_gs_simps[simp]:
  "update_gs Structures_A.apiobject_type.CapTableObject us ptrs =
   gsCNodes_update (\<lambda>cns x. if x \<in> ptrs then Some us else cns x)"
  "update_gs (ArchObject SmallPageObj) us ptrs =
   gsUserPages_update (\<lambda>ups x. if x \<in> ptrs then Some ARMSmallPage else ups x)"
  "update_gs (ArchObject LargePageObj) us ptrs =
   gsUserPages_update (\<lambda>ups x. if x \<in> ptrs then Some ARMLargePage else ups x)"
  "update_gs (ArchObject SectionObj) us ptrs =
   gsUserPages_update (\<lambda>ups x. if x \<in> ptrs then Some ARMSection else ups x)"
  "update_gs (ArchObject SuperSectionObj) us ptrs =
   gsUserPages_update (\<lambda>ups x. if x \<in> ptrs then Some ARMSuperSection else ups x)"
  by (simp_all add: update_gs_def)

lemma objBitsKO_gt_0[Retype_R_assms]:
  "0 < objBitsKO ko"
  apply (case_tac ko)
         apply (simp_all add: objBits_simps' pageBits_def)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object)
    apply (simp_all add: objBits_simps' vspace_bits_defs)
  done

lemma cwo_ret:
  assumes not_0: "n\<noteq> 0"
  assumes cover: "range_cover ptr sz v n"
  shows "\<lbrace>pspace_no_overlap' ptr sz and valid_pspace' and K (v = 12 + bs)\<rbrace>
         createObjects ptr n (if dev then KOUserDataDevice else KOUserData) bs
         \<lbrace>\<lambda>rv s. \<forall>x\<in>set rv. \<forall>p<2 ^ (v - pageBits).
                   typ_at' (if dev then UserDataDeviceT else UserDataT) (x + p * 2 ^ pageBits) s\<rbrace>"
proof -
  note create_objs_device = hoare_post_imp [OF _ hoare_conj [OF createObjects_ret
     createObjects_ko_at[where val = UserDataDevice,simplified]]]

  note create_objs_normal = hoare_post_imp [OF _ hoare_conj [OF createObjects_ret
     createObjects_ko_at[where val = UserData,simplified]]]

show ?thesis
  apply (cases dev)
   apply (rule hoare_gen_asm)
   apply (rule hoare_pre)
   apply (rule create_objs_device)
         apply (clarsimp simp add: pageBits_def)
         apply (drule bspec, simp, drule spec, drule(1) mp)
         apply (simp add: typ_at'_def obj_at'_real_def objBits_simps pageBits_def shiftl_t2n field_simps)
         apply (erule ko_wp_at'_weakenE)
         apply (clarsimp simp add: projectKO_opts_defs split: kernel_object.splits)
        apply (rule le_less_trans[OF _ power_strict_increasing])
          apply (rule range_cover.range_cover_n_le(1)[OF cover])
         apply (simp add: word_bits_def pageBits_def not_0)+
     apply (rule range_cover_rel[OF cover])
      apply (simp add: objBitsKO_def pageBits_def not_0)+
     using not_0 apply simp_all
  apply (rule hoare_gen_asm[unfolded K_def])
  apply (rule hoare_pre)
  apply (rule create_objs_normal)
         apply (clarsimp simp add: pageBits_def)
         apply (drule bspec, simp, drule spec, drule(1) mp)
         apply (simp add: typ_at'_def obj_at'_real_def objBits_simps pageBits_def shiftl_t2n field_simps)
         apply (erule ko_wp_at'_weakenE)
         apply (clarsimp simp add: projectKO_opts_defs split: kernel_object.splits)
        apply (rule le_less_trans[OF _ power_strict_increasing])
          apply (rule range_cover.range_cover_n_le(1)[OF cover])
         apply (simp add: word_bits_def pageBits_def not_0)+
     apply (rule range_cover_rel[OF cover])
      apply (simp add: objBitsKO_def pageBits_def not_0)+
  done
qed

lemma range_cover_canonical_address':
  "\<lbrakk> range_cover ptr sz us n; p < of_nat n;
     canonical_address (ptr && ~~ mask sz); sz \<le> maxUntypedSizeBits \<rbrakk>
   \<Longrightarrow> canonical_address (ptr + p * 2 ^ us)"
  apply (frule range_cover_canonical_address[where p="unat p"]; simp?)
  using unat_less_helper by blast

lemma createNewCaps_valid_cap:
  fixes ptr :: machine_word
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n "
  assumes not_0: "n \<noteq> 0"
  assumes ct: "ty = APIObjectType ArchTypes_H.CapTableObject \<Longrightarrow> 0 < us"
              "ty = APIObjectType apiobject_type.Untyped \<Longrightarrow> minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits"
  assumes ptr: " ptr \<noteq> 0"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s\<rbrace>
           createNewCaps ty ptr n us dev
         \<lbrace>\<lambda>r s. (\<forall>cap \<in> set r. s \<turnstile>' cap)\<rbrace>"
proof -
  note [simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
                    atLeastatMost_subset_iff atLeastLessThan_iff Int_atLeastAtMost
                    atLeastatMost_empty_iff split_paired_Ex
  note if_split[split del]

  show ?thesis
  proof(cases "Types_H.toAPIType ty")
    case None thus ?thesis
      using not_0
      apply (clarsimp simp: createNewCaps_def Arch_createNewCaps_def)
      using cover
      apply (simp add: range_cover_def)
      using cover
      apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def
                     split: ARM_H.object_type.splits)
       \<comment> \<open>SmallPageObject\<close>
       apply (wp mapM_x_wp' hoare_vcg_op_lift)
       apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                        ball_conj_distrib)
       apply ((wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
                 cwo_ret[OF not_0]
         | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+)
       apply (simp add:pageBits_def ptr word_bits_def)
      \<comment> \<open>LargePageObject\<close>
      apply (wp mapM_x_wp' hoare_vcg_op_lift)
      apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                       ball_conj_distrib)
      apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
                cwo_ret[OF not_0]
        | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+
      apply (simp add:pageBits_def ptr word_bits_def)

     \<comment> \<open>SectionObject\<close>
     apply (wp mapM_x_wp' hoare_vcg_op_lift)
     apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                      ball_conj_distrib)
     apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
               cwo_ret[OF not_0]
       | simp add: objBits_if_dev vspace_bits_defs ptr range_cover_n_wb)+
     apply (simp add: pageBits_def ptr word_bits_def)

    \<comment> \<open>SuperSectionObject\<close>
    apply (wp mapM_x_wp' hoare_vcg_op_lift)
    apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                     ball_conj_distrib)
    apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
              cwo_ret[OF not_0]
      | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+
    apply (simp add:pageBits_def ptr word_bits_def)

   \<comment> \<open>PageTableObject\<close>
    apply (wp mapM_x_wp' hoare_vcg_op_lift)
     apply (simp add: valid_cap'_def capAligned_def n_less_word_bits)
     apply (simp only: imp_conv_disj page_table_at'_def
                       typ_at_to_obj_at_arches)
     apply (rule hoare_chain)
       apply (rule hoare_vcg_conj_lift)
        apply (rule createObjects_aligned [OF _ range_cover.range_cover_n_less(1)
            [where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
        apply (simp add:objBits_simps vspace_bits_defs mask_def)+
       apply (simp add:range_cover_def word_bits_def)
       apply (rule createObjects_obj_at[where 'a =pte, OF _  not_0])
         apply (simp add:objBits_simps vspace_bits_defs)+
  \<comment> \<open>PageDirectoryObject\<close>
   apply (wp mapM_x_wp' hoare_vcg_op_lift)
   apply (simp add: valid_cap'_def capAligned_def n_less_word_bits)
   apply (simp only: imp_conv_disj page_directory_at'_def
                     typ_at_to_obj_at_arches)
   apply (rule hoare_chain)
     apply (rule hoare_vcg_conj_lift)
      apply (rule createObjects_aligned [OF _ range_cover.range_cover_n_less(1)
          [where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
       apply (simp add:objBits_simps vspace_bits_defs)+
      apply (simp add:range_cover_def word_bits_def)
     apply (rule createObjects_obj_at [where 'a=pde, OF _  not_0])
      apply (simp add:objBits_simps vspace_bits_defs)
     apply simp
    apply simp
   apply (clarsimp simp: objBits_simps vspace_bits_defs)
  apply simp
  done
  next
    case (Some a) thus ?thesis
    proof(cases a)
      case Untyped with Some cover ct show ?thesis
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def fromIntegral_def
                             toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_H.object_type.splits)
        apply wp
        apply (intro ballI)
        apply (clarsimp simp: image_def upto_enum_red' valid_cap'_def capAligned_def
                              canonical_address_def APIType_capBits_gen_def
                       split: capability.splits)
        apply (drule word_leq_minus_one_le[rotated])
       apply (rule range_cover_not_zero[OF not_0 cover])
      apply (intro conjI)
         apply (rule is_aligned_add_multI[OF _ le_refl refl])
         apply (fastforce simp:range_cover_def word_bits_def)+
       apply (clarsimp simp:valid_untyped'_def ko_wp_at'_def obj_range'_def)
       apply (drule(1) pspace_no_overlapD'[rotated])
       apply (frule(1) range_cover_cell_subset)
       apply (erule disjE)
        apply (simp add: mask_def add_diff_eq)
        apply (drule psubset_imp_subset)
        apply (drule(1) disjoint_subset2[rotated])
        apply (drule(1) disjoint_subset)
        apply (drule(1) range_cover_subset_not_empty)
        apply clarsimp+
       apply (simp add: mask_def add_diff_eq)
       apply blast
      apply (drule(1) range_cover_no_0[OF ptr _ unat_less_helper])
      apply simp
      done
    next
      case TCBObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def curDomain_def
                      split: ARM_H.object_type.splits)
        apply (wp mapM_x_wp' hoare_vcg_const_Ball_lift)+
         apply (rule hoare_post_imp)
          prefer 2
          apply (rule createObjects_obj_at [where 'a = "tcb",OF _ not_0])
           using cover
           apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def objBits_simps
                          split: ARM_H.object_type.splits)
           apply simp+
         apply (clarsimp simp: valid_cap'_def objBits_simps)
         apply (fastforce intro: capAligned_tcbI)
        apply wp
        done
    next
      case EndpointObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_H.object_type.splits)
        apply wp
        apply (rule hoare_post_imp)
         prefer 2
         apply (rule createObjects_obj_at [where 'a=endpoint, OF _ not_0])
          using cover
          apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def objBits_simps
                         split: ARM_H.object_type.splits)
         apply simp
        apply (clarsimp simp: valid_cap'_def objBits_simps)
        apply (fastforce intro: capAligned_epI)
        done
    next
      case NotificationObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_H.object_type.splits)
        apply wp
        apply (rule hoare_post_imp)
         prefer 2
         apply (rule createObjects_obj_at [where 'a="notification", OF _ not_0])
          using cover
          apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def objBits_simps
                         split: ARM_H.object_type.splits)
         apply simp
        apply (clarsimp simp: valid_cap'_def objBits_simps)
        apply (fastforce intro: capAligned_ntfnI)
        done
    next
      case CapTableObject with Some cover ct show ?thesis
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_gen_def
                      split: ARM_H.object_type.splits)
        apply wp
         apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def objBits_simps
                        split: ARM_H.object_type.split object_type.splits)
         apply (rule hoare_strengthen_post)
           apply (rule hoare_vcg_conj_lift)
           apply (rule createObjects_aligned [OF _ _ not_0 ])
              apply ((clarsimp simp:objBits_simps range_cover_def range_cover.range_cover_n_less[where 'a=32, unfolded word_bits_len_of, OF cover])+)[3]
            apply (simp add: word_bits_def)
           apply (rule hoare_vcg_conj_lift)
            apply (rule createObjects_ret [OF range_cover.range_cover_n_less(1)[where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
           apply (rule createObjects_obj_at [where 'a=cte, OF _ not_0])
            apply (simp add: objBits_simps APIType_capBits_def)
           apply simp
          apply simp
         apply (clarsimp simp: valid_cap'_def capAligned_def objBits_simps
                        dest!: less_two_pow_divD)
         apply (thin_tac "\<forall>x\<in>S. is_aligned (p x) n" for S p n)
         apply (intro conjI)
           apply ((simp add:range_cover_def word_bits_def)+)[2]
         apply (clarsimp simp: power_sub)
         apply (drule bspec, simp)
         apply (drule_tac x = "addr && mask us" in spec)
         apply (drule mp)
          apply simp
          apply (rule and_mask_less')
          apply (simp add: range_cover_def word_bits_def)
         apply (clarsimp simp add: shiftl_t2n)
        apply simp
        done
    qed
  qed
qed

lemma arch_tcb_relation_default[Retype_R_assms]:
  "arch_tcb_relation default_arch_tcb newArchTCB"
  by (clarsimp simp: new_context_def newContext_def initContext_def
                     default_arch_tcb_def newArchTCB_def arch_tcb_relation_def)

lemma pagetable_relation_retype:
  "obj_relation_retype (default_object (ArchObject PageTableObj) dev n d)
                       (KOArch (KOPTE makeObject))"
  apply (simp add: default_object_def default_arch_object_def makeObject_pte obj_relation_retype_def
                   objBits_simps pte_relation_def)
  apply (clarsimp simp: range_composition[symmetric] shiftl_t2n field_simps)
  apply (subst image_comp [symmetric, where g=ucast, unfolded o_def])
  apply (simp add: ucast_range_less vspace_bits_defs)
  apply (fastforce simp:pte_relation_aligned_def)
  done

lemma pagedirectory_relation_retype:
  "obj_relation_retype (default_object (ArchObject PageDirectoryObj) dev n d)
                       (KOArch (KOPDE makeObject))"
  apply (simp add: default_object_def default_arch_object_def
                   makeObject_pde obj_relation_retype_def objBits_simps pde_relation_def)
  apply (clarsimp simp: range_composition[symmetric]
                        shiftl_t2n field_simps)
  apply (subst image_comp [symmetric, where g=ucast, unfolded o_def])
  apply (simp add: ucast_range_less vspace_bits_defs)
  apply (fastforce simp:pde_relation_aligned_def)
  done

lemmas makeObjectKO_simps =
  makeObjectKO_def[split_simps ARM_H.object_type.split apiobject_type.split sum.split
                               kernel_object.split ]

lemma init_arch_objects_APIType_map2:
  "init_arch_objects (APIType_map2 (Inr ty)) dev ptr bits sz refs =
     (case ty of APIObjectType _ \<Rightarrow> return ()
   | _ \<Rightarrow> init_arch_objects (APIType_map2 (Inr ty)) dev ptr bits sz refs)"
  apply (clarsimp split: ARM_H.object_type.split)
  apply (simp add: init_arch_objects_def APIType_map2_gen_def
            split: apiobject_type.split)
  done

lemma getObject_valid_pde'[wp]:
  "\<lbrace>valid_objs'\<rbrace> getObject x \<lbrace>\<lambda>rv _. valid_pde' rv\<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule getObject_ko_at, simp)
     apply (simp add: objBits_simps pdeBits_def)
    apply (rule getObject_inv[where P=valid_objs'])
    apply (simp add: loadObject_default_inv)
   apply simp
  apply (clarsimp simp: valid_obj'_def dest!: obj_at_valid_objs')
  done

lemma pde_relation_aligned_eq:
  "\<lbrakk>is_aligned (pd::word32) 6; is_aligned pd' 6\<rbrakk>
   \<Longrightarrow> pde_relation_aligned (pd + x >> 2) xa ya =
       pde_relation_aligned (pd' + x >> 2) xa ya"
  apply (clarsimp simp: pde_relation_aligned_def is_aligned_mask mask_def
                 split: ARM_H.pde.splits)
  apply word_bitwise
  apply auto
  done

lemma copyGlobalMappings_corres:
  "corres dc (valid_arch_state and pspace_aligned and page_directory_at pd)
             (valid_arch_state' and page_directory_at' pd)
          (copy_global_mappings pd)
          (copyGlobalMappings pd)"
  apply (simp add: copy_global_mappings_def
                   copyGlobalMappings_def
                   objBits_simps pd_bits_def pdBits_def mapM_x_mapM)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_trivial, clarsimp simp: state_relation_def arch_state_relation_def)
      apply (rule_tac F ="is_aligned pd 6 \<and> is_aligned global_pd 6" in corres_gen_asm)
      apply (simp add: liftM_def[symmetric])
      apply (rule_tac S="(=)" and r'=dc
                  and Q="\<lambda>xs s. \<forall>x \<in> set xs. pde_at (global_pd + (x << 2)) s
                                             \<and> pde_at (pd + (x << 2)) s \<and> pspace_aligned s"
                  and Q'="\<lambda>xs s. \<forall>x \<in> set xs. pde_at' (global_pd + (x << 2)) s
                                             \<and> pde_at' (pd + (x << 2)) s"
                         in corres_mapM_list_all2, (simp add: pdeBits_def)+)
         apply (rule corres_guard_imp, rule corres_split)
              apply (rule_tac getObject_PDE_corres[OF refl])
             apply (rule storePDE_corres[OF _ refl])
             apply clarsimp
             apply (drule(1) pde_relation_aligned_eq)
             apply fastforce
            apply (wp hoare_vcg_const_Ball_lift | simp)+
      apply (clarsimp simp add: kernel_base_def list_all2_refl pageBits_def)
     apply wp+
   apply (clarsimp simp: valid_arch_state_def)
   apply (auto elim: page_directory_pde_atI is_aligned_weaken[OF pd_aligned])[1]
  apply (clarsimp simp: valid_arch_state'_def)
  apply (auto simp: le_less_trans elim!: page_directory_pde_atI'[simplified pageBits_def, simplified])
  done

(* FIXME: move *)
lemma copyGlobalMappings_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     copyGlobalMappings pd
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  by (simp add: copyGlobalMappings_def)
     (wp mapM_x_wp')

crunch copyGlobalMappings
  for ct[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv mapM_x_wp')

lemmas copyGlobalMappings_ctes_of[wp]
    = ctes_of_from_cte_wp_at[where Q="\<top>", simplified,
                             OF copyGlobalMappings_cte_wp_at]

lemmas object_splits =
  gen_object_splits
  ARM_H.object_type.split_asm
  arch_kernel_object.split_asm

lemma valid_arch_badges_not_arch:
  "\<not>isArchObjectCap cap' \<Longrightarrow> valid_arch_badges cap cap' node"
  by (auto simp: isCap_simps valid_arch_badges_def)

lemma valid_arch_badges_NullCap[simp]:
  "valid_arch_badges cap NullCap node"
  by (simp add: valid_arch_badges_not_arch gen_isCap_simps)

lemma valid_untyped'_helper_arch_cap[Retype_R_assms]:
  "\<lbrakk>pspace_aligned' s; pspace_distinct' s; pspace_no_overlap' ptr sz s;
    range_cover ptr sz (objBitsKO val) n; valid_arch_cap' acap s \<rbrakk>
   \<Longrightarrow> valid_arch_cap' acap
        (s\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr val) (new_cap_addrs n ptr val) (ksPSpace s)\<rparr>)"
  by (clarsimp simp: valid_arch_cap'_def retype_obj_at_disj'
                     typ_at_to_obj_at_arches page_directory_at'_def page_table_at'_def
               split: if_split_asm arch_capability.splits)

lemma retype_in_kernel_mappings'[Retype_R_assms]:
  assumes pc': "pspace_in_kernel_mappings' s'"
      and cover: "range_cover ptr sz (objBitsKO ko) n"
      and sz_limit: "sz \<le> maxUntypedSizeBits"
      and ptr_cn: "(ptr && ~~ mask sz) \<in> kernel_mappings"
  shows
  "pspace_in_kernel_mappings' (s' \<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko)
                                             (new_cap_addrs n ptr ko) (ksPSpace s')\<rparr>)"
  (is "pspace_in_kernel_mappings' (s'\<lparr>ksPSpace := ?ps\<rparr>)")
  by simp

crunch copyGlobalMappings
  for valid_objs'[wp]: "valid_objs'"
  and pspace_aligned'[wp]: "pspace_aligned'"
  and pspace_canonical'[wp]: "pspace_canonical'"
  and pspace_distinct'[wp]: "pspace_distinct'"
  and no_0_obj'[wp]: no_0_obj'
  and valid_mdb[wp]: "valid_mdb'"
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and state_hyp_refs_of'[wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  and ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksReadyQueuesL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksReadyQueuesL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and valid_idle'[wp]: "valid_idle'"
  and iflive'[wp]: "if_live_then_nonz_cap'"
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  and valid_bitmaps[wp]: valid_bitmaps
  and sched_pointers[wp]: "\<lambda>s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"
  and valid_sched_pointers[wp]: valid_sched_pointers
  (ignore: storePDE wp: crunch_wps valid_bitmaps_lift)

lemmas storePDE_valid_mdb[wp]
    = storePDE_ctes[where P=valid_mdb_ctes, folded valid_mdb'_def]

lemma copyGlobalMappings_valid_pspace[wp]:
  "\<lbrace>valid_pspace'\<rbrace> copyGlobalMappings pd \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  by (simp add: valid_pspace'_def | wp)+

lemma createNewCaps_cte_wp_at2[Retype_R_assms]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s) \<and> \<not> P' makeObject
      \<and> n \<noteq> 0
      \<and> range_cover ptr sz (APIType_capBits ty objsz) n
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
     createNewCaps ty ptr n objsz dev
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  unfolding createNewCaps_def Arch_createNewCaps_def createObjects_def ARM_H.toAPIType_def
  apply (case_tac ty; simp split del: if_split cong: if_cong)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (wpsimp wp: createObjects_orig_cte_wp_at2'[where sz = sz] mapM_x_wp'
                          split_del: if_split
                          simp: curDomain_def APIType_capBits_def APIType_capBits_gen_def
                   | simp add: projectKO_opts_defs makeObject_tcb tcb_cte_cases_def Let_def
                               objBits_if_dev objBits_simps' vspace_bits_defs
                          split del: if_split
                   | simp)+
  done

lemma copyGlobalMappings_ko_wp_at:
  "\<lbrace>(\<lambda>s. P (ko_wp_at' P' p s)) and K (createNewCaps_arch_ko_pre P')\<rbrace>
   copyGlobalMappings pd
   \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p s)\<rbrace>"
proof (rule hoare_gen_asm)
  assume a: "createNewCaps_arch_ko_pre P'"

  note non_specific_pde =
    createNewCaps_arch_ko_pre_def[simplified atomize_eq, THEN iffD1, OF a, rule_format]

  show
    "copyGlobalMappings pd \<lbrace>\<lambda>s. P (ko_wp_at' P' p s)\<rbrace>"
   apply (simp add: copyGlobalMappings_def storePDE_def)
    apply (wp mapM_x_wp' setObject_ko_wp_at)
         apply (simp add: objBits_simps pdeBits_def cong: if_cong split del: if_split)+
      apply (subst non_specific_pde)
      apply (wpsimp wp: getObject_inv loadObject_default_inv hoare_vcg_imp_lift split_del: if_split)
      apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
      apply (subst (asm) non_specific_pde, fastforce)
     apply wpsimp+
    done
qed

lemma createNewCaps_cte_wp_at'[Retype_R_assms]:
  "\<lbrace>\<lambda>s. cte_wp_at' P p s
      \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  supply APIType_capBits_generic[simp del]
  apply (simp add: createNewCaps_def ARM_H.toAPIType_def
              split del: if_split)
  apply (case_tac ty; simp add: Arch_createNewCaps_def
                           split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (wp createObjects_orig_cte_wp_at'[where sz = sz] mapM_x_wp'
                     threadSet_cte_wp_at'T
                  | clarsimp simp: objBits_simps field_simps mult_2_right APIType_capBits_def
                                   createObjects_def curDomain_def vspace_bits_defs
                  | intro conjI impI
                  | force simp: tcb_cte_cases_def cteSizeBits_def)+
  done

(* example of arch-split attempt of this kind of proof; unfortunately splitting off the
   arch-specific part doesn't actually save space, so we will leave these in Arch *)
lemma createNewCaps_state_refs_of'[Retype_R_assms]:
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  and     not_0: "n \<noteq> 0"
  shows
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s \<and> P (state_refs_of' s)\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  unfolding createNewCaps_def
  supply if_split[split del]
  using cover
  apply (clarsimp split: option.splits)
  apply (rule conjI; clarsimp split: option.splits)
   (* Arch *)
   apply (simp add: APIType_capBits_def toAPIType_def Arch_createNewCaps_def
               split: object_type.splits apiobject_type.splits)
        apply ((wpsimp wp: mapM_x_wp' createObjects_state_refs_of'' simp: createObjects_def,
               force simp: not_0 zero_less_iff_neq_zero refs_of'_def valid_pspace'_def
                               objBits_simps mult_2_right field_simps vspace_bits_defs
                     split: if_split)+)[6]
  (* generic *)
  using cover
  apply (clarsimp)
  apply (wpsimp simp: createObjects_def curDomain_def wp: createObjects_state_refs_of'')
  apply (clarsimp simp: not_0 zero_less_iff_neq_zero APIType_capBits_gen_def
                        makeObject_notification makeObject_tcb makeObject_endpoint)
  apply (force simp: gen_objBits_simps split: ArchTypes_H.apiobject_type.splits)
  done

lemma createNewCaps_state_hyp_refs_of'[Retype_R_assms]:
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  and     not_0: "n \<noteq> 0"
  shows
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s
        \<and> P (state_hyp_refs_of' s)\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: ARM_H.toAPIType_def
             split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (insert cover not_0)
           apply (wp mapM_x_wp' createObjects_state_hyp_refs_of'' threadSet_state_hyp_refs_of'
                  | simp add: not_0 pspace_no_overlap'_def objBitsKO_def APIType_capBits_def
                              valid_pspace'_def makeObject_tcb objBits_def
                              newArchTCB_def field_simps
                              archObjSize_def createObjects_def curDomain_def mult_2_right
                              vspace_bits_defs
                  | intro conjI impI)+
  done

lemma arch_live'_KOPTE[simp]:
  "arch_live' (KOPTE makeObject) = False"
  by (simp add: makeObject_pte arch_live'_def)

lemma createNewCaps_iflive'[Retype_R_assms, wp]:
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  and     not_0: "n \<noteq> 0"
  shows
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s
        \<and> if_live_then_nonz_cap' s\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  unfolding createNewCaps_def
  apply (insert cover)
  apply (clarsimp simp: toAPIType_def)
  apply (cases ty, simp_all add: createNewCaps_def Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)[1]
            apply (rule hoare_pre, wp, simp)
           apply (wp mapM_x_wp' createObjects_iflive' threadSet_iflive'
                | simp add: not_0 pspace_no_overlap'_def createObjects_def live'_def hyp_live'_def
                            valid_pspace'_def makeObject_tcb makeObject_endpoint
                            makeObject_notification objBitsKO_def newArchTCB_def arch_live'_def
                            APIType_capBits_def objBits_def
                            archObjSize_def vspace_bits_defs APIType_capBits_gen_def
                            curDomain_def
                       split del: if_split
                | simp split: if_split
                | fastforce)+
  done

crunch createNewCaps
  for qs[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and qsL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and qsL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and ct[Retype_R_assms, wp]: "\<lambda>s. P (ksCurThread s)"
  and ksCurDomain[Retype_R_assms, wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksInterrupt[Retype_R_assms, wp]: "\<lambda>s. P (ksInterruptState s)"
  and nosch[Retype_R_assms, wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and it[Retype_R_assms, wp]: "\<lambda>s. P (ksIdleThread s)"
  and asid_table[wp]: "\<lambda>s. P (armKSASIDTable (ksArchState s))"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and irq_states'[Retype_R_assms, wp]: valid_irq_states'
  and ksDomSchedule[Retype_R_assms, wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[Retype_R_assms, wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksDomScheduleStart[Retype_R_assms, wp]: "\<lambda>s. P (ksDomScheduleStart s)"
  and gsUntypedZeroRanges[Retype_R_assms, wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and ksArch[wp]: "\<lambda>s. P (ksArchState s)"
  (simp: crunch_simps unless_def
   wp: mapM_x_wp' setObject_ksInterrupt updateObject_default_inv crunch_wps
       no_irq no_irq_clearMemory)

lemma createNewCaps_arch_ko_type_pre_non_arch[Retype_R_assms]:
  "(case ty of ArchT _ \<Rightarrow> False | _ \<Rightarrow> True) \<Longrightarrow> createNewCaps_arch_ko_type_pre ty"
  by (clarsimp simp add: createNewCaps_arch_ko_type_pre_def)

lemma createNewCaps_ko_wp_atQ'[Retype_R_assms]:
  "\<lbrace>(\<lambda>s. P (ko_wp_at' P' p s)
       \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s)
       and K (createNewCaps_arch_ko_pre P')
       and K (\<forall>d (tcb_x :: tcb). \<not>tcbQueued tcb_x \<and> tcbState tcb_x = Inactive
                   \<longrightarrow> P' (injectKO (tcb_x \<lparr> tcbDomain := d \<rparr>)) = P' (injectKO tcb_x))
       and (\<lambda>s. \<forall>v. makeObjectKO dev (ksCurDomain s) (Inr ty) = Some v \<longrightarrow> P' v \<longrightarrow> P True)\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>_ s. P (ko_wp_at' P' p s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: createNewCaps_def ARM_H.toAPIType_def
             split del: if_split)
  apply (cases ty, simp_all add: Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)[1]
            apply (wp mapM_x_threadSet_createNewCaps_futz mapM_x_wp' createObjects_obj_at
                      createObjects_ko_wp_at2 createObjects_makeObject_not_tcbQueued
                      copyGlobalMappings_ko_wp_at
                   | simp add: makeObjectKO_def objBitsKO_def archObjSize_def makeObjectKO_gen_def
                               APIType_capBits_def APIType_capBits_gen_def vspace_bits_defs
                               objBits_def curDomain_def field_simps mult_2_right
                          split del: if_split
                   | intro conjI impI | fastforce
                   | split if_split_asm)+
  done

lemma createNewCaps_global_refs'[Retype_R_assms]:
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s \<and> valid_global_refs' s
       \<and> 0 < gsMaxObjectSize s\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_cap_sizes'_def valid_refs'_def)
  apply (rule_tac Q'="\<lambda>rv s. \<forall>ptr. \<not> cte_wp_at' (\<lambda>cte. (kernel_data_refs \<inter> capRange (cteCap cte) \<noteq> {}
        \<or> 2 ^ capBits (cteCap cte) > gsMaxObjectSize s)) ptr s \<and> global_refs' s \<subseteq> kernel_data_refs"
                 in hoare_post_imp)
   apply (auto simp: cte_wp_at_ctes_of linorder_not_less elim!: ranE)[1]
  apply (rule hoare_pre)
   apply (simp add: global_refs'_def)
   apply (rule hoare_use_eq [where f=ksArchState, OF createNewCaps_ksArch])
   apply (rule hoare_use_eq [where f=ksIdleThread, OF createNewCaps_it])
   apply (rule hoare_use_eq [where f=irq_node', OF createNewCaps_ksInterrupt])
   apply (rule hoare_use_eq [where f=gsMaxObjectSize], wp)
   apply (wp hoare_vcg_all_lift createNewCaps_cte_wp_at2[where sz=sz])
  apply (clarsimp simp: cte_wp_at_ctes_of global_refs'_def makeObject_cte)
  apply (auto simp: linorder_not_less ball_ran_eq)
  done

lemma copyGlobalMappings_ksMachineState[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace>
    copyGlobalMappings newPM
   \<lbrace>\<lambda>_ s. P (ksMachineState s)\<rbrace>"
  by (simp add: copyGlobalMappings_def storePDE_def split_def
      | wp mapM_x_wp_inv setObject_ksMachine updateObject_default_inv)+

lemma createNewCaps_valid_bitmaps[Retype_R_assms]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s \<and> valid_bitmaps s\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>_. valid_bitmaps\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: toAPIType_def
             split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (wpsimp wp: createObjects_valid_bitmaps[simplified o_def] mapM_x_wp
                   | simp add: makeObject_tcb objBits_def createObjects_def
                   | intro conjI impI)+
  done

lemma createNewCaps_valid_sched_pointers[Retype_R_assms]:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s \<and> valid_sched_pointers s\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: toAPIType_def split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (wpsimp wp: createObjects_valid_sched_pointers[simplified o_def] mapM_x_wp
                   | simp add: makeObject_tcb objBits_def createObjects_def
                   | intro conjI impI)+
  done

lemma createNewCaps_vms[Retype_R_assms]:
  "\<lbrace>pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz and
    K (range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n) and
    valid_machine_state'\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>archCaps. valid_machine_state'\<rbrace>"
  apply (clarsimp simp: valid_machine_state'_def pointerInDeviceData_def
                        Arch_createNewCaps_def createNewCaps_def pointerInUserData_def
                        typ_at'_def createObjects_def doMachineOp_return_foo
                  split del: if_split)
  apply (rule hoare_pre)
   apply (wpc
         | wp hoare_vcg_const_Ball_lift hoare_vcg_disj_lift
           hoare_vcg_all_lift
           doMachineOp_ko_wp_at' createObjects_orig_ko_wp_at2'[where sz = sz]
           hoare_vcg_all_lift
           dmo_lift' mapM_x_wp' threadSet_ko_wp_at2' copyGlobalMappings_ko_wp_at
         | clarsimp simp: createObjects_def Arch_createNewCaps_def curDomain_def Let_def
                          createNewCaps_arch_ko_pre_def
               split del: if_split
         | assumption)+
  apply (case_tac ty)
   apply (auto simp: APIType_capBits_def objBits_simps toAPIType_def object_type.splits
                     field_simps mult_2_right vspace_bits_defs)
  done

lemma createNewCaps_pspace_domain_valid[Retype_R_assms, wp]:
  "\<lbrace>pspace_domain_valid and K ({ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}
            \<inter> kernel_data_refs = {}
        \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n)\<rbrace>
    createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv. pspace_domain_valid\<rbrace>"
  apply (simp add: createNewCaps_def)
  apply (rule hoare_pre)
   apply (wp createObjects_pspace_domain_valid[where sz=sz]
            mapM_x_wp'
        | wpc | simp add: Arch_createNewCaps_def curDomain_def Let_def
                     split del: if_split)+
  apply (simp add: ARM_H.toAPIType_def
            split: object_type.splits)
  apply (auto simp: objBits_simps APIType_capBits_def field_simps mult_2_right vspace_bits_defs)
  done

end (* Arch *)

arch_requalify_consts
  makeObjectKO
  APIType_map2
  APIType_capBits
  update_gs

interpretation Retype_R?: Retype_R makeObjectKO APIType_map2 APIType_capBits update_gs
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Retype_R_assms)?)?)
qed

locale Arch_retype_mdb = retype_mdb + Arch
begin

lemma valid_badges_n: "valid_badges n"
proof -
  from valid
  have "valid_badges m" ..
  thus ?thesis
    apply (clarsimp simp: valid_badges_def)
    apply (simp add: n_Some_eq n_next gen_isCap_simps split: if_split_asm)
    apply fastforce
    done
qed

lemma valid_n:
  "valid_mdb_ctes n"
  by (simp add: valid_mdb_ctes_def dlist_n no_0_n mdb_chain_0_n
                valid_badges_n caps_contained_n untyped_mdb_n
                untyped_inc_n mdb_chunked_n valid_nullcaps_n ut_rev_n
                class_links_n irq_control_n dist_z_n
                reply_masters_rvk_fb_n)

end (* Arch_retype_mdb *)

context Arch begin arch_global_naming

named_theorems Retype_R_2_assms

(* drop the Arch assumption directly instead of requalifying to improve processing time
   (unfold_locales for Arch is slow) *)
lemmas [Retype_R_2_assms] = Arch_retype_mdb.valid_n[simplified Arch_retype_mdb_def]

(* FIXME arch-split: currently only the gen_ version is used *)
lemmas valid_obj_makeObject_rules =
  gen_valid_obj_makeObject_rules
  valid_obj_makeObject_pte valid_obj_makeObject_asid_pool

lemma retype_state_relation[Retype_R_2_assms]:
  notes data_map_insert_def[simp del]
  assumes  sr:   "(s, s') \<in> state_relation"
      and  vs:   "valid_pspace s" "valid_mdb s"
      and  et:   "valid_list s"
      and vs':   "pspace_aligned' s'" "pspace_distinct' s'"
      and  pn:   "pspace_no_overlap_range_cover ptr sz s"
      and pn':   "pspace_no_overlap' ptr sz s'"
      and cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
      and  ko:   "makeObjectKO dev d ty = Some ko"
      and api:   "obj_bits_api (APIType_map2 ty) us \<le> sz"
      and orr:   "obj_relation_retype (default_object (APIType_map2 ty) dev us d) ko"
      and num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
  "(s \<lparr>kheap :=
              foldr (\<lambda>p. data_map_insert p (default_object (APIType_map2 ty) dev us d))
               (retype_addrs ptr (APIType_map2 ty) n us) (kheap s)\<rparr>,
           update_gs (APIType_map2 ty) us (set (retype_addrs ptr (APIType_map2 ty) n us))
            (s'\<lparr>ksPSpace :=
                  foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko)
                   (ksPSpace s')\<rparr>))
          \<in> state_relation"
  (is "(s\<lparr>kheap := ?ps\<rparr>, update_gs _ _ _ (s'\<lparr>ksPSpace := ?ps'\<rparr>))
       \<in> state_relation")
  proof (rule state_relation_null_filterE[OF sr refl _ _ _ _ _ _ _ _ vs'],
         simp_all add: trans_state_update[symmetric] del: trans_state_update)

  have cover':"range_cover ptr sz (objBitsKO ko) m"
    by (rule range_cover_rel[OF cover objBits_le_obj_bits_api[OF ko] num_r])
  have al':"is_aligned ptr (objBitsKO ko)"
    using cover'
    by (simp add:range_cover_def)
  have sz:"sz < word_bits"
    using cover'
    by (simp add:range_cover_def word_bits_def)
  let ?t = "s\<lparr>kheap := ?ps\<rparr>"
  let ?tp = "APIType_map2 ty"
  let ?al = "retype_addrs ptr ?tp n us"
  let ?t' = "update_gs ?tp us (set ?al) (s'\<lparr>ksPSpace := ?ps'\<rparr>)"

  note pad' = retype_aligned_distinct' [OF vs' pn' cover']
  thus pa': "pspace_aligned' (s'\<lparr>ksPSpace := ?ps'\<rparr>)"
   and pd': "pspace_distinct' (s'\<lparr>ksPSpace := ?ps'\<rparr>)"
    by simp_all

  note pa'' = pa'[simplified foldr_upd_app_if[folded data_map_insert_def]]
  note pd'' = pd'[simplified foldr_upd_app_if[folded data_map_insert_def]]

  note not_unt = makeObjectKO_Untyped [OF ko]
  show "null_filter (caps_of_state ?t) = null_filter (caps_of_state s)"
    apply (rule null_filter_caps_of_state_foldr[folded data_map_insert_def])
     apply (simp add: not_unt)
    apply (rule ballI)
    apply (erule pspace_no_overlapD2 [OF pn _ cover vs(1)])
    done

  have nc_dis: "distinct (new_cap_addrs m ptr ko)"
    by (rule new_cap_addrs_distinct [OF cover'])

  note nc_al = bspec [OF new_cap_addrs_aligned [OF al']]
  note nc_al' = nc_al[unfolded objBits_def]
  show "null_filter' (map_to_ctes ?ps') = null_filter' (ctes_of s')"
    apply (rule null_filter_ctes_retype [OF ko vs' pa'' pd''])
     apply (simp add: nc_al)
    apply clarsimp
    apply (drule subsetD [OF new_cap_addrs_subset [OF cover']])
    apply (insert pspace_no_overlap_disjoint'[OF vs'(1) pn'])
    apply (drule orthD1)
      apply (simp add:ptr_add_def field_simps)
    apply clarsimp
    done

  show "valid_objs s" using vs
    by (clarsimp simp: valid_pspace_def)

  show "valid_mdb s" using vs
    by (clarsimp)

  show "valid_list s" using et
    by (clarsimp)

  show "mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)" using vs
    by (clarsimp simp: valid_mdb_def)

  have pspr: "pspace_relation (kheap s) (ksPSpace s')"
    using sr by (simp add: state_relation_def)

  thus "pspace_relation ?ps ?ps'"
    by (rule retype_pspace_relation [OF _ vs vs' pn pn' ko cover orr num_r,
        folded data_map_insert_def])

  have pn2: "\<forall>a\<in>set ?al. kheap s a = None"
    by (rule ccontr) (clarsimp simp: pspace_no_overlapD1[OF pn _ cover vs(1)])

  from sr
  have gr: "ghost_relation_wrapper s s'"
    by (rule state_relationE)

  from pn2
  have ups_of_heap_nonarch:
    "(\<And>ao. ?tp \<noteq> ArchObject ao) \<Longrightarrow> ups_of_heap ?ps = ups_of_heap (kheap s)"
    apply -
    apply (rule ext, induct (?al); clarsimp simp: ups_of_heap_def default_object_def)
    apply (case_tac "?tp";
           force simp: APIType_map2_gen_def not_unt data_map_insert_def map_upd_Some_unfold
                 split: Structures_A.kernel_object.splits option.splits)
    done

  from pn2
  have cns_of_heap_noncnode:
    "?tp \<noteq> Structures_A.CapTableObject \<Longrightarrow> cns_of_heap ?ps = cns_of_heap (kheap s)"
    apply -
    apply (rule ext, induct (?al); clarsimp simp: cns_of_heap_def default_object_def)
    apply (case_tac "?tp";
           force simp: APIType_map2_gen_def not_unt data_map_insert_def map_upd_Some_unfold
                 split: Structures_A.kernel_object.splits option.splits)
    done

  show "ghost_relation ?ps (gsUserPages ?t') (gsCNodes ?t')"
  proof (cases ?tp)
    case Untyped thus ?thesis by (simp add: not_unt)
  next
    case TCBObject
    from gr show ?thesis
      by (simp add: ghost_relation_of_heap)
         (simp add: TCBObject update_gs_def ups_of_heap_nonarch[@\<open>simp add: TCBObject\<close>]
                    cns_of_heap_noncnode[@\<open>simp add: TCBObject\<close>])
  next
    case EndpointObject
    from gr show ?thesis
      by (simp add: ghost_relation_of_heap)
         (simp add: EndpointObject update_gs_def ups_of_heap_nonarch[@\<open>simp add: EndpointObject\<close>]
                    cns_of_heap_noncnode[@\<open>simp add: EndpointObject\<close>])
  next
    case NotificationObject
    from gr show ?thesis
      by (simp add: ghost_relation_of_heap)
         (simp add: NotificationObject update_gs_def ups_of_heap_nonarch[@\<open>simp add: NotificationObject\<close>]
                    cns_of_heap_noncnode[@\<open>simp add: NotificationObject\<close>])
  next
    case CapTableObject
    have [simp]: "cns_of_heap ?ps = (\<lambda>x. if x \<in> set ?al then Some us
                                         else cns_of_heap (kheap s) x)"
      by (rule ext, induct (?al),
          simp_all add: cns_of_heap_def wf_empty_bits wf_unique default_object_def CapTableObject
                        data_map_insert_def)
    from gr show ?thesis
      by (simp add: ghost_relation_of_heap,
          simp add: CapTableObject update_gs_def ext ups_of_heap_nonarch[@\<open>simp add: CapTableObject\<close>])
  next
    case (ArchObject ao)

    from pn2 gr show ?thesis
      apply (clarsimp simp add: ghost_relation_of_heap)
      apply (rule conjI[rotated])
       apply (simp add: update_gs_def ArchObject cns_of_heap_noncnode[@\<open>simp add: ArchObject\<close>]
                   split: aobject_type.splits)
      apply (thin_tac "cns_of_heap h = g" for h g)
      apply (drule sym)
      apply (rule ext)
      apply (induct (?al))
       apply (simp add: update_gs_def ArchObject split: aobject_type.splits)
      apply (simp add: update_gs_def ArchObject default_object_def
                       default_arch_object_def ups_of_heap_def
                       data_map_insert_def
                split: aobject_type.splits)
      done
  qed

  show "\<exists>f' g' h' as'. ?t' =
          s'\<lparr>ksPSpace := f' (ksPSpace s'), gsUserPages := g' (gsUserPages s'),
             gsCNodes := h' (gsCNodes s'),
             ksArchState := as' (ksArchState s')\<rparr>"
    apply (clarsimp simp: update_gs_def
                   split: Structures_A.apiobject_type.splits)
    apply (intro conjI impI)
         apply (subst ex_comm, rule_tac x=id in exI,
                subst ex_comm, rule_tac x=id in exI,
                subst ex_comm, rule_tac x=id in exI, fastforce)+
     apply (subst ex_comm, rule_tac x=id in exI)
     apply (subst ex_comm)
     apply (rule_tac x="\<lambda>cns x. if x\<in>set ?al then Some us else cns x" in exI,
            simp)
     apply (subst ex_comm, rule_tac x=id in exI)
     apply (rule_tac x="\<lambda>x. foldr (\<lambda>addr. data_map_insert addr ko)
                                  (new_cap_addrs m ptr ko) x" in exI, simp)
    apply clarsimp
    apply (rule_tac x="\<lambda>x. foldr (\<lambda>addr. data_map_insert addr ko)
                                 (new_cap_addrs m ptr ko) x" in exI)
    apply (subst ex_comm, rule_tac x=id in exI)
    apply (simp split: aobject_type.splits)
    apply (intro conjI impI)
           apply (subst ex_comm, rule_tac x=id in exI)
           apply (rule_tac x="\<lambda>cns x. if x \<in> set ?al then Some ARMSmallPage
                                      else cns x" in exI, simp)
          apply (subst ex_comm, rule_tac x=id in exI)
          apply (rule_tac x="\<lambda>cns x. if x \<in> set ?al then Some ARMLargePage
                                     else cns x" in exI, simp)
         apply (subst ex_comm, rule_tac x=id in exI)
         apply (rule_tac x="\<lambda>cns x. if x \<in> set ?al then Some ARMSection
                                    else cns x" in exI, simp)
        apply (subst ex_comm, rule_tac x=id in exI)
        apply (rule_tac x="\<lambda>cns x. if x \<in> set ?al then Some ARMSuperSection
                                   else cns x" in exI, simp)
       apply (rule_tac x=id in exI)
       apply (cases s', rename_tac arch machine, case_tac arch)
       apply fastforce
      apply (rule_tac x=id in exI)
      apply (cases s', rename_tac arch machine, case_tac arch)
      apply fastforce
     apply (rule_tac x=id in exI, simp)+
    done

  have rdyqrel: "ready_queues_relation s s'"
    using sr by (simp add: state_relation_def)

  thus "ready_queues_relation_2 (ready_queues s) (ksReadyQueues s')
                                (?ps' |> tcb_of' |> tcbSchedNext) (?ps' |> tcb_of' |> tcbSchedPrev)
                                (\<lambda>d p. inQ d p |< (?ps' |> tcb_of'))"
    using retype_ready_queues_relation[OF _ vs' pn' ko cover num_r]
    by (clarsimp simp: ready_queues_relation_def Let_def)

  have asr: "(arch_state s, ksArchState s') \<in> arch_state_relation" using sr
    by (blast dest: state_relationD)

  thus "(arch_state s, ksArchState ?t') \<in> arch_state_relation"
    using asr
    by (clarsimp simp: arch_state_relation_def update_gs_def comp_def
                 split: Structures_A.apiobject_type.splits aobject_type.splits)
qed

lemma createObjects_valid_objs'[Retype_R_2_assms]:
  assumes mko: "makeObjectKO dev d ty = Some val"
    and max_d: "ty = Inr (APIObjectType TCBObject) \<longrightarrow> d \<le> maxDomain"
    and vo: "valid_objs' s"
    and ad: "pspace_aligned' s" "pspace_distinct' s"
    and pn: "pspace_no_overlap' ptr sz s"
    and cover: "range_cover ptr sz (objBitsKO val + gbits) n"
    and pc: "caps_no_overlap'' ptr sz s"
    and reserved : "caps_overlap_reserved' {ptr..ptr + of_nat n *2 ^ gbits * 2 ^ objBitsKO val - 1} s"
  shows
  "valid_objs'
     (s\<lparr>ksPSpace :=
          foldr (\<lambda>addr. data_map_insert addr val) (new_cap_addrs (n * 2 ^ gbits) ptr val) (ksPSpace s)\<rparr>)"
proof -

  note cover' = range_cover_rel[where sbit' = "objBitsKO val",OF cover _ refl,simplified]

  note obj_at_disj = retype_obj_at_disj' [OF ad pn cover']

  note obj_at_disj' = obj_at_disj [unfolded foldr_upd_app_if[folded data_map_insert_def]]

  let ?s' = "s\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr val) (new_cap_addrs (n * 2 ^ gbits) ptr val) (ksPSpace s)\<rparr>"

  have valid_cap: "\<And>cap q. \<lbrakk> s \<turnstile>' cap; cte_wp_at' (\<lambda>cte. cteCap cte = cap) q s \<rbrakk>
                      \<Longrightarrow> ?s' \<turnstile>' cap"
     apply (rule valid_untyped'_helper[OF _ _ _ pc _ ad pn ])
          apply simp+
        apply (subst mult.commute)
        apply (rule cover')
       using reserved
     apply (clarsimp simp:caps_overlap_reserved'_def cte_wp_at_ctes_of)
     apply (drule_tac x = cte in bspec)
       apply fastforce
     apply simp
   done

  show ?thesis using vo
    apply (clarsimp simp: valid_objs'_def
                          foldr_upd_app_if[folded data_map_insert_def]
                   elim!: ranE
                   split: if_split_asm)
     apply (insert sym[OF mko])[1]
     apply (clarsimp simp: makeObjectKO_def max_d
                    split: bool.split_asm sum.split_asm
                           ARM_H.object_type.split_asm
                           apiobject_type.split_asm
                           kernel_object.split_asm
                           arch_kernel_object.split_asm)
    apply (drule bspec, erule ranI)
    apply (subst mult.commute)
    apply (case_tac obj; simp add: valid_obj'_def)
       apply (rename_tac endpoint)
       apply (case_tac endpoint; simp add: valid_ep'_def obj_at_disj')
      apply (rename_tac notification)
      apply (case_tac notification; simp add: valid_ntfn'_def valid_bound_tcb'_def obj_at_disj')
      apply (rename_tac ntfn xa)
      apply (case_tac ntfn, simp_all, (clarsimp simp: obj_at_disj' split:option.splits)+)
     apply (rename_tac tcb)
     apply (case_tac tcb, clarsimp simp add: valid_tcb'_def)
     apply (frule pspace_alignedD' [OF _ ad(1)])
     apply (frule pspace_distinctD' [OF _ ad(2)])
     apply (simp add: objBits_simps)
     apply (subst mult.commute)
     apply (intro conjI ballI)
       apply (clarsimp elim!: ranE)
       apply (rule valid_cap[unfolded foldr_upd_app_if[folded data_map_insert_def]])
        apply (fastforce)
       apply (rule_tac ptr="x + xa" in cte_wp_at_tcbI', assumption+)
        apply fastforce
       apply simp
      apply (rename_tac thread_state mcp priority bool option nat cptr vptr bound tcbprev tcbnext tcbflags tcbarch)
      apply (case_tac thread_state, simp_all add: valid_tcb_state'_def valid_bound_tcb'_def
                                                  valid_bound_ntfn'_def obj_at_disj' opt_tcb_at'_def
                                           split: option.splits)[4]
     apply (clarsimp simp add: valid_arch_tcb'_def typ_at_to_obj_at_arches obj_at_disj')
    apply (simp add: valid_cte'_def)
    apply (frule pspace_alignedD' [OF _ ad(1)])
    apply (frule pspace_distinctD' [OF _ ad(2)])
    apply (simp add: objBits_simps')
    apply (subst mult.commute)
    apply (erule valid_cap[unfolded foldr_upd_app_if[folded data_map_insert_def]])
    apply (erule(2) cte_wp_at_cteI'[unfolded cte_level_bits_def])
    apply simp
    done
qed

lemma createNewCaps_idle'[Retype_R_2_assms, wp]:
  "\<lbrace>valid_idle' and valid_pspace' and pspace_no_overlap' ptr sz
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
   createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: createNewCaps_def ARM_H.toAPIType_def
             split del: if_split)
  apply (cases ty, simp_all add: Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)[1]
            apply (wpsimp wp: createObjects_idle'[where sz=sz] mapM_x_wp' split_del: if_split
                        simp: curDomain_def APIType_capBits_def createObjects_def
                   | simp add: projectKO_opt_tcb projectKO_opt_cte mult_2 makeObject_cte makeObject_tcb
                               archObjSize_def tcb_cte_cases_def objBitsKO_def APIType_capBits_gen_def
                               vspace_bits_defs objBits_def createObjects_def tcb_cte_cases_neqs)+
  done

lemma valid_pde_mappings'_def3:
  "valid_pde_mappings' =
     (\<lambda>s. \<forall>x. \<not> obj_at' (Not \<circ> valid_pde_mapping' (x && mask pdBits)) x s)"
  apply (simp add: valid_pde_mappings'_def)
  apply (rule ext, rule iff_allI)
  apply (auto simp: obj_at'_def)
  done

lemma createObjects'_pde_mappings'[wp]:
  "\<lbrace>\<lambda>s. valid_pde_mappings' s \<and> range_cover ptr sz (objBitsKO val + gbits) n  \<and> n \<noteq> 0
            \<and> pspace_aligned' s \<and> pspace_distinct' s
            \<and> pspace_no_overlap' ptr sz s
            \<and> (\<forall>pde. projectKO_opt val = Some pde \<longrightarrow> pde = InvalidPDE)\<rbrace>
       createObjects' ptr n val gbits
   \<lbrace>\<lambda>_. valid_pde_mappings'\<rbrace>"
  apply (simp only: valid_pde_mappings'_def3 all_simps(1)[symmetric])
  apply (rule hoare_vcg_all_lift)
  apply (wp createObjects_orig_obj_at2')
  apply (clarsimp simp: projectKO_opt_pde o_def valid_pde_mapping'_def
                 split: Structures_H.kernel_object.split_asm
                        arch_kernel_object.split_asm)
  apply auto
  done

lemma createObjects_pde_mappings'[wp]:
  "\<lbrace>\<lambda>s. valid_pde_mappings' s \<and> range_cover ptr sz (objBitsKO ko + gbits) n  \<and> n \<noteq> 0
            \<and> pspace_aligned' s \<and> pspace_distinct' s
            \<and> pspace_no_overlap' ptr sz s
            \<and> (\<forall>pde. projectKO_opt ko = Some pde \<longrightarrow> pde = InvalidPDE)\<rbrace>
       createObjects ptr n ko gbits
   \<lbrace>\<lambda>_. valid_pde_mappings'\<rbrace>"
  by (simp add: createObjects_def objBits_def | intro conjI | wp | clarsimp)+

lemma getObject_valid_pde_mapping':
  "\<lbrace>valid_pde_mappings' and K (p && mask pdBits = p')\<rbrace> getObject p \<lbrace>\<lambda>pde s. valid_pde_mapping' p' pde\<rbrace>"
  apply (wp getPDE_wp)
  apply (clarsimp simp: valid_pde_mappings'_def)
  done

lemma copyGlobalMappings_pde_mappings':
  "\<lbrace>valid_pde_mappings' and (\<lambda>s. is_aligned (armKSGlobalPD (ksArchState s)) pdBits)
        and K (is_aligned pd pdBits)\<rbrace> copyGlobalMappings pd \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (simp add: copyGlobalMappings_def objBits_simps)
  apply wp
   apply (rule_tac P="is_aligned globalPD pdBits \<and> is_aligned pd pdBits"
                in hoare_gen_asm)
   apply (rule mapM_x_wp[where S="{x. x < 2 ^ (pdBits - 2)}"])
    apply (wp getObject_valid_pde_mapping' | simp)+
     apply clarsimp
     apply (drule(1) is_aligned_add_helper[OF _ shiftl_less_t2n])
      apply (simp add: pdBits_def pageBits_def pdeBits_def)
     apply (drule(1) is_aligned_add_helper[OF _ shiftl_less_t2n])
      apply (simp add: pdBits_def pageBits_def pdeBits_def)
     apply (simp add: pdeBits_def)
    apply simp
   apply (clarsimp simp: pdBits_def pdeBits_def le_less_trans)
  apply wp
  apply clarsimp
  done

lemma copyGlobalMappings_valid_arch_state'[wp]:
  "\<lbrace>valid_arch_state' and K (is_aligned pd pdBits) \<rbrace> copyGlobalMappings pd \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (wp valid_arch_state_lift'_valid_pde_mappings' copyGlobalMappings_pde_mappings')
     (clarsimp simp: valid_arch_state'_def page_directory_at'_def)

lemma mapM_x_copyGlobalMappings_pde_mappings':
  "\<lbrace>valid_pde_mappings' and (\<lambda>s. is_aligned (armKSGlobalPD (ksArchState s)) pdBits)
        and K (\<forall>x \<in> set xs. is_aligned x pdBits)\<rbrace>
      mapM_x copyGlobalMappings xs \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp [OF _ subset_refl])
   apply (wp copyGlobalMappings_pde_mappings' | simp)+
  done

lemma createNewCaps_pde_mappings'[wp]:
  "\<lbrace>\<lambda>s. valid_pde_mappings' s \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
            \<and> valid_arch_state' s
            \<and> pspace_aligned' s \<and> pspace_distinct' s
            \<and> pspace_no_overlap' ptr sz s\<rbrace>
       createNewCaps ty ptr n us d
   \<lbrace>\<lambda>_. valid_pde_mappings'\<rbrace>"
  apply (simp add: createNewCaps_def Arch_createNewCaps_def Let_def
              split del: if_split cong: option.case_cong
                                        object_type.case_cong)
  apply (rule hoare_pre)
   apply (wp mapM_x_copyGlobalMappings_pde_mappings'
             mapM_x_wp'[where f="\<lambda>r. doMachineOp (m r)" for m]
         | wpc
         | simp split del: if_split)+
    apply (rule_tac P="range_cover ptr sz (APIType_capBits ty us) n \<and> n\<noteq> 0" in hoare_gen_asm)
    apply (rule hoare_strengthen_post)
     apply (rule createObjects_aligned, simp+)
        apply (simp add: objBits_simps vspace_bits_defs APIType_capBits_def range_cover_def)
       apply (rule range_cover.range_cover_n_less[where 'a=32, folded word_bits_def],fastforce+)
     apply (simp add: objBits_simps vspace_bits_defs APIType_capBits_def range_cover_def word_bits_def)+
   apply (wp mapM_x_wp[OF _ subset_refl] | wpc | simp add: curDomain_def)+
  apply clarsimp
  apply (simp add: objBits_simps pdBits_def pageBits_def APIType_capBits_def)
  apply (case_tac ty; simp)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type)
  apply (auto simp: ARM_H.toAPIType_def objBits_simps vspace_bits_defs
                    makeObject_pde valid_arch_state'_def page_directory_at'_def)
  done

lemma createNewCaps_obj_at'':
  "\<lbrace>\<lambda>s. obj_at' (P :: ('a :: pspace_storable) \<Rightarrow> bool) p s
       \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s
       \<and> (koType(TYPE('a)) = koType(TYPE(pde))
               \<longrightarrow> (\<forall>x. P x)
                \<and> (\<forall>pde :: pde. \<exists>x :: 'a. injectKO x = injectKO pde))
       \<and> (\<forall>tcb d. \<not>tcbQueued tcb \<and> tcbState tcb = Inactive \<longrightarrow> ((\<exists>obj :: 'a. injectKOS obj = KOTCB (tcb\<lparr>tcbDomain := d\<rparr>) \<and> P obj) \<longleftrightarrow> (\<exists>obj :: 'a. injectKOS obj = KOTCB tcb \<and> P obj)))\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. obj_at' P p s\<rbrace>"
  apply (simp add: obj_at'_real_def)
  apply (wp createNewCaps_ko_wp_at')
  apply clarsimp
  apply (clarsimp simp: createNewCaps_arch_ko_pre_def)
  apply (intro conjI impI)
     apply simp+
   apply (fastforce simp: project_koType project_inject dest!: iffD1[OF project_koType, OF exI])
  apply (clarsimp simp: project_koType project_inject)
  done

lemma createNewCaps_valid_arch_state[Retype_R_2_assms]:
  "\<lbrace>(\<lambda>s. valid_arch_state' s \<and> valid_pspace' s \<and> pspace_no_overlap' ptr sz s
        \<and> (tp = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> us > 0))
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  unfolding valid_arch_state'_def
  apply (simp add: valid_arch_state'_def
                   valid_asid_table'_def
                   valid_global_pts'_def
                   page_table_at'_def
                   page_directory_at'_def
                   typ_at_to_obj_at_arches)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksArchState, OF createNewCaps_ksArch])
   apply (wp hoare_vcg_const_Ball_lift
             hoare_vcg_prop
             createNewCaps_obj_at''
             createNewCaps_ko_wp_at'
             hoare_vcg_all_lift
             hoare_vcg_const_imp_lift)
  apply (auto simp add: valid_arch_state'_def
                   valid_asid_table'_def
                   valid_global_pts'_def
                   page_table_at'_def
                   page_directory_at'_def
                   typ_at_to_obj_at_arches comp_def)
  done

lemma createNewCaps_sched_queues[Retype_R_2_assms]:
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  assumes not_0: "n \<noteq> 0"
  shows
    "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s
          \<and> P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>
     createNewCaps ty ptr n us dev
     \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: ARM_H.toAPIType_def split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (wp, simp)
           apply (insert cover not_0)
           apply (wpsimp wp: mapM_x_wp' createObjects_sched_queues threadSet_sched_pointers
                         simp: curDomain_def createObjects_def)
           apply (simp add: valid_pspace'_def objBits_simps APIType_capBits_gen_def makeObject_tcb)
          by (wpsimp wp: mapM_x_wp' createObjects_sched_queues threadSet_sched_pointers
                     simp: createObjects_def valid_pspace'_def objBits_simps APIType_capBits_def
                     split_del: if_split,
              fastforce simp add: mult_2 add_ac vspace_bits_defs)+

lemma createNewCaps_null_filter'[Retype_R_2_assms]:
  "\<lbrace>(\<lambda>s. P (null_filter' (ctes_of s)))
      and pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz
      and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0) \<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>_ s. P (null_filter' (ctes_of s))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: createNewCaps_def toAPIType_def
                   Arch_createNewCaps_def
               split del: if_split cong: option.case_cong)
  apply (cases ty, simp_all split del: if_split)
          apply (rename_tac apiobject_type)
          apply (case_tac apiobject_type, simp_all split del: if_split)
              apply (rule hoare_pre, wp,simp)
             apply (simp add: createObjects_def makeObjectKO_def APIType_capBits_def
                              objBits_def APIType_capBits_gen_def
                              curDomain_def objBits_if_dev vspace_bits_defs
                       split del: if_split
                    | wp createObjects_null_filter'[where ty = "Inr ty" and sz = sz and dev=dev]
                         threadSet_ctes_of mapM_x_wp'
                    | simp add: objBits_simps
                    | fastforce)+
  done

lemma createObjects_no_cte_valid_global[Retype_R_2_assms]:
  assumes no_cte: "\<And>c. projectKO_opt val \<noteq> Some (c::cte)"
  assumes no_tcb: "\<And>t. projectKO_opt val \<noteq> Some (t::tcb)"
  shows "\<lbrace>\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and>
        range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        valid_global_refs' s\<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s. valid_global_refs' s\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_cap_sizes'_def valid_refs'_def)
  apply (rule_tac Q'="\<lambda>rv s. \<forall>ptr. \<not> cte_wp_at' (\<lambda>cte. (kernel_data_refs \<inter> capRange (cteCap cte) \<noteq> {}
        \<or> 2 ^ capBits (cteCap cte) > gsMaxObjectSize s)) ptr s \<and> global_refs' s \<subseteq> kernel_data_refs"
                 in hoare_post_imp)
   apply (auto simp: cte_wp_at_ctes_of linorder_not_less elim!: ranE)[1]
  apply (rule hoare_pre)
   apply (simp add: global_refs'_def)
   apply (rule hoare_use_eq [where f=ksIdleThread, OF createObjects_it])
   apply (rule hoare_use_eq [where f=irq_node', OF createObjects_ksInterrupt])
   apply (rule hoare_use_eq [where f=gsMaxObjectSize], wp)
   apply (simp add: createObjects_def)
   apply (wp hoare_vcg_all_lift createObjects_orig_cte_wp_at2')
  using no_cte no_tcb
  apply (simp add: split_def cte_wp_at_ctes_of split: option.splits)
  apply (clarsimp simp: global_refs'_def)
  apply (auto simp: ball_ran_eq linorder_not_less[symmetric])
  done

lemma createObjects_valid_arch:
  "\<lbrace>\<lambda>s. valid_arch_state' s \<and> pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and> range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        (\<forall>pde. projectKO_opt val = Some pde \<longrightarrow> pde = InvalidPDE) \<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s. valid_arch_state' s\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def
                   page_directory_at'_def valid_global_pts'_def
                   page_table_at'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksArchState, OF createObjects_ksArch])
    apply (simp add: createObjects_def)
    apply (wp createObjects'_typ_at hoare_vcg_all_lift hoare_vcg_const_imp_lift
              hoare_vcg_const_Ball_lift)
  apply (simp add: o_def)
  apply auto
  done

lemma createObjects_untyped_ranges_zero'[Retype_R_2_assms]:
  assumes moKO: "makeObjectKO dev d ty = Some val"
  shows
  "\<lbrace>ct_active' and valid_pspace' and pspace_no_overlap' ptr sz
       and untyped_ranges_zero'
       and K (range_cover ptr sz (objBitsKO val + gSize) n \<and> n \<noteq> 0)\<rbrace>
     createObjects ptr n val gSize
   \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: untyped_zero_ranges_cte_def iff_conv_conj_imp
                   createObjects_def)
  apply (simp only: imp_conv_disj not_all not_ex)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_conj_lift
             hoare_vcg_disj_lift createObjects_orig_cte_wp_at2'[where sz=sz])
  apply (clarsimp simp: valid_pspace'_def)
  apply (cut_tac moKO[symmetric])
  apply (simp add: makeObjectKO_def projectKO_opt_tcb projectKO_opt_cte
                   split: sum.split_asm kernel_object.split_asm
                          arch_kernel_object.split_asm
                          object_type.split_asm apiobject_type.split_asm)
   apply (simp add: makeObject_tcb tcb_cte_cases_def cteSizeBits_def makeObject_cte
                    untypedZeroRange_def)
  apply (simp add: makeObject_cte untypedZeroRange_def)
  done

end (* Arch *)

interpretation Retype_R_2?: Retype_R_2 makeObjectKO APIType_map2
                                        APIType_capBits update_gs
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Retype_R_2_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Retype_R_3_assms

lemma createObjects_no_cte_invs:
  assumes moKO: "makeObjectKO dev d ty = Some val"
  assumes no_cte: "\<And>c. projectKO_opt val \<noteq> Some (c::cte)"
  assumes no_tcb: "\<And>t. projectKO_opt val \<noteq> Some (t::tcb)"
  and     mdom: "ty = Inr (APIObjectType ArchTypes_H.apiobject_type.TCBObject) \<longrightarrow> d \<le> maxDomain"
  shows
  "\<lbrace>\<lambda>s. range_cover ptr sz ((objBitsKO val) + gbits) n \<and> n \<noteq> 0
        \<and> sz \<le> maxUntypedSizeBits
        \<and> invs' s \<and> ct_active' s
        \<and> pspace_no_overlap' ptr sz s \<and> ptr \<noteq> 0
        \<and> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<inter> kernel_data_refs = {}
        \<and> caps_overlap_reserved' {ptr..ptr + of_nat (n * 2 ^ gbits * 2 ^ objBitsKO val) - 1} s
        \<and> caps_no_overlap'' ptr sz s \<and> refs_of' val = {} \<and> hyp_refs_of' val = {} \<and> \<not> live' val
        \<and> (\<forall>pde. projectKO_opt val = Some pde \<longrightarrow> pde = InvalidPDE)\<rbrace>
   createObjects ptr n val gbits
   \<lbrace>\<lambda>_. invs'\<rbrace>"
proof -
  have co_ct_not_inQ:
    "\<lbrakk>range_cover ptr sz ((objBitsKO val) + gbits) n; n \<noteq> 0\<rbrakk> \<Longrightarrow>
     \<lbrace>\<lambda>s. ct_not_inQ s \<and> pspace_no_overlap' ptr sz s \<and> valid_pspace' s\<rbrace>
      createObjects ptr n val gbits \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
    (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. ct_not_inQ s \<and> ?REST s\<rbrace> _ \<lbrace>_\<rbrace>")
    apply (simp add: ct_not_inQ_def)
    apply (rule_tac P'="\<lambda>s. (ksSchedulerAction s = ResumeCurrentThread) \<longrightarrow>
                             (obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<and> ?REST s)"
             in hoare_pre_imp, clarsimp)
    apply (rule hoare_convert_imp [OF createObjects_nosch])
    apply (rule hoare_weaken_pre)
     apply (wps createObjects_ct)
     apply (wp createObjects_obj_at_other)
      apply (simp)+
    done
  show ?thesis
    supply canonical_address_def[simp]
    apply (rule hoare_grab_asm)+
    apply (clarsimp simp: invs'_def valid_state'_def)
    apply wp
     apply (rule hoare_pre)
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: createObjects_def,wp createObjects_valid_pspace_untyped')
             apply (wp assms | simp add: objBits_def)+
      apply (wp createObjects_sch)
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: createObjects_def)
       apply (wp createObjects_state_refs_of'')
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: createObjects_def)
       apply (wp createObjects_state_hyp_refs_of'')
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: createObjects_def)
       apply (wp createObjects_iflive')
      apply (wp createObjects_no_cte_ifunsafe'
                assms | simp add: objBits_def)+
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: createObjects_def)
       apply (wp createObjects_idle')
      apply (wp irqs_masked_lift createObjects_no_cte_valid_global
                createObjects_valid_arch createObjects_irq_state
                createObjects_no_cte_irq_handlers assms
             | simp)+
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: createObjects_def)
       apply (wp createObjects_sched_queues)
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: createObjects_def)
       apply (wpsimp wp: createObjects_valid_sched_pointers)
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: createObjects_def)
       apply (wp createObjects_idle')
       apply (wpsimp wp: createObjects_valid_bitmaps)
      apply (wp createObjects_cur' valid_dom_schedule'_lift
                createObjects_pspace_domain_valid co_ct_not_inQ
                createObjects_ct_idle_or_in_cur_domain'
                createObjects_untyped_ranges_zero'[OF moKO]
             | simp)+
    using no_cte no_tcb
    apply (clarsimp simp: valid_pspace'_def)
    apply (extract_conjunct \<open>match conclusion in "pspace_no_overlap' ptr ?x _" \<Rightarrow> -\<close>, assumption)+
    apply (extract_conjunct \<open>match conclusion in "range_cover ptr ?x ?y _" \<Rightarrow> -\<close>, assumption)
    apply simp
    apply (rule conjI, fastforce simp add: split_def split: option.splits)
    by (auto simp: invs'_def no_tcb valid_state'_def no_cte
             split: option.splits kernel_object.splits)
qed

lemma createNewCaps_valid_pspace[Retype_R_3_assms]:
  assumes  not_0: "n \<noteq> 0"
  and      cover: "range_cover ptr sz (APIType_capBits ty us) n"
  and      sz_limit: "sz \<le> maxUntypedSizeBits"
  and      ptr_cn: "canonical_address (ptr && ~~ mask sz)"
  and      ptr_km: "ptr && ~~ mask sz \<in> kernel_mappings"
  shows
  "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s
     \<and> caps_no_overlap'' ptr sz s \<and> ptr \<noteq> 0 \<and> caps_overlap_reserved' {ptr..ptr + of_nat n * 2^(APIType_capBits ty us) - 1} s
     \<and> ksCurDomain s \<le> maxDomain\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  unfolding createNewCaps_def Arch_createNewCaps_def
  using gen_valid_obj_makeObject_rules sz_limit ptr_cn
  apply (clarsimp simp: ARM_H.toAPIType_def
             split del: if_split cong: option.case_cong)
  apply (cases ty, simp_all split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)
            apply (rule hoare_pre, wp, clarsimp)
           apply (insert cover)
           (* for TCBObject, we need to know a bit more about tcbDomain *)
           apply (simp add: curDomain_def)
           apply (rule bind_wp[OF _ gets_sp])
           apply (clarsimp simp: createObjects_def)
           apply (rule hoare_assume_pre)
           apply (wpsimp wp: createObjects_valid_pspace_untyped'[of _ _ "Inr ty", where ptr=ptr]
                             mapM_x_wp'
                  split_del: if_split
                       simp: createObjects_def makeObjectKO_def objBits_def objBitsKO_def
                             not_0 APIType_capBits_def field_simps APIType_capBits_gen_def
                             objBits_simps vspace_bits_defs
                  | simp add: power_add)+
  done

lemma data_page_relation_retype:
  "obj_relation_retype (ArchObj (DataPage False pgsz)) KOUserData"
  "obj_relation_retype (ArchObj (DataPage True pgsz)) KOUserDataDevice"
  apply (simp_all add: obj_relation_retype_def shiftl_t2n mult_ac
                   objBits_simps pbfs_atleast_pageBits)
   apply (clarsimp simp: image_def)+
  done

lemma corres_retype_region_createNewCaps:
  "corres ((\<lambda>r r'. length r = length r' \<and> list_all2 cap_relation r r')
               \<circ> map (\<lambda>ref. default_cap (APIType_map2 (Inr ty)) ref us dev))
            (\<lambda>s. valid_pspace s \<and> valid_mdb s \<and> valid_list s \<and> valid_arch_state s
                   \<and> caps_no_overlap y sz s \<and> pspace_no_overlap_range_cover y sz s
                   \<and> caps_overlap_reserved {y..y + of_nat n * 2 ^ (obj_bits_api (APIType_map2 (Inr ty)) us) - 1} s
                   \<and> (\<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area y sz \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
                   \<and> (APIType_map2 (Inr ty) = Structures_A.CapTableObject \<longrightarrow> 0 < us))
            (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' y sz s
                  \<and> valid_pspace' s \<and> valid_arch_state' s
                  \<and> range_cover y sz (obj_bits_api (APIType_map2 (Inr ty)) us) n \<and> n\<noteq> 0)
            (do x \<leftarrow> retype_region y n us (APIType_map2 (Inr ty)) dev :: obj_ref list det_ext_monad;
                init_arch_objects (APIType_map2 (Inr ty)) dev y n us x;
                return x od)
            (createNewCaps ty y n us dev)"
  supply APIType_map2_generic[simp del]
  apply (rule_tac F="range_cover y sz (obj_bits_api (APIType_map2 (Inr ty)) us) n
                      \<and> n \<noteq> 0 \<and> (APIType_map2 (Inr ty) = Structures_A.CapTableObject \<longrightarrow> 0 < us)"
           in corres_req, simp)
  apply (clarsimp simp: createNewCaps_def toAPIType_def
             split del: if_split cong: if_cong)
  apply (subst init_arch_objects_APIType_map2)
  apply (cases ty, simp_all add: Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)
            \<comment> \<open>Untyped\<close>
            apply (simp add: retype_region_def obj_bits_api_def APIType_map2_def
                        split del: if_split cong: if_cong)
            apply (subst upto_enum_red')
             apply (drule range_cover_not_zero[rotated])
              apply simp
             apply unat_arith
            apply (clarsimp simp: list_all2_same enum_word_def range_cover.unat_of_nat_n
                                  list_all2_map1 list_all2_map2 ptr_add_def fromIntegral_def
                                  toInteger_nat fromInteger_nat)
            apply (subst unat_of_nat_minus_1)
              apply (rule le_less_trans[OF range_cover.range_cover_n_le(2) power_strict_increasing])
                apply simp
               apply (clarsimp simp: range_cover_def)
               apply (arith+)[4]
           \<comment> \<open>TCB\<close>
           apply (simp_all add: curDomain_def APIType_map2_gen_def split del: if_split)
           apply (rule corres_underlying_gets_pre_rhs[rotated])
            apply (rule gets_sp)
           apply (rule corres_guard_imp)
             apply (rule corres_bind_return)
             apply (rule corres_split_eqr)
                apply (rule corres_retype[where 'a = tcb],
                       simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                     APIType_map2_def makeObjectKO_def)[1]
                 apply (fastforce simp: range_cover_def)
                apply (simp add: tcb_relation_retype)
               apply (rule corres_returnTT, simp)
               apply (clarsimp simp: list_all2_same list_all2_map1 list_all2_map2
                                     objBits_simps APIType_map2_def)
              apply ((wp | simp add: APIType_map2_def)+)[1]
             apply ((wp createObjects_tcb_at'[where sz=sz] | simp add: APIType_map2_def objBits_simps' obj_bits_api_def)+)[1]
            apply simp
           apply simp
          \<comment> \<open>EP, NTFN\<close>
          apply (simp add: liftM_def[symmetric] split del: if_split)
          apply (rule corres_rel_imp)
           apply (rule corres_guard_imp)
             apply (rule corres_retype[where 'a = endpoint],
                    simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                  APIType_map2_def makeObjectKO_def
                                  other_objs_default_relation)[1]
             apply ((simp add: range_cover_def APIType_map2_def
                               list_all2_same list_all2_map1 list_all2_map2)+)[4]
         apply (simp add: liftM_def[symmetric] split del: if_split)
         apply (rule corres_rel_imp)
          apply (rule corres_guard_imp)
            apply (rule corres_retype[where 'a = notification],
                   simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                 APIType_map2_def makeObjectKO_def
                                 other_objs_default_relation)[1]
            apply ((simp add: range_cover_def APIType_map2_def
                              list_all2_same list_all2_map1 list_all2_map2)+)[4]
        \<comment> \<open>CapTable\<close>
        apply (find_case \<open>CapTableObject\<close>)
        apply (subst bind_assoc_return_reverse[of "createObjects y n (KOCTE makeObject) us"])
        apply (subst liftM_def [of "map (\<lambda>addr. capability.CNodeCap addr us 0 0)", symmetric])
        apply simp
        apply (rule corres_rel_imp)
         apply (rule corres_guard_imp)
           apply (rule corres_retype_update_gsI,
                  simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                APIType_map2_def makeObjectKO_def slot_bits_def
                                field_simps ext)[1]
            apply ((clarsimp simp: range_cover_def APIType_map2_def word_bits_def
                                   list_all2_same list_all2_map1 list_all2_map2
                    | rule captable_relation_retype)+)[5]
       \<comment> \<open>SmallPageObject\<close>
       apply (in_case \<open>SmallPageObject\<close>)
       apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
       apply (simp add: init_arch_objects_def split del: if_split)
       apply (subst regroup_createObjects_dmo_userPages)
       apply (rule corres_guard_imp)
         apply (rule corres_split)
            apply (rule corres_retype_update_gsI,
                   simp_all add: APIType_map2_def makeObjectKO_def
                                 arch_default_cap_def obj_bits_api_def3
                                 default_object_def default_arch_object_def pageBits_def
                                 ext objBits_simps range_cover.aligned,
                   simp_all add: data_page_relation_retype)[1]
           apply (simp add: APIType_map2_def vs_apiobj_size_def
                       flip: when_def split del: if_split cong: if_cong)
           apply (rule corres_split)
              apply corres
              apply (rule corres_mapM_x', clarsimp)
                 apply (corres corres: corres_machine_op)
                apply wp+
              apply (rule refl)
             apply (rule corres_returnTT)
             apply (simp add: APIType_map2_def arch_default_cap_def vm_read_write_def vmrights_map_def
                              list_all2_map1 list_all2_map2 list_all2_same)
            apply ((wpsimp split_del: if_split)+)[6]
      \<comment> \<open>LargePageObject\<close>
      apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
      apply (simp add: init_arch_objects_def split del: if_split)
      apply (subst regroup_createObjects_dmo_userPages)
      apply (rule corres_guard_imp)
        apply (rule corres_split)
           apply (rule corres_retype_update_gsI,
                  simp_all add: APIType_map2_def makeObjectKO_def
                                arch_default_cap_def obj_bits_api_def3
                                default_object_def default_arch_object_def pageBits_def
                                ext objBits_simps range_cover.aligned,
                  simp_all add: data_page_relation_retype)[1]
          apply (simp add: APIType_map2_def vs_apiobj_size_def
                      flip: when_def split del: if_split cong: if_cong)
          apply (rule corres_split)
             apply corres
             apply (rule corres_mapM_x', clarsimp)
                apply (corres corres: corres_machine_op)
               apply wp+
             apply (rule refl)
            apply (rule corres_returnTT)
            apply (simp add: APIType_map2_def arch_default_cap_def vm_read_write_def vmrights_map_def
                             list_all2_map1 list_all2_map2 list_all2_same)
           apply ((wpsimp split_del: if_split)+)[6]
     \<comment> \<open>SectionObject\<close>
     apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
     apply (simp add: init_arch_objects_def split del: if_split)
     apply (subst regroup_createObjects_dmo_userPages)
     apply (rule corres_guard_imp)
       apply (rule corres_split)
          apply (rule corres_retype_update_gsI,
                 simp_all add: APIType_map2_def makeObjectKO_def
                               arch_default_cap_def obj_bits_api_def3
                               default_object_def default_arch_object_def pageBits_def
                               ext objBits_simps range_cover.aligned,
                 simp_all add: data_page_relation_retype)[1]
         apply (simp add: APIType_map2_def vs_apiobj_size_def
                     flip: when_def split del: if_split cong: if_cong)
         apply (rule corres_split)
            apply corres
            apply (rule corres_mapM_x', clarsimp)
               apply (corres corres: corres_machine_op)
              apply wp+
            apply (rule refl)
           apply (rule corres_returnTT)
           apply (simp add: APIType_map2_def arch_default_cap_def vm_read_write_def vmrights_map_def
                            list_all2_map1 list_all2_map2 list_all2_same)
          apply ((wpsimp split_del: if_split)+)[6]
    \<comment> \<open>SuperSectionObject\<close>
    apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
    apply (simp add: init_arch_objects_def split del: if_split)
    apply (subst regroup_createObjects_dmo_userPages)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule corres_retype_update_gsI,
                simp_all add: APIType_map2_def makeObjectKO_def
                              arch_default_cap_def obj_bits_api_def3
                              default_object_def default_arch_object_def pageBits_def
                              ext objBits_simps range_cover.aligned,
                simp_all add: data_page_relation_retype)[1]
        apply (simp add: APIType_map2_def vs_apiobj_size_def
                    flip: when_def split del: if_split cong: if_cong)
        apply (rule corres_split)
           apply corres
           apply (rule corres_mapM_x', clarsimp)
              apply (corres corres: corres_machine_op)
             apply wp+
           apply (rule refl)
          apply (rule corres_returnTT)
          apply (simp add: APIType_map2_def arch_default_cap_def vm_read_write_def vmrights_map_def
                           list_all2_map1 list_all2_map2 list_all2_same)
         apply ((wpsimp split_del: if_split)+)[6]
   \<comment> \<open>PageTableObject\<close>
   apply (in_case \<open>PageTableObject\<close>)
   apply (simp add: corres_liftM2_simp[unfolded liftM_def])
   apply (simp add: init_arch_objects_def bind_assoc split del: if_split)
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule corres_retype[where 'a =pte],
               simp_all add: APIType_map2_def obj_bits_api_def default_arch_object_def objBits_simps
                             ptBits_def pteBits_def makeObjectKO_def range_cover.aligned)[1]
        apply (rule pagetable_relation_retype)
       apply (clarsimp simp: APIType_map2_def vs_apiobj_size_def
                             pt_bits_def ptBits_def pageBits_def pteBits_def)
       apply (rule corres_split)
          apply (rule corres_mapM_x', clarsimp)
             apply (corres corres: corres_machine_op)
            apply wp+
          apply (rule refl)
         apply (rule corres_returnTT)
         apply corres
         apply (clarsimp simp: list_all2_map1 list_all2_map2 list_all2_same
                               APIType_map2_def arch_default_cap_def)
        apply ((wpsimp split_del: if_split)+)[6]
  \<comment> \<open>PageDirectoryObject\<close>
  apply (in_case \<open>PageDirectoryObject\<close>)
  apply (simp add: bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_retype[where ty = "Inr PageDirectoryObject" and 'a = pde],
              simp_all add: APIType_map2_def obj_bits_api_def
                            default_arch_object_def objBits_simps
                            pdBits_def pageBits_def
                            pteBits_def pdeBits_def
                            makeObjectKO_def)[1]
        apply (simp add: range_cover_def)+
       apply (rule pagedirectory_relation_retype)
      apply (rename_tac pds)
      apply (simp add: init_arch_objects_def bind_assoc APIType_map2_def
                       vs_apiobj_size_def pdBits_eq
                  split del: if_split)
      apply (rule corres_split)
         apply (rule_tac P="valid_arch_state and pspace_aligned and
                            (\<lambda>s. \<forall>pd \<in> set pds. typ_at (AArch APageDirectory) pd s)" and
                         P'="valid_arch_state' and (\<lambda>s. \<forall>pd \<in> set pds. page_directory_at' pd s)"
                         in corres_mapM_x')
            apply (clarsimp, rule corres_guard_imp, rule copyGlobalMappings_corres; simp)
           apply (wpsimp wp: hoare_vcg_op_lift simp: page_directory_at'_def)+
        apply (rule corres_split, rule corres_mapM_x', rule corres_machine_op)
              apply (clarsimp cong: corres_weak_cong)
              apply (rule corres_underlying_trivial_dc)
              apply wp+
           apply (rule refl)
          apply (rule corres_returnTT)
          apply (simp add: list_all2_map1 list_all2_map2 list_all2_same arch_default_cap_def)
         apply (wpsimp wp: retype_region_valid_arch retype_region_aligned)+
     apply (rule hoare_post_imp)
      prefer 2
      apply (rule hoare_vcg_conj_lift)
       apply (rule retype_region_obj_at)
       apply (simp add: APIType_map2_def)
      apply (simp add: APIType_map2_def)
      apply (rule retype_region_ret)
     apply (clarsimp simp: retype_addrs_def obj_bits_api_def APIType_map2_def
                           default_arch_object_def default_object_def obj_at_def a_type_def)
    apply (wpsimp wp: createObjects_valid_arch)
    apply (rule hoare_post_imp)
     prefer 2
     apply (rule hoare_vcg_conj_lift)
      apply (rule createObjects_ko_at[where sz = sz and 'a = pde])
        apply (simp add: objBits_simps pdBits_def pteBits_def pdeBits_def APIType_map2_def
                         obj_bits_api_def default_arch_object_def pageBits_def page_directory_at'_def)+
     apply (rule createObjects_aligned)
        apply (simp add: objBits_simps pdBits_def
                      pageBits_def page_directory_at'_def)+
        apply (simp add: range_cover_def pteBits_def pdeBits_def)
       apply (rule le_less_trans[OF range_cover.range_cover_n_le(2) power_strict_increasing])
         apply simp
        apply (clarsimp simp: range_cover_def word_bits_def)
        apply arith+
     apply (simp add: objBits_simps pdBits_def pageBits_def page_directory_at'_def)
     apply (simp add: word_bits_def pteBits_def pdeBits_def)
    apply clarsimp
    apply (drule (1) bspec)+
    apply (simp add: objBits_simps retype_addrs_def obj_bits_api_def pdBits_def pageBits_def
                     ptBits_def APIType_map2_def default_arch_object_def default_object_def)
    apply (clarsimp simp: objBits_simps pdBits_def
                          pageBits_def page_directory_at'_def pteBits_def pdeBits_def)
    apply (rename_tac offset)
    apply (drule_tac x = offset in spec)
    apply (clarsimp simp:typ_at'_def obj_at'_real_def)
    apply (erule ko_wp_at'_weakenE)
    apply clarsimp
   apply (auto simp: objBits_simps retype_addrs_def obj_bits_api_def pdBits_def pageBits_def
                     APIType_map2_def default_arch_object_def default_object_def
                     pteBits_def pdeBits_def ptBits_def
                     pd_bits_def fromIntegral_def toInteger_nat fromInteger_nat makeObject_pde)
  done

end (* Arch *)

interpretation Retype_R_3?: Retype_R_3 makeObjectKO APIType_map2
                                        APIType_capBits update_gs
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Retype_R_3_assms)?)?)
qed

end
