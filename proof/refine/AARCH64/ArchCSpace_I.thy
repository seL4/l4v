(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* CSpace invariants - architecture-specific *)

theory ArchCSpace_I
imports CSpace_I
begin

context Arch begin arch_global_naming

named_theorems CSpace_I_assms

lemma arch_capUntypedPtr_simps[simp]:
  "Arch.capUntypedPtr (ASIDPoolCap r asid) = r"
  "Arch.capUntypedPtr (FrameCap r rghts sz d mapdata) = r"
  "Arch.capUntypedPtr (PageTableCap r pt_t mapdata2) = r"
  "Arch.capUntypedPtr (VCPUCap r) = r"
  by (auto simp: AARCH64_H.capUntypedPtr_def)

lemma maskCapRights_allRights[simp]:
  "maskCapRights allRights c = c"
  unfolding global.maskCapRights_def isCap_defs allRights_def maskCapRights_def maskVMRights_def
  by (cases c) (simp_all add: Let_def split: arch_capability.split vmrights.split)

lemma isPhysicalCap[CSpace_I_assms, simp]:
  "isPhysicalCap cap = (capClass cap = PhysicalClass)"
  by (simp add: global.isPhysicalCap_def isPhysicalCap_def
         split: capability.split arch_capability.split)

definition arch_capMasterCap :: "arch_capability \<Rightarrow> arch_capability" where
  "arch_capMasterCap acap \<equiv> (case acap of
      FrameCap ref rghts sz d mapdata \<Rightarrow>
         FrameCap ref VMReadWrite sz d None
    | ASIDPoolCap pool asid \<Rightarrow>
         ASIDPoolCap pool 0
    | PageTableCap ptr pt_t data \<Rightarrow>
         PageTableCap ptr pt_t None
    | VCPUCap ptr \<Rightarrow>
         VCPUCap ptr
    | SMCCap _ \<Rightarrow> SMCCap 0
    | _ \<Rightarrow> acap)"

lemmas arch_capMasterCap_simps[simp] = arch_capMasterCap_def[split_simps arch_capability.split]

lemma acapClass_arch_capMasterCap[CSpace_I_assms,simp]:
  "acapClass (arch_capMasterCap acap) = acapClass acap"
  unfolding arch_capMasterCap_def
  by (simp split: arch_capability.splits)

lemma capUntypedPtr_arch_capMasterCap[CSpace_I_assms, simp]:
  "Arch.capUntypedPtr (arch_capMasterCap acap) = Arch.capUntypedPtr acap"
  unfolding arch_capMasterCap_def
  by (simp add: AARCH64_H.capUntypedPtr_def split: arch_capability.splits)

lemma acapBits_arch_capMasterCap[CSpace_I_assms, simp]:
  "acapBits (arch_capMasterCap acap) = acapBits acap"
  unfolding arch_capMasterCap_def
  by (simp split: arch_capability.splits)

lemmas isArchFrameCap_simps[simp] =
  isArchFrameCap_def[split_simps capability.split arch_capability.split]

lemma isArchFrameCap_arch_capMasterCap[CSpace_I_assms, simp]:
  "isArchFrameCap (ArchObjectCap (arch_capMasterCap acap)) = isArchFrameCap (ArchObjectCap acap)"
  by (simp add: arch_capMasterCap_def split: arch_capability.split)

lemma isArchFrameCap_non_arch[CSpace_I_assms]:
  "\<not>is_ArchObjectCap cap \<Longrightarrow> isArchFrameCap cap = False"
  by (simp add: isArchFrameCap_def is_ArchObjectCap_def split: capability.split)

(* No assertion necessary for this architecture. *)
definition arch_mdb_assert :: "cte_heap \<Rightarrow> bool" where
  "arch_mdb_assert m \<equiv> True"

definition arch_capBadge :: "arch_capability \<Rightarrow> machine_word option" where
  "arch_capBadge acap \<equiv>
     case acap of
       SMCCap smc_badge \<Rightarrow> Some smc_badge
     | _ \<Rightarrow> None"

lemmas arch_capBadge_simps[simp] = arch_capBadge_def[split_simps arch_capability.split]

lemma arch_capBadge_def2:
  "arch_capBadge acap = (if is_SMCCap acap then Some (capSMCBadge acap) else None)"
  by (cases acap; simp add: is_SMCCap_def)

end

interpretation CSpace_I?: CSpace_I AARCH64.arch_capMasterCap AARCH64.arch_capBadge
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CSpace_I_assms)?)?)
qed


context Arch begin arch_global_naming

named_theorems CSpace_I_2_assms

(* for the Arch locale we want the fully expanded version covering all cases, but avoiding the
   capMasterCap_ArchObjectCap rewrite case for an unspecified ArchObjectCap *)
declare gen_capMasterCap_simps[simp del]

lemmas capMasterCap_simps[simp] =
  capMasterCap_def[simplified arch_capMasterCap_def,
                   split_simps capability.split arch_capability.split]

lemma isArchFrameCap_capMasterCap[CSpace_I_2_assms, simp]:
  "isArchFrameCap (capMasterCap cap) = isArchFrameCap cap"
  by (simp add: isArchFrameCap_def split: capability.split arch_capability.split)

lemma arch_isCap_Master:
  "isArchObjectCap cap \<Longrightarrow> isSGISignalCap (capCap (capMasterCap cap)) = isSGISignalCap (capCap cap)"
  by (auto simp: isCap_simps capMasterCap_def arch_capMasterCap_def
           split: capability.split arch_capability.split)

lemma arch_capMasterCap_eqDs1:
  "capMasterCap cap = ArchObjectCap (FrameCap ref rghts sz d mapdata)
   \<Longrightarrow> rghts = VMReadWrite \<and> mapdata = None
      \<and> (\<exists>rghts mapdata. cap = ArchObjectCap (FrameCap ref rghts sz d mapdata))"
  "capMasterCap cap = ArchObjectCap ASIDControlCap
   \<Longrightarrow> cap = ArchObjectCap ASIDControlCap"
  "capMasterCap cap = ArchObjectCap (ASIDPoolCap pool asid)
   \<Longrightarrow> asid = 0 \<and> (\<exists>asid. cap = ArchObjectCap (ASIDPoolCap pool asid))"
  "capMasterCap cap = ArchObjectCap (PageTableCap ptr pt_t data)
   \<Longrightarrow> data = None \<and> (\<exists>data. cap = ArchObjectCap (PageTableCap ptr pt_t data))"
  "capMasterCap cap = ArchObjectCap (VCPUCap v)
   \<Longrightarrow> cap = ArchObjectCap (VCPUCap v)"
  "capMasterCap cap = ArchObjectCap (SGISignalCap sirq target)
   \<Longrightarrow> cap = ArchObjectCap (SGISignalCap sirq target)"
  "capMasterCap cap = ArchObjectCap (SMCCap smc_badge)
   \<Longrightarrow> smc_badge = 0 \<and> (\<exists>smc_badge. cap = ArchObjectCap (SMCCap smc_badge))"
  by (clarsimp simp: capMasterCap_def arch_capMasterCap_def
              split: capability.split_asm arch_capability.split_asm)+

lemmas arch_capMasterCap_eqDs[dest!] = arch_capMasterCap_eqDs1 arch_capMasterCap_eqDs1[OF sym]

lemma capUntypedSize_capBits:
  "capClass cap = PhysicalClass \<Longrightarrow> capUntypedSize cap = 2 ^ (capBits cap)"
  by (fastforce simp: global.capUntypedSize_def objBits_simps bit_simps' capUntypedSize_def
                split: capability.splits arch_capability.splits zombie_type.splits)

lemma sameRegionAs_def2:
  "sameRegionAs cap cap' =
     (\<lambda>cap cap'.
       (cap = cap'
        \<and> \<not> isNullCap cap \<and> \<not> isZombie cap \<and> \<not> isUntypedCap cap \<and> \<not> isArchFrameCap cap
        \<and> \<not> isNullCap cap' \<and> \<not> isZombie cap' \<and> \<not> isUntypedCap cap' \<and> \<not> isArchFrameCap cap')
       \<or> capRange cap' \<noteq> {} \<and> capRange cap' \<subseteq> capRange cap
         \<and> (isUntypedCap cap \<or> (isArchFrameCap cap \<and> isArchFrameCap cap'))
       \<or> isIRQControlCap cap \<and> isIRQHandlerCap cap'
       \<or> isIRQControlCap cap \<and> isArchObjectCap cap' \<and> isSGISignalCap (capCap cap'))
     (capMasterCap cap) (capMasterCap cap')"
  apply (cases "isUntypedCap cap")
   apply (clarsimp simp: global.sameRegionAs_def Let_def
                         gen_isCap_Master arch_isCap_Master capRange_Master capClass_Master)
   apply (clarsimp simp: isCap_simps
                         capMasterCap_def[where cap="UntypedCap d p n f" for d p n f])
   apply (simp add: capRange_def capUntypedSize_capBits)
   apply (intro impI iffI)
    apply (clarsimp del: subsetI intro!: range_subsetI)
   apply clarsimp
  apply (simp cong: conj_cong)
  apply (simp     add: capMasterCap_def arch_capMasterCap_def global.sameRegionAs_def
                       isArchFrameCap_def isCap_simps
                split: capability.split
            split del: if_split cong: if_cong)
  apply (simp    add: AARCH64_H.sameRegionAs_def isCap_simps
               split: arch_capability.split
           split del: if_split cong: if_cong)
  apply (clarsimp simp: capRange_def Let_def isCap_simps)
  apply (simp add: range_subset_eq2 cong: conj_cong)
  apply (simp add: conj_comms mask_def add_diff_eq isIRQControlCapDescendant_def)
  done

lemma sameObjectAs_def2:
 "sameObjectAs cap cap' = (\<lambda>cap cap'.
     (cap = cap'
          \<and> (\<not> isNullCap cap \<and> \<not> isZombie cap \<and> \<not> isUntypedCap cap)
          \<and> (\<not> isNullCap cap' \<and> \<not> isZombie cap' \<and> \<not> isUntypedCap cap')
          \<and> (isArchFrameCap cap \<longrightarrow> capRange cap \<noteq> {})
          \<and> (isArchFrameCap cap' \<longrightarrow> capRange cap' \<noteq> {})
          \<and> \<not> isIRQControlCap cap
          \<and> \<not>isArchSGISignalCap cap))
        (capMasterCap cap) (capMasterCap cap')"
  apply (simp add: global.sameObjectAs_def sameRegionAs_def2
                   isCap_simps capMasterCap_def arch_capMasterCap_def
            split: capability.split)
  apply (clarsimp simp: AARCH64_H.sameObjectAs_def isCap_simps
                 split: arch_capability.split cong: if_cong)
  apply (clarsimp simp: AARCH64_H.sameRegionAs_def isCap_simps
                  split del: if_split cong: if_cong)
  apply (simp add: capRange_def isCap_simps mask_def add_diff_eq
              split del: if_split)
  apply fastforce
  done

lemmas sameRegionAs_def3 =
  sameRegionAs_def2[simplified capClass_Master capRange_Master gen_isCap_Master arch_isCap_Master]

lemmas sameObjectAs_def3 =
  sameObjectAs_def2[simplified capClass_Master capRange_Master gen_isCap_Master arch_isCap_Master]

lemma sameRegionAsE:
  "\<lbrakk> sameRegionAs cap cap';
     \<lbrakk> capMasterCap cap = capMasterCap cap'; \<not> isNullCap cap; \<not> isZombie cap;
       \<not> isUntypedCap cap; \<not> isArchFrameCap cap\<rbrakk> \<Longrightarrow> R;
     \<lbrakk> capRange cap' \<noteq> {}; capRange cap' \<subseteq> capRange cap; isUntypedCap cap \<rbrakk> \<Longrightarrow> R;
     \<lbrakk> capRange cap' \<noteq> {}; capRange cap' \<subseteq> capRange cap; isArchFrameCap cap;
          isArchFrameCap cap' \<rbrakk> \<Longrightarrow> R;
     \<lbrakk> isIRQControlCap cap; isIRQHandlerCap cap' \<rbrakk> \<Longrightarrow> R;
     \<lbrakk> isIRQControlCap cap; isArchObjectCap cap'; isSGISignalCap (capCap cap') \<rbrakk> \<Longrightarrow> R
   \<rbrakk> \<Longrightarrow> R"
  by (simp add: sameRegionAs_def3, fastforce simp: gen_isCap_Master arch_isCap_Master)

lemma sameObjectAsE:
  "\<lbrakk> sameObjectAs cap cap';
     \<lbrakk> capMasterCap cap = capMasterCap cap'; \<not> isNullCap cap; \<not> isZombie cap;
       \<not> isUntypedCap cap;
       isArchFrameCap cap \<Longrightarrow> capRange cap \<noteq> {} \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (clarsimp simp add: sameObjectAs_def3)

lemma sameObjectAs_sameRegionAs:
  "sameObjectAs cap cap' \<Longrightarrow> sameRegionAs cap cap'"
  by (clarsimp simp add: sameObjectAs_def2 sameRegionAs_def2 isCap_simps)

lemma sameObjectAs_sym[CSpace_I_2_assms]:
  "sameObjectAs c d = sameObjectAs d c"
  by (auto simp: sameObjectAs_def2)

lemma sameObject_capRange:
  "sameObjectAs cap cap' \<Longrightarrow> capRange cap' = capRange cap"
  apply (rule master_eqI, rule capRange_Master)
  apply (clarsimp simp: sameObjectAs_def2)
  done

lemma sameRegionAs_Null[CSpace_I_2_assms, simp]:
  "sameRegionAs c NullCap = False"
  "sameRegionAs NullCap c = False"
  by (simp add: sameRegionAs_def3 capRange_def isCap_simps)+

lemma sameRegionAs_classes[CSpace_I_2_assms]:
  "sameRegionAs cap cap' \<Longrightarrow> capClass cap = capClass cap'"
  by (erule sameRegionAsE, rule master_eqI)
     (clarsimp simp: capRange_def isCap_simps intro!: capClass_Master split: if_split_asm)+

lemma sameRegionAs_capRange_Int[CSpace_I_2_assms]:
  "\<lbrakk> sameRegionAs cap cap'; capClass cap = PhysicalClass \<or> capClass cap' = PhysicalClass;
     capAligned cap; capAligned cap' \<rbrakk>
   \<Longrightarrow> capRange cap' \<inter> capRange cap \<noteq> {}"
  apply (frule sameRegionAs_classes, simp)
  apply (drule(1) capAligned_capUntypedPtr)+
  apply (erule sameRegionAsE)
      apply (subgoal_tac "capRange (capMasterCap cap') \<inter> capRange (capMasterCap cap) \<noteq> {}")
       apply (simp(no_asm_use) add: capRange_Master)
      apply (fastforce simp: capRange_Master isCap_simps)+
  done

lemma sameRegionAs_trans:
  "\<lbrakk> sameRegionAs a b; sameRegionAs b c \<rbrakk> \<Longrightarrow> sameRegionAs a c"
  by (simp add: sameRegionAs_def2, elim conjE disjE)
     (auto simp: isCap_simps capRange_def) (* long *)

lemma capMasterCap_maskCapRights[simp, CSpace_I_2_assms]:
  "capMasterCap (maskCapRights msk cap) = capMasterCap cap"
  apply (cases cap; simp add: global.maskCapRights_def Let_def isCap_simps capMasterCap_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability; simp add: maskCapRights_def Let_def isCap_simps)
  done

lemma capBadge_maskCapRights[simp]:
  "capBadge (maskCapRights msk cap) = capBadge cap"
  apply (cases cap; simp add: global.maskCapRights_def Let_def gen_isCap_simps capBadge_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability; simp add: maskCapRights_def Let_def isCap_simps)
  done

lemma cte_refs_capRange:
  "\<lbrakk> s \<turnstile>' c; \<forall>irq. c \<noteq> IRQHandlerCap irq \<rbrakk> \<Longrightarrow> cte_refs' c x \<subseteq> capRange c"
  apply (cases c; simp add: capRange_def gen_isCap_simps)
    apply (clarsimp dest!: valid_capAligned
                    simp: capAligned_def gen_objBits_simps field_simps)
    apply (frule tcb_cte_cases_small)
    apply (intro conjI)
     apply (erule(1) is_aligned_no_wrap')
    apply (rule word_plus_mono_right[where z="2^tcbBlockSizeBits - 1", simplified field_simps])
     apply (drule word_le_minus_one_leq, simp)
    apply (erule is_aligned_no_wrap'[where off="2^tcbBlockSizeBits - 1", simplified field_simps])
    apply (drule word_le_minus_one_leq)
    apply simp
   defer
   \<comment> \<open>CNodeCap\<close>
   apply (clarsimp simp: gen_objBits_simps capAligned_def dest!: valid_capAligned)
   apply (rename_tac word1 nat1 word2 nat2 x)
   apply (subgoal_tac "x * 2^cteSizeBits < 2 ^ (cteSizeBits + nat1)")
    apply (intro conjI)
     apply (simp add: shiftl_t2n mult_ac)
     apply (erule(1) is_aligned_no_wrap')
    apply (simp add: add_diff_eq[symmetric])
    apply (rule word_plus_mono_right)
     apply simp
    apply (simp add: shiftl_t2n mult_ac)
    apply (erule is_aligned_no_wrap')
    apply simp
   apply (simp add: power_add field_simps mask_def)
   apply (erule word_mult_less_mono1)
    apply simp
   apply (frule power_strict_increasing [where a="2 :: nat" and n="y + z" for y z])
    apply simp
   apply (simp only: power_add)
   apply (simp add: word_bits_def)
  \<comment> \<open>Zombie\<close>
  apply (rename_tac word zombie_type nat)
  apply (clarsimp simp: capAligned_def valid_cap'_def gen_objBits_simps)
  apply (subgoal_tac "xa * 2^cteSizeBits < 2 ^ zBits zombie_type")
   apply (intro conjI)
    apply (simp add: shiftl_t2n mult_ac)
    apply (erule(1) is_aligned_no_wrap')
   apply (simp add: add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply (simp add: shiftl_t2n mult_ac)
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (case_tac zombie_type)
   apply simp
   apply (rule div_lt_mult)
    apply (simp add: objBits_defs)
    apply (erule order_less_le_trans)
    apply (simp add: word_le_nat_alt)
    apply (subst le_unat_uoi[where z=5])
     apply simp+
  apply (simp add: objBits_simps' power_add mult.commute)
  apply (rule word_mult_less_mono1)
    apply (erule order_less_le_trans)
    apply (simp add: word_le_nat_alt)
    apply (subst le_unat_uoi)
     apply (subst unat_power_lower)
      prefer 2
      apply assumption
     apply (simp add: word_bits_def)
    apply (simp add: word_bits_def)
   apply simp
  apply (frule power_strict_increasing [where a="2 :: nat" and n="y + z" for y z])
   apply simp
  apply (simp only: power_add)
  apply (simp add: word_bits_def)
  done

lemma capBits_Master[CSpace_I_2_assms]:
  "capBits (capMasterCap cap) = capBits cap"
  by (clarsimp simp: capMasterCap_def split: capability.split arch_capability.split)

lemma capUntyped_Master[CSpace_I_2_assms]:
  "capUntypedPtr (capMasterCap cap) = capUntypedPtr cap"
  by (clarsimp simp: capMasterCap_def AARCH64_H.capUntypedPtr_def split: capability.split arch_capability.split)

lemma distinct_zombies_copyMasterE[CSpace_I_2_assms]:
  "\<lbrakk> distinct_zombies m; m x = Some cte;
     capClass (cteCap cte') = PhysicalClass
     \<Longrightarrow> capMasterCap (cteCap cte) = capMasterCap (cteCap cte');
     isZombie (cteCap cte') \<Longrightarrow> x = y \<rbrakk>
   \<Longrightarrow> distinct_zombies (m (y \<mapsto> cte'))"
  apply (erule(1) distinct_zombies_copyE, simp_all)
       apply (rule master_eqI, rule gen_isCap_Master, simp)
      apply (drule_tac f=isUntypedCap in arg_cong)
      apply (simp add: gen_isCap_Master)
     apply (drule_tac f=isArchFrameCap in arg_cong)
     apply (simp add: arch_isCap_Master)
    apply (rule master_eqI, rule capBits_Master, simp)
   apply clarsimp
   apply (drule_tac f=capClass in arg_cong, simp add: capClass_Master)
  apply (drule_tac f=capUntypedPtr in arg_cong, simp add: capUntyped_Master)
  done

lemmas distinct_zombies_sameMasterE
    = distinct_zombies_copyMasterE[where x=x and y=x for x, simplified,
                                   OF _ _ _]

declare distinct_zombies_sameMasterE[CSpace_I_2_assms]

lemma cap_table_at_gsCNodes[CSpace_I_2_assms]:
  "\<lbrakk> cap_table_at bits ptr s; (s, s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> gsCNodes s' ptr = Some bits"
  by (fastforce simp: state_relation_def ghost_relation_def obj_at_def is_cap_table)

end

interpretation CSpace_I_2?: CSpace_I_2 AARCH64.arch_capMasterCap AARCH64.arch_capBadge
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CSpace_I_2_assms)?)?)
qed

(* Arch constant definitions required to exist for sane locales in CSpace1_R *)

context Arch begin arch_global_naming

definition arch_mdb_preservation :: "capability \<Rightarrow> capability \<Rightarrow> bool" where
  "arch_mdb_preservation cap cap' \<equiv>
     isArchSGISignalCap cap' = isArchSGISignalCap cap \<and>
     (isArchSGISignalCap cap \<longrightarrow> cap' = cap) \<and>
     isArchSMCCap cap'  = isArchSMCCap cap \<and>
     (isArchSMCCap cap \<longrightarrow> cap' = cap)"

definition vs_cap_ref_arch' :: "arch_capability \<Rightarrow> (asid \<times> vspace_ref) option" where
  "vs_cap_ref_arch' acap \<equiv>
     case acap of
       ASIDPoolCap _ asid \<Rightarrow> Some (asid, 0)
     | ASIDControlCap \<Rightarrow> None
     | FrameCap _ _ _ _ m \<Rightarrow> m
     | PageTableCap _ _ m \<Rightarrow> m
     | _ \<Rightarrow> None"

lemmas vs_cap_ref_arch'_simps[simp] = vs_cap_ref_arch'_def[split_simps arch_capability.split]

definition
  "vs_cap_ref' = arch_cap'_fun_lift None vs_cap_ref_arch'"

lemmas vs_cap_ref'_simps[simp] =
  vs_cap_ref'_def[THEN fun_cong, unfolded arch_cap'_fun_lift_def, split_simps capability.split]

definition
  "capASID cap \<equiv> case cap of
     ArchObjectCap (FrameCap _ _ _ _ (Some (asid, _))) \<Rightarrow> Some asid
   | ArchObjectCap (PageTableCap _ _ (Some (asid, _))) \<Rightarrow> Some asid
   | _ \<Rightarrow> None"

lemmas capASID_simps[simp] =
  capASID_def[split_simps capability.split arch_capability.split option.split prod.split]

definition
  "cap_asid_base' cap \<equiv> case cap of
     ArchObjectCap (ASIDPoolCap _ asid) \<Rightarrow> Some asid
   | _ \<Rightarrow> None"

lemmas cap_asid_base'_simps[simp] =
  cap_asid_base'_def[split_simps capability.split arch_capability.split option.split prod.split]

definition
  "cap_vptr' cap \<equiv> case cap of
     ArchObjectCap (FrameCap _ _ _ _ (Some (_, vptr))) \<Rightarrow> Some vptr
   | ArchObjectCap (PageTableCap _ _ (Some (_, vptr))) \<Rightarrow> Some vptr
   | _ \<Rightarrow> None"

lemmas cap_vptr'_simps[simp] =
  cap_vptr'_def[split_simps capability.split arch_capability.split option.split prod.split]

definition
  "is_derived' m p cap' cap \<equiv>
  cap' \<noteq> NullCap \<and>
  \<not> isZombie cap \<and>
  \<not> isIRQControlCap cap' \<and>
  badge_derived' cap' cap \<and>
  (isUntypedCap cap \<longrightarrow> descendants_of' p m = {}) \<and>
  (isReplyCap cap = isReplyCap cap') \<and>
  (isReplyCap cap \<longrightarrow> capReplyMaster cap) \<and>
  (isReplyCap cap' \<longrightarrow> \<not> capReplyMaster cap') \<and>
  (vs_cap_ref' cap = vs_cap_ref' cap' \<or> isArchFrameCap cap) \<and>
  (isArchCap isPageTableCap cap \<longrightarrow> capASID cap = capASID cap' \<and> capASID cap \<noteq> None)"

end (* Arch *)

end (* of theory *)
