(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* This theory contains the arch-dependent part of invariant definitions.
   Due to the large amount of definitions, we place it before Invariants_H rather than fixing
   constants in locales. *)

theory ArchInvsDefs_H
imports
  InvariantsPre_H
  ArchMove_R
begin

(* disambiguate name clash between Arch and non-arch definitions with same names *)
context Arch begin

lemmas haskell_crunch_def[crunch_def] =
  deriveCap_def finaliseCap_def
  hasCancelSendRights_def sameRegionAs_def isPhysicalCap_def
  sameObjectAs_def updateCapData_def maskCapRights_def
  createObject_def capUntypedPtr_def capUntypedSize_def
  performInvocation_def decodeInvocation_def

context begin global_naming global
requalify_facts (aliasing)
  Retype_H.deriveCap_def Retype_H.finaliseCap_def
  Retype_H.hasCancelSendRights_def Retype_H.sameRegionAs_def Retype_H.isPhysicalCap_def
  Retype_H.sameObjectAs_def Retype_H.updateCapData_def Retype_H.maskCapRights_def
  Retype_H.createObject_def Retype_H.capUntypedPtr_def Retype_H.capUntypedSize_def
  Retype_H.performInvocation_def Retype_H.decodeInvocation_def
end
end

context Arch begin arch_global_naming

definition canonical_address :: "machine_word \<Rightarrow> bool" where
  "canonical_address \<equiv> \<top>" \<comment> \<open>this concept does not exist on ARM_HYP\<close>

(* this architecture does not use kernel_mappings / pspace_in_kernel_mappings *)
definition kernel_mappings :: "machine_word set" where
  "kernel_mappings \<equiv> UNIV"

definition pspace_in_kernel_mappings' :: "kernel_state \<Rightarrow> bool" where
 "pspace_in_kernel_mappings' \<equiv> \<top>"

(* FIXME arch-split: if pspace_in_kernel_mappings becomes part of generic interface,
   check whether having this simp is still beneficial *)
lemmas [simp] = pspace_in_kernel_mappings'_def kernel_mappings_def

abbreviation vcpu_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "vcpu_at' \<equiv> typ_at' (ArchT VCPUT)"

abbreviation pde_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pde_at' \<equiv> typ_at' (ArchT PDET)"
abbreviation pte_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pte_at' \<equiv> typ_at' (ArchT PTET)"

(* hyp_refs *)

definition tcb_vcpu_refs' :: "machine_word option \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_vcpu_refs' t \<equiv> set_option t \<times> {TCBHypRef}"

definition tcb_hyp_refs' :: "arch_tcb \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_hyp_refs' t \<equiv> tcb_vcpu_refs' (ARM_HYP_H.atcbVCPUPtr t)"

definition vcpu_tcb_refs' :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set" where
  "vcpu_tcb_refs' t \<equiv> set_option t \<times> {HypTCBRef}"

definition refs_of_a' :: "arch_kernel_object \<Rightarrow> (obj_ref \<times> reftype) set" where
  "refs_of_a' x \<equiv> case x of
     ARM_HYP_H.KOASIDPool _ \<Rightarrow> {}
   | ARM_HYP_H.KOPDE _ \<Rightarrow> {}
   | ARM_HYP_H.KOPTE _ \<Rightarrow> {}
   | ARM_HYP_H.KOVCPU vcpu \<Rightarrow> vcpu_tcb_refs' (ARM_HYP_H.vcpuTCBPtr vcpu)"

definition arch_live' :: "arch_kernel_object \<Rightarrow> bool" where
  "arch_live' ao \<equiv> case ao of
     ARM_HYP_H.KOVCPU vcpu \<Rightarrow> bound (ARM_HYP_H.vcpuTCBPtr vcpu)
   | _ \<Rightarrow>  False"

definition hyp_live' :: "kernel_object \<Rightarrow> bool" where
  "hyp_live' ko \<equiv> case ko of
     (KOTCB tcb) \<Rightarrow> bound (ARM_HYP_H.atcbVCPUPtr (tcbArch tcb))
   | (KOArch ako) \<Rightarrow> arch_live' ako
   |  _ \<Rightarrow> False"

primrec azobj_refs' :: "arch_capability \<Rightarrow> obj_ref set" where
  "azobj_refs' (ASIDPoolCap _ _) = {}"
| "azobj_refs' ASIDControlCap = {}"
| "azobj_refs' (PageCap _ _ _ _ _) = {}"
| "azobj_refs' (PageTableCap _ _) = {}"
| "azobj_refs' (PageDirectoryCap _ _) = {}"
| "azobj_refs' (VCPUCap v) = {v}"
| "azobj_refs' (SGISignalCap _ _) = {}"

lemma azobj_refs'_only_vcpu:
  "(x \<in> azobj_refs' acap) = (acap = VCPUCap x)"
  by (cases acap) auto


section "Valid caps and objects (design spec)"

definition isArchSGISignalCap :: "capability \<Rightarrow> bool" where
  "isArchSGISignalCap cap \<equiv> \<exists>irq target. cap = ArchObjectCap (SGISignalCap irq target)"

primrec acapBits :: "arch_capability \<Rightarrow> nat" where
  "acapBits (ASIDPoolCap x y) = asidLowBits + 2"
| "acapBits ASIDControlCap = asidHighBits + 2"
| "acapBits (PageCap d x y sz z) = pageBitsForSize sz"
| "acapBits (PageTableCap x y) = 12"
| "acapBits (PageDirectoryCap x y) = 14"
| "acapBits (VCPUCap v) = 12"
| "acapBits (SGISignalCap _ _) = 0"

definition page_table_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "page_table_at' x \<equiv> \<lambda>s. is_aligned x ptBits
                          \<and> (\<forall>y < 2 ^ 9. typ_at' (ArchT PTET) (x + (y << 3)) s)"

definition page_directory_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "page_directory_at' x \<equiv> \<lambda>s. is_aligned x pdBits
                              \<and> (\<forall>y < 2 ^ 11. typ_at' (ArchT PDET) (x + (y << 3)) s)"

lemmas vspace_table_at'_defs = page_table_at'_def page_directory_at'_def

abbreviation asid_pool_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "asid_pool_at' \<equiv> typ_at' (ArchT ASIDPoolT)"

(* FIXME: duplicated with vmsz_aligned *)
definition
  "vmsz_aligned' ref sz \<equiv> is_aligned ref (pageBitsForSize sz)"

definition valid_arch_cap' :: "arch_capability \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_cap' acap s \<equiv> case acap
   of ASIDPoolCap pool asid \<Rightarrow>
      typ_at' (ArchT ASIDPoolT) pool s \<and> is_aligned asid asid_low_bits \<and> asid \<le> 2^asid_bits - 1
    | ASIDControlCap \<Rightarrow> True
    | PageCap d ref rghts sz mapdata \<Rightarrow> ref \<noteq> 0 \<and>
      (\<forall>p < 2 ^ (pageBitsForSize sz - pageBits). typ_at' (if d then UserDataDeviceT else UserDataT)
      (ref + p * 2 ^ pageBits) s) \<and>
      (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow>
              0 < asid \<and> asid \<le> 2 ^ asid_bits - 1 \<and> vmsz_aligned' ref sz \<and> ref < pptrBase) \<and>
      rghts \<noteq> VMNoAccess
    | PageTableCap ref mapdata \<Rightarrow>
      page_table_at' ref s \<and>
      (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow>
              0 < asid \<and> asid \<le> 2^asid_bits - 1 \<and> ref < pptrBase)
    | PageDirectoryCap ref mapdata \<Rightarrow>
      page_directory_at' ref s \<and>
      case_option True (\<lambda>asid. 0 < asid \<and> asid \<le> 2^asid_bits - 1) mapdata
    | VCPUCap v \<Rightarrow> vcpu_at' v s
    | SGISignalCap _ _ \<Rightarrow> True"

lemmas valid_arch_cap'_simps[simp] =
  valid_arch_cap'_def[split_simps arch_capability.split, simplified]

definition arch_valid_irq :: "irq \<Rightarrow> bool" where
  "arch_valid_irq irq \<equiv> irq \<le> maxIRQ"

(* within the Arch locale, we want automatic expansion of the valid irq conditions *)
lemmas [simp] = arch_valid_irq_def

definition valid_arch_tcb' :: "Structures_H.arch_tcb \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_tcb' \<equiv> \<lambda>t s. \<forall>v. atcbVCPUPtr t = Some v \<longrightarrow> vcpu_at' v s "

definition valid_mapping' :: "word32 \<Rightarrow> vmpage_size \<Rightarrow> bool" where
 "valid_mapping' x sz \<equiv> is_aligned x (pageBitsForSize sz)
                        \<and> ptrFromPAddr x \<noteq> 0"

primrec valid_pte' :: "ARM_HYP_H.pte \<Rightarrow> bool" where
  "valid_pte' (InvalidPTE) = True"
  (* The first LargePagePTE is aligned to ARMLargePage, all other `duplicates' to ARMSmallPage.
     The former is only stated in the abstract spec invariants, not here. *)
| "valid_pte' (LargePagePTE ptr _ _ r) = (valid_mapping' ptr ARMSmallPage \<and> r \<noteq> VMNoAccess)"
| "valid_pte' (SmallPagePTE ptr _ _ r) = (valid_mapping' ptr ARMSmallPage \<and> r \<noteq> VMNoAccess)"

primrec valid_pde' :: "ARM_HYP_H.pde \<Rightarrow> bool" where
  "valid_pde' (InvalidPDE) = True"
| "valid_pde' (SectionPDE ptr _ _ r) = (valid_mapping' ptr ARMSection \<and> r \<noteq> VMNoAccess)"
  (* The first SuperSectionPDE is aligned to ARMSuperSection, all other `duplicates' to ARMSection.
     The former is only stated in the abstract spec invariants, not here. *)
| "valid_pde' (SuperSectionPDE ptr _ _ r) = (valid_mapping' ptr ARMSection \<and> r \<noteq> VMNoAccess)"
| "valid_pde' (PageTablePDE ptr) = is_aligned ptr ptBits"

primrec valid_asid_pool' :: "asidpool \<Rightarrow> bool" where
  "valid_asid_pool' (ASIDPool pool)
     = (dom pool \<subseteq> {0 .. 2^asid_low_bits - 1}
        \<and> 0 \<notin> ran pool \<and> (\<forall>x \<in> ran pool. is_aligned x pdBits))"

definition valid_vcpu' :: "vcpu \<Rightarrow> bool" where
  "valid_vcpu' v \<equiv> case vcpuTCBPtr v of None \<Rightarrow> True | Some vt \<Rightarrow> is_aligned vt tcbBlockSizeBits"

primrec valid_arch_obj' :: "arch_kernel_object \<Rightarrow> bool" where
  "valid_arch_obj' (KOASIDPool pool) = valid_asid_pool' pool"
| "valid_arch_obj' (KOPDE pde) = valid_pde' pde"
| "valid_arch_obj' (KOPTE pte) = valid_pte' pte"
| "valid_arch_obj' (KOVCPU vcpu) = valid_vcpu' vcpu"

primrec acapClass :: "arch_capability \<Rightarrow> capclass" where
  "acapClass (ASIDPoolCap x y)      = PhysicalClass"
| "acapClass ASIDControlCap         = ASIDMasterClass"
| "acapClass (PageCap d x y sz z)   = PhysicalClass"
| "acapClass (PageTableCap x y)     = PhysicalClass"
| "acapClass (PageDirectoryCap x y) = PhysicalClass"
| "acapClass (VCPUCap x)            = PhysicalClass"
| "acapClass (SGISignalCap _ _ )    = IRQClass"

definition valid_arch_badges :: "capability \<Rightarrow> capability \<Rightarrow> mdbnode \<Rightarrow> bool" where
  "valid_arch_badges cap cap' node' \<equiv>
     isArchSGISignalCap cap' \<longrightarrow> cap \<noteq> cap' \<longrightarrow> mdbFirstBadged node'"

definition mdb_chunked_arch_assms :: "capability \<Rightarrow> bool" where
  "mdb_chunked_arch_assms cap \<equiv> \<not>isArchSGISignalCap cap"

definition isArchFrameCap :: "capability \<Rightarrow> bool" where
 "isArchFrameCap cap \<equiv> case cap of ArchObjectCap (PageCap _ _ _ _ _) \<Rightarrow> True | _ \<Rightarrow> False"

(* FIXME arch-split: compatibility shim, can be removed by arch-wide rename *)
abbreviation (input)
  "isArchPageCap \<equiv> isArchFrameCap"

lemmas isArchPageCap_def = isArchFrameCap_def

definition page_directory_refs' :: "word32 \<Rightarrow> word32 set" where
  "page_directory_refs' x \<equiv> (\<lambda>y. x + (y << 3)) ` {y. y < 2 ^ 11}"

definition page_table_refs' :: "word32 \<Rightarrow> word32 set" where
  "page_table_refs' x \<equiv> (\<lambda>y. x + (y << 3)) ` {y. y < 2 ^ 9}"

definition global_refs' :: "kernel_state \<Rightarrow> obj_ref set" where
  "global_refs' \<equiv> \<lambda>s.
  {ksIdleThread s, armUSGlobalPD (ksArchState s)} \<union>
   range (\<lambda>irq :: irq. irq_node' s + 16 * ucast irq)"

definition valid_asid_table' :: "(asid \<rightharpoonup> word32) \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_asid_table' table \<equiv> \<lambda>s. dom table \<subseteq> {0 .. 2^asid_high_bits - 1}
                                 \<and> 0 \<notin> ran table"

definition valid_global_pts' :: "word32 list \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_global_pts' pts \<equiv> \<lambda>s. \<forall>p \<in> set pts. page_table_at' p s"

definition valid_asid_map' :: "(word32 \<rightharpoonup> word8 \<times> word32) \<Rightarrow> bool" where
 "valid_asid_map' m \<equiv> inj_on (option_map snd o m) (dom m)
                      \<and> dom m \<subseteq> ({0 .. mask asid_bits} - {0})"

definition
  "pt_index_bits \<equiv> pt_bits - pte_bits"

lemmas vspace_bits_defs = vspace_bits_defs pt_index_bits_def

definition pd_asid_slot :: word32 where
 "pd_asid_slot \<equiv> 0xff000000 >> (pt_index_bits + pageBits)"

(* ideally, all mappings above kernel_base are global and kernel-only, and
   of them one particular mapping is clear. at the moment all we can easily say
   is that the mapping is clear. *)
definition valid_pde_mapping_offset' :: "word32 \<Rightarrow> bool" where
 "valid_pde_mapping_offset' offset \<equiv> offset \<noteq> (pd_asid_slot << pte_bits)"

definition valid_pde_mapping' :: "word32 \<Rightarrow> pde \<Rightarrow> bool" where
 "valid_pde_mapping' offset pde \<equiv> pde = InvalidPDE \<or> valid_pde_mapping_offset' offset"

definition valid_pde_mappings' :: "kernel_state \<Rightarrow> bool" where
  "valid_pde_mappings' \<equiv> \<lambda>s.
     \<forall>x pde. ko_at' pde x s
          \<longrightarrow> valid_pde_mapping' (x && mask pdBits) pde"

definition "is_vcpu' \<equiv> \<lambda>ko. \<exists>vcpu. ko = (KOArch (KOVCPU vcpu))"

definition max_armKSGICVCPUNumListRegs :: nat where
  "max_armKSGICVCPUNumListRegs \<equiv> 63"

definition valid_arch_state' :: "kernel_state \<Rightarrow> bool" where
  "valid_arch_state' \<equiv> \<lambda>s.
    valid_asid_table' (armKSASIDTable (ksArchState s)) s \<and>
    (case (armHSCurVCPU (ksArchState s)) of Some (v, b) \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') v s | _ \<Rightarrow> True) \<and>
    is_inv (armKSHWASIDTable (ksArchState s))
              (option_map fst o armKSASIDMap (ksArchState s)) \<and>
    valid_asid_map' (armKSASIDMap (ksArchState s)) \<and>
    armKSGICVCPUNumListRegs (ksArchState s) \<le> max_armKSGICVCPUNumListRegs \<and>
    valid_pde_mappings' s"

definition archMakeObjectT :: "arch_kernel_object_type \<Rightarrow> kernel_object" where
  "archMakeObjectT atp \<equiv>
     case atp
     of PDET \<Rightarrow> injectKO (makeObject :: pte)
      | PTET \<Rightarrow> injectKO (makeObject :: pte)
      | ASIDPoolT \<Rightarrow> injectKO (makeObject :: asidpool)
      | VCPUT \<Rightarrow> injectKO (makeObject :: vcpu)"


section "Misc properties not directly included in invariants"

definition
  "isSuperSection pde \<equiv> case pde of SuperSectionPDE _ _ _ _ \<Rightarrow> True | _ \<Rightarrow> False"

definition
  "isLargePage pte \<equiv> case pte of LargePagePTE _ _ _ _ \<Rightarrow> True | _ \<Rightarrow> False"

definition
  "valid_pde_duplicates_at' \<equiv> \<lambda>h p.
    \<exists>pde. h p = Some (KOArch (KOPDE pde)) \<and> isSuperSection pde \<and>
          vmsz_aligned (pdeFrame pde) ARMSuperSection \<and>
          (\<forall>(p',i) \<in> set (zip superSectionPDEOffsets [0.e.15]).
              h (p + p') = Some (KOArch (KOPDE (addPDEOffset pde i))))"

definition
  "valid_pte_duplicates_at' \<equiv> \<lambda>h p.
    \<exists>pte. h p = Some (KOArch (KOPTE pte)) \<and> isLargePage pte \<and>
          vmsz_aligned (pteFrame pte) ARMLargePage \<and>
          (\<forall>(p',i) \<in> set (zip largePagePTEOffsets [0.e.15]).
              h (p + p') = Some (KOArch (KOPTE (addPTEOffset pte i))))"

definition vs_valid_duplicates' where
  "vs_valid_duplicates' \<equiv> \<lambda>h. \<forall>x::32 word.
     case h x of
       Some (KOArch (KOPTE pte)) \<Rightarrow>
            isLargePage pte \<longrightarrow> valid_pte_duplicates_at' h (x && ~~ mask (pte_bits + 4))
     | Some (KOArch (KOPDE pde)) \<Rightarrow>
            isSuperSection pde \<longrightarrow> valid_pde_duplicates_at' h (x && ~~ mask (pde_bits + 4))
     | _ \<Rightarrow> True"

end
end
