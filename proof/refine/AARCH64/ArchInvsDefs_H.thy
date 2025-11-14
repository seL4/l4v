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

declare lookupPTSlotFromLevel.simps[simp del]
declare lookupPTFromLevel.simps[simp del]

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

abbreviation pte_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pte_at' \<equiv> typ_at' (ArchT PTET)"

(* hyp_refs *)

definition tcb_vcpu_refs' :: "machine_word option \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_vcpu_refs' t \<equiv> set_option t \<times> {TCBHypRef}"

definition tcb_hyp_refs' :: "arch_tcb \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_hyp_refs' t \<equiv> tcb_vcpu_refs' (AARCH64_H.atcbVCPUPtr t)"

definition vcpu_tcb_refs' :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set" where
  "vcpu_tcb_refs' t \<equiv> set_option t \<times> {HypTCBRef}"

definition refs_of_a' :: "arch_kernel_object \<Rightarrow> (obj_ref \<times> reftype) set" where
  "refs_of_a' x \<equiv> case x of
     AARCH64_H.KOASIDPool asidpool \<Rightarrow> {}
   | AARCH64_H.KOPTE pte \<Rightarrow> {}
   | AARCH64_H.KOVCPU vcpu \<Rightarrow> vcpu_tcb_refs' (AARCH64_H.vcpuTCBPtr vcpu)"

definition arch_live' :: "arch_kernel_object \<Rightarrow> bool" where
  "arch_live' ao \<equiv> case ao of
     AARCH64_H.KOVCPU vcpu \<Rightarrow> bound (AARCH64_H.vcpuTCBPtr vcpu)
   | _ \<Rightarrow>  False"

definition hyp_live' :: "kernel_object \<Rightarrow> bool" where
  "hyp_live' ko \<equiv> case ko of
     (KOTCB tcb) \<Rightarrow> bound (AARCH64_H.atcbVCPUPtr (tcbArch tcb))
   | (KOArch ako) \<Rightarrow> arch_live' ako
   |  _ \<Rightarrow> False"

primrec azobj_refs' :: "arch_capability \<Rightarrow> obj_ref set" where
  "azobj_refs' (ASIDPoolCap _ _) = {}"
| "azobj_refs' ASIDControlCap = {}"
| "azobj_refs' (FrameCap _ _ _ _ _) = {}"
| "azobj_refs' (PageTableCap _ _ _) = {}"
| "azobj_refs' (VCPUCap v) = {v}"
| "azobj_refs' (SGISignalCap _ _) = {}"

lemma azobj_refs'_only_vcpu:
  "(x \<in> azobj_refs' acap) = (acap = VCPUCap x)"
  by (cases acap) auto


section "Valid caps and objects (design spec)"

definition isArchSGISignalCap :: "capability \<Rightarrow> bool" where
  "isArchSGISignalCap cap \<equiv> \<exists>irq target. cap = ArchObjectCap (SGISignalCap irq target)"

primrec acapBits :: "arch_capability \<Rightarrow> nat" where
  "acapBits (ASIDPoolCap _ _)       = asidLowBits + word_size_bits"
| "acapBits ASIDControlCap          = asidHighBits + word_size_bits"
| "acapBits (FrameCap _ _ sz _ _)   = pageBitsForSize sz"
| "acapBits (PageTableCap _ pt_t _) = table_size pt_t"
| "acapBits (VCPUCap v)             = vcpuBits"
| "acapBits (SGISignalCap _ _)      = 0"

definition page_table_at' :: "pt_type \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
 "page_table_at' pt_t p \<equiv> \<lambda>s.
    is_aligned p (ptBits pt_t) \<and>
    (\<forall>i \<le> mask (ptTranslationBits pt_t). pte_at' (p + (i << pte_bits)) s)"

lemmas vspace_table_at'_defs = page_table_at'_def

abbreviation asid_pool_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "asid_pool_at' \<equiv> typ_at' (ArchT ASIDPoolT)"

definition asid_wf :: "asid \<Rightarrow> bool" where
  "asid_wf asid \<equiv> asid \<le> mask asid_bits"

definition wellformed_mapdata' :: "asid \<times> vspace_ref \<Rightarrow> bool" where
  "wellformed_mapdata' \<equiv> \<lambda>(asid, vref). 0 < asid \<and> asid_wf asid \<and> vref \<in> user_region"

definition wellformed_acap' :: "arch_capability \<Rightarrow> bool" where
  "wellformed_acap' ac \<equiv>
   case ac of
     ASIDPoolCap r asid \<Rightarrow> is_aligned asid asid_low_bits \<and> asid_wf asid
   | FrameCap r rghts sz dev  mapdata \<Rightarrow>
       case_option True wellformed_mapdata' mapdata \<and>
       case_option True (swp vmsz_aligned sz \<circ> snd) mapdata
   | PageTableCap pt_t r (Some mapdata) \<Rightarrow> wellformed_mapdata' mapdata
   | _ \<Rightarrow> True"

lemmas wellformed_acap'_simps[simp] = wellformed_acap'_def[split_simps arch_capability.split]

definition frame_at' :: "obj_ref \<Rightarrow> vmpage_size \<Rightarrow> bool \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "frame_at' r sz dev s \<equiv>
     \<forall>p < 2 ^ (pageBitsForSize sz - pageBits).
       typ_at' (if dev then UserDataDeviceT else UserDataT) (r + (p << pageBits)) s"

definition valid_arch_cap_ref' :: "arch_capability \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_cap_ref' ac s \<equiv> case ac of
     ASIDPoolCap r as \<Rightarrow> typ_at' (ArchT ASIDPoolT) r s
   | ASIDControlCap \<Rightarrow> True
   | FrameCap r rghts sz dev mapdata \<Rightarrow> frame_at' r sz dev s
   | PageTableCap r pt_t mapdata \<Rightarrow> page_table_at' pt_t r s
   | VCPUCap r \<Rightarrow> vcpu_at' r s
   | SGISignalCap _ _ \<Rightarrow> True"

lemmas valid_arch_cap_ref'_simps[simp] =
  valid_arch_cap_ref'_def[split_simps arch_capability.split]

definition valid_arch_cap' :: "arch_capability \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_cap' cap \<equiv> \<lambda>s. wellformed_acap' cap \<and> valid_arch_cap_ref' cap s"

lemmas valid_arch_cap'_simps[simp] =
  valid_arch_cap'_def[unfolded wellformed_acap'_def valid_arch_cap_ref'_def,
                      split_simps arch_capability.split, simplified]

definition arch_valid_irq :: "irq \<Rightarrow> bool" where
  "arch_valid_irq irq \<equiv> irq \<le> maxIRQ"

(* within the Arch locale, we want automatic expansion of the valid irq conditions *)
lemmas [simp] = arch_valid_irq_def

definition is_device_frame_cap' :: "capability \<Rightarrow> bool" where
  "is_device_frame_cap' cap \<equiv> case cap of ArchObjectCap (FrameCap _ _ _ dev _) \<Rightarrow> dev | _ \<Rightarrow> False"

definition valid_arch_tcb' :: "Structures_H.arch_tcb \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_tcb' \<equiv> \<lambda>t s. \<forall>v. atcbVCPUPtr t = Some v \<longrightarrow> vcpu_at' v s "

definition valid_vcpu' :: "vcpu \<Rightarrow> bool" where
  "valid_vcpu' v \<equiv> case vcpuTCBPtr v of None \<Rightarrow> True | Some vt \<Rightarrow> is_aligned vt tcbBlockSizeBits"

(* This is a slight abuse of "canonical_address". What we really need to know for ADT_C in CRefine
   is that the top pageBits bits of TablePTEs have a known value, because we shift left by pageBits.
   What we actually know is that this is a physical address, so it is bound by the physical address
   space size, which depending on config can be 40, 44, or 48. 48 happens to also be the bound for
   the virtual address space, which canonical_address is for. This is good enough for our purposes. *)
definition ppn_bounded :: "pte \<Rightarrow> bool" where
  "ppn_bounded pte \<equiv> case pte of PageTablePTE ppn \<Rightarrow> canonical_address ppn | _ \<Rightarrow> True"

definition valid_arch_obj' :: "arch_kernel_object \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_obj' ako _ \<equiv> case ako of
     KOPTE pte \<Rightarrow> ppn_bounded pte
   | KOVCPU vcpu \<Rightarrow> valid_vcpu' vcpu
   | _ \<Rightarrow> True"

primrec
  acapClass :: "arch_capability \<Rightarrow> capclass"
where
  "acapClass (ASIDPoolCap _ _)    = PhysicalClass"
| "acapClass ASIDControlCap       = ASIDMasterClass"
| "acapClass (FrameCap _ _ _ _ _) = PhysicalClass"
| "acapClass (PageTableCap _ _ _) = PhysicalClass"
| "acapClass (VCPUCap _)          = PhysicalClass"
| "acapClass (SGISignalCap _ _)   = IRQClass"

definition valid_arch_badges :: "capability \<Rightarrow> capability \<Rightarrow> mdbnode \<Rightarrow> bool" where
  "valid_arch_badges cap cap' node' \<equiv>
     isArchSGISignalCap cap' \<longrightarrow> cap \<noteq> cap' \<longrightarrow> mdbFirstBadged node'"

definition mdb_chunked_arch_assms :: "capability \<Rightarrow> bool" where
  "mdb_chunked_arch_assms cap \<equiv> \<not>isArchSGISignalCap cap"

definition
  isArchFrameCap :: "capability \<Rightarrow> bool"
where
 "isArchFrameCap cap \<equiv> case cap of ArchObjectCap (FrameCap _ _ _ _ _) \<Rightarrow> True | _ \<Rightarrow> False"

(* Addresses of all PTEs in a VSRoot table at p *)
definition table_refs' :: "machine_word \<Rightarrow> machine_word set" where
  "table_refs' p \<equiv> (\<lambda>i. p + (i << pte_bits)) ` mask_range 0 (ptTranslationBits VSRootPT_T)"

definition global_refs' :: "kernel_state \<Rightarrow> obj_ref set" where
  "global_refs' \<equiv> \<lambda>s.
   {ksIdleThread s} \<union>
   table_refs' (armKSGlobalUserVSpace (ksArchState s)) \<union>
   range (\<lambda>irq :: irq. irq_node' s + (ucast irq << cteSizeBits))"

definition valid_asid_table' :: "(asid \<rightharpoonup> machine_word) \<Rightarrow> bool" where
  "valid_asid_table' table \<equiv> dom table \<subseteq> mask_range 0 asid_high_bits \<and> 0 \<notin> ran table"

definition "is_vcpu' \<equiv> \<lambda>ko. \<exists>vcpu. ko = (KOArch (KOVCPU vcpu))"

definition max_armKSGICVCPUNumListRegs :: nat where
  "max_armKSGICVCPUNumListRegs \<equiv> if config_ARM_GIC_V3 then 16 else 64"

definition valid_arch_state' :: "kernel_state \<Rightarrow> bool" where
  "valid_arch_state' \<equiv> \<lambda>s.
   valid_asid_table' (armKSASIDTable (ksArchState s)) \<and>
   0 \<notin> ran (armKSVMIDTable (ksArchState s)) \<and>
   (case armHSCurVCPU (ksArchState s) of
      Some (v, b) \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') v s
      | _ \<Rightarrow> True) \<and>
   armKSGICVCPUNumListRegs (ksArchState s) < max_armKSGICVCPUNumListRegs \<and>
   canonical_address (addrFromKPPtr (armKSGlobalUserVSpace (ksArchState s)))"

definition archMakeObjectT :: "arch_kernel_object_type \<Rightarrow> kernel_object" where
  "archMakeObjectT atp \<equiv>
     case atp
     of PTET \<Rightarrow> injectKO (makeObject :: pte)
      | ASIDPoolT \<Rightarrow> injectKO (makeObject :: asidpool)
      | VCPUT \<Rightarrow> injectKO (makeObject :: vcpu)"

end

(* Need to declare code equation outside Arch locale *)
declare AARCH64.max_armKSGICVCPUNumListRegs_def[code]

end
