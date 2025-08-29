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

definition pspace_in_kernel_mappings' :: "kernel_state \<Rightarrow> bool" where
  "pspace_in_kernel_mappings' s \<equiv> \<forall>p \<in> dom (ksPSpace s). p \<in> kernel_mappings"

abbreviation pte_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pte_at' \<equiv> typ_at' (ArchT PTET)"

(* hyp_refs *)

definition tcb_hyp_refs' :: "arch_tcb \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_hyp_refs' t \<equiv> {}" \<comment> \<open>no VCPUs on this architecture\<close>

definition refs_of_a' :: "arch_kernel_object \<Rightarrow> (obj_ref \<times> reftype) set" where
  "refs_of_a' x \<equiv> {}"

definition arch_live' :: "arch_kernel_object \<Rightarrow> bool" where
  "arch_live' ao \<equiv> False"

definition hyp_live' :: "kernel_object \<Rightarrow> bool" where
  "hyp_live' ko \<equiv> False"

definition azobj_refs' :: "arch_capability \<Rightarrow> obj_ref set" where
  "azobj_refs' _ = {}"

(* FIXME arch-split: might need to add more here, non-arch-split RISCV64 proofs don't know these yet *)
lemmas [simp] = refs_of_a'_def azobj_refs'_def


section "Valid caps and objects (design spec)"

primrec acapBits :: "arch_capability \<Rightarrow> nat" where
  "acapBits (ASIDPoolCap _ _)     = asidLowBits + word_size_bits"
| "acapBits ASIDControlCap        = asidHighBits + word_size_bits"
| "acapBits (FrameCap _ _ sz _ _) = pageBitsForSize sz"
| "acapBits (PageTableCap _ _)    = table_size"

definition page_table_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
 "page_table_at' p \<equiv> \<lambda>s.
    is_aligned p ptBits \<and> (\<forall>i::pt_index. pte_at' (p + (ucast i << pte_bits)) s)"

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
   | PageTableCap r (Some mapdata) \<Rightarrow> wellformed_mapdata' mapdata
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
   | PageTableCap r mapdata \<Rightarrow> page_table_at' r s"

lemmas valid_arch_cap_ref'_simps[simp] =
  valid_arch_cap_ref'_def[split_simps arch_capability.split]

definition valid_arch_cap' :: "arch_capability \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_cap' cap \<equiv> \<lambda>s. wellformed_acap' cap \<and> valid_arch_cap_ref' cap s"

lemmas valid_arch_cap'_simps[simp] =
  valid_arch_cap'_def[unfolded wellformed_acap'_def valid_arch_cap_ref'_def,
                      split_simps arch_capability.split, simplified]

definition arch_cap'_fun_lift :: "(arch_capability \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> capability \<Rightarrow> 'a" where
  "arch_cap'_fun_lift P F c \<equiv> case c of ArchObjectCap ac \<Rightarrow> P ac | _ \<Rightarrow> F"

lemmas arch_cap'_fun_lift_simps[simp] = arch_cap'_fun_lift_def[split_simps capability.split]

(* on RISCV64, there is an invalid IRQ within the bound of maxIRQ *)
definition arch_valid_irq :: "irq \<Rightarrow> bool" where
  "arch_valid_irq irq \<equiv> irq \<le> maxIRQ \<and> irq \<noteq> irqInvalid"

(* within the Arch locale, we want automatic expansion of the valid irq conditions *)
lemmas [simp] = arch_valid_irq_def

definition is_device_frame_cap' :: "capability \<Rightarrow> bool" where
  "is_device_frame_cap' cap \<equiv> case cap of ArchObjectCap (FrameCap _ _ _ dev _) \<Rightarrow> dev | _ \<Rightarrow> False"

definition valid_arch_tcb' :: "Structures_H.arch_tcb \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_tcb' \<equiv> \<lambda>t. \<top>"

definition valid_arch_obj' :: "arch_kernel_object \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_obj' ako _ \<equiv> case ako of
     _ \<Rightarrow> True"

primrec
  acapClass :: "arch_capability \<Rightarrow> capclass"
where
  "acapClass (ASIDPoolCap _ _)    = PhysicalClass"
| "acapClass ASIDControlCap       = ASIDMasterClass"
| "acapClass (FrameCap _ _ _ _ _) = PhysicalClass"
| "acapClass (PageTableCap _ _)   = PhysicalClass"

definition
  isArchFrameCap :: "capability \<Rightarrow> bool"
where
 "isArchFrameCap cap \<equiv> case cap of ArchObjectCap (FrameCap _ _ _ _ _) \<Rightarrow> True | _ \<Rightarrow> False"

(* Addresses of all PTEs in a VSRoot table at p *)
definition table_refs' :: "machine_word \<Rightarrow> machine_word set" where
  "table_refs' x \<equiv> (\<lambda>y. x + (y << pte_bits)) ` mask_range 0 ptTranslationBits"

definition global_refs' :: "kernel_state \<Rightarrow> obj_ref set" where
  "global_refs' \<equiv> \<lambda>s.
   {ksIdleThread s, idle_sc_ptr} \<union>
   (\<Union>l. (\<Union> (table_refs' ` set (riscvKSGlobalPTs (ksArchState s) l)))) \<union>
   range (\<lambda>irq :: irq. irq_node' s + (ucast irq << cteSizeBits))"

definition valid_asid_table' :: "(asid \<rightharpoonup> machine_word) \<Rightarrow> bool" where
  "valid_asid_table' table \<equiv> dom table \<subseteq> mask_range 0 asid_high_bits \<and> 0 \<notin> ran table"


definition valid_global_pts' :: "machine_word list \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_global_pts' pts \<equiv> \<lambda>s. \<forall>p \<in> set pts. page_table_at' p s"

definition valid_arch_state' :: "kernel_state \<Rightarrow> bool" where
  "valid_arch_state' \<equiv> \<lambda>s.
   valid_asid_table' (riscvKSASIDTable (ksArchState s)) \<and>
   (\<forall>l. valid_global_pts' (riscvKSGlobalPTs (ksArchState s) l) s) \<and>
   riscvKSGlobalPTs (ksArchState s) maxPTLevel \<noteq> []"

definition archMakeObjectT :: "arch_kernel_object_type \<Rightarrow> kernel_object" where
  "archMakeObjectT atp \<equiv>
     case atp
     of PTET \<Rightarrow> injectKO (makeObject :: pte)
      | ASIDPoolT \<Rightarrow> injectKO (makeObject :: asidpool)"

end
end
