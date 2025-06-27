(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   The refinement relation between abstract and concrete states - architecture-specific definitions.
*)

theory ArchStateRelation
imports StateRelationPre
begin

context Arch begin arch_global_naming

primrec arch_fault_map :: "Machine_A.AARCH64_A.arch_fault \<Rightarrow> arch_fault" where
  "arch_fault_map (Machine_A.AARCH64_A.VMFault ptr msg) = VMFault ptr msg"
| "arch_fault_map (Machine_A.AARCH64_A.VGICMaintenance datalist) = VGICMaintenance datalist "
| "arch_fault_map (Machine_A.AARCH64_A.VPPIEvent irq) = VPPIEvent irq"
| "arch_fault_map (Machine_A.AARCH64_A.VCPUFault data) = VCPUFault data"

definition vmrights_map :: "rights set \<Rightarrow> vmrights" where
  "vmrights_map S \<equiv> if AllowRead \<in> S
                    then (if AllowWrite \<in> S then VMReadWrite else VMReadOnly)
                    else VMKernelOnly"

definition mdata_map ::
  "(Machine_A.AARCH64_A.asid \<times> vspace_ref) option \<Rightarrow> (asid \<times> vspace_ref) option" where
  "mdata_map = map_option (\<lambda>(asid, ref). (ucast asid, ref))"

primrec acap_relation :: "arch_cap \<Rightarrow> arch_capability \<Rightarrow> bool" where
  "acap_relation (arch_cap.ASIDPoolCap p asid) c =
     (c = ASIDPoolCap p (ucast asid))"
| "acap_relation (arch_cap.ASIDControlCap) c =
     (c = ASIDControlCap)"
| "acap_relation (arch_cap.FrameCap p rghts sz dev data) c =
     (c = FrameCap p (vmrights_map rghts) sz dev (mdata_map data))"
| "acap_relation (arch_cap.PageTableCap p pt_t data) c =
     (c = PageTableCap p pt_t (mdata_map data))"
| "acap_relation (arch_cap.VCPUCap vcpu) c  = (c =
        arch_capability.VCPUCap vcpu)"

definition abs_asid_entry :: "asidpool_entry \<Rightarrow> asid_pool_entry" where
  "abs_asid_entry ap = AARCH64_A.ASIDPoolVSpace (apVMID ap) (apVSpace ap)"

definition asid_pool_relation :: "asid_pool \<Rightarrow> asidpool \<Rightarrow> bool" where
  "asid_pool_relation \<equiv> \<lambda>p p'. p = map_option abs_asid_entry \<circ> inv ASIDPool p' \<circ> ucast"

lemma inj_ASIDPool[simp]:
  "inj ASIDPool"
  by (auto intro: injI)

lemma asid_pool_relation_def':
  "asid_pool_relation ap (ASIDPool ap') =
    (\<forall>asid_low. ap asid_low = map_option abs_asid_entry (ap' (ucast asid_low)))"
  by (auto simp add: asid_pool_relation_def)

definition vgic_map :: "gic_vcpu_interface \<Rightarrow> gicvcpuinterface" where
  "vgic_map \<equiv> \<lambda>v. VGICInterface (vgic_hcr v) (vgic_vmcr v) (vgic_apr v) (vgic_lr v)"

definition vcpu_relation :: "AARCH64_A.vcpu \<Rightarrow> vcpu \<Rightarrow> bool" where
  "vcpu_relation \<equiv> \<lambda>v v'. vcpu_tcb v = vcpuTCBPtr v' \<and>
                           vgic_map (vcpu_vgic v) = vcpuVGIC v' \<and>
                           vcpu_regs v = vcpuRegs v' \<and>
                           vcpu_vppi_masked v = vcpuVPPIMasked v' \<and>
                           vcpu_vtimer v = vcpuVTimer v'"

definition arch_tcb_relation :: "Structures_A.arch_tcb \<Rightarrow> Structures_H.arch_tcb \<Rightarrow> bool" where
  "arch_tcb_relation \<equiv>
     \<lambda>atcb atcb'. tcb_context atcb = atcbContext atcb' \<and> tcb_vcpu atcb = atcbVCPUPtr atcb'"

primrec pte_relation' :: "AARCH64_A.pte \<Rightarrow> AARCH64_H.pte \<Rightarrow> bool" where
  "pte_relation' AARCH64_A.InvalidPTE x =
     (x = AARCH64_H.InvalidPTE)"
| "pte_relation' (AARCH64_A.PageTablePTE ppn) x =
     (x = AARCH64_H.PageTablePTE (ucast ppn))"
| "pte_relation' (AARCH64_A.PagePTE page_addr is_small attrs rights) x =
     (x = AARCH64_H.PagePTE page_addr is_small (Global \<in> attrs) (Execute \<notin> attrs) (Device \<in> attrs)
                            (vmrights_map rights))"

definition pte_relation :: "machine_word \<Rightarrow> Structures_A.kernel_object \<Rightarrow> kernel_object \<Rightarrow> bool" where
 "pte_relation y \<equiv> \<lambda>ko ko'. \<exists>pt pte. ko = ArchObj (PageTable pt) \<and> ko' = KOArch (KOPTE pte)
                                      \<and> pte_relation' (pt_apply pt y) pte"

(* this is the arch version of other_obj_relation *)
definition
  other_aobj_relation :: "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "other_aobj_relation obj obj' \<equiv>
   (case (obj, obj') of
      (ArchObj (AARCH64_A.ASIDPool ap), KOArch (KOASIDPool ap')) \<Rightarrow> asid_pool_relation ap ap'
    | (ArchObj (AARCH64_A.VCPU vcpu), KOArch (KOVCPU vcpu')) \<Rightarrow> vcpu_relation vcpu vcpu'
    | _ \<Rightarrow> False)"

primrec aobj_relation_cuts :: "AARCH64_A.arch_kernel_obj \<Rightarrow> machine_word \<Rightarrow> obj_relation_cuts" where
  "aobj_relation_cuts (DataPage dev sz) x =
     { (x + (n << pageBits), \<lambda>_ obj. obj = (if dev then KOUserDataDevice else KOUserData))
       | n. n < 2 ^ (pageBitsForSize sz - pageBits) }"
| "aobj_relation_cuts (AARCH64_A.ASIDPool pool) x =
     {(x, other_aobj_relation)}"
| "aobj_relation_cuts (PageTable pt) x =
     (\<lambda>y. (x + (y << pteBits), pte_relation y)) ` {0..mask (ptTranslationBits (pt_type pt))}"
| "aobj_relation_cuts (AARCH64_A.VCPU v) x =
     {(x, other_aobj_relation)}"

definition is_other_obj_relation_type :: "a_type \<Rightarrow> bool" where
 "is_other_obj_relation_type tp \<equiv>
    case tp of
      ACapTable n \<Rightarrow> False
    | ATCB \<Rightarrow> False
    | AArch (APageTable _) \<Rightarrow> False
    | AArch (AUserData _) \<Rightarrow> False
    | AArch (ADeviceData _) \<Rightarrow> False
    | AGarbage _ \<Rightarrow> False
    | _ \<Rightarrow> True"

definition ghost_relation ::
  "Structures_A.kheap \<Rightarrow> (machine_word \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<rightharpoonup> nat) \<Rightarrow> (machine_word \<rightharpoonup> pt_type) \<Rightarrow> bool" where
  "ghost_relation h ups cns pt_types \<equiv>
     (\<forall>a sz. (\<exists>dev. h a = Some (ArchObj (DataPage dev sz))) \<longleftrightarrow> ups a = Some sz) \<and>
     (\<forall>a n. (\<exists>cs. h a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow> cns a = Some n) \<and>
     (\<forall>a pt_t. (\<exists>pt. h a = Some (ArchObj (PageTable pt)) \<and> pt_t = pt_type pt) \<longleftrightarrow> pt_types a = Some pt_t)"

(* FIXME arch-split: provided only so that ghost_relation can be used within generic definition
   of state_relation (since arch_state_relation doesn't have access to kheap, and
   gsPTTypes on AARCH64 isn't generic) *)
definition ghost_relation_wrapper :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ghost_relation_wrapper s s' \<equiv>
     ghost_relation (kheap s) (gsUserPages s') (gsCNodes s') (gsPTTypes (ksArchState s'))"

(* inside Arch locale, we have no need for the wrapper *)
lemmas [simp] = ghost_relation_wrapper_def

definition arch_state_relation :: "(arch_state \<times> AARCH64_H.kernel_state) set" where
  "arch_state_relation \<equiv> {(s, s') .
         arm_asid_table s = armKSASIDTable s' \<circ> ucast
         \<and> arm_us_global_vspace s = armKSGlobalUserVSpace s'
         \<and> arm_next_vmid s = armKSNextVMID s'
         \<and> map_option ucast \<circ> arm_vmid_table s = armKSVMIDTable s'
         \<and> arm_kernel_vspace s = armKSKernelVSpace s'
         \<and> arm_current_vcpu s = armHSCurVCPU s'
         \<and> arm_gicvcpu_numlistregs s = armKSGICVCPUNumListRegs s'
         \<and> arm_current_fpu_owner s = armKSCurFPUOwner s'}"

end

end
