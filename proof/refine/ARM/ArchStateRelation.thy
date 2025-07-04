(*
 * Copyright 2014, General Dynamics C4 Systems
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

primrec arch_fault_map :: "Machine_A.ARM_A.arch_fault \<Rightarrow> ArchFault_H.ARM_H.arch_fault" where
 "arch_fault_map (Machine_A.ARM_A.VMFault ptr msg) = ArchFault_H.ARM_H.VMFault ptr msg"

definition vmrights_map :: "rights set \<Rightarrow> vmrights" where
 "vmrights_map S \<equiv> if AllowRead \<in> S
                   then (if AllowWrite \<in> S then VMReadWrite else VMReadOnly)
                   else VMKernelOnly"

primrec acap_relation :: "arch_cap \<Rightarrow> arch_capability \<Rightarrow> bool" where
  "acap_relation (arch_cap.ASIDPoolCap x y) c             = (c =
        arch_capability.ASIDPoolCap x y)"
| "acap_relation (arch_cap.ASIDControlCap) c              = (c =
        arch_capability.ASIDControlCap)"
| "acap_relation (arch_cap.PageCap dev word rghts sz data) c  = (c =
        arch_capability.PageCap dev word (vmrights_map rghts) sz data)"
| "acap_relation (arch_cap.PageTableCap word data) c      = (c =
        arch_capability.PageTableCap word data)"
| "acap_relation (arch_cap.PageDirectoryCap word data) c  = (c =
        arch_capability.PageDirectoryCap word data)"
| "acap_relation (arch_cap.SGISignalCap irq target) c  = (c =
        arch_capability.SGISignalCap (ucast irq) (ucast target))"

definition asid_pool_relation :: "(10 word \<rightharpoonup> word32) \<Rightarrow> asidpool \<Rightarrow> bool" where
  "asid_pool_relation \<equiv> \<lambda>p p'. p = inv ASIDPool p' o ucast"

definition arch_tcb_relation :: "Structures_A.arch_tcb \<Rightarrow> Structures_H.arch_tcb \<Rightarrow> bool" where
 "arch_tcb_relation \<equiv> \<lambda>atcb atcb'.
   tcb_context atcb = atcbContext atcb'"

primrec
   pde_relation' :: "ARM_A.pde \<Rightarrow> ARM_H.pde \<Rightarrow> bool"
where
  "pde_relation'  ARM_A.InvalidPDE x = (x = ARM_H.InvalidPDE)"
| "pde_relation' (ARM_A.PageTablePDE ptr atts domain) x
      = (x = ARM_H.PageTablePDE ptr (ParityEnabled \<in> atts) domain)"
| "pde_relation' (ARM_A.SectionPDE ptr atts domain rghts) x
      = (x = ARM_H.SectionPDE ptr (ParityEnabled \<in> atts) domain
               (PageCacheable \<in> atts) (Global \<in> atts) (XNever \<in> atts) (vmrights_map rghts))"
| "pde_relation' (ARM_A.SuperSectionPDE ptr atts rghts) x
      = (x = ARM_H.SuperSectionPDE ptr (ParityEnabled \<in> atts)
               (PageCacheable \<in> atts) (Global \<in> atts) (XNever \<in> atts) (vmrights_map rghts))"


primrec
   pte_relation' :: "ARM_A.pte \<Rightarrow> ARM_H.pte \<Rightarrow> bool"
where
  "pte_relation'  ARM_A.InvalidPTE x = (x = ARM_H.InvalidPTE)"
| "pte_relation' (ARM_A.LargePagePTE ptr atts rghts) x
      = (x = ARM_H.LargePagePTE ptr (PageCacheable \<in> atts) (Global \<in> atts)
                                         (XNever \<in> atts) (vmrights_map rghts))"
| "pte_relation' (ARM_A.SmallPagePTE ptr atts rghts) x
      = (x = ARM_H.SmallPagePTE ptr (PageCacheable \<in> atts) (Global \<in> atts)
                                         (XNever \<in> atts) (vmrights_map rghts))"


definition
  pde_align' :: "ARM_H.pde \<Rightarrow> nat"
where
 "pde_align' pde \<equiv>
  case pde of ARM_H.pde.SuperSectionPDE _ _ _ _ _ _ \<Rightarrow> 4 | _ \<Rightarrow> 0"

lemmas pde_align_simps[simp] =
  pde_align'_def[split_simps ARM_A.pde.split]

definition
  pte_align' :: "ARM_H.pte \<Rightarrow> nat"
where
 "pte_align' pte \<equiv> case pte of ARM_H.pte.LargePagePTE _ _ _ _ _ \<Rightarrow> 4 | _ \<Rightarrow> 0"

lemmas pte_align_simps[simp] =
  pte_align'_def[split_simps ARM_A.pte.split]

definition
  "pde_relation_aligned y pde pde' \<equiv>
   if is_aligned y (pde_align' pde') then pde_relation' pde pde'
   else pde = ARM_A.InvalidPDE"

definition
  "pte_relation_aligned y pte pte' \<equiv>
   if is_aligned y (pte_align' pte') then pte_relation' pte pte'
   else pte = ARM_A.InvalidPTE"

definition
 "pte_relation y \<equiv> \<lambda>ko ko'. \<exists>pt pte. ko = ArchObj (PageTable pt) \<and> ko' = KOArch (KOPTE pte)
                              \<and> pte_relation_aligned y (pt y) pte"

definition
 "pde_relation y \<equiv> \<lambda>ko ko'. \<exists>pd pde. ko = ArchObj (PageDirectory pd) \<and> ko' = KOArch (KOPDE pde)
                              \<and> pde_relation_aligned y (pd y) pde"

(* this is the arch version of other_obj_relation *)
definition other_aobj_relation ::
  "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool" where
  "other_aobj_relation obj obj' \<equiv>
   (case (obj, obj')
      of (ArchObj (ARM_A.ASIDPool pool), KOArch (KOASIDPool pool'))
         \<Rightarrow> asid_pool_relation pool pool'
    | _ \<Rightarrow> False)"

primrec aobj_relation_cuts :: "ARM_A.arch_kernel_obj \<Rightarrow> word32 \<Rightarrow> obj_relation_cuts" where
  "aobj_relation_cuts (DataPage dev sz) x =
      {(x + n * 2 ^ pageBits, \<lambda>_ obj. obj = (if dev then KOUserDataDevice else KOUserData) ) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }"
| "aobj_relation_cuts (ARM_A.ASIDPool pool) x =
     {(x, other_aobj_relation)}"
| "aobj_relation_cuts (PageTable pt) x =
     (\<lambda>y. (x + (ucast y << 2), pte_relation y)) ` UNIV"
| "aobj_relation_cuts (PageDirectory pd) x =
     (\<lambda>y. (x + (ucast y << 2), pde_relation y)) ` UNIV"

definition
 "is_other_obj_relation_type tp \<equiv>
  case tp of
     ACapTable n \<Rightarrow> False
   | ATCB \<Rightarrow> False
   | AArch APageTable \<Rightarrow> False
   | AArch APageDirectory \<Rightarrow> False
   | AArch (AUserData _)   \<Rightarrow> False
   | AArch (ADeviceData _)   \<Rightarrow> False
   | AGarbage _ \<Rightarrow> False
   | _ \<Rightarrow> True"

definition ghost_relation ::
  "Structures_A.kheap \<Rightarrow> (word32 \<rightharpoonup> vmpage_size) \<Rightarrow> (word32 \<rightharpoonup> nat) \<Rightarrow> bool" where
  "ghost_relation h ups cns \<equiv>
   (\<forall>a sz. (\<exists>dev. h a = Some (ArchObj (DataPage dev sz))) \<longleftrightarrow> ups a = Some sz) \<and>
   (\<forall>a n. (\<exists>cs. h a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow>
          cns a = Some n)"

(* FIXME arch-split: provided only so that ghost_relation can be used within generic definition
   of state_relation (since arch_state_relation doesn't have access to kheap, and
   gsPTTypes on AARCH64 isn't generic) *)
definition ghost_relation_wrapper :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ghost_relation_wrapper s s' \<equiv>
     ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')"

(* inside Arch locale, we have no need for the wrapper *)
lemmas [simp] = ghost_relation_wrapper_def

definition arch_state_relation :: "(arch_state \<times> ARM_H.kernel_state) set" where
  "arch_state_relation \<equiv> {(s, s') .
         arm_asid_table s = armKSASIDTable s' o ucast
       \<and> arm_global_pd s = armKSGlobalPD s'
       \<and> arm_hwasid_table s = armKSHWASIDTable s'
       \<and> arm_global_pts s = armKSGlobalPTs s'
       \<and> arm_next_asid s = armKSNextASID s'
       \<and> arm_asid_map s = armKSASIDMap s'
       \<and> arm_kernel_vspace s = armKSKernelVSpace s'}"

end
end
