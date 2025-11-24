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

primrec arch_fault_map :: "Machine_A.X64_A.arch_fault \<Rightarrow> ArchFault_H.X64_H.arch_fault" where
  "arch_fault_map (Machine_A.X64_A.VMFault ptr msg) = ArchFault_H.X64_H.VMFault ptr msg"

definition vmrights_map :: "rights set \<Rightarrow> vmrights" where
  "vmrights_map S \<equiv> if AllowRead \<in> S
                    then (if AllowWrite \<in> S then VMReadWrite else VMReadOnly)
                    else VMKernelOnly"

primrec acap_relation :: "arch_cap \<Rightarrow> arch_capability \<Rightarrow> bool" where
  "acap_relation (arch_cap.ASIDPoolCap x y) c             = (c =
        arch_capability.ASIDPoolCap x y)"
| "acap_relation (arch_cap.ASIDControlCap) c              = (c =
        arch_capability.ASIDControlCap)"
| "acap_relation (arch_cap.PageCap dev word rghts typ sz data) c  = (c =
        arch_capability.PageCap word (vmrights_map rghts) typ sz dev data)"
| "acap_relation (arch_cap.PageTableCap word data) c      = (c =
        arch_capability.PageTableCap word data)"
| "acap_relation (arch_cap.PageDirectoryCap word data) c  = (c =
        arch_capability.PageDirectoryCap word data)"
| "acap_relation (arch_cap.PDPointerTableCap word data) c = (c =
        arch_capability.PDPointerTableCap word data)"
| "acap_relation (arch_cap.PML4Cap word data) c = (c =
        arch_capability.PML4Cap word data)"
| "acap_relation (arch_cap.IOPortCap f l) c = (c =
        arch_capability.IOPortCap f l)"
| "acap_relation (arch_cap.IOPortControlCap) c = (c = arch_capability.IOPortControlCap)"

definition asid_pool_relation :: "(9 word \<rightharpoonup> machine_word) \<Rightarrow> asidpool \<Rightarrow> bool" where
  "asid_pool_relation \<equiv> \<lambda>p p'. p = inv ASIDPool p' o ucast"

definition arch_tcb_relation :: "Structures_A.arch_tcb \<Rightarrow> Structures_H.arch_tcb \<Rightarrow> bool" where
 "arch_tcb_relation \<equiv> \<lambda>atcb atcb'. tcb_context atcb = atcbContext atcb'"

(* this is the arch version of other_obj_relation *)
definition
  other_aobj_relation :: "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "other_aobj_relation obj obj' \<equiv>
   (case (obj, obj') of
      (ArchObj (X64_A.ASIDPool pool), KOArch (KOASIDPool pool')) \<Rightarrow> asid_pool_relation pool pool'
    | _ \<Rightarrow> False)"

primrec
   pml4e_relation' :: "X64_A.pml4e \<Rightarrow> X64_H.pml4e \<Rightarrow> bool"
where
  "pml4e_relation'  X64_A.InvalidPML4E x = (x = X64_H.InvalidPML4E)"
| "pml4e_relation' (X64_A.PDPointerTablePML4E ptr atts rights) x
      = (x = X64_H.PDPointerTablePML4E ptr (Accessed \<in> atts) (CacheDisabled \<in> atts) (WriteThrough \<in> atts)
                                    (ExecuteDisable \<in> atts) (vmrights_map rights))"

primrec
   pdpte_relation' :: "X64_A.pdpte \<Rightarrow> X64_H.pdpte \<Rightarrow> bool"
where
  "pdpte_relation'  X64_A.InvalidPDPTE x = (x = X64_H.InvalidPDPTE)"
| "pdpte_relation' (X64_A.PageDirectoryPDPTE ptr atts rights) x
      = (x = X64_H.PageDirectoryPDPTE ptr (Accessed \<in> atts) (CacheDisabled \<in> atts) (WriteThrough \<in> atts)
                                    (ExecuteDisable \<in> atts) (vmrights_map rights))"
| "pdpte_relation' (X64_A.HugePagePDPTE ptr atts rghts) x
      = (x = X64_H.HugePagePDPTE ptr (Global \<in> atts) (PAT \<in> atts) (Dirty \<in> atts)
                                    (PTAttr Accessed \<in> atts) (PTAttr CacheDisabled \<in> atts)
                                    (PTAttr WriteThrough \<in> atts) (PTAttr ExecuteDisable \<in> atts)
                                    (vmrights_map rghts))"

primrec
   pde_relation' :: "X64_A.pde \<Rightarrow> X64_H.pde \<Rightarrow> bool"
where
  "pde_relation'  X64_A.InvalidPDE x = (x = X64_H.InvalidPDE)"
| "pde_relation' (X64_A.PageTablePDE ptr atts rights) x
      = (x = X64_H.PageTablePDE ptr (Accessed \<in> atts) (CacheDisabled \<in> atts) (WriteThrough \<in> atts)
                                    (ExecuteDisable \<in> atts) (vmrights_map rights))"
| "pde_relation' (X64_A.LargePagePDE ptr atts rghts) x
      = (x = X64_H.LargePagePDE ptr (Global \<in> atts) (PAT \<in> atts) (Dirty \<in> atts)
                                    (PTAttr Accessed \<in> atts) (PTAttr CacheDisabled \<in> atts)
                                    (PTAttr WriteThrough \<in> atts) (PTAttr ExecuteDisable \<in> atts)
                                    (vmrights_map rghts))"

primrec
   pte_relation' :: "X64_A.pte \<Rightarrow> X64_H.pte \<Rightarrow> bool"
where
  "pte_relation'  X64_A.InvalidPTE x = (x = X64_H.InvalidPTE)"
| "pte_relation' (X64_A.SmallPagePTE ptr atts rghts) x
      = (x = X64_H.SmallPagePTE ptr (Global \<in> atts) (PAT \<in> atts) (Dirty \<in> atts)
                                    (PTAttr Accessed \<in> atts) (PTAttr CacheDisabled \<in> atts)
                                    (PTAttr WriteThrough \<in> atts) (PTAttr ExecuteDisable \<in> atts)
                                    (vmrights_map rghts))"

definition
 "pte_relation y \<equiv> \<lambda>ko ko'. \<exists>pt pte. ko = ArchObj (PageTable pt) \<and> ko' = KOArch (KOPTE pte)
                              \<and> pte_relation' (pt y) pte"

definition
 "pde_relation y \<equiv> \<lambda>ko ko'. \<exists>pd pde. ko = ArchObj (PageDirectory pd) \<and> ko' = KOArch (KOPDE pde)
                              \<and> pde_relation' (pd y) pde"

definition
 "pdpte_relation y \<equiv> \<lambda>ko ko'. \<exists>pd pdpte. ko = ArchObj (PDPointerTable pd) \<and> ko' = KOArch (KOPDPTE pdpte)
                              \<and> pdpte_relation' (pd y) pdpte"

definition
 "pml4e_relation y \<equiv> \<lambda>ko ko'. \<exists>pd pml4e. ko = ArchObj (PageMapL4 pd) \<and> ko' = KOArch (KOPML4E pml4e)
                              \<and> pml4e_relation' (pd y) pml4e"

primrec aobj_relation_cuts :: "X64_A.arch_kernel_obj \<Rightarrow> machine_word \<Rightarrow> obj_relation_cuts" where
  "aobj_relation_cuts (DataPage dev sz) x =
      {(x + n * 2 ^ pageBits, \<lambda>_ obj. obj = (if dev then KOUserDataDevice else KOUserData) ) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }"
| "aobj_relation_cuts (X64_A.ASIDPool pool) x =
     {(x, other_aobj_relation)}"
| "aobj_relation_cuts (PageTable pt) x =
     (\<lambda>y. (x + (ucast y << word_size_bits), pte_relation y)) ` UNIV"
| "aobj_relation_cuts (PageDirectory pd) x =
     (\<lambda>y. (x + (ucast y << word_size_bits), pde_relation y)) ` UNIV"
| "aobj_relation_cuts (PDPointerTable pdpt) x =
     (\<lambda>y. (x + (ucast y << word_size_bits), pdpte_relation y)) ` UNIV"
| "aobj_relation_cuts (PageMapL4 pm) x =
     (\<lambda>y. (x + (ucast y << word_size_bits), pml4e_relation y)) ` UNIV"

definition
  "is_other_obj_relation_type tp \<equiv>
     case tp of
       ACapTable n \<Rightarrow> False
     | ATCB \<Rightarrow> False
     | AArch APageTable \<Rightarrow> False
     | AArch APageDirectory \<Rightarrow> False
     | AArch APDPointerTable \<Rightarrow> False
     | AArch APageMapL4 \<Rightarrow> False
     | AArch (AUserData _)   \<Rightarrow> False
     | AArch (ADeviceData _)   \<Rightarrow> False
     | AGarbage _ \<Rightarrow> False
     | _ \<Rightarrow> True"

definition ghost_relation ::
  "kheap \<Rightarrow> (machine_word \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<rightharpoonup> nat) \<Rightarrow> bool" where
  "ghost_relation h ups cns \<equiv>
     (\<forall>a sz. (\<exists>dev. h a = Some (ArchObj (DataPage dev sz))) \<longleftrightarrow> ups a = Some sz) \<and>
     (\<forall>a n. (\<exists>cs. h a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow> cns a = Some n)"

(* provided only so that ghost_relation can be used within generic definition
   of state_relation (since arch_state_relation doesn't have access to kheap, and
   gsPTTypes on AARCH64 isn't generic) *)
definition ghost_relation_wrapper_2 ::
  "kheap \<Rightarrow> (machine_word \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<rightharpoonup> nat) \<Rightarrow> Arch.kernel_state \<Rightarrow> bool"
  where
  "ghost_relation_wrapper_2 h ups cns as \<equiv> ghost_relation h ups cns"

(* inside Arch locale, we have no need for the wrapper *)
lemmas ghost_relation_wrapper_def[simp] = ghost_relation_wrapper_2_def

definition cr3_relation :: "X64_A.cr3 \<Rightarrow> cr3 \<Rightarrow> bool" where
  "cr3_relation c c' \<equiv> cr3_base_address c = cr3BaseAddress c' \<and> cr3_pcid c = cr3pcid c'"

fun x64irqstate_to_abstract :: "x64irqstate \<Rightarrow> X64IRQState" where
  "x64irqstate_to_abstract X64IRQFree = IRQFree"
| "x64irqstate_to_abstract X64IRQReserved = IRQReserved"
| "x64irqstate_to_abstract (X64IRQMSI bus dev func handle) = (IRQMSI bus dev func handle)"
| "x64irqstate_to_abstract (X64IRQIOAPIC ioapic pin level polarity masked) =
     (IRQIOAPIC ioapic pin level polarity masked)"

definition x64_irq_relation :: "(8 word \<Rightarrow> X64IRQState) \<Rightarrow> (8 word \<Rightarrow> x64irqstate) \<Rightarrow> bool" where
  "x64_irq_relation irq_states irq_states' \<equiv> irq_states = x64irqstate_to_abstract o irq_states'"

definition arch_state_relation :: "(arch_state \<times> X64_H.kernel_state) set" where
  "arch_state_relation \<equiv> {(s, s') .
         x64_asid_table s = x64KSASIDTable s' o ucast
       \<and> x64_global_pml4 s = x64KSSKIMPML4 s'
       \<and> x64_global_pdpts s = x64KSSKIMPDPTs s'
       \<and> x64_global_pds s = x64KSSKIMPDs s'
       \<and> x64_global_pts s = x64KSSKIMPTs s'
       \<and> cr3_relation (x64_current_cr3 s) (x64KSCurrentUserCR3 s')
       \<and> x64_kernel_vspace s = x64KSKernelVSpace s'
       \<and> x64_allocated_io_ports s = x64KSAllocatedIOPorts s'
       \<and> x64_num_ioapics s = x64KSNumIOAPICs s'
       \<and> x64_ioapic_nirqs s = x64KSIOAPICnIRQs s'
       \<and> x64_irq_relation (x64_irq_state s) (x64KSIRQState s')
       \<and> x64_current_fpu_owner s = x64KSCurFPUOwner s'}"

lemma ghost_relation_of_heap:
  "ghost_relation h ups cns \<longleftrightarrow> ups_of_heap h = ups \<and> cns_of_heap h = cns"
  apply (rule iffI)
   apply (rule conjI)
    apply (rule ext)
    apply (clarsimp simp add: ghost_relation_def ups_of_heap_def)
    apply (drule_tac x=x in spec)
    apply (auto simp: ghost_relation_def ups_of_heap_def
                split: option.splits Structures_A.kernel_object.splits
                       arch_kernel_obj.splits)[1]
    subgoal for x dev sz
     by (drule_tac x = sz in spec,simp)
   apply (rule ext)
   apply (clarsimp simp add: ghost_relation_def cns_of_heap_def)
   apply (drule_tac x=x in spec)+
   apply (rule ccontr)
   apply (simp split: option.splits Structures_A.kernel_object.splits
                      arch_kernel_obj.splits)[1]
   apply (simp split: if_split_asm)
    apply force
   apply (drule not_sym)
   apply clarsimp
   apply (erule_tac x=y in allE)
   apply simp
  apply (auto simp add: ghost_relation_def ups_of_heap_def cns_of_heap_def
              split: option.splits Structures_A.kernel_object.splits
                     arch_kernel_obj.splits if_split_asm)
  done

end
end
