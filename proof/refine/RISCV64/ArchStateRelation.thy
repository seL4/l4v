(*
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

primrec arch_fault_map :: "Machine_A.RISCV64_A.arch_fault \<Rightarrow> arch_fault" where
  "arch_fault_map (Machine_A.RISCV64_A.VMFault ptr msg) = VMFault ptr msg"

definition vmrights_map :: "rights set \<Rightarrow> vmrights" where
  "vmrights_map S \<equiv> if AllowRead \<in> S
                     then (if AllowWrite \<in> S then VMReadWrite else VMReadOnly)
                     else VMKernelOnly"

definition mdata_map ::
  "(Machine_A.RISCV64_A.asid \<times> vspace_ref) option \<Rightarrow> (asid \<times> vspace_ref) option" where
  "mdata_map = map_option (\<lambda>(asid, ref). (ucast asid, ref))"

primrec acap_relation :: "arch_cap \<Rightarrow> arch_capability \<Rightarrow> bool" where
  "acap_relation (arch_cap.ASIDPoolCap p asid) c =
     (c = ASIDPoolCap p (ucast asid))"
| "acap_relation (arch_cap.ASIDControlCap) c =
     (c = ASIDControlCap)"
| "acap_relation (arch_cap.FrameCap p rghts sz dev data) c =
     (c = FrameCap p (vmrights_map rghts) sz dev (mdata_map data))"
| "acap_relation (arch_cap.PageTableCap p data) c =
     (c = PageTableCap p (mdata_map data))"

definition asid_pool_relation :: "(asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> asidpool \<Rightarrow> bool" where
  "asid_pool_relation \<equiv> \<lambda>p p'. p = inv ASIDPool p' o ucast"

definition arch_tcb_relation :: "Structures_A.arch_tcb \<Rightarrow> Structures_H.arch_tcb \<Rightarrow> bool" where
  "arch_tcb_relation \<equiv> \<lambda>atcb atcb'. tcb_context atcb = atcbContext atcb'"

primrec pte_relation' :: "RISCV64_A.pte \<Rightarrow> RISCV64_H.pte \<Rightarrow> bool" where
  "pte_relation' RISCV64_A.InvalidPTE x =
     (x = RISCV64_H.InvalidPTE)"
| "pte_relation' (RISCV64_A.PageTablePTE ppn atts) x =
     (x = RISCV64_H.PageTablePTE (ucast ppn) (Global \<in> atts) \<and> Execute \<notin> atts \<and> User \<notin> atts)"
| "pte_relation' (RISCV64_A.PagePTE ppn atts rghts) x =
     (x = RISCV64_H.PagePTE (ucast ppn) (Global \<in> atts) (User \<in> atts) (Execute \<in> atts)
                            (vmrights_map rghts))"

definition pte_relation :: "pt_index \<Rightarrow> Structures_A.kernel_object \<Rightarrow> kernel_object \<Rightarrow> bool" where
 "pte_relation y \<equiv> \<lambda>ko ko'. \<exists>pt pte. ko = ArchObj (PageTable pt) \<and> ko' = KOArch (KOPTE pte)
                                      \<and> pte_relation' (pt y) pte"

(* this is the arch version of other_obj_relation *)
definition other_aobj_relation ::
  "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool" where
  "other_aobj_relation obj obj' \<equiv>
   (case (obj, obj')
      of (ArchObj (RISCV64_A.ASIDPool ap), KOArch (KOASIDPool ap')) \<Rightarrow> asid_pool_relation ap ap'
       | _ \<Rightarrow> False)"

primrec aobj_relation_cuts :: "RISCV64_A.arch_kernel_obj \<Rightarrow> machine_word \<Rightarrow> obj_relation_cuts" where
  "aobj_relation_cuts (DataPage dev sz) x =
     { (x + (n << pageBits), \<lambda>_ obj. obj = (if dev then KOUserDataDevice else KOUserData))
       | n. n < 2 ^ (pageBitsForSize sz - pageBits) }"
| "aobj_relation_cuts (RISCV64_A.ASIDPool pool) x =
     {(x, other_aobj_relation)}"
| "aobj_relation_cuts (PageTable pt) x =
     (\<lambda>y. (x + (ucast y << pteBits), pte_relation y)) ` UNIV"

definition is_other_obj_relation_type :: "a_type \<Rightarrow> bool" where
 "is_other_obj_relation_type tp \<equiv>
    case tp of
      ACapTable n \<Rightarrow> False
    | ATCB \<Rightarrow> False
    | AArch APageTable \<Rightarrow> False
    | AArch (AUserData _) \<Rightarrow> False
    | AArch (ADeviceData _) \<Rightarrow> False
    | AGarbage _ \<Rightarrow> False
    | _ \<Rightarrow> True"

definition ghost_relation ::
  "Structures_A.kheap \<Rightarrow> (machine_word \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<rightharpoonup> nat) \<Rightarrow> bool" where
  "ghost_relation h ups cns \<equiv>
     (\<forall>a sz. (\<exists>dev. h a = Some (ArchObj (DataPage dev sz))) \<longleftrightarrow> ups a = Some sz) \<and>
     (\<forall>a n. (\<exists>cs. h a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow> cns a = Some n)"

(* FIXME arch-split: provided only so that ghost_relation can be used within generic definition
   of state_relation (since arch_state_relation doesn't have access to kheap, and
   gsPTTypes on AARCH64 isn't generic) *)
definition ghost_relation_wrapper :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ghost_relation_wrapper s s' \<equiv>
     ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')"

(* inside Arch locale, we have no need for the wrapper *)
lemmas [simp] = ghost_relation_wrapper_def

definition arch_state_relation :: "(arch_state \<times> RISCV64_H.kernel_state) set" where
  "arch_state_relation \<equiv> {(s, s') .
         riscv_asid_table s = riscvKSASIDTable s' o ucast
         \<and> riscv_global_pts s = (\<lambda>l. set (riscvKSGlobalPTs s' (size l)))
         \<and> riscv_kernel_vspace s = riscvKSKernelVSpace s'}"

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
