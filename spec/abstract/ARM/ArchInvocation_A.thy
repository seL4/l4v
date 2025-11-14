(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Arch specific object invocations
*)

chapter "ARM Object Invocations"

theory ArchInvocation_A
imports Structures_A
begin

context Arch begin arch_global_naming (A)

text \<open>These datatypes encode the arguments to the various possible
ARM-specific system calls. Selectors are defined for various fields
for convenience elsewhere.\<close>

datatype flush_type = Clean | Invalidate | CleanInvalidate | Unify

datatype page_directory_invocation =
    PageDirectoryFlush (pd_flush_type: flush_type) (pd_flush_start: vspace_ref)
                       (pd_flush_end: vspace_ref) (pd_flush_pstart: word32)
                       (pd_flush_pd: obj_ref) (pd_flush_asid: asid)
  | PageDirectoryNothing

datatype page_table_invocation =
    PageTableMap cap cslot_ptr pde obj_ref
  | PageTableUnmap cap cslot_ptr

datatype asid_control_invocation =
    MakePool obj_ref cslot_ptr cslot_ptr asid

datatype asid_pool_invocation =
    Assign asid obj_ref cslot_ptr

datatype page_invocation
     = PageMap
         (page_map_asid: asid)
         (page_map_cap: cap)
         (page_map_ct_slot: cslot_ptr)
         (page_map_entries: "pte \<times> (obj_ref list) + pde \<times> (obj_ref list)")
     | PageUnmap
         (page_unmap_cap: arch_cap)
         (page_unmap_cap_slot: cslot_ptr)
     | PageFlush
         (page_flush_type: flush_type)
         (page_flush_start: vspace_ref)
         (page_flush_end: vspace_ref)
         (page_flush_pstart: word32)
         (page_flush_pd: obj_ref)
         (page_flush_asid: asid)
     | PageGetAddr
         (page_get_paddr: obj_ref)

datatype sgi_signal_invocation =
    SGISignalGenerate (sgi_irq : sgi_irq) (sgi_target : sgi_target)

datatype arch_invocation
     = InvokePageTable page_table_invocation
     | InvokePageDirectory page_directory_invocation
     | InvokePage page_invocation
     | InvokeASIDControl asid_control_invocation
     | InvokeASIDPool asid_pool_invocation
     | InvokeSGISignal sgi_signal_invocation

datatype arch_copy_register_sets = ARMNoExtraRegisters

definition "ArchDefaultExtraRegisters \<equiv> ARMNoExtraRegisters"

datatype arch_irq_control_invocation =
    ArchIRQControlIssue irq cslot_ptr cslot_ptr bool
  | IssueSGISignal
      (issue_sgi_irq : sgi_irq)
      (issue_sgi_target : sgi_target)
      (issue_control_slot : cslot_ptr)
      (issue_sgi_slot : cslot_ptr)

end

end
