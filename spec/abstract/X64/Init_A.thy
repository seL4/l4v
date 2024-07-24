(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Dummy initial kernel state. Real kernel boot up is more complex.
*)

chapter "An Initial Kernel State"

theory Init_A
imports Retype_A
begin

context Arch begin arch_global_naming (A)

text \<open>
  This is not a specification of true kernel
  initialisation. This theory describes a dummy initial state only, to
  show that the invariants and refinement relation are consistent.
\<close>

(* 8KiB *)
definition
  init_irq_node_ptr :: obj_ref where
  "init_irq_node_ptr = kernel_base + 0x2000"

(* 4KiB *)
definition
  init_global_pml4 :: obj_ref where
  "init_global_pml4 = kernel_base + 0x4000"

(* 4KiB *)
definition
  init_global_pdpt :: obj_ref where
  "init_global_pdpt = kernel_base + 0x5000"

(* 4KiB *)
definition
  init_global_pd :: obj_ref where
  "init_global_pd = kernel_base + 0x6000"

definition
  "init_arch_state \<equiv> \<lparr>
    x64_asid_table = Map.empty,
    x64_global_pml4 = init_global_pml4,
    x64_kernel_vspace =
      \<lambda>ref. if ref \<in> {pptr_base .. pptr_base + mask pml4_shift_bits}
              then X64VSpaceKernelWindow
              else X64VSpaceInvalidRegion,
    x64_global_pts = [],
    x64_global_pdpts = [init_global_pdpt],
    x64_global_pds = [init_global_pd],
    x64_current_cr3 = cr3 0 0,
    x64_allocated_io_ports = \<lambda>_. False,
    x64_num_ioapics = 1,
    x64_ioapic_nirqs = \<lambda>_. ucast ioapicIRQLines,
    x64_irq_state = K IRQFree
   \<rparr>"

definition [simp]:
  "global_pml4 \<equiv> (\<lambda>_ :: 9 word. InvalidPML4E)
    (0x1FF := PDPointerTablePML4E (addrFromPPtr init_global_pdpt) {} {})"

(* The kernel uses huge page mappings in the global PDPT to get a view of all physical memory.
   The exception is the upper-most PDPT entry, which maps to the global page directory. *)
definition [simp]:
  "global_pdpt \<equiv> (\<lambda> i :: 9 word. HugePagePDPTE (ucast i << 30) {} {})
                    (0x1FF := PageDirectoryPDPTE (addrFromPPtr init_global_pd) {} {})"

(* C kernel initialisation refines this down to small pages for devices, but we'll stop here. *)
definition [simp]:
  "global_pd \<equiv> (\<lambda> i :: 9 word. LargePagePDE (0x03FE00 + ucast i << 21) {} {})"

definition
  "init_kheap \<equiv>
    (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
           then Some (CNode 0 (empty_cnode 0))
           else None)
    (idle_thread_ptr \<mapsto>
       TCB \<lparr>
         tcb_ctable = NullCap,
         tcb_vtable = NullCap,
         tcb_reply = NullCap,
         tcb_caller = NullCap,
         tcb_ipcframe = NullCap,
         tcb_state = IdleThreadState,
         tcb_fault_handler = replicate word_bits False,
         tcb_ipc_buffer = 0,
         tcb_fault = None,
         tcb_bound_notification = None,
         tcb_mcpriority = minBound,
         tcb_arch = init_arch_tcb
         \<rparr>,
     init_global_pml4 \<mapsto> ArchObj (PageMapL4 global_pml4),
     init_global_pdpt \<mapsto> ArchObj (PDPointerTable global_pdpt),
     init_global_pd \<mapsto> ArchObj (PageDirectory global_pd)
    )"

definition
  "init_cdt \<equiv> Map.empty"

definition
  "init_ioc \<equiv>
   \<lambda>(a,b). (\<exists>obj. init_kheap a = Some obj \<and>
                  (\<exists>cap. cap_of obj b = Some cap \<and> cap \<noteq> cap.NullCap))"

definition
  "init_A_st \<equiv> \<lparr>
    kheap = init_kheap,
    cdt = init_cdt,
    is_original_cap = init_ioc,
    cur_thread = idle_thread_ptr,
    idle_thread = idle_thread_ptr,
    machine_state = init_machine_state,
    interrupt_irq_node = \<lambda>irq. init_irq_node_ptr + (ucast irq << cte_level_bits),
    interrupt_states = \<lambda>_. Structures_A.IRQInactive,
    arch_state = init_arch_state,
    exst = ext_init
  \<rparr>"

end
end
