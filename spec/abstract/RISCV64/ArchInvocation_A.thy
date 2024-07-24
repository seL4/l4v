(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "RISCV64 Object Invocations"

theory ArchInvocation_A
imports Structures_A
begin

context Arch begin arch_global_naming (A)

text \<open>These datatypes encode the arguments to the various possible RISCV64-specific system calls.
Selectors are defined for various fields for convenience elsewhere.\<close>
datatype page_table_invocation =
    PageTableMap
      (pt_inv_cap : arch_cap)
      (pt_inv_cslot : cslot_ptr)
      (pt_map_pte : pte)
      (pt_map_slot : obj_ref)
  | PageTableUnmap
      (pt_inv_cap : arch_cap)
      (pt_inv_cslot : cslot_ptr)

datatype asid_control_invocation =
    MakePool obj_ref cslot_ptr cslot_ptr asid

datatype asid_pool_invocation =
    Assign asid obj_ref cslot_ptr

datatype page_invocation =
    PageMap
      (pg_inv_cap : arch_cap)
      (pg_inv_cslot : cslot_ptr)
      (pg_inv_entries : "pte \<times> obj_ref")
  | PageUnmap
      (pg_inv_cap : arch_cap)
      (pg_inv_cslot : cslot_ptr)
  | PageGetAddr
      (pg_get_paddr : obj_ref)

datatype arch_invocation =
    InvokePageTable page_table_invocation
  | InvokePage page_invocation
  | InvokeASIDControl asid_control_invocation
  | InvokeASIDPool asid_pool_invocation

datatype arch_copy_register_sets =
    RISCVNoExtraRegisters

definition ArchDefaultExtraRegisters :: arch_copy_register_sets
  where
  "ArchDefaultExtraRegisters = RISCVNoExtraRegisters"

datatype arch_irq_control_invocation =
    RISCVIRQControlInvocation irq cslot_ptr cslot_ptr bool

end
end
