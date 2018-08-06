(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "RISCV64 Object Invocations"

theory ArchInvocation_A
imports "../Structures_A"
begin

context Arch begin global_naming RISCV64_A

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
  | PageRemap
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
    RISCVNoIRQControlInvocation

end
end
