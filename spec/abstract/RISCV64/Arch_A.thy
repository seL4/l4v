(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Toplevel RISCV64 Definitions"

theory Arch_A
imports CSpace_A
begin

context Arch begin arch_global_naming (A)

definition page_bits :: nat
  where
  "page_bits \<equiv> pageBits"

fun arch_invoke_irq_control :: "arch_irq_control_invocation \<Rightarrow> (unit,'z::state_ext) p_monad"
  where
  "arch_invoke_irq_control (RISCVIRQControlInvocation irq handler_slot control_slot trigger) =
     without_preemption (do
       do_machine_op $ setIRQTrigger irq trigger;
       set_irq_state IRQSignal (irq);
       cap_insert (IRQHandlerCap (irq)) control_slot handler_slot
  od)"

definition arch_switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_switch_to_thread t \<equiv> set_vm_root t"

definition arch_switch_to_idle_thread :: "(unit,'z::state_ext) s_monad"
  where
  "arch_switch_to_idle_thread \<equiv> do
    thread \<leftarrow> gets idle_thread;
    set_vm_root thread
  od"

definition arch_activate_idle_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_activate_idle_thread t \<equiv> return ()"

definition store_asid_pool_entry :: "obj_ref \<Rightarrow> asid \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
  where
  "store_asid_pool_entry pool_ptr asid ptr \<equiv> do
    pool \<leftarrow> get_asid_pool pool_ptr;
    pool' \<leftarrow> return $ pool(asid_low_bits_of asid := ptr);
    set_asid_pool pool_ptr pool'
  od"

text \<open>
  The ASIDControl capability confers the authority to create a new ASID pool object. This
  operation creates the new ASID pool, provides a capability to it and connects it to the global
  virtual ASID table.
\<close>
definition perform_asid_control_invocation :: "asid_control_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "perform_asid_control_invocation iv \<equiv> case iv of
     MakePool frame slot parent base \<Rightarrow> do
       delete_objects frame pageBits;
       pcap \<leftarrow> get_cap parent;
       set_cap (max_free_index_update pcap) parent;
       retype_region frame 1 0 (ArchObject ASIDPoolObj) False;
       cap_insert (ArchObjectCap $ ASIDPoolCap frame base) parent slot;
       assert (asid_low_bits_of base = 0);
       asid_table \<leftarrow> gets (riscv_asid_table \<circ> arch_state);
       asid_table' \<leftarrow> return (asid_table (asid_high_bits_of base \<mapsto> frame));
       modify (\<lambda>s. s \<lparr>arch_state := (arch_state s) \<lparr>riscv_asid_table := asid_table'\<rparr>\<rparr>)
     od"

text \<open>The ASIDPool capability confers the authority to assign an ASID to a top-level page table.\<close>
definition perform_asid_pool_invocation :: "asid_pool_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "perform_asid_pool_invocation iv \<equiv> case iv of
     Assign asid pool_ptr ct_slot \<Rightarrow> do
       pt_cap \<leftarrow> get_cap ct_slot;
       assert $ is_ArchObjectCap pt_cap;
       acap \<leftarrow> return $ the_arch_cap pt_cap;
       assert $ is_PageTableCap acap;
       set_cap (ArchObjectCap $ update_map_data acap $ Some (asid,0)) ct_slot;
       pt_base \<leftarrow> return $ acap_obj acap;
       copy_global_mappings pt_base;
       store_asid_pool_entry pool_ptr asid (Some pt_base)
     od"

definition perform_pg_inv_unmap :: "arch_cap \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "perform_pg_inv_unmap cap ct_slot \<equiv> do
     assert $ is_FrameCap cap;
     case acap_map_data cap of
       Some (asid, vaddr) \<Rightarrow> unmap_page (acap_fsize cap) asid vaddr (acap_obj cap)
     | _ \<Rightarrow> return ();
     old_cap \<leftarrow> get_cap ct_slot;
     set_cap (ArchObjectCap $ update_map_data (the_arch_cap old_cap) None) ct_slot
   od"

definition perform_pg_inv_map :: "arch_cap \<Rightarrow> cslot_ptr \<Rightarrow> pte \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "perform_pg_inv_map cap ct_slot pte slot \<equiv> do
     set_cap (ArchObjectCap cap) ct_slot;
     store_pte slot pte;
     do_machine_op sfence
   od"

definition perform_pg_inv_get_addr :: "obj_ref \<Rightarrow> (data list,'z::state_ext) s_monad"
  where
  "perform_pg_inv_get_addr ptr \<equiv> return [addrFromPPtr ptr]"

text \<open>The Frame capability confers the authority to map and unmap memory.\<close>
definition perform_page_invocation :: "page_invocation \<Rightarrow> (data list,'z::state_ext) s_monad"
  where
  "perform_page_invocation iv \<equiv> case iv of
     PageMap cap ct_slot (pte,slot) \<Rightarrow> do perform_pg_inv_map cap ct_slot pte slot; return [] od
   | PageUnmap cap ct_slot \<Rightarrow> do perform_pg_inv_unmap cap ct_slot; return [] od
   | PageGetAddr ptr \<Rightarrow> perform_pg_inv_get_addr ptr"


definition perform_pt_inv_map :: "arch_cap \<Rightarrow> cslot_ptr \<Rightarrow> pte \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "perform_pt_inv_map cap ct_slot pte slot = do
     set_cap (ArchObjectCap cap) ct_slot;
     store_pte slot pte;
     do_machine_op sfence
   od"

definition perform_pt_inv_unmap :: "arch_cap \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "perform_pt_inv_unmap cap ct_slot = do
     assert $ is_PageTableCap cap;
     case acap_map_data cap of
       Some (asid, vaddr) \<Rightarrow> do
         p \<leftarrow> return $ acap_obj cap;
         unmap_page_table asid vaddr p;
         slots \<leftarrow> return [p, p + (1 << pte_bits) .e. p + (1 << pt_bits) - 1];
         mapM_x (swp store_pte InvalidPTE) slots
       od
     | _ \<Rightarrow> return ();
     old_cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
     set_cap (ArchObjectCap $ update_map_data old_cap None) ct_slot
   od"

text \<open>PageTable capabilities confer the authority to map and unmap page tables.\<close>
definition perform_page_table_invocation :: "page_table_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "perform_page_table_invocation iv \<equiv> case iv of
     PageTableMap cap ct_slot pte slot \<Rightarrow> perform_pt_inv_map cap ct_slot pte slot
   | PageTableUnmap cap ct_slot \<Rightarrow> perform_pt_inv_unmap cap ct_slot"

locale_abbrev arch_no_return :: "(unit, 'z::state_ext) s_monad \<Rightarrow> (data list, 'z::state_ext) s_monad"
  where
  "arch_no_return oper \<equiv> do oper; return [] od"

text \<open>Top level system call dispatcher for all RISCV64-specific system calls.\<close>
definition arch_perform_invocation :: "arch_invocation \<Rightarrow> (data list,'z::state_ext) p_monad"
  where
  "arch_perform_invocation i \<equiv> liftE $ case i of
     InvokePageTable oper \<Rightarrow> arch_no_return $ perform_page_table_invocation oper
   | InvokePage oper \<Rightarrow> perform_page_invocation oper
   | InvokeASIDControl oper \<Rightarrow> arch_no_return $ perform_asid_control_invocation oper
   | InvokeASIDPool oper \<Rightarrow> arch_no_return $ perform_asid_pool_invocation oper"

end
end
