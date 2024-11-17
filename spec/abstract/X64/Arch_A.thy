(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Entry point for architecture dependent definitions.
*)

chapter "Toplevel x64 Definitions"

theory Arch_A
imports TcbAcc_A
begin

context Arch begin arch_global_naming (A)

definition "page_bits \<equiv> pageBits"

definition
  updateIRQState :: "irq \<Rightarrow> X64IRQState \<Rightarrow> ('a abstract_state_scheme, unit) nondet_monad" where
  "updateIRQState irq irqState \<equiv> do
     irq_states \<leftarrow> gets (x64_irq_state o arch_state);
     modify (\<lambda>s. s \<lparr>arch_state := (arch_state s) \<lparr>x64_irq_state := irq_states (irq := irqState)\<rparr>\<rparr>)
  od"

definition
  arch_invoke_irq_control :: "arch_irq_control_invocation \<Rightarrow> (unit,'z::state_ext) p_monad" where
  "arch_invoke_irq_control aic \<equiv> (case aic of
    IssueIRQHandlerIOAPIC irq dest src ioapic pin level polarity vector \<Rightarrow> without_preemption (do
      do_machine_op $ ioapicMapPinToVector ioapic pin level polarity vector;
      irq_state \<leftarrow> return $ IRQIOAPIC (ioapic && mask 5) (pin && mask 5) (level && 1) (polarity && 1) True;
      updateIRQState irq irq_state;
      set_irq_state IRQSignal (IRQ irq);
      cap_insert (IRQHandlerCap (IRQ irq)) src dest
    od) |
    IssueIRQHandlerMSI irq dest src bus dev func handle \<Rightarrow> without_preemption (do
      irq_state \<leftarrow> return $ IRQMSI (bus && mask 8) (dev && mask 5) (func && mask 3) (handle && mask 32);
      updateIRQState irq irq_state;
      set_irq_state IRQSignal (IRQ irq);
      cap_insert (IRQHandlerCap (IRQ irq)) src dest
    od)
   )"

text \<open>Switch to a thread's virtual address space context.\<close>

definition
  arch_switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_switch_to_thread t \<equiv> set_vm_root t"

definition
   arch_switch_to_idle_thread :: "(unit,'z::state_ext) s_monad" where
   "arch_switch_to_idle_thread \<equiv> do
     thread \<leftarrow> gets idle_thread;
     set_vm_root thread
   od"

definition
  arch_activate_idle_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_activate_idle_thread t \<equiv> return ()"

definition
  "store_asid_pool_entry pool_ptr asid pml4base \<equiv> do
    pool \<leftarrow> get_asid_pool pool_ptr;
    pool' \<leftarrow> return (pool(asid_low_bits_of asid := pml4base));
    set_asid_pool pool_ptr pool'
  od"

text \<open>The ASIDControl capability confers the authority to create a new ASID
pool object. This operation creates the new ASID pool, provides a capability
to it and connects it to the global virtual ASID table.\<close>
definition
perform_asid_control_invocation :: "asid_control_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_asid_control_invocation iv \<equiv> case iv of
  MakePool frame slot parent base \<Rightarrow> do
    delete_objects frame page_bits;
    pcap \<leftarrow> get_cap parent;
    set_cap (max_free_index_update pcap) parent;
    retype_region frame 1 0 (ArchObject ASIDPoolObj) False;
    cap_insert (ArchObjectCap $ ASIDPoolCap frame base) parent slot;
    assert (asid_low_bits_of base = 0);
    asid_table \<leftarrow> gets (x64_asid_table \<circ> arch_state);
    asid_table' \<leftarrow> return (asid_table (asid_high_bits_of base \<mapsto> frame));
    modify (\<lambda>s. s \<lparr>arch_state := (arch_state s) \<lparr>x64_asid_table := asid_table'\<rparr>\<rparr>)
od"

text \<open>The ASIDPool capability confers the authority to assign a virtual ASID
to a page directory.\<close>
definition
perform_asid_pool_invocation :: "asid_pool_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_asid_pool_invocation iv \<equiv> case iv of Assign asid pool_ptr ct_slot \<Rightarrow>
do
    pml4_cap \<leftarrow> get_cap ct_slot;
    case pml4_cap of
      ArchObjectCap (PML4Cap pml4_base _) \<Rightarrow> do
        set_cap (ArchObjectCap $ PML4Cap pml4_base (Some asid)) ct_slot;
        store_asid_pool_entry pool_ptr asid (Some pml4_base)
      od
    | _ \<Rightarrow> fail
od"


definition
  pte_check_if_mapped :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "pte_check_if_mapped slot \<equiv> do
     pt \<leftarrow> get_pte slot;
     return (pt \<noteq> InvalidPTE)
  od"

definition
  pde_check_if_mapped :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "pde_check_if_mapped slot \<equiv> do
     pd \<leftarrow> get_pde slot;
     return (pd \<noteq> InvalidPDE)
  od"

definition
  perform_page_invocation_unmap :: "arch_cap \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "perform_page_invocation_unmap cap ct_slot \<equiv>
      (case cap
         of PageCap dev base rights map_type sz mapped \<Rightarrow> do
            case mapped of Some (asid, vaddr) \<Rightarrow> unmap_page sz asid vaddr base
                          | None \<Rightarrow> return ();
            cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
            set_cap (ArchObjectCap $ update_map_data cap None (Some VMNoMap)) ct_slot
          od
      | _ \<Rightarrow> fail)"

text \<open>The Page capability confers the authority to map, unmap and flush the
  memory page.\<close>
definition
perform_page_invocation :: "page_invocation \<Rightarrow> (data list,'z::state_ext) s_monad" where
"perform_page_invocation iv \<equiv> case iv of
    PageMap cap ct_slot entries vspace \<Rightarrow> do
      set_cap cap ct_slot;
      case entries of
          (VMPTE pte, slot) \<Rightarrow> store_pte slot pte
        | (VMPDE pde, slot) \<Rightarrow> store_pde slot pde
        | (VMPDPTE pdpte, slot) \<Rightarrow> store_pdpte slot pdpte;
      asid \<leftarrow> case cap of
                  ArchObjectCap (PageCap _ _ _ _ _ (Some (as, _))) \<Rightarrow> return as
                | _ \<Rightarrow> fail;
      invalidate_page_structure_cache_asid (addrFromPPtr vspace) asid;
      return []
    od
  | PageUnmap cap ct_slot \<Rightarrow>
      (case cap of
        PageCap dev base rights map_type sz mapped \<Rightarrow> do
            case mapped of
              Some _ \<Rightarrow> (case map_type of
                          VMVSpaceMap \<Rightarrow> perform_page_invocation_unmap cap ct_slot
                        | _ \<Rightarrow> fail)
            | None \<Rightarrow> return ();
            return []
        od
      | _ \<Rightarrow> fail)
\<^cancel>\<open>| PageIOMap asid cap ct_slot entries \<Rightarrow> undefined\<close>
  | PageGetAddr ptr \<Rightarrow>
      return [addrFromPPtr ptr]"

text \<open>PageTable capabilities confer the authority to map and unmap page tables.\<close>
definition
perform_page_table_invocation :: "page_table_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_page_table_invocation iv \<equiv>
case iv of PageTableMap cap ct_slot pde pd_slot vspace \<Rightarrow> do
    set_cap cap ct_slot;
    store_pde pd_slot pde;
    asid <- case cap of ArchObjectCap (PageTableCap  _ (Some (as, _))) \<Rightarrow> return as
            | _ \<Rightarrow> fail;
    invalidate_page_structure_cache_asid (addrFromPPtr vspace) asid
  od
  | PageTableUnmap (ArchObjectCap (PageTableCap p mapped_address)) ct_slot \<Rightarrow> do
    case mapped_address of Some (asid, vaddr) \<Rightarrow> do
      unmap_page_table asid vaddr p;
      pte_bits \<leftarrow> return word_size_bits;
      slots \<leftarrow> return [p, p + (1 << pte_bits) .e. p + (1 <<  pt_bits) - 1];
      mapM_x (swp store_pte InvalidPTE) slots
    od | None \<Rightarrow> return ();
    cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
    set_cap (ArchObjectCap $ update_map_data cap None None) ct_slot
  od
  | _ \<Rightarrow> fail"

text \<open>PageDirectory capabilities confer the authority to map and unmap page
tables.\<close>
definition
perform_page_directory_invocation :: "page_directory_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_page_directory_invocation iv \<equiv>
case iv of PageDirectoryMap cap ct_slot pdpte pdpt_slot vspace \<Rightarrow> do
    set_cap cap ct_slot;
    store_pdpte pdpt_slot pdpte;
    asid <- case cap of ArchObjectCap (PageDirectoryCap _ (Some (as, _))) \<Rightarrow> return as
            | _ \<Rightarrow> fail;
    invalidate_page_structure_cache_asid (addrFromPPtr vspace) asid
  od
  | PageDirectoryUnmap (ArchObjectCap (PageDirectoryCap p mapped_address)) ct_slot \<Rightarrow> do
    case mapped_address of Some (asid, vaddr) \<Rightarrow> do
      unmap_pd asid vaddr p;
      pde_bits \<leftarrow> return word_size_bits;
      slots \<leftarrow> return [p, p + (1 << pde_bits) .e. p + (1 << pd_bits) - 1];
      mapM_x (swp store_pde InvalidPDE) slots
    od | None \<Rightarrow> return ();
    cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
    set_cap (ArchObjectCap $ update_map_data cap None None) ct_slot
  od
  | _ \<Rightarrow> fail"

text \<open>PageDirectory capabilities confer the authority to map and unmap page
tables.\<close>
definition
perform_pdpt_invocation :: "pdpt_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_pdpt_invocation iv \<equiv>
case iv of PDPTMap cap ct_slot pml4e pml4_slot vspace \<Rightarrow> do
    set_cap cap ct_slot;
    store_pml4e pml4_slot pml4e;
    asid <- case cap of ArchObjectCap (PDPointerTableCap _ (Some (as, _))) \<Rightarrow> return as
            | _ \<Rightarrow> fail;
    invalidate_page_structure_cache_asid (addrFromPPtr vspace) asid
  od
  | PDPTUnmap (ArchObjectCap (PDPointerTableCap p mapped_address)) ct_slot \<Rightarrow> do
    case mapped_address of Some (asid, vaddr) \<Rightarrow> do
      unmap_pdpt asid vaddr p;
      pdept_bits \<leftarrow> return word_size_bits;
      slots \<leftarrow> return [p, p + (1 << pdept_bits) .e. p + (1 << pdpt_bits) - 1];
      mapM_x (swp store_pdpte InvalidPDPTE) slots
    od | None \<Rightarrow> return ();
    cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
    set_cap (ArchObjectCap $ update_map_data cap None None) ct_slot
  od
  | _ \<Rightarrow> fail"

definition
  port_out :: "('a word \<Rightarrow> unit machine_monad) \<Rightarrow> ('a word) \<Rightarrow> (data list,'z::state_ext) s_monad" where
  "port_out f w = do
    do_machine_op $ f w;
    return []
  od"

definition
  port_in :: "(data machine_monad) \<Rightarrow> (data list,'z::state_ext) s_monad" where
  "port_in f = do
    res \<leftarrow> do_machine_op f;
    return [res]
  od"

definition
  perform_io_port_invocation :: "io_port_invocation \<Rightarrow> (data list,'z::state_ext) s_monad" where
  "perform_io_port_invocation i \<equiv> (
    case i of (IOPortInvocation port port_data) \<Rightarrow> (
      case port_data of
        IOPortIn8 \<Rightarrow> port_in (in8 port)
      | IOPortIn16 \<Rightarrow> port_in (in16 port)
      | IOPortIn32 \<Rightarrow> port_in (in32 port)
      | IOPortOut8 w \<Rightarrow> port_out (out8 port) w
      | IOPortOut16 w \<Rightarrow> port_out (out16 port) w
      | IOPortOut32 w \<Rightarrow> port_out (out32 port) w
    )
    )"

definition
  perform_ioport_control_invocation :: "io_port_control_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "perform_ioport_control_invocation i \<equiv>
    case i of (IOPortControlInvocation f l dest_slot control_slot) \<Rightarrow> do
      set_ioport_mask f l True;
      c \<leftarrow> return $ ArchObjectCap $ IOPortCap f l;
      cap_insert (ArchObjectCap (IOPortCap f l)) control_slot dest_slot
    od"

abbreviation
  arch_no_return :: "(unit, 'z::state_ext) s_monad \<Rightarrow> (data list, 'z::state_ext) s_monad"
where
  "arch_no_return oper \<equiv> do oper; return [] od"

text \<open>Top level system call despatcher for all x64-specific system calls.\<close>
definition
  arch_perform_invocation :: "arch_invocation \<Rightarrow> (data list,'z::state_ext) p_monad" where
  "arch_perform_invocation i \<equiv> liftE $
    case i of
          InvokePageTable oper \<Rightarrow> arch_no_return $ perform_page_table_invocation oper
        | InvokePageDirectory oper \<Rightarrow> arch_no_return $ perform_page_directory_invocation oper
        | InvokePDPT oper \<Rightarrow> arch_no_return $ perform_pdpt_invocation oper
        | InvokePage oper \<Rightarrow> perform_page_invocation oper
        | InvokeASIDControl oper \<Rightarrow> arch_no_return $ perform_asid_control_invocation oper
        | InvokeASIDPool oper \<Rightarrow> arch_no_return $ perform_asid_pool_invocation oper
        | InvokeIOPort oper \<Rightarrow> perform_io_port_invocation oper
        | InvokeIOPortControl oper \<Rightarrow> arch_no_return $ perform_ioport_control_invocation oper"

end
end
