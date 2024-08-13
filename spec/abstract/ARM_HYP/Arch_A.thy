(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Entry point for architecture dependent definitions.
*)

chapter "Toplevel ARM Definitions"

theory Arch_A
imports TcbAcc_A VCPU_A
begin

context Arch begin arch_global_naming (A)

definition "page_bits \<equiv> pageBits"

fun
  arch_invoke_irq_control :: "arch_irq_control_invocation \<Rightarrow> (unit,'z::state_ext) p_monad"
where
  "arch_invoke_irq_control (ArchIRQControlIssue irq handler_slot control_slot trigger) = without_preemption (do
    when haveSetTrigger $ do_machine_op $ setIRQTrigger irq trigger;
    set_irq_state IRQSignal irq;
    cap_insert (IRQHandlerCap irq) control_slot handler_slot
  od)"
| "arch_invoke_irq_control (IssueSGISignal irq target control_slot sgi_slot) =
     without_preemption
       (cap_insert (ArchObjectCap (SGISignalCap irq target)) control_slot sgi_slot)"

text \<open>Switch to a thread's virtual address space context. Clear the load-exclusive monitor.\<close>
definition
  arch_switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_switch_to_thread t \<equiv> do
     t' \<leftarrow> gets_the $ get_tcb t;
     vcpu_switch $ tcb_vcpu $ tcb_arch t';
     set_vm_root t;
     do_machine_op $ clearExMonitor
   od"

text \<open>The idle thread does not need to be handled specially on ARM.\<close>
definition
   arch_switch_to_idle_thread :: "(unit,'z::state_ext) s_monad" where
   "arch_switch_to_idle_thread \<equiv> do
     vcpu_switch None;
     t \<leftarrow> gets idle_thread;
     set_vm_root t
   od"

definition arch_prepare_next_domain :: "(unit,'z::state_ext) s_monad" where
  "arch_prepare_next_domain \<equiv> vcpu_flush"

definition
  arch_activate_idle_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_activate_idle_thread t \<equiv> return ()"

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
    assert (base && mask asid_low_bits = 0);
    asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
    asid_table' \<leftarrow> return (asid_table (asid_high_bits_of base \<mapsto> frame));
    modify (\<lambda>s. s \<lparr>arch_state := (arch_state s) \<lparr>arm_asid_table := asid_table'\<rparr>\<rparr>)
od"

text \<open>The ASIDPool capability confers the authority to assign a virtual ASID
to a page directory.\<close>
definition
perform_asid_pool_invocation :: "asid_pool_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_asid_pool_invocation iv \<equiv> case iv of Assign asid pool_ptr ct_slot \<Rightarrow>
do
    pd_cap \<leftarrow> get_cap ct_slot;
    case pd_cap of
      ArchObjectCap (PageDirectoryCap pd_base _) \<Rightarrow> do
        pool \<leftarrow> get_asid_pool pool_ptr;
        pool' \<leftarrow> return (pool (ucast asid \<mapsto> pd_base));
        set_cap (ArchObjectCap $ PageDirectoryCap pd_base (Some asid)) ct_slot;
        set_asid_pool pool_ptr pool'
      od
    | _ \<Rightarrow> fail
od"

text \<open>The PageDirectory capability confers the authority to flush cache entries
associated with that PD\<close>
definition
  perform_page_directory_invocation :: "page_directory_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "perform_page_directory_invocation iv \<equiv> case iv of
       PageDirectoryFlush typ start end pstart pd asid \<Rightarrow>
         when (start < end) $ do
           root_switched \<leftarrow> set_vm_root_for_flush pd asid;
           do_machine_op $ do_flush typ start end pstart;
           when root_switched $ do
             tcb \<leftarrow> gets cur_thread;
             set_vm_root tcb
           od
        od
     | PageDirectoryNothing \<Rightarrow> return ()"

definition
  pte_check_if_mapped :: "32 word \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "pte_check_if_mapped slot \<equiv> do
     pt \<leftarrow> get_master_pte slot;
     return (pt \<noteq> InvalidPTE)
  od"

definition
  pde_check_if_mapped :: "32 word \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "pde_check_if_mapped slot \<equiv> do
     pd \<leftarrow> get_master_pde slot;
     return (pd \<noteq> InvalidPDE)
  od"


text \<open>The Page capability confers the authority to map, unmap and flush the
  memory page.\<close>
definition
perform_page_invocation :: "page_invocation \<Rightarrow> (data list,'z::state_ext) s_monad" where
"perform_page_invocation iv \<equiv> case iv of
  PageMap asid cap ct_slot entries \<Rightarrow> do
    set_cap cap ct_slot;
    case entries of
          Inl (pte, slots) \<Rightarrow> do
            flush \<leftarrow> pte_check_if_mapped (hd slots);
            store_pte (hd slots) pte;
            mapM (swp store_pte InvalidPTE) (tl slots);
            do_machine_op $ cleanCacheRange_PoU (hd slots) (last_byte_pte (last slots))
                                                (addrFromPPtr (hd slots));
            if flush then (invalidate_tlb_by_asid asid) else return ()
          od
        | Inr (pde, slots) \<Rightarrow> do
            flush \<leftarrow> pde_check_if_mapped (hd slots);
            store_pde (hd slots) pde;
            mapM (swp store_pde InvalidPDE) (tl slots);
            do_machine_op $ cleanCacheRange_PoU (hd slots) (last_byte_pde (last slots))
                                                (addrFromPPtr (hd slots));
            if flush then (invalidate_tlb_by_asid asid) else return ()
          od;
    return []
  od
| PageUnmap cap ct_slot \<Rightarrow>
    (case cap of
      PageCap dev p R vp_size vp_mapped_addr \<Rightarrow> do
        case vp_mapped_addr of
            Some (asid, vaddr) \<Rightarrow> unmap_page vp_size asid vaddr p
          | None \<Rightarrow> return ();
        cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
        set_cap (ArchObjectCap $ update_map_data cap None) ct_slot;
        return []
      od
    | _ \<Rightarrow> fail)
| PageFlush typ start end pstart pd asid \<Rightarrow> do
    when (start < end) $ do
      root_switched \<leftarrow> set_vm_root_for_flush pd asid;
      do_machine_op $ do_flush typ start end pstart;
      when root_switched $ do
        tcb \<leftarrow> gets cur_thread;
        set_vm_root tcb
      od
    od;
    return []
  od
| PageGetAddr ptr \<Rightarrow>
    return [addrFromPPtr ptr]
  "

text \<open>PageTable capabilities confer the authority to map and unmap page
tables.\<close>
definition
perform_page_table_invocation :: "page_table_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_page_table_invocation iv \<equiv>
case iv of PageTableMap cap ct_slot pde pd_slot \<Rightarrow> do
    set_cap cap ct_slot;
    store_pde pd_slot pde;
    do_machine_op $ cleanByVA_PoU pd_slot (addrFromPPtr pd_slot)
  od
  | PageTableUnmap (ArchObjectCap (PageTableCap p mapped_address)) ct_slot \<Rightarrow> do
    case mapped_address of Some (asid, vaddr) \<Rightarrow> do
      unmap_page_table asid vaddr p;
      slots \<leftarrow> return [p, p + (1 << pte_bits) .e. p + (1 << pt_bits) - 1];
      mapM_x (swp store_pte InvalidPTE) slots;
      do_machine_op $ cleanCacheRange_PoU p (p + (1 << pt_bits) - 1)
                                          (addrFromPPtr p)
    od | None \<Rightarrow> return ();
    cap \<leftarrow> liftM the_arch_cap $ get_cap ct_slot;
    set_cap (ArchObjectCap $ update_map_data cap None) ct_slot
  od
  | _ \<Rightarrow> fail"


definition perform_sgi_invocation :: "sgi_signal_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "perform_sgi_invocation iv \<equiv> case iv of
     SGISignalGenerate irq target \<Rightarrow> do_machine_op $ sendSGI (ucast irq) (ucast target)"

text \<open>Top level system call despatcher for all ARM-specific system calls.\<close>
definition
  arch_perform_invocation :: "arch_invocation \<Rightarrow> (data list,'z::state_ext) p_monad" where
  "arch_perform_invocation i \<equiv> liftE $
    case i of
          InvokePageTable oper \<Rightarrow> do perform_page_table_invocation oper; return [] od
        | InvokePageDirectory oper \<Rightarrow> do perform_page_directory_invocation oper; return [] od
        | InvokePage oper \<Rightarrow> perform_page_invocation oper
        | InvokeASIDControl oper \<Rightarrow> do perform_asid_control_invocation oper; return [] od
        | InvokeASIDPool oper \<Rightarrow> do perform_asid_pool_invocation oper; return [] od
        | InvokeVCPU oper \<Rightarrow> perform_vcpu_invocation oper
        | InvokeSGISignal oper \<Rightarrow> do perform_sgi_invocation oper; return [] od"

end

end
