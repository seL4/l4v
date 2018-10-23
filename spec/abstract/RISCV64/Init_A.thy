(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "An Initial Kernel State"

theory Init_A
imports "../Retype_A"
begin

context Arch begin global_naming RISCV64_A

text \<open>
  This is not a specification of true kernel initialisation. This theory describes a dummy
  initial state only, to show that the invariants and refinement relation are consistent.
\<close>

definition riscv_global_pt_ptr :: obj_ref
  where
  "riscv_global_pt_ptr = kernel_base + 0x1000"

definition init_irq_node_ptr :: obj_ref
  where
  "init_irq_node_ptr = kernel_base + 0x2000"

definition init_arch_state :: arch_state
  where
  "init_arch_state \<equiv> \<lparr>
     riscv_asid_table = Map.empty,
     riscv_global_pt = riscv_global_pt_ptr,
     riscv_kernel_vspace = \<lambda>_. RISCVVSpaceKernelWindow  (* FIXME RISCV *)
   \<rparr>"

definition init_global_pt :: kernel_object
  where
  "init_global_pt \<equiv> ArchObj $ PageTable (\<lambda>_. InvalidPTE)"

definition init_kheap :: kheap
  where
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
      riscv_global_pt_ptr \<mapsto> init_global_pt
    )"

definition init_cdt :: cdt
  where
  "init_cdt \<equiv> Map.empty"

definition init_ioc :: "cslot_ptr \<Rightarrow> bool"
  where
  "init_ioc \<equiv>
   \<lambda>(a,b). (\<exists>obj. init_kheap a = Some obj \<and>
                  (\<exists>cap. cap_of obj b = Some cap \<and> cap \<noteq> cap.NullCap))"

definition init_A_st :: "'z::state_ext state"
  where
  "init_A_st \<equiv> \<lparr>
    kheap = init_kheap,
    cdt = init_cdt,
    is_original_cap = init_ioc,
    cur_thread = idle_thread_ptr,
    idle_thread = idle_thread_ptr,
    machine_state = init_machine_state,
    interrupt_irq_node = \<lambda>irq. init_irq_node_ptr + (ucast irq << cte_level_bits),
    interrupt_states = \<lambda>_. IRQInactive,
    arch_state = init_arch_state,
    exst = ext_init
  \<rparr>"

end
end
