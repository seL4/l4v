(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
Dummy initial kernel state. Real kernel boot up is more complex.
*)

chapter "An Initial Kernel State"

theory Init_A
imports "../Retype_A"
begin
(*FIXME x64: needs to be defined such that x64 invariants hold *)

context Arch begin global_naming X64_A

text {* 
  This is not a specification of true kernel
  initialisation. This theory describes a dummy initial state only, to
  show that the invariants and refinement relation are consistent. 
*}



definition
  init_tcb_ptr :: obj_ref where
  "init_tcb_ptr = kernel_base + 0x2000"

definition
  init_irq_node_ptr :: obj_ref where
  "init_irq_node_ptr = kernel_base + 0x3000"

definition
  "init_arch_state \<equiv> undefined :: arch_state"

definition
  empty_context :: user_context where
  "empty_context \<equiv> \<lambda>_. 0"


definition
  "init_kheap \<equiv>
  (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
       then Some (CNode 0 (empty_cnode 0)) else None)
  (idle_thread_ptr \<mapsto> TCB \<lparr>
    tcb_ctable = NullCap,
    tcb_vtable = NullCap,
    tcb_reply = NullCap,
    tcb_caller = NullCap,
    tcb_ipcframe = NullCap,
    tcb_state = IdleThreadState,
    tcb_fault_handler = replicate word_bits False,
    tcb_ipc_buffer = 0,
    tcb_context = empty_context,
    tcb_fault = None,
    tcb_bound_notification = None
  \<rparr>
  )"

definition
  "init_cdt \<equiv> empty"

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
