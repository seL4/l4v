(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Kernel_DP
imports
  "DSpec.Syscall_D"
  "SepDSpec.Types_SD"
begin

(* Bootinfo contructs *)

(* BootInfo record. Modelled on the C implementation, though only contains information needed for the booter. *)
type_synonym bi_slot_region = "cdl_cptr \<times> cdl_cptr"

record cdl_bootinfo =
  bi_untypes    :: bi_slot_region
  bi_free_slots :: bi_slot_region

(* Bootinfo constants *)
definition "seL4_CapNull                = (0 :: cdl_cptr)"
definition "seL4_CapInitThreadTCB       = (1 :: cdl_cptr)"
definition "seL4_CapInitThreadCNode     = (2 :: cdl_cptr)"
definition "seL4_CapInitThreadPD        = (3 :: cdl_cptr)"
definition "seL4_CapIRQControl          = (4 :: cdl_cptr)"
definition "seL4_CapASIDControl         = (5 :: cdl_cptr)"
definition "seL4_CapInitThreadASIDPool  = (6 :: cdl_cptr)"
definition "seL4_CapIOPort              = (7 :: cdl_cptr)"
definition "seL4_CapIOSpace             = (8 :: cdl_cptr)"
definition "seL4_CapBootInfoFrame       = (9 :: cdl_cptr)"
definition "seL4_CapInitThreadIPCBuffer = (10 :: cdl_cptr)"

(* This should be added as an axiom or something.
 * To be fixed when we have a better schedule story.
 *)
consts
  root_tcb_id :: cdl_object_id

text \<open>This wrapper lifts monadic operations on the underlying kernel state to
monadic operations on the user state.\<close>
definition
  do_kernel_op :: "(cdl_state, 'a) nondet_monad \<Rightarrow> (user_state, 'a) nondet_monad"
where
 "do_kernel_op kop \<equiv> do
    ms \<leftarrow> gets kernel_state;
    (r, ms') \<leftarrow> select_f (kop ms);
    modify (\<lambda>state. state \<lparr> kernel_state := ms' \<rparr>);
    return r
  od"

(* check error *)
definition thread_has_error :: "cdl_object_id \<Rightarrow> bool k_monad"
where
  "thread_has_error thread_ptr = do
    tcb \<leftarrow> get_thread thread_ptr;
    return (cdl_intent_error (cdl_tcb_intent tcb))
  od"

definition
  call_kernel_loop :: "event \<Rightarrow> unit k_monad"
where
  "call_kernel_loop ev = do
      \<comment> \<open>Deal with the event.\<close>
      whileLoop (\<lambda>rv s. isLeft rv)
        (\<lambda>_. handle_event ev
            <handle> (\<lambda> _. do handle_pending_interrupts; throwError PreemptError od)
            )
      (Inl PreemptError);
      schedule;
      t \<leftarrow> gets cdl_current_thread;
      case t of Some thread \<Rightarrow> do
       restart \<leftarrow> has_restart_cap thread;
       when restart $ set_cap (thread, tcb_pending_op_slot) RunningCap
      od | None \<Rightarrow> return ()
    od"

(* Kernel call functions *)
definition call_kernel_with_intent :: "cdl_full_intent \<Rightarrow>bool \<Rightarrow> bool k_monad"
where
  "call_kernel_with_intent full_intent check_error =
    do
      thread_ptr \<leftarrow> gets_the cdl_current_thread;
      assert (thread_ptr = root_tcb_id);
      domain \<leftarrow> gets cdl_current_domain;
      assert (domain = minBound);
      update_thread thread_ptr (cdl_tcb_intent_update (\<lambda>x. full_intent));
      call_kernel_loop $ SyscallEvent SysCall;
      ntptr \<leftarrow> gets_the cdl_current_thread;
      assert (thread_ptr = ntptr);
      ndomain \<leftarrow> gets cdl_current_domain;
      assert (minBound = ndomain);
      has_error \<leftarrow> thread_has_error thread_ptr;
      \<comment> \<open>capDL will need to be extended to support return types.\<close>
      when (check_error) (assert (\<not> has_error));
      return has_error
    od"

definition seL4_TCB_Configure :: "cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> cdl_raw_capdata \<Rightarrow> cdl_cptr \<Rightarrow> cdl_raw_capdata \<Rightarrow> word32 \<Rightarrow> cdl_cptr \<Rightarrow> bool u_monad"
where
  "seL4_TCB_Configure tcb_cap fault_ep cspace_root cspace_root_data vspace_root vspace_root_data buffer_addr buffer_frame \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ TcbIntent $ TcbConfigureIntent fault_ep cspace_root_data vspace_root_data buffer_addr,
       cdl_intent_error = False,
       cdl_intent_cap = tcb_cap,
       cdl_intent_extras = [cspace_root, vspace_root, buffer_frame],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_TCB_SetIPCBuffer :: "cdl_cptr \<Rightarrow> word32 \<Rightarrow> cdl_cptr
  \<Rightarrow> bool u_monad"
where
  "seL4_TCB_SetIPCBuffer tcb_cap buffer_addr buffer_frame \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ TcbIntent $ TcbSetIPCBufferIntent buffer_addr,
       cdl_intent_error = False,
       cdl_intent_cap = tcb_cap,
       cdl_intent_extras = [buffer_frame],
       cdl_intent_recv_slot = None\<rparr> False"

definition seL4_TCB_SetPriority :: "cdl_cptr \<Rightarrow> word8 \<Rightarrow> bool u_monad"
where
  "seL4_TCB_SetPriority tcb_cap priority \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ TcbIntent $ TcbSetPriorityIntent priority,
       cdl_intent_error = False,
       cdl_intent_cap = tcb_cap,
       cdl_intent_extras = [],
       cdl_intent_recv_slot = None\<rparr> False"

definition seL4_TCB_SetSpace :: "cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> cdl_raw_capdata \<Rightarrow> cdl_cptr \<Rightarrow> cdl_raw_capdata \<Rightarrow>  bool u_monad"
where
  "seL4_TCB_SetSpace tcb_cap fault_ep cspace_root cspace_root_data vspace_root vspace_root_data \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ TcbIntent $ TcbSetSpaceIntent fault_ep cspace_root_data vspace_root_data,
       cdl_intent_error = False,
       cdl_intent_cap = tcb_cap,
       cdl_intent_extras = [cspace_root, vspace_root],
       cdl_intent_recv_slot = None\<rparr> False"

definition seL4_TCB_Resume :: "cdl_cptr \<Rightarrow> bool u_monad"
where
  "seL4_TCB_Resume tcb_cap \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ TcbIntent $ TcbResumeIntent,
       cdl_intent_error = False,
       cdl_intent_cap = tcb_cap,
       cdl_intent_extras = [],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_TCB_WriteRegisters :: "cdl_cptr \<Rightarrow> bool \<Rightarrow> word8 \<Rightarrow> word32 \<Rightarrow> cdl_raw_usercontext \<Rightarrow> bool u_monad"
where
  "seL4_TCB_WriteRegisters tcb_cap resume_target arch_flags count regs \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ TcbIntent $ TcbWriteRegistersIntent resume_target arch_flags count regs,
       cdl_intent_error = False,
       cdl_intent_cap = tcb_cap,
       cdl_intent_extras = [],
       cdl_intent_recv_slot = None\<rparr> False"

definition seL4_Untyped_Retype :: "cdl_cptr \<Rightarrow> cdl_object_type \<Rightarrow> word32 \<Rightarrow> cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> bool u_monad"
where
  "seL4_Untyped_Retype untyped_cap type size_bits croot node_index node_depth node_offset node_window \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ UntypedIntent $ UntypedRetypeIntent type size_bits node_index node_depth node_offset node_window,
       cdl_intent_error = False,
       cdl_intent_cap = untyped_cap,
       cdl_intent_extras = [croot],
       cdl_intent_recv_slot = None\<rparr> False"

definition seL4_IRQControl_Get :: "cdl_cptr \<Rightarrow> cdl_irq \<Rightarrow> cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> bool u_monad"
where
  "seL4_IRQControl_Get control_cap irq croot node_index node_depth \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ IrqControlIntent $ IrqControlIssueIrqHandlerIntent irq node_index node_depth,
       cdl_intent_error = False,
       cdl_intent_cap = control_cap,
       cdl_intent_extras = [croot],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_IRQHandler_SetEndpoint :: "cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> bool u_monad"
where
  "seL4_IRQHandler_SetEndpoint handler_cap endpoint_cap \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ IrqHandlerIntent $ IrqHandlerSetEndpointIntent,
       cdl_intent_error = False,
       cdl_intent_cap = handler_cap,
       cdl_intent_extras = [endpoint_cap],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_ASIDPool_Assign :: "cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> bool u_monad"
where
  "seL4_ASIDPool_Assign asid_pool_cap pd \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ AsidPoolIntent $ AsidPoolAssignIntent,
       cdl_intent_error = False,
       cdl_intent_cap = asid_pool_cap,
       cdl_intent_extras = [pd],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_PageTable_Map :: "cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> word32 \<Rightarrow> cdl_raw_vmattrs \<Rightarrow> bool u_monad"
where
  "seL4_PageTable_Map sel4_page_table sel4_page_directory vaddr vmattribs \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ PageTableIntent $ PageTableMapIntent vaddr vmattribs,
       cdl_intent_error = False,
       cdl_intent_cap = sel4_page_table,
       cdl_intent_extras = [sel4_page_directory],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_Page_Map :: "cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> word32 \<Rightarrow> cdl_right set \<Rightarrow> cdl_raw_vmattrs \<Rightarrow> bool u_monad"
where
  "seL4_Page_Map sel4_page sel4_page_directory vaddr perms vmattribs \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ PageIntent $ PageMapIntent vaddr perms vmattribs,
       cdl_intent_error = False,
       cdl_intent_cap = sel4_page,
       cdl_intent_extras = [sel4_page_directory],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_CNode_Move :: "cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> bool u_monad"
where
  "seL4_CNode_Move dest_root dest_index dest_depth src_root src_index src_depth \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ CNodeIntent $ CNodeMoveIntent dest_index dest_depth src_index src_depth,
       cdl_intent_error = False,
       cdl_intent_cap = dest_root,
       cdl_intent_extras = [src_root],
       cdl_intent_recv_slot = None\<rparr> False"

definition seL4_CNode_Copy :: "cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32  \<Rightarrow> cdl_right set \<Rightarrow> bool u_monad"
where
  "seL4_CNode_Copy dest_root dest_index dest_depth src_root src_index src_depth rights \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ CNodeIntent $ CNodeCopyIntent dest_index dest_depth src_index src_depth rights,
       cdl_intent_error = False,
       cdl_intent_cap = dest_root,
       cdl_intent_extras = [src_root],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_CNode_Mint :: "cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32  \<Rightarrow> cdl_right set \<Rightarrow> cdl_raw_capdata \<Rightarrow> bool u_monad"
where
  "seL4_CNode_Mint dest_root dest_index dest_depth src_root src_index src_depth rights data \<equiv>
    do_kernel_op $ call_kernel_with_intent
       \<lparr>cdl_intent_op = Some $ CNodeIntent $ CNodeMintIntent dest_index dest_depth src_index src_depth rights data,
       cdl_intent_error = False,
       cdl_intent_cap = dest_root,
       cdl_intent_extras = [src_root],
       cdl_intent_recv_slot = None\<rparr> True"

definition seL4_CNode_Mutate :: "cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> cdl_cptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> cdl_raw_capdata \<Rightarrow> bool u_monad"
where
  "seL4_CNode_Mutate dest_root dest_index dest_depth src_root src_index src_depth data \<equiv>
    do_kernel_op $ call_kernel_with_intent
      \<lparr>cdl_intent_op = Some $ CNodeIntent $ CNodeMutateIntent dest_index dest_depth src_index src_depth data,
       cdl_intent_error = False,
       cdl_intent_cap = dest_root,
       cdl_intent_extras = [src_root],
       cdl_intent_recv_slot = None\<rparr> False"

(* End of kernel call funtions *)

end

