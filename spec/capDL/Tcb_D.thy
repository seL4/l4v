(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Operations on thread control blocks.
 *)

theory Tcb_D
imports Invocations_D CSpace_D
begin

definition cdl_update_cnode_cap_data :: "cdl_cap \<Rightarrow> word32 \<Rightarrow> cdl_cap"
where "cdl_update_cnode_cap_data cap data  \<equiv>
  case cap of cdl_cap.CNodeCap oid _ _ sz \<Rightarrow> if data\<noteq>0 then
    (let reserved_bits = 3; guard_bits = 18; guard_size_bits = 5; new_guard_size = unat ((data >> reserved_bits) && mask guard_size_bits);
        new_guard =
          (data >> reserved_bits + guard_size_bits) && mask (min (unat ((data >> reserved_bits) && mask guard_size_bits)) guard_bits)
    in CNodeCap oid new_guard new_guard_size sz)
    else cap
  | _ \<Rightarrow> cap"

definition cdl_same_arch_obj_as :: "cdl_cap \<Rightarrow> cdl_cap \<Rightarrow> bool"
where "cdl_same_arch_obj_as capa capb \<equiv>
  case capa of AsidPoolCap x _ \<Rightarrow> (
        case capb of AsidPoolCap y _ \<Rightarrow>  y = x
        | _ \<Rightarrow> False)
  | AsidControlCap \<Rightarrow> (
       case capb of AsidControlCap \<Rightarrow> True
        | _ \<Rightarrow> False)
  | FrameCap dev ra _ sa _ _ \<Rightarrow> (
       case capb of FrameCap dev' rb _ sb _ _ \<Rightarrow> rb = ra \<and> sb = sa \<and> dev = dev'
        | _ \<Rightarrow> False)
  | cdl_cap.PageTableCap a _ _ \<Rightarrow> (
       case capb of cdl_cap.PageTableCap b _ _ \<Rightarrow> b = a
        | _ \<Rightarrow> False)
  | cdl_cap.PageDirectoryCap a _ _ \<Rightarrow> (
       case capb of cdl_cap.PageDirectoryCap b _ _ \<Rightarrow> b = a
        | _ \<Rightarrow> False)
  | _ \<Rightarrow> False"

definition
  decode_tcb_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
      cdl_tcb_intent \<Rightarrow> cdl_tcb_invocation except_monad"
where
  "decode_tcb_invocation target slot caps intent \<equiv> case intent of
       \<comment> \<open>Read another thread's registers.\<close>
       TcbReadRegistersIntent suspend flags count \<Rightarrow>
         returnOk (ReadRegisters (cap_object target) suspend 0 0) \<sqinter> throw

       \<comment> \<open>Write another thread's registers.\<close>
     | TcbWriteRegistersIntent resume flags count regs \<Rightarrow>
         returnOk (WriteRegisters (cap_object target) resume [0] 0) \<sqinter> throw

       \<comment> \<open>Copy registers from one thread to another.\<close>
     | TcbCopyRegistersIntent suspend_source resume_target f1 f2 f3 \<Rightarrow>
         doE
           (source_cap, _) \<leftarrow> throw_on_none $ get_index caps 0;
           source_tcb \<leftarrow> (
              case source_cap of
                  TcbCap x \<Rightarrow> returnOk x
                | _ \<Rightarrow> throw);
           target_tcb \<leftarrow> returnOk $ cap_object target;
           returnOk (CopyRegisters target_tcb source_tcb suspend_source resume_target f1 f2 0)
         odE \<sqinter> throw

       \<comment> \<open>Suspend the target thread.\<close>
     | TcbSuspendIntent \<Rightarrow>
         returnOk (Suspend (cap_object target)) \<sqinter> throw

       \<comment> \<open>Resume the target thread.\<close>
     | TcbResumeIntent \<Rightarrow>
         returnOk (Resume (cap_object target)) \<sqinter> throw

       \<comment> \<open>Configure: target, fault_ep, mcp, priority, cspace_root_data, vspace_root_data, buffer\<close>
     | TcbConfigureIntent fault_ep cspace_root_data vspace_root_data buffer \<Rightarrow>
         doE
           cspace_root \<leftarrow> throw_on_none $ get_index caps 0;
           vspace_root \<leftarrow> throw_on_none $ get_index caps 1;
           buffer_frame \<leftarrow> throw_on_none $ get_index caps 2;
           cspace_root_cap_ref \<leftarrow> returnOk $ (cdl_update_cnode_cap_data (fst cspace_root) cspace_root_data,snd cspace_root);
           vspace_root_cap_ref \<leftarrow> returnOk $ vspace_root;
           buffer_frame_opt \<leftarrow> returnOk $ (if (buffer \<noteq> 0) then Some (reset_mem_mapping (fst buffer_frame), snd buffer_frame) else None);
           returnOk (ThreadControl (cap_object target) slot (Some fault_ep)
               (Some cspace_root_cap_ref) (Some vspace_root_cap_ref) (buffer_frame_opt))
         odE \<sqinter> throw

       \<comment> \<open>Modify a thread's maximum control priority.\<close>
     | TcbSetMCPriorityIntent mcp \<Rightarrow>
         doE
           auth_cap \<leftarrow> throw_on_none $ get_index caps 0;
           returnOk (ThreadControl (cap_object target) slot None None None None)
         odE \<sqinter> throw

       \<comment> \<open>Modify a thread's priority.\<close>
     | TcbSetPriorityIntent priority \<Rightarrow>
         doE
           auth_cap \<leftarrow> throw_on_none $ get_index caps 0;
           returnOk (ThreadControl (cap_object target) slot None None None None)
         odE \<sqinter> throw

       \<comment> \<open>Modify a thread's mcp and priority at the same time.\<close>
     | TcbSetSchedParamsIntent mcp priority \<Rightarrow>
         doE
           auth_cap \<leftarrow> throw_on_none $ get_index caps 0;
           returnOk (ThreadControl (cap_object target) slot None None None None)
         odE \<sqinter> throw

       \<comment> \<open>Modify a thread's IPC buffer.\<close>
     | TcbSetIPCBufferIntent buffer \<Rightarrow>
         doE
           buffer_frame \<leftarrow> throw_on_none $ get_index caps 0;
           buffer_frame_opt \<leftarrow> returnOk $ (if (buffer \<noteq> 0) then Some (reset_mem_mapping (fst buffer_frame), snd buffer_frame) else None);
           returnOk (ThreadControl (cap_object target) slot None None None buffer_frame_opt)
         odE \<sqinter> throw

       \<comment> \<open>Update the various spaces (CSpace/VSpace) of a thread.\<close>
     | TcbSetSpaceIntent fault_ep cspace_root_data vspace_root_data \<Rightarrow>
         doE
           cspace_root \<leftarrow> throw_on_none $ get_index caps 0;
           vspace_root \<leftarrow> throw_on_none $ get_index caps 1;
           cspace_root_cap_ref \<leftarrow> returnOk $ (cdl_update_cnode_cap_data (fst cspace_root) cspace_root_data,snd cspace_root);
           vspace_root_cap_ref \<leftarrow> returnOk $ vspace_root;
           returnOk (ThreadControl (cap_object target) slot (Some fault_ep)
               (Some cspace_root_cap_ref) (Some vspace_root_cap_ref) None)
        odE \<sqinter> throw
     | TcbBindNTFNIntent \<Rightarrow> doE
           (ntfn_cap, _) \<leftarrow> throw_on_none $ get_index caps 0;
           returnOk (NotificationControl (cap_object target) (Some (cap_object ntfn_cap)))
         odE \<sqinter> throw
     | TcbUnbindNTFNIntent \<Rightarrow> returnOk (NotificationControl (cap_object target) None) \<sqinter> throw
     | TcbSetTLSBaseIntent \<Rightarrow> returnOk (SetTLSBase (cap_object target)) \<sqinter> throw
     | TcbSetFlagsIntent \<Rightarrow> returnOk (SetFlags (cap_object target)) \<sqinter> throw"


(* Delete the given slot of a TCB. *)

definition
  tcb_empty_thread_slot :: "cdl_object_id \<Rightarrow> cdl_cnode_index \<Rightarrow> unit preempt_monad"
where
  "tcb_empty_thread_slot target_tcb target_slot \<equiv> doE
    cap \<leftarrow> liftE $ get_cap (target_tcb,target_slot);
    whenE (cap \<noteq> NullCap) $
      delete_cap  (target_tcb, target_slot)
  odE"

(* Update the given slot of a TCB with a new cap, delete the previous
 * capability that was in the slot. *)

definition
  tcb_update_thread_slot :: "cdl_object_id \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cnode_index \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) \<Rightarrow> unit preempt_monad"
where
  "tcb_update_thread_slot target_tcb tcb_cap_slot target_slot pcap \<equiv>
         liftE (do
           thread_cap \<leftarrow> get_cap tcb_cap_slot;
           when (thread_cap = TcbCap target_tcb)
           (insert_cap_child (fst pcap) (snd pcap) (target_tcb, target_slot)
            \<sqinter> insert_cap_sibling (fst pcap) (snd pcap) (target_tcb,target_slot))
         od)"

(* Update a thread's CSpace root. *)
definition
  tcb_update_cspace_root :: "cdl_object_id \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap \<times> cdl_cap_ref \<Rightarrow> unit preempt_monad"
where
  "tcb_update_cspace_root target_tcb tcb_cap_ref croot \<equiv>
  doE
     tcb_empty_thread_slot target_tcb tcb_cspace_slot;
     src_cap \<leftarrow> liftE $ get_cap (snd croot);
     whenE (is_cnode_cap src_cap \<and> (cap_object src_cap = cap_object (fst croot)))
       $ tcb_update_thread_slot target_tcb tcb_cap_ref tcb_cspace_slot croot
  odE"

(* Update a thread's VSpace root. *)
definition
  tcb_update_vspace_root :: "cdl_object_id \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) \<Rightarrow> unit preempt_monad"
where
  "tcb_update_vspace_root target_tcb tcb_cap_ref vroot \<equiv>
  doE
     tcb_empty_thread_slot target_tcb tcb_vspace_slot;
     src_cap \<leftarrow> liftE $ get_cap (snd vroot);
     whenE (cdl_same_arch_obj_as (fst vroot) src_cap)
       $ tcb_update_thread_slot target_tcb tcb_cap_ref tcb_vspace_slot vroot
  odE"



(* Modify the TCB's intent to indicate an error during decode. *)
definition
  mark_tcb_intent_error :: "cdl_object_id \<Rightarrow> bool \<Rightarrow> unit k_monad"
where
  "mark_tcb_intent_error target_tcb has_error \<equiv>
      update_thread target_tcb (\<lambda>t. (t\<lparr>cdl_tcb_intent := (cdl_tcb_intent t)\<lparr>cdl_intent_error := has_error\<rparr>\<rparr>))"

(* Update a thread's IPC buffer. *)

definition
  tcb_update_ipc_buffer :: "cdl_object_id \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) \<Rightarrow> unit preempt_monad"
where
  "tcb_update_ipc_buffer target_tcb tcb_cap_ref ipc_buffer \<equiv>
     doE
       tcb_empty_thread_slot target_tcb tcb_ipcbuffer_slot;
       liftE $ corrupt_tcb_intent target_tcb;
       src_cap \<leftarrow> liftE $ get_cap (snd ipc_buffer);
       whenE (cdl_same_arch_obj_as (fst ipc_buffer) src_cap)
         $ tcb_update_thread_slot target_tcb tcb_cap_ref tcb_ipcbuffer_slot ipc_buffer
     odE
"

(* Resume a thread, aborting any pending operation, and revoking
 * any incoming reply caps. *)
definition
  restart :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "restart target_tcb \<equiv>
  do
     cap \<leftarrow> KHeap_D.get_cap (target_tcb,tcb_pending_op_slot);
     when (cap \<noteq> RestartCap \<and> cap\<noteq> RunningCap)
     (do
       CSpace_D.cancel_ipc target_tcb;
       KHeap_D.set_cap (target_tcb,tcb_replycap_slot) (cdl_cap.MasterReplyCap target_tcb);
       KHeap_D.set_cap (target_tcb,tcb_pending_op_slot) (cdl_cap.RestartCap)
      od)
  od"

(* Suspend a thread, aborting any pending operation, and revoking
 * any incoming reply caps. *)
definition
  suspend :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "suspend target_tcb \<equiv> CSpace_D.cancel_ipc target_tcb >>= K (KHeap_D.set_cap (target_tcb,tcb_pending_op_slot) cdl_cap.NullCap)"

definition
  bind_notification :: "cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> unit k_monad"
where
  "bind_notification tcb_id ntfn_id \<equiv> set_cap (tcb_id, tcb_boundntfn_slot) (BoundNotificationCap ntfn_id)"

definition
  invoke_tcb :: "cdl_tcb_invocation \<Rightarrow> unit preempt_monad"
where
  "invoke_tcb params \<equiv> case params of
    \<comment> \<open>Modify a thread's registers.\<close>
      WriteRegisters target_tcb resume _ _ \<Rightarrow>
        liftE $
        do
          corrupt_tcb_intent target_tcb;
          when resume $ restart target_tcb
        od

    \<comment> \<open>Read a thread's registers.\<close>
    | ReadRegisters src_tcb _ _ _ \<Rightarrow>
        liftE $ suspend src_tcb \<sqinter> return ()

    \<comment> \<open>Copy registers from one thread to another\<close>
    | CopyRegisters target_tcb source_tcb _ _ _ _ _ \<Rightarrow>
        liftE $
        do
          suspend source_tcb \<sqinter> return ();
          restart target_tcb \<sqinter> return ();
          corrupt_tcb_intent target_tcb
       od

    \<comment> \<open>Suspend this thread.\<close>
    | Suspend target_tcb \<Rightarrow>
        liftE $ suspend target_tcb \<sqinter> return ()

    \<comment> \<open>Resume this thread.\<close>
    | Resume target_tcb \<Rightarrow>
        liftE $ restart target_tcb

    \<comment> \<open>Update a thread's options.\<close>
    | ThreadControl target_tcb tcb_cap_slot faultep croot vroot ipc_buffer \<Rightarrow>
        doE
          case faultep of
              Some x \<Rightarrow> liftE $ update_thread target_tcb (\<lambda>tcb. tcb\<lparr>cdl_tcb_fault_endpoint := x\<rparr>)
            | None \<Rightarrow> returnOk ();

          \<comment> \<open>Possibly update CSpace\<close>
          case croot of
              Some x \<Rightarrow> tcb_update_cspace_root target_tcb tcb_cap_slot x
            | None \<Rightarrow> returnOk ();

          \<comment> \<open>Possibly update VSpace\<close>
          case vroot of
              Some x \<Rightarrow> tcb_update_vspace_root target_tcb tcb_cap_slot x
            | None \<Rightarrow> returnOk ();

          \<comment> \<open>Possibly update Ipc Buffer\<close>
          case ipc_buffer of
              Some x \<Rightarrow> tcb_update_ipc_buffer target_tcb tcb_cap_slot x
            | None \<Rightarrow> (returnOk () \<sqinter> (doE tcb_empty_thread_slot target_tcb tcb_ipcbuffer_slot;
                 liftE $ corrupt_tcb_intent target_tcb odE))
        odE
    | NotificationControl tcb ntfn \<Rightarrow>
          liftE $ (case ntfn of
             Some ntfn_id \<Rightarrow> bind_notification tcb ntfn_id
           | None \<Rightarrow> unbind_notification tcb)
    | SetTLSBase tcb \<Rightarrow> liftE $ corrupt_tcb_intent tcb
    | SetFlags tcb \<Rightarrow> liftE $ corrupt_tcb_intent tcb"

definition
  decode_domain_invocation :: "(cdl_cap \<times> cdl_cap_ref) list \<Rightarrow> cdl_domain_intent \<Rightarrow> cdl_domain_invocation except_monad"
where
  "decode_domain_invocation caps intent \<equiv> case intent of
     DomainSetIntent d \<Rightarrow> returnOk (SetDomain (cap_object (fst (hd caps))) d) \<sqinter> throw"

definition
  set_domain :: "cdl_object_id \<Rightarrow> word8 \<Rightarrow> unit k_monad"
where
  "set_domain tcb d \<equiv> update_thread tcb (\<lambda>t. (t\<lparr>cdl_tcb_domain := d \<rparr>))"

definition
  invoke_domain :: "cdl_domain_invocation \<Rightarrow> unit preempt_monad"
where
  "invoke_domain params \<equiv> case params of
     SetDomain tcb d \<Rightarrow> liftE $ set_domain tcb d"


end
