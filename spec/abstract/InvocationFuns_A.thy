(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Monad instantiations, handling of faults, errors, and interrupts.
*)

chapter "Basic Kernel and Exception Monads"

theory InvocationFuns_A
imports Ipc_A
begin

section \<open>Allow preemption at this point.\<close>
definition
  preemption_point :: "(unit,'z::state_ext) p_monad" where
 "preemption_point \<equiv> doE liftE $ do_extended_op update_work_units;
                         OR_choiceE (work_units_limit_reached)
                           (doE liftE $ do_extended_op reset_work_units;
                                irq_opt \<leftarrow> liftE $ do_machine_op (getActiveIRQ True);
                                case_option (do
                                               update_time_stamp;
                                               result \<leftarrow> check_budget;
                                               if (\<not> result)
                                               then returnOk ()
                                               else (throwError $ ())
                                             od)
                                            (K (throwError $ ())) irq_opt
                           odE) (returnOk ())
                     odE"


section \<open>invoke\_untyped\<close>

text \<open>Untyped capabilities note a currently free region. Sometimes this
region is reset during a Retype operation. This progressively clears the
underlying memory and also the object level representation, moving the free
region pointer back to the start of the newly cleared region each time.\<close>
definition
  reset_untyped_cap :: "cslot_ptr \<Rightarrow> (unit,'z::state_ext) p_monad"
where
  "reset_untyped_cap src_slot = doE
  cap \<leftarrow> liftE $ get_cap src_slot;
  sz \<leftarrow> returnOk $ bits_of cap;
  base \<leftarrow> returnOk $ obj_ref_of cap;
  if free_index_of cap = 0
    then returnOk ()
  else doE
    liftE $ delete_objects base sz;
  dev \<leftarrow> returnOk $ is_device_untyped_cap cap;

  if dev \<or> sz < reset_chunk_bits
      then liftE $ do
        unless dev $ do_machine_op $ clearMemory base (2 ^ sz);
        set_cap (UntypedCap dev base sz 0) src_slot
      od
    else mapME_x (\<lambda>i. doE
          liftE $ do_machine_op $ clearMemory (base + (of_nat i << reset_chunk_bits))
              (2 ^ reset_chunk_bits);
          liftE $ set_cap (UntypedCap dev base sz
              (i * 2 ^ reset_chunk_bits)) src_slot;
          preemption_point
        odE) (rev [i \<leftarrow> [0 ..< 2 ^ (sz - reset_chunk_bits)].
            i * 2 ^ reset_chunk_bits < free_index_of cap])
    odE
  odE"

text \<open>Untyped capabilities confer authority to the Retype method. This
clears existing objects from a region, creates new objects of the requested type,
initialises them and installs new capabilities to them.\<close>
definition
  invoke_untyped :: "untyped_invocation \<Rightarrow> (unit,'z::state_ext) p_monad"
where
"invoke_untyped ui \<equiv> case ui
    of Retype src_slot reset base retype_base new_type obj_sz slots is_device \<Rightarrow>
doE
  whenE reset $ reset_untyped_cap src_slot;
  liftE $ do

  cap \<leftarrow> get_cap src_slot;

  \<comment> \<open>Update the untyped cap to track the amount of space used.\<close>
  total_object_size \<leftarrow> return $ (of_nat (length slots) << (obj_bits_api new_type obj_sz));
  free_ref \<leftarrow> return $ retype_base + total_object_size;
  set_cap (UntypedCap is_device base (bits_of cap) (unat (free_ref - base))) src_slot;

  \<comment> \<open>Create new objects.\<close>
  orefs \<leftarrow> retype_region retype_base (length slots) obj_sz new_type is_device;
  init_arch_objects new_type retype_base (length slots) obj_sz orefs;
  mapM_x (create_cap new_type obj_sz src_slot is_device) (zip slots orefs)
od odE"


section \<open>invoke\_cnode\<close>

text \<open>The complete recursive delete operation.\<close>
function (sequential)
  rec_del :: "rec_del_call \<Rightarrow> (bool * cap,'z::state_ext) p_monad"
where
  "rec_del (CTEDeleteCall slot exposed) s =
 (doE
    (success, cleanup_info) \<leftarrow> rec_del (FinaliseSlotCall slot exposed);
    without_preemption $ when (exposed \<or> success) $ empty_slot slot cleanup_info;
    returnOk undefined
  odE) s"
|
  "rec_del (FinaliseSlotCall slot exposed) s =
 (doE
    cap \<leftarrow> without_preemption $ get_cap slot;
    if cap = NullCap
    then returnOk (True, NullCap)
    else (doE
      is_final \<leftarrow> without_preemption $ is_final_cap cap;
      (remainder, cleanup_info) \<leftarrow> without_preemption $ finalise_cap cap is_final;
      if cap_removeable remainder slot
      then returnOk (True, cleanup_info)
      else if cap_cyclic_zombie remainder slot \<and> \<not> exposed
      then doE
        without_preemption $ set_cap remainder slot;
        returnOk (False, NullCap)
      odE
      else doE
        without_preemption $ set_cap remainder slot;
        rec_del (ReduceZombieCall remainder slot exposed);
        preemption_point;
        rec_del (FinaliseSlotCall slot exposed)
      odE
    odE)
  odE) s"

| "rec_del (ReduceZombieCall (Zombie ptr bits (Suc n)) slot False) s =
 (doE
    cn \<leftarrow> returnOk $ first_cslot_of (Zombie ptr bits (Suc n));
    assertE (cn \<noteq> slot);
    without_preemption $ cap_swap_for_delete cn slot;
    returnOk undefined
  odE) s"
|
 "rec_del (ReduceZombieCall (Zombie ptr bits (Suc n)) slot True) s =
 (doE
    end_slot \<leftarrow> returnOk (ptr, nat_to_cref (zombie_cte_bits bits) n);
    rec_del (CTEDeleteCall end_slot False);
    new_cap \<leftarrow> without_preemption $ get_cap slot;
    if new_cap = Zombie ptr bits (Suc n)
    then without_preemption $ set_cap (Zombie ptr bits n) slot
    else assertE (new_cap = NullCap \<or>
                  is_zombie new_cap \<and> first_cslot_of new_cap = slot
                   \<and> first_cslot_of (Zombie ptr bits (Suc n)) \<noteq> slot);
    returnOk undefined
  odE) s"
|
 "rec_del (ReduceZombieCall cap slot exposed) s =
  fail s"
  by pat_completeness auto

text \<open>Delete a capability by calling the recursive delete operation.\<close>
definition
  cap_delete :: "cslot_ptr \<Rightarrow> (unit, 'z::state_ext) p_monad" where
 "cap_delete slot \<equiv> doE rec_del (CTEDeleteCall slot True); returnOk () odE"

text \<open>Prepare the capability in a slot for deletion but do not delete it.\<close>
definition
  finalise_slot :: "cslot_ptr \<Rightarrow> bool \<Rightarrow> (bool * cap,'z::state_ext) p_monad"
where
  "finalise_slot p e \<equiv> rec_del (FinaliseSlotCall p e)"

text \<open>Helper functions for the type of recursive delete calls.\<close>
primrec
  exposed_rdcall :: "rec_del_call \<Rightarrow> bool"
where
  "exposed_rdcall (CTEDeleteCall slot exposed) = exposed"
| "exposed_rdcall (FinaliseSlotCall slot exposed) = exposed"
| "exposed_rdcall (ReduceZombieCall cap slot exposed) = exposed"

primrec
  isCTEDeleteCall :: "rec_del_call \<Rightarrow> bool"
where
  "isCTEDeleteCall (CTEDeleteCall slot exposed) = True"
| "isCTEDeleteCall (FinaliseSlotCall slot exposed) = False"
| "isCTEDeleteCall (ReduceZombieCall cap slot exposed) = False"

primrec
  slot_rdcall :: "rec_del_call \<Rightarrow> cslot_ptr"
where
  "slot_rdcall (CTEDeleteCall slot exposed) = slot"
| "slot_rdcall (FinaliseSlotCall slot exposed) = slot"
| "slot_rdcall (ReduceZombieCall cap slot exposed) = slot"

text \<open>Revoke the derived capabilities of a given capability, deleting them
all.\<close>

function cap_revoke :: "cslot_ptr \<Rightarrow> (unit, 'z::state_ext) p_monad"
where
"cap_revoke slot s = (doE
    cap \<leftarrow> without_preemption $ get_cap slot;
    cdt \<leftarrow> without_preemption $ gets cdt;
    descendants \<leftarrow> returnOk $ descendants_of slot cdt;
    whenE (cap \<noteq> NullCap \<and> descendants \<noteq> {}) (doE
      child \<leftarrow> without_preemption $ select_ext (next_revoke_cap slot) descendants;
      cap \<leftarrow> without_preemption $ get_cap child;
      assertE (cap \<noteq> NullCap);
      cap_delete child;
      preemption_point;
      cap_revoke slot
    odE)
odE) s"
by auto

text \<open>Invoking CNode capabilities\<close>

text \<open>The CNode capability confers authority to various methods
which act on CNodes and the capabilities within them. Copies of
capabilities may be inserted in empty CNode slots by
Insert. Capabilities may be moved to empty slots with Move or swapped
with others in a three way rotate by Rotate. A Reply capability stored
in a thread's last-caller slot may be saved into a regular CNode slot
with Save.  The Revoke, Delete and Recycle methods may also be
invoked on the capabilities stored in the CNode.\<close>

definition
  invoke_cnode :: "cnode_invocation \<Rightarrow> (unit, 'z::state_ext) p_monad" where
  "invoke_cnode i \<equiv> case i of
    RevokeCall dest_slot \<Rightarrow> cap_revoke dest_slot
  | DeleteCall dest_slot \<Rightarrow> cap_delete dest_slot
  | InsertCall cap src_slot dest_slot \<Rightarrow>
       without_preemption $ cap_insert cap src_slot dest_slot
  | MoveCall cap src_slot dest_slot \<Rightarrow>
       without_preemption $ cap_move cap src_slot dest_slot
  | RotateCall cap1 cap2 slot1 slot2 slot3 \<Rightarrow>
       without_preemption $
       if slot1 = slot3 then
         cap_swap cap1 slot1 cap2 slot2
       else
         do cap_move cap2 slot2 slot3; cap_move cap1 slot1 slot2 od
  | CancelBadgedSendsCall (EndpointCap ep b R) \<Rightarrow>
    without_preemption $ when (b \<noteq> 0) $ cancel_badged_sends ep b
  | CancelBadgedSendsCall _ \<Rightarrow> fail"



section \<open>invoke\_tcb\<close>

definition
  install_tcb_cap :: "obj_ref \<Rightarrow> cslot_ptr \<Rightarrow> nat \<Rightarrow> (cap \<times> cslot_ptr) option \<Rightarrow> (unit, 'z::state_ext) p_monad"
where
  "install_tcb_cap target slot n slot_opt \<equiv>
     case slot_opt of None \<Rightarrow> returnOk ()
     | Some (new_cap, src_slot) \<Rightarrow> doE
      cap_delete (target, tcb_cnode_index n);
      unlessE (new_cap = NullCap) $
              liftE $ check_cap_at new_cap src_slot
                    $ check_cap_at (ThreadCap target) slot
                    $ cap_insert new_cap src_slot (target, tcb_cnode_index n)
    odE"

definition
  install_tcb_frame_cap :: "obj_ref \<Rightarrow> cslot_ptr \<Rightarrow> (vspace_ref \<times> (cap \<times> cslot_ptr) option) option \<Rightarrow> (unit, 'z::state_ext) p_monad"
where
  "install_tcb_frame_cap target slot buffer \<equiv>
     case buffer of
       None \<Rightarrow> returnOk ()
     | Some (ptr, frame)
         \<Rightarrow> doE
              cap_delete (target, tcb_cnode_index 2);
              liftE $ thread_set (\<lambda>t. t \<lparr> tcb_ipc_buffer := ptr \<rparr>) target;
              liftE $ case frame of
                        None \<Rightarrow> return ()
                      | Some (new_cap, src_slot)
                          \<Rightarrow>  check_cap_at new_cap src_slot
                              $ check_cap_at (ThreadCap target) slot
                              $ cap_insert new_cap src_slot (target, tcb_cnode_index 2);
              cur \<leftarrow> liftE $ gets cur_thread;
              liftE $ when (target = cur) reschedule_required
            odE"

text \<open>TCB capabilities confer authority to perform seven actions. A thread can
request to yield its timeslice to another, to suspend or resume another, to
reconfigure another thread, or to copy register sets into, out of or between
other threads.\<close>
fun
  invoke_tcb :: "tcb_invocation \<Rightarrow> (data list, 'z::state_ext) p_monad"
where
  "invoke_tcb (Suspend thread) = liftE (do suspend thread; return [] od)"
| "invoke_tcb (Resume thread) = liftE (do restart thread; return [] od)"

| "invoke_tcb (ThreadControlCaps target slot fault_handler timeout_handler croot vroot buffer)
   = doE
    install_tcb_cap target slot 3 fault_handler;
    install_tcb_cap target slot 4 timeout_handler;
    install_tcb_cap target slot 0 croot;
    install_tcb_cap target slot 1 vroot;
    install_tcb_frame_cap target slot buffer;
    returnOk []
  odE"

| "invoke_tcb (ThreadControlSched target slot fault_handler mcp priority sc)
   = doE
    install_tcb_cap target slot 3 fault_handler;
    liftE $ maybeM (\<lambda>(newmcp, _). set_mcpriority target newmcp) mcp;
    liftE $ maybeM (\<lambda>(prio, _). set_priority target prio) priority;
    liftE $ maybeM (\<lambda>scopt. case scopt of
                              None \<Rightarrow> maybe_sched_context_unbind_tcb target
                            | Some sc_ptr \<Rightarrow> maybe_sched_context_bind_tcb sc_ptr target) sc;
    returnOk []
  odE"

| "invoke_tcb (CopyRegisters dest src suspend_source resume_target transfer_frame transfer_integer transfer_arch) =
  (liftE $ do
    when suspend_source $ suspend src;
    when resume_target $ restart dest;
    when transfer_frame $ do
        mapM_x (\<lambda>r. do
                v \<leftarrow> as_user src $ getRegister r;
                as_user dest $ setRegister r v
        od) frame_registers;
        pc \<leftarrow> as_user dest getRestartPC;
        as_user dest $ setNextPC pc
    od;
    when transfer_integer $
        mapM_x (\<lambda>r. do
                v \<leftarrow> as_user src $ getRegister r;
                as_user dest $ setRegister r v
        od) gpRegisters;
    cur \<leftarrow> gets cur_thread;
    arch_post_modify_registers cur dest;
    when (dest = cur) reschedule_required;
    return []
  od)"

| "invoke_tcb (ReadRegisters src suspend_source n arch) =
  (liftE $ do
    when suspend_source $ suspend src;
    self \<leftarrow> gets cur_thread;
    regs \<leftarrow> return (take (unat n) $ frame_registers @ gp_registers);
    as_user src $ mapM getRegister regs
  od)"

| "invoke_tcb (WriteRegisters dest resume_target values arch) =
  (liftE $ do
    self \<leftarrow> gets cur_thread;
    b \<leftarrow> arch_get_sanitise_register_info dest;
    as_user dest $ do
        zipWithM (\<lambda>r v. setRegister r (sanitise_register b r v))
            (frameRegisters @ gpRegisters) values;
        pc \<leftarrow> getRestartPC;
        setNextPC pc
    od;
    arch_post_modify_registers self dest;
    when resume_target $ restart dest;
    when (dest = self) reschedule_required;
    return []
  od)"

| "invoke_tcb (NotificationControl tcb (Some ntfnptr)) =
  (liftE $ do
    bind_notification tcb ntfnptr;
    return []
  od)"

| "invoke_tcb (NotificationControl tcb None) =
  (liftE $ do
    unbind_notification tcb;
    return []
  od)"

| "invoke_tcb (SetTLSBase tcb tls_base) =
  (liftE $ do
    as_user tcb $ setRegister tlsBaseRegister tls_base;
    cur \<leftarrow> gets cur_thread;
    when (tcb = cur) reschedule_required;
    return []
  od)"



end
