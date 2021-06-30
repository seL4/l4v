(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Decoding system calls
*)

chapter "Decoding System Calls"

theory Decode_A
imports
  Interrupt_A
  "./$L4V_ARCH/ArchDecode_A"
  "ExecSpec.InvocationLabels_H"
begin

context begin interpretation Arch .

requalify_consts
  ArchDefaultExtraRegisters
  check_valid_ipc_buffer
  is_valid_vtable_root
  arch_decode_irq_control_invocation
  arch_data_to_obj_type
  arch_decode_invocation
  arch_check_irq

end


text \<open>
  This theory includes definitions describing how user arguments are
decoded into invocation structures; these structures are then used
to perform the actual system call (see @{text "perform_invocation"}).
In addition, these definitions check the validity of these arguments,
throwing an error if given an invalid request.

  As such, this theory describes the binary interface between the
user and the kernel, along with the preconditions on each argument.
\<close>


section "CNode"

text \<open>This definition decodes CNode invocations.\<close>

definition
  decode_cnode_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (cnode_invocation,'z::state_ext) se_monad"
where
"decode_cnode_invocation label args cap excaps \<equiv> doE
  unlessE (gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeRotate]) $
    throwError IllegalOperation;
  whenE (length args < 2) (throwError TruncatedMessage);
  index \<leftarrow> returnOk $ data_to_cptr $ args ! 0;
  bits \<leftarrow> returnOk $ data_to_nat $ args ! 1;
  args \<leftarrow> returnOk $ drop 2 args;
  dest_slot \<leftarrow> lookup_target_slot cap index bits;
  if length args \<ge> 2 \<and> length excaps > 0
        \<and> gen_invocation_type label \<in> set [CNodeCopy .e. CNodeMutate] then
  doE
    src_index \<leftarrow> returnOk $ data_to_cptr $ args ! 0;
    src_depth \<leftarrow> returnOk $ data_to_nat $ args ! 1;
    args \<leftarrow> returnOk $ drop 2 args;
    src_root_cap \<leftarrow> returnOk $ excaps ! 0;
    ensure_empty dest_slot;
    src_slot \<leftarrow>
         lookup_source_slot src_root_cap src_index src_depth;
    src_cap \<leftarrow> liftE $ get_cap src_slot;
    whenE (src_cap = NullCap) $
         throwError $ FailedLookup True $ MissingCapability src_depth;
    (rights, cap_data, is_move) \<leftarrow> case (gen_invocation_type label, args) of
      (CNodeCopy, rightsWord # _) \<Rightarrow> doE
                    rights \<leftarrow> returnOk $ data_to_rights $ rightsWord;
                    returnOk $ (rights, None, False)
                odE
     | (CNodeMint, rightsWord # capData # _) \<Rightarrow> doE
                    rights \<leftarrow> returnOk $ data_to_rights $ rightsWord;
                    returnOk $ (rights, Some capData, False)
                odE
     | (CNodeMove, _) \<Rightarrow> returnOk (all_rights, None, True)
     | (CNodeMutate, capData # _) \<Rightarrow> returnOk (all_rights, Some capData, True)
     | _ \<Rightarrow> throwError TruncatedMessage;
    src_cap \<leftarrow> returnOk $ mask_cap rights src_cap;
    new_cap \<leftarrow> (if is_move then returnOk else derive_cap src_slot) (case cap_data of
                  Some w \<Rightarrow> update_cap_data is_move w src_cap
                | None \<Rightarrow> src_cap);
    whenE (new_cap = NullCap) $ throwError IllegalOperation;
    returnOk $ (if is_move then MoveCall else InsertCall) new_cap src_slot dest_slot
  odE
  else if gen_invocation_type label = CNodeRevoke then returnOk $ RevokeCall dest_slot
  else if gen_invocation_type label = CNodeDelete then returnOk $ DeleteCall dest_slot
  else if gen_invocation_type label = CNodeCancelBadgedSends then doE
    cap \<leftarrow> liftE $ get_cap dest_slot;
    unlessE (has_cancel_send_rights cap) $ throwError IllegalOperation;
    returnOk $ CancelBadgedSendsCall cap
  odE
  else if gen_invocation_type label = CNodeRotate \<and> length args > 5
          \<and> length excaps > 1 then
  doE
    pivot_new_data \<leftarrow> returnOk $ args ! 0;
    pivot_index \<leftarrow> returnOk $ data_to_cptr $ args ! 1;
    pivot_depth \<leftarrow> returnOk $ data_to_nat $ args ! 2;
    src_new_data \<leftarrow> returnOk $ args ! 3;
    src_index \<leftarrow> returnOk $ data_to_cptr $ args ! 4;
    src_depth \<leftarrow> returnOk $ data_to_nat $ args ! 5;
    pivot_root_cap <- returnOk $ excaps ! 0;
    src_root_cap <- returnOk $ excaps ! 1;

    src_slot <- lookup_source_slot src_root_cap src_index src_depth;
    pivot_slot <- lookup_pivot_slot pivot_root_cap pivot_index pivot_depth;

    whenE (pivot_slot = src_slot \<or> pivot_slot = dest_slot) $
      throwError IllegalOperation;

    unlessE (src_slot = dest_slot) $ ensure_empty dest_slot;

    src_cap <- liftE $ get_cap src_slot;
    whenE (src_cap = NullCap) $
      throwError $ FailedLookup True $ MissingCapability src_depth;

    pivot_cap <- liftE $ get_cap pivot_slot;
    whenE (pivot_cap = NullCap) $
      throwError $ FailedLookup False $ MissingCapability pivot_depth;

    new_src_cap \<leftarrow> returnOk $ update_cap_data True src_new_data src_cap;
    new_pivot_cap \<leftarrow> returnOk $ update_cap_data True pivot_new_data pivot_cap;

    whenE (new_src_cap = NullCap) $ throwError IllegalOperation;
    whenE (new_pivot_cap = NullCap) $ throwError IllegalOperation;

    returnOk $ RotateCall new_src_cap new_pivot_cap src_slot pivot_slot dest_slot
  odE
  else
    throwError TruncatedMessage
odE"

section "Threads"

text \<open>The definitions in this section decode invocations on TCBs.\<close>

definition
  decode_read_registers :: "data list \<Rightarrow> cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_read_registers data cap \<equiv> case data of
  flags#n#_ \<Rightarrow> doE
    range_check n 1 $ of_nat (length frameRegisters + length gpRegisters);
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    self \<leftarrow> liftE $ gets cur_thread;
    whenE (p = self) $ throwError IllegalOperation;
    returnOk $ ReadRegisters p (flags !! 0) n ArchDefaultExtraRegisters
  odE
| _ \<Rightarrow> throwError TruncatedMessage"

definition
  decode_copy_registers :: "data list \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_copy_registers data cap extra_caps \<equiv> case data of
  flags#_ \<Rightarrow>  doE
    suspend_source \<leftarrow> returnOk (flags !! 0);
    resume_target \<leftarrow> returnOk (flags !! 1);
    transfer_frame \<leftarrow> returnOk (flags !! 2);
    transfer_integer \<leftarrow> returnOk (flags !! 3);
    whenE (extra_caps = []) $ throwError TruncatedMessage;
    src_tcb \<leftarrow> (case extra_caps of
      ThreadCap p # _ \<Rightarrow> returnOk p
    | _ \<Rightarrow> throwError $ InvalidCapability 1);
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    returnOk $ CopyRegisters p src_tcb
                             suspend_source resume_target
                             transfer_frame transfer_integer
                             ArchDefaultExtraRegisters
  odE
| _ \<Rightarrow>  throwError TruncatedMessage"


definition
  decode_write_registers :: "data list \<Rightarrow> cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_write_registers data cap \<equiv> case data of
  flags#n#values \<Rightarrow> doE
    whenE (length values < unat n) $ throwError TruncatedMessage;
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    self \<leftarrow> liftE $ gets cur_thread;
    whenE (p = self) $ throwError IllegalOperation;
    returnOk $ WriteRegisters p (flags !! 0)
               (take (unat n) values) ArchDefaultExtraRegisters
  odE
| _ \<Rightarrow> throwError TruncatedMessage"


definition
  check_prio :: "data \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "check_prio new_prio auth_tcb \<equiv>
    doE
      mcp \<leftarrow> liftE $ thread_get tcb_mcpriority auth_tcb;
      whenE (new_prio > ucast mcp) $ throwError (RangeError 0 (ucast mcp))
    odE"


definition
  decode_set_priority :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_priority args cap slot extra_caps \<equiv> doE
     whenE (length args = 0 \<or> length extra_caps = 0) $ throwError TruncatedMessage;
     prio \<leftarrow> returnOk $ ucast (args ! 0);
     auth_tcb \<leftarrow> case fst (extra_caps ! 0) of
         ThreadCap tcb_ptr \<Rightarrow> returnOk tcb_ptr
       | _ \<Rightarrow> throwError (InvalidCapability 1);
     check_prio (args ! 0) auth_tcb;
     returnOk (ThreadControlSched (obj_ref_of cap) slot None None
                             (Some (prio, auth_tcb)) None)
     odE"


definition
  decode_set_mcpriority :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_mcpriority args cap slot extra_caps \<equiv> doE
     whenE (length args = 0 \<or> length extra_caps = 0) $ throwError TruncatedMessage;
     new_mcp \<leftarrow> returnOk $ ucast $ args ! 0;
     auth_tcb \<leftarrow> case fst (extra_caps ! 0) of
         ThreadCap tcb_ptr \<Rightarrow> returnOk tcb_ptr
       | _ \<Rightarrow> throwError (InvalidCapability 1);
     check_prio (args ! 0) auth_tcb;
     returnOk (ThreadControlSched (obj_ref_of cap) slot None (Some (new_mcp, auth_tcb))
                             None None)
     odE"


definition
  decode_set_ipc_buffer ::
  "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_set_ipc_buffer args cap slot excs \<equiv> doE
  whenE (length args = 0) $ throwError TruncatedMessage;
  whenE (length excs = 0) $ throwError TruncatedMessage;
  buffer \<leftarrow> returnOk $ data_to_vref $ args ! 0;
  (bcap, bslot) \<leftarrow> returnOk $ excs ! 0;
  newbuf \<leftarrow> if buffer = 0 then returnOk None
           else doE
      buffer_cap \<leftarrow> derive_cap bslot bcap;
      check_valid_ipc_buffer buffer buffer_cap;
      returnOk $ Some (buffer_cap, bslot)
    odE;
  returnOk $
    ThreadControlCaps (obj_ref_of cap) slot None None None None (Some (buffer, newbuf))
odE"

definition has_handler_rights :: "cap \<Rightarrow> bool" where
  "has_handler_rights cap \<equiv>
     AllowSend \<in> cap_rights cap \<and> {AllowGrant, AllowGrantReply} \<inter> cap_rights cap \<noteq> {}"

definition valid_fault_handler :: "cap \<Rightarrow> bool" where
  "valid_fault_handler \<equiv> is_ep_cap and has_handler_rights or (=) NullCap"

definition
  check_handler_ep :: "nat \<Rightarrow> (cap \<times> cslot_ptr) \<Rightarrow> ((cap \<times> cslot_ptr),'z::state_ext) se_monad"
where
  "check_handler_ep pos h_cap_h_slot \<equiv> doE
    unlessE (valid_fault_handler $ fst h_cap_h_slot) $ throwError $ InvalidCapability pos;
    returnOk h_cap_h_slot
  odE"

definition
  decode_cv_space
  :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_cv_space args cap slot excaps \<equiv> doE
   whenE (length args < 2 \<or> length excaps < 2) $ throwError TruncatedMessage;
   croot_data  \<leftarrow> returnOk $ args ! 0;
   vroot_data  \<leftarrow> returnOk $ args ! 1;
   croot_arg  \<leftarrow> returnOk $ excaps ! 0;
   vroot_arg  \<leftarrow> returnOk $ excaps ! 1;
   can_chg_cr \<leftarrow> liftE $ liftM Not $ slot_cap_long_running_delete
                      $ get_tcb_ctable_ptr $ obj_ref_of cap;
   can_chg_vr \<leftarrow> liftE $ liftM Not $ slot_cap_long_running_delete
                      $ get_tcb_vtable_ptr $ obj_ref_of cap;
   unlessE (can_chg_cr \<and> can_chg_vr) $ throwError IllegalOperation;

   croot_cap  \<leftarrow> returnOk $ fst croot_arg;
   croot_slot \<leftarrow> returnOk $ snd croot_arg;
   croot_cap' \<leftarrow> derive_cap croot_slot $
                   (if croot_data = 0 then id else update_cap_data False croot_data)
                   croot_cap;
   unlessE (is_cnode_cap croot_cap') $ throwError IllegalOperation;
   croot \<leftarrow> returnOk (croot_cap', croot_slot);

   vroot_cap  \<leftarrow> returnOk $ fst vroot_arg;
   vroot_slot \<leftarrow> returnOk $ snd vroot_arg;
   vroot_cap' \<leftarrow> derive_cap vroot_slot $
                   (if vroot_data = 0 then id else update_cap_data False vroot_data)
                   vroot_cap;
   unlessE (is_valid_vtable_root vroot_cap') $ throwError IllegalOperation;
   vroot \<leftarrow> returnOk (vroot_cap', vroot_slot);

   returnOk $ ThreadControlCaps (obj_ref_of cap) slot None None
                            (Some croot) (Some vroot) None
 odE"


definition
  decode_set_space
  :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_space args cap slot excaps \<equiv> doE
    whenE (length args < 2 \<or> length excaps < 3) $ throwError TruncatedMessage;
    space \<leftarrow> decode_cv_space (take 2 args) cap slot (take 2 (drop 1 excaps));
    fh_arg  \<leftarrow> returnOk $ excaps ! 0;
    fault_handler \<leftarrow> check_handler_ep 1 fh_arg;
    returnOk $ ThreadControlCaps (obj_ref_of cap) slot (Some fault_handler) None
                            (tc_new_croot space) (tc_new_vroot space) None
 odE"

definition
  decode_update_sc :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> (obj_ref option,'z::state_ext) se_monad"
where
  "decode_update_sc cap slot sc_cap \<equiv>
    (case sc_cap of
       NullCap \<Rightarrow>
         doE tcb_ptr \<leftarrow> returnOk $ obj_ref_of cap;
             ct_ptr \<leftarrow> liftE $ gets cur_thread;
             whenE (tcb_ptr = ct_ptr) $ throwError IllegalOperation;
             returnOk None
         odE
     | SchedContextCap _ _ \<Rightarrow>
         doE tcb_ptr \<leftarrow> returnOk $ obj_ref_of cap;
             sc_ptr \<leftarrow> returnOk $ obj_ref_of sc_cap;
             sc_ptr' \<leftarrow> liftE $ get_tcb_obj_ref tcb_sched_context tcb_ptr;
             whenE (sc_ptr' \<noteq> None) $ throwError IllegalOperation;
             sc \<leftarrow> liftE $ get_sched_context sc_ptr;
             whenE (sc_tcb sc \<noteq> None) $ throwError IllegalOperation;
             blocked \<leftarrow> liftE $ is_blocked tcb_ptr;
             released \<leftarrow> liftE $ get_sc_released sc_ptr;
             whenE (blocked \<and> \<not>released) $ throwError IllegalOperation;
             returnOk $ Some sc_ptr
         odE
     | _ \<Rightarrow> throwError (InvalidCapability 2))"

definition
  decode_tcb_configure ::
  "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_tcb_configure args cap slot extra_caps \<equiv> doE
     whenE (length args < 3) $ throwError TruncatedMessage;
     whenE (length extra_caps < 3) $ throwError TruncatedMessage;
     buffer \<leftarrow> returnOk $ args ! 2;
     buffer_cap \<leftarrow> returnOk $ extra_caps ! 2;
     set_params \<leftarrow> decode_set_ipc_buffer [buffer] cap slot [buffer_cap];
     set_space \<leftarrow> decode_cv_space (take 2 args) cap slot (take 2 extra_caps);
     returnOk $ ThreadControlCaps (obj_ref_of cap) slot
                              None None
                              (tc_new_croot set_space) (tc_new_vroot set_space)
                              (tc_new_buffer set_params)
   odE"

definition
  decode_set_timeout_ep ::
  "cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_timeout_ep cap slot extra_caps \<equiv> doE
     whenE (length extra_caps < 1) $ throwError TruncatedMessage;
     th_arg \<leftarrow> returnOk $ extra_caps ! 0;
     handler \<leftarrow> check_handler_ep 1 th_arg;
     returnOk $ ThreadControlCaps (obj_ref_of cap) slot
                              None (Some handler) None None None
   odE"

definition
  decode_bind_notification ::
  "cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_bind_notification cap extra_caps \<equiv> case cap of
    ThreadCap tcb \<Rightarrow> doE
     whenE (length extra_caps = 0) $ throwError TruncatedMessage;
     nTFN \<leftarrow> liftE $ get_tcb_obj_ref tcb_bound_notification tcb;
     case nTFN of
         Some _ \<Rightarrow> throwError IllegalOperation
       | None \<Rightarrow> returnOk ();
     (ntfnptr, rights) \<leftarrow> case fst (hd extra_caps) of
         NotificationCap ptr _ r \<Rightarrow> returnOk (ptr, r)
       | _ \<Rightarrow> throwError IllegalOperation;
     whenE (AllowRecv \<notin> rights) $ throwError IllegalOperation;
     ntfn \<leftarrow> liftE  $ get_notification ntfnptr;
     case (ntfn_obj ntfn, ntfn_bound_tcb ntfn) of
         (IdleNtfn, None) \<Rightarrow> returnOk ()
       | (ActiveNtfn _, None) \<Rightarrow> returnOk ()
       | _ \<Rightarrow> throwError IllegalOperation;
      returnOk $ NotificationControl tcb (Some ntfnptr)
   odE
 | _ \<Rightarrow> throwError IllegalOperation"


definition
  decode_unbind_notification :: "cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_unbind_notification cap \<equiv> case cap of
     ThreadCap tcb \<Rightarrow> doE
       nTFN \<leftarrow> liftE $ get_tcb_obj_ref tcb_bound_notification tcb;
       case nTFN of
           None \<Rightarrow> throwError IllegalOperation
         | Some _ \<Rightarrow> returnOk ();
       returnOk $ NotificationControl tcb None
    odE
 | _ \<Rightarrow> throwError IllegalOperation"

definition
  decode_set_tls_base :: "data list \<Rightarrow> cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_tls_base args cap \<equiv> doE
     whenE (length args = 0) $ throwError TruncatedMessage;
     returnOk (SetTLSBase (obj_ref_of cap) (ucast (args ! 0)))
   odE"

definition
  decode_set_sched_params :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_sched_params args cap slot extra_caps \<equiv> doE
     whenE (length args < 2) $ throwError TruncatedMessage;
     whenE (length extra_caps < 3) $ throwError TruncatedMessage;
     new_mcp \<leftarrow> returnOk $ ucast $ args ! 0;
     new_prio \<leftarrow> returnOk $ ucast $ args ! 1;
     auth_cap \<leftarrow> returnOk $ fst $ extra_caps ! 0;
     sc_cap \<leftarrow> returnOk $ fst $ extra_caps ! 1;
     fh_arg \<leftarrow> returnOk $ extra_caps ! 2;
     auth_tcb \<leftarrow> case auth_cap of
         ThreadCap tcb_ptr \<Rightarrow> returnOk tcb_ptr
       | _ \<Rightarrow> throwError (InvalidCapability 1);
     check_prio (args ! 0) auth_tcb;
     check_prio (args ! 1) auth_tcb;
     sc \<leftarrow> decode_update_sc cap slot sc_cap;
     fh \<leftarrow> check_handler_ep 3 fh_arg;
     returnOk $ ThreadControlSched (obj_ref_of cap) slot (Some fh)
                              (Some (new_mcp, auth_tcb)) (Some (new_prio, auth_tcb))
                              (Some sc)
     odE"

definition
  decode_tcb_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
  (tcb_invocation,'z::state_ext) se_monad"
where
 "decode_tcb_invocation label args cap slot excs \<equiv>
  case gen_invocation_type label of
      TCBReadRegisters \<Rightarrow> decode_read_registers args cap
    | TCBWriteRegisters \<Rightarrow> decode_write_registers args cap
    | TCBCopyRegisters \<Rightarrow> decode_copy_registers args cap $ map fst excs
    | TCBSuspend \<Rightarrow> returnOk $ Suspend $ obj_ref_of cap
    | TCBResume \<Rightarrow> returnOk $ Resume $ obj_ref_of cap
    | TCBConfigure \<Rightarrow> decode_tcb_configure args cap slot excs
    | TCBSetPriority \<Rightarrow> decode_set_priority args cap slot excs
    | TCBSetMCPriority \<Rightarrow> decode_set_mcpriority args cap slot excs
    | TCBSetSchedParams \<Rightarrow> decode_set_sched_params args cap slot excs
    | TCBSetTimeoutEndpoint \<Rightarrow> decode_set_timeout_ep cap slot excs
    | TCBSetIPCBuffer \<Rightarrow> decode_set_ipc_buffer args cap slot excs
    | TCBSetSpace \<Rightarrow> decode_set_space args cap slot excs
    | TCBBindNotification \<Rightarrow> decode_bind_notification cap excs
    | TCBUnbindNotification \<Rightarrow> decode_unbind_notification cap
    | TCBSetTLSBase \<Rightarrow> decode_set_tls_base args cap
    | _ \<Rightarrow> throwError IllegalOperation"

definition
  decode_domain_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
    ((obj_ref \<times> domain), 'z::state_ext) se_monad"
where
  "decode_domain_invocation label args excs \<equiv> doE
     whenE (gen_invocation_type label \<noteq> DomainSetSet) $ throwError IllegalOperation;
     domain \<leftarrow> (case args of
       x # xs \<Rightarrow> doE
         whenE (unat x \<ge> num_domains) $ throwError $ InvalidArgument 0;
         returnOk (ucast x)
       odE
       | _ \<Rightarrow> throwError TruncatedMessage);
     whenE (length excs = 0) $ throwError TruncatedMessage;
     case fst (hd excs) of ThreadCap ptr \<Rightarrow> returnOk $ (ptr, domain)
       | _ \<Rightarrow> throwError $ InvalidArgument 1
   odE"

section "Scheduling Contexts"

text \<open>The following definitions decode system calls related to scheduling contexts
and scheduling control.\<close>

definition
  decode_sched_context_bind :: "obj_ref \<Rightarrow> cap list \<Rightarrow> (sched_context_invocation, 'z::state_ext) se_monad"
where
  "decode_sched_context_bind sc_ptr excaps \<equiv> doE
      whenE (length excaps = 0) $ throwError TruncatedMessage;
      cap \<leftarrow> returnOk $ hd excaps;
      sc \<leftarrow> liftE $ get_sched_context sc_ptr;
      whenE (sc_tcb sc \<noteq> None \<or> sc_ntfn sc \<noteq> None) $ throwError IllegalOperation;
      case cap of
        ThreadCap tcb_ptr \<Rightarrow> doE
          sc_ptr_opt \<leftarrow> liftE $ get_tcb_obj_ref tcb_sched_context tcb_ptr;
          whenE (sc_ptr_opt \<noteq> None) $ throwError IllegalOperation;
          released \<leftarrow> liftE $ get_sc_released sc_ptr;
          st \<leftarrow> liftE $ get_thread_state tcb_ptr;
          whenE (ipc_queued_thread_state st \<and> \<not>released) $
            throwError IllegalOperation
        odE
      | NotificationCap ntfn_ptr _ _ \<Rightarrow> doE
          sc_ptr_opt \<leftarrow> liftE $ get_ntfn_obj_ref ntfn_sc ntfn_ptr;
          whenE (sc_ptr_opt \<noteq> None) $ throwError IllegalOperation
        odE
      | _ \<Rightarrow> throwError (InvalidCapability 1);
      returnOk $ InvokeSchedContextBind sc_ptr cap
    odE"

definition
  decode_sched_context_unbind_object ::
  "obj_ref \<Rightarrow> cap list \<Rightarrow> (sched_context_invocation, 'z::state_ext) se_monad"
where
  "decode_sched_context_unbind_object sc_ptr excaps \<equiv> doE
      whenE (length excaps = 0) $ throwError TruncatedMessage;
      cap \<leftarrow> returnOk $ hd excaps;
      case cap of
        ThreadCap tcb_ptr \<Rightarrow> doE
          sc_tcb_opt \<leftarrow> liftE $ get_sc_obj_ref sc_tcb sc_ptr;
          whenE (sc_tcb_opt \<noteq> Some tcb_ptr) $ throwError IllegalOperation;
          ct_ptr \<leftarrow> liftE $ gets cur_thread;
          whenE (tcb_ptr = ct_ptr) $ throwError IllegalOperation
        odE
      | NotificationCap ntfn_ptr _ _ \<Rightarrow> doE
          sc_ntfn_opt \<leftarrow> liftE $ get_sc_obj_ref sc_ntfn sc_ptr;
          whenE (sc_ntfn_opt \<noteq> Some ntfn_ptr) $ throwError IllegalOperation
        odE
      | _ \<Rightarrow> throwError (InvalidCapability 1);
      returnOk $ InvokeSchedContextUnbindObject sc_ptr cap
    odE"

definition
  decode_sched_context_yield_to ::
  "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (sched_context_invocation, 'z::state_ext) se_monad"
where
  "decode_sched_context_yield_to sc_ptr buffer \<equiv> doE
      sc_tcb_opt \<leftarrow> liftE $ get_sc_obj_ref sc_tcb sc_ptr;
      whenE (sc_tcb_opt = None) $ throwError IllegalOperation;
      ct_ptr \<leftarrow> liftE $ gets cur_thread;
      whenE (sc_tcb_opt = Some ct_ptr) $ throwError IllegalOperation;
      prios \<leftarrow> liftE $ thread_get tcb_priority (the sc_tcb_opt);
      ct_mcp \<leftarrow> liftE $ thread_get tcb_mcpriority ct_ptr;
      whenE (prios > ct_mcp) $ throwError IllegalOperation;
      yt_ptr \<leftarrow> liftE $ thread_get tcb_yield_to ct_ptr;
      whenE (yt_ptr \<noteq> None) $ throwError IllegalOperation;
      returnOk $ InvokeSchedContextYieldTo sc_ptr buffer
   odE"

definition
  decode_sched_context_invocation ::
  "data \<Rightarrow> obj_ref \<Rightarrow> cap list \<Rightarrow> obj_ref option \<Rightarrow> (sched_context_invocation, 'z::state_ext) se_monad"
where
  "decode_sched_context_invocation label sc_ptr excaps buffer \<equiv>
  case gen_invocation_type label of
    SchedContextConsumed \<Rightarrow> returnOk $ InvokeSchedContextConsumed sc_ptr buffer
  | SchedContextBind \<Rightarrow> decode_sched_context_bind sc_ptr excaps
  | SchedContextUnbindObject \<Rightarrow> decode_sched_context_unbind_object sc_ptr excaps
  | SchedContextUnbind \<Rightarrow> doE
      sc \<leftarrow> liftE $ get_sched_context sc_ptr;
      ct_ptr \<leftarrow> liftE $ gets cur_thread;
      whenE (sc_tcb sc = Some ct_ptr) $ throwError IllegalOperation;
      returnOk $ InvokeSchedContextUnbind sc_ptr odE
  | SchedContextYieldTo \<Rightarrow> decode_sched_context_yield_to sc_ptr buffer
  | _ \<Rightarrow> throwError $ IllegalOperation"

definition
  TIME_ARG_SIZE :: nat
where
  "TIME_ARG_SIZE \<equiv> 2" (* sizeof(ticks_t) / sizeof(word_t) *)

definition
  decode_sched_control_invocation_flags ::
  "data \<Rightarrow> data list \<Rightarrow> cap list \<Rightarrow> (sched_control_invocation,'z::state_ext) se_monad"
where
  "decode_sched_control_invocation_flags label args excaps \<equiv> doE
    unlessE (gen_invocation_type label = SchedControlConfigureFlags) $ throwError IllegalOperation;
    whenE (length excaps = 0) $ throwError TruncatedMessage;
    whenE (length args < TIME_ARG_SIZE*2 + 3) $ throwError TruncatedMessage;
    budget_\<mu>s \<leftarrow> returnOk $ parse_time_arg 0 args;
    period_\<mu>s \<leftarrow> returnOk $ parse_time_arg TIME_ARG_SIZE args;
    extra_refills \<leftarrow> returnOk $ args ! (2 * TIME_ARG_SIZE);
    badge \<leftarrow> returnOk $ args ! (2 * TIME_ARG_SIZE + 1);
    flags \<leftarrow> returnOk $ args ! (2 * TIME_ARG_SIZE + 2);
    target_cap \<leftarrow> returnOk $ hd excaps;
    whenE (\<not>is_sched_context_cap target_cap) $ throwError (InvalidCapability 1);
    sc_ptr \<leftarrow> returnOk $ obj_ref_of target_cap;
    whenE (MAX_PERIOD_US < budget_\<mu>s \<or> budget_\<mu>s < MIN_BUDGET_US) $
      throwError (RangeError (ucast MIN_BUDGET_US) (ucast MAX_PERIOD_US));
    whenE (MAX_PERIOD_US < period_\<mu>s \<or> period_\<mu>s < MIN_BUDGET_US) $
      throwError (RangeError (ucast MIN_BUDGET_US) (ucast MAX_PERIOD_US));
    whenE (period_\<mu>s < budget_\<mu>s) $
      throwError (RangeError (ucast MIN_BUDGET_US) (ucast period_\<mu>s));
    whenE (unat extra_refills + MIN_REFILLS > max_refills_cap target_cap) $
      throwError (RangeError 0 (of_nat (max_refills_cap target_cap - MIN_REFILLS)));
    assertE (MIN_REFILLS \<le> unat extra_refills + MIN_REFILLS);
    returnOk $ InvokeSchedControlConfigureFlags sc_ptr
       (us_to_ticks budget_\<mu>s) (us_to_ticks period_\<mu>s) (unat extra_refills + MIN_REFILLS)
        badge flags
  odE"


section "IRQ"

text \<open>The following two definitions decode system calls for the
interrupt controller and interrupt handlers\<close>

definition
  decode_irq_control_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap list
                                     \<Rightarrow> (irq_control_invocation,'z::state_ext) se_monad" where
 "decode_irq_control_invocation label args src_slot cps \<equiv>
  (if gen_invocation_type label = IRQIssueIRQHandler
    then if length args \<ge> 3 \<and> length cps \<ge> 1
      then let irq_word = args ! 0;
               index = args ! 1;
               depth = args ! 2;
               cnode = cps ! 0;
               irq = ucast irq_word
      in doE
        arch_check_irq irq_word;
        irq_active \<leftarrow> liftE $ is_irq_active irq;
        whenE irq_active $ throwError RevokeFirst;

        dest_slot \<leftarrow> lookup_target_slot
               cnode (data_to_cptr index) (unat depth);
        ensure_empty dest_slot;

        returnOk $ IRQControl irq dest_slot src_slot
      odE
    else throwError TruncatedMessage
  else liftME ArchIRQControl $ arch_decode_irq_control_invocation label args src_slot cps)"

definition
  decode_irq_handler_invocation :: "data \<Rightarrow> irq \<Rightarrow> (cap \<times> cslot_ptr) list
                                     \<Rightarrow> (irq_handler_invocation,'z::state_ext) se_monad" where
 "decode_irq_handler_invocation label irq cps \<equiv>
  if gen_invocation_type label = IRQAckIRQ
    then returnOk $ ACKIrq irq
  else if gen_invocation_type label = IRQSetIRQHandler
    then if cps \<noteq> []
      then let (cap, slot) = hd cps in
      if is_ntfn_cap cap \<and> AllowSend \<in> cap_rights cap
      then returnOk $ SetIRQHandler irq cap slot
      else throwError $ InvalidCapability 0
    else throwError TruncatedMessage
  else if gen_invocation_type label = IRQClearIRQHandler
    then returnOk $ ClearIRQHandler irq
  else throwError IllegalOperation"

section "Untyped"

text \<open>The definitions in this section deal with decoding invocations
of untyped memory capabilities.
\<close>

definition
  data_to_obj_type :: "data \<Rightarrow> (apiobject_type,'z::state_ext) se_monad" where
  "data_to_obj_type type \<equiv> doE
    n \<leftarrow> returnOk $ data_to_nat type;
    if n = 0 then
      returnOk $ Untyped
    else if n = 1 then
      returnOk $ TCBObject
    else if n = 2 then
      returnOk $ EndpointObject
    else if n = 3 then
      returnOk $ NotificationObject
    else if n = 4 then
      returnOk $ CapTableObject
    else if n = 5 then
      returnOk $ SchedContextObject
    else if n = 6 then
      returnOk $ ReplyObject
    else (case arch_data_to_obj_type (n - 7)
       of Some tp \<Rightarrow> returnOk (ArchObject tp)
        | None \<Rightarrow> throwError (InvalidArgument 0))
  odE"

definition
  decode_untyped_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (untyped_invocation,'z::state_ext) se_monad"
where (* for SchedContext objects, user_obj_size arg represents the whole size *)
"decode_untyped_invocation label args slot cap excaps \<equiv> doE
  unlessE (gen_invocation_type label = UntypedRetype) $ throwError IllegalOperation;
  whenE (length args < 6) $ throwError TruncatedMessage;
  whenE (length excaps = 0) $ throwError TruncatedMessage;
  root_cap \<leftarrow> returnOk $ excaps ! 0;
  new_type \<leftarrow> data_to_obj_type (args!0);

  user_obj_size \<leftarrow> returnOk $ data_to_nat (args!1);
  object_size \<leftarrow> returnOk (obj_bits_api new_type user_obj_size);
  unlessE (user_obj_size < word_bits \<and> object_size \<le> untyped_max_bits)
    $ throwError (RangeError 0 (of_nat untyped_max_bits));
  whenE (new_type = CapTableObject \<and> user_obj_size = 0)
    $ throwError (InvalidArgument 1);
  whenE (new_type = Untyped \<and> user_obj_size < untyped_min_bits)
    $ throwError (InvalidArgument 1);
  whenE (new_type = SchedContextObject \<and> user_obj_size < 8) \<comment> \<open>@{text seL4_MfsinSchedContextBits}\<close>
    $ throwError (InvalidArgument 1);
  node_index \<leftarrow> returnOk $ data_to_cptr (args!2);
  node_depth \<leftarrow> returnOk $ data_to_nat (args!3);

  node_cap \<leftarrow> if node_depth = 0
        then returnOk root_cap
        else doE
            node_slot \<leftarrow> lookup_target_slot
                root_cap node_index node_depth;
            liftE $ get_cap node_slot
        odE;

  if is_cnode_cap node_cap
        then  returnOk ()
        else  throwError $ FailedLookup False $ MissingCapability node_depth;

  node_offset \<leftarrow> returnOk $ data_to_nat (args ! 4);
  node_window \<leftarrow> returnOk $ data_to_nat (args ! 5);
  radix_bits \<leftarrow> returnOk $ bits_of node_cap;
  node_size \<leftarrow> returnOk (2 ^ radix_bits);

  whenE (node_offset < 0 \<or> node_offset > node_size - 1) $
    throwError $ RangeError 0 (of_nat (node_size - 1));

  whenE (node_window < 1 \<or> node_window > 256) $ throwError $ RangeError 1 256;

  whenE (node_window < 1 \<or> node_window > node_size - node_offset) $
    throwError $ RangeError 1 (of_nat (node_size - node_offset));

  oref \<leftarrow> returnOk $ obj_ref_of node_cap;
  offsets \<leftarrow> returnOk $ map (nat_to_cref radix_bits)
                           [node_offset ..< node_offset + node_window];
  slots \<leftarrow> returnOk $ map (\<lambda>cref. (oref, cref)) offsets;

  mapME_x ensure_empty slots;

  reset \<leftarrow> liftE $ const_on_failure False $ (doE
    ensure_no_children slot;
    returnOk True
  odE);

  free_index \<leftarrow> returnOk (if reset then 0 else free_index_of cap);
  free_ref \<leftarrow> returnOk (get_free_ref (obj_ref_of cap) free_index);
  aligned_free_ref \<leftarrow> returnOk (alignUp free_ref object_size);
  untyped_free_bytes \<leftarrow> returnOk (obj_size cap - of_nat (free_index));

  max_count \<leftarrow> returnOk ( untyped_free_bytes >> object_size);
  whenE (unat max_count < node_window) $
        throwError $ NotEnoughMemory $ untyped_free_bytes;

  not_frame \<leftarrow> returnOk (\<not> is_frame_type new_type);
  (ptr, is_device) \<leftarrow> case cap of
                        UntypedCap dev p n f \<Rightarrow> returnOk (p,dev)
                      | _ \<Rightarrow> fail;
  whenE (is_device \<and> not_frame \<and> new_type \<noteq> Untyped) $
           throwError $ InvalidArgument 1;
  returnOk $ Retype slot reset ptr aligned_free_ref new_type user_obj_size slots is_device
odE"

section "Toplevel invocation decode."

text \<open>This definition is the toplevel decoding definition; it dispatches
to the above definitions, after checking, in some cases, whether the
invocation is allowed.
\<close>

definition
  decode_invocation ::
  "bool \<Rightarrow> data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow>
   (cap \<times> cslot_ptr) list \<Rightarrow> obj_ref option \<Rightarrow> (invocation, 'z::state_ext) se_monad"
where
  "decode_invocation first_phase label args cap_index slot cap excaps buffer \<equiv>
  case cap of
    EndpointCap ptr badge rights \<Rightarrow>
      if AllowSend \<in> rights then
        returnOk $ InvokeEndpoint ptr badge (AllowGrant \<in> rights) (AllowGrantReply \<in> rights)
      else throwError $ InvalidCapability 0
  | NotificationCap ptr badge rights \<Rightarrow>
      if AllowSend \<in> rights then
        returnOk $ InvokeNotification ptr badge
      else throwError $ InvalidCapability 0
  | ReplyCap reply rights \<Rightarrow>
      returnOk $ InvokeReply reply (AllowGrant \<in> rights)
  | IRQControlCap \<Rightarrow>
      liftME InvokeIRQControl
        $ decode_irq_control_invocation label args slot (map fst excaps)
  | IRQHandlerCap irq \<Rightarrow>
      liftME InvokeIRQHandler
        $ decode_irq_handler_invocation label irq excaps
  | ThreadCap ptr \<Rightarrow>
      if first_phase
      then throwError $ InvalidCapability 0
      else liftME InvokeTCB $ decode_tcb_invocation label args cap slot excaps
  | DomainCap \<Rightarrow>
      if first_phase
      then throwError $ InvalidCapability 0
      else liftME (case_prod InvokeDomain) $ decode_domain_invocation label args excaps
  | SchedContextCap sc sz \<Rightarrow>
      if first_phase
      then throwError $ InvalidCapability 0
      else liftME InvokeSchedContext $ decode_sched_context_invocation label sc (map fst excaps) buffer
  | SchedControlCap \<Rightarrow>
      if first_phase
      then throwError $ InvalidCapability 0
      else liftME InvokeSchedControl $ decode_sched_control_invocation_flags label args (map fst excaps)
  | CNodeCap ptr bits _ \<Rightarrow>
      if first_phase
      then throwError $ InvalidCapability 0
      else liftME InvokeCNode $ decode_cnode_invocation label args cap (map fst excaps)
  | UntypedCap dev ptr sz fi \<Rightarrow>
      liftME InvokeUntyped $ decode_untyped_invocation label args slot cap (map fst excaps)
  | ArchObjectCap arch_cap \<Rightarrow>
      liftME InvokeArchObject $
        arch_decode_invocation label args cap_index slot arch_cap excaps
  | _ \<Rightarrow>
      throwError $ InvalidCapability 0"


end