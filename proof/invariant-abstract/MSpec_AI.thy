(*
 * Copyright 2024, The University of New South Wales
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory MSpec_AI
imports
  Syscall_AI
begin

(* From Structures_A.thy *)
term "s :: abstract_state"

consts
  MICROKIT_INPUT_CAP :: cnode_index
  MICROKIT_REPLY_CAP :: cnode_index

axiomatization where microkit_input_reply_caps_distinct:
  "MICROKIT_INPUT_CAP \<noteq> MICROKIT_REPLY_CAP"

(* Based on KernelState in Mathieu's gordian-relation-proof *)

(* The 1st member is supposed to end up being the return value of seL4_(Reply)Recv. *)
(* The 2nd member was specified as a cap, but actually we don't get a new cap from the sender,
   we simply register the new sender with the reply cap given by the caller. *)
(* The 3rd member of the KernelOracle tuple was of type SeL4_Ntfn. My guess is this was meant
   to mean a type for the notification word. But that's only in the notification case; in the
   endpoint case, this should be the badge of the endpoint capability invoked by the sender. *)
(* I'm also making the minfo and new_reply_tcb optional because, as far as I can tell,
   these aren't set in the notification case. *)
record mspec_recv_oracle =
  (* In the notification case, seL4_(Reply)Recv will just return whatever's already in the msg info
     register. But we can't query what's in there without invoking the (unspecified) machine
     operation to getRegister, so there's not much point asserting anything about it. *)
  minfo :: message_info
  new_reply_tcb :: "tcb option"
  badge_val :: badge

(* FIXME: Come back to this.
datatype mspec_writable = Writable | WritableExclusive
*)

record mspec_state =
  cur_thread_cnode :: cnode_contents
  cur_thread_bound_notification :: "obj_ref option"
  (* Dropped: (ks_reply_obj_has_cap (Array SeL4_Cap Bool)).
     I think this can instead be phrased as a predicate on the CNode contents.
     See valid_reply_obj_for_tcb below for experimentation. *)
  (* Dropped: (ks_recv_oracle (Maybe KernelOracle)).
     Again trying to phrase it as a predicate on the CNode contents.
     See valid_ep_obj_with_message below. *)
  (* Dropped: (ks_local_mem Mem).
     It doesn't actually seem to be used by the coupling invariant, and it was only used to assert
     something about the returned badge value, which we can do directly on the badge register. *)
  (* FIXME: Come back to this.
  (* TODO: (ks_local_mem_writable (Array Word64 Bool))
     That this address is mapped writable for the current PD. *)
  (* TODO: (ks_local_mem_safe (Array Word64 Bool))
     That the current PD is the *only* one with write access to this address. *)
  cur_thread_mem_writable :: "vspace_ref \<rightharpoonup> mspec_writable"
  *)

(* The sorts of things Mathieu's smt file asserts about:
  - ks_local_mem
    - that seL4_(Reply)Recv modifies the ks_local_mem to store the new badge_val at the badge_ptr
      - NB: actually, from the kernel perspective it just sets the badge register, so presumably
        the libsel4 wrapper code is the one dereferencing the user-provided badge pointer - we
        can't check inside the kernel if that pointer is mapped because we aren't given it.
      - NB: furthermore, it looks like the libsel4 wrapper code just trusts that the user/microkit
        provided badge pointer (2nd argument "seL4_Word *sender") is a valid, mapped address;
        it only checks that it isn't NULL.
  - ks_local_mem_writable
    - that the badge_ptr argument to seL4_(Reply)Recv is writable
    - that for all addresses, (is_writable_mem addr mi) if the addr is writable (see relation_mmrs_mem)
  - ks_local_mem_safe
    - that for all addresses, if an address is safe, then nobody else has write access
      (see relation_mmrs_mem)
*)

(* FIXME: Come back to this.
definition
  local_mem_writable :: "mspec_state \<Rightarrow> vspace_ref \<Rightarrow> bool"
where
  "local_mem_writable m r \<equiv> \<exists>w. cur_thread_mapped_mem_writable_exclusive m r = Some w"

definition
  local_mem_safe :: "mspec_state \<Rightarrow> vspace_ref \<Rightarrow> bool"
where
  "local_mem_safe m r \<equiv> cur_thread_mapped_mem_writable_exclusive m r = Some WritableExclusive"

thm ARM.addrFromKPPtr_def
  ARM.addrFromPPtr_def
  ARM.ptrFromPAddr_def
  ARM.kernelELFBaseOffset_def
  ARM.pptrBaseOffset_def
*)

term "TCB t"
term "t :: tcb"
definition
  mspec_transform :: "'a::state_ext state \<Rightarrow> mspec_state"
where
  "mspec_transform s \<equiv> \<lparr>
     cur_thread_cnode = (case kheap s (cur_thread s) of
       Some (TCB t) \<Rightarrow> tcb_cnode_map t |
       _ \<Rightarrow> \<lambda>_. None),
     cur_thread_bound_notification = (case kheap s (cur_thread s) of
       Some (TCB t) \<Rightarrow> tcb_bound_notification t |
       _ \<Rightarrow> None)
     \<comment> \<open>FIXME: Come back to this.
     cur_thread_mem_writable = \<lambda>_. None \<comment> \<open>TODO\<close>
     \<close>
   \<rparr>"

term "is_reply_cap"

definition
  valid_reply_obj :: "mspec_state \<Rightarrow> 'a::state_ext state \<Rightarrow> cnode_index \<Rightarrow> bool"
where
  (* FIXME: Ideally we don't want to take the abstract_state s as an argument here,
     if we want to phrase this purely as a predicate on mspec_state m. But that means
     getting what we need of `kheap s` into the mspec_state - maybe as local_mem? *)
  "valid_reply_obj m s i \<equiv> case cur_thread_cnode m i of
     Some (ReplyCap rp _) \<Rightarrow> \<exists> r. kheap s rp = Some (Reply r) |
     _ \<Rightarrow> False"

definition
  valid_reply_obj_for_tcb :: "mspec_state \<Rightarrow> 'a::state_ext state \<Rightarrow> cnode_index \<Rightarrow> obj_ref \<Rightarrow> bool"
where
  "valid_reply_obj_for_tcb m s i tp \<equiv> case cur_thread_cnode m i of
     Some (ReplyCap rp _) \<Rightarrow> (case kheap s rp of
       Some (Reply r) \<Rightarrow> reply_tcb r = Some tp |
       _ \<Rightarrow> False) |
     _ \<Rightarrow> False"

(* Experimentation to find more usable lemmas about return values of monads *)
definition
  getRegister_as_user_ret :: "'a state \<Rightarrow> obj_ref \<Rightarrow> register \<Rightarrow> machine_word option"
where
  "getRegister_as_user_ret s thread r \<equiv> case kheap s thread of
    Some (TCB t) \<Rightarrow> (case arch_tcb_context_get (tcb_arch t) of
      ARM.UserContext u \<Rightarrow> Some (u r)) |
    _ \<Rightarrow> None"

lemma getRegister_as_user_ret_valid:
  "\<lbrace>\<lambda>s'. s = s'\<rbrace> as_user (cur_thread s) $ getRegister r
   \<lbrace>\<lambda> r' s''. s = s'' \<and> getRegister_as_user_ret s (cur_thread s) r = Some r'\<rbrace>"
  unfolding getRegister_as_user_ret_def
  apply wp
   unfolding as_user_def
   apply wpsimp
  apply wpsimp
  unfolding ARM.getRegister_def get_tcb_def gets_def get_def
  apply wpsimp
  apply(clarsimp split:option.splits kernel_object.splits ARM.user_context.splits
    simp:bind_def return_def)
  using ARM.user_context.sel by force

definition
  get_message_info_ret :: "'a state \<Rightarrow> obj_ref \<Rightarrow> message_info option"
where
  "get_message_info_ret s thread \<equiv> case kheap s thread of
    Some (TCB t) \<Rightarrow> (case arch_tcb_context_get (tcb_arch t) of
      ARM.UserContext u \<Rightarrow> Some (data_to_message_info (u msg_info_register))) |
    _ \<Rightarrow> None"

lemma get_message_info_ret_valid:
  "\<lbrace>\<lambda>s'. s = s'\<rbrace> get_message_info (cur_thread s)
   \<lbrace>\<lambda> r s''. s = s'' \<and> get_message_info_ret s (cur_thread s) = Some r\<rbrace>"
  unfolding get_message_info_def get_message_info_ret_def
  apply wp
   unfolding as_user_def
   apply wpsimp
  apply wpsimp
  unfolding ARM.getRegister_def get_tcb_def gets_def get_def
  apply wpsimp
  apply(clarsimp split:option.splits kernel_object.splits ARM.user_context.splits
    simp:bind_def return_def)
  using ARM.user_context.sel by force

(* copy_mrs will only return the number of message registers successfully transferred *)
definition copy_mrs_ret ::
  "obj_ref option \<Rightarrow> obj_ref option \<Rightarrow> length_type \<Rightarrow> length_type"
where
  "copy_mrs_ret sbuf rbuf n \<equiv>
   let hardware_mrs_len = length (take (unat n) msg_registers);
       buf_mrs_len = case (sbuf, rbuf) of
         (Some sb_ptr, Some rb_ptr) \<Rightarrow> length [length msg_registers + 1..<Suc (unat n)] |
         _ \<Rightarrow> 0
    in min n (nat_to_len (hardware_mrs_len + buf_mrs_len))"

lemma copy_mrs_ret_valid:
  "\<lbrace>\<top>\<rbrace> copy_mrs sender sbuf receiver rbuf n \<lbrace>\<lambda> r _. r = copy_mrs_ret sbuf rbuf n\<rbrace>"
  unfolding copy_mrs_def copy_mrs_ret_def
  by wpsimp

(* Turns out Microkit won't transfers caps via channels, their endpoints shouldn't be given Grant.
  So we specify do_normal_transfer's behaviour under these assumptions. *)
definition transfer_caps_none_ret :: "message_info \<Rightarrow> obj_ref option \<Rightarrow> message_info"
where
  "transfer_caps_none_ret info recv_buffer \<equiv>
   let mi = MI (mi_length info) 0 0 (mi_label info)
    in case recv_buffer of None \<Rightarrow> mi |
         _ \<Rightarrow> (MI (mi_length mi) (word_of_nat 0) (mi_caps_unwrapped mi) (mi_label mi))"

lemma transfer_caps_none_valid:
  "\<lbrace>\<top>\<rbrace> transfer_caps info [] endpoint receiver recv_buffer
   \<lbrace>\<lambda> r _. r = transfer_caps_none_ret info recv_buffer\<rbrace>"
  unfolding transfer_caps_def transfer_caps_none_ret_def
  by wpsimp

definition
  get_cap_ret :: "'a state \<Rightarrow> cslot_ptr \<Rightarrow> cap option"
where
  "get_cap_ret \<equiv> \<lambda>s (oref, cref).
   let obj = kheap s oref;
       caps = case obj of
             Some (CNode sz cnode) \<Rightarrow> cnode
           | Some (TCB tcb) \<Rightarrow> tcb_cnode_map tcb
           | _ \<Rightarrow> \<lambda>_. None
    in caps cref"

lemma get_cap_ret_valid:
  "\<lbrace>\<lambda>s'. s = s' \<and> (\<forall> cap. get_cap_ret s' p = Some cap \<longrightarrow> Q cap s')\<rbrace> get_cap p
   \<lbrace>Q\<rbrace>"
  unfolding get_cap_def get_cap_ret_def get_object_def
  by wpsimp

(* FIXME: In the long run we'll need to interface off the arch-specific parts properly.
  But some of the return values depend on arch-specific implementations, so for now
  while experimenting I'll just open up the Arch context and do it in here. *)
context Arch begin global_naming ARM_A

definition
  lookup_ipc_buffer_ret :: "('a::state_ext) state \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow> 32 word option"
where
  "lookup_ipc_buffer_ret s is_receiver thread \<equiv>
   case get_tcb thread s of Some t \<Rightarrow>
     (let buffer_ptr = tcb_ipc_buffer t;
          buffer_frame_slot = (thread, tcb_cnode_index 2)
       in case get_cap_ret s buffer_frame_slot of
         Some (ArchObjectCap (PageCap _ p R vms _)) \<Rightarrow>
              if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
              then Some (p + (buffer_ptr && mask (pageBitsForSize vms)))
              else None
            | _ \<Rightarrow> None) |
   _ \<Rightarrow> None"

lemma lookup_ipc_buffer_ret_valid:
  "\<lbrace>\<lambda>s'. s = s' \<and> tcb_at thread s\<rbrace>
    lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda> r s''. s = s'' \<and> r = lookup_ipc_buffer_ret s'' is_receiver thread\<rbrace>"
  unfolding lookup_ipc_buffer_def lookup_ipc_buffer_ret_def
  apply wpsimp
     apply(wpsimp wp:get_cap_ret_valid)
    apply wpsimp
   apply(wpsimp wp:thread_get_wp)
  apply(wpsimp simp:tcb_at_def get_tcb_def obj_at_def)
  apply(clarsimp simp:get_cap_ret_def is_tcb_def
    split:option.splits kernel_object.splits cap.splits arch_cap.splits)
  by fast

(* Refer to these functions - we need to be making the same validity checks *)
term handle_recv
term receive_ipc (* This handles the EndpointCap case, but will check the bound notification *)
term do_ipc_transfer
term do_normal_transfer
definition
  valid_ep_obj_with_message :: "mspec_state \<Rightarrow> 'a::state_ext state \<Rightarrow> cnode_index \<Rightarrow> mspec_recv_oracle \<Rightarrow> bool"
where
  (* FIXME: Again, ideally we don't want to take the abstract_state s as an argument here. *)
  "valid_ep_obj_with_message m s i oracle \<equiv> case cur_thread_cnode m i of
     \<comment> \<open>Microkit only checks notifications via EndpointCap, not via any standalone NotificationCap\<close>
     Some (EndpointCap ref _ rights) \<Rightarrow> AllowRead \<in> rights \<and>
       (case kheap s ref of Some (Endpoint ep) \<Rightarrow>
         (case cur_thread_bound_notification m of Some n \<Rightarrow>
           (case kheap s n of Some (Notification ntfn) \<Rightarrow>
             \<comment> \<open>receive_ipc prefers to handle any waiting bound notification via complete_signal\<close>
             (case ntfn_obj ntfn of ActiveNtfn badge \<Rightarrow>
               \<comment> \<open>we assert that the notification case leaves the value in the user's message_info
                  register untouched from when it called seL4_Recv, so we just retrieve that here\<close>
               get_message_info_ret s (cur_thread s) = Some (minfo oracle) \<and>
               new_reply_tcb oracle = None \<and>
               badge_val oracle = badge |
             \<comment> \<open>if there's no bound notification to receive, receive_ipc then checks the endpoint\<close>
             _ \<Rightarrow> (case ep of SendEP q \<Rightarrow> q \<noteq> [] \<and>
               (case kheap s (hd q) of Some (TCB sender) \<Rightarrow>
                 (case tcb_state sender of BlockedOnSend _ data \<Rightarrow>
                   \<comment> \<open>That the sender made a call and can grant the reply is treated as
                      conditional in ASpec, but we're going to require them here as Microkit
                      will assume the sender to be following the correct ppcall convention.\<close>
                   sender_is_call data \<and>
                   sender_can_grant_reply data \<and>
                   \<comment> \<open>Also assert Microkit doesn't support channel endpoints with grant rights.\<close>
                   \<not> sender_can_grant data \<and>
                   \<comment> \<open>Assert minfo oracle corresponds to the message_info Recv would return.\<close>
                   (\<exists> mi. get_message_info_ret s (cur_thread s) = Some mi \<and>
                      \<comment> \<open>These are sbuf, rbuf args given by do_ipc_transfer to do_normal_transfer\<close>
                      (let rbuf = lookup_ipc_buffer_ret s True (cur_thread s);
                           sbuf = lookup_ipc_buffer_ret s False (hd q);
                           \<comment> \<open>These are mrs_transferred, mi' calculated by do_normal_transfer\<close>
                           mrs_transferred = copy_mrs_ret sbuf rbuf (mi_length mi);
                           mi' = transfer_caps_none_ret mi rbuf
                        \<comment> \<open>This is the final minfo written to the register by do_normal_transfer\<close>
                        in minfo oracle = MI mrs_transferred (mi_extra_caps mi')
                                   (mi_caps_unwrapped mi') (mi_label mi))) \<and>
                   badge_val oracle = sender_badge data \<and>
                   new_reply_tcb oracle = Some sender |
                 _ \<Rightarrow> False) |
               _ \<Rightarrow> False) |
             _ \<Rightarrow> False)) |
           _ \<Rightarrow> False) |
         _ \<Rightarrow> False) |
       _ \<Rightarrow> False) |
     _ \<Rightarrow> False"

thm getRegister_as_user_ret_valid
  get_message_info_ret_valid
  copy_mrs_ret_valid
  transfer_caps_none_valid
  get_cap_ret_valid
  lookup_ipc_buffer_ret_valid

find_theorems name:handle_fault valid

lemma handle_SysRecv_syscall_valid:
  "\<lbrace>\<lambda>s. valid_reply_obj (mspec_transform s) s MICROKIT_REPLY_CAP \<and>
      valid_ep_obj_with_message (mspec_transform s) s MICROKIT_INPUT_CAP ro\<rbrace>
    handle_recv True True
   \<lbrace>\<lambda> _ s'. getRegister_as_user_ret s' (cur_thread s') badge_register = Some (badge_val ro) \<and>
      get_message_info_ret s' (cur_thread s') = Some (minfo ro)\<rbrace>"
  unfolding handle_recv_def
  apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
    copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid)
      defer
     apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
       copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid)
      apply(wpsimp simp:Let_def)

       (* 19 subgoals *)
       unfolding receive_ipc_def
       apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
        copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid)

        (* 25 subgoals *)
        unfolding complete_signal_def refill_unblock_check_def refill_head_overlapping_loop_def
          merge_overlapping_refills_def update_refill_hd_def update_sched_context_def
          set_object_def get_object_def refill_pop_head_def
        apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
          copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid)

         (* 39 subgoals *)
         apply(rule conjI)
          apply(force simp:getRegister_as_user_ret_def)
         apply(force simp:get_message_info_ret_def)
        apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
          copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid
          simp:getRegister_as_user_ret_def get_message_info_ret_def)+

       unfolding is_round_robin_def get_tcb_obj_ref_def thread_get_def maybe_donate_sc_def
         sched_context_resume_def postpone_def tcb_release_enqueue_def
       (* 33 subgoals *)
       apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
         copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid
         simp:getRegister_as_user_ret_def get_message_info_ret_def)+

        (* 48 subgoals. Noticing I'm seeing a lot of scheduling stuff here. It's occurred to me,
           since we're on the MCS kernel, that I really can't assert that the kernel will return
           to the original caller unless we somehow know that it won't run out of time. But I
           definitely have not ensured that with the precondition and I'm not sure how, so should
           I figure out how to phrase this or am I better off trying to prove some of these kinds
           of properties on the non-MCS kernel ASpec first? *)
         apply(clarsimp simp:valid_def mapM_wp[simplified valid_def])
         apply auto[1]
        apply(clarsimp simp:valid_def mapM_wp[simplified valid_def])
        apply auto[1]
       apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
         copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid
         simp:getRegister_as_user_ret_def get_message_info_ret_def)+

      (* 31 subgoals *)
      unfolding sched_context_donate_def set_tcb_obj_ref_def set_object_def update_sched_context_def
      apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
        copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid
        simp:getRegister_as_user_ret_def get_message_info_ret_def)+

      unfolding get_object_def test_reschedule_def reschedule_required_def set_scheduler_action_def
        tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def thread_get_def
      apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
        copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid
        simp:getRegister_as_user_ret_def get_message_info_ret_def)+

      unfolding is_schedulable_def
      (* FIXME: Now we seem to be stuck following the kitchen sink approach. Maybe not surprising
         for it to be once seL4 asks if the (presumably current?) thread is still schedulable?
      apply(wpsimp wp:crunch_wps getRegister_as_user_ret_valid get_message_info_ret_valid
        copy_mrs_ret_valid transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid
        simp:getRegister_as_user_ret_def get_message_info_ret_def)+
      *)
  oops

end (* Arch ARM_A *)

end