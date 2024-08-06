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
  minfo :: "message_info option"
  new_reply_tcb :: "tcb option"
  badge_val :: badge

record mspec_state =
  cur_thread_cnode :: cnode_contents
  cur_thread_bound_notification :: "obj_ref option"
  (* Dropped: (ks_reply_obj_has_cap (Array SeL4_Cap Bool)).
     I think this can instead be phrased as a predicate on the CNode contents.
     See valid_reply_obj_for_tcb below for experimentation. *)
  (* Dropped: (ks_recv_oracle (Maybe KernelOracle)).
     Again trying to phrase it as a predicate on the CNode contents.
     See valid_ep_obj_with_message below. *)
  (* TODO: (ks_local_mem Mem)
     A comment in Mathieu's smt file says "shouldn't be called local mem, this can represent memory
     in shared memory regions" - but regardless, should these be virtual or physical addresses? *)
  (* TODO: (ks_local_mem_writable (Array Word64 Bool))
     That this address is mapped writable for the current PD. *)
  (* TODO: (ks_local_mem_safe (Array Word64 Bool))
     That the current PD is the *only* one with write access to this address. *)

(* The sorts of things Mathieu's smt file asserts about:
  - ks_local_mem
    - that seL4_(Reply)Recv modifies the ks_local_mem to store the new badge_val at the badge_ptr
  - ks_local_mem_writable
    - that the badge_ptr argument to seL4_(Reply)Recv is writable
    - that for all addresses, (is_writable_mem addr mi) if the addr is writable (see relation_mmrs_mem)
  - ks_local_mem_safe
    - that for all addresses, if an address is safe, then nobody else has write access
      (see relation_mmrs_mem)

*)

term "TCB t"
term "t :: tcb"
definition
  mspec_transform :: "abstract_state \<Rightarrow> mspec_state"
where
  "mspec_transform s \<equiv> \<lparr>
     cur_thread_cnode = (case kheap s (cur_thread s) of
       Some (TCB t) \<Rightarrow> tcb_cnode_map t |
       _ \<Rightarrow> \<lambda>_. None),
     cur_thread_bound_notification = (case kheap s (cur_thread s) of
       Some (TCB t) \<Rightarrow> tcb_bound_notification t |
       _ \<Rightarrow> None)
   \<rparr>"

term "is_reply_cap"
definition
  valid_reply_obj_for_tcb :: "mspec_state \<Rightarrow> abstract_state \<Rightarrow> cnode_index \<Rightarrow> obj_ref \<Rightarrow> bool"
where
  (* FIXME: Ideally we don't want to take the abstract_state s as an argument here,
     if we want to phrase this purely as a predicate on mspec_state m. But that means
     getting what we need of `kheap s` into the mspec_state - maybe as local_mem? *)
  "valid_reply_obj_for_tcb m s i tp \<equiv> case cur_thread_cnode m i of
     Some (ReplyCap rp _) \<Rightarrow> (case kheap s rp of
       Some (Reply r) \<Rightarrow> reply_tcb r = Some tp |
       _ \<Rightarrow> False) |
     _ \<Rightarrow> False"

(* Experimentation to find more usable lemmas about return values of monads *)
definition
  get_message_info_ret :: "'a state \<Rightarrow> obj_ref \<Rightarrow> message_info \<Rightarrow> bool"
where
  "get_message_info_ret s thread r \<equiv> \<exists>t u. the (kheap s thread) = TCB t \<and>
    arch_tcb_context_get (tcb_arch t) = ARM.UserContext u \<and>
    r = data_to_message_info (u msg_info_register)"

lemma get_message_info_ret_valid:
  "\<lbrace>\<lambda>s'. s = s'\<rbrace> get_message_info (cur_thread s) \<lbrace>\<lambda> r s''. get_message_info_ret s (cur_thread s) r\<rbrace>"
  unfolding get_message_info_def get_message_info_ret_def
  apply wp
   unfolding as_user_def
   apply wpsimp
  apply wpsimp
  apply(rename_tac y x xa)
  apply(rule_tac x=y in exI)
  unfolding ARM.getRegister_def get_tcb_def gets_def get_def
  apply wpsimp
  apply(clarsimp split:option.splits kernel_object.splits simp:bind_def return_def)
  apply(rule_tac x="ARM.user_regs (arch_tcb_context_get (tcb_arch y))" in exI)
  apply wpsimp
  by (meson ARM.user_context.exhaust_sel)
thm use_valid[OF _ get_message_info_ret_valid,simplified get_message_info_ret_def]

(* Maybe do transfer_caps first to see how caps gets used.
  UPDATE: it never gets called, because the sender never has grant rights.
find_theorems lookup_extra_caps
thm lookup_extra_caps_def
definition lookup_extra_caps_ret ::
  "'a state \<Rightarrow> obj_ref \<Rightarrow> data option \<Rightarrow> message_info \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> bool"
where
  "lookup_extra_caps_ret s sender sbuf mi cs \<equiv> True"
*)

(* find_theorems(150) transfer_caps_loop valid *)
thm transfer_caps_def transfer_caps_loop.simps
(* Maybe also look to see if Microkit ever transfers caps via sending it to the server loop.
  If not, then we can skip the entire transfer caps loop. *)

(* Turns out Microkit won't transfers caps via channels, their endpoints shouldn't be given Grant.
  So we can specify do_normal_transfer's behaviour under these assumptions. *)
thm do_normal_transfer_def
thm copy_mrs_def
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

thm transfer_caps_def transfer_caps_loop.simps
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

term assert_opt
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
  "\<lbrace>\<lambda>s'. s = s'\<rbrace> get_cap p \<lbrace>\<lambda> r s''. r = the (get_cap_ret s p)\<rbrace>"
  unfolding get_cap_def get_cap_ret_def get_object_def
  by wpsimp

context Arch begin global_naming ARM_A
term lookup_ipc_buffer
find_theorems name:buffer_frame_slot
definition
  lookup_ipc_buffer_ret :: "'a state \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> bool"
where
(*  buffer_ptr \<leftarrow> thread_get tcb_ipc_buffer thread;
    buffer_frame_slot \<leftarrow> return (thread, tcb_cnode_index 2);
    buffer_cap \<leftarrow> get_cap buffer_frame_slot;
    (case buffer_cap of
      ArchObjectCap (PageCap _ p R vms _) \<Rightarrow>
        if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
        then return $ Some $ p + (buffer_ptr && mask (pageBitsForSize vms))
        else return None
    | _ \<Rightarrow> return None)
*)
  "lookup_ipc_buffer_ret s is_receiver thread r \<equiv> \<exists> t. kheap s thread = Some (TCB t) \<and>
   (let buffer_ptr = tcb_ipc_buffer t;
        buffer_frame_slot = (thread, tcb_cnode_index 2);
        buffer_cap = the (get_cap_ret s buffer_frame_slot)
     in case buffer_cap of
          ArchObjectCap (PageCap _ p R vms _) \<Rightarrow>
            if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
            then r = (p + (buffer_ptr && mask (pageBitsForSize vms)))
            else False
        | _ \<Rightarrow> False)"

thm lookup_ipc_buffer_def
lemma lookup_ipc_buffer_ret_valid:
  "\<lbrace>\<lambda>s'. s = s'\<rbrace> lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda> r s''. lookup_ipc_buffer_ret s is_receiver thread (the r)\<rbrace>"
  unfolding lookup_ipc_buffer_def lookup_ipc_buffer_ret_def
  apply wpsimp
  apply(wpsimp split:cap.splits)
  (* TODO *)
  using get_cap_ret_valid
  oops
end


term "is_ep_cap"
term "k :: kheap"
term "obj :: kernel_object"
term "e :: endpoint"
term "n :: notification"
term handle_recv (* refer to this - we need to be making the same validity checks *)
term receive_ipc (* This handles the EndpointCap case, but will check the bound notification *)
term msg_info_register
term "m :: message_info"
term "l :: msg_label"
term do_ipc_transfer
term do_normal_transfer
term as_user
term getRegister
term "SendEP q"
term get_thread_state
term "tcb_state t"
term "t :: arch_tcb"
term "p :: sender_payload"
term "Notification ntfn"
term "ntfn :: notification"
term reply_push
term set_reply_obj_ref
term data_to_message_info
thm lookup_extra_caps_def copy_mrs_def transfer_caps_def
term ARM.UserContext
definition
  valid_ep_obj_with_message :: "mspec_state \<Rightarrow> 'a state \<Rightarrow> cnode_index \<Rightarrow> mspec_recv_oracle \<Rightarrow> bool"
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
               get_message_info_ret s (cur_thread s) (the (minfo oracle))
                 \<comment> \<open>FIXME: make non-optional once I've specified the ppc case too\<close> \<and>
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
                   \<comment> \<open>FIXME: Specify sbuf, rbuf args to do_normal_transfer - WIP\<close>
                   (\<exists> mi sbuf rbuf.
                      get_message_info_ret s (cur_thread s) mi \<and>
                      (let mrs_transferred = copy_mrs_ret sbuf rbuf (mi_length mi);
                           mi' = transfer_caps_none_ret mi rbuf
                        in minfo oracle = Some (MI mrs_transferred (mi_extra_caps mi')
                                   (mi_caps_unwrapped mi') (mi_label mi)))) \<and>
                   badge_val oracle = sender_badge data \<and>
                   new_reply_tcb oracle = Some sender |
                 _ \<Rightarrow> False) |
               _ \<Rightarrow> False) |
             _ \<Rightarrow> False)) |
           _ \<Rightarrow> False) |
         _ \<Rightarrow> False) |
       _ \<Rightarrow> False) |
     _ \<Rightarrow> False"

thm do_normal_transfer_def
  do_ipc_transfer_def
  receive_ipc_def

end