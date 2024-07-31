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
(* The 2nd member is supposed to give us the new reply cap. *)
(* The 3rd member of the KernelOracle tuple was of type SeL4_Ntfn. My guess is this was meant
   to mean a type for the notification word. But that's only in the notification case; in the
   endpoint case, this should be the badge of the endpoint capability invoked by the sender. *)
type_synonym mspec_recv_oracle = "(message_info \<times> cap) \<times> badge"

record mspec_state =
  cur_thread_cnode :: cnode_contents
  cur_thread_bound_notification :: "obj_ref option"
  (* Dropped: (ks_reply_obj_has_cap (Array SeL4_Cap Bool)).
     I think this can instead be phrased as a predicate on the CNode contents.
     See valid_reply_obj_for_tcb below for experimentation. *)
  (* Dropped: (ks_recv_oracle (Maybe KernelOracle)).
     Again trying to phrase it as a predicate on the CNode contents.
     See valid_ep_obj_with_message below. *)
  (* TODO: (ks_local_mem Mem) *)
  (* TODO: (ks_local_mem_writable (Array Word64 Bool)) *)
  (* TODO: (ks_local_mem_safe (Array Word64 Bool)) *)

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

term "is_ep_cap"
term "k :: kheap"
term "obj :: kernel_object"
term "e :: endpoint"
term "n :: notification"
term handle_recv (* refer to this - we need to be making the same validity checks *)
term receive_ipc (* This handles the EndpointCap case *)
term "SendEP q"
term get_thread_state
term "tcb_state t"
term "p :: sender_payload"
term receive_signal (* This handles the NotificationCap case *)
term "Notification ntfn"
term "ntfn :: notification"
definition
  valid_ep_obj_with_message :: "mspec_state \<Rightarrow> abstract_state \<Rightarrow> cnode_index \<Rightarrow> mspec_recv_oracle \<Rightarrow> bool"
where
  (* FIXME: Again, ideally we don't want to take the abstract_state s as an argument here. *)
  "valid_ep_obj_with_message m s i oracle \<equiv> case cur_thread_cnode m i of
     Some (EndpointCap ref _ rights) \<Rightarrow> AllowRead \<in> rights \<and>
       (case kheap s ref of Some (Endpoint ep) \<Rightarrow>
         (case ep of SendEP q \<Rightarrow> q \<noteq> [] \<and>
           (case kheap s (hd q) of Some (TCB sender) \<Rightarrow>
             \<comment> \<open>TODO: Assert fst (fst oracle) corresponds to the message_info Recv would return.\<close>
             \<comment> \<open>TODO: Assert snd (fst oracle) corresponds to the new reply cap.\<close>
             (case tcb_state sender of BlockedOnSend _ data \<Rightarrow> snd oracle = sender_badge data |
             _ \<Rightarrow> False) |
           _ \<Rightarrow> False) |
         _ \<Rightarrow> False) |
       _ \<Rightarrow> False) |
     Some (NotificationCap ref _ rights) \<Rightarrow> AllowRead \<in> rights \<and>
       (case kheap s ref of Some (Notification ntfn) \<Rightarrow>
         \<comment> \<open>TODO: Assert fst (fst oracle) corresponds to the message_info Recv would return.\<close>
         \<comment> \<open>TODO: Assert snd (fst oracle) corresponds to the new reply cap.\<close>
         (case ntfn_obj ntfn of ActiveNtfn badge \<Rightarrow> snd oracle = badge |
         _ \<Rightarrow> False) |
       _ \<Rightarrow> False) |
     _ \<Rightarrow> False"

end