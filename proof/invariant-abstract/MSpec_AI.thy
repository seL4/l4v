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

(* MCS only - no reply cap argument or related pre/postconditions on non-MCS kernel
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
*)

(* Experimentation to find more usable lemmas about return values of monads *)
definition
  getRegister_as_user_ret :: "'a state \<Rightarrow> obj_ref \<Rightarrow> register \<Rightarrow> machine_word option"
where
  "getRegister_as_user_ret s thread r \<equiv> case kheap s thread of
    Some (TCB t) \<Rightarrow> (case arch_tcb_context_get (tcb_arch t) of
      AARCH64.UserContext _ u \<Rightarrow> Some (u r)) |
    _ \<Rightarrow> None"

lemma getRegister_as_user_ret_valid:
  "\<lbrace>\<lambda>s'. s = s'\<rbrace> as_user t $ getRegister r
   \<lbrace>\<lambda> r' s''. s = s'' \<and> getRegister_as_user_ret s t r = Some r'\<rbrace>"
  unfolding getRegister_as_user_ret_def
  apply wp
   unfolding as_user_def
   apply wpsimp
  apply wpsimp
  unfolding AARCH64.getRegister_def get_tcb_def gets_def get_def
  apply(clarsimp split:option.splits kernel_object.splits AARCH64.user_context.splits
    simp:bind_def return_def)
  using AARCH64.user_context.sel by force

definition
  get_message_info_ret :: "'a state \<Rightarrow> obj_ref \<Rightarrow> message_info option"
where
  "get_message_info_ret s thread \<equiv> case kheap s thread of
    Some (TCB t) \<Rightarrow> (case arch_tcb_context_get (tcb_arch t) of
      AARCH64.UserContext _ u \<Rightarrow> Some (data_to_message_info (u msg_info_register))) |
    _ \<Rightarrow> None"

lemma get_message_info_ret_valid:
  "\<lbrace>\<lambda>s'. s = s'\<rbrace> get_message_info t
   \<lbrace>\<lambda> r s''. s = s'' \<and> get_message_info_ret s t = Some r\<rbrace>"
  unfolding get_message_info_def get_message_info_ret_def
  apply wp
   unfolding as_user_def
   apply wpsimp
  apply wpsimp
  unfolding AARCH64.getRegister_def get_tcb_def gets_def get_def
  apply(clarsimp split:option.splits kernel_object.splits AARCH64.user_context.splits
    simp:bind_def return_def)
  using AARCH64.user_context.sel by force

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

(* FIXME: We know all these things are true, I'm just not phrasing them in a way
   that makes them usable in the context of a wp proof.
   In particular, how do we say things about arguments to wp proofs if those arguments
   don't immediately seem to rely on the state? *)

(* need caps = [] in the precondition for this to be usable
lemma transfer_caps_none_valid:
  "\<lbrace>P\<rbrace> transfer_caps info [] endpoint receiver recv_buffer
   \<lbrace>\<lambda> r _. r = transfer_caps_none_ret info recv_buffer\<rbrace>"
  unfolding transfer_caps_def transfer_caps_none_ret_def
  by wpsimp
*)

(* no longer needed, just use hoare_strengthen post to achieve this
lemma transfer_caps_loop_none:
  "(\<forall> r s. r = MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi) (mi_label mi) \<longrightarrow> Q r s) \<Longrightarrow>
   \<lbrace>\<lambda>s. caps = []\<rbrace> transfer_caps_loop ep rcv_buffer n caps slots mi \<lbrace>Q\<rbrace>"
  unfolding transfer_caps_def
  apply (wpsimp simp:Let_def split:option.splits)
  by (clarsimp simp:valid_def return_def)
*)

lemma transfer_caps_loop_none_valid:
  "\<lbrace>\<lambda>_. caps = []\<rbrace> transfer_caps_loop ep rcv_buffer 0 caps slots mi
   \<lbrace>\<lambda>r _. r = MI (mi_length mi) 0 (mi_caps_unwrapped mi) (mi_label mi)\<rbrace>"
  unfolding transfer_caps_def
  by (clarsimp simp:valid_def return_def)

lemma transfer_caps_none_valid:
  "\<lbrace>\<lambda>_. caps = []\<rbrace> transfer_caps info caps endpoint receiver recv_buffer
   \<lbrace>\<lambda>r s. r = transfer_caps_none_ret info recv_buffer\<rbrace>"
  unfolding transfer_caps_def transfer_caps_none_ret_def
  apply(clarsimp simp:Let_def)
  apply wpsimp
     (* ah *this* is how you use them *)
     apply(wp only:transfer_caps_loop_none_valid[THEN hoare_strengthen_post])
     apply clarsimp
    apply clarsimp
   apply wp
  apply clarsimp
  done

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
context Arch begin global_naming AARCH64_A

definition
  lookup_ipc_buffer_ret :: "('a::state_ext) state \<Rightarrow> bool \<Rightarrow> machine_word \<Rightarrow> machine_word option"
where
  "lookup_ipc_buffer_ret s is_receiver thread \<equiv>
   case get_tcb thread s of Some t \<Rightarrow>
     (let buffer_ptr = tcb_ipc_buffer t;
          buffer_frame_slot = (thread, tcb_cnode_index 4)
       in case get_cap_ret s buffer_frame_slot of
         Some (ArchObjectCap (FrameCap p R vms False _)) \<Rightarrow>
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

declare getRegister_as_user_ret_valid get_message_info_ret_valid copy_mrs_ret_valid
  transfer_caps_none_valid get_cap_ret_valid lookup_ipc_buffer_ret_valid [wp]

thm transfer_caps_none_ret_def get_message_info_ret_def

(* fragments that Tom typed in, related to forward reasoning - though he doesn't advise
   to use that approach if we can do everything wp style
  apply (rule hoare_pre)
   apply (rule_tac P="\<not> grant" in hoare_gen_asm)

  apply (rule bind_wp_fwd)
thm get_message_info_def
find_theorems valid get_message_info
thm get_mi_sp
ML_val \<open>
 @{term "do x <- f; g od"}
\<close>
find_theorems Nondet_Monad.bind valid
*)

(* Tom's suggested helpers *)
lemma asUser_setRegister_getRegister_as_user:
  "\<lbrace>\<lambda>s. P (if t = t' \<and> r = r' then Some v else getRegister_as_user_ret s t' r')\<rbrace>
    as_user t (setRegister r v)
  \<lbrace>\<lambda>rv s. P (getRegister_as_user_ret s t' r')\<rbrace>"
  sorry

find_consts "_ \<Rightarrow> _ option \<Rightarrow> _ option"

lemma get_message_info_ret_getRegister_as_user_ret:
  "get_message_info_ret s t =
    Option.map_option data_to_message_info (getRegister_as_user_ret s t msg_info_register)"
  sorry

lemma do_normal_transfer_valid:
  "\<lbrace>(\<lambda>s. \<comment> \<open>MCS only - no reply cap argument or related pre/postconditions on non-MCS kernel
      valid_reply_obj (mspec_transform s) s MICROKIT_REPLY_CAP \<and>\<close>
      \<comment> \<open>when do we need to assert this?
      valid_ep_obj_with_message (mspec_transform s) s MICROKIT_INPUT_CAP ro \<and>\<close>
      tcb_at sender s)
      and K (sender \<noteq> receiver \<and> grant = False)\<rbrace>
    do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda> _ s'. getRegister_as_user_ret s' receiver badge_register = Some badge \<and>
      get_message_info_ret s' receiver =
      Some (transfer_caps_none_ret (the (get_message_info_ret s' sender)) rbuf)\<rbrace>"
  unfolding do_normal_transfer_def
  apply(wpsimp wp:crunch_wps simp:do_normal_transfer_def)
(* Advice from Tom: better to stick with wp approach and bring preconds in manually as needed
   using hoare_gen_asm and appropriate such tools, or prove better lemmas to infer the needed
   preconditions for given postconditions of the individual constituent functions in question. *)
(* My brief, naive attempt to use forward reasoning:
        (* Start with a bit of forward reasoning to bring the preconds forward *)
        prefer 6
        apply blast
       prefer 6
       apply(rule get_mi_inv)
      prefer 5
      find_theorems name:hoare_seq_ext
      apply clarsimp
      apply(rule return_sp)
     prefer 4
     apply(rule valid_pre_satisfies_post)
     apply assumption
     apply wpc
*)
        thm as_user_wp_thread_set_helper
        thm get_message_info_ret_def getRegister_as_user_ret_def
        (* setting of badge register *)
        apply(wpsimp wp:asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
          simp:get_message_info_ret_getRegister_as_user_ret)
       apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register"
         in hoare_gen_asm)
       apply (simp split del: if_split)
       (* setting of message_info register *)
       (* apply(simp only:get_message_info_ret_getRegister_as_user_ret[symmetric]) *)
       apply(wpsimp wp:asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
         simp:set_message_info_def get_message_info_ret_getRegister_as_user_ret)
      apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register \<and> caps = []"
         in hoare_gen_asm)
      apply clarsimp
      (* Tom: shouldn't be needing to insert such facts in here
      apply(rule_tac P="\<lambda>s. tcb_at sender s" in hoare_gen_asm_spec)
       apply(rotate_tac -1)
       apply assumption
      *)
      apply(wp only:transfer_caps_none_valid[THEN hoare_strengthen_post])
      apply(clarsimp simp only:transfer_caps_none_ret_def)
      (* no need for this now
      apply(rule conjI)
       (* badge_val conjunct *)
       apply clarsimp
       apply(clarsimp simp:Let_def)
       apply(clarsimp simp:getRegister_as_user_ret_def get_message_info_ret_def)
       apply(clarsimp simp:setRegister_def modify_def bind_def get_def put_def)
      *)
      (* message_info conjunct *)
      apply(clarsimp simp:Let_def split:option.splits)
      (*
      apply(clarsimp simp:getRegister_as_user_ret_def get_message_info_ret_def)
      apply(clarsimp simp:setRegister_def modify_def bind_def get_def put_def)
      *)
      (* Still not sure how useful this validity predicate is *)
      using data_to_message_info_valid
      apply -
      apply(clarsimp simp:valid_message_info_def)
      (* Is what's missing a predicate about mi *being* based on the message info retrieved
         from the sender's registers, from the earlier part of do_normal_transfer? *)
      apply(clarsimp simp:data_to_message_info_def)
      apply(clarsimp simp:mi_length_def split:message_info.splits)
      apply(erule_tac x="(mi_label mi << 12) || mrs_transferred" in meta_allE)
      apply(rule conjI)
       apply(clarsimp simp:Let_def split:if_splits)
        (* when the message info length v > 0x78 according to the sender, then the
           message info length returned to the reciever should be 0x78 *)
        defer
       (* otherwise the message info length should be v *)
       defer
      (*
      apply(clarsimp simp:mi_label_def mask_def split:message_info.splits)
      apply(clarsimp simp:of_nat_def msg_max_length_def)
      *)
      apply(rule conjI)
       (* FIXME: that the extra caps field of MI is 0 *)
       defer
      apply(rule conjI)
       (* FIXME: that the caps_unwrapped field of MI is 0 *)
       defer
      thm data_to_message_info_def
      (* FIXME: that the label field of MI is the expected value *)
      defer
     (* I suspect the culprit is the use of transfer_caps_none_valid *)
     thm transfer_caps_none_valid
     apply wpsimp
    apply wpsimp
   apply wpsimp
  apply wpsimp
  (* use this to resolve badge_register vs msg_info_register distinctness*)
  apply(solves\<open>simp add: AARCH64.badgeRegister_def AARCH64.msgInfoRegister_def badge_register_def msg_info_register_def\<close>)
  oops

lemma handle_SysRecv_syscall_valid:
  "\<lbrace>\<lambda>s. \<comment> \<open>MCS only - no reply cap argument or related pre/postconditions on non-MCS kernel
      valid_reply_obj (mspec_transform s) s MICROKIT_REPLY_CAP \<and>\<close>
      valid_ep_obj_with_message (mspec_transform s) s MICROKIT_INPUT_CAP ro\<rbrace>
    handle_recv True
   \<lbrace>\<lambda> _ s'. getRegister_as_user_ret s' (cur_thread s') badge_register = Some (badge_val ro) \<and>
      get_message_info_ret s' (cur_thread s') = Some (minfo ro)\<rbrace>"
  apply(wpsimp wp:crunch_wps simp:handle_recv_def)
      defer
     apply(wpsimp wp:crunch_wps)
      apply(wpsimp simp:Let_def)
       (* 17 subgoals *)
       apply(wpsimp simp:receive_ipc_def complete_signal_def)
        (* 23 subgoals *)
        apply(wpsimp wp:crunch_wps set_object_wp get_simple_ko_wp get_object_wp
          simp:set_simple_ko_def setRegister_def as_user_def set_thread_state_def)+
          apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def)
         apply(wpsimp wp:crunch_wps set_object_wp simp:setup_caller_cap_def)+
          (* 30 subgoals *)
          apply(rule conjI)
           apply(wpsimp wp:crunch_wps simp:cap_insert_def)
               (* 41 subgoals *)
               apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def)
              apply(wpsimp wp:crunch_wps set_object_wp get_object_wp
                simp:update_cdt_def set_cdt_def set_cap_def)+
            (* 35 subgoals *)
            apply(wpsimp wp:crunch_wps get_object_wp simp:set_untyped_cap_as_full_def get_cap_def
              set_thread_state_def)+
          apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def)
         apply(wpsimp wp:crunch_wps set_object_wp)+
        apply(wpsimp wp:crunch_wps get_object_wp simp:cap_insert_def)
                 apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def)
                apply(wpsimp wp:crunch_wps simp:update_cdt_def set_cdt_def set_cap_def)+         
               apply(wpsimp wp:crunch_wps set_object_wp get_object_wp)+
           apply(wpsimp wp:crunch_wps get_object_wp simp:set_untyped_cap_as_full_def get_cap_def
             set_thread_state_def)+
         apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def)
        apply(wpsimp wp:crunch_wps set_object_wp get_object_wp)+
      apply(wpsimp wp:crunch_wps simp:set_thread_state_def)+
        apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def)
       apply(wpsimp wp:crunch_wps set_object_wp)+
      apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def)
     apply(wpsimp wp:crunch_wps simp:set_thread_state_def)+
       apply(wpsimp wp:crunch_wps set_object_wp|solves\<open>clarsimp simp:getRegister_as_user_ret_def get_message_info_ret_def\<close>)+
       apply(wpsimp wp:crunch_wps simp:do_ipc_transfer_def do_normal_transfer_def)+
                (* 39 subgoals *)
                apply(wpsimp wp:crunch_wps as_user_wp_thread_set_helper set_object_wp
                  simp:thread_set_def set_message_info_def)+
              apply(wp only:transfer_caps_none_valid[THEN hoare_strengthen_post])
              apply clarsimp
              apply(clarsimp simp only:transfer_caps_none_ret_def)
              apply(rule conjI)
               apply clarsimp
               apply(rule conjI)
                apply clarsimp
                apply(rule conjI)
                 apply clarsimp
                 apply(rule conjI)
                  apply(clarsimp simp:Let_def)
                  apply(clarsimp simp:getRegister_as_user_ret_def get_message_info_ret_def)
                  apply(rule conjI)
                   apply clarsimp
                   apply(rule conjI)
                    apply clarsimp
                    apply(clarsimp split:option.splits)
     (* FIXME: Make use of the fact that we know from the precondition there are no caps to be
        transferred because the endpoint cap has no grant rights. *)
  oops

end (* Arch AARCH64_A *)

end