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
  MICROKIT_INPUT_CAP_NAT :: nat
  MICROKIT_INPUT_CAP :: cnode_index
  MICROKIT_REPLY_CAP :: cnode_index

axiomatization where
  microkit_input_reply_caps_distinct:
    "MICROKIT_INPUT_CAP \<noteq> MICROKIT_REPLY_CAP" and
  MICROKIT_INPUT_CAP_NAT_def:
    "MICROKIT_INPUT_CAP_NAT \<equiv> 1" and
  MICROKIT_INPUT_CAP_def:
    (* FIXME: The conventional constant Microkit uses is 1, but I'm not sure that's
       raw value is what tcb_cnode_index's input corresponds to *)
    "MICROKIT_INPUT_CAP \<equiv> tcb_cnode_index MICROKIT_INPUT_CAP_NAT"

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
  "\<lbrace>\<lambda>s. P s\<rbrace> as_user t $ getRegister r
   \<lbrace>\<lambda> rv s. P s \<and> getRegister_as_user_ret s t r = Some rv\<rbrace>"
  unfolding getRegister_as_user_ret_def
  apply wp
   unfolding as_user_def
   apply(wpsimp wp:set_object_wp)
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
  "\<lbrace>P\<rbrace> get_message_info t
   \<lbrace>\<lambda> rv s. P s \<and> get_message_info_ret s t = Some rv \<and> valid_message_info rv\<rbrace>"
  unfolding get_message_info_def get_message_info_ret_def
  apply wp
   unfolding as_user_def
   apply(wpsimp wp:set_object_wp)
  apply wpsimp
  unfolding AARCH64.getRegister_def get_tcb_def gets_def get_def
  apply(clarsimp split:option.splits kernel_object.splits AARCH64.user_context.splits
    simp:bind_def return_def)
  apply(rule conjI)
   using AARCH64.user_context.sel apply force
  by (rule data_to_message_info_valid)

(* FIXME: In the long run we'll need to interface off the arch-specific parts properly.
  But some of the return values depend on arch-specific implementations, so for now
  while experimenting I'll just open up the Arch context and do it in here. *)
context Arch begin global_naming AARCH64_A

(* Tom's suggested helpers *)
lemma asUser_setRegister_getRegister_as_user:
  "\<lbrace>\<lambda>s. P (if t = t' \<and> r = r' then Some v else getRegister_as_user_ret s t' r')\<rbrace>
    as_user t (setRegister r v)
  \<lbrace>\<lambda>rv s. P (getRegister_as_user_ret s t' r')\<rbrace>"
  apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
  apply(clarsimp simp:getRegister_as_user_ret_def)
  apply(rule conjI)
   apply(clarsimp split:if_splits)
    (* case: retrieving exactly the value that was set *)
    apply(clarsimp split:user_context.splits)
    apply(clarsimp simp:setRegister_def modify_def bind_def put_def)
   (* case: retrieving whatever was in that unaffected register *)
   apply(clarsimp simp:get_tcb_def split:option.splits kernel_object.splits)
   apply(force simp:setRegister_def modify_def bind_def put_def get_def split:user_context.splits)
  apply clarsimp
  done

lemma get_message_info_ret_getRegister_as_user_ret:
  "get_message_info_ret s t =
    Option.map_option data_to_message_info (getRegister_as_user_ret s t msg_info_register)"
  by (clarsimp simp:get_message_info_ret_def getRegister_as_user_ret_def
    split:option.splits kernel_object.splits user_context.splits)

end

(* copy_mrs will only return the number of message registers successfully transferred *)
thm copy_mrs_def
definition copy_mrs_ret ::
  "obj_ref option \<Rightarrow> obj_ref option \<Rightarrow> length_type \<Rightarrow> length_type"
where
  "copy_mrs_ret sbuf rbuf n \<equiv>
   let hardware_mrs_len = length (take (unat n) msg_registers);
       buf_mrs_len = case (sbuf, rbuf) of
         (Some sb_ptr, Some rb_ptr) \<Rightarrow> length [length msg_registers + 1..<Suc (unat n)] |
         _ \<Rightarrow> 0
    in min n (nat_to_len (hardware_mrs_len + buf_mrs_len))"

lemma copy_mrs_ret_leq_msg_max_length:
  "valid_message_info rv \<Longrightarrow> unat (copy_mrs_ret sbuf rbuf (mi_length rv)) \<le> msg_max_length"
  apply(clarsimp simp:valid_message_info_def)
  apply(clarsimp simp:copy_mrs_ret_def min_def Let_def split:option.splits split del:if_split)
  apply(rule conjI)
   apply clarsimp
   apply(simp only:unat_arith_simps unat_of_nat)
   apply(clarsimp simp:msg_max_length_def)
  apply clarsimp
  apply(simp only:unat_arith_simps unat_of_nat)
  apply(clarsimp simp:msg_max_length_def)
  done

(* I think we have to know that n is constrained by the wellformedness requirements of
   data_to_message_info_valid because it ultimately came from the sender's msg_info_register *)
lemma copy_mrs_ret_valid:
  "\<lbrace>(\<lambda>s. P (get_message_info_ret s t)) and K (t \<noteq> receiver \<and>
      (\<exists> mi. n = mi_length mi \<and> valid_message_info mi))\<rbrace>
     copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda> r s. P (get_message_info_ret s t) \<and> r = copy_mrs_ret sbuf rbuf n\<rbrace>"
  unfolding copy_mrs_def copy_mrs_ret_def
  apply (simp del: upt_Suc)
  (* Tom: Consider removing these from default simp/split sets if they're making the goal state
     explode. In addition, a big risk with these is that if they split your goal into conjuncts
     of two or more hoare triples, then solving one hoare triple might fill in the
     precondition's schematic variable such that proving the rest might be impossible.
  thm imp_disjL if_split *)
  apply (wpsimp simp_del: upt_Suc split_del: if_split)
    apply(rule_tac P="t \<noteq> receiver" in hoare_gen_asm)
    apply(wpsimp wp:mapM_wp' simp:get_message_info_ret_def store_word_offs_def split_del: if_split)
   apply(rule_tac P="t \<noteq> receiver" in hoare_gen_asm)
   apply(wpsimp wp:mapM_wp' hoare_vcg_imp_lift split_del: if_split)
     apply(rule_tac P="t \<noteq> receiver" in hoare_gen_asm)
     apply(wpsimp wp:AARCH64_A.asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
       simp:AARCH64_A.get_message_info_ret_getRegister_as_user_ret split_del: if_split)
    apply clarsimp
    apply(rule_tac P="t \<noteq> receiver" in hoare_gen_asm)
    apply(wpsimp wp:AARCH64_A.asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
      simp:AARCH64_A.get_message_info_ret_getRegister_as_user_ret split_del: if_split)
   apply(clarsimp simp:AARCH64_A.get_message_info_ret_getRegister_as_user_ret[symmetric]
     split del:if_split)
   apply(rule hoare_pre)
    apply(rule_tac P="t \<noteq> receiver" in hoare_gen_asm)
    apply(wpsimp wp:getRegister_as_user_ret_valid split_del: if_split)
   apply(clarsimp split:option.splits)
  apply(clarsimp simp:min_def)
  apply(insert valid_msg_length_strengthen)
  apply(erule_tac x=mi in meta_allE)
  apply clarsimp
  apply(clarsimp simp:valid_message_info_def)
  apply(simp only: unat_arith_simps unat_of_nat)
  apply clarsimp
  using not_less_eq_eq by force

(* Turns out Microkit won't transfers caps via channels, their endpoints shouldn't be given Grant.
  So we specify do_normal_transfer's behaviour under these assumptions. *)

definition transfer_caps_none_ret :: "message_info \<Rightarrow> obj_ref option \<Rightarrow> message_info"
where
  "transfer_caps_none_ret info recv_buffer \<equiv> MI (mi_length info) 0 0 (mi_label info)"

(* NB: Turns out it's idiomatic to use `\<lbrace>P and K (state-independent assumptions on args)\<rbrace>`
   to state state-independent assumptions about arguments to functions for their wp lemmas. *)

lemma transfer_caps_loop_none_valid:
  "\<lbrace>K (caps = []) and (\<lambda>s. P (get_message_info_ret s t))\<rbrace>
     transfer_caps_loop ep rcv_buffer n caps slots mi
   \<lbrace>\<lambda>r s. r = MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi) (mi_label mi) \<and>
      P (get_message_info_ret s t)\<rbrace>"
  unfolding transfer_caps_def
  by (clarsimp simp:valid_def return_def)

lemma transfer_caps_none_valid:
  "\<lbrace>K (caps = []) and (\<lambda>s. P (get_message_info_ret s t))\<rbrace>
     transfer_caps info caps endpoint receiver recv_buffer
   \<lbrace>\<lambda>r s. r = transfer_caps_none_ret info recv_buffer \<and> P (get_message_info_ret s t)\<rbrace>"
  unfolding transfer_caps_def transfer_caps_none_ret_def
  apply(clarsimp simp:Let_def)
  apply wpsimp
     (* ah *this* is how you use them *)
     apply(wp only:transfer_caps_loop_none_valid[THEN hoare_strengthen_post])
     apply clarsimp
     apply force
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
  "\<lbrace>\<lambda>s'. \<forall> cap. get_cap_ret s' p = Some cap \<longrightarrow> Q cap s'\<rbrace> get_cap p
   \<lbrace>Q\<rbrace>"
  unfolding get_cap_def get_cap_ret_def get_object_def
  by wpsimp

definition
  lookup_ipc_buffer_ret :: "('a::state_ext) state \<Rightarrow> bool \<Rightarrow> machine_word \<Rightarrow> machine_word option"
where
  "lookup_ipc_buffer_ret s is_receiver thread \<equiv>
   case get_tcb thread s of Some t \<Rightarrow>
     (let buffer_ptr = tcb_ipc_buffer t;
          buffer_frame_slot = (thread, tcb_cnode_index 4)
       in case get_cap_ret s buffer_frame_slot of
         Some (ArchObjectCap (AARCH64_A.FrameCap p R vms False _)) \<Rightarrow>
              if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
              then Some (p + (buffer_ptr && mask (AARCH64.pageBitsForSize vms)))
              else None
            | _ \<Rightarrow> None) |
   _ \<Rightarrow> None"

lemma lookup_ipc_buffer_ret_valid:
  "\<lbrace>\<lambda>s. tcb_at thread s\<rbrace>
    lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda> r s. r = lookup_ipc_buffer_ret s is_receiver thread\<rbrace>"
  unfolding AARCH64_A.lookup_ipc_buffer_def lookup_ipc_buffer_ret_def
  apply wpsimp
     apply(wpsimp wp:get_cap_ret_valid[THEN hoare_strengthen_post])
    apply wpsimp
   apply(wpsimp wp:thread_get_wp)
  apply(wpsimp simp:tcb_at_def get_tcb_def obj_at_def)
  by (clarsimp simp:get_cap_ret_def is_tcb_def
    vm_read_write_def vm_read_only_def AARCH64_A.arch_cap.simps
    split:option.splits kernel_object.splits cap.splits AARCH64_A.arch_cap.splits bool.splits)

(* Refer to these functions - we need to be making the same validity checks *)
term handle_recv
term receive_ipc (* This handles the EndpointCap case, but will check the bound notification *)
term get_bound_notification
term thread_get
term do_ipc_transfer
term do_normal_transfer
definition
  valid_ep_obj_with_ntfn :: "obj_ref \<Rightarrow> mspec_state \<Rightarrow> ('a::state_ext) state \<Rightarrow> cnode_index \<Rightarrow> mspec_recv_oracle \<Rightarrow> bool"
where
  (* FIXME: Again, ideally we don't want to take the abstract_state s as an argument here. *)
  (* FIXME: rename src to sender and refer to receiver instead of (cur_thread s) so that
     we can use this predicate for relies and guarantees across context switch *)
  "valid_ep_obj_with_ntfn src m s i oracle \<equiv> src \<noteq> cur_thread s \<and>
     \<comment> \<open>Microkit only checks notifications via EndpointCap, not via any standalone NotificationCap\<close>
     (\<exists> ref ep_badge rights.
       \<comment> \<open>cur_thread_cnode m i = Some (EndpointCap ref something rights)\<close>
       cte_wp_at ((=) (EndpointCap ref ep_badge rights)) (cur_thread s, MICROKIT_INPUT_CAP) s \<and>
       AllowRead \<in> rights \<and>
       (\<exists>ep. obj_at ((=) (Endpoint ep)) ref s \<and>
         \<comment> \<open>cur_thread_bound_notification m of Some n\<close>
         (\<exists>ntfnptr. bound_tcb_at ((=) ntfnptr) (cur_thread s) s) \<and>
         (\<forall>ntfnptr. bound_tcb_at ((=) ntfnptr) (cur_thread s) s \<longrightarrow>
           \<comment> \<open>The if (ntfnptr \<noteq> None \<and> isActive ntfn) branch should be here. See receive_ipc\<close>
           (\<exists>ntfn n badge. ntfnptr = Some n \<and>
             obj_at ((=) (Notification ntfn)) n s \<and>
             \<comment> \<open>Note: receive_ipc handles waiting bound notifications via complete_signal\<close>
             ntfn_obj ntfn = ActiveNtfn badge \<and>
             \<comment> \<open>we assert that the notification case leaves the value in the user's message_info
                register untouched from when it called seL4_Recv, so we just retrieve that here\<close>
             get_message_info_ret s (cur_thread s) = Some (minfo oracle) \<and>
             new_reply_tcb oracle = None \<and>
             badge_val oracle = badge))))"

definition
  valid_ep_obj_with_ppc :: "obj_ref \<Rightarrow> mspec_state \<Rightarrow> ('a::state_ext) state \<Rightarrow> cnode_index \<Rightarrow> mspec_recv_oracle \<Rightarrow> bool"
where
  (* FIXME: rename src to sender and refer to receiver instead of (cur_thread s) so that
     we can use this predicate for relies and guarantees across context switch *)
  "valid_ep_obj_with_ppc src m s i oracle \<equiv> src \<noteq> cur_thread s \<and>
     \<comment> \<open>Microkit only checks notifications via EndpointCap, not via any standalone NotificationCap\<close>
     (\<exists> ref ep_badge rights.
       \<comment> \<open>cur_thread_cnode m i = Some (EndpointCap ref something rights)\<close>
       cte_wp_at ((=) (EndpointCap ref ep_badge rights)) (cur_thread s, MICROKIT_INPUT_CAP) s \<and>
       AllowRead \<in> rights \<and>
       (\<exists>ep. obj_at ((=) (Endpoint ep)) ref s \<and>
         \<comment> \<open>cur_thread_bound_notification m of Some n\<close>
         (\<exists>ntfnptr. bound_tcb_at ((=) ntfnptr) (cur_thread s) s) \<and>
           \<comment> \<open>The if (ntfnptr \<noteq> None \<and> isActive ntfn) branch is be here. See receive_ipc.
               Everything above this should be identical to valid_ep_obj_with_ntfn.
               FIXME: Find a nice way to refactor out this redundancy.
               FIXME: Refactor the below to be idiomatic, too.\<close>
         \<comment> \<open>if there's no bound notification to receive, receive_ipc then checks the endpoint\<close>
         (case ep of SendEP q \<Rightarrow> q \<noteq> [] \<and>
               src = (hd q) \<and> \<comment> \<open>This is a bit of a hack because the oracle doesn't really
                 identify the sender TCB, but it's useful to know this for the proofs.\<close>
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
             _ \<Rightarrow> False)))"


(* this should be true if msg_max_length = 128, because mask 7 is 127 *)
lemma mask_7_under_msg_max_idemp:
  "unat (n::word64) \<le> msg_max_length \<Longrightarrow> n && mask 7 = n"
  apply(simp only:and_mask_eq_iff_le_mask)
  apply(clarsimp simp:msg_max_length_def mask_def)
  apply unat_arith (* also try at other times: uint_arith *)
  done

(* an existing lemma tells us when we shift by the mask length then mask it, we get 0 *)
thm shiftl_mask_is_0

(* generalisation when shifted *further* left of the mask. turns out this is provable
  using exactly the same tactic as shiftl_mask_is_0 *)
lemma shiftl_ge_mask_is_0:
  "n \<ge> m \<Longrightarrow> ((y::word64) << n) && mask m = 0"
  by (simp flip: take_bit_eq_mask add: take_bit_push_bit shiftl_def)

(* Johannes: Can try `apply word_bitwise` if word size is fixed. *)
(* also potentially useful: methods word_eqI and word_eqI_solve *)
lemma mi_to_data_to_mi_len:
  "valid_message_info mi \<Longrightarrow>
   unat (mi_length (data_to_message_info (message_info_to_data mi))) =
     min msg_max_length (unat (mi_length mi))"
  apply(case_tac mi)
  apply(clarsimp simp:valid_message_info_def data_to_message_info_def Let_def min_def
    split del:if_split)
  apply(clarsimp simp:bit.conj_disj_distrib2 shiftl_ge_mask_is_0 msg_max_length_def)
  apply(simp only:unat_arith_simps unat_of_nat)
  apply(force simp:mask_7_under_msg_max_idemp msg_max_length_def)
  done

lemma trim_shiftlr_above_mask:
  "r \<le> l \<Longrightarrow> m \<le> l - r \<Longrightarrow> ((x::64 word) << l >> r) && mask m = 0"
  (* informally: if m \<le> l - r, then x << (l - r) lies outside the mask of m *)
  apply(simp add:shiftl_shiftr1[where b=l and c=r and a=x])
  apply word_eqI
  done

lemma trim_shiftlr_below_mask:
  "r > l \<Longrightarrow> (x::64 word) \<le> mask (r - l) \<Longrightarrow> (x << l >> r) && mask m = 0"
  apply(simp add:shiftl_shiftr2[where b=l and c=r and a=x])
  apply word_eqI
  done

context Arch begin global_naming AARCH64_A

lemma mi_to_data_to_mi:
  "valid_message_info mi \<Longrightarrow>
   mi_extra_caps mi = 0 \<Longrightarrow>
   mi_caps_unwrapped mi = 0 \<Longrightarrow>
   \<comment> \<open>I think we get this only about the produced MI by the fact that the upper 12 bits
     of the label will be truncated by shifting the 64-bit value left by 12 bits.
   mi_label mi \<le> mask 52 \<Longrightarrow> \<close>
   data_to_message_info (message_info_to_data mi) =
   MI (word_of_nat (min msg_max_length (unat (mi_length mi)))) 0 0 (mi_label mi && mask 52)"
  thm message_info_to_data_def
  apply(case_tac mi)
  apply(clarsimp simp:valid_message_info_def data_to_message_info_def Let_def
    split del:if_split)
  apply(rule conjI)
   (* essentially redoing the mi_to_data_to_mi_len proof here *)
   apply(clarsimp simp:bit.conj_disj_distrib2 shiftl_ge_mask_is_0 msg_max_length_def)
   apply(simp only:unat_arith_simps unat_of_nat)
   apply(force simp:mask_7_under_msg_max_idemp msg_max_length_def)
  (* for getting rid of x1 from each conjunct *)
  apply(insert trim_shiftlr_below_mask[where l=0])
  apply simp
  apply(rename_tac x1 x4)
  apply(rule conjI)
   (* finish getting rid of x1 *)
   apply(erule_tac x=7 in meta_allE)
   apply(erule_tac x=x1 in meta_allE)
   apply(erule_tac x=2 in meta_allE)
   apply(clarsimp simp:bit.disj_assoc msg_max_length_def)
   apply(erule meta_impE)
    apply(clarsimp simp:msg_max_length_def mask_def)
    apply unat_arith (* also try at other times: uint_arith *)
   apply(clarsimp simp:shiftr_over_or_dist)
   apply(clarsimp simp:bit.conj_disj_distribs)
   (* get rid of x4 *)
   apply(simp add:trim_shiftlr_above_mask)
  apply(rule conjI)
   apply(erule_tac x=9 in meta_allE)
   apply(erule_tac x=x1 in meta_allE)
   apply(erule_tac x=3 in meta_allE)
   apply(clarsimp simp:bit.disj_assoc msg_max_length_def)
   apply(erule meta_impE)
    apply(clarsimp simp:msg_max_length_def mask_def)
    apply unat_arith
   apply(clarsimp simp:shiftr_over_or_dist bit.conj_disj_distribs)
   apply(simp add:trim_shiftlr_above_mask)
  apply(erule_tac x=12 in meta_allE)
  apply(erule_tac x=x1 in meta_allE)
  apply(erule_tac x=52 in meta_allE)
  apply(clarsimp simp:bit.disj_assoc msg_max_length_def)
  apply(erule meta_impE)
   apply(clarsimp simp:msg_max_length_def mask_def)
   apply unat_arith
  apply(clarsimp simp:shiftr_over_or_dist bit.conj_disj_distribs)
  by word_eqI metis

end

definition do_normal_transfer_mi :: "message_info \<Rightarrow> obj_ref option
   \<Rightarrow> obj_ref option \<Rightarrow> message_info"
where
  "do_normal_transfer_mi mi sbuf rbuf \<equiv>
     (let mrs_transferred = copy_mrs_ret sbuf rbuf (mi_length mi)
        \<comment> \<open>With grant = False, the extra_caps and caps_unwrapped end up as 0. Moreover, the
           conversion from MI to data format will truncate the original label's top 12 bits.\<close>
        in (MI mrs_transferred 0 0 (mi_label mi && mask 52)))"

lemma asUser_setRegister_lookup_ipc_buffer_ret:
  "\<lbrace>\<lambda>s. P (lookup_ipc_buffer_ret s b t')\<rbrace>
     as_user t (setRegister r v)
   \<lbrace>\<lambda>rv s. P (lookup_ipc_buffer_ret s b t')\<rbrace>"
  apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
  apply(clarsimp simp:AARCH64.setRegister_def modify_def bind_def put_def get_def)
  (* it should come down to lookup_ipc_buffer not depending on whatever setRegister could change *)
  by (auto simp:lookup_ipc_buffer_ret_def get_cap_ret_def get_tcb_def tcb_cnode_map_def
    vm_read_write_def vm_read_only_def AARCH64_A.arch_cap.simps
    split:option.splits kernel_object.splits cap.splits AARCH64_A.arch_cap.splits bool.splits)

lemma transfer_caps_loop_none_lookup_ipc_buffer:
  "\<lbrace>K (caps = []) and (\<lambda>s. P (lookup_ipc_buffer_ret s b t))\<rbrace>
     transfer_caps_loop ep rcv_buffer n caps slots mi
   \<lbrace>\<lambda>_ s. P (lookup_ipc_buffer_ret s b t)\<rbrace>"
  unfolding transfer_caps_def
  by (clarsimp simp:valid_def return_def)

lemma transfer_caps_none_lookup_ipc_buffer:
  "\<lbrace>K (caps = []) and
   (\<lambda>s. P (lookup_ipc_buffer_ret s b t))\<rbrace>
    transfer_caps info caps endpoint receiver recv_buffer
  \<lbrace>\<lambda>_ s. P (lookup_ipc_buffer_ret s b t)\<rbrace>"
  by (wpsimp simp:transfer_caps_def wp:transfer_caps_loop_none_lookup_ipc_buffer)

lemma copy_mrs_lookup_ipc_buffer:
  "\<lbrace>\<lambda>s. P (lookup_ipc_buffer_ret s b t)\<rbrace>
     copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>_ s. P (lookup_ipc_buffer_ret s b t)\<rbrace>"
  unfolding copy_mrs_def copy_mrs_ret_def
  apply(simp del: upt_Suc)
  apply(wpsimp simp_del:upt_Suc split_del:if_split)
    apply(wpsimp wp:mapM_wp' split_del: if_split)
     apply(wpsimp simp:store_word_offs_def
       lookup_ipc_buffer_ret_def get_cap_ret_def get_tcb_def tcb_cnode_map_def
       vm_read_write_def vm_read_only_def
       split_del: if_split simp_del: upt_Suc
       split:option.splits kernel_object.splits cap.splits AARCH64_A.arch_cap.splits bool.splits)
    apply(wpsimp simp:load_word_offs_def
      lookup_ipc_buffer_ret_def get_cap_ret_def get_tcb_def tcb_cnode_map_def
       vm_read_write_def vm_read_only_def AARCH64_A.arch_cap.simps
       split_del: if_split simp_del: upt_Suc
       split:option.splits kernel_object.splits cap.splits AARCH64_A.arch_cap.splits bool.splits)
    apply(clarsimp split:if_splits)
     apply(fastforce simp:AARCH64_A.arch_cap.simps)
    apply(fastforce simp:AARCH64_A.arch_cap.simps)
   apply(wpsimp wp:mapM_wp' split_del: if_split)
    apply(wpsimp wp:asUser_setRegister_lookup_ipc_buffer_ret)
   apply(wpsimp wp:getRegister_as_user_ret_valid split_del: if_split)
  apply force
  done

lemma do_normal_transfer_lookup_ipc_buffer_ret:
  "\<lbrace>(\<lambda>s. P (lookup_ipc_buffer_ret s b t))
      and K (sender \<noteq> receiver \<and> \<not> grant)\<rbrace>
    do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda> _ s. P (lookup_ipc_buffer_ret s b t)\<rbrace>"
  apply(wpsimp simp:do_normal_transfer_def)
        apply(wpsimp wp:asUser_setRegister_lookup_ipc_buffer_ret)
       apply(wpsimp wp:asUser_setRegister_lookup_ipc_buffer_ret simp:set_message_info_def)
      apply(wpsimp wp:transfer_caps_none_lookup_ipc_buffer)
     apply(wpsimp wp:copy_mrs_lookup_ipc_buffer)
    apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant" in hoare_gen_asm)
    apply wpsimp
   apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant" in hoare_gen_asm)
   apply(wpsimp wp:asUser_setRegister_lookup_ipc_buffer_ret)
  apply force
  done

declare message_info_to_data.simps [simp del] (* proof becomes a mess if we leave these in *)
lemma do_normal_transfer_valid:
  "\<lbrace>(\<lambda>s. \<comment> \<open>MCS only - no reply cap argument or related pre/postconditions on non-MCS kernel
      valid_reply_obj (mspec_transform s) s MICROKIT_REPLY_CAP \<and>\<close>
      \<comment> \<open>when do we need to assert this?
      valid_ep_obj_with_message (mspec_transform s) s MICROKIT_INPUT_CAP ro \<and>\<close>
      \<comment> \<open>P' (get_message_info_ret s sender) (lookup_ipc_buffer_ret s False sender) (lookup_ipc_buffer_ret s True receiver)\<close>
      P (lookup_ipc_buffer_ret s False sender) \<and>
      P' (lookup_ipc_buffer_ret s True receiver) \<and>
      P'' (get_message_info_ret s sender))
      and K (sender \<noteq> receiver \<and> \<not> grant)\<rbrace>
    do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda> _ s.
      P (lookup_ipc_buffer_ret s False sender) \<and>
      P' (lookup_ipc_buffer_ret s True receiver) \<and>
      P'' (get_message_info_ret s sender) \<and>
      getRegister_as_user_ret s receiver badge_register = Some badge \<and>
      get_message_info_ret s receiver = Some (do_normal_transfer_mi
        (the (get_message_info_ret s sender)) sbuf rbuf) \<and>
      valid_message_info (the (get_message_info_ret s sender))
      \<comment> \<open>P' (get_message_info_ret s' sender) (lookup_ipc_buffer_ret s' False sender) (lookup_ipc_buffer_ret s' True receiver)\<close>\<rbrace>"
  apply(wpsimp simp:do_normal_transfer_def)
(* Advice from Tom: better to stick with wp approach & bring in only state-independent assumptions
   using hoare_gen_asm etc, but for state-dependent preconds, prove better lemmas to infer needed
   preconditions for given postconditions of the individual constituent functions in question. *)
        (* setting of badge register *)
        apply(rule hoare_vcg_conj_lift)
         apply(wpsimp wp:asUser_setRegister_lookup_ipc_buffer_ret)
        apply(rule hoare_vcg_conj_lift)
         apply(wpsimp wp:asUser_setRegister_lookup_ipc_buffer_ret)
        apply(wpsimp wp:AARCH64_A.asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
          simp:AARCH64_A.get_message_info_ret_getRegister_as_user_ret Let_def split_del: if_split)
       apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register"
         in hoare_gen_asm)
       apply(simp split del: if_split)
       apply(rule hoare_vcg_conj_lift)
        apply(wpsimp wp:asUser_setRegister_lookup_ipc_buffer_ret simp:set_message_info_def)
       apply(rule hoare_vcg_conj_lift)
        apply(wpsimp wp:asUser_setRegister_lookup_ipc_buffer_ret simp:set_message_info_def)
       (* setting of message_info register *)
       apply(wpsimp wp:AARCH64_A.asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
         simp:set_message_info_def AARCH64_A.get_message_info_ret_getRegister_as_user_ret)
      apply(simp split del: if_split)
      apply(clarsimp simp:AARCH64_A.get_message_info_ret_getRegister_as_user_ret[symmetric])
      apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register \<and>
        caps = [] \<and> mrs_transferred = copy_mrs_ret sbuf rbuf (mi_length mi) \<and>
        valid_message_info mi" in hoare_gen_asm)
      apply clarsimp
      apply(rule hoare_vcg_conj_lift)
       apply(wpsimp wp:transfer_caps_none_lookup_ipc_buffer)
      apply(rule hoare_vcg_conj_lift)
       apply(wpsimp wp:transfer_caps_none_lookup_ipc_buffer)
      (* Note: Tom advised to try not to insert state-dependent facts using hoare_gen_asm_spec,
         but rather try to prove wp lemmas that give the needed precondition. *)
      apply(wp only:transfer_caps_none_valid[where t=sender, THEN hoare_strengthen_post])
      apply clarsimp
      apply assumption
     apply(wpsimp split_del:if_split)
     apply(rule hoare_vcg_conj_lift)
      apply(wpsimp wp:copy_mrs_lookup_ipc_buffer)
     apply(rule hoare_vcg_conj_lift)
      apply(wpsimp wp:copy_mrs_lookup_ipc_buffer)
     apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register \<and>
        caps = [] \<and> valid_message_info mi" in hoare_gen_asm)
     apply(wpsimp wp:copy_mrs_ret_valid[THEN hoare_strengthen_post])
     apply(simp split del:if_split)
    apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register"
      in hoare_gen_asm)
    apply wpsimp
   apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register"
     in hoare_gen_asm)
   apply wpsimp
   apply(clarsimp simp:transfer_caps_none_ret_def)
   apply(wpsimp wp:get_message_info_ret_valid[where P=\<top>, THEN hoare_strengthen_post])
   apply(rule conjI)
    using AARCH64_A.mi_to_data_to_mi
    apply(erule_tac x="(MI (copy_mrs_ret sbuf rbuf (mi_length rv)) 0 0 (mi_label rv))" in meta_allE)
    apply simp
    apply(erule meta_impE)
     apply(clarsimp simp:valid_message_info_def)
     apply(clarsimp simp:copy_mrs_ret_def split:option.splits split del:if_split)
     apply(rule conjI)
      apply(clarsimp simp:min_def)
      apply(simp only:unat_arith_simps unat_of_nat)
     apply clarsimp
     apply(clarsimp simp:min_def)
     apply(simp only:unat_arith_simps unat_of_nat)
    apply(clarsimp simp:do_normal_transfer_mi_def)
    using copy_mrs_ret_leq_msg_max_length do_normal_transfer_mi_def
    apply force
   apply(rule_tac x=rv in exI)
   apply clarsimp
  apply clarsimp
  (* resolve badge_register vs msg_info_register distinctness*)
  by (simp add: AARCH64.badgeRegister_def AARCH64.msgInfoRegister_def AARCH64.register.distinct(1)
    AARCH64_A.badge_register_def AARCH64_A.msg_info_register_def)

lemma do_normal_transfer_get_message_info:
  "\<lbrace>(\<lambda>s. P (get_message_info_ret s sender))
    and K (sender \<noteq> receiver \<and> \<not> grant)\<rbrace>
    do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda> _ s'. P (get_message_info_ret s' sender)\<rbrace>"
  apply(wpsimp wp: do_normal_transfer_valid[THEN hoare_strengthen_post])
   apply force
  apply force
  done

(* only bring these in when strictly needed *)
declare if_split [split del]
declare imp_disjL [simp del]

definition do_ipc_transfer_mi :: "('a::state_ext) state \<Rightarrow> message_info \<Rightarrow> obj_ref
   \<Rightarrow> obj_ref \<Rightarrow> message_info"
where
  "do_ipc_transfer_mi s mi sender receiver \<equiv>
      (let rbuf = lookup_ipc_buffer_ret s True receiver;
           sbuf = lookup_ipc_buffer_ret s False sender in
       do_normal_transfer_mi mi sbuf rbuf) "

lemma do_ipc_transfer_valid:
  "\<lbrace>(\<lambda>s. P' (lookup_ipc_buffer_ret s False sender) \<and>
      P'' (lookup_ipc_buffer_ret s True receiver) \<and>
      P (get_message_info_ret s sender) \<and>
      pred_tcb_at itcb_fault ((=) None) sender s \<and> tcb_at receiver s) and
    K (sender \<noteq> receiver \<and> \<not> grant)\<rbrace>
     do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda> _ s. P' (lookup_ipc_buffer_ret s False sender) \<and>
      P'' (lookup_ipc_buffer_ret s True receiver) \<and>
      tcb_at sender s \<and> tcb_at receiver s \<and>
      P (get_message_info_ret s sender) \<and>
      getRegister_as_user_ret s receiver badge_register = Some badge \<and>
      get_message_info_ret s receiver =
        Some (do_ipc_transfer_mi s (the (get_message_info_ret s sender)) sender receiver) \<and>
      valid_message_info (the (get_message_info_ret s sender))\<rbrace>"
  unfolding do_ipc_transfer_def
  apply wpsimp
       apply(clarsimp simp:do_ipc_transfer_mi_def)
       apply(rule hoare_vcg_conj_lift)
        apply(wpsimp wp:do_normal_transfer_lookup_ipc_buffer_ret)
       apply(rule hoare_vcg_conj_lift)
        apply(wpsimp wp:do_normal_transfer_lookup_ipc_buffer_ret)
       apply(rule hoare_vcg_conj_lift)
        apply(wpsimp wp:do_normal_tcb)
       apply(rule hoare_vcg_conj_lift)
        apply(wpsimp wp:do_normal_tcb)
       apply(wpsimp wp:insert do_normal_transfer_valid[THEN hoare_strengthen_post])
       apply(rule conjI)
        apply assumption
       apply(subgoal_tac "send_buffer = lookup_ipc_buffer_ret s False sender")
        apply(subgoal_tac "recv_buffer = lookup_ipc_buffer_ret s True receiver")
         apply simp
        apply assumption
       apply assumption
      apply(wpsimp wp:lookup_ipc_buffer_ret_valid)
     apply(rule_tac P="fault = None" in hoare_gen_asm)
     apply wpsimp
    apply(wpsimp wp:thread_get_wp)
   apply(wpsimp wp:lookup_ipc_buffer_inv hoare_vcg_ex_lift hoare_vcg_conj_lift hoare_vcg_imp_lift
     simp:obj_at_def)
     apply(wpsimp wp:lookup_ipc_buffer_ret_valid[THEN hoare_strengthen_post])
    apply(rule hoare_vcg_conj_lift)
     apply(wpsimp wp:lookup_ipc_buffer_inv)
    apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant" in hoare_gen_asm)
    apply(wpsimp wp:lookup_ipc_buffer_ret_valid[THEN hoare_strengthen_post])
   apply(wpsimp wp:lookup_ipc_buffer_inv)
  by (clarsimp simp:pred_tcb_at_def obj_at_def is_tcb_def)

lemma asUser_setRegister_obj_at:
  "\<lbrace>\<lambda>s. if t = ref then (let y = the (get_tcb ref s) in
          \<exists>b. ((), b) \<in> fst (setRegister r v (arch_tcb_context_get (tcb_arch y))) \<and>
          P (TCB (y\<lparr>tcb_arch := arch_tcb_context_set b (tcb_arch y)\<rparr>)))
      else obj_at P ref s\<rbrace>
     as_user t (setRegister r v)
   \<lbrace>\<lambda>rv s. obj_at P ref s\<rbrace>"
  apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
  apply(clarsimp simp:get_tcb_def obj_at_def split:if_splits split:kernel_object.splits)
  by (clarsimp simp: AARCH64.setRegister_def modify_def bind_def get_def put_def split:AARCH64.user_context.splits)

lemma asUser_setRegister_not_obj_at:
  "\<lbrace>\<lambda>s. if t = ref then (let y = the (get_tcb ref s) in
          \<exists>b. ((), b) \<in> fst (setRegister r v (arch_tcb_context_get (tcb_arch y))) \<and>
          \<not> P (TCB (y\<lparr>tcb_arch := arch_tcb_context_set b (tcb_arch y)\<rparr>)))
      else \<not> obj_at P ref s\<rbrace>
     as_user t (setRegister r v)
   \<lbrace>\<lambda>rv s. \<not> obj_at P ref s\<rbrace>"
  apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
  apply(clarsimp simp:get_tcb_def obj_at_def split:if_splits split:kernel_object.splits)
  by (clarsimp simp: AARCH64.setRegister_def modify_def bind_def get_def put_def split:AARCH64.user_context.splits)

lemma complete_signal_ct:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>
     complete_signal ntfnptr tcb
   \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  unfolding complete_signal_def
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def get_object_def)
    apply(wpsimp wp:crunch_wps Arch.as_user_cur_thread)
   apply(wpsimp wp:crunch_wps)
  apply simp
  done

lemma getRegister_as_user_ret_notif_simp:
  "\<not> tcb_at ntfnptr s \<Longrightarrow>
   getRegister_as_user_ret (s\<lparr>kheap :=
      \<lambda>a. if a = ntfnptr
          then Some (Notification (ntfn_set_obj ntfn IdleNtfn))
          else kheap s a\<rparr>) =
   getRegister_as_user_ret s"
  unfolding getRegister_as_user_ret_def tcb_at_def get_tcb_def
  apply(rule ext)
  apply(rule ext)
  by (clarsimp split:option.splits if_splits kernel_object.splits AARCH64.user_context.splits)

thm handle_recv_def
thm receive_ipc_def
thm complete_signal_def

lemma complete_signal_wp_1st_try:
  "\<lbrace>(\<lambda>s. P (getRegister_as_user_ret s t) \<and>
      obj_at (\<lambda>ko. \<exists> badge notification. ko = Notification notification \<and>
      ntfn_obj notification = (ActiveNtfn badge) \<and>
      getRegister_as_user_ret s tcb badge_register = Some badge) ntfnptr s) and
    K (ntfnptr \<noteq> tcb \<and> ntfnptr \<noteq> t)\<rbrace>
     complete_signal ntfnptr tcb \<lbrace>\<lambda>_ s. P (getRegister_as_user_ret s t)\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(rule_tac P=P in subst)
   prefer 2
   apply assumption
  apply(rule ext)
  apply(clarsimp split:option.splits if_splits kernel_object.splits AARCH64.user_context.splits
    simp:getRegister_as_user_ret_def get_tcb_def AARCH64_A.arch_tcb_context_get_def
      AARCH64_A.arch_tcb_context_set_def AARCH64.setRegister_def
      modify_def bind_def get_def put_def)
  by (metis AARCH64.user_context.sel(2) fun_upd_idem)

(* TODO: Some other part of the notification handling code must be responsible for copying the
   message info. Is `get_message_info_ret s receiver = get_message_info_ret s sender` the
   result? Or something more subtle because it might've been done when the sender signalled
   asynchronously, thus it may be no longer in the sender's buffer? *)
find_theorems ntfn_obj complete_signal
lemma complete_signal_wp:
  "\<lbrace>(\<lambda>s. ntfn_at ntfnptr s \<and>
     (\<forall>ntfn. obj_at ((=) (Notification ntfn)) ntfnptr s \<longrightarrow> ntfn_obj ntfn = ActiveNtfn badge))
     \<comment> \<open>obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_obj ntfn = (ActiveNtfn badge)) ntfnptr s)\<close>
   \<rbrace>
     complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. getRegister_as_user_ret s receiver badge_register = Some badge\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp split:option.splits if_splits kernel_object.splits AARCH64.user_context.splits
    simp:getRegister_as_user_ret_def get_tcb_def AARCH64_A.arch_tcb_context_get_def
      AARCH64_A.arch_tcb_context_set_def AARCH64.setRegister_def AARCH64.user_context.inject
      modify_def bind_def get_def put_def)
  done

lemma complete_signal_lookup_ipc_buffer:
  "\<lbrace>(\<lambda>s. P (lookup_ipc_buffer_ret s b t)) and K (ntfnptr \<noteq> t)\<rbrace>
     complete_signal ntfnptr tcb
    \<lbrace>\<lambda>_ s. P (lookup_ipc_buffer_ret s b t)\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(rule_tac P=P in subst)
   prefer 2
   apply assumption
  apply(clarsimp split:option.splits if_splits kernel_object.splits
    simp:lookup_ipc_buffer_ret_def get_tcb_def)
   apply(clarsimp simp:get_cap_ret_def tcb_cnode_map_def vm_read_write_def vm_read_only_def)
  apply(clarsimp simp:get_cap_ret_def tcb_cnode_map_def vm_read_write_def vm_read_only_def)
  by (clarsimp split:cap.splits AARCH64_A.arch_cap.splits bool.splits simp:AARCH64_A.arch_cap.simps)

lemma complete_signal_tcb_at:
  "\<lbrace>(\<lambda>s. P (tcb_at p s)) and K (ntfnptr \<noteq> tcb)\<rbrace>
     complete_signal ntfnptr tcb
   \<lbrace>\<lambda>_ s. P (tcb_at p s)\<rbrace>"
  unfolding complete_signal_def
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp wp:set_object_wp simp:set_simple_ko_def get_object_def)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def is_tcb_def)
  apply(rule_tac P=P in subst)
   prefer 2
   apply assumption
  apply(clarsimp split:option.splits if_splits kernel_object.splits
    simp:lookup_ipc_buffer_ret_def get_tcb_def)
  done

(* FIXME: not sure yet how much this would help even in true. I suspect actually that I shouldn't
   need this, as we should only be calling complete_signal on getting a notification, not a ppcall
lemma complete_signal_preserves_received_mi:
  "\<lbrace>(\<lambda>s. get_message_info_ret s receiver = Some
        (do_ipc_transfer_mi s (the (get_message_info_ret s sender)) sender receiver))\<rbrace>
     complete_signal ntfnptr tcb
    \<lbrace>\<lambda>_ s. get_message_info_ret s receiver = Some
        (do_ipc_transfer_mi s (the (get_message_info_ret s sender)) sender receiver)\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp split:option.splits if_splits kernel_object.splits
    simp:get_message_info_ret_def lookup_ipc_buffer_ret_def get_tcb_def)
  oops
*)

thm cap_delete_one_ep_at
(* too strong - surely cap_delete_one_ep_at is enough? *)
lemma delete_caller_cap_obj_at:
  "\<lbrace>(\<lambda>s. obj_at P ntfnptr s)
    and K (ntfnptr \<noteq> receiver)\<rbrace>
     delete_caller_cap receiver
   \<lbrace>\<lambda>_ s. obj_at P ntfnptr s\<rbrace>"
  apply(rule_tac P="ntfnptr \<noteq> receiver" in hoare_gen_asm)
  apply(wpsimp simp:delete_caller_cap_def)
  thm cap_delete_one_typ_at (* not strong enough *)
  thm cap_delete_one_ntfn_at[where word=ntfnptr] (* also not strong enough *)
  thm cap_delete_one_cte_wp_at_preserved (* not sure this really helps *)
  oops

(* again might be unnecessarily strong even if we went through the trouble of proving it
thm cap_delete_one_ep_at
crunch delete_caller_cap
  for ep_at'[wp]: "\<lambda>s. obj_at P ptr s"
  (wp: crunch_wps)
*)

thm cap_delete_one_ntfn_at
(* going back to supposing we have this for specific notifications
   to see how it impacts later goals *)
(* XXX: actually, we need the converse version after all
lemma delete_caller_cap_specific_ntfn_at:
  "\<lbrace>\<lambda>s. ko_at (Notification ntfn) word s\<rbrace>
     delete_caller_cap t
   \<lbrace>\<lambda>_ s. ko_at (Notification ntfn) word s\<rbrace>"
  sorry (* FIXME: prove *)
*)

lemma delete_caller_cap_not_bound_tcb_at:
  "delete_caller_cap receiver \<lbrace>\<lambda>s. \<not> bound_tcb_at ((=) ntfn) receiver s\<rbrace>"
  (* that the cap deletion isn't suddenly going to bind a tcb where there wasn't one.
     seems like this ought to be true? *)
  sorry (* FIXME: prove *)

(* FIXME: Is the specificity needed? *)
lemma delete_caller_cap_specific_ntfn_not_at:
  "\<lbrace>\<lambda>s. \<not> ko_at (Notification ntfn) word s\<rbrace>
     delete_caller_cap t
   \<lbrace>\<lambda>_ s. \<not> ko_at (Notification ntfn) word s\<rbrace>"
  (* cap deletion isn't suddenly going to create a notification where there wasn't one *)
  sorry (* FIXME: prove *)

(*
lemma
  "\<lbrace>(\<lambda>s. ko_at (Endpoint ep) ep_ptr s) and K (ep_ptr \<noteq> p)\<rbrace>
     delete_caller_cap p
   \<lbrace>\<lambda>_ s. ko_at (Endpoint ep) ep_ptr s\<rbrace>"
  apply(rule_tac P="ep_ptr \<noteq> p" in hoare_gen_asm)
  apply(wpsimp wp:crunch_wps set_object_wp get_object_wp fast_finalise_lift
    simp:crunch_simps
    delete_caller_cap_def cap_delete_one_def empty_slot_def post_cap_deletion_def set_cap_def
    obj_at_def set_cdt_def cancel_all_ipc_def set_thread_state_def)
             apply (smt (verit, del_insts) get_tcb_SomeD kernel_object.simps(15) kernel_object.simps(9) option.simps(1))
            apply(rule_tac P="ep_ptr \<noteq> p" in hoare_gen_asm)
            apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
           apply(wpsimp wp:get_ep_queue_inv)
          apply(rule_tac P="ep_ptr \<noteq> p" in hoare_gen_asm)
          apply(wpsimp wp:get_ep_queue_inv)
            apply(wpsimp wp:mapM_x_wp')
            apply(wpsimp simp:set_thread_state_def wp:set_object_wp)
            apply (smt (verit, del_insts) get_tcb_SomeD kernel_object.simps(15) kernel_object.simps(9) option.simps(1))
           apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
          apply(wpsimp wp:get_ep_queue_inv)
         apply(rule_tac P="ep_ptr \<noteq> p" in hoare_gen_asm)
         apply(wpsimp wp:get_simple_ko_wp)
        apply clarsimp
        apply(rule conjI)
         apply(clarsimp split:if_splits simp:obj_at_def)
         apply(rule conjI)
          apply clarsimp
         apply clarsimp
*)


(* FIXME: somehow need to jump through some hoops to get these from Syscall_AI - do it later *)
thm Syscall_AI.do_ipc_transfer_cur_thread
lemma do_ipc_transfer_cur_thread':
  "\<lbrace>\<lambda> s. P (cur_thread s)\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  unfolding do_ipc_transfer_def
  sorry
(* might need to use this if I start talking about cur_thread again
thm Syscall_AI.cap_delete_one_cur_thread
lemma cap_delete_one_cur_thread':
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> cap_delete_one a \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  sorry
*)

(* The original rule I think says that for all predicates P that are independent of the rights of
   a cap, if P holds of the return value rv then it holds for all caps found at pointers to
   irq notification objects looked up by cte_refs. So perhaps this adaptation is not that helpful.
*)
thm lookup_cap_cte_caps_to
lemma lookup_cap_cte_caps_to':
  "\<lbrace>\<lambda>s. P' s \<and> (\<forall>rs cp. P (mask_cap rs cp) = P cp)\<rbrace>
     lookup_cap t cref
   \<lbrace>\<lambda>rv s. P' s \<and> (P rv \<longrightarrow> (\<forall>p\<in>cte_refs rv (interrupt_irq_node s). ex_cte_cap_wp_to P p s))\<rbrace>,-"
  by (simp add: lookup_cap_def split_def) wpsimp

lemma lookup_cap_cte_caps_to'':
  "\<lbrace>\<lambda>s. \<forall>rs cp. P (mask_cap rs cp) = P cp\<rbrace>
     lookup_cap t cref
   \<lbrace>\<lambda>rv s. P rv \<longrightarrow> (\<forall>p\<in>cte_refs rv (interrupt_irq_node s). ex_cte_cap_wp_to P p s)\<rbrace>,\<lbrace>\<lambda>rv s. False\<rbrace>"
  oops
  (* by (simp add: lookup_cap_def split_def) wpsimp *)

(* NB: tcb = (the (get_tcb t s)) *)
thm resolve_address_bits_cte_at
thm resolve_address_bits_real_cte_at
lemma resolve_address_bits_specific:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
     valid_cap mycap s \<and>
     valid_cap (fst args) s \<and>
     is_CNodeCap (fst args) \<and>
     \<comment> \<open> FIXME: Have to work out how args and mycref relate. \<close>
     \<comment> \<open> XXX: I think I'm starting to say the right things, but in the wrong place.
          This is saying an awful lot about what's effectively the return value of
          the function - maybe it'd make more sense as some kind of _ret predicate
          in terms of the return value, for which I can prove a _ret wp lemma? \<close>
     (\<exists> obj_ref nat list. fst args = CNodeCap obj_ref nat list \<and>
       (let offset = take nat (drop (length list) (snd args));
            rest = drop (nat + length list) (snd args)
        in (if rest = [] then (obj_ref, offset) = mycref else
               \<forall> r bits g.
               (if {(CNodeCap r bits g, s)} = fst (get_cap (obj_ref, offset) s)
                 then \<exists> rest' s'. {(Inr (mycref, rest'), s')} =
                   fst (resolve_address_bits' z (CNodeCap r bits g, rest) s)
                 else (obj_ref, offset) = mycref)))) \<and>
     \<comment> \<open>snd mycref = snd args \<and>  -- bit dubious in hindsight\<close>
     cte_wp_at ((=) mycap) mycref s \<rbrace> resolve_address_bits' z args
   \<lbrace>\<lambda>rv s. cte_wp_at ((=) mycap) mycref s \<and> (fst rv) = mycref\<rbrace>,
   \<lbrace>\<lambda>rv s. False\<rbrace>"
unfolding resolve_address_bits_def
thm resolve_address_bits_real_cte_at
(* basing the proof structure on that of resolve_address_bits_real_cte_at *)
proof (induct args rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]
    apply (simp only: cap.simps)
    (* I think the first conjunct is asking us to show that rab *doesn't* fail *)
    apply(rule conjI)
     (* FIXME: come back to this *)
     defer
    apply(rename_tac obj_ref nat list)
    apply (case_tac "nat + length list = 0")
     apply (simp add: fail_def)
    apply (simp only: if_False)
    apply clarify
    apply (simp only: K_bind_def in_bindE_R)
    apply (elim conjE exE)
    apply (simp only: split: if_split_asm)
     (* case: rest = [], so returnOk ((obj_ref, offset), []) happens *)
     apply (clarsimp simp add: in_monad Let_def)
    (* case: rest \<noteq> [] *)
    apply (simp only: K_bind_def in_bindE_R)
    apply (elim conjE exE)
    apply (simp only: split: if_split_asm)
     (* case: is_cnode_cap next_cap *)
     apply (frule "1.hyps", simp_all)
     apply clarsimp
     apply (clarsimp simp: in_monad validE_def validE_R_def valid_def)
     apply (frule in_inv_by_hoareD [OF get_cap_inv])
     apply simp
     apply (frule (1) post_by_hoare [OF get_cap_valid])
     (*
     apply (erule allE, erule impE, blast)
     apply (clarsimp simp: in_monad split: cap.splits)
     *)
     apply(erule allE)
     apply(erule impE)
      apply(rule context_conjI)
       apply blast
      apply(rule context_conjI)
       apply blast
      apply(rule context_conjI)
       apply blast
      apply(rule context_conjI)
       apply(clarsimp simp:is_cap_simps)
      apply(clarsimp simp:Let_def)
      apply(clarsimp simp:is_cap_simps)
(*
      apply(erule disjE) back
       apply(subgoal_tac "ra=r \<and> bitsa=bits \<and> ga=g")
        prefer 2
        apply blast
       apply clarsimp
       (* Similarly I would've thought this would be true as well, but no?
       apply(subgoal_tac "(aa,ba)=mycref \<and> bb=rest' \<and> b=s'")
        prefer 2
        apply clarsimp
       *)
*)
(* do this as late as possible
         apply(erule_tac x=r in allE)
         apply(erule_tac x=bits in allE)
         apply(erule_tac x=g in allE)
*)
.      (* DOWN TO HERE
      apply(clarsimp split:if_split)
       apply(rule conjI)
        apply clarsimp
        apply(erule disjE)
         apply clarsimp
         apply(erule disjE)
          apply(reul
          apply clarsimp
          defer (* FIXME *)
         apply clarsimp
         apply(rule conjI)
          apply clarsimp
          defer (* FIXME *)
         apply clarsimp
         defer (* FIXME *)
        apply clarsimp

. (*
           apply(clarsimp simp:cte_wp_at_def)
         defer
         apply clarsimp
         

. (*
       apply(force simp add: is_CNodeCap_def is_cap_simps)

      apply blast
     apply clarsimp
     apply (drule (1) bspec, simp)+
    apply (clarsimp simp: in_monad)
    apply (frule in_inv_by_hoareD [OF get_cap_inv])
    apply clarsimp
    defer (* FIXME: study and rework preconditions to prove this *)
   (* FIXME: back to the deferred goals *)
   sorry
qed

lemma lookup_slot_specific:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
     valid_cap mycap s \<and>
     is_CNodeCap (tcb_ctable (the (get_tcb t s))) \<and>
     valid_cap (tcb_ctable (the (get_tcb t s))) s \<and>
     cte_wp_at ((=) mycap) cref s \<rbrace> lookup_slot_for_thread t c
   \<lbrace>\<lambda>rv s. cte_wp_at ((=) mycap) cref s \<and> fst rv = cref\<rbrace>,
   \<lbrace>\<lambda>rv s. False\<rbrace>"
  (* suppose we can prove this doesn't fail *)
  apply(clarsimp simp:lookup_slot_for_thread_def)
  apply(wp only:resolve_address_bits_specific[where mycap=mycap,THEN hoare_strengthen_postE])
   apply wpsimp
  apply wpsimp
  done

term valid_cap
thm lookup_cap_gets
lemma lookup_cap_specific:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
    cte_wp_at ((=) mycap) cref s \<and>
    is_CNodeCap (tcb_ctable (the (get_tcb t s))) \<and>
    valid_cap (tcb_ctable (the (get_tcb t s))) s \<and>
    wellformed_cap mycap \<and> valid_cap mycap s\<rbrace>
     lookup_cap t c
   \<comment> \<open>\<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>cap. rv = cap \<and> cap = mycap) cref s\<rbrace>,\<close>
   \<lbrace>\<lambda>rv s. cte_wp_at ((=) mycap and (=) rv) cref s\<rbrace>,
   \<lbrace>\<lambda>rv s. False\<rbrace>"
   (* \<lbrace>\<lambda>rv s. \<exists>cref. cte_wp_at (\<lambda>cap. rv = cap \<and> rv = ep_cap) cref s\<rbrace>, - *)
   (* \<lbrace>\<lambda>rv s. \<exists>msk. cte_wp_at (\<lambda>cap. rv = mask_cap msk ep_cap) cref s\<rbrace>, - *)
  unfolding lookup_cap_def fun_app_def split_def
  apply(rule hoare_pre)
   apply wpsimp
    apply(rule_tac P="cref = (a, b)" in hoare_gen_asm)
    apply(wpsimp wp:get_cap_cte_wp_at_rv[THEN hoare_strengthen_post])
    apply assumption
   (*
   apply(wpsimp wp:lookup_slot_cte_at_wp[THEN hoare_strengthen_postE_R])
   *)
   (* FIXME: sorried lemma *)
   apply(wpsimp wp:lookup_slot_specific[where mycap=mycap and cref=cref,THEN hoare_strengthen_postE])
(*
    using cte_wp_at_lift apply fastforce
   apply clarsimp
*)
  apply clarsimp
  done
(*
   apply(rule conjI)
    apply assumption
. (*
   find_theorems lookup_slot_for_thread
   apply(wpsimp wp:lookup_slot_for_thread_inv[THEN valid_validE_R,THEN hoare_strengthen_postE_R])


(*
     apply(clarsimp simp:cte_wp_at_def)

     apply assumption
find_theorems get_cap
   apply wpsimp
   apply(wpsimp wp:hoare_vcg_all_liftE_R)
   (*
   apply(rule_tac P="wellformed_cap mycap \<and> (\<exists>msk. cap = mask_cap msk mycap)" in hoare_gen_asmE)
   *)
   apply clarsimp
   (*
   apply(wpsimp wp:lookup_slot_cte_at_wp[THEN hoare_strengthen_postE_R])
*)
   
   apply clarsimp
*)
   apply wpsimp
   apply(wpsimp wp:lookup_slot_for_thread_inv[THEN valid_validE_R,THEN hoare_strengthen_postE_R])
   
   apply(rule_tac x="a" in exI)
   apply(rule_tac x="b" in exI)
   apply(clarsimp simp:cte_wp_at_def)
   defer
  apply clarsimp
  apply(rule context_conjI)
   prefer 2
   apply(
  apply(clarsimp simp:cte_wp_at_def)
  apply(rule_tac x=msk in exI)
   (* left conjunct is fine if x is wellformed *)
   thm cap_mask_UNIV
   defer
  (* but we still don't have any way to know x = mycap *)
  sorry
*) *)

thm lookup_cap_inv
lemma lookup_cap_invE:
  "\<lbrace>P\<rbrace> lookup_cap t c \<lbrace>\<lambda>_. P\<rbrace>,\<lbrace>\<lambda>_ _. False\<rbrace>"
  sorry (* FIXME: suppose we had this too... *)

lemma hoare_absorb_impE_R:
  "\<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,- \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s\<rbrace>,-"
  using hoare_strengthen_postE_R by fastforce

definition
  "good_preconds s ro sender receiver \<equiv>
     \<comment> \<open> FIXME: Some of these might be redundant with what's in valid_ep_obj_with_message
     (\<exists> ntfnptr ntfn. cur_thread_bound_notification (mspec_transform s) = Some ntfnptr \<and>
       kheap s ntfnptr = Some (Notification ntfn) \<and>
       ntfn_obj ntfn = ActiveNtfn (badge_val ro)) \<and>
     \<close>
     receiver = cur_thread s \<and>
     valid_ep_obj_with_ntfn sender (mspec_transform s) s MICROKIT_INPUT_CAP ro"

find_theorems "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_ _. \<not> _\<rbrace>"

(* Actually, I think we want to be saying that we do not fault.
lemma handle_fault_good_preconds:
  "handle_fault thread ex \<lbrace>\<lambda>s. good_preconds s ro receiver\<rbrace> "
  sorry

lemma handle_fault_not_good_preconds:
  "handle_fault thread ex \<lbrace>\<lambda>s. \<not> good_preconds s ro receiver\<rbrace> "
  sorry
*)

thm hoare_vcg_split_lift
thm hoare_vcg_split_case_optionE
lemma hoare_vcg_split_ep_capE[wp]:
  "\<lbrakk>\<And>x ref badge rights. x = EndpointCap ref badge rights \<Longrightarrow>
      \<lbrace>P x ref badge rights\<rbrace> f x ref badge rights \<lbrace>Q x\<rbrace>, \<lbrace>E x\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. (\<exists>ref badge rights. x = EndpointCap ref badge rights \<and> P x ref badge rights s)\<rbrace>
    case x of
      EndpointCap ref badge rights \<Rightarrow> f x ref badge rights |
      NotificationCap ref badge rights \<Rightarrow> g x ref badge rights |
      _ \<Rightarrow> h
    \<lbrace>Q x\<rbrace>, \<lbrace>E x\<rbrace>"
  by (clarsimp split:cap.splits)

lemma hoare_gen_asmE':
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validE_R_def validE_def valid_def) blast

lemma ko_at_ep_at:
  "(\<exists>ep. ko_at (Endpoint ep) ref s) = ep_at ref s"
  apply(clarsimp simp add:obj_at_def is_ep_def split:kernel_object.splits)
  by (metis kernel_object.distinct(17) kernel_object.distinct(9) kernel_object.exhaust kernel_object.simps(21) kernel_object.simps(9))

lemma ko_at_ntfn_at:
  "(\<exists>ntfn. ko_at (Notification ntfn) ref s) = ntfn_at ref s"
  apply(clarsimp simp add:obj_at_def is_ntfn_def split:kernel_object.splits)
  by (metis kernel_object.distinct(15) kernel_object.distinct(6) kernel_object.exhaust kernel_object.simps(16) kernel_object.simps(25))

lemma ko_at_ntfn_at':
  "(ko_at (Notification ntfn) ref s) \<Longrightarrow> ntfn_at ref s"
  apply(clarsimp simp add:obj_at_def is_ntfn_def split:kernel_object.splits)
  done

thm handle_recv_def
thm cap_fault_on_failure_def
term "(\<Union>a\<in>fst (get_object x1 s). something)"
term "\<Union>"
lemma handle_SysRecv_syscall_notification:
  "\<lbrace>\<lambda>s. \<comment> \<open>MCS only - no reply cap argument or related pre/postconditions on non-MCS kernel
      valid_reply_obj (mspec_transform s) s MICROKIT_REPLY_CAP \<and>\<close>
      \<comment> \<open>
      P (cur_thread s) \<and>
      P'' (lookup_ipc_buffer_ret s False sender) \<and>
      P''' (lookup_ipc_buffer_ret s True receiver) \<and>
      P' (get_message_info_ret s sender) \<and>
      \<close>
      \<comment> \<open> having woes with types - bring this back in later
      valid_ep_obj_with_message sender (mspec_transform s) s MICROKIT_INPUT_CAP ro \<and> \<close>
      tcb_at sender s \<and> tcb_at receiver s \<and>
      valid_objs s \<and>
      good_preconds s ro sender receiver \<and>
      \<comment> \<open>That the user has provided MICROKIT_INPUT_CAP_NAT in the cap_register\<close>
      to_bl (the (getRegister_as_user_ret s receiver cap_register)) = MICROKIT_INPUT_CAP
      \<comment> \<open>NB: Not yet sure if this is a safe assumption to make, or even needed
      ntfn_at (the (cur_thread_bound_notification (mspec_transform s))) s\<close>\<rbrace>
    handle_recv True
   \<lbrace>\<lambda> _ s.
      \<comment> \<open>
      P (cur_thread s) \<and>
      P'' (lookup_ipc_buffer_ret s False sender) \<and>
      P''' (lookup_ipc_buffer_ret s True receiver) \<and>
      P' (get_message_info_ret s sender) \<and>
      \<close>
      \<comment> \<open>notification reqs on successful complete_signal\<close>
      \<comment> \<open>good_preconds s ro receiver \<and>\<close>
      getRegister_as_user_ret s receiver badge_register = Some (badge_val ro)
      \<comment> \<open>FIXME: figure out the mechanism for transferring message info and how we ought
        to express its correctness
      get_message_info_ret s receiver = Some (minfo ro) \<and> \<close>
      \<comment> \<open>Do we really need these?
      tcb_at sender s \<and> tcb_at receiver s\<close>
      \<comment> \<open>NB: put back if needed
      valid_message_info (the (get_message_info_ret s sender)) \<and>
      ntfn_at (the (cur_thread_bound_notification (mspec_transform s))) s\<close>\<rbrace>"
  unfolding handle_recv_def
  apply wp
      apply(wp only:hoare_pre_cont)
     apply simp
     apply(wp only:cap_fault_wp)
     (* XXX: if we call wpsimp we're dead because False ends up in the postcondition
        of the lookup_cap lemma, so instead carefully split on the cases *)
     apply(simp add:Let_def)
     apply(wp only:hoare_vcg_split_ep_capE)
       (* FIXME: indentation's off by one from here *)
       apply(wpsimp simp:receive_ipc_def)
           apply(rename_tac tcb ep_cptr ep_cap ref badge rights ep rva ntfnptr)
           apply(rule_tac P="ntfnptr \<noteq> receiver \<and> tcb = receiver" (*  \<and> badge = badge_val ro *)
             in hoare_gen_asm)
            apply simp
            apply(wpsimp wp:complete_signal_wp)
           (* FIXME: figure out how to express correctness for transfer of message info
           apply(wpsimp wp:hoare_vcg_conj_lift)
            apply(wpsimp wp:complete_signal_wp_1st_try[THEN hoare_strengthen_post] hoare_vcg_ex_lift
              simp:AARCH64_A.get_message_info_ret_getRegister_as_user_ret)
            apply assumption
           apply(wpsimp wp:complete_signal_tcb_at complete_signal_ct) *)
          apply clarsimp
          apply(rename_tac tcb x xa ep_ptr badge rights rv ntfnptr ntfn)
          (* apply(rule_tac P="\<not> (ntfnptr = None \<or> \<not> isActive ntfn)" in hoare_gen_asm)
          (* ^ actually this was just a way of saying this can only arise from a contradiction *) *)
          apply(wp only:hoare_pre_cont)
         apply clarsimp
         apply(rename_tac x xa ep_ptr badge rights rv ntfnptr)
         apply(rule_tac P="\<not> (ntfnptr = None)" in hoare_gen_asm)
         apply wpsimp
         apply(wpsimp wp:get_simple_ko_wp)
        apply clarsimp
        apply wpsimp
        apply(wpsimp wp:gbn_wp)
       apply(wp only:get_simple_ko_wp)
      (* This delete_caller_cap immediately precedes the call to receive_ipc in handle_recv.
         I think what I'll need is a bunch of lemmas to show that most of the predicates in
         the postcondition are unaffected by delete_caller_cap. *)
      (* That deleting the caller cap doesn't impact this Endpoint object *)
      apply(wpsimp wp:hoare_vcg_conj_lift)
      (* Note: converted to ep_at by ko_at_ep_at *)
      apply(wpsimp wp:hoare_absorb_imp simp:ko_at_ep_at) (* NB: absorb_imp maybe problematic? *)
      apply(wpsimp wp:hoare_vcg_conj_lift)
       (* Note: in ep_at form, cap_delete_one_ep_at is enough to discharge it *)
       apply(wpsimp simp:delete_caller_cap_def)
      apply(rename_tac thread ep_cptr ep_cap ref badge rights)
      apply(rule_tac P="thread = receiver \<and> receiver \<noteq> ref" in hoare_gen_asm)
      apply wpsimp
      apply(wpsimp wp:hoare_vcg_all_lift)
      thm hoare_absorb_imp
      (*apply(wpsimp wp:hoare_absorb_imp) (* NB: this becomes a problem later *) *)
      apply(wpsimp wp:hoare_vcg_imp_lift)
       (* FIXME: sorried lemma *)
       apply(wp only:delete_caller_cap_not_bound_tcb_at)
      apply wpsimp
      apply(wpsimp wp:hoare_vcg_all_lift)
       (* apply(wpsimp wp:hoare_absorb_imp) (* NB: this becomes a problem later *) *)
       apply(wpsimp wp:hoare_vcg_imp_lift)
       (* That deleting the caller cap doesn't impact this Notification object *)
       (* Note: This is tricker than the Endpoint object case because this demands to know other
          facts about the Notification, not just that there is one at that address *)
       apply(wpsimp wp:hoare_vcg_all_lift)
       apply(rename_tac ep_cptr ep_cap ep_ref badge rights ep ntfn_ref ntfn)
       (* then drop the imp because there's no hope of proving it for a fixed ntfn
       apply(wpsimp wp:hoare_drop_imp) (* NB: this creates problems later. *) *)
       (* apply(wpsimp wp:hoare_absorb_imp) (* NB: so does this, apparently. *) *)
       (* suppose for now we have a specific ntfn-preserving delete_caller_cap lemma
       apply(wpsimp wp:delete_caller_cap_specific_ntfn_at) *)
       apply(wpsimp wp:hoare_vcg_imp_lift)
        (* actually, we need the converse *)
        (* FIXME: sorried lemma *)
        apply(wpsimp wp:delete_caller_cap_specific_ntfn_not_at)
       apply(wpsimp wp:hoare_vcg_conj_lift)
        apply(wpsimp wp:hoare_vcg_imp_lift)
        apply(wpsimp wp:hoare_vcg_conj_lift)
         (* find_theorems name:"context" name:conj *)
         (* Note: in ntfn_at form, cap_delete_one_ntfn_at is enough to discharge it *)
         apply(wpsimp simp:delete_caller_cap_def)
        apply(wpsimp wp:hoare_vcg_all_lift)
       (* apply(wp only:hoare_drop_imp) (* NB: this creates problems later:
          The goal then becomes state independent and looks solvable trivially,
          but this actually produces postcondition "(\<forall>x. ntfn_obj x = ActiveNtfn badge)"
          which is too general to prove later on. *) *)
       (* apply(wpsimp wp:hoare_absorb_imp) (* NB: also creates problems later *) *)
         apply(wpsimp wp:hoare_vcg_imp_lift)
          (* FIXME: sorried lemma *)
          apply(wpsimp wp:delete_caller_cap_specific_ntfn_not_at)
         apply wpsimp
        apply wpsimp
       apply wpsimp
      apply wpsimp
     (* might need to use this if I start talking about cur_thread again
     apply(wpsimp simp:delete_caller_cap_def wp:cap_delete_one_cur_thread')
     *)
     apply wpsimp
    (* XXX: again, if we call wpsimp here we're dead because False ends up in the postcondition
       NB: liftM_pre oddly has False as its postcondition but I couldn't see how it helps.
    apply wpsimp *)
    apply(rename_tac thread ref)
    apply(wp only:hoare_vcg_ex_liftE)
    apply(rename_tac thread ref ep_ptr badge rights)
    apply clarsimp

(* This is the relevant code:
     thread \<leftarrow> gets cur_thread;

     ep_cptr \<leftarrow> liftM data_to_cptr $ as_user thread $
                 getRegister cap_register;

     (cap_fault_on_failure (of_bl ep_cptr) True $ doE
        ep_cap \<leftarrow> lookup_cap thread ep_cptr;
*)

    (* take care of some state-independent assumptions *)
    (*
    apply(rule_tac P="AllowRecv \<in> rights \<and> thread = receiver \<and> receiver \<noteq> ep_ptr" in hoare_gen_asmE')
    apply clarsimp
    *)
    (* That lookup_cap succeeds for our EndpointCap *)
    (* FIXME: Add new preconditions here that ensure the lookup succeeds,
       and prove lemmas that say it succeeds under those preconditions. *)
    (* Use this conj_lift for validE:
    apply(wp only:hoare_vcg_conj_liftE_weaker) *)
    apply(wp only:hoare_vcg_conj_liftE_weaker)
     thm lookup_cap_specific
     (* FIXME: sorried lemma *)
     apply(rule_tac mycap1="EndpointCap ep_ptr badge rights" and cref1="(receiver,ref)" and c1=ref
       in lookup_cap_specific[THEN hoare_strengthen_postE])
      apply(clarsimp simp:cte_wp_at_def)
      defer (* it isn't enough, we do need the statement on the rv *)
     apply clarsimp
    (* if we have this, it covers the rest that don't refer to rv, all in one go *)
    (* FIXME: sorried lemma *)
    apply(wp only:lookup_cap_invE)
    (* step by step:
    apply(wp only:hoare_vcg_conj_liftE_weaker)
     (* overkill, should be able to use some variant of lookup_cap_inv
     apply(rule_tac mycap1="EndpointCap ep_ptr badge rights" and c1="ref"
       in lookup_cap_specific[THEN hoare_strengthen_postE])
      apply(clarsimp simp:cte_wp_at_def get_cap_def get_object_def bind_def gets_def return_def
        assert_def get_def obj_at_def assert_opt_def fail_def
        split:prod.splits if_splits kernel_object.splits option.splits)
     *)
     apply(wp only:lookup_cap_invE)
    apply(wp only:hoare_vcg_all_liftE)
    (* state-independent assumptions for this new forall-quantified x *)
    (* apply(rule_tac P="\<exists>y. x = Some y" in hoare_gen_asmE') XXX: creates problems later *)
    apply(wp only:hoare_vcg_conj_liftE_weaker)
     apply(wp only:lookup_cap_invE)
    apply(wp only:hoare_vcg_conj_liftE_weaker)
     apply(wp only:lookup_cap_invE)
    apply(wp only:hoare_vcg_conj_liftE_weaker)
     apply(wp only:lookup_cap_invE)
    apply(wp only:hoare_vcg_conj_liftE_weaker)
     apply(wp only:hoare_vcg_all_liftE)
     (* state-independent assumptions for this new forall-quantified x *)
     (* apply(rule_tac P="y = x" in hoare_gen_asmE') XXX: creates problems later *)
     apply(wp only:hoare_vcg_conj_liftE_weaker)
      apply(wp only:lookup_cap_invE)
     apply(wp only:hoare_vcg_all_liftE)
     apply(wp only:hoare_vcg_conj_liftE_weaker)
      apply(wp only:lookup_cap_invE)
     apply(wp only:hoare_vcg_conj_liftE_weaker)
      apply(wp only:lookup_cap_invE)
     apply(wp only:hoare_vcg_conj_liftE_weaker)
      apply(wp only:lookup_cap_invE)
     apply(wp only:hoare_vcg_conj_liftE_weaker)
      apply(wp only:lookup_cap_invE)
     apply(wp only:lookup_cap_invE)
    apply(wp only:lookup_cap_invE)
    *)
    term to_bl
    term data_to_cptr
    apply(clarsimp)
    apply wpsimp
    apply(clarsimp simp:comp_def)
    apply wpsimp
    apply(wpsimp wp:hoare_vcg_ex_lift)
    apply(wpsimp wp:hoare_vcg_conj_lift)
     apply(wpsimp wp:getRegister_as_user_ret_valid[THEN hoare_strengthen_post,simplified])
     apply(clarsimp simp:getRegister_as_user_ret_def)
     apply(case_tac "kheap s thread"; clarsimp)
     apply(rename_tac thread x xa xb rv s a)
     apply(case_tac a; clarsimp)
     apply(clarsimp simp:AARCH64_A.arch_tcb_context_get_def)
     apply(subgoal_tac "rv = AARCH64.user_regs (AARCH64_A.tcb_context (tcb_arch x2)) cap_register")
      apply clarsimp
      apply(subgoal_tac "x2 = un_TCB (the (kheap s thread))")
       apply(thin_tac "(case AARCH64_A.tcb_context (tcb_arch x2) of
         AARCH64.UserContext x u \<Rightarrow> Some (u cap_register)) =
        Some (AARCH64.user_regs (AARCH64_A.tcb_context (tcb_arch x2)) cap_register)")
       apply clarsimp
       apply assumption
      apply clarsimp
     apply clarsimp
     apply(clarsimp simp:AARCH64.user_context.sel split:AARCH64.user_context.splits)
    apply(wpsimp wp:getRegister_as_user_ret_valid[THEN hoare_strengthen_post])
   apply wpsimp
  (* okay. we're finally at the point where we can try to line up the wp-derived precondition
     with the mega-precondition I originally drafted. *)
  apply wpsimp
  apply(clarsimp simp:good_preconds_def valid_ep_obj_with_ntfn_def
    split:option.splits cap.splits)
  apply(rename_tac s ref ep_badge rights ep ntfnptr)
  apply(rule_tac x=ref in exI)
  apply(rule_tac x=ep_badge in exI)
  apply(rule_tac x=rights in exI)
  apply(rule context_conjI)
   apply(clarsimp simp:cte_wp_at_def)
   apply(simp only:get_cap_caps_of_state[simplified])
   apply(clarsimp simp:pred_tcb_at_def obj_at_def)
   apply(rename_tac s ref ep_badge rights ep ko tcb ntfn n)
   using caps_of_state_tcb_index_trans[where p=receiver]
   apply(erule_tac x=s in meta_allE)
   apply(erule_tac x=tcb in meta_allE)
   apply(erule_tac x=MICROKIT_INPUT_CAP_NAT in meta_allE)
   apply simp
   apply(subgoal_tac "to_bl (AARCH64.user_regs (AARCH64_A.tcb_context (tcb_arch tcb)) cap_register)
     = tcb_cnode_index MICROKIT_INPUT_CAP_NAT")
    apply clarsimp
    apply(simp add: MICROKIT_INPUT_CAP_def get_tcb_rev)
   (* We just need a requirement that says the microkit passed MICROKIT_INPUT_CAP in
      via the cap_register *)
   apply(clarsimp split:AARCH64.user_context.splits
     simp:getRegister_as_user_ret_def AARCH64_A.arch_tcb_context_get_def AARCH64.user_regs_def)
   apply(subgoal_tac "x2=x2a")
    prefer 2
    using AARCH64.user_context.inject apply blast
   apply(force simp:MICROKIT_INPUT_CAP_def tcb_cnode_index_def)
  apply(rule context_conjI)
   defer (* FIXME: prove *)
  apply(rule context_conjI)
   apply(force simp:get_tcb_at objs_valid_tcb_ctable)
  apply(rule context_conjI)
   apply(force simp:wellformed_cap_simps)
  apply(rule context_conjI)
   using cte_wp_valid_cap apply blast
  apply(clarsimp simp:AllowRecv_def)
  apply(rule context_conjI)
   apply(force simp add:valid_cap_simps)
  apply(rule context_conjI)
   apply clarsimp
   apply(rename_tac s ref ep_badge rights ep ntfnptr ntfnptr')
   apply(erule_tac x=ntfnptr' in allE)
   apply clarsimp
   apply(rule context_conjI)
    apply clarsimp
    apply(rule context_conjI)
     apply(clarsimp simp:obj_at_def is_ntfn_def)
    apply(rule context_conjI)
     apply(clarsimp simp:obj_at_def)
    apply(clarsimp simp:obj_at_def is_tcb_def)
   apply(clarsimp simp:obj_at_def isActive_def)
  apply(clarsimp simp:obj_at_def is_tcb_def)
  done

    (* Old attempts below. These use validE_R but we actually need validE
              where E=False to say basically that it *must* succeed.
      (* still nope.
      thm lookup_cap_cte_caps_to'
      apply(rule_tac P1="\<lambda>rv. rv = EndpointCap ep_ptr badge rights"
        in lookup_cap_cte_caps_to'[THEN hoare_strengthen_postE_R])
      apply clarsimp
      apply assumption *)
      (* also nope, because it still references the rv, which I can't do here.
      apply(wp only:lookup_cap_cte_caps_to'[where P="\<lambda>rv. \<exists> a b c. rv = EndpointCap a b c",THEN hoare_strengthen_postE_R])
      apply clarsimp
      apply(rotate_tac 2)
      apply(erule impE)
       apply assumption
      *)
      (* FIXME: is this the relationship between cref and ref? *)
      apply(rule_tac mycap1="EndpointCap ep_ptr badge rights" and cref1="(something, ref)"
        in lookup_cap_specific[THEN hoare_strengthen_postE_R])
      apply(clarsimp simp:cte_wp_at_def)
     (* these don't refer to rv, so the inv lemma should be fine *)
     apply(wp only:lookup_cap_inv[THEN valid_validE_R, THEN hoare_strengthen_postE_R])
    (* I'm evidently missing something in this lemma relating cref and ref - is it this? *)
    apply(rule_tac mycap1="EndpointCap a b c" and cref1="(something, ref)"
      in lookup_cap_specific[THEN hoare_strengthen_postE_R])
    apply(clarsimp simp:cte_wp_at_def)
    *)

(* This is the relevant code:
     thread \<leftarrow> gets cur_thread;

     ep_cptr \<leftarrow> liftM data_to_cptr $ as_user thread $
                 getRegister cap_register;

     (cap_fault_on_failure (of_bl ep_cptr) True $ doE
        ep_cap \<leftarrow> lookup_cap thread ep_cptr;
*)

(*
     (* Not strong enough.
     apply(wpsimp wp:lookup_cap_valid[THEN hoare_strengthen_postE_R])
     *)

      find_theorems lookup_cap validE_R

     apply(wp only:lookup_cap_cte_caps_to[THEN hoare_strengthen_postE_R])
     (* Neither of these help because they fill in the P.
        I think I need a new lemma about lookup_cap.
     apply(rule_tac P1="\<lambda>rv. rv = EndpointCap ep_ptr badge rights"
       in lookup_cap_cte_caps_to[THEN hoare_strengthen_postE_R])
     apply(wp only:lookup_cap_cte_caps_to[where P="\<lambda>rv. \<exists> a b c. rv = EndpointCap a b c", THEN hoare_strengthen_postE_R])
     *)
. (*
     apply(wpsimp wp:hoare_vcg_conj_liftE_R lookup_cap_gets hoare_vcg_ex_lift)
      find_theorems lookup_cap validE_R
      apply(wpsimp wp:lookup_cap_ex[THEN hoare_strengthen_postE_R])
      apply(clarsimp simp:cte_wp_at_def)

. (*

find_theorems name:imp name:hoare name:absorb
thm hoare_vcg_imp_liftE_R
hoare_vcg_imp_liftE_R'
     apply(wpsimp wp:hoare_absorb_imp[THEN valid_validE_R, THEN hoare_strengthen_postE_R])
. (*
(*
     apply(rotate_tac 1)
     apply(rule conjE)
      prefer 2
      apply(rule conjI)
       apply assumption
      apply(rotate_tac -1)
      apply(rule conjI)
       apply assumption
*)

      
thm conjI
     apply(rule conj_forward[where P=P'])


     apply(wp only:lookup_cap_cte_caps_to[THEN hoare_strengthen_postE_R])
     apply clarsimp
     apply(wp only:lookup_cap_cte_caps_to[where P="\<lambda>rv. \<exists> a b c. rv = EndpointCap a b c", THEN hoare_strengthen_postE_R])
     
     apply(wp only:hoare_absorb_imp[THEN valid_validE_R])
. (*
      
find_theorems name:conj intro
     apply(wpsimp wp:lookup_cap_cte_caps_to[where P="\<lambda>rv. \<exists> a b c. rv = EndpointCap a b c", THEN hoare_strengthen_postE_R])
apply assumption
     apply wpsimp
     apply(wpsimp wp:lookup_cap_cte_caps_to[where P="\<lambda>rv. \<exists> a b c. rv = EndpointCap a b c", THEN hoare_strengthen_postE_R])
     apply clarsimp
     apply(rule_tac P="thread = receiver" in hoare_gen_asmE)
     apply clarsimp
     apply(wp only:hoare_vcg_all_liftE_R)
      apply(rename_tac ref ep_ptr badge rights)
      apply(rule_tac P="receiver \<noteq> ep_ptr" in hoare_gen_asmE)
      apply clarsimp
find_theorems lookup_cap validE_R
thm lookup_cap_ex
. (*
      apply(wpsimp wp:hoare_vcg_all_liftE_R)

thm hoare_absorb_imp[THEN valid_validE_R, THEN hoare_strengthen_postE_R]
      apply(wp hoare_absorb_imp[THEN valid_validE_R, THEN hoare_strengthen_postE_R])
      apply clarsimp
apply assumption
      apply(rename_tac ref ep_ptr badge rights)
      apply(rule_tac P="receiver \<noteq> ep_ptr" in hoare_gen_asmE)
      apply clarsimp
      apply(wp only:hoare_vcg_all_liftE_R)
      apply(wp only:lookup_cap_inv[THEN valid_validE_R, THEN hoare_strengthen_postE_R])
     apply(wp only:lookup_cap_inv[THEN valid_validE_R, THEN hoare_strengthen_postE_R])

    apply assumption


(*
find_theorems lookup_cap
     apply(wpsimp wp:lookup_cap_gets[THEN hoare_strengthen_postE_R])
*)
     apply(wpsimp wp:lookup_cap_inv[THEN valid_validE_R, THEN hoare_strengthen_postE_R])

     apply(wpsimp wp:lookup_cap_gets[THEN hoare_strengthen_postE_R])
     apply(clarsimp simp:cte_wp_at_def)
     apply(rule conjI)
      apply clarsimp
      apply(rule conjI)
       apply clarsimp

     apply(wpsimp wp:hoare_vcg_all_liftE_R)


      apply clarsimp
(*
     apply(wpsimp wp:lookup_cap_inv[THEN valid_validE_R, THEN hoare_strengthen_postE_R])
apply assumption
*)

      apply(wpsimp wp:hoare_drop_impE_R)
     apply(wpsimp wp:lookup_cap_inv[THEN valid_validE_R, THEN hoare_strengthen_postE_R])

     apply clarsimp
     apply(wpsimp wp:hoare_drop_impE_R)



      apply(wpsimp wp:lookup_cap_gets[THEN hoare_strengthen_postE_R])

     apply(wpsimp wp:lookup_cap_inv)

      apply(wpsimp wp:hoare_drop_impE_R)
     apply
     apply(wpsimp wp:hoare_vcg_conj_liftE_R)
thm lookup_cap_inv
     apply(wpsimp wp:lookup_cap_inv)

      apply wpsimp


     apply(rule_tac P="thread = receiver \<and> receiver \<noteq> ref" in hoare_gen_asmE)
     apply(wpsimp wp:lookup_cap_gets[THEN hoare_strengthen_postE_R])
     apply(clarsimp simp:cte_wp_at_def get_cap_def)
     apply(rule conjI)
      apply clarsimp
      apply(rule conjI)
       apply clarsimp
     (* FIXME: yeah, we're missing a relevant precondition on the syscall *)
     defer
    apply wpsimp
   apply wpsimp
  apply wpsimp
  (* okay, we're back to the fault handling case. but we probably don't want these as arbitrary
     postconditions to this (unless they're in the precondition too) *)
  oops
*) *) *) *) *) *)

(* stuff's broken below this

lemma handle_SysRecv_syscall_ppcall:
  "\<lbrace>\<lambda>s. \<comment> \<open>MCS only - no reply cap argument or related pre/postconditions on non-MCS kernel
      valid_reply_obj (mspec_transform s) s MICROKIT_REPLY_CAP \<and>\<close>
      \<comment> \<open>
      P (cur_thread s) \<and>
      P'' (lookup_ipc_buffer_ret s False sender) \<and>
      P''' (lookup_ipc_buffer_ret s True receiver) \<and>
      P' (get_message_info_ret s sender) \<and>
      \<close>
      \<comment> \<open> having woes with types - bring this back in later
      valid_ep_obj_with_message sender (mspec_transform s) s MICROKIT_INPUT_CAP ro \<and>
      \<close>
      tcb_at sender s \<and> tcb_at receiver s \<and>
      receiver = cur_thread s
      \<comment> \<open> having woes with types - bring this back in later
      \<comment> \<open>FIXME: We need to catch the third case where there's neither a notification or ppcall\<close>
      \<not> (\<exists> n ntfn badge. cur_thread_bound_notification (mspec_transform s) = Some n \<and>
        kheap s n = Some (Notification ntfn) \<and>
        ntfn_obj ntfn = ActiveNtfn badge) \<close>
      \<comment> \<open>NB: Not yet sure if this is a safe assumption to make, or even needed
      ntfn_at (the (cur_thread_bound_notification (mspec_transform s))) s\<close>\<rbrace>
    handle_recv True
   \<lbrace>\<lambda> _ s.
      \<comment> \<open>
      P (cur_thread s) \<and>
      P'' (lookup_ipc_buffer_ret s False sender) \<and>
      P''' (lookup_ipc_buffer_ret s True receiver) \<and>
      P' (get_message_info_ret s sender) \<and>
      \<close>
      tcb_at sender s \<and> tcb_at receiver s \<and> \<comment> \<open>maybe a bit overkill, but not sure I care\<close>
      receiver = cur_thread s \<and>
      getRegister_as_user_ret s receiver badge_register = Some (badge_val ro) \<and>
      get_message_info_ret s receiver = Some
        (do_ipc_transfer_mi s (the (get_message_info_ret s sender)) sender receiver)
        \<comment> \<open>(do_ipc_transfer_mi s (minfo ro) sender receiver) \<and>\<close>
      \<comment> \<open>NB: put back if needed
      valid_message_info (the (get_message_info_ret s sender)) \<and>
      ntfn_at (the (cur_thread_bound_notification (mspec_transform s))) s\<close>\<rbrace>"
  apply(wpsimp wp:crunch_wps simp:handle_recv_def)
      (* fault handling - I think in reality we want to prove that the precondition
         ensures that there is no fault to handle. skip this for now *)
      defer
     apply wpsimp
      apply(wpsimp simp:Let_def)
       (* 17 subgoals *)
       (* more automated version *)
       apply(wpsimp simp:receive_ipc_def)
        (* 21 subgoals *)
        apply(rename_tac tcb xa x31 x32 x33 rv rvb ntfnptr)
        apply(rule_tac P="\<not> isActive rvb" in hoare_gen_asm)
        apply(wpsimp wp:crunch_wps set_object_wp get_simple_ko_wp get_object_wp
          simp:set_simple_ko_def AARCH64.setRegister_def as_user_def set_thread_state_def)+
            apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def
              do_ipc_transfer_mi_def do_normal_transfer_mi_def lookup_ipc_buffer_ret_def
              get_cap_ret_def get_tcb_def)
           apply(wpsimp wp:set_object_wp)
          apply wpsimp
         apply simp
        apply wpsimp
          (* 30 subgoals *)
          apply(wpsimp wp:crunch_wps set_object_wp simp:setup_caller_cap_def)+
           (* 31 subgoals *)
           apply(wpsimp wp:crunch_wps simp:cap_insert_def)
                   (* 40 subgoals *)
                   apply(force simp:getRegister_as_user_ret_def get_message_info_ret_def
                     do_ipc_transfer_mi_def do_normal_transfer_mi_def lookup_ipc_buffer_ret_def
                     get_cap_ret_def get_tcb_def)
                  (* more automated version *)
                  apply(wpsimp wp:crunch_wps set_object_wp get_object_wp
                    simp:update_cdt_def set_cdt_def set_cap_def)+
                (* 34 subgoals *)
                apply(wpsimp wp:crunch_wps get_object_wp simp:set_untyped_cap_as_full_def get_cap_def
                  set_thread_state_def)+
                  (* more careful version
                  apply(wpsimp simp:update_cdt_def set_cdt_def)
                 apply(wpsimp wp:gets_wp)
                apply(wpsimp wp:gets_wp)
               apply(wpsimp wp:gets_wp)
              apply(wpsimp wp:set_object_wp get_object_wp simp:set_cap_def)
             apply(wpsimp simp:set_untyped_cap_as_full_def)
            apply(wpsimp wp:assert_wp)
           apply(wpsimp wp:get_cap_wp)
          apply(wpsimp wp:get_cap_wp)
         apply(wpsimp simp:set_thread_state_def) *)
              (* 32 subgoals *)
              apply(wpsimp wp:crunch_wps set_object_wp get_object_wp simp:set_thread_state_def
                    |solves\<open>clarsimp simp:getRegister_as_user_ret_def get_message_info_ret_def
                     do_ipc_transfer_mi_def do_normal_transfer_mi_def lookup_ipc_buffer_ret_def
                     get_cap_ret_def get_tcb_def\<close>)+
           apply(rename_tac dst xa ep_obj x32 x33 ntfnptr_opt ntfn x2 rvd src rvg payload)
           apply(rule_tac P="\<not> (sender_can_grant payload) \<and> sender_badge payload = badge_val ro \<and>
             src \<noteq> dst \<and> src = sender \<and> dst = receiver" in hoare_gen_asm)
           apply(wpsimp wp:hoare_vcg_conj_lift)
            apply(wpsimp wp:do_ipc_transfer_cur_thread')
           apply(wpsimp wp:do_ipc_transfer_valid[where P=\<top> and P'=\<top> and P''=\<top>,
             THEN hoare_strengthen_post] simp:obj_at_def)
           apply(rule conjI)
            apply(clarsimp simp:getRegister_as_user_ret_def
              AARCH64_A.get_message_info_ret_getRegister_as_user_ret)
           apply clarsimp
           apply(rule conjI)
            apply(clarsimp simp:getRegister_as_user_ret_def)
           apply(clarsimp simp:get_message_info_ret_def)
           apply(clarsimp split:option.splits kernel_object.splits simp:is_tcb_def)
           apply(clarsimp simp:do_ipc_transfer_mi_def do_normal_transfer_mi_def
             lookup_ipc_buffer_ret_def get_cap_ret_def get_tcb_def tcb_cnode_map_def
             vm_read_write_def vm_read_only_def AARCH64_A.arch_cap.simps
             split:cap.splits AARCH64_A.arch_cap.splits bool.splits)
          apply(rename_tac dst xa ep_obj x32 x33 rv rva rvb x2 rvc rvd src rvf rvg payload)
          (* FIXME: exclude sender_can_grant_reply for now, but might we need this for ppcall? *)
          apply(rule_tac P="\<not> (sender_can_grant payload \<or> sender_can_grant_reply payload) \<and> sender_badge payload = badge_val ro \<and>
            src \<noteq> dst \<and> src = sender \<and> dst = receiver" in hoare_gen_asm)
          apply(wpsimp wp:hoare_vcg_conj_lift)
           apply(wpsimp wp:do_ipc_transfer_cur_thread')
          apply(wpsimp wp:do_ipc_transfer_valid[where P=\<top> and P'=\<top> and P''=\<top>,
            THEN hoare_strengthen_post] simp:obj_at_def)
          apply(rule conjI)
           apply(clarsimp simp:getRegister_as_user_ret_def
             AARCH64_A.get_message_info_ret_getRegister_as_user_ret)
          apply(clarsimp simp:get_message_info_ret_def)
          apply(clarsimp split:option.splits kernel_object.splits simp:is_tcb_def)
          apply(clarsimp simp:do_ipc_transfer_mi_def do_normal_transfer_mi_def
            lookup_ipc_buffer_ret_def get_cap_ret_def get_tcb_def tcb_cnode_map_def
            vm_read_write_def vm_read_only_def AARCH64_A.arch_cap.simps
            split:cap.splits AARCH64_A.arch_cap.splits bool.splits)
         apply(rename_tac dst xa ep_obj x32 x33 rv rva rvb x2 rvc rvd src rvf rvg payload)
         (* FIXME: might we need sender_is_call for ppcall? *)
         apply(rule_tac P="\<not> (sender_can_grant payload \<or> sender_is_call payload) \<and> sender_badge payload = badge_val ro \<and>
           src \<noteq> dst \<and> src = sender \<and> dst = receiver" in hoare_gen_asm)
         apply(wpsimp wp:hoare_vcg_conj_lift)
          apply(wpsimp wp:do_ipc_transfer_cur_thread')
         apply(wpsimp wp:do_ipc_transfer_valid[where P=\<top> and P'=\<top> and P''=\<top>,
           THEN hoare_strengthen_post] simp:obj_at_def)
         apply(rule conjI)
          apply(clarsimp simp:getRegister_as_user_ret_def
            AARCH64_A.get_message_info_ret_getRegister_as_user_ret)
         apply(clarsimp simp:get_message_info_ret_def)
         apply(clarsimp split:option.splits kernel_object.splits simp:is_tcb_def)
         apply(clarsimp simp:do_ipc_transfer_mi_def do_normal_transfer_mi_def
           lookup_ipc_buffer_ret_def get_cap_ret_def get_tcb_def tcb_cnode_map_def
           vm_read_write_def vm_read_only_def AARCH64_A.arch_cap.simps
           split:cap.splits AARCH64_A.arch_cap.splits bool.splits)
        apply clarsimp
        apply(wpsimp split:thread_state.splits wp:return_wp)
       apply(wpsimp wp:thread_get_wp simp:get_thread_state_def)
      apply(wpsimp wp:set_object_wp get_object_wp simp:set_simple_ko_def)+
      (* okay - we now seem to be on a different case where the recv syscall gets blocked
         because there is no message waiting to be received. need to rule this out with
         the precondition. *)
  oops
*)

end