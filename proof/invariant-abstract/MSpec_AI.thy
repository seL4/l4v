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
     apply(wpsimp wp:asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
       simp:get_message_info_ret_getRegister_as_user_ret split_del: if_split)
    apply clarsimp
    apply(rule_tac P="t \<noteq> receiver" in hoare_gen_asm)
    apply(wpsimp wp:asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
      simp:get_message_info_ret_getRegister_as_user_ret split_del: if_split)
   apply clarsimp
   apply(clarsimp simp:get_message_info_ret_getRegister_as_user_ret[symmetric])
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
  done

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
  "\<lbrace>\<lambda>s'. s = s' \<and> (\<forall> cap. get_cap_ret s' p = Some cap \<longrightarrow> Q cap s')\<rbrace> get_cap p
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

declare message_info_to_data.simps [simp del] (* proof becomes a mess if we leave these in *)
lemma do_normal_transfer_valid:
  "\<lbrace>(\<lambda>s. \<comment> \<open>MCS only - no reply cap argument or related pre/postconditions on non-MCS kernel
      valid_reply_obj (mspec_transform s) s MICROKIT_REPLY_CAP \<and>\<close>
      \<comment> \<open>when do we need to assert this?
      valid_ep_obj_with_message (mspec_transform s) s MICROKIT_INPUT_CAP ro \<and>\<close>
      P (get_message_info_ret s sender))
      and K (sender \<noteq> receiver \<and> \<not> grant)\<rbrace>
    do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda> _ s'. P (get_message_info_ret s' sender) \<and>
      getRegister_as_user_ret s' receiver badge_register = Some badge \<and>
      get_message_info_ret s' receiver =
      (let mi = the (get_message_info_ret s' sender);
           mrs_transferred = copy_mrs_ret sbuf rbuf (mi_length mi)
        \<comment> \<open>With grant = False, the extra_caps and caps_unwrapped end up as 0. Moreover, the
           conversion from MI to data format will truncate the original label's top 12 bits.\<close>
        in Some (MI mrs_transferred 0 0 (mi_label mi && mask 52))) \<and>
      valid_message_info (the (get_message_info_ret s' sender))\<rbrace>"
  unfolding do_normal_transfer_def
  apply(wpsimp simp:do_normal_transfer_def)
(* Advice from Tom: better to stick with wp approach & bring in only state-independent assumptions
   using hoare_gen_asm etc, but for state-dependent preconds, prove better lemmas to infer needed
   preconditions for given postconditions of the individual constituent functions in question. *)
        (* setting of badge register *)
        apply(wpsimp wp:asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
          simp:get_message_info_ret_getRegister_as_user_ret Let_def)
       apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register"
         in hoare_gen_asm)
       apply(simp split del: if_split)
       (* setting of message_info register *)
       apply(wpsimp wp:asUser_setRegister_getRegister_as_user hoare_vcg_ex_lift
         simp:set_message_info_def get_message_info_ret_getRegister_as_user_ret)
      apply(simp split del: if_split)
      apply(clarsimp simp:get_message_info_ret_getRegister_as_user_ret[symmetric])
      apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register \<and>
        caps = [] \<and> mrs_transferred = copy_mrs_ret sbuf rbuf (mi_length mi) \<and>
        valid_message_info mi" in hoare_gen_asm)
      apply clarsimp
      (* Note: Tom advised to try not to insert state-dependent facts using hoare_gen_asm_spec,
         but rather try to prove wp lemmas that give the needed precondition. *)
      apply(wp only:transfer_caps_none_valid[where t=sender, THEN hoare_strengthen_post])
      apply(simp split del:if_split)
     apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register \<and>
        caps = [] \<and> valid_message_info mi" in hoare_gen_asm)
     apply(wpsimp wp:copy_mrs_ret_valid[where t=sender, THEN hoare_strengthen_post])
     apply(simp split del:if_split)
    apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register"
      in hoare_gen_asm)
    apply clarsimp
    apply wpsimp
   apply(rule_tac P="sender \<noteq> receiver \<and> \<not> grant \<and> badge_register \<noteq> msg_info_register"
     in hoare_gen_asm)
   apply(clarsimp simp:transfer_caps_none_ret_def)
   apply(wpsimp wp:get_message_info_ret_valid[where P="\<lambda>s. P (get_message_info_ret s sender)",
     THEN hoare_strengthen_post])
   apply(rule conjI)
    using mi_to_data_to_mi
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
    using copy_mrs_ret_leq_msg_max_length
    apply force
   apply(rule_tac x=rv in exI)
   apply clarsimp
  apply clarsimp
  (* use this to resolve badge_register vs msg_info_register distinctness*)
  apply(solves\<open>simp add: AARCH64.badgeRegister_def AARCH64.msgInfoRegister_def badge_register_def msg_info_register_def\<close>)
  done

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