(*
 * Copyright 2024, The University of New South Wales
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory MSpec_AI
imports
  (* just make sure we have everything by importing the top-level module in the AInvs session *)
  AInvs.ArchDetSchedSchedule_AI
begin

consts
  MICROKIT_INPUT_CAP_WORD :: machine_word
  MICROKIT_REPLY_CAP_WORD :: machine_word
  MICROKIT_BASE_OUTPUT_NTFN_CAP_WORD :: machine_word
  MICROKIT_MAX_CHANNELS :: machine_word
  MICROKIT_PD_CAP_BITS :: nat

axiomatization where
  (* These numbers can also be found in tool/microkit/src/main.rs *)
  (* These are #define'd in libmicrokit/src/main.h *)
  MICROKIT_INPUT_CAP_WORD_def: "MICROKIT_INPUT_CAP_WORD \<equiv> 1" and
  MICROKIT_REPLY_CAP_WORD_def: "MICROKIT_REPLY_CAP_WORD \<equiv> 4" and
  (* These are #define'd in libmicrokit/include/microkit.h *)
  MICROKIT_BASE_OUTPUT_NTFN_CAP_WORD_def: "MICROKIT_BASE_OUTPUT_NTFN_CAP_WORD \<equiv> 10" and
  MICROKIT_MAX_CHANNELS_def: "MICROKIT_MAX_CHANNELS = 62" and
  (* PD_CAP_BITS is defined in tool/microkit/src/main.rs as ilog2 of PD_CAP_SIZE = 512, i.e. 9.
     SLOT_BITS = 5. SLOT_SIZE = 1 << SLOT_BITS = 2^5 = 32.
     api_size = log2(PD_CAP_SIZE) = 9 gets passed in as the size_bits to the UntypedRetype call
     that creates each PD's CNode.  *)
  MICROKIT_PD_CAP_BITS_def: "MICROKIT_PD_CAP_BITS \<equiv> 9"

definition MICROKIT_PD_CAP_GUARD :: "bool list"
where
  "MICROKIT_PD_CAP_GUARD \<equiv> drop MICROKIT_PD_CAP_BITS (data_to_cptr 0)"

term resolve_address_bits'
abbreviation to_microkit_cap_bl :: "machine_word \<Rightarrow> cnode_index"
where
  "to_microkit_cap_bl val \<equiv> drop (size MICROKIT_PD_CAP_GUARD) (data_to_cptr val)"

lemma microkit_cap_bl_size:
  "size (to_microkit_cap_bl val) = MICROKIT_PD_CAP_BITS"
  unfolding MICROKIT_PD_CAP_BITS_def MICROKIT_PD_CAP_GUARD_def
  by simp

abbreviation valid_microkit_cap :: "machine_word \<Rightarrow> bool"
where
  "valid_microkit_cap val \<equiv> val < 2^MICROKIT_PD_CAP_BITS"

(* that the guard is a prefix of the raw bitlist translation of the 64-bit value if
   the latter fits into the remaining bits after the guard *)
lemma
  "valid_microkit_cap val \<Longrightarrow> MICROKIT_PD_CAP_GUARD \<le> data_to_cptr val"
  unfolding MICROKIT_PD_CAP_GUARD_def
  (* XXX: surely this is true? not quite sure how to prove it yet *)
  oops

(* word bits should be 64. cte_level_bits should be 5.
   so the microkit caps shouldn't have a bit length greater than 58. *)
lemma microkit_cap_words_valid:
  "valid_microkit_cap MICROKIT_INPUT_CAP_WORD"
  "valid_microkit_cap MICROKIT_REPLY_CAP_WORD"
  "ch < MICROKIT_MAX_CHANNELS \<Longrightarrow> valid_microkit_cap (MICROKIT_BASE_OUTPUT_NTFN_CAP_WORD + ch)"
  unfolding MICROKIT_INPUT_CAP_WORD_def MICROKIT_REPLY_CAP_WORD_def
    MICROKIT_BASE_OUTPUT_NTFN_CAP_WORD_def MICROKIT_MAX_CHANNELS_def MICROKIT_PD_CAP_BITS_def
    MICROKIT_PD_CAP_GUARD_def data_to_cptr_def to_bl_def
  by (fastforce+, unat_arith)

definition MICROKIT_INPUT_CAP :: cnode_index
where
  "MICROKIT_INPUT_CAP \<equiv> to_microkit_cap_bl MICROKIT_INPUT_CAP_WORD"

definition MICROKIT_REPLY_CAP :: cnode_index
where
  "MICROKIT_REPLY_CAP \<equiv> to_microkit_cap_bl MICROKIT_REPLY_CAP_WORD"

definition MICROKIT_OUTPUT_NTFN_CAP :: "machine_word \<Rightarrow> cnode_index"
where
  "MICROKIT_OUTPUT_NTFN_CAP ch \<equiv> to_microkit_cap_bl (MICROKIT_BASE_OUTPUT_NTFN_CAP_WORD + ch)"

lemma microkit_cap_bl_sz_valid:
  "length (to_microkit_cap_bl val) < word_bits - cte_level_bits"
  using microkit_cap_bl_size
  unfolding MICROKIT_PD_CAP_BITS_def word_bits_def cte_level_bits_def
  by simp

(* XXX: Retiring this because the individual ntfn and ppc oracles are more useful
   and easier to treat as first-class projections.)
datatype mspec_recv_oracle =
  (* KO stands for "Kernel Oracle" *)
  KO_Notification badge |
  KO_PPCall obj_ref (* sender. FIXME: add message_info? *) |
  KO_Unknown
*)

datatype mspec_ntfn_status =
  KN_BoundTcbFree obj_ref |
  KN_BoundTcbBlocked obj_ref |
  KN_Unknown

(* When we get to supporting PPCs, I wonder if input_ep_status should be indexed by channel id
   from the sender's perspective with the datatype identifying the receiver, like for ntfn_status.
   But for now, just acknowledge it's from the receiver's perspective (and cnode). *)
datatype mspec_ppc_status =
  KP_ReceiverFree |
  KP_ReceiverBlocked |
  KP_Unknown

record mspec_state =
  ks_thread_cnode :: "cnode_contents option"
  ks_bound_notification :: "obj_ref option"
  (* ks_recv_oracle :: mspec_recv_oracle - retired. *)
  ks_ntfn_to_recv :: "badge option"
  ks_ntfn_status :: "machine_word \<Rightarrow> mspec_ntfn_status"
  (* obj_ref is sender. FIXME: need to add message_info when we verify proper ppc handling *)
  ks_ppc_to_recv :: "obj_ref option"
  ks_input_ep_status :: mspec_ppc_status
  ks_mapped_writable :: "machine_word \<Rightarrow> bool"
  ks_not_writable_others :: "machine_word \<Rightarrow> bool"

definition thread_cnode_cap :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> cap option"
where
  "thread_cnode_cap s t \<equiv>
     bind (get_tcb t s) (\<lambda>tcb. Some (tcb_ctable tcb))"

(* we have invs_valid_tcb_ctable but it won't enforce the precise microkit bit layout,
   we'll still need to do that ourselves *)
thm invs_valid_tcb_ctable valid_cap_def

abbreviation microkit_pd_bits_guard :: "nat \<Rightarrow> bool list \<Rightarrow> bool"
where
  "microkit_pd_bits_guard sz_bits guard \<equiv>
     sz_bits = MICROKIT_PD_CAP_BITS \<and>
     guard = MICROKIT_PD_CAP_GUARD"

definition thread_cnode :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> cnode_contents option"
where
  "thread_cnode s t \<equiv> case thread_cnode_cap s t of
     Some (CNodeCap cn_obj sz_bits guard) \<Rightarrow>
       (if microkit_pd_bits_guard sz_bits guard
         then (case kheap s cn_obj of Some (CNode sz contents) \<Rightarrow> Some contents |
           _ \<Rightarrow> None)
         else None) |
     _ \<Rightarrow> None"

lemma thread_cnode_has_wf_cap:
  "thread_cnode s t = Some contents \<Longrightarrow>
   \<exists>scn. thread_cnode_cap s t = Some (CNodeCap scn MICROKIT_PD_CAP_BITS MICROKIT_PD_CAP_GUARD)"
  by (clarsimp simp:thread_cnode_def thread_cnode_cap_def get_tcb_def
    split:option.splits cap.splits if_splits)

lemma thread_cnode_tcb_at[intro]:
  "thread_cnode s t = Some contents \<Longrightarrow>
   tcb_at t s"
  by (clarsimp simp:thread_cnode_def thread_cnode_cap_def get_tcb_def tcb_at_def
    split:option.splits cap.splits if_splits kernel_object.splits)

definition thread_cnode_paper :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> cnode_contents option"
where
  "thread_cnode_paper s t \<equiv>
     case bind (get_tcb t s) (\<lambda>tcb. Some (tcb_ctable tcb)) of
       Some (CNodeCap cn_obj sz_bits guard) \<Rightarrow>
         (if sz_bits = MICROKIT_PD_CAP_BITS \<and> guard = MICROKIT_PD_CAP_GUARD
           then (case kheap s cn_obj of
             Some (CNode sz contents) \<Rightarrow> Some contents |
             _ \<Rightarrow> None) else None) |_ \<Rightarrow> None"

lemma "thread_cnode_paper = thread_cnode"
  unfolding thread_cnode_def thread_cnode_cap_def thread_cnode_paper_def
  apply(rule ext)+
  by blast

definition bound_notification :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> obj_ref option"
where
  "bound_notification s t \<equiv>
     bind (get_tcb t s) tcb_bound_notification"

(* XXX retired
definition recv_oracle_old :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> mspec_recv_oracle"
where
  "recv_oracle_old s t \<equiv>
     case bound_notification s t of Some ntfnptr \<Rightarrow>
       (case kheap s ntfnptr of Some (Notification ntfn) \<Rightarrow>
         (case ntfn_obj ntfn of ActiveNtfn badge \<Rightarrow>
           KO_Notification badge |
     _ \<Rightarrow> KO_Unknown) | _ \<Rightarrow> KO_Unknown) | _ \<Rightarrow> KO_Unknown"
*)

definition ntfn_to_recv :: "'a::state_ext state \<Rightarrow> obj_ref option \<Rightarrow> badge option"
where
  "ntfn_to_recv s notif_opt \<equiv>
     case notif_opt of Some ntfnptr \<Rightarrow>
       (case kheap s ntfnptr of Some (Notification ntfn) \<Rightarrow>
         (case ntfn_obj ntfn of ActiveNtfn badge \<Rightarrow> Some badge |
     _ \<Rightarrow> None) | _ \<Rightarrow> None) | _ \<Rightarrow> None"

(* XXX retired
lemma recv_oracle_old_Some:
  "ntfn_to_recv s (bound_notification s t) = Some badge \<equiv>
   recv_oracle_old s t = KO_Notification badge"
  unfolding ntfn_to_recv_def recv_oracle_old_def
  apply(rule eq_reflection)
  by (force split:option.splits kernel_object.splits ntfn.splits)

lemma recv_oracle_old_None:
  "ntfn_to_recv s (bound_notification s t) = None \<equiv>
   recv_oracle_old s t = KO_Unknown"
  unfolding ntfn_to_recv_def recv_oracle_old_def
  apply(rule eq_reflection)
  by (force split:option.splits kernel_object.splits ntfn.splits)

*)

definition
  get_message_info_ret :: "'a state \<Rightarrow> obj_ref \<Rightarrow> message_info option"
where
  "get_message_info_ret s thread \<equiv> case kheap s thread of
    Some (TCB t) \<Rightarrow> (case arch_tcb_context_get (tcb_arch t) of
      RISCV64.UserContext u \<Rightarrow> Some (data_to_message_info (u msg_info_register))) |
    _ \<Rightarrow> None"

definition ppc_to_recv :: "'a::state_ext state \<Rightarrow> cnode_contents option \<Rightarrow> obj_ref option"
where
  "ppc_to_recv s contents \<equiv> case contents of None \<Rightarrow> None | Some c \<Rightarrow> (case c MICROKIT_INPUT_CAP of
     Some (EndpointCap ref ep_badge rights) \<Rightarrow> (case (AllowRead \<in> rights, kheap s ref) of
       (True, Some (Endpoint (SendEP (qh # qt)))) \<Rightarrow> Some qh |
         \<comment> \<open>FIXME: simplified even further yet again:
         (case kheap s qh of
         Some (TCB sender) \<Rightarrow> Some sender |
           \<comment> \<open>FIXME: simplified even further:
           (case tcb_state sender of
           \<comment> \<open>FIXME: Taking the raw, unmodified message_info here is a simplification for now.
             There are actually some further checks and processing that need to be done.
             (See draft `valid_ep_obj_with_ppc` predicate in MSpecExtras_AI.thy)\<close>
           BlockedOnSend _ data \<Rightarrow> (case get_message_info_ret s t of
             Some mi \<Rightarrow> Some (sender, mi) |
             _ \<Rightarrow> None) |
           _ \<Rightarrow> None) |\<close>
         _ \<Rightarrow> None) |\<close>
       _ \<Rightarrow> None) |
     _ \<Rightarrow> None)"

(* XXX retired
definition recv_oracle ::
  "'a::state_ext state \<Rightarrow> obj_ref option \<Rightarrow> cnode_contents option \<Rightarrow> mspec_recv_oracle"
where
  "recv_oracle s notif_opt contents \<equiv> case ntfn_to_recv s notif_opt of
     Some badge \<Rightarrow> KO_Notification badge |
     None \<Rightarrow> (case ppc_to_recv s contents of
       Some t' \<Rightarrow> KO_PPCall t' |
       None \<Rightarrow> KO_Unknown)"
*)

definition ntfn_of_ch :: "cnode_contents \<Rightarrow> machine_word \<Rightarrow> obj_ref option"
where
  "ntfn_of_ch contents ch \<equiv>
     case contents (MICROKIT_OUTPUT_NTFN_CAP ch) of
       Some (NotificationCap ntfnptr _ _) \<Rightarrow> Some ntfnptr | _ \<Rightarrow> None"

definition ntfn_status' :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> mspec_ntfn_status"
where
  "ntfn_status' s ntfnptr \<equiv>
     case kheap s ntfnptr of Some (Notification ntfn) \<Rightarrow>
       (case (ntfn_obj ntfn, ntfn_bound_tcb ntfn) of
         (IdleNtfn, Some receiver) \<Rightarrow>
         \<comment> \<open>For bound notifications, send_signal actually consults the bound tcb's status
           rather than whether the notification's status itself is IdleNtfn vs WaitingNtfn, etc.
           Consequently, we don't ever expect bound notifications to be in WaitingNtfn status.\<close>
           (case kheap s receiver of Some (TCB rtcb) \<Rightarrow>
              if receive_blocked (tcb_state rtcb)
              then KN_BoundTcbBlocked receiver
              else KN_BoundTcbFree receiver | _ \<Rightarrow> KN_Unknown) |
         \<comment> \<open>View 'active' as free as well, in the sense the receiver isn't blocked.\<close>
         (ActiveNtfn _, Some receiver) \<Rightarrow> KN_BoundTcbFree receiver |
         \<comment> \<open>TODO: valid_ntfn ensures the queue is [receiver] in this case, but what is the point
           of that if WaitingNtfn is never used for bound notifications? Have I misunderstood?\<close>
         (WaitingNtfn _, Some receiver) \<Rightarrow> KN_Unknown |
         \<comment> \<open>We only handle bound notifications here.\<close>
     _ \<Rightarrow> KN_Unknown) | _ \<Rightarrow> KN_Unknown"

definition ntfn_status :: "'a::state_ext state \<Rightarrow> cnode_contents option \<Rightarrow> machine_word \<Rightarrow> mspec_ntfn_status"
where
  "ntfn_status s contents ch \<equiv> case contents of
     Some c \<Rightarrow> (case ntfn_of_ch c ch of Some ntfnptr \<Rightarrow> ntfn_status' s ntfnptr | _ \<Rightarrow> KN_Unknown) |
     _ => KN_Unknown"

definition input_ep_status :: "'a::state_ext state \<Rightarrow> cnode_contents option \<Rightarrow> mspec_ppc_status"
where
  "input_ep_status s contents \<equiv> case contents of
     Some c \<Rightarrow> (case c MICROKIT_INPUT_CAP of
       Some (EndpointCap ref ep_badge rights) \<Rightarrow> (case (AllowRead \<in> rights, kheap s ref) of
         (True, Some (Endpoint ep)) \<Rightarrow> (case ep of
           RecvEP q \<Rightarrow> KP_ReceiverBlocked |
           _ \<Rightarrow> KP_ReceiverFree) |
         _ \<Rightarrow> KP_Unknown) |
       _ \<Rightarrow> KP_Unknown) |
     _ \<Rightarrow> KP_Unknown"

definition get_asid_of_thread :: "kheap \<Rightarrow> arch_state \<Rightarrow> obj_ref \<Rightarrow> asid option"
where
  "get_asid_of_thread khp astate tcb_ref \<equiv>
   case khp tcb_ref of Some (TCB tcb) \<Rightarrow>
     (case tcb_vtable tcb of
        ArchObjectCap (RISCV64_A.PageTableCap pt (Some (asid, _))) \<Rightarrow> Some asid |
        _ \<Rightarrow> None) | _ \<Rightarrow> None"

definition vs_lookup_rights :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> word64 \<Rightarrow> rights set option"
where
  "vs_lookup_rights s tcb addr \<equiv> if tcb_at tcb s then
    case get_asid_of_thread (kheap s) (arch_state s) tcb of
    Some asid \<Rightarrow> (case vs_lookup s 0 asid addr of 
      Some (lvl, ref) \<Rightarrow> (case RISCV64_A.ptes_of s ref of
        Some (RISCV64_A.PagePTE ppn attr rights) \<Rightarrow> Some rights |
        _ \<Rightarrow> None) |_ \<Rightarrow> None) | _ \<Rightarrow> None else None"

definition mapped_writable :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> word64 \<Rightarrow> bool"
where
  "mapped_writable s t \<equiv> \<lambda>addr. case vs_lookup_rights s t addr
     of Some rs \<Rightarrow> AllowWrite \<in> rs | None \<Rightarrow> False"

definition not_writable_others :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> word64 \<Rightarrow> bool"
where
  "not_writable_others s t \<equiv>
     \<lambda>addr. \<forall>t'. t' \<noteq> t \<longrightarrow> (case vs_lookup_rights s t' addr
       of Some rs \<Rightarrow> AllowWrite \<notin> rs | None \<Rightarrow> True)"

(* Some additional Microkit wellformedness conditions *)

definition no_channels_to' :: "'a::state_ext state \<Rightarrow> cnode_contents \<Rightarrow> obj_ref \<Rightarrow> bool"
where
  "no_channels_to' s contents t \<equiv> \<forall>ch. case ntfn_of_ch contents ch of Some nptr \<Rightarrow>
     (case kheap s nptr of Some (Notification n) \<Rightarrow>
       (case ntfn_bound_tcb n of Some t' \<Rightarrow> t' \<noteq> t | _ \<Rightarrow> True) | _ \<Rightarrow> True) | _ \<Rightarrow> True"

definition no_channels_to :: "cnode_contents \<Rightarrow> obj_ref option \<Rightarrow> bool"
where
  "no_channels_to contents bound_notif \<equiv> \<forall>ch. case ntfn_of_ch contents ch of Some nptr \<Rightarrow>
     (bound_notif \<noteq> Some nptr) | _ \<Rightarrow> True"

lemma tcb_bound_ntfn_bound_tcb:
  "invs s \<Longrightarrow>
   kheap s t = Some (TCB tcb) \<Longrightarrow>
   tcb_bound_notification tcb = Some ntfnptr \<Longrightarrow>
   kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow>
   ntfn_bound_tcb ntfn = Some t"
  by (force intro:bound_tcb_bound_notification_at simp:pred_tcb_at_def obj_at_def)

lemma ntfn_bound_tcb_bound_ntfn:
  "invs s \<Longrightarrow>
   kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow>
   ntfn_bound_tcb ntfn = Some t \<Longrightarrow>
   kheap s t = Some (TCB tcb) \<Longrightarrow>
   tcb_bound_notification tcb = Some ntfnptr"
  using ntfn_bound_tcb_at[where s=s and ntfnptr=ntfnptr and ntfn=ntfn and tcbptr=t,
    simplified pred_tcb_at_def obj_at_def]
  by (smt (verit) bound_tcb_bound_notification_at invs_sym_refs invs_valid_objs kernel_object.simps(2) option.simps(1) tcb_to_itcb_simps(5))

lemma no_channels_to':
  "invs s \<Longrightarrow> valid_objs s \<Longrightarrow> tcb_at t' s \<Longrightarrow>
   thread_cnode s t \<noteq> None \<Longrightarrow>
   no_channels_to (the (thread_cnode s t)) (bound_notification s t') =
   no_channels_to' s (the (thread_cnode s t)) t'"
  unfolding no_channels_to'_def no_channels_to_def ntfn_of_ch_def
    thread_cnode_def thread_cnode_cap_def tcb_at_def get_tcb_def 
  apply(clarsimp split:option.splits kernel_object.splits cap.splits)
  apply(clarsimp simp:valid_objs_def)
  apply(frule_tac x=t in bspec)
   apply clarsimp
  apply clarsimp
  apply(frule_tac x=t' in bspec)
   apply clarsimp
  apply clarsimp
  apply(rule iffI)
   apply(clarsimp simp:bound_notification_def get_tcb_def split: if_splits)
   apply(drule_tac x=x41 in bspec)
    apply clarsimp
   apply(clarsimp simp:valid_obj_def valid_tcb_def valid_bound_ntfn_def)
   apply(clarsimp simp:obj_at_def is_ntfn_def)
   using ntfn_bound_tcb_bound_ntfn
   apply blast
  apply(clarsimp simp:bound_notification_def get_tcb_def)
  apply(clarsimp simp:valid_obj_def valid_tcb_def valid_bound_ntfn_def)
  apply(clarsimp simp:obj_at_def is_ntfn_def)
  using tcb_bound_ntfn_bound_tcb
  apply(metis (no_types, lifting) kernel_object.case_eq_if kernel_object.collapse(4))
  done

definition tcb_of_ch :: "'a::state_ext state \<Rightarrow> cnode_contents \<Rightarrow> machine_word \<Rightarrow> obj_ref option"
where
  "tcb_of_ch s contents ch \<equiv> case ntfn_of_ch contents ch of Some nptr \<Rightarrow>
     (case kheap s nptr of Some (Notification n) \<Rightarrow> ntfn_bound_tcb n | _ \<Rightarrow> None) | _ \<Rightarrow> None"

definition tcbs_of_channels :: "'a::state_ext state \<Rightarrow> cnode_contents \<Rightarrow> obj_ref set"
where
  "tcbs_of_channels s contents \<equiv> {t'. \<exists>ch nptr n. ntfn_of_ch contents ch = Some nptr \<and>
     kheap s nptr = Some (Notification n) \<and> ntfn_bound_tcb n = Some t'}"

lemma tcbs_of_channels_def2:
  "tcbs_of_channels s t \<equiv> {t'. \<exists>ch. tcb_of_ch s t ch = Some t'}"
  unfolding tcbs_of_channels_def tcb_of_ch_def
  apply(rule eq_reflection)
  apply(rule set_eqI)
  apply(rule iffI)
   apply(auto split:option.splits kernel_object.splits)[1]
  apply(clarsimp split:option.splits kernel_object.splits)
  by (metis kernel_object.exhaust)

lemma no_channels_to_def2:
  "no_channels_to' s contents t \<equiv> t \<notin> tcbs_of_channels s contents"
  unfolding no_channels_to'_def tcbs_of_channels_def
  apply(rule eq_reflection)
  by (force split:option.splits kernel_object.splits)

definition channels_distinct_tcbs :: "'a::state_ext state \<Rightarrow> cnode_contents \<Rightarrow> bool"
where
  "channels_distinct_tcbs s contents \<equiv> \<forall>ch ch' t' t''. ch \<noteq> ch' \<and>
     tcb_of_ch s contents ch = Some t' \<and> tcb_of_ch s contents ch' = Some t''
     \<longrightarrow> t' \<noteq> t''"

(* Actually, I think this should *always* hold as long as different channels have
   distinct notification objects because, if not, then there would have to exist
   one tcb bound to two different notification objs, which is impossible. *)

definition channels_distinct_ntfns :: "cnode_contents \<Rightarrow> bool"
where
  "channels_distinct_ntfns contents \<equiv> \<forall>ch ch'. ch \<noteq> ch' \<longrightarrow>
     ntfn_of_ch contents ch \<noteq> ntfn_of_ch contents ch'"

lemma channels_distinct_ntfns_tcbs:
  "invs s \<Longrightarrow>
   channels_distinct_ntfns contents \<Longrightarrow>
   channels_distinct_tcbs s contents"
  unfolding channels_distinct_tcbs_def tcb_of_ch_def channels_distinct_ntfns_def ntfn_of_ch_def
  apply(frule invs_valid_objs)
  apply(clarsimp simp:valid_objs_def)
  apply(clarsimp split:option.splits kernel_object.splits)
  apply(rename_tac ch ch' t'' n1 n2 x2b x2d x4 x4a)
  apply(erule_tac x=ch in allE)
  apply clarsimp
  apply(erule_tac x=ch' in allE)
  apply clarsimp
  apply(frule_tac x=n1 in bspec)
   apply clarsimp
  apply(frule_tac x=n2 in bspec)
   apply clarsimp
  apply(clarsimp simp:valid_obj_def valid_ntfn_def tcb_at_def get_tcb_def split:option.splits)
  apply(drule_tac x=t'' in bspec)
   apply clarsimp
  apply(clarsimp split:kernel_object.splits)
  apply(clarsimp simp:valid_tcb_def valid_bound_ntfn_def)
  apply(frule_tac ntfnptr=n1 and ntfn=x4 in ntfn_bound_tcb_bound_ntfn, simp_all)
  apply(drule_tac ntfnptr=n2 and ntfn=x4a in ntfn_bound_tcb_bound_ntfn, simp_all)
  by force

definition input_cap_configured :: "cnode_contents option \<Rightarrow> obj_ref \<Rightarrow> bool"
where
  "input_cap_configured contents ref \<equiv> \<exists> c ep_badge rights.
     contents = Some c \<and> c MICROKIT_INPUT_CAP = Some (EndpointCap ref ep_badge rights) \<and>
     AllowRead \<in> rights"

definition output_ntfn_cap_configured :: "cnode_contents option \<Rightarrow> machine_word \<Rightarrow> badge \<Rightarrow> bool"
where
  "output_ntfn_cap_configured contents ch badge_val \<equiv> \<exists> c ntfnptr rights.
     contents = Some c \<and> c (MICROKIT_OUTPUT_NTFN_CAP ch) =
       Some (NotificationCap ntfnptr badge_val rights) \<and>
     AllowWrite \<in> rights"

(* Microkit state projection function *)

definition
  ks_of :: "'a::state_ext state \<Rightarrow> obj_ref \<Rightarrow> mspec_state"
where
  "ks_of s t \<equiv> \<lparr>
     ks_thread_cnode = thread_cnode s t,
     ks_bound_notification = bound_notification s t,
     \<comment> \<open>NB: Broadly we try to make dependencies between MSpec fields explicit.\<close>
     ks_ntfn_to_recv = ntfn_to_recv s (bound_notification s t),
     ks_ntfn_status = \<lambda>ch. ntfn_status s (thread_cnode s t) ch,
     ks_ppc_to_recv = ppc_to_recv s (thread_cnode s t),
     ks_input_ep_status = input_ep_status s (thread_cnode s t),
     ks_mapped_writable = mapped_writable s t,
     ks_not_writable_others = not_writable_others s t
   \<rparr>"

(* More usable lemmas about return values of monads *)
definition
  getRegister_ret :: "'a state \<Rightarrow> obj_ref \<Rightarrow> register \<Rightarrow> machine_word option"
where
  "getRegister_ret s thread r \<equiv> case kheap s thread of
    Some (TCB t) \<Rightarrow> (case arch_tcb_context_get (tcb_arch t) of
      RISCV64.UserContext u \<Rightarrow> Some (u r)) |
    _ \<Rightarrow> None"

lemma getRegister_ret_valid:
  "\<lbrace>\<lambda>s. P s\<rbrace> as_user t $ getRegister r
   \<lbrace>\<lambda> rv s. P s \<and> getRegister_ret s t r = Some rv\<rbrace>"
  unfolding getRegister_ret_def
  apply wp
   unfolding as_user_def
   apply(wpsimp wp:set_object_wp)
  apply wpsimp
  unfolding RISCV64.getRegister_def get_tcb_def gets_def get_def
  apply(clarsimp split:option.splits kernel_object.splits RISCV64.user_context.splits
    simp:bind_def return_def)
  using RISCV64.user_context.sel by force

lemma get_message_info_ret_valid:
  "\<lbrace>P\<rbrace> get_message_info t
   \<lbrace>\<lambda> rv s. P s \<and> get_message_info_ret s t = Some rv \<and> valid_message_info rv\<rbrace>"
  unfolding get_message_info_def get_message_info_ret_def
  apply wp
   unfolding as_user_def
   apply(wpsimp wp:set_object_wp)
  apply wpsimp
  unfolding RISCV64.getRegister_def get_tcb_def gets_def get_def
  apply(clarsimp split:option.splits kernel_object.splits RISCV64.user_context.splits
    simp:bind_def return_def)
  apply(rule conjI)
   using RISCV64.user_context.sel apply force
  by (rule data_to_message_info_valid)

lemma vs_lookup_rights_lift:
  assumes tcb: "\<And>P. \<lbrace>\<lambda>s. Q s \<and> P (tcb_at t s)\<rbrace> f \<lbrace>\<lambda>r s. P (tcb_at t s)\<rbrace>"
  assumes gta: "\<And>P. \<lbrace>\<lambda>s. Q s \<and> P (get_asid_of_thread (kheap s) (arch_state s) t)\<rbrace>
    f \<lbrace>\<lambda>r s. P (get_asid_of_thread (kheap s) (arch_state s) t)\<rbrace>"
  assumes vsl: "\<And>P. \<lbrace>\<lambda>s. Q s \<and> P (vs_lookup s)\<rbrace> f \<lbrace>\<lambda>r s. P (vs_lookup s)\<rbrace>"
  assumes ptes: "\<And>P. \<lbrace>\<lambda>s. Q s \<and> P (RISCV64_A.ptes_of s)\<rbrace>
    f \<lbrace>\<lambda>r s. P (RISCV64_A.ptes_of s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> P (vs_lookup_rights s t a)\<rbrace> f \<lbrace>\<lambda>r s. P (vs_lookup_rights s t a)\<rbrace>"
  unfolding vs_lookup_rights_def
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:vsl)
    apply(wpsimp wp:gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:ptes)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:vsl)
    apply(wpsimp wp:gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:ptes)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:vsl)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:gta)
   apply(wpsimp wp:tcb)
  apply(wpsimp wp:hoare_vcg_conj_lift)
  apply(rule context_conjI)
   apply force
  apply clarsimp
  by (meson cases_simp_option not_Some_eq_tuple)

lemma vs_lookup_rights_lift':
  assumes tcb: "\<And>P. f \<lbrace>\<lambda>s. P (tcb_at t s)\<rbrace>"
  assumes gta: "\<And>P. f \<lbrace>\<lambda>s. P (get_asid_of_thread (kheap s) (arch_state s) t)\<rbrace>"
  assumes vsl: "\<And>P. f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  assumes ptes: "\<And>P x. f \<lbrace>\<lambda>s. P (RISCV64_A.ptes_of s x)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_rights s t)\<rbrace>"
  unfolding vs_lookup_rights_def
  apply(rule_tac P=P in hoare_liftP_ext)
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:vsl)
    apply(wpsimp wp:gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:ptes)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:vsl)
    apply(wpsimp wp:gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:ptes)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:vsl)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:gta)
   apply(wpsimp wp:tcb)
  apply clarsimp
  apply(rule context_conjI)
   apply clarsimp
   apply force
  apply clarsimp
  apply(metis not_Some_eq)
  done

(* XXX retired
lemma recv_oracle_lift:
  assumes nr: "\<And>P. f  \<lbrace>\<lambda>s. P (ntfn_to_recv s notif_opt)\<rbrace>"
  assumes pr: "\<And>P. f  \<lbrace>\<lambda>s. P (ppc_to_recv s contents)\<rbrace>"
  shows "f  \<lbrace>\<lambda>s. P (recv_oracle s notif_opt contents)\<rbrace>"
  unfolding recv_oracle_def
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_op_lift nr pr)
  done
*)

lemma ntfn_status_lift:
  assumes ns: "\<And>P ntfnptr. f \<lbrace>\<lambda>s. P (ntfn_status' s ntfnptr)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (ntfn_status s contents)\<rbrace>"
  unfolding ntfn_status_def
  apply(rule_tac P=P in hoare_liftP_ext)
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_op_lift ns)
  done

lemma mapped_writable_lift:
  assumes vlr: "\<And>P. \<lbrace>\<lambda>s. Q s \<and> P (vs_lookup_rights s t)\<rbrace> f \<lbrace>\<lambda>r s. P (vs_lookup_rights s t)\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> P (mapped_writable s t)\<rbrace> f \<lbrace>\<lambda>r s. P (mapped_writable s t)\<rbrace>"
  unfolding mapped_writable_def
  by (wpsimp wp:vlr)

lemma hoare_liftP_all':
  "\<forall>x. \<lbrace>\<lambda>s. Q s \<and> P (R x s)\<rbrace> f \<lbrace>\<lambda>r s. P (R x s)\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. Q s \<and> P (\<forall>x. R x s)\<rbrace> f \<lbrace>\<lambda>r s. P (\<forall>x. R x s)\<rbrace>"
  apply(clarsimp simp:valid_def)
  by (smt (verit, best) split_conv)

lemma hoare_liftP_imp':
  "Q \<longrightarrow> \<lbrace>\<lambda>s. Q' s \<and> P (R x s)\<rbrace> f \<lbrace>\<lambda>r s. P (R x s)\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. Q' s \<and> P (Q \<longrightarrow> R x s)\<rbrace> f \<lbrace>\<lambda>r s. P (Q \<longrightarrow> R x s)\<rbrace>"
  apply(clarsimp simp:valid_def split:prod.splits)
  by (smt (verit, best))

lemma hoare_liftP_ext':
  assumes "\<And>P x. \<lbrace>\<lambda>s. Q s \<and> P (f s x)\<rbrace> m \<lbrace>\<lambda>r s. P (f s x)\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> P (f s)\<rbrace> m \<lbrace>\<lambda>r s. P (f s)\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (erule subst[rotated, where P=P])
  apply (rule ext)
  using use_valid assms
  by fastforce

lemma not_writable_others_lift:
  assumes vlr: "\<And>Pv t' a. t' \<noteq> t \<Longrightarrow>
    \<lbrace>\<lambda>(s::'a::state_ext state). Q s \<and> Pv (case vs_lookup_rights s t' a of
      Some rs \<Rightarrow> AllowWrite \<notin> rs |
      None \<Rightarrow> True)\<rbrace>
    f \<lbrace>\<lambda>r s. Pv (case vs_lookup_rights s t' a of
      Some rs \<Rightarrow> AllowWrite \<notin> rs |
      None \<Rightarrow> True)\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> P (not_writable_others s t)\<rbrace> f \<lbrace>\<lambda>r s. P (not_writable_others s t)\<rbrace>"
  unfolding not_writable_others_def
  apply(rule_tac P=P in hoare_liftP_ext')
  apply(rule hoare_liftP_all')
  apply clarsimp
  apply(rule hoare_liftP_imp')
  apply clarsimp
  apply(wpsimp wp:vlr)
  done

lemma ks_of_lift:
  assumes tc: "\<And>P. f \<lbrace>\<lambda>s. P (thread_cnode s t)\<rbrace>"
  assumes bn: "\<And>P. f \<lbrace>\<lambda>s. P (bound_notification s t)\<rbrace>"
  assumes nr: "\<And>P notif_opt. f \<lbrace>\<lambda>s. P (ntfn_to_recv s notif_opt)\<rbrace>"
  assumes ns: "\<And>P contents. f \<lbrace>\<lambda>s. P (ntfn_status s contents)\<rbrace>"
  assumes pr: "\<And>P contents. f \<lbrace>\<lambda>s. P (ppc_to_recv s contents)\<rbrace>"
  assumes ie: "\<And>P contents. f \<lbrace>\<lambda>s. P (input_ep_status s contents)\<rbrace>"
  assumes mw: "\<And>P. f \<lbrace>\<lambda>s. P (mapped_writable s t)\<rbrace>"
  assumes nwo: "\<And>P. f \<lbrace>\<lambda>s. P (not_writable_others s t)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (ks_of s t)\<rbrace>"
  unfolding ks_of_def valid_def
  apply clarsimp
  using use_valid[OF _ tc] use_valid[OF _ bn] use_valid[OF _ nr] use_valid[OF _ ns]
    use_valid[OF _ pr] use_valid[OF _ ie] use_valid[OF _ mw] use_valid[OF _ nwo]
  proof -
    fix s :: "'a state" and a :: 'b and b :: "'a state"
    assume a1: "P \<lparr>ks_thread_cnode = thread_cnode s t, ks_bound_notification = bound_notification s t, ks_ntfn_to_recv = ntfn_to_recv s (bound_notification s t), ks_ntfn_status = ntfn_status s (thread_cnode s t), ks_ppc_to_recv = ppc_to_recv s (thread_cnode s t), ks_input_ep_status = input_ep_status s (thread_cnode s t), ks_mapped_writable = mapped_writable s t, ks_not_writable_others = not_writable_others s t\<rparr>"
    assume a2: "(a, b) \<in> fst (f s)"
    then have f3: "\<forall>p z. \<not> p (ntfn_status s z) \<or> p (ntfn_status b z)"
      by (smt (z3) \<open>\<And>s' s r contents P. \<lbrakk>(r, s') \<in> fst (f s); P (ntfn_status s contents)\<rbrakk> \<Longrightarrow> P (ntfn_status s' contents)\<close>)
    have f4: "\<forall>p. \<not> p (mapped_writable s t) \<or> p (mapped_writable b t)"
      using a2 by (smt (z3) \<open>\<And>s' s r P. \<lbrakk>(r, s') \<in> fst (f s); P (mapped_writable s t)\<rbrakk> \<Longrightarrow> P (mapped_writable s' t)\<close>)
    have "P \<lparr>ks_thread_cnode = thread_cnode b t, ks_bound_notification = bound_notification b t, ks_ntfn_to_recv = ntfn_to_recv b (bound_notification b t), ks_ntfn_status = ntfn_status s (thread_cnode b t), ks_ppc_to_recv = ppc_to_recv s (thread_cnode b t), ks_input_ep_status = input_ep_status s (thread_cnode b t), ks_mapped_writable = mapped_writable s t, ks_not_writable_others = not_writable_others s t\<rparr>"
      using a2 a1 by (meson \<open>\<And>s' s r P. \<lbrakk>(r, s') \<in> fst (f s); P (bound_notification s t)\<rbrakk> \<Longrightarrow> P (bound_notification s' t)\<close> \<open>\<And>s' s r P. \<lbrakk>(r, s') \<in> fst (f s); P (thread_cnode s t)\<rbrakk> \<Longrightarrow> P (thread_cnode s' t)\<close> \<open>\<And>s' s r notif_opt P. \<lbrakk>(r, s') \<in> fst (f s); P (ntfn_to_recv s notif_opt)\<rbrakk> \<Longrightarrow> P (ntfn_to_recv s' notif_opt)\<close>)
    then show "P \<lparr>ks_thread_cnode = thread_cnode b t, ks_bound_notification = bound_notification b t, ks_ntfn_to_recv = ntfn_to_recv b (bound_notification b t), ks_ntfn_status = ntfn_status b (thread_cnode b t), ks_ppc_to_recv = ppc_to_recv b (thread_cnode b t), ks_input_ep_status = input_ep_status b (thread_cnode b t), ks_mapped_writable = mapped_writable b t, ks_not_writable_others = not_writable_others b t\<rparr>"
      using f4 f3 a2 by (meson \<open>\<And>s' s r P. \<lbrakk>(r, s') \<in> fst (f s); P (not_writable_others s t)\<rbrakk> \<Longrightarrow> P (not_writable_others s' t)\<close> \<open>\<And>s' s r contents P. \<lbrakk>(r, s') \<in> fst (f s); P (input_ep_status s contents)\<rbrakk> \<Longrightarrow> P (input_ep_status s' contents)\<close> \<open>\<And>s' s r contents P. \<lbrakk>(r, s') \<in> fst (f s); P (ppc_to_recv s contents)\<rbrakk> \<Longrightarrow> P (ppc_to_recv s' contents)\<close>)
  qed
  (* ^^^ XXX: not ideal to lean on smt (z3) but revisit later. unfortunately,
     adding "ie" was the straw that broke (force intro: ...)'s back.
  by (force intro:use_valid[OF _ tc] use_valid[OF _ bn] use_valid[OF _ nr] use_valid[OF _ ns]
    use_valid[OF _ pr] use_valid[OF _ ie] use_valid[OF _ mw] use_valid[OF _ nwo]) *)

(* FIXME: In the long run we'll need to interface off the arch-specific parts properly.
  But some of the return values depend on arch-specific implementations, so for now
  while experimenting we'll just open up the Arch context and do it in here. *)
context Arch begin global_naming RISCV64_A

lemma asUser_setRegister_getRegister_as_user:
  "\<lbrace>\<lambda>s. P (if t = t' \<and> r = r' then Some v else getRegister_ret s t' r')\<rbrace>
    as_user t (setRegister r v)
  \<lbrace>\<lambda>rv s. P (getRegister_ret s t' r')\<rbrace>"
  apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
  apply(clarsimp simp:getRegister_ret_def)
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

lemma tcb_at_setRegister_as_user:
  "\<lbrace>\<lambda>s. P (tcb_at t' s)\<rbrace>
    as_user t (setRegister r v)
  \<lbrace>\<lambda>rv s. P (tcb_at t' s)\<rbrace>"
  by (wpsimp wp:as_user_wp_thread_set_helper set_object_wp
    simp:get_asid_of_thread_def thread_set_def get_tcb_def tcb_at_def)

lemma vs_lookup_rights_setRegister_as_user:
  "\<lbrace>\<lambda>s. P (vs_lookup_rights s t')\<rbrace>
    as_user t (setRegister r v)
  \<lbrace>\<lambda>rv s. P (vs_lookup_rights s t')\<rbrace>"
  apply(wpsimp wp:vs_lookup_rights_lift')
      apply(wpsimp wp:tcb_at_setRegister_as_user)
     apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp
       simp:get_asid_of_thread_def thread_set_def get_tcb_def)
     apply(clarsimp split:option.splits cap.splits arch_cap.splits kernel_object.splits)
    apply(wpsimp wp:set_object_wp simp:thread_set_def)
   apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp
     simp:thread_set_def get_tcb_def opt_map_def)
   apply(clarsimp simp:aobj_of_def pt_of_def pte_of_def oassert_def oapply_def
     split:if_splits option.splits)
   apply(clarsimp simp:obind_def)
   apply(fastforce split:option.splits kernel_object.splits arch_kernel_obj.splits if_splits)
  apply assumption
  done

lemma ks_of_setRegister_as_user:
  "\<lbrace>\<lambda>s. P (ks_of s t')\<rbrace>
    as_user t (setRegister r v)
  \<lbrace>\<lambda>rv s. P (ks_of s t')\<rbrace>"
  apply(wpsimp wp:ks_of_lift set_object_wp simp:thread_set_def, simp_all)
         apply(solves\<open>wpsimp wp:as_user_wp_thread_set_helper set_object_wp
           simp:thread_set_def thread_cnode_def thread_cnode_cap_def get_tcb_def
           split:option.splits kernel_object.splits cap.splits,
           fastforce+\<close>)
        apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp
          simp:thread_set_def bound_notification_def get_tcb_def)
       apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp
         simp:thread_set_def get_tcb_def
         split:option.splits kernel_object.splits ntfn.splits)
       apply(fastforce simp:ntfn_to_recv_def split:option.splits kernel_object.splits ntfn.splits)
      apply(rule_tac P=P in hoare_liftP_ext)
      apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp ntfn_status_lift
         simp:thread_set_def get_tcb_def
         split:option.splits kernel_object.splits)
       apply(solves\<open>clarsimp simp:ntfn_status'_def receive_blocked_def
         split:option.splits kernel_object.splits ntfn.splits if_splits,
         (rule conjI | clarsimp)+\<close>)
      apply assumption
     apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp
       simp:thread_set_def get_tcb_def
       split:option.splits kernel_object.splits ntfn.splits)
     apply(fastforce simp:ppc_to_recv_def split:option.splits cap.splits bool.splits)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp
      simp:thread_set_def get_tcb_def
      split:option.splits kernel_object.splits ntfn.splits)
    apply(fastforce simp:input_ep_status_def split:option.splits cap.splits bool.splits)
   apply(wpsimp wp:mapped_writable_lift vs_lookup_rights_setRegister_as_user)
  by (wpsimp wp:not_writable_others_lift vs_lookup_rights_setRegister_as_user)

lemma get_message_info_ret_getRegister_ret:
  "get_message_info_ret s t =
    Option.map_option data_to_message_info (getRegister_ret s t msg_info_register)"
  by (clarsimp simp:get_message_info_ret_def getRegister_ret_def
    split:option.splits kernel_object.splits user_context.splits)

end

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
         Some (ArchObjectCap (RISCV64_A.FrameCap p R vms False _)) \<Rightarrow>
              if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
              then Some (p + (buffer_ptr && mask (RISCV64.pageBitsForSize vms)))
              else None
            | _ \<Rightarrow> None) |
   _ \<Rightarrow> None"

lemma lookup_ipc_buffer_ret_valid:
  "\<lbrace>\<lambda>s. tcb_at thread s\<rbrace>
    lookup_ipc_buffer is_receiver thread
   \<lbrace>\<lambda> r s. r = lookup_ipc_buffer_ret s is_receiver thread\<rbrace>"
  unfolding RISCV64_A.lookup_ipc_buffer_def lookup_ipc_buffer_ret_def
  apply wpsimp
     apply(wpsimp wp:get_cap_ret_valid[THEN hoare_strengthen_post])
    apply wpsimp
   apply(wpsimp wp:thread_get_wp)
  apply(wpsimp simp:tcb_at_def get_tcb_def obj_at_def)
  by (clarsimp simp:get_cap_ret_def is_tcb_def
    vm_read_write_def vm_read_only_def RISCV64_A.arch_cap.simps
    split:option.splits kernel_object.splits cap.splits RISCV64_A.arch_cap.splits bool.splits)

definition
  valid_ep_obj_with_ntfn :: "('a::state_ext) state \<Rightarrow> badge \<Rightarrow> bool"
where
  "valid_ep_obj_with_ntfn s badge_val \<equiv>
     thread_cnode s (cur_thread s) \<noteq> None \<and>
     \<comment> \<open>Microkit only checks notifications via EndpointCap, not via any standalone NotificationCap\<close>
     (\<exists> cn_ref some_nat bool_list sz contents ref ep_badge rights.
       thread_cnode_cap s (cur_thread s) = Some (CNodeCap cn_ref some_nat bool_list) \<and>
       microkit_pd_bits_guard some_nat bool_list \<and>
       kheap s cn_ref = Some (CNode sz contents) \<and>
       cte_wp_at ((=) (EndpointCap ref ep_badge rights)) (cn_ref, MICROKIT_INPUT_CAP) s \<and> 
       AllowRead \<in> rights \<and>
         (\<exists>ntfnptr. bound_tcb_at ((=) ntfnptr) (cur_thread s) s) \<and>
         (\<forall>ntfnptr. bound_tcb_at ((=) ntfnptr) (cur_thread s) s \<longrightarrow>
           (\<exists>ntfn n badge. ntfnptr = Some n \<and>
             ko_at (Notification ntfn) n s \<and>
             \<comment> \<open>Note: receive_ipc handles waiting bound notifications via complete_signal\<close>
             ntfn_obj ntfn = ActiveNtfn badge \<and>
             badge_val = badge)))"

definition
  valid_ep_obj_with_ntfn' :: "('a::state_ext) state \<Rightarrow> badge \<Rightarrow> bool"
where
  "valid_ep_obj_with_ntfn' s badge_val \<equiv>
     thread_cnode s (cur_thread s) \<noteq> None \<and>
     (\<exists> ref ep_badge rights.
       the (thread_cnode s (cur_thread s)) MICROKIT_INPUT_CAP =
         Some (EndpointCap ref ep_badge rights) \<and>
       AllowRead \<in> rights) \<and>
     (\<exists>ntfnptr. bound_notification s (cur_thread s) = Some ntfnptr) \<and>
     (\<forall>ntfnptr. bound_notification s (cur_thread s) = Some ntfnptr \<longrightarrow>
       (\<exists>ntfn badge.
         ko_at (Notification ntfn) ntfnptr s \<and>
         ntfn_obj ntfn = ActiveNtfn badge \<and>
         badge_val = badge))"

lemma valid_ep_obj_with_ntfn':
  "valid_objs s \<Longrightarrow> valid_ep_obj_with_ntfn' s badge \<equiv> valid_ep_obj_with_ntfn s badge"
  apply(rule eq_reflection)
  apply(rule iffI)
   unfolding valid_ep_obj_with_ntfn_def valid_ep_obj_with_ntfn'_def
     thread_cnode_def thread_cnode_cap_def bound_notification_def
   apply(clarsimp split:option.splits cap.splits kernel_object.splits if_splits)
   apply(rename_tac cn_obj x11 x12 ref ep_badge rights ntfnptr ntfn)
   apply(rule_tac x=ref in exI)
   apply(rule_tac x=ep_badge in exI)
   apply(rule_tac x=rights in exI)
   apply clarsimp
   apply(rule conjI)
    apply(clarsimp simp:cte_wp_at_def)
    apply(clarsimp simp:valid_objs_def valid_obj_def)
    apply(frule_tac x=cn_obj in bspec)
     apply blast
    apply clarsimp
    apply(clarsimp simp:valid_cs_def valid_cap_def)
    apply(drule_tac x="EndpointCap ref ep_badge rights" in bspec)
     apply blast
    apply(clarsimp simp:valid_cs_size_def)
    apply(clarsimp simp:get_cap_def thread_cnode_def thread_cnode_cap_def
      get_object_def bind_def gets_def get_def return_def assert_def valid_cs_size_def
      split:cap.split option.split kernel_object.split prod.split)
   apply(rule conjI)
    apply(smt (verit, del_insts) bind_eq_Some_conv pred_tcb_def2)
   apply clarsimp
   apply(metis (mono_tags, lifting) bind.bind_lunit pred_tcb_def2 tcb_to_itcb_simps(5))
  apply clarsimp
  apply(rename_tac ref ep_badge rights ntfnptr)
  apply(rule conjI)
   apply(clarsimp simp:cte_wp_at_cases2 split:option.splits cap.splits)
  apply(rule conjI)
   apply(metis (mono_tags, lifting) bind.bind_lunit pred_tcb_def2 tcb_to_itcb_simps(5))
  apply clarsimp
  apply(metis (mono_tags) bind.bind_lunit option.simps(1) pred_tcb_def2 tcb_to_itcb_simps(5))
  done

definition
  valid_ep_obj_with_ntfn'' :: "('a::state_ext) state \<Rightarrow> badge \<Rightarrow> bool"
where
  "valid_ep_obj_with_ntfn'' s badge_val \<equiv>
     thread_cnode s (cur_thread s) \<noteq> None \<and>
     \<comment> \<open>Microkit only checks notifications via EndpointCap, not via any standalone NotificationCap\<close>
     (\<exists> ref ep_badge rights.
       the (thread_cnode s (cur_thread s)) MICROKIT_INPUT_CAP =
         Some (EndpointCap ref ep_badge rights) \<and>
       AllowRead \<in> rights) \<and>
     ntfn_to_recv s (bound_notification s (cur_thread s)) =
       Some badge_val"

lemma valid_ep_obj_with_ntfn'':
  "valid_ep_obj_with_ntfn'' s badge \<equiv> valid_ep_obj_with_ntfn' s badge"
  apply(rule eq_reflection)
  apply(rule iffI)
   unfolding valid_ep_obj_with_ntfn''_def valid_ep_obj_with_ntfn'_def
     thread_cnode_def bound_notification_def ntfn_to_recv_def
   apply(clarsimp simp:obj_at_def split:option.splits kernel_object.splits ntfn.splits)
  apply(clarsimp simp:obj_at_def)
  done

lemma valid_ep_obj_with_ntfn_final:
  "valid_objs s \<Longrightarrow> valid_ep_obj_with_ntfn'' s badge \<equiv> valid_ep_obj_with_ntfn s badge"
  apply(rule eq_reflection)
  using valid_ep_obj_with_ntfn'' valid_ep_obj_with_ntfn'
  by blast

lemma complete_signal_wp:
  "\<lbrace>\<lambda>s. ntfn_at ntfnptr s \<and>
     (\<forall>ntfn. obj_at ((=) (Notification ntfn)) ntfnptr s \<longrightarrow> ntfn_obj ntfn = ActiveNtfn badge)\<rbrace>
     complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. getRegister_ret s receiver badge_register = Some badge\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp split:option.splits if_splits kernel_object.splits RISCV64.user_context.splits
    simp:getRegister_ret_def get_tcb_def RISCV64_A.arch_tcb_context_get_def
      RISCV64_A.arch_tcb_context_set_def RISCV64.setRegister_def RISCV64.user_context.inject
      modify_def bind_def get_def put_def)
  done

lemma complete_signal_ntfn_at:
  "\<lbrace>\<lambda>s. ntfn_at ntfnptr s\<rbrace>
     complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. ntfn_at ntfnptr s\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  done

lemma complete_signal_thread_cnode:
  "complete_signal ntfnptr receiver
   \<lbrace>\<lambda>s. P (thread_cnode s t)\<rbrace>"
  unfolding thread_cnode_def thread_cnode_cap_def
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp split:option.splits if_splits kernel_object.splits RISCV64.user_context.splits
    simp:getRegister_ret_def get_tcb_def RISCV64_A.arch_tcb_context_get_def
      RISCV64_A.arch_tcb_context_set_def RISCV64.setRegister_def RISCV64.user_context.inject
      modify_def bind_def get_def put_def)
  by (fastforce simp:tcb_cnode_map_def split:cap.splits option.splits if_splits kernel_object.splits)

lemma complete_signal_bound_notification:
  "complete_signal ntfnptr receiver \<lbrace>\<lambda>s. P (bound_notification s t)\<rbrace>"
  unfolding bound_notification_def
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp split:option.splits if_splits kernel_object.splits RISCV64.user_context.splits
    simp:getRegister_ret_def get_tcb_def RISCV64_A.arch_tcb_context_get_def
      RISCV64_A.arch_tcb_context_set_def RISCV64.setRegister_def RISCV64.user_context.inject
      modify_def bind_def get_def put_def)
  apply force
  done

lemma complete_signal_active_to_idle:
  "\<lbrace>\<lambda>s. bound_notification s receiver = Some ntfnptr\<rbrace>
     complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. bound_notification s receiver = Some ntfnptr \<and>
      (\<forall>ntfn. obj_at ((=) (Notification ntfn)) ntfnptr s \<longrightarrow> ntfn_obj ntfn = IdleNtfn)\<rbrace>"
  unfolding bound_notification_def
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  by (clarsimp split:option.splits if_splits kernel_object.splits RISCV64.user_context.splits
    simp:getRegister_ret_def get_tcb_def RISCV64_A.arch_tcb_context_get_def
      RISCV64_A.arch_tcb_context_set_def RISCV64.setRegister_def RISCV64.user_context.inject
      modify_def bind_def get_def put_def)

lemma complete_signal_ntfn_to_recv:
  "\<lbrace>\<lambda>s. (\<exists>badge. ntfn_to_recv s (bound_notification s receiver) = Some badge) \<and>
     bound_notification s receiver = Some ntfnptr\<rbrace>
     complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. ntfn_to_recv s (bound_notification s receiver) = None\<rbrace>"
  unfolding ntfn_to_recv_def
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
    complete_signal_bound_notification)
    apply(wpsimp simp:complete_signal_def)
      apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
     apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
    apply(wpsimp wp:get_simple_ko_wp)
   apply(wpsimp wp:complete_signal_bound_notification)
  apply fastforce
  done

lemma complete_signal_ppc_to_recv_None:
  "\<lbrace>\<lambda>s. ppc_to_recv s (thread_cnode s receiver) = None\<rbrace>
     complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. ppc_to_recv s (thread_cnode s receiver) = None\<rbrace>"
  unfolding ppc_to_recv_def
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
    complete_signal_thread_cnode)
   apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp split:option.splits if_splits kernel_object.splits RISCV64.user_context.splits
      cap.splits bool.splits endpoint.splits
    simp:getRegister_ret_def get_tcb_def RISCV64_A.arch_tcb_context_get_def
      RISCV64_A.arch_tcb_context_set_def RISCV64.setRegister_def RISCV64.user_context.inject
      modify_def bind_def get_def put_def)
  (* XXX: might be needed when we reintroduce other fields into KO_PPCall
  apply(clarsimp split:list.splits thread_state.splits)
  apply(fastforce simp:get_message_info_ret_def get_tcb_rev
    split:option.splits kernel_object.splits thread_state.splits RISCV64.user_context.splits) *)
  done

(* NB: Probably only expect this to work while we have the simplified definition
   of recv_oracle that merely checks if the Endpoint is in SendEP mode. *)
lemma complete_signal_ppc_to_recv:
  "\<lbrace>\<lambda>s. P (ppc_to_recv s (thread_cnode s receiver))\<rbrace>
     complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. P (ppc_to_recv s (thread_cnode s receiver))\<rbrace>"
  unfolding ppc_to_recv_def
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
    complete_signal_thread_cnode)
   apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp split:option.splits if_splits kernel_object.splits RISCV64.user_context.splits
      cap.splits bool.splits endpoint.splits list.splits
    simp:getRegister_ret_def get_tcb_def RISCV64_A.arch_tcb_context_get_def
      RISCV64_A.arch_tcb_context_set_def RISCV64.setRegister_def RISCV64.user_context.inject
      modify_def bind_def get_def put_def
      thread_cnode_def thread_cnode_cap_def tcb_cnode_map_def get_tcb_rev)
  apply((rule conjI | clarsimp)+, blast)
  apply((rule conjI | clarsimp)+, metis Some_helper)+
  done

lemma complete_signal_input_ep_status:
  "\<lbrace>\<lambda>s. P (input_ep_status s (thread_cnode s receiver))\<rbrace>
     complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. P (input_ep_status s (thread_cnode s receiver))\<rbrace>"
  unfolding input_ep_status_def
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
    complete_signal_thread_cnode)
   apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp split:option.splits if_splits kernel_object.splits RISCV64.user_context.splits
      cap.splits bool.splits endpoint.splits list.splits
    simp:getRegister_ret_def get_tcb_def RISCV64_A.arch_tcb_context_get_def
      RISCV64_A.arch_tcb_context_set_def RISCV64.setRegister_def RISCV64.user_context.inject
      modify_def bind_def get_def put_def
      thread_cnode_def thread_cnode_cap_def tcb_cnode_map_def get_tcb_rev)
  apply((rule conjI | clarsimp)+, blast)
  apply((rule conjI | clarsimp)+, metis Some_helper)+
  done

lemma complete_signal_vs_lookup:
  "complete_signal ntfnptr receiver \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply clarsimp
  done

(* only bring these in when strictly needed *)
declare if_split [split del]
declare imp_disjL [simp del]

lemma complete_signal_ptes_of_some:
  "\<lbrace>\<lambda>s. (\<exists>y. (RISCV64_A.ptes_of s) x = Some y)\<rbrace>
    complete_signal ntfnptr receiver
   \<lbrace>\<lambda>r s. \<exists>y. (RISCV64_A.ptes_of s) x = Some y\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply(wpsimp wp:hoare_vcg_all_lift)
  apply(rule_tac x=y in exI)
  apply(clarsimp simp:RISCV64_A.pte_of_def)
  apply(clarsimp simp:obind_def opt_map_def aobj_of_def obj_at_def get_tcb_def)
  apply(fastforce split:option.splits if_splits kernel_object.splits)
  done

lemma complete_signal_ptes_of_not_some:
  "\<lbrace>\<lambda>s. (RISCV64_A.ptes_of s) x \<noteq> Some y\<rbrace>
    complete_signal ntfnptr receiver
   \<lbrace>\<lambda>r s. (RISCV64_A.ptes_of s) x \<noteq> Some y\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply(wpsimp wp:hoare_vcg_all_lift)
  apply(clarsimp simp:RISCV64_A.pte_of_def)
  apply(clarsimp simp:obind_def opt_map_def aobj_of_def obj_at_def get_tcb_def)
  apply(fastforce split:option.splits if_splits kernel_object.splits)
  done

lemma complete_signal_ptes_of_none:
  "\<lbrace>\<lambda>s. (RISCV64_A.ptes_of s) x = None\<rbrace>
    complete_signal ntfnptr receiver
   \<lbrace>\<lambda>r s. (RISCV64_A.ptes_of s) x = None\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply(wpsimp wp:hoare_vcg_all_lift)
  apply(clarsimp simp:RISCV64_A.pte_of_def)
  apply(clarsimp simp:obind_def opt_map_def aobj_of_def obj_at_def get_tcb_def)
  apply(fastforce split:option.splits if_splits kernel_object.splits)
  done

lemma complete_signal_gta:
  "\<lbrace>\<lambda>s. P (get_asid_of_thread (kheap s) (arch_state s) t)\<rbrace>
     complete_signal ntfnptr receiver 
   \<lbrace>\<lambda>rv s. P (get_asid_of_thread (kheap s) (arch_state s) t)\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply(wpsimp wp:hoare_vcg_all_lift)
  apply(force simp:get_asid_of_thread_def obj_at_def get_tcb_def RISCV64_A.arch_cap.simps
    split:if_splits option.splits kernel_object.splits cap.splits RISCV64_A.arch_cap.splits)
  done

lemma complete_signal_not_tcb_at:
  "complete_signal ntfnptr receiver \<lbrace>\<lambda>s. \<not> tcb_at t s\<rbrace>"
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply(clarsimp simp:tcb_at_def get_tcb_def split:if_splits)
  done

lemma complete_signal_tcb_at:
  "complete_signal ntfnptr tcb \<lbrace>\<lambda>s. P (tcb_at p s)\<rbrace>"
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

lemma complete_signal_vs_lookup_rights:
  "\<lbrace>\<lambda>s. P (vs_lookup_rights s t a)\<rbrace>
   complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. P (vs_lookup_rights s t a)\<rbrace>"
  unfolding vs_lookup_rights_def
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:complete_signal_gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:complete_signal_vs_lookup)
    apply(wpsimp wp:complete_signal_gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:complete_signal_ptes_of_some)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:complete_signal_vs_lookup)
    apply(wpsimp wp:complete_signal_gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:complete_signal_ptes_of_not_some)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:complete_signal_vs_lookup)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:complete_signal_gta)
   apply(clarsimp split:if_splits)
   apply(wpsimp wp:complete_signal_tcb_at)
  apply(rule context_conjI)
   apply clarsimp
  apply clarsimp
  apply(rule context_conjI)
   apply clarsimp
   apply(metis not_Some_eq surj_pair)
  apply(clarsimp split:if_splits)
  apply blast
  done

lemma complete_signal_vs_lookup_rights_general:
  "ntfnptr \<noteq> receiver \<Longrightarrow>
   \<lbrace>\<lambda>s. P (vs_lookup_rights s t)\<rbrace>
   complete_signal ntfnptr receiver
   \<lbrace>\<lambda>_ s. P (vs_lookup_rights s t)\<rbrace>"
  unfolding vs_lookup_rights_def
  apply(rule_tac P=P in hoare_liftP_ext)
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:complete_signal_gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:complete_signal_vs_lookup)
    apply(wpsimp wp:complete_signal_gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_conj_lift)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:complete_signal_ptes_of_some)
    apply(wpsimp wp:hoare_vcg_imp_lift)
     apply(wpsimp wp:complete_signal_vs_lookup)
    apply(wpsimp wp:complete_signal_gta)
   apply(wpsimp wp:hoare_vcg_all_lift)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:complete_signal_ptes_of_not_some)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:complete_signal_vs_lookup)
   apply(wpsimp wp:hoare_vcg_imp_lift)
    apply(wpsimp wp:complete_signal_gta)
   apply(wpsimp wp:complete_signal_tcb_at)
  apply clarsimp
  apply(rule context_conjI)
   apply clarsimp
   apply force
  apply clarsimp
  apply(metis not_Some_eq)
  done

lemma complete_signal_cur_thread:
  "complete_signal ntfnptr receiver \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
  unfolding complete_signal_def
  apply wpsimp
   apply(wpsimp wp:get_simple_ko_wp)
  apply blast
  done

lemma complete_signal_cur_thread_mapped_writable''':
  "ntfnptr \<noteq> t \<Longrightarrow> ntfnptr \<noteq> receiver \<Longrightarrow>
   \<lbrace>\<lambda>s. P (vs_lookup_rights s t) \<and>
      t = (cur_thread s)\<rbrace> complete_signal ntfnptr receiver 
   \<lbrace>\<lambda>_ s. P (vs_lookup_rights s t) \<and>
      t = (cur_thread s)\<rbrace>"
  find_theorems complete_signal cur_thread
  apply(wpsimp wp:complete_signal_cur_thread complete_signal_vs_lookup_rights_general)
  done

lemma complete_signal_mapped_writable_general:
  "ntfnptr \<noteq> t \<Longrightarrow> ntfnptr \<noteq> receiver \<Longrightarrow>
   \<lbrace>\<lambda>s. P (mapped_writable s t) \<and>
      t = (cur_thread s)\<rbrace>
   complete_signal ntfnptr receiver
   \<lbrace>\<lambda>r s. P (mapped_writable s t) \<and>
      t = (cur_thread s)\<rbrace>"
  unfolding mapped_writable_def
  by (wpsimp wp:complete_signal_cur_thread_mapped_writable''' hoare_strengthen_post)

lemma complete_signal_not_writable_others_general:
  "ntfnptr \<noteq> receiver \<Longrightarrow>
   \<lbrace>\<lambda>s. ntfn_at ntfnptr s \<and> tcb_at t s \<and> P (not_writable_others s t) \<and>
     t = cur_thread s\<rbrace>
   complete_signal ntfnptr receiver
   \<lbrace>\<lambda>r s. P (not_writable_others s t) \<and>
     t = cur_thread s\<rbrace>"
  apply(wp not_writable_others_lift[where Q="ntfn_at ntfnptr"])
    apply(wp only:complete_signal_vs_lookup_rights)
    apply clarsimp
   apply(wpsimp wp:complete_signal_cur_thread)
  apply clarsimp
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
  by (clarsimp split:cap.splits RISCV64_A.arch_cap.splits bool.splits simp:RISCV64_A.arch_cap.simps)

lemma set_object_P_obj_at[wp]:
  "\<lbrace>\<lambda>s. P (obj_at P' p (if p = p' then
      (s\<lparr>kheap := (kheap s)(p' \<mapsto> new_obj)\<rparr>)
      else s))\<rbrace> set_object p' new_obj \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  by (wpsimp wp:set_object_wp crunch_wps simp:obj_at_def split:if_splits)

lemma set_simple_ko_P_obj_at[wp]:
  "\<lbrace>\<lambda>s. P (obj_at P' p (if p = p' then
      (s\<lparr>kheap := (kheap s)(p' \<mapsto> f ep)\<rparr>)
      else s))\<rbrace> set_simple_ko f p' ep \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  by (wpsimp wp:set_object_P_obj_at simp:set_simple_ko_def get_object_def)

lemma set_thread_state_P_obj_at[wp]:
  "\<lbrace>\<lambda>s. P (obj_at P' p (if p = p' then
      (s\<lparr>kheap := (kheap s)(p' \<mapsto> TCB (un_TCB (the (kheap s p'))\<lparr>tcb_state := ts\<rparr>))\<rparr>)
      else s))\<rbrace> set_thread_state p' ts \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  by (wpsimp simp:set_thread_state_def get_tcb_def wp:dxo_wp_weak
    split:option.splits if_splits kernel_object.splits)

lemma set_bound_notification_P_obj_at[wp]:
  "\<lbrace>\<lambda>s. P (obj_at P' p (if p = p' then
      (s\<lparr>kheap := (kheap s)(p' \<mapsto> TCB (un_TCB (the (kheap s p'))\<lparr>tcb_bound_notification := ntfn\<rparr>))\<rparr>)
      else s))\<rbrace> set_bound_notification p' ntfn \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  by (wpsimp simp:set_bound_notification_def get_tcb_def
    split:option.splits if_splits kernel_object.splits)

lemma resolve_address_bits'_specific:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
     valid_cap (fst args) s \<and>
     (\<exists>cn_ref sz_bits guard. fst args = CNodeCap cn_ref sz_bits guard \<and>
       length (snd args) = sz_bits + size guard \<and>
       microkit_pd_bits_guard sz_bits guard \<and>
       \<comment> \<open>the guard is a prefix of the raw 64-bit list given via the args\<close>
       guard \<le> snd args \<and>
       cte_wp_at ((=) mycap) (cn_ref, drop (size guard) (snd args)) s)\<rbrace>
     resolve_address_bits' z args
   \<lbrace>\<lambda>rv s. \<exists>cn_ref. cte_wp_at ((=) mycap) (fst rv) s \<and>
      fst rv = (cn_ref, drop (size MICROKIT_PD_CAP_GUARD) (snd args))\<rbrace>,
   \<lbrace>\<lambda>rv s. False\<rbrace>"
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
    apply(rule conjI)
     apply (clarsimp simp add: in_monad Let_def)
     apply(force simp:fail_def in_returnOk split:if_splits)
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
    (* for microkit caps, we don't hit the other cases *)
    apply(clarsimp simp:in_monad)
    done
qed

lemma lookup_slot_specific:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
     valid_cap (tcb_ctable (the (get_tcb t s))) s \<and>
     (\<exists>cn_ref sz_bits guard. (tcb_ctable (the (get_tcb t s))) = CNodeCap cn_ref sz_bits guard \<and>
       length c = sz_bits + size guard \<and>
       microkit_pd_bits_guard sz_bits guard \<and>
       guard \<le> c \<and>
       cte_wp_at ((=) mycap) (cn_ref, drop (size guard) c) s)\<rbrace>
   lookup_slot_for_thread t c
   \<lbrace>\<lambda>rv s. \<exists>cn_ref. cte_wp_at ((=) mycap) (fst rv) s \<and>
      fst rv = (cn_ref, drop (size MICROKIT_PD_CAP_GUARD) c)\<rbrace>,
   \<lbrace>\<lambda>rv s. False\<rbrace>"
  unfolding lookup_slot_for_thread_def resolve_address_bits_def
  by (wpsimp wp:resolve_address_bits'_specific [where mycap=mycap,THEN hoare_strengthen_postE])

lemma lookup_cap_specific:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
    valid_cap (tcb_ctable (the (get_tcb t s))) s \<and>
    (\<exists>cn_ref sz_bits guard. (tcb_ctable (the (get_tcb t s))) = CNodeCap cn_ref sz_bits guard \<and>
      length c = sz_bits + size guard \<and>
      microkit_pd_bits_guard sz_bits guard \<and>
      guard \<le> c \<and>
      cte_wp_at ((=) mycap) (cn_ref, drop (size guard) c) s)\<rbrace>
     lookup_cap t c
   \<lbrace>\<lambda>rv s. \<exists>cn_ref. cte_wp_at ((=) mycap and (=) rv)
      (cn_ref, drop (size MICROKIT_PD_CAP_GUARD) c) s\<rbrace>,
   \<lbrace>\<lambda>rv s. False\<rbrace>"
  unfolding lookup_cap_def fun_app_def split_def
  apply(rule hoare_pre)
   apply wpsimp
    apply(rule_tac P="\<exists>cn_ref. (cn_ref, drop (size MICROKIT_PD_CAP_GUARD) c) = (a, b)"
      in hoare_gen_asm)
    apply(wpsimp wp:get_cap_cte_wp_at_rv[THEN hoare_strengthen_post])
    apply(rule_tac x=a in exI)
    apply assumption
   apply(wpsimp wp:lookup_slot_specific[where mycap=mycap,THEN hoare_strengthen_postE])
  apply clarsimp
  done

lemma lookup_cap_specific_invE:
  "\<lbrace>\<lambda>s. valid_objs s \<and>
    valid_cap (tcb_ctable (the (get_tcb t s))) s \<and>
    (\<exists>cn_ref sz_bits guard. (tcb_ctable (the (get_tcb t s))) = CNodeCap cn_ref sz_bits guard \<and>
      length c = sz_bits + size guard \<and>
      microkit_pd_bits_guard sz_bits guard \<and>
      guard \<le> c \<and>
      cte_wp_at ((=) mycap) (cn_ref, drop (size guard) c) s) \<and>
    P s\<rbrace> lookup_cap t c
   \<lbrace>\<lambda>r s. P s \<and> (\<exists>cn_ref. cte_wp_at ((=) mycap and (=) r)
      (cn_ref, drop (size MICROKIT_PD_CAP_GUARD) c) s)\<rbrace>,
   \<lbrace>\<lambda>_ _. False\<rbrace>"
  apply(wp only:hoare_vcg_conj_liftE1)
    apply(wpsimp wp:lookup_cap_inv)
   apply(wpsimp wp:lookup_cap_specific)
  apply clarsimp
  done

lemma hoare_absorb_impE_R:
  "\<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,- \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s\<rbrace>,-"
  using hoare_strengthen_postE_R by fastforce

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

lemma complete_signal_ntfn_status'_general:
  "\<lbrace>\<lambda>s. P (ntfn_status' (if \<exists>ntfn.
        p = ntfnptr \<and>
        kheap s ntfnptr = Some (Notification ntfn) \<and>
        isActive ntfn
      then (s\<lparr>kheap := (kheap s)(ntfnptr \<mapsto> Notification
        (un_Notification (the (kheap s ntfnptr))\<lparr>ntfn_obj := IdleNtfn\<rparr>))\<rparr>)
      else s) p)\<rbrace>
    complete_signal ntfnptr t
   \<lbrace>\<lambda>_ s. P (ntfn_status' s p)\<rbrace>"
  unfolding ntfn_status'_def
  apply(wpsimp simp:complete_signal_def)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp wp:as_user_wp_thread_set_helper set_object_wp simp:thread_set_def)
   apply(wpsimp wp:get_simple_ko_wp)
  apply(clarsimp simp:obj_at_def ntfn_of_ch_def)
  apply(clarsimp split:option.split kernel_object.split if_split ntfn.split
    simp:get_tcb_def isActive_def)
  apply(fastforce split:option.splits kernel_object.splits if_splits ntfn.splits)
  done

lemma complete_signal_ntfn_status_general:
  "\<lbrace>\<lambda>s. P (ntfn_status (if \<exists>ntfn badge.
        kheap s ntfnptr = Some (Notification ntfn) \<and>
        ntfn_obj ntfn = ActiveNtfn badge
      then (s\<lparr>kheap := (kheap s)(ntfnptr \<mapsto> Notification
        (un_Notification (the (kheap s ntfnptr))\<lparr>ntfn_obj := IdleNtfn\<rparr>))\<rparr>)
      else s) (thread_cnode s t) x)\<rbrace>
    complete_signal ntfnptr t
   \<lbrace>\<lambda>rv s. P (ntfn_status s (thread_cnode s t) x)\<rbrace>"
  unfolding ntfn_status_def ntfn_of_ch_def
  apply(clarsimp split:option.splits)
  apply(wpsimp wp:hoare_vcg_op_lift complete_signal_thread_cnode)
   apply(wpsimp wp:complete_signal_ntfn_status'_general)
  apply clarsimp
  apply(rename_tac s xa xaa xb)
  apply(erule_tac x=xa in allE)
  apply clarsimp
  apply(clarsimp simp:isActive_def)
  apply(clarsimp split:if_splits)
   apply(rule conjI)
    apply clarsimp
   apply(fastforce simp:ntfn_status'_def split:option.splits if_splits kernel_object.splits)
  apply(fastforce split:ntfn.splits)
  done

(* A new liftP helper that allows the monad m's modifications g to the state, too *)
lemma hoare_liftP_ext'':
  assumes "\<And>P x. \<lbrace>\<lambda>s. P (f (g s) x)\<rbrace> m \<lbrace>\<lambda>_ s. P (f s x)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (f (g s))\<rbrace> m \<lbrace>\<lambda>_ s. P (f s)\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (erule subst[rotated, where P=P])
  apply (rule ext)
  apply (drule use_valid, rule assms, rule refl)
  apply simp
  done

lemma hoare_liftP_ext''':
  assumes "\<And>P x. \<lbrace>\<lambda>s. P (f (g s) (h s) x)\<rbrace> m \<lbrace>\<lambda>_ s. P (f s (h s) x)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (f (g s) (h s))\<rbrace> m \<lbrace>\<lambda>_ s. P (f s (h s))\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (erule subst[rotated, where P=P])
  apply (rule ext)
  apply (drule use_valid, rule assms, rule refl)
  apply simp
  done

lemma complete_signal_ntfn_status:
  "\<lbrace>\<lambda>s. P (ntfn_status (if \<exists>ntfn badge.
        kheap s ntfnptr = Some (Notification ntfn) \<and>
        ntfn_obj ntfn = ActiveNtfn badge
      then (s\<lparr>kheap := (kheap s)(ntfnptr \<mapsto> Notification
        (un_Notification (the (kheap s ntfnptr))\<lparr>ntfn_obj := IdleNtfn\<rparr>))\<rparr>)
      else s) (thread_cnode s t))\<rbrace>
    complete_signal ntfnptr t
   \<lbrace>\<lambda>rv s. P (ntfn_status s (thread_cnode s t))\<rbrace>"
  apply(rule_tac P=P in hoare_liftP_ext''')
  apply(wpsimp wp:complete_signal_ntfn_status_general)
  done

lemma delete_null_caller_cap:
   "\<lbrace>\<lambda>s. P s \<and> (\<exists>tcb. ko_at (TCB tcb) t s \<and> tcb_caller tcb = NullCap)\<rbrace>
    delete_caller_cap t \<lbrace>\<lambda>_ s. P s\<rbrace>"
  unfolding delete_caller_cap_def cap_delete_one_def
  apply wpsimp
      apply(wpsimp wp:hoare_pre_cont)
     apply(wpsimp wp:hoare_pre_cont)
    apply(wpsimp wp:hoare_pre_cont)
   apply(wpsimp wp:get_cap_wp)
  by (clarsimp simp:obj_at_def cte_wp_at_def tcb_cnode_map_def get_cap_def bind_def get_object_def
    gets_def get_def return_def)

lemma thread_cnode_ntfn_upd_agnostic:
  "kheap s x = Some (Notification ntfn) \<Longrightarrow>
   thread_cnode (s\<lparr>kheap := (kheap s)(x \<mapsto> Notification (ntfn_set_obj ntfn IdleNtfn))\<rparr>) t =
   thread_cnode s t"
  apply(clarsimp simp:thread_cnode_def thread_cnode_cap_def get_tcb_def
    split:if_splits option.splits kernel_object.splits cap.splits)
  done

(* XXX: Just pulling this file in for the resolve_address_bits lemmas. Not refurbishing the below.
lemma handle_SysRecv_syscall_notification:
  "\<lbrace>\<lambda>s. invs s \<and>
      tcb_at receiver s \<and>
      receiver = cur_thread s \<and>
      (\<exists>tcb. ko_at (TCB tcb) receiver s \<and> tcb_caller tcb = NullCap \<and> tcb_state tcb = Running) \<and>
      valid_ep_obj_with_ntfn s badge_val \<and>
      \<comment> \<open>Rule out PPCs from consideration for now\<close>
      ppc_to_recv s cnode = None \<and>
      \<comment> \<open>That the user has provided MICROKIT_INPUT_CAP_WORD in the cap_register\<close>
      the (getRegister_ret s receiver cap_register) = MICROKIT_INPUT_CAP_WORD \<and>
      cnode = thread_cnode s receiver \<and>
      bound_notif = bound_notification s receiver \<and>
      ntfn_st = ntfn_status s cnode \<and>
      ppc_tr = ppc_to_recv s cnode \<and>
      iep_st = input_ep_status s cnode \<and>
      not_wr_others = not_writable_others s (cur_thread s) \<and>
      mapped_wr = mapped_writable s (cur_thread s)\<rbrace>
    handle_recv True
   \<lbrace>\<lambda> _ s. \<comment> \<open>notification reqs on successful complete_signal\<close>
      getRegister_ret s receiver badge_register = Some badge_val \<and>
      ntfn_to_recv s (bound_notification s receiver) = None \<and>
      ppc_to_recv s (thread_cnode s receiver) = None \<and>
      cnode = thread_cnode s receiver \<and>
      bound_notif = bound_notification s receiver \<and>
      ntfn_st = ntfn_status s (thread_cnode s receiver) \<and>
      ppc_tr = ppc_to_recv s (thread_cnode s receiver) \<and>
      iep_st = input_ep_status s (thread_cnode s receiver) \<and>
      not_wr_others = not_writable_others s (cur_thread s) \<and>
      mapped_wr = mapped_writable s (cur_thread s) \<and>
      receiver = cur_thread s\<rbrace>"
  unfolding handle_recv_def
  apply wp
      apply(wp only:hoare_pre_cont)
     apply simp
     apply(wp only:cap_fault_wp)
     (* Note: if we call wpsimp at this point we're dead because False ends up in the
        postcondition of the lookup_cap lemma, so instead carefully split on the cases *)
      apply(simp add:Let_def)
      apply(wp only:hoare_vcg_split_ep_capE)
       apply(wpsimp simp:receive_ipc_def)
            apply(rename_tac tcb ep_cptr ep_cap ref badge rights ep rva ntfnptr)
            apply(rule_tac P="ntfnptr \<noteq> receiver \<and> tcb = receiver"
              in hoare_gen_asm)
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_wp)
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_ntfn_to_recv)
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_ppc_to_recv)
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_thread_cnode)
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_bound_notification)
            apply wpsimp
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_ntfn_status)
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_ppc_to_recv)
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_input_ep_status)
            apply(wpsimp wp:hoare_vcg_conj_lift)
             apply(wpsimp wp:complete_signal_not_writable_others_general[where t=receiver,THEN hoare_strengthen_post])
             apply assumption
            apply(wpsimp wp:complete_signal_mapped_writable_general[where t=receiver,THEN hoare_strengthen_post])
            apply assumption
           apply clarsimp
           apply(rename_tac tcb x xa ep_ptr badge rights rv ntfnptr ntfn)
           apply(wp only:hoare_pre_cont)
          apply clarsimp
          apply(rename_tac x xa ep_ptr badge rights rv ntfnptr)
          apply(rule_tac P="\<not> (ntfnptr = None)" in hoare_gen_asm)
          apply(wpsimp wp:get_simple_ko_wp)
         apply(wpsimp wp:gbn_wp)
        apply(wp only:get_simple_ko_wp)
      (* This delete_caller_cap immediately precedes the call to receive_ipc in handle_recv.
         Originally I proved a bunch of lemmas to show that most of the predicates in
         the postcondition are unaffected by delete_caller_cap - these are archived in
         MSpecDeleteCaller_AI.thy now. *)
       apply(wpsimp wp:hoare_absorb_imp simp:ko_at_ep_at)
       (* Instead we assume for now that there is no caller cap to delete. We'll have to
          revisit this once we add support for Microkit PPCs, which use seL4 IPC calls *)
       apply(wpsimp wp:delete_null_caller_cap)
      apply wpsimp
     (* Note: Again, if we call wpsimp here we're dead because False ends up in the
        postcondition of a later goal - so we don't. *)
     apply(rename_tac thread ref)
     apply(wp only:hoare_vcg_ex_liftE)
     apply(rename_tac thread ref ep_ptr badge rights)
    (* That lookup_cap succeeds for our EndpointCap *)
     apply(rule_tac mycap1="EndpointCap ep_ptr badge rights" and c1="ref"
       in lookup_cap_specific_invE[THEN hoare_strengthen_postE])
      apply(clarsimp simp:cte_wp_at_def)
      apply assumption
     apply clarsimp
    apply(wpsimp simp:comp_def wp:hoare_vcg_ex_lift)
     apply(wpsimp wp:getRegister_ret_valid[THEN hoare_strengthen_post,simplified])
     apply(clarsimp simp:getRegister_ret_def)
     apply(case_tac "kheap s thread"; clarsimp)
     apply(rename_tac thread x xa xb cn_ref rv s a)
     apply(case_tac a; clarsimp)
     apply(clarsimp simp:RISCV64_A.arch_tcb_context_get_def)
     apply(subgoal_tac "rv = RISCV64.user_regs (RISCV64_A.tcb_context (tcb_arch x2)) cap_register")
      apply clarsimp
      apply(subgoal_tac "x2 = un_TCB (the (kheap s thread))")
       apply clarify
       apply assumption
      apply clarsimp
     apply clarsimp
     apply(clarsimp simp:RISCV64.user_context.sel split:RISCV64.user_context.splits)
    apply(wpsimp wp:getRegister_ret_valid[THEN hoare_strengthen_post])
   apply wpsimp
  (* Okay. We're finally at the point where we can try to line up the wp-derived precondition
     with the precondition for the overall Hoare triple. *)
  apply wpsimp
  apply(frule invs_valid_objs)
  apply(clarsimp simp:valid_ep_obj_with_ntfn'_def valid_ep_obj_with_ntfn'[symmetric]
    split:option.splits cap.splits)
  apply(rule context_conjI)
   apply(rule objs_valid_tcb_ctable[where t=receiver])
    apply blast
   apply(clarsimp simp:get_tcb_def tcb_at_def split:option.splits)
  apply(rename_tac s tcb y ref ep_badge rights ntfnptr ntfn)
  apply(rule_tac x=ref in exI)
  apply(rule_tac x=ep_badge in exI)
  apply(rule_tac x=rights in exI)
  apply(clarsimp simp:tcb_at_def pred_tcb_at_def get_tcb_def getRegister_ret_def
    split:option.splits kernel_object.splits RISCV64.user_context.splits)
  apply(clarsimp split:RISCV64.user_context.splits
    simp:getRegister_ret_def RISCV64_A.arch_tcb_context_get_def RISCV64.user_regs_def)
  apply(clarsimp simp:thread_cnode_def thread_cnode_cap_def get_tcb_rev split:cap.splits)
  apply(clarsimp split:option.splits kernel_object.splits if_splits)
  apply(rename_tac s tcb y ref ep_badge rights ntfnptr ntfn tcba x1 x2b x1a x2 cn_ref sz)
  apply(subgoal_tac "valid_cs sz (the cnode) s")
   prefer 2
   apply(clarsimp simp:valid_objs_def valid_obj_def)
   apply(frule_tac x=cn_ref in bspec)
    apply blast
   apply clarsimp
  apply(clarsimp simp:valid_cs_def valid_cap_def)
  apply(clarsimp simp:valid_cs_size_def)
  apply(rename_tac s tcb y ref ep_badge rights ntfnptr ntfn tcba x1 x2b x1a x2 cn_ref sz)
  apply(clarsimp simp:cte_wp_at_def)
  apply(frule RISCV64.valid_objs_caps)
  apply(subgoal_tac "length MICROKIT_INPUT_CAP < word_bits - cte_level_bits")
   prefer 2
   using microkit_cap_bl_sz_valid MICROKIT_INPUT_CAP_def
   apply metis
  apply(drule_tac x="EndpointCap ref ep_badge rights" in bspec)
   apply blast
  apply clarsimp
  apply(clarsimp simp:well_formed_cnode_n_def)
  apply(subgoal_tac "MICROKIT_INPUT_CAP \<in> dom (the cnode)")
   prefer 2
   apply clarsimp
   apply blast
  apply(subgoal_tac "sz = length MICROKIT_INPUT_CAP")
   prefer 2
   apply(clarsimp simp:MICROKIT_INPUT_CAP_def MICROKIT_PD_CAP_BITS_def)
  apply(clarsimp simp:get_cap_def thread_cnode_def thread_cnode_cap_def get_tcb_def
    get_object_def bind_def gets_def get_def return_def assert_def valid_cs_size_def
    assert_opt_def fail_def
    split:cap.splits option.splits kernel_object.splits if_splits)
  apply(clarsimp simp:word_bits_def obj_at_def bound_notification_def get_tcb_def)
  apply(clarsimp simp:is_ntfn_def is_ep_def AllowRecv_def isActive_def)
  apply(clarsimp simp:is_cap_table_def)
  apply(simp add:RISCV64.user_context.simps(1))
  apply(clarsimp simp:MICROKIT_INPUT_CAP_def)
  apply(rule conjI)
   apply force
  apply(rule conjI)
   apply(clarsimp simp:MICROKIT_INPUT_CAP_WORD_def MICROKIT_PD_CAP_GUARD_def
     to_bl_def MICROKIT_PD_CAP_BITS_def)
  apply clarsimp
  apply(rename_tac s ref ep_badge rights ntfnptr ntfn tcba x2b x1a cn_ref ko x)
  apply(frule (3) tcb_bound_ntfn_bound_tcb)
  apply(rule conjI)
   apply clarsimp
   apply(rule conjI)
    apply(clarsimp simp:ntfn_to_recv_def bound_notification_def get_tcb_def split:option.splits)
   apply(rule conjI)
    apply(simp only:fun_upd_apply[symmetric])
    (* Intuitively, this should be true if the previous ntfn_status for the updated ntfn was
       ActiveNtfn and if that maps to the same KN_* value as IdleNtfn, which it's being set to.
       I updated ntfn_status' to make that true - KN_BoundTcbFree means "not blocked". *)
    apply(rule ext)
    apply(clarsimp simp:ntfn_status_def ntfn_of_ch_def ntfn_status'_def)
    apply(clarsimp split:option.splits)
    apply(simp only:fun_upd_apply[symmetric] thread_cnode_ntfn_upd_agnostic)
    apply(rule conjI)
     apply(clarsimp split:kernel_object.splits ntfn.splits option.splits if_splits cap.splits)
    apply clarsimp
    apply(rule conjI)
     apply(force split:kernel_object.splits ntfn.splits option.splits if_splits cap.splits)
    apply(clarsimp split:kernel_object.splits ntfn.split cap.splits)
    apply(fastforce split:kernel_object.split option.splits if_splits simp:receive_blocked_def)
   (* obviously the current thread can't be a notification *)
   apply fastforce
  apply clarsimp
  done

lemma handle_recv_microkit_notification:
  "\<lbrace>\<lambda>s. invs s \<and> valid_objs s \<and>
      receiver = cur_thread s \<and> tcb_at receiver s \<and>
      valid_ep_obj_with_ntfn'' s badge_val \<and>
      \<comment> \<open>Rule out PPCs from consideration for now\<close>
      ppc_to_recv s cnode = None \<and>
      the (getRegister_ret s receiver cap_register) = MICROKIT_INPUT_CAP_WORD \<and>
      (\<exists>tcb. ko_at (TCB tcb) receiver s \<and> tcb_caller tcb = NullCap \<and> tcb_state tcb = Running) \<and>
      cnode = thread_cnode s receiver \<and>
      bound_notif = bound_notification s receiver \<and>
      ntfn_st = ntfn_status s cnode \<and>
      ppc_tr = ppc_to_recv s cnode \<and>
      iep_st = input_ep_status s cnode \<and>
      mapped_wr = mapped_writable s (cur_thread s) \<and>
      not_wr_others = not_writable_others s (cur_thread s)
    \<rbrace> handle_recv True \<lbrace>\<lambda> _ s.
      receiver = cur_thread s \<and>
      getRegister_ret s receiver badge_register = Some badge_val \<and>
      cnode = thread_cnode s receiver \<and>
      bound_notif = bound_notification s receiver \<and>
      ntfn_to_recv s (bound_notification s receiver) = None \<and>
      ntfn_st = ntfn_status s (thread_cnode s receiver) \<and>
      ppc_tr = ppc_to_recv s (thread_cnode s receiver) \<and>
      iep_st = input_ep_status s (thread_cnode s receiver) \<and>
      mapped_wr = mapped_writable s (cur_thread s) \<and>
      not_wr_others = not_writable_others s (cur_thread s)\<rbrace>"
  apply(wpsimp simp:valid_ep_obj_with_ntfn_final
    wp:handle_SysRecv_syscall_notification hoare_strengthen_post)
   apply blast
  by (clarsimp simp:valid_ep_obj_with_ntfn_final obj_at_def)

lemma handle_recv_microkit_notification_pretty:
  "\<lbrace>\<lambda>s. invs s \<and>
      getRegister_ret s receiver cap_register = Some MICROKIT_INPUT_CAP_WORD \<and>
      \<comment> \<open>In the current thread’s CNode, this cptr must resolve to
         a valid endpoint cap with read rights.\<close>
      (\<exists>epptr. input_cap_configured (thread_cnode s receiver) epptr) \<and>
      \<comment> \<open>We assume (for now) a system where nobody makes synchronous IPC calls. Note that
        we will have to relax this assumption when we generalise to Microkit PPC support.\<close>
      (\<exists>tcb. ko_at (TCB tcb) receiver s \<and> tcb_caller tcb = NullCap \<and> tcb_state tcb = Running) \<and>
      \<comment> \<open>There must be a notification to receive according to the receive oracle.\<close>
      ntfn_to_recv s (bound_notification s receiver) = Some badge_val \<and>
      ppc_to_recv s (thread_cnode s receiver) = None \<and>
      \<comment> \<open>Constants for expressing postcondition on what stays the same/changes in projected state.\<close>
      receiver = cur_thread s \<and> ks = ks_of s receiver
    \<rbrace> handle_recv True \<lbrace>\<lambda> _ s.
      cur_thread s = receiver \<and>
      \<comment> \<open>The system call returns the notification badge value that was predicted
         by the receive oracle.\<close>
      getRegister_ret s receiver badge_register = Some badge_val \<and>
      \<comment> \<open>The system call updates the receive oracle to indicate the notification
         has been consumed.
         In all other respects, the system call does not modify the state.\<close>
      ks_of s receiver = ks\<lparr>ks_ntfn_to_recv := None\<rparr>\<rbrace>"
  apply(wpsimp wp:handle_recv_microkit_notification[where
    receiver=receiver and
    cnode="ks_thread_cnode ks" and
    bound_notif="ks_bound_notification ks" and
    ntfn_st="ks_ntfn_status ks" and
    ppc_tr="ks_ppc_to_recv ks" and
    iep_st="ks_input_ep_status ks" and
    mapped_wr="ks_mapped_writable ks" and
    not_wr_others="ks_not_writable_others ks"] hoare_strengthen_post
    simp:ks_of_def)
   apply blast
  unfolding valid_ep_obj_with_ntfn''_def input_cap_configured_def
  apply(clarsimp simp:invs_def cur_tcb_def invs_valid_objs2 simp:ks_of_def obj_at_def)
  done
*)

end
