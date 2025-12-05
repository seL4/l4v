(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Access
imports ArchAccess
begin

arch_requalify_consts
  vspace_cap_rights_to_auth
  arch_cap_auth_conferred
  state_vrefs
  aobj_ref'
  acap_asid'
  state_asids_to_policy_arch
  integrity_asids_2
  integrity_hyp_2
  integrity_fpu_2
  arch_integrity_obj_atomic
  arch_integrity_obj_alt
  arch_IP_update
  auth_ipc_buffers
  valid_cur_hyp (* FIXME AC: incorporate into invs *)

subsection \<open>Policy wellformedness\<close>

text\<open>

Wellformedness of the agent authority function with respect to a label
(the current thread):

\begin{itemize}

\item For (the current untrusted) @{term "agent"}, large enough
  authority must be contained within the agent's boundaries.

\item @{term "agent"} has all the self authority it could want.

\item If an agent can grant caps through an endpoint, then it is
  authority-equivalent to all agents that can receive on that
  endpoint.

\item Similarly, if an agent can grant through a reply cap, then
  it is authority-equivalent to the original caller.

\item Anyone can send on any IRQ notification.

\item Call implies a send ability.

\item If an agent could reply to a call, then the caller has the
  authority to delete the derived reply cap. This can happen if
  the caller thread is deleted before the reply takes place.

\item Reply caps can be transferred, so the DeleteDerived
  authority propagates transitively.

\end{itemize}

\<close>

definition policy_wellformed where
  "policy_wellformed aag maySendIrqs irqs agent \<equiv>
     (\<forall>agent'. (agent, Control, agent') \<in> aag \<longrightarrow> agent = agent')
   \<and> (\<forall>a. (agent, a, agent) \<in> aag)
   \<and> (\<forall>s r ep. (s, Grant, ep) \<in> aag \<and> (r, Receive, ep) \<in> aag
                \<longrightarrow> (s, Control, r) \<in> aag \<and> (r, Control, s) \<in> aag)
   \<and> (maySendIrqs \<longrightarrow> (\<forall>irq ntfn. irq \<in> irqs \<and> (irq, Notify, ntfn) \<in> aag
                                  \<longrightarrow> (agent, Notify, ntfn) \<in> aag))
   \<and> (\<forall>s ep. (s, Call, ep) \<in> aag \<longrightarrow> (s, SyncSend, ep) \<in> aag)
   \<and> (\<forall>s r ep. (s, Call, ep) \<in> aag \<and> (r, Receive, ep) \<in> aag \<longrightarrow> (r, Reply, s) \<in> aag)
   \<and> (\<forall>s r. (s, Reply, r) \<in> aag \<longrightarrow> (r, DeleteDerived, s) \<in> aag)
   \<and> (\<forall>l1 l2 l3. (l1, DeleteDerived, l2) \<in> aag \<longrightarrow> (l2, DeleteDerived, l3) \<in> aag
                  \<longrightarrow> (l1, DeleteDerived, l3) \<in> aag)
   \<and> (\<forall>s r ep. (s, Call, ep) \<in> aag \<and> (r, Receive, ep) \<in> aag \<and> (r, Grant, ep) \<in> aag
                \<longrightarrow> (s, Control, r) \<in> aag \<and> (r, Control, s) \<in> aag)"

abbreviation pas_wellformed where
  "pas_wellformed aag \<equiv>
     policy_wellformed (pasPolicy aag) (pasMaySendIrqs aag) (range (pasIRQAbs aag)) (pasSubject aag)"


subsection \<open>auth_graph_map\<close>

text\<open>

Abstract a graph by relabelling the nodes (agents). Clearly this can
collapse (and not create) distinctions.

\<close>

definition auth_graph_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a auth_graph \<Rightarrow> 'b auth_graph" where
  "auth_graph_map f aag \<equiv> {(f x, auth, f y) | x auth y. (x, auth, y) \<in> aag}"


subsection \<open>Transform caps and tcb states into authority\<close>

text\<open>

Abstract the state to an agent authority graph. This definition states
what authority is conferred by a particular capability to the obj_refs
in it.

\<close>

definition cap_rights_to_auth :: "cap_rights \<Rightarrow> bool \<Rightarrow> auth set" where
  "cap_rights_to_auth r sync \<equiv>
     {Reset}
   \<union> (if AllowRead \<in> r then {Receive} else {})
   \<union> (if AllowWrite \<in> r then (if sync then {SyncSend} else {Notify}) else {})
   \<union> (if AllowGrant \<in> r then UNIV else {})
   \<union> (if AllowGrantReply \<in> r \<and> AllowWrite \<in> r then {Call} else {})"

definition reply_cap_rights_to_auth :: "bool \<Rightarrow> cap_rights \<Rightarrow> auth set" where
  "reply_cap_rights_to_auth master r \<equiv> if AllowGrant \<in> r \<or> master then UNIV else {Reply}"

definition cap_auth_conferred :: "cap \<Rightarrow> auth set" where
 "cap_auth_conferred cap \<equiv> case cap of
    NullCap \<Rightarrow> {}
  | UntypedCap isdev oref bits freeIndex \<Rightarrow> {Control}
  | EndpointCap oref badge r \<Rightarrow> cap_rights_to_auth r True
  | NotificationCap oref badge r \<Rightarrow> cap_rights_to_auth (r - {AllowGrant, AllowGrantReply}) False
  | ReplyCap oref m r \<Rightarrow> reply_cap_rights_to_auth m r
  | CNodeCap oref bits guard \<Rightarrow> {Control}
  | ThreadCap obj_ref \<Rightarrow> {Control}
  | DomainCap \<Rightarrow> {Control}
  | IRQControlCap \<Rightarrow> {Control}
  | IRQHandlerCap irq \<Rightarrow> {Control}
  | Zombie ptr b n \<Rightarrow> {Control}
  | ArchObjectCap arch_cap \<Rightarrow> arch_cap_auth_conferred arch_cap"

fun tcb_st_to_auth :: "thread_state \<Rightarrow> (obj_ref \<times> auth) set" where
  "tcb_st_to_auth (BlockedOnNotification ntfn) = {(ntfn, Receive)}"
| "tcb_st_to_auth (BlockedOnSend ep payl) =
     {(ep, SyncSend)} \<union> (if sender_can_grant payl then {(ep, Grant),(ep, Call)} else {})
   \<union> (if sender_can_grant_reply payl then {(ep, Call)} else {})"
| "tcb_st_to_auth (BlockedOnReceive ep payl) =
     {(ep, Receive)} \<union> (if receiver_can_grant payl then {(ep, Grant)} else {})"
| "tcb_st_to_auth _ = {}"


subsection \<open>Transferability: Moving caps between agents\<close>

text \<open>
  Tells if cap can move/be derived between agents without grant
  due to the inner workings of the system (Calling and replying for now)
\<close>

(* FIXME is_transferable should guarantee directly that a non-NullCap cap is owned by its CDT
   parents without using directly the CDT so that we can use it in integrity *)
inductive is_transferable for opt_cap where
  it_None: "opt_cap = None \<Longrightarrow> is_transferable opt_cap" |
  it_Null: "opt_cap = Some NullCap \<Longrightarrow> is_transferable opt_cap" |
  it_Reply: "opt_cap = Some (ReplyCap t False R) \<Longrightarrow> is_transferable opt_cap"

abbreviation "is_transferable_cap cap \<equiv> is_transferable (Some cap)"
abbreviation "is_transferable_in slot s \<equiv> is_transferable (caps_of_state s slot)"


subsection \<open>Generating a policy from the current cap, ASID and IRQs distribution\<close>

(* TODO split that section between sbta sata and sita and move a maximum
   of accesor functions back to AInvs *)

(* FIXME: update comment *)
text \<open>
  sbta_caps/sbta_asid imply that a thread and it's vspace are labelled
  the same -- caps_of_state (tcb, vspace_index) will be the PD cap.
  Thus, a thread is completely managed or completely self-managed.
  We can (possibly) weaken this by only talking about addressable caps
  (i.e., only cspace in a tcb). This would also mean that we should use
  the current cspace for the current label ... a bit strange, though.

  The set of all objects affected by a capability. We cheat a bit and
  say that a DomainCap contains references to everything, as it
  intuitively grants its owners that sort of access. This allows us to
  reuse sbta for DomainCaps.

  The sbta definition is non-inductive. We use the "inductive"
  construct for convenience, i.e. to get a nice set of intro rules,
  cases, etc.

\<close>

primrec obj_refs_ac :: "cap \<Rightarrow> obj_ref set" where
  "obj_refs_ac NullCap = {}"
| "obj_refs_ac (ReplyCap r m cr) = {r}"
| "obj_refs_ac IRQControlCap = {}"
| "obj_refs_ac (IRQHandlerCap irq) = {}"
| "obj_refs_ac (UntypedCap d r s f) = {}"
| "obj_refs_ac (CNodeCap r bits guard) = {r}"
| "obj_refs_ac (EndpointCap r b cr) = {r}"
| "obj_refs_ac (NotificationCap r b cr) = {r}"
| "obj_refs_ac (ThreadCap r) = {r}"
| "obj_refs_ac (Zombie ptr b n) = {ptr}"
| "obj_refs_ac (ArchObjectCap x) = aobj_ref' x"
| "obj_refs_ac DomainCap = UNIV" (* hack, see above *)

fun cap_irqs_controlled :: "cap \<Rightarrow> irq set" where
  "cap_irqs_controlled IRQControlCap = UNIV"
| "cap_irqs_controlled (IRQHandlerCap irq) = {irq}"
| "cap_irqs_controlled _ = {}"

inductive_set state_irqs_to_policy_aux for aag caps where
  sita_controlled:
    "\<lbrakk> caps ptr = Some cap; irq \<in> cap_irqs_controlled cap \<rbrakk>
       \<Longrightarrow> (pasObjectAbs aag (fst ptr), Control, pasIRQAbs aag irq) \<in> state_irqs_to_policy_aux aag caps"

abbreviation state_irqs_to_policy where
  "state_irqs_to_policy aag s \<equiv> state_irqs_to_policy_aux aag (caps_of_state s)"

definition irq_map_wellformed_aux where
  "irq_map_wellformed_aux aag irqs \<equiv> \<forall>irq. pasObjectAbs aag (irqs irq) = pasIRQAbs aag irq"

abbreviation irq_map_wellformed where
  "irq_map_wellformed aag s \<equiv> irq_map_wellformed_aux aag (interrupt_irq_node s)"

definition thread_st_auth where
  "thread_st_auth s \<equiv> case_option {} tcb_st_to_auth \<circ> tcb_states_of_state s"

definition thread_bound_ntfns where
  "thread_bound_ntfns s \<equiv> \<lambda>p. case_option None tcb_bound_notification (get_tcb p s)"

inductive_set state_bits_to_policy for caps thread_sts thread_bas cdt vrefs hrefs where
  sbta_caps:
    "\<lbrakk> caps ptr = Some cap; oref \<in> obj_refs_ac cap; auth \<in> cap_auth_conferred cap \<rbrakk>
       \<Longrightarrow> (fst ptr, auth, oref) \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs hrefs"
| sbta_untyped:
    "\<lbrakk> caps ptr = Some cap; oref \<in> untyped_range cap \<rbrakk>
       \<Longrightarrow> (fst ptr, Control, oref) \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs hrefs"
| sbta_ts:
    "(oref', auth) \<in> thread_sts oref
     \<Longrightarrow> (oref, auth, oref') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs hrefs"
| sbta_bounds:
    "\<lbrakk> thread_bas oref = Some oref'; auth \<in> {Receive, Reset} \<rbrakk>
       \<Longrightarrow> (oref, auth, oref') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs hrefs"
| sbta_cdt:
    "\<lbrakk> cdt slot' = Some slot ; \<not>is_transferable (caps slot') \<rbrakk>
       \<Longrightarrow> (fst slot, Control, fst slot') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs hrefs"
| sbta_cdt_transferable:
    "cdt slot' = Some slot
     \<Longrightarrow> (fst slot, DeleteDerived, fst slot') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs hrefs"
| sbta_vref:
    "(ptr', _, _, auth) \<in> vrefs ptr
     \<Longrightarrow> (ptr, auth, ptr') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs hrefs"
| sbta_href:
    "\<lbrakk> (ptr',_) \<in> hrefs ptr \<rbrakk>
       \<Longrightarrow> (ptr, Control, ptr') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs hrefs"

definition state_objs_to_policy :: "det_state \<Rightarrow> (obj_ref \<times> auth \<times> obj_ref) set" where
  "state_objs_to_policy s = state_bits_to_policy (caps_of_state s) (thread_st_auth s)
                                                 (thread_bound_ntfns s) (cdt s)
                                                 (state_vrefs s) (state_hyp_refs_of s)"


subsection \<open>Policy Refinement\<close>

text\<open>

We map scheduler domains to labels. This asserts that the labels on
tcbs are consistent with the labels on the domains they run in.

We need this to show that the ready queues are not reordered by
unauthorised subjects (see integrity_ready_queues).

\<close>

inductive_set domains_of_state_aux for etcbs_of where
  domtcbs:
    "\<lbrakk> etcbs_of ptr = Some tcb; d = etcb_domain tcb \<rbrakk> \<Longrightarrow> (ptr, d) \<in> domains_of_state_aux etcbs_of"

abbreviation "domains_of_state s \<equiv> domains_of_state_aux (etcbs_of s)"

definition tcb_domain_map_wellformed_aux where
  "tcb_domain_map_wellformed_aux aag tcbs_doms \<equiv>
     \<forall>(ptr, d) \<in> tcbs_doms. pasObjectAbs aag ptr \<in> pasDomainAbs aag d"

abbreviation tcb_domain_map_wellformed where
  "tcb_domain_map_wellformed aag s \<equiv> tcb_domain_map_wellformed_aux aag (domains_of_state s)"

text\<open>

We sometimes need to know that our current subject may run in the current domain.

\<close>

abbreviation "pas_cur_domain aag s \<equiv> pasSubject aag \<in> pasDomainAbs aag (cur_domain s)"

text\<open>

The relation we want to hold between the current state and
the policy:
\begin{itemize}

\item The policy should be well-formed.

\item The abstraction of the state should respect the policy.

\end{itemize}

\<close>

abbreviation state_objs_in_policy :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "state_objs_in_policy aag s \<equiv>
                auth_graph_map (pasObjectAbs aag) (state_objs_to_policy s) \<subseteq> pasPolicy aag"

abbreviation state_asids_to_policy :: "'a PAS \<Rightarrow> det_state \<Rightarrow> ('a \<times> auth \<times> 'a) set" where
  "state_asids_to_policy aag s \<equiv>
     state_asids_to_policy_arch aag (caps_of_state s) (arch_state s) (state_vrefs s)"

definition pas_refined :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "pas_refined aag \<equiv> \<lambda>s.
     pas_wellformed aag
   \<and> irq_map_wellformed aag s
   \<and> tcb_domain_map_wellformed aag s
   \<and> state_objs_in_policy aag s
   \<and> state_asids_to_policy aag s \<subseteq> pasPolicy aag
   \<and> state_irqs_to_policy aag s \<subseteq> pasPolicy aag"


section \<open>Integrity definition\<close>

subsection \<open>How kernel objects can change\<close>

fun blocked_on :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool" where
  "blocked_on ref (BlockedOnReceive ref' _)    = (ref = ref')"
| "blocked_on ref (BlockedOnSend    ref' _)    = (ref = ref')"
| "blocked_on ref (BlockedOnNotification ref') = (ref = ref')"
| "blocked_on _ _ = False"

fun receive_blocked_on :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool" where
  "receive_blocked_on ref (BlockedOnReceive ref' _)    = (ref = ref')"
| "receive_blocked_on ref (BlockedOnNotification ref') = (ref = ref')"
| "receive_blocked_on _ _ = False"

lemma receive_blocked_on_def2:
  "receive_blocked_on ref ts = ((ref, Receive) \<in> tcb_st_to_auth ts)"
  by (cases ts, simp_all)

fun send_blocked_on :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool" where
  "send_blocked_on ref (BlockedOnSend ref' _) = (ref = ref')"
| "send_blocked_on _ _ = False"

lemma send_blocked_on_def2:
  "send_blocked_on ref ts = ((ref, SyncSend) \<in> tcb_st_to_auth ts)"
  by (cases ts, simp_all)

fun send_is_call :: "thread_state \<Rightarrow> bool" where
  "send_is_call (BlockedOnSend _ payl) = sender_is_call payl"
| "send_is_call _ = False"

definition tcb_bound_notification_reset_integrity ::
  "obj_ref option \<Rightarrow> obj_ref option \<Rightarrow> 'a set \<Rightarrow> 'a PAS \<Rightarrow> bool" where
  "tcb_bound_notification_reset_integrity ntfn ntfn' subjects aag \<equiv>
     (ntfn = ntfn') \<comment> \<open>no change to bound ntfn\<close>
   \<or> (ntfn' = None \<and> aag_subjects_have_auth_to subjects aag Reset (the ntfn)) \<comment> \<open>ntfn is unbound\<close>"

definition direct_send :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> obj_ref \<Rightarrow> tcb \<Rightarrow> bool" where
  "direct_send subjects aag ep tcb \<equiv> receive_blocked_on ep (tcb_state tcb) \<and>
                                     (aag_subjects_have_auth_to subjects aag SyncSend ep \<or>
                                      aag_subjects_have_auth_to subjects aag Notify ep)"

abbreviation ep_recv_blocked :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool" where
  "ep_recv_blocked ep ts \<equiv> case ts of BlockedOnReceive w _ \<Rightarrow> w = ep | _ \<Rightarrow> False"

definition direct_call :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> obj_ref \<Rightarrow> thread_state \<Rightarrow> bool" where
  "direct_call subjects aag ep tcbst \<equiv> ep_recv_blocked ep (tcbst) \<and>
                                        aag_subjects_have_auth_to subjects aag Call ep"

definition indirect_send :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> tcb \<Rightarrow> bool" where
  "indirect_send subjects aag ntfn recv_ep tcb \<equiv>
     ep_recv_blocked recv_ep (tcb_state tcb) \<and> aag_subjects_have_auth_to subjects aag Notify ntfn
              \<comment> \<open>tcb is blocked on sync ep\<close> \<and> (tcb_bound_notification tcb = Some ntfn)"

definition call_blocked :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool" where
  "call_blocked ep tst \<equiv> \<exists>pl. tst = BlockedOnSend ep pl \<and> sender_is_call pl"

definition allowed_call_blocked :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool" where
  "allowed_call_blocked ep tst \<equiv> \<exists>pl. tst = BlockedOnSend ep pl \<and> sender_is_call pl \<and>
                                              (sender_can_grant pl \<or> sender_can_grant_reply pl)"

definition direct_reply :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> 'a \<Rightarrow> tcb \<Rightarrow> bool" where
  "direct_reply subjects aag tcb_owner tcb \<equiv>
     (awaiting_reply (tcb_state tcb)
        \<or> (\<exists>ep. allowed_call_blocked ep (tcb_state tcb)
            \<and> aag_subjects_have_auth_to subjects aag Receive ep))
     \<and> aag_subjects_have_auth_to_label subjects aag Reply tcb_owner"

definition reply_cap_deletion_integrity :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> bool" where
  "reply_cap_deletion_integrity subjects aag cap cap' \<equiv>
   (cap = cap') \<or> (\<exists>caller R. cap = ReplyCap caller False R \<and> cap' = NullCap \<and>
                              pasObjectAbs aag caller \<in> subjects)"

(* WARNING: if some one want to add a cap to is_transferable, it must appear here *)
definition cnode_integrity :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> cnode_contents \<Rightarrow> cnode_contents \<Rightarrow> bool" where
  "cnode_integrity subjects aag content content' \<equiv>
   \<forall>l. content l = content' l \<or> (\<exists>cap cap'. content l = Some cap \<and> content' l = Some cap' \<and>
                                            reply_cap_deletion_integrity subjects aag cap cap')"


subsubsection \<open>Definition of object integrity\<close>

text \<open>
  The object integrity relation describes which modification to kernel objects are allowed by the
  policy aag when the system is controlled by subjects.

  ko and ko' are the initial and final version of the particular kernel object
  on which we are reasoning.
  The corresponding memory emplacement must belong to l.

  The activate boolean allows reactivation of a thread in a @{term Restart} state.

  Creation and destruction or retyping of kernel objects are not allowed unless l \<in> subjects
\<close>

(* FIXME it would be nice if there was an arch_tcb_context_update with all the required lemmas*)
inductive integrity_obj_atomic for aag activate subjects l ko ko' where
  (* l can modify any object it owns *)
  troa_lrefl:
    "l \<in> subjects \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* l can modify a Notification object state if it has rights to interact with it *)
| troa_ntfn:
    "\<lbrakk> ko = Some (Notification ntfn); ko' = Some (Notification ntfn');
       auth \<in> {Receive, Notify, Reset}; s \<in> subjects; (s, auth, l) \<in> pasPolicy aag \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* l can modify an Endpoint object state if it has rights to interact with it *)
| troa_ep:
    "\<lbrakk> ko = Some (Endpoint ep); ko' = Some (Endpoint ep');
       auth \<in> {Receive, SyncSend, Reset}; s \<in> subjects; (s, auth, l) \<in> pasPolicy aag \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If a tcb is waiting on receiving on an Endpoint but could be bound to a notification ntfn.
     Then if we can Notify ntfn, we could modify the endpoint *)
| troa_ep_unblock:
    "\<lbrakk> ko = Some (Endpoint ep); ko' = Some (Endpoint ep');
       (tcb, Receive, pasObjectAbs aag ntfn) \<in> pasPolicy aag;
       (tcb, Receive, l) \<in> pasPolicy aag;
       aag_subjects_have_auth_to subjects aag Notify ntfn \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If the subjects can send to an Endpoint or its bound notification, they can also
     modify any thread that is waiting on it *)
| troa_tcb_send:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := arch_tcb_set_registers regs' (tcb_arch tcb), tcb_state := Running\<rparr>;
       direct_send subjects aag ep tcb
       \<or> indirect_send subjects aag (the (tcb_bound_notification tcb)) ep tcb \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If a tcb is waiting on an Endpoint that the subjects can Call, they are allowed
     to do that call, and insert a ReplyCap back towards a subject*)
| troa_tcb_call:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := arch_tcb_set_registers regs' (tcb_arch tcb), tcb_state := Running,
                   tcb_caller := ReplyCap caller False R\<rparr>;
       pasObjectAbs aag caller \<in> subjects;
       direct_call subjects aag ep (tcb_state tcb) \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Subjects can reply to a tcb waiting for a Reply, if they have authority to do that Reply
     In case of a fault Reply, the new state of the thread can be Restart or Inactive depending on
     the fault handler*)
| troa_tcb_reply:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := arch_tcb_set_registers regs' (tcb_arch tcb),
                   tcb_state := new_st, tcb_fault := None\<rparr>;
       new_st = Running \<or> (tcb_fault tcb \<noteq> None \<and> (new_st = Restart \<or> new_st = Inactive));
       awaiting_reply (tcb_state tcb); aag_subjects_have_auth_to_label subjects aag Reply l \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Subjects can receive a message from an Endpoint. The sender state will then be set to
     Running if it is a normal send and to Inactive or BlockedOnReply if it is a call.
     TODO split that rule *)
| troa_tcb_receive:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_state := new_st\<rparr>;
       new_st = Running
       \<or> (inactive new_st \<and> call_blocked ep (tcb_state tcb))
       \<or> (awaiting_reply new_st \<and> allowed_call_blocked ep (tcb_state tcb));
       send_blocked_on ep (tcb_state tcb);
       aag_subjects_have_auth_to subjects aag Receive ep \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Subjects can Reset an Endpoint/Notification they have Reset authority to, and thus
     all TCBs blocked on it need to be restarted *)
| troa_tcb_restart:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb\<lparr>tcb_state := Restart\<rparr>;
       blocked_on ep (tcb_state tcb);
       aag_subjects_have_auth_to subjects aag Reset ep \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Subjects can Reset a bound Notification which then need to be unbound*)
| troa_tcb_unbind:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb\<lparr>tcb_bound_notification := None\<rparr>;
       aag_subjects_have_auth_to subjects aag Reset (the (tcb_bound_notification tcb)) \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Allow subjects to delete their reply caps in other subjects' threads.
   * Note that we need to account for the reply cap being in tcb_ctable,
   * because recursive deletion of the root CNode may temporarily place any
   * contained cap (in particular, a copied reply cap) in that location. *)
| troa_tcb_empty_ctable:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb\<lparr>tcb_ctable := cap'\<rparr>;
       reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) cap' \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
| troa_tcb_empty_caller:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb\<lparr>tcb_caller := cap'\<rparr>;
       reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap' \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If the activate flag is on, any thread in Restart state can be restarted *)
| troa_tcb_activate:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb\<lparr>tcb_arch := arch_IP_update (tcb_arch tcb),
                  tcb_state := Running\<rparr>;
       tcb_state tcb = Restart; activate \<rbrakk> \<comment> \<open>Anyone can do this\<close>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Allow any FPU changes; constraints are imposed by integrity_fpu instead *)
| troa_tcb_fpu:
    "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb\<lparr>tcb_arch := new_arch\<rparr>;
       arch_tcb_get_registers new_arch = arch_tcb_get_registers (tcb_arch tcb);
       tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb) \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If there is a deletable_cap in a CNode, it must be allowed to be deleted *)
| troa_cnode:
      "\<lbrakk> ko = Some (CNode n content); ko' = Some (CNode n content');
         cnode_integrity subjects aag content content' \<rbrakk>
         \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Arch-specific rules *)
| troa_arch:
      "\<lbrakk> ko = Some (ArchObj ao); ko' = Some (ArchObj ao');
         arch_integrity_obj_atomic aag subjects l ao ao' \<rbrakk>
         \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"

definition integrity_obj where
  "integrity_obj aag activate subjects l \<equiv> (integrity_obj_atomic aag activate subjects l)\<^sup>*\<^sup>*"

abbreviation integrity_obj_state where
  "integrity_obj_state aag activate subjects s s' \<equiv>
     (\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x))"


subsubsection \<open>Alternative tagged formulation of object integrity\<close>

datatype Tro_rules = LRefl | ORefl | RNtfn | REp | EpUnblock | TCBSend | TCBCall | TCBReply
                           | TCBReceive | TCBRestart | TCBGeneric | RArch | TCBActivate | RCNode

definition tro_tag :: "Tro_rules \<Rightarrow> bool" where
  "tro_tag t \<equiv> True"

(* do not put that one in the simpset unless you know what you are doing *)
lemma tro_tagI[intro!]:
  "tro_tag t"
  unfolding tro_tag_def ..

definition tro_tag' :: "Tro_rules \<Rightarrow> bool" where
  "tro_tag' t \<equiv> True"

(* do not put that one in the simpset unless you know what you are doing *)
lemma tro_tag'_intro[intro!]:
  "tro_tag' t"
  unfolding tro_tag'_def ..

lemma tro_tag_to_prime:
  "tro_tag t = tro_tag' t"
  unfolding tro_tag_def tro_tag'_def by simp


text \<open>
  This is the old definition of @{const integrity_obj}, corresponding
  to @{const integrity_obj_atomic} but with certain atomic steps
  combined (notably TCB updates).

  We keep this here because it is used by many of the existing proofs,
  and having common combinations of steps is sometimes useful.

  The @{const tro_tag}s are used to tag each rule, for use in the
  transitivity proof. The transitivity property is, in turn, needed to
  prove that these steps are included in @{const integrity_obj}
  (which is the transitive closure of @{const integrity_obj_atomic}).

  NB: we do not try to prove the converse, i.e. integrity_obj_alt
      implying @{const integrity_obj}. It is not quite true, and we
      do not need it in any case.
\<close>

inductive integrity_obj_alt for aag activate subjects l' ko ko' where
  tro_alt_lrefl:
    "\<lbrakk> tro_tag LRefl; l' \<in> subjects \<rbrakk> \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_orefl:
    "\<lbrakk> tro_tag ORefl; ko = ko' \<rbrakk> \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_ntfn:
    "\<lbrakk> tro_tag RNtfn; ko = Some (Notification ntfn); ko' = Some (Notification ntfn');
       auth \<in> {Receive, Notify, Reset};
       \<exists>s \<in> subjects. (s, auth, l') \<in> pasPolicy aag \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_ep:
    "\<lbrakk> tro_tag REp; ko = Some (Endpoint ep); ko' = Some (Endpoint ep');
       auth \<in> {Receive, SyncSend, Reset}; (\<exists>s \<in> subjects. (s, auth, l') \<in> pasPolicy aag) \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_ep_unblock:
    "\<lbrakk> tro_tag EpUnblock; ko = Some (Endpoint ep); ko' = Some (Endpoint ep');
       \<exists>tcb ntfn. (tcb, Receive, pasObjectAbs aag ntfn) \<in> pasPolicy aag \<and>
                  (tcb, Receive, l') \<in> pasPolicy aag \<and>
                  aag_subjects_have_auth_to subjects aag Notify ntfn \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_send:
    "\<lbrakk> tro_tag TCBSend; ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := new_arch,
                   tcb_state := Running, tcb_bound_notification := ntfn',
                   tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
       tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb);
       tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
       reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
       reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
       direct_send subjects aag ep tcb
       \<or> indirect_send subjects aag (the (tcb_bound_notification tcb)) ep tcb \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_call:
    "\<lbrakk> tro_tag TCBCall; ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := new_arch,
                   tcb_state := Running, tcb_bound_notification := ntfn',
                   tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
       tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb);
       pasObjectAbs aag caller \<in> subjects;
       tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
       reply_cap_deletion_integrity subjects aag (ReplyCap caller False R) cap';
       reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
       direct_call subjects aag ep (tcb_state tcb) \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_reply:
    "\<lbrakk> tro_tag TCBReply; ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := new_arch,
                   tcb_state := new_st, tcb_fault := None,
                   tcb_bound_notification := ntfn',
                   tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
       tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb);
       new_st = Running \<or> (tcb_fault tcb \<noteq> None \<and> (new_st = Restart \<or> new_st = Inactive));
       tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
       reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
       reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
       direct_reply subjects aag l' tcb \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_receive:
    "\<lbrakk> tro_tag TCBReceive; ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_state := new_st, tcb_arch := new_arch,
                   tcb_bound_notification := ntfn',
                   tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
       tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb);
       new_st = Running \<or> ((new_st = Inactive \<and> call_blocked ep (tcb_state tcb)) \<or>
       (new_st = BlockedOnReply \<and> (allowed_call_blocked ep (tcb_state tcb))));
       tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
       reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
       reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
       send_blocked_on ep (tcb_state tcb);
       aag_subjects_have_auth_to subjects aag Receive ep \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_restart:
    "\<lbrakk> tro_tag TCBRestart; ko  = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := new_arch,
                   tcb_state := tcb_state tcb', tcb_bound_notification := ntfn',
                   tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
       tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb);
       tcb_state tcb' = Restart \<or> tcb_state tcb' = Running;
       tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
       reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
       reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
       blocked_on ep (tcb_state tcb);
       aag_subjects_have_auth_to subjects aag Reset ep \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_generic:
    "\<lbrakk> tro_tag TCBGeneric; ko = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := new_arch, tcb_bound_notification := ntfn',
                   tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
       tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb);
       tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag ;
       reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
       reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap' \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_activate:
    "\<lbrakk> tro_tag TCBActivate; ko  = Some (TCB tcb); ko' = Some (TCB tcb');
       tcb' = tcb \<lparr>tcb_arch := new_arch, tcb_caller := cap', tcb_ctable := ccap',
                   tcb_state := Running, tcb_bound_notification := ntfn'\<rparr>;
       tcb_hyp_refs new_arch = tcb_hyp_refs (tcb_arch tcb);
       tcb_state tcb = Restart;
       reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
       reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
       tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
       activate \<rbrakk> \<comment> \<open>Anyone can do this\<close>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_cnode:
    "\<lbrakk> tro_tag RCNode; ko  = Some (CNode n content); ko' = Some (CNode n content');
       cnode_integrity subjects aag content content' \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_arch:
    "\<lbrakk> tro_tag RArch; ko = Some (ArchObj ao); ko' = Some (ArchObj ao');
       arch_integrity_obj_alt aag subjects l' ao ao'\<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"


subsubsection \<open>ready queues\<close>

text\<open>

  Assume two subjects can't interact. Then AINVS already implies that
  the ready queues of one won't change when the other is running.

  Assume two subjects can interact via an endpoint. (Probably an
  notification object for infoflow purposes.) Then the following says
  that the ready queues for the non-running subject can be extended by
  the running subject, e.g. by sending a message. Note these threads are
  added to the start of the queue.

\<close>

definition integrity_ready_queues where
  "integrity_ready_queues aag subjects queue_labels rq rq' \<equiv>
     pasMayEditReadyQueues aag \<or> (queue_labels \<inter> subjects = {} \<longrightarrow> (\<exists>threads. threads @ rq = rq'))"


abbreviation object_integrity where
  "object_integrity aag \<equiv> integrity_obj (aag :: 'a PAS) (pasMayActivate aag) {pasSubject aag}"


subsection \<open>How the CDT can change\<close>

text \<open>
  The CDT and CDT_list integrity relations describe which modification to the CDT (@{term cdt})
  , @{term is_original_cap} and @{term cdt_list})
  are allowed by the policy aag when the system is controlled by subjects.

  A modification to the CDT at a specific slot can happen for different reasons :
  \begin{itemize}
  \item we own directly or indirectly the slot. The "indirectly" means that
        if an ancestor of a slot is owned by the subject, the slot is indirectly own by the subject
  \item we are allowed explicitly to take ownership of the slot, for now this only happens when
        we call someone: we are allowed to put a reply cap in its caller slot (slot number 3)
\<close>

inductive cdt_direct_change_allowed for aag subjects tcbsts ptr where
  cdca_owned:
    "pasObjectAbs aag (fst ptr) \<in> subjects \<Longrightarrow> cdt_direct_change_allowed aag subjects tcbsts ptr"
| cdca_reply:
    "\<lbrakk> tcbsts (fst ptr) = Some tcbst; direct_call subjects aag ep tcbst; (snd ptr) = tcb_cnode_index 3 \<rbrakk>
       \<Longrightarrow> cdt_direct_change_allowed aag subjects tcbsts ptr"

(* for the moment the only caps that can be affected by that indirect control are reply caps *)
definition cdt_change_allowed where
  "cdt_change_allowed aag subjects m tcbsts ptr \<equiv>
     \<exists>pptr. m \<Turnstile> pptr \<rightarrow>* ptr \<and> cdt_direct_change_allowed aag subjects tcbsts pptr"

(* FIXME get a coherent naming scheme *)
abbreviation cdt_change_allowed' where
  "cdt_change_allowed' aag ptr s \<equiv>
     cdt_change_allowed aag {pasSubject aag} (cdt s) (tcb_states_of_state s) ptr"

text\<open>
  ptr is the slot we currently looking at
  s is the initial state (v should be coherent with s)
  v = (initial parent of ptr, initial "originality" of ptr)
  v' = (final parent of ptr, final "originality" of ptr)
\<close>
definition integrity_cdt ::
   "'a PAS \<Rightarrow> 'a set \<Rightarrow> cdt \<Rightarrow> (obj_ref \<Rightarrow> thread_state option) \<Rightarrow> cslot_ptr
           \<Rightarrow> (cslot_ptr option \<times> bool) \<Rightarrow> (cslot_ptr option \<times> bool) \<Rightarrow> bool" where
  "integrity_cdt aag subjects m tcbsts ptr v v' \<equiv>
     v = v' \<or> cdt_change_allowed aag subjects m tcbsts ptr"

abbreviation integrity_cdt_state where
  "integrity_cdt_state aag subjects s s' \<equiv>
     (\<forall>x. integrity_cdt aag subjects (cdt s) (tcb_states_of_state s) x
                        (cdt s x,is_original_cap s x) (cdt s' x, is_original_cap s' x))"

abbreviation "cdt_integrity aag \<equiv> integrity_cdt (aag :: 'a PAS) {pasSubject aag} "

abbreviation cdt_integrity_state where
  "cdt_integrity_state aag s s' \<equiv>
     (\<forall>x. integrity_cdt (aag :: 'a PAS) {pasSubject aag} (cdt s) (tcb_states_of_state s) x
                        (cdt s x,is_original_cap s x) (cdt s' x, is_original_cap s' x))"

text\<open>
  m is the cdt of the initial state
  tcbsts are tcb_states_of_state of the initial state
  ptr is the slot we currently looking at
  l and l' are the initial and final list of children of ptr
\<close>
definition integrity_cdt_list ::
   "'a PAS \<Rightarrow> 'a set \<Rightarrow> cdt \<Rightarrow> (obj_ref \<Rightarrow> thread_state option)
           \<Rightarrow> cslot_ptr \<Rightarrow> (cslot_ptr list) \<Rightarrow> (cslot_ptr list) \<Rightarrow> bool" where
  "integrity_cdt_list aag subjects m tcbsts ptr l l' \<equiv>
     filtered_eq (cdt_change_allowed aag subjects m tcbsts) l l'
   \<or> cdt_change_allowed aag subjects m tcbsts ptr"

abbreviation integrity_cdt_list_state where
  "integrity_cdt_list_state aag subjects s s' \<equiv>
     (\<forall>x. integrity_cdt_list aag subjects (cdt s) (tcb_states_of_state s)
                             x (cdt_list s x) (cdt_list s' x))"

abbreviation "cdt_list_integrity aag \<equiv> integrity_cdt_list (aag :: 'a PAS) {pasSubject aag}"

abbreviation cdt_list_integrity_state where
  "cdt_list_integrity_state aag  s s' \<equiv>
     (\<forall>x. integrity_cdt_list (aag :: 'a PAS) {pasSubject aag} (cdt s) (tcb_states_of_state s) x
                             (cdt_list s x) (cdt_list s' x))"


subsection \<open>How user and device memory can change\<close>

text \<open>
  The memory integrity relation describes which modification to user memory are allowed by the
  policy aag when the system is controlled by subjects.

  p is the physical pointer to the concerned memory.
  ts and ts' are the @{term tcb_states_of_state} of both states
  icp_buf is the @{term auth_ipc_buffers} of the initial state
  globals is a deprecated parameter that is used in InfoFlow with the value {}
         TODO: It would be nice if someone made it disappear.
  w and w' are the data in the initial and final state.

  The possible reason allowing for a write are :
  \begin{itemize}
  \item owning the memory
  \item being explicitly allowed to write by the policy
  \item The pointer is in the "globals" set. This is an obsolete concept and will be removed
  \item The thread is receiving an IPC, and we write to its IPC buffer
        We indirectly use the constraints of tro (@{term integrity_obj})
        to decide when to allow that in order to avoid duplicating the definitions.

  Inductive for now, we should add something about user memory/transitions.
\<close>

inductive integrity_mem for aag subjects p ts ts' ipcbufs globals w w' where
  trm_lrefl:
    "pasObjectAbs aag p \<in> subjects \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
| trm_orefl:
    "w = w' \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
| trm_write:
    "aag_subjects_have_auth_to subjects aag Write p
     \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
| trm_globals:
    "p \<in> globals \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
| trm_ipc:
    "\<lbrakk> case_option False can_receive_ipc (ts p');
       ts' p' = Some Running; p \<in> ipcbufs p'; pasObjectAbs aag p' \<notin> subjects \<rbrakk>
       \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"

abbreviation
  "memory_integrity X aag x t1 t2 ipc \<equiv> integrity_mem (aag :: 'a PAS) {pasSubject aag} x t1 t2 ipc X"

inductive integrity_device for aag subjects p ts ts' w w' where
  trd_lrefl:
    "pasObjectAbs aag p \<in> subjects \<Longrightarrow> integrity_device aag subjects p ts ts' w w'"
| trd_orefl:
    "w = w' \<Longrightarrow> integrity_device aag subjects p ts ts' w w'"
| trd_write:
    "aag_subjects_have_auth_to subjects aag Write p \<Longrightarrow> integrity_device aag subjects p ts ts' w w'"


subsection \<open>How other stuff can change\<close>

definition integrity_interrupts ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> irq \<Rightarrow> (obj_ref \<times> irq_state) \<Rightarrow> (obj_ref \<times> irq_state) \<Rightarrow> bool" where
  "integrity_interrupts aag subjects irq v v' \<equiv> v = v' \<or> pasIRQAbs aag irq \<in> subjects"

subsection \<open>Abbreviations for arch-specific definitions\<close>

abbreviation integrity_asids ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> obj_ref \<Rightarrow> asid \<Rightarrow> 'st::state_ext state \<Rightarrow> 's::state_ext state  \<Rightarrow> bool" where
  "integrity_asids aag subjects x asid s s' \<equiv>
   integrity_asids_2 aag subjects x asid (arch_state s) (arch_state s') (aobjs_of s) (aobjs_of s')"

abbreviation integrity_hyp ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> obj_ref \<Rightarrow> 'st::state_ext state \<Rightarrow> 's::state_ext state \<Rightarrow> bool"
 where
  "integrity_hyp aag subjects x s s' \<equiv>
   integrity_hyp_2 aag subjects x (machine_state s) (machine_state s')
                   (arch_state s) (arch_state s') (aobjs_of s) (aobjs_of s')"

abbreviation integrity_fpu ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> obj_ref \<Rightarrow> 'st::state_ext state \<Rightarrow> 's::state_ext state \<Rightarrow> bool"
where
  "integrity_fpu aag subjects x s s' \<equiv>
   integrity_fpu_2 aag subjects x (machine_state s) (machine_state s') (kheap s) (kheap s')"


subsection \<open>General integrity\<close>

text\<open>

Half of what we ultimately want to say: that the parts of the
system state that change are allowed to by the labelling @{term
"aag"}.

The other half involves showing that @{term "aag"} concords with the
policy. See @{term "state_objs_to_policy s"} and @{term "pas_refined aag s"}.

\<close>

definition integrity_subjects ::
  "'a set \<Rightarrow> 'a PAS \<Rightarrow> bool \<Rightarrow> obj_ref set \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "integrity_subjects subjects aag activate X s s' \<equiv>
     (\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x))
   \<and> integrity_cdt_state aag subjects s s'
   \<and> integrity_cdt_list_state aag subjects s s'
   \<and> (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s x, interrupt_states s x)
                               (interrupt_irq_node s' x, interrupt_states s' x))
   \<and> (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d) (ready_queues s d p)
                                   (ready_queues s' d p))
   \<and> (\<forall>x. integrity_mem aag subjects x (tcb_states_of_state s) (tcb_states_of_state s')
                        (auth_ipc_buffers s) X
                        (underlying_memory (machine_state s) x)
                        (underlying_memory (machine_state s') x))
   \<and> (\<forall>x. integrity_device aag subjects x (tcb_states_of_state s) (tcb_states_of_state s')
                           (device_state (machine_state s) x)
                           (device_state (machine_state s') x))
   \<and> (\<forall>x a. integrity_asids aag subjects x a s s')
   \<and> (\<forall>x. integrity_hyp aag subjects x s s')
   \<and> (\<forall>x. integrity_fpu aag subjects x s s')"

abbreviation "integrity aag \<equiv> integrity_subjects {pasSubject aag} aag (pasMayActivate aag)"

subsection \<open>Various definitions and abbreviations\<close>

definition label_owns_asid_slot :: "'a PAS \<Rightarrow> 'a \<Rightarrow> asid \<Rightarrow> bool" where
  "label_owns_asid_slot aag l asid \<equiv>
     (l, Control, pasASIDAbs aag asid) \<in> pasPolicy aag"

fun cap_asid' :: "cap \<Rightarrow> asid set" where
  "cap_asid' (ArchObjectCap acap) = acap_asid' acap"
| "cap_asid' _ = {}"

definition cap_links_asid_slot :: "'a PAS \<Rightarrow> 'a \<Rightarrow> cap \<Rightarrow> bool" where
  "cap_links_asid_slot aag l cap \<equiv> (\<forall>asid \<in> cap_asid' cap. label_owns_asid_slot aag l asid)"

abbreviation is_subject_asid :: "'a PAS \<Rightarrow> asid \<Rightarrow> bool" where
  "is_subject_asid aag asid \<equiv> pasASIDAbs aag asid = pasSubject aag"

definition cap_links_irq :: "'a PAS \<Rightarrow> 'a \<Rightarrow> cap \<Rightarrow> bool" where
  "cap_links_irq aag l cap \<equiv>
     \<forall>irq \<in> cap_irqs_controlled cap. (l, Control, pasIRQAbs aag irq) \<in> pasPolicy aag"

abbreviation is_subject_irq :: "'a PAS \<Rightarrow> irq \<Rightarrow> bool" where
  "is_subject_irq aag irq \<equiv> pasIRQAbs aag irq = pasSubject aag"

definition aag_cap_auth :: "'a PAS \<Rightarrow> 'a \<Rightarrow> cap \<Rightarrow> bool" where
  "aag_cap_auth aag l cap \<equiv>
     (\<forall>x \<in> obj_refs_ac cap. \<forall>auth \<in> cap_auth_conferred cap. (l, auth, pasObjectAbs aag x) \<in> pasPolicy aag)
   \<and> (\<forall>x \<in> untyped_range cap. (l, Control, pasObjectAbs aag x) \<in> pasPolicy aag)
   \<and> cap_links_asid_slot aag l cap \<and> cap_links_irq aag l cap"

abbreviation pas_cap_cur_auth :: "'a PAS \<Rightarrow> cap \<Rightarrow> bool" where
  "pas_cap_cur_auth aag cap \<equiv> aag_cap_auth aag (pasSubject aag) cap"

end
