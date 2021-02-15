(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Access
imports Deterministic_AC
begin

context begin interpretation Arch . (*FIXME: arch_split*)

section \<open>Policy and policy refinement\<close>

subsection \<open>Policy definition\<close>

text\<open>

The goal is to place limits on what untrusted agents can do while the
trusted agents are not running. This supports a framing constraint in
the descriptions (Hoare triples) of syscalls. Roughly the existing
proofs show the effect of the syscall, and this proof summarises what
doesn't (or isn't allowed to) change.

The basic intuition is to map all object references to the agent they
belong to and show that changes to the object reference graph are
allowed by the policy specified by the user. The policy is a labelled
graph amongst agents independent of the current state, i.e. a static
external summary of what should be talking to what and how.

The interesting cases occur between trusted and untrusted components:
e.g. we assume that it is unsafe for untrusted components (UT)
to send capabilities to trusted components (T), and so T must ensure
that all endpoints it shares with UT that it receives on do not have
the grant bit set.

\<close>

type_synonym 'a agent_map = "obj_ref \<Rightarrow> 'a"
type_synonym 'a agent_asid_map = "asid \<Rightarrow> 'a"
type_synonym 'a agent_irq_map = "irq \<Rightarrow> 'a"
type_synonym 'a agent_domain_map = "domain \<Rightarrow> 'a set"

text\<open>

What one agent can do to another. We allow multiple edges between
agents in the graph.

Control is special. It implies the ability to do pretty much anything,
including get access the other rights, create, remove, etc.

DeleteDerived allows you to delete a cap derived from a cap you own
\<close>

datatype auth = Control | Receive | SyncSend | Notify
                    | Reset | Grant | Call | Reply | Write | Read
                    | ASIDPoolMapsASID | DeleteDerived

text\<open>

The interesting case is for endpoints.

Consider an EP between T and UT (across a trust boundary). We want to
be able to say that all EPs and tcbs that T does not expose to UT do
not change when it is not running. If UT had a direct Send right to T
then integrity (see below) could not guarantee this, as it doesn't
know which EP can be changed by UT. Thus we set things up like this
(all distinct labels):

T -Receive-> EP <-Send- UT

Now UT can interfere with EP and all of T's tcbs blocked for receive on EP,
but not endpoints internal to T, or tcbs blocked on other (suitably
labelled) EPs, etc.

\<close>

type_synonym 'a auth_graph = "('a \<times> auth \<times> 'a) set"

text \<open>

Each global namespace will need a labeling function.

We map each scheduling domain to a single label; concretely, each tcb
in a scheduling domain has to have the same label. We will want to
weaken this in the future.

The booleans @{text pasMayActivate} and @{text pasMayEditReadyQueues}
are used to weaken the integrity property. When @{const True},
@{text pasMayActivate} causes the integrity property to permit
activation of newly-scheduled threads. Likewise, @{text pasMayEditReadyQueues}
has the integrity property permit the removal of threads from ready queues,
as occurs when scheduling a new domain for instance. By setting each of these
@{const False} we get a more constrained integrity property that is useful for
establishing some of the proof obligations for the infoflow proofs, particularly
those over @{const handle_event} that neither activates new threads nor schedules
new domains.

The @{text pasDomainAbs} relation describes which labels may run in
a given scheduler domain. This relation is not relevant to integrity
but will be used in the information flow theory (with additional
constraints on its structure).
\<close>

end

record 'a PAS =
  pasObjectAbs :: "'a agent_map"
  pasASIDAbs :: "'a agent_asid_map"
  pasIRQAbs :: "'a agent_irq_map"
  pasPolicy :: "'a auth_graph"
  pasSubject :: "'a"                \<comment> \<open>The active label\<close>
  pasMayActivate :: "bool"
  pasMayEditReadyQueues :: "bool"
  pasMaySendIrqs :: "bool"
  pasDomainAbs :: "'a agent_domain_map"

text\<open>

Very often we want to say that the agent currently running owns a
given pointer.

\<close>

abbreviation is_subject :: "'a PAS \<Rightarrow> obj_ref \<Rightarrow> bool"
where
  "is_subject aag ptr \<equiv> pasObjectAbs aag ptr = pasSubject aag"

text\<open>

Also we often want to say the current agent can do something to a
pointer that he doesn't own but has some authority to.

\<close>

abbreviation(input) aag_has_auth_to :: "'a PAS \<Rightarrow> auth \<Rightarrow> obj_ref \<Rightarrow> bool"
where
  "aag_has_auth_to aag auth ptr \<equiv> (pasSubject aag, auth, pasObjectAbs aag ptr) \<in> pasPolicy aag"

abbreviation aag_subjects_have_auth_to_label :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> auth \<Rightarrow> 'a \<Rightarrow> bool"
where
 "aag_subjects_have_auth_to_label subs aag auth label
    \<equiv> \<exists>s \<in> subs. (s, auth, label) \<in> pasPolicy aag"

abbreviation aag_subjects_have_auth_to :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> auth \<Rightarrow> obj_ref \<Rightarrow> bool"
where
 "aag_subjects_have_auth_to subs aag auth oref
    \<equiv> aag_subjects_have_auth_to_label subs aag auth (pasObjectAbs aag oref)"


context begin interpretation Arch . (*FIXME: arch_split*)

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

definition policy_wellformed
where
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

abbreviation pas_wellformed
where
  "pas_wellformed aag \<equiv>
    policy_wellformed (pasPolicy aag) (pasMaySendIrqs aag) (range (pasIRQAbs aag)) (pasSubject aag)"

lemma aag_wellformed_Control:
  "\<lbrakk>  (x, Control, y) \<in> aag; policy_wellformed aag mirqs irqs x \<rbrakk> \<Longrightarrow> x = y"
  unfolding policy_wellformed_def by metis

lemma aag_wellformed_refl:
  "\<lbrakk> policy_wellformed aag mirqs irqs x \<rbrakk> \<Longrightarrow> (x, a, x) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_grant_Control_to_recv:
  "\<lbrakk> (s, Grant, ep) \<in> aag; (r, Receive, ep) \<in> aag; policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (s, Control, r) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_grant_Control_to_send:
  "\<lbrakk> (s, Grant, ep) \<in> aag; (r, Receive, ep) \<in> aag; policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (r, Control, s) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_reply:
  "\<lbrakk> (s, Call, ep) \<in> aag; (r, Receive, ep) \<in> aag; policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (r, Reply, s) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_delete_derived':
  "\<lbrakk>  (s, Call, ep) \<in> aag; (r, Receive, ep) \<in> aag; policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (s, DeleteDerived, r) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_delete_derived:
  "\<lbrakk> (s, Reply, r) \<in> aag; policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (r, DeleteDerived, s) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_delete_derived_trans:
  "\<lbrakk> (l1, DeleteDerived, l2) \<in> aag; (l2, DeleteDerived, l3) \<in> aag;
     policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (l1, DeleteDerived, l3) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_call_to_syncsend:
  "\<lbrakk> (s, Call, ep) \<in> aag; policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (s, SyncSend, ep) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_grant_Control_to_send_by_reply:
  "\<lbrakk> (s, Call, ep) \<in> aag; (r, Receive, ep) \<in> aag; (r, Grant, ep) \<in> aag;
   policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (r, Control, s) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_grant_Control_to_recv_by_reply:
  "\<lbrakk> (s, Call, ep) \<in> aag; (r, Receive, ep) \<in> aag; (r, Grant, ep) \<in> aag;
   policy_wellformed aag mirqs irqs l\<rbrakk>
        \<Longrightarrow> (s, Control, r) \<in> aag"
  unfolding policy_wellformed_def by blast


subsection \<open>auth_graph_map\<close>

text\<open>

Abstract a graph by relabelling the nodes (agents). Clearly this can
collapse (and not create) distinctions.

\<close>

definition
  auth_graph_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a auth_graph \<Rightarrow> 'b auth_graph"
where
  "auth_graph_map f aag \<equiv> {(f x, auth, f y) | x auth y. (x, auth, y) \<in> aag}"

lemma auth_graph_map_mem:
  "(x, auth, y) \<in> auth_graph_map f S
     = (\<exists>x' y'. x = f x' \<and> y = f y' \<and> (x', auth, y') \<in> S)"
  by (simp add: auth_graph_map_def)

lemmas auth_graph_map_memD = auth_graph_map_mem[THEN iffD1]
lemma auth_graph_map_memE:
  assumes hyp:"(x, auth, y) \<in> auth_graph_map f S"
  obtains x' and y' where "x = f x'" and "y = f y'" and "(x', auth, y') \<in> S"
  using hyp[THEN auth_graph_map_mem[THEN iffD1]] by fastforce

lemma auth_graph_map_memI:
  "\<lbrakk> (x', auth, y') \<in> S; x = f x'; y = f y' \<rbrakk>
      \<Longrightarrow> (x, auth, y) \<in> auth_graph_map f S"
  by (fastforce simp add: auth_graph_map_mem)

lemma auth_graph_map_mono:
  "S \<subseteq> S' \<Longrightarrow> auth_graph_map G S \<subseteq> auth_graph_map G S'"
  unfolding auth_graph_map_def by auto



subsection \<open>Transform caps and tcb states into authority\<close>

text\<open>

Abstract the state to an agent authority graph. This definition states
what authority is conferred by a particular capability to the obj_refs
in it.

\<close>

definition cap_rights_to_auth :: "cap_rights \<Rightarrow> bool \<Rightarrow> auth set"
where
  "cap_rights_to_auth r sync \<equiv>
     {Reset}
   \<union> (if AllowRead \<in> r then {Receive} else {})
   \<union> (if AllowWrite \<in> r then (if sync then {SyncSend} else {Notify}) else {})
   \<union> (if AllowGrant \<in> r then UNIV else {})
   \<union> (if AllowGrantReply \<in> r \<and> AllowWrite \<in> r then {Call} else {})"

definition vspace_cap_rights_to_auth :: "cap_rights \<Rightarrow> auth set"
where
  "vspace_cap_rights_to_auth r \<equiv>
      (if AllowWrite \<in> r then {Write} else {})
    \<union> (if AllowRead \<in> r then {Read} else {})"

definition reply_cap_rights_to_auth :: "bool \<Rightarrow> cap_rights \<Rightarrow> auth set"
where
  "reply_cap_rights_to_auth master r \<equiv> if AllowGrant \<in> r \<or> master then UNIV else {Reply}"

definition cap_auth_conferred :: "cap \<Rightarrow> auth set"
where
 "cap_auth_conferred cap \<equiv>
    case cap of
      Structures_A.NullCap \<Rightarrow> {}
    | Structures_A.UntypedCap isdev oref bits freeIndex \<Rightarrow> {Control}
    | Structures_A.EndpointCap oref badge r \<Rightarrow>
         cap_rights_to_auth r True
    | Structures_A.NotificationCap oref badge r \<Rightarrow>
         cap_rights_to_auth (r - {AllowGrant, AllowGrantReply}) False
    | Structures_A.ReplyCap oref m r \<Rightarrow> reply_cap_rights_to_auth m r
    | Structures_A.CNodeCap oref bits guard \<Rightarrow> {Control}
    | Structures_A.ThreadCap obj_ref \<Rightarrow> {Control}
    | Structures_A.DomainCap \<Rightarrow> {Control}
    | Structures_A.IRQControlCap \<Rightarrow> {Control}
    | Structures_A.IRQHandlerCap irq \<Rightarrow> {Control}
    | Structures_A.Zombie ptr b n \<Rightarrow> {Control}
    | Structures_A.ArchObjectCap arch_cap \<Rightarrow>
         (if is_page_cap (the_arch_cap cap)
         then vspace_cap_rights_to_auth (acap_rights arch_cap)
             else {Control})"

fun tcb_st_to_auth :: "Structures_A.thread_state \<Rightarrow> (obj_ref \<times> auth) set"
where
  "tcb_st_to_auth (Structures_A.BlockedOnNotification ntfn) = {(ntfn, Receive)}"
| "tcb_st_to_auth (Structures_A.BlockedOnSend ep payl)
     = {(ep, SyncSend)} \<union> (if sender_can_grant payl then {(ep, Grant),(ep, Call)} else {})
       \<union> (if sender_can_grant_reply payl then {(ep, Call)} else {})"
| "tcb_st_to_auth (Structures_A.BlockedOnReceive ep payl)
     = {(ep, Receive)} \<union> (if receiver_can_grant payl then {(ep, Grant)} else {})"
| "tcb_st_to_auth _ = {}"

subsection \<open>FIXME MOVE\<close>

definition pte_ref
where
  "pte_ref pte \<equiv> case pte of
    SmallPagePTE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSmallPage, vspace_cap_rights_to_auth rights)
  | LargePagePTE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMLargePage, vspace_cap_rights_to_auth rights)
  | _ \<Rightarrow> None"

definition pde_ref2
where
  "pde_ref2 pde \<equiv> case pde of
    SectionPDE addr atts domain rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSection, vspace_cap_rights_to_auth rights)
  | SuperSectionPDE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSuperSection, vspace_cap_rights_to_auth rights)
  | PageTablePDE addr atts domain
    \<comment> \<open>The 0 is a hack, saying that we own only addr, although 12 would also be OK\<close>
       \<Rightarrow> Some (ptrFromPAddr addr, 0, {Control})
  | _ \<Rightarrow> None"

definition ptr_range
where
  "ptr_range p sz \<equiv> {p .. p + 2 ^ sz - 1}"

(* We exclude the global page tables from the authority graph. Alternatively,
   we could include them and add a wellformedness constraint to policies that
   requires that every label has the necessary authority to whichever label owns
   the global page tables, so that when a new page directory is created and
   references to the global page tables are added to it, no new authority is gained.
   Note: excluding the references to global page tables in this way
         brings in some ARM arch-specific VM knowledge here *)
definition vs_refs_no_global_pts :: "Structures_A.kernel_object \<Rightarrow> (obj_ref \<times> vs_ref \<times> auth) set"
where
  "vs_refs_no_global_pts \<equiv> \<lambda>ko. case ko of
    ArchObj (ASIDPool pool) \<Rightarrow>
       (\<lambda>(r,p). (p, VSRef (ucast r) (Some AASIDPool), Control)) ` graph_of pool
  | ArchObj (PageDirectory pd) \<Rightarrow>
      \<Union>(r,(p, sz, auth)) \<in> graph_of (pde_ref2 o pd) - {(x,y). (ucast (kernel_base >> 20) \<le> x)}.
          (\<lambda>(p, a). (p, VSRef (ucast r) (Some APageDirectory), a)) ` (ptr_range p sz \<times> auth)
  | ArchObj (PageTable pt) \<Rightarrow>
      \<Union>(r,(p, sz, auth)) \<in> graph_of (pte_ref o pt).
          (\<lambda>(p, a). (p, VSRef (ucast r) (Some APageTable), a)) ` (ptr_range p sz \<times> auth)
  | _ \<Rightarrow> {}"

subsection \<open>Transferability: Moving caps between agents\<close>

text \<open>
  Tells if cap can move/be derived between agents without grant
  due to the inner workings of the system (Calling and replying for now)
\<close>
(* FIXME is_transferable should garantee directly that a non-NullCap cap is owned by its CDT
   parents without using directly the CDT so that we can use it in integrity *)
inductive is_transferable for opt_cap
where
  it_None: "opt_cap = None \<Longrightarrow> is_transferable opt_cap" |
  it_Null: "opt_cap = Some NullCap \<Longrightarrow> is_transferable opt_cap" |
  it_Reply: "opt_cap = Some (ReplyCap t False R) \<Longrightarrow> is_transferable opt_cap"

abbreviation "is_transferable_cap cap \<equiv> is_transferable (Some cap)"
abbreviation "is_transferable_in slot s \<equiv> is_transferable (caps_of_state s slot)"

lemma is_transferable_capE:
  assumes hyp:"is_transferable_cap cap"
  obtains "cap = NullCap" | t R where "cap = ReplyCap t False R"
  by (rule is_transferable.cases[OF hyp]) auto

lemma is_transferable_None[simp]: "is_transferable None"
  using is_transferable.simps by simp
lemma is_transferable_Null[simp]: "is_transferable_cap NullCap"
  using is_transferable.simps by simp
lemma is_transferable_Reply[simp]: "is_transferable_cap (ReplyCap t False R)"
  using is_transferable.simps by simp

lemma is_transferable_NoneE:
  assumes hyp: "is_transferable opt_cap"
  obtains "opt_cap = None" | cap where "opt_cap = Some cap" and "is_transferable_cap cap"
  by (rule is_transferable.cases[OF hyp];simp)

lemma is_transferable_Untyped[simp]: "\<not> is_transferable (Some (UntypedCap dev ptr sz freeIndex))"
  by (blast elim: is_transferable.cases)
lemma is_transferable_IRQ[simp]: "\<not> is_transferable_cap IRQControlCap"
  by (blast elim: is_transferable.cases)
lemma is_transferable_Zombie[simp]: "\<not> is_transferable (Some (Zombie ptr sz n))"
  by (blast elim: is_transferable.cases)
lemma is_transferable_Ntfn[simp]: "\<not> is_transferable (Some (NotificationCap ntfn badge R))"
  by (blast elim: is_transferable.cases)
lemma is_transferable_Endpoint[simp]: "\<not> is_transferable (Some (EndpointCap ntfn badge R))"
  by (blast elim: is_transferable.cases)

(*FIXME MOVE *)
lemmas descendants_incD
    = descendants_inc_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

lemma acap_class_reply:
  "(acap_class acap \<noteq> ReplyClass t)"
  (* warning: arch split *)
  by (cases acap; simp)

lemma cap_class_reply:
  "(cap_class cap = ReplyClass t) = (\<exists>r m. cap = ReplyCap t m r)"
  by (cases cap; simp add: acap_class_reply)

lemma reply_cap_no_children:
  "\<lbrakk> valid_mdb s; caps_of_state s p = Some (ReplyCap t False r) \<rbrakk> \<Longrightarrow> cdt s p' \<noteq> Some p"
  apply (clarsimp simp: valid_mdb_def)
  apply (frule descendants_incD[where p=p' and p'=p])
   apply (rule child_descendant)
   apply (fastforce)
  apply clarsimp
  apply (subgoal_tac "caps_of_state s p' \<noteq> None")
   apply (clarsimp simp: cap_class_reply)
   apply (simp only: reply_mdb_def reply_caps_mdb_def reply_masters_mdb_def)
   apply (elim conjE allE[where x=p'])
   apply simp
  apply (drule(1) mdb_cte_atD)
  apply (fastforce simp add: cte_wp_at_def caps_of_state_def)
  done

(*FIXME MOVE *)
lemmas all_childrenI = all_children_def[THEN meta_eq_to_obj_eq, THEN iffD2, rule_format]
lemmas all_childrenD = all_children_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

(*FIXME MOVE *)
lemma valid_mdb_descendants_inc[elim!]:
  "valid_mdb s \<Longrightarrow> descendants_inc (cdt s) (caps_of_state s)"
  by (simp add:valid_mdb_def)

(*FIXME MOVE *)
lemma valid_mdb_mdb_cte_at [elim!]:
  "valid_mdb s \<Longrightarrow> mdb_cte_at (swp (cte_wp_at ((\<noteq>) NullCap)) s) (cdt s)"
  by (simp add:valid_mdb_def)

(*FIXME MOVE *)
lemma descendants_inc_cap_classD:
  "\<lbrakk> descendants_inc m caps; p \<in> descendants_of p' m; caps p = Some cap ; caps p' = Some cap'\<rbrakk>
   \<Longrightarrow> cap_class cap = cap_class cap'"
  by (fastforce dest:descendants_incD)

lemma is_transferable_all_children:
  "valid_mdb s \<Longrightarrow> all_children (\<lambda>slot . is_transferable (caps_of_state s slot)) (cdt s)"
  apply (rule all_childrenI)
  apply (erule is_transferable.cases)
    apply (fastforce dest: mdb_cte_atD valid_mdb_mdb_cte_at
                     simp: mdb_cte_at_def cte_wp_at_def caps_of_state_def)
   apply (fastforce dest: mdb_cte_atD valid_mdb_mdb_cte_at
                    simp: mdb_cte_at_def cte_wp_at_def caps_of_state_def)
  apply (blast dest:reply_cap_no_children)
done




subsection \<open>Generating a policy from the current cap, ASID and IRQs distribution\<close>

(* TODO split that section between stba sata and sita and move a maximun
   of accesor functions back to AInvs *)


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

primrec aobj_ref' :: "arch_cap \<Rightarrow> obj_ref set"
where
  "aobj_ref' (arch_cap.ASIDPoolCap p as) = {p}"
| "aobj_ref' arch_cap.ASIDControlCap = {}"
| "aobj_ref' (arch_cap.PageCap isdev x rs sz as4) = ptr_range x (pageBitsForSize sz)"
| "aobj_ref' (arch_cap.PageDirectoryCap x as2) = {x}"
| "aobj_ref' (arch_cap.PageTableCap x as3) = {x}"

primrec obj_refs :: "cap \<Rightarrow> obj_ref set"
where
  "obj_refs cap.NullCap = {}"
| "obj_refs (cap.ReplyCap r m cr) = {r}"
| "obj_refs cap.IRQControlCap = {}"
| "obj_refs (cap.IRQHandlerCap irq) = {}"
| "obj_refs (cap.UntypedCap d r s f) = {}"
| "obj_refs (cap.CNodeCap r bits guard) = {r}"
| "obj_refs (cap.EndpointCap r b cr) = {r}"
| "obj_refs (cap.NotificationCap r b cr) = {r}"
| "obj_refs (cap.ThreadCap r) = {r}"
| "obj_refs (cap.Zombie ptr b n) = {ptr}"
| "obj_refs (cap.ArchObjectCap x) = aobj_ref' x"
| "obj_refs cap.DomainCap = UNIV" (* hack, see above *)

inductive_set state_bits_to_policy for caps thread_sts thread_bas cdt vrefs
where
  sbta_caps: "\<lbrakk> caps ptr = Some cap; oref \<in> obj_refs cap;
                auth \<in> cap_auth_conferred cap \<rbrakk>
           \<Longrightarrow> (fst ptr, auth, oref) \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"
| sbta_untyped: "\<lbrakk> caps ptr = Some cap; oref \<in> untyped_range cap \<rbrakk>
           \<Longrightarrow> (fst ptr, Control, oref) \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"
| sbta_ts: "\<lbrakk> (oref', auth) \<in> thread_sts oref \<rbrakk>
           \<Longrightarrow> (oref, auth, oref') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"
| sbta_bounds: "\<lbrakk>thread_bas oref = Some oref'; auth \<in> {Receive, Reset} \<rbrakk>
           \<Longrightarrow> (oref, auth, oref') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"
| sbta_cdt: "\<lbrakk> cdt slot' = Some slot ; \<not>is_transferable (caps slot') \<rbrakk>
           \<Longrightarrow> (fst slot, Control, fst slot')
                                   \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"
| sbta_cdt_transferable: "\<lbrakk>cdt slot' = Some slot\<rbrakk>
           \<Longrightarrow> (fst slot, DeleteDerived, fst slot')
                                   \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"
| sbta_vref: "\<lbrakk> (ptr', ref, auth) \<in> vrefs ptr \<rbrakk>
           \<Longrightarrow> (ptr, auth, ptr') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"

fun cap_asid' :: "cap \<Rightarrow> asid set"
where
  "cap_asid' (ArchObjectCap (PageCap _ _ _ _ mapping))
      = fst ` set_option mapping"
  | "cap_asid' (ArchObjectCap (PageTableCap _ mapping))
      = fst ` set_option mapping"
  | "cap_asid' (ArchObjectCap (PageDirectoryCap _ asid_opt))
      = set_option asid_opt"
  | "cap_asid' (ArchObjectCap (ASIDPoolCap _ asid))
          = {x. asid_high_bits_of x = asid_high_bits_of asid \<and> x \<noteq> 0}"
  | "cap_asid' (ArchObjectCap ASIDControlCap) = UNIV"
  | "cap_asid' _ = {}"

inductive_set state_asids_to_policy_aux for aag caps asid_tab vrefs
where
    sata_asid: "\<lbrakk> caps ptr = Some cap; asid \<in> cap_asid' cap \<rbrakk>
              \<Longrightarrow> ( pasObjectAbs aag (fst ptr), Control, pasASIDAbs aag asid)
                        \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"
  | sata_asid_lookup: "\<lbrakk> asid_tab (asid_high_bits_of asid) = Some poolptr;
                           (pdptr, VSRef (asid && mask asid_low_bits)
                                         (Some AASIDPool), a) \<in> vrefs poolptr \<rbrakk>
                       \<Longrightarrow> (pasASIDAbs aag asid, a, pasObjectAbs aag pdptr)
                              \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"
  | sata_asidpool:    "\<lbrakk> asid_tab (asid_high_bits_of asid) = Some poolptr; asid \<noteq> 0 \<rbrakk> \<Longrightarrow>
                        (pasObjectAbs aag poolptr, ASIDPoolMapsASID, pasASIDAbs aag asid)
                                             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"

fun cap_irqs_controlled :: "cap \<Rightarrow> irq set"
where
  "cap_irqs_controlled cap.IRQControlCap = UNIV"
  | "cap_irqs_controlled (cap.IRQHandlerCap irq) = {irq}"
  | "cap_irqs_controlled _ = {}"

inductive_set state_irqs_to_policy_aux for aag caps
where
  sita_controlled: "\<lbrakk> caps ptr = Some cap; irq \<in> cap_irqs_controlled cap \<rbrakk>
  \<Longrightarrow> (pasObjectAbs aag (fst ptr), Control, pasIRQAbs aag irq) \<in> state_irqs_to_policy_aux aag caps"

abbreviation state_irqs_to_policy
where
  "state_irqs_to_policy aag s \<equiv> state_irqs_to_policy_aux aag (caps_of_state s)"

definition irq_map_wellformed_aux
where
  "irq_map_wellformed_aux aag irqs \<equiv> \<forall>irq. pasObjectAbs aag (irqs irq) = pasIRQAbs aag irq"

abbreviation irq_map_wellformed
where
  "irq_map_wellformed aag s \<equiv> irq_map_wellformed_aux aag (interrupt_irq_node s)"

definition state_vrefs
where
  "state_vrefs s = case_option {} vs_refs_no_global_pts o kheap s"

abbreviation state_asids_to_policy
where
  "state_asids_to_policy aag s \<equiv> state_asids_to_policy_aux aag (caps_of_state s)
        (arm_asid_table (arch_state s)) (state_vrefs s)"

definition tcb_states_of_state
where
  "tcb_states_of_state s \<equiv> \<lambda>p. option_map tcb_state (get_tcb p s)"

(* FIXME: RENAME: should be named something thread_st_auth. thread_states is confusing as
   it outputs autorities *)
definition thread_states
where
  "thread_states s \<equiv> case_option {} tcb_st_to_auth \<circ> tcb_states_of_state s"

definition thread_bound_ntfns
where
  "thread_bound_ntfns s \<equiv> \<lambda>p. case (get_tcb p s) of None \<Rightarrow> None
                                                  | Some tcb \<Rightarrow> tcb_bound_notification tcb"

definition state_objs_to_policy
where
  "state_objs_to_policy s =
      state_bits_to_policy (caps_of_state s) (thread_states s) (thread_bound_ntfns s)
                           (cdt s) (state_vrefs s)"

lemmas state_objs_to_policy_mem = eqset_imp_iff[OF state_objs_to_policy_def]

lemmas state_objs_to_policy_intros
    = state_bits_to_policy.intros[THEN state_objs_to_policy_mem[THEN iffD2]]

(* FIXME this is non resilient at all to adding or removing rules to or from state_bits_to_policy *)
lemmas sta_caps = state_objs_to_policy_intros(1)
  and sta_untyped = state_objs_to_policy_intros(2)
  and sta_ts = state_objs_to_policy_intros(3)
  and sta_bas = state_objs_to_policy_intros(4)
  and sta_cdt = state_objs_to_policy_intros(5)
  and sta_cdt_transferable = state_objs_to_policy_intros(6)
  and sta_vref = state_objs_to_policy_intros(7)

lemmas state_objs_to_policy_cases
    = state_bits_to_policy.cases[OF state_objs_to_policy_mem[THEN iffD1]]

end

context pspace_update_eq begin

interpretation Arch . (*FIXME: arch_split*)

lemma state_vrefs[iff]: "state_vrefs (f s) = state_vrefs s"
  by (simp add: state_vrefs_def pspace)

lemma thread_states[iff]: "thread_states (f s) = thread_states s"
  by (simp add: thread_states_def pspace get_tcb_def swp_def tcb_states_of_state_def)

lemma thread_bound_ntfns[iff]: "thread_bound_ntfns (f s) = thread_bound_ntfns s"
  by (simp add: thread_bound_ntfns_def pspace get_tcb_def swp_def split: option.splits)

(*
  lemma ipc_buffers_of_state[iff]: "ipc_buffers_of_state (f s) = ipc_buffers_of_state s"
  by (simp add: ipc_buffers_of_state_def pspace get_tcb_def swp_def)
*)

end

context begin interpretation Arch . (*FIXME: arch_split*)

lemma tcb_states_of_state_preserved:
  "\<lbrakk> get_tcb thread s = Some tcb; tcb_state tcb' = tcb_state tcb \<rbrakk>
     \<Longrightarrow> tcb_states_of_state (s\<lparr>kheap := kheap s(thread \<mapsto> TCB tcb')\<rparr>) = tcb_states_of_state s"
  apply rule
  apply (auto split: option.splits simp: tcb_states_of_state_def get_tcb_def)
  done

lemma thread_states_preserved:
  "\<lbrakk> get_tcb thread s = Some tcb; tcb_state tcb' = tcb_state tcb \<rbrakk>
     \<Longrightarrow> thread_states (s\<lparr>kheap := kheap s(thread \<mapsto> TCB tcb')\<rparr>) = thread_states s"
  by (simp add: tcb_states_of_state_preserved thread_states_def)

lemma thread_bound_ntfns_preserved:
  "\<lbrakk> get_tcb thread s = Some tcb; tcb_bound_notification tcb' = tcb_bound_notification tcb \<rbrakk>
     \<Longrightarrow> thread_bound_ntfns (s\<lparr>kheap := kheap s(thread \<mapsto> TCB tcb')\<rparr>) = thread_bound_ntfns s"
  by (auto simp:  thread_bound_ntfns_def get_tcb_def split: option.splits)

(* FIXME: move all three *)
lemma null_filterI:
  "\<lbrakk> cs p = Some cap; cap \<noteq> cap.NullCap \<rbrakk> \<Longrightarrow> null_filter cs p = Some cap"
  unfolding null_filter_def by auto
lemma null_filterI2:
  "\<lbrakk> cs p = None \<rbrakk> \<Longrightarrow> null_filter cs p = None"
  unfolding null_filter_def by auto

lemma null_filterE2:
  "\<lbrakk> null_filter cps x = None;
      \<lbrakk> cps x = Some NullCap \<rbrakk> \<Longrightarrow> R ; \<lbrakk> cps x = None \<rbrakk> \<Longrightarrow> R  \<rbrakk>
     \<Longrightarrow> R"
  by (simp add: null_filter_def split: if_split_asm)

lemma is_transferable_null_filter[simp]:
  "is_transferable (null_filter caps ptr) = is_transferable (caps ptr)"
  by (auto simp: is_transferable.simps null_filter_def)

lemma sbta_null_filter:
  "state_bits_to_policy (null_filter cs) sr bar cd vr = state_bits_to_policy cs sr bar cd vr"
  apply (rule subset_antisym)
  apply clarsimp
  apply (erule state_bits_to_policy.induct,
        (fastforce intro: state_bits_to_policy.intros
                   elim: null_filterE null_filterE2 split: option.splits)+)[1]
  apply clarsimp
  apply (erule state_bits_to_policy.induct)
  by (fastforce intro: state_bits_to_policy.intros null_filterI split:option.splits)+

lemma sata_null_filter:
  "state_asids_to_policy_aux aag (null_filter cs) asid_tab vrefs
        = state_asids_to_policy_aux aag cs asid_tab vrefs"
  by (auto elim!: state_asids_to_policy_aux.induct null_filterE
           intro: state_asids_to_policy_aux.intros sata_asid[OF null_filterI])

subsection \<open>Policy Refinement\<close>


text\<open>

We map scheduler domains to labels. This asserts that the labels on
tcbs are consistent with the labels on the domains they run in.

We need this to show that the ready queues are not reordered by
unauthorised subjects (see integrity_ready_queues).

\<close>

inductive_set domains_of_state_aux for ekheap
where
  domtcbs: "\<lbrakk> ekheap ptr = Some etcb; d = tcb_domain etcb \<rbrakk>
  \<Longrightarrow> (ptr, d) \<in> domains_of_state_aux ekheap"

abbreviation domains_of_state
where
  "domains_of_state s \<equiv> domains_of_state_aux (ekheap s)"

definition tcb_domain_map_wellformed_aux
where
  "tcb_domain_map_wellformed_aux aag etcbs_doms \<equiv>
     \<forall>(ptr, d) \<in> etcbs_doms. pasObjectAbs aag ptr \<in> pasDomainAbs aag d"

abbreviation tcb_domain_map_wellformed
where
  "tcb_domain_map_wellformed aag s \<equiv> tcb_domain_map_wellformed_aux aag (domains_of_state s)"

lemma tcb_domain_map_wellformed_mono:
  "\<lbrakk> domains_of_state s' \<subseteq> domains_of_state s; tcb_domain_map_wellformed pas s \<rbrakk> \<Longrightarrow> tcb_domain_map_wellformed pas s'"
by (auto simp: tcb_domain_map_wellformed_aux_def get_etcb_def)

text\<open>

We sometimes need to know that our current subject may run in the current domain.

\<close>

abbreviation
  "pas_cur_domain aag s \<equiv> pasSubject aag \<in> pasDomainAbs aag (cur_domain s)"

text\<open>

The relation we want to hold between the current state and
the policy:
\begin{itemize}

\item The policy should be well-formed.

\item The abstraction of the state should respect the policy.

\end{itemize}

\<close>
abbreviation state_objs_in_policy :: "'a PAS \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "state_objs_in_policy aag s \<equiv>
                auth_graph_map (pasObjectAbs aag) (state_objs_to_policy s) \<subseteq> pasPolicy aag"


definition pas_refined :: "'a PAS \<Rightarrow> det_ext state \<Rightarrow> bool"
where
 "pas_refined aag \<equiv> \<lambda>s.
     pas_wellformed aag
   \<and> irq_map_wellformed aag s
   \<and> tcb_domain_map_wellformed aag s
   \<and> state_objs_in_policy aag s
   \<and> state_asids_to_policy aag s \<subseteq> pasPolicy aag
   \<and> state_irqs_to_policy aag s \<subseteq> pasPolicy aag"

lemma pas_refined_mem:
  "\<lbrakk> (x, auth, y) \<in> state_objs_to_policy s; pas_refined aag s \<rbrakk>
       \<Longrightarrow> (pasObjectAbs aag x, auth, pasObjectAbs aag y) \<in> pasPolicy aag"
  by (auto simp: pas_refined_def intro: auth_graph_map_memI)

lemma pas_refined_wellformed[elim!]:
  "pas_refined aag s \<Longrightarrow> pas_wellformed aag"
  unfolding pas_refined_def by simp

lemmas pas_refined_Control
    = aag_wellformed_Control[OF _ pas_refined_wellformed]
  and pas_refined_refl = aag_wellformed_refl [OF pas_refined_wellformed]

lemma caps_of_state_pasObjectAbs_eq:
  "\<lbrakk> caps_of_state s p = Some cap; Control \<in> cap_auth_conferred cap;
     is_subject aag (fst p); pas_refined aag s;
     x \<in> obj_refs cap \<rbrakk>
       \<Longrightarrow> is_subject aag x"
  apply (frule sta_caps, simp+)
  apply (drule pas_refined_mem, simp+)
  apply (drule pas_refined_Control, simp+)
  done

lemma pas_refined_state_objs_to_policy_subset:
  "\<lbrakk> pas_refined aag s;
     state_objs_to_policy s' \<subseteq> state_objs_to_policy s;
     state_asids_to_policy aag s' \<subseteq> state_asids_to_policy aag s;
     state_irqs_to_policy aag s' \<subseteq> state_irqs_to_policy aag s;
     domains_of_state s' \<subseteq> domains_of_state s;
     interrupt_irq_node s' = interrupt_irq_node s
    \<rbrakk>
    \<Longrightarrow> pas_refined aag s'"
by (simp add: pas_refined_def) (blast dest: tcb_domain_map_wellformed_mono dest: auth_graph_map_mono[where G="pasObjectAbs aag"])

lemma aag_wellformed_all_auth_is_owns':
  "\<lbrakk> Control \<in> S; pas_wellformed aag \<rbrakk> \<Longrightarrow> (\<forall>auth \<in> S. aag_has_auth_to aag auth x) = (is_subject aag x)"
  apply (rule iffI)
   apply (drule (1) bspec)
   apply (frule (1) aag_wellformed_Control )
   apply fastforce
  apply (clarsimp simp: aag_wellformed_refl)
  done

lemmas aag_wellformed_all_auth_is_owns
   = aag_wellformed_all_auth_is_owns'[where S=UNIV, simplified]
     aag_wellformed_all_auth_is_owns'[where S="{Control}", simplified]

lemmas aag_wellformed_control_is_owns
   = aag_wellformed_all_auth_is_owns'[where S="{Control}", simplified]

lemmas pas_refined_all_auth_is_owns = aag_wellformed_all_auth_is_owns[OF pas_refined_wellformed]

lemma pas_refined_sita_mem:
  "\<lbrakk> (x, auth, y) \<in> state_irqs_to_policy aag s; pas_refined aag s \<rbrakk>
       \<Longrightarrow> (x, auth, y) \<in> pasPolicy aag"
  by (auto simp: pas_refined_def)




section \<open>Integrity definition\<close>

subsection \<open>How kernel objects can change\<close>

fun blocked_on :: "obj_ref \<Rightarrow> Structures_A.thread_state \<Rightarrow> bool"
where
    "blocked_on ref (Structures_A.BlockedOnReceive ref' _)     = (ref = ref')"
  | "blocked_on ref (Structures_A.BlockedOnSend    ref' _)     = (ref = ref')"
  | "blocked_on ref (Structures_A.BlockedOnNotification ref')  = (ref = ref')"
  | "blocked_on _ _ = False"

lemma blocked_on_def2:
  "blocked_on ref ts = (ref \<in> fst ` tcb_st_to_auth ts)"
  by (cases ts, simp_all)

fun receive_blocked_on :: "obj_ref \<Rightarrow> Structures_A.thread_state \<Rightarrow> bool"
where
   "receive_blocked_on ref (Structures_A.BlockedOnReceive ref' _)     = (ref = ref')"
  | "receive_blocked_on ref (Structures_A.BlockedOnNotification ref') = (ref = ref')"
  | "receive_blocked_on _ _ = False"

lemma receive_blocked_on_def2:
  "receive_blocked_on ref ts = ((ref, Receive) \<in> tcb_st_to_auth ts)"
  by (cases ts, simp_all)

fun can_receive_ipc :: "Structures_A.thread_state \<Rightarrow> bool"
where
   "can_receive_ipc (Structures_A.BlockedOnReceive _ _)     = True"
  | "can_receive_ipc (Structures_A.BlockedOnSend _ pl)     =
         (sender_is_call pl \<and> (sender_can_grant pl \<or> sender_can_grant_reply pl))"
  | "can_receive_ipc (Structures_A.BlockedOnNotification _) = True"
  | "can_receive_ipc Structures_A.BlockedOnReply = True"
  | "can_receive_ipc _ = False"

lemma receive_blocked_on_can_receive_ipc[elim!,simp]:
  "receive_blocked_on ref ts \<Longrightarrow>can_receive_ipc ts"
  by (cases ts;simp)

lemma receive_blocked_on_can_receive_ipc'[elim!,simp]:
  "case_option False (receive_blocked_on ref) tsopt \<Longrightarrow> case_option False can_receive_ipc tsopt"
  by (cases tsopt;simp)


fun send_blocked_on :: "obj_ref \<Rightarrow> Structures_A.thread_state \<Rightarrow> bool"
where
  "send_blocked_on ref (Structures_A.BlockedOnSend ref' _)     = (ref = ref')"
  | "send_blocked_on _ _ = False"

lemma send_blocked_on_def2:
  "send_blocked_on ref ts = ((ref, SyncSend) \<in> tcb_st_to_auth ts)"
  by (cases ts, simp_all)

lemma send_blocked_on_def3:
  "send_blocked_on ref ts = (\<exists> pl. ts = BlockedOnSend ref pl)"
  by (cases ts; force)

fun send_is_call :: "Structures_A.thread_state \<Rightarrow> bool"
where
  "send_is_call (Structures_A.BlockedOnSend _ payl) = sender_is_call payl"
| "send_is_call _ = False"



definition tcb_bound_notification_reset_integrity
  :: "obj_ref option \<Rightarrow> obj_ref option \<Rightarrow> 'a set \<Rightarrow> 'a PAS \<Rightarrow> bool"
where
  "tcb_bound_notification_reset_integrity ntfn ntfn' subjects aag
    = ((ntfn = ntfn') \<comment> \<open>no change to bound ntfn\<close>
       \<or> (ntfn' = None \<and> aag_subjects_have_auth_to subjects aag Reset (the ntfn))
         \<comment> \<open>ntfn is unbound\<close>)"

lemma tcb_bound_notification_reset_integrity_refl[simp]:
  "tcb_bound_notification_reset_integrity ntfn ntfn subjects aag"
  by (simp add: tcb_bound_notification_reset_integrity_def)


definition direct_send :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> obj_ref \<Rightarrow> tcb \<Rightarrow> bool"
where
  "direct_send subjects aag ep tcb \<equiv> receive_blocked_on ep (tcb_state tcb) \<and>
                                   (aag_subjects_have_auth_to subjects aag SyncSend ep
                                     \<or> aag_subjects_have_auth_to subjects aag Notify ep)"

abbreviation ep_recv_blocked :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool"
where
  "ep_recv_blocked ep ts \<equiv> case ts of BlockedOnReceive w _ \<Rightarrow> w = ep
                             | _ \<Rightarrow> False"

definition direct_call :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> obj_ref \<Rightarrow> thread_state \<Rightarrow> bool"
where
  "direct_call subjects aag ep tcbst \<equiv> ep_recv_blocked ep (tcbst) \<and>
                                   aag_subjects_have_auth_to subjects aag Call ep"

definition indirect_send :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> tcb \<Rightarrow> bool"
where
  "indirect_send subjects aag ntfn recv_ep tcb \<equiv> ep_recv_blocked recv_ep (tcb_state tcb)
                                                    \<comment> \<open>tcb is blocked on sync ep\<close>
                                         \<and> (tcb_bound_notification tcb = Some ntfn)
                                         \<and> aag_subjects_have_auth_to subjects aag Notify ntfn"


definition call_blocked :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool"
where
  "call_blocked ep tst \<equiv> \<exists> pl. tst = BlockedOnSend ep pl \<and> sender_is_call pl"

definition allowed_call_blocked :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool"
where
  "allowed_call_blocked ep tst \<equiv> \<exists> pl. tst = BlockedOnSend ep pl \<and> sender_is_call pl \<and>
                                              (sender_can_grant pl \<or> sender_can_grant_reply pl)"

lemma allowed_call_blocked_call_blocked[elim!]:
  "allowed_call_blocked ep tst \<Longrightarrow> call_blocked ep tst"
  unfolding allowed_call_blocked_def call_blocked_def by fastforce

definition direct_reply :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> 'a \<Rightarrow> tcb \<Rightarrow> bool"
where
  "direct_reply subjects aag tcb_owner tcb \<equiv>
     (awaiting_reply (tcb_state tcb)
        \<or> (\<exists>ep. allowed_call_blocked ep (tcb_state tcb)
            \<and> aag_subjects_have_auth_to subjects aag Receive ep))
     \<and> aag_subjects_have_auth_to_label subjects aag Reply tcb_owner"

definition reply_cap_deletion_integrity :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> bool"
where
  "reply_cap_deletion_integrity subjects aag cap cap' \<equiv>
   (cap = cap') \<or> (\<exists> caller R. cap = ReplyCap caller False R \<and>
                               cap' = NullCap \<and>
                               pasObjectAbs aag caller \<in> subjects)"

lemmas reply_cap_deletion_integrityI1 =
       reply_cap_deletion_integrity_def[THEN meta_eq_to_obj_eq,THEN iffD2,OF disjI1]
lemmas reply_cap_deletion_integrityI2 =
       reply_cap_deletion_integrity_def[THEN meta_eq_to_obj_eq,THEN iffD2, OF disjI2, OF exI,
                                        OF exI, OF conjI [OF _ conjI], rule_format]
lemmas reply_cap_deletion_integrity_intros =
       reply_cap_deletion_integrityI1 reply_cap_deletion_integrityI2

lemma reply_cap_deletion_integrityE:
  assumes hyp:"reply_cap_deletion_integrity subjects aag cap cap'"
  obtains "cap = cap'" | caller R where "cap = ReplyCap caller False R"
  and "cap' = NullCap" and "pasObjectAbs aag caller \<in> subjects"
  using hyp reply_cap_deletion_integrity_def by blast

lemma reply_cap_deletion_integrity_refl[simp]:
  "reply_cap_deletion_integrity subjects aag cap cap"
  by (rule reply_cap_deletion_integrityI1) simp


(* WARNING if some one want to add a cap to is_transferable, it must appear here *)
definition cnode_integrity :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> cnode_contents \<Rightarrow> cnode_contents \<Rightarrow> bool"
  where
  "cnode_integrity subjects aag content content' \<equiv>
   \<forall> l. content l = content' l \<or> (\<exists> cap cap'. content l = Some cap \<and> content' l = Some cap' \<and>
                                         reply_cap_deletion_integrity subjects aag cap cap')"

lemmas cnode_integrityI = cnode_integrity_def[THEN meta_eq_to_obj_eq,THEN iffD2,rule_format]
lemmas cnode_integrityD = cnode_integrity_def[THEN meta_eq_to_obj_eq,THEN iffD1,rule_format]
lemma cnode_integrityE:
  assumes hyp:"cnode_integrity subjects aag content content'"
  obtains "content l = content' l" | cap cap' where "content l = Some cap"
  and "content' l = Some cap'" and "reply_cap_deletion_integrity subjects aag cap cap'"
  using hyp cnode_integrityD by blast

definition asid_pool_integrity ::
  "'a set \<Rightarrow> 'a PAS \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> bool"
  where
  "asid_pool_integrity subjects aag pool pool' \<equiv>
   \<forall>x. pool' x \<noteq> pool x \<longrightarrow> pool' x = None
       \<and> aag_subjects_have_auth_to subjects aag Control (the (pool x))"


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
inductive integrity_obj_atomic for aag activate subjects l ko ko'
  where
  (* l can modify any object it owns *)
  troa_lrefl:
    "\<lbrakk>l \<in> subjects \<rbrakk> \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* l can modify an Notification object state if it has rights to interact with it *)
| troa_ntfn:
    "\<lbrakk>ko = Some (Notification ntfn); ko' = Some (Notification ntfn');
      auth \<in> {Receive, Notify, Reset}; s \<in> subjects;
      (s, auth, l) \<in> pasPolicy aag\<rbrakk>
     \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* l can modify an Endpoint object state if it has rights to interact with it *)
| troa_ep:
    "\<lbrakk> ko = Some (Endpoint ep); ko' = Some (Endpoint ep');
      auth \<in> {Receive, SyncSend, Reset}; s \<in> subjects;
      (s, auth, l) \<in> pasPolicy aag\<rbrakk>
     \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If a tcb is waiting on receiving on an Endpoint but could be bound to a notification ntfn.
     Then if we can Notify ntfn, we could modify the endpoint *)
| troa_ep_unblock:
    "\<lbrakk>ko = Some (Endpoint ep); ko' = Some (Endpoint ep');
      (tcb, Receive, pasObjectAbs aag ntfn) \<in> pasPolicy aag;
      (tcb, Receive, l) \<in> pasPolicy aag;
      aag_subjects_have_auth_to subjects aag Notify ntfn\<rbrakk>
     \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If the subjects can send to an Endpoint or its bound notification, they can also
     modify any thread that is waiting on it *)
| troa_tcb_send:
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
      tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb), tcb_state := Running\<rparr>;
      direct_send subjects aag ep tcb
       \<or> indirect_send subjects aag (the (tcb_bound_notification tcb)) ep tcb\<rbrakk>
     \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If a tcb is waiting on an Endpoint that the subjects can Call, they are allowed
     to do that call, and insert a ReplyCap back towards a subject*)
| troa_tcb_call:
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
      tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb), tcb_state := Running,
                  tcb_caller := ReplyCap caller False R\<rparr>;
      pasObjectAbs aag caller \<in> subjects;
      direct_call subjects aag ep (tcb_state tcb)\<rbrakk>
     \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Subjects can reply to a tcb waiting for a Reply, if they have authority to do that Reply
     In case of a fault Reply, the new state of the thread can be Restart or Inactive depending on
     the fault handler*)
| troa_tcb_reply:
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
      tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                  tcb_state := new_st, tcb_fault := None\<rparr>;
      new_st = Running \<or> (tcb_fault tcb \<noteq> None \<and> (new_st = Restart \<or> new_st = Inactive));
      awaiting_reply (tcb_state tcb);
      aag_subjects_have_auth_to_label subjects aag Reply l\<rbrakk>
     \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Subjects can receive a message from an Endpoint. The sender state will then be set to
     Running if it is a normal send and to Inactive or BlockedOnReply if it is a call.
     TODO split that rule *)
| troa_tcb_receive:
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
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
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
      tcb' = tcb\<lparr>tcb_state := Restart\<rparr>;
      blocked_on ep (tcb_state tcb);
      aag_subjects_have_auth_to subjects aag Reset ep\<rbrakk>
    \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Subjects can Reset a bound Notification which then need to be unbound*)
| troa_tcb_unbind:
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
      tcb' = tcb\<lparr>tcb_bound_notification := None\<rparr>;
      aag_subjects_have_auth_to subjects aag Reset (the (tcb_bound_notification tcb))\<rbrakk>
    \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Allow subjects to delete their reply caps in other subjects' threads.
   * Note that we need to account for the reply cap being in tcb_ctable,
   * because recursive deletion of the root CNode may temporarily place any
   * contained cap (in particular, a copied reply cap) in that location. *)
| troa_tcb_empty_ctable:
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
      tcb' = tcb\<lparr>tcb_ctable := cap'\<rparr>;
      reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) cap'\<rbrakk>
    \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
| troa_tcb_empty_caller:
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
      tcb' = tcb\<lparr>tcb_caller := cap'\<rparr>;
      reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap'\<rbrakk>
    \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If the activate flag is on, any thread in Restart state can be restarted *)
| troa_tcb_activate:
    "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
      tcb' = tcb\<lparr>tcb_arch := arch_tcb_context_set
                        ((arch_tcb_context_get (tcb_arch tcb))(NextIP :=
                                          (arch_tcb_context_get (tcb_arch tcb)) FaultIP)
                        ) (tcb_arch tcb),
                   tcb_state := Running\<rparr>;
      tcb_state tcb = Restart;
      activate\<rbrakk> \<comment> \<open>Anyone can do this\<close>
     \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* Subjects can clear ASIDs that they control *)
| troa_asidpool_clear:
    "\<lbrakk>ko = Some (ArchObj (ASIDPool pool)); ko' = Some (ArchObj (ASIDPool pool'));
      asid_pool_integrity subjects aag pool pool' \<rbrakk>
    \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"
  (* If there is a deletable_cap in a CNode, it must be allowed to be deleted *)
| troa_cnode:
      "\<lbrakk>ko = Some (CNode n content); ko' = Some (CNode n content');
         cnode_integrity subjects aag content content' \<rbrakk>
       \<Longrightarrow> integrity_obj_atomic aag activate subjects l ko ko'"

definition integrity_obj
  where
  "integrity_obj aag activate subjects l \<equiv> (integrity_obj_atomic aag activate subjects l)\<^sup>*\<^sup>*"

subsubsection \<open>Introduction rules for object integrity\<close>

lemma troa_tro:
  "integrity_obj_atomic aag activate subjects l ko ko'
    \<Longrightarrow> integrity_obj aag activate subjects l ko ko'"
  unfolding integrity_obj_def by (rule r_into_rtranclp)

lemmas tro_lrefl = troa_lrefl[THEN troa_tro]
lemma tro_orefl:
  "\<lbrakk> ko = ko' \<rbrakk> \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
  unfolding integrity_obj_def by simp
lemmas tro_ntfn = troa_ntfn[THEN troa_tro]
lemmas tro_ep = troa_ep[THEN troa_tro]
lemmas tro_ep_unblock = troa_ep_unblock[THEN troa_tro]
lemmas tro_tcb_send = troa_tcb_send[THEN troa_tro]
lemmas tro_tcb_call = troa_tcb_call[THEN troa_tro]
lemmas tro_tcb_reply = troa_tcb_reply[THEN troa_tro]
lemmas tro_tcb_receive = troa_tcb_receive[THEN troa_tro]
lemmas tro_tcb_restart = troa_tcb_restart[THEN troa_tro]
lemmas tro_tcb_unbind = troa_tcb_unbind[THEN troa_tro]
lemmas tro_tcb_empty_ctable = troa_tcb_empty_ctable[THEN troa_tro]
lemmas tro_tcb_empty_caller = troa_tcb_empty_caller[THEN troa_tro]
lemmas tro_tcb_activate = troa_tcb_activate[THEN troa_tro]
lemmas tro_asidpool_clear = troa_asidpool_clear[THEN troa_tro]
lemmas tro_cnode = troa_cnode[THEN troa_tro]

lemmas tro_intros = tro_lrefl tro_orefl tro_ntfn tro_ep tro_ep_unblock tro_tcb_send tro_tcb_call
           tro_tcb_reply tro_tcb_receive tro_tcb_restart tro_tcb_unbind tro_tcb_empty_ctable
           tro_tcb_empty_caller tro_tcb_activate tro_asidpool_clear tro_cnode

lemma tro_tcb_unbind':
  "\<lbrakk> ko  = Some (TCB tcb); ko' = Some (TCB tcb');
     tcb' = tcb\<lparr>tcb_bound_notification := ntfn'\<rparr>;
     tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag\<rbrakk>
                 \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
  apply (clarsimp simp:tcb_bound_notification_reset_integrity_def)
  apply (elim disjE)
   apply (rule tro_orefl;fastforce)
  apply (rule tro_tcb_unbind;fastforce)
  done

lemmas rtranclp_transp[intro!] = transp_rtranclp

lemma tro_transp[intro!]:
  "transp (integrity_obj aag activate es subjects)"
  unfolding integrity_obj_def by simp

lemmas tro_trans_spec = tro_transp[THEN transpD]

lemma tro_tcb_generic':
  "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
    tcb' = tcb \<lparr>tcb_bound_notification := ntfn', tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
    tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag ;
    reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
    reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap' \<rbrakk>
   \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
  apply clarsimp
  apply (rule tro_trans_spec)
   apply (rule tro_tcb_empty_caller[OF refl refl refl];simp)
  apply (rule tro_trans_spec)
   apply (rule tro_tcb_empty_ctable[OF refl refl refl];simp)
  apply (rule tro_trans_spec)
   apply (rule tro_tcb_unbind'[OF refl refl refl];simp)
  apply (fastforce intro!: tro_orefl tcb.equality)
  done

lemma tro_tcb_reply':
  "\<lbrakk>ko = Some (TCB tcb); ko' = Some (TCB tcb');
    tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                        tcb_state := new_st, tcb_fault := None\<rparr>;
    new_st = Running \<or> (tcb_fault tcb \<noteq> None \<and> (new_st = Restart \<or> new_st = Inactive));
    direct_reply subjects aag l' tcb \<rbrakk>
   \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
  apply (clarsimp simp:direct_reply_def simp del:not_None_eq)
  apply (erule disjE, (rule tro_tcb_reply[OF refl refl], force; force)) (* Warning: schematics *)
  apply (clarsimp simp del:not_None_eq)
  apply (rule tro_trans_spec)
   apply (frule allowed_call_blocked_def[THEN meta_eq_to_obj_eq,THEN iffD1],clarsimp)
   apply (rule tro_tcb_receive[OF refl refl refl, where new_st=BlockedOnReply];force)
  apply (rule tro_trans_spec)
   apply (rule tro_tcb_reply[OF refl refl refl, where new_st=new_st];force)
  by (fastforce intro!: tro_orefl tcb.equality)

abbreviation integrity_obj_state
where
  "integrity_obj_state aag activate subjects s s' \<equiv>
       (\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x))"



subsubsection \<open>Alternative tagged formulation of object integrity\<close>

datatype Tro_rules = LRefl | ORefl | RNtfn | REp | EpUnblock | TCBSend | TCBCall |
  TCBReply | TCBReceive | TCBRestart | TCBGeneric | RASID | TCBActivate | RCNode

definition tro_tag :: "Tro_rules \<Rightarrow> bool"
where
  "tro_tag t \<equiv> True"

(* do not put that one in the simpset unless you know what you are doing *)
lemma tro_tagI[intro!]:
  "tro_tag t"
  unfolding tro_tag_def ..

definition tro_tag' :: "Tro_rules \<Rightarrow> bool"
where
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
inductive integrity_obj_alt for aag activate subjects l' ko ko'
where
  tro_alt_lrefl:
      "\<lbrakk> tro_tag LRefl ; l' \<in> subjects  \<rbrakk> \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_orefl:
      "\<lbrakk> tro_tag ORefl; ko = ko' \<rbrakk> \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_ntfn:
      "\<lbrakk>tro_tag RNtfn; ko = Some (Notification ntfn); ko' = Some (Notification ntfn');
        auth \<in> {Receive, Notify, Reset};
        \<exists>s \<in> subjects. (s, auth, l') \<in> pasPolicy aag \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_ep:
      "\<lbrakk>tro_tag REp; ko = Some (Endpoint ep); ko' = Some (Endpoint ep');
             auth \<in> {Receive, SyncSend, Reset};
             (\<exists>s \<in> subjects. (s, auth, l') \<in> pasPolicy aag) \<rbrakk>
           \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_ep_unblock:
      "\<lbrakk>tro_tag EpUnblock; ko = Some (Endpoint ep); ko' = Some (Endpoint ep');
        \<exists>tcb ntfn. (tcb, Receive, pasObjectAbs aag ntfn) \<in> pasPolicy aag \<and>
                   (tcb, Receive, l') \<in> pasPolicy aag \<and>
        aag_subjects_have_auth_to subjects aag Notify ntfn \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"

| tro_alt_tcb_send:
      "\<lbrakk>tro_tag TCBSend; ko = Some (TCB tcb); ko' = Some (TCB tcb');
        \<exists>ctxt'. tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                            tcb_state := Running,
                            tcb_bound_notification := ntfn', tcb_caller := cap',
                            tcb_ctable := ccap'\<rparr>;
        tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
        reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
        reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
        direct_send subjects aag ep tcb \<or> indirect_send subjects aag (the (tcb_bound_notification tcb)) ep tcb \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_call:
      "\<lbrakk>tro_tag TCBCall; ko = Some (TCB tcb); ko' = Some (TCB tcb');
        \<exists>ctxt'. tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                            tcb_state := Running,
                            tcb_bound_notification := ntfn', tcb_caller := cap',
                            tcb_ctable := ccap'\<rparr>;
        pasObjectAbs aag caller \<in> subjects;
        tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
        reply_cap_deletion_integrity subjects aag (ReplyCap caller False R) cap';
        reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
        direct_call subjects aag ep (tcb_state tcb) \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_reply:
      "\<lbrakk>tro_tag TCBReply; ko = Some (TCB tcb); ko' = Some (TCB tcb');
        \<exists>ctxt'. tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                            tcb_state := new_st, tcb_fault := None,
                            tcb_bound_notification := ntfn', tcb_caller := cap',
                            tcb_ctable := ccap'\<rparr>;
        new_st = Running \<or> (tcb_fault tcb \<noteq> None \<and> (new_st = Restart \<or> new_st = Inactive));
        tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
        reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
        reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
        direct_reply subjects aag l' tcb \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_receive:
      "\<lbrakk>tro_tag TCBReceive; ko = Some (TCB tcb); ko' = Some (TCB tcb');
        tcb' = tcb \<lparr>tcb_state := new_st, tcb_bound_notification := ntfn', tcb_caller := cap',
                    tcb_ctable := ccap'\<rparr>;
        new_st = Running \<or> (((new_st = Inactive \<and> call_blocked ep (tcb_state tcb)) \<or> (new_st = BlockedOnReply \<and> (allowed_call_blocked ep (tcb_state tcb)))));
        tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
        reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
        reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
        send_blocked_on ep (tcb_state tcb);
        aag_subjects_have_auth_to subjects aag Receive ep \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_restart:
      "\<lbrakk>tro_tag TCBRestart; ko  = Some (TCB tcb); ko' = Some (TCB tcb');
        tcb' = tcb\<lparr> tcb_arch := arch_tcb_context_set
                                         (arch_tcb_context_get (tcb_arch tcb')) (tcb_arch tcb),
                    tcb_state := tcb_state tcb', tcb_bound_notification := ntfn',
                    tcb_caller := cap',tcb_ctable := ccap'\<rparr>;
        (tcb_state tcb' = Restart \<and>
               arch_tcb_context_get (tcb_arch tcb') = arch_tcb_context_get (tcb_arch tcb)) \<or>
        (tcb_state tcb' = Running \<and>
        arch_tcb_context_get (tcb_arch tcb')
             = (arch_tcb_context_get (tcb_arch tcb))
                   (NextIP := arch_tcb_context_get (tcb_arch tcb) FaultIP));
        tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
        reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
        reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
        blocked_on ep (tcb_state tcb);
        aag_subjects_have_auth_to subjects aag Reset ep \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_generic:
      "\<lbrakk>tro_tag TCBGeneric; ko = Some (TCB tcb); ko' = Some (TCB tcb');
        tcb' = tcb \<lparr>tcb_bound_notification := ntfn', tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
        tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag ;
        reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
        reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap' \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_asidpool_clear:
      "\<lbrakk>tro_tag RASID; ko = Some (ArchObj (ASIDPool pool)); ko' = Some (ArchObj (ASIDPool pool'));
        asid_pool_integrity subjects aag pool pool'\<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_tcb_activate:
      "\<lbrakk>tro_tag TCBActivate; ko  = Some (TCB tcb); ko' = Some (TCB tcb');
        tcb' = tcb \<lparr> tcb_arch := arch_tcb_context_set
                              ((arch_tcb_context_get (tcb_arch tcb))(NextIP :=
                                           (arch_tcb_context_get (tcb_arch tcb)) FaultIP)
                               ) (tcb_arch tcb),
                     tcb_caller := cap', tcb_ctable := ccap',
                     tcb_state := Running, tcb_bound_notification := ntfn'\<rparr>;
        tcb_state tcb = Restart;
        reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
        reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap';
        tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
        activate \<rbrakk> \<comment> \<open>Anyone can do this\<close>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"
| tro_alt_cnode:
      "\<lbrakk>tro_tag RCNode; ko  = Some (CNode n content); ko' = Some (CNode n content');
        cnode_integrity subjects aag content content' \<rbrakk>
       \<Longrightarrow> integrity_obj_alt aag activate subjects l' ko ko'"

lemmas disj_cong' = arg_cong2[where f="(\<or>)"]


lemma troa_tro_alt[elim!]:
  "integrity_obj_atomic aag activate subjects l ko ko'
   \<Longrightarrow> integrity_obj_alt aag activate subjects l ko ko'"
  apply (erule integrity_obj_atomic.cases)

  text \<open>Single out TCB cases for special handling. We manually simplify
        the TCB updates in the tro_alt rules using @{thm tcb.equality}.\<close>
  (* somewhat slow 10s *)
  apply (find_goal \<open>match premises in "ko = Some (TCB _)" \<Rightarrow> succeed\<close>,
         ((erule(1) integrity_obj_alt.intros[OF tro_tagI],
                  (intro exI tcb.equality; solves \<open>simp\<close>));
          fastforce simp: reply_cap_deletion_integrity_def
                          tcb_bound_notification_reset_integrity_def
                          direct_reply_def))+

  text \<open>Remaining cases.\<close>
  apply (fastforce intro: integrity_obj_alt.intros[OF tro_tagI])+
  done



subsubsection \<open>ekheap and ready queues\<close>

text\<open>

  Assume two subjects can't interact. Then AINVS already implies that
  the ready queues of one won't change when the other is running.

  Assume two subjects can interact via an endpoint. (Probably an
  notification object for infoflow purposes.) Then the following says
  that the ready queues for the non-running subject can be extended by
  the running subject, e.g. by sending a message. Note these threads are
  added to the start of the queue.

\<close>

definition integrity_ready_queues
where
  "integrity_ready_queues aag subjects queue_labels rq rq' \<equiv>
     pasMayEditReadyQueues aag \<or> (queue_labels \<inter> subjects = {} \<longrightarrow> (\<exists>threads. threads @ rq = rq'))"

lemma integrity_ready_queues_refl[simp]: "integrity_ready_queues aag subjects ptr s s"
unfolding integrity_ready_queues_def by simp

inductive integrity_eobj for aag subjects l' eko eko'
where
  tre_lrefl: "\<lbrakk> l' \<in> subjects \<rbrakk> \<Longrightarrow> integrity_eobj aag subjects l' eko eko'"
| tre_orefl: "\<lbrakk> eko = eko' \<rbrakk> \<Longrightarrow> integrity_eobj aag subjects l' eko eko'"

subsubsection \<open>generic stuff : FIXME MOVE\<close>

lemma integrity_obj_activate:
  "integrity_obj aag False subjects l' ko ko' \<Longrightarrow>
   integrity_obj aag activate subjects l' ko ko'"
  unfolding integrity_obj_def
  apply (erule rtranclp_mono[THEN predicate2D, rotated])
  apply (rule predicate2I)
  by (erule integrity_obj_atomic.cases; (intro integrity_obj_atomic.intros; assumption | simp))

abbreviation object_integrity
where
  "object_integrity aag \<equiv> integrity_obj (aag :: 'a PAS) (pasMayActivate aag) {pasSubject aag}"


subsection \<open>auth_ipc_buffer\<close>

definition auth_ipc_buffers :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> obj_ref set"
where
  "auth_ipc_buffers s \<equiv>
     \<lambda>p. case (get_tcb p s) of
         None \<Rightarrow> {}
       | Some tcb \<Rightarrow>
           (case tcb_ipcframe tcb of
              cap.ArchObjectCap (arch_cap.PageCap False p' R vms _) \<Rightarrow>
                if AllowWrite \<in> R
                then (ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms)))
                                msg_align_bits)
                else {}
            | _ \<Rightarrow> {})"

(* MOVE *)
lemma caps_of_state_tcb':
  "\<lbrakk> get_tcb p s = Some tcb; option_map fst (tcb_cap_cases idx) = Some getF \<rbrakk> \<Longrightarrow> caps_of_state s (p, idx) = Some (getF tcb)"
  apply (drule get_tcb_SomeD)
  apply clarsimp
  apply (drule (1) cte_wp_at_tcbI [where t = "(p, idx)" and P = "(=) (getF tcb)", simplified])
  apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

(* MOVE *)
lemma caps_of_state_tcb_cap_cases:
  "\<lbrakk> get_tcb p s = Some tcb; idx \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> caps_of_state s (p, idx) = Some ((the (option_map fst (tcb_cap_cases idx))) tcb)"
  apply (clarsimp simp: dom_def)
  apply (erule caps_of_state_tcb')
  apply simp
  done

lemma auth_ipc_buffers_member_def:
  "x \<in> auth_ipc_buffers s p =
      (\<exists>tcb p' R vms xx. get_tcb p s = Some tcb
                       \<and> tcb_ipcframe tcb = (cap.ArchObjectCap (arch_cap.PageCap False p' R vms xx))
                       \<and> caps_of_state s (p, tcb_cnode_index 4) =
                                    Some (cap.ArchObjectCap (arch_cap.PageCap False p' R vms xx))
                       \<and> AllowWrite \<in> R
                       \<and> x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms)))
                                       msg_align_bits)"
  unfolding auth_ipc_buffers_def
  by (clarsimp simp: caps_of_state_tcb' split: option.splits cap.splits arch_cap.splits bool.splits)

subsection \<open>How User and device memory can change\<close>

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

inductive integrity_mem for aag subjects p ts ts' ipcbufs globals w w'
where
  trm_lrefl: "\<lbrakk> pasObjectAbs aag p \<in> subjects \<rbrakk>
     \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'" (* implied by wf and write *)
  | trm_orefl: "\<lbrakk> w = w' \<rbrakk> \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
  | trm_write: "\<lbrakk> aag_subjects_have_auth_to subjects aag Write p \<rbrakk> \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
  | trm_globals: "\<lbrakk> p \<in> globals \<rbrakk> \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
  | trm_ipc: "\<lbrakk> case_option False can_receive_ipc (ts p'); ts' p' = Some Structures_A.Running;
                p \<in> ipcbufs p'; pasObjectAbs aag p' \<notin> subjects
        \<rbrakk> \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"


abbreviation memory_integrity
where
  "memory_integrity X aag x t1 t2 ipc == integrity_mem (aag :: 'a PAS) {pasSubject aag} x t1 t2 ipc X"

inductive integrity_device for aag subjects p ts ts' w w'
where
  trd_lrefl: "\<lbrakk> pasObjectAbs aag p \<in> subjects \<rbrakk>
     \<Longrightarrow> integrity_device aag subjects p ts ts' w w'" (* implied by wf and write *)
  | trd_orefl: "\<lbrakk> w = w' \<rbrakk> \<Longrightarrow> integrity_device aag subjects p ts ts' w w'"
  | trd_write: "\<lbrakk> aag_subjects_have_auth_to subjects aag Write p \<rbrakk> \<Longrightarrow> integrity_device aag subjects p ts ts' w w'"

lemmas integrity_obj_simps [simp] = tro_orefl[OF refl]
    tro_lrefl[OF singletonI]
    trm_orefl[OF refl]
    trd_orefl[OF refl]
    tre_lrefl[OF singletonI]
    tre_orefl[OF refl]




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

(* FIXME MOVE*)
notation parent_of_rtrancl ("_ \<Turnstile> _ \<rightarrow>* _" [60,0,60] 60)

inductive cdt_direct_change_allowed for aag subjects tcbsts ptr
  where
  cdca_owned:
  "pasObjectAbs aag (fst ptr) \<in> subjects \<Longrightarrow> cdt_direct_change_allowed aag subjects tcbsts ptr"
| cdca_reply:
  "\<lbrakk>tcbsts (fst ptr) = Some tcbst; direct_call subjects aag ep tcbst; (snd ptr) = tcb_cnode_index 3\<rbrakk>
   \<Longrightarrow> cdt_direct_change_allowed aag subjects tcbsts ptr"

(* for the moment the only caps that can be affected by that indirect control are reply caps *)
definition cdt_change_allowed
  where
  "cdt_change_allowed aag subjects m tcbsts ptr \<equiv>
   \<exists> pptr. m \<Turnstile> pptr \<rightarrow>* ptr \<and> cdt_direct_change_allowed aag subjects tcbsts pptr"

lemma cdt_change_allowedI:
  "\<lbrakk>m \<Turnstile> pptr \<rightarrow>* ptr; cdt_direct_change_allowed aag subjects tcbsts pptr\<rbrakk>
   \<Longrightarrow> cdt_change_allowed aag subjects m tcbsts ptr"
  by (fastforce simp: cdt_change_allowed_def simp del: split_paired_Ex)

lemma cdt_change_allowedE:
  assumes "cdt_change_allowed aag subjects m tcbsts ptr"
  obtains pptr where "m \<Turnstile> pptr \<rightarrow>* ptr" "cdt_direct_change_allowed aag subjects tcbsts pptr"
  using assms by (fastforce simp: cdt_change_allowed_def simp del: split_paired_Ex)

lemma cdca_ccaI:
  "\<lbrakk>cdt_direct_change_allowed aag subjects tcbsts ptr\<rbrakk>
   \<Longrightarrow> cdt_change_allowed aag subjects m tcbsts ptr"
  by (fastforce simp: cdt_change_allowed_def simp del: split_paired_Ex)

lemmas cca_owned = cdt_change_allowedI[OF _ cdca_owned]
lemmas cca_reply' = cdt_change_allowedI[OF _ cdca_owned]
lemmas cca_direct[intro] = cdca_ccaI[OF cdca_owned]
lemmas cca_reply = cdca_ccaI[OF cdca_reply]

lemma cca_direct_single[intro]:
  "is_subject aag (fst ptr) \<Longrightarrow> cdt_change_allowed aag {pasSubject aag} m kh ptr"
  apply (rule cca_direct) by blast

(* FIXME get a coherent naming scheme *)
abbreviation cdt_change_allowed'
where
  "cdt_change_allowed' aag ptr s \<equiv> cdt_change_allowed aag {pasSubject aag} (cdt s)
(tcb_states_of_state s) ptr"



text\<open>
  ptr is the slot we currently looking at
  s is the initial state (v should be coherent with s)
  v = (initial parent of ptr, initial "originality" of ptr)
  v' = (final parent of ptr, final "originality" of ptr)
\<close>
definition integrity_cdt
  :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> cdt \<Rightarrow> (obj_ref \<Rightarrow> thread_state option)
       \<Rightarrow> cslot_ptr \<Rightarrow> (cslot_ptr option \<times> bool) \<Rightarrow> (cslot_ptr option \<times> bool) \<Rightarrow> bool"
where
  "integrity_cdt aag subjects m tcbsts ptr v v'
     \<equiv> v = v' \<or> cdt_change_allowed aag subjects m tcbsts ptr"

lemma integrity_cdtE:
  assumes hyp:"integrity_cdt aag subjects m tcbsts ptr v v'"
  obtains "v = v'" | "cdt_change_allowed aag subjects m tcbsts ptr"
  using hyp integrity_cdt_def by blast

abbreviation integrity_cdt_state
where
  "integrity_cdt_state aag subjects s s' \<equiv>
   (\<forall>x. integrity_cdt aag subjects (cdt s) (tcb_states_of_state s) x
                      (cdt s x,is_original_cap s x) (cdt s' x, is_original_cap s' x))"

abbreviation cdt_integrity
where
  "cdt_integrity aag \<equiv> integrity_cdt (aag :: 'a PAS) {pasSubject aag} "

abbreviation cdt_integrity_state
where
  "cdt_integrity_state aag s s' \<equiv>
   (\<forall>x. integrity_cdt (aag :: 'a PAS) {pasSubject aag} (cdt s) (tcb_states_of_state s) x
                      (cdt s x,is_original_cap s x) (cdt s' x, is_original_cap s' x))"

lemma integrity_cdt_refl[simp]: "integrity_cdt aag subjects m kh ptr v v"
  by (simp add: integrity_cdt_def)

lemma integrity_cdt_change_allowed[simp,intro]:
  "cdt_change_allowed aag subjects m kh ptr \<Longrightarrow> integrity_cdt aag subjects m kh ptr v v'"
  by (simp add: integrity_cdt_def)

lemmas integrity_cdt_intros = integrity_cdt_refl integrity_cdt_change_allowed

lemmas integrity_cdt_direct = cca_direct[THEN  integrity_cdt_change_allowed]



text\<open>
  m is the cdt of the initial state
  tcbsts are tcb_states_of_state of the initial state
  ptr is the slot we currently looking at
  l and l' are the initial and final list of children of ptr
\<close>
definition integrity_cdt_list
  :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> cdt \<Rightarrow> (obj_ref \<Rightarrow> thread_state option) \<Rightarrow> cslot_ptr \<Rightarrow>
      (cslot_ptr list) \<Rightarrow> (cslot_ptr list) \<Rightarrow> bool"
where
  "integrity_cdt_list aag subjects m tcbsts ptr l l'
     \<equiv> (filtered_eq (cdt_change_allowed aag subjects m tcbsts) l l') \<or>
        cdt_change_allowed aag subjects m tcbsts ptr"

abbreviation integrity_cdt_list_state
where
  "integrity_cdt_list_state aag subjects s s' \<equiv>
     (\<forall>x. integrity_cdt_list aag subjects (cdt s) (tcb_states_of_state s) x (cdt_list s x) (cdt_list s' x))"

abbreviation cdt_list_integrity
where
  "cdt_list_integrity aag == integrity_cdt_list (aag :: 'a PAS) {pasSubject aag}"

abbreviation cdt_list_integrity_state
where
  "cdt_list_integrity_state aag  s s' \<equiv>
     (\<forall>x. integrity_cdt_list (aag :: 'a PAS) {pasSubject aag} (cdt s) (tcb_states_of_state s) x
                             (cdt_list s x) (cdt_list s' x))"

lemma integrity_cdt_list_refl[simp]: "integrity_cdt_list aag subjects m kh ptr v v"
  by (simp add: integrity_cdt_list_def)

lemma integrity_cdt_list_filt:
  "filtered_eq (cdt_change_allowed aag subjects m kh) l l' \<Longrightarrow> integrity_cdt_list aag subjects m kh ptr l l'"
  by (simp add: integrity_cdt_list_def)
lemma integrity_cdt_list_change_allowed:
  "cdt_change_allowed aag subjects m kh ptr \<Longrightarrow> integrity_cdt_list aag subjects m kh ptr l l'"
  by (simp add: integrity_cdt_list_def)

lemmas integrity_cdt_list_intros = integrity_cdt_list_filt integrity_cdt_list_change_allowed

lemma integrity_cdt_listE:
  assumes hyp:"integrity_cdt_list aag subjects m kh ptr l l'"
  obtains "filtered_eq (cdt_change_allowed aag subjects m kh) l l'" |
          "cdt_change_allowed aag subjects m kh ptr"
  using hyp integrity_cdt_list_def by blast



subsection \<open>How other stuff can change\<close>

definition integrity_interrupts
  :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> irq \<Rightarrow> (obj_ref \<times> irq_state) \<Rightarrow> (obj_ref \<times> irq_state) \<Rightarrow> bool"
where
  "integrity_interrupts aag subjects irq v v'
     \<equiv> v = v' \<or> pasIRQAbs aag irq \<in> subjects"

lemma integrity_interrupts_refl[simp]: "integrity_interrupts aag subjects ptr v v"
  by (simp add: integrity_interrupts_def)

definition integrity_asids :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> asid \<Rightarrow> obj_ref option \<Rightarrow> obj_ref option \<Rightarrow> bool"
where
  "integrity_asids aag subjects asid pp_opt pp_opt'
     \<equiv> pp_opt = pp_opt' \<or> (\<forall> asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid \<longrightarrow> pasASIDAbs aag asid' \<in> subjects)"

lemma integrity_asids_refl[simp]: "integrity_asids aag subjects ptr s s"
  by (simp add: integrity_asids_def)

subsection \<open>General integrity\<close>

text\<open>

Half of what we ultimately want to say: that the parts of the
system state that change are allowed to by the labelling @{term
"aag"}.

The other half involves showing that @{term "aag"} concords with the
policy. See @{term "state_objs_to_policy s"} and @{term "pas_refined aag s"}.

\<close>

definition integrity_subjects
  :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> bool \<Rightarrow> obj_ref set \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "integrity_subjects subjects aag activate X s s' \<equiv>
         (\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x)) \<and>
         (\<forall>x. integrity_eobj aag subjects (pasObjectAbs aag x) (ekheap s x) (ekheap s' x)) \<and>
         (\<forall>x. integrity_mem aag subjects x (tcb_states_of_state s) (tcb_states_of_state s')
                       (auth_ipc_buffers s) X
                       (underlying_memory (machine_state s) x)
                       (underlying_memory (machine_state s') x)) \<and>
         (\<forall>x. integrity_device aag subjects x (tcb_states_of_state s) (tcb_states_of_state s')
                       (device_state (machine_state s) x)
                       (device_state (machine_state s') x)) \<and>
         integrity_cdt_state aag subjects s s'\<and>
         integrity_cdt_list_state aag subjects s s' \<and>
         (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s x, interrupt_states s x)
                                   (interrupt_irq_node s' x, interrupt_states s' x)) \<and>
         (\<forall>x. integrity_asids aag subjects x (arm_asid_table (arch_state s) (asid_high_bits_of x))
                              (arm_asid_table (arch_state s') (asid_high_bits_of x))) \<and>
         (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d) (ready_queues s d p)
                                       (ready_queues s' d p))"

abbreviation integrity
where
  "integrity pas \<equiv> integrity_subjects {pasSubject pas} pas (pasMayActivate pas)"



section \<open>Integrity transitivity\<close>

subsection \<open>Object integrity transitivity\<close>

lemma clear_asidpool_trans[elim]:
  "\<lbrakk>asid_pool_integrity subjects aag pool pool';
    asid_pool_integrity subjects aag pool' pool''\<rbrakk>
   \<Longrightarrow> asid_pool_integrity subjects aag pool pool''"
  unfolding asid_pool_integrity_def
  apply clarsimp
  apply (drule_tac x=x in spec)+
  apply auto
  done

lemma tcb_bound_notification_reset_integrity_trans[elim]:
  "\<lbrakk> tcb_bound_notification_reset_integrity ntfn ntfn' subjects aag;
    tcb_bound_notification_reset_integrity ntfn' ntfn'' subjects aag \<rbrakk>
    \<Longrightarrow> tcb_bound_notification_reset_integrity ntfn ntfn'' subjects aag"
  by (auto simp: tcb_bound_notification_reset_integrity_def)

lemma reply_cap_deletion_integrity_trans[elim]:
  "\<lbrakk> reply_cap_deletion_integrity subjects aag cap cap';
    reply_cap_deletion_integrity subjects aag cap' cap'' \<rbrakk>
    \<Longrightarrow> reply_cap_deletion_integrity subjects aag cap cap''"
  by (auto simp: reply_cap_deletion_integrity_def)


lemma cnode_integrity_trans[elim]:
  "\<lbrakk> cnode_integrity subjects aag cont cont';
    cnode_integrity subjects aag cont' cont'' \<rbrakk>
    \<Longrightarrow> cnode_integrity subjects aag cont cont''"
   unfolding cnode_integrity_def
   apply (intro allI)
   apply (drule_tac x=l in spec)+
   by fastforce

lemma tcb_bound_notification_reset_eq_or_none:
  "tcb_bound_notification_reset_integrity ntfn ntfn' subjects aag \<Longrightarrow> ntfn = ntfn' \<or> ntfn' = None"
  by (auto simp: tcb_bound_notification_reset_integrity_def)


lemma tro_alt_trans_spec: (* this takes a long time to process *)
  "\<lbrakk>integrity_obj_alt aag activate es subjects ko ko';
    integrity_obj_alt aag activate es subjects ko' ko'' \<rbrakk> \<Longrightarrow>
    integrity_obj_alt aag activate es subjects ko ko''"
  (* We need to consider nearly 200 cases, one for each possible pair
     of integrity steps. We use the tro_tags to select subsets of goals
     that can be solved by the same method. *)

  (* Expand the first integrity step *)
  apply (erule integrity_obj_alt.cases[where ko=ko and ko'=ko'])

  (* LRefl and ORefl trivially collapse into the second integrity step *)
  apply (find_goal \<open>match premises in "tro_tag LRefl" \<Rightarrow> -\<close>)
  subgoal by (rule tro_alt_lrefl, simp)

  apply (find_goal \<open>match premises in "tro_tag ORefl" \<Rightarrow> -\<close>)
  subgoal by simp

  (* Now re-tag the first step with tro_tag' *)
  apply (all \<open>simp only:tro_tag_to_prime\<close>)
  (* Expand the second integrity step, which will be tagged with tro_tag *)
  apply (all \<open>erule integrity_obj_alt.cases\<close>)

  (* There are some special cases that would be too slow or unsolvable by the bulk tactics.
     We move them up here and solve manually *)
  apply (find_goal \<open>match premises in "tro_tag' TCBReply" and "tro_tag TCBActivate" \<Rightarrow> -\<close>)
  apply (clarsimp, rule tro_alt_tcb_reply[OF tro_tagI refl refl],
         (rule exI; rule tcb.equality; simp add: arch_tcb_context_set_def); fastforce)

  apply (find_goal \<open>match premises in "tro_tag' TCBReceive" and "tro_tag TCBReply" \<Rightarrow> -\<close>)
  apply (clarsimp, rule tro_alt_tcb_reply[OF tro_tagI refl refl],
         (rule exI; rule tcb.equality;
          simp add: arch_tcb_context_set_def);
         fastforce simp: indirect_send_def direct_send_def direct_reply_def
                         allowed_call_blocked_def)

  apply (find_goal \<open>match premises in "tro_tag TCBGeneric" and "tro_tag' TCBRestart" \<Rightarrow> -\<close>)
  subgoal
    apply (erule integrity_obj_alt.intros[simplified tro_tag_to_prime])
            apply (rule refl | assumption
                  | fastforce intro: tcb.equality
                  | (erule tcb_bound_notification_reset_integrity_trans
                           reply_cap_deletion_integrity_trans;
                     fastforce))+
    done

  apply (find_goal \<open>match premises in "tro_tag TCBActivate" and "tro_tag' TCBRestart" \<Rightarrow> -\<close>)
  apply (rule tro_alt_tcb_restart[OF tro_tagI],
                 rule refl,
                assumption,
               (* somehow works better than tcb.equality *)
               (simp only: tcb.splits; simp),
              force+)[1]

  apply (find_goal \<open>match premises in "tro_tag REp" and "tro_tag' REp" \<Rightarrow> -\<close>)
  subgoal by (erule integrity_obj_alt.intros, (rule refl | assumption)+)

  (* Select groups of subgoals by tag, then solve with the given methods *)
  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag LRefl"]\<close>
             | time_methods \<open>solves \<open>
                   fastforce intro: tro_alt_lrefl\<close>\<close>\<close>)

  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag ORefl"]\<close>
             | time_methods \<open>solves \<open>
                   drule sym[where t="ko''"];
                   erule integrity_obj_alt.intros[simplified tro_tag_to_prime];
                   solves \<open>simp\<close>\<close>\<close>\<close>)

  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag RNtfn"] thin_rl[of "tro_tag' RNtfn"]\<close>
             | time_methods \<open>solves \<open>
                   fastforce intro: tro_alt_ntfn\<close>\<close>\<close>)

  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag REp"]
                    | erule thin_rl[of "tro_tag' REp"]
                    | erule thin_rl[of "tro_tag RASID"]
                    | erule thin_rl[of "tro_tag' RASID"]
                    | erule thin_rl[of "tro_tag EpUnblock"]
                    | erule thin_rl[of "tro_tag' EpUnblock"]
                    | erule thin_rl[of "tro_tag RCNode"]
                    | erule thin_rl[of "tro_tag' RCNode"]\<close>
             | time_methods \<open>solves \<open>
                   fastforce intro: integrity_obj_alt.intros tcb.equality
                             simp: indirect_send_def direct_send_def\<close>\<close>\<close>)

  (* TCB-TCB steps, somewhat slow *)
  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag TCBGeneric"]\<close>
             | time_methods \<open>solves \<open>
                    erule integrity_obj_alt.intros[simplified tro_tag_to_prime],
                    (assumption | rule refl
                    | ((erule exE)+)?, (rule exI)?, force intro: tcb.equality)+\<close>\<close>\<close>)

  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag' TCBGeneric"]\<close>
             | time_methods \<open>solves \<open>
                    erule integrity_obj_alt.intros,
                    (assumption | rule refl
                    | (elim exE)?, (intro exI)?, fastforce intro: tcb.equality
                    | fastforce simp: indirect_send_def direct_send_def direct_call_def direct_reply_def
                                dest: tcb_bound_notification_reset_eq_or_none)+\<close>\<close>\<close>)

  apply (time_methods \<open>
           succeeds \<open>match premises in T: "tro_tag _" and T': "tro_tag' _" \<Rightarrow>
                                       \<open>print_fact T, print_fact T'\<close>\<close>,
           fastforce intro: integrity_obj_alt.intros tcb.equality
                     simp: indirect_send_def direct_send_def direct_call_def direct_reply_def
                           send_blocked_on_def3 call_blocked_def allowed_call_blocked_def\<close>)+
  done

lemma tro_alt_reflp[intro!]:
  "reflp (integrity_obj_alt aag activate es subjects)"
  by (rule reflpI) (rule tro_alt_orefl; blast)

lemma tro_alt_transp[intro!]:
  "transp (integrity_obj_alt aag activate es subjects)"
  by (rule transpI) (rule tro_alt_trans_spec)



lemma tro_tro_alt[elim!]:
  "integrity_obj aag activate es subjects ko ko'
  \<Longrightarrow> integrity_obj_alt aag activate es subjects ko ko'"
  unfolding integrity_obj_def
  by (subst rtranclp_id[symmetric]; fastforce elim: rtranclp_mono[THEN predicate2D,rotated])

lemmas integrity_objE = tro_tro_alt[THEN integrity_obj_alt.cases
                                          [simplified tro_tag_def True_implies_equals]]



lemma tro_trans:
  "\<lbrakk>integrity_obj_state aag activate es s s'; integrity_obj_state aag activate es s' s''\<rbrakk>
    \<Longrightarrow> integrity_obj_state aag activate es s s''"
   unfolding integrity_obj_def
  apply clarsimp
  apply (drule_tac x = x in spec)+
  by force

lemma tre_trans:
  "\<lbrakk>(\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh x) (ekh' x));
    (\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh' x) (ekh'' x)) \<rbrakk> \<Longrightarrow>
    (\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh x) (ekh'' x))"
by (fastforce elim!: integrity_eobj.cases
              intro: integrity_eobj.intros)



subsection \<open>CDT integrity transitivity\<close>

lemma tcb_caller_slot_empty_on_recieve:
  "\<lbrakk> valid_mdb s ; valid_objs s; kheap s tcb_ptr = Some (TCB tcb); ep_recv_blocked ep (tcb_state tcb) \<rbrakk> \<Longrightarrow>
   tcb_caller tcb = NullCap \<and> cdt s (tcb_ptr,(tcb_cnode_index 3)) = None \<and>
   descendants_of (tcb_ptr,(tcb_cnode_index 3)) (cdt s) = {}"
   apply (simp only:valid_objs_def)
   apply (drule bspec,fastforce)
   apply (simp add:valid_obj_def)
   apply (simp only:valid_tcb_def)
   apply (drule conjunct1)
   apply (drule_tac x="the (tcb_cap_cases (tcb_cnode_index 3))" in  bspec)
    apply (fastforce simp:tcb_cap_cases_def)
   apply (simp add:tcb_cap_cases_def split: thread_state.splits)
  apply (subgoal_tac "caps_of_state s (tcb_ptr, tcb_cnode_index 3) = Some NullCap")
   apply (simp only: valid_mdb_def2, drule conjunct1)
   apply (intro conjI)
    apply (simp add: mdb_cte_at_def)
    apply (rule classical)
    apply fastforce
   apply (rule mdb_cte_at_no_descendants, fastforce+)[1]
  apply (fastforce simp add: tcb_cnode_map_def caps_of_state_tcb_index_trans[OF get_tcb_rev])
done


(* FIXME MOVE next to tcb_states_of_state definition *)
lemma tcb_states_of_state_kheap:
   "\<lbrakk>kheap s slot = Some (TCB tcb)\<rbrakk>
    \<Longrightarrow> tcb_states_of_state s slot = Some (tcb_state tcb)"
  by (simp add:tcb_states_of_state_def get_tcb_def split: option.splits kernel_object.splits)

lemma tcb_states_of_state_kheapI:
   "\<lbrakk>kheap s slot = Some (TCB tcb); tcb_state tcb = tcbst\<rbrakk>
    \<Longrightarrow> tcb_states_of_state s slot = Some tcbst"
  by (simp add:tcb_states_of_state_def get_tcb_def split: option.splits kernel_object.splits)

lemma tcb_states_of_state_kheapD:
   "tcb_states_of_state s slot = Some tcbst \<Longrightarrow>
    \<exists> tcb. kheap s slot = Some (TCB tcb) \<and> tcb_state tcb = tcbst"
  by (simp add:tcb_states_of_state_def get_tcb_def split: option.splits kernel_object.splits)

lemma tcb_states_of_state_kheapE:
   assumes "tcb_states_of_state s slot = Some tcbst"
   obtains tcb where "kheap s slot = Some (TCB tcb)" "tcb_state tcb = tcbst"
  using assms tcb_states_of_state_kheapD by blast

lemma cdt_direct_change_allowed_backward:
  "\<lbrakk>integrity_obj_state aag activate subjects s s';
    cdt_direct_change_allowed aag subjects (tcb_states_of_state s') ptr\<rbrakk> \<Longrightarrow>
    cdt_direct_change_allowed aag subjects (tcb_states_of_state s) ptr"
  apply (erule cdt_direct_change_allowed.cases)
   subgoal by (rule cdca_owned)
  apply (erule tcb_states_of_state_kheapE)
  by (drule spec,
      erule integrity_objE, erule cdca_owned;
      (elim exE)?;
      simp;
      rule cdca_reply[rotated], assumption, assumption,
        fastforce elim:tcb_states_of_state_kheapI simp:direct_call_def)

lemma cdt_change_allowed_to_child:
  "cdt_change_allowed aag subjects m tcbsts pptr \<Longrightarrow> m ptr = Some pptr
   \<Longrightarrow> cdt_change_allowed aag subjects m tcbsts ptr"
  apply (elim cdt_change_allowedE)
  apply (erule cdt_change_allowedI[rotated])
  by(fastforce intro: rtrancl_into_rtrancl simp: cdt_parent_of_def)

lemma cdt_change_allowed_backward:
  "\<lbrakk>integrity_obj_state aag activate subjects s s';
    integrity_cdt_state aag subjects s s';
    cdt_change_allowed aag subjects (cdt s') (tcb_states_of_state s') ptr\<rbrakk> \<Longrightarrow>
    cdt_change_allowed aag subjects (cdt s) (tcb_states_of_state s) ptr"
  apply (elim cdt_change_allowedE)
  apply (drule(1) cdt_direct_change_allowed_backward)
  apply (erule rtrancl_induct)
  subgoal by (rule cdca_ccaI)
  apply (rename_tac pptr0 ptr)
  apply (frule_tac x=ptr in spec)
  apply (elim integrity_cdtE; simp; elim conjE)
  apply (erule cdt_change_allowed_to_child)
  by(simp add: cdt_parent_of_def)

lemma trcdt_trans:
  "\<lbrakk>integrity_cdt_state aag subjects s s' ;
    integrity_obj_state aag activate subjects s s' ;
    integrity_cdt_state aag subjects s' s'' \<rbrakk>
   \<Longrightarrow> integrity_cdt_state aag subjects s s''"
  apply (intro allI)
  apply (frule_tac x=x in spec)
  apply (frule_tac x=x in spec[where P = "\<lambda>x. integrity_cdt _ _ (cdt s') _ x (_ x) (_ x)"])
  apply (erule integrity_cdtE)+
  apply simp
  by (blast dest: cdt_change_allowed_backward)+

lemma trcdtlist_trans:
  "\<lbrakk>integrity_cdt_list_state aag subjects s s' ;
    integrity_obj_state aag activate subjects s s' ;
    integrity_cdt_state aag subjects s s' ;
    integrity_cdt_list_state aag subjects s' s'' \<rbrakk>
   \<Longrightarrow> integrity_cdt_list_state aag subjects s s''"
  apply (intro allI)
  apply (drule_tac x=x in spec [where P="\<lambda>ptr. integrity_cdt_list _ _ _ _ ptr (_ ptr) (_ ptr)"] )+
  apply (erule integrity_cdt_listE)+
      apply (rule integrity_cdt_list_filt)
      apply (simp del: split_paired_All split_paired_Ex)
      apply (erule weaken_filter_eq')
  by (blast intro: integrity_cdt_list_intros dest: cdt_change_allowed_backward)+


subsection \<open>Main integrity transitivity\<close>


lemma trinterrupts_trans:
  "\<lbrakk> (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s x, interrupt_states s x) (interrupt_irq_node s' x, interrupt_states s' x));
    (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s' x, interrupt_states s' x) (interrupt_irq_node s'' x, interrupt_states s'' x)) \<rbrakk>
   \<Longrightarrow> (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s x, interrupt_states s x) (interrupt_irq_node s'' x, interrupt_states s'' x))"
  apply (simp add: integrity_interrupts_def
                  del: split_paired_All)
  apply metis
  done

lemma trasids_trans:
  "\<lbrakk> (\<forall>x. integrity_asids aag subjects x (arm_asid_table (arch_state s) (asid_high_bits_of x)) (arm_asid_table (arch_state s') (asid_high_bits_of x)));
     (\<forall>x. integrity_asids aag subjects x (arm_asid_table (arch_state s') (asid_high_bits_of x)) (arm_asid_table (arch_state s'') (asid_high_bits_of x)))\<rbrakk>
   \<Longrightarrow>
     (\<forall>x. integrity_asids aag subjects x (arm_asid_table (arch_state s) (asid_high_bits_of x)) (arm_asid_table (arch_state s'') (asid_high_bits_of x)))"
  apply (clarsimp simp: integrity_asids_def)
  apply metis
  done

lemma trrqs_trans:
  "\<lbrakk> (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d) (ready_queues s d p) (ready_queues s' d p));
     (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d) (ready_queues s' d p) (ready_queues s'' d p)) \<rbrakk>
   \<Longrightarrow> (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d) (ready_queues s d p) (ready_queues s'' d p))"
apply (clarsimp simp: integrity_ready_queues_def)
apply (metis append_assoc)
done

(* FIXME RENAME *)
lemma tsos_tro:
  "\<lbrakk>integrity_obj_state aag activate subjects s s'; tcb_states_of_state s' p = Some a;
    receive_blocked_on ep a; pasObjectAbs aag p \<notin> subjects \<rbrakk> \<Longrightarrow> tcb_states_of_state s p = Some a"
  apply (drule_tac x = p in spec)
  apply (erule integrity_objE, simp_all add: tcb_states_of_state_def get_tcb_def)
  by fastforce+

lemma can_receive_ipc_backward:
  "\<lbrakk>integrity_obj_state aag activate subjects s s'; tcb_states_of_state s' p = Some a;
    can_receive_ipc a; pasObjectAbs aag p \<notin> subjects \<rbrakk>
   \<Longrightarrow> case tcb_states_of_state s p of None \<Rightarrow> False | Some x \<Rightarrow> can_receive_ipc x"
  apply (drule_tac x = p in spec)
  apply (erule integrity_objE;
         (fastforce simp: tcb_states_of_state_def get_tcb_def
                         call_blocked_def allowed_call_blocked_def
                   split: option.splits kernel_object.splits
         | cases a \<comment> \<open>only split when needed\<close>)+)
  done



lemma auth_ipc_buffers_tro:
  "\<lbrakk>integrity_obj_state aag activate subjects s s'; x \<in> auth_ipc_buffers s' p;
          pasObjectAbs aag p \<notin> subjects \<rbrakk>
  \<Longrightarrow> x \<in> auth_ipc_buffers s p "
  by (drule_tac x = p in spec)
     (erule integrity_objE;
      fastforce simp: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def
               split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)


lemma auth_ipc_buffers_tro_fwd:
  "\<lbrakk>integrity_obj_state aag activate subjects s s'; x \<in> auth_ipc_buffers s p;
          pasObjectAbs aag p \<notin> subjects \<rbrakk>
  \<Longrightarrow> x \<in> auth_ipc_buffers s' p "
  by (drule_tac x = p in spec)
     (erule integrity_objE;
      fastforce simp: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def
               split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)


lemma tsos_tro_running:
  "\<lbrakk>\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x);
       tcb_states_of_state s p = Some Structures_A.Running;
          pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> tcb_states_of_state s' p = Some Structures_A.Running"
  by (drule_tac x = p in spec)
     (erule integrity_objE,
         simp_all add: tcb_states_of_state_def get_tcb_def indirect_send_def
                       direct_send_def direct_call_def direct_reply_def call_blocked_def allowed_call_blocked_def)


lemma integrity_trans:
  assumes t1: "integrity_subjects subjects aag activate X s s'"
  and     t2: "integrity_subjects subjects aag activate X s' s''"
  shows  "integrity_subjects subjects aag activate X s s''"
proof -
  from t1 have tro1: "integrity_obj_state aag activate subjects s s'"
    unfolding integrity_subjects_def by simp
  from t2 have tro2: "integrity_obj_state aag activate subjects s' s''"
    unfolding integrity_subjects_def by simp

  have intm: "\<forall>x. integrity_mem aag subjects x
                  (tcb_states_of_state s) (tcb_states_of_state s'') (auth_ipc_buffers s) X
                  (underlying_memory (machine_state s) x)
                  (underlying_memory (machine_state s'') x)" (is "\<forall>x. ?P x s s''")
  proof
    fix x
    from t1 t2 have m1: "?P x s s'" and m2: "?P x s' s''" unfolding integrity_subjects_def by auto

    from m1 show "?P x s s''"
    proof cases
      case trm_lrefl thus ?thesis by (rule integrity_mem.intros)
    next
      case trm_globals thus ?thesis by (rule integrity_mem.intros)
    next
      case trm_orefl
      from m2 show ?thesis
      proof cases
        case (trm_ipc p')

        show ?thesis
        proof (rule integrity_mem.trm_ipc)
          from trm_ipc show "case_option False can_receive_ipc (tcb_states_of_state s p')"
            by (fastforce split: option.splits dest: can_receive_ipc_backward [OF tro1])

          from trm_ipc show "x \<in> auth_ipc_buffers s p'"
            by (fastforce split: option.splits intro: auth_ipc_buffers_tro [OF tro1])
        qed (simp_all add: trm_ipc)
      qed (auto simp add: trm_orefl intro: integrity_mem.intros)
    next
      case trm_write thus ?thesis by (rule integrity_mem.intros)
    next
      case (trm_ipc p')
      note trm_ipc1 = trm_ipc

      from m2 show ?thesis
      proof cases
        case trm_orefl
        thus ?thesis using trm_ipc1
          by (auto intro!: integrity_mem.trm_ipc simp add: restrict_map_Some_iff elim!: tsos_tro_running [OF tro2, rotated])
      next
        case (trm_ipc p'')
        show ?thesis
        proof (cases "p' = p''")
          case True thus ?thesis using trm_ipc trm_ipc1 by (simp add: restrict_map_Some_iff)
        next
          (* 2 tcbs sharing same IPC buffer, we can appeal to either t1 or t2 *)
          case False
          thus ?thesis using trm_ipc1
            by (auto intro!: integrity_mem.trm_ipc simp add: restrict_map_Some_iff elim!: tsos_tro_running [OF tro2, rotated])
        qed
      qed (auto simp add: trm_ipc intro: integrity_mem.intros)
    qed
  qed

  moreover have "\<forall>x. integrity_device aag subjects x
                  (tcb_states_of_state s) (tcb_states_of_state s'')
                  (device_state (machine_state s) x)
                  (device_state (machine_state s'') x)" (is "\<forall>x. ?P x s s''")
  proof
    fix x
    from t1 t2 have m1: "?P x s s'" and m2: "?P x s' s''" unfolding integrity_subjects_def by auto

    from m1 show "?P x s s''"
    proof cases
      case trd_lrefl thus ?thesis by (rule integrity_device.intros)
    next
      case torel1: trd_orefl
      from m2 show ?thesis
      proof cases
        case (trd_lrefl) thus ?thesis by (rule integrity_device.trd_lrefl)
      next
        case trd_orefl thus ?thesis
          by (simp add:torel1)
      next
        case trd_write thus ?thesis by (rule integrity_device.trd_write)
      qed
    next
      case trd_write thus ?thesis by (rule integrity_device.intros)
    qed
  qed
  thus ?thesis using tro_trans[OF tro1 tro2] t1 t2 intm
    apply (clarsimp simp add: integrity_subjects_def simp del:  split_paired_All)
    apply (frule(2) trcdt_trans)
    apply (frule(3) trcdtlist_trans)
    apply (frule(1) trinterrupts_trans[simplified])
    apply (frule(1) trasids_trans[simplified])
    apply (frule(1) tre_trans[simplified])
    apply (frule(1) trrqs_trans[simplified])
    by blast
qed

lemma integrity_refl [simp]:
  "integrity_subjects S aag activate X s s"
unfolding integrity_subjects_def
by simp

section \<open>Generic AC stuff\<close>

subsection \<open>Basic integrity lemmas\<close>

(* Tom says that Gene Wolfe says that autarchy \<equiv> self authority. *)

lemma integrity_update_autarch:
  "\<lbrakk> integrity aag X st s; is_subject aag ptr \<rbrakk>
   \<Longrightarrow> integrity aag X st (s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr>)"
  unfolding integrity_subjects_def
  apply (intro conjI,simp_all)
   apply clarsimp
   apply (drule_tac x = x in spec, erule integrity_mem.cases)
   apply ((auto intro: integrity_mem.intros)+)[4]
   apply (erule trm_ipc, simp_all)
   apply (clarsimp simp: restrict_map_Some_iff tcb_states_of_state_def get_tcb_def)
  apply clarsimp
  apply (drule_tac x = x in spec, erule integrity_device.cases)
    apply (erule integrity_device.trd_lrefl)
   apply (erule integrity_device.trd_orefl)
  apply (erule integrity_device.trd_write)
  done

lemma set_object_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag ptr)\<rbrace>
     set_object ptr obj
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (rule integrity_update_autarch, simp_all)
  done

lemma tcb_states_of_state_trans_state[simp]:
  "tcb_states_of_state (trans_state f s) = tcb_states_of_state s"
  by (simp add: tcb_states_of_state_def get_tcb_exst_update)

lemma eintegrity_sa_update[simp]:
  "integrity aag X st (scheduler_action_update f s) = integrity aag X st s"
  by (simp add: integrity_subjects_def trans_state_update'[symmetric])

lemma trans_state_back[simp]:
  "trans_state (\<lambda>_. exst s) s = s"
  by simp

declare wrap_ext_op_det_ext_ext_def[simp]

crunch integrity[wp]: set_thread_state_ext "integrity aag X st"

crunch integrity_autarch: set_thread_state "integrity aag X st"

lemmas integrity_def = integrity_subjects_def

subsection \<open>Out of subject cap manipulation\<close>

(* FIXME MOVE *)
lemma all_children_descendants_of:
  "\<lbrakk> all_children P m ; p \<in> descendants_of q m ; P q \<rbrakk> \<Longrightarrow> P p "
  apply (simp add: descendants_of_def)
  apply (erule trancl_induct[where P=P])
  unfolding cdt_parent_of_def
   apply (erule(2) all_childrenD)+
  done

lemmas all_children_parent_of_trancl =
                    all_children_descendants_of[simplified descendants_of_def,simplified]

lemma all_children_parent_of_rtrancl:
  "\<lbrakk> all_children P m ; m \<Turnstile> q \<rightarrow>* p ; P q \<rbrakk> \<Longrightarrow> P p "
  by (drule rtranclD,elim conjE disjE; blast dest:all_children_parent_of_trancl)

lemma pas_refined_all_children':
  "\<lbrakk>valid_mdb s ; pas_refined aag s ; m = (cdt s) \<rbrakk> \<Longrightarrow>
   all_children (\<lambda>x. is_subject aag (fst x) \<or> is_transferable (caps_of_state s x)) m"
  apply (rule all_childrenI)
  apply (erule disjE)
   apply (simp add: pas_refined_def,elim conjE)
   apply (rule disjCI)
   apply (subgoal_tac
               "(pasObjectAbs aag (fst p), Control, pasObjectAbs aag (fst c)) \<in> pasPolicy aag")
    apply (fastforce elim: aag_wellformed_control_is_owns[THEN iffD1])
   apply (simp add: state_objs_to_policy_def auth_graph_map_def)
   apply (erule set_mp)
   apply (frule(1) sbta_cdt)
   apply force
  apply (rule disjI2)
  by (rule is_transferable_all_children[THEN all_childrenD]; solves \<open>simp\<close>)

lemmas pas_refined_all_children = pas_refined_all_children'[OF _ _ refl]

(* FIXME MOVE just after cte_wp_at_cases2 *)
lemma caps_of_state_def':
  "caps_of_state s slot =
    (case kheap s (fst slot) of
       Some (TCB tcb) \<Rightarrow> tcb_cnode_map tcb (snd slot)
     | Some (CNode sz content) \<Rightarrow> (if well_formed_cnode_n sz content then content (snd slot) else None)
     | _ \<Rightarrow> None)"
  by (fastforce simp: caps_of_state_cte_wp_at cte_wp_at_cases2
                split: option.splits kernel_object.splits)

lemma caps_of_state_cnode:
  "\<lbrakk>kheap s pos = Some (CNode sz content); well_formed_cnode_n sz content\<rbrakk> \<Longrightarrow>
   caps_of_state s (pos,addr) = content addr"
  by (simp add:caps_of_state_def')

lemma caps_of_state_tcb:
  "\<lbrakk>kheap s pos = Some (TCB tcb)\<rbrakk> \<Longrightarrow>
   caps_of_state s (pos,addr) = tcb_cnode_map tcb addr"
  by (simp add:caps_of_state_def')

(* FIXME MOVE next to tcb_cnode_cases_simps *)
lemma tcb_cnode_map_simps[simp]:
  "tcb_cnode_map tcb (tcb_cnode_index 0) = Some (tcb_ctable tcb)"
  "tcb_cnode_map tcb (tcb_cnode_index (Suc 0)) = Some (tcb_vtable tcb)"
  "tcb_cnode_map tcb (tcb_cnode_index 2) = Some (tcb_reply tcb)"
  "tcb_cnode_map tcb (tcb_cnode_index 3) = Some (tcb_caller tcb)"
  "tcb_cnode_map tcb (tcb_cnode_index 4) = Some (tcb_ipcframe tcb)"
  by (simp_all add: tcb_cnode_map_def)

(* FIXME MOVE *)
lemma valid_mdb_reply_mdb[elim!]:
  "valid_mdb s \<Longrightarrow> reply_mdb (cdt s) (caps_of_state s)"
  by (simp add:valid_mdb_def)

(* FIXME MOVE *)
lemma invs_reply_mdb[elim!]: "invs s \<Longrightarrow> reply_mdb (cdt s) (caps_of_state s)"
  by (simp add:invs_def valid_state_def valid_mdb_def)

lemma parent_of_rtrancl_no_descendant:
  "\<lbrakk>m \<Turnstile> pptr \<rightarrow>* ptr; descendants_of pptr m = {}\<rbrakk> \<Longrightarrow> pptr = ptr"
  by (fastforce simp add:rtrancl_eq_or_trancl descendants_of_def)

(* FIXME MOVE *)
lemma tcb_atD:
  "tcb_at ptr s \<Longrightarrow> \<exists>tcb. kheap s ptr = Some (TCB tcb)"
   by (cases "the (kheap s ptr)";fastforce simp:obj_at_def is_tcb_def)

(* FIXME MOVE *)
lemma tcb_atE:
  assumes hyp: "tcb_at ptr s"
  obtains tcb where "kheap s ptr = Some (TCB tcb)"
   using hyp[THEN tcb_atD] by blast

(*FIXME MOVE *)
lemma tcb_atI:
  "kheap s ptr = Some (TCB tcb) \<Longrightarrow> tcb_at ptr s"
  by (simp add:obj_at_def is_tcb_def)



lemma descendant_of_caller_slot:
  "\<lbrakk>valid_mdb s; valid_objs s; tcb_at t s\<rbrakk> \<Longrightarrow> descendants_of (t, tcb_cnode_index 3) (cdt s) = {}"
  apply (frule(1) tcb_caller_cap)
  apply (clarsimp simp add:cte_wp_at_caps_of_state is_cap_simps; elim disjE ;clarsimp)
  subgoal by (intro allI no_children_empty_desc[THEN iffD1] reply_cap_no_children)
  apply (drule valid_mdb_mdb_cte_at)
  apply (erule mdb_cte_at_no_descendants)
  apply (simp add:cte_wp_at_caps_of_state)
  done

lemma cca_to_transferable_or_subject:
  "\<lbrakk>valid_objs s; valid_mdb s; pas_refined aag s; cdt_change_allowed' aag ptr s \<rbrakk>
  \<Longrightarrow> is_subject aag (fst ptr) \<or> is_transferable (caps_of_state s ptr)"
  apply (elim cdt_change_allowedE cdt_direct_change_allowed.cases)
   apply (rule all_children_parent_of_rtrancl[OF pas_refined_all_children]; blast)
  apply (simp add:rtrancl_eq_or_trancl,elim disjE conjE)
   apply (simp add:direct_call_def, elim conjE)
   apply (drule tcb_states_of_state_kheapD, elim exE conjE)
   apply (frule(2) tcb_caller_slot_empty_on_recieve ,simp)
   apply (cases ptr,simp)
   apply (simp add:caps_of_state_tcb)
  apply (elim tcb_states_of_state_kheapE)
  apply (drule(2) descendant_of_caller_slot[OF _ _ tcb_atI])
  by (force simp add: descendants_of_def simp del:split_paired_All)

lemma is_transferable_weak_derived:
  "weak_derived cap cap' \<Longrightarrow> is_transferable_cap cap = is_transferable_cap cap'"
  unfolding is_transferable.simps weak_derived_def copy_of_def same_object_as_def
  by (fastforce simp: is_cap_simps split:cap.splits)

lemma aag_cdt_link_Control:
  "\<lbrakk> cdt s x = Some y; \<not> is_transferable(caps_of_state s x); pas_refined aag s \<rbrakk>
    \<Longrightarrow> (pasObjectAbs aag (fst y), Control, pasObjectAbs aag (fst x)) \<in> pasPolicy aag"
  by (fastforce elim: pas_refined_mem[rotated] sta_cdt)

lemma aag_cdt_link_DeleteDerived:
  "\<lbrakk> cdt s x = Some y; pas_refined aag s \<rbrakk>
    \<Longrightarrow> (pasObjectAbs aag (fst y), DeleteDerived, pasObjectAbs aag (fst x)) \<in> pasPolicy aag"
  by (fastforce elim: pas_refined_mem[rotated] sta_cdt_transferable)

lemma tcb_states_of_state_to_auth:
  "\<lbrakk>tcb_states_of_state s thread = Some tcbst; pas_refined aag s \<rbrakk>
   \<Longrightarrow> \<forall> (obj,auth) \<in> tcb_st_to_auth tcbst.
                  (pasObjectAbs aag thread, auth, pasObjectAbs aag obj) \<in> pasPolicy aag"

   apply clarsimp
   apply (erule pas_refined_mem[rotated])
   apply (rule sta_ts)
   apply (simp add:thread_states_def)
   done

lemma tcb_states_of_state_to_auth':
  "\<lbrakk>tcb_states_of_state s thread = Some tcbst; pas_refined aag s;
    (obj,auth) \<in> tcb_st_to_auth tcbst \<rbrakk>
   \<Longrightarrow> (pasObjectAbs aag thread, auth, pasObjectAbs aag obj) \<in> pasPolicy aag"
   using tcb_states_of_state_to_auth by blast

lemma ep_recv_blocked_def:
  "ep_recv_blocked ep st \<longleftrightarrow> (\<exists>pl. st = BlockedOnReceive ep pl)"
  by (simp split: thread_state.split)

lemma cdt_change_allowed_delete_derived:
  "valid_objs s \<Longrightarrow> valid_mdb s \<Longrightarrow> pas_refined aag s \<Longrightarrow> cdt_change_allowed' aag slot s
   \<Longrightarrow> aag_has_auth_to aag DeleteDerived (fst slot)"
  apply (elim cdt_change_allowedE cdt_direct_change_allowed.cases)
   apply (erule rtrancl_induct)
    apply (solves\<open>simp add: pas_refined_refl\<close>)
   apply (fastforce simp: cdt_parent_of_def
                    dest: aag_cdt_link_DeleteDerived
                   intro: aag_wellformed_delete_derived_trans)
  apply (clarsimp simp: direct_call_def ep_recv_blocked_def)
  apply (frule(1)tcb_states_of_state_to_auth)
  apply (elim tcb_states_of_state_kheapE)
  apply (frule(2) descendant_of_caller_slot[OF _ _ tcb_atI])
  apply (frule(1) parent_of_rtrancl_no_descendant)
  apply clarsimp
  by (rule aag_wellformed_delete_derived'[OF _ _ pas_refined_wellformed])

end

context pspace_update_eq begin

interpretation Arch . (*FIXME: arch_split*)

lemma integrity_update_eq[iff]:
  "tcb_states_of_state (f s) = tcb_states_of_state s"
  by (simp add: pspace tcb_states_of_state_def get_tcb_def)

end

subsection \<open>Various abbreviations\<close>

context begin interpretation Arch . (*FIXME: arch_split*)

definition label_owns_asid_slot :: "'a PAS \<Rightarrow> 'a \<Rightarrow> asid \<Rightarrow> bool"
where
  "label_owns_asid_slot aag l asid \<equiv>
     (l, Control, pasASIDAbs aag asid) \<in> pasPolicy aag"

definition cap_links_asid_slot :: "'a PAS \<Rightarrow> 'a \<Rightarrow> cap \<Rightarrow> bool"
where
  "cap_links_asid_slot aag l cap \<equiv> (\<forall>asid \<in> cap_asid' cap.
      label_owns_asid_slot aag l asid)"

abbreviation is_subject_asid :: "'a PAS \<Rightarrow> asid \<Rightarrow> bool"
where
  "is_subject_asid aag asid \<equiv> pasASIDAbs aag asid = pasSubject aag"

lemma clas_no_asid:
  "cap_asid' cap = {} \<Longrightarrow> cap_links_asid_slot aag l cap"
  unfolding cap_links_asid_slot_def by simp

definition cap_links_irq
where
  "cap_links_irq aag l cap \<equiv>
       \<forall>irq \<in> cap_irqs_controlled cap. (l, Control, pasIRQAbs aag irq) \<in> pasPolicy aag"

lemma cli_no_irqs:
  "cap_irqs_controlled cap = {} \<Longrightarrow> cap_links_irq aag l cap"
  unfolding cap_links_irq_def by simp

abbreviation is_subject_irq :: "'a PAS \<Rightarrow> irq \<Rightarrow> bool"
where
  "is_subject_irq aag irq \<equiv> pasIRQAbs aag irq = pasSubject aag"

definition aag_cap_auth :: "'a PAS \<Rightarrow> 'a \<Rightarrow> cap \<Rightarrow> bool"
where
  "aag_cap_auth aag l cap \<equiv>
      (\<forall>x \<in> obj_refs cap. \<forall>auth \<in> cap_auth_conferred cap. (l, auth, pasObjectAbs aag x) \<in> pasPolicy aag)
    \<and> (\<forall>x \<in> untyped_range cap. (l, Control, pasObjectAbs aag x) \<in> pasPolicy aag)
    \<and> cap_links_asid_slot aag l cap \<and> cap_links_irq aag l cap"

abbreviation pas_cap_cur_auth :: "'a PAS \<Rightarrow> cap \<Rightarrow> bool"
where
  "pas_cap_cur_auth aag cap \<equiv> aag_cap_auth aag (pasSubject aag) cap"

subsection \<open>Random lemmas that belong here\<close>

crunch integrity_autarch: as_user "integrity aag X st"

lemma owns_thread_owns_cspace:
  "\<lbrakk> is_subject aag thread; pas_refined aag s; get_tcb thread s = Some tcb; is_cnode_cap (tcb_ctable tcb); x \<in> obj_refs (tcb_ctable tcb)\<rbrakk>
    \<Longrightarrow> is_subject aag x"
  apply (drule get_tcb_SomeD)
  apply (drule cte_wp_at_tcbI[where t="(thread, tcb_cnode_index 0)" and P="\<lambda>cap. cap = tcb_ctable tcb", simplified])
  apply (auto simp: cte_wp_at_caps_of_state is_cap_simps cap_auth_conferred_def
              elim: caps_of_state_pasObjectAbs_eq [where p = "(thread, tcb_cnode_index 0)"])
  done



lemma is_subject_into_is_subject_asid:
  "\<lbrakk> cap_links_asid_slot aag (pasObjectAbs aag p) cap; is_subject aag p; pas_refined aag s;
         asid \<in> cap_asid' cap \<rbrakk>
     \<Longrightarrow> is_subject_asid aag asid"
  apply (clarsimp simp add: cap_links_asid_slot_def label_owns_asid_slot_def)
  apply (drule (1) bspec)
  apply (drule (1) pas_refined_Control)
  apply simp
  done

(* MOVE *)
lemma clas_caps_of_state:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk> \<Longrightarrow> cap_links_asid_slot aag (pasObjectAbs aag (fst slot)) cap"
apply (clarsimp simp add: cap_links_asid_slot_def label_owns_asid_slot_def pas_refined_def)
apply (blast dest: state_asids_to_policy_aux.intros)
done

lemma as_user_state_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: as_user_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def get_tcb_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: option.split_asm Structures_A.kernel_object.split)
  done

lemma as_user_tcb_states[wp]:
  "\<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (tcb_states_of_state s)\<rbrace>"
  apply (simp add: as_user_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: thread_states_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext] split: option.split)
  done

lemma as_user_thread_state[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: thread_states_def)
  apply wp
  done

lemma as_user_thread_bound_ntfn[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: as_user_def set_object_def split_def thread_bound_ntfns_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_states_def get_tcb_def
                 elim!: rsubst[where P=P, OF _ ext] split: option.split)
  done

lemma tcb_domain_map_wellformed_lift:
  assumes 1: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  shows "\<lbrace>tcb_domain_map_wellformed aag\<rbrace> f \<lbrace>\<lambda>rv. tcb_domain_map_wellformed aag\<rbrace>"
  by (rule 1)

lemma as_user_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> as_user t f \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
apply (simp add: pas_refined_def state_objs_to_policy_def)
apply (rule hoare_pre)
 apply wps
 apply wp
apply simp
done

(* **************************************** *)

subsection\<open>Random lemmas that belong elsewhere.\<close>

(* FIXME: move *)
lemma bang_0_in_set:
  "xs \<noteq> [] \<Longrightarrow> xs ! 0 \<in> set xs"
  apply(fastforce simp: in_set_conv_nth)
  done

(* FIXME: move *)
lemma update_one_strg:
  "((b \<longrightarrow> P c v) \<and> (\<not> b \<longrightarrow> (\<forall>v'. f c' = Some v' \<longrightarrow> P c v')))
  \<longrightarrow>
  ((f(c := if b then Some v else f c')) x = Some y \<and> f x \<noteq> Some y \<longrightarrow> P x y)"
  by auto

(* FIXME: move *)
lemma hoare_gen_asm2:
  assumes a: "P \<Longrightarrow> \<lbrace>\<top>\<rbrace> f \<lbrace>Q\<rbrace>"
  shows "\<lbrace>K P\<rbrace> f \<lbrace>Q\<rbrace>"
  using a by (fastforce simp: valid_def)

(* FIXME: move *)
lemma hoare_vcg_all_liftE:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>, \<lbrace>Q' x\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>, \<lbrace>\<lambda>rv s. \<forall>x. Q' x rv s\<rbrace>"
  unfolding validE_def
  apply (rule hoare_post_imp [where Q = "\<lambda>v s. \<forall>x. case v of Inl e \<Rightarrow> Q' x e s | Inr r \<Rightarrow> Q x r s"])
   apply (clarsimp split: sum.splits)
  apply (erule hoare_vcg_all_lift)
  done

(* FIXME: eliminate *)
lemma hoare_weak_lift_impE:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>Q'\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. R \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>rv s. R \<longrightarrow> Q rv s\<rbrace>, \<lbrace>\<lambda>rv s. R \<longrightarrow> Q' rv s\<rbrace>"
  by (rule wp_throw_const_impE)

(* FIXME: move *)
lemma hoare_use_ex_R:
  "(\<And>x. \<lbrace>P x and Q \<rbrace> f \<lbrace>R\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. (\<exists>x. P x s) \<and> Q s \<rbrace> f \<lbrace>R\<rbrace>, -"
  unfolding validE_R_def validE_def valid_def by fastforce

(* FIXME: move *)
lemma mapM_x_and_const_wp:
  assumes f: "\<And>v. \<lbrace>P and K (Q v)\<rbrace> f v \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>P and K (\<forall>v \<in> set vs. Q v)\<rbrace> mapM_x f vs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct vs)
   apply (simp add: mapM_x_Nil)
  apply (simp add: mapM_x_Cons)
  apply (wp f | assumption | simp)+
  done

(* stronger *)
(* FIXME: MOVE *)
lemma ep_queued_st_tcb_at':
  "\<And>P. \<lbrakk>ko_at (Endpoint ep) ptr s; (t, rt) \<in> ep_q_refs_of ep;
         valid_objs s; sym_refs (state_refs_of s);
         \<And>pl pl'. P (Structures_A.BlockedOnSend ptr pl) \<and> P (Structures_A.BlockedOnReceive ptr pl') \<rbrakk>
    \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac ep, simp_all)
  apply (frule(1) sym_refs_ko_atD, clarsimp, erule (1) my_BallE,
         clarsimp simp: st_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

(* Sometimes we only care about one of the queues. *)
(* FIXME: move *)
lemma ep_rcv_queued_st_tcb_at:
  "\<And>P. \<lbrakk>ko_at (Endpoint ep) epptr s; (t, EPRecv) \<in> ep_q_refs_of ep;
         valid_objs s; sym_refs (state_refs_of s);
         \<And>pl. P (Structures_A.BlockedOnReceive epptr pl);
         kheap s' t = kheap s t\<rbrakk>
    \<Longrightarrow> st_tcb_at P t s'"
  apply (case_tac ep, simp_all)
  apply (subgoal_tac "st_tcb_at P t s")
   apply (simp add: st_tcb_at_def obj_at_def)
  apply (frule(1) sym_refs_ko_atD, clarsimp, erule (1) my_BallE,
         clarsimp simp: st_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

(* FIXME: move. *)
lemma ntfn_queued_st_tcb_at':
  "\<And>P. \<lbrakk>ko_at (Notification ntfn) ntfnptr s; (t, rt) \<in> ntfn_q_refs_of (ntfn_obj ntfn);
         valid_objs s; sym_refs (state_refs_of s);
         P (Structures_A.BlockedOnNotification ntfnptr) \<rbrakk>
   \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac "ntfn_obj ntfn", simp_all)
  apply (frule(1) sym_refs_ko_atD)
  apply (clarsimp)
  apply (erule_tac y="(t, NTFNSignal)" in my_BallE, clarsimp)
  apply (clarsimp simp: pred_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

(* FIXME: move *)
lemma case_prod_wp:
  "(\<And>a b. x = (a, b) \<Longrightarrow> \<lbrace>P a b\<rbrace> f a b \<lbrace>Q\<rbrace>)
  \<Longrightarrow> \<lbrace>P (fst x) (snd x)\<rbrace> case_prod f x \<lbrace>Q\<rbrace>"
 by (cases x, simp)

(* FIXME: move *)
lemma case_sum_wp:
  "\<lbrakk> (\<And>a. x = Inl a \<Longrightarrow> \<lbrace>P a\<rbrace> f a \<lbrace>Q\<rbrace>);
     (\<And>a. x = Inr a \<Longrightarrow> \<lbrace>P' a\<rbrace> g a \<lbrace>Q\<rbrace>) \<rbrakk>
  \<Longrightarrow> \<lbrace>\<lambda>s. (\<forall>a. x = Inl a \<longrightarrow> P a s) \<and> (\<forall>a. x = Inr a \<longrightarrow> P' a s)\<rbrace> case_sum f g x \<lbrace>Q\<rbrace>"
  by (cases x, simp_all)

(* MOVE *)
crunch arm_asid_table_inv [wp]: store_pte "\<lambda>s. P (arm_asid_table (arch_state s))"

lemma st_tcb_at_to_thread_states:
  "st_tcb_at P t s \<Longrightarrow> \<exists>st. P st \<and> thread_states s t = tcb_st_to_auth st"
  by (fastforce simp: st_tcb_def2 thread_states_def tcb_states_of_state_def)

lemma aag_Control_into_owns:
  "\<lbrakk> aag_has_auth_to aag Control p; pas_refined aag s \<rbrakk> \<Longrightarrow> is_subject aag p"
  apply (drule (1) pas_refined_Control)
  apply simp
  done

lemma aag_has_Control_iff_owns:
  "pas_refined aag s \<Longrightarrow> (aag_has_auth_to aag Control x) = (is_subject aag x)"
  apply (rule iffI)
  apply (erule (1) aag_Control_into_owns)
  apply (simp add: pas_refined_refl)
  done

lemma aag_Control_owns_strg:
  "pas_wellformed aag \<and> is_subject aag v \<longrightarrow> aag_has_auth_to aag Control v"
  by (clarsimp simp: aag_wellformed_refl)

(* **************************************** *)

subsection \<open>Policy entailments\<close>

lemma owns_ep_owns_receivers:
  "\<lbrakk>\<forall>auth. aag_has_auth_to aag auth epptr; pas_refined aag s; invs s;
    ko_at (Endpoint ep) epptr s; (t, EPRecv) \<in> ep_q_refs_of ep\<rbrakk>
  \<Longrightarrow> is_subject aag t"
  apply (drule (1) ep_rcv_queued_st_tcb_at [where P = "receive_blocked_on epptr"])
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply (rule refl)
  apply (drule st_tcb_at_to_thread_states)
  apply (clarsimp simp: receive_blocked_on_def2)
  apply (drule spec [where x = Grant])
  apply (frule aag_wellformed_grant_Control_to_recv
           [OF _ _ pas_refined_wellformed])
    apply (rule pas_refined_mem [OF sta_ts])
     apply fastforce
    apply assumption+
  apply (erule (1) aag_Control_into_owns)
  done

(* MOVE *)
lemma cli_caps_of_state:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk> \<Longrightarrow> cap_links_irq aag (pasObjectAbs aag (fst slot)) cap"
apply (clarsimp simp add: cap_links_irq_def pas_refined_def)
apply (blast dest: state_irqs_to_policy_aux.intros)
done

(* MOVE *)
lemma cap_auth_caps_of_state:
  "\<lbrakk> caps_of_state s p = Some cap; pas_refined aag s \<rbrakk>
  \<Longrightarrow> aag_cap_auth aag (pasObjectAbs aag (fst p)) cap"
  unfolding aag_cap_auth_def
  apply (intro conjI)
    apply clarsimp
    apply (drule (2) sta_caps)
    apply (drule_tac f="pasObjectAbs aag" in auth_graph_map_memI[OF _ refl refl])
    apply (fastforce simp: pas_refined_def)
   apply clarsimp
   apply (drule (2) sta_untyped [THEN pas_refined_mem] )
   apply simp
  apply (drule (1) clas_caps_of_state)
  apply simp
  apply (drule (1) cli_caps_of_state)
  apply simp
  done

lemma cap_cur_auth_caps_of_state:
  "\<lbrakk> caps_of_state s p = Some cap; pas_refined aag s; is_subject aag (fst p) \<rbrakk>
  \<Longrightarrow> pas_cap_cur_auth aag cap"
  by (metis cap_auth_caps_of_state)

subsection \<open>Integrity monotony over subjects\<close>

lemmas new_range_subset' = aligned_range_offset_subset
lemmas ptr_range_subset = new_range_subset' [folded ptr_range_def]

lemma pbfs_less_wb:
  "pageBitsForSize x < word_bits"
  by (cases x, simp_all add: word_bits_def)

lemma ipcframe_subset_page:
  "\<lbrakk>valid_objs s; get_tcb p s = Some tcb;
    tcb_ipcframe tcb = cap.ArchObjectCap (arch_cap.PageCap d p' R vms xx);
    x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits \<rbrakk>
  \<Longrightarrow> x \<in> ptr_range p' (pageBitsForSize vms)"
   apply (frule (1) valid_tcb_objs)
   apply (clarsimp simp add: valid_tcb_def ran_tcb_cap_cases)
   apply (erule set_mp[rotated])
   apply (rule ptr_range_subset)
     apply (simp add: valid_cap_def cap_aligned_def)
    apply (simp add: valid_tcb_def valid_ipc_buffer_cap_def is_aligned_andI1 split:bool.splits)
   apply (rule order_trans [OF _ pbfs_atleast_pageBits])
   apply (simp add: msg_align_bits pageBits_def)
  apply (rule and_mask_less')
  apply (simp add: pbfs_less_wb [unfolded word_bits_conv])
  done

lemma trm_ipc':
  "\<lbrakk> pas_refined aag s; valid_objs s; case_option False can_receive_ipc (tcb_states_of_state s p');
     (tcb_states_of_state s' p') = Some Structures_A.Running;
     p \<in> auth_ipc_buffers s p' \<rbrakk> \<Longrightarrow>
    integrity_mem aag subjects p
          (tcb_states_of_state s) (tcb_states_of_state s') (auth_ipc_buffers s) X
          (underlying_memory (machine_state s) p)
          (underlying_memory (machine_state s') p)"
  apply (cases "pasObjectAbs aag p' \<in> subjects")
   apply (rule trm_write)
   apply (clarsimp simp: auth_ipc_buffers_member_def)
   apply (frule pas_refined_mem[rotated])
    apply (erule sta_caps, simp)
     apply (erule(3) ipcframe_subset_page)
    apply (simp add: cap_auth_conferred_def vspace_cap_rights_to_auth_def
                     is_page_cap_def)
    apply fastforce
   apply fastforce
  by (rule trm_ipc)


lemma tcb_bound_notification_reset_integrity_mono:
  "\<lbrakk> tcb_bound_notification_reset_integrity ntfn ntfn' S aag ; S \<subseteq> T\<rbrakk>
   \<Longrightarrow> tcb_bound_notification_reset_integrity ntfn ntfn' T aag"
  unfolding tcb_bound_notification_reset_integrity_def by blast

lemma reply_cap_deletion_integrity_mono:
  "\<lbrakk> reply_cap_deletion_integrity S aag cap cap' ; S \<subseteq> T\<rbrakk> \<Longrightarrow> reply_cap_deletion_integrity T aag cap cap'"
  by (blast intro: reply_cap_deletion_integrity_intros elim: reply_cap_deletion_integrityE)

lemma cnode_integrity_mono:
  "\<lbrakk> cnode_integrity S aag cont cont' ; S \<subseteq> T\<rbrakk> \<Longrightarrow> cnode_integrity T aag cont cont'"
  by (blast intro!: cnode_integrityI elim: cnode_integrityE dest:reply_cap_deletion_integrity_mono)

lemma asid_pool_integrity_mono:
  "\<lbrakk> asid_pool_integrity S aag cont cont' ; S \<subseteq> T\<rbrakk> \<Longrightarrow> asid_pool_integrity T aag cont cont'"
  unfolding asid_pool_integrity_def by fastforce

lemma cdt_change_allowed_mono:
  "\<lbrakk>cdt_change_allowed aag S (cdt s) (tcb_states_of_state s) ptr; S \<subseteq> T \<rbrakk> \<Longrightarrow>
    cdt_change_allowed aag T (cdt s) (tcb_states_of_state s) ptr"
  unfolding cdt_change_allowed_def cdt_direct_change_allowed.simps direct_call_def by blast



lemmas rtranclp_monoE = rtranclp_mono[THEN predicate2D,rotated,OF _ predicate2I]

lemma integrity_mono:
  "\<lbrakk> integrity_subjects S aag activate X s s'; S \<subseteq> T;
           pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> integrity_subjects T aag activate X s s'"
  apply (clarsimp simp: integrity_subjects_def simp del:split_paired_All)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec)+
   apply (simp only: integrity_obj_def)
   apply (erule rtranclp_monoE)
   apply (erule integrity_obj_atomic.cases[OF _ integrity_obj_atomic.intros];
          auto simp: indirect_send_def direct_send_def direct_call_def direct_reply_def
               elim: asid_pool_integrity_mono reply_cap_deletion_integrity_mono
                     cnode_integrity_mono)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec)+
   apply (erule integrity_eobj.cases; auto intro: integrity_eobj.intros)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec, erule integrity_mem.cases;
          blast intro: integrity_mem.intros trm_ipc')
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec, erule integrity_device.cases;
          blast intro: integrity_device.intros)
  apply (rule conjI)
  apply (intro allI)
  apply (drule_tac x=x in spec)+
   apply (erule integrity_cdtE; auto elim: cdt_change_allowed_mono)
  apply (rule conjI)
   apply (intro allI)
   apply (drule_tac x=x in spec)+
   apply (erule integrity_cdt_listE;
          auto elim!: weaken_filter_eq' intro: integrity_cdt_list_intros
               elim: cdt_change_allowed_mono)
  apply (rule conjI)
   apply (fastforce simp: integrity_interrupts_def)
  apply (rule conjI)
   apply (fastforce simp: integrity_asids_def)
  apply (clarsimp simp: integrity_ready_queues_def)
  apply blast
  done

subsection\<open>Access control do not care about machine_state\<close>

lemma integrity_irq_state_independent[intro!, simp]:
  "integrity x y z (s\<lparr>machine_state :=
                              machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = integrity x y z s"
  by (simp add: integrity_def)

lemma state_objs_to_policy_irq_state_independent[intro!, simp]:
  "state_objs_to_policy (s\<lparr>machine_state :=
                                   machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = state_objs_to_policy s"
  by (simp add: state_objs_to_policy_def)

lemma tcb_domain_map_wellformed_independent[intro!, simp]:
  "tcb_domain_map_wellformed aag (s\<lparr>machine_state :=
                                  machine_state s\<lparr>irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr>)
   = tcb_domain_map_wellformed aag s"
  by (simp add: tcb_domain_map_wellformed_aux_def get_etcb_def)

lemma pas_refined_irq_state_independent[intro!, simp]:
  "pas_refined x (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = pas_refined x s"
  by (simp add: pas_refined_def)


subsection\<open>Transitivity of integrity lemmas and tactics\<close>

lemma integrity_trans_start:
  "(\<And> s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. integrity aag X s\<rbrace>)
    \<Longrightarrow> \<lbrace>integrity aag X st and P\<rbrace> f \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding spec_valid_def valid_def using integrity_trans
  by simp blast

method integrity_trans_start
    = ((simp only: and_assoc[symmetric])?, rule integrity_trans_start[rotated])

(* Q should be explicitly supplied, if not, use wp_integrity_clean' *)
lemma wp_integrity_clean:
  "\<lbrakk>\<And>s. Q s \<Longrightarrow> integrity aag X s (g s);
    \<lbrace> P \<rbrace> f \<lbrace>\<lambda>_. integrity aag X st and Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace>\<lambda>_ s. integrity aag X st (g s) \<rbrace> "
   by (rule hoare_post_imp[of "\<lambda>_. integrity aag X st and Q"])
      (fastforce elim: integrity_trans)

lemmas wp_integrity_clean'= wp_integrity_clean[of \<top>, simplified]


end

end
