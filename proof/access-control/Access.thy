(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Access
imports Deterministic_AC
begin

context begin interpretation Arch . (*FIXME: arch_split*)

text{*

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

*}

type_synonym 'a agent_map = "obj_ref \<Rightarrow> 'a"
type_synonym 'a agent_asid_map = "asid \<Rightarrow> 'a"
type_synonym 'a agent_irq_map = "10 word \<Rightarrow> 'a"

text{*

What one agent can do to another. We allow multiple edges between
agents in the graph.

Control is special. It implies the ability to do pretty much anything,
including get access the other rights, create, remove, etc.

*}

datatype auth = Control | Receive | SyncSend | Notify
                    | Reset | Grant | Write | Read
                    | ASIDPoolMapsASID

text{*

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

*}

type_synonym 'a auth_graph = "('a \<times> auth \<times> 'a) set"

text {*

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

*}

end

record 'a PAS =
  pasObjectAbs :: "'a agent_map"
  pasASIDAbs :: "'a agent_asid_map"
  pasIRQAbs :: "'a agent_irq_map"
  pasPolicy :: "'a auth_graph"
  pasSubject :: "'a"                -- "The active label"
  pasMayActivate :: "bool"
  pasMayEditReadyQueues :: "bool"
  pasMaySendIrqs :: "bool"
  pasDomainAbs :: "domain \<Rightarrow> 'a"

context begin interpretation Arch . (*FIXME: arch_split*)

text{*

Wellformedness of the agent authority function with respect to a label
(the current thread):

\begin{itemize}

\item for (the current untrusted) @{term "agent"}, large enough
  authority must be contained within the agent's boundaries.

\item @{term "agent"} has all the self authority it could want.

\item If an agent can grant caps through an endpoint, then it is
  authority-equivalent to all agents that can receive on that
  endpoint.

\item Anyone can send on any IRQ notification.

\end{itemize}

*}

definition
  policy_wellformed
where
  "policy_wellformed aag maySendIrqs irqs agent \<equiv>
     (\<forall>agent'. (agent, Control, agent') \<in> aag \<longrightarrow> agent = agent')
   \<and> (\<forall>a. (agent, a, agent) \<in> aag)
   \<and> (\<forall>s r ep. (s, Grant, ep) \<in> aag \<and> (r, Receive, ep) \<in> aag
              \<longrightarrow> (s, Control, r) \<in> aag \<and> (r, Control, s) \<in> aag)
   \<and> (maySendIrqs \<longrightarrow> (\<forall>irq ntfn. irq \<in> irqs \<and> (irq, Notify, ntfn) \<in> aag \<longrightarrow> (agent, Notify, ntfn) \<in> aag))"

abbreviation
  "pas_wellformed aag \<equiv> policy_wellformed (pasPolicy aag) (pasMaySendIrqs aag) (range (pasIRQAbs aag)) (pasSubject aag)"

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

text{*

Abstract a graph by relabelling the nodes (agents). Clearly this can
collapse (and not create) distinctions.

*}

definition
  auth_graph_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a auth_graph \<Rightarrow> 'b auth_graph"
where
  "auth_graph_map f aag \<equiv> {(f x, auth, f y) | x auth y. (x, auth, y) \<in> aag}"

lemma auth_graph_map_mem:
  "(x, auth, y) \<in> auth_graph_map f S
     = (\<exists>x' y'. x = f x' \<and> y = f y' \<and> (x', auth, y') \<in> S)"
  by (simp add: auth_graph_map_def)

lemmas auth_graph_map_memD = auth_graph_map_mem[THEN iffD1]

lemma auth_graph_map_memI:
  "\<lbrakk> (x', auth, y') \<in> S; x = f x'; y = f y' \<rbrakk>
      \<Longrightarrow> (x, auth, y) \<in> auth_graph_map f S"
  by (fastforce simp add: auth_graph_map_mem)

lemma auth_graph_map_mono:
  "S \<subseteq> S' \<Longrightarrow> auth_graph_map G S \<subseteq> auth_graph_map G S'"
  unfolding auth_graph_map_def by auto

text{*

Very often we want to say that the agent currently running owns a
given pointer.

*}

abbreviation
  is_subject :: "'a PAS \<Rightarrow> word32 \<Rightarrow> bool"
where
  "is_subject aag ptr \<equiv> pasObjectAbs aag ptr = pasSubject aag"

text{*

Also we often want to say the current agent can do something to a
pointer that he doesn't own but has some authority to.

*}

abbreviation(input)
  aag_has_auth_to :: "'a PAS \<Rightarrow> auth \<Rightarrow> word32 \<Rightarrow> bool"
where
  "aag_has_auth_to aag auth ptr \<equiv> (pasSubject aag, auth, pasObjectAbs aag ptr) \<in> pasPolicy aag"

text{*

Abstract the state to an agent authority graph. This definition states
what authority is conferred by a particular capability to the obj_refs
in it.

*}

definition
  cap_rights_to_auth :: "cap_rights \<Rightarrow> bool \<Rightarrow> auth set"
where
  "cap_rights_to_auth r sync \<equiv>
     {Reset}
   \<union> (if AllowRead \<in> r then {Receive} else {})
   \<union> (if AllowWrite \<in> r then (if sync then {SyncSend} else {Notify}) else {})
   \<union> (if AllowGrant \<in> r then UNIV else {})"

definition
  vspace_cap_rights_to_auth :: "cap_rights \<Rightarrow> auth set"
where
 "vspace_cap_rights_to_auth r \<equiv>
      (if AllowWrite \<in> r then {Write} else {})
    \<union> (if AllowRead \<in> r then {Read} else {})"

definition
  cap_auth_conferred :: "cap \<Rightarrow> auth set"
where
 "cap_auth_conferred cap \<equiv>
    case cap of
      Structures_A.NullCap \<Rightarrow> {}
    | Structures_A.UntypedCap isdev oref bits freeIndex \<Rightarrow> {Control}
    | Structures_A.EndpointCap oref badge r \<Rightarrow>
         cap_rights_to_auth r True
    | Structures_A.NotificationCap oref badge r \<Rightarrow>
         cap_rights_to_auth (r - {AllowGrant}) False
    | Structures_A.ReplyCap oref m \<Rightarrow> {Control}
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

fun
  tcb_st_to_auth :: "Structures_A.thread_state \<Rightarrow> (obj_ref \<times> auth) set"
where
  "tcb_st_to_auth (Structures_A.BlockedOnNotification ntfn) = {(ntfn, Receive)}"
| "tcb_st_to_auth (Structures_A.BlockedOnSend ep payl)
     = {(ep, SyncSend)} \<union> (if sender_can_grant payl then {(ep, Grant)} else {})"
| "tcb_st_to_auth (Structures_A.BlockedOnReceive ep) = {(ep, Receive)}"
| "tcb_st_to_auth _ = {}"

definition
 "pte_ref pte \<equiv> case pte of
    SmallPagePTE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSmallPage, vspace_cap_rights_to_auth rights)
  | LargePagePTE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMLargePage, vspace_cap_rights_to_auth rights)
  | _ \<Rightarrow> None"

definition
 "pde_ref2 pde \<equiv> case pde of
    SectionPDE addr atts domain rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSection, vspace_cap_rights_to_auth rights)
  | SuperSectionPDE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSuperSection, vspace_cap_rights_to_auth rights)
  | PageTablePDE addr atts domain
       \<Rightarrow> Some (ptrFromPAddr addr, 0, {Control}) (* The 0 is a hack, saying that we own only addr, although 12 would also be OK *)
  | _ \<Rightarrow> None"

definition "ptr_range p sz \<equiv> {p .. p + 2 ^ sz - 1}"

(* We exclude the global page tables from the authority graph. Alternatively,
   we could include them and add a wellformedness constraint to policies that
   requires that every label has the necessary authority to whichever label owns
   the global page tables, so that when a new page directory is created and
   references to the global page tables are added to it, no new authority is gained.
   Note: excluding the references to global page tables in this way
         brings in some ARM arch-specific VM knowledge here *)
definition
  vs_refs_no_global_pts :: "Structures_A.kernel_object
            \<Rightarrow> (obj_ref \<times> vs_ref \<times> auth) set"
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


text {*

  sbta_caps/sbta_asid imply that a thread and it's vspace are labelled the same -- caps_of_state (tcb, vspace_index) will
  be the PD cap.  Thus, a thread is completely managed or completely self-managed.  We can (possibly) weaken this
  by only talking about addressable caps (i.e., only cspace in a tcb).  This would also mean that we should use the current
  cspace for the current label ... a bit strange, though.

  The set of all objects affected by a capability. We cheat a bit and
  say that a DomainCap contains references to everything, as it
  intuitively grants its owners that sort of access. This allows us to
  reuse sbta for DomainCaps.

  The sbta definition is non-inductive. We use the "inductive"
  construct for convenience, i.e. to get a nice set of intro rules,
  cases, etc.

*}

primrec
  aobj_ref' :: "arch_cap \<Rightarrow> obj_ref set"
where
  "aobj_ref' (arch_cap.ASIDPoolCap p as) = {p}"
| "aobj_ref' arch_cap.ASIDControlCap = {}"
| "aobj_ref' (arch_cap.PageCap isdev x rs sz as4) = ptr_range x (pageBitsForSize sz)"
| "aobj_ref' (arch_cap.PageDirectoryCap x as2) = {x}"
| "aobj_ref' (arch_cap.PageTableCap x as3) = {x}"

primrec
  obj_refs :: "cap \<Rightarrow> obj_ref set"
where
  "obj_refs cap.NullCap = {}"
| "obj_refs (cap.ReplyCap r m) = {r}"
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

inductive_set
  state_bits_to_policy for caps thread_sts thread_bas cdt vrefs
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
| sbta_cdt: "\<lbrakk> cdt slot' = Some slot \<rbrakk>
           \<Longrightarrow> (fst slot, Control, fst slot') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"
| sbta_vref: "\<lbrakk> (ptr', ref, auth) \<in> vrefs ptr \<rbrakk>
           \<Longrightarrow> (ptr, auth, ptr') \<in> state_bits_to_policy caps thread_sts thread_bas cdt vrefs"

fun
  cap_asid' :: "cap \<Rightarrow> asid set"
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

inductive_set
  state_asids_to_policy_aux for aag caps asid_tab vrefs
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
                        (pasObjectAbs aag poolptr, ASIDPoolMapsASID, pasASIDAbs aag asid) \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"

fun
  cap_irqs_controlled :: "cap \<Rightarrow> irq set"
where
  "cap_irqs_controlled cap.IRQControlCap = UNIV"
  | "cap_irqs_controlled (cap.IRQHandlerCap irq) = {irq}"
  | "cap_irqs_controlled _ = {}"

inductive_set
  state_irqs_to_policy_aux for aag caps
where
  sita_controlled: "\<lbrakk> caps ptr = Some cap; irq \<in> cap_irqs_controlled cap \<rbrakk>
  \<Longrightarrow> (pasObjectAbs aag (fst ptr), Control, pasIRQAbs aag irq) \<in> state_irqs_to_policy_aux aag caps"

abbreviation
  "state_irqs_to_policy aag s \<equiv> state_irqs_to_policy_aux aag (caps_of_state s)"

definition
  "irq_map_wellformed_aux aag irqs \<equiv> \<forall>irq. pasObjectAbs aag (irqs irq) = pasIRQAbs aag irq"

abbreviation
  "irq_map_wellformed aag s \<equiv> irq_map_wellformed_aux aag (interrupt_irq_node s)"

definition
 "state_vrefs s = case_option {} vs_refs_no_global_pts o kheap s"

abbreviation
  "state_asids_to_policy aag s \<equiv> state_asids_to_policy_aux aag (caps_of_state s)
        (arm_asid_table (arch_state s)) (state_vrefs s)"

definition
  "tcb_states_of_state s \<equiv> \<lambda>p. option_map tcb_state (get_tcb p s)"

definition
  "thread_states s = case_option {} tcb_st_to_auth \<circ> tcb_states_of_state s"

definition
  "thread_bound_ntfns s \<equiv> \<lambda>p. case (get_tcb p s) of None \<Rightarrow> None | Some tcb \<Rightarrow> tcb_bound_notification tcb"

definition
  "state_objs_to_policy s = state_bits_to_policy (caps_of_state s) (thread_states s) (thread_bound_ntfns s) (cdt s) (state_vrefs s)"

lemmas state_objs_to_policy_mem = eqset_imp_iff[OF state_objs_to_policy_def]

lemmas state_objs_to_policy_intros
    = state_bits_to_policy.intros[THEN state_objs_to_policy_mem[THEN iffD2]]

lemmas sta_caps = state_objs_to_policy_intros(1)
  and sta_untyped = state_objs_to_policy_intros(2)
  and sta_ts = state_objs_to_policy_intros(3)
  and sta_bas = state_objs_to_policy_intros(4)
  and sta_cdt = state_objs_to_policy_intros(5)
  and sta_vref = state_objs_to_policy_intros(6)

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

(* FIXME: move *)
lemma null_filterI:
  "\<lbrakk> cs p = Some cap; cap \<noteq> cap.NullCap \<rbrakk> \<Longrightarrow> null_filter cs p = Some cap"
  unfolding null_filter_def by auto

lemma sbta_null_filter:
  "state_bits_to_policy (null_filter cs) sr bar cd vr = state_bits_to_policy cs sr bar cd vr"
  apply (rule)
  apply clarsimp
  apply (erule state_bits_to_policy.induct, auto intro: state_bits_to_policy.intros elim: null_filterE)[1]
  apply clarsimp
  apply (erule state_bits_to_policy.induct, auto intro: sbta_caps [OF null_filterI] sbta_untyped [OF null_filterI] state_bits_to_policy.intros)[1]
  done

lemma sata_null_filter:
  "state_asids_to_policy_aux aag (null_filter cs) asid_tab vrefs
        = state_asids_to_policy_aux aag cs asid_tab vrefs"
  by (auto elim!: state_asids_to_policy_aux.induct null_filterE
           intro: state_asids_to_policy_aux.intros sata_asid[OF null_filterI])

text{*

We map scheduler domains to labels. This asserts that the labels on
tcbs are consistent with the labels on the domains they run in.

We need this to show that the ready queues are not reordered by
unauthorised subjects (see integrity_ready_queues).

*}

inductive_set
  domains_of_state_aux for ekheap
where
  domtcbs: "\<lbrakk> ekheap ptr = Some etcb; d = tcb_domain etcb \<rbrakk>
  \<Longrightarrow> (ptr, d) \<in> domains_of_state_aux ekheap"

abbreviation
  "domains_of_state s \<equiv> domains_of_state_aux (ekheap s)"

definition
  "tcb_domain_map_wellformed_aux aag etcbs_doms \<equiv> \<forall>(ptr, d) \<in> etcbs_doms. pasObjectAbs aag ptr = pasDomainAbs aag d"

abbreviation
  "tcb_domain_map_wellformed aag s \<equiv> tcb_domain_map_wellformed_aux aag (domains_of_state s)"

lemma tcb_domain_map_wellformed_mono:
  "\<lbrakk> domains_of_state s' \<subseteq> domains_of_state s; tcb_domain_map_wellformed pas s \<rbrakk> \<Longrightarrow> tcb_domain_map_wellformed pas s'"
by (auto simp: tcb_domain_map_wellformed_aux_def get_etcb_def)

text{*

We sometimes need to know that the label on the current domain is that
of the current subject.

*}

abbreviation
  "pas_cur_domain aag s \<equiv> pasDomainAbs aag (cur_domain s) = pasSubject aag"

text{*

The relation we want to hold between the current state and
the policy:
\begin{itemize}

\item The policy should be well-formed.

\item The abstraction of the state should respect the policy.

\end{itemize}

*}

definition
  pas_refined :: "'a PAS \<Rightarrow> det_ext state \<Rightarrow> bool"
where
 "pas_refined aag \<equiv> \<lambda>s.
     pas_wellformed aag
   \<and> irq_map_wellformed aag s
   \<and> tcb_domain_map_wellformed aag s
   \<and> auth_graph_map (pasObjectAbs aag) (state_objs_to_policy s) \<subseteq> pasPolicy aag
   \<and> state_asids_to_policy aag s \<subseteq> pasPolicy aag
   \<and> state_irqs_to_policy aag s \<subseteq> pasPolicy aag"

lemma pas_refined_mem:
  "\<lbrakk> (x, auth, y) \<in> state_objs_to_policy s; pas_refined aag s \<rbrakk>
       \<Longrightarrow> (pasObjectAbs aag x, auth, pasObjectAbs aag y) \<in> pasPolicy aag"
  by (auto simp: pas_refined_def intro: auth_graph_map_memI)

lemma pas_refined_wellformed:
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

lemmas pas_refined_all_auth_is_owns = aag_wellformed_all_auth_is_owns[OF pas_refined_wellformed]

lemma pas_refined_sita_mem:
  "\<lbrakk> (x, auth, y) \<in> state_irqs_to_policy aag s; pas_refined aag s \<rbrakk>
       \<Longrightarrow> (x, auth, y) \<in> pasPolicy aag"
  by (auto simp: pas_refined_def)

(* **************************************** *)

subsection{* How kernel objects can change *}

fun
  blocked_on :: "obj_ref \<Rightarrow> Structures_A.thread_state \<Rightarrow> bool"
where
 "blocked_on ref (Structures_A.BlockedOnReceive ref')     = (ref = ref')"
  | "blocked_on ref (Structures_A.BlockedOnSend ref' _)     = (ref = ref')"
  | "blocked_on ref (Structures_A.BlockedOnNotification ref') = (ref = ref')"
  | "blocked_on _ _ = False"

lemma blocked_on_def2:
  "blocked_on ref ts = (ref \<in> fst ` tcb_st_to_auth ts)"
  by (cases ts, simp_all)

fun
  receive_blocked_on :: "obj_ref \<Rightarrow> Structures_A.thread_state \<Rightarrow> bool"
where
   "receive_blocked_on ref (Structures_A.BlockedOnReceive ref')     = (ref = ref')"
  | "receive_blocked_on ref (Structures_A.BlockedOnNotification ref') = (ref = ref')"
  | "receive_blocked_on _ _ = False"

lemma receive_blocked_on_def2:
  "receive_blocked_on ref ts = ((ref, Receive) \<in> tcb_st_to_auth ts)"
  by (cases ts, simp_all)

fun
  send_blocked_on :: "obj_ref \<Rightarrow> Structures_A.thread_state \<Rightarrow> bool"
where
  "send_blocked_on ref (Structures_A.BlockedOnSend ref' _)     = (ref = ref')"
  | "send_blocked_on _ _ = False"

lemma send_blocked_on_def2:
  "send_blocked_on ref ts = ((ref, SyncSend) \<in> tcb_st_to_auth ts)"
  by (cases ts, simp_all)

fun
  send_is_call :: "Structures_A.thread_state \<Rightarrow> bool"
where
  "send_is_call (Structures_A.BlockedOnSend _ payl) = sender_is_call payl"
| "send_is_call _ = False"

abbreviation
  aag_subjects_have_auth_to :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> auth \<Rightarrow> obj_ref \<Rightarrow> bool"
where
 "aag_subjects_have_auth_to subs aag auth oref
    \<equiv> \<exists>s \<in> subs. (s, auth, pasObjectAbs aag oref) \<in> pasPolicy aag"

text{*

The integrity_obj relation captures the changes allowed to a
particular kernel object between the initial and final states: @{text
"integrity_obj aag l' ko ko'"} holds when the current label can
change @{term "ko"} to @{term "ko'"} when the address of @{term "ko"}
(and hence @{term "ko'"}) is labelled by @{term "l'"}.

*}

definition
  tcb_bound_notification_reset_integrity :: "obj_ref option \<Rightarrow> obj_ref option
    \<Rightarrow> 'a set \<Rightarrow> 'a PAS \<Rightarrow> bool"
where
  "tcb_bound_notification_reset_integrity ntfn ntfn' subjects aag
    = ((ntfn = ntfn') (*NO CHANGE TO BOUND NTFN *) 
       \<or> (ntfn' = None \<and> aag_subjects_have_auth_to subjects aag Reset (the ntfn)) (* NTFN IS UNBOUND *))" 

definition direct_send :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> obj_ref \<Rightarrow> tcb \<Rightarrow> bool"
where
  "direct_send subjects aag ep tcb \<equiv> receive_blocked_on ep (tcb_state tcb) \<and> 
                                   (aag_subjects_have_auth_to subjects aag SyncSend ep 
                                     \<or> aag_subjects_have_auth_to subjects aag Notify ep)"

abbreviation ep_recv_blocked :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> bool"
where
  "ep_recv_blocked ep ts \<equiv> case ts of BlockedOnReceive w \<Rightarrow> w = ep
                             | _ \<Rightarrow> False"

definition indirect_send :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> tcb \<Rightarrow> bool"
where
  "indirect_send subjects aag ntfn recv_ep tcb \<equiv> ep_recv_blocked recv_ep (tcb_state tcb) (* tcb is blocked on sync ep *)
                                         \<and> (tcb_bound_notification tcb = Some ntfn)
                                         \<and> aag_subjects_have_auth_to subjects aag Notify ntfn"

inductive
  integrity_obj for aag activate subjects l' ko ko'
where
  tro_lrefl: "\<lbrakk> l' \<in> subjects \<rbrakk>
      \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_orefl: "\<lbrakk> ko = ko' \<rbrakk> \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_ntfn: "\<lbrakk> ko  = Some (Notification ntfn);
              ko' = Some (Notification ntfn');
              auth \<in> {Receive, Notify, Reset};
              (\<exists>s \<in> subjects. (s, auth, l') \<in> pasPolicy aag) \<rbrakk>
           \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_ep: "\<lbrakk> ko  = Some (Endpoint ep);
             ko' = Some (Endpoint ep');
             auth \<in> {Receive, SyncSend, Reset};
             (\<exists>s \<in> subjects. (s, auth, l') \<in> pasPolicy aag) \<rbrakk>
           \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_ep_unblock: "\<lbrakk> ko  = Some (Endpoint ep);
             ko' = Some (Endpoint ep');
             \<exists>tcb ntfn. (tcb, Receive, pasObjectAbs aag ntfn) \<in> pasPolicy aag \<and> 
                       (tcb, Receive, l') \<in> pasPolicy aag \<and> 
                       aag_subjects_have_auth_to subjects aag Notify ntfn \<rbrakk>
           \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"

| tro_tcb_send: "\<lbrakk> ko  = Some (TCB tcb);
                   ko' = Some (TCB tcb'); 
                   \<exists>ctxt'. tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb), tcb_state := Structures_A.Running,
                     tcb_bound_notification := ntfn'\<rparr>;
                   tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
                   direct_send subjects aag ep tcb \<or> indirect_send subjects aag ep recv tcb \<rbrakk>
        \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_tcb_receive: "\<lbrakk> ko  = Some (TCB tcb);
                      ko' = Some (TCB tcb');
                      tcb' = tcb \<lparr>tcb_state := new_st, tcb_bound_notification := ntfn'\<rparr>;
                      new_st = Structures_A.Running
                          \<or> (new_st = Structures_A.Inactive \<and>
                                  (send_is_call (tcb_state tcb) \<or> tcb_fault tcb \<noteq> None)); (* maybe something about can_grant here? *)
                      tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
                      send_blocked_on ep (tcb_state tcb);
                      aag_subjects_have_auth_to subjects aag Receive ep \<rbrakk>
        \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_tcb_restart: "\<lbrakk> ko  = Some (TCB tcb);
                      ko' = Some (TCB tcb');
                      tcb' = tcb\<lparr> tcb_arch := arch_tcb_context_set (arch_tcb_context_get (tcb_arch tcb')) (tcb_arch tcb)
                                , tcb_state := tcb_state tcb', tcb_bound_notification := ntfn'\<rparr>;
                      (tcb_state tcb' = Structures_A.Restart \<and> arch_tcb_context_get (tcb_arch tcb') = arch_tcb_context_get (tcb_arch tcb)) \<or>
                      (* to handle activation *)
                      (tcb_state tcb' = Structures_A.Running \<and>
                       arch_tcb_context_get (tcb_arch tcb')
                         = (arch_tcb_context_get (tcb_arch tcb))(LR_svc := arch_tcb_context_get (tcb_arch tcb) FaultInstruction));
                      tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
                      blocked_on ep (tcb_state tcb);
                      aag_subjects_have_auth_to subjects aag Reset ep \<rbrakk>
        \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_tcb_unbind: "\<lbrakk> ko  = Some (TCB tcb);
                     ko' = Some (TCB tcb');
                     tcb' = tcb \<lparr>tcb_bound_notification := None\<rparr>;
                     tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) None subjects aag \<rbrakk>
                 \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_asidpool_clear: "\<lbrakk> ko = Some (ArchObj (ASIDPool pool));
                         ko' = Some (ArchObj (ASIDPool pool'));
                         \<forall>x. pool' x \<noteq> pool x \<longrightarrow> pool' x = None
                            \<and> aag_subjects_have_auth_to subjects aag Control (the (pool x)) \<rbrakk>
        \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
| tro_tcb_activate: "\<lbrakk> ko  = Some (TCB tcb);
                       ko' = Some (TCB tcb');
                       tcb' = tcb \<lparr> tcb_arch := arch_tcb_context_set ((arch_tcb_context_get (tcb_arch tcb))(LR_svc := (arch_tcb_context_get (tcb_arch tcb)) FaultInstruction)) (tcb_arch tcb)
                                  , tcb_state := Structures_A.Running, tcb_bound_notification := ntfn'\<rparr>;
                       tcb_state tcb = Structures_A.Restart;
                       (* to handle unbind *)
                       tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
                       activate \<rbrakk> (* Anyone can do this *)
        \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"

text{*

Assume two subjects can't interact. Then AINVS already implies that
the ready queues of one won't change when the other is running.

Assume two subjects can interact via an endpoint. (Probably an
notification object for infoflow purposes.) Then the following says
that the ready queues for the non-running subject can be extended by
the running subject, e.g. by sending a message. Note these threads are
added to the start of the queue.

*}

definition
  integrity_ready_queues
where
  "integrity_ready_queues aag subjects l' rq rq' \<equiv> pasMayEditReadyQueues aag \<or> (l' \<notin> subjects \<longrightarrow> (\<exists>threads. threads @ rq = rq'))"

lemma integrity_ready_queues_refl[simp]: "integrity_ready_queues aag subjects ptr s s"
unfolding integrity_ready_queues_def by simp

inductive
  integrity_eobj for aag subjects l' eko eko'
where
  tre_lrefl: "\<lbrakk> l' \<in> subjects \<rbrakk> \<Longrightarrow> integrity_eobj aag subjects l' eko eko'"
| tre_orefl: "\<lbrakk> eko = eko' \<rbrakk> \<Longrightarrow> integrity_eobj aag subjects l' eko eko'"

lemma integrity_obj_activate:
  "integrity_obj aag False subjects l' ko ko' \<Longrightarrow>
   integrity_obj aag activate subjects l' ko ko'"
by (fast elim: integrity_obj.cases intro: integrity_obj.intros)

abbreviation "object_integrity aag
    \<equiv> integrity_obj (aag :: 'a PAS) (pasMayActivate aag) {pasSubject aag}"

definition
  auth_ipc_buffers :: "'z::state_ext state \<Rightarrow> word32 \<Rightarrow> word32 set"
where
  "auth_ipc_buffers s \<equiv> \<lambda>p. case (get_tcb p s) of
                                 None \<Rightarrow> {}
                               | Some tcb \<Rightarrow> case tcb_ipcframe tcb of
                                                  cap.ArchObjectCap (arch_cap.PageCap False p' R vms _) \<Rightarrow>
                                                       if AllowWrite \<in> R then (ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits) else {}
                                                 | _ \<Rightarrow> {}"

(* MOVE *)
lemma caps_of_state_tcb:
  "\<lbrakk> get_tcb p s = Some tcb; option_map fst (tcb_cap_cases idx) = Some getF \<rbrakk> \<Longrightarrow> caps_of_state s (p, idx) = Some (getF tcb)"
  apply (drule get_tcb_SomeD)
  apply clarsimp
  apply (drule (1) cte_wp_at_tcbI [where t = "(p, idx)" and P = "op = (getF tcb)", simplified])
  apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

(* MOVE *)
lemma caps_of_state_tcb_cap_cases:
  "\<lbrakk> get_tcb p s = Some tcb; idx \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> caps_of_state s (p, idx) = Some ((the (option_map fst (tcb_cap_cases idx))) tcb)"
  apply (clarsimp simp: dom_def)
  apply (erule caps_of_state_tcb)
  apply simp
  done

lemma auth_ipc_buffers_member_def:
  "x \<in> auth_ipc_buffers s p = (\<exists>tcb p' R vms xx. get_tcb p s = Some tcb
                                              \<and> tcb_ipcframe tcb = (cap.ArchObjectCap (arch_cap.PageCap False p' R vms xx))
                                              \<and> caps_of_state s (p, tcb_cnode_index 4) = Some (cap.ArchObjectCap (arch_cap.PageCap False p' R vms xx))
                                              \<and> AllowWrite \<in> R
                                              \<and> x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits)"
  unfolding auth_ipc_buffers_def
  by (clarsimp simp: caps_of_state_tcb split: option.splits cap.splits arch_cap.splits bool.splits)

text {*
  Inductive for now, we should add something about user memory/transitions.

  This relies on tro to tell us when a tcb state can change to avoid
  duplicating the defs etc.
*}

inductive
  integrity_mem for aag subjects p ts ts' ipcbufs globals w w'
where
  trm_lrefl: "\<lbrakk> pasObjectAbs aag p \<in> subjects \<rbrakk>
     \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'" (* implied by wf and write *)
  | trm_orefl: "\<lbrakk> w = w' \<rbrakk> \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
  | trm_write: "\<lbrakk> aag_subjects_have_auth_to subjects aag Write p \<rbrakk> \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
  | trm_globals: "\<lbrakk> p \<in> globals \<rbrakk> \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"
  | trm_ipc: "\<lbrakk> case_option False (receive_blocked_on ep) (ts p'); ts' p' = Some Structures_A.Running;
                p \<in> ipcbufs p'; pasObjectAbs aag p' \<notin> subjects
        \<rbrakk> \<Longrightarrow> integrity_mem aag subjects p ts ts' ipcbufs globals w w'"

abbreviation
  "memory_integrity X aag x t1 t2 ipc == integrity_mem (aag :: 'a PAS) {pasSubject aag} x t1 t2 ipc X"

inductive
  integrity_device for aag subjects p ts ts'  w w'
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

definition
  integrity_cdt :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> cslot_ptr \<Rightarrow>
       (cslot_ptr option \<times> bool) \<Rightarrow> (cslot_ptr option \<times> bool) \<Rightarrow> bool"
where
  "integrity_cdt aag subjects ptr v v'
     \<equiv> v = v' \<or> pasObjectAbs aag (fst ptr) \<in> subjects"


abbreviation
  "cdt_integrity aag == integrity_cdt (aag :: 'a PAS) {pasSubject aag}"

lemma integrity_cdt_refl[simp]: "integrity_cdt aag subjects ptr v v"
  by (simp add: integrity_cdt_def)


definition
  integrity_cdt_list :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> cslot_ptr \<Rightarrow>
       (cslot_ptr list) \<Rightarrow> (cslot_ptr list) \<Rightarrow> bool"
where
  "integrity_cdt_list aag subjects ptr v v'
     \<equiv> (filtered_eq (\<lambda>x. pasObjectAbs aag (fst x) \<in> subjects) v v') \<or> pasObjectAbs aag (fst ptr) \<in> subjects"


abbreviation
  "cdt_list_integrity aag == integrity_cdt_list (aag :: 'a PAS) {pasSubject aag}"

lemma integrity_cdt_list_refl[simp]: "integrity_cdt_list aag subjects ptr v v"
  by (simp add: integrity_cdt_list_def)

definition
  integrity_interrupts :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> irq \<Rightarrow>
       (obj_ref \<times> irq_state) \<Rightarrow> (obj_ref \<times> irq_state) \<Rightarrow> bool"
where
  "integrity_interrupts aag subjects irq v v'
     \<equiv> v = v' \<or> pasIRQAbs aag irq \<in> subjects"

lemma integrity_interrupts_refl[simp]: "integrity_interrupts aag subjects ptr v v"
  by (simp add: integrity_interrupts_def)

definition
  integrity_asids :: "'a PAS \<Rightarrow> 'a set \<Rightarrow> asid \<Rightarrow> word32 option \<Rightarrow> word32 option \<Rightarrow> bool"
where
  "integrity_asids aag subjects asid pp_opt pp_opt'
     \<equiv> pp_opt = pp_opt' \<or> (\<forall> asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid \<longrightarrow> pasASIDAbs aag asid' \<in> subjects)"

lemma integrity_asids_refl[simp]: "integrity_asids aag subjects ptr s s"
  by (simp add: integrity_asids_def)

text{*

Half of what we ultimately want to say: that the parts of the
system state that change are allowed to by the labelling @{term
"aag"}.

The other half involves showing that @{term "aag"} concords with the
policy. See @{term "state_objs_to_policy s"}.

*}

definition
  integrity_subjects :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> bool \<Rightarrow> obj_ref set \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
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
         (\<forall>x. integrity_cdt aag subjects x (cdt s x, is_original_cap s x) (cdt s' x, is_original_cap s' x)) \<and>
         (\<forall>x. integrity_cdt_list aag subjects x (cdt_list s x) (cdt_list s' x)) \<and>
         (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s x, interrupt_states s x) (interrupt_irq_node s' x, interrupt_states s' x)) \<and>
         (\<forall>x. integrity_asids aag subjects x (arm_asid_table (arch_state s) (asid_high_bits_of x)) (arm_asid_table (arch_state s') (asid_high_bits_of x))) \<and>
         (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d) (ready_queues s d p) (ready_queues s' d p))"

abbreviation
  "integrity pas \<equiv> integrity_subjects {pasSubject pas} pas (pasMayActivate pas)"

lemma clear_asidpool_trans:
  "\<lbrakk> \<forall>x. pool' x \<noteq> pool x \<longrightarrow> pool' x = None
                            \<and> aag_subjects_have_auth_to es aag Control (the (pool x));
     \<forall>x. pool'' x \<noteq> pool' x \<longrightarrow> pool'' x = None
                            \<and> aag_subjects_have_auth_to es aag Control (the (pool' x)) \<rbrakk>
   \<Longrightarrow> \<forall>x. pool'' x \<noteq> pool x \<longrightarrow> pool'' x = None
                            \<and> aag_subjects_have_auth_to es aag Control (the (pool x))"
  apply clarsimp
  apply (drule_tac x=x in spec)+
  apply auto
  done

lemma tcb_bound_notification_reset_integrity_trans[elim]:
  "\<lbrakk> tcb_bound_notification_reset_integrity ntfn ntfn' subjects aag;
    tcb_bound_notification_reset_integrity ntfn' ntfn'' subjects aag \<rbrakk>
    \<Longrightarrow> tcb_bound_notification_reset_integrity ntfn ntfn'' subjects aag"
  by (auto simp: tcb_bound_notification_reset_integrity_def)

lemma tro_trans: (* this takes a long time to process *)
  "\<lbrakk>(\<forall>x. integrity_obj aag activate es (pasObjectAbs aag x) (kheap s x) (kheap s' x));
    (\<forall>x. integrity_obj aag activate es (pasObjectAbs aag x) (kheap s' x) (kheap s'' x)) \<rbrakk> \<Longrightarrow>
    (\<forall>x. integrity_obj aag activate es (pasObjectAbs aag x) (kheap s x) (kheap s'' x))"
  apply clarsimp
  apply (drule_tac x = x in spec)+
  apply (erule integrity_obj.cases)
  prefer 10
   apply ((clarsimp
       | erule integrity_obj.cases
       | erule disjE
       | drule(1) clear_asidpool_trans
       | drule sym[where s = "Some x" for x]
       | blast intro: integrity_obj.intros)+)[1]
  by (((fastforce intro: integrity_obj.intros simp: indirect_send_def direct_send_def) 
                              | erule integrity_obj.cases)+)

lemma tre_trans:
  "\<lbrakk>(\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh x) (ekh' x));
    (\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh' x) (ekh'' x)) \<rbrakk> \<Longrightarrow>
    (\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh x) (ekh'' x))"
by (fastforce elim!: integrity_eobj.cases
              intro: integrity_eobj.intros)+

lemma trcdt_trans:
  "\<lbrakk> (\<forall>x. integrity_cdt aag subjects x (cdt s x, is_original_cap s x) (cdt s' x, is_original_cap s' x));
    (\<forall>x. integrity_cdt aag subjects x (cdt s' x, is_original_cap s' x) (cdt s'' x, is_original_cap s'' x)) \<rbrakk>
   \<Longrightarrow> (\<forall>x. integrity_cdt aag subjects x (cdt s x, is_original_cap s x) (cdt s'' x, is_original_cap s'' x))"
  apply (simp add: integrity_cdt_def
                  del: split_paired_All)
  apply metis
  done

lemma trcdtlist_trans:
  "\<lbrakk> (\<forall>x. integrity_cdt_list aag subjects x (t x) (t' x));
    (\<forall>x. integrity_cdt_list aag subjects x (t' x) (t'' x)) \<rbrakk>
   \<Longrightarrow> (\<forall>x. integrity_cdt_list aag subjects x (t x) (t'' x))"
  apply (simp add: integrity_cdt_list_def
                  del: split_paired_All)
  apply metis
  done


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

lemma tsos_tro:
  "\<lbrakk>\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x); tcb_states_of_state s' p = Some a;
    receive_blocked_on ep a; pasObjectAbs aag p \<notin> subjects \<rbrakk> \<Longrightarrow> tcb_states_of_state s p = Some a"
  apply (drule_tac x = p in spec)
  apply (erule integrity_obj.cases, simp_all add: tcb_states_of_state_def get_tcb_def)
   apply clarsimp
  apply fastforce
  apply fastforce
  done

lemma auth_ipc_buffers_tro:
  "\<lbrakk>\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x); x \<in> auth_ipc_buffers s' p;
          pasObjectAbs aag p \<notin> subjects \<rbrakk>
  \<Longrightarrow> x \<in> auth_ipc_buffers s p "
  apply (drule_tac x = p in spec)
  apply (erule integrity_obj.cases, 
        simp_all add: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def 
               split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)
  apply fastforce
  done

lemma auth_ipc_buffers_tro_fwd:
  "\<lbrakk>\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x); x \<in> auth_ipc_buffers s p;
          pasObjectAbs aag p \<notin> subjects \<rbrakk>
  \<Longrightarrow> x \<in> auth_ipc_buffers s' p "
  apply (drule_tac x = p in spec)
  apply (erule integrity_obj.cases,
        simp_all add: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def
                split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)
  apply fastforce
  done

lemma tsos_tro_running:
  "\<lbrakk>\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x);
       tcb_states_of_state s p = Some Structures_A.Running;
          pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> tcb_states_of_state s' p = Some Structures_A.Running"
  apply (drule_tac x = p in spec)
  apply (erule integrity_obj.cases, simp_all add: tcb_states_of_state_def get_tcb_def indirect_send_def direct_send_def)
  done

lemma integrity_trans:
  assumes t1: "integrity_subjects subjects aag activate X s s'"
  and     t2: "integrity_subjects subjects aag activate X s' s''"
  shows  "integrity_subjects subjects aag activate X s s''"
proof -
  from t1 have tro1: "\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x)"
    unfolding integrity_subjects_def by simp
  from t2 have tro2: "\<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s' x) (kheap s'' x)"
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
        case (trm_ipc ep p')

        show ?thesis
        proof (rule integrity_mem.trm_ipc)
          from trm_ipc show "case_option False (receive_blocked_on ep) (tcb_states_of_state s p')"
            by (fastforce split: option.splits dest: tsos_tro [OF tro1])

          from trm_ipc show "x \<in> auth_ipc_buffers s p'"
            by (fastforce split: option.splits intro: auth_ipc_buffers_tro [OF tro1])
        qed (simp_all add: trm_ipc)
      qed (auto simp add: trm_orefl intro: integrity_mem.intros)
    next
      case trm_write thus ?thesis by (rule integrity_mem.intros)
    next
      case (trm_ipc ep p')
      note trm_ipc1 = trm_ipc

      from m2 show ?thesis
      proof cases
        case trm_orefl
        thus ?thesis using trm_ipc1
          by (auto intro!: integrity_mem.trm_ipc simp add: restrict_map_Some_iff elim!: tsos_tro_running [OF tro2, rotated])
      next
        case (trm_ipc ep' p'')
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
    apply (clarsimp simp add: integrity_subjects_def)
    apply (drule(1) trcdt_trans[simplified])
    apply (drule(1) trcdtlist_trans[simplified])
    apply (drule(1) trinterrupts_trans[simplified])
    apply (drule(1) trasids_trans[simplified])
    apply (drule(1) tre_trans[simplified])
    apply (drule(1) trrqs_trans)
    apply simp
    done
qed

lemma integrity_refl [simp]:
  "integrity_subjects S aag activate X s s"
unfolding integrity_subjects_def
by simp

subsection{* Generic stuff *}

(* Tom says that Gene Wolfe says that autarchy \<equiv> self authority. *)

lemma integrity_update_autarch:
  "\<lbrakk> integrity aag X st s; is_subject aag ptr \<rbrakk> \<Longrightarrow> integrity aag X st (s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr>)"
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
  apply (simp add: set_object_def)
  apply (wp gets_the_wp)
  apply (rule integrity_update_autarch, simp_all)
  done

lemma tcb_states_of_state_trans_state[simp]: "tcb_states_of_state (trans_state f s) = tcb_states_of_state s"
  apply (simp add: tcb_states_of_state_def get_tcb_exst_update)
  done

lemma eintegrity_sa_update[simp]: "integrity aag X st (scheduler_action_update f s) = integrity aag X st s"
  apply (simp add: integrity_subjects_def trans_state_update'[symmetric])
  done

lemma trans_state_back[simp]: "trans_state (\<lambda>_. exst s) s = s"
  by simp

declare wrap_ext_op_det_ext_ext_def[simp]

crunch integrity[wp]: set_thread_state_ext "integrity aag X st"

crunch integrity_autarch: set_thread_state "integrity aag X st"

lemmas integrity_def = integrity_subjects_def

end

context pspace_update_eq begin

interpretation Arch . (*FIXME: arch_split*)

lemma integrity_update_eq[iff]:
  "tcb_states_of_state (f s) = tcb_states_of_state s"
  by (simp add: pspace tcb_states_of_state_def get_tcb_def)

end

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  label_owns_asid_slot :: "'a PAS \<Rightarrow> 'a \<Rightarrow> asid \<Rightarrow> bool"
where
  "label_owns_asid_slot aag l asid \<equiv>
     (l, Control, pasASIDAbs aag asid) \<in> pasPolicy aag"

definition
  cap_links_asid_slot :: "'a PAS \<Rightarrow> 'a \<Rightarrow> cap \<Rightarrow> bool"
where
  "cap_links_asid_slot aag l cap \<equiv> (\<forall>asid \<in> cap_asid' cap.
      label_owns_asid_slot aag l asid)"

abbreviation
  is_subject_asid :: "'a PAS \<Rightarrow> asid \<Rightarrow> bool"
where
  "is_subject_asid aag asid \<equiv> pasASIDAbs aag asid = pasSubject aag"

lemma clas_no_asid:
  "cap_asid' cap = {} \<Longrightarrow> cap_links_asid_slot aag l cap"
  unfolding cap_links_asid_slot_def by simp

definition
  "cap_links_irq aag l cap \<equiv> \<forall>irq \<in> cap_irqs_controlled cap. (l, Control, pasIRQAbs aag irq) \<in> pasPolicy aag"

lemma cli_no_irqs:
  "cap_irqs_controlled cap = {} \<Longrightarrow> cap_links_irq aag l cap"
  unfolding cap_links_irq_def by simp

abbreviation
  is_subject_irq :: "'a PAS \<Rightarrow> irq \<Rightarrow> bool"
where
  "is_subject_irq aag irq \<equiv> pasIRQAbs aag irq = pasSubject aag"

definition
  aag_cap_auth :: "'a PAS \<Rightarrow> 'a \<Rightarrow> cap \<Rightarrow> bool"
where
  "aag_cap_auth aag l cap \<equiv>
      (\<forall>x \<in> obj_refs cap. \<forall>auth \<in> cap_auth_conferred cap. (l, auth, pasObjectAbs aag x) \<in> pasPolicy aag)
    \<and> (\<forall>x \<in> untyped_range cap. (l, Control, pasObjectAbs aag x) \<in> pasPolicy aag)
    \<and> cap_links_asid_slot aag l cap \<and> cap_links_irq aag l cap"

abbreviation
  pas_cap_cur_auth :: "'a PAS \<Rightarrow> cap \<Rightarrow> bool"
where
  "pas_cap_cur_auth aag cap \<equiv> aag_cap_auth aag (pasSubject aag) cap"

crunch integrity_autarch: as_user "integrity aag X st"

lemma owns_thread_owns_cspace:
  "\<lbrakk> is_subject aag thread; pas_refined aag s; get_tcb thread s = Some tcb; is_cnode_cap (tcb_ctable tcb); x \<in> obj_refs (tcb_ctable tcb)\<rbrakk>
    \<Longrightarrow> is_subject aag x"
  apply (drule get_tcb_SomeD)
  apply (drule cte_wp_at_tcbI[where t="(thread, tcb_cnode_index 0)" and P="\<lambda>cap. cap = tcb_ctable tcb", simplified])
  apply (auto simp: cte_wp_at_caps_of_state is_cap_simps cap_auth_conferred_def
              elim: caps_of_state_pasObjectAbs_eq [where p = "(thread, tcb_cnode_index 0)"])
  done

lemma aag_cdt_link_Control:
  "\<lbrakk> cdt s x = Some y; pas_refined aag s \<rbrakk> \<Longrightarrow> (pasObjectAbs aag (fst y), Control, pasObjectAbs aag (fst x)) \<in> pasPolicy aag"
  by (fastforce dest: sta_cdt pas_refined_mem pas_refined_Control)

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
  apply (simp add: as_user_def set_object_def split_def)
  apply wp
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def get_tcb_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: option.split_asm Structures_A.kernel_object.split)
  done

lemma as_user_tcb_states[wp]:
  "\<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (tcb_states_of_state s)\<rbrace>"
  apply (simp add: as_user_def set_object_def split_def tcb_states_of_state_def)
  apply wp
  apply (clarsimp simp: thread_states_def get_tcb_def
                 elim!: rsubst[where P=P, OF _ ext] split: option.split)
  done

lemma as_user_thread_state[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: thread_states_def )
  apply wp
  done

lemma as_user_thread_bound_ntfn[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: as_user_def set_object_def split_def thread_bound_ntfns_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_states_def get_tcb_def
                 elim!: rsubst[where P=P, OF _ ext] split: option.split)
  done

crunch cdt_preserved[wp]: as_user "\<lambda>s. P (cdt s)"

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

text{* Random lemmas that belong elsewhere. *}

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

(* really? *)
(* MOVE *)
lemma get_endpoint_wp:
  "\<lbrace>\<lambda>s. \<forall>ep. ko_at (Endpoint ep) epptr s \<longrightarrow> P ep s\<rbrace> get_endpoint epptr \<lbrace>P\<rbrace>"
  apply (rule hoare_post_imp)
  defer
  apply (rule get_endpoint_sp)
  apply clarsimp
  done

(* stronger *)
(* FIXME: MOVE *)
lemma ep_queued_st_tcb_at':
  "\<And>P. \<lbrakk>ko_at (Endpoint ep) ptr s; (t, rt) \<in> ep_q_refs_of ep;
         valid_objs s; sym_refs (state_refs_of s);
         \<And>pl. P (Structures_A.BlockedOnSend ptr pl) \<and> P (Structures_A.BlockedOnReceive ptr) \<rbrakk>
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
         P (Structures_A.BlockedOnReceive epptr);
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

subsection {* Policy entailments *}

lemma owns_ep_owns_receivers:
  "\<lbrakk> (\<forall>auth. aag_has_auth_to aag auth epptr); pas_refined aag s; invs s; ko_at (Endpoint ep) epptr s; (t, EPRecv) \<in> ep_q_refs_of ep\<rbrakk>
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

lemmas new_range_subset' = aligned_range_offset_subset
lemmas ptr_range_subset = new_range_subset' [folded ptr_range_def]

lemma pbfs_less_wb:
  "pageBitsForSize x < word_bits"
  by (cases x, simp_all add: word_bits_def)

lemma ipcframe_subset_page:
  "\<lbrakk>valid_objs s; get_tcb p s = Some tcb; tcb_ipcframe tcb = cap.ArchObjectCap (arch_cap.PageCap d p' R vms xx);
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
  "\<lbrakk> pas_refined aag s; valid_objs s; case_option False (receive_blocked_on ep) (tcb_states_of_state s p');
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
  apply (erule (3) trm_ipc)
  done

lemma integrity_mono:
  "\<lbrakk> integrity_subjects S aag activate X s s'; S \<subseteq> T;
           pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> integrity_subjects T aag activate X s s'"
  apply (clarsimp simp: integrity_subjects_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec)+
   apply (erule integrity_obj.cases[OF _ integrity_obj.intros],
          auto simp: tcb_bound_notification_reset_integrity_def indirect_send_def direct_send_def)[1]
   apply (blast intro: tro_asidpool_clear)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec)+
   apply (erule integrity_eobj.cases, auto intro: integrity_eobj.intros)[1]
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec, erule integrity_mem.cases,
           (blast intro: integrity_mem.intros trm_ipc')+)[1]
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec, erule integrity_device.cases,
           (blast intro: integrity_device.intros)+)[1]
  apply (simp add: integrity_cdt_list_def)
  apply (rule conjI)
   apply (fastforce simp: integrity_cdt_def)
  apply (rule conjI)
   apply clarsimp
   apply (blast intro: weaken_filter_eq[where P="\<lambda>x. pasObjectAbs aag (fst x) \<in> S"])
  (* be more manual here to make this part of the proof much faster *)
  apply (rule conjI)
   apply (fastforce simp: integrity_interrupts_def)
  apply (rule conjI)
   apply (fastforce simp: integrity_asids_def)
  apply (clarsimp simp: integrity_ready_queues_def)
  apply blast
  done

abbreviation "einvs \<equiv> invs and valid_list and valid_sched"

end

end
