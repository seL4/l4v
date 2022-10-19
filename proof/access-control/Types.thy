(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Types
imports ArchTypes
begin

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

datatype auth = Control | Receive | SyncSend | Notify | Reset | Grant | Call
                        | Reply | Write | Read | DeleteDerived | AAuth arch_auth

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

abbreviation is_subject :: "'a PAS \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "is_subject aag ptr \<equiv> pasObjectAbs aag ptr = pasSubject aag"

text\<open>

Also we often want to say the current agent can do something to a
pointer that he doesn't own but has some authority to.

\<close>

abbreviation(input) abs_has_auth_to :: "'a PAS \<Rightarrow> auth \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "abs_has_auth_to aag auth ptr ptr' \<equiv>
     (pasObjectAbs aag ptr, auth, pasObjectAbs aag ptr') \<in> pasPolicy aag"

abbreviation(input) aag_has_auth_to :: "'a PAS \<Rightarrow> auth \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "aag_has_auth_to aag auth ptr \<equiv> (pasSubject aag, auth, pasObjectAbs aag ptr) \<in> pasPolicy aag"

abbreviation aag_subjects_have_auth_to_label :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> auth \<Rightarrow> 'a \<Rightarrow> bool" where
  "aag_subjects_have_auth_to_label subs aag auth label \<equiv>
     \<exists>s \<in> subs. (s, auth, label) \<in> pasPolicy aag"

abbreviation aag_subjects_have_auth_to :: "'a set \<Rightarrow> 'a PAS \<Rightarrow> auth \<Rightarrow> obj_ref \<Rightarrow> bool" where
 "aag_subjects_have_auth_to subs aag auth oref \<equiv>
    aag_subjects_have_auth_to_label subs aag auth (pasObjectAbs aag oref)"

subsection \<open>Misc. definitions\<close>

definition ptr_range where
  "ptr_range p sz \<equiv> {p .. p + 2 ^ sz - 1}"

lemma ptr_range_0[simp]: "ptr_range (p :: obj_ref) 0 = {p}"
  unfolding ptr_range_def by simp

definition tcb_states_of_state where
  "tcb_states_of_state s \<equiv> \<lambda>p. option_map tcb_state (get_tcb False p s)"

fun can_receive_ipc :: "thread_state \<Rightarrow> bool" where
  "can_receive_ipc (BlockedOnReceive _ _) = True"
| "can_receive_ipc (BlockedOnSend _ pl)
     = (sender_is_call pl \<and> (sender_can_grant pl \<or> sender_can_grant_reply pl))"
| "can_receive_ipc (BlockedOnNotification _) = True"
| "can_receive_ipc BlockedOnReply = True"
| "can_receive_ipc _ = False"

end
