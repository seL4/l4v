(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

text \<open>
  This file provide the main confidentiality unwinding condition:
  the reads_respects family.
  In order to do that it provides subjectReads, the set of labels a label can observe from
  and subjectAffects, the set of labels a label can affect.
  Then we can build read_equiv and affects_equiv which are parts of the unwinding relation.
  reads_respects then states that reads_equiv and affects_equiv are preserved
  through a specific function
\<close>


theory InfoFlow
imports ArchInfoFlow
begin

section \<open>Scheduler domain constraint\<close>

text \<open>
  For the information flow theorem, we assume that every domain
  contains threads of exactly one label, so that labels cannot leak
  information through the scheduler.

  Morally, domains that have no labels ought to be allowed as well,
  but this definition is easier to reason about. In practice, we can
  just put all empty domains into some dummy label to satisfy the
  exactly-one requirement. See e.g. the mapping in Example_Valid_State.
\<close>

definition pas_domains_distinct :: "('a, 'b) PAS_scheme \<Rightarrow> bool"
  where
    "pas_domains_distinct aag \<equiv> \<forall>d. \<exists>l. pasDomainAbs aag d = {l}"


section \<open>Reading: subjectReads and associated equivalence properties\<close>

subsection \<open>subjectReads\<close>

text\<open>We take the authority graph from the access proofs. We identify each
   label in that graph with an information flow domain. Our goal is to
   construct an equivalence relation (R l) on states, for each label l of
   the authority graph, that tells us when those two states are equal for
   all state readable by label l -- i.e. all state that falls within l's
   information flow domain. The set of all such state, we denote
   subjectReads g l, where g is the authority graph.\<close>


(* TODO: consider putting the current subject as a parameter and restricting
         the inductive rules to require that 'a' is the current subject *)
inductive_set subjectReads :: "'a auth_graph \<Rightarrow> 'a \<Rightarrow> 'a set"
  for g :: "'a auth_graph" and l :: "'a" where
  (* clearly, l can read from anything it has Read authority to *)
  reads_read: "(l,Read,l') \<in> g \<Longrightarrow>  l' \<in> subjectReads g l"
  (* l can read from itself *)
| reads_lrefl[simp,intro!]: "l \<in> subjectReads g l"
  (* if l has SyncSend or Receive authority to an endpoint, l can read it *)
|  reads_ep:
  "\<lbrakk> (l,auth,ep) \<in> g; auth \<in> {SyncSend,Receive} \<rbrakk>
     \<Longrightarrow> ep \<in> subjectReads g l"
|  reads_read_queued_thread_read_ep:
  (* if someone can send on or reset an endpoint, and l can read from a thread t
     that can receive or send synchronously on that endpoint, then l needs to
     be able to read from the endpoint too. This is because the thread t might
     be blocked waiting to send or receive an that endpoint. When the other
     party completes the rendezvous,
     the affects caused to t depend of course on the state of the endpoint.
     Since t is in l's domain, the ep better be too. *)
  "\<lbrakk> (a, auth', ep) \<in> g; auth' \<in> {Notify,SyncSend,Reset};
     (t, auth, ep) \<in> g; auth \<in> {SyncSend, Receive}; t \<in> subjectReads g l \<rbrakk>
     \<Longrightarrow> ep \<in> subjectReads g l"
  (* if someone, t, can write to a page, and the page is in l's domain, that the
     writer better be too. This is needed for when the page is t's ipc buffer,
     and t is blocked on an IPC and the other party completes the operation.
     The affects caused to the page in question naturally depend on t's state,
     so if the page is part of l's domain, t better be too. *)
| reads_read_page_read_thread:
  "\<lbrakk> b \<in> subjectReads g l; (t,Write,b) \<in> g \<rbrakk>
     \<Longrightarrow> t \<in> subjectReads g l"
  (* This is the symmetric case for the rule reads_read_page_read_thread.
     Here now suppose t is a sender of an IPC and p is its IPC buffer, to which
     it necessarily has Read authority. Suppose t is blocked waiting to complete
     the send, and the receiver completes the rendezvous.
     IF t is in l's domain, then the IPC buffer  had better be too, since it
     will clearly be read during the operation to send the IPC *)
| reads_read_thread_read_pages:
  "\<lbrakk> t \<in> subjectReads g l; (t,Read,p) \<in> g \<rbrakk>
     \<Longrightarrow> p \<in> subjectReads g l"
  (* This rule allows domain l to read from all senders to synchronous endpoints
     for all such endpoints in its domain. This is needed for when someone
     does a receive (for which a sender is already blocked) or reset on the ep.
     The affects on the ep here will depend on the state of any blocked
     senders. So if the ep is in l's domain, the senders better be too. *)
| read_sync_ep_read_senders:
  "\<lbrakk> ep \<in> subjectReads g l; (b,SyncSend,ep) \<in> g \<rbrakk>
     \<Longrightarrow> b \<in> subjectReads g l"
| read_sync_ep_call_senders:
  "\<lbrakk> ep \<in> subjectReads g l; (b,Call,ep) \<in> g \<rbrakk>
     \<Longrightarrow> b \<in> subjectReads g l"
  (* This rule allows anyone who can read a synchronous endpoint, to also be
     able to read from its receivers. The intuition is that the state of the
     receivers can affect how the endpoint is affected. *)
  (* I'm not convinced that this rule is strictly necessary. I think that
     the specific state of the receiver doesn't affect the ep too much and
     that we could probably do away with this rule at the cost of some way more
     complex confidentiality proofs for send_ipc. We would have to prove that
     the affect on the ep is the same regardless of /who/ the reciever is
     (and which page their IPC buffer is etc.). This would involve some quite
     tedious equiv_valid_2 proofs for send_ipc and the functions it calls,
     which don't really seem worth it at the moment. *)
  (* If we removed this rule, all it would gain us I think would be the absence
     of direct edges from receiver \<rightarrow> sender in the infoflow policy, but we
     would still have edges from receiver \<rightarrow> ep \<rightarrow> sender in either case. I
     cannot imagine a useful intransitive noninterference policy that permits
     the latter case but not the former, so the extra cost of doing away with
     this rule does not seem worth it IMO. *)
| read_sync_ep_read_receivers:
  "\<lbrakk> ep \<in> subjectReads g l; (b,Receive,ep) \<in> g \<rbrakk>
     \<Longrightarrow> b \<in> subjectReads g l"
  (* if t can reply to t', then t can send directly information to t' *)
| read_reply_thread_read_thread:
  "\<lbrakk> t' \<in> subjectReads g l; (t,Reply,t') \<in> g \<rbrakk>
     \<Longrightarrow> t \<in> subjectReads g l"
  (* This rule is only there for convinience if Reply authorities corresponds to Call authorities*)
| read_reply_thread_read_thread_rev:
  "\<lbrakk> t' \<in> subjectReads g l; (t',Reply,t) \<in> g \<rbrakk>
     \<Longrightarrow> t \<in> subjectReads g l"
  (* if t can reply to t', then t can send directly information to t' *)
| read_delder_thread_read_thread:
  "\<lbrakk> t' \<in> subjectReads g l; (t,DeleteDerived,t') \<in> g \<rbrakk>
     \<Longrightarrow> t \<in> subjectReads g l"
  (* This rule is only there for convinience if Reply authorities corresponds to Call authorities*)
| read_delder_thread_read_thread_rev:
  "\<lbrakk> t' \<in> subjectReads g l; (t',DeleteDerived,t) \<in> g \<rbrakk>
     \<Longrightarrow> t \<in> subjectReads g l"

abbreviation aag_can_read :: "'a PAS \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "aag_can_read aag x \<equiv> (pasObjectAbs aag x) \<in> subjectReads (pasPolicy aag) (pasSubject aag)"

abbreviation aag_can_read_irq :: "'a PAS \<Rightarrow> irq \<Rightarrow> bool" where
  "aag_can_read_irq aag x \<equiv> (pasIRQAbs aag x) \<in> subjectReads (pasPolicy aag) (pasSubject aag)"

abbreviation aag_can_read_asid :: "'a PAS \<Rightarrow> asid \<Rightarrow> bool" where
  "aag_can_read_asid aag x \<equiv> (pasASIDAbs aag x) \<in> subjectReads (pasPolicy aag) (pasSubject aag)"

(* FIXME: having an op\<noteq> in the definition causes clarsimp to spuriously
   apply classical rules. Using @{term disjnt} may avoid this issue *)
abbreviation aag_can_read_domain :: "'a PAS \<Rightarrow> domain \<Rightarrow> bool" where
  "aag_can_read_domain aag x \<equiv>
     pasDomainAbs aag x \<inter> subjectReads (pasPolicy aag) (pasSubject aag) \<noteq> {}"


subsection \<open>Generic equivalence\<close>

definition equiv_for where
  "equiv_for P f c c' \<equiv>  \<forall>x. P x \<longrightarrow> f c x = f c' x"


subsection \<open>Machine state equivalence\<close>

abbreviation equiv_machine_state :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool"
where
  "equiv_machine_state P s s' \<equiv> equiv_for (\<lambda>x. P x) underlying_memory s s'
                              \<and> equiv_for (\<lambda>x. P x) device_state s s'"


subsection \<open>ASID equivalence\<close>

definition equiv_asids :: "(asid \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "equiv_asids R s s' \<equiv> \<forall>asid. asid \<noteq> 0 \<and> R asid \<longrightarrow> equiv_asid asid s s'"

definition identical_updates where
  "identical_updates k k' kh kh' \<equiv> \<forall>x. (kh x \<noteq> kh' x \<longrightarrow> (k x = kh x \<and> k' x = kh' x))"

abbreviation identical_kheap_updates where
  "identical_kheap_updates s s' kh kh' \<equiv> identical_updates (kheap s) (kheap s') kh kh'"

abbreviation identical_ekheap_updates where
  "identical_ekheap_updates s s' kh kh' \<equiv> identical_updates (ekheap s) (ekheap s') kh kh'"

lemmas identical_kheap_updates_def = identical_updates_def
lemmas identical_ekheap_updates_def = identical_updates_def


subsection \<open>Generic state equivalence\<close>

text\<open>Define state equivalence for a given set of object references, irqs, asids and domains

The first four parameters are just predicate for those four sets:
  - P : object reference predicate
  - Q : irq predicate
  - R : asid predicate
  - S : domain predicate
\<close>

(*FIXME: We're not ancient Romans and don't need to condense the meaning of
         the universe into S P Q R *)
definition states_equiv_for ::
  "(obj_ref \<Rightarrow> bool) \<Rightarrow> (irq \<Rightarrow> bool) \<Rightarrow> (asid \<Rightarrow> bool) \<Rightarrow>
   (domain \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equiv_for P Q R S s s' \<equiv>
     equiv_for P kheap s s' \<and>
     equiv_machine_state P (machine_state s) (machine_state s') \<and>
     equiv_for (P \<circ> fst) cdt s s' \<and>
     equiv_for P ekheap s s' \<and>
     equiv_for (P \<circ> fst) cdt_list s s' \<and>
     equiv_for (P \<circ> fst) is_original_cap s s' \<and>
     equiv_for Q interrupt_states s s' \<and>
     equiv_for Q interrupt_irq_node s s' \<and>
     equiv_for S  ready_queues s s' \<and>
     equiv_asids R s s'"

(* This the main use of states_equiv_for : P is use to restrict the labels we want to consider *)
abbreviation states_equiv_for_labels ::
  "'a PAS \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equiv_for_labels aag P \<equiv>
      states_equiv_for (\<lambda>x. P (pasObjectAbs aag x)) (\<lambda>x. P (pasIRQAbs aag x))
                       (\<lambda>x. P (pasASIDAbs aag x)) (\<lambda>x. \<exists>l\<in>pasDomainAbs aag x. P l)"

(* We need this to correctly complement the domain mapping, i.e. it's not true that
     states_equiv_but_for_labels aag P = states_equiv_for_labels aag (not P) *)
abbreviation states_equiv_but_for_labels ::
  "'a PAS \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equiv_but_for_labels aag P \<equiv>
     states_equiv_for (\<lambda>x. \<not> P (pasObjectAbs aag x)) (\<lambda> x. \<not> P (pasIRQAbs aag x))
                      (\<lambda>x. \<not> P (pasASIDAbs aag x)) (\<lambda> x. \<forall>l\<in>pasDomainAbs aag x. \<not> P l)"


subsection \<open>Idle thread equivalence\<close>

definition idle_equiv :: "('z :: state_ext) state \<Rightarrow> ('z :: state_ext) state \<Rightarrow> bool" where
  "idle_equiv s s' \<equiv> idle_thread s = idle_thread s' \<and>
                     (\<forall>tcb tcb'. kheap s (idle_thread s) = Some (TCB tcb)
                                 \<longrightarrow> kheap s' (idle_thread s) = Some (TCB tcb')
                                 \<longrightarrow> arch_tcb_context_get (tcb_arch tcb) =
                                     arch_tcb_context_get (tcb_arch tcb')) \<and>
                     (tcb_at (idle_thread s) s \<longleftrightarrow> tcb_at (idle_thread s) s')"


subsection \<open>Global (Kernel) VSpace equivalence\<close>

(* cur_thread is included here also to enforce this being an equivalence relation *)
definition globals_equiv :: "det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "globals_equiv s s' \<equiv>
     arch_globals_equiv (cur_thread s) (idle_thread s) (kheap s) (kheap s')
                        (arch_state s) (arch_state s') (machine_state s) (machine_state s') \<and>
     idle_equiv s s' \<and> cur_thread s = cur_thread s' \<and>
     dom (device_state (machine_state s)) = dom (device_state (machine_state s'))"


subsection \<open>read_equiv\<close>

(* Basically defines the domain of the current thread, excluding globals.
   This also includes the things that are in the scheduler's domain, which
   the current domain is always allowed to read. *)
definition reads_equiv :: "'a PAS \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "reads_equiv aag s s' \<equiv>
     (\<forall>d\<in>subjectReads (pasPolicy aag) (pasSubject aag).
        states_equiv_for_labels aag ((=) d) s s') \<and>
        cur_thread s = cur_thread s' \<and>
        cur_domain s = cur_domain s' \<and>
        scheduler_action s = scheduler_action s' \<and>
        work_units_completed s = work_units_completed s' \<and>
        irq_state (machine_state s) = irq_state (machine_state s')"


(* this is the main equivalence we want to be maintained, since it defines
   everything the current thread can read from; however, we'll deal with
   reads_equiv in the reads_respects proofs, since globals_equiv is always preserved *)
definition reads_equiv_g :: "'a PAS \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "reads_equiv_g aag s s' \<equiv> reads_equiv aag s s' \<and> globals_equiv s s'"


section \<open>Writing: subjectsAffects and affects_equiv\<close>

text \<open>
  This defines the other labels of the authority graph that subject l can
  affect, i.e. if there is some part of the state that carries a label l', and
  through the actions of l, this state can be modified, then we say that the
  label l' can be affected by l. This is, of course, just a more coarse
  statement of the integrity property from the access proofs.
\<close>
(* FIXME: theorem no longer exists
  The case in which @{thm tro_asidpool_clear} is covered when the graph is wellformed
  since, in this case, the subject has Control rights to the asid.
*)
inductive_set subjectAffects :: "'a auth_graph \<Rightarrow> 'a \<Rightarrow> 'a set"
  for g :: "'a auth_graph" and l :: "'a" where
  affects_lrefl:
    "l \<in> subjectAffects g l"
| affects_write:
    "\<lbrakk> (l,auth,l') \<in> g; auth \<in> {Control, Write} \<rbrakk>
       \<Longrightarrow> l' \<in> subjectAffects g l"
| affects_ep:
    "\<lbrakk> (l,auth,l') \<in> g; auth \<in> {Receive, Notify, SyncSend, Call, Reset} \<rbrakk>
       \<Longrightarrow> l' \<in> subjectAffects g l"
  (* ipc buffer is not necessarily owned by thread *)
| affects_send:
    "\<lbrakk> (l,auth,ep) \<in> g; auth \<in> {SyncSend, Notify, Call}; (l',Receive,ep) \<in> g; (l',Write,l'') \<in> g \<rbrakk>
       \<Longrightarrow> l'' \<in> subjectAffects g l"
  (* synchronous sends provide a back-channel from receiver to sender *)
| affects_recv:
    "\<lbrakk> (l,Receive,ep) \<in> g; (l',SyncSend,ep) \<in> g \<rbrakk>
       \<Longrightarrow> l' \<in> subjectAffects g l"
  (* a reply right can only exist if l has a call right to l',
   * so including this case saves us from having to re-derive it *)
| affects_reply_back:
    "(l',Reply,l) \<in> g \<Longrightarrow> l' \<in> subjectAffects g l"
  (* reply direct ipc buffer writing *)
| affects_reply:
    "\<lbrakk> (l,Reply,l') \<in> g; (l',Write,l'') \<in> g \<rbrakk>
       \<Longrightarrow> l'' \<in> subjectAffects g l"
  (* deletion direct channel *)
| affects_delete_derived:
    "(l,DeleteDerived,l') \<in> g \<Longrightarrow> l' \<in> subjectAffects g l"
  (* If two agents can delete the same caps, they can affect each other *)
| affects_delete_derived2:
    "\<lbrakk> (l,DeleteDerived,l') \<in> g; (l'',DeleteDerived,l') \<in> g \<rbrakk>
       \<Longrightarrow> l'' \<in> subjectAffects g l"
  (* integrity definitions allow resets to modify ipc buffer *)
| affects_reset:
    "\<lbrakk> (l,Reset,ep) \<in> g; (l',auth,ep) \<in> g; auth \<in> {SyncSend, Receive}; (l',Write,l'') \<in> g \<rbrakk>
       \<Longrightarrow> l'' \<in> subjectAffects g l"
  (* if you alter an asid mapping, you affect the domain who owns that asid *)
| affects_asidpool_map:
    "(l,AAuth ASIDPoolMapsASID,l') \<in> g \<Longrightarrow> l' \<in> subjectAffects g l"
  (* if you are sending to an ntfn, which is bound to a tcb that i
     receive blocked on an ep, then you can affect that ep *)
| affects_ep_bound_trans:
    "(\<exists>tcb ntfn. (tcb, Receive, ntfn) \<in> g \<and> (tcb, Receive, ep) \<in> g \<and> (l, Notify, ntfn) \<in> g)
     \<Longrightarrow> ep \<in> subjectAffects g l"

(* We define when the current subject can affect another domain whose label is
   l. This occurs when the current subject can affect some label d that is
   considered to be part of what domain l can read. *)
definition aag_can_affect_label where
  "aag_can_affect_label aag l \<equiv> \<exists>d. d \<in> subjectAffects (pasPolicy aag) (pasSubject aag)
                                  \<and> d \<in> subjectReads (pasPolicy aag) l"

(* Defines when two states are equivalent for some domain l that can be affected
   by the current subject. When the current subject cannot affect domain l,
   we relate all states. *)
definition affects_equiv :: "'a PAS \<Rightarrow> 'a \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "affects_equiv aag l s s' \<equiv>
     if aag_can_affect_label aag l
     then states_equiv_for_labels aag (\<lambda>l'. l' \<in> subjectReads (pasPolicy aag) l) s s'
     else True"

abbreviation aag_can_affect where
  "aag_can_affect aag l \<equiv> \<lambda>x. aag_can_affect_label aag l
                            \<and> pasObjectAbs aag x \<in> subjectReads (pasPolicy aag) l"

abbreviation aag_can_affect_irq where
  "aag_can_affect_irq aag l \<equiv> \<lambda>x. aag_can_affect_label aag l
                                \<and> pasIRQAbs aag x \<in> subjectReads (pasPolicy aag) l"

abbreviation aag_can_affect_asid where
  "aag_can_affect_asid aag l \<equiv> \<lambda>x. aag_can_affect_label aag l
                                 \<and> pasASIDAbs aag x \<in> subjectReads (pasPolicy aag) l"

abbreviation aag_can_affect_domain where
  "aag_can_affect_domain aag l \<equiv> \<lambda>x. aag_can_affect_label aag l
                                   \<and> pasDomainAbs aag x \<inter> subjectReads (pasPolicy aag) l \<noteq> {}"


section \<open>reads_respects\<close>

abbreviation reads_equiv_valid ::
  "(det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow>
   'a PAS \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool" where
  "reads_equiv_valid A B aag P f \<equiv> equiv_valid (reads_equiv aag) A B P f"

abbreviation reads_equiv_valid_inv where
  "reads_equiv_valid_inv A aag P f \<equiv> reads_equiv_valid A A aag P f"

abbreviation reads_spec_equiv_valid ::
  "det_state \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow>
   'a PAS \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool" where
  "reads_spec_equiv_valid s A B aag P f \<equiv> spec_equiv_valid s (reads_equiv aag) A B P f"

abbreviation reads_spec_equiv_valid_inv where
  "reads_spec_equiv_valid_inv s A aag P f \<equiv> reads_spec_equiv_valid s A A aag P f"

(* This property is essentially the confidentiality unwinding condition for
   noninterference. *)
abbreviation reads_respects ::
  "'a PAS \<Rightarrow> 'a \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool" where
  "reads_respects aag l P f \<equiv> reads_equiv_valid_inv (affects_equiv aag l) aag P f"

abbreviation spec_reads_respects ::
  "det_state \<Rightarrow> 'a PAS \<Rightarrow> 'a \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool" where
  "spec_reads_respects s aag l P f \<equiv> reads_spec_equiv_valid_inv s (affects_equiv aag l) aag P f"

abbreviation reads_respects_g ::
  "'a PAS \<Rightarrow> 'a \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool" where
  "reads_respects_g aag l P f \<equiv> equiv_valid_inv (reads_equiv_g aag) (affects_equiv aag l) P f"

definition doesnt_touch_globals where
  "doesnt_touch_globals P f \<equiv> \<forall>(s :: det_state). P s \<longrightarrow> (\<forall>(rv,s')\<in>fst (f s). globals_equiv s s')"

abbreviation reads_equiv_valid_rv where
  "reads_equiv_valid_rv A B aag R P f \<equiv> equiv_valid_2 (reads_equiv aag) A B R P P f f"

abbreviation reads_equiv_valid_rv_inv where
  "reads_equiv_valid_rv_inv A aag R P f \<equiv> reads_equiv_valid_rv A A aag R P f"

section \<open>Constraining modifications to a set of label\<close>
(*
   We define here some machinery for reasoning about updates that occur
   outside of what the current subject can read, and the domain l in
   reads_respects. Such updates cannot be "observed" by reads_respects, which
   allows the two code paths to potentially diverge from each other. This is
   important when, e.g. we look at notifications/signals. The actions taken
   during send_signal cannot depend on the state of the notification, so we
   could have the situation in which in one execution the ntfn has someone
   queued on it but in the other it doesn't. This will occur only if the party
   queued on the ntfn is not in the domains the current subject is allowed to
   read from plus domain l (otherwise being reads_equiv aag and affects_equiv
   aag l would (with the invariants) cause him to be on the queue in both
   scenarios). The update that happens to this party's threadstate in one
   execution but not the other, and the different effects that occur to the
   ntfn in each case, therefore, should not break reads_respects because they
   cannot be observed. We need to be able to reason about this, hence this
   machinery.
*)

abbreviation equiv_irq_state where
  "equiv_irq_state ms ms' \<equiv> irq_state ms = irq_state ms'"

definition equiv_but_for_labels where
  "equiv_but_for_labels aag L s s' \<equiv>
     states_equiv_but_for_labels aag (\<lambda>l. l \<in> L) s s' \<and>
     cur_thread s = cur_thread s' \<and> cur_domain s = cur_domain s' \<and>
     scheduler_action s = scheduler_action s' \<and> work_units_completed s = work_units_completed s' \<and>
     equiv_irq_state (machine_state s) (machine_state s')"

definition equiv_but_for_domain where
  "equiv_but_for_domain aag l s s' \<equiv> equiv_but_for_labels aag (subjectReads (pasPolicy aag) l) s s'"

definition modifies_at_most where
  "modifies_at_most aag L P f \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>(rv,s')\<in>fst(f s). equiv_but_for_labels aag L s s')"

end
