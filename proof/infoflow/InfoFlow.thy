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
imports
  "Access.ArchSyscall_AC"
  "Lib.EquivValid"
begin

context begin interpretation Arch . (*FIXME: arch_split*)

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

lemma pas_domains_distinct_inj:
  "\<lbrakk> pas_domains_distinct aag;
     l1 \<in> pasDomainAbs aag d;
     l2 \<in> pasDomainAbs aag d \<rbrakk> \<Longrightarrow>
   l1 = l2"
  apply (clarsimp simp: pas_domains_distinct_def)
  apply (drule_tac x=d in spec)
  apply auto
  done

lemma domain_has_unique_label:
  "pas_domains_distinct aag \<Longrightarrow> \<exists>l. pasDomainAbs aag d = {l}"
  by (simp add: pas_domains_distinct_def)

lemma domain_has_the_label:
  "pas_domains_distinct aag \<Longrightarrow> l \<in> pasDomainAbs aag d \<Longrightarrow> the_elem (pasDomainAbs aag d) = l"
  apply (simp add: pas_domains_distinct_def)
  apply (metis singletonD the_elem_eq)
  done


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
  for g :: "'a auth_graph" and l :: "'a"
where
  (* clearly, l can read from anything it has Read authority to *)
  reads_read: "(l,Read,l') \<in> g \<Longrightarrow>  l' \<in> subjectReads g l" |
  (* l can read from itself *)
  reads_lrefl[simp,intro!]: "l \<in> subjectReads g l" |
  (* if l has SyncSend or Receive authority to an endpoint, l can read it *)
  reads_ep:
  "\<lbrakk>(l,auth,ep) \<in> g;  auth \<in> {SyncSend,Receive}\<rbrakk> \<Longrightarrow>
   ep \<in> subjectReads g l" |
  reads_read_queued_thread_read_ep:
  (* if someone can send on or reset an endpoint, and l can read from a thread t
     that can receive or send synchronously on that endpoint, then l needs to
     be able to read from the endpoint too. This is because the thread t might
     be blocked waiting to send or receive an that endpoint. When the other
     party completes the rendezvous,
     the affects caused to t depend of course on the state of the endpoint.
     Since t is in l's domain, the ep better be too. *)
  "\<lbrakk>(a, auth', ep) \<in> g; auth' \<in> {Notify,SyncSend,Reset};
    (t, auth, ep) \<in> g; auth \<in> {SyncSend, Receive};
   t \<in> subjectReads g l\<rbrakk>
   \<Longrightarrow> ep \<in> subjectReads g l" |
  (* if someone, t, can write to a page, and the page is in l's domain, that the
     writer better be too. This is needed for when the page is t's ipc buffer,
     and t is blocked on an IPC and the other party completes the operation.
     The affects caused to the page in question naturally depend on t's state,
     so if the page is part of l's domain, t better be too. *)
  reads_read_page_read_thread:
  "\<lbrakk>b \<in> subjectReads g l; (t,Write,b) \<in> g\<rbrakk> \<Longrightarrow>
   t \<in> subjectReads g l" |
  (* This is the symmetric case for the rule reads_read_page_read_thread.
     Here now suppose t is a sender of an IPC and p is its IPC buffer, to which
     it necessarily has Read authority. Suppose t is blocked waiting to complete
     the send, and the receiver completes the rendezvous.
     IF t is in l's domain, then the IPC buffer  had better be too, since it
     will clearly be read during the operation to send the IPC *)
  reads_read_thread_read_pages:
   "\<lbrakk>t \<in> subjectReads g l; (t,Read,p) \<in> g\<rbrakk> \<Longrightarrow>
    p \<in> subjectReads g l" |
  (* This rule allows domain l to read from all senders to synchronous endpoints
     for all such endpoints in its domain. This is needed for when someone
     does a receive (for which a sender is already blocked) or reset on the ep.
     The affects on the ep here will depend on the state of any blocked
     senders. So if the ep is in l's domain, the senders better be too. *)
  read_sync_ep_read_senders_strong:
  "\<lbrakk>ep \<in> subjectReads g l; (b,SyncSend,ep) \<in> g\<rbrakk> \<Longrightarrow>
   b \<in> subjectReads g l" |
  read_sync_ep_call_senders_strong:
  "\<lbrakk>ep \<in> subjectReads g l; (b,Call,ep) \<in> g\<rbrakk> \<Longrightarrow>
   b \<in> subjectReads g l" |
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
  read_sync_ep_read_receivers_strong:
  "\<lbrakk>ep \<in> subjectReads g l; (b,Receive,ep) \<in> g\<rbrakk> \<Longrightarrow>
   b \<in> subjectReads g l" |

  (* if t can reply to t', then t can send directly information to t' *)
  read_reply_thread_read_thread:
  "\<lbrakk>t' \<in> subjectReads g l; (t,Reply,t') \<in> g\<rbrakk> \<Longrightarrow>
   t \<in> subjectReads g l" |
  (* This rule is only there for convinience if Reply authorities corresponds to Call authorities*)
  read_reply_thread_read_thread_rev:
  "\<lbrakk>t' \<in> subjectReads g l; (t',Reply,t) \<in> g\<rbrakk> \<Longrightarrow>
   t \<in> subjectReads g l" |
  (* if t can reply to t', then t can send directly information to t' *)
  read_delder_thread_read_thread:
  "\<lbrakk>t' \<in> subjectReads g l; (t,DeleteDerived,t') \<in> g\<rbrakk> \<Longrightarrow>
   t \<in> subjectReads g l" |
  (* This rule is only there for convinience if Reply authorities corresponds to Call authorities*)
  read_delder_thread_read_thread_rev:
  "\<lbrakk>t' \<in> subjectReads g l; (t',DeleteDerived,t) \<in> g\<rbrakk> \<Longrightarrow>
   t \<in> subjectReads g l"


lemma read_sync_ep_read_senders:
  "\<lbrakk>(a,auth,ep) \<in> g; auth \<in> {Reset,Receive};
    ep \<in> subjectReads g l; (b,SyncSend,ep) \<in> g\<rbrakk> \<Longrightarrow>
   b \<in> subjectReads g l"
   by (rule read_sync_ep_read_senders_strong)

lemma read_sync_ep_read_receivers:
  "\<lbrakk>(a,auth,ep) \<in> g; auth \<in> {SyncSend};
    ep \<in> subjectReads g l; (b,Receive,ep) \<in> g\<rbrakk> \<Longrightarrow>
   b \<in> subjectReads g l"
   by (rule read_sync_ep_read_receivers_strong)


abbreviation aag_can_read :: "'a PAS \<Rightarrow> word32 \<Rightarrow> bool"
where
  "aag_can_read aag x \<equiv> (pasObjectAbs aag x) \<in> subjectReads (pasPolicy aag) (pasSubject aag)"

abbreviation aag_can_read_irq :: "'a PAS \<Rightarrow> 10 word \<Rightarrow> bool"
where
  "aag_can_read_irq aag x \<equiv> (pasIRQAbs aag x) \<in> subjectReads (pasPolicy aag) (pasSubject aag)"

abbreviation aag_can_read_asid :: "'a PAS \<Rightarrow> asid \<Rightarrow> bool"
where
  "aag_can_read_asid aag x \<equiv> (pasASIDAbs aag x) \<in> subjectReads (pasPolicy aag) (pasSubject aag)"

(* FIXME: having an op\<noteq> in the definition causes clarsimp to spuriously
   apply classical rules. Using @{term disjnt} may avoid this issue *)
abbreviation aag_can_read_domain :: "'a PAS \<Rightarrow> domain \<Rightarrow> bool"
where
  "aag_can_read_domain aag x \<equiv>
     pasDomainAbs aag x \<inter> subjectReads (pasPolicy aag) (pasSubject aag) \<noteq> {}"

lemma aag_can_read_self:
  "is_subject aag x \<Longrightarrow> aag_can_read aag x"
  by simp

lemma aag_can_read_read:
  "aag_has_auth_to aag Read x \<Longrightarrow> aag_can_read aag x"
  by (rule reads_read)

lemma aag_can_read_irq_self:
  "is_subject_irq aag x \<Longrightarrow> aag_can_read_irq aag x"
  by simp

subsection \<open>Generic equivalence\<close>

definition equiv_for
where
  "equiv_for P f c c' \<equiv>  \<forall> x. P x \<longrightarrow> f c x = f c' x"

lemma equiv_forE:
  assumes e: "equiv_for P f c c'"
  obtains "\<And> x. P x \<Longrightarrow> f c x = f c' x"
  apply (erule meta_mp)
  apply(erule e[simplified equiv_for_def, rule_format])
  done

lemma equiv_forI:
  "(\<And> x. P x \<Longrightarrow> f c x = f c' x) \<Longrightarrow> equiv_for P f c c'"
  by(simp add: equiv_for_def)

lemma equiv_forD:
  "equiv_for P f c c' \<Longrightarrow> P x \<Longrightarrow> f c x = f c' x"
  apply(blast elim: equiv_forE)
  done

lemma equiv_for_comp:
  "equiv_for P (f \<circ> g) s s' = equiv_for P f (g s) (g s')"
  apply(simp add: equiv_for_def)
  done

lemma equiv_for_or:
  "equiv_for (A or B) f c c' = (equiv_for A f c c' \<and> equiv_for B f c c')"
  by (fastforce simp: equiv_for_def)

lemma equiv_for_id_update:
  "equiv_for P id c c' \<Longrightarrow>
   equiv_for P id (c(x := v)) (c'(x := v))"
  by (simp add: equiv_for_def)

subsection \<open>Machine state equivalence\<close>
abbreviation equiv_machine_state
  :: "(word32 \<Rightarrow> bool)  \<Rightarrow> 'a machine_state_scheme \<Rightarrow> 'a machine_state_scheme \<Rightarrow> bool"
where
  "equiv_machine_state P s s' \<equiv> equiv_for (\<lambda>x. P x) underlying_memory s s' \<and>
                                equiv_for (\<lambda>x. P x) device_state s s'"

subsection \<open>ASID equivalence\<close>

definition equiv_asid :: "asid \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "equiv_asid asid s s' \<equiv>
    ((arm_asid_table (arch_state s) (asid_high_bits_of asid)) =
     (arm_asid_table (arch_state s') (asid_high_bits_of asid))) \<and>
    (\<forall> pool_ptr.
         arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some pool_ptr \<longrightarrow>
          asid_pool_at pool_ptr s = asid_pool_at pool_ptr s' \<and>
          (\<forall> asid_pool asid_pool'.
             kheap s pool_ptr = Some (ArchObj (ASIDPool asid_pool)) \<and>
             kheap s' pool_ptr = Some (ArchObj (ASIDPool asid_pool')) \<longrightarrow>
               asid_pool (ucast asid) = asid_pool' (ucast asid)))"


definition equiv_asid'
where
  "equiv_asid' asid pool_ptr_opt pool_ptr_opt' kh kh' \<equiv>
    (case pool_ptr_opt of None \<Rightarrow> pool_ptr_opt' = None
                        | Some pool_ptr \<Rightarrow>
       (case pool_ptr_opt' of None \<Rightarrow> False
                            | Some pool_ptr' \<Rightarrow>
          (pool_ptr' = pool_ptr \<and>
           ((\<exists> asid_pool. kh pool_ptr = Some (ArchObj (ASIDPool asid_pool))) =
            (\<exists> asid_pool'. kh' pool_ptr' = Some (ArchObj (ASIDPool asid_pool')))) \<and>
           (\<forall> asid_pool asid_pool'.
             kh pool_ptr = Some (ArchObj (ASIDPool asid_pool)) \<and>
             kh' pool_ptr' = Some (ArchObj (ASIDPool asid_pool')) \<longrightarrow>
               asid_pool (ucast asid) = asid_pool' (ucast asid)))
       )
    )"

lemma asid_pool_at_kheap:
  "asid_pool_at ptr s = (\<exists> asid_pool. kheap s ptr = Some (ArchObj (ASIDPool asid_pool)))"
  apply(clarsimp simp:  obj_at_def)
  apply(rule iffI)
   apply(erule exE, rename_tac ko, clarsimp)
  apply (clarsimp simp: a_type_simps)
  done

lemma equiv_asid:
  "equiv_asid asid s s' = equiv_asid' asid (arm_asid_table (arch_state s) (asid_high_bits_of asid))
                                      (arm_asid_table (arch_state s') (asid_high_bits_of asid))
                                      (kheap s) (kheap s')"
  apply(auto simp: equiv_asid_def equiv_asid'_def split: option.splits simp: asid_pool_at_kheap)
  done


definition equiv_asids :: "(asid \<Rightarrow> bool) \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "equiv_asids R s s' \<equiv> \<forall> asid. asid \<noteq> 0 \<and> R asid \<longrightarrow> equiv_asid asid s s'"

lemma equiv_asids_refl:
  "equiv_asids R s s"
  apply(auto simp: equiv_asids_def equiv_asid_def)
  done

lemma equiv_asids_sym:
  "equiv_asids R s t \<Longrightarrow> equiv_asids R t s"
  apply(auto simp: equiv_asids_def equiv_asid_def)
  done

lemma equiv_asids_trans:
  "\<lbrakk>equiv_asids R s t; equiv_asids R t u\<rbrakk> \<Longrightarrow> equiv_asids R s u"
  apply(fastforce simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)
  done


definition non_asid_pool_kheap_update
where
  "non_asid_pool_kheap_update s kh \<equiv>
    \<forall>x. (\<exists> asid_pool. kheap s x = Some (ArchObj (ASIDPool asid_pool)) \<or>
         kh x = Some (ArchObj (ASIDPool asid_pool))) \<longrightarrow> kheap s x = kh x"

definition identical_updates
where
  "identical_updates k k' kh kh' \<equiv> \<forall>x. (kh x \<noteq> kh' x \<longrightarrow> (k x = kh x \<and> k' x = kh' x))"

abbreviation identical_kheap_updates
where
  "identical_kheap_updates s s' kh kh' \<equiv> identical_updates (kheap s) (kheap s') kh kh'"

abbreviation identical_ekheap_updates
where
  "identical_ekheap_updates s s' kh kh' \<equiv> identical_updates (ekheap s) (ekheap s') kh kh'"

lemmas identical_kheap_updates_def = identical_updates_def
lemmas identical_ekheap_updates_def = identical_updates_def

lemma equiv_asids_non_asid_pool_kheap_update:
  "\<lbrakk>equiv_asids R s s';
    non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh'\<rbrakk> \<Longrightarrow>
  equiv_asids R (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  apply(clarsimp simp: equiv_asids_def equiv_asid non_asid_pool_kheap_update_def)
  apply(fastforce simp: equiv_asid'_def split: option.splits)
  done

lemma equiv_asids_identical_kheap_updates:
  "\<lbrakk>equiv_asids R s s';
    identical_kheap_updates s s' kh kh'\<rbrakk> \<Longrightarrow>
  equiv_asids R (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  apply(clarsimp simp: equiv_asids_def identical_kheap_updates_def)
  apply(clarsimp simp: equiv_asid_def asid_pool_at_kheap)
  apply(case_tac "kh pool_ptr = kh' pool_ptr")
   apply fastforce
  apply fastforce
  done

lemma equiv_asids_triv:
  "\<lbrakk>equiv_asids R s s';
    kheap t = kheap s; arm_asid_table (arch_state t) = arm_asid_table (arch_state s);
    kheap t' = kheap s'; arm_asid_table (arch_state t') = arm_asid_table (arch_state s')\<rbrakk> \<Longrightarrow>
   equiv_asids R t t'"
  apply(fastforce simp: equiv_asids_def equiv_asid equiv_asid'_def)
  done

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
definition states_equiv_for
  :: "(word32 \<Rightarrow> bool) \<Rightarrow> (10 word \<Rightarrow> bool) \<Rightarrow> (asid \<Rightarrow> bool) \<Rightarrow> (domain \<Rightarrow> bool) \<Rightarrow>
      det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
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
abbreviation states_equiv_for_labels :: "'a PAS \<Rightarrow> ('a \<Rightarrow> bool)\<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
  "states_equiv_for_labels aag P \<equiv>
      states_equiv_for (\<lambda> x. P (pasObjectAbs aag x)) (\<lambda> x. P (pasIRQAbs aag x))
                       (\<lambda> x. P (pasASIDAbs aag x))   (\<lambda> x. \<exists>l\<in>pasDomainAbs aag x. P l)"

(* We need this to correctly complement the domain mapping, i.e. it's not true that
     states_equiv_but_for_labels aag P = states_equiv_for_labels aag (not P) *)
abbreviation states_equiv_but_for_labels :: "'a PAS \<Rightarrow> ('a \<Rightarrow> bool)\<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
  "states_equiv_but_for_labels aag P \<equiv>
      states_equiv_for (\<lambda> x. \<not> P (pasObjectAbs aag x)) (\<lambda> x. \<not> P (pasIRQAbs aag x))
                       (\<lambda> x. \<not> P (pasASIDAbs aag x))   (\<lambda> x. \<forall>l\<in>pasDomainAbs aag x. \<not> P l)"

lemma states_equiv_forI:
  "\<lbrakk>equiv_for P kheap s s';
   equiv_machine_state P (machine_state s) (machine_state s');
   equiv_for (P \<circ> fst) cdt s s';
   equiv_for P ekheap s s';
   equiv_for (P \<circ> fst) cdt_list s s';
   equiv_for (P \<circ> fst) is_original_cap s s';
   equiv_for Q interrupt_states s s';
   equiv_for Q interrupt_irq_node s s';
   equiv_asids R s s';
   equiv_for S ready_queues s s'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S s s'"
  by(auto simp: states_equiv_for_def)


lemma states_equiv_for_machine_state_update:
  "\<lbrakk>states_equiv_for P Q R S s s'; equiv_machine_state P kh kh'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (s\<lparr> machine_state := kh \<rparr>) (s'\<lparr> machine_state := kh' \<rparr>)"
  apply(fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
                 elim!: equiv_asids_triv)
  done

lemma states_equiv_for_non_asid_pool_kheap_update:
  "\<lbrakk>states_equiv_for P Q R S s s'; equiv_for P id kh kh';
    non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (s\<lparr> kheap := kh \<rparr>) (s'\<lparr> kheap := kh' \<rparr>)"
  apply(fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
                 elim!: equiv_asids_non_asid_pool_kheap_update)
  done

lemma states_equiv_for_identical_kheap_updates:
  "\<lbrakk>states_equiv_for P Q R S s s';
    identical_kheap_updates s s' kh kh'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (s\<lparr> kheap := kh \<rparr>) (s'\<lparr> kheap := kh' \<rparr>)"
  apply(clarsimp simp: states_equiv_for_def)
  apply(auto elim!: equiv_forE intro!: equiv_forI elim!: equiv_asids_identical_kheap_updates
              simp: identical_kheap_updates_def)
  done

lemma states_equiv_for_cdt_update:
  "\<lbrakk>states_equiv_for P Q R S s s'; equiv_for (P \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (s\<lparr> cdt := kh \<rparr>) (s'\<lparr> cdt := kh' \<rparr>)"
  by (fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
               elim!: equiv_asids_triv)



lemma states_equiv_for_cdt_list_update:
  "\<lbrakk>states_equiv_for P Q R S s s'; equiv_for (P \<circ> fst) id (kh (cdt_list s)) (kh' (cdt_list s'))\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (cdt_list_update kh s) (cdt_list_update kh' s')"
  by (fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
               elim!: equiv_asids_triv)


lemma states_equiv_for_identical_ekheap_updates:
  "\<lbrakk>states_equiv_for P Q R S s s';
    identical_ekheap_updates s s' (kh (ekheap s)) (kh' (ekheap s'))\<rbrakk> \<Longrightarrow>
    states_equiv_for P Q R S (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: identical_ekheap_updates_def equiv_for_def states_equiv_for_def
                      equiv_asids_def equiv_asid_def)


lemma states_equiv_for_ekheap_update:
  "\<lbrakk>states_equiv_for P Q R S s s';
    equiv_for P id (kh (ekheap s)) (kh' (ekheap s'))\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
               elim!: equiv_asids_triv)


lemma states_equiv_for_is_original_cap_update:
  "\<lbrakk>states_equiv_for P Q R S s s'; equiv_for (P \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (s\<lparr> is_original_cap := kh \<rparr>) (s'\<lparr> is_original_cap := kh' \<rparr>)"
  by (fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
               elim!: equiv_asids_triv)


lemma states_equiv_for_interrupt_states_update:
  "\<lbrakk>states_equiv_for P Q R S s s'; equiv_for Q id kh kh'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (s\<lparr> interrupt_states := kh \<rparr>) (s'\<lparr> interrupt_states := kh' \<rparr>)"
  by (fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
               elim!: equiv_asids_triv)


lemma states_equiv_for_interrupt_irq_node_update:
  "\<lbrakk>states_equiv_for P Q R S s s'; equiv_for Q id kh kh'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (s\<lparr> interrupt_irq_node := kh \<rparr>) (s'\<lparr> interrupt_irq_node := kh' \<rparr>)"
  by (fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
               elim!: equiv_asids_triv)


lemma states_equiv_for_ready_queues_update:
  "\<lbrakk>states_equiv_for P Q R S s s'; equiv_for S id kh kh'\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S (s\<lparr> ready_queues := kh \<rparr>) (s'\<lparr> ready_queues := kh' \<rparr>)"
  by (fastforce simp: states_equiv_for_def elim: equiv_forE intro: equiv_forI
               elim!: equiv_asids_triv)


lemma states_equiv_forE:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "equiv_machine_state P (machine_state s) (machine_state s')"
          "equiv_for P kheap s s'"
          "equiv_for (P \<circ> fst) cdt s s'"
          "equiv_for (P \<circ> fst) cdt_list s s'"
          "equiv_for P ekheap s s'"
          "equiv_for (P \<circ> fst) is_original_cap s s'"
          "equiv_for Q interrupt_states s s'"
          "equiv_for Q interrupt_irq_node s s'"
          "equiv_asids R s s'"
          "equiv_for S ready_queues s s'"
  using sef[simplified states_equiv_for_def] by auto

lemma equiv_for_apply: "equiv_for P g (f s) (f s') = equiv_for P (g o f) s s'"
  by (simp add: equiv_for_def)


lemma states_equiv_forE_kheap:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. P x \<Longrightarrow> kheap s x = kheap s' x"
  using sef by(auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_mem:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. P x \<Longrightarrow>
    (underlying_memory (machine_state s)) x = (underlying_memory (machine_state s')) x \<and>
    (device_state (machine_state s)) x = (device_state (machine_state s')) x"
  using sef
  apply (clarsimp simp: states_equiv_for_def elim: equiv_forE)
  apply (elim equiv_forE)
  apply fastforce
  done

lemma states_equiv_forE_cdt:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. P (fst x) \<Longrightarrow> cdt s x = cdt s' x"
  using sef by(auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_cdt_list:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. P (fst x) \<Longrightarrow> cdt_list s x = cdt_list s' x"
  using sef by(auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_ekheap:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. P x \<Longrightarrow> ekheap s x = ekheap s' x"
  using sef by(auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_is_original_cap:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. P (fst x) \<Longrightarrow> is_original_cap s x = is_original_cap s' x"
  using sef by(auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_interrupt_states:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. Q x \<Longrightarrow> interrupt_states s x = interrupt_states s' x"
  using sef by(auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_interrupt_irq_node:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. Q x \<Longrightarrow> interrupt_irq_node s x = interrupt_irq_node s' x"
  using sef by(auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_ready_queues:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And> x. S x \<Longrightarrow> ready_queues s x = ready_queues s' x"
  using sef by(auto simp: states_equiv_for_def elim: equiv_forE)

lemma equiv_for_refl:
  "equiv_for P f s s"
  by(auto simp: equiv_for_def)

lemma equiv_for_sym:
  "equiv_for P f s t \<Longrightarrow> equiv_for P f t s"
  by(auto simp: equiv_for_def)

lemma equiv_for_trans:
  "\<lbrakk>equiv_for P f s t; equiv_for P f t u\<rbrakk> \<Longrightarrow>
   equiv_for P f s u"
  by(auto simp: equiv_for_def)


lemma states_equiv_for_refl:
  "states_equiv_for P Q R S s s"
  by(auto simp: states_equiv_for_def  intro: equiv_for_refl equiv_asids_refl)


lemma states_equiv_for_sym:
  "states_equiv_for P Q R S s t \<Longrightarrow> states_equiv_for P Q R S t s"
  by (auto simp: states_equiv_for_def intro: equiv_for_sym equiv_asids_sym simp: equiv_for_def)



lemma states_equiv_for_trans:
  "\<lbrakk>states_equiv_for P Q R S s t; states_equiv_for P Q R S t u\<rbrakk> \<Longrightarrow>
   states_equiv_for P Q R S s u"
  by (auto simp: states_equiv_for_def
          intro: equiv_for_trans equiv_asids_trans equiv_forI
           elim: equiv_forE)

(* FIXME MOVE *)
lemma or_comp_dist:
  "(A or B) \<circ> f = (A \<circ> f or B \<circ> f)"
  by (simp add: pred_disj_def comp_def)



subsection \<open>Idle thread equivalence\<close>

definition idle_equiv :: "('z :: state_ext) state \<Rightarrow> ('z :: state_ext) state \<Rightarrow> bool"
where
"idle_equiv s s' \<equiv> idle_thread s = idle_thread s' \<and>
                  (\<forall>tcb tcb'. kheap s (idle_thread s) = Some (TCB tcb) \<longrightarrow>
                  kheap s' (idle_thread s) = Some (TCB tcb') \<longrightarrow>
                  arch_tcb_context_get (tcb_arch  tcb) = arch_tcb_context_get (tcb_arch tcb')) \<and>
                  (tcb_at (idle_thread s) s \<longleftrightarrow> tcb_at (idle_thread s) s')"

lemma idle_equiv_refl: "idle_equiv s s"
  by (simp add: idle_equiv_def)

lemma idle_equiv_sym: "idle_equiv s s' \<Longrightarrow> idle_equiv s' s"
  by (clarsimp simp add: idle_equiv_def)

lemma idle_equiv_trans: "idle_equiv s s' \<Longrightarrow> idle_equiv s' s'' \<Longrightarrow> idle_equiv s s''"
  by (clarsimp simp add: idle_equiv_def tcb_at_def get_tcb_def split: option.splits
                  kernel_object.splits)

subsection \<open>Exclusive machine state equivalence\<close>
abbreviation exclusive_state_equiv
where
  "exclusive_state_equiv s s' \<equiv>
     exclusive_state (machine_state s) = exclusive_state (machine_state s')"

subsection \<open>Global (Kernel) VSpace equivalence\<close>
(* globals_equiv should be maintained by everything except the scheduler, since
   nothing else touches the globals frame *)

(* cur_thread is included here also to enforce this being an equivalence relation *)
definition globals_equiv :: "('z :: state_ext) state \<Rightarrow> ('z :: state_ext) state \<Rightarrow> bool" where
  "globals_equiv s s' \<equiv>
     arm_global_pd (arch_state s) = arm_global_pd (arch_state s') \<and>
     kheap s (arm_global_pd (arch_state s)) = kheap s' (arm_global_pd (arch_state s)) \<and>
      idle_equiv s s' \<and>
      dom (device_state (machine_state s)) = dom (device_state (machine_state s')) \<and>
      cur_thread s = cur_thread s' \<and>
      (cur_thread s \<noteq> idle_thread s \<longrightarrow> exclusive_state_equiv s s')"

subsection \<open>read_equiv\<close>
(* Basically defines the domain of the current thread, excluding globals.
   This also includes the things that are in the scheduler's domain, which
   the current domain is always allowed to read. *)
definition reads_equiv :: "'a PAS \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
  "reads_equiv aag s s' \<equiv>
   ((\<forall> d\<in>subjectReads (pasPolicy aag) (pasSubject aag).
         states_equiv_for_labels aag ((=) d) s s') \<and>
         cur_thread s = cur_thread s' \<and>
         cur_domain s = cur_domain s' \<and>
         scheduler_action s = scheduler_action s' \<and>
         work_units_completed s = work_units_completed s' \<and>
         irq_state (machine_state s) = irq_state (machine_state s'))"


(* this is the main equivalence we want to be maintained, since it defines
   everything the current thread can read from; however, we'll deal with
   reads_equiv in the reads_respects proofs, since globals_equiv is always preserved *)
definition reads_equiv_g :: "'a PAS \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
  "reads_equiv_g aag s s' \<equiv> reads_equiv aag s s' \<and> globals_equiv s s'"


lemma reads_equiv_def2:
  "reads_equiv aag s s' =
  (states_equiv_for (aag_can_read aag) (aag_can_read_irq aag) (aag_can_read_asid aag)
                    (aag_can_read_domain aag) s s' \<and>
   cur_thread s = cur_thread s' \<and> cur_domain s = cur_domain s' \<and>
   scheduler_action s = scheduler_action s' \<and> work_units_completed s = work_units_completed s' \<and>
   irq_state (machine_state s) = irq_state (machine_state s'))"
  apply(rule iffI)
   apply(auto simp: reads_equiv_def equiv_for_def states_equiv_for_def equiv_asids_def)
  done


lemma reads_equivE:
  assumes sef: "reads_equiv aag s s'"
  obtains "equiv_for (aag_can_read aag) kheap s s'"
          "equiv_machine_state (aag_can_read aag) (machine_state s) (machine_state s')"
          "equiv_for ((aag_can_read aag) \<circ> fst) cdt s s'"
          "equiv_for ((aag_can_read aag) \<circ> fst) cdt_list s s'"
          "equiv_for (aag_can_read aag) ekheap s s'"
          "equiv_for ((aag_can_read aag) \<circ> fst) is_original_cap s s'"
          "equiv_for (aag_can_read_irq aag) interrupt_states s s'"
          "equiv_for (aag_can_read_irq aag) interrupt_irq_node s s'"
          "equiv_asids (aag_can_read_asid aag) s s'"
          "equiv_for (aag_can_read_domain aag) ready_queues s s'"
          "cur_thread s = cur_thread s'"
          "cur_domain s = cur_domain s'"
          "scheduler_action s = scheduler_action s'"
          "work_units_completed s = work_units_completed s'"
          "irq_state (machine_state s) = irq_state (machine_state s')"
  using sef by(auto simp: reads_equiv_def2 elim: states_equiv_forE)


lemma reads_equiv_machine_state_update:
 "\<lbrakk>reads_equiv aag s s'; equiv_machine_state (aag_can_read aag)  kh kh'; irq_state kh = irq_state kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr> machine_state := kh \<rparr>) (s'\<lparr> machine_state := kh' \<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_machine_state_update)


lemma reads_equiv_non_asid_pool_kheap_update:
  "\<lbrakk>reads_equiv aag s s'; equiv_for (aag_can_read aag) id kh kh';
    non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr> kheap := kh \<rparr>) (s'\<lparr> kheap := kh' \<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_non_asid_pool_kheap_update)


lemma reads_equiv_identical_kheap_updates:
  "\<lbrakk>reads_equiv aag s s';
    identical_kheap_updates s s' kh kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr> kheap := kh \<rparr>) (s'\<lparr> kheap := kh' \<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_identical_kheap_updates)



lemma reads_equiv_cdt_update:
  "\<lbrakk>reads_equiv aag s s'; equiv_for ((aag_can_read aag) \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr> cdt := kh \<rparr>) (s'\<lparr> cdt := kh' \<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_cdt_update)



lemma reads_equiv_cdt_list_update:
  "\<lbrakk>reads_equiv aag s s'; equiv_for ((aag_can_read aag) \<circ> fst) id (kh (cdt_list s)) (kh' (cdt_list s'))\<rbrakk> \<Longrightarrow>
   reads_equiv aag (cdt_list_update kh s) (cdt_list_update kh' s')"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_cdt_list_update)


lemma reads_equiv_identical_ekheap_updates:
  "\<lbrakk>reads_equiv aag s s'; identical_ekheap_updates s s' (kh (ekheap s)) (kh' (ekheap s'))\<rbrakk> \<Longrightarrow>
   reads_equiv aag (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_identical_ekheap_updates)


lemma reads_equiv_ekheap_updates:
  "\<lbrakk>reads_equiv aag s s'; equiv_for (aag_can_read aag) id (kh (ekheap s)) (kh' (ekheap s')) \<rbrakk> \<Longrightarrow>
   reads_equiv aag (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_ekheap_update)


lemma reads_equiv_is_original_cap_update:
  "\<lbrakk>reads_equiv aag s s'; equiv_for ((aag_can_read aag) \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr> is_original_cap := kh \<rparr>) (s'\<lparr> is_original_cap := kh' \<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_is_original_cap_update)


lemma reads_equiv_interrupt_states_update:
  "\<lbrakk>reads_equiv aag s s'; equiv_for (aag_can_read_irq aag) id kh kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr> interrupt_states := kh \<rparr>) (s'\<lparr> interrupt_states := kh' \<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_interrupt_states_update)


lemma reads_equiv_interrupt_irq_node_update:
  "\<lbrakk>reads_equiv aag s s'; equiv_for (aag_can_read_irq aag) id kh kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr> interrupt_irq_node := kh \<rparr>) (s'\<lparr> interrupt_irq_node := kh' \<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_interrupt_irq_node_update)


lemma reads_equiv_ready_queues_update:
  "\<lbrakk>reads_equiv aag s s'; equiv_for (aag_can_read_domain aag) id kh kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr> ready_queues := kh \<rparr>) (s'\<lparr> ready_queues := kh' \<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_ready_queues_update)


lemma reads_equiv_scheduler_action_update:
  "reads_equiv aag s s' \<Longrightarrow>
   reads_equiv aag (s\<lparr> scheduler_action := kh \<rparr>) (s'\<lparr> scheduler_action := kh \<rparr>)"
  by (fastforce simp: reads_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)


lemma reads_equiv_work_units_completed_update:
  "reads_equiv aag s s' \<Longrightarrow>
   reads_equiv aag (s\<lparr> work_units_completed := kh \<rparr>) (s'\<lparr> work_units_completed := kh \<rparr>)"
  by (fastforce simp: reads_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)


lemma reads_equiv_work_units_completed_update':
  "reads_equiv aag s s' \<Longrightarrow>
   reads_equiv aag (s\<lparr> work_units_completed := (f (work_units_completed s)) \<rparr>)
                   (s'\<lparr> work_units_completed := (f (work_units_completed s')) \<rparr>)"
  by (fastforce simp: reads_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)





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
  for g :: "'a auth_graph" and l :: "'a"
where
  affects_lrefl:
    "l \<in> subjectAffects g l" |
  affects_write:
    "\<lbrakk>(l,auth,l') \<in> g; auth \<in> {Control, Write}\<rbrakk> \<Longrightarrow>
     l' \<in> subjectAffects g l" |
  affects_ep:
    "\<lbrakk>(l,auth,l') \<in> g; auth \<in> {Receive, Notify, SyncSend, Call, Reset}\<rbrakk> \<Longrightarrow>
     l' \<in> subjectAffects g l" |
  (* ipc buffer is not necessarily owned by thread *)
  affects_send:
    "\<lbrakk>(l,auth,ep) \<in> g; auth \<in> {SyncSend, Notify, Call}; (l',Receive,ep) \<in> g;
      (l',Write,l'') \<in> g\<rbrakk> \<Longrightarrow>
     l'' \<in> subjectAffects g l" |
  (* synchronous sends provide a back-channel from receiver to sender *)
  affects_recv:
    "\<lbrakk>(l,Receive,ep) \<in> g; (l',SyncSend,ep) \<in> g\<rbrakk> \<Longrightarrow>
     l' \<in> subjectAffects g l" |
  (* a reply right can only exist if l has a call right to l',
   * so including this case saves us from having to re-derive it *)
  affects_reply_back:
    "\<lbrakk>(l',Reply,l) \<in> g\<rbrakk> \<Longrightarrow>
     l' \<in> subjectAffects g l" |
  (* reply direct ipc buffer writing *)
  affects_reply:
    "\<lbrakk>(l,Reply,l') \<in> g; (l',Write,l'') \<in> g\<rbrakk> \<Longrightarrow>
     l'' \<in> subjectAffects g l" |
  (* deletion direct channel *)
  affects_delete_derived:
    "\<lbrakk>(l,DeleteDerived,l') \<in> g\<rbrakk> \<Longrightarrow>
     l' \<in> subjectAffects g l" |
  (* If two agents can delete the same caps, they can affect each other *)
  affects_delete_derived2:
    "\<lbrakk>(l,DeleteDerived,l') \<in> g; (l'',DeleteDerived,l') \<in> g\<rbrakk> \<Longrightarrow>
     l'' \<in> subjectAffects g l" |
  (* integrity definitions allow resets to modify ipc buffer *)
  affects_reset:
    "\<lbrakk>(l,Reset,ep) \<in> g; (l',auth,ep) \<in> g; auth \<in> {SyncSend, Receive};
      (l',Write,l'') \<in> g\<rbrakk> \<Longrightarrow>
     l'' \<in> subjectAffects g l" |
  (* if you alter an asid mapping, you affect the domain who owns that asid *)
  affects_asidpool_map:
    "(l,AAuth ASIDPoolMapsASID,l') \<in> g \<Longrightarrow> l' \<in> subjectAffects g l" |
  (* if you are sending to an ntfn, which is bound to a tcb that is
     receive blocked on an ep, then you can affect that ep *)
  affects_ep_bound_trans:
    "\<lbrakk>\<exists>tcb ntfn. (tcb, Receive, ntfn) \<in> g \<and> (tcb, Receive, ep) \<in> g \<and>
                (l, Notify, ntfn) \<in> g\<rbrakk> \<Longrightarrow>
        ep \<in> subjectAffects g l"

(* We define when the current subject can affect another domain whose label is
   l. This occurs when the current subject can affect some label d that is
   considered to be part of what domain l can read. *)
definition aag_can_affect_label
where
  "aag_can_affect_label aag l \<equiv> \<exists> d. d \<in> subjectAffects (pasPolicy aag) (pasSubject aag) \<and>
                                     d \<in> subjectReads (pasPolicy aag) l"

lemma aag_can_affect_labelI[intro!]:
  "\<lbrakk>d \<in> subjectAffects (pasPolicy aag) (pasSubject aag); d \<in> subjectReads (pasPolicy aag) l\<rbrakk>
     \<Longrightarrow> aag_can_affect_label aag l"
  by (auto simp: aag_can_affect_label_def)

(* Defines when two states are equivalent for some domain l that can be affected
   by the current subject. When the current subject cannot affect domain l,
   we relate all states. *)
definition affects_equiv :: "'a PAS \<Rightarrow> 'a \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool"
where
  "affects_equiv aag l s s' \<equiv>
     (if (aag_can_affect_label aag l) then
         (states_equiv_for_labels aag (\<lambda>l'. l' \<in> subjectReads (pasPolicy aag) l) s s')
      else True)"


lemma equiv_for_trivial:
  "(\<And> x. P x \<Longrightarrow> False) \<Longrightarrow> equiv_for P f c c'"
  by (auto simp: equiv_for_def)

lemma equiv_asids_trivial:
  "(\<And> x. P x \<Longrightarrow> False) \<Longrightarrow> equiv_asids P x y"
  by (auto simp: equiv_asids_def)

abbreviation aag_can_affect
where
  "aag_can_affect aag l \<equiv> \<lambda>x. aag_can_affect_label aag l \<and>
                              pasObjectAbs aag x \<in> subjectReads (pasPolicy aag) l"

abbreviation aag_can_affect_irq
where
  "aag_can_affect_irq aag l \<equiv> \<lambda>x. aag_can_affect_label aag l \<and>
                                  pasIRQAbs aag x \<in> subjectReads (pasPolicy aag) l"

abbreviation aag_can_affect_asid
where
  "aag_can_affect_asid aag l \<equiv> \<lambda>x. aag_can_affect_label aag l \<and>
                                   pasASIDAbs aag x \<in> subjectReads (pasPolicy aag) l"

abbreviation aag_can_affect_domain
where
  "aag_can_affect_domain aag l \<equiv> \<lambda>x. aag_can_affect_label aag l \<and>
                                      pasDomainAbs aag x \<inter> subjectReads (pasPolicy aag) l \<noteq> {}"


lemma affects_equiv_def2:
  "affects_equiv aag l s s' = states_equiv_for (aag_can_affect aag l) (aag_can_affect_irq aag l) (aag_can_affect_asid aag l) (aag_can_affect_domain aag l) s s'"
  apply(clarsimp simp: affects_equiv_def)
  apply(auto intro!: states_equiv_forI equiv_forI equiv_asids_trivial
             dest: equiv_forD
             elim!: states_equiv_forE)
  done

lemma affects_equivE:
  assumes sef: "affects_equiv aag l s s'"
  obtains "equiv_for (aag_can_affect aag l) kheap s s'"
          "equiv_machine_state (aag_can_affect aag l) (machine_state s) (machine_state s')"
          "equiv_for ((aag_can_affect aag l) \<circ> fst) cdt s s'"
          "equiv_for ((aag_can_affect aag l) \<circ> fst) cdt_list s s'"
          "equiv_for (aag_can_affect aag l) ekheap s s'"
          "equiv_for ((aag_can_affect aag l) \<circ> fst) is_original_cap s s'"
          "equiv_for (aag_can_affect_irq aag l) interrupt_states s s'"
          "equiv_for (aag_can_affect_irq aag l) interrupt_irq_node s s'"
          "equiv_asids (aag_can_affect_asid aag l) s s'"
          "equiv_for (aag_can_affect_domain aag l) ready_queues s s'"
  using sef by(auto simp: affects_equiv_def2 elim: states_equiv_forE)


lemma affects_equiv_machine_state_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_machine_state (aag_can_affect aag l) kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr> machine_state := kh \<rparr>) (s'\<lparr> machine_state := kh' \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_machine_state_update)
  done

lemma affects_equiv_non_asid_pool_kheap_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect aag l) id kh kh';
    non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr> kheap := kh \<rparr>) (s'\<lparr> kheap := kh' \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_non_asid_pool_kheap_update)
  done

lemma affects_equiv_identical_kheap_updates:
  "\<lbrakk>affects_equiv aag l s s';
    identical_kheap_updates s s' kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr> kheap := kh \<rparr>) (s'\<lparr> kheap := kh' \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_identical_kheap_updates)
  done

lemma affects_equiv_cdt_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for ((aag_can_affect aag l) \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr> cdt := kh \<rparr>) (s'\<lparr> cdt := kh' \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_cdt_update)
  done

lemma affects_equiv_cdt_list_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for ((aag_can_affect aag l) \<circ> fst) id (kh (cdt_list s)) (kh' (cdt_list s'))\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (cdt_list_update kh s) (cdt_list_update kh' s')"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_cdt_list_update)
  done

lemma affects_equiv_identical_ekheap_updates:
  "\<lbrakk>affects_equiv aag l s s'; identical_ekheap_updates s s' (kh (ekheap s)) (kh' (ekheap s'))\<rbrakk> \<Longrightarrow>
    affects_equiv aag l (ekheap_update kh s) (ekheap_update kh' s')"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_identical_ekheap_updates)
  done

lemma affects_equiv_ekheap_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect aag l) id (kh (ekheap s)) (kh' (ekheap s')) \<rbrakk> \<Longrightarrow>
    affects_equiv aag l (ekheap_update kh s) (ekheap_update kh' s')"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_ekheap_update)
  done

lemma affects_equiv_is_original_cap_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for ((aag_can_affect aag l) \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr> is_original_cap := kh \<rparr>) (s'\<lparr> is_original_cap := kh' \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_is_original_cap_update)
  done

lemma affects_equiv_interrupt_states_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect_irq aag l) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr> interrupt_states := kh \<rparr>) (s'\<lparr> interrupt_states := kh' \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_interrupt_states_update)
  done

lemma affects_equiv_interrupt_irq_node_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect_irq aag l) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr> interrupt_irq_node := kh \<rparr>) (s'\<lparr> interrupt_irq_node := kh' \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_interrupt_irq_node_update)
  done

lemma affects_equiv_ready_queues_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect_domain aag l) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr> ready_queues := kh \<rparr>) (s'\<lparr> ready_queues := kh' \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 intro: states_equiv_for_ready_queues_update)
  done

lemma affects_equiv_scheduler_action_update:
  "affects_equiv aag l s s' \<Longrightarrow>
   affects_equiv aag l (s\<lparr> scheduler_action := kh \<rparr>) (s'\<lparr> scheduler_action := kh \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)
  done

lemma affects_equiv_work_units_completed_update:
  "affects_equiv aag l s s' \<Longrightarrow>
   affects_equiv aag l (s\<lparr> work_units_completed := kh \<rparr>) (s'\<lparr> work_units_completed := kh \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)
  done

lemma affects_equiv_work_units_completed_update':
  "affects_equiv aag l s s' \<Longrightarrow>
   affects_equiv aag l (s\<lparr> work_units_completed := (f (work_units_completed s)) \<rparr>)
                       (s'\<lparr> work_units_completed := (f (work_units_completed s')) \<rparr>)"
  apply(fastforce simp: affects_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)
  done

(* reads_equiv and affects_equiv want to be equivalence relations *)
lemma reads_equiv_refl:
  "reads_equiv aag s s"
  by(auto simp: reads_equiv_def2 intro: states_equiv_for_refl equiv_asids_refl)

lemma reads_equiv_sym:
  "reads_equiv aag s t \<Longrightarrow> reads_equiv aag t s"
  by(auto simp: reads_equiv_def2 intro: states_equiv_for_sym equiv_asids_sym)

lemma reads_equiv_trans:
  "\<lbrakk>reads_equiv aag s t; reads_equiv aag t u\<rbrakk> \<Longrightarrow>
   reads_equiv aag s u"
  by(auto simp: reads_equiv_def2 intro: states_equiv_for_trans equiv_asids_trans)

lemma affects_equiv_refl:
  "affects_equiv aag l s s"
  by(auto simp: affects_equiv_def intro: states_equiv_for_refl equiv_asids_refl)

lemma affects_equiv_sym:
  "affects_equiv aag l s t \<Longrightarrow> affects_equiv aag l t s"
  by(auto simp: affects_equiv_def2 intro: states_equiv_for_sym equiv_asids_sym)

lemma affects_equiv_trans:
  "\<lbrakk>affects_equiv aag l s t; affects_equiv aag l t u\<rbrakk> \<Longrightarrow>
   affects_equiv aag l s u"
  by(auto simp: affects_equiv_def2 intro: states_equiv_for_trans equiv_asids_trans)

section \<open>reads_respects\<close>

abbreviation reads_equiv_valid
  :: "(det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow>
      'a PAS \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool"
where
  "reads_equiv_valid A B aag P f \<equiv> equiv_valid (reads_equiv aag) A B P f"

abbreviation reads_equiv_valid_inv
where
  "reads_equiv_valid_inv A aag P f \<equiv> reads_equiv_valid A A aag P f"


abbreviation reads_spec_equiv_valid
  :: "det_state \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow>
      (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow> 'a PAS \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow>
      (det_state,'b) nondet_monad \<Rightarrow> bool"
where
  "reads_spec_equiv_valid s A B aag P f \<equiv> spec_equiv_valid s (reads_equiv aag) A B P f"

abbreviation reads_spec_equiv_valid_inv
where
  "reads_spec_equiv_valid_inv s A aag P f \<equiv> reads_spec_equiv_valid s A A aag P f"


(* This property is essentially the confidentiality unwinding condition for
   noninterference. *)
abbreviation reads_respects
  :: "'a PAS \<Rightarrow> 'a \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool"
where
  "reads_respects aag l P f \<equiv>
   reads_equiv_valid_inv (affects_equiv aag l) aag P f"

abbreviation spec_reads_respects
  :: "det_state \<Rightarrow> 'a PAS \<Rightarrow> 'a \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool"
where
  "spec_reads_respects s aag l P f \<equiv> reads_spec_equiv_valid_inv s (affects_equiv aag l) aag P f"

abbreviation reads_respects_g
  :: "'a PAS \<Rightarrow> 'a \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool"
where
  "reads_respects_g aag l P f \<equiv>
   equiv_valid_inv (reads_equiv_g aag) (affects_equiv aag l) P f"

definition doesnt_touch_globals
where
  "doesnt_touch_globals P f \<equiv>
   \<forall> s. P s \<longrightarrow> (\<forall>(rv,s')\<in>fst (f s). globals_equiv s s')"

lemma globals_equivI:
  "\<lbrakk>doesnt_touch_globals P f; P s; (rv,s')\<in>fst(f s)\<rbrakk> \<Longrightarrow> globals_equiv s s'"
  by(fastforce simp: doesnt_touch_globals_def)

lemma reads_equiv_gD:
  "reads_equiv_g aag s s' \<Longrightarrow> reads_equiv aag s s' \<and> globals_equiv s s'"
  by(simp add: reads_equiv_g_def)

lemma reads_equiv_gI:
  "\<lbrakk>reads_equiv aag s s'; globals_equiv s s'\<rbrakk> \<Longrightarrow> reads_equiv_g aag s s'"
  by(simp add: reads_equiv_g_def)

lemma globals_equiv_refl:
  "globals_equiv s s"
  by(simp add: globals_equiv_def idle_equiv_refl)

lemma globals_equiv_sym:
  "globals_equiv s t \<Longrightarrow> globals_equiv t s"
  by(auto simp: globals_equiv_def idle_equiv_def)


lemma globals_equiv_trans:
  "\<lbrakk>globals_equiv s t; globals_equiv t u\<rbrakk> \<Longrightarrow> globals_equiv s u"
  unfolding globals_equiv_def
  by clarsimp (metis idle_equiv_trans idle_equiv_def)

(* since doesnt_touch_globals is true for all of the kernel except the scheduler,
   the following lemma shows that we can just prove reads_respects for it, and
   from there get the stronger reads_respects_g result that we need for the
   noninterference theorem *)
lemma reads_respects_g:
  "\<lbrakk>reads_respects aag l P f; doesnt_touch_globals Q f\<rbrakk> \<Longrightarrow>
   reads_respects_g aag l (P and Q) f"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply(drule reads_equiv_gD)
  apply(subgoal_tac "globals_equiv b ba", fastforce intro: reads_equiv_gI)
  apply(rule globals_equiv_trans)
   apply(rule globals_equiv_sym)
   apply(fastforce intro: globals_equivI)
  apply(rule globals_equiv_trans)
   apply(elim conjE, assumption)
  apply(fastforce intro: globals_equivI)
  done



(* prove doesnt_touch_globals as an invariant *)
lemma globals_equiv_invD:
  "\<lbrace> globals_equiv st and P \<rbrace> f \<lbrace> \<lambda>_. globals_equiv st \<rbrace> \<Longrightarrow>
   \<lbrace> P and (=) st \<rbrace> f \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  by(fastforce simp: valid_def intro: globals_equiv_refl)

lemma doesnt_touch_globalsI:
  assumes globals_equiv_inv:
    "\<And> st. \<lbrace> globals_equiv st and P \<rbrace> f \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  shows "doesnt_touch_globals P f"
  apply(clarsimp simp: doesnt_touch_globals_def)
  apply(cut_tac st=s in globals_equiv_inv)
  apply(drule globals_equiv_invD)
  by(fastforce simp: valid_def)


(* Slightly nicer to use version to lift up trivial cases*)
lemma reads_respects_g_from_inv:
  "\<lbrakk>reads_respects aag l P f; \<And>st. invariant f (globals_equiv st)\<rbrakk> \<Longrightarrow>
  reads_respects_g aag l P f"
  apply (rule equiv_valid_guard_imp)
   apply (erule reads_respects_g[where Q="\<lambda>s. True"])
   apply (rule doesnt_touch_globalsI)
   apply simp+
  done


(*Useful for chaining OFs so we don't have to re-state rules*)
lemma reads_respects_g':
  assumes rev: "reads_respects aag l P f"
  assumes gev: "\<And>st. \<lbrace>\<lambda> s. R (globals_equiv st s) s\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  assumes and_imp: "\<And> st s. Q st s \<Longrightarrow> P s \<and> R (globals_equiv st s) s"
  assumes gev_imp: "\<And> st s. R (globals_equiv st s) s \<Longrightarrow> globals_equiv st s"
  shows
   "reads_respects_g aag l (Q st) f"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g[OF rev, where Q="\<lambda>s. R (globals_equiv st s) s"])
   apply (rule doesnt_touch_globalsI)
   apply (rule hoare_pre)
    apply (rule gev)
   apply clarsimp
   apply (frule gev_imp)
   apply (simp add: and_imp)+
  done


lemma equiv_for_guard_imp:
  "\<lbrakk>equiv_for P f s s'; \<And> x. Q x \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> equiv_for Q f s s'"
  by(auto simp: equiv_for_def)

lemma equiv_asids_guard_imp:
  "\<lbrakk>equiv_asids R s s'; \<And> x. Q x \<Longrightarrow> R x\<rbrakk> \<Longrightarrow>  equiv_asids Q s s'"
  by(auto simp: equiv_asids_def)

lemma states_equiv_for_guard_imp:
  "\<lbrakk>states_equiv_for P Q R S s s'; \<And> x. P' x \<Longrightarrow> P x; \<And> x. Q' x \<Longrightarrow> Q x; \<And> x. R' x \<Longrightarrow> R x;
    \<And> x. S' x \<Longrightarrow> S x\<rbrakk> \<Longrightarrow> states_equiv_for P' Q' R' S' s s'"
  by(auto simp: states_equiv_for_def intro: equiv_for_guard_imp equiv_asids_guard_imp)

lemma cur_subject_reads_equiv_affects_equiv:
  "pasSubject aag = l \<Longrightarrow>
   reads_equiv aag s s' \<Longrightarrow> affects_equiv aag l s s'"
  apply(auto simp: reads_equiv_def2 affects_equiv_def equiv_for_def states_equiv_for_def)
  done

(* This lemma says that, if we prove reads_respects above for all l, we will
   prove that information can flow into the domain only from what it is allowed
   to read. *)
lemma reads_equiv_self_reads_respects:
  "pasSubject aag = l \<Longrightarrow>
   reads_equiv_valid_inv \<top>\<top> aag P f = reads_respects aag l P f"
  unfolding equiv_valid_def2 equiv_valid_2_def
  apply(fastforce intro: cur_subject_reads_equiv_affects_equiv)
  done

lemma requiv_get_tcb_eq[intro]:
  "\<lbrakk>reads_equiv aag s t; is_subject aag thread\<rbrakk> \<Longrightarrow> get_tcb thread s = get_tcb thread t"
  apply(auto simp: reads_equiv_def2 elim: states_equiv_forE_kheap dest!: aag_can_read_self
             simp: get_tcb_def split: option.split kernel_object.split)
  done

lemma requiv_cur_thread_eq[intro]:
  "reads_equiv aag s t \<Longrightarrow> cur_thread s = cur_thread t"
  apply (simp add: reads_equiv_def2)
  done

lemma requiv_cur_domain_eq[intro]:
  "reads_equiv aag s t \<Longrightarrow> cur_domain s = cur_domain t"
  apply (simp add: reads_equiv_def2)
  done

lemma requiv_sched_act_eq[intro]:
  "reads_equiv aag s t \<Longrightarrow> scheduler_action s = scheduler_action t"
  apply (simp add: reads_equiv_def2)
  done

lemma requiv_wuc_eq[intro]:
  "reads_equiv aag s t \<Longrightarrow> work_units_completed s = work_units_completed t"
  apply (simp add: reads_equiv_def2)
  done

lemma set_object_reads_respects:
  "reads_respects aag l \<top> (set_object ptr obj)"
  unfolding set_object_def
  apply(clarsimp simp: set_object_def bind_def' get_def gets_def put_def return_def fail_def assert_def
                       get_object_def identical_kheap_updates_def
                 cong del: if_weak_cong)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (rule conjI)
   apply (erule reads_equiv_identical_kheap_updates)
   apply (clarsimp simp: identical_kheap_updates_def)
  apply (erule affects_equiv_identical_kheap_updates)
  apply (clarsimp simp: identical_kheap_updates_def)
  done

lemma update_object_noop:
  "kheap s ptr = Some obj \<Longrightarrow> s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr> = s"
  apply(subgoal_tac "kheap s(ptr \<mapsto> obj) = kheap s")
   apply(simp)
  apply(blast intro: map_upd_triv)
  done

lemma set_object_rev:
  "reads_equiv_valid_inv A aag (\<lambda> s. kheap s ptr = Some obj \<and> is_subject aag ptr) (set_object ptr obj)"
  unfolding equiv_valid_def2 equiv_valid_2_def
  apply(clarsimp simp: set_object_def bind_def get_def gets_def put_def return_def assert_def get_object_def)
  apply(fastforce dest: update_object_noop)
  done

lemma lookup_error_on_failure_rev:
  "reads_equiv_valid_inv A aag P m \<Longrightarrow>
   reads_equiv_valid_inv A aag P (lookup_error_on_failure s m)"
  unfolding lookup_error_on_failure_def
  apply(unfold handleE'_def)
  apply (wp | wpc | simp)+
  done

abbreviation reads_equiv_valid_rv
where
  "reads_equiv_valid_rv A B aag R P f \<equiv> equiv_valid_2 (reads_equiv aag) A B R P P f f"

abbreviation reads_equiv_valid_rv_inv
where
  "reads_equiv_valid_rv_inv A aag R P f \<equiv> reads_equiv_valid_rv A A aag R P f"

section \<open>Basic getters/modifiers lemmas\<close>

lemma gets_kheap_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
               (equiv_for (aag_can_read aag or aag_can_affect aag l) id) \<top> (gets kheap)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                  elim: reads_equivE affects_equivE)
  done

lemma gets_kheap_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag) id) \<top> (gets kheap)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

abbreviation equiv_irq_state
where
  "equiv_irq_state ms ms' \<equiv> irq_state ms = irq_state ms'"

lemma gets_machine_state_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
          (equiv_machine_state (aag_can_read aag or aag_can_affect aag l) And equiv_irq_state)
          \<top> (gets machine_state)"
  apply(simp add: gets_def get_def return_def bind_def)
  apply(clarsimp simp: equiv_valid_2_def)
  apply(fastforce intro: equiv_forI elim: reads_equivE affects_equivE equiv_forE)
  done

lemma gets_machine_state_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_machine_state (aag_can_read aag) And equiv_irq_state) \<top>
                           (gets machine_state)"
  apply(simp add: gets_def get_def return_def bind_def)
  apply(clarsimp simp: equiv_valid_2_def)
  apply(fastforce intro: equiv_forI elim: reads_equivE affects_equivE equiv_forE)
  done

lemma gets_cdt_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id)
                            \<top> (gets cdt)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                  elim: reads_equivE affects_equivE)
  done


lemma gets_cdt_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag \<circ> fst) id) \<top> (gets cdt)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

lemma internal_exst[simp]:"cdt_list_internal o exst = cdt_list"
                           "ekheap_internal o exst = ekheap"
  apply (simp add: o_def)+
  done

lemma gets_cdt_list_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id)
                            \<top> (gets cdt_list)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                  elim: reads_equivE affects_equivE)
  done


lemma gets_cdt_list_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag \<circ> fst) id) \<top> (gets cdt_list)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

lemma gets_ekheap_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for (aag_can_read aag or aag_can_affect aag l) id) \<top> (gets ekheap)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                  elim: reads_equivE affects_equivE)
  done

lemma gets_ekheap_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag) id) \<top> (gets kheap)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

lemma gets_is_original_cap_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id)
                            \<top> (gets is_original_cap)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                  elim: reads_equivE affects_equivE)
  done

lemma gets_is_original_cap_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag \<circ> fst) id) \<top> (gets is_original_cap)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

lemma gets_ready_queues_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for (aag_can_read_domain aag or aag_can_affect_domain aag l) id)
                            \<top> (gets ready_queues)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  (* NB: only clarsimp works here *)
  apply(clarsimp simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist equiv_for_def disjoint_iff_not_equal
                 elim!: reads_equivE affects_equivE)
  done


lemma gets_ready_queues_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read_domain aag) id) \<top> (gets ready_queues)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  (* NB: only force works here *)
  apply(force simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist equiv_for_def disjoint_iff_not_equal
              elim: reads_equivE)
  done


(* We want to prove this kind of thing for functions that don't modify the
   state *)
lemma gets_cur_thread_ev:
  "reads_equiv_valid_inv A aag \<top> (gets cur_thread)"
  apply (rule equiv_valid_guard_imp)
  apply wp
  apply (simp add: reads_equiv_def)
  done

lemma as_user_rev:
  "reads_equiv_valid_inv A aag (K (det f \<and> (\<forall>P. invariant f P) \<and> is_subject aag thread)) (as_user thread f)"
  unfolding as_user_def fun_app_def split_def
  apply (wp set_object_rev select_f_ev)
  apply (rule conjI, fastforce)
  apply (clarsimp split: option.split_asm kernel_object.split_asm simp: get_tcb_def)
  apply (drule state_unchanged[rotated,symmetric])
   apply simp_all
  done

lemma as_user_reads_respects:
  "reads_respects aag l (K (det f \<and> is_subject aag thread)) (as_user thread f)"
  apply (simp add: as_user_def split_def)
  apply (rule gen_asm_ev)
  apply (wp set_object_reads_respects select_f_ev gets_the_ev)
  apply fastforce
  done

lemma get_message_info_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_message_info ptr)"
  apply (simp add: get_message_info_def)
  apply (wp as_user_rev | clarsimp simp: getRegister_def)+
  done

lemma syscall_rev:
  assumes reads_res_m_fault:
    "reads_equiv_valid_inv A aag P m_fault"
  assumes reads_res_m_error:
    "\<And> v. reads_equiv_valid_inv A aag (Q (Inr v)) (m_error v)"
  assumes reads_res_h_fault:
    "\<And> v. reads_equiv_valid_inv A aag (Q (Inl v)) (h_fault v)"
  assumes reads_res_m_finalise:
    "\<And> v. reads_equiv_valid_inv A aag (R (Inr v)) (m_finalise v)"
  assumes reads_res_h_error:
    "\<And> v. reads_equiv_valid_inv A aag (R (Inl v)) (h_error v)"
  assumes m_fault_hoare:
    "\<lbrace> P \<rbrace> m_fault \<lbrace> Q \<rbrace>"
  assumes m_error_hoare:
    "\<And> v. \<lbrace> Q (Inr v) \<rbrace> m_error v \<lbrace> R \<rbrace>"
  shows "reads_equiv_valid_inv A aag P (Syscall_A.syscall m_fault h_fault m_error h_error m_finalise)"
  unfolding Syscall_A.syscall_def without_preemption_def fun_app_def
  apply (wp assms equiv_valid_guard_imp[OF liftE_bindE_ev]
       | rule hoare_strengthen_post[OF m_error_hoare]
       | rule hoare_strengthen_post[OF m_fault_hoare]
       | wpc
       | fastforce)+
  done

lemma syscall_reads_respects_g:
  assumes reads_res_m_fault:
    "reads_respects_g aag l P m_fault"
  assumes reads_res_m_error:
    "\<And> v. reads_respects_g aag l (Q'' v) (m_error v)"
  assumes reads_res_h_fault:
    "\<And> v. reads_respects_g aag l (Q' v) (h_fault v)"
  assumes reads_res_m_finalise:
    "\<And> v. reads_respects_g aag l (R'' v) (m_finalise v)"
  assumes reads_res_h_error:
    "\<And> v. reads_respects_g aag l (R' v) (h_error v)"
  assumes m_fault_hoare:
    "\<lbrace> P \<rbrace> m_fault \<lbrace> case_sum Q' Q'' \<rbrace>"
  assumes m_error_hoare:
    "\<And> v. \<lbrace> Q'' v \<rbrace> m_error v \<lbrace> case_sum R' R'' \<rbrace>"
  shows "reads_respects_g aag l P (Syscall_A.syscall m_fault h_fault m_error h_error m_finalise)"
  unfolding Syscall_A.syscall_def without_preemption_def fun_app_def
  apply (wp assms equiv_valid_guard_imp[OF liftE_bindE_ev]
       | rule hoare_strengthen_post[OF m_error_hoare]
       | rule hoare_strengthen_post[OF m_fault_hoare]
       | wpc
       | fastforce)+
  done


lemma do_machine_op_spec_reads_respects':
  assumes equiv_dmo:
   "equiv_valid_inv (equiv_machine_state (aag_can_read aag) And equiv_irq_state)
                    (equiv_machine_state (aag_can_affect aag l) ) \<top> f"
  shows
  "spec_reads_respects st aag l \<top> (do_machine_op f)"
  unfolding do_machine_op_def spec_equiv_valid_def
  apply(rule equiv_valid_2_guard_imp)
   apply(rule_tac R'="\<lambda> rv rv'. equiv_machine_state (aag_can_read aag or aag_can_affect aag l) rv rv'
                               \<and> equiv_irq_state rv rv'"
              and Q="\<lambda> r s. st = s" and Q'="\<top>\<top>" and P="(=) st" and P'="\<top>"  in equiv_valid_2_bind)
       apply(rule_tac R'="\<lambda> (r, ms') (r', ms'').  r = r'
                                   \<and> equiv_machine_state (aag_can_read aag)  ms' ms''
                                   \<and> equiv_machine_state (aag_can_affect aag l)  ms' ms''
                                   \<and> equiv_irq_state ms' ms''"
                  and Q="\<lambda> r s. st = s" and Q'="\<top>\<top>" and P="\<top>" and P'="\<top>"
             in equiv_valid_2_bind_pre)
            apply(clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
            apply(fastforce intro: reads_equiv_machine_state_update affects_equiv_machine_state_update)
            apply(insert equiv_dmo)[1]
           apply(clarsimp simp: select_f_def equiv_valid_2_def equiv_valid_def2 equiv_for_or
                                split_def equiv_for_def
                         split: prod.splits)
           apply(drule_tac x=rv in spec, drule_tac x=rv' in spec)
           apply(fastforce)
          apply(rule select_f_inv)
         apply(rule wp_post_taut)
        apply simp+
      apply(clarsimp simp: equiv_valid_2_def in_monad)
      apply(fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
     apply(wp | simp)+
  done

(* most of the time (i.e. always except for getActiveIRQ) you'll want this rule *)
lemma do_machine_op_spec_reads_respects:
  assumes equiv_dmo:
   "equiv_valid_inv (equiv_machine_state (aag_can_read aag)) (equiv_machine_state (aag_can_affect aag l)) \<top> f"
  assumes irq_state_inv:
    "\<And>P. \<lbrace>\<lambda>ms. P (irq_state ms)\<rbrace> f \<lbrace>\<lambda>_ ms. P (irq_state ms)\<rbrace>"
  shows
  "spec_reads_respects st aag l \<top> (do_machine_op f)"
  apply(rule do_machine_op_spec_reads_respects')
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply(subgoal_tac "equiv_irq_state b ba", simp)
   apply(insert equiv_dmo, fastforce simp: equiv_valid_def2 equiv_valid_2_def)
  apply(insert irq_state_inv)
  apply(drule_tac x="\<lambda>ms. ms = irq_state s" in meta_spec)
  apply(clarsimp simp: valid_def)
  apply(frule_tac x=s in spec)
  apply(erule (1) impE)
  apply(drule bspec, assumption, simp)
  apply(drule_tac x=t in spec, simp)
  apply(drule bspec, assumption)
  apply simp
  done


lemma do_machine_op_spec_rev:
  assumes equiv_dmo:
   "spec_equiv_valid_inv (machine_state st) (equiv_machine_state (aag_can_read aag)) \<top>\<top> \<top> f"
  assumes mo_inv: "\<And> P. invariant f P"
  shows
  "reads_spec_equiv_valid_inv st A aag P (do_machine_op f)"
  unfolding do_machine_op_def spec_equiv_valid_def
  apply(rule equiv_valid_2_guard_imp)
   apply(rule_tac R'="\<lambda> rv rv'. equiv_machine_state (aag_can_read aag) rv rv' \<and>
                                equiv_irq_state rv rv'"
              and Q="\<lambda> r s. st = s \<and> r = machine_state s"
              and Q'="\<lambda>r s. r = machine_state s"
              and P="(=) st" and P'="\<top>"
               in equiv_valid_2_bind)
       apply(rule_tac R'="\<lambda> (r, ms') (r', ms'').  r = r' \<and>
                                        equiv_machine_state (aag_can_read aag) ms' ms''"
                  and Q="\<lambda> (r,ms') s. ms' = rv \<and> rv = machine_state s \<and> st = s"
                  and Q'="\<lambda> (r,ms') s. ms' = rv' \<and> rv' = machine_state s"
                  and P="\<lambda> s. st = s \<and> rv = machine_state s" and P'="\<lambda> s. rv' = machine_state s"
                  and S="\<lambda> s. st = s \<and> rv = machine_state s" and S'="\<lambda>s. rv' = machine_state s"
                   in equiv_valid_2_bind_pre)
            apply(clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
           apply(clarsimp simp: select_f_def equiv_valid_2_def equiv_valid_def2 equiv_for_or
                                split_def equiv_for_def
                         split: prod.splits)
           apply(insert equiv_dmo)[1]
           apply(clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
           apply(drule_tac x="machine_state t" in spec)
           apply(clarsimp simp: equiv_for_def)
           apply blast
          apply(wp select_f_inv)
          apply clarsimp
          apply(drule state_unchanged[OF mo_inv], simp)
         apply(wp select_f_inv)
         apply clarsimp
         apply(drule state_unchanged[OF mo_inv], simp)
        apply simp+
      apply(clarsimp simp: equiv_valid_2_def in_monad)
      apply(fastforce intro: elim: equiv_forE reads_equivE)
     apply(wp | simp)+
  done

lemma do_machine_op_rev:
  assumes equiv_dmo: "equiv_valid_inv (equiv_machine_state (aag_can_read aag)) \<top>\<top> \<top> f"
  assumes mo_inv: "\<And> P. invariant f P"
  shows "reads_equiv_valid_inv A aag \<top> (do_machine_op f)"
  unfolding do_machine_op_def equiv_valid_def2
  apply(rule_tac W="\<lambda> rv rv'. equiv_machine_state (aag_can_read aag) rv rv' \<and> equiv_irq_state rv rv'"
             and Q="\<lambda> rv s. rv = machine_state s " in equiv_valid_rv_bind)
    apply(blast intro: equiv_valid_rv_guard_imp[OF gets_machine_state_revrv'[simplified bipred_conj_def]])
   apply(rule_tac R'="\<lambda> (r, ms') (r', ms'').  r = r' \<and> equiv_machine_state (aag_can_read aag) ms' ms''"
              and Q="\<lambda> (r,ms') s. ms' = rv \<and> rv = machine_state s "
              and Q'="\<lambda> (r',ms'') s. ms'' = rv' \<and> rv' = machine_state s"
              and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
        apply(clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
       apply(clarsimp simp: select_f_def equiv_valid_2_def)
       apply(insert equiv_dmo, clarsimp simp: equiv_valid_def2 equiv_valid_2_def)[1]
       apply(blast)
    apply(wp select_f_inv)+
    apply(fastforce simp: select_f_def dest: state_unchanged[OF mo_inv])+
  done

definition for_each_byte_of_word :: "(word32 \<Rightarrow> bool) \<Rightarrow> word32 \<Rightarrow> bool"
where
  "for_each_byte_of_word P w \<equiv> \<forall> y\<in>{w..w + 3}. P y"

lemma spec_equiv_valid_hoist_guard:
  "((P st) \<Longrightarrow> spec_equiv_valid_inv st I A \<top> f) \<Longrightarrow> spec_equiv_valid_inv st I A P f"
  apply(clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
  done

lemma dmo_loadWord_rev:
  "reads_equiv_valid_inv A aag (K (for_each_byte_of_word (aag_can_read aag) p))
     (do_machine_op (loadWord p))"
  apply(rule gen_asm_ev)
  apply(rule use_spec_ev)
  apply(rule spec_equiv_valid_hoist_guard)
  apply(rule do_machine_op_spec_rev)
  apply(simp add: loadWord_def equiv_valid_def2 spec_equiv_valid_def)
  apply(rule_tac R'="\<lambda> rv rv'. for_each_byte_of_word (\<lambda> y. rv y = rv' y) p" and Q="\<top>\<top>" and Q'="\<top>\<top>"
             and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
       apply(rule_tac R'="(=)" and Q="\<lambda> r s. p && mask 2 = 0" and Q'="\<lambda> r s. p && mask 2 = 0"
                  and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
            apply(rule return_ev2)
            apply(rule_tac f="word_rcat" in arg_cong)
            apply(fastforce intro: is_aligned_no_wrap' word_plus_mono_right
                             simp: is_aligned_mask for_each_byte_of_word_def) (* slow *)
           apply(rule assert_ev2[OF refl])
          apply(rule assert_wp)+
        apply simp+
       apply(clarsimp simp: equiv_valid_2_def in_monad for_each_byte_of_word_def)
       apply(erule equiv_forD)
       apply fastforce
      apply (wp wp_post_taut loadWord_inv | simp)+
  done

lemma for_each_byte_of_word_imp:
  "(\<And> x. P x \<Longrightarrow> Q x) \<Longrightarrow>
   for_each_byte_of_word P p \<Longrightarrow> for_each_byte_of_word Q p"
  apply(fastforce simp: for_each_byte_of_word_def)
  done

lemma load_word_offs_rev:
  "\<lbrakk>for_each_byte_of_word (aag_can_read aag) (a + of_nat x * of_nat word_size)\<rbrakk> \<Longrightarrow>
  reads_equiv_valid_inv A aag \<top> (load_word_offs a x)"
  unfolding load_word_offs_def fun_app_def
  apply(rule equiv_valid_guard_imp[OF dmo_loadWord_rev])
  apply(clarsimp)
  done

(* generalises auth_ipc_buffers_mem_Write *)
lemma auth_ipc_buffers_mem_Write':
  "\<lbrakk> x \<in> auth_ipc_buffers s thread; pas_refined aag s; valid_objs s\<rbrakk>
  \<Longrightarrow> (pasObjectAbs aag thread, Write, pasObjectAbs aag x) \<in> pasPolicy aag"
  apply (clarsimp simp add: auth_ipc_buffers_member_def)
  apply (drule (1) cap_auth_caps_of_state)
    apply simp
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        vspace_cap_rights_to_auth_def vm_read_write_def is_page_cap_def
                 split: if_split_asm)
   apply (auto dest: ipcframe_subset_page)
  done

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
definition equiv_but_for_labels
where
  "equiv_but_for_labels aag L s s' \<equiv>
      states_equiv_but_for_labels aag (\<lambda>l. l \<in> L) s s' \<and>
      cur_thread s = cur_thread s' \<and> cur_domain s = cur_domain s' \<and>
      scheduler_action s = scheduler_action s' \<and> work_units_completed s = work_units_completed s' \<and>
      equiv_irq_state (machine_state s) (machine_state s')"

definition equiv_but_for_domain
where
  "equiv_but_for_domain aag l s s' \<equiv> equiv_but_for_labels aag (subjectReads (pasPolicy aag) l) s s'"

definition modifies_at_most
where
  "modifies_at_most aag L P f \<equiv> \<forall> s. P s \<longrightarrow> (\<forall> (rv,s')\<in>fst(f s). equiv_but_for_labels aag L s s')"

lemma modifies_at_mostD:
  "\<lbrakk>modifies_at_most aag L P f; P s; (rv,s') \<in> fst(f s)\<rbrakk> \<Longrightarrow>
   equiv_but_for_labels aag L s s'"
  by(auto simp: modifies_at_most_def)

lemma modifies_at_mostI:
  assumes hoare: "\<And> st. \<lbrace> P and equiv_but_for_labels aag L st \<rbrace> f \<lbrace> \<lambda>_. equiv_but_for_labels aag L st \<rbrace>"
  shows "modifies_at_most aag L P f"
  apply(clarsimp simp: modifies_at_most_def)
  apply(erule use_valid)
   apply(rule hoare)
  apply(fastforce simp: equiv_but_for_labels_def states_equiv_for_refl)
  done

(*FIXME: Move*)
lemma invs_kernel_mappings:
  "invs s \<Longrightarrow> valid_kernel_mappings s"
  by (auto simp: invs_def valid_state_def)

end

end
