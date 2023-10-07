(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Abstract Specification Instantiations"

theory Deterministic_A
imports
  Structures_A
  "Lib.List_Lib"

begin

text \<open>
\label{c:ext-spec}

The kernel specification operates over states of type @{typ "'a state"}, which
includes all of the abstract kernel state plus an extra field, @{term exst}
of type @{typ "'a"}. By choosing an appropriate concrete type for @{typ "'a"},
we obtain different \emph{instantiations} of this specification, at differing
levels of abstraction. The abstract specification is thus \emph{extensible}.
The basic technique, and its motivation, are described in~\cite{Matichuk_Murray_12}.

Here, we define two such instantiations. The first yields a
largely-deterministic specification by instantiating @{typ "'a"} with
a record that includes concrete scheduler state and
information about sibling ordering in the capability derivation tree (CDT).
We call the resulting
specification the \emph{deterministic abstract specification} and it is
defined below in \autoref{s:det-spec}.

The second instantiation uses the type @{typ unit} for @{typ 'a}, yielding
a specification that is far more nondeterministic. In particular, the
scheduling behaviour and the order in which capabilities are deleted during
a \emph{revoke} system call both become completely nondeterministic.
We call this second instantiation the
\emph{nondeterministic abstract specification} and it is defined below in
\autoref{s:nondet-spec}.
\<close>

text \<open>Translate a state of type @{typ "'a state"} to one of type @{typ "'b state"}
  via a function @{term t} from @{typ "'a"} to @{typ "'b"}.
\<close>
definition trans_state :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a state \<Rightarrow> 'b state" where
"trans_state t s = \<lparr>kheap = kheap s, cdt = cdt s, is_original_cap = is_original_cap s,
                     cur_thread = cur_thread s, idle_thread = idle_thread s,
                     machine_state = machine_state s,
                     interrupt_irq_node = interrupt_irq_node s,
                     interrupt_states = interrupt_states s, arch_state = arch_state s,
                     exst = t(exst s)\<rparr>"

(*<*)
lemma trans_state[simp]: "kheap (trans_state t s) = kheap s"
                            "cdt (trans_state t s) = cdt s"
                            "is_original_cap (trans_state t s) = is_original_cap s"
                            "cur_thread (trans_state t s) = cur_thread s"
                            "idle_thread (trans_state t s) = idle_thread s"
                            "machine_state (trans_state t s) = machine_state s"
                            "interrupt_irq_node (trans_state t s) = interrupt_irq_node s"
                           "interrupt_states (trans_state t s) = interrupt_states s"
                            "arch_state (trans_state t s) = arch_state s"
                            "exst (trans_state t s) = (t (exst s))"
                            "exst (trans_state (\<lambda>_. e) s) = e"
  apply (simp add: trans_state_def)+
  done

lemma trans_state_update[simp]:
 "trans_state t (kheap_update f s) = kheap_update f (trans_state t s)"
 "trans_state t (cdt_update g s) = cdt_update g (trans_state t s)"
 "trans_state t (is_original_cap_update h s) = is_original_cap_update h (trans_state t s)"
 "trans_state t (cur_thread_update i s) = cur_thread_update i (trans_state t s)"
 "trans_state t (idle_thread_update j s) = idle_thread_update j (trans_state t s)"
 "trans_state t (machine_state_update k s) = machine_state_update k (trans_state t s)"
 "trans_state t (interrupt_irq_node_update l s) = interrupt_irq_node_update l (trans_state t s)"
 "trans_state t (arch_state_update m s) = arch_state_update m (trans_state t s)"
 "trans_state t (interrupt_states_update p s) = interrupt_states_update p (trans_state t s)"
  apply (simp add: trans_state_def)+
  done


lemma trans_state_update':
  "trans_state f = exst_update f"
  apply (rule ext)
  apply simp
  done

lemma trans_state_update''[simp]:
  "trans_state t' (trans_state t s) = trans_state (\<lambda>e. t' (t e)) s"
  apply simp
  done
(*>*)

text \<open>Truncate an extended state of type @{typ "'a state"}
  by effectively throwing away all the @{typ "'a"} information.
\<close>
abbreviation "truncate_state \<equiv> trans_state (\<lambda>_. ())"

section "Deterministic Abstract Specification"

text \<open>\label{s:det-spec}
  The deterministic abstract specification tracks the state of the scheduler
and ordering information about sibling nodes in the CDT.\<close>

text \<open>The current scheduler action,
  which is part of the scheduling state.\<close>
datatype scheduler_action =
    resume_cur_thread
  | switch_thread (sch_act_target : obj_ref)
  | choose_new_thread

type_synonym domain = word8

record etcb =
 tcb_priority :: "priority"
 tcb_time_slice :: "nat"
 tcb_domain :: "domain"

definition default_priority :: "priority" where
  "default_priority \<equiv> minBound"

definition default_domain :: "domain" where
  "default_domain \<equiv> minBound"

definition default_etcb :: "etcb" where
  "default_etcb \<equiv> \<lparr>tcb_priority = default_priority, tcb_time_slice = timeSlice, tcb_domain = default_domain\<rparr>"

type_synonym ready_queue = "obj_ref list"

text \<open>
  For each entry in the CDT, we record an ordered list of its children.
  This encodes the order of sibling nodes in the CDT.
\<close>
type_synonym cdt_list = "cslot_ptr \<Rightarrow> cslot_ptr list"

definition work_units_limit :: "machine_word" where
  "work_units_limit = 0x64"
text \<open>
  The extended state of the deterministic abstract specification.
\<close>
record det_ext =
   work_units_completed_internal :: "machine_word"
   scheduler_action_internal :: scheduler_action
   ekheap_internal :: "obj_ref \<Rightarrow> etcb option"
   domain_list_internal :: "(domain \<times> machine_word) list"
   domain_index_internal :: nat
   cur_domain_internal :: domain
   domain_time_internal :: "machine_word"
   ready_queues_internal :: "domain \<Rightarrow> priority \<Rightarrow> ready_queue"
   cdt_list_internal :: cdt_list

text \<open>
  The state of the deterministic abstract specification extends the
  abstract state with the @{typ det_ext} record.
\<close>
type_synonym det_state = "det_ext state"

text \<open>Accessor and update functions for the extended state of the
  deterministic abstract specification.
\<close>
abbreviation
  "work_units_completed (s::det_state) \<equiv> work_units_completed_internal (exst s)"

abbreviation
  "work_units_completed_update f (s::det_state) \<equiv>  trans_state (work_units_completed_internal_update f) s"

abbreviation
  "scheduler_action (s::det_state) \<equiv> scheduler_action_internal (exst s)"

abbreviation
  "scheduler_action_update f (s::det_state) \<equiv>  trans_state (scheduler_action_internal_update f) s"

abbreviation
  "ekheap (s::det_state) \<equiv> ekheap_internal (exst s)"

abbreviation
  "ekheap_update f (s::det_state) \<equiv> trans_state (ekheap_internal_update f) s"

abbreviation
  "domain_list (s::det_state) \<equiv> domain_list_internal (exst s)"

abbreviation
  "domain_list_update f (s::det_state) \<equiv> trans_state (domain_list_internal_update f) s"

abbreviation
  "domain_index (s::det_state) \<equiv> domain_index_internal (exst s)"

abbreviation
  "domain_index_update f (s::det_state) \<equiv> trans_state (domain_index_internal_update f) s"

abbreviation
  "cur_domain (s::det_state) \<equiv> cur_domain_internal (exst s)"

abbreviation
  "cur_domain_update f (s::det_state) \<equiv> trans_state (cur_domain_internal_update f) s"

abbreviation
  "domain_time (s::det_state) \<equiv> domain_time_internal (exst s)"

abbreviation
  "domain_time_update f (s::det_state) \<equiv> trans_state (domain_time_internal_update f) s"

abbreviation
  "ready_queues (s::det_state) \<equiv> ready_queues_internal (exst s)"

abbreviation
  "ready_queues_update f (s::det_state) \<equiv> trans_state (ready_queues_internal_update f) s"

abbreviation
  "cdt_list (s::det_state) \<equiv> cdt_list_internal (exst s)"

abbreviation
  "cdt_list_update f (s::det_state) \<equiv> trans_state (cdt_list_internal_update f) s"

type_synonym 'a det_ext_monad = "(det_state,'a) nondet_monad"

text \<open>
  Basic monadic functions for operating on the extended state of the
  deterministic abstract specification.
\<close>
definition
  get_etcb :: "obj_ref \<Rightarrow> det_state \<Rightarrow> etcb option"
where
  "get_etcb tcb_ref es \<equiv> ekheap es tcb_ref"

definition
  ethread_get :: "(etcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> 'a det_ext_monad"
where
  "ethread_get f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_etcb tptr;
     return $ f tcb
   od"

(* For infoflow, we want to avoid certain read actions, such as reading the priority of the
   current thread when it could be idle. Then we need to make sure we do not rely on the result.
   undefined is the closest we have to a result that can't be relied on *)
definition
  ethread_get_when :: "bool \<Rightarrow> (etcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> 'a det_ext_monad"
where
  "ethread_get_when b f tptr \<equiv> if b then (ethread_get f tptr) else return undefined"

definition set_eobject :: "obj_ref \<Rightarrow> etcb \<Rightarrow> unit det_ext_monad"
  where
 "set_eobject ptr obj \<equiv>
  do es \<leftarrow> get;
    ekh \<leftarrow> return $ (ekheap es)(ptr \<mapsto> obj);
    put (es\<lparr>ekheap := ekh\<rparr>)
  od"

definition
  ethread_set :: "(etcb \<Rightarrow> etcb) \<Rightarrow> obj_ref \<Rightarrow> unit det_ext_monad"
where
  "ethread_set f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_etcb tptr;
     set_eobject tptr $ f tcb
   od"

definition
  set_scheduler_action :: "scheduler_action \<Rightarrow> unit det_ext_monad" where
  "set_scheduler_action action \<equiv>
     modify (\<lambda>es. es\<lparr>scheduler_action := action\<rparr>)"

definition
  thread_set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> unit det_ext_monad" where
  "thread_set_priority tptr prio \<equiv> ethread_set (\<lambda>tcb. tcb\<lparr>tcb_priority := prio\<rparr>) tptr"

definition
  thread_set_time_slice :: "obj_ref \<Rightarrow> nat \<Rightarrow> unit det_ext_monad" where
  "thread_set_time_slice tptr time \<equiv> ethread_set (\<lambda>tcb. tcb\<lparr>tcb_time_slice := time\<rparr>) tptr"

definition
  thread_set_domain :: "obj_ref \<Rightarrow> domain \<Rightarrow> unit det_ext_monad" where
  "thread_set_domain tptr domain \<equiv> ethread_set (\<lambda>tcb. tcb\<lparr>tcb_domain := domain\<rparr>) tptr"


definition
  get_tcb_queue :: "domain \<Rightarrow> priority \<Rightarrow> ready_queue det_ext_monad" where
  "get_tcb_queue d prio \<equiv> do
     queues \<leftarrow> gets ready_queues;
     return (queues d prio)
   od"

definition
  set_tcb_queue :: "domain \<Rightarrow> priority \<Rightarrow> ready_queue \<Rightarrow> unit det_ext_monad" where
  "set_tcb_queue d prio queue \<equiv>
     modify (\<lambda>es. es\<lparr> ready_queues :=
      (\<lambda>d' p. if d' = d \<and> p = prio then queue else ready_queues es d' p)\<rparr>)"


definition
  tcb_sched_action :: "(obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list) \<Rightarrow> obj_ref  \<Rightarrow> unit det_ext_monad" where
  "tcb_sched_action action thread \<equiv> do
     d \<leftarrow> ethread_get tcb_domain thread;
     prio \<leftarrow> ethread_get tcb_priority thread;
     queue \<leftarrow> get_tcb_queue d prio;
     set_tcb_queue d prio (action thread queue)
   od"

definition
  tcb_sched_enqueue :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_enqueue thread queue \<equiv> if (thread \<notin> set queue) then thread # queue else queue"

definition
  tcb_sched_append :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_append thread queue \<equiv> if (thread \<notin> set queue) then queue @ [thread] else queue"

definition
  tcb_sched_dequeue :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_dequeue thread queue \<equiv> filter (\<lambda>x. x \<noteq> thread) queue"


definition reschedule_required :: "unit det_ext_monad" where
  "reschedule_required \<equiv> do
     action \<leftarrow> gets scheduler_action;
     case action of switch_thread t \<Rightarrow> tcb_sched_action (tcb_sched_enqueue) t | _ \<Rightarrow> return ();
     set_scheduler_action choose_new_thread
   od"

definition
  possible_switch_to :: "obj_ref \<Rightarrow> unit det_ext_monad" where
  "possible_switch_to target \<equiv> do
     cur_dom \<leftarrow> gets cur_domain;
     target_dom \<leftarrow> ethread_get tcb_domain target;
     action \<leftarrow> gets scheduler_action;

     if (target_dom \<noteq> cur_dom) then
       tcb_sched_action tcb_sched_enqueue target
     else if (action \<noteq> resume_cur_thread) then
       do
         reschedule_required;
         tcb_sched_action tcb_sched_enqueue target
       od
     else
       set_scheduler_action $ switch_thread target
   od"

definition
  next_domain :: "unit det_ext_monad" where
  "next_domain \<equiv>
    modify (\<lambda>s.
      let domain_index' = (domain_index s + 1) mod length (domain_list s) in
      let next_dom = (domain_list s)!domain_index'
      in s\<lparr> domain_index := domain_index',
            cur_domain := fst next_dom,
            domain_time := snd next_dom,
            work_units_completed := 0\<rparr>)"

definition
  dec_domain_time :: "unit det_ext_monad" where
  "dec_domain_time = modify (\<lambda>s. s\<lparr>domain_time := domain_time s - 1\<rparr>)"

definition set_cdt_list :: "cdt_list \<Rightarrow> (det_state, unit) nondet_monad" where
  "set_cdt_list t \<equiv> do
    s \<leftarrow> get;
    put $ s\<lparr> cdt_list := t \<rparr>
  od"

definition
  update_cdt_list :: "(cdt_list \<Rightarrow> cdt_list) \<Rightarrow> (det_state, unit) nondet_monad"
where
  "update_cdt_list f \<equiv> do
     t \<leftarrow> gets cdt_list;
     set_cdt_list (f t)
  od"


text \<open>The CDT in the implementation is stored in prefix traversal order.
  The following functions traverse its abstract representation here to
  yield corresponding information.
\<close>
definition next_child :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cslot_ptr option" where
  "next_child slot t \<equiv> case (t slot) of [] \<Rightarrow> None |
                                        x # xs \<Rightarrow> Some x"

definition next_sib :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cdt \<Rightarrow> cslot_ptr option" where
  "next_sib slot t m \<equiv> case m slot of None \<Rightarrow> None |
                       Some p \<Rightarrow> after_in_list (t p) slot"


function (domintros) next_not_child :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cdt \<Rightarrow> cslot_ptr option" where
  "next_not_child slot t m = (if next_sib slot t m = None
                             then (case m slot of
                               None \<Rightarrow> None |
                               Some p \<Rightarrow> next_not_child p t m)
                             else next_sib slot t m)"
  by auto

(* next_slot traverses the cdt, replicating mdb_next in the Haskell spec.
        The cdt is traversed child first, by next_child
        going to a nodes first child when it exists,
        otherwise next_not_child looks up the tree until it finds
        a new node to visit as a sibling of its self or some ancestor *)

definition next_slot :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cdt \<Rightarrow> cslot_ptr option" where
  "next_slot slot t m \<equiv> if t slot \<noteq> []
                        then next_child slot t
                        else next_not_child slot t m"

text \<open>\emph{Extended operations} for the deterministic abstract specification.\<close>

definition max_non_empty_queue :: "(priority \<Rightarrow> ready_queue) \<Rightarrow> ready_queue" where
  "max_non_empty_queue queues \<equiv> queues (Max {prio. queues prio \<noteq> []})"


definition default_ext :: "apiobject_type \<Rightarrow> domain \<Rightarrow> etcb option" where
  "default_ext type cdom \<equiv>
      case type of TCBObject \<Rightarrow> Some (default_etcb\<lparr>tcb_domain := cdom\<rparr>)
                         | _ \<Rightarrow> None"

definition retype_region_ext :: "obj_ref list \<Rightarrow> apiobject_type \<Rightarrow> unit det_ext_monad" where
  "retype_region_ext ptrs type \<equiv>  do
                                     ekh \<leftarrow> gets ekheap;
                                     cdom \<leftarrow> gets cur_domain;
                                     ekh' \<leftarrow> return $ foldr (\<lambda>p ekh. (ekh(p := default_ext type cdom))) ptrs ekh;
                                     modify (\<lambda>s. s\<lparr>ekheap := ekh'\<rparr>)
                                  od"

definition cap_swap_ext where
"cap_swap_ext \<equiv> (\<lambda> slot1 slot2 slot1_op slot2_op.
      do
       update_cdt_list (\<lambda>list. list(slot1 := list slot2, slot2 := list slot1));
       update_cdt_list
        (\<lambda>list. case if slot2_op = Some slot1 then Some slot2
                     else if slot2_op = Some slot2 then Some slot1 else slot2_op of
                None \<Rightarrow> (case if slot1_op = Some slot1 then Some slot2
                            else if slot1_op = Some slot2 then Some slot1 else slot1_op of
                       None \<Rightarrow> list
                       | Some slot2_p \<Rightarrow> list(slot2_p := list_replace (list slot2_p) slot1 slot2))
                | Some slot1_p \<Rightarrow>
                    (case if slot1_op = Some slot1 then Some slot2
                         else if slot1_op = Some slot2 then Some slot1 else slot1_op of
                    None \<Rightarrow> list(slot1_p := list_replace (list slot1_p) slot2 slot1)
                    | Some slot2_p \<Rightarrow>
                        if slot1_p = slot2_p
                        then list(slot1_p := list_swap (list slot1_p) slot1 slot2)
                        else list(slot1_p := list_replace (list slot1_p) slot2 slot1,
                                  slot2_p := list_replace (list slot2_p) slot1 slot2)))
    od)"

definition cap_move_ext where
"cap_move_ext \<equiv> (\<lambda> src_slot dest_slot src_p dest_p.
 do

    update_cdt_list (\<lambda>list. case (dest_p) of
      None \<Rightarrow> list |
      Some p \<Rightarrow> list (p := list_remove (list p) dest_slot));

   if (src_slot = dest_slot) then return () else

    (do
    update_cdt_list (\<lambda>list. case (src_p) of
      None \<Rightarrow> list |
      Some p \<Rightarrow> list (p := list_replace (list p) src_slot dest_slot));

    update_cdt_list (\<lambda>list. list (src_slot := [], dest_slot := (list src_slot) @ (list dest_slot)))
    od)

  od)"


definition cap_insert_ext where
"cap_insert_ext \<equiv> (\<lambda> src_parent src_slot dest_slot src_p dest_p.
 do

 update_cdt_list (\<lambda>list. case (dest_p) of
      None \<Rightarrow> list |
      Some p \<Rightarrow> (list (p := list_remove (list p) dest_slot)));

    update_cdt_list (\<lambda>list. case (src_p) of
      None \<Rightarrow> list (
        src_slot := if src_parent then [dest_slot] @ (list src_slot) else list src_slot) |
      Some p \<Rightarrow> list (
        src_slot := if src_parent then [dest_slot] @ (list src_slot) else list src_slot,
        p := if (src_parent \<and> p \<noteq> src_slot) then (list p) else if (src_slot \<noteq> dest_slot) then (list_insert_after (list p) src_slot dest_slot) else (dest_slot # (list p))))
 od)"

definition empty_slot_ext where
"empty_slot_ext \<equiv> (\<lambda> slot slot_p.

    update_cdt_list (\<lambda>list. case slot_p of None \<Rightarrow> list (slot := []) |
      Some p \<Rightarrow> if (p = slot) then list(p := list_remove (list p) slot) else list (p := list_replace_list (list p) slot (list slot), slot := [])))"

definition create_cap_ext where
"create_cap_ext \<equiv> (\<lambda> untyped dest dest_p. do

    update_cdt_list (\<lambda>list. case dest_p of
      None \<Rightarrow> list |
      Some p \<Rightarrow> (list (p := list_remove (list p) dest)));

    update_cdt_list (\<lambda>list. list (untyped := [dest] @ (list untyped)))
  od)"

definition next_revoke_cap where
"next_revoke_cap \<equiv> (\<lambda>slot ext. the (next_child slot (cdt_list ext)))"

definition
  free_asid_select :: "(asid_high_index \<rightharpoonup> 'a) \<Rightarrow> asid_high_index"
where
  "free_asid_select \<equiv> \<lambda>asid_table. fst (hd (filter (\<lambda>(x,y). x \<le> 2 ^ asid_high_bits - 1 \<and> y = None) (assocs asid_table)))"

definition
  free_asid_pool_select :: "(asid_low_index \<rightharpoonup> 'a) \<Rightarrow> asid \<Rightarrow> asid_low_index"
where
  "free_asid_pool_select \<equiv> (\<lambda>pool base.
     fst (hd ((filter (\<lambda> (x,y). ucast x + base \<noteq> 0 \<and> y = None) (assocs pool)))))"

definition update_work_units where
  "update_work_units \<equiv>
     modify (\<lambda>s. s\<lparr>work_units_completed := work_units_completed s + 1\<rparr>)"

definition reset_work_units where
  "reset_work_units \<equiv>
     modify (\<lambda>s. s\<lparr>work_units_completed := 0\<rparr>)"

definition work_units_limit_reached where
  "work_units_limit_reached \<equiv> do
     work_units \<leftarrow> gets work_units_completed;
     return (work_units_limit \<le> work_units)
   od"

text \<open>
  A type class for all instantiations of the abstract specification. In
  practice, this is restricted to basically allow only two sensible
  implementations at present: the deterministic abstract specification and
  the nondeterministic one.
\<close>
class state_ext =
 fixes unwrap_ext :: "'a state \<Rightarrow> det_ext state"
 fixes wrap_ext :: "(det_ext \<Rightarrow> det_ext) \<Rightarrow> ('a \<Rightarrow> 'a)"
 fixes wrap_ext_op :: "unit det_ext_monad \<Rightarrow> ('a state,unit) nondet_monad"
 fixes wrap_ext_bool :: "bool det_ext_monad \<Rightarrow> ('a state,bool) nondet_monad"
 fixes select_switch :: "'a \<Rightarrow> bool"
 fixes ext_init :: "'a"

definition detype_ext :: "obj_ref set \<Rightarrow> 'z::state_ext \<Rightarrow> 'z" where
 "detype_ext S \<equiv> wrap_ext (\<lambda>s. s\<lparr>ekheap_internal := (\<lambda>x. if x \<in> S then None else ekheap_internal s x)\<rparr>)"

instantiation  det_ext_ext :: (type) state_ext
begin

definition "unwrap_ext_det_ext_ext == (\<lambda>x. x) :: det_ext state \<Rightarrow> det_ext state"

definition "wrap_ext_det_ext_ext == (\<lambda>x. x) ::
  (det_ext \<Rightarrow> det_ext) \<Rightarrow> det_ext \<Rightarrow> det_ext"

definition "wrap_ext_op_det_ext_ext == (\<lambda>x. x) ::
  (det_ext state \<Rightarrow> ((unit \<times> det_ext state) set) \<times> bool)
  \<Rightarrow> det_ext state  \<Rightarrow> ((unit \<times> det_ext state) set) \<times> bool"

definition "wrap_ext_bool_det_ext_ext == (\<lambda>x. x) ::
  (det_ext state \<Rightarrow> ((bool \<times> det_ext state) set) \<times> bool)
  \<Rightarrow> det_ext state \<Rightarrow> ((bool \<times> det_ext state) set) \<times> bool"

definition "select_switch_det_ext_ext == (\<lambda>_. True)  :: det_ext\<Rightarrow> bool"

(* this probably doesn't satisfy the invariants *)
definition "ext_init_det_ext_ext \<equiv>
     \<lparr>work_units_completed_internal = 0,
      scheduler_action_internal = resume_cur_thread,
      ekheap_internal = Map.empty (idle_thread_ptr \<mapsto> default_etcb),
      domain_list_internal = [(0,15)],
      domain_index_internal = 0,
      cur_domain_internal = 0,
      domain_time_internal = 15,
      ready_queues_internal = const (const []),
      cdt_list_internal = const []\<rparr> :: det_ext"

instance ..

end

section "Nondeterministic Abstract Specification"

text \<open>\label{s:nondet-spec}
The nondeterministic abstract specification instantiates the extended state
with the unit type -- i.e. it doesn't have any meaningful extended state.
\<close>

instantiation unit :: state_ext
begin


definition "unwrap_ext_unit == (\<lambda>_. undefined) :: unit state \<Rightarrow> det_ext state"

definition "wrap_ext_unit == (\<lambda>f s. ()) :: (det_ext \<Rightarrow> det_ext) \<Rightarrow> unit \<Rightarrow> unit"


definition "wrap_ext_op_unit == (\<lambda>m. return ()) ::
  (det_ext state \<Rightarrow> ((unit \<times> det_ext state) set) \<times> bool) \<Rightarrow> unit state \<Rightarrow> ((unit \<times> unit state) set) \<times> bool"

definition "wrap_ext_bool_unit == (\<lambda>m. select UNIV) ::
  (det_ext state \<Rightarrow> ((bool \<times> det_ext state ) set) \<times> bool) \<Rightarrow> unit state \<Rightarrow> ((bool \<times> unit state) set) \<times> bool"

definition "select_switch_unit == (\<lambda>s. False) :: unit \<Rightarrow> bool"

definition "ext_init_unit \<equiv> () :: unit"

instance ..

end

text \<open>Run an extended operation over the extended state without
  modifying it and use the return value to choose between two computations
  to run.
\<close>
lemmas ext_init_def = ext_init_det_ext_ext_def ext_init_unit_def

definition OR_choice :: "bool det_ext_monad \<Rightarrow> ('z::state_ext state,'a) nondet_monad \<Rightarrow> ('z state,'a) nondet_monad \<Rightarrow> ('z state,'a) nondet_monad" where
"OR_choice c f g \<equiv>
  do
    ex \<leftarrow> get;
    (rv,_) \<leftarrow> select_f (mk_ef ((wrap_ext_bool c) ex));
    if rv then f else g
  od"

definition OR_choiceE :: "bool det_ext_monad \<Rightarrow> ('z::state_ext state,'e + 'a) nondet_monad \<Rightarrow> ('z state,'e + 'a) nondet_monad \<Rightarrow> ('z state,'e + 'a) nondet_monad" where
"OR_choiceE c f g \<equiv>
  doE
    ex \<leftarrow> liftE get;
    (rv,_) \<leftarrow> liftE $ select_f (mk_ef ((wrap_ext_bool c) ex));
    if rv then f else g
  odE"

text \<open>Run an extended operation over the extended state to update the
  extended state, ignoring any return value that the extended operation might
  yield.
\<close>

definition do_extended_op :: "unit det_ext_monad \<Rightarrow> ('z::state_ext state,unit) nondet_monad" where
 "do_extended_op eop \<equiv> do
                         ex \<leftarrow> get;
                         (_,es') \<leftarrow> select_f (mk_ef ((wrap_ext_op eop) ex));
                         modify (\<lambda> state. state\<lparr>exst := (exst es')\<rparr>)
                        od"

text \<open>
  Use the extended state to choose a value from a bounding set @{term S} when
  @{term select_switch} is true. Otherwise just select from @{term S}.
\<close>
definition select_ext :: "(det_ext state \<Rightarrow> 'd) \<Rightarrow> ('d set) \<Rightarrow> ('a::state_ext state,'d) nondet_monad" where
  "select_ext a S \<equiv> do
                      s \<leftarrow> get;
                      x \<leftarrow> if (select_switch (exst s)) then (return (a (unwrap_ext s)))
                          else (select S);
                      assert (x \<in> S);
                      return x
                    od"

(*Defined here because it's asserted before empty_slot*)
definition valid_list_2 :: "cdt_list \<Rightarrow> cdt \<Rightarrow> bool" where
  "valid_list_2 t m \<equiv> (\<forall>p. set (t p) = {c. m c = Some p}) \<and> (\<forall>p. distinct (t p))"

abbreviation valid_list :: "det_ext state \<Rightarrow> bool" where
  "valid_list s \<equiv> valid_list_2 (cdt_list s) (cdt s)"

end
