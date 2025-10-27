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

(* FIXME: this needs style cleanup *)

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
a record that includes
information about sibling ordering in the capability derivation tree (CDT).
We call the resulting
specification the \emph{deterministic abstract specification} and it is
defined below in \autoref{s:det-spec}.

The second instantiation uses the type @{typ unit} for @{typ 'a}, yielding
a specification that is far more nondeterministic. In particular, the
order in which capabilities are deleted during
a \emph{revoke} system call becomes completely nondeterministic.
We call this second instantiation the
\emph{nondeterministic abstract specification} and it is defined below in
\autoref{s:nondet-spec}.
\<close>

text \<open>Translate a state of type @{typ "'a state"} to one of type @{typ "'b state"}
  via a function @{term t} from @{typ "'a"} to @{typ "'b"}.
\<close>
definition trans_state :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a state \<Rightarrow> 'b state" where
  "trans_state t s = abstract_state.extend (abstract_state.truncate s) (state.fields (t (exst s)))"

(*<*)
lemma trans_state[simp]:
  "kheap (trans_state t s) = kheap s"
  "cdt (trans_state t s) = cdt s"
  "is_original_cap (trans_state t s) = is_original_cap s"
  "cur_thread (trans_state t s) = cur_thread s"
  "idle_thread (trans_state t s) = idle_thread s"
  "machine_state (trans_state t s) = machine_state s"
  "interrupt_irq_node (trans_state t s) = interrupt_irq_node s"
  "interrupt_states (trans_state t s) = interrupt_states s"
  "arch_state (trans_state t s) = arch_state s"
  "consumed_time (trans_state t s) = consumed_time s"
  "cur_time (trans_state t s) = cur_time s"
  "cur_sc (trans_state t s) = cur_sc s"
  "reprogram_timer (trans_state t s) = reprogram_timer s"
  "scheduler_action (trans_state t s) = scheduler_action s"
  "domain_list (trans_state t s) = domain_list s"
  "domain_index (trans_state t s) = domain_index s"
  "cur_domain (trans_state t s) = cur_domain s"
  "domain_time (trans_state t s) = domain_time s"
  "ready_queues (trans_state t s) = ready_queues s"
  "release_queue (trans_state t s) = release_queue s"
  "exst (trans_state t s) = (t (exst s))"
  "exst (trans_state (\<lambda>_. e) s) = e"
  by (simp add: trans_state_def abstract_state.defs state.defs)+

lemma trans_state_update[simp]:
  "trans_state t (kheap_update f s) = kheap_update f (trans_state t s)"
  "trans_state t (cdt_update g s) = cdt_update g (trans_state t s)"
  "trans_state t (is_original_cap_update h s) = is_original_cap_update h (trans_state t s)"
  "trans_state t (cur_thread_update i s) = cur_thread_update i (trans_state t s)"
  "trans_state t (idle_thread_update j s) = idle_thread_update j (trans_state t s)"
  "trans_state t (machine_state_update k s) = machine_state_update k (trans_state t s)"
  "trans_state t (interrupt_irq_node_update l s) = interrupt_irq_node_update l (trans_state t s)"
  "trans_state t (arch_state_update m s) = arch_state_update m (trans_state t s)"
  "trans_state t (consumed_time_update x s) = consumed_time_update x (trans_state t s)"
  "trans_state t (cur_time_update y s) = cur_time_update y (trans_state t s)"
  "trans_state t (cur_sc_update z s) = cur_sc_update z (trans_state t s)"
  "trans_state t (reprogram_timer_update a s) = reprogram_timer_update a (trans_state t s)"
  "trans_state t (scheduler_action_update b s) = scheduler_action_update b (trans_state t s)"
  "trans_state t (domain_list_update c s) = domain_list_update c (trans_state t s)"
  "trans_state t (domain_index_update d s) = domain_index_update d (trans_state t s)"
  "trans_state t (cur_domain_update e s) = cur_domain_update e (trans_state t s)"
  "trans_state t (domain_time_update f2 s) = domain_time_update f2 (trans_state t s)"
  "trans_state t (ready_queues_update g2 s) = ready_queues_update g2 (trans_state t s)"
  "trans_state t (release_queue_update h2 s) = release_queue_update h2 (trans_state t s)"
  by (simp add: trans_state_def abstract_state.defs)+


lemma trans_state_update':
  "trans_state f = exst_update f"
  by (rule ext) simp

lemma trans_state_update''[simp]:
  "trans_state t' (trans_state t s) = trans_state (\<lambda>e. t' (t e)) s"
  by simp
(*>*)

text \<open>Truncate an extended state of type @{typ "'a state"}
  by effectively throwing away all the @{typ "'a"} information.
\<close>
abbreviation "truncate_state \<equiv> trans_state (\<lambda>_. ())"

section "Deterministic Abstract Specification"

text \<open>\label{s:det-spec}
  The deterministic abstract specification tracks
  ordering information about sibling nodes in the CDT.\<close>

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
  "cdt_list (s::det_state) \<equiv> cdt_list_internal (exst s)"

abbreviation
  "cdt_list_update f (s::det_state) \<equiv> trans_state (cdt_list_internal_update f) s"

type_synonym 'a det_ext_monad = "(det_state,'a) nondet_monad"


section \<open>Type Class\<close>

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


section \<open>Type Class Instances\<close>

subsection "Deterministic Abstract Specification"

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

definition "ext_init_det_ext_ext \<equiv>
     \<lparr>work_units_completed_internal = 0,
      cdt_list_internal = const [] \<rparr> :: det_ext"

instance ..

end

subsection "Nondeterministic Abstract Specification"

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


section \<open>Basic Deterministic Monadic Accessors\<close>

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
(* FIXME: use Lib.hd_opt instead *)
definition next_child :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cslot_ptr option" where
  "next_child slot t \<equiv> case t slot of [] \<Rightarrow> None | x # xs \<Rightarrow> Some x"

definition next_sib :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cdt \<Rightarrow> cslot_ptr option" where
  "next_sib slot t m \<equiv> case m slot of None \<Rightarrow> None |
                       Some p \<Rightarrow> after_in_list (t p) slot"


function (domintros) next_not_child :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cdt \<Rightarrow> cslot_ptr option" where
  "next_not_child slot t m = (if next_sib slot t m = None
                              then case m slot of
                                      None \<Rightarrow> None
                                    | Some p \<Rightarrow> next_not_child p t m
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

    update_cdt_list (\<lambda>list. case dest_p of
      None \<Rightarrow> list |
      Some p \<Rightarrow> list (p := list_remove (list p) dest_slot));

   if src_slot = dest_slot then return () else

    (do
    update_cdt_list (\<lambda>list. case src_p of
      None \<Rightarrow> list |
      Some p \<Rightarrow> list (p := list_replace (list p) src_slot dest_slot));

    update_cdt_list (\<lambda>list. list (src_slot := [], dest_slot := list src_slot @ list dest_slot))
    od)

  od)"


definition cap_insert_ext where
  "cap_insert_ext \<equiv> \<lambda>src_parent src_slot dest_slot src_p dest_p. do
     update_cdt_list (\<lambda>list. case dest_p of
       None \<Rightarrow> list
     | Some p \<Rightarrow> list (p := list_remove (list p) dest_slot));
     update_cdt_list (\<lambda>list. case src_p of
       None \<Rightarrow> list (src_slot := if src_parent then [dest_slot] @ list src_slot else list src_slot)
     | Some p \<Rightarrow> list (src_slot := if src_parent then [dest_slot] @ list src_slot else list src_slot,
                       p := if src_parent \<and> p \<noteq> src_slot
                            then list p
                            else if src_slot \<noteq> dest_slot
                                 then list_insert_after (list p) src_slot dest_slot
                                 else dest_slot # list p))
   od"

definition empty_slot_ext where
"empty_slot_ext \<equiv> \<lambda> slot slot_p.
    update_cdt_list (\<lambda>list. case slot_p of None \<Rightarrow> list (slot := []) |
      Some p \<Rightarrow> if p = slot
                then list(p := list_remove (list p) slot)
                else list (p := list_replace_list (list p) slot (list slot), slot := []))"

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
definition select_ext ::
  "(det_ext state \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> ('a::state_ext state,'d) nondet_monad" where
  "select_ext a S \<equiv> do
     s \<leftarrow> get;
     x \<leftarrow> if select_switch (exst s)
          then return (a (unwrap_ext s))
          else select S;
     assert (x \<in> S);
     return x
   od"

(*Defined here because it's asserted before empty_slot*)
definition valid_list_2 :: "cdt_list \<Rightarrow> cdt \<Rightarrow> bool" where
  "valid_list_2 t m \<equiv> (\<forall>p. set (t p) = {c. m c = Some p}) \<and> (\<forall>p. distinct (t p))"

abbreviation valid_list :: "det_ext state \<Rightarrow> bool" where
  "valid_list s \<equiv> valid_list_2 (cdt_list s) (cdt s)"

end
