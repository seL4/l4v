(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
Functions to access kernel memory.
*)

chapter {* Accessing the Kernel Heap *}

theory KHeap_A
imports Exceptions_A
begin

text {* This theory gives auxiliary getter and setter methods
for kernel objects. *}

section "General Object Access"

definition
  get_object :: "obj_ref \<Rightarrow> (kernel_object,'z::state_ext) s_monad"
where
  "get_object ptr \<equiv> do
     kh \<leftarrow> gets kheap;
     assert (kh ptr \<noteq> None);
     return $ the $ kh ptr
   od"

definition
  set_object :: "obj_ref \<Rightarrow> kernel_object \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_object ptr obj \<equiv> do
     s \<leftarrow> get;
     kh \<leftarrow> return $ (kheap s)(ptr := Some obj);
     put (s \<lparr> kheap := kh \<rparr>)
   od"


section "TCBs"

definition
  thread_get :: "(tcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "thread_get f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     return $ f tcb
   od"

definition
  thread_set :: "(tcb \<Rightarrow> tcb) \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "thread_set f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     set_object tptr $ TCB $ f tcb
   od"

definition
  arch_thread_get :: "(arch_tcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "arch_thread_get f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     return $ f (tcb_arch tcb)
   od"

definition
  arch_thread_set :: "(arch_tcb \<Rightarrow> arch_tcb) \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "arch_thread_set f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     set_object tptr $ TCB $ tcb \<lparr> tcb_arch := f (tcb_arch tcb) \<rparr>
   od"

definition
  get_thread_state :: "obj_ref \<Rightarrow> (thread_state,'z::state_ext) s_monad"
where
  "get_thread_state ref \<equiv> thread_get tcb_state ref"

definition
  get_tcb_obj_ref :: "(tcb => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_tcb_obj_ref f ref \<equiv> thread_get f ref"

definition
  set_tcb_obj_ref :: "((obj_ref option \<Rightarrow> obj_ref option) \<Rightarrow> tcb \<Rightarrow> tcb) \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_tcb_obj_ref f ref new \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb ref;
     set_object ref (TCB (f (K new) tcb))
   od"

section "getters/setters for simple kernel objects"
(* to be used for abstraction unifying kernel objects other than TCB, CNode, and SchedContext *)

definition
  get_simple_ko :: "('a \<Rightarrow> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "get_simple_ko f ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (is_simple_type kobj);
     (case partial_inv f kobj of Some e \<Rightarrow> return e | _ \<Rightarrow> fail)
   od"


definition
  set_simple_ko :: "('a \<Rightarrow> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> 'a \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_simple_ko f ptr ep \<equiv> do
     obj \<leftarrow> get_object ptr;
     assert (is_simple_type obj);
     assert (case partial_inv f obj of Some e \<Rightarrow> a_type obj = a_type (f ep) | _ \<Rightarrow> False);
     set_object ptr (f ep)
   od"


section {* Synchronous and Asyncronous Endpoints *}


abbreviation
  get_endpoint :: "obj_ref \<Rightarrow> (endpoint,'z::state_ext) s_monad" where
  "get_endpoint \<equiv> get_simple_ko Endpoint"

abbreviation
  set_endpoint :: "obj_ref \<Rightarrow> endpoint \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_endpoint \<equiv> set_simple_ko Endpoint"

abbreviation
  get_notification :: "obj_ref \<Rightarrow> (notification,'z::state_ext) s_monad" where
  "get_notification \<equiv> get_simple_ko Notification"

abbreviation
  set_notification :: "obj_ref \<Rightarrow> notification \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_notification \<equiv> set_simple_ko Notification"


section {* IRQ State and Slot *}

definition
  get_irq_state :: "irq \<Rightarrow> (irq_state,'z::state_ext) s_monad" where
 "get_irq_state irq \<equiv> gets (\<lambda>s. interrupt_states s irq)"

definition
  set_irq_state :: "irq_state \<Rightarrow> irq \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "set_irq_state state irq \<equiv> do
    modify (\<lambda>s. s \<lparr> interrupt_states := (interrupt_states s) (irq := state)\<rparr>);
    do_machine_op $ maskInterrupt (state = IRQInactive) irq
  od"

definition
  get_irq_slot :: "irq \<Rightarrow> (cslot_ptr,'z::state_ext) s_monad" where
 "get_irq_slot irq \<equiv> gets (\<lambda>st. (interrupt_irq_node st irq, []))"

section {* Reply Objects *}

abbreviation
  get_reply :: "obj_ref \<Rightarrow> (reply,'z::state_ext) s_monad" where
  "get_reply \<equiv> get_simple_ko Reply"

abbreviation
  set_reply :: "obj_ref \<Rightarrow> reply \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_reply \<equiv> set_simple_ko Reply"


abbreviation
  "get_reply_tcb r \<equiv> liftM reply_tcb (get_reply r)"
(*
abbreviation
  "get_reply_caller r \<equiv> liftM reply_caller (get_reply r)"

abbreviation
  "get_reply_callee r \<equiv> liftM reply_callee (get_reply r)"
*)

section {* Scheduling Contexts *}

definition
  get_sched_context :: "obj_ref \<Rightarrow> (sched_context,'z::state_ext) s_monad"
where
  "get_sched_context ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     case kobj of SchedContext sc n \<Rightarrow> return sc
                 | _ \<Rightarrow> fail
   od"

definition
  set_sched_context_obj :: "obj_ref \<Rightarrow> sched_context \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_sched_context_obj ptr sc n  \<equiv> do
     obj \<leftarrow> get_object ptr;
     assert (case obj of SchedContext sc n \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (SchedContext sc n)
   od"

definition
  get_sc_obj_ref :: "(sched_context => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_sc_obj_ref f ref \<equiv> do
     sc \<leftarrow> get_sched_context ref;
     return $ f sc
   od"

definition (* set only the schedcontext, keeping the size *)
  set_sched_context :: "obj_ref \<Rightarrow> sched_context \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_sched_context ptr sc  \<equiv> do
     obj \<leftarrow> get_object ptr;
     case obj of SchedContext sc' n \<Rightarrow> set_object ptr (SchedContext sc n) | _ \<Rightarrow> fail
   od"

definition (* update only the schedcontext in place, keeping the size *)
  update_sched_context :: "obj_ref \<Rightarrow> (sched_context \<Rightarrow> sched_context) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "update_sched_context ptr f  \<equiv> do
     obj \<leftarrow> get_object ptr;
     case obj of SchedContext sc n \<Rightarrow> set_object ptr (SchedContext (f sc) n) | _ \<Rightarrow> fail
   od"

definition
  set_sc_obj_ref :: "(('a \<Rightarrow> 'a) \<Rightarrow> sched_context \<Rightarrow> sched_context) \<Rightarrow> obj_ref \<Rightarrow> 'a \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_sc_obj_ref f ref new \<equiv> update_sched_context ref (f (K new))"

definition
  is_schedulable :: "obj_ref \<Rightarrow> bool \<Rightarrow> ('z::state_ext state, bool) nondet_monad"
where
  "is_schedulable tcb_ptr in_release_q \<equiv> do
    tcb \<leftarrow> gets_the $ get_tcb tcb_ptr;
    if Option.is_none (tcb_sched_context tcb)
    then return False
    else do
      sc \<leftarrow> get_sched_context $ the $ tcb_sched_context tcb;
      return (runnable (tcb_state tcb)
              \<and> sc_refill_max sc > 0 \<and> \<not>in_release_q)
    od
  od"

definition
  test_sc_refill_max :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "test_sc_refill_max sp \<equiv> (\<lambda>s.
     case kheap s sp of
       Some (SchedContext sc _) \<Rightarrow> (sc_refill_max sc > 0)
     | _ \<Rightarrow> False)"

definition
  is_schedulable_opt :: "obj_ref \<Rightarrow> bool \<Rightarrow> 'z::state_ext state \<Rightarrow> bool option"
where
  "is_schedulable_opt tcb_ptr in_release_q \<equiv> \<lambda>s.
    case get_tcb tcb_ptr s of None \<Rightarrow> None | Some tcb \<Rightarrow>
      (case tcb_sched_context tcb of None => Some False
       | Some sc_ptr =>
           Some (runnable (tcb_state tcb) \<and> (test_sc_refill_max sc_ptr s)
           \<and> \<not>in_release_q))"

definition reschedule_required :: "unit det_ext_monad" where
  "reschedule_required \<equiv> do
     action \<leftarrow> gets scheduler_action;
     case action of
       switch_thread t \<Rightarrow> do
         in_release_q \<leftarrow> gets $ in_release_queue t;
         sched \<leftarrow> is_schedulable t in_release_q;
         when sched $ tcb_sched_action (tcb_sched_enqueue) t
       od
     | _ \<Rightarrow> return ();
     set_scheduler_action choose_new_thread
   od"

definition
  schedule_tcb :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "schedule_tcb tcb_ptr \<equiv> do
    cur \<leftarrow> gets cur_thread;
    sched_act \<leftarrow> gets scheduler_action;
    in_release_q \<leftarrow> gets $ in_release_queue tcb_ptr;
    schedulable \<leftarrow> is_schedulable tcb_ptr in_release_q;
    when (tcb_ptr = cur \<and> sched_act = resume_cur_thread \<and> \<not>schedulable) $ reschedule_required
  od"

definition
  set_thread_state_ext :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "set_thread_state_ext tcb_ptr \<equiv> do
    cur \<leftarrow> gets cur_thread;
    sched_act \<leftarrow> gets scheduler_action;
    in_release_q \<leftarrow> gets $ in_release_queue tcb_ptr;
    schedulable \<leftarrow> is_schedulable tcb_ptr in_release_q;
    when (tcb_ptr = cur \<and> sched_act = resume_cur_thread \<and> \<not>schedulable) $ set_scheduler_action choose_new_thread
  od"




(***)

definition
  set_thread_state :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_thread_state ref ts \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb ref;
     set_object ref (TCB (tcb \<lparr> tcb_state := ts \<rparr>));
     do_extended_op (set_thread_state_ext ref)
   od"

definition
  set_mcpriority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad"  where
  "set_mcpriority ref mcp \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_mcpriority:=mcp\<rparr>) ref "

section {* Synchronous and Asyncronous Endpoints *}

section "simple kernel objects"
(* to be used for abstraction unifying kernel objects other than TCB and CNode *)

definition
  partial_inv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a option)"
where
  "partial_inv f x = (if \<exists>!y. f y = x then Some (THE y. f y = x) else None)"

lemma proj_inj: "inj f \<Longrightarrow> (partial_inv f ko = Some v) = (f v = ko)"
  by (auto simp: partial_inv_def the_equality injD)

lemma inj_Endpoint: "inj Endpoint" by (auto intro: injI)
lemma inj_Notification: "inj Notification"  by (auto intro: injI)

lemmas proj_inj_ep[simp] = proj_inj[OF inj_Endpoint]
lemma proj_ko_type_ep[simp]: "(\<exists>v. partial_inv Endpoint  ko = Some (v::endpoint)) = (a_type ko = AEndpoint)"
  by (cases ko; auto simp: partial_inv_def a_type_def)

lemmas proj_inj_ntfn[simp] = proj_inj[OF inj_Notification]
lemma proj_ko_type_ntfn[simp]:
  "(\<exists>v. partial_inv Notification  ko = Some (v::notification)) = (a_type ko = ANTFN)"
  by (cases ko; auto simp: partial_inv_def a_type_def)


abbreviation
  "is_simple_type \<equiv> (\<lambda>ob. a_type ob \<in> {AEndpoint, ANTFN})"


definition
  get_simple_ko :: "('a \<Rightarrow> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "get_simple_ko f ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (is_simple_type kobj);
     (case partial_inv f kobj of Some e \<Rightarrow> return e | _ \<Rightarrow> fail)
   od"


definition
  set_simple_ko :: "('a \<Rightarrow> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> 'a \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_simple_ko f ptr ep \<equiv> do
     obj \<leftarrow> get_object ptr;
     assert (is_simple_type obj);
     assert (case partial_inv f obj of Some e \<Rightarrow> a_type obj = a_type (f ep) | _ \<Rightarrow> False);
     set_object ptr (f ep)
   od"

section {* Reply Objects *}

definition
  get_reply :: "obj_ref \<Rightarrow> (reply, 'z::state_ext) s_monad"
where
  "get_reply ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of Reply r \<Rightarrow> return r
                 | _ \<Rightarrow> fail)
   od"
  
definition
  set_reply :: "obj_ref \<Rightarrow> reply \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_reply ptr r \<equiv> do
     obj \<leftarrow> get_object ptr;
     assert (case obj of Reply _ \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (Reply r)
   od"

abbreviation
  "get_reply_tcb r \<equiv> liftM reply_tcb (get_reply r)"
(*
abbreviation
  "get_reply_caller r \<equiv> liftM reply_caller (get_reply r)"

abbreviation
  ntfn_set_bound_tcb :: "notification \<Rightarrow> obj_ref option \<Rightarrow> notification" where
  "ntfn_set_bound_tcb ntfn t \<equiv> ntfn \<lparr> ntfn_bound_tcb := t \<rparr>"

abbreviation
  ntfn_set_obj :: "notification \<Rightarrow> ntfn \<Rightarrow> notification" where
  "ntfn_set_obj ntfn a \<equiv> ntfn \<lparr> ntfn_obj := a \<rparr>"



section {* Synchronous and Asyncronous Endpoints *}


abbreviation
  get_endpoint :: "obj_ref \<Rightarrow> (endpoint,'z::state_ext) s_monad" where
  "get_endpoint \<equiv> get_simple_ko Endpoint"

abbreviation
  set_endpoint :: "obj_ref \<Rightarrow> endpoint \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_endpoint \<equiv> set_simple_ko Endpoint"

abbreviation
  get_notification :: "obj_ref \<Rightarrow> (notification,'z::state_ext) s_monad" where
  "get_notification \<equiv> get_simple_ko Notification"

abbreviation
  set_notification :: "obj_ref \<Rightarrow> notification \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_notification \<equiv> set_simple_ko Notification"


section {* IRQ State and Slot *}

definition
  get_irq_state :: "irq \<Rightarrow> (irq_state,'z::state_ext) s_monad" where
 "get_irq_state irq \<equiv> gets (\<lambda>s. interrupt_states s irq)"

definition
  set_irq_state :: "irq_state \<Rightarrow> irq \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "set_irq_state state irq \<equiv> do
    modify (\<lambda>s. s \<lparr> interrupt_states := (interrupt_states s) (irq := state)\<rparr>);
    do_machine_op $ maskInterrupt (state = IRQInactive) irq
  od"

definition
  get_irq_slot :: "irq \<Rightarrow> (cslot_ptr,'z::state_ext) s_monad" where
 "get_irq_slot irq \<equiv> gets (\<lambda>st. (interrupt_irq_node st irq, []))"


text{* obj\_ref field accessor for notification, sched\_context, and reply *}


definition
  get_sk_obj_ref :: "('a \<Rightarrow> kernel_object) \<Rightarrow> ('a => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_sk_obj_ref C f ref \<equiv> do
     sc \<leftarrow> get_simple_ko C ref;
     return $ f sc
   od"

definition
  update_sk_obj_ref :: "('a \<Rightarrow> kernel_object) \<Rightarrow> ((obj_ref option \<Rightarrow> obj_ref option) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "update_sk_obj_ref C f ref new \<equiv> do
     sc \<leftarrow> get_simple_ko C ref;
     set_simple_ko C ref (f (K new) sc)
   od"

abbreviation
  get_reply_obj_ref :: "(reply => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_reply_obj_ref update ref \<equiv> get_sk_obj_ref Reply update ref"

abbreviation
  set_reply_obj_ref :: "((obj_ref option \<Rightarrow> obj_ref option) \<Rightarrow> reply \<Rightarrow> reply) \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_reply_obj_ref update ref new \<equiv> update_sk_obj_ref Reply update ref new"

abbreviation
  get_ntfn_obj_ref :: "(notification => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_ntfn_obj_ref update ref \<equiv> get_sk_obj_ref Notification update ref"

abbreviation
  set_ntfn_obj_ref :: "((obj_ref option \<Rightarrow> obj_ref option) \<Rightarrow> notification \<Rightarrow> notification) \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_ntfn_obj_ref update ref new \<equiv> update_sk_obj_ref Notification update ref new"

(****)

section "User Context"

text {*
  Changes user context of specified thread by running
  specified user monad.
*}
definition
  as_user :: "obj_ref \<Rightarrow> 'a user_monad \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "as_user tptr f \<equiv> do
    tcb \<leftarrow> gets_the $ get_tcb tptr;
    uc \<leftarrow> return $ arch_tcb_context_get (tcb_arch tcb);
    (a, uc') \<leftarrow> select_f $ f uc;
    new_tcb \<leftarrow> return $ tcb \<lparr> tcb_arch := arch_tcb_context_set uc' (tcb_arch tcb)\<rparr>;
    set_object tptr (TCB new_tcb);
    return a
  od"

text {* Raise an exception if a property does not hold. *}
definition
throw_on_false :: "'e \<Rightarrow> (bool,'z::state_ext) s_monad \<Rightarrow> ('e + unit,'z::state_ext) s_monad" where
"throw_on_false ex f \<equiv> doE v \<leftarrow> liftE f; unlessE v $ throwError ex odE"

end
