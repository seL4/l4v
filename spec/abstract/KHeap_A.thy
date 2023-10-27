(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Functions to access kernel memory.
*)

chapter \<open>Accessing the Kernel Heap\<close>

theory KHeap_A
imports Exceptions_A
begin

text \<open>This theory gives auxiliary getter and setter methods
for kernel objects.\<close>

section "General Object Access"

text \<open>The kernel reader option monad\<close>
type_synonym ('a,'z) r_monad = "('z state, 'a) lookup"

definition
  read_object :: "obj_ref \<Rightarrow> (kernel_object,'z::state_ext) r_monad"
where
  "read_object \<equiv> swp kheap"
(*  "read_object ptr s = kheap s ptr" *)

definition
  get_object :: "obj_ref \<Rightarrow> (kernel_object,'z::state_ext) s_monad"
where
  "get_object ptr \<equiv> gets_the $ read_object ptr"
(* this is equivalent to "get_object ptr \<equiv> gets_map kheap ptr" *)

definition
  set_object :: "obj_ref \<Rightarrow> kernel_object \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_object ptr obj \<equiv> do
     kobj <- get_object ptr;
     assert (a_type kobj = a_type obj);
     s \<leftarrow> get;
     put (s\<lparr>kheap := (kheap s)(ptr \<mapsto> obj)\<rparr>)
   od"


section "TCBs"

definition
  get_tcb :: "obj_ref \<Rightarrow> (tcb, 'z::state_ext ) r_monad"
where
  "get_tcb tcb_ref state \<equiv>
   case read_object tcb_ref state of
      None      \<Rightarrow> None
    | Some kobj \<Rightarrow> (case kobj of
        TCB tcb \<Rightarrow> Some tcb
      | _       \<Rightarrow> None)"

definition
  thread_read :: "(tcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) r_monad" where
  "thread_read f tptr \<equiv> oliftM f (get_tcb tptr)"

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
  read_thread_state :: "obj_ref \<Rightarrow> (thread_state,'z::state_ext) r_monad"
where
  "read_thread_state ref \<equiv> thread_read tcb_state ref"

definition
  get_thread_state :: "obj_ref \<Rightarrow> (thread_state,'z::state_ext) s_monad"
where
  "get_thread_state ref \<equiv> thread_get tcb_state ref"

definition
  read_tcb_obj_ref :: "(tcb => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) r_monad"
where
  "read_tcb_obj_ref f ref \<equiv> thread_read f ref"

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

section "simple kernel objects"
(* to be used for abstraction unifying kernel objects other than TCB and CNode *)

lemma inj_Endpoint: "inj Endpoint" by (auto intro: injI)
lemma inj_Notification: "inj Notification"  by (auto intro: injI)

lemmas proj_inj_ep[simp] = proj_inj[OF inj_Endpoint]
lemma proj_ko_type_ep[simp]: "(\<exists>v. partial_inv Endpoint  ko = Some (v::endpoint)) = (a_type ko = AEndpoint)"
  by (cases ko; auto simp: partial_inv_def a_type_def)

lemmas proj_inj_ntfn[simp] = proj_inj[OF inj_Notification]
lemma proj_ko_type_ntfn[simp]:
  "(\<exists>v. partial_inv Notification  ko = Some (v::notification)) = (a_type ko = ANTFN)"
  by (cases ko; auto simp: partial_inv_def a_type_def)

lemma proj_inj_reply[simp]: "(partial_inv Reply ko = Some v) = (Reply v = ko)"
  by (auto simp: partial_inv_def)
lemma proj_ko_type_reply[simp]: "(\<exists>v. partial_inv Reply  ko = Some (v::reply)) = (a_type ko = AReply)"
  by (cases ko; auto simp: partial_inv_def a_type_def)

abbreviation
  "is_simple_type \<equiv> (\<lambda>ob. a_type ob \<in> {AEndpoint, ANTFN, AReply})"

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
     assert (partial_inv f obj \<noteq> None);
     set_object ptr (f ep)
   od"


section \<open>Synchronous and Asyncronous Endpoints\<close>


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

abbreviation
  ntfn_set_bound_tcb :: "notification \<Rightarrow> obj_ref option \<Rightarrow> notification" where
  "ntfn_set_bound_tcb ntfn t \<equiv> ntfn \<lparr> ntfn_bound_tcb := t \<rparr>"

abbreviation
  ntfn_set_obj :: "notification \<Rightarrow> ntfn \<Rightarrow> notification" where
  "ntfn_set_obj ntfn a \<equiv> ntfn \<lparr> ntfn_obj := a \<rparr>"


section \<open>IRQ State and Slot\<close>

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

section \<open>Reply Objects\<close>

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

section \<open>Scheduling Contexts\<close>

definition
  read_sched_context :: "obj_ref \<Rightarrow> (sched_context,'z::state_ext) r_monad"
where
  "read_sched_context ptr \<equiv> do {
     kobj \<leftarrow> read_object ptr;
     case kobj of SchedContext sc n \<Rightarrow> oreturn sc
                 | _ \<Rightarrow> ofail
   }"

definition
  get_sched_context :: "obj_ref \<Rightarrow> (sched_context,'z::state_ext) s_monad"
where
  "get_sched_context ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     case kobj of SchedContext sc n \<Rightarrow> return sc
                 | _ \<Rightarrow> fail
   od"

definition
  read_sc_obj_ref :: "(sched_context => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) r_monad"
where
  "read_sc_obj_ref f ref \<equiv> oliftM f (read_sched_context ref)"

definition
  get_sc_obj_ref :: "(sched_context => obj_ref option) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_sc_obj_ref f ref \<equiv> do
     sc \<leftarrow> get_sched_context ref;
     return $ f sc
   od"

definition (* update only the schedcontext in place, keeping the size *)
  update_sched_context :: "obj_ref \<Rightarrow> (sched_context \<Rightarrow> sched_context) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "update_sched_context ptr f  \<equiv> do
     obj \<leftarrow> get_object ptr;
     case obj of SchedContext sc n \<Rightarrow> set_object ptr (SchedContext (f sc) n) | _ \<Rightarrow> fail
   od"

abbreviation
  set_sc_obj_ref :: "(('a \<Rightarrow> 'a) \<Rightarrow> sched_context \<Rightarrow> sched_context) \<Rightarrow> obj_ref \<Rightarrow> 'a \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_sc_obj_ref f ref new \<equiv> update_sched_context ref (f (\<lambda>_. new))"

definition
  active_sc :: "nat \<Rightarrow> bool"
where
  "active_sc refill_max \<equiv> 0 < refill_max"

abbreviation
  sc_active :: "sched_context \<Rightarrow> bool"
where
  "sc_active sc \<equiv> active_sc (sc_refill_max sc)"

definition
  get_sc_active :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "get_sc_active sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    return $ sc_active sc
  od"

definition
  in_release_queue :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "in_release_queue tcb_ptr \<equiv> \<lambda>s. tcb_ptr \<in> set (release_queue s)"

definition
  is_schedulable :: "obj_ref \<Rightarrow> ('z::state_ext state, bool) nondet_monad"
where
  "is_schedulable tcb_ptr \<equiv> do
    tcb \<leftarrow> gets_the $ get_tcb tcb_ptr;
    if Option.is_none (tcb_sched_context tcb)
    then return False
    else do
      sc \<leftarrow> get_sched_context $ the $ tcb_sched_context tcb;
      is_runnable \<leftarrow> return (runnable (tcb_state tcb));
      in_release_q \<leftarrow> gets $ in_release_queue tcb_ptr;
      return (is_runnable \<and> sc_active sc \<and> \<not>in_release_q)
    od
  od"

definition
  is_sc_active :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "is_sc_active sp \<equiv> (\<lambda>s.
     case kheap s sp of
       Some (SchedContext sc _) \<Rightarrow> sc_active sc
     | _ \<Rightarrow> False)"

definition
  is_schedulable_opt :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool option"
where
  "is_schedulable_opt tcb_ptr \<equiv> \<lambda>s.
     case get_tcb tcb_ptr s of None \<Rightarrow> None
     | Some tcb \<Rightarrow>
       (case tcb_sched_context tcb of None => Some False
        | Some sc_ptr =>
            Some (runnable (tcb_state tcb) \<and> (is_sc_active sc_ptr s)
            \<and> \<not>(in_release_queue tcb_ptr s)))"

definition
  schedulable :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "schedulable tcb_ptr \<equiv> \<lambda>s.
     case get_tcb tcb_ptr s of None \<Rightarrow> False
     | Some tcb \<Rightarrow>
       (case tcb_sched_context tcb of None => False
        | Some sc_ptr =>
            (runnable (tcb_state tcb) \<and> (is_sc_active sc_ptr s)
              \<and> \<not>(in_release_queue tcb_ptr s)))"

abbreviation ct_schedulable where
  "ct_schedulable s \<equiv> schedulable (cur_thread s) s"

(* refill checks *)

abbreviation
  "refill_hd sc \<equiv> hd (sc_refills sc)"

abbreviation
  "refill_tl sc \<equiv> last (sc_refills sc)" (** condition? **)

definition
  get_refills :: "obj_ref \<Rightarrow> (refill list, 'z::state_ext) s_monad"
where
  "get_refills sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    return $ sc_refills sc
  od"

definition read_refill_head :: "obj_ref \<Rightarrow> (refill, 'z::state_ext) r_monad" where
  "read_refill_head sc_ptr \<equiv> do {
     sc \<leftarrow> read_sched_context sc_ptr;
     oreturn (refill_hd sc)
   }"

definition get_refill_head :: "obj_ref \<Rightarrow> (refill, 'z::state_ext) s_monad" where
  "get_refill_head sc_ptr \<equiv> gets_the (read_refill_head sc_ptr)"

definition
  refill_capacity :: "time \<Rightarrow> refill \<Rightarrow> time"
where
  "refill_capacity usage refill \<equiv>
    if r_amount refill < usage then 0 else r_amount refill - usage"

definition read_sc_refill_capacity :: "obj_ref \<Rightarrow> ticks \<Rightarrow> (ticks, 'z::state_ext) r_monad" where
  "read_sc_refill_capacity sc_ptr usage \<equiv> do {
     refill_head \<leftarrow> read_refill_head sc_ptr;
     oreturn (refill_capacity usage refill_head)
   }"

definition get_sc_refill_capacity :: "obj_ref \<Rightarrow> ticks \<Rightarrow> (ticks, 'z::state_ext) s_monad" where
  "get_sc_refill_capacity sc_ptr usage \<equiv> gets_the (read_sc_refill_capacity sc_ptr usage)"

definition refill_sufficient :: "time \<Rightarrow> refill \<Rightarrow> bool" where
  "refill_sufficient usage refill \<equiv> (MIN_BUDGET \<le> refill_capacity usage refill)"

definition read_sc_refill_sufficient :: "obj_ref \<Rightarrow> ticks \<Rightarrow> (bool, 'z::state_ext) r_monad" where
  "read_sc_refill_sufficient sc_ptr usage \<equiv> do {
     head \<leftarrow> read_refill_head sc_ptr;
     oreturn (refill_sufficient usage head)
   }"

definition get_sc_refill_sufficient :: "obj_ref \<Rightarrow> ticks \<Rightarrow> (bool, 'z::state_ext) s_monad" where
  "get_sc_refill_sufficient sc_ptr usage \<equiv> gets_the (read_sc_refill_sufficient sc_ptr usage)"

definition refill_ready' :: "time \<Rightarrow> time \<Rightarrow> refill \<Rightarrow> bool" where
  "refill_ready' usage curtime refill \<equiv>
    r_time refill + usage \<le> curtime + kernelWCET_ticks"

abbreviation refill_ready :: "time \<Rightarrow> refill \<Rightarrow> bool" where
  "refill_ready \<equiv> refill_ready' 0"

lemmas refill_ready_def = refill_ready'_def

definition read_sc_refill_ready :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) r_monad" where
  "read_sc_refill_ready sc_ptr = do {
     refill_head \<leftarrow> read_refill_head sc_ptr;
     cur_time \<leftarrow> asks cur_time;
     oreturn $ refill_ready cur_time refill_head
   }"

definition get_sc_refill_ready :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad" where
  "get_sc_refill_ready sc_ptr \<equiv> gets_the $ read_sc_refill_ready sc_ptr"

(* end refill checks *)

definition sc_released :: "time \<Rightarrow> sched_context \<Rightarrow> bool" where
  "sc_released curtime sc \<equiv> sc_active sc \<and> refill_ready curtime (refill_hd sc)"

definition read_sc_released :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) r_monad" where
  "read_sc_released sc_ptr = do {
     sc \<leftarrow> read_sched_context sc_ptr;
     cur_time \<leftarrow> asks cur_time;
     oreturn $ sc_released cur_time sc
   }"

definition get_sc_released :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad" where
  "get_sc_released sc_ptr \<equiv> gets_the $ read_sc_released sc_ptr"

definition
  get_tcb_queue :: "domain \<Rightarrow> priority \<Rightarrow> (ready_queue, 'z::state_ext) s_monad" where
  "get_tcb_queue d prio \<equiv> do
     queues \<leftarrow> gets ready_queues;
     return (queues d prio)
   od"

definition
  set_tcb_queue :: "domain \<Rightarrow> priority \<Rightarrow> ready_queue \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "set_tcb_queue d prio queue \<equiv>
     modify (\<lambda>es. es\<lparr> ready_queues :=
      (\<lambda>d' p. if d' = d \<and> p = prio then queue else ready_queues es d' p)\<rparr>)"

definition
  tcb_sched_action :: "(obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list) \<Rightarrow> obj_ref
                        \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "tcb_sched_action action thread \<equiv> do
     d \<leftarrow> thread_get tcb_domain thread;
     prio \<leftarrow> thread_get tcb_priority thread;
     queue \<leftarrow> get_tcb_queue d prio;
     set_tcb_queue d prio (action thread queue)
   od"

definition
  is_blocked :: "obj_ref \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "is_blocked thread = (liftM ipc_queued_thread_state $ get_thread_state thread)"

definition
  tcb_sched_enqueue :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_enqueue thread queue \<equiv> if thread \<notin> set queue then thread # queue else queue"

definition
  tcb_sched_append :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_append thread queue \<equiv> if thread \<notin> set queue then queue @ [thread] else queue"

definition
  tcb_sched_dequeue :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_dequeue thread queue \<equiv> filter ((\<noteq>) thread) queue"

definition
  tcb_release_remove :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "tcb_release_remove tcb_ptr \<equiv> do
     qs \<leftarrow> gets release_queue;
     when (qs \<noteq> [] \<and> hd qs = tcb_ptr) $
         modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>);
     modify (\<lambda>s. s\<lparr>release_queue := tcb_sched_dequeue tcb_ptr qs\<rparr>)
  od"

definition
  set_scheduler_action :: "scheduler_action \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "set_scheduler_action action \<equiv>
     modify (\<lambda>es. es\<lparr>scheduler_action := action\<rparr>)"

definition
  thread_set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "thread_set_priority tptr prio \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_priority := prio\<rparr>) tptr"

definition
  thread_set_domain :: "obj_ref \<Rightarrow> domain \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "thread_set_domain tptr domain \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_domain := domain\<rparr>) tptr"


definition reschedule_required :: "(unit, 'z::state_ext) s_monad" where
  "reschedule_required \<equiv> do
     action \<leftarrow> gets scheduler_action;
     case action of
       switch_thread t \<Rightarrow> do
         sched \<leftarrow> is_schedulable t;
         when sched $ do
           sc_opt \<leftarrow> thread_get tcb_sched_context t;
           scp \<leftarrow> assert_opt sc_opt;
           sufficient \<leftarrow> get_sc_refill_sufficient scp 0;
           ready \<leftarrow> get_sc_refill_ready scp;
           assert (sufficient & ready);
           tcb_sched_action (tcb_sched_enqueue) t
         od
       od
     | _ \<Rightarrow> return ();
     set_scheduler_action choose_new_thread
   od"

definition
  schedule_tcb :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "schedule_tcb tcb_ptr \<equiv> do
    cur \<leftarrow> gets cur_thread;
    sched_act \<leftarrow> gets scheduler_action;
    schedulable \<leftarrow> is_schedulable tcb_ptr;
    when (tcb_ptr = cur \<and> sched_act = resume_cur_thread \<and> \<not>schedulable) $ reschedule_required
  od"

definition
  set_thread_state_act :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_thread_state_act tcb_ptr \<equiv> do
    cur \<leftarrow> gets cur_thread;
    sched_act \<leftarrow> gets scheduler_action;
    schedulable \<leftarrow> is_schedulable tcb_ptr;
    when (tcb_ptr = cur \<and> sched_act = resume_cur_thread \<and> \<not>schedulable) $ set_scheduler_action choose_new_thread
  od"


(***)

definition
  set_thread_state :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_thread_state ref ts \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb ref;
     set_object ref (TCB (tcb \<lparr> tcb_state := ts \<rparr>));
     set_thread_state_act ref
   od"

definition
  set_mcpriority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad"  where
  "set_mcpriority ref mcp \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_mcpriority:=mcp\<rparr>) ref "


text\<open>obj\_ref field accessor for notification, sched\_context, and reply\<close>


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

text \<open>Tests whether an IRQ identifier is in use.\<close>
definition
  is_irq_active :: "irq \<Rightarrow> (bool,'z::state_ext) s_monad" where
 "is_irq_active irq \<equiv> liftM (\<lambda>st. st \<noteq> IRQInactive) $ get_irq_state irq"

section "User Context"

text \<open>
  Changes user context of specified thread by running
  specified user monad.
\<close>
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

text \<open>Raise an exception if a property does not hold.\<close>
definition
throw_on_false :: "'e \<Rightarrow> (bool,'z::state_ext) s_monad \<Rightarrow> ('e + unit,'z::state_ext) s_monad" where
"throw_on_false ex f \<equiv> doE v \<leftarrow> liftE f; unlessE v $ throwError ex odE"

text \<open>Allow preemption at this point.\<close>

definition
  is_cur_domain_expired :: "'z::state_ext state \<Rightarrow> bool"
where
  "is_cur_domain_expired = (\<lambda>s. numDomains > 1 \<and> domain_time s = 0)"

text \<open>Update current and consumed time.\<close>
definition
  update_time_stamp :: "(unit, 'z::state_ext) s_monad"
where
  "update_time_stamp = do
     previous_time \<leftarrow> gets cur_time;
     current_time \<leftarrow> do_machine_op getCurrentTime;
     consumed \<leftarrow> return (current_time - previous_time);
     modify (\<lambda>s. s\<lparr> cur_time := current_time \<rparr>);
     modify (\<lambda>s. s\<lparr> consumed_time := consumed_time s + consumed \<rparr>);
     domain_time \<leftarrow> gets domain_time;
     when (numDomains > 1) $ if consumed + MIN_BUDGET \<ge> domain_time
                             then modify (\<lambda>s. s\<lparr> domain_time := 0 \<rparr>)
                             else modify (\<lambda>s. s\<lparr> domain_time := domain_time - consumed \<rparr>)
  od"

definition
  preemption_point :: "(unit,'z::state_ext) p_monad"
where
  "preemption_point \<equiv> doE
     liftE $ do_extended_op update_work_units;
     OR_choiceE work_units_limit_reached
     (doE liftE $ do_extended_op reset_work_units;
          liftE $ update_time_stamp;
          irq_opt \<leftarrow> liftE $ do_machine_op (getActiveIRQ True);
          cur_sc \<leftarrow> liftE $ gets cur_sc;
          consumed \<leftarrow> liftE $ gets consumed_time;
          test \<leftarrow> liftE $ andM (get_sc_active cur_sc)
                               (get_sc_refill_sufficient cur_sc consumed);
          exp \<leftarrow> liftE $ gets is_cur_domain_expired;
          whenE (\<not>test \<or> exp \<or> irq_opt \<noteq> None) $ throwError ()
      odE)
     (returnOk ())
   odE"

end
