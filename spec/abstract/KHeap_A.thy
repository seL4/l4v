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
     kobj \<leftarrow> get_object ptr;
     assert (a_type kobj = a_type obj);
     s \<leftarrow> get;
     put (s\<lparr>kheap := (kheap s)(ptr \<mapsto> obj)\<rparr>)
   od"


section "TCBs"

definition
  get_tcb :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> tcb option"
where
  "get_tcb tcb_ref state \<equiv>
   case kheap state tcb_ref of
      None      \<Rightarrow> None
    | Some kobj \<Rightarrow> (case kobj of
        TCB tcb \<Rightarrow> Some tcb
      | _       \<Rightarrow> None)"

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
  get_bound_notification :: "obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_bound_notification ref \<equiv> thread_get tcb_bound_notification ref"

definition
  set_bound_notification :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_bound_notification ref ntfn \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb ref;
     set_object ref (TCB (tcb \<lparr> tcb_bound_notification := ntfn \<rparr>))
   od"


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

section "getters/setters for simple kernel objects"
(* to be used for abstraction unifying kernel objects other than TCB and CNode*)

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

text \<open>Tests whether an IRQ identifier is in use.\<close>
definition
  is_irq_active :: "irq \<Rightarrow> (bool,'z::state_ext) s_monad" where
 "is_irq_active irq \<equiv> liftM (\<lambda>st. st \<noteq> IRQInactive) $ get_irq_state irq"


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
  tcb_sched_enqueue :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_enqueue thread queue \<equiv> if thread \<notin> set queue then thread # queue else queue"

definition
  tcb_sched_append :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_append thread queue \<equiv> if thread \<notin> set queue then queue @ [thread] else queue"

definition
  tcb_sched_dequeue :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref list" where
  "tcb_sched_dequeue thread queue \<equiv> filter ((\<noteq>) thread) queue"

definition
  set_scheduler_action :: "scheduler_action \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "set_scheduler_action action \<equiv>
     modify (\<lambda>es. es\<lparr>scheduler_action := action\<rparr>)"

definition
  thread_set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "thread_set_priority tptr prio \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_priority := prio\<rparr>) tptr"

definition
  thread_set_time_slice :: "obj_ref \<Rightarrow> nat \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "thread_set_time_slice tptr time \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_time_slice := time\<rparr>) tptr"

definition
  thread_set_domain :: "obj_ref \<Rightarrow> domain \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "thread_set_domain tptr domain \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_domain := domain\<rparr>) tptr"

definition reschedule_required :: "(unit, 'z::state_ext) s_monad" where
  "reschedule_required \<equiv> do
     action \<leftarrow> gets scheduler_action;
     case action of
       switch_thread t \<Rightarrow> tcb_sched_action (tcb_sched_enqueue) t | _ \<Rightarrow> return ();
     set_scheduler_action choose_new_thread
   od"

definition
  possible_switch_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "possible_switch_to target \<equiv> do
     cur_dom \<leftarrow> gets cur_domain;
     target_dom \<leftarrow> thread_get tcb_domain target;
     action \<leftarrow> gets scheduler_action;

     if (target_dom \<noteq> cur_dom) then
       tcb_sched_action tcb_sched_enqueue target
     else if (action \<noteq> resume_cur_thread) then do
         reschedule_required;
         tcb_sched_action tcb_sched_enqueue target
       od
     else set_scheduler_action $ switch_thread target
   od"

definition
  set_thread_state_act :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_thread_state_act tcb_ptr \<equiv> do
    ts \<leftarrow> get_thread_state tcb_ptr;
    cur \<leftarrow> gets cur_thread;
    sched_act \<leftarrow> gets scheduler_action;
    when (tcb_ptr = cur \<and> sched_act = resume_cur_thread \<and> \<not> runnable ts) $ set_scheduler_action choose_new_thread
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
  set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_priority tptr prio \<equiv> do
     tcb_sched_action tcb_sched_dequeue tptr;
     thread_set_priority tptr prio;
     ts \<leftarrow> get_thread_state tptr;
     when (runnable ts) $ do
       cur \<leftarrow> gets cur_thread;
       if tptr = cur then reschedule_required else possible_switch_to tptr
     od
   od"

definition
  set_mcpriority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad"  where
  "set_mcpriority ref mcp \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_mcpriority:=mcp\<rparr>) ref "


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

end
