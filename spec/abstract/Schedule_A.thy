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
Non-deterministic scheduler functionality.
*)

chapter "Scheduler"

theory Schedule_A
imports "./$L4V_ARCH/Arch_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_switch_to_thread
  arch_switch_to_idle_thread

end

abbreviation
  "idle st \<equiv> st = Structures_A.IdleThreadState"

text {* Gets the TCB at an address if the thread can be scheduled. *}
definition
  getActiveTCB :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> tcb option"
where
  "getActiveTCB tcb_ref state \<equiv>
   case (get_tcb tcb_ref state)
     of None           \<Rightarrow> None
      | Some tcb       \<Rightarrow> if (runnable $ tcb_state tcb)
                         then Some tcb else None"

text {* Gets all schedulable threads in the system. *}
definition
  allActiveTCBs :: "(obj_ref set,'z::state_ext) s_monad" where
  "allActiveTCBs \<equiv> do
    state \<leftarrow> get;
    return {x. getActiveTCB x state \<noteq> None}
   od"

text {* Switches the current thread to the specified one. *}
definition
  switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "switch_to_thread t \<equiv> do
     state \<leftarrow> get;
     assert (get_tcb t state \<noteq> None);
     arch_switch_to_thread t;
     do_extended_op (tcb_sched_action (tcb_sched_dequeue) t);
     modify (\<lambda>s. s \<lparr> cur_thread := t \<rparr>)
   od"

text {* Asserts that a thread is runnable before switching to it. *}
definition guarded_switch_to :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"guarded_switch_to thread \<equiv> do ts \<leftarrow> get_thread_state thread;
                    assert (runnable ts);
                    switch_to_thread thread
                 od"

text {* Switches to the idle thread. *}
definition
  switch_to_idle_thread :: "(unit,'z::state_ext) s_monad" where
  "switch_to_idle_thread \<equiv> do
     thread \<leftarrow> gets idle_thread;
     arch_switch_to_idle_thread;
     modify (\<lambda>s. s \<lparr> cur_thread := thread \<rparr>)
   od"

class state_ext_sched = state_ext +
  fixes schedule :: "(unit,'a) s_monad"

definition choose_thread :: "det_ext state \<Rightarrow> (unit \<times> det_ext state) set \<times> bool" where
"choose_thread \<equiv>
      do
        d \<leftarrow> gets cur_domain;
        queues \<leftarrow> gets (\<lambda>s. ready_queues s d);
        if (\<forall>prio. queues prio = []) then (switch_to_idle_thread)
        else (guarded_switch_to (hd (max_non_empty_queue queues)))
      od"


instantiation  det_ext_ext :: (type) state_ext_sched
begin

definition "schedule_det_ext_ext \<equiv> do
     cur \<leftarrow> gets cur_thread;
     cur_ts \<leftarrow> get_thread_state cur;
     action \<leftarrow> gets scheduler_action;
     (case action of
       resume_cur_thread \<Rightarrow> do
                            id \<leftarrow> gets idle_thread;
                            assert (runnable cur_ts \<or> cur = id);
                            return ()
                           od |
       choose_new_thread \<Rightarrow> do
         when (runnable cur_ts) ((tcb_sched_action tcb_sched_enqueue cur));
         dom_time \<leftarrow> gets domain_time;
         when (dom_time = 0) next_domain;
         choose_thread;
         (set_scheduler_action resume_cur_thread) od |
       switch_thread t \<Rightarrow> do
         when (runnable cur_ts) ((tcb_sched_action tcb_sched_enqueue cur));
         guarded_switch_to t;
         (set_scheduler_action resume_cur_thread) od)
    od"

instance ..
end


instantiation unit :: state_ext_sched
begin


text {*
  The scheduler is heavily underspecified.
  It is allowed to pick any active thread or the idle thread.
  If the thread the scheduler picked is the current thread, it
  may omit the call to @{const switch_to_thread}.
*}
definition schedule_unit :: "(unit,unit) s_monad" where
"schedule_unit \<equiv> do
   cur \<leftarrow> gets cur_thread;
   threads \<leftarrow> allActiveTCBs;
   thread \<leftarrow> select threads;
     if thread = cur then
     return () OR switch_to_thread thread
   else
     switch_to_thread thread
 od OR
 switch_to_idle_thread"

instance ..
end


lemmas schedule_def = schedule_det_ext_ext_def schedule_unit_def

end
