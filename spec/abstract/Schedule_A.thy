(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Non-deterministic scheduler functionality.
*)

chapter "Scheduler"

theory Schedule_A
imports Arch_A
begin

arch_requalify_consts (A)
  arch_switch_to_thread
  arch_switch_to_idle_thread

abbreviation
  "idle st \<equiv> st = Structures_A.IdleThreadState"

text \<open>Gets the TCB at an address if the thread can be scheduled.\<close>
definition
  getActiveTCB :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> tcb option"
where
  "getActiveTCB tcb_ref state \<equiv>
   case (get_tcb tcb_ref state)
     of None           \<Rightarrow> None
      | Some tcb       \<Rightarrow> if (runnable $ tcb_state tcb)
                         then Some tcb else None"

text \<open>Gets all schedulable threads in the system.\<close>
definition
  allActiveTCBs :: "(obj_ref set,'z::state_ext) s_monad" where
  "allActiveTCBs \<equiv> do
    state \<leftarrow> get;
    return {x. getActiveTCB x state \<noteq> None}
   od"

text \<open>Switches the current thread to the specified one.\<close>
definition
  switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "switch_to_thread t \<equiv> do
     state \<leftarrow> get;
     assert (get_tcb t state \<noteq> None);
     arch_switch_to_thread t;
     do_extended_op (tcb_sched_action (tcb_sched_dequeue) t);
     modify (\<lambda>s. s \<lparr> cur_thread := t \<rparr>)
   od"

text \<open>Asserts that a thread is runnable before switching to it.\<close>
definition guarded_switch_to :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"guarded_switch_to thread \<equiv> do ts \<leftarrow> get_thread_state thread;
                    assert (runnable ts);
                    switch_to_thread thread
                 od"

text \<open>Switches to the idle thread.\<close>
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

text \<open>
  Determine whether given priority is highest among queued ready threads in given domain.
  Trivially true if no threads are ready.\<close>
definition
  is_highest_prio :: "domain \<Rightarrow> priority \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "is_highest_prio d p s \<equiv>
    (\<forall>prio. ready_queues s d prio = [])
    \<or> p \<ge> Max {prio. ready_queues s d prio \<noteq> []}"

instantiation  det_ext_ext :: (type) state_ext_sched
begin

definition
  "schedule_switch_thread_fastfail ct it ct_prio target_prio \<equiv>
     if ct \<noteq> it
     then return (target_prio < ct_prio)
     else return True"

definition
  "schedule_choose_new_thread \<equiv> do
     dom_time \<leftarrow> gets domain_time;
     when (dom_time = 0) next_domain;
     choose_thread;
     set_scheduler_action resume_cur_thread
   od"

definition
  "schedule_det_ext_ext \<equiv> do
     ct \<leftarrow> gets cur_thread;
     ct_st \<leftarrow> get_thread_state ct;
     ct_runnable \<leftarrow> return $ runnable ct_st;
     action \<leftarrow> gets scheduler_action;
     (case action
       of resume_cur_thread \<Rightarrow> do
            id \<leftarrow> gets idle_thread;
            assert (ct_runnable \<or> ct = id);
            return ()
         od
       | choose_new_thread \<Rightarrow> do
           when ct_runnable (tcb_sched_action tcb_sched_enqueue ct);
           schedule_choose_new_thread
         od
       | switch_thread candidate \<Rightarrow> do
           when ct_runnable (tcb_sched_action tcb_sched_enqueue ct);

           it \<leftarrow> gets idle_thread;
           target_prio \<leftarrow> ethread_get tcb_priority candidate;

           \<comment> \<open>Infoflow does not like asking about the idle thread's priority or domain.\<close>
           ct_prio \<leftarrow> ethread_get_when (ct \<noteq> it) tcb_priority ct;
           \<comment> \<open>When to look at the bitmaps. This optimisation is used in the C fast path,
              but there we know @{text cur_thread} is not idle.\<close>
           fastfail \<leftarrow> schedule_switch_thread_fastfail ct it ct_prio target_prio;

           cur_dom \<leftarrow> gets cur_domain;
           highest \<leftarrow> gets (is_highest_prio cur_dom target_prio);
           if (fastfail \<and> \<not>highest)
           then do
               \<comment> \<open>Candidate is not best candidate, choose a new thread\<close>
               tcb_sched_action tcb_sched_enqueue candidate;
               set_scheduler_action choose_new_thread;
               schedule_choose_new_thread
             od
           else if (ct_runnable \<and> ct_prio = target_prio)
           then do
               \<comment> \<open>Current thread was runnable and candidate is not strictly better
                  want current thread to run next, so append the candidate to end of queue
                  and choose again\<close>
               tcb_sched_action tcb_sched_append candidate;
               set_scheduler_action choose_new_thread;
               schedule_choose_new_thread
             od
           else do
             guarded_switch_to candidate;
             \<comment> \<open>Duplication assists in wp proof under different scheduler actions\<close>
             set_scheduler_action resume_cur_thread
           od
        od)
    od"

instance ..
end


instantiation unit :: state_ext_sched
begin


text \<open>
  The scheduler is heavily underspecified.
  It is allowed to pick any active thread or the idle thread.
  If the thread the scheduler picked is the current thread, it
  may omit the call to @{const switch_to_thread}. Likewise it
  may omit the call to @{const switch_to_idle_thread} if the
  idle thread is the current thread.
\<close>
definition schedule_unit :: "(unit,unit) s_monad" where
"schedule_unit \<equiv> (do
   cur \<leftarrow> gets cur_thread;
   threads \<leftarrow> allActiveTCBs;
   thread \<leftarrow> select threads;
   (if thread = cur then
     return () \<sqinter> switch_to_thread thread
   else
     switch_to_thread thread)
 od) \<sqinter>
 (do
   cur \<leftarrow> gets cur_thread;
   idl \<leftarrow> gets idle_thread;
   if idl = cur then
     return () \<sqinter> switch_to_idle_thread
   else switch_to_idle_thread
  od)"

instance ..
end


lemmas schedule_def = schedule_det_ext_ext_def schedule_unit_def

end
