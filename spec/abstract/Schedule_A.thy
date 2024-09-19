(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Scheduler"

theory Schedule_A
imports Arch_A
begin

arch_requalify_consts (A)
  arch_switch_to_thread
  arch_switch_to_idle_thread
  arch_prepare_next_domain

abbreviation
  "idle st \<equiv> st = Structures_A.IdleThreadState"

text \<open>Switches the current thread to the specified one.\<close>
definition
  switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "switch_to_thread t \<equiv> do
     state \<leftarrow> get;
     assert (get_tcb t state \<noteq> None);
     arch_switch_to_thread t;
     tcb_sched_action (tcb_sched_dequeue) t;
     modify (\<lambda>s. s \<lparr> cur_thread := t \<rparr>)
   od"

text \<open>Asserts that a thread is runnable before switching to it.\<close>
definition guarded_switch_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "guarded_switch_to thread \<equiv> do
     ts \<leftarrow> get_thread_state thread;
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

definition
  next_domain :: "(unit, 'z::state_ext) s_monad" where
  "next_domain \<equiv> do
    modify (\<lambda>s.
      let domain_index' = (domain_index s + 1) mod length (domain_list s) in
      let next_dom = (domain_list s)!domain_index'
      in s\<lparr> domain_index := domain_index',
            cur_domain := fst next_dom,
            domain_time := snd next_dom\<rparr>);
    do_extended_op $ modify (\<lambda>s. s \<lparr>work_units_completed := 0\<rparr>)
  od"

definition
  dec_domain_time :: "(unit, 'z::state_ext) s_monad" where
  "dec_domain_time = modify (\<lambda>s. s\<lparr>domain_time := domain_time s - 1\<rparr>)"

definition max_non_empty_queue :: "(priority \<Rightarrow> ready_queue) \<Rightarrow> ready_queue" where
  "max_non_empty_queue queues \<equiv> queues (Max {prio. queues prio \<noteq> []})"

definition choose_thread :: "(unit, 'z::state_ext) s_monad" where
  "choose_thread \<equiv> do
     d \<leftarrow> gets cur_domain;
     queues \<leftarrow> gets (\<lambda>s. ready_queues s d);
     if \<forall>prio. queues prio = []
     then switch_to_idle_thread
     else guarded_switch_to (hd (max_non_empty_queue queues))
   od"

text \<open>
  Determine whether given priority is highest among queued ready threads in given domain.
  Trivially true if no threads are ready.\<close>
definition
  is_highest_prio :: "domain \<Rightarrow> priority \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "is_highest_prio d p s \<equiv>
    (\<forall>prio. ready_queues s d prio = [])
    \<or> p \<ge> Max {prio. ready_queues s d prio \<noteq> []}"

definition
  "schedule_switch_thread_fastfail ct it ct_prio target_prio \<equiv>
     return $ ct \<noteq> it \<longrightarrow> target_prio < ct_prio"

definition
  "schedule_choose_new_thread \<equiv> do
     dom_time \<leftarrow> gets domain_time;
     when (dom_time = 0) $ do
       arch_prepare_next_domain;
       next_domain
     od;
     choose_thread;
     set_scheduler_action resume_cur_thread
   od"

definition
  "schedule \<equiv> do
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
           target_prio \<leftarrow> thread_get tcb_priority candidate;

           \<comment> \<open>Infoflow does not like asking about the idle thread's priority or domain.\<close>
           ct_prio \<leftarrow> if ct \<noteq> it then thread_get tcb_priority ct else return 0;
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

end
