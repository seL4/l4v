(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
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

text \<open>Asserts that a thread is schedulable, ready and sufficient before switching to it.\<close>
definition guarded_switch_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "guarded_switch_to thread \<equiv> do
     sc_opt \<leftarrow> thread_get tcb_sched_context thread;
     scp \<leftarrow> assert_opt sc_opt;
     sched \<leftarrow> is_schedulable thread;
     assert sched;
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

definition "\<mu>s_to_ms = 1000"

definition
  next_domain :: "(unit, 'z::state_ext) s_monad" where
  "next_domain \<equiv> do
    modify (\<lambda>s.
      let domain_index' = (domain_index s + 1) mod length (domain_list s) in
      let next_dom = (domain_list s)!domain_index'
      in s\<lparr> domain_index := domain_index',
            cur_domain := fst next_dom,
            domain_time := us_to_ticks (snd next_dom * \<mu>s_to_ms),
            reprogram_timer := True\<rparr>);
    do_extended_op $ modify (\<lambda>s. s \<lparr>work_units_completed := 0\<rparr>)
  od"

definition
  dec_domain_time :: "(unit, 'z::state_ext) s_monad" where
  "dec_domain_time = modify (\<lambda>s. s\<lparr>domain_time := domain_time s - 1\<rparr>)"

definition
  set_next_interrupt :: "(unit, 'z::state_ext) s_monad"
where
  "set_next_interrupt = do
     cur_tm \<leftarrow> gets cur_time;
     cur_th \<leftarrow> gets cur_thread;
     sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context cur_th;
     sc_ptr \<leftarrow> assert_opt sc_opt;
     sc \<leftarrow> get_sched_context sc_ptr;
     next_interrupt \<leftarrow> return $ cur_tm + r_amount (refill_hd sc);
     next_interrupt \<leftarrow>
     if num_domains > 1 then do
       domain_tm \<leftarrow> gets domain_time;
       return $ min next_interrupt (cur_tm + domain_tm) od
     else
       return next_interrupt;
     rq \<leftarrow> gets release_queue;
     next_interrupt \<leftarrow> if rq = [] then return next_interrupt else do
       rqsc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context (hd rq);
       rqsc_ptr \<leftarrow> assert_opt rqsc_opt;
       rqsc \<leftarrow> get_sched_context rqsc_ptr;
       return $ min (r_time (refill_hd rqsc)) next_interrupt
     od;
     do_machine_op $ setDeadline (next_interrupt - timerPrecision)
  od"

definition
  switch_sched_context :: "(unit,'z::state_ext) s_monad"
where
  "switch_sched_context = do
    cur_sc \<leftarrow> gets cur_sc;
    cur_th \<leftarrow> gets cur_thread;
    sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context cur_th;
    scp \<leftarrow> assert_opt sc_opt;
    sc' \<leftarrow> get_sched_context cur_sc;

    when (scp \<noteq> cur_sc \<and> 0 < sc_refill_max sc') $ do
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>);
      if_constant_bandwidth_refill_unblock_check (Some scp)
     od;

    reprogram \<leftarrow> gets reprogram_timer;
    when reprogram $ commit_time;

    modify (\<lambda>s. s\<lparr> cur_sc:= scp \<rparr>)
  od"

definition
  sc_and_timer :: "(unit, 'z::state_ext) s_monad"
where
  "sc_and_timer = do
    switch_sched_context;
    reprogram \<leftarrow> gets reprogram_timer;
    when reprogram $ do
      set_next_interrupt;
      modify (\<lambda>s. s\<lparr>reprogram_timer:= False\<rparr>)
    od
  od"

definition
  read_tcb_refill_ready :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) r_monad"
where
  "read_tcb_refill_ready t = do {
     sc_opt \<leftarrow> read_tcb_obj_ref tcb_sched_context t;
     sc_ptr \<leftarrow> oassert_opt sc_opt;
     ready \<leftarrow> read_sc_refill_ready sc_ptr;
     oreturn ready
  }"

definition read_release_q_non_empty_and_ready :: "(bool, 'z::state_ext) r_monad"
where
  "read_release_q_non_empty_and_ready \<equiv> do {
     rq \<leftarrow> asks release_queue;
     if rq = []
     then oreturn False
     else read_tcb_refill_ready (hd rq)
   }"

definition tcb_release_dequeue :: "(obj_ref, 'z::state_ext) s_monad"
where
  "tcb_release_dequeue = do
     rq \<leftarrow> gets release_queue;
     tcb_release_remove (hd rq);
     return (hd rq)
   od"

definition awaken_body :: "(unit, 'z::state_ext) s_monad"
where
  "awaken_body = do
     awakened \<leftarrow> tcb_release_dequeue;
     possible_switch_to awakened
   od"

definition awaken :: "(unit, 'z::state_ext) s_monad"
where
  "awaken \<equiv> whileLoop (\<lambda>r s. the (read_release_q_non_empty_and_ready s)) (\<lambda>_. awaken_body) ()"

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
     when (dom_time = 0) next_domain;
     choose_thread;
     set_scheduler_action resume_cur_thread
   od"

definition
  "schedule \<equiv> do
     awaken;
     ct \<leftarrow> gets cur_thread;
     ct_schedulable \<leftarrow> is_schedulable ct;
     action \<leftarrow> gets scheduler_action;
     (case action
       of resume_cur_thread \<Rightarrow> return ()
       | choose_new_thread \<Rightarrow> do
           when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct); \<comment> \<open>schedulable\<close>
           schedule_choose_new_thread
         od
       | switch_thread candidate \<Rightarrow> do
           when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct); \<comment> \<open>schedulable\<close>

           it \<leftarrow> gets idle_thread;
           target_prio \<leftarrow> thread_get tcb_priority candidate;

           \<comment> \<open>Infoflow does not like asking about the idle thread's priority or domain.\<close>
           ct_prio \<leftarrow> if ct \<noteq> it then thread_get tcb_priority ct else return 0;
           \<comment> \<open>When to look at the bitmaps. This optimisation is used in the C fast path,
              but there we know @{text cur_thread} is not idle.\<close>
           fastfail \<leftarrow> schedule_switch_thread_fastfail ct it ct_prio target_prio;

           cur_dom \<leftarrow> gets cur_domain;
           highest \<leftarrow> gets (is_highest_prio cur_dom target_prio);
           if fastfail \<and> \<not>highest
           then do
               \<comment> \<open>Candidate is not best candidate, choose a new thread\<close>
               tcb_sched_action tcb_sched_enqueue candidate;
               set_scheduler_action choose_new_thread;
               schedule_choose_new_thread
             od
           else if ct_schedulable \<and> ct_prio = target_prio
           then do
               \<comment> \<open>Current thread was runnable and candidate is not strictly better
                  want current thread to run next, so append the candidate to end of queue
                  and choose again\<close>
               tcb_sched_action tcb_sched_append candidate;
               set_scheduler_action choose_new_thread;
               schedule_choose_new_thread
             od
           else do
             switch_to_thread candidate;
             \<comment> \<open>Duplication assists in wp proof under different scheduler actions\<close>
             set_scheduler_action resume_cur_thread
           od
        od);
     sc_and_timer
   od"


text \<open>Scheduling context invocation function\<close>

text \<open> User-level scheduling context invocations. \<close>

definition
  parse_time_arg :: "nat \<Rightarrow> data list \<Rightarrow> time"
where
  "parse_time_arg i args \<equiv> (ucast (args!(i+1)) << 32) + ucast (args!i)"

definition
  sched_context_yield_to :: "obj_ref \<Rightarrow> data option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_yield_to sc_ptr buffer \<equiv> do
    sc_yf_opt \<leftarrow> get_sc_obj_ref sc_yield_from sc_ptr;
    when (sc_yf_opt \<noteq> None) $ do
      complete_yield_to (the sc_yf_opt); \<comment> \<open>@{text \<open>sc_yield_from = None\<close>}\<close>
      sc_yf_opt \<leftarrow> get_sc_obj_ref sc_yield_from sc_ptr;
      assert (sc_yf_opt = None)
    od;

    sc_tcb_opt \<leftarrow> get_sc_obj_ref sc_tcb sc_ptr;
    tcb_ptr \<leftarrow> assert_opt sc_tcb_opt;

    sched_context_resume sc_ptr;
    schedulable <- is_schedulable tcb_ptr;
    if schedulable then do
      sc \<leftarrow> get_sched_context sc_ptr;
      curtime \<leftarrow> gets cur_time;
      assert (sc_refill_ready curtime sc \<and> sc_refill_sufficient 0 sc);
      ct_ptr \<leftarrow> gets cur_thread;
      prios \<leftarrow> thread_get tcb_priority tcb_ptr;
      ct_prios \<leftarrow> thread_get tcb_priority ct_ptr;
      if prios < ct_prios
      then do
        tcb_sched_action tcb_sched_dequeue tcb_ptr;
        tcb_sched_action tcb_sched_enqueue tcb_ptr; \<comment> \<open>@{text \<open>schedulable & dequeued & sufficient & ready\<close>}\<close>
        set_consumed sc_ptr buffer
      od
      else do
        set_sc_obj_ref sc_yield_from_update sc_ptr (Some ct_ptr);
        set_tcb_obj_ref tcb_yield_to_update ct_ptr (Some sc_ptr);
        tcb_sched_action tcb_sched_dequeue tcb_ptr;
        tcb_sched_action tcb_sched_enqueue ct_ptr;
        tcb_sched_action tcb_sched_enqueue tcb_ptr;
        reschedule_required
      od
    od
    else set_consumed sc_ptr buffer
  od"


definition
  invoke_sched_context :: "sched_context_invocation \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "invoke_sched_context iv \<equiv> case iv of
    InvokeSchedContextConsumed sc_ptr args \<Rightarrow> set_consumed sc_ptr args
  | InvokeSchedContextBind sc_ptr cap \<Rightarrow> (case cap of
      ThreadCap tcb_ptr \<Rightarrow> sched_context_bind_tcb sc_ptr tcb_ptr
    | NotificationCap ntfn _ _ \<Rightarrow> sched_context_bind_ntfn sc_ptr ntfn
    | _ \<Rightarrow> fail)
  | InvokeSchedContextUnbindObject sc_ptr cap \<Rightarrow> (case cap of
      ThreadCap _ \<Rightarrow> sched_context_unbind_tcb sc_ptr
    | NotificationCap _ _ _ \<Rightarrow> sched_context_unbind_ntfn sc_ptr
    | _ \<Rightarrow> fail)
  | InvokeSchedContextUnbind sc_ptr \<Rightarrow> do
      sched_context_unbind_all_tcbs sc_ptr;
      sched_context_unbind_ntfn sc_ptr;
      sched_context_unbind_reply sc_ptr
    od
  | InvokeSchedContextYieldTo sc_ptr args \<Rightarrow>
      sched_context_yield_to sc_ptr args"

end
