(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
(*
text {* Gets the TCB at an address if the thread can be scheduled. *}
definition
  getActiveTCB :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> tcb option"
where
  "getActiveTCB tcb_ref s \<equiv>
   case get_tcb tcb_ref s
     of None     \<Rightarrow> None  (* FIXME is_schedulable_opt *)
      | Some tcb \<Rightarrow> if is_schedulable_opt tcb_ref False s = Some True then Some tcb else None"

text {* Gets all schedulable threads in the system. *}
definition
  allActiveTCBs :: "(obj_ref set,'z::state_ext) s_monad" where
  "allActiveTCBs \<equiv> do
    state \<leftarrow> get;
    return {x. getActiveTCB x state \<noteq> None}
   od"
*)
text {* Switches the current thread to the specified one. *}
definition
  switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "switch_to_thread t \<equiv> do
     state \<leftarrow> get;
     assert (get_tcb t state \<noteq> None);

     sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context t;
     scp \<leftarrow> assert_opt sc_opt; (* must have an sc *)
     inq \<leftarrow> gets $ in_release_queue t;
     assert (\<not> inq);  (* not in release q *)
     sc \<leftarrow> get_sched_context scp;
     curtime \<leftarrow> gets cur_time;
     sufficient \<leftarrow> return $ sufficient_refills 0 (sc_refills sc); (* refill_sufficient sc_ptr 0 *)
     ready \<leftarrow> return $ (r_time (refill_hd sc)) \<le> curtime + kernelWCET_ticks; (* refill_ready sc_ptr *)
     assert sufficient;
     assert ready;   (* asserting ready & sufficient *)

     arch_switch_to_thread t;
     tcb_sched_action (tcb_sched_dequeue) t;
     modify (\<lambda>s. s \<lparr> cur_thread := t \<rparr>)
   od"

text {* Asserts that a thread is schedulable before switching to it. *}
definition guarded_switch_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "guarded_switch_to thread \<equiv> do
     inq \<leftarrow> gets $ in_release_queue thread;
     sched \<leftarrow> is_schedulable thread inq;
     sc_opt \<leftarrow> thread_get tcb_sched_context thread;
     scp \<leftarrow> assert_opt sc_opt;
     assert sched;
     sc \<leftarrow> get_sched_context scp;
     curtime \<leftarrow> gets cur_time;
     sufficient \<leftarrow> return $ sufficient_refills 0 (sc_refills sc); (* refill_sufficient sc_ptr 0 *)
     ready \<leftarrow> return $ (r_time (refill_hd sc)) \<le> curtime + kernelWCET_ticks; (* refill_ready sc_ptr *)
     assert sufficient;
     assert ready;   (* asserting ready & sufficient *)
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
  set_next_timer_interrupt :: "time \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_next_timer_interrupt thread_time = do
     cur_tm \<leftarrow> gets cur_time;
     domain_tm \<leftarrow> gets domain_time;
     new_domain_tm \<leftarrow> return $ cur_tm + domain_tm;
     do_machine_op $ setDeadline (min thread_time new_domain_tm - timerPrecision)
  od"

definition
  set_next_interrupt :: "(unit, 'z::state_ext) s_monad"
where
  "set_next_interrupt = do
     cur_tm \<leftarrow> gets cur_time;
     cur_th \<leftarrow> gets cur_thread;
     sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context cur_th;
     sc_ptr \<leftarrow> assert_opt sc_opt;
     sc \<leftarrow> get_sched_context sc_ptr;
     new_thread_time \<leftarrow> return $ cur_tm + r_amount (refill_hd sc);
     rq \<leftarrow> gets release_queue;
     new_thread_time \<leftarrow> if rq = [] then return new_thread_time else do
       rqsc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context (hd rq);
       rqsc_ptr \<leftarrow> assert_opt rqsc_opt;
       rqsc \<leftarrow> get_sched_context rqsc_ptr;
       return $ min (r_time (refill_hd rqsc)) new_thread_time
     od;
     set_next_timer_interrupt new_thread_time
  od"

definition
  switch_sched_context :: "(unit,'z::state_ext) s_monad"
where
  "switch_sched_context = do
    cur_sc \<leftarrow> gets cur_sc;
    cur_th \<leftarrow> gets cur_thread;
    sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context cur_th;
    scp \<leftarrow> assert_opt sc_opt;
    when (scp \<noteq> cur_sc) $ do
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>);
      refill_unblock_check scp;
      sc \<leftarrow> get_sched_context scp;
      curtime \<leftarrow> gets cur_time;
      sufficient \<leftarrow> return $ sufficient_refills 0 (sc_refills sc); (* refill_sufficient sc_ptr 0 *)
      ready \<leftarrow> return $ (r_time (refill_hd sc)) \<le> curtime + kernelWCET_ticks; (* refill_ready sc_ptr *)
      assert sufficient;
      assert ready   (* asserting ready & sufficient *)
     od;
    reprogram \<leftarrow> gets reprogram_timer;
    if reprogram
    then
      commit_time
    else
      rollback_time;

   (* the C code asserts ((ready & sufficient cur_sc) \<or> not in ready q) here *)
      sc_tcb_opt \<leftarrow> get_sc_obj_ref sc_tcb cur_sc;
      ct \<leftarrow> assert_opt sc_tcb_opt;
      d \<leftarrow> thread_get tcb_domain ct;
      prio \<leftarrow> thread_get tcb_priority ct;
      queue \<leftarrow> get_tcb_queue d prio;
      sufficient \<leftarrow> refill_sufficient cur_sc 0;
      ready \<leftarrow> refill_ready cur_sc;
      assert ((ready \<and> sufficient) \<or>\<not>(ct \<in> set queue));

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
  fun_of_m :: "('s, 'a) nondet_monad \<Rightarrow> 's \<Rightarrow> 'a option"
where
  "fun_of_m m \<equiv> \<lambda>s. if \<exists>x s'. m s = ({(x,s')}, False)
                    then Some (THE x. \<exists>s'. m s = ({(x,s')}, False))
                    else None"

definition
  refill_ready_tcb :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "refill_ready_tcb t = do
     sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context t;
     sc_ptr \<leftarrow> assert_opt sc_opt;
     ready \<leftarrow> refill_ready sc_ptr;
     sufficient \<leftarrow> refill_sufficient sc_ptr 0;
     return (ready \<and> sufficient)
   od"

definition
  awaken :: "(unit, 'z::state_ext) s_monad"
where
  "awaken \<equiv> do
    rq \<leftarrow> gets release_queue;
    s \<leftarrow> get;
    rq1 \<leftarrow> return $ takeWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s)) rq;
    rq2 \<leftarrow> return $ drop (length rq1) rq;
    modify $ release_queue_update (K rq2);
    mapM_x (\<lambda>t. do
      (* the C code asserts refill_sufficient here \<rightarrow> we guarantee this inside refill_ready_tcb for now *)
      possible_switch_to t;
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>)
    od) rq1
  od"

definition max_non_empty_queue :: "(priority \<Rightarrow> ready_queue) \<Rightarrow> ready_queue" where
  "max_non_empty_queue queues \<equiv> queues (Max {prio. queues prio \<noteq> []})"

definition choose_thread :: "(unit, 'z::state_ext) s_monad" where
"choose_thread \<equiv>
      do
        d \<leftarrow> gets cur_domain;
        queues \<leftarrow> gets (\<lambda>s. ready_queues s d);
        if (\<forall>prio. queues prio = []) then (switch_to_idle_thread)
        else (guarded_switch_to (hd (max_non_empty_queue queues)))
      od"

text {*
  Determine whether given priority is highest among queued ready threads in given domain.
  Trivially true if no threads are ready. *}
definition
  is_highest_prio :: "domain \<Rightarrow> priority \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "is_highest_prio d p s \<equiv>
    (\<forall>prio. ready_queues s d prio = [])
    \<or> p \<ge> Max {prio. ready_queues s d prio \<noteq> []}"

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
  "schedule \<equiv> do
     awaken;
     ct \<leftarrow> gets cur_thread;
     inq \<leftarrow> gets $ in_release_queue ct;
     ct_schedulable \<leftarrow> is_schedulable ct inq;
     action \<leftarrow> gets scheduler_action;
     (case action
       of resume_cur_thread \<Rightarrow> do
            id \<leftarrow> gets idle_thread;
            assert (ct_schedulable \<or> ct = id);
            return ()
         od
       | choose_new_thread \<Rightarrow> do
           when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct); (* schedulable *)
           schedule_choose_new_thread
         od
       | switch_thread candidate \<Rightarrow> do
           when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct); (* schedulable *)

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
           else if (ct_schedulable \<and> ct_prio = target_prio)
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
        od);
     sc_and_timer
   od"


text {* Scheduling context invocation function *}

text \<open> User-level scheduling context invocations. \<close>

definition
  parse_time_arg :: "nat \<Rightarrow> data list \<Rightarrow> time"
where
  "parse_time_arg i args \<equiv> (ucast (args!(i+1)) << 32) + ucast (args!i)"

definition
  sched_context_yield_to :: "obj_ref \<Rightarrow> data list \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_yield_to sc_ptr args \<equiv> do
    sc_yf_opt \<leftarrow> get_sc_obj_ref sc_yield_from sc_ptr;
    when (sc_yf_opt \<noteq> None) $ do
      complete_yield_to (the sc_yf_opt); \<comment> \<open> sc_yield_from = None \<close>
      sc_yf_opt \<leftarrow> get_sc_obj_ref sc_yield_from sc_ptr;
      assert (sc_yf_opt = None)
    od;
    flag \<leftarrow> return True;
    refill_unblock_check sc_ptr;
    sc_tcb_opt \<leftarrow> get_sc_obj_ref sc_tcb sc_ptr;
    tcb_ptr \<leftarrow> assert_opt sc_tcb_opt;
    in_release_q <- gets $ in_release_queue tcb_ptr;
    schedulable <- is_schedulable tcb_ptr in_release_q;
    when (schedulable) $ do
      sc \<leftarrow> get_sched_context sc_ptr;
      cur_time \<leftarrow> gets cur_time;
      ready \<leftarrow> return $ (r_time (refill_hd sc)) \<le> cur_time + kernelWCET_ticks; \<comment> \<open> refill_ready sc_ptr \<close>
      sufficient \<leftarrow> return $ sufficient_refills 0 (sc_refills sc); \<comment> \<open> refill_sufficient sc_ptr 0 \<close>
      assert (sufficient \<and> ready);
      ct_ptr \<leftarrow> gets cur_thread;
      prios \<leftarrow> thread_get tcb_priority tcb_ptr;
      ct_prios \<leftarrow> thread_get tcb_priority ct_ptr;
      if (prios < ct_prios)
      then do
        tcb_sched_action tcb_sched_dequeue tcb_ptr;
        tcb_sched_action tcb_sched_enqueue tcb_ptr \<comment> \<open> schedulable & dequeud & sufficient & ready \<close>
      od
      else do
        flag \<leftarrow> return False;
        set_sc_obj_ref sc_yield_from_update sc_ptr (Some ct_ptr);
        set_tcb_obj_ref tcb_yield_to_update ct_ptr (Some sc_ptr);
        tcb_sched_action tcb_sched_dequeue tcb_ptr;
        tcb_sched_action tcb_sched_enqueue tcb_ptr;
        tcb_sched_action tcb_sched_enqueue ct_ptr;
        reschedule_required
      od
    od;
    when flag $ set_consumed sc_ptr args
  od"


definition
  invoke_sched_context :: "sched_context_invocation \<Rightarrow> (unit, 'z::state_ext) se_monad"
where
  "invoke_sched_context iv \<equiv> liftE $ case iv of
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
