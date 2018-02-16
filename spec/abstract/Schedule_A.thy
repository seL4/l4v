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

text {* Asserts that a thread is schedulable before switching to it. *}
definition guarded_switch_to :: "obj_ref \<Rightarrow> unit det_ext_monad" where
  "guarded_switch_to thread \<equiv> do
     inq \<leftarrow> gets $ in_release_queue thread;
     sched \<leftarrow> is_schedulable thread inq;
     assert sched;
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

definition
  set_next_interrupt :: "unit det_ext_monad"
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
       sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context (hd rq);
       sc_ptr \<leftarrow> assert_opt sc_opt;
       sc \<leftarrow> get_sched_context sc_ptr;
       return $ min (r_time (refill_hd sc)) new_thread_time
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
    sc \<leftarrow> assert_opt sc_opt;
    when (sc \<noteq> cur_sc) $ do
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>);
      refill_unblock_check sc
    od;
    reprogram \<leftarrow> gets reprogram_timer;
    if reprogram
    then
      commit_time
    else
      rollback_time;
    modify (\<lambda>s. s\<lparr> cur_sc:= sc \<rparr>)
  od"

definition
  sc_and_timer :: "(unit, 'z::state_ext) s_monad"
where
  "sc_and_timer = do
    switch_sched_context;
    reprogram \<leftarrow> gets reprogram_timer;
    when reprogram $ do
      do_extended_op set_next_interrupt;
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
     refill_ready sc_ptr
   od"

definition
  awaken :: "unit det_ext_monad"
where
  "awaken \<equiv> do
    rq \<leftarrow> gets release_queue;
    s \<leftarrow> get;
    rq1 \<leftarrow> return $ takeWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s)) rq;
    rq2 \<leftarrow> return $ drop (length rq1) rq;
    modify $ release_queue_update (K rq);
    mapM_x (\<lambda>t. do
      possible_switch_to t;
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>)
    od) rq1
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

text {*
  Determine whether given priority is highest among queued ready threads in given domain.
  Trivially true if no threads are ready. *}
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
           when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct);
           schedule_choose_new_thread
         od
       | switch_thread candidate \<Rightarrow> do
           when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct);

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

instance ..
end


instantiation unit :: state_ext_sched
begin


text {*
  The scheduler is heavily underspecified.
  It is allowed to pick any active thread or the idle thread.
  If the thread the scheduler picked is the current thread, it
  may omit the call to @{const switch_to_thread}. Likewise it
  may omit the call to @{const switch_to_idle_thread} if the
  idle thread is the current thread.
*}
definition schedule_unit :: "(unit,unit) s_monad" where
"schedule_unit \<equiv> do
 (do
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
  od);
  sc_and_timer
  od"

instance ..
end


lemmas schedule_def = schedule_det_ext_ext_def schedule_unit_def

text {* Scheduling context invocation function *}

text \<open> User-level scheduling context invocations. \<close>

definition
  parse_time_arg :: "nat \<Rightarrow> data list \<Rightarrow> time"
where
  "parse_time_arg i args \<equiv> (ucast (args!(i+1)) << 32) + ucast (args!i)"

definition
  sched_context_yield_to :: "obj_ref \<Rightarrow> data list \<Rightarrow> (unit, det_ext) s_monad"
where
  "sched_context_yield_to sc_ptr args \<equiv> do
    flag \<leftarrow> return True;
    refill_unblock_check sc_ptr;
    sc_opt \<leftarrow> get_sc_obj_ref sc_tcb sc_ptr;
    tcb_ptr \<leftarrow> assert_opt sc_opt;
    schedulable \<leftarrow> is_schedulable tcb_ptr False;
    when (schedulable) $ do
      sufficient \<leftarrow> refill_sufficient sc_ptr 0;
      ready \<leftarrow> refill_ready sc_ptr;
      assert (sufficient \<and> ready);
      ct_ptr \<leftarrow> gets cur_thread;
      prios \<leftarrow> ethread_get tcb_priority tcb_ptr;
      ct_prios \<leftarrow> ethread_get tcb_priority ct_ptr;
      if (prios < ct_prios)
      then do
        tcb_sched_action tcb_sched_dequeue tcb_ptr;
        tcb_sched_action tcb_sched_enqueue tcb_ptr
      od
      else do
        flag \<leftarrow> return False;
        set_sc_obj_ref sc_yield_from_update sc_ptr (Some ct_ptr);
        set_tcb_obj_ref tcb_yield_to_update ct_ptr (Some sc_ptr);
        possible_switch_to ct_ptr
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
      ThreadCap tcb_ptr \<Rightarrow> do_extended_op $ sched_context_bind_tcb sc_ptr tcb_ptr
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
      do_extended_op $ sched_context_yield_to sc_ptr args"



end
