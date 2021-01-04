(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Scheduling Contexts and Control"

theory SchedContext_A
imports TcbAcc_A IpcCancel_A
begin

text \<open> This theory contains operations on scheduling contexts and scheduling control. \<close>

definition
  postpone :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "postpone sc_ptr = do
    tcb_opt \<leftarrow> get_sc_obj_ref sc_tcb sc_ptr;
    tcb_ptr \<leftarrow> assert_opt tcb_opt;
    tcb_sched_action tcb_sched_dequeue tcb_ptr;
    tcb_release_enqueue tcb_ptr;
    modify (\<lambda>s. s\<lparr> reprogram_timer := True \<rparr>)
  od"

text \<open>
  Resume a scheduling context: check if the bound TCB
  is runnable and add it to the scheduling queue if required
\<close>
definition
  sched_context_resume :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_resume sc_ptr \<equiv> do
     sc \<leftarrow> get_sched_context sc_ptr;
     tptr \<leftarrow> assert_opt $ sc_tcb sc;
     sched \<leftarrow> is_schedulable tptr;
     when sched $ do
       ts \<leftarrow> thread_get tcb_state tptr;
       ready \<leftarrow> get_sc_refill_ready sc_ptr;
       sufficient \<leftarrow> get_sc_refill_sufficient sc_ptr 0;
       when (runnable ts \<and> sc_active sc \<and> \<not>(ready \<and> sufficient)) $ do

         \<comment> \<open>C code also asserts that tptr is not in ready q\<close>
         d \<leftarrow> thread_get tcb_domain tptr;
         prio \<leftarrow> thread_get tcb_priority tptr;
         queue \<leftarrow> get_tcb_queue d prio;
         assert (\<not>(tptr \<in> set queue));

         postpone sc_ptr
       od
     od
   od"


text \<open>consumed related functions\<close>

definition
  sched_context_update_consumed :: "obj_ref \<Rightarrow> (time,'z::state_ext) s_monad" where
  "sched_context_update_consumed sc_ptr \<equiv> do
    sc \<leftarrow> get_sched_context sc_ptr;
    consumed \<leftarrow> return (sc_consumed sc);
    if max_ticks_to_us \<le> consumed
    then do set_sc_obj_ref sc_consumed_update sc_ptr (consumed - max_ticks_to_us);
            return (ticks_to_us (max_ticks_to_us))
         od
    else do set_sc_obj_ref sc_consumed_update sc_ptr 0;
            return (ticks_to_us (sc_consumed sc))
         od
   od"

definition
  set_consumed :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_consumed sc_ptr buf \<equiv> do
      consumed \<leftarrow> sched_context_update_consumed sc_ptr;
      ct \<leftarrow> gets cur_thread;
      sent \<leftarrow> set_mrs ct buf ((ucast consumed) # [ucast (consumed >> 32)]);
      set_message_info ct $ MI sent 0 0 0 \<comment> \<open>FIXME RT: is this correct?\<close>
    od"

text \<open>yield\_to related functions\<close>

definition
  complete_yield_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "complete_yield_to tcb_ptr \<equiv> do
     yt_opt \<leftarrow> get_tcb_obj_ref tcb_yield_to tcb_ptr;
     maybeM (\<lambda>sc_ptr. do
         buf \<leftarrow> lookup_ipc_buffer True tcb_ptr;
         set_consumed sc_ptr buf;
         set_sc_obj_ref sc_yield_from_update sc_ptr None;
         set_tcb_obj_ref tcb_yield_to_update tcb_ptr None
       od) yt_opt
    od"

definition
  sched_context_unbind_yield_from :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_yield_from sc_ptr \<equiv> do
    sc \<leftarrow> get_sched_context sc_ptr;
    maybeM complete_yield_to (sc_yield_from sc)
od"

text \<open>  Bind a TCB to a scheduling context. \<close>

definition
  test_possible_switch_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "test_possible_switch_to tcb_ptr = do
    sched \<leftarrow> is_schedulable tcb_ptr;
    when sched $ possible_switch_to tcb_ptr
  od"

definition
  sched_context_bind_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_bind_tcb sc_ptr tcb_ptr = do
    set_tcb_obj_ref tcb_sched_context_update tcb_ptr (Some sc_ptr);
    set_sc_obj_ref sc_tcb_update sc_ptr (Some tcb_ptr);
    active \<leftarrow> get_sc_active sc_ptr;
    when active $ refill_unblock_check sc_ptr;
    sched_context_resume sc_ptr;
    sched \<leftarrow> is_schedulable tcb_ptr;
    when sched $ do
      tcb_sched_action tcb_sched_enqueue tcb_ptr;
      reschedule_required
      od
  od"

definition
  maybe_sched_context_bind_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_sched_context_bind_tcb sc_ptr tcb_ptr = do
     sc' \<leftarrow> get_tcb_obj_ref tcb_sched_context tcb_ptr;
     when (sc' \<noteq> Some sc_ptr) $ sched_context_bind_tcb sc_ptr tcb_ptr
   od"


text \<open> Unbind TCB from its scheduling context, if there is one bound. \<close>
definition
  unbind_from_sc :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "unbind_from_sc tcb_ptr = do
    sc_ptr_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context tcb_ptr;
    maybeM sched_context_unbind_tcb sc_ptr_opt;
    maybeM (\<lambda>scptr. do
              sc \<leftarrow> get_sched_context scptr;
              maybeM complete_yield_to (sc_yield_from sc) od) sc_ptr_opt
  od"

definition
  maybe_donate_sc :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_donate_sc tcb_ptr ntfn_ptr = do
     sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context tcb_ptr;
     when (sc_opt = None) $
       get_ntfn_obj_ref ntfn_sc ntfn_ptr >>= maybeM (\<lambda>sc_ptr. do
         sc_tcb \<leftarrow> get_sc_obj_ref sc_tcb sc_ptr;
         when (sc_tcb = None) $ do
           sched_context_donate sc_ptr tcb_ptr;
           sched_context_resume sc_ptr
         od
       od)
   od"

definition
  maybe_return_sc :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_return_sc ntfn_ptr tcb_ptr = do
    nsc_opt \<leftarrow> get_ntfn_obj_ref ntfn_sc ntfn_ptr;
    tsc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context tcb_ptr;
    when (nsc_opt = tsc_opt \<and> nsc_opt \<noteq> None) $ do
      sc_ptr \<leftarrow> assert_opt nsc_opt;
      set_tcb_obj_ref tcb_sched_context_update tcb_ptr None;
      set_sc_obj_ref sc_tcb_update sc_ptr None;
      ct \<leftarrow> gets cur_thread;
      when (tcb_ptr = ct) reschedule_required
    od
  od"


definition
  commit_domain_time :: "(unit, 'z::state_ext) s_monad"
where
  "commit_domain_time = do
    consumed \<leftarrow> gets consumed_time;
    domain_time \<leftarrow> gets domain_time;
    time' \<leftarrow> return (if domain_time < consumed then 0 else domain_time - consumed);
    modify (\<lambda>s. s\<lparr>domain_time := time'\<rparr>)
  od"

text \<open> Update time consumption of current scheduling context and current domain. \<close>
definition
  commit_time :: "(unit, 'z::state_ext) s_monad"
where
  "commit_time = do
    csc \<leftarrow> gets cur_sc;
    sc \<leftarrow> get_sched_context csc;
    when (sc_active sc) $ do
      consumed \<leftarrow> gets consumed_time;
      when (0 < consumed) $ do
        robin \<leftarrow> is_round_robin csc;
        if robin
        then refill_budget_check_round_robin consumed
        else refill_budget_check consumed
      od;
      update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := (sc_consumed sc) + consumed \<rparr>)
    od;
    when (num_domains > 1) $
      commit_domain_time;
    modify (\<lambda>s. s\<lparr>consumed_time := 0\<rparr> )
  od"

section "Global time"

text \<open>Update current and consumed time.\<close>
definition
  update_time_stamp :: "(unit, 'z::state_ext) s_monad"
where
  "update_time_stamp = do
    prev_time \<leftarrow> gets cur_time;
    cur_time' \<leftarrow> do_machine_op getCurrentTime;
    modify (\<lambda>s. s\<lparr> cur_time := cur_time' \<rparr>);
    modify (\<lambda>s. s\<lparr> consumed_time := consumed_time s + cur_time' - prev_time \<rparr>)
  od"

text \<open>Currently, @{text update_restart_pc} can be defined generically up to
the actual register numbers.\<close>
definition
  update_restart_pc :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "update_restart_pc thread_ptr =
        as_user thread_ptr (getRegister nextInstructionRegister
                            >>= setRegister faultRegister)"

definition
  sched_context_cancel_yield_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_cancel_yield_to thread \<equiv> do
     yt_opt \<leftarrow> get_tcb_obj_ref tcb_yield_to thread;
     maybeM (\<lambda>sc_ptr. do
       set_sc_obj_ref sc_yield_from_update sc_ptr None;
       set_tcb_obj_ref tcb_yield_to_update thread None
     od) yt_opt
   od"

text \<open>Suspend a thread, cancelling any pending operations and preventing it
from further execution by setting it to the Inactive state.\<close>
definition
  suspend :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "suspend thread \<equiv> do
     cancel_ipc thread;
     state \<leftarrow> get_thread_state thread;
     when (state = Running) $ update_restart_pc thread;
     set_thread_state thread Inactive;
     tcb_sched_action (tcb_sched_dequeue) thread;
     tcb_release_remove thread;
     sched_context_cancel_yield_to thread
   od"

end
