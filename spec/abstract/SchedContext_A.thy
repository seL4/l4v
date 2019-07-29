(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "Scheduling Contexts and Control"

theory SchedContext_A
imports TcbAcc_A IpcCancel_A
begin

text \<open> This theory contains operations on scheduling contexts and scheduling control. \<close>

definition
  is_cur_domain_expired :: "'z::state_ext state \<Rightarrow> bool"
where
  "is_cur_domain_expired = (\<lambda>s. domain_time  s < consumed_time s + MIN_BUDGET)"

definition
  is_round_robin :: "obj_ref \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "is_round_robin sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    return (sc_period sc = 0)
  od"

definition
  get_tcb_sc :: "obj_ref \<Rightarrow> (sched_context,'z::state_ext) s_monad"
where
  "get_tcb_sc tcb_ptr = do
    sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context tcb_ptr;
    sc_ptr \<leftarrow> assert_opt sc_opt;
    get_sched_context sc_ptr
  od"

definition
  get_sc_time :: "obj_ref \<Rightarrow> (time, 'z::state_ext) s_monad"
where
  "get_sc_time tcb_ptr = do
    sc \<leftarrow> get_tcb_sc tcb_ptr;
    return $ r_time (refill_hd sc)
  od"


text \<open>Enqueue a TCB in the release queue, sorted by release time of
  the corresponding scheduling context.\<close>
definition
  tcb_release_enqueue :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "tcb_release_enqueue tcb_ptr = do
     time \<leftarrow> get_sc_time tcb_ptr;
     qs \<leftarrow> gets release_queue;
     times \<leftarrow> mapM get_sc_time qs;
     qst \<leftarrow> return $ zip qs times;
     qst' \<leftarrow> return $ filter (\<lambda>(_,t'). t' \<le> time) qst @ [(tcb_ptr,time)] @ filter (\<lambda>(_,t'). \<not>t' \<le> time) qst;
     modify (\<lambda>s. s\<lparr>release_queue := map fst qst'\<rparr>)
  od"

definition
  refill_size :: "obj_ref \<Rightarrow> (nat, 'z::state_ext) s_monad"
where
  "refill_size sc_ptr = do
    refills \<leftarrow> get_refills sc_ptr;
    return $ size refills
  od"

definition
  refill_full :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "refill_full sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    return (size (sc_refills sc) = sc_refill_max sc)
  od"

definition
  refill_single :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "refill_single sc_ptr = do
    sz \<leftarrow> refill_size sc_ptr;
    return (sz = 1)
  od"

definition
  refills_sum :: "refill list \<Rightarrow> time"
where
  "refills_sum rf = sum_list (map r_amount rf)"

definition
  refill_sum :: "obj_ref \<Rightarrow> (time, 'z::state_ext) s_monad"
where
  "refill_sum sc_ptr = do
    refills \<leftarrow> get_refills sc_ptr;
    return $ refills_sum refills
  od"

definition
  refill_absolute_max :: "cap \<Rightarrow> nat"
where
  "refill_absolute_max cap =
    (case cap of SchedContextCap _ sc \<Rightarrow>
        (nat (1 << sc) - core_sched_context_bytes) div refill_size_bytes + MIN_REFILLS
    | _ \<Rightarrow> 0) "

definition
  set_refills :: "obj_ref \<Rightarrow> refill list \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_refills sc_ptr refills = update_sched_context sc_ptr (\<lambda>sc. sc\<lparr>sc_refills:= refills\<rparr>)"

definition
  refill_pop_head :: "obj_ref \<Rightarrow> (refill, 'z::state_ext) s_monad"
where
  "refill_pop_head sc_ptr = do
    refills \<leftarrow> get_refills sc_ptr;
    assert (1 < size refills);
    set_refills sc_ptr (tl refills);
    return $ hd refills
  od"

definition
  refill_add_tail :: "obj_ref \<Rightarrow> refill \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_add_tail sc_ptr rfl = do
    sc \<leftarrow> get_sched_context sc_ptr;
    refills \<leftarrow> return (sc_refills sc);
    assert (size refills < sc_refill_max sc);
    set_refills sc_ptr (refills @ [rfl])
  od"

definition
  refill_new :: "obj_ref \<Rightarrow> nat \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_new sc_ptr max_refills budget period = do
    assert (MIN_BUDGET < budget);
    cur_time \<leftarrow> gets cur_time;
    refill \<leftarrow> return \<lparr> r_time = cur_time, r_amount = budget \<rparr>;
    update_sched_context sc_ptr
            (\<lambda>sc. sc\<lparr> sc_period := period, sc_refills := [refill], sc_refill_max := max_refills,
                      sc_budget := budget \<rparr>)
  od"

(* definition
  schedule_used :: "obj_ref \<Rightarrow> refill \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "schedule_used sc_ptr new = do
    refills \<leftarrow> get_refills sc_ptr;
    tl \<leftarrow> return $ last refills;
    full \<leftarrow> refill_full sc_ptr;
    if (r_amount new < MIN_BUDGET \<or> full)
    then let new_tl = tl\<lparr>r_time := r_time new - r_amount tl,
                         r_amount := r_amount tl + r_amount new\<rparr> in
         set_refills sc_ptr ( (butlast refills) @ [new_tl] )
    else refill_add_tail sc_ptr new
  od" *)

fun
  schedule_used :: "bool \<Rightarrow> refill list \<Rightarrow> refill \<Rightarrow> refill list"
where
  "schedule_used full [] new = [new]"
| "schedule_used full (x#rs) new = (
      if (r_amount new < MIN_BUDGET \<or> full)
      then let tl = last (x#rs);
               new_tl = tl\<lparr> r_time := r_time new - r_amount tl,
                            r_amount := r_amount tl + r_amount new \<rparr> in
           (butlast (x#rs)) @ [new_tl]
      else (x#rs) @ [new])"

definition
  merge_refill :: "refill \<Rightarrow> refill \<Rightarrow> refill"
where
  "merge_refill r1 r2 = \<lparr> r_time = r_time r1, r_amount = r_amount r2 + r_amount r1 \<rparr>"

definition
  "can_merge_refill r1 r2 \<equiv> r_time r2 \<le> r_time r1 + r_amount r1"

fun
  refills_merge_prefix :: "refill list \<Rightarrow> refill list"
where
  "refills_merge_prefix [] = []"
| "refills_merge_prefix [r] = [r]"
| "refills_merge_prefix (r1 # r2 # rs) =
     (if can_merge_refill r1 r2
      then refills_merge_prefix (merge_refill r1 r2 # rs)
      else r1 # r2 # rs)"

definition
  refill_unblock_check :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_unblock_check sc_ptr = do
    robin \<leftarrow> is_round_robin sc_ptr;
    when (\<not> robin ) $ do
      ct \<leftarrow> gets cur_time;
      modify (\<lambda>s. s\<lparr> reprogram_timer := True \<rparr>);
      refills \<leftarrow> get_refills sc_ptr;
      ready \<leftarrow> refill_ready sc_ptr;
      when ready $ do
        refills' \<leftarrow> return $ refills_merge_prefix ((hd refills)\<lparr>r_time := ct\<rparr> # tl refills);
        set_refills sc_ptr refills'
      od
    od
  od"

fun
  min_budget_merge :: "bool \<Rightarrow> refill list \<Rightarrow> refill list"
where
  "min_budget_merge _ [] = []"
| "min_budget_merge _ [r] = [r]"
| "min_budget_merge full (r0#r1#rs) = (if (r_amount r0 < MIN_BUDGET \<or> full)
     then min_budget_merge False (r1\<lparr> r_amount := r_amount r0 + r_amount r1 \<rparr> # rs)
     else (r0#r1#rs))" (* RT: full can be true only at the beginning,
                              because the refills size decreases by 1 in each call *)

definition
  refill_budget_check :: "ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_budget_check usage = do
    sc_ptr \<leftarrow> gets cur_sc;
    sc \<leftarrow> get_sched_context sc_ptr;
    ready \<leftarrow> refill_ready sc_ptr;
    period \<leftarrow> return $ sc_period sc;
    robin \<leftarrow> is_round_robin sc_ptr;
    assert (\<not>robin);
    refills \<leftarrow> return (sc_refills sc);

    last_entry \<leftarrow> return $ r_time (hd refills);

    used \<leftarrow> return $ \<lparr>r_time = last_entry + period, r_amount = usage\<rparr>;

    if (\<not>ready \<or> r_amount (hd refills) < usage)
    then set_refills sc_ptr [used\<lparr>r_time := r_time used + usage, r_amount := sc_budget sc\<rparr>]
    else if (usage = r_amount (hd refills))
         then set_refills sc_ptr (schedule_used False (tl refills) used)
                \<comment> \<open>if refills has length at most sc_refills_max sc, then popping the head
                    will ensure the refills are not full, so we may use False here\<close>
         else do remnant \<leftarrow> return $ (r_amount (hd refills) - usage);
                 if (remnant < MIN_BUDGET)
                 then do snd \<leftarrow> return $ hd (tl refills);
                         new_snd \<leftarrow> return $ (snd\<lparr>r_time := r_time snd - remnant,
                                                  r_amount := r_amount snd + remnant\<rparr>);
                         set_refills sc_ptr (schedule_used False (new_snd # tl (tl refills)) used)
                      od
                 else do full \<leftarrow> refill_full sc_ptr;
                         rfhd \<leftarrow> return $ (hd refills);
                         new_head \<leftarrow> return $ (rfhd\<lparr>r_time := r_time rfhd + usage, r_amount := remnant\<rparr>);
                         set_refills sc_ptr (schedule_used full (new_head # (tl refills)) used)
                      od
              od
   od"

definition
  refill_update :: "obj_ref \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> nat \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_update sc_ptr new_period new_budget new_max_refills = do
     sc \<leftarrow> get_sched_context sc_ptr;
     refill_hd \<leftarrow> return $ hd (sc_refills sc);

     cur_time \<leftarrow> gets cur_time;
     ready \<leftarrow> refill_ready sc_ptr;

     new_time \<leftarrow> return $ if ready then cur_time else (r_time refill_hd);
     if (r_amount refill_hd \<ge> new_budget)
     then update_sched_context sc_ptr (\<lambda>_. sc\<lparr>sc_period := new_period,
                                       sc_refill_max := new_max_refills,
                                       sc_refills := [\<lparr> r_time = new_time,
                                                        r_amount = new_budget\<rparr>],
                                       sc_budget := new_budget\<rparr>)
     else do
            unused \<leftarrow> return $ (new_budget - r_amount refill_hd);
            new \<leftarrow> return $ \<lparr>r_time = r_time refill_hd + new_period - unused, r_amount = unused \<rparr>;
            new_refills \<leftarrow> return $ (schedule_used False [refill_hd] new);
                 \<comment> \<open>since the length of refill_hd is 1 and MAX_REFILLS is at least
                      @{term MIN_REFILLS} = 2, we will have that [refill_hd] is not full, and so
                      we may use False here\<close>
            update_sched_context sc_ptr (\<lambda>_. sc\<lparr>sc_period := new_period,
                                         sc_refill_max := new_max_refills,
                                         sc_refills := new_refills,
                                         sc_budget := new_budget\<rparr>)
          od
    od"

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
  sched_context_resume :: "obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_resume sc_opt \<equiv> maybeM (\<lambda>sc_ptr. do
     sc \<leftarrow> get_sched_context sc_ptr;
     tptr \<leftarrow> assert_opt $ sc_tcb sc;
     in_release_q \<leftarrow> gets $ in_release_queue tptr;
     sched \<leftarrow> is_schedulable tptr in_release_q;
     when sched $ do
       ts \<leftarrow> thread_get tcb_state tptr;

       cur_time \<leftarrow> gets cur_time;
       ready \<leftarrow> return $ (r_time (refill_hd sc)) \<le> cur_time + kernelWCET_ticks; \<comment> \<open>refill_ready sc_ptr\<close>

       sufficient \<leftarrow> return $ sufficient_refills 0 (sc_refills sc); \<comment> \<open>refill_sufficient sc_ptr 0\<close>
       when (runnable ts \<and> 0 < sc_refill_max sc \<and> \<not>(ready \<and> sufficient)) $ do

         \<comment> \<open>C code also asserts that tptr is not in ready q\<close>
         d \<leftarrow> thread_get tcb_domain tptr;
         prio \<leftarrow> thread_get tcb_priority tptr;
         queue \<leftarrow> get_tcb_queue d prio;
         assert (\<not>(tptr \<in> set queue));

         postpone sc_ptr
       od
     od
   od) sc_opt"


text \<open>consumed related functions\<close>

definition
  sched_context_update_consumed :: "obj_ref \<Rightarrow> (time,'z::state_ext) s_monad" where
  "sched_context_update_consumed sc_ptr \<equiv> do
    sc \<leftarrow> get_sched_context sc_ptr;
    update_sched_context sc_ptr (\<lambda>_. sc\<lparr>sc_consumed := 0 \<rparr>);
    return (sc_consumed sc)
   od"

definition
  set_consumed :: "obj_ref \<Rightarrow> data list \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_consumed sc_ptr args \<equiv>do
      consumed \<leftarrow> sched_context_update_consumed sc_ptr;
      ct \<leftarrow> gets cur_thread;
      buffer \<leftarrow> return $ data_to_oref $ args ! 0;
      sent \<leftarrow> set_mrs ct (Some buffer) ((ucast consumed) # [ucast (consumed >> 32)]);
      set_message_info ct $ MI sent 0 0 0 \<comment> \<open>RT: is this correct?\<close>
    od"

text \<open>yield\_to related functions\<close>
term maybeM
definition
  complete_yield_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "complete_yield_to tcb_ptr \<equiv> do
     yt_opt \<leftarrow> get_tcb_obj_ref tcb_yield_to tcb_ptr;
     maybeM (\<lambda>sc_ptr. do
         args \<leftarrow> lookup_ipc_buffer True tcb_ptr;
         buf \<leftarrow> assert_opt args;
         set_consumed sc_ptr [buf];
         set_tcb_obj_ref tcb_yield_to_update tcb_ptr None;
         set_sc_obj_ref sc_yield_from_update sc_ptr None
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
    inq \<leftarrow> gets $ in_release_queue tcb_ptr;
    sched \<leftarrow> is_schedulable tcb_ptr inq;
    when sched $ possible_switch_to tcb_ptr
  od"

definition
  sched_context_bind_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_bind_tcb sc_ptr tcb_ptr = do
    set_sc_obj_ref sc_tcb_update sc_ptr (Some tcb_ptr);
    set_tcb_obj_ref tcb_sched_context_update tcb_ptr (Some sc_ptr);
    sched_context_resume (Some sc_ptr);
    inq <- gets $ in_release_queue tcb_ptr;
    sched <- is_schedulable tcb_ptr inq;
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
           refill_unblock_check (sc_ptr);
           sched_context_resume (Some sc_ptr)
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
      set_sc_obj_ref sc_tcb_update sc_ptr None
    od
  od"


definition
  commit_domain_time :: "(unit, 'z::state_ext) s_monad"
where
  "commit_domain_time = do
    domain_time \<leftarrow> gets domain_time;
    consumed \<leftarrow> gets consumed_time;
    time' \<leftarrow> return (if domain_time < consumed then 0 else domain_time - consumed);
    modify (\<lambda>s. s\<lparr>domain_time := time'\<rparr>)
  od"

text \<open> Update time consumption of current scheduling context and current domain. \<close>
definition
  commit_time :: "(unit, 'z::state_ext) s_monad"
where
  "commit_time = do
    consumed \<leftarrow> gets consumed_time;
    csc \<leftarrow> gets cur_sc;
    sc \<leftarrow> get_sched_context csc;
    when (0 < sc_refill_max sc) $ do
      when (0 < consumed) $ do
        curtime \<leftarrow> gets cur_time;
        sufficient \<leftarrow> return $ sufficient_refills consumed (sc_refills sc); \<comment> \<open>refill_sufficient sc_ptr 0\<close>
        ready \<leftarrow> return $ (r_time (refill_hd sc)) \<le> curtime + kernelWCET_ticks; \<comment> \<open>refill_ready sc_ptr\<close>
        assert sufficient;
        assert ready;   \<comment> \<open>asserting ready & sufficient\<close>
        robin \<leftarrow> is_round_robin csc;
        if robin then
        let new = ((refill_hd sc) \<lparr> r_time := r_time (refill_hd sc) + consumed,
                                    r_amount := sc_budget sc \<rparr>) in
        set_refills csc [new]
      else refill_budget_check consumed;
        sc2 \<leftarrow> get_sched_context csc;
        curtime2 \<leftarrow> gets cur_time;
        sufficient2 \<leftarrow> return $ sufficient_refills consumed (sc_refills sc2); \<comment> \<open>refill_sufficient sc_ptr 0\<close>
        ready2 \<leftarrow> return $ (r_time (refill_hd sc2)) \<le> curtime2 + kernelWCET_ticks; \<comment> \<open>refill_ready sc_ptr\<close>
        assert sufficient2;
        assert ready2  \<comment> \<open>asserting ready & sufficient again\<close>
      od;
      update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := (sc_consumed sc) + consumed \<rparr>)
    od;
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

text \<open>Suspend a thread, cancelling any pending operations and preventing it
from further execution by setting it to the Inactive state.\<close>
definition
  suspend :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "suspend thread \<equiv> do
     cancel_ipc thread;
     yt_opt \<leftarrow> get_tcb_obj_ref tcb_yield_to thread;
     maybeM (\<lambda>sc_ptr. do
       set_sc_obj_ref sc_yield_from_update sc_ptr None;
       set_tcb_obj_ref tcb_yield_to_update thread None
     od) yt_opt;
     set_thread_state thread Inactive;
     tcb_sched_action (tcb_sched_dequeue) thread;
     tcb_release_remove thread
   od"

end
