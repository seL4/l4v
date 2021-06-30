(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Scheduling Contexts and Control"

theory Sporadic_A
imports CSpaceAcc_A
begin

text \<open> This theory contains operations on scheduling contexts and scheduling control. \<close>

definition
  is_round_robin :: "obj_ref \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "is_round_robin sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    return (sc_period sc = 0)
  od"

definition
  refill_pop_head :: "obj_ref \<Rightarrow> (refill, 'z::state_ext) s_monad"
where
  "refill_pop_head sc_ptr \<equiv> do
     refills \<leftarrow> get_refills sc_ptr;
     update_sched_context sc_ptr (sc_refills_update tl);
     return (hd refills)
   od"

definition
  refill_head_overlapping :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) r_monad"
where
  "refill_head_overlapping sc_ptr \<equiv> do {
    sc \<leftarrow> read_sched_context sc_ptr;
    oreturn (length (sc_refills sc) > 1
             \<and> r_time (hd (tl (sc_refills sc))) \<le> r_time (refill_hd sc) + r_amount (refill_hd sc))
  }"

definition
  update_refill_hd :: "obj_ref \<Rightarrow> (refill \<Rightarrow> refill) \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "update_refill_hd sc_ptr f = update_sched_context sc_ptr (sc_refills_update (\<lambda>refills. f (hd refills) # (tl refills)))"

definition
  "can_merge_refill r1 r2 \<equiv> r_time r2 \<le> r_time r1 + r_amount r1"

definition
  merge_refill :: "refill \<Rightarrow> refill \<Rightarrow> refill"
where
  "merge_refill r1 r2 = \<lparr> r_time = r_time r1, r_amount = r_amount r2 + r_amount r1 \<rparr>"

definition
  merge_refills :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "merge_refills sc_ptr \<equiv> do
     head \<leftarrow> refill_pop_head sc_ptr;
     update_refill_hd sc_ptr (merge_refill head)
   od"

definition
  refill_head_overlapping_loop :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_head_overlapping_loop sc_ptr
     \<equiv> whileLoop (\<lambda>_ s. the ((refill_head_overlapping sc_ptr) s)) (\<lambda>_. merge_refills sc_ptr) ()"

definition
  refill_unblock_check :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_unblock_check sc_ptr \<equiv> do
    robin \<leftarrow> is_round_robin sc_ptr;
    ready \<leftarrow> get_sc_refill_ready sc_ptr;
    when (ready \<and> \<not>robin) $ do
      modify (\<lambda>s. s\<lparr> reprogram_timer := True \<rparr>);
      ct \<leftarrow> gets cur_time;
      update_refill_hd sc_ptr (r_time_update (\<lambda>_. ct + kernelWCET_ticks));
      refill_head_overlapping_loop sc_ptr
    od
  od"


(*

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
     when (filter (\<lambda>(_,t'). t' \<le> time) qst = []) $
         modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>);
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
  max_refills_cap :: "cap \<Rightarrow> nat"
where
  "max_refills_cap cap \<equiv> case cap of SchedContextCap _ sz \<Rightarrow> max_num_refills (min_sched_context_bits + sz) | _ \<Rightarrow> 0"

definition
  set_refills :: "obj_ref \<Rightarrow> refill list \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_refills sc_ptr refills = set_sc_obj_ref sc_refills_update sc_ptr refills"

definition
  set_refill_hd :: "obj_ref \<Rightarrow> refill \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_refill_hd sc_ptr new = update_refill_hd sc_ptr (\<lambda>_. new)"

definition
  update_refill_tl :: "obj_ref \<Rightarrow> (refill \<Rightarrow> refill) \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "update_refill_tl sc_ptr f = update_sched_context sc_ptr (sc_refills_update (\<lambda>refills. butlast refills @ [f (last refills)]))"

definition
  set_refill_tl :: "obj_ref \<Rightarrow> refill \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_refill_tl sc_ptr new = update_refill_tl sc_ptr (\<lambda>_. new)"

definition
  refill_add_tail :: "obj_ref \<Rightarrow> refill \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_add_tail sc_ptr new_refill =
     update_sched_context sc_ptr (sc_refills_update (\<lambda>refills. refills @ [new_refill]))"

definition
  maybe_add_empty_tail :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_add_empty_tail sc_ptr = do
     robin \<leftarrow> is_round_robin sc_ptr;
     when robin $ do
       refills \<leftarrow> get_refills sc_ptr;
       empty_refill \<leftarrow> return \<lparr>r_time = r_time (hd refills), r_amount = 0\<rparr>;
       refill_add_tail sc_ptr empty_refill
     od
   od"

definition
  refill_new :: "obj_ref \<Rightarrow> nat \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_new sc_ptr max_refills budget period = do
     cur_time \<leftarrow> gets cur_time;
     set_sc_obj_ref sc_period_update sc_ptr period;
     set_sc_obj_ref sc_budget_update sc_ptr budget;
     set_sc_obj_ref sc_refill_max_update sc_ptr max_refills;
     refill \<leftarrow> return \<lparr> r_time = cur_time, r_amount = budget \<rparr>;
     set_sc_obj_ref sc_refills_update sc_ptr [refill];
     maybe_add_empty_tail sc_ptr
   od"

definition
  schedule_used :: "bool \<Rightarrow> refill list \<Rightarrow> refill \<Rightarrow> refill list"
where
  "schedule_used full original new
    = (if original = []
       then [new]
       else if (can_merge_refill (last original) new)
            then let new_last = \<lparr>r_time = r_time (last original),
                                 r_amount = r_amount (last original) + r_amount new \<rparr>
                 in (butlast original) @ [new_last]
            else if \<not>full
                 then original @ [new]
                 else let new_last = \<lparr>r_time = r_time new - r_amount (last original),
                                      r_amount = r_amount (last original) + r_amount new \<rparr>
                      in (butlast original) @ [new_last])"


definition
  refill_budget_check_round_robin :: "ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_budget_check_round_robin usage = do
    sc_ptr \<leftarrow> gets cur_sc;
    update_refill_hd sc_ptr (\<lambda>refill. refill\<lparr>r_amount := r_amount refill - usage\<rparr>);
    update_refill_tl sc_ptr (\<lambda>refill. refill\<lparr>r_amount := r_amount refill + usage\<rparr>)
   od"

definition
  head_insufficient :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) r_monad"
where
  "head_insufficient sc_ptr \<equiv>  do {
    sc \<leftarrow> read_sched_context sc_ptr;
    oreturn (r_amount (hd (sc_refills sc)) < MIN_BUDGET)
  }"

definition
  non_overlapping_merge_refills :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "non_overlapping_merge_refills sc_ptr \<equiv> do
     old_head \<leftarrow> refill_pop_head sc_ptr;
     update_refill_hd sc_ptr (r_time_update (\<lambda>t. t - r_amount old_head) o (r_amount_update (\<lambda>m. m + r_amount old_head)))
   od"

definition
  head_insufficient_loop :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "head_insufficient_loop sc_ptr
     \<equiv> whileLoop (\<lambda>_ s. the ((head_insufficient sc_ptr) s))
                  (\<lambda>_. non_overlapping_merge_refills sc_ptr) ()"

definition
  head_time_buffer :: "ticks \<Rightarrow> (bool, 'z::state_ext) r_monad"
where
  "head_time_buffer usage \<equiv> do {
    sc_ptr \<leftarrow> ogets cur_sc;
    sc \<leftarrow> read_sched_context sc_ptr;
    oreturn  (r_amount (refill_hd sc) \<le> usage
              \<and> max_time - r_time (refill_hd sc) \<ge> 5 * MAX_PERIOD)
  }"

definition
  handle_overrun_loop_body :: "ticks \<Rightarrow> (ticks, 'z::state_ext) s_monad"
where
  "handle_overrun_loop_body usage \<equiv> do
     sc_ptr \<leftarrow> gets cur_sc;
     single \<leftarrow> refill_single sc_ptr;
     sc \<leftarrow> get_sched_context sc_ptr;

     usage' \<leftarrow> return (usage - r_amount (refill_hd sc));

     if single

        then update_refill_hd sc_ptr (r_time_update (\<lambda>t. t + sc_period sc))
        else do old_head \<leftarrow> refill_pop_head sc_ptr;
                full \<leftarrow> refill_full sc_ptr;
                update_sched_context sc_ptr (sc_refills_update
                                                  (\<lambda>refills. schedule_used full refills
                                                   (old_head\<lparr>r_time := r_time old_head + sc_period sc\<rparr>)))
             od;
     return usage'
   od"

definition
  handle_overrun_loop :: "ticks \<Rightarrow> (ticks, 'z::state_ext) s_monad"
where
  "handle_overrun_loop usage
    \<equiv> whileLoop (\<lambda>usage s. the (head_time_buffer usage s))
                 (\<lambda>usage. handle_overrun_loop_body usage) usage"

definition
  refill_budget_check :: "ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_budget_check usage \<equiv> do
     sc_ptr \<leftarrow> gets cur_sc;

     robin \<leftarrow> is_round_robin sc_ptr;
     assert (\<not>robin);

     usage' \<leftarrow> handle_overrun_loop usage;

     refills \<leftarrow> get_refills sc_ptr;
     new_head_amount \<leftarrow> return (r_amount (hd refills));

     when (usage' > 0 \<and> usage' < new_head_amount) $ do
       sc \<leftarrow> get_sched_context sc_ptr;
       period \<leftarrow> return (sc_period sc);
       used \<leftarrow> return \<lparr>r_time = r_time (hd (sc_refills sc)) + period, r_amount = usage'\<rparr>;
       update_refill_hd sc_ptr (r_time_update (\<lambda>t. t + usage') o (r_amount_update (\<lambda>m. m - usage')));
       full \<leftarrow> return (size (sc_refills sc) = sc_refill_max sc);
       update_sched_context sc_ptr (sc_refills_update (\<lambda>refills. schedule_used full refills used))
     od;

     head_insufficient_loop sc_ptr
   od"

definition
  refill_update :: "obj_ref \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> nat \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_update sc_ptr new_period new_budget new_max_refills = do
     update_sched_context sc_ptr (sc_refills_update (\<lambda>rfs. [hd rfs]));
     set_sc_obj_ref sc_refill_max_update sc_ptr new_max_refills;
     set_sc_obj_ref sc_period_update sc_ptr new_period;
     set_sc_obj_ref sc_budget_update sc_ptr new_budget;

     ready \<leftarrow> get_sc_refill_ready sc_ptr;
     when ready $ do cur_time \<leftarrow> gets cur_time;
                     update_refill_hd sc_ptr (\<lambda>refill. refill\<lparr>r_time := cur_time\<rparr>)
                  od;

     sc \<leftarrow> get_sched_context sc_ptr;
     refill_hd \<leftarrow> return (hd (sc_refills sc));
     if new_budget \<le> r_amount refill_hd
     then do update_refill_hd sc_ptr (\<lambda>refill. refill\<lparr>r_amount := new_budget\<rparr>);
             maybe_add_empty_tail sc_ptr
          od
     else do unused \<leftarrow> return $ new_budget - r_amount refill_hd;
             new \<leftarrow> return \<lparr>r_time = r_time refill_hd + new_period, r_amount = unused\<rparr>;
             refill_add_tail sc_ptr new
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
    sched_context_resume sc_ptr;
    sched <- is_schedulable tcb_ptr;
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

definition
  sched_context_zero_refill_max :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_zero_refill_max sc_ptr = do
     update_sched_context sc_ptr (sc_refills_update (\<lambda>_. []));
     update_sched_context sc_ptr (sc_refill_max_update (\<lambda>_. 0))
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
           csc \<leftarrow> gets cur_sc;
           when (sc_ptr \<noteq> csc) $ refill_unblock_check (sc_ptr);
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
*)

end
