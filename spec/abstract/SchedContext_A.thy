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
  is_cur_domain_expired :: "det_ext state \<Rightarrow> bool"
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

abbreviation
  "refill_hd sc \<equiv> hd (sc_refills sc)"

abbreviation
  "refill_tl sc \<equiv> last (sc_refills sc)" (** condition? **)

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
  tcb_release_enqueue :: "obj_ref \<Rightarrow> unit det_ext_monad"
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
  refills_capacity :: "time \<Rightarrow> refill list \<Rightarrow> time"
where
  "refills_capacity usage refills \<equiv>
  if r_amount (hd refills) < usage then 0 else r_amount (hd refills) - usage"

definition
  get_refills :: "obj_ref \<Rightarrow> (refill list, 'z::state_ext) s_monad"
where
  "get_refills sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    return $ sc_refills sc
  od"

definition
  refill_capacity :: "obj_ref \<Rightarrow> time \<Rightarrow> (time, 'z::state_ext) s_monad"
where
  "refill_capacity sc_ptr usage = do
    refills \<leftarrow> get_refills sc_ptr;
    return $ refills_capacity usage refills
  od"

definition
  sufficient_refills :: "time \<Rightarrow> refill list \<Rightarrow> bool"
where
  "sufficient_refills usage refills = (MIN_BUDGET \<le> refills_capacity usage refills)"

definition
  refill_sufficient :: "obj_ref \<Rightarrow> time \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "refill_sufficient sc_ptr usage = do
    refills \<leftarrow> get_refills sc_ptr;
    return $ sufficient_refills usage refills
  od"

definition
  refill_ready :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "refill_ready sc_ptr = do
    cur_time \<leftarrow> gets cur_time;
    sc \<leftarrow> get_sched_context sc_ptr;
    sc_time \<leftarrow> return $ r_time (refill_hd sc);
    return $ sc_time \<le> cur_time + kernelWCET_ticks
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
    (case cap of SchedContextCap _ sc \<Rightarrow> (sc - core_sched_context_bytes) div refill_size_bytes
    | _ \<Rightarrow> 0) "  (* RT: is "sc" correct? *)

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
  maybe_add_empty_tail :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_add_empty_tail sc_ptr = do
     robin \<leftarrow> is_round_robin sc_ptr;
     when robin $ do
       cur_time \<leftarrow> gets cur_time;
       refill_add_tail sc_ptr \<lparr> r_time = cur_time, r_amount = 0 \<rparr>
     od
   od"


definition
  refill_new :: "obj_ref \<Rightarrow> nat \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_new sc_ptr max_refills budget period = do
    assert (MIN_BUDGET < budget);
    cur_time \<leftarrow> gets cur_time;
    refill \<leftarrow> return \<lparr> r_time = cur_time, r_amount = budget \<rparr>;
    update_sched_context sc_ptr
            (\<lambda>sc. sc\<lparr> sc_period := period, sc_refills := [refill], sc_refill_max := max_refills \<rparr>);
    maybe_add_empty_tail sc_ptr
  od"

(*definition   (* see the non-monad version *)
  schedule_used :: "obj_ref \<Rightarrow> refill \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "schedule_used sc_ptr new = do
    rfls \<leftarrow> get_refills sc_ptr;
    tl \<leftarrow> return $ last rfls;
    single \<leftarrow> refill_single sc_ptr;
    if (r_amount new < MIN_BUDGET \<and> \<not> single) then
      let newtl = tl \<lparr> r_amount := r_amount tl + r_amount new, r_time := max (r_time new) (r_time tl) \<rparr> in
      set_refills sc_ptr ((butlast rfls) @ [newtl])
    else if (r_time new \<le> r_time tl) then
      let newtl = tl \<lparr> r_amount := r_amount tl + r_amount new \<rparr> in
      set_refills sc_ptr ((butlast rfls) @ [newtl])
    else refill_add_tail sc_ptr new
  od" *)

fun
  schedule_used :: "refill list \<Rightarrow> refill \<Rightarrow> refill list"
where
  "schedule_used [] new = [new]"
| "schedule_used (x#rs) new =
    (let r_tl = last (x#rs) in
      if (r_amount new < MIN_BUDGET \<and> \<not> (rs = [])) then
      let newtl = r_tl \<lparr> r_amount := r_amount r_tl + r_amount new, r_time := max (r_time new) (r_time r_tl) \<rparr> in
      ((butlast (x#rs)) @ [newtl])
    else if (r_time new \<le> r_time r_tl) then
      let newtl = r_tl \<lparr> r_amount := r_amount r_tl + r_amount new \<rparr> in
      ((butlast (x#rs)) @ [newtl])
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
      refills' \<leftarrow> return $ refills_merge_prefix ((hd refills)\<lparr>r_time := ct\<rparr> # tl refills);
      assert (sufficient_refills 0 refills'); (* do we need this assert? *)
      set_refills sc_ptr refills'
    od
  od"

definition
  refill_split_check :: "obj_ref \<Rightarrow> time \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_split_check sc_ptr usage = do
    ct \<leftarrow> gets cur_time;
    sc \<leftarrow> get_sched_context sc_ptr;
    refills \<leftarrow> return (sc_refills sc);
    rfhd \<leftarrow> return $ hd refills;
    assert (0 < usage \<and> usage \<le> r_amount rfhd);
    assert (r_time rfhd \<le> ct);

    remaining \<leftarrow> return $ r_amount rfhd - usage;
    new \<leftarrow> return \<lparr> r_time = r_time rfhd + sc_period sc, r_amount = usage \<rparr>;

    if size refills = sc_refill_max sc \<or> remaining < MIN_BUDGET
    then if size refills = 1
      then set_refills sc_ptr [new \<lparr> r_amount := r_amount new + remaining \<rparr>]
      else
        let r2 = hd (tl refills); rs = tl (tl refills) in
        set_refills sc_ptr (schedule_used (r2 \<lparr>r_amount := r_amount r2 + remaining\<rparr> # rs) new)
    else
      set_refills sc_ptr (schedule_used (rfhd\<lparr>r_amount := remaining, r_time := r_time rfhd + usage\<rparr> # tl refills) new)
  od"

function
  refills_budget_check :: "ticks \<Rightarrow> ticks \<Rightarrow> refill list \<Rightarrow> ticks \<times> refill list"
where
  "refills_budget_check period usage [] = (usage, [])"
| "refills_budget_check period usage (r#rs) = (if r_amount r \<le> usage \<and> 0 < r_amount r
     then refills_budget_check period (usage - r_amount r)
                                         (schedule_used rs (r\<lparr>r_time := r_time r + period\<rparr>))
     else (usage, r#rs))"
  by pat_completeness auto

termination refills_budget_check
  apply (relation "measure (\<lambda>(p,u,rs). unat u)")
   apply clarsimp
  apply unat_arith
  done

fun
  min_budget_merge :: "bool \<Rightarrow> refill list \<Rightarrow> refill list"
where
  "min_budget_merge _ [] = []"
| "min_budget_merge _ [r] = [r]"
| "min_budget_merge full (r0#r1#rs) = (if (r_amount r0 < MIN_BUDGET \<or> full)
     then min_budget_merge False (r1\<lparr> r_amount := r_amount r1 + r_amount r0 \<rparr> # rs)
     else (r0#r1#rs))" (* RT: full can be true only at the beginning,
                              because the refills size decreases by 1 in each call *)


definition
  refill_budget_check :: "obj_ref \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_budget_check sc_ptr usage capacity = do
    sc \<leftarrow> get_sched_context sc_ptr;
    full \<leftarrow> return (size (sc_refills sc) = sc_refill_max sc); (* = refill_full sc_ptr *)
    assert (capacity < MIN_BUDGET \<or> full);
    period \<leftarrow> return $ sc_period sc;
    assert (period > 0); (* not round robin *)
    refills \<leftarrow> return (sc_refills sc);

    (usage', refills') \<leftarrow> return (if (capacity = 0) then
       refills_budget_check period usage refills
       else (usage, refills));

    refills'' \<leftarrow> return (if capacity = 0 \<and> 0 < usage' then
      let r1 = hd refills';
          r1' = r1 \<lparr>r_time := r_time r1 + usage\<rparr>;
          rs = tl refills'
      in if rs \<noteq> [] \<and> can_merge_refill r1' (hd rs)
         then merge_refill r1' (hd rs) # tl rs
         else r1'#rs
    else refills');

    set_refills sc_ptr refills'';

    capacity \<leftarrow> return $ refills_capacity usage' refills''; (* = refill_capacity sc_ptr usage'*)

    cur_time \<leftarrow> gets cur_time;  (* refill_ready sc_ptr *)
    ready \<leftarrow> return $ (r_time (hd refills'')) \<le> cur_time + kernelWCET_ticks;

    when (capacity > 0 \<and> ready) $ refill_split_check sc_ptr usage';
    full \<leftarrow> refill_full sc_ptr;
    update_sched_context sc_ptr (sc_refills_update (\<lambda>rs. min_budget_merge full rs))
  od"

definition
  refill_update :: "obj_ref \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> nat \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_update sc_ptr new_period new_budget new_max_refills = do
     sc \<leftarrow> get_sched_context sc_ptr;
     current \<leftarrow> gets cur_time;
     refill_hd \<leftarrow> return $ hd (sc_refills sc);

     cur_time \<leftarrow> gets cur_time;
     ready \<leftarrow> return $ (r_time refill_hd) \<le> cur_time + kernelWCET_ticks; (* refill_ready sc_ptr; *)

     new_time \<leftarrow> return $ if ready then current else (r_time refill_hd);
     if (r_amount refill_hd \<ge> new_budget)
     then do
       set_sched_context sc_ptr (sc\<lparr>sc_period := new_period, sc_refill_max := new_max_refills,
                                     sc_refills:=[\<lparr> r_time = new_time, r_amount = new_budget\<rparr>]\<rparr>);
       maybe_add_empty_tail sc_ptr
    od
    else
      set_sched_context sc_ptr (sc\<lparr>sc_period := new_period, sc_refill_max := new_max_refills,
         sc_refills:=[\<lparr> r_time = new_time, r_amount = r_amount refill_hd\<rparr>,
               \<lparr>r_time = new_time + new_period, r_amount = new_budget - (r_amount refill_hd)\<rparr>]\<rparr>)
od"

definition
  postpone :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "postpone sc_ptr = do
    tcb_opt \<leftarrow> get_sc_obj_ref sc_tcb sc_ptr;
    tcb_ptr \<leftarrow> assert_opt tcb_opt;
    do_extended_op $ tcb_sched_action tcb_sched_dequeue tcb_ptr;
    do_extended_op $ tcb_release_enqueue tcb_ptr;
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
     in_release_q \<leftarrow> select_ext (in_release_queue tptr) {True,False};
     sched \<leftarrow> is_schedulable tptr in_release_q;
     when sched $ do
       ts \<leftarrow> thread_get tcb_state tptr;

       cur_time \<leftarrow> gets cur_time;
       ready \<leftarrow> return $ (r_time (refill_hd sc)) \<le> cur_time + kernelWCET_ticks; (* refill_ready sc_ptr *)

       sufficient \<leftarrow> return $ sufficient_refills 0 (sc_refills sc); (* refill_sufficient sc_ptr 0 *)

       when (runnable ts \<and> 0 < sc_refill_max sc \<and> \<not>(ready \<and> sufficient)) $ postpone sc_ptr
     od
   od"


text {* consumed related functions *}

definition
  sched_context_update_consumed :: "obj_ref \<Rightarrow> (time,'z::state_ext) s_monad" where
  "sched_context_update_consumed sc_ptr \<equiv> do
    sc \<leftarrow> get_sched_context sc_ptr;
    set_sched_context sc_ptr (sc\<lparr>sc_consumed := 0 \<rparr>);
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
      set_message_info ct $ MI sent 0 0 0 (* RT: is this correct? *)
    od"

text {* yield\_to related functions *}
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
         set_sc_obj_ref sc_yield_from_update sc_ptr None;
         set_tcb_obj_ref tcb_yield_to_update tcb_ptr None;
         set_thread_state tcb_ptr Running
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
  test_possible_switch_to :: "obj_ref \<Rightarrow> unit det_ext_monad"
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
    sched_context_resume sc_ptr;
    do_extended_op $ test_possible_switch_to tcb_ptr
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
         when (sc_tcb = None) $ sched_context_donate sc_ptr tcb_ptr
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

text \<open> Update time consumption of current scheduling context and current domain. \<close>
definition
  commit_time :: "(unit, 'z::state_ext) s_monad"
where
  "commit_time = do
    consumed \<leftarrow> gets consumed_time;
    csc \<leftarrow> gets cur_sc;
    sc \<leftarrow> get_sched_context csc;
    when (0 < consumed) $ do
      robin \<leftarrow> return (sc_period sc = 0); (* is_round_robin csc;*)
      if robin then
        let new_hd = ((refill_hd sc) \<lparr> r_time := r_time (refill_hd sc) - consumed \<rparr>);
            new_tl = ((refill_tl sc) \<lparr> r_time := r_time (refill_tl sc) + consumed \<rparr>) in
        set_refills csc (new_hd # [new_tl])
      else refill_split_check csc consumed
    od;
    do_extended_op $ commit_domain_time; (***)
    update_sched_context csc (\<lambda>sc. sc\<lparr>sc_consumed := (sc_consumed sc) + consumed \<rparr>);
    modify (\<lambda>s. s\<lparr>consumed_time := 0\<rparr> )
  od"

section "Global time"

definition
  rollback_time :: "(unit, 'z::state_ext) s_monad"
where
  "rollback_time = do
    consumed \<leftarrow> gets consumed_time;
    reprogram \<leftarrow> gets reprogram_timer;
    assert (\<not> reprogram \<or> consumed = 0);
    modify (\<lambda>s. s\<lparr>cur_time := cur_time s - consumed \<rparr>);
    modify (\<lambda>s. s\<lparr>consumed_time := 0\<rparr> )
  od"


text \<open>Update current and consumed time.\<close>
definition
  update_time_stamp :: "(unit, 'z::state_ext) s_monad"
where
  "update_time_stamp = do
    prev_time \<leftarrow> gets cur_time;
    cur_time' \<leftarrow> do_machine_op getCurrentTime;
    modify (\<lambda>s. s\<lparr> cur_time := cur_time' \<rparr>);
    modify (\<lambda>s. s\<lparr> consumed_time := cur_time' - prev_time \<rparr>)
  od"

text {* Suspend a thread, cancelling any pending operations and preventing it
from further execution by setting it to the Inactive state. *}
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
     do_extended_op (tcb_sched_action (tcb_sched_dequeue) thread)
   od"


end
