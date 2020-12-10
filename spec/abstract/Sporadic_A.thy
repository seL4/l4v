(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Scheduling Contexts and Control"

theory Sporadic_A
imports "CSpaceAcc_A"
begin

text \<open> This theory contains basic operations on scheduling contexts. \<close>

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
  maybe_add_empty_tail :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_add_empty_tail sc_ptr = do
     robin <- is_round_robin sc_ptr;
     when robin $ do
       sc <- get_sched_context sc_ptr;
       refills <- return (sc_refills sc);
       empty_refill <- return \<lparr>r_time = r_time (hd refills), r_amount = 0\<rparr>;
       set_sc_obj_ref sc_refills_update sc_ptr (refills @ [empty_refill])
     od
   od"

definition
  refill_new :: "obj_ref \<Rightarrow> nat \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_new sc_ptr max_refills budget period = do
     assert (MIN_BUDGET < budget);
     cur_time \<leftarrow> gets cur_time;
     refill \<leftarrow> return \<lparr> r_time = cur_time, r_amount = budget \<rparr>;
     set_sc_obj_ref sc_period_update sc_ptr period;
     set_sc_obj_ref sc_refills_update sc_ptr [refill];
     set_sc_obj_ref sc_refill_max_update sc_ptr max_refills;
     set_sc_obj_ref sc_budget_update sc_ptr budget;
     maybe_add_empty_tail sc_ptr
   od"

definition
  "can_merge_refill r1 r2 \<equiv> r_time r2 \<le> r_time r1 + r_amount r1"

definition
  merge_refill :: "refill \<Rightarrow> refill \<Rightarrow> refill"
where
  "merge_refill r1 r2 = \<lparr> r_time = r_time r1, r_amount = r_amount r2 + r_amount r1 \<rparr>"

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
    ct \<leftarrow> gets cur_time;
    refills \<leftarrow> get_refills sc_ptr;

    ready \<leftarrow> get_sc_refill_ready sc_ptr;
    when (ready \<and> \<not>robin) $ do
         modify (\<lambda>s. s\<lparr> reprogram_timer := True \<rparr>);
         refills' \<leftarrow> return $ refills_merge_prefix ((hd refills)\<lparr>r_time := ct + kernelWCET_ticks\<rparr>
                                                    # tl refills);
         set_refills sc_ptr refills'
         od
  od"

definition
  refill_budget_check_round_robin :: "ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_budget_check_round_robin usage = do
    sc_ptr \<leftarrow> gets cur_sc;
    sc \<leftarrow> get_sched_context sc_ptr;
    refills \<leftarrow> return (sc_refills sc);
    set_refills sc_ptr [\<lparr>r_time = r_time (hd refills), r_amount = r_amount (hd refills) - usage\<rparr>,
                        \<lparr>r_time = r_time (hd (tl refills)), r_amount = r_amount (hd (tl refills)) + usage\<rparr>]
   od"

fun
  MIN_BUDGET_merge :: "refill list \<Rightarrow> refill list"
where
  "MIN_BUDGET_merge [] = []"
| "MIN_BUDGET_merge [r] = [r]"
| "MIN_BUDGET_merge (r0 # r1 # rs)
    = (if r_amount r0 < MIN_BUDGET
       then let new_hd = \<lparr>r_time = r_time r1 - r_amount r0,
                          r_amount = r_amount r0 + r_amount r1\<rparr>
            in MIN_BUDGET_merge (new_hd # rs)
       else r0 # r1 # rs)"

definition
  refill_budget_check :: "ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_budget_check usage = do
    sc_ptr \<leftarrow> gets cur_sc;
    sc \<leftarrow> get_sched_context sc_ptr;
    period \<leftarrow> return (sc_period sc);
    refills \<leftarrow> return (sc_refills sc);

    robin \<leftarrow> is_round_robin sc_ptr;
    assert (\<not>robin);

    usage' \<leftarrow> return $ min usage (r_amount (hd refills));

    when (usage' > 0) $ do
      used \<leftarrow> return \<lparr>r_time = r_time (hd refills) + period, r_amount = usage'\<rparr>;
      adjusted_hd \<leftarrow> return \<lparr>r_time = r_time (hd refills) + usage',
                             r_amount = r_amount (hd refills) - usage'\<rparr>;
      full \<leftarrow> refill_full sc_ptr;
      refills' \<leftarrow> return $ schedule_used full (adjusted_hd # (tl refills)) used;
      set_refills sc_ptr (refills_merge_prefix (MIN_BUDGET_merge refills'))
    od

   od"

definition
  refill_update :: "obj_ref \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> nat \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_update sc_ptr new_period new_budget new_max_refills = do

     set_sc_obj_ref sc_budget_update sc_ptr new_budget;
     set_sc_obj_ref sc_period_update sc_ptr new_period;
     set_sc_obj_ref sc_refill_max_update sc_ptr new_max_refills;

     sc \<leftarrow> get_sched_context sc_ptr;
     refills \<leftarrow> return (sc_refills sc);
     refill_hd \<leftarrow> return (hd refills);
     ready \<leftarrow> get_sc_refill_ready sc_ptr;
     cur_time \<leftarrow> gets cur_time;
     new_time \<leftarrow> return $ if ready then cur_time else (r_time refill_hd);
     refill_hd \<leftarrow> return $ \<lparr>r_time = new_time, r_amount = r_amount refill_hd\<rparr>;

     if new_budget \<le> r_amount refill_hd
     then do set_refills sc_ptr [refill_hd\<lparr>r_amount := new_budget\<rparr>];
             maybe_add_empty_tail sc_ptr
          od
     else do unused \<leftarrow> return $ new_budget - r_amount refill_hd;
             new \<leftarrow> return \<lparr>r_time = r_time refill_hd + new_period, r_amount = unused\<rparr>;
             set_refills sc_ptr ([refill_hd] @ [new])
          od

    od"

end